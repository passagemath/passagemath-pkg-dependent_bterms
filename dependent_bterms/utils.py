"""

::

    sage: import dependent_bterms as dbt
    sage: AR, n, k = dbt.AsymptoticRingWithDependentVariable('n^QQ', 'k', 0, 1/2)
    sage: AR.B(k*n)
    doctest:warning
    ...
    FutureWarning: ...
    ...
    B(abs(k)*n, n >= 0)

"""

from sage.ext.fast_callable import fast_callable
from sage.symbolic.expression import Expression
from sage.rings.asymptotic.asymptotic_ring import AsymptoticExpansion
from sage.rings.asymptotic.term_monoid import BTerm, ExactTerm
from sage.rings.integer_ring import ZZ

__all__ = [
    'evaluate',
    'simplify_expansion',
    'set_bterm_valid_from',
    'expansion_upper_bound',
]

def evaluate(expression: Expression, **eval_args):
    """Evaluate a symbolic expression without necessarily
    returning a result in the symbolic ring.
    
    Tests::

        sage: from dependent_bterms import evaluate
        sage: var('a b c')
        (a, b, c)
        sage: res = evaluate(a*b*c, a=1, b=2, c=3)
        sage: res, res.parent()
        (6, Integer Ring)
        sage: evaluate(a + b, b=42)
        a + 42
        
        sage: A.<n> = AsymptoticRing('n^QQ', SR, default_prec=3)
        sage: evaluate(a/(b + c), a=n, b=1)
        (1/(c + 1))*n
        sage: evaluate(a/(b + c), a=pi, b=-1/n, c=1)
        pi + pi*n^(-1) + pi*n^(-2) + O(n^(-3))
    
    """
    expression_vars = expression.variables()
    function_args = [eval_args.get(str(var), var) for var in expression_vars]

    return fast_callable(expression, vars=expression_vars)(*function_args)


def simplify_expansion(expr: AsymptoticExpansion):
    """Simplify an asymptotic expansion by allowing error terms
    to try and absorb parts of exact terms."""
    from sage.symbolic.operators import add_vararg
    
    A = expr.parent()
    new_expr = A.zero()
    for summand in expr.summands:
        if not summand.is_exact():
            new_expr += A(summand)
    
    for summand in expr.summands:
        if summand.is_exact():
            k, _, _ = summand.parent().variable_bounds
            if k in summand.coefficient.variables():
                coef_expanded = summand.coefficient.expand()
                if coef_expanded.operator() is add_vararg:
                    for part_coef in coef_expanded.operands():
                        new_expr += A.create_summand('exact', coefficient=part_coef, growth=summand.growth)
                else:
                    new_expr += A(summand)
            else:
                new_expr += A(summand)
    return new_expr


def set_bterm_valid_from(asy: AsymptoticExpansion, valid_from: dict[str, int] | int):
    """Changes the point from which a BTerm bound is valid
    such that the term remains valid.

    That is, the bounds can only be increased.

    TESTS::

        sage: A.<n> = AsymptoticRing('n^QQ', QQ)
        sage: t = 1/n - A.B(n^-3, valid_from=5)

        sage: from dependent_bterms import expansion_upper_bound, set_bterm_valid_from
        sage: expansion_upper_bound(t, numeric=True) == 1/5 + 1/5^3
        True

        sage: set_bterm_valid_from(t, valid_from={'z': 42})
        n^(-1) + B(n^(-3), n >= 5)

        sage: set_bterm_valid_from(t, valid_from={'n': 42})
        n^(-1) + B(n^(-3), n >= 42)

        sage: set_bterm_valid_from(t, valid_from={n: 43})
        n^(-1) + B(n^(-3), n >= 43)

        sage: set_bterm_valid_from(t, valid_from=10)
        n^(-1) + B(n^(-3), n >= 43)

        sage: AM.<k, m> = AsymptoticRing('k^QQ * m^QQ', QQ)
        sage: t = AM.B(1/k, valid_from=3) + A.B(1/m, valid_from=10)
        sage: set_bterm_valid_from(t, valid_from=5)
        B(k^(-1), k >= 5, m >= 5) + B(m^(-1), k >= 10, m >= 10)
    """
    default_value = ZZ.one()
    if valid_from in ZZ:
        default_value = valid_from
        valid_from = dict()
    else:
        valid_from = {str(v): bound for (v, bound) in valid_from.items()}
    for term in asy.summands:
        if isinstance(term, BTerm):
            for v, bound in term.valid_from.items():
                passed_bound = valid_from.get(v, default_value)
                if bound < passed_bound:
                    term.valid_from[v] = passed_bound
    return asy


def expansion_upper_bound(
        asy: AsymptoticExpansion,
        numeric: bool = False,
        valid_from: int | None = None,
    ) -> AsymptoticExpansion:
    r"""Returns an upper bound for the given asymptotic expansion
    by turning all :class:`.BTerm` instances into exact terms.

    Raises an error if no such bound can be constructed.
    
    PARAMETERS
    ----------
    numeric
        If false (the default), the constructed bound is
        returned as an exact asymptotic expansion containing
        variables. Otherwise, a positive number is returned
        which results from substituting the variables in the
        "symbolic" bound with the smallest integers such that
        all involved B-Terms are valid.
    valid_from
        
        

    EXAMPLES::

        sage: A.<n> = AsymptoticRing('n^QQ', QQ)

        sage: from dependent_bterms import expansion_upper_bound
        sage: expansion_upper_bound(n^2 + n + 1)
        n^2 + n + 1

        sage: expansion_upper_bound(1 + A.B(42/n, valid_from=5))
        1 + 42*n^(-1)

        sage: expansion_upper_bound(n - A.B(1/n^2, valid_from=1))
        n + n^(-2)

        sage: expansion_upper_bound(n - A.B(1/n^2, valid_from=10), numeric=True)
        1001/100

        sage: expansion_upper_bound(1 + O(1/n))
        Traceback (most recent call last):
        ...
        ValueError: No same-order bound can be constructed for O(n^(-1))

    """
    A = asy.parent()
    bound = A.zero()
    valid_from = {v: valid_from or A.coefficient_ring.one() for v in asy.variable_names()}
    for summand in asy.summands:
        if isinstance(summand, ExactTerm):
            bound += A(summand)
        elif isinstance(summand, BTerm):
            bound += A.create_summand(
                'exact',
                coefficient=abs(summand.coefficient),
                data=summand.growth,
            )
            for v, bd in summand.valid_from.items():
                valid_from[v] = max(valid_from[v], bd)
        else:
            raise ValueError(f"No same-order bound can be constructed for {summand}")
    
    if numeric:
        return bound.subs(valid_from)
    
    return bound