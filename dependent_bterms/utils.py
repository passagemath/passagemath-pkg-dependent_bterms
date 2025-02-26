"""Utility functions for working with expansions in the special
asymptotic ring provided by this package.

TESTS::

    sage: import dependent_bterms as dbt
    sage: AR, n, k = dbt.AsymptoticRingWithDependentVariable('n^QQ', 'k', 0, 1/2)
    sage: AR.B(k*n)
    doctest:warning
    ...
    FutureWarning: ...
    ...
    B(abs(k)*n, n >= 0)

"""

from __future__ import annotations


from sage.arith.srange import srange
from sage.ext.fast_callable import fast_callable
from sage.functions.other import ceil
from sage.symbolic.assumptions import assuming
from sage.symbolic.expression import Expression
from sage.symbolic.operators import add_vararg
from sage.rings.asymptotic.asymptotic_ring import AsymptoticExpansion, AsymptoticRing
from sage.rings.asymptotic.term_monoid import (
    BTerm,
    ExactTerm,
    OTerm,
    TermWithCoefficient,
)

from sage.rings.infinity import Infinity as oo
from sage.symbolic.ring import SR
from sage.rings.real_mpfi import RIF
from sage.rings.integer_ring import Z as ZZ

import dependent_bterms as dbt

__all__ = [
    "evaluate",
    "simplify_expansion",
    "round_bterm_coefficients",
    "set_bterm_valid_from",
    "expansion_upper_bound",
    "taylor_with_explicit_error",
]


def evaluate(expression: Expression, **eval_args):
    """Evaluate a symbolic expression without necessarily
    returning a result in the symbolic ring.

    INPUT:

    - ``expression`` -- a symbolic expression.

    - ``eval_args`` -- the values to be input for the variables
      in keyword argument form.

    EXAMPLES::

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
    expression = expression.expand()
    expression_vars = expression.variables()
    function_args = [eval_args.get(str(var), var) for var in expression_vars]

    return fast_callable(expression, vars=expression_vars)(*function_args)


def _distribute_coefficient(
    summand: TermWithCoefficient,
    ring: AsymptoticRing,
    simplify_bterm_growth: bool = False,
):
    term_type = "exact" if isinstance(summand, ExactTerm) else "B"
    extra_args = {} if term_type == "exact" else {"valid_from": summand.valid_from}
    result_summands = []
    k, _, upper = summand.parent().variable_bounds
    with assuming(k > 0):
        coef_expanded = summand.coefficient.simplify().expand()
    if term_type == "B" and simplify_bterm_growth:
        rest = ring.create_summand(
            term_type,
            coefficient=ring.coefficient_ring.one(),
            growth=summand.growth,
            valid_from=summand.valid_from,
        )
        return [evaluate(coef_expanded, **{str(k): upper}) * rest]
    if coef_expanded.operator() is add_vararg:
        for part_coef in coef_expanded.operands():
            result_summands.append(
                ring.create_summand(
                    term_type,
                    coefficient=part_coef,
                    growth=summand.growth,
                    **extra_args,
                )
            )
    else:
        result_summands.append(ring(summand))

    return result_summands


def simplify_expansion(
    expr: AsymptoticExpansion,
    simplify_bterm_growth: bool = False,
):
    """Simplify an asymptotic expansion by allowing error terms
    to try and absorb parts of exact terms.

    INPUT:

    - ``expr`` -- an asymptotic expansion.

    - ``simplify_bterm_growth`` -- if ``False`` (the default), B-terms
      are only expanded but remain otherwise unchanged. If ``True``,
      the upper bound of the monomially bounded variable is substituted
      which effectively collapses the B-terms to a single, "absolute" term.

    EXAMPLES::

        sage: import dependent_bterms as dbt
        sage: A, n, k = dbt.AsymptoticRingWithDependentVariable('n^QQ', 'k', 0, 1/2, bterm_round_to=1)
        sage: asy = (k + 1)^5*n + A.B(n^2, valid_from=10); asy
        ((k + 1)^5)*n + B(n^2, n >= 10)
        sage: dbt.simplify_expansion(asy)
        (k^5 + 5*k^4 + 10*k^3)*n + B(127/10*n^2, n >= 10)

        sage: dbt.simplify_expansion(A.B((k + 1)/n, valid_from=10))
        B((abs(k + 1))*n^(-1), n >= 10)
        sage: dbt.simplify_expansion(A.B((k + 1)/n, valid_from=10), simplify_bterm_growth=True)
        B(7/5*n^(-1/2), n >= 10)

    """
    A = expr.parent()
    new_expr = A.zero()
    for summand in expr.summands:
        if isinstance(summand, OTerm):
            new_expr += A(summand)
        elif isinstance(summand, BTerm):
            k, _, _ = summand.parent().variable_bounds
            if k in summand.coefficient.variables():
                distributed_summands = _distribute_coefficient(
                    summand, A, simplify_bterm_growth=simplify_bterm_growth
                )
                for part_summand in distributed_summands:
                    new_expr += part_summand
            else:
                new_expr += A(summand)

    for summand in expr.summands:
        if summand.is_exact():
            k, _, _ = summand.parent().variable_bounds
            if k in summand.coefficient.variables():
                distributed_summands = _distribute_coefficient(summand, A)
                for part_summand in distributed_summands:
                    new_expr += part_summand
            else:
                new_expr += A(summand)

    return new_expr


def round_bterm_coefficients(
    expansion: AsymptoticExpansion, floating_point_digits: int = 0
):
    """Rounds the coefficients of all BTerms in the given expansion to the
    next integer (or rational with respect to the provided precision).

    INPUT:

    - ``expansion`` -- an asymptotic expansion.

    - ``floating_point_digits`` -- the number of floating point digits
      to which the B-term coefficients should be rounded to.

    EXAMPLES::

        sage: import dependent_bterms as dbt
        sage: A.<n> = AsymptoticRing('n^QQ', QQ)
        sage: some_expansion = n - A.B(27/23/n^2, valid_from=10)
        sage: some_expansion
        n + B(27/23*n^(-2), n >= 10)
        sage: dbt.round_bterm_coefficients(some_expansion)
        n + B(2*n^(-2), n >= 10)
        sage: dbt.round_bterm_coefficients(some_expansion, floating_point_digits=3)
        n + B(587/500*n^(-2), n >= 10)
    """

    def bterm_map(t):
        if isinstance(t, BTerm):
            if isinstance(t.coefficient, Expression) and hasattr(
                t.parent(), "dependent_variable"
            ):
                k = t.parent().dependent_variable
                with assuming(k > 0):
                    coef_expanded = t.coefficient.simplify().expand()
                    coef_bound = sum(
                        ceil(c * 10**floating_point_digits)
                        / 10**floating_point_digits
                        * k**p
                        for (c, p) in coef_expanded.coefficients(k)
                    )
                t.coefficient = coef_bound
            else:
                t.coefficient = (
                    ceil(t.coefficient * 10**floating_point_digits)
                    / 10**floating_point_digits
                )
        return t

    # note: expansion.summands.copy() returns a shallow copy, which makes
    # this somewhat cumbersome.
    import copy

    P = expansion.parent()
    expansion_copy = sum(
        (P(copy.deepcopy(summand), convert=False) for summand in expansion.summands),
        P.zero(),
    )
    expansion_copy.summands.map(bterm_map)
    return expansion_copy


def set_bterm_valid_from(asy: AsymptoticExpansion, valid_from: dict[str, int] | int):
    """Changes the point from which a B-Term bound is valid
    such that the term remains valid.

    The validity bounds can only be increased.

    INPUT:

    - ``asy`` - an asymptotic expansion.

    - ``valid_from`` -- a dictionary mapping variable names to the new
      validity bounds, or a single integer to be used for all variables.

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

    INPUTS:

    - ``numeric`` -- If false (the default), the constructed bound is
      returned as an exact asymptotic expansion containing variables. Otherwise,
      a positive number is returned which results from substituting the variables
      in the "symbolic" bound with the smallest integers such that all involved
      B-terms are valid.

    - ``valid_from`` --  A new ``valid_from`` value to be used for all B-Terms.

    EXAMPLES::

        sage: import dependent_bterms as dbt
        sage: from dependent_bterms import expansion_upper_bound
        sage: A, n, k = dbt.AsymptoticRingWithDependentVariable('n^QQ', 'k', 0, 1/2)

        sage: expansion_upper_bound(n^2 + n + 1)
        n^2 + n + 1

        sage: expansion_upper_bound(1 + A.B(42/n, valid_from=5))
        1 + 42*n^(-1)

        sage: expansion_upper_bound(n - A.B(1/n^2, valid_from=1))
        n + n^(-2)

        sage: expansion_upper_bound(1/n - A.B(1/n^2, valid_from=10), numeric=True)
        11/100

        sage: expansion_upper_bound(1 + O(1/n))
        Traceback (most recent call last):
        ...
        ValueError: No same-order bound can be constructed for O(n^(-1))

        sage: expansion_upper_bound(-k/n)
        k*n^(-1)
        sage: expansion_upper_bound(-k/n, numeric=True, valid_from=10)
        1/10*sqrt(10)

        sage: expansion_upper_bound(A.B(k/n, valid_from=10), numeric=True)
        1/10*sqrt(10)

        sage: expansion_upper_bound((-2 + k)/n, numeric=True, valid_from=10)
        1/10*sqrt(10) + 1/5

    """
    A = asy.parent()
    bound = A.zero()
    valid_from = {
        v: valid_from or A.coefficient_ring.one() for v in asy.variable_names()
    }
    for summand in asy.summands:
        if isinstance(summand, TermWithCoefficient):
            coef = summand.coefficient
            if isinstance(coef, Expression) and hasattr(
                summand.parent(), "dependent_variable"
            ):
                k = summand.parent().dependent_variable
                with assuming(k > 0):
                    coef = coef.simplify().expand()
                    coef = sum(abs(c) * k**p for (c, p) in coef.coefficients(k))
            else:
                coef = abs(coef)
            bound += A.create_summand(
                "exact",
                coefficient=coef,
                data=summand.growth,
            )
            if isinstance(summand, BTerm):
                for v, bd in summand.valid_from.items():
                    valid_from[v] = max(valid_from[v], bd)
        else:
            raise ValueError(f"No same-order bound can be constructed for {summand}")

    if numeric:
        # check that expansion is bounded, in O(1)
        OT_one = A.term_monoid("O")(A.growth_group.one())
        if not all(OT_one.can_absorb(summand) for summand in bound.summands):
            raise ValueError(
                "Cannot determine numeric bound, the expansion "
                f"{bound} does not seem to be bounded."
            )

        if isinstance(A, dbt.structures.AsymptoticRingWithCustomPosetKey):
            ETM = A.term_monoid("exact")
            dependent_variable, _, upper = ETM.variable_bounds
            bound = bound.map_coefficients(
                lambda t: t.subs({dependent_variable: upper.subs(valid_from)})
            )

        return bound.subs(valid_from)

    return bound


def taylor_with_explicit_error(
    f,
    term: AsymptoticExpansion,
    order=None,
    valid_from=None,
    round_constant=True,
):
    r"""Determines the Taylor series expansion with explicit error bounds
    of a given function `f` at a specified asymptotic term.

    The term is assumed to be in o(1).

    INPUT:

    - ``f`` -- a callable function to be expanded.

    - ``term`` -- the asymptotic expansion (converging to 0) describing
      the center of the Taylor expansion.

    - ``order`` -- the order of the expansion. If ``None`` (the default),
      the default precision of the underlying asymptotic ring is used.

    - ``valid_from`` -- the point from which the error term is valid.

    - ``round_constant`` -- if ``True`` (the default), the bound for the
      derivative used to construct the error term is rounded to the closest
      integer.

    EXAMPLES::

        sage: import dependent_bterms as dbt
        sage: A, n, k = dbt.AsymptoticRingWithDependentVariable('n^QQ', 'k', 0, 1/2)

        sage: some_expansion = 2/n + 3/n^2 + A.B(4/n^3, valid_from=10)
        sage: expansion = dbt.taylor_with_explicit_error(lambda t: 1/(1 - t), some_expansion, order=3)
        sage: expansion
        1 + 2*n^(-1) + 7*n^(-2) + B(7149339/125000*n^(-3), n >= 10)
        sage: dbt.round_bterm_coefficients(expansion)
        1 + 2*n^(-1) + 7*n^(-2) + B(58*n^(-3), n >= 10)

        sage: dbt.taylor_with_explicit_error(lambda t: 1/(1 - t), k/n, order=3, valid_from=10)
        1 + k*n^(-1) + k^2*n^(-2) + B(5*abs(k^3)*n^(-3), n >= 10)

        sage: asy = dbt.taylor_with_explicit_error(lambda t: exp(t), (1 + k)/n, order=3, valid_from=10)
        sage: asy
        1 + (k + 1)*n^(-1) + (1/2*(k + 1)^2)*n^(-2) + B((abs(k^3 + 3*k^2 + 3*k + 1))*n^(-3), n >= 10)
        sage: dbt.simplify_expansion(asy)
        1 + (k + 1)*n^(-1) + (1/2*k^2 + k)*n^(-2) + B((abs(k^3 + 3*k^2 + 3*k + 1))*n^(-3), n >= 10) + 1/2*n^(-2)
        sage: dbt.simplify_expansion(asy, simplify_bterm_growth=True)
        1 + (k + 1)*n^(-1) + 1/2*k^2*n^(-2) + B((9/25*sqrt(10) + 23/10)*n^(-3/2), n >= 10)

        sage: dbt.taylor_with_explicit_error(exp, k/(10*n), order=3, valid_from=1000)
        1 + 1/10*k*n^(-1) + 1/200*k^2*n^(-2) + B(1/1000*abs(k^3)*n^(-3), n >= 1000)
        sage: A, n, k = dbt.AsymptoticRingWithDependentVariable('n^QQ', 'k', 0, 1/2, bterm_round_to=1)
        sage: dbt.taylor_with_explicit_error(exp, k/(10*n), order=3, valid_from=1000)
        1 + 1/10*k*n^(-1) + 1/200*k^2*n^(-2) + B(1/10*abs(k^3)*n^(-3), n >= 1000)

    TESTS:

    Make sure that functions for which the evaluation at an
    asymptotic expansion is not defined can still be used::

        sage: dbt.taylor_with_explicit_error(lambda t: sin(t)*cos(t), k/n, order=4, valid_from=10)
        k*n^(-1) - 2/3*k^3*n^(-3) + B(abs(k)^4*n^(-4), n >= 10)

    """
    if not term.is_little_o_of_one():
        raise ValueError("The asymptotic term needs to tend to 0.")

    AR = term.parent()

    if valid_from is not None:
        set_bterm_valid_from(term, valid_from=valid_from)

    if order is None:
        order = AR.default_prec

    zero = AR.coefficient_ring.zero()
    taylor_expansion = AR.zero()
    term_power = AR.one()
    sym = SR.var("z")
    f_sym = f(sym)

    for j in srange(order):
        taylor_expansion += evaluate(f_sym, z=zero) * term_power

        f_sym = f_sym.diff(sym, 1) / (j + 1)
        term_power *= term

    term_bound = expansion_upper_bound(term, valid_from=valid_from, numeric=True)
    bound_const = abs(evaluate(f_sym, z=RIF([0, term_bound]))).upper()

    if not bound_const < oo:
        raise ValueError(
            f"Could not find a finite bound for the derivative {f_sym} on the interval [0, {term_bound}]."
        )

    if round_constant:
        bound_const = ceil(bound_const)

    taylor_bound = bound_const * term_power
    if valid_from is None:
        valid_from = {str(v): ZZ.one() for v in AR.gens()}
        for summand in taylor_bound.error_part().summands:
            if isinstance(summand, BTerm):
                valid_from = {
                    v: max(bd, summand.valid_from.get(v, ZZ.one()))
                    for v, bd in valid_from.items()
                }

    taylor_bound = AR.B(taylor_bound, valid_from=valid_from)
    return taylor_expansion + taylor_bound
