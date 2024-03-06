from sage.ext.fast_callable import fast_callable
from sage.symbolic.expression import Expression
from sage.rings.asymptotic.asymptotic_ring import AsymptoticExpansion

__all__ = [
    'evaluate',
    'simplify_expansion',
]

def evaluate(expression: Expression, **eval_args):
    """Evaluate a symbolic expression without necessarily
    returning a result in the symbolic ring.
    
    Tests::

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