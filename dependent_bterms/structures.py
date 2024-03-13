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

from sage.functions.other import ceil
from sage.rings.asymptotic.asymptotic_ring import AsymptoticRing
from sage.rings.asymptotic.term_monoid import (
    BTermMonoid,
    BTerm,
    ExactTermMonoid,
    OTermMonoid,
    OTerm,
    TermWithCoefficient,
    ExactTerm
)
from sage.symbolic.assumptions import assuming
from sage.symbolic.expression import Expression
from sage.symbolic.operators import add_vararg

from sage.all import SR

from .utils import evaluate


def _verify_variable_and_bounds(dependent_variable, lower_bound, upper_bound):

    if not dependent_variable.is_symbol():
        raise ValueError("A suitable dependent variable must be passed.")

    if lower_bound is None or upper_bound is None:
        raise ValueError("The lower und upper bounds for the dependent variable must be set.")

def _element_key(element):
    """Determine the key for sorting the given element into the poset
    underlying an asymptotic expansion.
    
    The first component of the key is a growth bound consisting
    of both the actual growth in terms of the independent variable,
    combined with an estimate for a growth of the coefficient (using
    the specified bound for the dependent variable).
    The second component is the element growth (regardless of any coefficient).
    """
    growth_bound = None
    if hasattr(element.parent(), 'variable_bounds'):
        bound_var, lower, upper = element.parent().variable_bounds

        if isinstance(element, TermWithCoefficient):
            coef = element.coefficient

            if isinstance(coef, Expression) and bound_var in coef.variables():
                with assuming(bound_var > 0):
                    coef_simplified = coef.simplify()

                bounds = []
                for bound in [lower, upper]:
                    asy_bound = evaluate(coef_simplified, **{str(bound_var): bound})
                    if asy_bound.is_zero():
                        asy_bound = bound.parent().one()
                    bounds.append(asy_bound.O())
                
                coef_bound = max(
                    bounds,
                    key=lambda expr: list(expr.summands)[0].growth
                )
                [coef_bound_term] = list(coef_bound.summands)
                growth_bound = coef_bound_term.growth * element.growth

    
    if growth_bound is None:
        growth_bound = element.growth
    
    return (growth_bound, element.growth)


class AsymptoticRingWithCustomPosetKey(AsymptoticRing):
    def _element_constructor_(self, data, simplify=True, convert=True):
        from sage.data_structures.mutable_poset import MutablePoset
        from sage.rings.asymptotic.term_monoid import can_absorb, absorption
        element = super()._element_constructor_(data, simplify=simplify, convert=convert)

        element._summands_ = MutablePoset(
            list(element.summands),
            key=_element_key,
            can_merge=can_absorb,
            merge=absorption,
        )
        return element

    @staticmethod
    def _create_empty_summands_():
        from sage.data_structures.mutable_poset import MutablePoset
        from sage.rings.asymptotic.term_monoid import can_absorb, absorption
        return MutablePoset(key=_element_key,
                            can_merge=can_absorb,
                            merge=absorption)



class DependentGrowthAwareMixin:
    """Mixin class for implementing properties related to the
    monomial bounds.
    """
    @property
    def dependent_variable(self):
        return self._dependent_variable
    
    @property
    def dependent_variable_lower_bound(self):
        return self._lower_bound
    
    @property
    def dependent_variable_upper_bound(self):
        return self._upper_bound
    
    @property
    def variable_bounds(self):
        return (
            self.dependent_variable,
            self.dependent_variable_lower_bound,
            self.dependent_variable_upper_bound
        )

class MonBoundOTerm(OTerm):
    """OTerm that is coefficient-growth aware.

    ::

        sage: import dependent_bterms as dbt
        sage: A, n, k = dbt.AsymptoticRingWithDependentVariable('n^QQ', 'k', -1/2, 1/2, default_prec=4)
        sage: O(pi*n)
        O(n)
        sage: O(n*k)
        O(n^(3/2))
        sage: O(A(k^6))
        O(n^3)
        sage: O(n/k^2)
        O(n^2)
        sage: O(n/(1 + k^2))
        O(n)

        sage: 42*n + O(k^10 / n^4)
        O(n)
        sage: (1 + k + k^2) * O(n)
        O(n^2)
        sage: k^3*n + O(n^2)
        k^3*n + O(n^2)
        sage: k*n + O(n)
        k*n + O(n)

        sage: 1/(1 - k/n)
        1 + k*n^(-1) + k^2*n^(-2) + k^3*n^(-3) + O(n^(-2))
        sage: exp(k/n)
        1 + k*n^(-1) + 1/2*k^2*n^(-2) + 1/6*k^3*n^(-3) + O(n^(-2))
    """
    def __init__(self, parent, growth, coefficient):
        self._growth = growth
        if (
            isinstance(coefficient, Expression) 
            and parent.dependent_variable in coefficient.variables()
        ):
            
            _, lower, upper = parent.variable_bounds
            bounds = []
            for value in (lower, upper):
                eval_arg = {
                    str(parent.dependent_variable): value
                }
                bounds.append(evaluate(coefficient, **eval_arg).O())

            [coefficient_bound] = list(sum(bounds).summands)
            growth *= coefficient_bound.growth
            
        super().__init__(parent, growth)

    def dependent_growth_range(self):
        return (self.growth, self.growth)
    
    def can_absorb(self, other):
        if isinstance(other, TermWithCoefficient):
            return all(
                self.growth >= growth_bound 
                for growth_bound in other.dependent_growth_range()
            )
        return self.growth >= other.growth


def MonBoundOTermMonoidFactory(dependent_variable, lower_bound, upper_bound):
    _verify_variable_and_bounds(dependent_variable, lower_bound, upper_bound)

    class MonBoundOTermMonoid(OTermMonoid, DependentGrowthAwareMixin):
        Element = MonBoundOTerm

        def __init__(
            self,
            term_monoid_factory,
            growth_group,
            coefficient_ring,
            category,
        ):
            self._dependent_variable = dependent_variable
            self._lower_bound = lower_bound
            self._upper_bound = upper_bound

            super().__init__(
                term_monoid_factory, growth_group, coefficient_ring, category
            )

        def _convert_construction_(self, kwds_construction):
            try:
                del kwds_construction['valid_from']
            except KeyError:
                pass


    return MonBoundOTermMonoid


class MonBoundBTerm(BTerm):
    """BTerm that is coefficient growth aware.
    
    ::
        sage: from dependent_bterms.structures import MonBoundBTermMonoidFactory
        sage: A.<n> = AsymptoticRing('n^QQ', SR)
        sage: from sage.rings.asymptotic.term_monoid import DefaultTermMonoidFactory as TMF
        sage: k = SR.var('k')
        sage: BTermMonoidClass = MonBoundBTermMonoidFactory(k, 1, n, None)
        sage: MBTM = BTermMonoidClass(TMF, A.growth_group, A.coefficient_ring)
        sage: MBTM.variable_bounds
        (k, 1, n)
        sage: (ng,) = A.growth_group.gens_monomial()
        sage: A.create_summand(MBTM, coefficient=42*k, growth=ng^-2, valid_from=5)
        B(42*abs(k)*n^(-2), n >= 5)

        sage: A.create_summand(MBTM, coefficient=k-1, growth=ng^(-1), valid_from=10)
        B((abs(k + 1))*n^(-1), n >= 10)
    """
    def __init__(self, parent, growth, valid_from, **kwds):
        coef = kwds['coefficient']

        def round_coef(c):
            prec = parent._bterm_floating_point_digits
            if prec is not None:
                return SR(ceil(c * 10**prec) / 10**prec)
            return c
        
        if (
            isinstance(coef, Expression) 
            and parent.dependent_variable in coef.variables()
        ):
            with assuming(parent.dependent_variable > 0):        
                coef_expanded = coef.simplify().expand()
                coef_expanded_bound = sum(
                    round_coef(abs(c)) * parent.dependent_variable**p
                    for (c, p) in coef_expanded.coefficients(parent.dependent_variable)
                )
            kwds['coefficient'] = coef_expanded_bound
        else:
            kwds['coefficient'] = round_coef(coef)
        super().__init__(parent, growth, valid_from, **kwds)

    def dependent_growth_range(self):
        dependent_variable, lower, upper = self.parent().variable_bounds
        if not (
            isinstance(self.coefficient, Expression) 
            and dependent_variable in self.coefficient.variables()
        ):
            return (self.growth, self.growth)
        
        boundary_growths = []
        with assuming(dependent_variable > 0):
            coef_simplified = self.coefficient.simplify()
        for value in (lower, upper):
            eval_arg = {
                str(dependent_variable): value
            }
            term = evaluate(coef_simplified, **eval_arg)
            if term.is_zero():
                term = value.parent().one()
            term = term.O()
            [term] = list(term.summands)
            boundary_growths.append(term.growth * self.growth)
        
        return (min(boundary_growths), max(boundary_growths))
    
    def can_absorb(self, other):
        self_growth_lower, self_growth_upper = self.dependent_growth_range()
        other_growth_lower, other_growth_upper = other.dependent_growth_range()
        return (
            (self.growth >= other.growth) and
            (self_growth_lower >= other_growth_lower) and
            (self_growth_upper >= other_growth_upper)
        )
    
    def _absorb_(self, other):
        r"""
        
        ::

            sage: import dependent_bterms as dbt
            sage: A, n, k = dbt.AsymptoticRingWithDependentVariable('n^QQ', 'k', 0, 1/2)
            sage: A.B(k/n, valid_from=10) + k^5/n^5
            B(101/100*abs(k)*n^(-1), n >= 10)

            sage: A, n, k = dbt.AsymptoticRingWithDependentVariable('n^QQ', 'k', 0, 1/2, bterm_round_to=2)
            sage: A.B(1/n, valid_from=10) + 1/n^10
            B(101/100*n^(-1), n >= 10)
        """
        k, lower, upper = self.parent().variable_bounds
        with assuming(k > 0):
            self_coef = self.coefficient.simplify().expand()
            other_coef = other.coefficient.simplify().expand()
        
        if self_coef.degree(k) >= other_coef.degree(k):
            return super()._absorb_(other)

        # Degree of other coefficient in k is higher,
        # needs to be reduced first.

        with assuming(k > 0):
            other_coef_abs = other_coef.parent().zero()
            if other_coef.operator() is add_vararg:
                for op in other_coef.operands():
                    other_coef_abs += abs(op).simplify()
            else:
                other_coef_abs = abs(other_coef).simplify()
            
        other_coef_bound = other_coef_abs(k=1)
        deg_difference = other_coef.degree(k) - self_coef.degree(k)
        [difference_term] = list((upper ** deg_difference).summands)

        other_bound = other.parent()(
            other.growth * difference_term.growth,
            coefficient=other_coef_bound * k ** self_coef.degree(k)
        )
        return super()._absorb_(other_bound)



def MonBoundBTermMonoidFactory(dependent_variable, lower_bound, upper_bound, bterm_round_to):
    _verify_variable_and_bounds(dependent_variable, lower_bound, upper_bound)

        
    class MonBoundBTermMonoid(BTermMonoid, DependentGrowthAwareMixin):
        Element = MonBoundBTerm

        def __init__(
            self,
            term_monoid_factory,
            growth_group,
            coefficient_ring,
            category,
        ):
            self._dependent_variable = dependent_variable
            self._lower_bound = lower_bound
            self._upper_bound = upper_bound
            self._bterm_floating_point_digits = bterm_round_to

            super().__init__(
                term_monoid_factory, growth_group, coefficient_ring, category
            )

    
    return MonBoundBTermMonoid

class MonBoundExactTerm(ExactTerm):

    def dependent_growth_range(self):
        dependent_variable, lower, upper = self.parent().variable_bounds
        if dependent_variable not in self.coefficient.variables():
            return (self.growth, self.growth)
        
        boundary_growths = []
        with assuming(dependent_variable > 0):
            coef_simplified = self.coefficient.simplify()
        for value in (lower, upper):
            eval_arg = {
                str(dependent_variable): value
            }
            term = evaluate(coef_simplified, **eval_arg)
            if term.is_zero():
                term = value.parent().one()
            term = term.O()
            [term] = list(term.summands)
            boundary_growths.append(term.growth * self.growth)
        
        return (min(boundary_growths), max(boundary_growths))

def MonBoundExactTermMonoidFactory(
        dependent_variable,
        lower_bound,
        upper_bound
    ):
    _verify_variable_and_bounds(dependent_variable, lower_bound, upper_bound)
    

    class MonBoundExactTermMonoid(ExactTermMonoid, DependentGrowthAwareMixin):
        Element = MonBoundExactTerm

        def __init__(
            self,
            term_monoid_factory,
            growth_group,
            coefficient_ring,
            category,
        ):
            self._dependent_variable = dependent_variable
            self._lower_bound = lower_bound
            self._upper_bound = upper_bound

            super().__init__(
                term_monoid_factory, growth_group, coefficient_ring, category
            )

    return MonBoundExactTermMonoid
