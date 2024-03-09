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
from sage.symbolic.expression import Expression
from sage.symbolic.assumptions import assuming

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

            if bound_var in coef.variables():
                with assuming(bound_var > 0):
                    coef_simplified = coef.simplify()

                coef_bound = max(
                    [evaluate(coef_simplified, **{str(bound_var): bound}).O()
                    for bound in [lower, upper]],
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
    
    def can_absorb(self, other):
        dependent_variable, lower, upper = self.parent().variable_bounds
        if isinstance(other, TermWithCoefficient) and dependent_variable in other.coefficient.variables():
            boundary_terms = []
            for value in (lower, upper):
                eval_arg = {
                    str(dependent_variable): value
                }
                term = evaluate(other.coefficient, **eval_arg).O()
                [term] = list(term.summands)
                boundary_terms.append(term * other)
            return all(self.can_absorb(term) for term in boundary_terms)
        return self.growth >= other.growth

def MonBoundOTermMonoidFactory(dependent_variable, lower_bound, upper_bound):
    _verify_variable_and_bounds(dependent_variable, lower_bound, upper_bound)

    class MonBoundOTermMonoid(OTermMonoid):
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
    
    return MonBoundOTermMonoid

class MonBoundBTerm(BTerm):
    """BTerm that is coefficient growth aware.
    
    ::
        sage: from dependent_bterms.structures import MonBoundBTermMonoidFactory
        sage: A.<n> = AsymptoticRing('n^QQ', SR)
        sage: from sage.rings.asymptotic.term_monoid import DefaultTermMonoidFactory as TMF
        sage: k = SR.var('k')
        sage: BTermMonoidClass = MonBoundBTermMonoidFactory(k, 1, n)
        sage: MBTM = BTermMonoidClass(TMF, A.growth_group, A.coefficient_ring)
        sage: MBTM.variable_bounds
        (k, 1, n)
        sage: (ng,) = A.growth_group.gens_monomial()
        sage: A.create_summand(MBTM, coefficient=42*k, growth=ng^-2, valid_from=5)
        B(42*abs(k)*n^(-2), n >= 5)
    """
    
    def can_absorb(self, other):
        # TODO: proper absorption, cf. MonBoundOTerm.can_absorb
        return self.growth == other.growth
    
    def _absorb_(self, other):
        return super()._absorb_(other)



def MonBoundBTermMonoidFactory(dependent_variable, lower_bound, upper_bound):
    _verify_variable_and_bounds(dependent_variable, lower_bound, upper_bound)

        
    class MonBoundBTermMonoid(BTermMonoid):
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

            super().__init__(
                term_monoid_factory, growth_group, coefficient_ring, category
            )

        
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
    
    return MonBoundBTermMonoid

class MonBoundExactTerm(ExactTerm):
    pass

def MonBoundExactTermMonoidFactory(
        dependent_variable,
        lower_bound,
        upper_bound
    ):
    _verify_variable_and_bounds(dependent_variable, lower_bound, upper_bound)
    

    class MonBoundExactTermMonoid(ExactTermMonoid):
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

    return MonBoundExactTermMonoid
