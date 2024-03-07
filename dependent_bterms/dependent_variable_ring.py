from sage.symbolic.ring import SR

from sage.rings.asymptotic.asymptotic_ring import AsymptoticRing, AsymptoticExpansion
from sage.rings.asymptotic.term_monoid import TermMonoidFactory
from sage.symbolic.expression import Expression

from .structures import (
    MonBoundExactTermMonoidFactory,
    MonBoundOTermMonoidFactory,
    MonBoundBTermMonoidFactory,
    AsymptoticRingWithCustomPosetKey,
)


def _add_monomial_growth_restriction_to_ring(
        AR: AsymptoticRing,
        dependent_variable: Expression,
        lower_bound: AsymptoticExpansion,
        upper_bound: AsymptoticExpansion,
    ) -> AsymptoticRing:
    """Helper function to modify a given asymptotic ring such
    that an additional symbolic variable bounded in a specified
    range is supported.

    ::

        sage: A, n, k = AsymptoticRingWithDependentVariable('n^QQ', 'k', 0, 1/2)
        sage: A.B(k*n)
        B(abs(k)*n, n >= 0)
        sage: (k*n).O()
        O(n^(3/2))
    """
    lower_bound = AR(lower_bound)
    upper_bound = AR(upper_bound)
    term_monoid_factory = TermMonoidFactory(
        name=f"{__name__}.TermMonoidFactory",
        exact_term_monoid_class=MonBoundExactTermMonoidFactory(
            dependent_variable=dependent_variable,
            lower_bound=lower_bound,
            upper_bound=upper_bound,
        ),
        O_term_monoid_class=MonBoundOTermMonoidFactory(
            dependent_variable=dependent_variable,
            lower_bound=lower_bound,
            upper_bound=upper_bound,
        ),
        B_term_monoid_class=MonBoundBTermMonoidFactory(
            dependent_variable=dependent_variable,
            lower_bound=lower_bound,
            upper_bound=upper_bound,
        ),
    )
    return AR.change_parameter(term_monoid_factory=term_monoid_factory)

def AsymptoticRingWithDependentVariable(
        growth_group,
        dependent_variable,
        lower_bound_power,
        upper_bound_power,
        **ring_kwargs
    ):
    """Instantiate a special (univariate) :class:`.AsymptoticRing` that
    is aware of a monomially bounded symbolic variable.

    INPUT:

    - ``growth_group`` -- the (univariate) growth group of
      the :class:`.AsymptoticRing`.

    - ``dependent_variable`` -- a string representing a variable
      in the :class:`.SymbolicRing`, or any valid input for 
      :meth:`.SymbolicRing.var`.

    - ``lower_bound_power`` -- a nonnegative real number, the power
      to which the ring's independent variable is raised to in order
      to obtain the lower monomial power bound.

    - ``upper_bound_power`` -- analogous to ``lower_bound_power``, just
      for the upper bound.

    - ``ring_kwargs`` -- further keyword arguments being passed to
      the :class:`.AsymptoticRing` constructor.


    SEEALSO:

    - :class:`.AsymptoticRing`


    TESTS::

        sage: A, n, k = AsymptoticRingWithDependentVariable('n^QQ', 'k', 0, 1/2)
        sage: A.term_monoid_factory.BTermMonoid
        <class '__main__.MonBoundBTermMonoidFactory.<locals>.MonBoundBTermMonoid'>
        sage: O(k*n)
        O(n^(3/2))
    """
    AR = AsymptoticRingWithCustomPosetKey(
        growth_group=growth_group,
        coefficient_ring=SR,
        **ring_kwargs
    )
    k = SR.var(dependent_variable)
    n = AR.gen()
    AR_with_bound = _add_monomial_growth_restriction_to_ring(
        AR,
        k,
        lower_bound=n**lower_bound_power,
        upper_bound=n**upper_bound_power
    )
    n = AR_with_bound.gen()
    return AR_with_bound, n, k