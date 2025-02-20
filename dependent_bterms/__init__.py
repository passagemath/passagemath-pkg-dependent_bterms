"""Extension of SageMath's asymptotic ring that allows handling
monomially bounded auxiliary variables.

Everything in the ``utils`` module, as well as the
``AsymptoticRingWithDependentVariable`` convenience function are
being made available as top-level imports.

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

from .dependent_variable_ring import AsymptoticRingWithDependentVariable
from .utils import *
