# dependent_bterms

An extension to SageMath's module for computations with asymptotic expansions.
Provides a special AsymptoticRing that allows to specify a secondary,
dependent (monomially bounded) variable.

## Quickstart and Summary

The package can be made available to your SageMath installation by running
```sh
$ sage -pip install dependent_bterms
```
from your terminal, or just
```
!pip install dependent_bterms
```
from within a SageMath Jupyter notebook. The package can then be used as
follows:
```py
sage: import dependent_bterms as dbt
sage: AR, n, k = dbt.AsymptoticRingWithDependentVariable(  # create a special AsymptoticRing
....:     'n^QQ',  # in one asymptotic (monomial) variable n with rational powers
....:     'k', 0, 1/2,  # with a symbolic variable k assumed to be in the range n^0 <= k <= n^(1/2)
....:     bterm_round_to=2  # and explicit error terms should be rounded to two decimal places
....: )
sage: k*n^2 + O(n^(3/2)) + k^3*n  # summands are ordered w.r.t. their highest potential growth
k^3*n  + k*n^2 + O(n^(3/2))
sage: asy = 1/n + AR.B(k/n^2, valid_from=10)
sage: asy_exp = dbt.taylor_with_explicit_error(lambda t: exp(t), asy, order=3, valid_from=10)
sage: asy_exp
1 + n^(-1) + B((abs(28/25*k + 73/100))*n^(-2), n >= 10)
sage: dbt.simplify_expansion(asy_exp, simplify_bterm_growth=True)
1 + n^(-1) + B(34/25*n^(-3/2), n >= 10)
```

One-line descriptions of the top-level members exported with this module
are given below. A description of their respective input arguments and
several examples are provided in the respective docstrings.

- `AsymptoticRingWithDependentVariables` -- A special (univariate) `AsymptoticRing`
   that is aware of a monomially bounded symbolic variable.

- `evaluate` -- Evaluate a symbolic expression without necessarily returning a
  result in the symbolic ring.

- `simplify_expansion` -- Simplify an asymptotic expansion by allowing error
  terms to try and absorb parts of exact terms.

- `round_bterm_coefficients` -- Round the coefficients of all B-terms in the
  given expansion to the next integer (or rational with respect to the provided
  precision).

- `set_bterm_valid_from` -- Changes the point from which a B-term bound is valid
  such that the term remains valid.

- `expansion_upper_bound` -- Returns an upper bound for the given asymptotic
  expansion by turning all B-term instances into exact terms

- `taylor_with_explicit_error` -- Determines the series expansion with explicit
  error bounds of a given function `f` at a specified asymptotic term.


## Demo

A worksheet containing a comprehensive introduction to the capabilities of
this package can be found here: [`toolbox_demo.ipynb`](toolbox_demo.ipynb).


## Standalone installation in Python (no prior SageMath installation needed)

This package can be installed in Python, using the modularized distributions
of the Sage library from the passagemath project.

```sh
$ pip install "git+https://github.com/passagemath/passagemath-pkg-dependent_bterms.git[passagemath]"
```
