# Intrinsic centers of filter germs

Import `MinimalPrimes.Order.Filter.Germ.Center` for the small API, or
`MinimalPrimes` for the root export.

For `ι : Type u`, `M : Type v`, an arbitrary filter `D : Filter ι`, and a
representative `f : ι → M`, the characteristic interface is

```lean
Filter.Germ.mem_center_coe_iff (D : Filter ι) (f : ι → M)
```

Under `[Mul M]`, it identifies

```lean
(f : Filter.Germ D M) ∈ Set.center (Filter.Germ D M)
```

with `∀ᶠ i in D, f i ∈ Set.center M`. The two universes are independent.
This is the existing intrinsic magma center, including all three fields:

- `Commute z a` for every `a`;
- `z * (a * b) = (z * a) * b` for every `a, b`;
- `(a * b) * z = a * (b * z)` for every `a, b`.

With `[MulOneClass M]`, `Filter.Germ.mem_submonoid_center_coe_iff D f` gives
the same criterion for `Submonoid.center`. Its proof uses the existing carrier
identity `Submonoid.coe_center`; a two-sided identity is enough, with no
associativity assumption. Neither endpoint adds a predicate, carrier, evaluator,
or quotient construction. The two membership criteria are the public interface.

## Why varying tests matter

Sufficiency eliminates arbitrary test germs to representatives and applies each
centrality field on the same eventual central locus. Necessity tests against
varying witnesses to the failure of each field. At a good coordinate the supplied
value `f i` provides the fallback. Consequently, no separately supplied inhabitant
of `M` or properness assumption on `D` is needed. Only three eventual sets are
intersected; the proof does not commute an arbitrary intersection with the filter.

At the bottom filter the represented-function statement still holds. Empty index
and codomain types are permitted in the primary result: a given representative
supplies exactly what is needed, without asserting that a germ exists when no
function exists. The bundled statement already has its supplied unit.

## One finite varying client

The [client](../MinimalPrimesTest/Order/Filter/Germ/Center.lean) uses `Fin 4` with table

| × | 0 | 1 | 2 | 3 |
|---|---|---|---|---|
| 0 | 0 | 0 | 0 | 0 |
| 1 | 0 | 1 | 2 | 3 |
| 2 | 0 | 2 | 3 | 2 |
| 3 | 0 | 3 | 3 | 2 |

Zero and one are central. The multiplication is not commutative, since
`2 * 3 = 2` but `3 * 2 = 3`, and it is not associative, since
`(2 * 2) * 2 = 3` but `2 * (2 * 2) = 2`.
The function on `Fin 3` with values `0, 1, 2`, at the principal filter generated
by `{0, 1}`, represents a central germ. Its third value is noncentral, and the
two distinct retained values prevent the germ from being constant. This single
client exercises the nonassociative class floor and the eventual, rather than
everywhere or constant, character of the criterion.

## Foundations and attribution

The module builds on Mathlib's [intrinsic magma center](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Algebra/Group/Center.lean)
by Eric Wieser and Jireh Loreaux, its [submonoid center](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/GroupTheory/Submonoid/Center.lean)
by Eric Wieser, and the [germ API](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Order/Filter/Germ/Basic.lean)
by Yury Kudryashov and Abhimanyu Pallavi Sudhir. See [CREDITS](../CREDITS.md).
This generic germ API is a Mathlib-upstream candidate.
