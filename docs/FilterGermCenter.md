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
or quotient construction. These criteria underlie the equivalence below.

## Germs of centers and total central lifts

At the same `MulOneClass` floor,

```lean
Filter.Germ.centerEquiv (M := M) D :
  Filter.Germ D ↥(Submonoid.center M) ≃*
    ↥(Submonoid.center (Filter.Germ D M))
```

is a canonical multiplicative equivalence. The two carriers and the equivalence
lie in `Type (max u v)`. Its forward map is characterized by `coe_centerEquiv`:
after forgetting the central subtype, it is `Filter.Germ.map Subtype.val`.
`coe_centerEquiv_coe` gives the pointwise coercion equation on representatives.
The ordinary `MulEquiv` API supplies multiplication, unit and inverse laws.

`map_subtype_centerEquiv_symm` says that forgetting the subtype after taking the
inverse recovers the original central germ. `centerEquiv_symm_eq_coe` identifies
that inverse with any total center-valued function whose underlying germ is the
given germ. Thus uniqueness is at the germ level, not at each index.

For `z : ↥(Submonoid.center (Filter.Germ D M))`,
`Filter.Germ.centerRepresentative D z` is a total function
`ι → ↥(Submonoid.center M)`. Its germ is the inverse image of `z`, by
`coe_centerRepresentative`. Given a representative `f` of a central germ,
`centerRepresentative_eventuallyEq D f hf` says that the underlying selected
function agrees with `f` eventually. Users need not unfold either construction.

Surjectivity repairs exceptional values with the existing central unit. No extra
default element, proper filter or nonempty index assumption is required. A
selected representative is not canonical pointwise and need not take a prescribed
value on ignored indices. Bottom and empty-index filters remain covered. An empty
codomain cannot carry the supplied `MulOneClass`; this is not an extra assumption.
At the top filter the representative agreement is pointwise.

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
everywhere or constant, character of the criterion. It also uses
`centerRepresentative` to obtain `liftedVaryingValue`, a total function into the
actual center. The retained values are still `0` and `1`. Since the original
third value is noncentral, the total central lift cannot agree with it everywhere;
no particular replacement value is asserted.

## Foundations and attribution

The module builds on Mathlib's [intrinsic magma center](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Algebra/Group/Center.lean)
by Eric Wieser and Jireh Loreaux, its [submonoid center](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/GroupTheory/Submonoid/Center.lean)
by Eric Wieser, and the [germ API](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Order/Filter/Germ/Basic.lean)
by Yury Kudryashov and Abhimanyu Pallavi Sudhir. Injectivity reuses the library's
varying-application criterion in `Order/Filter/Germ/Map.lean`. See [CREDITS](../CREDITS.md).
This generic germ API is a Mathlib-upstream candidate.
