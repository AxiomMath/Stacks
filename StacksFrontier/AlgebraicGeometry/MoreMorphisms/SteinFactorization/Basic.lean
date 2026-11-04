module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksCore.Tactic.StacksAttribute

/-!
# The Stein factorization of a universally closed morphism

Let `f : X ⟶ S` be a universally closed and quasi-separated morphism of schemes.  Then `f` is
quasi-compact, so the normalization `S' = f.normalization` of `S` in `X` is defined and `f`
factors as
`X --f'--> S' --π--> S`
with `f' = f.toNormalization` and `π = f.fromNormalization`.  This module records the elementary
properties of the two factors: `f'` is universally closed, quasi-compact, quasi-separated and
surjective, while `π` is integral.

## Main results

* `Stacks.SteinFactorization.toNormalization_fromNormalization`: the factorization itself, with
  the normalization of `S` in `X` as its intermediate scheme.  A proper morphism is quasi-compact
  and quasi-separated, so this is also the factorization of [Stacks Project, Tag 03H2].
* `Stacks.SteinFactorization.quasiCompact_toNormalization`,
  `Stacks.SteinFactorization.quasiSeparated_toNormalization`,
  `Stacks.SteinFactorization.universallyClosed_toNormalization`,
  `Stacks.SteinFactorization.surjective_toNormalization`: the four properties of the first
  factor.
* `Stacks.SteinFactorization.isIntegralHom_fromNormalization`: the second factor is integral.

## Implementation notes

The intermediate scheme is Mathlib's relative normalization
`AlgebraicGeometry.Scheme.Hom.normalization`, which is the object of
[Stacks Project, Tag 035H].

## References

* [Stacks Project, Tag 03GY](https://stacks.math.columbia.edu/tag/03GY)
* [Stacks Project, Tag 03H2](https://stacks.math.columbia.edu/tag/03H2)
* [Stacks Project, Tag 035H](https://stacks.math.columbia.edu/tag/035H)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.SteinFactorization

variable {X S : Scheme.{u}} (f : X ⟶ S)

section QuasiCompact

variable [QuasiCompact f] [QuasiSeparated f]

/-- **Stacks Project, Tag 03GY.**  A quasi-compact, quasi-separated morphism `f : X ⟶ S`
factors as `f = f' ≫ π`, where `S'` is the normalization of `S` in `X`, where `f'` is the
canonical map to `S'` and where `π` is the structure morphism of `S'`.

A proper morphism is quasi-compact and quasi-separated, so this also supplies the factorization
of [Stacks Project, Tag 03H2]. -/
@[stacks 03GY "relative_normalization", stacks 03H2 "normalization"]
public theorem toNormalization_fromNormalization :
    f.toNormalization ≫ f.fromNormalization = f :=
  Scheme.Hom.toNormalization_fromNormalization f

/-- **Stacks Project, Tag 03GY.**  The first map of the factorization is quasi-compact. -/
@[stacks 03GY "first_quasi_compact"]
public theorem quasiCompact_toNormalization : QuasiCompact f.toNormalization :=
  inferInstance

/-- **Stacks Project, Tag 03GY.**  The first map of the factorization is quasi-separated. -/
@[stacks 03GY "first_quasi_separated"]
public theorem quasiSeparated_toNormalization : QuasiSeparated f.toNormalization :=
  inferInstance

/-- **Stacks Project, Tag 03GY.**  The second map of the factorization, the structure morphism
of the normalization of `S` in `X`, is integral.

A proper morphism is quasi-compact and quasi-separated, so this also supplies the integrality of
the second factor in [Stacks Project, Tag 03H2]. -/
@[stacks 03GY "integral_second_map", stacks 03H2 "integral_second_map"]
public theorem isIntegralHom_fromNormalization : IsIntegralHom f.fromNormalization :=
  inferInstance

end QuasiCompact

section UniversallyClosed

variable [UniversallyClosed f] [QuasiSeparated f]

/-- **Stacks Project, Tag 03GY.**  The first map of the factorization of a universally closed,
quasi-separated morphism is universally closed. -/
@[stacks 03GY "first_universally_closed"]
public theorem universallyClosed_toNormalization : UniversallyClosed f.toNormalization :=
  inferInstance

/-- **Stacks Project, Tag 03GY.**  The first map of the factorization of a universally closed,
quasi-separated morphism is surjective: it is universally closed and dominant. -/
@[stacks 03GY "first_surjective"]
public theorem surjective_toNormalization : Surjective f.toNormalization :=
  inferInstance

end UniversallyClosed

end Stacks.SteinFactorization
