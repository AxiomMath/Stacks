module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartPointCriterion

/-!
# The square of a chart localized at a prime of `𝒪_{X'}(U')`

Let `ch` be a Cartesian affine-open chart for a base-change square of schemes, with coordinate
rings `R = 𝒪_S(V)`, `A = 𝒪_X(U)`, `R' = 𝒪_{S'}(V')`, `A' = 𝒪_{X'}(U')`, and let `p` be a prime of
`A'`. The localization `A'_p` is again an `R`-, `A`- and `R'`-algebra, and the resulting square

```
R  ---> A
|       |
v       v
R' ---> A'_p
```

commutes. It is no longer a pushout square — `A'_p` is a localization of `A ⊗_R R'`, not that
tensor product — but the ring-level map of Stacks 0DJ7 needs no pushout hypothesis, so it is
defined for this square as well. That map is the affine reduction's meeting point with the
pointwise condition (1) of Stacks 0DJ8: at the point of `U'` that `p` names, the four rings above
are the four local rings of the base-change square.

This module records the algebra structures, the two scalar towers, the flatness of
`A' → A'_p`, and the base change of `RΓ(U', K')` to `A'_p`, which is the object the Stacks 0DJ7
map for the localized square has as its target.

## Main definitions

* `AlgebraicGeometry.BaseChangeChart.localizedAlgebraR`, `localizedAlgebraA`,
  `localizedAlgebraR'`: the three algebra structures on `A'_p`.
* `AlgebraicGeometry.BaseChangeChart.localizedSections'`: the derived sections `RΓ(U', K')` base
  changed to `A'_p`.

## Main results

* `AlgebraicGeometry.BaseChangeChart.flat_algebraMap_localization`: `A' → A'_p` is flat.
* `AlgebraicGeometry.BaseChangeChart.isScalarTower_localizedA`,
  `isScalarTower_localizedR'`: the two scalar towers of the localized square.

## Implementation notes

The algebra structures are defined by composing the chart's ring maps with `algebraMap A' A'_p`
rather than by transporting an existing instance, so that both scalar towers hold by the chart's
own square `isPushout_hom` and the definitional unfolding of `RingHom.toAlgebra`.

No tag attribute is placed here: nothing below states a clause of Stacks 0DJ8. The declarations
are the data the affine reduction consumes.

## References

* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars)

universe u

namespace AlgebraicGeometry

namespace BaseChangeChart

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}
  (ch : BaseChangeChart f g f' g') (p : Ideal ch.A') [p.IsPrime]

/-- The localization `𝒪_{X'}(U')_p` is an `𝒪_S(V)`-algebra, through the chart's `c ∘ a`. -/
@[instance_reducible]
public def localizedAlgebraR : Algebra ch.R (Localization.AtPrime p) :=
  ((algebraMap ch.A' (Localization.AtPrime p)).comp (ch.c.hom.comp ch.a.hom)).toAlgebra

/-- The localization `𝒪_{X'}(U')_p` is an `𝒪_X(U)`-algebra, through the chart's `c`. -/
@[instance_reducible]
public def localizedAlgebraA : Algebra ch.A (Localization.AtPrime p) :=
  ((algebraMap ch.A' (Localization.AtPrime p)).comp ch.c.hom).toAlgebra

/-- The localization `𝒪_{X'}(U')_p` is an `𝒪_{S'}(V')`-algebra, through the chart's `d`. -/
@[instance_reducible]
public def localizedAlgebraR' : Algebra ch.R' (Localization.AtPrime p) :=
  ((algebraMap ch.A' (Localization.AtPrime p)).comp ch.d.hom).toAlgebra

/-- **`𝒪_{X'}(U') → 𝒪_{X'}(U')_p` is flat**, being a localization. -/
public theorem flat_algebraMap_localization :
    RingHom.Flat (algebraMap ch.A' (Localization.AtPrime p)) :=
  RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ p.primeCompl)

section Towers

attribute [local instance] localizedAlgebraR localizedAlgebraA localizedAlgebraR'

/-- The tower `𝒪_S(V) → 𝒪_X(U) → 𝒪_{X'}(U')_p` of the localized square. -/
public theorem isScalarTower_localizedA :
    letI := ch.a.hom.toAlgebra
    IsScalarTower ch.R ch.A (Localization.AtPrime p) :=
  let := ch.a.hom.toAlgebra
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The tower `𝒪_S(V) → 𝒪_{S'}(V') → 𝒪_{X'}(U')_p` of the localized square. It is the chart's
own pushout square of rings, pushed along `𝒪_{X'}(U') → 𝒪_{X'}(U')_p`. -/
public theorem isScalarTower_localizedR' :
    letI := ch.b.hom.toAlgebra
    IsScalarTower ch.R ch.R' (Localization.AtPrime p) :=
  let := ch.b.hom.toAlgebra
  IsScalarTower.of_algebraMap_eq fun r =>
    congrArg (algebraMap ch.A' (Localization.AtPrime p))
      (DFunLike.congr_fun ch.isPushout_hom r)

end Towers

/-- `RΓ(U', K')` base changed to the local ring `𝒪_{X'}(U')_p`. -/
public abbrev localizedSections' (K' : DerivedCategory X'.Modules) :
    DerivedCategory (ModuleCat.{u} (Localization.AtPrime p)) :=
  (totalDerivedExtensionScalars.{u, u, u}
    (algebraMap ch.A' (Localization.AtPrime p))).functor.obj
      ((affineDerivedSections ch.incU').obj K')

end BaseChangeChart

end AlgebraicGeometry

end
