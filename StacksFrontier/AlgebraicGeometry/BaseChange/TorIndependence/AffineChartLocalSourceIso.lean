module

public import
  StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartCohomologyCorners
public import
  StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.LocalizedSquareDomainHomology

/-!
# The source identification of the cube at a chart, on cohomology

`AlgebraicGeometry.BaseChangeChart.squareComparison_localRings` reads the Tag 065Z comparison of
the four local rings of a chart at a point `y` of `Spec 𝒪_{X'}(U')` through
`RingTheory.TorIndependence.localizedSquareDomainIso` on the source. This module gives that
source identification at the chart's rings, with `𝒪_S(V) → 𝒪_{S', f' x'}` taken as the composite
`ch.toStalkR' ∘ ch.b` through `𝒪_{S'}(V')`, and its two equivariances on cohomology.

The composite `baseStalkMap ∘ ch.toStalkR` through `𝒪_{S, f(g' x')}` is the same ring map
(`AlgebraicGeometry.BaseChangeChart.toStalkR'_b`) but not the same term, so the two give different
`Algebra 𝒪_S(V) 𝒪_{S', f' x'}` instances and hence different rings
`𝒪_X(U) ⊗_{𝒪_S(V)} 𝒪_{S', f' x'}`. The identification is
`RingTheory.TorIndependence.localizedSquareDomainIsoOfEq`, which takes the ring map as data, at
the chart.

Applied to the derived stalk `K_{g' x'}`, the target of the identification is, on cohomology, the
base-change cohomology over the two local rings `𝒪_{S, f(g' x')} → 𝒪_{X, g' x'}` and
`𝒪_{S, f(g' x')} → 𝒪_{S', f' x'}` of the derived stalk of `K`.

## Main definitions

* `AlgebraicGeometry.BaseChangeChart.localRingsSourceIso`: the source identification at the
  chart's rings.

## Main results

* `AlgebraicGeometry.BaseChangeChart.localRingsSourceIso_homology_smul`: it is equivariant for
  scalar multiplication on the complex by `𝒪_{X, g' x'}`, which it carries to the left tensor
  factor of `𝒪_{X, g' x'} ⊗_{𝒪_{S, f(g' x')}} 𝒪_{S', f' x'}`.
* `AlgebraicGeometry.BaseChangeChart.localRingsSourceIso_homology_includeRight_smul`: it is
  equivariant for the right tensor factor `𝒪_{S', f' x'}`.

## Implementation notes

The three localization inputs are the chart's own: `ch.toStalkR` is the localization at the prime
of `f (g' x')` by `AlgebraicGeometry.BaseChangeChart.isLocalization_toStalkR`, and the two
compatibilities are `AlgebraicGeometry.BaseChangeChart.toStalkA_a` and
`AlgebraicGeometry.BaseChangeChart.toStalkR'_b`. The algebra structures are the chart's ring maps
taken as data, written as `letI` in the statements, exactly as in
`AlgebraicGeometry.BaseChangeChart.homologyBaseChangeLocalizedIso` and
`AlgebraicGeometry.BaseChangeChart.germBaseChangeCohomologyIso`.

## References

* [Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
attribute [local instance] ModuleCat.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars)
open scoped TensorProduct ChangeOfRings

universe u

namespace AlgebraicGeometry

namespace BaseChangeChart

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}
  (ch : BaseChangeChart f g f' g') (y : Spec ch.A') (w : g' ≫ f = f' ≫ g)

/-- **The source identification of the cube at a chart.** On a complex `P` of
`𝒪_{X, g' x'}`-modules,

`((P|_{𝒪_X(U)})|_{𝒪_S(V)}) ⊗ᴸ_{𝒪_S(V)} 𝒪_{S', f' x'}  ≅
  (P|_{𝒪_{S, f(g' x')}}) ⊗ᴸ_{𝒪_{S, f(g' x')}} 𝒪_{S', f' x'}`,

the left-hand side read over `𝒪_{S', f' x'}` along `ch.toStalkR' ∘ ch.b`.

This is `RingTheory.TorIndependence.localizedSquareDomainIsoOfEq` supplied with the chart's
localization `AlgebraicGeometry.BaseChangeChart.isLocalization_toStalkR` and the two
compatibilities `AlgebraicGeometry.BaseChangeChart.toStalkA_a`,
`AlgebraicGeometry.BaseChangeChart.toStalkR'_b`. -/
public def localRingsSourceIso :
    letI := (ch.toStalkR y).toAlgebra
    letI := (ch.toStalkA y).toAlgebra
    (ModuleCat.restrictScalars.{u} (ch.toStalkA y)).mapDerivedCategory ⋙
        ((ModuleCat.restrictScalars.{u} ch.a.hom).mapDerivedCategory ⋙
          (totalDerivedExtensionScalars.{u, u, u}
            ((ch.toStalkR' y).comp ch.b.hom)).functor) ≅
      (ModuleCat.restrictScalars.{u} (f.stalkMap (g' (ch.incU' y))).hom).mapDerivedCategory ⋙
        (totalDerivedExtensionScalars.{u, u, u}
          (baseStalkMap f g f' g' w (ch.incU' y))).functor :=
  letI := (ch.toStalkR y).toAlgebra
  letI := (ch.toStalkA y).toAlgebra
  haveI := ch.isLocalization_toStalkR y
  RingTheory.TorIndependence.localizedSquareDomainIsoOfEq.{u} (ch.primeComplR y) ch.a.hom
    (f.stalkMap (g' (ch.incU' y))).hom (baseStalkMap f g f' g' w (ch.incU' y))
    (ch.toStalkA_a y) (ch.toStalkR'_b y w)

/-- **The source identification of the cube at a chart is equivariant for `𝒪_{X, g' x'}`.** On
cohomology it carries scalar multiplication by `x : 𝒪_{X, g' x'}` on the complex to the action of
the left tensor factor of `𝒪_{X, g' x'} ⊗_{𝒪_{S, f(g' x')}} 𝒪_{S', f' x'}`.

This is `RingTheory.TorIndependence.localizedSquareDomainIsoOfEq_homology_smul` at the chart's
rings. -/
public theorem localRingsSourceIso_homology_smul (n : ℤ)
    (P : DerivedCategory (ModuleCat.{u} (X.presheaf.stalk (g' (ch.incU' y)))))
    (x : ToType (X.presheaf.stalk (g' (ch.incU' y)))) :
    letI := (ch.toStalkR y).toAlgebra
    letI := (ch.toStalkA y).toAlgebra
    letI := ch.a.hom.toAlgebra
    letI := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
    letI := (f.stalkMap (g' (ch.incU' y))).hom.toAlgebra
    letI := (baseStalkMap f g f' g' w (ch.incU' y)).toAlgebra
    ∀ m : RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        ((ModuleCat.restrictScalars.{u} (ch.toStalkA y)).mapDerivedCategory.obj P) n,
      ((DerivedCategory.homologyFunctor
              (ModuleCat.{u} (S'.presheaf.stalk (f' (ch.incU' y)))) n).map
            ((ch.localRingsSourceIso y w).hom.app P)).hom
          (((((ModuleCat.restrictScalars.{u} (ch.toStalkA y)).mapDerivedCategory ⋙
                  ((ModuleCat.restrictScalars.{u} ch.a.hom).mapDerivedCategory ⋙
                    (totalDerivedExtensionScalars.{u, u, u}
                      ((ch.toStalkR' y).comp ch.b.hom)).functor)) ⋙
                DerivedCategory.homologyFunctor
                  (ModuleCat.{u} (S'.presheaf.stalk (f' (ch.incU' y)))) n).map
              (x • 𝟙 P)).hom m) =
        (Algebra.TensorProduct.includeLeft
              (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
              (S := ToType (S.presheaf.stalk (f (g' (ch.incU' y))))) x :
            ToType (X.presheaf.stalk (g' (ch.incU' y)))
              ⊗[ToType (S.presheaf.stalk (f (g' (ch.incU' y))))]
              ToType (S'.presheaf.stalk (f' (ch.incU' y)))) •
          (show RingTheory.TorIndependence.baseChangeCohomology
              (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
              (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) P n from
            ((DerivedCategory.homologyFunctor
                  (ModuleCat.{u} (S'.presheaf.stalk (f' (ch.incU' y)))) n).map
                ((ch.localRingsSourceIso y w).hom.app P)).hom m) := by
  let := (ch.toStalkR y).toAlgebra
  let := (ch.toStalkA y).toAlgebra
  have := ch.isLocalization_toStalkR y
  exact RingTheory.TorIndependence.localizedSquareDomainIsoOfEq_homology_smul.{u}
    (ch.primeComplR y) ch.a.hom (f.stalkMap (g' (ch.incU' y))).hom
    (baseStalkMap f g f' g' w (ch.incU' y)) (ch.toStalkA_a y) (ch.toStalkR'_b y w) n P x

/-- **The source identification of the cube at a chart is equivariant for `𝒪_{S', f' x'}`.** On
cohomology it carries the action of the right tensor factor of
`𝒪_X(U) ⊗_{𝒪_S(V)} 𝒪_{S', f' x'}` to that of the right tensor factor of
`𝒪_{X, g' x'} ⊗_{𝒪_{S, f(g' x')}} 𝒪_{S', f' x'}`.

This is `RingTheory.TorIndependence.localizedSquareDomainIsoOfEq_homology_includeRight_smul` at
the chart's rings. -/
public theorem localRingsSourceIso_homology_includeRight_smul (n : ℤ)
    (P : DerivedCategory (ModuleCat.{u} (X.presheaf.stalk (g' (ch.incU' y)))))
    (r : ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :
    letI := (ch.toStalkR y).toAlgebra
    letI := (ch.toStalkA y).toAlgebra
    letI := ch.a.hom.toAlgebra
    letI := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
    letI := (f.stalkMap (g' (ch.incU' y))).hom.toAlgebra
    letI := (baseStalkMap f g f' g' w (ch.incU' y)).toAlgebra
    ∀ m : RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        ((ModuleCat.restrictScalars.{u} (ch.toStalkA y)).mapDerivedCategory.obj P) n,
      ((DerivedCategory.homologyFunctor
              (ModuleCat.{u} (S'.presheaf.stalk (f' (ch.incU' y)))) n).map
            ((ch.localRingsSourceIso y w).hom.app P)).hom
          ((Algebra.TensorProduct.includeRight r :
            ch.A ⊗[ch.R] ToType (S'.presheaf.stalk (f' (ch.incU' y)))) • m) =
        (Algebra.TensorProduct.includeRight r :
            ToType (X.presheaf.stalk (g' (ch.incU' y)))
              ⊗[ToType (S.presheaf.stalk (f (g' (ch.incU' y))))]
              ToType (S'.presheaf.stalk (f' (ch.incU' y)))) •
          (show RingTheory.TorIndependence.baseChangeCohomology
              (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
              (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) P n from
            ((DerivedCategory.homologyFunctor
                  (ModuleCat.{u} (S'.presheaf.stalk (f' (ch.incU' y)))) n).map
                ((ch.localRingsSourceIso y w).hom.app P)).hom m) := by
  let := (ch.toStalkR y).toAlgebra
  let := (ch.toStalkA y).toAlgebra
  have := ch.isLocalization_toStalkR y
  exact RingTheory.TorIndependence.localizedSquareDomainIsoOfEq_homology_includeRight_smul.{u}
    (ch.primeComplR y) ch.a.hom (f.stalkMap (g' (ch.incU' y))).hom
    (baseStalkMap f g f' g' w (ch.incU' y)) (ch.toStalkA_a y) (ch.toStalkR'_b y w) n P r

end BaseChangeChart

end AlgebraicGeometry

end
