module

public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentSquareZeroBaseChange
public import StacksFrontier.Deformation.ToposThickening.ExtensionPresentationRemark

/-!
# The class of a square-zero extension of ringed topoi through canonical complexes

Let `f : (Sh(𝒞), 𝒪) ⟶ (Sh(ℬ), 𝒪_ℬ)` be a morphism of ringed topoi, `𝒢` an `𝒪`-module and
`0 ⟶ 𝒢 ⟶ 𝒪' ⟶ 𝒪 ⟶ 0` an extension of `A = f⁻¹𝒪_ℬ`-algebras with `𝒢` an ideal of square zero.
**Stacks 0GQ5** attaches to it a class `ξ ∈ Ext¹_𝒪(NL_{𝒪/A}, 𝒢)`, and **Stacks 0GQ6** computes
`ξ` through any presentation `(ℰ, α, α')`. This file expresses `ξ` through *canonical* naive
cotangent complexes only:

`ξ = [NL_{𝒪/A} ⟶ NL_{𝒪/𝒪'} ≅ (Ker(𝒪' ⟶ 𝒪)/Ker²)[1] ⟶ 𝒢[1]]`,

the base change of **Stacks 08TX** along the structure map `A ⟶ 𝒪'`, the inverse of the
canonical isomorphism `η` of `Stacks.SheafOfModules.conormalToNaiveCotangentComplex` (the naive
cotangent complex of the surjection `𝒪' ⟶ 𝒪` is its conormal sheaf placed in degree `-1`),
and the identification of the conormal sheaf of the square-zero ideal with `𝒢`.

This is the form in which the class is compatible with change of rings and with inverse images:
every map in it is a functorial map of canonical naive cotangent complexes. It is what the proof
of **Stacks 0GQ7** uses.

## Main definitions

* `...CompatibleFirstOrderThickening.naiveCotangentBaseChange`: `NL_{𝒪/A} ⟶ NL_{𝒪/𝒪'}`.
* `...CompatibleFirstOrderThickening.kernelConormalToModule`: `Ker/Ker² ⟶ 𝒢`.

## Main results

* `...squareZeroExtensionClassesEquiv_mk_eq_canonical`: the formula.

## Implementation notes

The proof starts from **Stacks 0GQ6** at the presentation `ℰ = 𝒪'`, `α' = 𝟙`, whose class is
the conormal class of `𝒥/𝒥² ⟶ 𝒢`, and compares the two maps of presentations `A[𝒪'] ⟶ 𝒪'[𝒪]`
given by `[x] ↦ [x mod 𝒢]` (the comparison followed by the base change) and by
`[x] ↦ x` (the map `A[𝒪'] ⟶ 𝒪'` followed by the constants, which is `η` after the conormal
class); they are homotopic by **Stacks 00S1 (2)**.

## References

* [Stacks Project, Tag 0GQ5](https://stacks.math.columbia.edu/tag/0GQ5)
* [Stacks Project, Tag 0GQ6](https://stacks.math.columbia.edu/tag/0GQ6)
* [Stacks Project, Tag 08TX](https://stacks.math.columbia.edu/tag/08TX)
* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)
open Stacks.Sites.Conormal (conormalSheaf conormalDesc conormalSheafMapOfSquare conormalClass
  kernelIdeal conormalSequence)
open Stacks.Sites.FreeAlgebra (underlyingPresheaf freeAlgebraSheaf freeAlgebraSheafDesc
  freeAlgebraSheafCoefficientMap canonicalPresentation)
open Stacks.SheafOfModules

universe t u v' u' w'

attribute [local instance 5000] _root_.SheafOfModules.instAbelian

namespace Deformation.ToposThickening.RingedToposExtensionProblem.CompatibleFirstOrderThickening

variable {X : RingedTopos.{u, u, u}} {B : RingedTopos.{v', u', w'}}
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  {f : RingedToposHom X B}
  {G : SheafOfModules.{u} ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj X.O)}
  (Q : (ofTrivialBase f G).CompatibleFirstOrderThickening)

/-- The reduction `𝒪' ⟶ 𝒪` of a first-order thickening is locally surjective. -/
instance isLocallySurjective_reduction : Presheaf.IsLocallySurjective X.J Q.reduction.hom :=
  Q.locallySurjective

/-- The base change `NL_{𝒪/A} ⟶ NL_{𝒪/𝒪'}` of **Stacks 08TX** along the structure map
`A = f⁻¹𝒪_ℬ ⟶ 𝒪'` of the extension. -/
noncomputable abbrev naiveCotangentBaseChange :
    Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} X.J
        ((inverseImageCommRingFunctor f.toToposHom).obj B.O) X.O f.fSharpInverseImage ⟶
      Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} X.J Q.extension X.O Q.reduction :=
  naiveCotangentComplexMapOfBase.{u, u, u, u} X.J _ X.O f.fSharpInverseImage Q.extension
    Q.reduction Q.baseMap (baseMap_comp_reduction_ofTrivialBase Q).symm

/-- The identification `Ker/Ker² ⟶ 𝒢` of the conormal sheaf of the reduction `𝒪' ⟶ 𝒪` with the
module `𝒢`, read through the kernel identification of the extension. -/
noncomputable abbrev kernelConormalToModule :
    conormalSheaf.{u, u, u, u} X.J Q.extension X.O Q.reduction ⟶ (ofTrivialBase f G).G :=
  conormalDesc.{u, u, u, u} Q.reduction (ofTrivialBase f G).G Q.kernelIdentification

/-! ### A presentation `(ℰ, α, α')` of the source -/

section Presentation

variable (E : Functor X.Cᵒᵖ (Type u)) (α : E ⟶ underlyingPresheaf X.J X.O)
  (α' : E ⟶ underlyingPresheaf X.J Q.extension)
  (hα : α' ≫ Functor.whiskerRight Q.reduction.hom (forget CommRingCat.{u}) = α)
  [Presheaf.IsLocallySurjective X.J (Stacks.SheafOfModules.presentation X.J
    ((inverseImageCommRingFunctor f.toToposHom).obj B.O) X.O f.fSharpInverseImage E α).hom]

/-- The map `𝒥/𝒥² ⟶ 𝒢` of **Stacks 0GQ6** factors through `Ker/Ker²`: it is the map of
conormal sheaves induced by `A[ℰ] ⟶ 𝒪'`, followed by the identification `Ker/Ker² ⟶ 𝒢`. -/
theorem generatorsConormalToIdeal_eq_liftConormalMap_comp :
    Q.generatorsConormalToIdeal (A := (inverseImageCommRingFunctor f.toToposHom).obj B.O)
        (a := f.fSharpInverseImage) (base := Q.baseMap) hα
        (baseMap_comp_reduction_ofTrivialBase Q) =
      liftConormalMap X.J f.fSharpInverseImage Q.reduction Q.baseMap
          (baseMap_comp_reduction_ofTrivialBase Q) α α' hα ≫ Q.kernelConormalToModule := by
  refine Stacks.Sites.Conormal.conormal_hom_ext _ _ (fun U x ↦ ?_)
  have e₁ := liftConormalMap_conormalClass X.J f.fSharpInverseImage Q.reduction Q.baseMap
    (baseMap_comp_reduction_ofTrivialBase Q) α α' hα U x
  have e₂ := Stacks.Sites.Conormal.conormalDesc_toAssociatedModule Q.reduction
    (ofTrivialBase f G).G Q.kernelIdentification U
    ⟨((Q.generatorsLift E α' Q.baseMap).hom.app U) x.1,
      Q.generatorsLift_mem_kernelIdeal hα (baseMap_comp_reduction_ofTrivialBase Q) U x⟩
  refine (Stacks.Sites.Conormal.conormalDesc_toAssociatedModule _ _ _ U x).trans
    (Eq.trans ?_ ((congrArg (fun t ↦ (Q.kernelConormalToModule).val.app U t) e₁).trans e₂).symm)
  rfl

end Presentation

/-- **The class of a square-zero extension through canonical complexes.** The element of
`Ext¹_𝒪(NL_{𝒪/A}, 𝒢)` attached to `𝒪'` by **Stacks 0GQ5** is the base change
`NL_{𝒪/A} ⟶ NL_{𝒪/𝒪'}` of **Stacks 08TX**, followed by the inverse of the isomorphism
`η : (Ker/Ker²)[1] ≅ NL_{𝒪/𝒪'}` and the identification `Ker/Ker² ⟶ 𝒢`, shifted. -/
theorem squareZeroExtensionClassesEquiv_mk_eq_canonical
    [HasDerivedCategory.{t} (Sheaf.targetModules.{u, u, u} X.J X.O)] :
    squareZeroExtensionClassesEquiv f G
        (Quotient.mk (CompatibleFirstOrderThickening.isomorphicSetoid _) Q) =
      DerivedCategory.Q.map Q.naiveCotangentBaseChange ≫
        inv (DerivedCategory.Q.map
          (conormalToNaiveCotangentComplex X.J Q.extension X.O Q.reduction)) ≫
        DerivedCategory.Q.map ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (-1)).map
          Q.kernelConormalToModule) ≫
        ((DerivedCategory.singleFunctors
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).shiftIso
          (1 : ℤ) (-1) 0 (by decide)).inv.app G := by
  have : Presheaf.IsLocallySurjective X.J (Stacks.SheafOfModules.presentation X.J
      ((inverseImageCommRingFunctor f.toToposHom).obj B.O) X.O f.fSharpInverseImage
      Q.generators Q.generatorsMap).hom :=
    Q.presentation_isLocallySurjective
  rw [← squareZeroExtensionClassesEquiv_mk_eq_generators Q Q.generators Q.generatorsMap (𝟙 _)
    (Category.id_comp _), generatorsConormalToIdeal_eq_liftConormalMap_comp]
  have h := presentationConormalExtClass_liftConormalMap_comp_eq_canonical.{t} X.J
    f.fSharpInverseImage Q.reduction Q.baseMap (baseMap_comp_reduction_ofTrivialBase Q)
    Q.generatorsMap (𝟙 _) (Category.id_comp _) (G := G) Q.kernelConormalToModule
  exact (congrArg (inv (DerivedCategory.Q.map
    (Stacks.SheafOfModules.naiveCotangentComplexComparison.{u, u, u, u} X.J
      ((inverseImageCommRingFunctor f.toToposHom).obj B.O) X.O f.fSharpInverseImage
      Q.generators Q.generatorsMap)) ≫ ·) h).trans (IsIso.inv_hom_id_assoc _ _)

end Deformation.ToposThickening.RingedToposExtensionProblem.CompatibleFirstOrderThickening

end
