module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TorIndependentBaseChange
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.StructureSheafAsADerivedUnit
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.TensorPseudoCoherentPushforward
public import StacksFrontier.AlgebraicGeometry.Perfect.TorIndependence
import StacksCore.Tactic.StacksAttribute

/-!
# Pseudo-coherence of the derived pushforward along a flat proper morphism

Let `f : X ⟶ S` be a flat proper morphism of finite presentation and `E ∈ D(𝒪_X)`
pseudo-coherent. Then `Rf_*E` is a pseudo-coherent object of `D(𝒪_S)` and its formation commutes
with arbitrary base change.

## Main results

* `AlgebraicGeometry.isPseudoCoherent_derivedPushforward_of_flat_of_isProper`: the
  pseudo-coherence half of [Stacks, Tag 0CSD].
* `AlgebraicGeometry.isPseudoCoherent_derivedPushforward_and_isIso_derivedBaseChangeMap`:
  [Stacks, Tag 0CSD].

## References

* [Stacks Project, Tag 0CSD](https://stacks.math.columbia.edu/tag/0CSD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedBaseChange (derivedBaseChangeMap)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open AlgebraicGeometry.ProperFlatBaseChange (singleDegreeComplex)

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The unit constraint `E ⊗^L_{𝒪_X} 𝒪_X ≅ E`** of [Stacks, Tag 0FPT], with `𝒪_X` the complex
`𝒪_X` in degree zero. -/
private def derivedTensorStructureComplexIso (E : DerivedCategory X.Modules) :
    ((derivedTensorProductFunctor X.sheaf).obj E).obj (DerivedCategory.Q.obj
      (singleDegreeComplex (StrictlyPerfect.structureModule X.toRingedSpace : X.Modules))) ≅ E :=
  ((derivedTensorProductFunctor X.sheaf).obj E).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app
        (StrictlyPerfect.structureModule X.toRingedSpace : X.Modules)).symm ≪≫
    Stacks.RingedSpace.derivedTensorRightUnitIso X.toRingedSpace E

/-- **The pseudo-coherence half of [Stacks, Tag 0CSD].** If `f : X ⟶ S` is flat, proper and of
finite presentation and `E ∈ D(𝒪_X)` is pseudo-coherent, then `Rf_*E` is pseudo-coherent: this is
[Stacks, Tag 0CSC] at `𝒢^• = 𝒪_X` in degree zero, followed by the unit constraint. -/
theorem isPseudoCoherent_derivedPushforward_of_flat_of_isProper [Flat f] [IsProper f]
    [LocallyOfFinitePresentation f]
    (E : DerivedCategory X.Modules) (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E) :
    RingedSpace.IsPseudoCoherent (X := S.toRingedSpace)
      ((derivedPushforward f.toLRSHom.toShHom).obj E) :=
  have hG := ProperFlatBaseChange.flatProperSupportFinitelyPresented_structure f
  RingedSpace.IsPseudoCoherent.of_iso (X := S.toRingedSpace)
    (isPseudoCoherent_derivedPushforward_tensor f
      ⟨inferInstance, inferInstance, inferInstance⟩ E hE _
      (hG.bounded.elim fun _ h => h.elim fun b hb => ⟨b, hb.2⟩)
      hG.isFinitePresentation hG.isFlatOver hG.properSupport)
    ((derivedPushforward f.toLRSHom.toShHom).mapIso (derivedTensorStructureComplexIso E))

/-- **[Stacks, Tag 0CSD].** Let `f : X ⟶ S` be a flat proper morphism of schemes of finite
presentation and let `E ∈ D(𝒪_X)` be pseudo-coherent. Then `Rf_*E` is a pseudo-coherent object of
`D(𝒪_S)` and its formation commutes with arbitrary base change: for every cartesian square
`X' = X ×_S S'` the base change map `Lg^*Rf_*E ⟶ Rf'_*L(g')^*E` of [Stacks, Tag 08HY] is an
isomorphism. -/
@[stacks 0CSD]
theorem isPseudoCoherent_derivedPushforward_and_isIso_derivedBaseChangeMap [Flat f] [IsProper f]
    [LocallyOfFinitePresentation f]
    (E : DerivedCategory X.Modules) (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E) :
    RingedSpace.IsPseudoCoherent (X := S.toRingedSpace)
        ((derivedPushforward f.toLRSHom.toShHom).obj E) ∧
      ∀ {X' S' : Scheme.{u}} (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
        (sq : IsPullback g' f' f g),
        IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
          g.toLRSHom.toShHom (comp_toShHom_of_comm sq.w) E) :=
  ⟨isPseudoCoherent_derivedPushforward_of_flat_of_isProper f E hE,
    fun g _ _ sq => isIso_derivedBaseChangeMap_of_torIndependent sq
      (torIndependent_of_flat_left f g) E (isQuasicoherentDerived_of_isPseudoCoherent X E hE)⟩

end AlgebraicGeometry

end
