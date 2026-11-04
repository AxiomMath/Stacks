module

public import StacksFrontier.AlgebraicGeometry.SectionProduct.MonoidalUnitBridge
public import StacksFrontier.AlgebraicGeometry.AssociatedPointsMono.Basic

/-!
# Multiplication by a section nonvanishing near the associated points is a monomorphism

Let `X` be a locally Noetherian scheme, `F` and `L` quasi-coherent `𝒪_X`-modules and
`f : 𝟙_ X.Modules ⟶ L` a global section of `L`. Then

`Stacks.TensorSectionNonvanishing.mulRight F f : F ⟶ F ⊗ L`

is a monomorphism as soon as `f` does not vanish near any associated point of `F`.

## Main results

* `Stacks.SectionProduct.mono_mulRight_of_associatedPoints`: multiplication by a section
  nonvanishing near every associated point of `F` is a monomorphism.
* `Stacks.SectionProduct.mono_mulRight_comp_of_associatedPoints`: the same after composing with
  an isomorphism `F ⊗ L ≅ G`.

## References

* [Stacks Project, Tag 08A0](https://stacks.math.columbia.edu/tag/08A0)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0AVL](https://stacks.math.columbia.edu/tag/0AVL)
-/

@[expose] public noncomputable section

open CategoryTheory Category AlgebraicGeometry Opposite MonoidalCategory
  Stacks.SheafOfModules.TensorSheafification
open TopologicalSpace

universe u

namespace Stacks.SectionProduct

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

open Stacks.TensorSectionNonvanishing
open Stacks.AlgebraicGeometry.AssociatedPointsMono

/-- **Multiplication by a global section nonvanishing near every associated point of `F` is a
monomorphism.** The nonvanishing hypothesis gives, for each associated point, an open
neighbourhood inside the nonvanishing locus of the global section of `L` that `f` carries; `ψ` is
a pairing trivialising `L`. -/
theorem mono_mulRight_of_associatedPoints {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) {L N : X.Modules}
    [F.IsQuasicoherent] [(F ⊗ L).IsQuasicoherent]
    (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (L)).obj (N)) ≅
      _root_.SheafOfModules.unit _)
    (f : 𝟙_ X.Modules ⟶ L)
    (hW : ∀ x ∈ associatedPoints F, ∃ W : X.Opens, x ∈ W ∧ ∀ y ∈ W,
      y ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) L
        (monoidalUnitHomEquiv L f)) :
    Mono (mulRight F f) := by
  refine mono_of_stalk_injective_on_associatedPoints (mulRight F f) fun x ↦ ?_
  by_cases hx : x ∈ associatedPoints F
  · obtain ⟨W, hxW, hWloc⟩ := hW x hx
    exact Or.inl (bijective_mapFun_mulRight_of_le_nonvanishingLocus F L N ψ f hxW hWloc).1
  · exact Or.inr hx

/-- Multiplication by a global section nonvanishing near every associated point of `F`, followed
by an isomorphism `e : F ⊗ L ≅ G`, is a monomorphism. -/
theorem mono_mulRight_comp_of_associatedPoints {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) {L N G : X.Modules}
    [F.IsQuasicoherent] [(F ⊗ L).IsQuasicoherent]
    (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (L)).obj (N)) ≅
      _root_.SheafOfModules.unit _)
    (f : 𝟙_ X.Modules ⟶ L) (e : (F ⊗ L) ≅ G)
    (hW : ∀ x ∈ associatedPoints F, ∃ W : X.Opens, x ∈ W ∧ ∀ y ∈ W,
      y ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) L
        (monoidalUnitHomEquiv L f)) :
    Mono (mulRight F f ≫ e.hom) :=
  have : Mono (mulRight F f) := mono_mulRight_of_associatedPoints F ψ f hW
  mono_comp _ _

end Stacks.SectionProduct

end
