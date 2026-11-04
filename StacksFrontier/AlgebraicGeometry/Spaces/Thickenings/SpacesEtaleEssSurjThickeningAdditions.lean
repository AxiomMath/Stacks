module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurjThickening
import all StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurjThickening
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceSize
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.CartesianFiniteOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FormallyEtaleOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurj
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleFullyFaithfulThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleRangeEquivalence
import all StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurj

/-!
# Base change along a thickening on the spaces-étale sites

Morphisms over `Y` into a formally étale algebraic space extend uniquely across a thickening of
finite order, at the level of presheaves, and base change along a thickening of algebraic spaces
is an equivalence of spaces-étale sites (Stacks 05ZH).

## Main definitions

* `AlgebraicGeometry.Space.fullyFaithfulSpacesBaseChangeOfIsThickeningHom`: base change along a
  thickening of algebraic spaces is fully faithful.

## Main results

* `AlgebraicGeometry.Space.existsUnique_hom_presheaf_of_isNthOrderThickening`: a morphism into a
  formally étale algebraic space extends uniquely across a base change of an `n`th-order
  thickening.
* `AlgebraicGeometry.Space.hom_ext_presheaf_of_isNthOrderThickening`: two such morphisms agreeing
  on the thickening are equal.
* `AlgebraicGeometry.Space.isEquivalence_spacesBaseChange_of_isThickeningHom`: base change along a
  thickening of algebraic spaces is an equivalence of spaces-étale sites.
* `AlgebraicGeometry.Space.isEquivalence_spacesBaseChange_of_isNthOrderThickening`: the same for
  the inclusion of an `n`th-order thickening.

## References

* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Groupoids
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Unique extension of morphisms into a formally étale algebraic space, at the level of
presheaves.** Let `f : X ⟶ Y` be a monomorphism whose range is an `n`th-order thickening of `Y`,
let `π : H ⟶ F` be a base change of `f` along a morphism `v : F ⟶ Y.1` with `F` an algebraic
space, and let `w : G ⟶ Y.1` be formally étale with `G` an algebraic space. Every morphism
`H ⟶ G` over `Y` extends uniquely to a morphism `F ⟶ G` over `Y`. -/
theorem existsUnique_hom_presheaf_of_isNthOrderThickening {n : ℕ}
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) [Mono f.hom]
    (hT : IsNthOrderThickening B S hS n Y (Subfunctor.range f.hom))
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    {v : F ⟶ Y.1} {π : H ⟶ F} {q : H ⟶ X.1} (hpb : IsPullback π q v f.hom)
    (w : G ⟶ Y.1) (hw : FormallyEtale w)
    (d : H ⟶ G) (hd : d ≫ w = π ≫ v) :
    ∃! α : F ⟶ G, π ≫ α = d ∧ α ≫ w = v := by
  have hinv : inv (Subfunctor.toRange f.hom) ≫ f.hom = (Subfunctor.range f.hom).ι :=
    (cancel_epi (Subfunctor.toRange f.hom)).1 (by
      rw [IsIso.hom_inv_id_assoc]
      exact (Subfunctor.toRange_ι f.hom).symm)
  have hiso : IsPullback (inv (Subfunctor.toRange f.hom)) (Subfunctor.range f.hom).ι f.hom
      (𝟙 Y.1) :=
    IsPullback.of_horiz_isIso ⟨by rwa [Category.comp_id]⟩
  have hpaste := (Subfunctor.isPullback_preimage v (Subfunctor.range f.hom)).paste_horiz hiso
  rw [Category.comp_id] at hpaste
  obtain ⟨θ, hθiso, hθ⟩ :
      ∃ θ : H ⟶ ((Subfunctor.range f.hom).preimage v).toFunctor,
        IsIso θ ∧ θ ≫ ((Subfunctor.range f.hom).preimage v).ι = π :=
    ⟨(hpb.isoIsPullback _ _ hpaste.flip).hom, inferInstance,
      IsPullback.isoIsPullback_hom_fst _ _ hpb hpaste.flip⟩
  have hGp : IsNthOrderThickening B S hS n (⟨F, hF⟩ : AlgebraicSpaces B S hS)
      ((Subfunctor.range f.hom).preimage v) :=
    isNthOrderThickening_preimage B S hS (Subfunctor.range f.hom)
      (ObjectProperty.homMk v : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ Y) hT
  have hsq : (inv θ ≫ d) ≫ w = ((Subfunctor.range f.hom).preimage v).ι ≫ v := by
    rw [Category.assoc, hd, ← hθ]
    simp
  obtain ⟨α, ⟨ha1, ha2⟩, hauniq⟩ :=
    FormallyEtale.existsUnique_lift_of_isNthOrderThickening B S hS
      (T' := (⟨F, hF⟩ : AlgebraicSpaces B S hS))
      (ObjectProperty.homMk w : (⟨G, hG⟩ : AlgebraicSpaces B S hS) ⟶ Y) hw
      ((Subfunctor.range f.hom).preimage v) hGp (inv θ ≫ d) v hsq
  refine ⟨α, ⟨?_, ha2⟩, fun β ⟨hb1, hb2⟩ ↦ hauniq β ⟨?_, hb2⟩⟩
  · rw [← hθ, Category.assoc, ha1, IsIso.hom_inv_id_assoc]
  · rw [← hb1, ← hθ]
    simp

/-- **Two morphisms over `Y` into a formally étale algebraic space agreeing on a thickening are
equal.** -/
theorem hom_ext_presheaf_of_isNthOrderThickening {n : ℕ}
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) [Mono f.hom]
    (hT : IsNthOrderThickening B S hS n Y (Subfunctor.range f.hom))
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    {v : F ⟶ Y.1} {π : H ⟶ F} {q : H ⟶ X.1} (hpb : IsPullback π q v f.hom)
    (w : G ⟶ Y.1) (hw : FormallyEtale w) (α β : F ⟶ G)
    (hα : α ≫ w = v) (hβ : β ≫ w = v) (h : π ≫ α = π ≫ β) : α = β := by
  obtain ⟨α₀, -, huniq⟩ := existsUnique_hom_presheaf_of_isNthOrderThickening B S hS f hT hF hG
    hpb w hw (π ≫ α) (by rw [Category.assoc, hα])
  rw [huniq α ⟨rfl, hα⟩, huniq β ⟨h.symm, hβ⟩]

variable {X Y : AlgebraicSpaces B S hS}

namespace LiftedEtalePresentation

variable {B S hS}
variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} {C : SpacesEtale B S hS X}
  (P : LiftedEtalePresentation B S hS f C)

end LiftedEtalePresentation

variable {f : X ⟶ Y} {C : SpacesEtale B S hS X}

/-- **Stacks 05ZH for a thickening of algebraic spaces, in the morphism form.** Base change
`V ↦ X ×_Y V` is an equivalence from the spaces-étale site of `Y` to that of `X` for every
morphism `f : X ⟶ Y` which is a thickening in the sense of
`AlgebraicGeometry.Space.IsThickeningHom`, Stacks 05ZK part (1): an isomorphism onto its range,
whose range is a closed subspace of `Y` with the same points. No order is assumed. -/
theorem isEquivalence_spacesBaseChange_of_isThickeningHom (f : X ⟶ Y)
    (hT : IsThickeningHom B S hS f) :
    (spacesBaseChange B S hS f).functor.IsEquivalence :=
  let := hT.mono
  isEquivalence_spacesBaseChange_of_isThickening_range B S hS f hT.2

/-- **Stacks 05ZH, full faithfulness for a thickening of algebraic spaces, in the morphism
form.** The full-faithfulness half of
`AlgebraicGeometry.Space.isEquivalence_spacesBaseChange_of_isThickeningHom`. -/
noncomputable def fullyFaithfulSpacesBaseChangeOfIsThickeningHom (f : X ⟶ Y)
    (hT : IsThickeningHom B S hS f) :
    (spacesBaseChange B S hS f).functor.FullyFaithful :=
  letI := hT.mono
  fullyFaithfulSpacesBaseChangeOfMonoOfIsThickening B S hS f hT.2

/-- **Stacks 05ZH for the inclusion of a thickening of finite order.** Base change
`V ↦ X ×_Y V` is an equivalence from the spaces-étale site of `Y` to that of `X`, for the
inclusion `f` of an `n`th-order thickening, for every `n`. -/
theorem isEquivalence_spacesBaseChange_of_isNthOrderThickening {n : ℕ} (f : X ⟶ Y) [Mono f.hom]
    (hT : IsNthOrderThickening B S hS n Y (Subfunctor.range f.hom)) :
    (spacesBaseChange B S hS f).functor.IsEquivalence :=
  isEquivalence_spacesBaseChange_of_isThickening_range B S hS f hT.1

end AlgebraicGeometry.Space

end

