module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleSection

/-!
# Lifting morphisms into an étale algebraic space across a thickening

Let `f : X ⟶ Y` be a monomorphism of algebraic spaces over a scheme `S` whose range is a
thickening of `Y`, let `π : H ⟶ F` be a base change of `f`, and let `w : G ⟶ Y` be étale. Every
morphism `H ⟶ G` over `Y` extends uniquely to a morphism `F ⟶ G` over `Y`.

## Main results

* `AlgebraicGeometry.Space.existsUnique_hom_presheaf_of_isThickening`: the unique extension.
* `AlgebraicGeometry.Space.hom_ext_presheaf_of_isThickening_range`: its uniqueness half, as an
  extensionality statement for two morphisms over `Y` agreeing on the thickening.

## References

* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_EtaleHomLift :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_EtaleHomLift
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- Let `f` be a monomorphism and let `π : H ⟶ F` be a base change of it along `v : F ⟶ Y`. Then
`H` is isomorphic over `F` to the inverse image along `v` of the range of `f`. -/
theorem exists_isIso_comp_preimage_ι {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) [Mono f.hom]
    {F H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {v : F ⟶ Y.1} {π : H ⟶ F} {q : H ⟶ X.1}
    (hpb : IsPullback π q v f.hom) :
    ∃ θ : H ⟶ ((Subfunctor.range f.hom).preimage v).toFunctor,
      IsIso θ ∧ θ ≫ ((Subfunctor.range f.hom).preimage v).ι = π := by
  have hinv : inv (Subfunctor.toRange f.hom) ≫ f.hom = (Subfunctor.range f.hom).ι :=
    (cancel_epi (Subfunctor.toRange f.hom)).1 (by
      rw [IsIso.hom_inv_id_assoc, Subfunctor.toRange_ι])
  have hiso : IsPullback (inv (Subfunctor.toRange f.hom)) (Subfunctor.range f.hom).ι f.hom
      (𝟙 Y.1) :=
    IsPullback.of_horiz_isIso ⟨by rwa [Category.comp_id]⟩
  have hpaste := (Subfunctor.isPullback_preimage v (Subfunctor.range f.hom)).paste_horiz hiso
  rw [Category.comp_id] at hpaste
  exact ⟨(hpb.isoIsPullback _ _ hpaste.flip).hom, inferInstance,
    IsPullback.isoIsPullback_hom_fst _ _ hpb hpaste.flip⟩

/-- Let `f : X ⟶ Y` be a monomorphism whose range is a thickening of `Y`, let `π : H ⟶ F` be a
base change of `f` along `v : F ⟶ Y` with `F` an algebraic space, and let `w : G ⟶ Y` be étale
with `G` an algebraic space. Every morphism `H ⟶ G` over `Y` extends uniquely to a morphism
`F ⟶ G` over `Y`. -/
@[sga "1 I 5.6" "more general"]
theorem existsUnique_hom_presheaf_of_isThickening
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) [Mono f.hom]
    (hT : IsThickening B S hS Y (Subfunctor.range f.hom))
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    {v : F ⟶ Y.1} {π : H ⟶ F} {q : H ⟶ X.1} (hpb : IsPullback π q v f.hom)
    (w : G ⟶ Y.1) (hw : IsEtale B S hS w)
    (d : H ⟶ G) (hd : d ≫ w = π ≫ v) :
    ∃! α : F ⟶ G, π ≫ α = d ∧ α ≫ w = v := by
  obtain ⟨θ, _, hθ⟩ := exists_isIso_comp_preimage_ι B S hS f hpb
  have hK : IsThickening B S hS (⟨F, hF⟩ : AlgebraicSpaces B S hS)
      ((Subfunctor.range f.hom).preimage v) :=
    isThickening_preimage B S hS (Subfunctor.range f.hom)
      (ObjectProperty.homMk v : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ Y) hT
  have hP : IsAlgebraicSpace B S hS (pullback v w) :=
    isAlgebraicSpace_pullback B S hS v w hF hG Y.property
  have hPpb : IsPullback (pullback.fst v w) (pullback.snd v w) v w :=
    IsPullback.of_hasPullback v w
  have hp₁E : IsEtale B S hS (pullback.fst v w) := by
    have hsq : IsPullback
        (ObjectProperty.homMk (pullback.snd v w) :
          (⟨pullback v w, hP⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩)
        (ObjectProperty.homMk (pullback.fst v w) :
          (⟨pullback v w, hP⟩ : AlgebraicSpaces B S hS) ⟶ ⟨F, hF⟩)
        (ObjectProperty.homMk w : (⟨G, hG⟩ : AlgebraicSpaces B S hS) ⟶ Y)
        (ObjectProperty.homMk v : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ Y) :=
      IsPullback.of_map_of_faithful (ObjectProperty.ι _) hPpb.flip
    exact isEtale_of_isPullback B S hS _ _ _ _ hsq hw
  have hcond : ((Subfunctor.range f.hom).preimage v).ι ≫ v = (inv θ ≫ d) ≫ w := by
    simp [hd, ← hθ]
  obtain ⟨σ, ⟨hσ1, hσ2⟩, hσuniq⟩ :=
    existsUnique_section_of_isThickening B S hS hF hP hK hp₁E
      (hPpb.lift _ _ hcond) (hPpb.lift_fst _ _ hcond)
  refine ⟨σ ≫ pullback.snd v w, ⟨?_, ?_⟩, ?_⟩
  · calc π ≫ σ ≫ pullback.snd v w
        = (θ ≫ ((Subfunctor.range f.hom).preimage v).ι ≫ σ) ≫ pullback.snd v w := by
          rw [← hθ]; simp
      _ = (θ ≫ hPpb.lift _ _ hcond) ≫ pullback.snd v w := by rw [hσ2]
      _ = θ ≫ inv θ ≫ d := by rw [Category.assoc, hPpb.lift_snd]
      _ = d := by simp
  · rw [Category.assoc, ← hPpb.w, ← Category.assoc, hσ1, Category.id_comp]
  · rintro β ⟨hβ1, hβ2⟩
    have hβcond : (𝟙 F) ≫ v = β ≫ w := by rw [Category.id_comp, hβ2]
    have hτ : hPpb.lift (𝟙 F) β hβcond = σ := by
      refine hσuniq _ ⟨hPpb.lift_fst _ _ hβcond, hPpb.hom_ext ?_ ?_⟩
      · rw [Category.assoc, hPpb.lift_fst, Category.comp_id, hPpb.lift_fst]
      · rw [Category.assoc, hPpb.lift_snd, hPpb.lift_snd, ← cancel_epi θ, IsIso.hom_inv_id_assoc,
          ← Category.assoc, hθ]
        exact hβ1
    rw [← hτ, hPpb.lift_snd]

/-- Let `f : X ⟶ Y` be a monomorphism whose range is a thickening of `Y`, let `π : H ⟶ F` be a
base change of `f` along `v : F ⟶ Y`, and let `w : G ⟶ Y` be étale. Two morphisms `F ⟶ G` over
`Y` which agree after composing with `π` are equal. -/
theorem hom_ext_presheaf_of_isThickening_range
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) [Mono f.hom]
    (hT : IsThickening B S hS Y (Subfunctor.range f.hom))
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    {v : F ⟶ Y.1} {π : H ⟶ F} {q : H ⟶ X.1} (hpb : IsPullback π q v f.hom)
    (w : G ⟶ Y.1) (hw : IsEtale B S hS w) (α β : F ⟶ G)
    (hα : α ≫ w = v) (hβ : β ≫ w = v) (h : π ≫ α = π ≫ β) : α = β := by
  obtain ⟨α₀, -, huniq⟩ := existsUnique_hom_presheaf_of_isThickening B S hS f hT hF hG
    hpb w hw (π ≫ α) (by rw [Category.assoc, hα])
  rw [huniq α ⟨rfl, hα⟩, huniq β ⟨h.symm, hβ⟩]

end AlgebraicGeometry.Space

end
