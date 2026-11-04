module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatteningFiniteType.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformSpaceEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformSpaceFlatEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSource.Fppf
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceFinitePart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence

/-!
# Flatness of a strict transform descends along étale covers

Let `b : A' ⟶ A` be a morphism of algebraic spaces and `E ⊆ A'` an effective Cartier divisor.
The strict transform of `X ⟶ A` with respect to `(b, E)` pulls back, along a surjective étale
morphism `X₂ ⟶ X`, to the strict transform of `X₂` (Stacks 0863, part (2)), so flatness and
local finite presentation over `A'` descend from the latter to the former (Stacks 06ET, 06EV).
The statement allows the base to be changed along a monomorphism, which covers both an étale
chart of the source and an isomorphism of the base.

## Main results

* `AlgebraicGeometry.Space.isFlat_and_isLocallyOfFinitePresentation_strictTransform_of_etaleCover`.

## References

* [Stacks Project, Tag 0863](https://stacks.math.columbia.edu/tag/0863)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Flatness and local finite presentation of a strict transform descend along an étale cover
of the source and a monomorphism of the base.**  Let `f : X ⟶ A`, `b : A' ⟶ A`, and let
`f₂ : X₂ ⟶ A₂`, `b₂ : A' ⟶ A₂` be a second situation over the same `A'`, related by a
monomorphism `k : A₂ ⟶ A` with `b₂ ≫ k = b` and a surjective étale `u : X₂ ⟶ X` with
`f₂ ≫ k = u ≫ f`.  For an effective Cartier divisor `E ⊆ A'`, if the strict transform of `X₂`
with respect to `(b₂, E)` is flat and locally of finite presentation over `A'`, so is the strict
transform of `X` with respect to `(b, E)`. -/
theorem isFlat_and_isLocallyOfFinitePresentation_strictTransform_of_etaleCover
    {A A₂ X X₂ A' : AlgebraicSpaces B S hS} (f : X ⟶ A) (b : A' ⟶ A) (f₂ : X₂ ⟶ A₂)
    (b₂ : A' ⟶ A₂) (k : A₂ ⟶ A) [Mono k.hom] (u : X₂ ⟶ X) (hu : IsEtale B S hS u.hom)
    (hus : IsSurjective B S hS u.hom) (hf : f₂.hom ≫ k.hom = u.hom ≫ f.hom)
    (hbk : b₂.hom ≫ k.hom = b.hom) (E : ClosedSubspaces B S hS A'.1)
    (hE : IsEffectiveCartierDivisor B S hS A' E)
    (hflat : IsFlat B S hS (strictTransformSpaceToBlowUp B S hS f₂ b₂ E.1).hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS
      (strictTransformSpaceToBlowUp B S hS f₂ b₂ E.1).hom) :
    IsFlat B S hS (strictTransformSpaceToBlowUp B S hS f b E.1).hom ∧
      IsLocallyOfFinitePresentation B S hS
        (strictTransformSpaceToBlowUp B S hS f b E.1).hom := by
  -- the comparison of the two ambient fibre products
  have hw : (pullback.fst f₂.hom b₂.hom ≫ u.hom) ≫ f.hom = pullback.snd f₂.hom b₂.hom ≫ b.hom := by
    rw [Category.assoc, ← hf, ← hbk, ← Category.assoc, pullback.condition, Category.assoc]
  set can : strictTransformPullback B S hS f₂ b₂ ⟶ strictTransformPullback B S hS f b :=
    ObjectProperty.homMk (pullback.lift _ _ hw) with hcan
  have hcanB : can ≫ strictTransformPullbackToBlowUp B S hS f b =
      strictTransformPullbackToBlowUp B S hS f₂ b₂ ≫ 𝟙 A' := by
    rw [Category.comp_id]
    exact ObjectProperty.hom_ext _ (pullback.lift_snd _ _ _)
  -- `can` is the base change of `u`
  have hM : IsPullback b₂.hom (𝟙 A'.1) k.hom b.hom :=
    IsPullback.of_vert_isIso_mono ⟨by rw [hbk, Category.id_comp]⟩
  have hP2 := (IsPullback.of_hasPullback f₂.hom b₂.hom).paste_vert hM
  rw [Category.comp_id, hf] at hP2
  have hsq : IsPullback can.hom (pullback.fst f₂.hom b₂.hom) (pullback.fst f.hom b.hom) u.hom := by
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback f.hom b.hom).flip
    show IsPullback (pullback.lift _ _ hw ≫ pullback.snd f.hom b.hom) _ _ _
    rw [pullback.lift_snd]
    exact hP2.flip
  have hcanE : IsEtale B S hS can.hom :=
    isEtale_of_isPullback_of_isAlgebraicSpace B S hS hsq (strictTransformPullback B S hS f₂ b₂).2
      (strictTransformPullback B S hS f b).2 X₂.2 X.2 hu
  have hcanS : IsSurjective B S hS can.hom := by
    have hsq' : IsPullback (strictTransformPullbackToSource B S hS f₂ b₂) can u
        (strictTransformPullbackToSource B S hS f b) :=
      IsPullback.of_map (ObjectProperty.ι _)
        (ObjectProperty.hom_ext _ (pullback.lift_fst _ _ hw).symm) hsq.flip
    exact isSurjective_of_isPullback B S hS hsq' hus
  -- the strict transform of `X₂` is the inverse image of that of `X`
  have hT := exceptionalPreimageSet_eq_preimage_of_comp_eq B S hS f b E.1 f₂ b₂ E.1 (𝟙 A') can
    hcanB (by simp)
  have heq := strictTransformSubfunctor_eq_preimage_of_isEffectiveCartierDivisor B S hS f b E hE
    f₂ b₂ E.1 can hcanE hT
  set G := strictTransformSubfunctor B S hS f b E.1 with hG
  have hGcl : IsClosedSubspace B S hS G :=
    strictTransformSubfunctor_isClosedSubspace B S hS f b _
  have hGpcl : IsClosedSubspace B S hS (G.preimage can.hom) :=
    isClosedSubspace_preimage B S hS can.hom G (strictTransformPullback B S hS f b).2
      (strictTransformPullback B S hS f₂ b₂).2 hGcl
  change IsFlat B S hS ((strictTransformSubfunctor B S hS f₂ b₂ E.1).ι ≫
    (strictTransformPullbackToBlowUp B S hS f₂ b₂).hom) at hflat
  change IsLocallyOfFinitePresentation B S hS
    ((strictTransformSubfunctor B S hS f₂ b₂ E.1).ι ≫
      (strictTransformPullbackToBlowUp B S hS f₂ b₂).hom) at hlfp
  rw [heq] at hflat hlfp
  show IsFlat B S hS (G.ι ≫ (strictTransformPullbackToBlowUp B S hS f b).hom) ∧
    IsLocallyOfFinitePresentation B S hS
      (G.ι ≫ (strictTransformPullbackToBlowUp B S hS f b).hom)
  have hsqG := Subfunctor.isPullback_preimage can.hom G
  have hcomp : (G.preimage can.hom).ι ≫ (strictTransformPullbackToBlowUp B S hS f₂ b₂).hom =
      G.fromPreimage can.hom ≫ G.ι ≫ (strictTransformPullbackToBlowUp B S hS f b).hom := by
    have h2' : can.hom ≫ (strictTransformPullbackToBlowUp B S hS f b).hom =
        (strictTransformPullbackToBlowUp B S hS f₂ b₂).hom := by
      rw [← Category.comp_id (strictTransformPullbackToBlowUp B S hS f₂ b₂).hom]
      exact congrArg (fun k => k.hom) hcanB
    rw [← h2', ← Category.assoc, ← Category.assoc, ← Subfunctor.fromPreimage_ι]
  have hr : IsEtale B S hS (G.fromPreimage can.hom) :=
    isEtale_of_isPullback_of_isAlgebraicSpace B S hS hsqG hGpcl.1 hGcl.1
      (strictTransformPullback B S hS f₂ b₂).2 (strictTransformPullback B S hS f b).2 hcanE
  have hrs : IsSurjective B S hS (G.fromPreimage can.hom) := by
    let Gs : AlgebraicSpaces B S hS := ⟨G.toFunctor, hGcl.1⟩
    let Gps : AlgebraicSpaces B S hS := ⟨(G.preimage can.hom).toFunctor, hGpcl.1⟩
    have hsq' : IsPullback (ObjectProperty.homMk (G.preimage can.hom).ι :
          Gps ⟶ strictTransformPullback B S hS f₂ b₂)
        (ObjectProperty.homMk (G.fromPreimage can.hom) : Gps ⟶ Gs) can
        (ObjectProperty.homMk G.ι : Gs ⟶ strictTransformPullback B S hS f b) :=
      IsPullback.of_map (ObjectProperty.ι _)
        (ObjectProperty.hom_ext _ (Subfunctor.fromPreimage_ι G can.hom).symm) hsqG.flip
    exact isSurjective_of_isPullback B S hS hsq' hcanS
  rw [hcomp] at hflat hlfp
  exact ⟨isFlat_of_comp_of_isSurjective_of_isFlat B S hS hGpcl.1 hGcl.1 _ _ hrs
      (isFlat_of_isEtale B S hS hr) hflat,
    isLocallyOfFinitePresentation_of_comp_of_isEtale_of_isSurjective hGpcl.1 hGcl.1 A'.2 hr hrs
      hlfp⟩

end AlgebraicGeometry.Space

end
