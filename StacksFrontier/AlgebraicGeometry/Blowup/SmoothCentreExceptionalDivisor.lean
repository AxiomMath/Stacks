module

public import StacksFrontier.AlgebraicGeometry.Blowup.SmoothCentre
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FlatBaseChangeExceptionalDivisor
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CoordinateExceptionalSmooth
import all StacksFrontier.AlgebraicGeometry.Blowup.SmoothCentre

/-!
# The exceptional divisor of a blowup in a smooth centre is smooth

Let `S` be a scheme and let `i : Z ⟶ X` be a closed immersion of schemes smooth over `S`. The
blowup `X' = Bl_Z X` is smooth over `S` (`Stacks.AlgebraicGeometry.smooth_blowUpToBase_comp`). This
file proves that so is its exceptional divisor `E ⊆ X'`, the closed subscheme cut out by the
inverse image of the ideal sheaf of `Z`: the second assertion of Stacks tag 0FUT.

## Main results

* `Stacks.AlgebraicGeometry.smooth_exceptionalDivisor_coordinateSubspaceEmbedding`: the local
  model. The exceptional divisor of the blowup of relative affine `(m + n)`-space over `S` along
  the coordinate affine `m`-subspace is smooth over `S`.
* `Stacks.AlgebraicGeometry.smooth_exceptionalDivisor_comp`: the exceptional divisor of the blowup
  of a scheme smooth over `S` in a closed subscheme smooth over `S` is smooth over `S`.
* `Stacks.AlgebraicGeometry.smooth_exceptionalDivisor_comp_of_idealSheafData`: the same, for a
  closed subscheme presented by its quasi-coherent ideal sheaf.

## The argument

It runs along the four steps of
`StacksFrontier/AlgebraicGeometry/Blowup/SmoothCentre.lean`, with the
local model supplied by Stacks tag 0H1H (`Stacks.MoreMorphisms.exceptionalDivisor_smooth_of_pos`)
and the base-change squares by `AlgebraicGeometry.exists_isPullback_exceptionalDivisor_comap`,
which lifts flat base change of the blowup to its exceptional divisor. One step is shorter: there
is no case off the centre, because every point of the exceptional divisor lies over the centre —
its structure morphism to the ambient scheme factors through `i` by
`AlgebraicGeometry.Scheme.IdealSheafData.subschemeMap` — so the cover of the exceptional divisor by
the inverse images of the étale coordinate charts already exhausts it.

The remaining assertions of Tag 0FUT are in
`StacksFrontier/AlgebraicGeometry/Blowup/ExceptionalProjectiveBundle.lean`.

## References

* [Stacks Project, Tag 0FUT](https://stacks.math.columbia.edu/tag/0FUT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial

universe u

namespace Stacks.AlgebraicGeometry

/-! ### Smoothness of the exceptional divisor

The same four steps for the exceptional divisor `E ⊆ X'`, the closed subscheme cut out by the
inverse image of the centre. Throughout, the morphism `E ⟶ X` is written out as the composite
`(exceptionalIdeal ℐ).subschemeι ≫ blowUpToBase ℐ`.
-/

/-- Flat base change of the blowup morphism restricted to the exceptional divisor, for an ideal
sheaf `J` equal to the inverse image of `I`. -/
private theorem exists_isPullback_exceptionalDivisor_comp {X₁ X₂ : Scheme.{u}} (g : X₁ ⟶ X₂)
    [Flat g] (I : X₂.IdealSheafData) (J : X₁.IdealSheafData) (hJ : J = I.comap g) :
    ∃ e : exceptionalDivisor J ⟶ exceptionalDivisor I,
      IsPullback ((exceptionalIdeal J).subschemeι ≫ blowUpToBase J) e g
        ((exceptionalIdeal I).subschemeι ≫ blowUpToBase I) := by
  subst hJ
  obtain ⟨h, e, hpb, hepb⟩ := AlgebraicGeometry.exists_isPullback_exceptionalDivisor_comap g I
  exact ⟨e, hepb.paste_horiz hpb⟩

/-- Transport of smoothness of the exceptional divisor along an isomorphism of the ambient
scheme. -/
private theorem smooth_exceptionalDivisor_comp_of_isIso {X Y T : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (I : Y.IdealSheafData) (p : Y ⟶ T)
    (hs : Smooth ((exceptionalIdeal (I.comap g)).subschemeι ≫
      blowUpToBase (I.comap g) ≫ g ≫ p)) :
    Smooth ((exceptionalIdeal I).subschemeι ≫ blowUpToBase I ≫ p) := by
  have : IsOpenImmersion g := IsOpenImmersion.of_isIso g
  have : Flat g := inferInstance
  obtain ⟨e, hpb⟩ := exists_isPullback_exceptionalDivisor_comp g I _ rfl
  have : IsIso e := hpb.isIso_snd_of_isIso
  have hs' : Smooth (e ≫ ((exceptionalIdeal I).subschemeι ≫ blowUpToBase I) ≫ p) := by
    rw [← Category.assoc, ← hpb.w]
    simpa only [Category.assoc] using hs
  simpa only [Category.assoc] using
    (MorphismProperty.cancel_left_of_respectsIso @Smooth e _).mp hs'

/-- The exceptional divisor of the blowup of relative affine `(m + n)`-space over an affine base
`S` along the coordinate affine `m`-subspace is smooth over `S`. -/
theorem smooth_exceptionalDivisor_coordinateSubspaceEmbedding_of_isAffine
    (S : Scheme.{u}) [IsAffine S] (m n : ℕ) :
    Smooth ((exceptionalIdeal (coordinateSubspaceEmbedding S m n).ker).subschemeι ≫
      blowUpToBase (coordinateSubspaceEmbedding S m n).ker ≫
      (AffineSpace.over (ULift.{u} (Fin (m + n))) S).hom) := by
  have hci : IsClosedImmersion (coordinateSubspaceEmbedding S m n) :=
    coordinateSubspaceEmbedding_isClosedImmersion S m n
  refine smooth_exceptionalDivisor_comp_of_isIso
    (affineSpaceIsoSpec S (coordinateIndexEquiv.{u} m n)).inv _ _ ?_
  have hker : (coordinateSubspaceEmbedding S m n).ker.comap
        (affineSpaceIsoSpec S (coordinateIndexEquiv.{u} m n)).inv =
      Stacks.MoreMorphisms.coordinateIdeal (↥Γ(S, ⊤)) m n :=
    (AlgebraicGeometry.ker_eq_comap_ker_of_isPullback
      (IsPullback.of_horiz_isIso
        (CommSq.mk (affineSpaceIsoSpec_coordinate_sq S m n))).flip).symm
  rw [hker, show (affineSpaceIsoSpec S (coordinateIndexEquiv.{u} m n)).inv ≫
      (AffineSpace.over _ S).hom = _ from
    affineSpaceIsoSpec_inv_over S (coordinateIndexEquiv.{u} m n)]
  have : Smooth S.isoSpec.inv := inferInstance
  simpa only [Category.assoc] using MorphismProperty.comp_mem @Smooth _ _
    (Stacks.MoreMorphisms.exceptionalDivisor_smooth_of_pos (↥Γ(S, ⊤)) m n) this

/-- Restricting the base to an open subscheme exhibits the exceptional divisor of the blowup of the
coordinate subspace of relative affine space, with its structure morphism to the base, as a base
change. -/
private theorem exists_isPullback_exceptionalDivisor_ker_over
    (S : Scheme.{u}) (U : S.Opens) (m n : ℕ) :
    ∃ e : exceptionalDivisor (coordinateSubspaceEmbedding U.toScheme m n).ker ⟶
        exceptionalDivisor (coordinateSubspaceEmbedding S m n).ker,
      IsPullback
        ((exceptionalIdeal (coordinateSubspaceEmbedding U.toScheme m n).ker).subschemeι ≫
          blowUpToBase (coordinateSubspaceEmbedding U.toScheme m n).ker ≫
            𝔸(ULift.{u} (Fin (m + n)); U.toScheme) ↘ U.toScheme)
        e U.ι
        ((exceptionalIdeal (coordinateSubspaceEmbedding S m n).ker).subschemeι ≫
          blowUpToBase (coordinateSubspaceEmbedding S m n).ker ≫
            𝔸(ULift.{u} (Fin (m + n)); S) ↘ S) := by
  have : IsClosedImmersion (coordinateSubspaceEmbedding S m n) :=
    coordinateSubspaceEmbedding_isClosedImmersion S m n
  have hker : (coordinateSubspaceEmbedding U.toScheme m n).ker =
      (coordinateSubspaceEmbedding S m n).ker.comap
        (AffineSpace.map (ULift.{u} (Fin (m + n))) U.ι) :=
    AlgebraicGeometry.ker_eq_comap_ker_of_isPullback
      (isPullback_coordinateSubspaceEmbedding_map U.ι m n)
  have : Flat (AffineSpace.map (ULift.{u} (Fin (m + n))) U.ι) :=
    MorphismProperty.of_isPullback (P := @Flat)
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin (m + n))) U.ι).flip inferInstance
  obtain ⟨e, hesq⟩ := exists_isPullback_exceptionalDivisor_comp
    (AffineSpace.map (ULift.{u} (Fin (m + n))) U.ι) _ _ hker
  refine ⟨e, ?_⟩
  simpa only [Category.assoc] using
    hesq.paste_horiz (AffineSpace.isPullback_map (n := ULift.{u} (Fin (m + n))) U.ι).flip

/-- **The local model for the exceptional divisor.** The exceptional divisor of the blowup of
relative affine `(m + n)`-space over `S` along the coordinate affine `m`-subspace is smooth over
`S`. -/
theorem smooth_exceptionalDivisor_coordinateSubspaceEmbedding (S : Scheme.{u}) (m n : ℕ) :
    Smooth ((exceptionalIdeal (coordinateSubspaceEmbedding S m n).ker).subschemeι ≫
      blowUpToBase (coordinateSubspaceEmbedding S m n).ker ≫
      (AffineSpace.over (ULift.{u} (Fin (m + n))) S).hom) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @Smooth)
    (fun V : S.affineOpens => V.1) (iSup_affineOpens_eq_top S) fun V => ?_
  obtain ⟨e, hsq⟩ := exists_isPullback_exceptionalDivisor_ker_over S V.1 m n
  have : IsAffine V.1.toScheme := V.2
  refine (MorphismProperty.arrow_mk_iso_iff (P := @Smooth) ?_).mp
    (smooth_exceptionalDivisor_coordinateSubspaceEmbedding_of_isAffine V.1.toScheme m n)
  exact Arrow.isoMk (hsq.isoIsPullback _ _ (isPullback_morphismRestrict _ V.1)) (Iso.refl _)
    (hsq.isoIsPullback_hom_fst _ _ (isPullback_morphismRestrict _ V.1))

/-- Smoothness of the exceptional divisor over an open on which the closed immersion is the inverse
image of the coordinate subspace along an étale chart. -/
private theorem smooth_exceptionalDivisor_comap_comp
    {S X : Scheme.{u}} (f : X ⟶ S) (ℐ : X.IdealSheafData) (U : X.Opens) {m n : ℕ}
    (π : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin (m + n))) S) (hπ : Etale π)
    (hπS : π ≫ (AffineSpace.over (ULift.{u} (Fin (m + n))) S).hom = U.ι ≫ f)
    (hker : ℐ.comap U.ι = (coordinateSubspaceEmbedding S m n).ker.comap π) :
    Smooth ((exceptionalIdeal (ℐ.comap U.ι)).subschemeι ≫
      blowUpToBase (ℐ.comap U.ι) ≫ U.ι ≫ f) := by
  have := hπ
  have : Smooth π := inferInstance
  have : Flat π := inferInstance
  obtain ⟨e', hepb⟩ := exists_isPullback_exceptionalDivisor_comp π
    (coordinateSubspaceEmbedding S m n).ker _ hker
  have : Etale e' := MorphismProperty.of_isPullback (P := @Etale) hepb hπ
  have : Smooth e' := inferInstance
  have key := congrArg
    (fun t => t ≫ (AffineSpace.over (ULift.{u} (Fin (m + n))) S).hom) hepb.w
  simp only [Category.assoc] at key
  rw [← hπS, key]
  exact MorphismProperty.comp_mem @Smooth _ _ inferInstance
    (smooth_exceptionalDivisor_coordinateSubspaceEmbedding S m n)

/-- Flat base change along an open immersion identifies the exceptional divisor of the blowup of
the restricted ideal sheaf with the restriction of the exceptional divisor. -/
private theorem smooth_exceptionalDivisor_restrict_comp_of_comap
    {S X : Scheme.{u}} (f : X ⟶ S) (ℐ : X.IdealSheafData) (U : X.Opens)
    (h : Smooth ((exceptionalIdeal (ℐ.comap U.ι)).subschemeι ≫
      blowUpToBase (ℐ.comap U.ι) ≫ U.ι ≫ f)) :
    Smooth ((((exceptionalIdeal ℐ).subschemeι ≫ blowUpToBase ℐ) ∣_ U) ≫ U.ι ≫ f) := by
  obtain ⟨e, hsq⟩ := exists_isPullback_exceptionalDivisor_comp U.ι ℐ _ rfl
  have hsq2 := AlgebraicGeometry.isPullback_morphismRestrict
    ((exceptionalIdeal ℐ).subschemeι ≫ blowUpToBase ℐ) U
  rw [← MorphismProperty.cancel_left_of_respectsIso @Smooth
      (hsq.isoIsPullback _ _ hsq2).hom _, ← Category.assoc,
    IsPullback.isoIsPullback_hom_fst]
  simpa only [Category.assoc] using h

/-- Every point of the exceptional divisor has an open neighbourhood in the ambient scheme over
which the exceptional divisor, composed with the structure morphism to the base, is smooth. -/
private theorem exists_opens_smooth_exceptionalDivisor_restrict
    {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X)
    [IsClosedImmersion i] [Smooth f] [Smooth (i ≫ f)]
    (t : exceptionalDivisor i.ker) :
    ∃ U : X.Opens,
      t ∈ ((exceptionalIdeal i.ker).subschemeι ≫ blowUpToBase i.ker) ⁻¹ᵁ U ∧
      Smooth ((((exceptionalIdeal i.ker).subschemeι ≫ blowUpToBase i.ker) ∣_ U) ≫
        U.ι ≫ f) := by
  have hle : i.ker ≤ (exceptionalIdeal i.ker).map (blowUpToBase i.ker) :=
    Scheme.IdealSheafData.le_map_comap _ _
  have hfac := Scheme.IdealSheafData.subschemeMap_subschemeι
    (exceptionalIdeal i.ker) i.ker (blowUpToBase i.ker) hle
  have hmem : ((exceptionalIdeal i.ker).subschemeι ≫ blowUpToBase i.ker).base t ∈
      (i.ker.support : Set X) := by
    rw [← Scheme.IdealSheafData.range_subschemeι, ← hfac]
    exact ⟨_, rfl⟩
  have hrange : (i.ker.support : Set X) = Set.range i := by
    rw [Scheme.Hom.support_ker i, i.isClosedEmbedding.isClosed_range.closure_eq]
  obtain ⟨y, hy⟩ : ∃ y, i y =
      ((exceptionalIdeal i.ker).subschemeι ≫ blowUpToBase i.ker).base t := by
    rwa [hrange] at hmem
  obtain ⟨m, n, U, hyU, π, q, hπ, hπS, hpb⟩ :=
    exists_etale_coordinateSubspaceEmbedding_isPullback f i y
  have : IsClosedImmersion (coordinateSubspaceEmbedding S m n) :=
    coordinateSubspaceEmbedding_isClosedImmersion S m n
  have hker : i.ker.comap U.ι = (coordinateSubspaceEmbedding S m n).ker.comap π := by
    rw [← AlgebraicGeometry.ker_eq_comap_ker_of_isPullback
        (AlgebraicGeometry.isPullback_morphismRestrict i U),
      ← Scheme.Hom.resLE_eq_morphismRestrict,
      AlgebraicGeometry.ker_eq_comap_ker_of_isPullback hpb]
  have hyU' : i.base y ∈ U := hyU
  have ht : ((exceptionalIdeal i.ker).subschemeι ≫ blowUpToBase i.ker).base t ∈ U := hy ▸ hyU'
  exact ⟨U, ht, smooth_exceptionalDivisor_restrict_comp_of_comap f i.ker U
    (smooth_exceptionalDivisor_comap_comp f i.ker U π hπ hπS hker)⟩

/-- **Stacks Project, Tag 0FUT**, second assertion. Let `S` be a scheme and let `i : Z ⟶ X` be a
closed immersion of schemes smooth over `S`. Then the exceptional divisor of the blowup of `X` in
`Z` is smooth over `S`. -/
theorem smooth_exceptionalDivisor_comp {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X)
    [IsClosedImmersion i] [Smooth f] [Smooth (i ≫ f)] :
    Smooth ((exceptionalIdeal i.ker).subschemeι ≫ blowUpToBase i.ker ≫ f) := by
  choose V hxV hV using exists_opens_smooth_exceptionalDivisor_restrict f i
  have hgoal : Smooth (((exceptionalIdeal i.ker).subschemeι ≫ blowUpToBase i.ker) ≫ f) := by
    refine IsZariskiLocalAtSource.of_iSup_eq_top
      (fun t : exceptionalDivisor i.ker =>
        ((exceptionalIdeal i.ker).subschemeι ≫ blowUpToBase i.ker) ⁻¹ᵁ V t) ?_ fun t => ?_
    · rw [eq_top_iff]
      intro t _
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨t, hxV t⟩
    · rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
      exact hV t
  simpa only [Category.assoc] using hgoal

/-- The exceptional divisor of the blowup of a scheme smooth over `S` in a closed subscheme smooth
over `S`, presented by its quasi-coherent ideal sheaf, is smooth over `S`. -/
theorem smooth_exceptionalDivisor_comp_of_idealSheafData {S X : Scheme.{u}} (f : X ⟶ S)
    (I : X.IdealSheafData) [Smooth f] [Smooth (I.subschemeι ≫ f)] :
    Smooth ((exceptionalIdeal I).subschemeι ≫ blowUpToBase I ≫ f) := by
  have := smooth_exceptionalDivisor_comp f I.subschemeι
  rwa [Scheme.IdealSheafData.ker_subschemeι] at this

end Stacks.AlgebraicGeometry

end
