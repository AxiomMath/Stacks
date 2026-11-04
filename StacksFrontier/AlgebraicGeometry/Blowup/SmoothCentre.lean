module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor.ZeroIdeal
public import StacksFrontier.AlgebraicGeometry.Blowup.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CoordinateBlowupSmooth
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SmoothClosedImmersionCoordinates
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Blowing up a closed immersion of schemes smooth over a base

Let `S` be a scheme and let `i : Z ⟶ X` be a closed immersion of schemes smooth over `S`.  This
file proves that the blowup `X' = Bl_Z X`, the relative `Proj` of the Rees algebra of the ideal
sheaf of `Z`, is again smooth over `S`.

## Main definitions

* `Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding_over` and
  `Stacks.AlgebraicGeometry.isPullback_coordinateSubspaceEmbedding_map` record that the coordinate
  subspace of relative affine space is a closed subscheme over the base and that it is compatible
  with base change of the base.

## Main results

* `Stacks.AlgebraicGeometry.smooth_blowUp_coordinateSubspaceEmbedding`:  the local model.  The
  blowup of relative affine `(m + n)`-space over `S` along the coordinate affine `m`-subspace is
  smooth over `S`.
* `Stacks.AlgebraicGeometry.smooth_blowUpToBase_comp`:  the blowup of a scheme smooth over `S` in
  a closed subscheme smooth over `S` is smooth over `S`.  This is the first assertion of Stacks
  tag 0FUT.
* `Stacks.AlgebraicGeometry.smooth_blowUpToBase_comp_of_idealSheafData`:  the same, for a closed
  subscheme presented by its quasi-coherent ideal sheaf.

## The argument

The local model is the blowup of affine `(m + n)`-space along the vanishing locus of the last `n`
coordinates, which Stacks tag 0H1H exhibits as covered by polynomial affine spaces over the
coefficient ring.  Over an affine base `S` the relative statement is that one, transported along
the identification of `𝐀^{m+n}_S` with `Spec Γ(S, ⊤)[x₁, …, x_m, y₁, …, y_n]`:  blowing up
commutes with flat base change (Stacks tag 0805), so an isomorphism of the ambient scheme matching
up the two centres matches up the two blowups.  For a general base one descends along an affine
open cover, again by flat base change, using that the coordinate subspace of `𝐀^{m+n}_S` is the
inverse image of the coordinate subspace of `𝐀^{m+n}_T` under a base change `S ⟶ T`.

For the theorem itself, smoothness is Zariski local at the source, so it suffices to cover `X` by
opens `U` over which the blowup is smooth.  Off the centre the blowup morphism is an isomorphism
(Stacks tag 02OS), so there the structure morphism of `X` does the job.  At a point of the centre,
Stacks tag 0FUE presents the closed immersion as the inverse image of the coordinate subspace of
`𝐀^{m+n}_S` under an étale `π : U ⟶ 𝐀^{m+n}_S` over `S`.  Flat base change along `π` then
identifies the blowup over `U` as the base change of the local model along `π`, and an étale
morphism is smooth.

## References

* [Stacks Project, Tag 0FUT](https://stacks.math.columbia.edu/tag/0FUT)
* [Stacks Project, Tag 0FUE](https://stacks.math.columbia.edu/tag/0FUE)
* [Stacks Project, Tag 0H1H](https://stacks.math.columbia.edu/tag/0H1H)
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial

universe u

namespace Stacks.AlgebraicGeometry

/-! ### Instances for smoothness that instance search does not find

Both `MorphismProperty.RespectsIso @Smooth` and `IsZariskiLocalAtSource @Smooth` hold for the
generic reasons recorded in Mathlib, but neither is retrieved by instance search at the head
`@Smooth`, so they are restated here. -/

private instance smoothRespectsIso : MorphismProperty.RespectsIso @Smooth :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

private instance smoothIsZariskiLocalAtSource : IsZariskiLocalAtSource @Smooth :=
  HasRingHomProperty.instIsZariskiLocalAtSource

private instance smoothIsZariskiLocalAtTarget : IsZariskiLocalAtTarget @Smooth :=
  HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Smooth) (Q := RingHom.Smooth)

/-! ### The coordinate subspace of relative affine space -/

/-- The coordinate subspace embedding is a morphism over the base. -/
@[reassoc]
theorem coordinateSubspaceEmbedding_over (S : Scheme.{u}) (m n : ℕ) :
    coordinateSubspaceEmbedding S m n ≫ 𝔸(ULift.{u} (Fin (m + n)); S) ↘ S =
      𝔸(ULift.{u} (Fin m); S) ↘ S :=
  AffineSpace.homOfVector_over _ _

/-- The coordinate subspace embedding is compatible with base change of the base. -/
theorem coordinateSubspaceEmbedding_map_comm {S T : Scheme.{u}} (f : S ⟶ T) (m n : ℕ) :
    coordinateSubspaceEmbedding S m n ≫ AffineSpace.map (ULift.{u} (Fin (m + n))) f =
      AffineSpace.map (ULift.{u} (Fin m)) f ≫ coordinateSubspaceEmbedding T m n := by
  apply AffineSpace.hom_ext
  · rw [Category.assoc, AffineSpace.map_over, ← Category.assoc,
      coordinateSubspaceEmbedding_over, Category.assoc, coordinateSubspaceEmbedding_over,
      AffineSpace.map_over]
  · intro i
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
    obtain ⟨i⟩ := i
    induction i using Fin.addCases with
    | left j =>
      rw [CommRingCat.comp_apply, CommRingCat.comp_apply, AffineSpace.map_appTop_coord,
        coordinateSubspaceEmbedding_firstCoordinate, coordinateSubspaceEmbedding_firstCoordinate,
        AffineSpace.map_appTop_coord]
    | right j =>
      rw [CommRingCat.comp_apply, CommRingCat.comp_apply, AffineSpace.map_appTop_coord,
        coordinateSubspaceEmbedding_lastCoordinate, coordinateSubspaceEmbedding_lastCoordinate,
        map_zero]

/-- The coordinate subspace of relative affine `(m + n)`-space over `S` is the inverse image of
the coordinate subspace of relative affine `(m + n)`-space over `T` along a base change
`f : S ⟶ T`. -/
theorem isPullback_coordinateSubspaceEmbedding_map {S T : Scheme.{u}} (f : S ⟶ T) (m n : ℕ) :
    IsPullback (coordinateSubspaceEmbedding S m n)
      (AffineSpace.map (ULift.{u} (Fin m)) f)
      (AffineSpace.map (ULift.{u} (Fin (m + n))) f)
      (coordinateSubspaceEmbedding T m n) := by
  refine IsPullback.of_right ?_ (coordinateSubspaceEmbedding_map_comm f m n)
    (AffineSpace.isPullback_map (n := ULift.{u} (Fin (m + n))) f).flip
  rw [coordinateSubspaceEmbedding_over, coordinateSubspaceEmbedding_over]
  exact (AffineSpace.isPullback_map (n := ULift.{u} (Fin m)) f).flip

private instance isClosedImmersion_coordinateSubspaceEmbedding (S : Scheme.{u}) (m n : ℕ) :
    IsClosedImmersion (coordinateSubspaceEmbedding S m n) :=
  coordinateSubspaceEmbedding_isClosedImmersion S m n

/-! ### Glue -/

private theorem smooth_blowUpToBase_comp_of_isIso {X Y T : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (I : Y.IdealSheafData) (p : Y ⟶ T)
    (hs : Smooth (blowUpToBase (I.comap g) ≫ g ≫ p)) : Smooth (blowUpToBase I ≫ p) := by
  have : IsOpenImmersion g := IsOpenImmersion.of_isIso g
  have : Flat g := inferInstance
  obtain ⟨h, hpb⟩ := AlgebraicGeometry.exists_isPullback_blowUpToBase_comap g I
  have : IsIso h := hpb.isIso_snd_of_isIso
  rw [← Category.assoc, hpb.w, Category.assoc] at hs
  exact (MorphismProperty.cancel_left_of_respectsIso @Smooth h (blowUpToBase I ≫ p)).mp hs

/-! ### The local model over an affine base -/

/-- Pulling a global section of `Spec A` back along `Spec φ`. -/
private theorem specMap_appTop_ΓSpecIso_inv_eq {A B : CommRingCat.{u}} (φ : A ⟶ B) (a : A) :
    (Spec.map φ).appTop ((Scheme.ΓSpecIso A).inv a) = (Scheme.ΓSpecIso B).inv (φ a) := by
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]

/-- Renaming the variables of a polynomial ring along an equivalence of index types. -/
private def mvPolynomialRenameIso {σ : Type u} {τ : Type} (R : Type u) [CommRing R] (e : σ ≃ τ) :
    CommRingCat.of (MvPolynomial τ R) ≅ CommRingCat.of (MvPolynomial σ R) :=
  (MvPolynomial.renameEquiv R e.symm).toRingEquiv.toCommRingCatIso

section AffineBase

variable {σ : Type u} {τ : Type} (S : Scheme.{u}) [IsAffine S] (e : σ ≃ τ)

/-- Relative affine `σ`-space over an affine base `S`, identified with the spectrum of a
polynomial ring over `Γ(S, ⊤)` whose variables are indexed by `τ`. -/
private def affineSpaceIsoSpec : AffineSpace σ S ≅ Spec (.of (MvPolynomial τ Γ(S, ⊤))) :=
  AffineSpace.isoOfIsAffine _ S ≪≫ asIso (Spec.map (mvPolynomialRenameIso Γ(S, ⊤) e).hom)

/-- The inverse of `affineSpaceIsoSpec`, factored through Mathlib's identification. -/
private theorem affineSpaceIsoSpec_inv : (affineSpaceIsoSpec S e).inv =
    Spec.map (mvPolynomialRenameIso Γ(S, ⊤) e).inv ≫ (AffineSpace.isoOfIsAffine σ S).inv := by
  simp [affineSpaceIsoSpec, ← Spec.map_inv]

/-- The identification of `affineSpaceIsoSpec` is compatible with the structure morphisms to the
base. -/
private theorem affineSpaceIsoSpec_inv_over : (affineSpaceIsoSpec S e).inv ≫ 𝔸(σ; S) ↘ S =
    Spec.map (CommRingCat.ofHom (C : Γ(S, ⊤) →+* MvPolynomial τ Γ(S, ⊤))) ≫ S.isoSpec.inv := by
  rw [affineSpaceIsoSpec_inv, Category.assoc,
    show (AffineSpace.isoOfIsAffine σ S).inv ≫ 𝔸(σ; S) ↘ S = _ from
      AffineSpace.isoOfIsAffine_inv_over (n := σ) S, ← Spec.map_comp_assoc]
  congr 2
  ext r
  simp [mvPolynomialRenameIso, RingEquiv.toCommRingCatIso]

/-- The identification of `affineSpaceIsoSpec` carries the `k`-th coordinate to the variable
indexed by `e k`. -/
private theorem affineSpaceIsoSpec_inv_appTop_coord (k : σ) :
    (affineSpaceIsoSpec S e).inv.appTop (AffineSpace.coord S k) =
      (Scheme.ΓSpecIso (.of (MvPolynomial τ Γ(S, ⊤)))).inv (MvPolynomial.X (e k)) := by
  rw [affineSpaceIsoSpec_inv, Scheme.Hom.comp_appTop]
  simp only [CommRingCat.comp_apply, AffineSpace.isoOfIsAffine_inv_appTop_coord]
  rw [specMap_appTop_ΓSpecIso_inv_eq]
  congr 1
  simp [mvPolynomialRenameIso, RingEquiv.toCommRingCatIso]

end AffineBase

/-- The index of the `(m + n)` coordinates of relative affine space, split into the first `m` and
the last `n`. -/
private def coordinateIndexEquiv (m n : ℕ) : ULift.{u} (Fin (m + n)) ≃ Fin m ⊕ Fin n :=
  Equiv.ulift.trans finSumFinEquiv.symm

/-- The coordinate closed immersion of affine spaces over a ring is the spectrum of the coordinate
projection. -/
private theorem coordinateEmbedding_eq_specMap (R : Type u) [CommRing R] (m n : ℕ) :
    Stacks.MoreMorphisms.coordinateEmbedding R m n =
      Spec.map (CommRingCat.ofHom (Stacks.MoreMorphisms.coordinateProjection R m n)) := rfl

/-- Over an affine base, the coordinate subspace of relative affine space is identified with the
coordinate subspace of the spectrum of a polynomial ring. -/
private theorem affineSpaceIsoSpec_coordinate_sq (S : Scheme.{u}) [IsAffine S] (m n : ℕ) :
    (affineSpaceIsoSpec S (Equiv.ulift.{u} (α := Fin m))).inv ≫
        coordinateSubspaceEmbedding S m n =
      Stacks.MoreMorphisms.coordinateEmbedding Γ(S, ⊤) m n ≫
        (affineSpaceIsoSpec S (coordinateIndexEquiv.{u} m n)).inv := by
  refine AffineSpace.hom_ext ?_ ?_
  · rw [Category.assoc, coordinateSubspaceEmbedding_over, affineSpaceIsoSpec_inv_over,
      Category.assoc, affineSpaceIsoSpec_inv_over, coordinateEmbedding_eq_specMap,
      ← Spec.map_comp_assoc]
    congr 2
    ext r
    simp [Stacks.MoreMorphisms.coordinateProjection]
  · rintro ⟨k⟩
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
    simp only [CommRingCat.comp_apply]
    rw [coordinateEmbedding_eq_specMap, affineSpaceIsoSpec_inv_appTop_coord,
      specMap_appTop_ΓSpecIso_inv_eq]
    induction k using Fin.addCases with
    | left j =>
      rw [coordinateSubspaceEmbedding_firstCoordinate, affineSpaceIsoSpec_inv_appTop_coord]
      congr 1
      simp [coordinateIndexEquiv, Stacks.MoreMorphisms.coordinateProjection]
    | right j =>
      rw [coordinateSubspaceEmbedding_lastCoordinate]
      simp [coordinateIndexEquiv, Stacks.MoreMorphisms.coordinateProjection]

/-- The blowup of relative affine `(m + n)`-space over an affine base `S` along the coordinate
affine `m`-subspace is smooth over `S`. -/
theorem smooth_blowUp_coordinateSubspaceEmbedding_of_isAffine
    (S : Scheme.{u}) [IsAffine S] (m n : ℕ) :
    Smooth (blowUpToBase (coordinateSubspaceEmbedding S m n).ker ≫
      (AffineSpace.over (ULift.{u} (Fin (m + n))) S).hom) := by
  refine smooth_blowUpToBase_comp_of_isIso
    (affineSpaceIsoSpec S (coordinateIndexEquiv.{u} m n)).inv _ _ ?_
  have hker : (coordinateSubspaceEmbedding S m n).ker.comap
        (affineSpaceIsoSpec S (coordinateIndexEquiv.{u} m n)).inv =
      Stacks.MoreMorphisms.coordinateIdeal (↥Γ(S, ⊤)) m n :=
    (AlgebraicGeometry.ker_eq_comap_ker_of_isPullback
      (IsPullback.of_horiz_isIso
        (CommSq.mk (affineSpaceIsoSpec_coordinate_sq S m n))).flip).symm
  rw [hker, show (affineSpaceIsoSpec S (coordinateIndexEquiv.{u} m n)).inv ≫
      (AffineSpace.over _ S).hom = _ from
    affineSpaceIsoSpec_inv_over S (coordinateIndexEquiv.{u} m n), ← Category.assoc]
  have : Smooth S.isoSpec.inv := inferInstance
  exact MorphismProperty.comp_mem @Smooth _ _
    (Stacks.MoreMorphisms.blowUp_smooth_of_pos (↥Γ(S, ⊤)) m n) this

/-! ### The local model over an arbitrary base -/

/-- Restricting the base to an open subscheme exhibits the blowup of the coordinate subspace of
relative affine space, with its structure morphism to the base, as a base change. -/
private theorem exists_isPullback_blowUpToBase_ker_over (S : Scheme.{u}) (U : S.Opens) (m n : ℕ) :
    ∃ h : blowUp (coordinateSubspaceEmbedding U.toScheme m n).ker ⟶
        blowUp (coordinateSubspaceEmbedding S m n).ker,
      IsPullback
        (blowUpToBase (coordinateSubspaceEmbedding U.toScheme m n).ker ≫
          𝔸(ULift.{u} (Fin (m + n)); U.toScheme) ↘ U.toScheme)
        h U.ι
        (blowUpToBase (coordinateSubspaceEmbedding S m n).ker ≫
          𝔸(ULift.{u} (Fin (m + n)); S) ↘ S) := by
  have hker : (coordinateSubspaceEmbedding U.toScheme m n).ker =
      (coordinateSubspaceEmbedding S m n).ker.comap
        (AffineSpace.map (ULift.{u} (Fin (m + n))) U.ι) :=
    AlgebraicGeometry.ker_eq_comap_ker_of_isPullback
      (isPullback_coordinateSubspaceEmbedding_map U.ι m n)
  have : Flat (AffineSpace.map (ULift.{u} (Fin (m + n))) U.ι) :=
    MorphismProperty.of_isPullback (P := @Flat)
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin (m + n))) U.ι).flip inferInstance
  obtain ⟨h, hsq⟩ : ∃ h : blowUp (coordinateSubspaceEmbedding U.toScheme m n).ker ⟶
      blowUp (coordinateSubspaceEmbedding S m n).ker,
      IsPullback (blowUpToBase (coordinateSubspaceEmbedding U.toScheme m n).ker)
        h (AffineSpace.map (ULift.{u} (Fin (m + n))) U.ι)
        (blowUpToBase (coordinateSubspaceEmbedding S m n).ker) := by
    rw [hker]
    exact AlgebraicGeometry.exists_isPullback_blowUpToBase_comap _ _
  exact ⟨h, hsq.paste_horiz
    (AffineSpace.isPullback_map (n := ULift.{u} (Fin (m + n))) U.ι).flip⟩

/-- **The local model.** The blowup of relative affine `(m + n)`-space over `S` along the
coordinate affine `m`-subspace is smooth over `S`. -/
theorem smooth_blowUp_coordinateSubspaceEmbedding (S : Scheme.{u}) (m n : ℕ) :
    Smooth (blowUpToBase (coordinateSubspaceEmbedding S m n).ker ≫
      (AffineSpace.over (ULift.{u} (Fin (m + n))) S).hom) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @Smooth)
    (fun V : S.affineOpens => V.1) (iSup_affineOpens_eq_top S) fun V => ?_
  obtain ⟨h, hsq⟩ := exists_isPullback_blowUpToBase_ker_over S V.1 m n
  have : IsAffine V.1.toScheme := V.2
  refine (MorphismProperty.arrow_mk_iso_iff (P := @Smooth) ?_).mp
    (smooth_blowUp_coordinateSubspaceEmbedding_of_isAffine V.1.toScheme m n)
  exact Arrow.isoMk (hsq.isoIsPullback _ _ (isPullback_morphismRestrict _ V.1)) (Iso.refl _)
    (hsq.isoIsPullback_hom_fst _ _ (isPullback_morphismRestrict _ V.1))

/-! ### Smoothness of the blowup -/

/-- Smoothness of the blowup over an open on which the closed immersion is the inverse image of
the coordinate subspace along an étale chart. -/
private theorem smooth_blowUpToBase_comap_comp
    {S X : Scheme.{u}} (f : X ⟶ S) (ℐ : X.IdealSheafData) (U : X.Opens) {m n : ℕ}
    (π : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin (m + n))) S) (hπ : Etale π)
    (hπS : π ≫ (AffineSpace.over (ULift.{u} (Fin (m + n))) S).hom = U.ι ≫ f)
    (hker : ℐ.comap U.ι = (coordinateSubspaceEmbedding S m n).ker.comap π) :
    Smooth (blowUpToBase (ℐ.comap U.ι) ≫ U.ι ≫ f) := by
  have := hπ
  have : Smooth π := inferInstance
  have : Flat π := inferInstance
  obtain ⟨h', hsq⟩ := AlgebraicGeometry.exists_isPullback_blowUpToBase_comap π
    (coordinateSubspaceEmbedding S m n).ker
  have : Etale h' := MorphismProperty.of_isPullback (P := @Etale) hsq hπ
  have : Smooth h' := inferInstance
  have := smooth_blowUp_coordinateSubspaceEmbedding S m n
  rw [hker, ← hπS, ← Category.assoc, hsq.w, Category.assoc]
  infer_instance

/-- Off the centre the blowup morphism is an isomorphism, so there the blowup is smooth over the
base as soon as the ambient scheme is. -/
private theorem smooth_blowUpToBase_restrict_comp_of_compl
    {S X : Scheme.{u}} (f : X ⟶ S) [Smooth f] (ℐ : X.IdealSheafData) (U : X.Opens)
    (hU : (U : Set X) ⊆ (ℐ.support : Set X)ᶜ) :
    Smooth ((blowUpToBase ℐ ∣_ U) ≫ U.ι ≫ f) := by
  have := isIso_blowUpToBase_restrict_of_subset_compl_support ℐ U hU
  have : Smooth (blowUpToBase ℐ ∣_ U) := inferInstance
  infer_instance

/-- Flat base change along an open immersion identifies the blowup of the restricted ideal sheaf
with the restriction of the blowup. -/
private theorem smooth_blowUpToBase_restrict_comp_of_comap
    {S X : Scheme.{u}} (f : X ⟶ S) (ℐ : X.IdealSheafData) (U : X.Opens)
    (h : Smooth (blowUpToBase (ℐ.comap U.ι) ≫ U.ι ≫ f)) :
    Smooth ((blowUpToBase ℐ ∣_ U) ≫ U.ι ≫ f) := by
  obtain ⟨hh, hsq⟩ := AlgebraicGeometry.exists_isPullback_blowUpToBase_comap U.ι ℐ
  have hsq2 := AlgebraicGeometry.isPullback_morphismRestrict (blowUpToBase ℐ) U
  rw [← MorphismProperty.cancel_left_of_respectsIso @Smooth
      (hsq.isoIsPullback _ _ hsq2).hom _, ← Category.assoc,
    IsPullback.isoIsPullback_hom_fst]
  exact h

/-- Every point of the ambient scheme has an open neighbourhood over which the blowup, composed
with the structure morphism to the base, is smooth. -/
@[sga "7 XVIII 2.1" "partial"]
private theorem exists_opens_smooth_blowUpToBase_restrict
    {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X)
    [IsClosedImmersion i] [Smooth f] [Smooth (i ≫ f)] (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ Smooth ((blowUpToBase i.ker ∣_ U) ≫ U.ι ≫ f) := by
  by_cases hx : x ∈ (i.ker.support : Set X)
  · have hrange : (i.ker.support : Set X) = Set.range i := by
      rw [Scheme.Hom.support_ker i, i.isClosedEmbedding.isClosed_range.closure_eq]
    obtain ⟨y, rfl⟩ : ∃ y, i y = x := by rwa [hrange] at hx
    obtain ⟨m, n, U, hyU, π, q, hπ, hπS, hpb⟩ :=
      exists_etale_coordinateSubspaceEmbedding_isPullback f i y
    have hker : i.ker.comap U.ι = (coordinateSubspaceEmbedding S m n).ker.comap π := by
      rw [← AlgebraicGeometry.ker_eq_comap_ker_of_isPullback
          (AlgebraicGeometry.isPullback_morphismRestrict i U),
        ← Scheme.Hom.resLE_eq_morphismRestrict,
        AlgebraicGeometry.ker_eq_comap_ker_of_isPullback hpb]
    exact ⟨U, hyU, smooth_blowUpToBase_restrict_comp_of_comap f i.ker U
      (smooth_blowUpToBase_comap_comp f i.ker U π hπ hπS hker)⟩
  · exact ⟨⟨(i.ker.support : Set X)ᶜ, i.ker.support.isClosed.isOpen_compl⟩, hx,
      smooth_blowUpToBase_restrict_comp_of_compl f i.ker _ le_rfl⟩

/-- **Stacks Project, Tag 0FUT**, first assertion. Let `S` be a scheme and let `i : Z ⟶ X` be a
closed immersion of schemes smooth over `S`. Then the blowup of `X` in `Z` is smooth over `S`. -/
@[stacks 0FUT "smoothness of the blowup",
  sga "7 II 2.1" "more general",
  sga "7 XVIII 2.1" "Smoothness of tilde X",
  sga "7 XVIII 3.1" "more general"]
theorem smooth_blowUpToBase_comp {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X)
    [IsClosedImmersion i] [Smooth f] [Smooth (i ≫ f)] :
    Smooth (blowUpToBase i.ker ≫ f) := by
  choose V hxV hV using exists_opens_smooth_blowUpToBase_restrict f i
  refine IsZariskiLocalAtSource.of_iSup_eq_top
    (fun x : X => blowUpToBase i.ker ⁻¹ᵁ V x) ?_ fun x => ?_
  · rw [eq_top_iff]
    intro t _
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨(blowUpToBase i.ker).base t, hxV ((blowUpToBase i.ker).base t)⟩
  · rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    exact hV x

/-- The blowup of a scheme smooth over `S` in a closed subscheme smooth over `S`, presented by its
quasi-coherent ideal sheaf, is smooth over `S`. -/
@[sga "7 II 2.1" "more general", sga "7 XVIII 2.1" "Smoothness of tilde X"]
theorem smooth_blowUpToBase_comp_of_idealSheafData {S X : Scheme.{u}} (f : X ⟶ S)
    (I : X.IdealSheafData) [Smooth f] [Smooth (I.subschemeι ≫ f)] :
    Smooth (blowUpToBase I ≫ f) := by
  have := smooth_blowUpToBase_comp f I.subschemeι
  rwa [Scheme.IdealSheafData.ker_subschemeι] at this

end Stacks.AlgebraicGeometry

end
