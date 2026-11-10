module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FrobeniusAlphaPCover
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.SmoothTarget
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Syntomic
public import StacksFrontier.AlgebraicGeometry.Morphisms.SmoothMorphisms.Basic
import all StacksFrontier.AlgebraicGeometry.Crystalline.FrobeniusAlphaPCover

/-!
# Local charts of the relative Frobenius of a smooth morphism

Let `S` be a scheme in characteristic `p` and `X` an `S`-scheme smooth of relative dimension `d`,
with Frobenius twist `X^{(p)}` and relative Frobenius `F : X → X^{(p)}` (Stacks, Definition 0CC9).
Around every point of `X^{(p)}` there are an affine open `V ⊆ S`, an affine open `W ⊆ X^{(p)}`
over `V`, and an étale `V`-morphism `α : W → 𝔸^d_V` such that `F` over `W` is the base change
along `α` of the endomorphism `x_i ↦ x_i ^ p` of `𝔸^d_V`. This is the reduction of the proof of
Stacks, Lemma 0FW2 to affine space: the relative Frobenius of `X` is étale locally that of
`𝔸^d_S` (Stacks, Lemmas 054L, 0CCA, 0EBS), and the relative Frobenius of `𝔸^d_S` raises the
coordinates to their `p`-th powers.

## Main results

* `AlgebraicGeometry.exists_isPullback_relativeFrobenius_affineSpace`: the chart.

## References

* [Stacks Project, Tag 0FW2](https://stacks.math.columbia.edu/tag/0FW2)
* [Stacks Project, Tag 0EBS](https://stacks.math.columbia.edu/tag/0EBS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

section Chart

/-- An open immersion of `S`-schemes twists to an open immersion. -/
private theorem isOpenImmersion_frobeniusTwist_map (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) {X₁ X : Over S} (i : X₁ ⟶ X) [IsOpenImmersion i.left] :
    IsOpenImmersion ((frobeniusTwist S p hS).map i).left :=
  MorphismProperty.of_isPullback (isPullback_frobeniusTwist_map S p hS i).flip inferInstance

/-- Over the image of the twist of an open immersion `i : X₁ ⟶ X`, the relative Frobenius of `X`
is the relative Frobenius of `X₁`. -/
private theorem exists_iso_relativeFrobenius_restrict_opensRange (S : Scheme.{u}) (p : ℕ)
    [Fact p.Prime] (hS : IsInCharacteristic S p) {X₁ X : Over S} (i : X₁ ⟶ X)
    [IsOpenImmersion i.left] [IsOpenImmersion ((frobeniusTwist S p hS).map i).left] :
    ∃ eX : ((relativeFrobenius S p hS X).left ⁻¹ᵁ
        ((frobeniusTwist S p hS).map i).left.opensRange).toScheme ≅ X₁.left,
      (relativeFrobenius S p hS X).left ∣_ ((frobeniusTwist S p hS).map i).left.opensRange =
        eX.hom ≫ (relativeFrobenius S p hS X₁).left ≫
          ((frobeniusTwist S p hS).map i).left.isoOpensRange.hom := by
  let j := ((frobeniusTwist S p hS).map i).left
  have hsq : IsPullback ((relativeFrobenius S p hS X₁).left ≫ j.isoOpensRange.hom)
      i.left j.opensRange.ι (relativeFrobenius S p hS X).left := by
    apply (isPullback_relativeFrobenius_of_etale S p hS i).of_iso (Iso.refl _) j.isoOpensRange
      (Iso.refl _) (Iso.refl _) <;>
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    exact j.isoOpensRange_hom_ι.symm
  have hr := isPullback_morphismRestrict (relativeFrobenius S p hS X).left j.opensRange
  exact ⟨hr.isoIsPullback _ _ hsq, (hr.isoIsPullback_hom_fst _ _ hsq).symm⟩

/-- For `π : X₀ ⟶ 𝔸ⁿ_T` étale over `T` in characteristic `p`, the relative Frobenius of `X₀` is
the base change along an étale `T`-morphism from the twist of `X₀` to `𝔸ⁿ_T` of `x_i ↦ x_i ^ p`. -/
private theorem exists_isPullback_relativeFrobenius_of_etale_affineSpace (T : Scheme.{u}) (p : ℕ)
    [Fact p.Prime] (hT : IsInCharacteristic T p) (n : Type u) {X₀ : Over T}
    (π : X₀ ⟶ Over.mk (𝔸(n; T) ↘ T)) [Etale π.left] :
    ∃ φ : ((frobeniusTwist T p hT).obj X₀).left ⟶ 𝔸(n; T),
      Etale φ ∧ φ ≫ 𝔸(n; T) ↘ T = ((frobeniusTwist T p hT).obj X₀).hom ∧
      IsPullback π.left (relativeFrobenius T p hT X₀).left
        (AffineSpace.homOfVector (𝔸(n; T) ↘ T) fun i => AffineSpace.coord T i ^ p) φ := by
  let πp := ((frobeniusTwist T p hT).map π).left
  let tA := affineSpaceFrobeniusTwistIso n T p hT
  have : Etale πp :=
    MorphismProperty.of_isPullback (isPullback_frobeniusTwist_map T p hT π).flip inferInstance
  have hFA : (relativeFrobenius T p hT (Over.mk (𝔸(n; T) ↘ T))).left ≫ tA.inv =
      affineSpacePower n T p := by
    rw [relativeFrobenius_affineSpace, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have htA : tA.inv ≫ 𝔸(n; T) ↘ T = pullback.snd (𝔸(n; T) ↘ T) (absoluteFrobenius T p hT) := by
    rw [Iso.inv_comp_eq, affineSpaceFrobeniusTwistIso_hom_snd]
  have h : IsPullback π.left (relativeFrobenius T p hT X₀).left (affineSpacePower n T p)
      (πp ≫ tA.inv) :=
    (isPullback_relativeFrobenius_of_etale T p hT π).flip.of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) tA.symm
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
      (by simpa using hFA)
      (by simp only [Iso.refl_hom, Iso.symm_hom, Category.id_comp]; rfl)
  refine ⟨πp ≫ tA.inv, inferInstance, ?_, h⟩
  rw [Category.assoc, htA]
  exact ((frobeniusTwist T p hT).map π).w

variable (S : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic S p) (X : Over S)
  (d : ℕ) [SmoothOfRelativeDimension d X.hom]

/-- **The relative Frobenius of a smooth morphism is locally a base change of the Frobenius of
affine space.** Let `X` be smooth of relative dimension `d` over `S` in characteristic `p`. Every
point of the Frobenius twist `X^{(p)}` lies in an affine open `W` over an affine open `V` of `S`
with an étale `V`-morphism `α : W → 𝔸^d_V` and a morphism `β : F⁻¹W → 𝔸^d_V` exhibiting
`F ∣_ W : F⁻¹W → W` as the base change along `α` of `x_i ↦ x_i ^ p`. -/
theorem exists_isPullback_relativeFrobenius_affineSpace
    (x : ((frobeniusTwist S p hS).obj X).left) :
    ∃ (V : S.Opens) (_ : IsAffineOpen V) (W : ((frobeniusTwist S p hS).obj X).left.Opens)
      (_ : IsAffineOpen W) (_ : x ∈ W) (hWV : W ≤ ((frobeniusTwist S p hS).obj X).hom ⁻¹ᵁ V)
      (α : W.toScheme ⟶ 𝔸(ULift.{u} (Fin d); V.toScheme))
      (β : ((relativeFrobenius S p hS X).left ⁻¹ᵁ W).toScheme ⟶
        𝔸(ULift.{u} (Fin d); V.toScheme)),
      Etale α ∧
      α ≫ 𝔸(ULift.{u} (Fin d); V.toScheme) ↘ V.toScheme =
        ((frobeniusTwist S p hS).obj X).hom.resLE V W hWV ∧
      IsPullback β ((relativeFrobenius S p hS X).left ∣_ W)
        (AffineSpace.homOfVector (𝔸(ULift.{u} (Fin d); V.toScheme) ↘ V.toScheme)
          fun i => AffineSpace.coord V.toScheme i ^ p) α := by
  obtain ⟨x', hx'⟩ := relativeFrobenius_surjective S p hS X x
  obtain ⟨V, hV, U, hU, hxU, hUV, π, hπ, hcomm⟩ := exists_etale_affineSpace_chart X.hom d x'
  have : IsAffine V.toScheme := hV
  have : IsAffine U.toScheme := hU
  have hV' : IsInCharacteristic V.toScheme p := isInCharacteristic_of_hom V.ι p hS
  let X₀ : Over V.toScheme := Over.mk (X.hom.resLE V U hUV)
  let π₀ : X₀ ⟶ Over.mk (𝔸(ULift.{u} (Fin d); V.toScheme) ↘ V.toScheme) := Over.homMk π hcomm
  have : Etale π₀.left := hπ
  obtain ⟨φ, _, hφ, h₂⟩ :=
    exists_isPullback_relativeFrobenius_of_etale_affineSpace V.toScheme p hV' _ π₀
  let e := frobeniusTwistBaseIso V.ι p hS X₀
  let X₁ : Over S := Over.mk (X₀.hom ≫ V.ι)
  have hsndV : pullback.snd (X₀.hom ≫ V.ι) (absoluteFrobenius S p hS) =
      e.inv ≫ ((frobeniusTwist V.toScheme p hV').obj X₀).hom ≫ V.ι :=
    (Iso.eq_inv_comp e).mpr
      ((IsPullback.of_hasPullback X₀.hom (absoluteFrobenius V.toScheme p hV')).paste_vert
        (isPullback_absoluteFrobenius_of_etale V.ι p hS)).isoPullback_hom_snd
  let i : X₁ ⟶ X := Over.homMk U.ι (by simp [X₁, X₀])
  have : IsOpenImmersion i.left := inferInstanceAs (IsOpenImmersion U.ι)
  let j := ((frobeniusTwist S p hS).map i).left
  have : IsOpenImmersion j := isOpenImmersion_frobeniusTwist_map S p hS i
  have hi := isPullback_relativeFrobenius_of_etale S p hS i
  obtain ⟨eX, hF⟩ := exists_iso_relativeFrobenius_restrict_opensRange S p hS i
  have hjg : j ≫ ((frobeniusTwist S p hS).obj X).hom =
      pullback.snd (X₀.hom ≫ V.ι) (absoluteFrobenius S p hS) :=
    ((frobeniusTwist S p hS).map i).w
  have hWV : j.opensRange ≤ ((frobeniusTwist S p hS).obj X).hom ⁻¹ᵁ V := by
    rintro _ ⟨z, rfl⟩
    change (j ≫ ((frobeniusTwist S p hS).obj X).hom) z ∈ V
    rw [hjg, hsndV, ← Category.assoc, Scheme.Hom.comp_apply]
    exact ((e.inv ≫ ((frobeniusTwist V.toScheme p hV').obj X₀).hom) z).2
  have : IsAffine ((frobeniusTwist S p hS).obj X₁).left := by
    have : IsAffine ((frobeniusTwist V.toScheme p hV').obj X₀).left := by
      change IsAffine (pullback (X.hom.resLE V U hUV) _)
      infer_instance
    exact IsAffine.of_isIso e.inv
  refine ⟨V, hV, j.opensRange, isAffineOpen_opensRange j, ?_, hWV,
    j.isoOpensRange.inv ≫ e.inv ≫ φ, eX.hom ≫ π, inferInstance, ?_, ?_⟩
  · change x ∈ Set.range j
    exact ⟨(relativeFrobenius S p hS X₁).left ⟨x', hxU⟩,
      (congrArg (fun k : U.toScheme ⟶ ((frobeniusTwist S p hS).obj X).left =>
        k ⟨x', hxU⟩) hi.w).trans hx'⟩
  · rw [← cancel_mono V.ι, Scheme.Hom.resLE_comp_ι]
    simp only [Category.assoc, reassoc_of% hφ]
    rw [← hsndV, ← hjg, ← Category.assoc j.isoOpensRange.inv,
      j.isoOpensRange.inv_comp_eq.mpr j.isoOpensRange_hom_ι.symm]
  · refine h₂.of_iso eX.symm (Iso.refl _) (e ≪≫ j.isoOpensRange) (Iso.refl _) (by simp [π₀]) ?_
      (by simp) (by simp)
    rw [hF, ← relativeFrobenius_comp_frobeniusTwistBaseIso V.ι p hS X₀]
    simp only [Iso.symm_hom, Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]
    rfl

end Chart

/-! ### The universal Frobenius of affine space -/

section Universal

variable (n : Type u) (p : ℕ)

/-- **The universal Frobenius of affine space**: the endomorphism of `Spec ℤ[x_i : i ∈ n]` given by
`x_i ↦ x_i ^ p` (`MvPolynomial.expand p`). -/
noncomputable abbrev specExpand :
    Spec (CommRingCat.of (MvPolynomial n (ULift.{u} ℤ))) ⟶
      Spec (CommRingCat.of (MvPolynomial n (ULift.{u} ℤ))) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.expand (σ := n) (R := ULift.{u} ℤ) p).toRingHom)

/-- Raising the coordinates of `𝔸ⁿ_V` to their `p`-th powers covers the universal Frobenius
along `𝔸ⁿ_V → Spec ℤ[n]`. -/
theorem toSpecMvPoly_comp_specExpand (V : Scheme.{u}) :
    AffineSpace.toSpecMvPoly n V ≫ specExpand n p =
      AffineSpace.homOfVector (𝔸(n; V) ↘ V) (fun i => AffineSpace.coord V i ^ p) ≫
        AffineSpace.toSpecMvPoly n V := by
  apply (AffineSpace.toSpecMvPolyIntEquiv n).injective
  funext i
  rw [AffineSpace.toSpecMvPolyIntEquiv_comp, AffineSpace.toSpecMvPolyIntEquiv_comp]
  have h1 : AffineSpace.toSpecMvPolyIntEquiv n (AffineSpace.toSpecMvPoly n V) i =
      AffineSpace.coord V i := rfl
  have h2 : (specExpand n p).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial n (ULift.{u} ℤ)))).inv (MvPolynomial.X i)) =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial n (ULift.{u} ℤ)))).inv
        (MvPolynomial.X i ^ p) := by
    have := congrArg (fun φ => φ (MvPolynomial.X i))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
        (MvPolynomial.expand (σ := n) (R := ULift.{u} ℤ) p).toRingHom))
    change (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial n (ULift.{u} ℤ)))).inv
        (MvPolynomial.expand p (MvPolynomial.X i)) =
      (specExpand n p).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial n (ULift.{u} ℤ)))).inv
          (MvPolynomial.X i)) at this
    rw [MvPolynomial.expand_X] at this
    exact this.symm
  rw [h1, AffineSpace.homOfVector_appTop_coord, AffineSpace.toSpecMvPolyIntEquiv_apply, h2,
    map_pow, map_pow, ← AffineSpace.toSpecMvPolyIntEquiv_apply, h1]

/-- **`x_i ↦ x_i ^ p` on `𝔸ⁿ_V` is the base change of the universal Frobenius** along
`𝔸ⁿ_V → Spec ℤ[n]`. -/
theorem isPullback_specExpand (V : Scheme.{u}) :
    IsPullback (AffineSpace.toSpecMvPoly n V)
      (AffineSpace.homOfVector (𝔸(n; V) ↘ V) (fun i => AffineSpace.coord V i ^ p))
      (specExpand n p) (AffineSpace.toSpecMvPoly n V) := by
  have hB : IsPullback (AffineSpace.toSpecMvPoly n V) (𝔸(n; V) ↘ V)
      (terminal.from (Spec (CommRingCat.of (MvPolynomial n (ULift.{u} ℤ)))))
      (terminal.from V) :=
    (IsPullback.of_hasPullback (terminal.from V)
      (terminal.from (Spec (CommRingCat.of (MvPolynomial n (ULift.{u} ℤ)))))).flip
  exact IsPullback.of_bot (by rwa [AffineSpace.homOfVector_over, terminal.comp_from])
    (toSpecMvPoly_comp_specExpand n p V) hB

/-- The universal Frobenius is finite and flat on rings, being free of finite rank. -/
private theorem finite_and_flat_expand_toRingHom [Finite n] (hp : p ≠ 0) :
    (MvPolynomial.expand (σ := n) (R := ULift.{u} ℤ) p).toRingHom.Finite ∧
      (MvPolynomial.expand (σ := n) (R := ULift.{u} ℤ) p).toRingHom.Flat := by
  have := Fintype.ofFinite n
  obtain ⟨b⟩ := hasFiniteBasis_expand n (ULift.{u} ℤ) p hp
  let := (MvPolynomial.expand (σ := n) (R := ULift.{u} ℤ) p).toRingHom.toAlgebra
  let : Module (MvPolynomial n (ULift.{u} ℤ)) (MvPolynomial n (ULift.{u} ℤ)) := Algebra.toModule
  have : Module.Free _ _ := Module.Free.of_basis b
  exact ⟨Module.Finite.of_basis b, Module.Flat.of_free⟩

/-- The universal Frobenius has a basis of `p ^ #n` elements on global sections. -/
theorem hasFiniteBasis_specExpand_appTop [Fintype n] (hp : p ≠ 0) :
    HasFiniteBasis (specExpand n p).appTop.hom (p ^ Fintype.card n) :=
  hasFiniteBasis_spec_appTop _ _ (hasFiniteBasis_expand n (ULift.{u} ℤ) p hp)

variable [Finite n]

/-- The universal Frobenius is finite. -/
theorem isFinite_specExpand (hp : p ≠ 0) : IsFinite (specExpand n p) := by
  rw [IsFinite.SpecMap_iff, CommRingCat.hom_ofHom]
  exact (finite_and_flat_expand_toRingHom n p hp).1

/-- The universal Frobenius is flat. -/
theorem flat_specExpand (hp : p ≠ 0) : Flat (specExpand n p) := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat), CommRingCat.hom_ofHom]
  exact (finite_and_flat_expand_toRingHom n p hp).2

/-- **The universal Frobenius is syntomic**: it is flat, and a local complete intersection by
Stacks 069M, its composition with the smooth `Spec ℤ[n] → Spec ℤ` being that smooth map. -/
theorem syntomic_specExpand (hp : p ≠ 0) : Syntomic (specExpand n p) := by
  let s : Spec (CommRingCat.of (MvPolynomial n (ULift.{u} ℤ))) ⟶
      Spec (CommRingCat.of (ULift.{u} ℤ)) :=
    Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) (MvPolynomial n (ULift.{u} ℤ))))
  have hs : Smooth s := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth), CommRingCat.hom_ofHom]
    exact RingHom.smooth_algebraMap.mpr
      (Algebra.Smooth.mk inferInstance inferInstance :
        Algebra.Smooth (ULift.{u} ℤ) (MvPolynomial n (ULift.{u} ℤ)))
  have hcomp : specExpand n p ≫ s = s := by
    rw [specExpand, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (MvPolynomial.expand (σ := n) (R := ULift.{u} ℤ) p).comp_algebraMap
  have hlci : IsLocalCompleteIntersectionMorphism (specExpand n p ≫ s) := by
    rw [hcomp]
    exact isLocalCompleteIntersectionMorphism_of_syntomic (syntomic_of_smooth s)
  exact syntomic_of_flat_of_isLocalCompleteIntersectionMorphism (flat_specExpand n p hp)
    (isLocalCompleteIntersectionMorphism_of_comp_of_smooth _ s hlci)

end Universal

end AlgebraicGeometry
