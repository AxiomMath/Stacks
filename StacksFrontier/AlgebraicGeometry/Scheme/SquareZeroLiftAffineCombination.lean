module

public import Mathlib.AlgebraicGeometry.Stalk
public import StacksFrontier.RingTheory.Smooth.SquareZeroLiftCombination

/-!
# Affine combinations of morphisms out of the spectrum of a local ring

Let `B` be a local ring and `I ⊆ B` an ideal with `I ^ 2 = 0`. A morphism of schemes
`ℓ : Spec B ⟶ Z` is the same as a point `z` of `Z` together with a local ring map
`𝒪_{Z,z} → B` (`AlgebraicGeometry.SpecToEquivOfLocalRing`). Morphisms which agree on
`Spec (B ⧸ I)` send the closed point to the same point `z`, and their ring maps agree modulo
`I`; so an affine combination `∑ cᵢ ℓᵢ` with coefficients `cᵢ ∈ B` summing to `1` is defined, by
`Stacks.SquareZeroLift.affineCombinationRingHom`, as a morphism `Spec B ⟶ Z`.

This affine structure on infinitesimal lifts is canonical: it is compatible with composition by any
morphism `Z ⟶ W` and with automorphisms of `B` preserving `I`.

## Main definitions

* `AlgebraicGeometry.SquareZeroLift.stalkAt`: the local ring map `𝒪_{Z,z} → B` of a morphism
  `Spec B ⟶ Z` sending the closed point to `z`.
* `AlgebraicGeometry.SquareZeroLift.affineComb`: the affine combination of a family of
  morphisms `Spec B ⟶ Z` agreeing on `Spec (B ⧸ I)`.

## Main results

* `AlgebraicGeometry.SquareZeroLift.affineComb_comp`: compatibility with postcomposition.
* `AlgebraicGeometry.SquareZeroLift.specMap_comp_affineComb`: compatibility with a ring
  automorphism of `B` preserving `I`, acting on the coefficients.
* `AlgebraicGeometry.SquareZeroLift.reduction_comp_affineComb`: the combination agrees with the
  family on `Spec (B ⧸ I)`.
* `AlgebraicGeometry.SquareZeroLift.affineComb_const`: the combination of a constant family is
  its member.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.SquareZeroLift

variable {B : CommRingCat.{u}} [IsLocalRing B] {Z W : Scheme.{u}}

/-- The local ring map `𝒪_{Z,z} → B` of a morphism `Spec B ⟶ Z` sending the closed point to
`z`: the map `AlgebraicGeometry.Scheme.stalkClosedPointTo`, read at the prescribed point. -/
noncomputable def stalkAt (ℓ : Spec (B) ⟶ Z) {z : Z}
    (h : ℓ (closedPoint (B)) = z) : Z.presheaf.stalk z ⟶ B :=
  (Z.presheaf.stalkCongr (.of_eq h)).inv ≫ Scheme.stalkClosedPointTo ℓ

/-- The map `AlgebraicGeometry.SquareZeroLift.stalkAt ℓ h` is a local ring map. -/
instance isLocalHom_stalkAt (ℓ : Spec (B) ⟶ Z) {z : Z}
    (h : ℓ (closedPoint (B)) = z) : IsLocalHom (stalkAt ℓ h).hom := by
  subst h
  simp only [stalkAt, TopCat.Presheaf.stalkCongr_inv, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp]
  infer_instance

/-- A morphism `ℓ : Spec B ⟶ Z` factors as `Spec` of its local ring map at `z` followed by
`Z.fromSpecStalk z`. -/
theorem spec_stalkAt (ℓ : Spec (B) ⟶ Z) {z : Z}
    (h : ℓ (closedPoint (B)) = z) :
    Spec.map (stalkAt ℓ h) ≫ Z.fromSpecStalk z = ℓ := by
  subst h
  simp only [stalkAt, TopCat.Presheaf.stalkCongr_inv, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp]
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk ℓ

/-- The local ring map of `Spec φ ≫ Z.fromSpecStalk z` at `z` is `φ`. -/
theorem stalkAt_eq {z : Z} (φ : Z.presheaf.stalk z ⟶ B) [IsLocalHom φ.hom]
    (h : (Spec.map φ ≫ Z.fromSpecStalk z) (closedPoint (B)) = z) :
    stalkAt (Spec.map φ ≫ Z.fromSpecStalk z) h = φ := by
  have key := (SpecToEquivOfLocalRing Z (B)).apply_symm_apply ⟨z, φ, inferInstance⟩
  obtain ⟨h₁, h₂⟩ := SpecToEquivOfLocalRing_eq_iff.mp key
  have h₂' : Scheme.stalkClosedPointTo (Spec.map φ ≫ Z.fromSpecStalk z) =
      (Z.presheaf.stalkCongr (.of_eq h)).hom ≫ φ := h₂
  rw [stalkAt, h₂', Iso.inv_hom_id_assoc]

/-- `AlgebraicGeometry.SquareZeroLift.stalkAt` depends only on the morphism. -/
theorem stalkAt_congr {ℓ ℓ' : Spec B ⟶ Z} (e : ℓ = ℓ') {z : Z}
    (h : ℓ (closedPoint B) = z) (h' : ℓ' (closedPoint B) = z) :
    stalkAt ℓ h = stalkAt ℓ' h' := by
  subst e
  rfl

/-- Two morphisms with the same local ring map at the same point are equal. -/
theorem eq_of_stalkAt_eq {ℓ ℓ' : Spec (B) ⟶ Z} {z : Z}
    (h : ℓ (closedPoint (B)) = z) (h' : ℓ' (closedPoint (B)) = z)
    (he : stalkAt ℓ h = stalkAt ℓ' h') : ℓ = ℓ' := by
  rw [← spec_stalkAt ℓ h, ← spec_stalkAt ℓ' h', he]

/-- The local ring map of a composite is the stalk map followed by the local ring map. -/
theorem stalkAt_comp (ℓ : Spec (B) ⟶ Z) {z : Z}
    (h : ℓ (closedPoint (B)) = z) (g : Z ⟶ W) :
    stalkAt (ℓ ≫ g) (show (ℓ ≫ g) (closedPoint B) = g z by
        rw [← h]; rfl) =
      g.stalkMap z ≫ stalkAt ℓ h := by
  subst h
  simp only [stalkAt, TopCat.Presheaf.stalkCongr_inv, Scheme.stalkClosedPointTo_comp,
    TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
  exact (congrArg (· ≫ _) (TopCat.Presheaf.stalkSpecializes_refl W.presheaf _)).trans
    (Category.id_comp _)

/-- The local ring map of `Spec ρ ≫ ℓ` is the local ring map of `ℓ` followed by `ρ`. -/
theorem stalkAt_specMap_comp {B' : CommRingCat.{u}} [IsLocalRing B']
    (ρ : B ⟶ B') [IsLocalHom ρ.hom]
    (ℓ : Spec (B) ⟶ Z) {z : Z} (h : ℓ (closedPoint (B)) = z)
    (h' : (Spec.map ρ ≫ ℓ) (closedPoint (B')) = z) :
    stalkAt (Spec.map ρ ≫ ℓ) h' = stalkAt ℓ h ≫ ρ := by
  have : IsLocalHom (stalkAt ℓ h ≫ ρ).hom := by
    rw [CommRingCat.hom_comp]; infer_instance
  have hρ : Spec.map ρ ≫ ℓ = Spec.map (stalkAt ℓ h ≫ ρ) ≫ Z.fromSpecStalk z := by
    rw [Spec.map_comp, Category.assoc, spec_stalkAt]
  have h'' : (Spec.map (stalkAt ℓ h ≫ ρ) ≫ Z.fromSpecStalk z)
      (closedPoint (B')) = z := by rw [← hρ]; exact h'
  exact (stalkAt_congr hρ h' h'').trans (stalkAt_eq (stalkAt ℓ h ≫ ρ) h'')

variable (I : Ideal B) (hI : I ^ 2 = ⊥)

/-- The reduction `Spec (B ⧸ I) ⟶ Spec B`. -/
noncomputable abbrev reduction : Spec (CommRingCat.of (B ⧸ I)) ⟶ Spec (B) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))

include hI in
/-- An ideal of square zero in a local ring is proper. -/
theorem ne_top_of_sq_eq_bot : I ≠ ⊤ := by
  rintro rfl
  have : (1 : B) ∈ (⊤ : Ideal B) ^ 2 := by rw [Ideal.top_pow]; exact Submodule.mem_top
  rw [hI, Ideal.mem_bot] at this
  exact one_ne_zero this

include hI in
/-- The quotient of a local ring by an ideal of square zero is a local ring. -/
theorem isLocalRing_quotient : IsLocalRing (B ⧸ I) :=
  have : Nontrivial (B ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_sq_eq_bot I hI)
  IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

omit [IsLocalRing B] in
include hI in
/-- Every element of an ideal of square zero is nilpotent. -/
theorem mem_nilradical_of_mem {x : B} (hx : x ∈ I) : IsNilpotent x :=
  ⟨2, by
    have : x ^ 2 ∈ I ^ 2 := Ideal.pow_mem_pow hx 2
    simpa [hI] using this⟩

include hI in
/-- A morphism `Spec B ⟶ Z` sends the closed point where its restriction to `Spec (B ⧸ I)` sends
the closed point. -/
theorem apply_closedPoint_eq (ℓ : Spec (B) ⟶ Z) :
    letI := isLocalRing_quotient I hI
    (reduction I ≫ ℓ) (closedPoint (CommRingCat.of (B ⧸ I))) =
      ℓ (closedPoint (B)) := by
  let := isLocalRing_quotient I hI
  have : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have : IsLocalHom (CommRingCat.ofHom (Ideal.Quotient.mk I)).hom := ‹_›
  show ℓ ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) (closedPoint _)) = _
  rw [Spec_closedPoint]

/-- The local ring map of `reduction I ≫ ℓ` is that of `ℓ` followed by the quotient map. -/
private theorem stalkAt_reduction_comp [IsLocalRing (B ⧸ I)] (ℓ : Spec B ⟶ Z) {z : Z}
    (h : ℓ (closedPoint B) = z)
    (h' : (reduction I ≫ ℓ) (closedPoint (CommRingCat.of (B ⧸ I))) = z) :
    stalkAt (reduction I ≫ ℓ) h' = stalkAt ℓ h ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) := by
  have : IsLocalHom (CommRingCat.ofHom (Ideal.Quotient.mk I)).hom :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  exact stalkAt_specMap_comp _ ℓ h h'

include hI in
/-- Two morphisms `Spec B ⟶ Z` agreeing on `Spec (B ⧸ I)` have local ring maps agreeing
modulo `I`. -/
theorem stalkAt_sub_mem {ℓ ℓ' : Spec (B) ⟶ Z} {z : Z}
    (h : ℓ (closedPoint (B)) = z) (h' : ℓ' (closedPoint (B)) = z)
    (he : reduction I ≫ ℓ = reduction I ≫ ℓ') (x : Z.presheaf.stalk z) :
    (stalkAt ℓ h).hom x - (stalkAt ℓ' h').hom x ∈ I := by
  let := isLocalRing_quotient I hI
  have hz : (reduction I ≫ ℓ) (closedPoint (CommRingCat.of (B ⧸ I))) = z := by
    rw [apply_closedPoint_eq I hI, h]
  have hz' : (reduction I ≫ ℓ') (closedPoint (CommRingCat.of (B ⧸ I))) = z := by
    rw [apply_closedPoint_eq I hI, h']
  have e3 : stalkAt (reduction I ≫ ℓ) hz = stalkAt (reduction I ≫ ℓ') hz' := by
    simp only [he]
  rw [stalkAt_reduction_comp I ℓ h, stalkAt_reduction_comp I ℓ' h'] at e3
  have := congrArg (fun g => g.hom x) e3
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  rw [← Ideal.Quotient.eq]
  exact this

variable {ι : Type*} [Fintype ι]

/-- The ring map underlying an affine combination: `x ↦ ∑ cᵢ φᵢ x` at the stalk. -/
noncomputable def affineCombStalk (ℓ : ι → (Spec (B) ⟶ Z)) (z : Z)
    (hz : ∀ i, ℓ i (closedPoint (B)) = z) (c : ι → B) (hc : ∑ i, c i = 1)
    (i₀ : ι) (he : ∀ i, reduction I ≫ ℓ i = reduction I ≫ ℓ i₀) :
    Z.presheaf.stalk z ⟶ B :=
  CommRingCat.ofHom (Stacks.SquareZeroLift.affineCombinationRingHom I hI Finset.univ c hc i₀
    (fun i => (stalkAt (ℓ i) (hz i)).hom)
    (fun i _ x => stalkAt_sub_mem I hI (hz i) (hz i₀) (he i) x))

/-- The ring map `AlgebraicGeometry.SquareZeroLift.affineCombStalk` sends `x` to `∑ cᵢ φᵢ x`, the
`φᵢ` being the local ring maps of the `ℓᵢ`. -/
theorem affineCombStalk_apply (ℓ : ι → (Spec (B) ⟶ Z)) (z : Z)
    (hz : ∀ i, ℓ i (closedPoint (B)) = z) (c : ι → B) (hc : ∑ i, c i = 1)
    (i₀ : ι) (he : ∀ i, reduction I ≫ ℓ i = reduction I ≫ ℓ i₀) (x : Z.presheaf.stalk z) :
    (affineCombStalk I hI ℓ z hz c hc i₀ he).hom x = ∑ i, c i * (stalkAt (ℓ i) (hz i)).hom x :=
  rfl

/-- The ring map `AlgebraicGeometry.SquareZeroLift.affineCombStalk` is a local ring map. -/
instance isLocalHom_affineCombStalk (ℓ : ι → (Spec (B) ⟶ Z)) (z : Z)
    (hz : ∀ i, ℓ i (closedPoint (B)) = z) (c : ι → B) (hc : ∑ i, c i = 1)
    (i₀ : ι) (he : ∀ i, reduction I ≫ ℓ i = reduction I ≫ ℓ i₀) :
    IsLocalHom (affineCombStalk I hI ℓ z hz c hc i₀ he).hom := by
  refine ⟨fun x hx => ?_⟩
  have hmem := Stacks.SquareZeroLift.affineCombinationRingHom_sub_mem I hI Finset.univ c hc i₀
    (fun i => (stalkAt (ℓ i) (hz i)).hom)
    (fun i _ x => stalkAt_sub_mem I hI (hz i) (hz i₀) (he i) x) x
  have hnil := mem_nilradical_of_mem I hI hmem
  have hunit : IsUnit ((stalkAt (ℓ i₀) (hz i₀)).hom x) := by
    have h := hnil.neg.isUnit_add_left_of_commute hx (Commute.all _ _)
    have he : (affineCombStalk I hI ℓ z hz c hc i₀ he).hom x +
        -(Stacks.SquareZeroLift.affineCombinationRingHom I hI Finset.univ c hc i₀
          (fun i => (stalkAt (ℓ i) (hz i)).hom)
          (fun i _ x => stalkAt_sub_mem I hI (hz i) (hz i₀) (he i) x) x -
          (stalkAt (ℓ i₀) (hz i₀)).hom x) = (stalkAt (ℓ i₀) (hz i₀)).hom x := by
      rw [affineCombStalk_apply, Stacks.SquareZeroLift.affineCombinationRingHom_apply]
      ring
    rwa [he] at h
  exact isUnit_of_map_unit _ _ hunit

/-- **The affine combination `∑ cᵢ ℓᵢ` of morphisms `Spec B ⟶ Z` agreeing on `Spec (B ⧸ I)`**,
for coefficients `cᵢ ∈ B` summing to `1`: the morphism whose local ring map at the common image
`z` of the closed point is `∑ cᵢ φᵢ`, the `φᵢ` being the local ring maps of the `ℓᵢ`. -/
noncomputable def affineComb (ℓ : ι → (Spec B ⟶ Z)) (z : Z)
    (hz : ∀ i, ℓ i (closedPoint B) = z) (c : ι → B) (hc : ∑ i, c i = 1)
    (i₀ : ι) (he : ∀ i, reduction I ≫ ℓ i = reduction I ≫ ℓ i₀) : Spec B ⟶ Z :=
  Spec.map (affineCombStalk I hI ℓ z hz c hc i₀ he) ≫ Z.fromSpecStalk z

variable {I hI}

/-- An affine combination sends the closed point of `Spec B` to the common point `z`. -/
theorem affineComb_apply_closedPoint (ℓ : ι → (Spec B ⟶ Z)) (z : Z)
    (hz : ∀ i, ℓ i (closedPoint B) = z) (c : ι → B) (hc : ∑ i, c i = 1)
    (i₀ : ι) (he : ∀ i, reduction I ≫ ℓ i = reduction I ≫ ℓ i₀) :
    affineComb I hI ℓ z hz c hc i₀ he (closedPoint B) = z := by
  show Z.fromSpecStalk z ((Spec.map (affineCombStalk I hI ℓ z hz c hc i₀ he)) _) = z
  rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

/-- The local ring map of an affine combination is
`AlgebraicGeometry.SquareZeroLift.affineCombStalk`. -/
theorem stalkAt_affineComb (ℓ : ι → (Spec B ⟶ Z)) (z : Z)
    (hz : ∀ i, ℓ i (closedPoint B) = z) (c : ι → B) (hc : ∑ i, c i = 1)
    (i₀ : ι) (he : ∀ i, reduction I ≫ ℓ i = reduction I ≫ ℓ i₀) :
    stalkAt (affineComb I hI ℓ z hz c hc i₀ he) (affineComb_apply_closedPoint ℓ z hz c hc i₀ he) =
      affineCombStalk I hI ℓ z hz c hc i₀ he :=
  stalkAt_eq _ _

/-- Two affine combinations at the same point whose ring maps agree are equal; in particular an
affine combination does not depend on the choice of base member. -/
theorem affineComb_eq_of_apply {κ : Type*} [Fintype κ]
    (ℓ : ι → (Spec B ⟶ Z)) (z : Z)
    (hz : ∀ i, ℓ i (closedPoint B) = z) (c : ι → B) (hc : ∑ i, c i = 1)
    (i₀ : ι) (he : ∀ i, reduction I ≫ ℓ i = reduction I ≫ ℓ i₀)
    (ℓ' : κ → (Spec B ⟶ Z))
    (hz' : ∀ i, ℓ' i (closedPoint B) = z) (c' : κ → B) (hc' : ∑ i, c' i = 1)
    (i₀' : κ) (he' : ∀ i, reduction I ≫ ℓ' i = reduction I ≫ ℓ' i₀')
    (hval : ∀ x, ∑ i, c i * (stalkAt (ℓ i) (hz i)).hom x =
      ∑ i, c' i * (stalkAt (ℓ' i) (hz' i)).hom x) :
    affineComb I hI ℓ z hz c hc i₀ he = affineComb I hI ℓ' z hz' c' hc' i₀' he' := by
  refine eq_of_stalkAt_eq (affineComb_apply_closedPoint ℓ z hz c hc i₀ he)
    (affineComb_apply_closedPoint ℓ' z hz' c' hc' i₀' he') ?_
  rw [stalkAt_affineComb, stalkAt_affineComb]
  ext x
  exact hval x

/-- An affine combination of a constant family is its member. -/
theorem affineComb_const (ℓ₀ : Spec B ⟶ Z) (z : Z) (hz : ℓ₀ (closedPoint B) = z)
    (c : ι → B) (hc : ∑ i, c i = 1) (i₀ : ι) :
    affineComb I hI (fun _ => ℓ₀) z (fun _ => hz) c hc i₀ (fun _ => rfl) = ℓ₀ := by
  refine eq_of_stalkAt_eq (affineComb_apply_closedPoint _ z _ c hc i₀ _) hz ?_
  rw [stalkAt_affineComb]
  ext x
  rw [affineCombStalk_apply, ← Finset.sum_mul, hc, one_mul]

/-- **An affine combination agrees with the family on `Spec (B ⧸ I)`.** -/
theorem reduction_comp_affineComb (ℓ : ι → (Spec B ⟶ Z)) (z : Z)
    (hz : ∀ i, ℓ i (closedPoint B) = z) (c : ι → B) (hc : ∑ i, c i = 1)
    (i₀ : ι) (he : ∀ i, reduction I ≫ ℓ i = reduction I ≫ ℓ i₀) :
    reduction I ≫ affineComb I hI ℓ z hz c hc i₀ he = reduction I ≫ ℓ i₀ := by
  let := isLocalRing_quotient I hI
  have h₁ : (reduction I ≫ affineComb I hI ℓ z hz c hc i₀ he)
      (closedPoint (CommRingCat.of (B ⧸ I))) = z := by
    rw [apply_closedPoint_eq I hI, affineComb_apply_closedPoint]
  have h₂ : (reduction I ≫ ℓ i₀) (closedPoint (CommRingCat.of (B ⧸ I))) = z := by
    rw [apply_closedPoint_eq I hI, hz]
  refine eq_of_stalkAt_eq h₁ h₂ ?_
  rw [stalkAt_reduction_comp I _ (affineComb_apply_closedPoint ℓ z hz c hc i₀ he) h₁,
    stalkAt_reduction_comp I _ (hz i₀) h₂, stalkAt_affineComb]
  ext x
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  rw [Ideal.Quotient.eq]
  exact Stacks.SquareZeroLift.affineCombinationRingHom_sub_mem I hI Finset.univ c hc i₀
    (fun i => (stalkAt (ℓ i) (hz i)).hom)
    (fun i _ x => stalkAt_sub_mem I hI (hz i) (hz i₀) (he i) x) x

/-- **Affine combinations commute with postcomposition.** -/
theorem affineComb_comp (ℓ : ι → (Spec B ⟶ Z)) (z : Z)
    (hz : ∀ i, ℓ i (closedPoint B) = z) (c : ι → B) (hc : ∑ i, c i = 1)
    (i₀ : ι) (he : ∀ i, reduction I ≫ ℓ i = reduction I ≫ ℓ i₀) (g : Z ⟶ W)
    (hz' : ∀ i, (ℓ i ≫ g) (closedPoint B) = g z)
    (he' : ∀ i, reduction I ≫ ℓ i ≫ g = reduction I ≫ ℓ i₀ ≫ g) :
    affineComb I hI ℓ z hz c hc i₀ he ≫ g =
      affineComb I hI (fun i => ℓ i ≫ g) (g z) hz' c hc i₀ he' := by
  have h₁ : (affineComb I hI ℓ z hz c hc i₀ he ≫ g) (closedPoint B) = g z := by
    show g (affineComb I hI ℓ z hz c hc i₀ he (closedPoint B)) = g z
    rw [affineComb_apply_closedPoint]
  refine eq_of_stalkAt_eq h₁ (affineComb_apply_closedPoint _ _ hz' c hc i₀ he') ?_
  rw [stalkAt_comp _ (affineComb_apply_closedPoint ℓ z hz c hc i₀ he) g,
    stalkAt_affineComb, stalkAt_affineComb]
  ext x
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, affineCombStalk_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [stalkAt_comp (ℓ i) (hz i) g]
  rfl

/-- **Affine combinations commute with a ring automorphism of `B` preserving `I`**, which acts
on the coefficients. -/
theorem specMap_comp_affineComb (ℓ : ι → (Spec B ⟶ Z)) (z : Z)
    (hz : ∀ i, ℓ i (closedPoint B) = z) (c : ι → B) (hc : ∑ i, c i = 1)
    (i₀ : ι) (he : ∀ i, reduction I ≫ ℓ i = reduction I ≫ ℓ i₀) (ρ : B ⟶ B)
    [IsLocalHom ρ.hom]
    (hz' : ∀ i, (Spec.map ρ ≫ ℓ i) (closedPoint B) = z) (hc' : ∑ i, ρ (c i) = 1)
    (he' : ∀ i, reduction I ≫ Spec.map ρ ≫ ℓ i = reduction I ≫ Spec.map ρ ≫ ℓ i₀) :
    Spec.map ρ ≫ affineComb I hI ℓ z hz c hc i₀ he =
      affineComb I hI (fun i => Spec.map ρ ≫ ℓ i) z hz' (fun i => ρ (c i)) hc' i₀ he' := by
  have h₁ : (Spec.map ρ ≫ affineComb I hI ℓ z hz c hc i₀ he) (closedPoint B) = z := by
    show affineComb I hI ℓ z hz c hc i₀ he ((Spec.map ρ) (closedPoint B)) = z
    rw [Spec_closedPoint, affineComb_apply_closedPoint]
  refine eq_of_stalkAt_eq h₁ (affineComb_apply_closedPoint _ _ hz' _ hc' i₀ he') ?_
  rw [stalkAt_specMap_comp ρ _ (affineComb_apply_closedPoint ℓ z hz c hc i₀ he) h₁,
    stalkAt_affineComb, stalkAt_affineComb]
  ext x
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, affineCombStalk_apply, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [stalkAt_specMap_comp ρ (ℓ i) (hz i) (hz' i)]
  rfl

/-- **An affine combination of morphisms with a common composite has that composite.** -/
theorem affineComb_comp_eq (ℓ : ι → (Spec B ⟶ Z)) (z : Z)
    (hz : ∀ i, ℓ i (closedPoint B) = z) (c : ι → B) (hc : ∑ i, c i = 1)
    (i₀ : ι) (he : ∀ i, reduction I ≫ ℓ i = reduction I ≫ ℓ i₀) (g : Z ⟶ W)
    (m : Spec B ⟶ W) (hm : ∀ i, ℓ i ≫ g = m) :
    affineComb I hI ℓ z hz c hc i₀ he ≫ g = m := by
  have hmz : m (closedPoint B) = g z := by
    rw [← hm i₀]; change g (ℓ i₀ (closedPoint B)) = g z; rw [hz]
  have h₁ : (affineComb I hI ℓ z hz c hc i₀ he ≫ g) (closedPoint B) = g z := by
    show g (affineComb I hI ℓ z hz c hc i₀ he (closedPoint B)) = g z
    rw [affineComb_apply_closedPoint]
  refine eq_of_stalkAt_eq h₁ hmz ?_
  rw [stalkAt_comp _ (affineComb_apply_closedPoint ℓ z hz c hc i₀ he) g, stalkAt_affineComb]
  ext x
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, affineCombStalk_apply]
  have hk : ∀ k, (stalkAt (ℓ k) (hz k)).hom (g.stalkMap z x) = (stalkAt m hmz).hom x := by
    intro k
    have h1 := stalkAt_comp (ℓ k) (hz k) g
    have h2 := stalkAt_congr (hm k) (show (ℓ k ≫ g) (closedPoint B) = g z by
      show g (ℓ k (closedPoint B)) = g z; rw [hz]) hmz
    rw [← h2, h1]
    rfl
  simp only [hk, ← Finset.sum_mul, hc, one_mul]

/-- Affine combinations of pointwise equal families with equal coefficients are equal. -/
theorem affineComb_congr {ℓ ℓ' : ι → (Spec B ⟶ Z)} (hℓ : ∀ k, ℓ k = ℓ' k) {z z' : Z}
    (hzz : z = z') (hz : ∀ i, ℓ i (closedPoint B) = z) (hz' : ∀ i, ℓ' i (closedPoint B) = z')
    {c c' : ι → B} (hcc : ∀ k, c k = c' k) (hc : ∑ i, c i = 1) (hc' : ∑ i, c' i = 1)
    {i₀ i₀' : ι} (he : ∀ i, reduction I ≫ ℓ i = reduction I ≫ ℓ i₀)
    (he' : ∀ i, reduction I ≫ ℓ' i = reduction I ≫ ℓ' i₀') :
    affineComb I hI ℓ z hz c hc i₀ he = affineComb I hI ℓ' z' hz' c' hc' i₀' he' := by
  obtain rfl : ℓ = ℓ' := funext hℓ
  obtain rfl : c = c' := funext hcc
  subst hzz
  exact affineComb_eq_of_apply _ _ _ _ _ _ _ _ _ _ _ _ _ fun _ => rfl

/-- **Reindexing an affine combination** along a permutation of the index type. -/
theorem affineComb_reindex (ℓ : ι → (Spec B ⟶ Z)) (z : Z)
    (hz : ∀ i, ℓ i (closedPoint B) = z) (c : ι → B) (hc : ∑ i, c i = 1)
    (i₀ : ι) (he : ∀ i, reduction I ≫ ℓ i = reduction I ≫ ℓ i₀) (π : ι ≃ ι)
    (hc' : ∑ i, c (π i) = 1) (he' : ∀ i, reduction I ≫ ℓ (π i) = reduction I ≫ ℓ (π i₀)) :
    affineComb I hI (fun i => ℓ (π i)) z (fun i => hz (π i)) (fun i => c (π i)) hc' i₀ he' =
      affineComb I hI ℓ z hz c hc i₀ he :=
  affineComb_eq_of_apply _ _ _ _ _ _ _ _ _ _ _ _ _ fun x =>
    Fintype.sum_equiv π (fun i => c (π i) * (stalkAt (ℓ (π i)) (hz (π i))).hom x)
      (fun i => c i * (stalkAt (ℓ i) (hz i)).hom x) (fun _ => rfl)

end AlgebraicGeometry.SquareZeroLift

end
