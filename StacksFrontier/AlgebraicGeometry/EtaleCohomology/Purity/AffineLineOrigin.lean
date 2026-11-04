module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.AffineLineCohomology
public import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# The origin of the affine line

The origin `0 : Spec k ⟶ 𝐀¹_k` is the closed immersion defined by the constant coefficient
`k[t] ⟶ k`. Its image is the complement of the punctured affine line `𝐆_m = D(t)`: a prime of
`k[t]` contains `t` exactly when it contains the kernel `(t)` of the constant coefficient.

## Main definitions

* `Stacks.EtaleCohomology.Purity.origin`.

## Main results

* `Stacks.EtaleCohomology.Purity.isClosedImmersion_origin`.
* `Stacks.EtaleCohomology.Purity.range_origin`: `range 0 = (D t)ᶜ`.
* `Stacks.EtaleCohomology.Purity.range_punctured_ι`: `range (𝐆_m ⟶ 𝐀¹) = (range 0)ᶜ`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology.Purity

variable (k : Type u) [Field k]

/-- The origin `0 : Spec k ⟶ 𝐀¹_k`, the closed point `t = 0`. -/
def origin : Spec (.of k) ⟶ affineLine k :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.constantCoeff :
      MvPolynomial (ULift.{u} (Fin 1)) k →+* k)) ≫
    (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of k)).inv

/-- The origin is a closed immersion: the constant coefficient `k[t] ⟶ k` is surjective. -/
theorem isClosedImmersion_origin : IsClosedImmersion (origin k) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (MvPolynomial.constantCoeff :
      MvPolynomial (ULift.{u} (Fin 1)) k →+* k))) :=
    IsClosedImmersion.spec_of_surjective _ (fun c => ⟨MvPolynomial.C c, by simp⟩)
  exact IsClosedImmersion.comp _ _

/-- A prime of `k[t]` contains the kernel of the constant coefficient exactly when it contains
`t`. -/
theorem ker_constantCoeff_le_iff (𝔭 : Ideal (MvPolynomial (ULift.{u} (Fin 1)) k)) :
    RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (ULift.{u} (Fin 1)) k →+* k) ≤ 𝔭 ↔
      MvPolynomial.X ⟨0⟩ ∈ 𝔭 := by
  constructor
  · exact fun h => h (by simp)
  · intro hX f hf
    have hspan : f ∈ Ideal.span (MvPolynomial.X '' Set.univ :
        Set (MvPolynomial (ULift.{u} (Fin 1)) k)) := by
      rw [MvPolynomial.mem_ideal_span_X_image]
      intro m hm
      have hm0 : m ≠ 0 := by
        rintro rfl
        rw [MvPolynomial.mem_support_iff] at hm
        rw [RingHom.mem_ker, MvPolynomial.constantCoeff_eq] at hf
        exact hm hf
      obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hm0
      exact ⟨i, Set.mem_univ _, hi⟩
    refine (Ideal.span_le.2 ?_) hspan
    rintro _ ⟨i, -, rfl⟩
    rw [Subsingleton.elim i ⟨0⟩]
    exact hX

/-- The preimage of the punctured line in `Spec k[t]` is the basic open of `t`. -/
theorem preimage_punctured_specIso_inv :
    (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of k)).inv ⁻¹ᵁ punctured k =
      PrimeSpectrum.basicOpen (MvPolynomial.X ⟨0⟩ : MvPolynomial (ULift.{u} (Fin 1)) k) := by
  rw [punctured, Scheme.preimage_basicOpen_top, coordinate, AffineSpace.SpecIso_inv_appTop_coord,
    basicOpen_eq_of_affine]

/-- **The image of the origin is the complement of the punctured line.** -/
theorem range_origin : Set.range (origin k).base = ((punctured k : Set (affineLine k)))ᶜ := by
  set e := AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of k)
  set c : MvPolynomial (ULift.{u} (Fin 1)) k →+* k := MvPolynomial.constantCoeff
  have hrange : Set.range (PrimeSpectrum.comap c) = PrimeSpectrum.zeroLocus (RingHom.ker c) :=
    range_comap_of_surjective _ _ (fun a => ⟨MvPolynomial.C a, by simp [c]⟩)
  have hmem : ∀ y : PrimeSpectrum (MvPolynomial (ULift.{u} (Fin 1)) k),
      e.inv.base y ∈ (punctured k : Set (affineLine k)) ↔
        y ∈ PrimeSpectrum.basicOpen (MvPolynomial.X ⟨0⟩ : MvPolynomial (ULift.{u} (Fin 1)) k) := by
    intro y
    rw [← preimage_punctured_specIso_inv]
    rfl
  have horigin : Set.range (origin k).base =
      e.inv.base '' Set.range (PrimeSpectrum.comap c) := by
    rw [origin, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    rfl
  ext x
  obtain ⟨y, rfl⟩ : ∃ y : PrimeSpectrum (MvPolynomial (ULift.{u} (Fin 1)) k), e.inv.base y = x :=
    (Scheme.homeoOfIso e.symm).surjective x
  refine Iff.trans ?_ (not_congr (hmem y)).symm
  rw [PrimeSpectrum.mem_basicOpen, not_not, horigin]
  have hinj : Function.Injective e.inv.base := (Scheme.homeoOfIso e.symm).injective
  refine Iff.trans (hinj.mem_set_image (s := Set.range (PrimeSpectrum.comap c))) ?_
  have h2 : y ∈ Set.range (PrimeSpectrum.comap c) ↔ RingHom.ker c ≤ y.asIdeal := by
    rw [hrange, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
  exact h2.trans (ker_constantCoeff_le_iff k y.asIdeal)

/-- **The punctured line is the complement of the origin.** -/
theorem range_punctured_ι :
    Set.range (punctured k).ι.base = (Set.range (origin k).base)ᶜ := by
  rw [range_origin, compl_compl, Scheme.Opens.range_ι]

end Stacks.EtaleCohomology.Purity

end
