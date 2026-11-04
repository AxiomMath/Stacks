module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.RelativeSectorHomotopy

/-!
# The contracting homotopy of a relative sector anticommutes with the horizontal differential

Let `A` be a ring, let `(B, I, δ)` be a divided power ring which is an `A`-algebra, let `W`
index a family of divided power variables and let `P = B⟨x_w : w ∈ W⟩`.  On the `K`-sector the
divided power de Rham differential of `P` is the total differential `D = D_hor + κ` of the
bicomplex `Kos(supp K) ⊗_B Ω^*_{B/A,δ}`, and
`Crystalline.DividedPowerPolynomial.relativeSectorKoszul_homotopy` contracts the Koszul
direction: `κ h + h κ = id`.

Contractibility of the total complex needs one thing more.  From `D = D_hor + κ`,

`D h + h D = (κ h + h κ) + (D_hor h + h D_hor) = id + (D_hor h + h D_hor)`,

so the homotopy of the Koszul direction contracts the **total** complex exactly when

`D_hor h + h D_hor = 0`.

That is what this module proves.  The two terms carry the opposite signs `(-1)^i` and
`(-1)^(i+1)`, so the content is that the contraction commutes with `d_B`.

## Why this is not formal

`D_hor` is `1 ⊗ d_B` and `h` is `(-1)^i (1 ⊗ ι_φ)`, and `ι_φ` acts on the other tensor factor,
so one is tempted to quote `LinearMap.rTensor_comp_lTensor`.  There is no `lTensor` here:
`d_B` is only additive, so `D_hor` is not `LinearMap.lTensor` of anything, and indeed
`Crystalline.DividedPowerPolynomial.relativeSectorCoefficientDifferential` is defined through
the basis of the Koszul factor.  A genuinely `B`-linear operator on the Koszul factor would
**not** commute with it.

What saves the contraction is that its matrix in the sector basis has entries in `{0, ± 1}`:
`exteriorPower.contraction_ιMulti` expands it on a wedge of standard generators with
coefficients `(-1)^k φ(e_{w_k})`, and `φ` is a coordinate functional.  An integer scalar
commutes with any additive map, so the contraction does commute with `d_B` — and that is the
whole proof.

## Main results

* `Crystalline.DividedPowerPolynomial.relativeSectorCoefficientDifferential_ιMulti_tmul` — the
  horizontal differential is `1 ⊗ d_B` on a wedge of standard generators tensored with a
  coefficient form.  This is the step that fails for a general element of the Koszul factor.
* `Crystalline.DividedPowerPolynomial.relativeSectorHomotopy_coefficientDifferential` —
  **`D_hor h + h D_hor = 0`.**

## References

* [Stacks Project, Lemma 60.19.1, Tag 07LC](https://stacks.math.columbia.edu/tag/07LC)
* [Stacks Project, Lemma 60.19.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
-/

@[expose] public noncomputable section

open DividedPowers
open scoped TensorProduct

universe uA uB uW

namespace Crystalline

namespace DividedPowerPolynomial

section Horizontal

variable (A : Type uA) [CommRing A] (B : DividedPowerRing.{uB}) [Algebra A B] (W : Type uW)
  [LinearOrder W]

/-- The sign `(-1)^i` of the sector, read as an integer scalar.  The signs of the sector
differential and of its homotopy are powers of `-1` in the coefficient ring, but every use of
them here is against an only-additive map, so they are moved to `ℤ` once, here. -/
theorem neg_one_pow_smul_eq_zsmul {M : Type*} [AddCommGroup M] [Module (B : Type uB) M]
    (i : ℕ) (x : M) : (-1 : (B : Type uB)) ^ i • x = ((-1 : ℤ) ^ i) • x := by
  rw [← Int.cast_smul_eq_zsmul (B : Type uB) ((-1 : ℤ) ^ i) x]
  push_cast
  rfl

omit [LinearOrder W] in
/-- Placing an element of the Koszul factor against a fixed coefficient form is `B`-linear, so
it carries an integer multiple to an integer multiple. -/
theorem zsmul_tmul_sector (K : W →₀ ℕ) (i j : ℕ) (c : ℤ)
    (x : ⋀[(B : Type uB)]^j ((K.support : Type uW) →₀ (B : Type uB)))
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) :
    (c • x) ⊗ₜ[(B : Type uB)] omega = c • (x ⊗ₜ[(B : Type uB)] omega) :=
  map_zsmul ((TensorProduct.mk (B : Type uB)
    (⋀[(B : Type uB)]^j ((K.support : Type uW) →₀ (B : Type uB)))
    (dividedPowerDifferentialForms (A := A) B.dividedPowers i)).flip omega) c x

/-- **The functional dual to a variable takes an integer value on every standard generator.**
It is a coordinate functional, so the value is `1` or `0`; when `supp K` is empty it is `0`.
This is the only property of `Crystalline.DividedPowerPolynomial.sectorFunctional` the
anticommutation uses, and it is exactly what a `B`-linear operator would not have. -/
theorem sectorFunctional_single_eq_intCast (K : W →₀ ℕ) (u : (K.support : Type uW)) :
    ∃ n : ℤ, sectorFunctional B W K (Finsupp.single u (1 : (B : Type uB))) =
      ((n : ℤ) : (B : Type uB)) := by
  classical
  by_cases hK : K ≠ 0
  · rw [sectorFunctional, dite_eq_left hK]
    by_cases hu : u = (⟨(Finsupp.support_nonempty_iff.mpr hK).choose,
        (Finsupp.support_nonempty_iff.mpr hK).choose_spec⟩ : (K.support : Type uW))
    · exact ⟨1, by simp [Finsupp.lapply_apply, hu]⟩
    · exact ⟨0, by simp [Finsupp.lapply_apply, hu]⟩
  · exact ⟨0, by rw [sectorFunctional, dite_eq_right hK]; simp⟩

/-! ### The horizontal differential on wedges of standard generators -/

/-- **The horizontal differential is `1 ⊗ d_B` on a wedge of standard generators.**

`Crystalline.DividedPowerPolynomial.relativeSectorCoefficientDifferential_basis_tmul` says this
on a **sector basis** vector, whose variables are in increasing order.  A wedge of standard
generators in an arbitrary order is, by `Module.Basis.exteriorPower_ιMulti_eq_zsmul`, an
integer multiple of one of those, and an integer multiple survives an only-additive map. -/
theorem relativeSectorCoefficientDifferential_ιMulti_tmul (K : W →₀ ℕ) (i j : ℕ)
    (u : Fin j → (K.support : Type uW))
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) :
    relativeSectorCoefficientDifferential A B W K i j
        (exteriorPower.ιMulti (B : Type uB) j
          (fun k ↦ Finsupp.single (u k) (1 : (B : Type uB))) ⊗ₜ[(B : Type uB)] omega) =
      exteriorPower.ιMulti (B : Type uB) j
          (fun k ↦ Finsupp.single (u k) (1 : (B : Type uB))) ⊗ₜ[(B : Type uB)]
        dividedPowerDeRham B.dividedPowers i omega := by
  classical
  by_cases hu : Function.Injective u
  · obtain ⟨s, c, hc⟩ := Module.Basis.exteriorPower_ιMulti_eq_zsmul
      (Finsupp.basisSingleOne (R := (B : Type uB)) (ι := (K.support : Type uW))) j u hu
    have hX : exteriorPower.ιMulti (B : Type uB) j
          (fun k ↦ Finsupp.single (u k) (1 : (B : Type uB))) =
        c • sectorExteriorBasis B W K j s := by
      refine Eq.trans (congrArg (exteriorPower.ιMulti (B : Type uB) j) (funext fun k ↦ ?_)) hc
      rw [Finsupp.coe_basisSingleOne]
    rw [hX, zsmul_tmul_sector A B W K i j c, map_zsmul,
      relativeSectorCoefficientDifferential_basis_tmul, zsmul_tmul_sector A B W K (i + 1) j c]
  · have hzero : exteriorPower.ιMulti (B : Type uB) j
        (fun k ↦ Finsupp.single (u k) (1 : (B : Type uB))) = 0 :=
      AlternatingMap.map_eq_zero_of_not_injective _ _ fun h ↦
        hu fun a b hab ↦ h (congrArg (fun z ↦ Finsupp.single z (1 : (B : Type uB))) hab)
    rw [hzero, TensorProduct.zero_tmul, TensorProduct.zero_tmul, map_zero]

/-- The same for an integer combination of wedges of standard generators. -/
theorem relativeSectorCoefficientDifferential_sum_zsmul_ιMulti_tmul (K : W →₀ ℕ) (i j : ℕ)
    {iota : Type*} (s : Finset iota) (c : iota → ℤ)
    (u : iota → Fin j → (K.support : Type uW))
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) :
    relativeSectorCoefficientDifferential A B W K i j
        ((∑ k ∈ s, c k • exteriorPower.ιMulti (B : Type uB) j
          fun m ↦ Finsupp.single (u k m) (1 : (B : Type uB))) ⊗ₜ[(B : Type uB)] omega) =
      (∑ k ∈ s, c k • exteriorPower.ιMulti (B : Type uB) j
          fun m ↦ Finsupp.single (u k m) (1 : (B : Type uB))) ⊗ₜ[(B : Type uB)]
        dividedPowerDeRham B.dividedPowers i omega := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, TensorProduct.zero_tmul, TensorProduct.zero_tmul, map_zero]
  | @insert a t ha ih =>
      rw [Finset.sum_insert ha, TensorProduct.add_tmul,
        TensorProduct.add_tmul, map_add, ih, zsmul_tmul_sector A B W K i j (c a), map_zsmul,
        relativeSectorCoefficientDifferential_ιMulti_tmul,
        zsmul_tmul_sector A B W K (i + 1) j (c a)]

/-- **The contraction of a sector basis vector is an integer combination of wedges of standard
generators.**  `exteriorPower.contraction_ιMulti` expands it with coefficients
`(-1)^k φ(e_{w_k})`, and those are integers by
`Crystalline.DividedPowerPolynomial.sectorFunctional_single_eq_intCast`. -/
theorem contraction_sectorExteriorBasis_eq_sum (K : W →₀ ℕ) (j : ℕ)
    (I : Set.powersetCard (K.support : Type uW) (j + 1)) :
    ∃ c : Fin (j + 1) → ℤ,
      exteriorPower.contraction (sectorFunctional B W K) j
          (sectorExteriorBasis B W K (j + 1) I) =
        ∑ k : Fin (j + 1), c k • exteriorPower.ιMulti (B : Type uB) j
          fun m ↦ Finsupp.single
            (Fin.removeNth k (Set.powersetCard.ofFinEmbEquiv.symm I) m) (1 : (B : Type uB)) := by
  classical
  choose n hn using fun k : Fin (j + 1) ↦ sectorFunctional_single_eq_intCast B W K
    (Set.powersetCard.ofFinEmbEquiv.symm I k)
  refine ⟨fun k ↦ (-1 : ℤ) ^ (k : ℕ) * n k, ?_⟩
  rw [sectorExteriorBasis_apply, exteriorPower.contraction_ιMulti]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [hn k, Int.cast_smul_eq_zsmul, smul_smul]
  rfl

/-- The horizontal differential is `1 ⊗ d_B` on the contraction of a sector basis vector. -/
theorem relativeSectorCoefficientDifferential_contraction_tmul (K : W →₀ ℕ) (i j : ℕ)
    (I : Set.powersetCard (K.support : Type uW) (j + 1))
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) :
    relativeSectorCoefficientDifferential A B W K i j
        (exteriorPower.contraction (sectorFunctional B W K) j
          (sectorExteriorBasis B W K (j + 1) I) ⊗ₜ[(B : Type uB)] omega) =
      exteriorPower.contraction (sectorFunctional B W K) j
          (sectorExteriorBasis B W K (j + 1) I) ⊗ₜ[(B : Type uB)]
        dividedPowerDeRham B.dividedPowers i omega := by
  obtain ⟨c, hc⟩ := contraction_sectorExteriorBasis_eq_sum B W K j I
  rw [hc]
  exact relativeSectorCoefficientDifferential_sum_zsmul_ιMulti_tmul A B W K i j Finset.univ c
    (fun k ↦ Fin.removeNth k (Set.powersetCard.ofFinEmbEquiv.symm I)) omega

/-! ### The anticommutation -/

/-- **The contracting homotopy of the Koszul direction anticommutes with the horizontal
differential: `D_hor h + h D_hor = 0`.**

With `D = D_hor + κ` and `κ h + h κ = id` this is the missing half of
`D h + h D = id`, and it is where the relative argument differs from the absolute one: there
is no horizontal differential when the divided power ideal of the base is trivial.

The two terms carry the signs `(-1)^i` and `(-1)^(i+1)`, so what has to be shown is that the
contraction commutes with `d_B`; it does because its matrix in the sector basis is integral,
which is
`Crystalline.DividedPowerPolynomial.relativeSectorCoefficientDifferential_contraction_tmul`. -/
theorem relativeSectorHomotopy_coefficientDifferential (K : W →₀ ℕ) (i j : ℕ)
    (x : sectorModule A B W K i (j + 1)) :
    relativeSectorCoefficientDifferential A B W K i j
          (relativeSectorHomotopy A B W K i j x) +
        relativeSectorHomotopy A B W K (i + 1) j
          (relativeSectorCoefficientDifferential A B W K i (j + 1) x) = 0 := by
  classical
  obtain ⟨f, rfl⟩ := (sectorModuleEquiv A B W K i (j + 1)).symm.surjective x
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero, add_zero]
  | add f g hf hg =>
      simp only [map_add]
      rw [add_add_add_comm, hf, hg, add_zero]
  | single I omega =>
      rw [sectorModuleEquiv_symm_single]
      have hcontr : ∀ (m : ℕ) (eta : dividedPowerDifferentialForms (A := A) B.dividedPowers m),
          relativeSectorHomotopy A B W K m j
              (sectorExteriorBasis B W K (j + 1) I ⊗ₜ[(B : Type uB)] eta) =
            ((-1 : ℤ) ^ m) • (exteriorPower.contraction (sectorFunctional B W K) j
              (sectorExteriorBasis B W K (j + 1) I) ⊗ₜ[(B : Type uB)] eta) := fun m eta ↦ by
        rw [relativeSectorHomotopy, LinearMap.smul_apply, LinearMap.rTensor_tmul,
          neg_one_pow_smul_eq_zsmul]
      rw [hcontr, relativeSectorCoefficientDifferential_basis_tmul, hcontr, map_zsmul,
        relativeSectorCoefficientDifferential_contraction_tmul, pow_succ, mul_neg_one,
        neg_zsmul, add_neg_cancel]

end Horizontal

end DividedPowerPolynomial

end Crystalline

end
