module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import StacksFrontier.RingTheory.Cech.Substrate
public import StacksFrontier.RingTheory.Koszul.Defs

/-!
# The Koszul differential in the exterior basis

Let `R` be a commutative ring and `f_1, …, f_r ∈ R`. The terms of the Koszul complex
`Koszul.seqComplex f` are the exterior powers `⋀^q R^r`, with the basis
`e_S = e_{s_0} ∧ ⋯ ∧ e_{s_{q-1}}` indexed by the subsets `S = {s_0 < ⋯ < s_{q-1}}` of `{0, …, r-1}`
of cardinality `q`. This file computes the Koszul differential in that basis:

`d(e_T) = ∑_{i ∈ T} (-1)^{#{j ∈ T | j < i}} f_i e_{T ∖ {i}}`,

with the sign of the alternating Čech complex, `Cech.cechSign`.

## Main definitions

* `Koszul.exteriorBasis`: the basis `e_S` of `⋀^q R^r`.

## Main results

* `Koszul.d_exteriorBasis`: the differential on a basis vector, as a sum over the positions.
* `Koszul.coord_d_exteriorBasis`: the matrix coefficients of the differential, as a sum over the
  elements of `T` with the alternating Čech sign.
-/

@[expose] public noncomputable section

open scoped ExteriorAlgebra

namespace Koszul

universe u

variable {R : Type u} [CommRing R] {r : ℕ}

/-- The standard basis `e_S` of `⋀^q R^r`, indexed by the subsets of `{0, …, r - 1}` of
cardinality `q`. -/
abbrev exteriorBasis (R : Type u) [CommRing R] (r q : ℕ) :
    Module.Basis (Set.powersetCard (Fin r) q) R (⋀[R]^q (Fin r → R)) :=
  (Pi.basisFun R (Fin r)).exteriorPower q

/-- The basis vector `e_S` is the exterior product of the standard basis vectors `e_s` for the
elements `s` of `S` in increasing order. -/
theorem exteriorBasis_apply {q : ℕ} (s : Set.powersetCard (Fin r) q) :
    exteriorBasis R r q s =
      ⟨ExteriorAlgebra.ιMulti R q
          (fun k ↦ Pi.single (s.1.orderEmbOfFin (Set.powersetCard.card_eq s) k) 1),
        Koszul.ιMulti_mem q _⟩ := by
  rw [exteriorPower.basis_apply]
  apply Subtype.ext
  simp [exteriorPower.ιMulti_family, Set.powersetCard.ofFinEmbEquiv_symm_apply,
    exteriorPower.ιMulti_apply_coe, Function.comp_def, Pi.basisFun_apply]

/-- The increasing enumeration of `s` with its `k`-th element removed is the increasing
enumeration of `s` precomposed with `Fin.succAbove k`. -/
theorem orderEmbOfFin_erase {α : Type*} [LinearOrder α] {q : ℕ}
    (s : Finset α) (hs : s.card = q + 1) (k : Fin (q + 1))
    (h : (s.erase (s.orderEmbOfFin hs k)).card = q) :
    (s.erase (s.orderEmbOfFin hs k)).orderEmbOfFin h =
      k.succAboveOrderEmb.trans (s.orderEmbOfFin hs) := by
  symm
  apply Finset.orderEmbOfFin_unique'
  intro j
  simp only [RelEmbedding.coe_trans, Function.comp_apply, Finset.mem_erase]
  exact ⟨fun he ↦ Fin.succAbove_ne k j ((s.orderEmbOfFin hs).injective he),
    s.orderEmbOfFin_mem hs _⟩

/-- The subset obtained by removing the element in position `k`. -/
abbrev eraseAt {q : ℕ} (s : Set.powersetCard (Fin r) (q + 1)) (k : Fin (q + 1)) :
    Set.powersetCard (Fin r) q :=
  Set.powersetCard.ofCard (s := s.1.erase (s.1.orderEmbOfFin (Set.powersetCard.card_eq s) k)) (by
    rw [Finset.card_erase_of_mem (s.1.orderEmbOfFin_mem (Set.powersetCard.card_eq s) k),
      Set.powersetCard.card_eq s]
    omega)

/-- **The Koszul differential on a basis vector.** -/
theorem d_exteriorBasis {q : ℕ} (φ : Module.Dual R (Fin r → R))
    (s : Set.powersetCard (Fin r) (q + 1)) :
    Koszul.d φ q (exteriorBasis R r (q + 1) s) =
      ∑ k : Fin (q + 1),
        ((-1 : R) ^ k.val * φ (Pi.single (s.1.orderEmbOfFin (Set.powersetCard.card_eq s) k) 1)) •
          exteriorBasis R r q (eraseAt s k) := by
  apply Subtype.ext
  simp only [exteriorBasis_apply, Koszul.d_apply_coe,
    AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
  rw [Koszul.contraction_ιMulti]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2
  funext j
  exact congrArg (fun x => Pi.single x (1 : R))
    (DFunLike.congr_fun (orderEmbOfFin_erase s.1 (Set.powersetCard.card_eq s) k
      (Set.powersetCard.card_eq (eraseAt s k))) j).symm

/-- The number of elements of `s` smaller than its `k`-th element is `k`. -/
theorem card_filter_orderEmbOfFin {α : Type*} [LinearOrder α] (s : Finset α)
    {q : ℕ} (h : s.card = q) (k : Fin q) :
    (s.filter (· < s.orderEmbOfFin h k)).card = k.val := by
  have he : s.filter (· < s.orderEmbOfFin h k) =
      (Finset.Iio k).map (s.orderEmbOfFin h).toEmbedding := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_Iio,
      RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨hi, hlt⟩
      obtain ⟨j, rfl⟩ : i ∈ Set.range (s.orderEmbOfFin h) := by
        rwa [Finset.range_orderEmbOfFin]
      exact ⟨j, (s.orderEmbOfFin h).lt_iff_lt.mp hlt, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨s.orderEmbOfFin_mem h j, (s.orderEmbOfFin h).strictMono hj⟩
  rw [he, Finset.card_map, Fin.card_Iio]

/-- The position sign is the alternating Čech sign of the removed element. -/
theorem cechSign_orderEmbOfFin (s : Finset (Fin r)) {q : ℕ} (h : s.card = q) (k : Fin q) :
    ((Cech.cechSign s (s.orderEmbOfFin h k) : ℤ) : R) = (-1 : R) ^ k.val := by
  simp [Cech.cechSign, card_filter_orderEmbOfFin s h k]

/-- **The matrix coefficients of the Koszul differential**: the `S`-th coordinate of `d(e_T)` is
the sum over the elements `i` of `T` with `T ∖ {i} = S` of the alternating Čech sign of `i` in
`T` times `φ(e_i)`. -/
theorem coord_d_exteriorBasis {q : ℕ} (φ : Module.Dual R (Fin r → R))
    (T : Set.powersetCard (Fin r) (q + 1)) (S : Set.powersetCard (Fin r) q) :
    (exteriorBasis R r q).coord S (Koszul.d φ q (exteriorBasis R r (q + 1) T)) =
      ∑ i ∈ T.1.attach, if T.1.erase i = S.1 then
        ((Cech.cechSign T.1 i : ℤ) : R) * φ (Pi.single i.1 1) else 0 := by
  rw [d_exteriorBasis, map_sum]
  simp only [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, smul_eq_mul]
  rw [Finset.attach_eq_univ]
  refine Fintype.sum_equiv (T.1.orderIsoOfFin (Set.powersetCard.card_eq T)).toEquiv _ _
    fun k => ?_
  have he : ((T.1.orderIsoOfFin (Set.powersetCard.card_eq T)).toEquiv k : Fin r) =
      T.1.orderEmbOfFin (Set.powersetCard.card_eq T) k := rfl
  simp only [he, Finsupp.single_apply]
  have hiff : (eraseAt T k = S) ↔
      T.1.erase (T.1.orderEmbOfFin (Set.powersetCard.card_eq T) k) = S.1 := Subtype.ext_iff
  by_cases h : T.1.erase (T.1.orderEmbOfFin (Set.powersetCard.card_eq T) k) = S.1
  · rw [ite_eq_left (hiff.2 h), ite_eq_left h, cechSign_orderEmbOfFin, mul_one]
  · rw [ite_eq_right (fun h' => h (hiff.1 h')), ite_eq_right h, mul_zero]

/-- A linear form is the combination of the coordinate forms of a basis with its values on the
basis as coefficients. -/
theorem _root_.Module.Basis.eq_sum_smul_coord {ι M : Type*} [Fintype ι] [AddCommGroup M]
    [Module R M] (b : Module.Basis ι R M) (φ : M →ₗ[R] R) :
    φ = ∑ i, φ (b i) • b.coord i := by
  exact (b.sum_dual_apply_smul_coord φ).symm

/-- **The Koszul differential in coordinates**: the `S`-th coordinate of `d(x)` is the
combination of the coordinates of `x` with the matrix coefficients of the differential. -/
theorem coord_comp_d {q : ℕ} (φ : Module.Dual R (Fin r → R)) (S : Set.powersetCard (Fin r) q) :
    (exteriorBasis R r q).coord S ∘ₗ Koszul.d φ q =
      ∑ T : Set.powersetCard (Fin r) (q + 1), (∑ i ∈ T.1.attach, if T.1.erase i = S.1 then
        ((Cech.cechSign T.1 i : ℤ) : R) * φ (Pi.single i.1 1) else 0) •
          (exteriorBasis R r (q + 1)).coord T := by
  refine ((exteriorBasis R r (q + 1)).eq_sum_smul_coord _).trans ?_
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [LinearMap.comp_apply, coord_d_exteriorBasis]

end Koszul

end
