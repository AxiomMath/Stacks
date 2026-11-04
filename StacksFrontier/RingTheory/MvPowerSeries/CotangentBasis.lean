module

public import StacksFrontier.RingTheory.MvPowerSeries.LowDegree

/-!
# The cotangent space of a power-series ring, with the variables as a basis

For a field `k`, the cotangent space of `A = k[[x_0, …, x_{n-1}]]` has the cotangent classes of
the variables `x_0, …, x_{n-1}` as a basis over the residue field of `A`.

## Main definitions

* `Stacks.MvPowerSeries.RegularParameters.XMem`: the variable `X i` as an element of the maximal
  ideal.
* `Stacks.MvPowerSeries.RegularParameters.basisCotangentSpaceX`: the basis of `CotangentSpace A`
  whose `i`-th vector is the cotangent class of `X (e i)`, for a bijection `e : ι ≃ Fin n`.

## Main results

* `Stacks.MvPowerSeries.RegularParameters.span_range_toCotangent_X_eq_top`: the cotangent classes
  of the variables span the cotangent space.
* `Stacks.MvPowerSeries.RegularParameters.basisCotangentSpaceX_apply`: the basis vectors are the
  cotangent classes of the variables.

## Implementation notes

The basis is indexed by an arbitrary type `ι` equipped with a bijection `e : ι ≃ Fin n`, rather
than by `Fin n` itself, so that it may be indexed by a type in another universe.

A power series with zero constant term agrees with its linear part modulo the square of the
maximal ideal, by
`Stacks.MvPowerSeries.RegularParameters.mem_sq_maximalIdeal_of_linear_coeff_zero`, so the
cotangent classes of the variables span. Linear independence follows, the span being the whole of
a space of the right finite dimension.
-/

@[expose] public section

open IsLocalRing

namespace Stacks.MvPowerSeries.RegularParameters

variable {K : Type*} [Field K] {n : ℕ}

/-- The variable `X i` as an element of the maximal ideal of `k[[x_0, …, x_{n-1}]]`. -/
noncomputable def XMem (i : Fin n) : maximalIdeal (MvPowerSeries (Fin n) K) :=
  ⟨MvPowerSeries.X i,
    (mem_maximalIdeal_iff_constantCoeff_eq_zero_field _).2 (MvPowerSeries.constantCoeff_X i)⟩

/-- The underlying power series of `XMem i` is the variable `X i`. -/
@[simp]
theorem XMem_coe (i : Fin n) :
    ((XMem i : maximalIdeal (MvPowerSeries (Fin n) K)) : MvPowerSeries (Fin n) K) =
      MvPowerSeries.X i := rfl

/-- Scalars act on cotangent classes through the residue field. -/
theorem residue_smul_toCotangent {A : Type*} [CommRing A] [IsLocalRing A] (a : A)
    (x : maximalIdeal A) :
    residue A a • (maximalIdeal A).toCotangent x =
      (maximalIdeal A).toCotangent (a • x) := by
  rw [show residue A a • (maximalIdeal A).toCotangent x =
      a • (maximalIdeal A).toCotangent x from by
    rw [← IsScalarTower.algebraMap_smul (ResidueField A)]; rfl]
  rw [map_smul]

/-- **The cotangent classes of the variables span the cotangent space of
`k[[x_0, …, x_{n-1}]]`.** -/
theorem span_range_toCotangent_X_eq_top :
    Submodule.span (ResidueField (MvPowerSeries (Fin n) K))
        (Set.range fun i : Fin n =>
          (maximalIdeal (MvPowerSeries (Fin n) K)).toCotangent (XMem i)) = ⊤ := by
  classical
  set A := MvPowerSeries (Fin n) K with hA
  set m := maximalIdeal A with hm
  rw [eq_top_iff]
  intro ξ _
  obtain ⟨f, rfl⟩ := m.toCotangent_surjective ξ
  set c : Fin n → K := fun i => MvPowerSeries.coeff (Finsupp.single i 1) (f : A) with hc
  have hf0 : MvPowerSeries.constantCoeff (f : A) = (0 : K) :=
    (mem_maximalIdeal_iff_constantCoeff_eq_zero_field _).1 f.2
  set w : A := ∑ i : Fin n, MvPowerSeries.C (a := c i) * MvPowerSeries.X i with hw
  have hw0 : MvPowerSeries.constantCoeff w = (0 : K) := by
    rw [hw, map_sum]
    exact Finset.sum_eq_zero fun i _ => by
      rw [map_mul, MvPowerSeries.constantCoeff_X, mul_zero]
  have hw1 : ∀ j : Fin n, MvPowerSeries.coeff (Finsupp.single j 1) w = c j := by
    intro j
    rw [hw, map_sum, Finset.sum_eq_single j]
    · rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X, ite_eq_left rfl, mul_one]
    · intro i _ hij
      rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X,
        ite_eq_right (fun hcontra =>
          hij ((Finsupp.single_left_inj (by norm_num)).mp hcontra.symm)),
        mul_zero]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  have hdiff : (f : A) - w ∈ m ^ 2 := by
    refine mem_sq_maximalIdeal_of_linear_coeff_zero _ ?_ ?_
    · rw [map_sub, hf0, hw0, sub_zero]
    · intro j
      rw [map_sub, hw1 j, hc, sub_self]
  have hwmem : w ∈ m := (mem_maximalIdeal_iff_constantCoeff_eq_zero_field _).2 hw0
  have hkey : m.toCotangent f = m.toCotangent ⟨w, hwmem⟩ := by
    rw [← sub_eq_zero, ← map_sub, Ideal.toCotangent_eq_zero]
    simpa using hdiff
  rw [hkey]
  have hsum : (⟨w, hwmem⟩ : m) =
      ∑ i : Fin n, (MvPowerSeries.C (a := c i) : A) • (XMem i : m) := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, SetLike.val_smul, smul_eq_mul, XMem_coe, hw]
  rw [hsum, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [← residue_smul_toCotangent]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- **The basis of the cotangent space of `k[[x_0, …, x_{n-1}]]` given by the variables**, indexed
through a chosen bijection `e` onto `Fin n`. -/
noncomputable def basisCotangentSpaceX {ι : Type*} [Fintype ι] (e : ι ≃ Fin n) :
    Module.Basis ι (ResidueField (MvPowerSeries (Fin n) K))
      (CotangentSpace (MvPowerSeries (Fin n) K)) :=
  basisOfTopLeSpanOfCardEqFinrank
    (fun i : ι => (maximalIdeal (MvPowerSeries (Fin n) K)).toCotangent (XMem (e i)))
    (by
      have hr : (Set.range fun i : ι =>
            (maximalIdeal (MvPowerSeries (Fin n) K)).toCotangent (XMem (e i))) =
          Set.range fun i : Fin n =>
            (maximalIdeal (MvPowerSeries (Fin n) K)).toCotangent (XMem i) := by
        ext x
        simp only [Set.mem_range]
        exact ⟨fun ⟨i, h⟩ => ⟨e i, h⟩,
          fun ⟨j, h⟩ => ⟨e.symm j, by rwa [e.apply_symm_apply]⟩⟩
      rw [hr, span_range_toCotangent_X_eq_top])
    (by
      rw [Fintype.card_congr e, Fintype.card_fin,
        finrank_cotangentSpace_field (K := K) (n := n)])

/-- The `i`-th vector of `basisCotangentSpaceX e` is the cotangent class of the variable
`X (e i)`. -/
@[simp]
theorem basisCotangentSpaceX_apply {ι : Type*} [Fintype ι] (e : ι ≃ Fin n) (i : ι) :
    basisCotangentSpaceX (K := K) e i =
      (maximalIdeal (MvPowerSeries (Fin n) K)).toCotangent (XMem (e i)) := by
  rw [basisCotangentSpaceX, coe_basisOfTopLeSpanOfCardEqFinrank]

end Stacks.MvPowerSeries.RegularParameters

end
