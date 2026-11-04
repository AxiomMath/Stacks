module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Coalgebra.Basic
public import Mathlib.RingTheory.Flat.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Coalgebras over a field are locally finite

Let `k` be a field and `C` a coalgebra over `k`.  Every element of `C` lies in a
finite-dimensional subcoalgebra of `C`: a finite-dimensional subspace `D` whose comultiplication
lands in `D ⊗ D`.  This is the fundamental theorem of coalgebras.

## Main results

* `Coalgebra.exists_finiteDimensional_comul_mem_range_rTensor`: every element lies in a
  finite-dimensional subspace `W` with `Δ(W) ⊆ W ⊗ C`, a subcomodule of the right regular
  comodule.
* `Coalgebra.exists_finiteDimensional_subcoalgebra_mem`: every element lies in a
  finite-dimensional subcoalgebra.

## Implementation notes

For the first statement write `Δ x = ∑ᵢ mᵢ ⊗ eᵢ` along a basis `(eᵢ)` of `C` and take `W` the
span of the `mᵢ`.  Counitality puts `x` in `W`, and coassociativity, read off along the right
basis by contracting with the coordinate functionals, gives `Δ mᵢ = ∑ⱼ mⱼ ⊗ ⟨eᵢ*, Δ eⱼ⟩`.

For the second, with a basis `(bⱼ)` of such a `W`, write `Δ bⱼ = ∑ᵢ bᵢ ⊗ aᵢⱼ`.  Counitality
gives `bⱼ = ∑ᵢ ε(bᵢ) aᵢⱼ`, and coassociativity, compared along the basis `(bᵢ)` in
`W ⊗ (C ⊗ C) ⊆ C ⊗ (C ⊗ C)` (an inclusion because every module over a field is flat), gives
`Δ aₗⱼ = ∑ᵢ aₗᵢ ⊗ aᵢⱼ`.  So the span of the matrix coefficients `aᵢⱼ` is a finite-dimensional
subcoalgebra containing `W`, hence `x`.

## References

* W. C. Waterhouse, *Introduction to affine group schemes*, Theorem 3.3.
* M. E. Sweedler, *Hopf algebras*, Theorem 2.2.1.
-/

@[expose] public section

open TensorProduct

namespace Coalgebra

variable {k C : Type*} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

omit [Coalgebra k C] in
/-- Contracting the last factor of `(C ⊗ C) ⊗ C` with a functional commutes with the
associator. -/
private lemma rid_lTensor_assoc_symm_tmul (φ : C →ₗ[k] k) (m : C) (t : C ⊗[k] C) :
    TensorProduct.rid k (C ⊗[k] C)
        (φ.lTensor (C ⊗[k] C) ((TensorProduct.assoc k C C C).symm (m ⊗ₜ t))) =
      m ⊗ₜ TensorProduct.rid k C (φ.lTensor C t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [tmul_smul]
  | add s t hs ht => simp only [tmul_add, map_add, hs, ht]

/-- Contracting the last factor with a functional commutes with the comultiplication of the
first factor. -/
private lemma comul_rid_lTensor (φ : C →ₗ[k] k) (y : C ⊗[k] C) :
    comul (R := k) (TensorProduct.rid k C (φ.lTensor C y)) =
      TensorProduct.rid k (C ⊗[k] C) (φ.lTensor (C ⊗[k] C) ((comul (R := k)).rTensor C y)) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add s t hs ht => simp only [map_add, hs, ht]

/-- Comultiplication sends the span of a family into a subspace `P` of `C ⊗ C` as soon as it
sends each member of the family into `P`. -/
private lemma comul_mem_of_mem_span_range {ι : Type*} (v : ι → C)
    {P : Submodule k (C ⊗[k] C)} (h : ∀ i, comul (R := k) (v i) ∈ P) {d : C}
    (hd : d ∈ Submodule.span k (Set.range v)) : comul (R := k) d ∈ P :=
  (Submodule.span_le (p := P.comap (comul (R := k)))).mpr (by rintro _ ⟨i, rfl⟩; exact h i) hd

/-- Every element of a coalgebra over a field lies in a finite-dimensional subspace `W` with
`Δ(W) ⊆ W ⊗ C`, i.e. a finite-dimensional subcomodule of the right regular comodule. -/
@[sga "3 VIB 11.10" "special case", sga "3 XVII 3.1" "(iii), special case"]
theorem exists_finiteDimensional_comul_mem_range_rTensor (x : C) :
    ∃ W : Submodule k C, FiniteDimensional k W ∧ x ∈ W ∧
      ∀ w ∈ W, comul (R := k) w ∈ LinearMap.range (W.subtype.rTensor C) := by
  classical
  let e := Module.Free.chooseBasis k C
  let m := TensorProduct.equivFinsuppOfBasisRight e (comul (R := k) x)
  have hm : comul (R := k) x = m.sum fun i c => c ⊗ₜ e i := by
    rw [← TensorProduct.equivFinsuppOfBasisRight_symm_apply e, LinearEquiv.symm_apply_apply]
  have hmi : ∀ i, m i = TensorProduct.rid k C ((e.coord i).lTensor C (comul (R := k) x)) :=
    fun i => TensorProduct.equivFinsuppOfBasisRight_apply e _ i
  let W := Submodule.span k (Set.range fun i : m.support => m i)
  have hmem : ∀ i ∈ m.support, m i ∈ W := fun i hi => Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
  refine ⟨W, FiniteDimensional.span_of_finite k (Set.finite_range _), ?_, ?_⟩
  · have hx : x = TensorProduct.rid k C ((counit (R := k)).lTensor C (comul (R := k) x)) := by
      rw [lTensor_counit_comul]
      simp
    rw [hx, hm, Finsupp.sum, map_sum, map_sum]
    refine Submodule.sum_mem _ fun i hi => ?_
    simpa using W.smul_mem _ (hmem i hi)
  · refine fun w hw => comul_mem_of_mem_span_range _ (fun ⟨i, hi⟩ => ?_) hw
    change comul (R := k) (m i) ∈ LinearMap.range (W.subtype.rTensor C)
    rw [hmi, comul_rid_lTensor, ← coassoc_symm_apply, hm, Finsupp.sum, map_sum, map_sum,
      map_sum, map_sum]
    refine Submodule.sum_mem _ fun j hj => ?_
    rw [LinearMap.lTensor_tmul, rid_lTensor_assoc_symm_tmul]
    exact ⟨⟨m j, hmem j hj⟩ ⊗ₜ _, rfl⟩

omit [Coalgebra k C] in
/-- Along a basis of a subspace `W` of `C`, sums `∑ᵢ bᵢ ⊗ tᵢ` in `C ⊗ M` determine their
coefficients: the inclusion `W ⊗ M → C ⊗ M` is injective over a field. -/
private lemma sum_tmul_basis_injective {W : Submodule k C} {ι : Type*} [Fintype ι]
    (b : Module.Basis ι k W) {M : Type*} [AddCommGroup M] [Module k M] :
    Function.Injective fun t : ι → M => ∑ i, (b i : C) ⊗ₜ[k] t i := by
  classical
  intro s t h
  have h' : (∑ i, b i ⊗ₜ[k] s i) = ∑ i, b i ⊗ₜ[k] t i :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := M) W.subtype
      W.injective_subtype (by simpa [map_sum] using h)
  funext i
  simpa [map_sum, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply,
    Finsupp.single_apply] using congr($(congrArg (TensorProduct.equivFinsuppOfBasisLeft b) h') i)

/-- The span of a family of matrix coefficients `aᵢⱼ` with `Δ aₗⱼ = ∑ᵢ aₗᵢ ⊗ aᵢⱼ` is a
subcoalgebra. -/
theorem comul_mem_range_map_span_of_comul_eq_sum {ι : Type*} [Fintype ι] (a : ι → ι → C)
    (h : ∀ l j, comul (R := k) (a l j) = ∑ i, a l i ⊗ₜ[k] a i j) {d : C}
    (hd : d ∈ Submodule.span k (Set.range fun p : ι × ι => a p.1 p.2)) :
    comul (R := k) d ∈ LinearMap.range (TensorProduct.map
      (Submodule.span k (Set.range fun p : ι × ι => a p.1 p.2)).subtype
      (Submodule.span k (Set.range fun p : ι × ι => a p.1 p.2)).subtype) := by
  have haD : ∀ i j, a i j ∈ Submodule.span k (Set.range fun p : ι × ι => a p.1 p.2) :=
    fun i j => Submodule.subset_span ⟨(i, j), rfl⟩
  refine comul_mem_of_mem_span_range _ (fun ⟨l, j⟩ => ?_) hd
  rw [h]
  exact Submodule.sum_mem _ fun i _ => ⟨⟨a l i, haD l i⟩ ⊗ₜ ⟨a i j, haD i j⟩, rfl⟩

/-- **The fundamental theorem of coalgebras.**  Every element of a coalgebra `C` over a field
`k` lies in a finite-dimensional subcoalgebra: a finite-dimensional subspace `D` such that the
comultiplication maps `D` into the image of `D ⊗ D` in `C ⊗ C`. -/
theorem exists_finiteDimensional_subcoalgebra_mem (x : C) :
    ∃ D : Submodule k C, FiniteDimensional k D ∧ x ∈ D ∧
      ∀ d ∈ D, comul (R := k) d ∈ LinearMap.range (TensorProduct.map D.subtype D.subtype) := by
  classical
  obtain ⟨W, hWfin, hxW, hW⟩ := exists_finiteDimensional_comul_mem_range_rTensor (k := k) x
  let b := Module.finBasis k W
  let n := Module.finrank k W
  choose u hu using fun j : Fin n => hW _ (b j).2
  let a : Fin n → Fin n → C := fun i j => TensorProduct.equivFinsuppOfBasisLeft b (u j) i
  have hcomul : ∀ j, comul (R := k) (b j : C) = ∑ i, (b i : C) ⊗ₜ[k] a i j := by
    intro j
    rw [← hu j]
    conv_lhs => rw [← (TensorProduct.equivFinsuppOfBasisLeft b).symm_apply_apply (u j),
      TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp [map_sum, a]
  have hcounit : ∀ j, (b j : C) = ∑ i, counit (R := k) (b i : C) • a i j := by
    intro j
    have := congrArg (TensorProduct.lid k C) (rTensor_counit_comul (R := k) (b j : C))
    rw [hcomul j] at this
    simpa [map_sum] using this.symm
  have hcoassoc : ∀ l j, comul (R := k) (a l j) = ∑ i, a l i ⊗ₜ[k] a i j := by
    intro l j
    have key : (∑ l, (b l : C) ⊗ₜ[k] comul (R := k) (a l j)) =
        ∑ l, (b l : C) ⊗ₜ[k] ∑ i, a l i ⊗ₜ[k] a i j := by
      have := coassoc_apply (R := k) (b j : C)
      rw [hcomul j] at this
      simp only [map_sum, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, hcomul, sum_tmul,
        TensorProduct.assoc_tmul] at this
      rw [← this]
      simp only [tmul_sum]
      exact Finset.sum_comm
    exact congrFun (sum_tmul_basis_injective b key) l
  let D := Submodule.span k (Set.range fun p : Fin n × Fin n => a p.1 p.2)
  have hWD : W ≤ D := by
    intro w hw
    obtain ⟨y, rfl⟩ : ∃ y : W, (y : C) = w := ⟨⟨w, hw⟩, rfl⟩
    rw [← b.sum_repr y]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    refine Submodule.sum_mem _ fun j _ => D.smul_mem _ ?_
    rw [hcounit j]
    exact Submodule.sum_mem _ fun i _ => D.smul_mem _ (Submodule.subset_span ⟨(i, j), rfl⟩)
  exact ⟨D, FiniteDimensional.span_of_finite k (Set.finite_range _), hWD hxW,
    fun _ => comul_mem_range_map_span_of_comul_eq_sum a hcoassoc⟩

end Coalgebra
