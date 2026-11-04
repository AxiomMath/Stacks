module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.PiTensorProduct

/-! # Algebra morphisms from multi-tensor-product -/

@[expose] public section

open TensorProduct

namespace PiTensorProduct
variable (R : Type*) {ι : Type*} (A : ι → Type*)
  [CommSemiring R] [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]

/-- Generalizes `Algebra.TensorProduct.includeLeft` and `Algebra.TensorProduct.includeRight`. -/
def of [DecidableEq ι] (i : ι) : A i →ₐ[R] ⨂[R] j, A j where
  __ := (tprod R).toLinearMap 1 i
  map_zero' := by simp
  map_one' := by simp [one_def]
  map_mul' x y := by simp [← Pi.mulSingle.eq_1, Pi.mulSingle_mul]
  commutes' r := by simp [algebraMap_apply r i, Pi.mulSingle]

theorem of_apply [DecidableEq ι] (i : ι) (x : A i) : of R A i x = tprod R (Pi.mulSingle i x) := rfl

variable {R A} in
theorem of_commute [DecidableEq ι] {i j : ι} {x : A i} {y : A j} (hij : i ≠ j) :
    Commute (of R A i x) (of R A j y) := by
  simp [commute_iff_eq, of_apply, (Pi.mulSingle_commute hij x y).eq]

theorem tprod_eq_noncommProd_of [Fintype ι] [DecidableEq ι] (x : ∀ i, A i) :
    tprod R x = Finset.univ.noncommProd (fun i ↦ of R A i (x i)) fun _ _ _ _ ↦ of_commute := by
  simp_rw [of_apply]
  rw [← tprod_noncommProd (hx := fun _ _ _ _ h ↦ Pi.mulSingle_commute h ..),
    Finset.noncommProd_mulSingle]

theorem iSup_range_of_eq_top [Finite ι] [DecidableEq ι] : ⨆ i, (of R A i).range = ⊤ := by
  have := Fintype.ofFinite ι
  rw [eq_top_iff, ← Subalgebra.toSubmodule.le_iff_le, Algebra.top_toSubmodule,
    ← span_tprod_eq_top, Submodule.span_le, Set.range_subset_iff]
  rintro x
  rw [tprod_eq_noncommProd_of]
  exact Submonoid.noncommProd_mem _ _ _ _ fun i _ ↦ le_iSup (of R A · |>.range) i ⟨_, rfl⟩

variable {R A} {S : Type*} [CommSemiring S] [Algebra R S] [Fintype ι]

/-- Generalizes `Algebra.TensorProduct.productMap`. -/
def productMap (f : ∀ i, A i →ₐ[R] S) : (⨂[R] i, A i) →ₐ[R] S :=
  liftAlgHom (.compLinearMap (.mkPiAlgebra R ι S) (f ·)) (by simp) <| by
    simp [Finset.prod_mul_distrib]

variable (f : ∀ i, A i →ₐ[R] S)

@[simp] theorem productMap_tmul (x : ∀ i, A i) :
    productMap f (tprod _ x) = ∏ i, f i (x i) := by simp [productMap]

@[simp] theorem productMap_of [DecidableEq ι] (i : ι) (x : A i) :
    productMap f (of R A i x) = f i x := by
  simp [of, Function.update, apply_dite]

@[simp] theorem productMap_comp_of [DecidableEq ι] (i : ι) :
    (productMap f).comp (of R A i) = f i := by ext; simp

theorem range_productMap : (productMap f).range = ⨆ i, (f i).range := by
  classical
  simp only [← Algebra.map_top, ← iSup_range_of_eq_top, le_antisymm_iff, iSup_le_iff,
    Subalgebra.map_le]
  simp_rw [Algebra.map_top]
  exact ⟨fun i x _ ↦ le_iSup (f · |>.range) i ⟨x, by simp⟩,
    fun i x _ ↦ ⟨of R A i x, by simpa using le_iSup (of R A · |>.range) i ⟨x, rfl⟩⟩⟩

end PiTensorProduct
