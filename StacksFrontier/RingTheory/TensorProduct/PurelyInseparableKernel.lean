module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Nilpotency of the multiplication kernel of a purely inseparable tensor square

Let `k'/k` be a purely inseparable extension of fields. Every element of `k' ⊗[k] k'` has a
positive power lying in the image of the left factor; consequently the kernel of the
multiplication map `k' ⊗[k] k' → k'` consists of nilpotent elements, and so does the kernel of
the threefold multiplication `(k' ⊗[k] k') ⊗[k] k' → k'`.

## Main results

* `Stacks.PurelyInseparable.isNilpotent_of_mem_ker_of_isNilpotent_comp`: the general step, for an
  algebra map `R ⊗[k] k' → k'` whose restriction along `algebraMap R (R ⊗[k] k')` kills only
  nilpotent elements.
* `Stacks.PurelyInseparable.isNilpotent_mem_ker_lmul'`: every element of the kernel of
  `k' ⊗[k] k' → k'` is nilpotent.
* `Stacks.PurelyInseparable.lmulTriple` and
  `Stacks.PurelyInseparable.isNilpotent_mem_ker_lmulTriple`: the threefold multiplication
  `(k' ⊗[k] k') ⊗[k] k' → k'` and the nilpotency of its kernel.
-/

@[expose] public noncomputable section

open TensorProduct

namespace Stacks.PurelyInseparable

variable {k k' : Type*} [Field k] [Field k'] [Algebra k k'] [IsPurelyInseparable k k']

/-- Let `k'/k` be purely inseparable, `R` a `k`-algebra and `φ : R ⊗[k] k' → k'` a `k`-algebra
map. If every element of `R` killed by `φ ∘ algebraMap R (R ⊗[k] k')` is nilpotent, then every
element of the kernel of `φ` is nilpotent. -/
theorem isNilpotent_of_mem_ker_of_isNilpotent_comp {R : Type*} [CommRing R] [Algebra k R]
    (φ : R ⊗[k] k' →ₐ[k] k')
    (hφ : ∀ a : R, φ (algebraMap R (R ⊗[k] k') a) = 0 → IsNilpotent a)
    {x : R ⊗[k] k'} (hx : x ∈ RingHom.ker φ) : IsNilpotent x := by
  obtain ⟨n, hn, a, ha⟩ := IsPurelyInseparable.exists_pow_mem_range_tensorProduct (R := R) x
  have h0 : φ (algebraMap R (R ⊗[k] k') a) = 0 := by
    rw [ha, map_pow, RingHom.mem_ker.mp hx, zero_pow hn.ne']
  obtain ⟨m, hm⟩ := (hφ a h0).map (algebraMap R (R ⊗[k] k'))
  exact ⟨n * m, by rw [pow_mul, ← ha]; exact hm⟩

/-- For a purely inseparable extension `k'/k`, every element of the kernel of the multiplication
map `k' ⊗[k] k' → k'` is nilpotent. -/
@[ega "0 21.1.5" "(iii)"]
theorem isNilpotent_mem_ker_lmul' :
    ∀ x ∈ RingHom.ker (Algebra.TensorProduct.lmul' k : k' ⊗[k] k' →ₐ[k] k'), IsNilpotent x := by
  intro x hx
  refine isNilpotent_of_mem_ker_of_isNilpotent_comp
    (Algebra.TensorProduct.lmul' k : k' ⊗[k] k' →ₐ[k] k') (fun a ha => ?_) hx
  have h : a = 0 := by simpa using ha
  simp [h]

/-- The threefold multiplication map `(k' ⊗[k] k') ⊗[k] k' → k'`, `(a ⊗ b) ⊗ c ↦ a * b * c`. -/
def lmulTriple (k k' : Type*) [Field k] [Field k'] [Algebra k k'] :
    (k' ⊗[k] k') ⊗[k] k' →ₐ[k] k' :=
  Algebra.TensorProduct.lift (Algebra.TensorProduct.lmul' k) (AlgHom.id k k')
    fun _ _ => mul_comm _ _

/-- For a purely inseparable extension `k'/k`, every element of the kernel of the threefold
multiplication map `(k' ⊗[k] k') ⊗[k] k' → k'` is nilpotent. -/
theorem isNilpotent_mem_ker_lmulTriple :
    ∀ x ∈ RingHom.ker (lmulTriple k k'), IsNilpotent x := by
  intro x hx
  refine isNilpotent_of_mem_ker_of_isNilpotent_comp (lmulTriple k k') (fun a ha => ?_) hx
  refine isNilpotent_mem_ker_lmul' a (RingHom.mem_ker.mpr ?_)
  have h : Algebra.TensorProduct.lmul' k a * (1 : k') = 0 := ha
  simpa using h

end Stacks.PurelyInseparable

end
