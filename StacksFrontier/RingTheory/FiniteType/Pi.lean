module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.RingHom.FiniteType

/-!
# Finite type for a finite product of algebras

A product, over a finite index type, of algebras of finite type is of finite type: adjoin the
idempotents `Pi.single i 1` to the images under `Pi.single i` of generators of the factors.  The
elements of the `i`-th factor whose `Pi.single i` lies in the resulting subalgebra form a
subalgebra of that factor containing its generators, so all of them do, and every element of the
product is the sum of its components.

## Main results

* `Algebra.FiniteType.pi`: a product of finitely many algebras of finite type is of finite type.
* `RingHom.FiniteType.pi`: `RingHom.pi f` is of finite type when each component is.
-/

@[expose] public section

universe u v w

/-- A product, over a finite index type, of algebras of finite type is of finite type. -/
public theorem Algebra.FiniteType.pi {R : Type u} [CommRing R] {ι : Type v}
    [_root_.Finite ι] (C : ι → Type w) [∀ i, CommRing (C i)] [∀ i, Algebra R (C i)]
    [∀ i, Algebra.FiniteType R (C i)] : Algebra.FiniteType R (∀ i, C i) := by
  classical
  cases nonempty_fintype ι
  choose s hs using fun i ↦ (Algebra.FiniteType.out (R := R) (A := C i))
  set T : Finset (∀ i, C i) :=
    (Finset.univ.biUnion fun i ↦ (s i).image (Pi.single i)) ∪
      (Finset.univ.image fun i ↦ Pi.single i (1 : C i))
  refine ⟨T, Algebra.eq_top_iff.mpr fun y ↦ ?_⟩
  have he : ∀ i, Pi.single i (1 : C i) ∈ Algebra.adjoin R (T : Set (∀ i, C i)) := fun i ↦
    Algebra.subset_adjoin (Finset.mem_coe.mpr
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))))
  have hsingle : ∀ i (x : C i), Pi.single i x ∈ Algebra.adjoin R (T : Set (∀ i, C i)) := by
    intro i x
    have hx : x ∈ Algebra.adjoin R ((s i : Finset (C i)) : Set (C i)) := by
      rw [hs i]
      exact Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
        exact Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_union_left _
          (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
            Finset.mem_image_of_mem _ (Finset.mem_coe.mp hy)⟩)))
    | algebraMap r =>
        have heq : Pi.single i (algebraMap R (C i) r) =
            algebraMap R (∀ j, C j) r * Pi.single i (1 : C i) := by
          funext j
          by_cases h : j = i
          · subst h
            simp
          · simp [h]
        rw [heq]
        exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ r) (he i)
    | add y z hy hz ihy ihz =>
        rw [Pi.single_add]
        exact Subalgebra.add_mem _ ihy ihz
    | mul y z hy hz ihy ihz =>
        rw [Pi.single_mul]
        exact Subalgebra.mul_mem _ ihy ihz
  rw [← Finset.univ_sum_single y]
  exact Subalgebra.sum_mem _ fun i _ ↦ hsingle i (y i)

/-- A ring homomorphism into a product, over a finite index type, of algebras of finite type is
of finite type. -/
public theorem RingHom.FiniteType.pi {R : Type u} [CommRing R] {ι : Type v}
    [_root_.Finite ι] {C : ι → Type w} [∀ i, CommRing (C i)] (f : ∀ i, R →+* C i)
    (hf : ∀ i, (f i).FiniteType) : (RingHom.pi f).FiniteType := by
  let _ : ∀ i, Algebra R (C i) := fun i ↦ (f i).toAlgebra
  have _ : ∀ i, Algebra.FiniteType R (C i) := hf
  rw [show RingHom.pi f = algebraMap R (∀ i, C i) from rfl, RingHom.finiteType_algebraMap]
  exact Algebra.FiniteType.pi C

end
