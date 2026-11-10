module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import StacksCore.RingTheory.FiniteStability
public import StacksCore.Tactic.StacksAttribute

/-!
# Avoiding a prime while meeting the associated primes of a fibre

Let `R → S` be a finitely presented ring map, let `N` be a finitely presented `S`-module and
let `q` be a prime of `S` lying over a prime `p` of `R`. The associated primes of the fibre
module over the fibre ring `κ(p) ⊗[R] S` are finite in number, so one element of `S` outside
`q` can be chosen whose image lies in all of those associated primes which are not contained
in the extension of `q`.

## Main results

* `Stacks.PureModules.exists_not_mem_and_mem_associatedPrimes_not_le_fiberIdeal` produces the
  required element of `S`.

## Implementation notes

The fibre ring is Mathlib's `Ideal.Fiber`, with `p.Fiber S = κ(p) ⊗[R] S`, and the image of
`q` in it is the extension of `q` along the right tensor-factor map. The fibre module is the
standard base change `(p.Fiber S) ⊗[S] N`, canonically isomorphic to `N ⊗[R] κ(p)`.

## References

* [Stacks Project, Tag 0CU6](https://stacks.math.columbia.edu/tag/0CU6)
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.PureModules

/-- Given finitely many ideals of `B`, each of which contains the image under `f` of some
element outside the prime `q` of `A`, a single element outside `q` has its image in all of
them: multiply the witnesses together. -/
private lemma exists_not_mem_and_map_mem_all_of_finset
    {A B : Type*} [CommRing A] [CommRing B] (q : Ideal A) [q.IsPrime]
    (f : A →+* B) {s : Finset (Ideal B)}
    (h : ∀ I ∈ s, ∃ x : A, x ∉ q ∧ f x ∈ I) :
    ∃ x : A, x ∉ q ∧ ∀ I ∈ s, f x ∈ I := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, (Ideal.ne_top_iff_one q).mp ‹q.IsPrime›.ne_top, by simp⟩
  | @insert I t hIt ih =>
    obtain ⟨x, hxq, hxI⟩ := h I (by simp)
    obtain ⟨y, hyq, hy⟩ := ih fun K hK => h K (by simp [hK])
    refine ⟨x * y, fun hz => (‹q.IsPrime›.mem_or_mem hz).elim hxq hyq, fun K hK => ?_⟩
    rcases Finset.mem_insert.mp hK with rfl | hK
    · simpa using Ideal.mul_mem_right (f y) _ hxI
    · simpa using Ideal.mul_mem_left (I := K) (f x) (hy K hK)

/-- **Stacks Project, Tag 0CU6.** An element can be chosen outside `q` whose image in the
fibre lies in every associated prime of the fibre module that is not contained in the
extension of `q`. -/
@[stacks 0CU6]
theorem exists_not_mem_and_mem_associatedPrimes_not_le_fiberIdeal
    {R S N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [AddCommGroup N] [Module S N]
    [Module.FinitePresentation S N]
    (p : Ideal R) (q : Ideal S) [p.IsPrime] [q.IsPrime] [q.LiesOver p] :
    letI : Algebra S (p.Fiber S) := Algebra.TensorProduct.rightAlgebra
    ∃ g : S, g ∉ q ∧
      ∀ r ∈ associatedPrimes (p.Fiber S) (TensorProduct S (p.Fiber S) N),
        ¬ r ≤ Ideal.map
          (Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S).toRingHom q →
        (Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S) g ∈ r := by
  classical
  let _ : Algebra S (p.Fiber S) := Algebra.TensorProduct.rightAlgebra
  let _ : Algebra.FinitePresentation p.ResidueField (p.Fiber S) :=
    Algebra.FinitePresentation.baseChange (R := R) (A := S) (B := p.ResidueField)
  let _ : IsNoetherianRing (p.Fiber S) :=
    Algebra.FiniteType.isNoetherianRing p.ResidueField (p.Fiber S)
  let ι : S →ₐ[R] p.Fiber S := Algebra.TensorProduct.includeRight
  let J : Ideal (p.Fiber S) := Ideal.map ι.toRingHom q
  let u : Set (Ideal (p.Fiber S)) :=
    {r | r ∈ associatedPrimes (p.Fiber S) (TensorProduct S (p.Fiber S) N) ∧ ¬ r ≤ J}
  have hu : u.Finite :=
    (associatedPrimes.finite (p.Fiber S) (TensorProduct S (p.Fiber S) N)).subset fun _ hr => hr.1
  have hall : ∀ r ∈ hu.toFinset, ∃ x : S, x ∉ q ∧ ι.toRingHom x ∈ r := by
    intro r hr
    obtain ⟨a, har, haJ⟩ := Set.not_subset.mp (hu.mem_toFinset.mp hr).2
    obtain ⟨c, hcp, x, hx⟩ := Ideal.Fiber.exists_smul_eq_one_tmul p a
    refine ⟨x, fun hxq => haJ ?_, ?_⟩
    · have hca : c • a ∈ J := by
        rw [hx]
        exact Ideal.mem_map_of_mem _ hxq
      have hcunit : IsUnit (algebraMap R (p.Fiber S) c) := by
        rw [IsScalarTower.algebraMap_apply R p.ResidueField]
        exact (isUnit_iff_ne_zero.mpr (by simpa using hcp)).map _
      rwa [Algebra.smul_def, J.unit_mul_mem_iff_mem hcunit] at hca
    · change (1 ⊗ₜ[R] x) ∈ r
      rw [← hx, Algebra.smul_def]
      exact Ideal.mul_mem_left (I := r) _ har
  obtain ⟨g, hgq, hg⟩ := exists_not_mem_and_map_mem_all_of_finset q ι.toRingHom hall
  exact ⟨g, hgq, fun r hr hnot => hg r (hu.mem_toFinset.mpr ⟨hr, hnot⟩)⟩

end Stacks.PureModules
