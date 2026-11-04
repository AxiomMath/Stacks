module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.IsTensorProduct
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Three inputs to the étale-local reduction of 05IG

The reduction of [Stacks, Tag 05IG] to a local base with a projective module needs three small
facts, collected here because none of them is about weakly associated primes.

The first says that a flat base change does not kill a witness:  if `y` generates a cyclic
submodule whose annihilator is contained in the contraction of a prime `𝔮₁` of `S₁`, then the
image of `y` in a base change `S₁ ⊗_S Y` is nonzero.  Indeed `S/Ann(y) ↪ Y` stays injective after
tensoring with the flat module `S₁`, and the image of `1` is nonzero because `Ann(y) S₁ ⊆ 𝔮₁`.

The second is the contraction of an associated prime along a ring map:  the `A`-annihilator of a
witness is the contraction of its `B`-annihilator.

The third is prime avoidance in its crudest form:  finitely many ideals, none contained in a prime
`𝔮`, admit a common element outside `𝔮` — take the product of witnesses.  This is what chooses the
element to be inverted before the structure theorem [Stacks, Tag 05ID] is applied.

## Main results

* `Stacks.WeaklyAssociatedPrimes.ne_zero_of_isBaseChange_of_annihilator_le`
* `Stacks.WeaklyAssociatedPrimes.comap_mem_associatedPrimes_of_isScalarTower`
* `Stacks.WeaklyAssociatedPrimes.exists_notMem_and_forall_mem`

## References

* [Stacks Project, Tag 05IG](https://stacks.math.columbia.edu/tag/05IG)
* [Stacks Project, Tag 0CU6](https://stacks.math.columbia.edu/tag/0CU6)
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.WeaklyAssociatedPrimes

/-- **A flat base change does not kill a witness.**  Let `S → S₁` be flat, let `Y` be an
`S`-module and let `f : Y → Y₁` exhibit `Y₁` as the base change of `Y` to `S₁`.  If the
annihilator of `y : Y` is contained in the contraction of a prime `𝔮₁` of `S₁`, then
`f y ≠ 0`. -/
theorem ne_zero_of_isBaseChange_of_annihilator_le
    {S S₁ Y Y₁ : Type*} [CommRing S] [CommRing S₁] [Algebra S S₁] [Module.Flat S S₁]
    [AddCommGroup Y] [Module S Y] [AddCommGroup Y₁] [Module S Y₁] [Module S₁ Y₁]
    [IsScalarTower S S₁ Y₁]
    (f : Y →ₗ[S] Y₁) (hf : IsBaseChange S₁ f) {q₁ : Ideal S₁} (hq₁ : q₁ ≠ ⊤) {y : Y}
    (h : (S ∙ y).annihilator ≤ q₁.comap (algebraMap S S₁)) : f y ≠ 0 := by
  set J : Ideal S := (S ∙ y).annihilator with hJ
  -- `S ⧸ J` embeds in `Y` by `1 ↦ y`
  have hker : LinearMap.ker (LinearMap.toSpanSingleton S Y y) = J := by
    ext a
    simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, hJ,
      Submodule.mem_annihilator_span_singleton]
  let ψ : (S ⧸ J) →ₗ[S] Y := J.liftQ (LinearMap.toSpanSingleton S Y y) hker.ge
  have hψ : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ hker.le
  have hψ1 : ψ (1 : S ⧸ J) = y := one_smul S y
  intro hfy
  -- `y ⊗ 1 = 0`, hence `1 ⊗ 1 = 0`, hence `1 ∈ J S₁`
  have hy1 : y ⊗ₜ[S] (1 : S₁) = 0 := by
    have hcomm : (TensorProduct.comm S S₁ Y) ((1 : S₁) ⊗ₜ[S] y) = y ⊗ₜ[S] (1 : S₁) := rfl
    have h0 : (1 : S₁) ⊗ₜ[S] y = 0 := by
      have := hf.equiv_tmul (1 : S₁) y
      rw [hfy, smul_zero] at this
      exact (map_eq_zero_iff _ hf.equiv.injective).mp this
    rw [← hcomm, h0, map_zero]
  have h11 : (1 : S ⧸ J) ⊗ₜ[S] (1 : S₁) = 0 := by
    -- tensoring the embedding with the flat module `S₁`
    refine Module.Flat.rTensor_preserves_injective_linearMap ψ hψ ?_
    rw [LinearMap.rTensor_tmul, hψ1, hy1, map_zero]
  have hmem : (1 : S₁) ∈ J • (⊤ : Submodule S S₁) := by
    have := congrArg (TensorProduct.quotTensorEquivQuotSMul S₁ J) h11
    rw [map_zero, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul] at this
    exact (Submodule.Quotient.mk_eq_zero _).mp this
  -- but `J S₁` is contained in `𝔮₁`
  have hle : J • (⊤ : Submodule S S₁) ≤ Submodule.restrictScalars S q₁ := by
    refine Submodule.smul_le.mpr fun a ha x _ => ?_
    rw [Submodule.restrictScalars_mem, Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (h ha)
  exact hq₁ (q₁.eq_top_of_isUnit_mem (hle hmem) isUnit_one)

/-- Restriction of scalars along `A → B` contracts a prime associated to a `B`-module to a prime
associated to the same module read over `A`:  the `A`-colon ideal of a witness is the contraction
of its `B`-colon ideal. -/
@[ega "IV 3.1.10.1" "Contraction inclusion"]
theorem comap_mem_associatedPrimes_of_isScalarTower
    {A B X : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup X] [Module B X] [Module A X] [IsScalarTower A B X]
    {r : Ideal B} (hr : r ∈ associatedPrimes B X) :
    r.comap (algebraMap A B) ∈ associatedPrimes A X := by
  obtain ⟨hrp, z, hz⟩ := hr
  refine ⟨hrp.comap _, z, ?_⟩
  have hcolon : (⊥ : Submodule A X).colon {z}
      = ((⊥ : Submodule B X).colon {z}).comap (algebraMap A B) := by
    ext a
    simp [Ideal.mem_comap, Submodule.mem_colon_singleton, algebraMap_smul]
  rw [hcolon, ← Ideal.comap_radical, hz]

/-- **Prime avoidance, crude form.**  Finitely many ideals of `A`, none of them contained in a
prime `𝔮`, have a common element outside `𝔮`:  pick an element of each outside `𝔮` and multiply. -/
theorem exists_notMem_and_forall_mem {A : Type*} [CommRing A] (q : Ideal A) [q.IsPrime]
    {u : Set (Ideal A)} (hu : u.Finite) (h : ∀ I ∈ u, ¬ I ≤ q) :
    ∃ g : A, g ∉ q ∧ ∀ I ∈ u, g ∈ I := by
  classical
  suffices hfin : ∀ s : Finset (Ideal A), (∀ I ∈ s, ¬ I ≤ q) →
      ∃ g : A, g ∉ q ∧ ∀ I ∈ s, g ∈ I by
    obtain ⟨g, hgq, hg⟩ := hfin hu.toFinset fun I hI => h I (hu.mem_toFinset.mp hI)
    exact ⟨g, hgq, fun I hI => hg I (hu.mem_toFinset.mpr hI)⟩
  intro s
  induction s using Finset.induction_on with
  | empty =>
      exact fun _ => ⟨1, fun h1 => ‹q.IsPrime›.ne_top (q.eq_top_of_isUnit_mem h1 isUnit_one),
        by simp⟩
  | @insert I t _ ih =>
      intro hall
      obtain ⟨x, hxI, hxq⟩ := Set.not_subset.mp (hall I (Finset.mem_insert_self I t))
      obtain ⟨y, hyq, hy⟩ := ih fun K hK => hall K (Finset.mem_insert_of_mem hK)
      refine ⟨x * y, fun hz => (‹q.IsPrime›.mem_or_mem hz).elim hxq hyq, fun K hK => ?_⟩
      rcases Finset.mem_insert.mp hK with rfl | hK
      · exact Ideal.mul_mem_right y _ hxI
      · exact Ideal.mul_mem_left K x (hy K hK)

end Stacks.WeaklyAssociatedPrimes

end
