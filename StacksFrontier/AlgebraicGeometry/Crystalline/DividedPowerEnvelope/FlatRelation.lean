module

public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Decomposing a relation over a flat quotient extension

Let `φ : B → B'` carry an ideal `I ⊆ B` into an ideal `I' ⊆ B'`, and suppose the induced
homomorphism `B ⧸ I → B' ⧸ I'` is flat. A finitely supported `B'`-linear relation among the
images `φ (f t)` of a family `f : T → B`, whose value lies in `I'`, is then — modulo `I'` —
a `B'`-linear combination of finitely many relations among the `f t` themselves whose values
lie in `I`.

## Main results

* `Ideal.flat_relation_decomposition` is that decomposition.

## Implementation notes

This is the equational criterion for flatness, `Module.Flat.isTrivialRelation_of_sum_smul_eq_zero`,
applied to the relation read in `B' ⧸ I'` over `B ⧸ I`, with the resulting coefficients lifted
back along the two quotient maps. The supports of the produced relations are contained in the
support of the given one, which is what lets the conclusion be used to rewrite a single
generator of an ideal of relations.

## References

* [Stacks Project, Tag 07HE](https://stacks.math.columbia.edu/tag/07HE)
-/

@[expose] public section

universe u v

namespace Ideal

/-- A relation among the images `φ (f t)` whose value lies in `I'` is, modulo `I'`, a
`B'`-linear combination of relations among the `f t` whose values lie in `I`. -/
public lemma flat_relation_decomposition
    {B B' : Type u} [CommRing B] [CommRing B']
    (I : Ideal B) (I' : Ideal B') (φ : B →+* B')
    (hI : I.map φ ≤ I')
    (hflat : RingHom.Flat (Ideal.quotientMap I' φ
      (Ideal.map_le_iff_le_comap.mp hI)))
    {T : Type u} (f : T → B) (r : T →₀ B')
    (hr : r.sum (fun t a => a * φ (f t)) ∈ I') :
    ∃ (k : ℕ) (c : Fin k → B') (s : Fin k → T →₀ B),
      (∀ j, (s j).sum (fun t a => a * f t) ∈ I) ∧
      (∀ j, (s j).support ⊆ r.support) ∧
      ∀ t, r t - ∑ j, c j * φ (s j t) ∈ I' := by
  classical
  let : Algebra (B ⧸ I) (B' ⧸ I') :=
    (Ideal.quotientMap I' φ (Ideal.map_le_iff_le_comap.mp hI)).toAlgebra
  have : Module.Flat (B ⧸ I) (B' ⧸ I') := hflat
  let S := r.support
  let x : S → (B' ⧸ I') := fun t => Ideal.Quotient.mk I' (r t.1)
  have hscalar (b : B) (z : B') :
      Ideal.Quotient.mk I b • Ideal.Quotient.mk I' z =
      Ideal.Quotient.mk I' (φ b * z) := by
    show Ideal.quotientMap I' φ (Ideal.map_le_iff_le_comap.mp hI)
      (Ideal.Quotient.mk I b) * Ideal.Quotient.mk I' z = _
    rw [Ideal.quotientMap_mk]
    exact (map_mul (Ideal.Quotient.mk I') (φ b) z).symm
  have hrel : ∑ t : S, (Ideal.Quotient.mk I (f t.1)) • x t = 0 := by
    calc
      ∑ t : S, (Ideal.Quotient.mk I (f t.1)) • x t =
          Ideal.Quotient.mk I' (r.sum (fun t a => a * φ (f t))) := by
        rw [Finsupp.sum, map_sum]
        calc
          ∑ t : S, (Ideal.Quotient.mk I (f t.1)) • x t =
              ∑ t : S, Ideal.Quotient.mk I' (φ (f t.1) * r t.1) :=
            Finset.sum_congr rfl fun t _ => hscalar (f t.1) (r t.1)
          _ = ∑ t ∈ S, Ideal.Quotient.mk I' (φ (f t) * r t) :=
            Finset.sum_coe_sort S fun t => Ideal.Quotient.mk I' (φ (f t) * r t)
          _ = ∑ t ∈ S, Ideal.Quotient.mk I' (r t * φ (f t)) :=
            Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
      _ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hr
  obtain ⟨k, a, y, ha, hb⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  choose aLift haLift using fun (t : S) (j : Fin k) => Ideal.Quotient.mk_surjective (a t j)
  choose c hc using fun j => Ideal.Quotient.mk_surjective (y j)
  let aLiftT : T → Fin k → B := fun t j =>
    if ht : t ∈ S then aLift ⟨t, ht⟩ j else 0
  let s : Fin k → T →₀ B := fun j => Finsupp.onFinset S (aLiftT · j) (by
    intro t ht
    by_contra hnot
    simp [aLiftT, hnot] at ht)
  have hs_eval (j : Fin k) (t : S) : s j t = aLift t j := by simp [s, aLiftT]
  refine ⟨k, c, s, fun j => ?_, fun _ => Finsupp.support_onFinset_subset, fun t => ?_⟩
  · have hs : (s j).sum (fun t a => a * f t) =
        ∑ t : S, aLift t j * f t.1 := by
      rw [Finsupp.onFinset_sum _ fun _ => zero_mul _, ← Finset.sum_coe_sort]
      exact Finset.sum_congr rfl fun t _ => congrArg (· * f t.1) (hs_eval j t)
    refine Ideal.Quotient.eq_zero_iff_mem.mp ?_
    rw [hs, map_sum]
    simpa only [map_sum, map_mul, ← haLift, mul_comm] using hb j
  · by_cases ht : t ∈ S
    · let tS : S := ⟨t, ht⟩
      have hcoef' : Ideal.Quotient.mk I' (r t) =
          ∑ j, Ideal.Quotient.mk I' (c j * φ (aLift tS j)) := by
        calc
          Ideal.Quotient.mk I' (r t) = x tS := rfl
          _ = ∑ j, a tS j • y j := ha tS
          _ = ∑ j, Ideal.Quotient.mk I' (c j * φ (aLift tS j)) := by
            simp [hscalar, ← haLift, ← hc, mul_comm]
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      have hs' (j : Fin k) : s j t = aLift tS j := hs_eval j tS
      have hres := congrArg (fun z : B' ⧸ I' =>
        z - ∑ j, Ideal.Quotient.mk I' (c j * φ (s j t))) hcoef'
      rw [← map_sum, ← map_sub] at hres
      simpa [hs', map_sum] using hres
    · apply Ideal.Quotient.eq_zero_iff_mem.mp
      simp [s, aLiftT, ht, Finsupp.notMem_support_iff.mp ht]

end Ideal
