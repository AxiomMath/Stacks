module

public import StacksFrontier.RingTheory.Koszul.DerivedComparison

/-!
# A chain of Koszul comparison arrows

Let `f₁, …, f_r` be elements of a commutative ring `R`, let `K_m` be the Koszul differential
graded algebra with `d ξᵢ = fᵢ ^ m` and fix `t ≥ 1`. Tag 0GZ7
(`Koszul.exists_derivedComparisonArrow`) produces, for every `n ≥ t`, an index `N > n` and a
comparison map `σ : {}_NK_t ⟶ {}_N(K_n ⊗_R K_t)` in the derived category of left differential
graded `K_N`-modules whose two composites with the multiplication maps are the multiplication map
`μ_n` inverted and the transition map `τ_{N,n} ⊗ id`.

Iterating that produces a strictly increasing sequence of indices
`ι 0 = t < ι 1 < ι 2 < ⋯` together with, for every `k`, a comparison map at level `ι (k+1)`
relating `K_t` to `K_{ι k} ⊗_R K_t`. This file performs that iteration. Such a sequence of
indices, with its comparison maps, is exactly the data needed to exhibit the two systems
`({}_nK_t)` and `(K_n ⊗_R K_t)` of left differential graded `K_n`-modules as pro-isomorphic in
the derived category, which is the step of Tag 0GZJ that appeals to Tag 0GZ7.

## Main definitions

* `Koszul.DerivedComparisonStep`: one stage — an index `next > n` and the comparison map of Tag
  0GZ7 at that index, together with its two composite identities.
* `Koszul.derivedComparisonIdx`: the sequence of indices, obtained by iterating the stage from
  the starting index `t`.
* `Koszul.DerivedComparisonChain` and `Koszul.derivedComparisonChain`: the whole chain, and its
  construction.

## Implementation notes

The index produced by Tag 0GZ7 depends on a choice, so the sequence is built by recursion over a
subtype `{n // t ≤ n}` carrying the bound that the hypotheses of the Koszul transition maps need;
`Koszul.derivedComparisonIndex` is that recursion, written with `Nat.rec` so that its value at
`k + 1` reduces definitionally and the comparison map at stage `k` can be read off without a
transport.

## References

* [Stacks Project, Tag 0GZ7](https://stacks.math.columbia.edu/tag/0GZ7)
* [Stacks Project, Tag 0GZJ](https://stacks.math.columbia.edu/tag/0GZJ)
-/

@[expose] public noncomputable section

namespace Koszul

universe u

open CategoryTheory DifferentialGradedAlgebra DifferentialGradedModule

variable {R : Type u} [CommRing R] {r : ℕ}

section Step

/-- **One stage of the comparison of Tag 0GZ7.** For `n ≥ t ≥ 1` this records an index
`next > n`, the comparison map `{}_{next}K_t ⟶ {}_{next}(K_n ⊗_R K_t)` in the derived category of
left differential graded `K_{next}`-modules, and its two composites with the multiplication
maps. -/
structure DerivedComparisonStep (f : Fin r → R) {t : ℕ} (ht : 1 ≤ t) (n : ℕ) (htn : t ≤ n) where
  /-- The index at which the comparison map lives. -/
  next : ℕ
  /-- The index is strictly larger than `n`. -/
  lt_next : n < next
  /-- The comparison map `σ : {}_{next}K_t ⟶ {}_{next}(K_n ⊗_R K_t)`. -/
  arrow : (powDerived f next).obj (powRestrictedModule f ht (htn.trans lt_next.le)) ⟶
    (powDerived f next).obj (powTensorRestrictedModule f t (ht.trans htn) lt_next.le)
  /-- Postcomposing `σ` with the multiplication map `μ_n` is the identity. -/
  arrow_comp_mul :
    arrow ≫ (powDerived f next).map (powMulHom f ht htn lt_next.le) =
      CategoryStruct.id
        ((powDerived f next).obj (powRestrictedModule f ht (htn.trans lt_next.le)))
  /-- Precomposing `σ` with the multiplication map `μ_{next}` is `τ_{next,n} ⊗ id`. -/
  mul_comp_arrow :
    (powDerived f next).map (powMulBaseHom f ht (htn.trans lt_next.le)) ≫ arrow =
      (powDerived f next).map (powTransitionTensorHom f t (ht.trans htn) lt_next.le)

/-- A stage of the comparison exists for every `n ≥ t ≥ 1`: this is Tag 0GZ7. -/
theorem nonempty_derivedComparisonStep (f : Fin r → R) {t n : ℕ} (ht : 1 ≤ t) (htn : t ≤ n) :
    Nonempty (DerivedComparisonStep f ht n htn) := by
  obtain ⟨N, hnN, σ, hσ₁, hσ₂⟩ := exists_derivedComparisonArrow f ht htn
  exact ⟨⟨N, hnN, σ, hσ₁, hσ₂⟩⟩

/-- A chosen stage of the comparison at the index `n`. -/
def derivedComparisonStep (f : Fin r → R) {t : ℕ} (ht : 1 ≤ t) (n : ℕ) (htn : t ≤ n) :
    DerivedComparisonStep f ht n htn :=
  (nonempty_derivedComparisonStep f ht htn).some

end Step

section Index

variable (f : Fin r → R) {t : ℕ} (ht : 1 ≤ t)

/-- The sequence of indices of the chain, valued in the integers that are at least `t`: start at
`t` and pass at each stage to the index that Tag 0GZ7 produces. -/
def derivedComparisonIndex (k : ℕ) : {n : ℕ // t ≤ n} :=
  Nat.rec (motive := fun _ => {n : ℕ // t ≤ n}) ⟨t, le_rfl⟩
    (fun _ p => ⟨(derivedComparisonStep f ht p.1 p.2).next,
      p.2.trans (derivedComparisonStep f ht p.1 p.2).lt_next.le⟩) k

/-- The sequence of indices of the chain. -/
def derivedComparisonIdx (k : ℕ) : ℕ := (derivedComparisonIndex f ht k).1

/-- Every index of the chain is at least `t`. -/
theorem le_derivedComparisonIdx (k : ℕ) : t ≤ derivedComparisonIdx f ht k :=
  (derivedComparisonIndex f ht k).2

/-- The chain starts at `t`. -/
theorem derivedComparisonIdx_zero : derivedComparisonIdx f ht 0 = t := rfl

/-- The next index of the chain is the one that Tag 0GZ7 produces at the current one. -/
theorem derivedComparisonIdx_succ (k : ℕ) :
    derivedComparisonIdx f ht (k + 1) =
      (derivedComparisonStep f ht (derivedComparisonIdx f ht k)
        (le_derivedComparisonIdx f ht k)).next := rfl

/-- The indices of the chain increase strictly at each stage. -/
theorem lt_derivedComparisonIdx_succ (k : ℕ) :
    derivedComparisonIdx f ht k < derivedComparisonIdx f ht (k + 1) :=
  (derivedComparisonStep f ht (derivedComparisonIdx f ht k)
    (le_derivedComparisonIdx f ht k)).lt_next

/-- The sequence of indices of the chain is strictly increasing. -/
theorem derivedComparisonIdx_strictMono : StrictMono (derivedComparisonIdx f ht) :=
  strictMono_nat_of_lt_succ (lt_derivedComparisonIdx_succ f ht)

end Index

section Chain

/-- **A chain of Koszul comparison arrows.** A strictly increasing sequence of indices
`ι 0 < ι 1 < ⋯`, all at least `t`, together with for every `k` the comparison map
`{}_{ι (k+1)}K_t ⟶ {}_{ι (k+1)}(K_{ι k} ⊗_R K_t)` of Tag 0GZ7 and its two composites with the
multiplication maps. This is the data that exhibits the two systems `({}_nK_t)` and
`(K_n ⊗_R K_t)` as pro-isomorphic in the derived category. -/
structure DerivedComparisonChain (f : Fin r → R) {t : ℕ} (ht : 1 ≤ t) where
  /-- The sequence of indices. -/
  idx : ℕ → ℕ
  /-- Every index is at least `t`. -/
  le_idx : ∀ k, t ≤ idx k
  /-- The sequence of indices is strictly increasing. -/
  idx_strictMono : StrictMono idx
  /-- The comparison map `σ_k : {}_{ι (k+1)}K_t ⟶ {}_{ι (k+1)}(K_{ι k} ⊗_R K_t)`. -/
  arrow (k : ℕ) : (powDerived f (idx (k + 1))).obj
      (powRestrictedModule f ht ((le_idx k).trans (idx_strictMono (Nat.lt_succ_self k)).le)) ⟶
    (powDerived f (idx (k + 1))).obj
      (powTensorRestrictedModule f t (ht.trans (le_idx k))
        (idx_strictMono (Nat.lt_succ_self k)).le)
  /-- Postcomposing `σ_k` with the multiplication map `μ_{ι k}` is the identity. -/
  arrow_comp_mul (k : ℕ) :
    arrow k ≫ (powDerived f (idx (k + 1))).map
        (powMulHom f ht (le_idx k) (idx_strictMono (Nat.lt_succ_self k)).le) =
      CategoryStruct.id ((powDerived f (idx (k + 1))).obj
        (powRestrictedModule f ht ((le_idx k).trans (idx_strictMono (Nat.lt_succ_self k)).le)))
  /-- Precomposing `σ_k` with the multiplication map `μ_{ι (k+1)}` is `τ_{ι (k+1), ι k} ⊗ id`. -/
  mul_comp_arrow (k : ℕ) :
    (powDerived f (idx (k + 1))).map (powMulBaseHom f ht
        ((le_idx k).trans (idx_strictMono (Nat.lt_succ_self k)).le)) ≫ arrow k =
      (powDerived f (idx (k + 1))).map
        (powTransitionTensorHom f t (ht.trans (le_idx k))
          (idx_strictMono (Nat.lt_succ_self k)).le)

/-- **The chain of Koszul comparison arrows.** Iterating Tag 0GZ7 from the starting index `t`
produces a strictly increasing sequence of indices carrying a comparison map at every stage. -/
def derivedComparisonChain (f : Fin r → R) {t : ℕ} (ht : 1 ≤ t) :
    DerivedComparisonChain f ht where
  idx := derivedComparisonIdx f ht
  le_idx := le_derivedComparisonIdx f ht
  idx_strictMono := derivedComparisonIdx_strictMono f ht
  arrow k := (derivedComparisonStep f ht (derivedComparisonIdx f ht k)
    (le_derivedComparisonIdx f ht k)).arrow
  arrow_comp_mul k := (derivedComparisonStep f ht (derivedComparisonIdx f ht k)
    (le_derivedComparisonIdx f ht k)).arrow_comp_mul
  mul_comp_arrow k := (derivedComparisonStep f ht (derivedComparisonIdx f ht k)
    (le_derivedComparisonIdx f ht k)).mul_comp_arrow

end Chain

end Koszul

end
