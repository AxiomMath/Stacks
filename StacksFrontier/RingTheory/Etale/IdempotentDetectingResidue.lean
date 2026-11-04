module

public import StacksFrontier.RingTheory.Etale.LocalStructure

/-!
# An idempotent detecting `a ≡ 1` at the primes over a fibre, after an étale extension

Let `R → M` be a ring map, `a ∈ M` integral over `R` and `p` a prime of `R`.  After an étale
base change `R → R'`, at a prime `p'` over `p`, there is an idempotent `ε` of `R' ⊗_R M` which
detects, at every prime of `R' ⊗_R M` lying over `p'`, whether `a` is congruent to `1`: for every
ring map `χ` from `R' ⊗_R M` to a field whose kernel meets `R'` in `p'`, `χ(ε) ≠ 0` if and only if
`χ(1 ⊗ a) = 1`.

This is the commutative-algebra input of the connectedness clause of the Stein factorization
for algebraic spaces (Stacks 0A1C) in this library: there it splits a clopen part of a fibre
off an étale neighbourhood of the base point.

## Main results

* `Algebra.exists_etale_isIdempotentElem_detecting_sub_one`.

## Implementation notes

The subalgebra `D = R[a]` of `M` is finite over `R` because `a` is integral.  Stacks 00UK
(`Algebra.exists_etale_completeOrthogonalIdempotents_finite_not_quasiFiniteAt`) splits
`R' ⊗_R D = A₁ × ⋯ × Aₙ × B` with `Aᵢ` having a single prime `rᵢ` over `p'` and `R' → B`
quasi-finite at no prime over `p'`.  As `R' ⊗_R D` is finite over `R'`, it is quasi-finite at
every prime, so `B` has no prime over `p'`, and every prime over `p'` is one of the `rᵢ`.  The
idempotent is the image in `R' ⊗_R M` of the sum of the idempotents of those `Aᵢ` with
`1 ⊗ a ≡ 1` modulo `rᵢ`.

## References

* [Stacks Project, Tag 00UK](https://stacks.math.columbia.edu/tag/00UK)
-/

@[expose] public section

open TensorProduct

universe u

/-- Given orthogonal idempotents `e` and a prime `q` missing `e j`, a partial sum of the `e i`
lies in `q` exactly when it omits `j`. -/
theorem OrthogonalIdempotents.sum_mem_iff_notMem_of_notMem {S ι : Type*} [CommRing S]
    {e : ι → S} (he : OrthogonalIdempotents e) {q : Ideal S} [hq : q.IsPrime] {j : ι}
    (hj : e j ∉ q) (I : Finset ι) : ∑ i ∈ I, e i ∈ q ↔ j ∉ I := by
  classical
  have hother : ∀ i, i ≠ j → e i ∈ q := fun i hi =>
    (hq.mem_or_mem (he.ortho hi ▸ q.zero_mem : e i * e j ∈ q)).resolve_right hj
  refine ⟨fun hmem hjI => hj ?_, fun hjI => Ideal.sum_mem _ fun i hi => hother i fun h =>
    hjI (h ▸ hi)⟩
  rw [← Finset.add_sum_erase I e hjI] at hmem
  exact (Ideal.add_mem_iff_left q
    (Ideal.sum_mem _ fun i hi => hother i (Finset.ne_of_mem_erase hi))).1 hmem

/-- Some member of a complete family of orthogonal idempotents lies outside a given prime. -/
theorem CompleteOrthogonalIdempotents.exists_notMem {S ι : Type*} [CommRing S] [Fintype ι]
    {e : ι → S} (he : CompleteOrthogonalIdempotents e) (q : Ideal S) [hq : q.IsPrime] :
    ∃ j, e j ∉ q := by
  by_contra hall
  simp only [not_exists, not_not] at hall
  refine hq.ne_top ((Ideal.eq_top_iff_one q).2 ?_)
  rw [← he.complete]
  exact Ideal.sum_mem _ fun j _ => hall j

namespace Algebra

/-- **An idempotent detecting `a ≡ 1` along the fibre over `p`, after an étale extension.**  Let
`a ∈ M` be integral over `R` and `p` a prime of `R`.  There are an étale `R`-algebra `R'`, a prime
`p'` of `R'` lying over `p`, and an idempotent `ε` of `R' ⊗_R M` such that for every ring map `χ`
from `R' ⊗_R M` to a field with `χ ∘ (R' → R' ⊗_R M)` of kernel `p'`, `χ(ε) ≠ 0` if and only if
`χ(1 ⊗ (a - 1)) = 0`. -/
theorem exists_etale_isIdempotentElem_detecting_sub_one {R M : Type u} [CommRing R]
    [CommRing M] [Algebra R M] {a : M} (ha : IsIntegral R a) (p : Ideal R) [p.IsPrime] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (p' : Ideal R') (_ : p'.IsPrime) (_ : p'.LiesOver p) (ε : R' ⊗[R] M),
      IsIdempotentElem ε ∧
      ∀ {K : Type*} [Field K] (χ : R' ⊗[R] M →+* K),
        RingHom.ker (χ.comp (TensorProduct.includeLeftRingHom (R := R))) = p' →
        (χ ε ≠ 0 ↔ χ (1 ⊗ₜ (a - 1)) = 0) := by
  classical
  set D : Subalgebra R M := Algebra.adjoin R {a}
  have : Module.Finite R D := Algebra.finite_adjoin_simple_of_isIntegral ha
  have : Algebra.FiniteType R D := inferInstance
  obtain ⟨R', _, _, _, p', _, _, n, e, he, r, hr, hrl, -, -, hne, huniq, hB⟩ :=
    Algebra.exists_etale_completeOrthogonalIdempotents_finite_not_quasiFiniteAt (S := D) p
  let ι : R' ⊗[R] D →ₐ[R'] R' ⊗[R] M :=
    Algebra.TensorProduct.map (AlgHom.id R' R') D.val
  let aD : D := ⟨a, Algebra.subset_adjoin rfl⟩
  let I : Finset (Fin n) := Finset.univ.filter fun i => (1 ⊗ₜ (aD - 1) : R' ⊗[R] D) ∈ r i
  let εD : R' ⊗[R] D := ∑ i ∈ I, e i.castSucc
  have hortho := he.toOrthogonalIdempotents
  have hεD : IsIdempotentElem εD := (hortho.embedding Fin.castSuccEmb).isIdempotentElem_sum (s := I)
  refine ⟨R', inferInstance, inferInstance, inferInstance, p', inferInstance, inferInstance,
    ι εD, hεD.map ι, ?_⟩
  intro K _ χ hχ
  let χ' : R' ⊗[R] D →+* K := χ.comp ι.toRingHom
  let q : Ideal (R' ⊗[R] D) := RingHom.ker χ'
  have hq : q.IsPrime := RingHom.ker_isPrime χ'
  have hqo : q.LiesOver p' := by
    refine ⟨?_⟩
    rw [← hχ]
    ext s
    simp only [Ideal.under, Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply, q, χ']
    change χ (ι (algebraMap R' (R' ⊗[R] D) s)) = 0 ↔ χ (s ⊗ₜ 1) = 0
    rw [Algebra.TensorProduct.algebraMap_apply]
    simp [ι]
  have : Module.Finite R' (R' ⊗[R] D) := Module.Finite.base_change R R' D
  have hlast : e (Fin.last n) ∈ q := by
    by_contra hmem
    exact hB q hqo hmem (Algebra.QuasiFinite.instLocalization q.primeCompl)
  obtain ⟨j, hj⟩ := he.exists_notMem q
  obtain ⟨i₀, rfl⟩ : ∃ i₀ : Fin n, i₀.castSucc = j :=
    ⟨j.castPred fun h => hj (h ▸ hlast), Fin.castSucc_castPred _ _⟩
  have hkey : χ (ι εD) ≠ 0 ↔ i₀ ∈ I := by
    change χ' εD ≠ 0 ↔ i₀ ∈ I
    rw [← not_iff_not, not_not]
    exact (hortho.embedding Fin.castSuccEmb).sum_mem_iff_notMem_of_notMem hj I
  rw [hkey, show χ (1 ⊗ₜ (a - 1)) = χ' (1 ⊗ₜ (aD - 1)) by simp [χ', ι, aD]]
  change i₀ ∈ I ↔ (1 ⊗ₜ (aD - 1) : R' ⊗[R] D) ∈ q
  rw [huniq i₀ q hq hqo hj]
  simp [I]

end Algebra

end
