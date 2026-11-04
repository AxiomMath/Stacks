module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Associated primes of a module with a finite filtration by prime cyclic quotients

Throughout, `R` is a commutative ring and `M` an `R`-module. Following the Stacks
project, a prime ideal `p` of `R` is an *associated prime* of `M` when `p` occurs as
the annihilator `Ann_R(m) = {r ∈ R | r • m = 0}` of a single element `m ∈ M`, and
`Ass(M)` denotes the set of such primes. This is the radical-free notion: it is in
general stronger than Mathlib's `IsAssociatedPrime`, which asks only that `p` be the
radical of such an annihilator.

## Main definitions

* `annihilatorOfElem R M m`: the ideal `Ann_R(m)`.
* `IsAssPrime R M p`: `p` is prime and equals `Ann_R(m)` for some `m : M`.
* `assPrimes R M`: the set `Ass(M)` of associated primes of `M`.

## Main results

* `mem_annOfElem_iff` and `isAssPrime_iff_injective` unfold the definitions:
  `r ∈ Ann_R(m) ↔ r • m = 0`, and `p ∈ Ass(M)` iff `p` is prime and there is an
  injective `R`-linear map `R ⧸ p ↪ M` (which sends `⟦1⟧` to the witness `m`).
* `assPrimes_congr`: `Ass(M)` is invariant under `R`-linear isomorphism.
* `assPrimes_quotient_subset`: `Ass(R ⧸ q) ⊆ {q}` for a prime ideal `q`.
* `assPrimes_le_submodule_sup_quotient` (Stacks tag 00L9): additivity along the short
  exact sequence `0 → N → P → P ⧸ N → 0`, that is `Ass(P) ⊆ Ass(N) ∪ Ass(P ⧸ N)`.
* `ass_subset_of_filtration` (Stacks tag 00LB): if `M` admits a finite filtration
  `0 = M_0 ⊆ M_1 ⊆ ⋯ ⊆ M_n = M` by `R`-submodules whose successive quotients satisfy
  `M_i / M_{i-1} ≅ R ⧸ p_i` for prime ideals `p_i`, then `Ass(M) ⊆ {p_1, …, p_n}`.
  This is an inclusion only; equality need not hold.

## Implementation notes

The filtration is `0`-indexed as `Mfil : Fin (n + 1) → Submodule R M` with
`Mfil 0 = ⊥` and `Mfil (Fin.last n) = ⊤`, and the primes as `p : Fin n → Ideal R`;
the successive quotient at index `i : Fin n` is `Mfil i.succ` modulo `Mfil i.castSucc`.

Primality of each `p i` is essential rather than cosmetic: over `R = k[x]` the module
`M = R ⧸ (x ^ 2)` has associated prime `(x)`, not `(x ^ 2)`.

The main theorem is proved by induction on `k : Fin (n + 1)` for the claim
`Ass(Mfil k) ⊆ Set.range p`, using additivity at each step and transporting the
sub- and quotient pieces along `Submodule.comapSubtypeEquivOfLe` and the supplied
isomorphisms; the statement for `M` follows at `k = Fin.last n` via
`Submodule.topEquiv`.
-/

@[expose] public section

open Submodule

/-- The annihilator (in `R`) of an element `m` of an `R`-module `M`:
the ideal of `r ∈ R` with `r • m = 0`. -/
def annihilatorOfElem (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] (m : M) : Ideal R :=
  (R ∙ m).annihilator

/-- A prime ideal `p` is an *associated prime* of `M` if it occurs as the
annihilator of some element of `M`. This is the Stacks-project definition. -/
@[sga "2 III 1.1"]
def IsAssPrime (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] (p : Ideal R) : Prop :=
  p.IsPrime ∧ ∃ m : M, p = annihilatorOfElem R M m

/-- The set of associated primes of `M`. -/
@[sga "2 III 1.1"]
def assPrimes (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] : Set (Ideal R) :=
  {p | IsAssPrime R M p}

/-- `r` annihilates `m` iff `r ∈ annihilatorOfElem R M m`. -/
@[ega "0 1.7.4" "one generator"]
theorem mem_annOfElem_iff (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (m : M) (r : R) : r ∈ annihilatorOfElem R M m ↔ r • m = 0 := by
  unfold annihilatorOfElem
  rw [Submodule.mem_annihilator_span_singleton]

/-- A prime `p` is associated to `M` iff there is an injective `R`-linear map
`R ⧸ p ↪ M`. This is the standard alternative characterization of `Ass(M)`. -/
theorem isAssPrime_iff_injective (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (p : Ideal R) :
    IsAssPrime R M p ↔
      p.IsPrime ∧ ∃ f : (R ⧸ p) →ₗ[R] M, Function.Injective f := by
  unfold IsAssPrime annihilatorOfElem
  refine and_congr_right fun hp => ?_
  constructor
  · -- forward: from `m` with `p = ann(m)`, the map `r ↦ r • m : R → M` has kernel
    -- `ann(m) = p`, so it factors through an injective map `R/p ↪ M`.
    rintro ⟨m, hm⟩
    have hker : LinearMap.ker (LinearMap.toSpanSingleton R M m) = p := by
      rw [← annihilator_span_singleton m, hm]
    exact ⟨p.liftQ (LinearMap.toSpanSingleton R M m) (le_of_eq hker.symm), by
      rw [← LinearMap.ker_eq_bot, Submodule.ker_liftQ_eq_bot' _ _ hker.symm]⟩
  · -- backward: set `m = f(⟦1⟧)`. Then `r • m = f(⟦r⟧)`, so by injectivity of `f`,
    -- `r • m = 0 ↔ ⟦r⟧ = 0 ↔ r ∈ p`; hence `ann(m) = p`.
    rintro ⟨f, hf⟩
    refine ⟨f (Ideal.Quotient.mk p 1), ?_⟩
    ext r
    rw [Submodule.mem_annihilator_span_singleton]
    have key : r • f (Ideal.Quotient.mk p 1) = f (Ideal.Quotient.mk p r) := by
      rw [← LinearMap.map_smul]
      congr 1
      rw [Algebra.smul_def]
      simp
    rw [key, map_eq_zero_iff f hf, Ideal.Quotient.eq_zero_iff_mem]

/-- `assPrimes` is invariant under `R`-linear isomorphism. If `e : M ≃ₗ[R] N`,
then `M` and `N` have the same associated primes, since `ann(m) = ann(e m)`
(as `e` is an `R`-linear bijection: `r • m = 0 ↔ r • (e m) = e (r • m) = 0`). -/
theorem assPrimes_congr {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    assPrimes R M = assPrimes R N := by
  -- The `IsPrime` conjunct is shared, so only the witnesses have to be transported,
  -- and they may be transported because `e` preserves annihilators.
  have hann (m : M) : annihilatorOfElem R N (e m) = annihilatorOfElem R M m :=
    Ideal.ext fun r => by
      rw [mem_annOfElem_iff, mem_annOfElem_iff, ← e.map_smul, e.map_eq_zero_iff]
  ext p
  unfold assPrimes IsAssPrime
  simp only [Set.mem_ofPred_eq]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨e m, by rw [hann, hm]⟩
  · rintro ⟨n, hn⟩
    exact ⟨e.symm n, by rw [← hann, e.apply_symm_apply, hn]⟩

/-- The annihilator of a zero element is `⊤`, so it is not prime. -/
private theorem not_isPrime_annihilatorOfElem_of_eq_zero {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {m : M} (hm : m = 0) :
    ¬ (annihilatorOfElem R M m).IsPrime := fun h =>
  h.ne_top <| (Ideal.eq_top_iff_one _).2 <| (mem_annOfElem_iff R M m 1).2 (by simp [hm])

/-- **`Ass(R/q) = {q}` (the easy half: ⊆).** For a prime ideal `q`, the only
associated prime of `R/q` is `q` itself. Indeed `R/q` is a domain; for any
nonzero class `x̄`, `r • x̄ = 0 ↔ r x ∈ q ↔ r ∈ q` (using `x ∉ q` and primality),
so `ann(x̄) = q`; and for `x̄ = 0`, `ann = ⊤` is not prime. Hence every annihilator
of an element that is a prime ideal equals `q`. -/
theorem assPrimes_quotient_subset {R : Type*} [CommRing R] (q : Ideal R) (hq : q.IsPrime) :
    assPrimes R (R ⧸ q) ⊆ {q} := by
  -- Writing the witness as `x̄ = Quotient.mk q x`, the chain of equivalences
  -- `r ∈ ann(x̄) ↔ r • x̄ = 0 ↔ r * x ∈ q ↔ r ∈ q`
  -- identifies `ann(x̄)` with `q`, the last step using primality of `q` and `x ∉ q`.
  rintro p ⟨hp_prime, xbar, hx⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective xbar
  -- First: `x ∉ q`, else `ann = ⊤` contradicting primality of `p`.
  have hxq : x ∉ q := fun hxmem => by
    exact not_isPrime_annihilatorOfElem_of_eq_zero (Ideal.Quotient.eq_zero_iff_mem.mpr hxmem)
      (hx ▸ hp_prime)
  rw [Set.mem_singleton_iff]
  ext r
  rw [hx, mem_annOfElem_iff]
  have hsmul : r • Ideal.Quotient.mk q x = Ideal.Quotient.mk q (r * x) := by
    rw [Algebra.smul_def, map_mul]
    rfl
  have := hq
  rw [hsmul, Ideal.Quotient.eq_zero_iff_mem, Ideal.IsPrime.mul_mem_right_iff hxq]

/-- **Stacks Tag 00L9 (additivity of Ass in a short exact sequence).** For a
submodule `N` of `P`, every associated prime of `P` is an associated prime of `N`
or of `P/N`. Proof: let `p = ann(m)` for `m ∈ P`. Consider the cyclic submodule
`R • m`. If `R • m ∩ N = 0`, then `m` maps injectively to `P/N` and
`ann(m̄) = ann(m) = p`, so `p ∈ Ass(P/N)`. Otherwise pick `r` with `r • m ∈ N`,
`r • m ≠ 0`; since `p` is prime, `ann(r • m) = (p : r) = p` (as `r ∉ p`), so
`p ∈ Ass(N)`. -/
@[ega "IV 3.1.7" "(i), special case"]
theorem assPrimes_le_submodule_sup_quotient {R P : Type*} [CommRing R] [AddCommGroup P]
    [Module R P] (N : Submodule R P) :
    assPrimes R P ⊆ assPrimes R N ∪ assPrimes R (P ⧸ N) := by
  -- The case split is on whether the cyclic submodule `R ∙ m` meets `N` nontrivially.
  rintro p ⟨hp_prime, m, hm⟩
  by_cases hcase : ∀ r : R, r • m ∈ N → r • m = 0
  · -- `(R ∙ m) ⊓ N = ⊥`, so `m` survives in `P ⧸ N` with the same annihilator:
    -- `r • m̄ = 0 ↔ r • m ∈ N ↔ r • m = 0 ↔ r ∈ p`.
    right
    refine ⟨hp_prime, Submodule.Quotient.mk m, ?_⟩
    rw [hm]
    ext r
    rw [mem_annOfElem_iff, mem_annOfElem_iff, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero]
    exact ⟨fun hr => hr ▸ N.zero_mem, hcase r⟩
  · -- Some `r • m` is a nonzero element of `N`; as `p` is prime and `r ∉ p`, the
    -- colon ideal `(p : r)` collapses to `p`, so `ann(r • m) = p` inside `N`.
    left
    simp only [not_forall, exists_prop] at hcase
    obtain ⟨r, hmem, hne⟩ := hcase
    have hr_notin : r ∉ p := by rwa [hm, mem_annOfElem_iff]
    refine ⟨hp_prime, ⟨r • m, hmem⟩, Ideal.ext fun s => ?_⟩
    rw [mem_annOfElem_iff]
    have hcoe : (s • (⟨r • m, hmem⟩ : N) = 0) ↔ (s * r) • m = 0 := by
      rw [← Subtype.coe_inj, Submodule.coe_smul]
      simp only [ZeroMemClass.coe_zero, mul_smul]
    have hsm : (s * r) • m = 0 ↔ (s * r) ∈ p := by
      rw [hm, mem_annOfElem_iff]
    have := hp_prime
    rw [hcoe, hsm, Ideal.IsPrime.mul_mem_right_iff hr_notin]

/-- **Stacks Tag 00LB.** If `M` admits a finite filtration by `R`-submodules
`0 = M_0 ⊆ M_1 ⊆ ... ⊆ M_n = M` whose successive quotients `M_i / M_{i-1}` are
isomorphic to `R / p_i` for prime ideals `p_i`, then every associated prime of
`M` is among the `p_i`. -/
@[stacks 00LB]
theorem ass_subset_of_filtration
    (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (n : ℕ) (Mfil : Fin (n + 1) → Submodule R M)
    (hbot : Mfil 0 = ⊥) (htop : Mfil (Fin.last n) = ⊤)
    (hmono : Monotone Mfil)
    (p : Fin n → Ideal R)
    (hp : ∀ i : Fin n, (p i).IsPrime)
    (hquot : ∀ i : Fin n,
      Nonempty (((Mfil i.succ) ⧸ (Submodule.comap (Mfil i.succ).subtype (Mfil i.castSucc)))
        ≃ₗ[R] (R ⧸ p i))) :
    assPrimes R M ⊆ Set.range p := by
  -- Induct along the filtration: each stage `Mfil k` has all of its associated primes
  -- among the `p i`, because the stage splits as an extension of `Mfil k.castSucc` by a
  -- quotient isomorphic to `R ⧸ p k`, and `Ass` is subadditive for such extensions.
  have key : ∀ k : Fin (n + 1), assPrimes R (Mfil k) ⊆ Set.range p := by
    intro k
    induction k using Fin.induction with
    | zero =>
      -- `Mfil 0 = ⊥` is the zero module, whose only element has annihilator `⊤`;
      -- since `⊤` is not prime, `Ass(⊥) = ∅`.
      have : Subsingleton ↥(Mfil 0) := by
        rw [hbot]
        infer_instance
      rintro p' ⟨hp_prime, z, rfl⟩
      exact (not_isPrime_annihilatorOfElem_of_eq_zero (Subsingleton.elim z 0) hp_prime).elim
    | succ i ih =>
      -- `Nsub` is `Mfil i.castSucc` viewed inside `Mfil i.succ`, so that
      -- `Mfil i.succ` is an extension of `Nsub` by `Mfil i.succ ⧸ Nsub ≅ R ⧸ p i`.
      set Nsub : Submodule R ↥(Mfil i.succ) :=
        Submodule.comap (Mfil i.succ).subtype (Mfil i.castSucc)
      have hle : Mfil i.castSucc ≤ Mfil i.succ := hmono (Fin.castSucc_le_succ i)
      -- `↥Nsub ≃ₗ ↥(Mfil i.castSucc)`
      have hN : assPrimes R ↥Nsub ⊆ Set.range p :=
        (assPrimes_congr (Submodule.comapSubtypeEquivOfLe hle)).subset.trans ih
      -- `P ⧸ Nsub ≃ₗ R ⧸ p i`
      have hQ : assPrimes R (↥(Mfil i.succ) ⧸ Nsub) ⊆ Set.range p :=
        (assPrimes_congr (hquot i).some).subset.trans <|
          (assPrimes_quotient_subset (p i) (hp i)).trans
            (Set.singleton_subset_iff.mpr (Set.mem_range_self i))
      exact (assPrimes_le_submodule_sup_quotient Nsub).trans (Set.union_subset hN hQ)
  -- The top stage is all of `M`: transport along `M ≃ₗ[R] ↥(Mfil (Fin.last n))`.
  exact (assPrimes_congr ((Submodule.topEquiv (R := R) (M := M)).symm.trans
    (LinearEquiv.ofEq _ _ htop.symm))).subset.trans (key _)
