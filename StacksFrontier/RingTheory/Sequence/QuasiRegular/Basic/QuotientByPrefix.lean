module

import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

public import StacksFrontier.RingTheory.Sequence.QuasiRegular.Defs.Defs
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.TensorProduct.IsBaseChangeSpan

@[expose] public section

open scoped Finset

/-!
# Quasi-regularity passes to the quotient by an initial segment of the sequence

Let `R` be a commutative ring, `M` an `R`-module and `f_0, …, f_{c-1} ∈ R` an `M`-quasi-regular
sequence, with `J = (f_0, …, f_{c-1})`. Fix `i` and put `K = (f_0, …, f_{i-1})`, `R̄ = R/K` and
`M̄ = M/KM`. This file proves Stacks 061R: the images `f̄_i, …, f̄_{c-1} ∈ R̄` form an
`M̄`-quasi-regular sequence.

Since the canonical map of tag 061N is always surjective, both hypothesis and conclusion are
injectivity of that map, and injectivity is degreewise elementary: it says exactly that a
relation `∑_{|e| = n} f^e m_e ∈ J^{n+1}M` forces `m_e ∈ JM` for every multi-index `e` of total
degree `n`. That equivalence is proved here in both directions
(`mem_of_sum_fpow_smul_mem`, `injective_of_mem_of_sum_fpow_smul_mem`) by identifying the source
`R̄[X_0, …, X_{c-1}] ⊗_{R̄} M̄` with the free `M̄`-module `(Fin c →₀ ℕ) →₀ M̄` on multi-indices
(`srcFinsuppEquiv`), so that a vanishing element of the source is literally a family of
coefficients that must vanish in `M̄ = M/JM`.

Granted that reformulation, the content of the lemma is the identity
`J^{n+1}M ∩ KM = K · J^n M`. Call a multi-index *marked* when it involves one of
`f_0, …, f_{i-1}`; the identity is `inf_le_monSub_markedIdx`, proved by induction on `n`: an
element of `J^{n+1}M ∩ KM` is, inductively, a sum of marked monomials `f^e m_e` of total degree
`n + 1`, and the degreewise relation condition puts every `m_e` into `JM`, which raises the total
degree by one while keeping the marked variable. Descending, a relation among the `ḡ^d` of degree
`n` in `M̄` lifts to a relation of degree `n` in `M` after subtracting such a marked element
(`exists_mem_monSub_markedIdx_of_mk_mem`), and marked multi-indices are distinguishable from those
coming from the tail `f_i, …, f_{c-1}`, so the lifted coefficient lands in `JM`
(`mem_smul_top_of_sum_sub_monSub_mem`) and its class lands in `J̄M̄`.

## Main results

* `Stacks.QuasiregularSequence.ModPrefix.solution`: the statement of
  `RingTheory.Sequence.IsQuasiRegular.quasiRegular_drop_mod_prev`, Lemma 061R.

## Implementation notes

The source's proof reduces to `i = 1` and then computes `J̄^nM̄/J̄^{n+1}M̄` as a quotient of the
polynomial module `(M/JM)[X_0, …, X_{c-1}]` by `X_0`. The route taken here proves the general `i`
directly, because the reduction to `i = 1` is not free in this formalization: iterating it would
require transporting quasi-regularity along the ring isomorphism `(R/(f_0))/(f̄_1, …, f̄_{i-1}) ≅
R/(f_0, …, f_{i-1})` and the matching module isomorphism at every step, which is more work than
the induction on the degree `n` in `inf_le_monSub_markedIdx`, whose statement is uniform in `i`.
The identity `J^nM ∩ f_0M = f_0J^{n-1}M` the source isolates for `i = 1` is exactly that
lemma's conclusion for `i = 1`, so no step of the source's argument is skipped, only its induction
on `i` is replaced by an induction on `n`.

The graded objects are never formed as such: the source's computation with
`⨁_n J^nM/J^{n+1}M` is replaced throughout by membership statements in the submodules `JpowM M f n`
of `M`, with `degLift` naming the map `J^nM → ⨁_k J^kM/J^{k+1}M` that reads a single degree into
the target. `monSub f D` is the auxiliary submodule of `M` spanned by the monomial multiples
`f^e m` with `e ∈ D`; `JpowM M f n` is `monSub f {e | |e| = n}` (`JpowM_eq_monSub`), and the marked
multi-indices of total degree `n` are `markedIdx c i n`.

The index data of the tail is passed to `injective_quotient` as an embedding
`emb : Fin c' ↪ Fin c` whose range is `{j | i ≤ j}`, rather than as `Fin (c - i) ≃ {j // i ≤ j}`:
the embedding is what `Finsupp.embDomain` consumes, and `Finsupp.embDomain` is what turns a
multi-index of the tail into one of the full sequence with the first `i` entries zero. For the list
form of the statement the embedding is `j ↦ i + j`.

## References

* [StacksProject 061R](https://stacks.math.columbia.edu/tag/061R), Lemma 10.69.5.
-/

@[expose] public section

namespace Stacks.QuasiregularSequence.ModPrefix

open RingTheory.Sequence

section Bridge

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {c : ℕ}

end Bridge

section MonSub

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {c : ℕ}

/-- `f^e` is multiplicative in the multi-index. -/
private theorem fpow_add (f : Fin c → R) (e e' : Fin c →₀ ℕ) :
    fpow f (e + e') = fpow f e * fpow f e' := by simp [fpow, pow_add, Finset.prod_mul_distrib]

/-- Total degree is additive in the multi-index. -/
private theorem qrMdeg_add (e e' : Fin c →₀ ℕ) : qrMdeg (e + e') = qrMdeg e + qrMdeg e' := by
  simp [qrMdeg, Finset.sum_add_distrib]

/-- `f^{X_j} = f_j`. -/
private theorem fpow_single (f : Fin c → R) (j : Fin c) : fpow f (Finsupp.single j 1) = f j := by
  simp [fpow, Finsupp.single_apply]

/-- The monomial `X_j` has total degree one. -/
private theorem qrMdeg_single (j : Fin c) : qrMdeg (Finsupp.single j (1 : ℕ)) = 1 := by
  simp [qrMdeg]

/-- The `R`-submodule of `M` spanned by the monomial multiples `f^e · m` with `e ∈ D`. -/
private noncomputable def monSub (f : Fin c → R) (D : Set (Fin c →₀ ℕ)) : Submodule R M :=
  Submodule.span R {x : M | ∃ e ∈ D, ∃ m : M, x = fpow f e • m}

/-- The monomial multiple `f^e · m` lies in `monSub f D` as soon as `e ∈ D`. -/
private theorem fpow_smul_mem_monSub (f : Fin c → R) {D : Set (Fin c →₀ ℕ)} {e : Fin c →₀ ℕ}
    (he : e ∈ D) (m : M) : fpow f e • m ∈ monSub f D :=
  Submodule.mem_span_of_mem ⟨e, he, m, rfl⟩

/-- **Grouped finite representation.** An element of `monSub f D` is a finite sum
`∑_{e ∈ S} f^e · m_e` with `S ⊆ D`, carrying one coefficient per multi-index. -/
private theorem mem_monSub_iff (f : Fin c → R) (D : Set (Fin c →₀ ℕ)) (x : M) :
    x ∈ monSub f D ↔
      ∃ (S : Finset (Fin c →₀ ℕ)) (s : (Fin c →₀ ℕ) → M),
        (↑S ⊆ D) ∧ x = ∑ e ∈ S, fpow f e • s e := by
  classical
  have hres :
    ∀ (S T : Finset (Fin c →₀ ℕ)) (u : (Fin c →₀ ℕ) → M),
      S ⊆ T → ∑ e ∈ T, fpow f e • (if e ∈ S then u e else 0) = ∑ e ∈ S, fpow f e • u e := by
    intro S T u hST
    rw [← Finset.sum_subset hST (fun e _ he => by simp [he])]
    exact Finset.sum_congr rfl (fun e he => by simp [he])
  refine ⟨fun hx => ?_, ?_⟩
  · refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro y ⟨e, he, m, rfl⟩
      exact ⟨{e}, fun _ => m, by simpa using he, by simp⟩
    · exact ⟨∅, fun _ => 0, by simp, by simp⟩
    · rintro y z - - ⟨S₁, s₁, h₁, rfl⟩ ⟨S₂, s₂, h₂, rfl⟩
      refine
        ⟨S₁ ∪ S₂, fun e => (if e ∈ S₁ then s₁ e else 0) + (if e ∈ S₂ then s₂ e else 0), by
          simpa using Set.union_subset h₁ h₂, ?_⟩
      simp only [smul_add, Finset.sum_add_distrib]
      rw [hres S₁ (S₁ ∪ S₂) s₁ Finset.subset_union_left,
        hres S₂ (S₁ ∪ S₂) s₂ Finset.subset_union_right]
    · rintro r y - ⟨S, s, hS, rfl⟩
      refine ⟨S, fun e => r • s e, hS, ?_⟩
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun e _ => smul_comm r (fpow f e) (s e)
  · rintro ⟨S, s, hS, rfl⟩
    exact Submodule.sum_mem _ fun e he => fpow_smul_mem_monSub f (hS (by simpa using he)) (s e)

/-- `J^n M` is spanned by the monomial multiples of total degree `n`. -/
private theorem JpowM_eq_monSub (f : Fin c → R) (n : ℕ) :
    JpowM M f n = monSub f {e | qrMdeg e = n} := by
  rw [JpowM_eq_span, monSub]
  congr 1
  ext x
  exact ⟨fun ⟨e, m, he, hx⟩ => ⟨e, he, m, hx⟩, fun ⟨e, he, m, hx⟩ => ⟨e, m, he, hx⟩⟩

/-- Multiplying by `f^e` shifts a monomial span by `e`. -/
private theorem fpow_smul_monSub_le (f : Fin c → R) (e : Fin c →₀ ℕ) (D D' : Set (Fin c →₀ ℕ))
    (h : ∀ e' ∈ D, e + e' ∈ D') {x : M} (hx : x ∈ monSub f D) : fpow f e • x ∈ monSub f D' := by
  classical
  obtain ⟨S, s, hS, rfl⟩ := (mem_monSub_iff f D x).mp hx
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun e' he' => ?_
  rw [smul_smul, ← fpow_add]
  exact fpow_smul_mem_monSub f (h e' (hS (by simpa using he'))) (s e')

end MonSub

section Descent

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {c c' : ℕ}

/-- The **marked** multi-indices: those of total degree `n` involving at least one of the first `i`
variables. -/
private def markedIdx (c i n : ℕ) : Set (Fin c →₀ ℕ) :=
  {e | qrMdeg e = n ∧ ∃ j : Fin c, (j : ℕ) < i ∧ e j ≠ 0}

/-- **The key step of Lemma 061R.** Let `f` be `M`-quasi-regular and let `N ⊆ M` be a submodule
contained in the span of the degree-one marked monomials — for `N = (f_0, …, f_{i-1})M` this is an
equality. Then `J^{n+1}M ∩ N = (f_0, …, f_{i-1}) · J^n M`: an element of `J^{n+1}M` lying in `N` is
a combination of marked monomials of degree `n + 1`. -/
private theorem inf_le_monSub_markedIdx (f : Fin c → R) (i : ℕ)
    (hinj : Function.Injective (quasiRegularCanonicalMap (M := M) f)) (N : Submodule R M)
    (hN : N ≤ monSub f (markedIdx c i 1)) (n : ℕ) :
    JpowM M f (n + 1) ⊓ N ≤ monSub f (markedIdx c i (n + 1)) := by
  classical
    induction n with
  | zero => exact inf_le_of_right_le hN
  | succ n ih =>
    intro v hv
    obtain ⟨S, s, hS, hvs⟩ := (mem_monSub_iff f _ v).mp (ih ⟨JpowM_succ_le f (n + 1) hv.1, hv.2⟩)
    have hdeg : ∀ e ∈ S, qrMdeg e = n + 1 := fun e he => (hS (by simpa using he)).1
    have hcoef : ∀ e ∈ S, s e ∈ Jid f • (⊤ : Submodule R M) :=
      mem_of_sum_fpow_smul_mem hinj (n + 1) S s hdeg
        (by
          rw [← hvs]; exact hv.1)
    rw [hvs]
    refine Submodule.sum_mem _ fun e he => ?_
    obtain ⟨hde, j, hji, hej⟩ := hS (by simpa using he)
    refine
      fpow_smul_monSub_le f e {e' | qrMdeg e' = 1} (markedIdx c i (n + 1 + 1)) ?_
        (by
          rw [← JpowM_eq_monSub, JpowM_one]; exact hcoef e he)
    intro e' he'
    refine ⟨by rw [qrMdeg_add, hde, (he' : qrMdeg e' = 1)], j, hji, ?_⟩
    simp only [Finsupp.add_apply]
    omega

/-- `mk (f^e) ∈ J̄^{|e|}`, where `J̄` is generated by the images of the `f_j`. -/
private theorem mk_fpow_mem (K : Ideal R) (f : Fin c → R) (g : Fin c' → R ⧸ K)
    (hmkJ : ∀ j : Fin c, Ideal.Quotient.mk K (f j) ∈ Jid g) (e : Fin c →₀ ℕ) :
    Ideal.Quotient.mk K (fpow f e) ∈ Jid g ^ qrMdeg e := by
  simp only [fpow, map_prod, map_pow, qrMdeg]
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod (fun j _ => Ideal.pow_mem_pow (hmkJ j) (e j))

/-- Total degree is unchanged by pushing a multi-index forward along `emb`. -/
private theorem qrMdeg_embDomain (emb : Fin c' ↪ Fin c) (d : Fin c' →₀ ℕ) :
    qrMdeg (Finsupp.embDomain emb d) = qrMdeg d := by
  classical
  rw [qrMdeg, qrMdeg, ←
    Finset.sum_subset (Finset.subset_univ (Finset.univ.image (emb : Fin c' → Fin c)))
      (fun j _ hj =>
        Finsupp.embDomain_of_notMem_range emb d j (by simpa [Finset.mem_image] using hj)),
    Finset.sum_image (fun a _ b _ h => emb.injective h)]
  exact Finset.sum_congr rfl fun j _ => Finsupp.embDomain_apply_self emb d j

/-- The monomial `f^{emb_* d}` reduces to the monomial `ḡ^d` in `R/K`. -/
private theorem mk_fpow_embDomain (K : Ideal R) (f : Fin c → R) (g : Fin c' → R ⧸ K)
    (emb : Fin c' ↪ Fin c) (hg : ∀ j, g j = Ideal.Quotient.mk K (f (emb j))) (d : Fin c' →₀ ℕ) :
    Ideal.Quotient.mk K (fpow f (Finsupp.embDomain emb d)) = fpow g d := by
  classical
  simp only [fpow, map_prod, map_pow]
  rw [←
    Finset.prod_subset (Finset.subset_univ (Finset.univ.image (emb : Fin c' → Fin c)))
      (fun j _ hj => by
        rw [Finsupp.embDomain_of_notMem_range emb d j (by simpa [Finset.mem_image] using hj),
          pow_zero]),
    Finset.prod_image (fun a _ b _ h => emb.injective h)]
  exact Finset.prod_congr rfl fun j _ => by rw [Finsupp.embDomain_apply_self, hg j]

/-- The class in `M/KM` of a combination `∑ a_k • m_k` is the combination of the classes. -/
private theorem mk_sum_smul (K : Ideal R) {κ : Type*} (S : Finset κ) (a : κ → R) (m : κ → M) :
    (Submodule.Quotient.mk (∑ k ∈ S, a k • m k) : M ⧸ (K • (⊤ : Submodule R M))) =
      ∑ k ∈ S, Ideal.Quotient.mk K (a k) •
        (Submodule.Quotient.mk (m k) : M ⧸ (K • (⊤ : Submodule R M))) := by
  rw [← Submodule.mkQ_apply, map_sum]
  exact Finset.sum_congr rfl fun k _ => rfl

/-- `J^n M` maps into `J̄^n M̄` under `M → M/KM`. -/
private theorem mk_mem_JpowM (K : Ideal R) (f : Fin c → R) (g : Fin c' → R ⧸ K)
    (hmkJ : ∀ j : Fin c, Ideal.Quotient.mk K (f j) ∈ Jid g) (n : ℕ) {x : M}
    (hx : x ∈ JpowM M f n) :
    (Submodule.Quotient.mk x : M ⧸ (K • (⊤ : Submodule R M))) ∈
      JpowM (M ⧸ (K • (⊤ : Submodule R M))) g n := by
  classical
  rw [JpowM_eq_monSub] at hx
  obtain ⟨S, s, hS, rfl⟩ := (mem_monSub_iff f _ x).mp hx
  rw [mk_sum_smul, JpowM]
  refine Submodule.sum_mem _ fun e he => Submodule.smul_mem_smul ?_ Submodule.mem_top
  have hm := mk_fpow_mem K f g hmkJ e
  rwa [(hS (by simpa using he) : qrMdeg e = n)] at hm

/-- Conversely, an element of `M` whose class lies in `J̄^n M̄` agrees modulo `KM` with an element
of `J^n M`. -/
private theorem exists_of_mk_mem_JpowM (K : Ideal R) (f : Fin c → R) (g : Fin c' → R ⧸ K)
    (emb : Fin c' ↪ Fin c) (hg : ∀ j, g j = Ideal.Quotient.mk K (f (emb j))) (n : ℕ) {x : M}
    (hx :
      (Submodule.Quotient.mk x : M ⧸ (K • (⊤ : Submodule R M))) ∈
        JpowM (M ⧸ (K • (⊤ : Submodule R M))) g n) :
    ∃ y ∈ JpowM M f n, x - y ∈ K • (⊤ : Submodule R M) := by
  classical
  have key :
    ∀ z : M ⧸ (K • (⊤ : Submodule R M)),
      z ∈ JpowM (M ⧸ (K • (⊤ : Submodule R M))) g n →
        ∃ y ∈ JpowM M f n, z = Submodule.Quotient.mk y := by
    intro z hz
    rw [JpowM_eq_span] at hz
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
    · rintro w ⟨dd, mm, hdd, rfl⟩
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ mm
      refine ⟨fpow f (Finsupp.embDomain emb dd) • m, ?_, ?_⟩
      · have hme := fpow_smul_mem f (Finsupp.embDomain emb dd) m
        rwa [qrMdeg_embDomain, hdd] at hme
      · rw [← mk_fpow_embDomain K f g emb hg dd]; rfl
    · exact ⟨0, Submodule.zero_mem _, rfl⟩
    · rintro a b - - ⟨y₁, h₁, rfl⟩ ⟨y₂, h₂, rfl⟩
      exact ⟨y₁ + y₂, Submodule.add_mem _ h₁ h₂, rfl⟩
    · rintro r a - ⟨y, h, rfl⟩
      obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective r
      exact ⟨r' • y, Submodule.smul_mem _ _ h, rfl⟩
  obtain ⟨y, hy, hxy⟩ := key _ hx
  exact ⟨y, hy, (Submodule.Quotient.eq _).mp hxy⟩

/-- `KM` is spanned by the degree-one marked monomials, `K` being generated by the first `i`
elements of the sequence. -/
private theorem smul_top_le_monSub_markedIdx (f : Fin c → R) (i : ℕ) (K : Ideal R)
    (hK : K = Ideal.span (f '' {j : Fin c | (j : ℕ) < i})) :
    K • (⊤ : Submodule R M) ≤ monSub f (markedIdx c i 1) := by
  rw [Submodule.smul_le]
  intro r hr m _
  refine
    Submodule.span_induction (p := fun a _ => a • m ∈ monSub f (markedIdx c i 1)) ?_ ?_ ?_ ?_
      (hK ▸ hr)
  · rintro a ⟨j, hj, rfl⟩
    rw [← fpow_single f j]
    exact fpow_smul_mem_monSub f (D := markedIdx c i 1) ⟨qrMdeg_single j, j, hj, by simp⟩ m
  · simp
  · intro a b _ _ ha hb; rw [add_smul]; exact Submodule.add_mem _ ha hb
  · intro a b _ hb; rw [smul_eq_mul, mul_smul]; exact Submodule.smul_mem _ a hb

/-- **Descent of a relation to `M`.** An `x ∈ J^n M` whose class in `M̄ = M/KM` is a relation of
degree `n`, i.e. lies in `J̄^{n+1}M̄`, is one modulo the marked monomials: `x = v + w` with `v` a
combination of marked monomials of degree `n` and `w ∈ J^{n+1}M`. -/
private theorem exists_mem_monSub_markedIdx_of_mk_mem (f : Fin c → R) (i : ℕ) (K : Ideal R)
    (g : Fin c' → R ⧸ K) (emb : Fin c' ↪ Fin c)
    (hinj : Function.Injective (quasiRegularCanonicalMap (M := M) f))
    (hgemb : ∀ j, g j = Ideal.Quotient.mk K (f (emb j)))
    (hK : K = Ideal.span (f '' {j : Fin c | (j : ℕ) < i})) (n : ℕ) {x : M} (hx : x ∈ JpowM M f n)
    (hmk :
      (Submodule.Quotient.mk x : M ⧸ (K • (⊤ : Submodule R M))) ∈
        JpowM (M ⧸ (K • (⊤ : Submodule R M))) g (n + 1)) :
    ∃ v ∈ monSub f (markedIdx c i n), x - v ∈ JpowM M f (n + 1) := by
  obtain ⟨y, hy, hxy⟩ := exists_of_mk_mem_JpowM K f g emb hgemb (n + 1) hmk
  cases n with
  | zero =>
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    have h1 : x - y ∈ JpowM M f (0 + 1) := by
      rw [zero_add, JpowM_one]
      refine Submodule.smul_mono ?_ le_rfl hxy
      exact
        hK.trans_le
          (Ideal.span_mono
            (by
              rintro z ⟨j, -, rfl⟩; exact Set.mem_range_self j))
    simpa using Submodule.add_mem _ hy h1
  | succ m =>
    refine ⟨x - y, ?_, by simpa using hy⟩
    exact
      inf_le_monSub_markedIdx f i hinj (K • (⊤ : Submodule R M))
        (smul_top_le_monSub_markedIdx f i K hK) m
        ⟨Submodule.sub_mem _ hx (JpowM_succ_le f (m + 1) hy), hxy⟩

/-- **A coefficient at an unmarked multi-index.** Marked monomials cannot interfere with a
multi-index avoiding the first `i` variables: if `∑_{k ∈ S} f^{d k} · m_k` differs from an element
of `J^{n+1}M` by a combination `v` of marked monomials of degree `n`, and the unmarked tag `d k₀`
occurs only at `k₀`, then `m_{k₀} ∈ JM`. -/
private theorem mem_smul_top_of_sum_sub_monSub_mem {f : Fin c → R}
    (hinj : Function.Injective (quasiRegularCanonicalMap (M := M) f)) (i n : ℕ) {κ : Type*}
    (S : Finset κ) (d : κ → (Fin c →₀ ℕ)) (m : κ → M) (hdeg : ∀ k ∈ S, qrMdeg (d k) = n) {v : M}
    (hv : v ∈ monSub f (markedIdx c i n))
    (hrel : (∑ k ∈ S, fpow f (d k) • m k) - v ∈ JpowM M f (n + 1)) (k₀ : κ) (hk₀ : k₀ ∈ S)
    (huniq : ∀ k ∈ S, d k = d k₀ → k = k₀) (hunmarked : ∀ j : Fin c, (j : ℕ) < i → d k₀ j = 0) :
    m k₀ ∈ Jid f • (⊤ : Submodule R M) := by
  classical
  obtain ⟨Sv, sv, hSv, rfl⟩ := (mem_monSub_iff f _ v).mp hv
  refine
    mem_of_sum_fpow_smul_mem_of_unique hinj n (S.disjSum Sv) (Sum.elim d id)
      (Sum.elim m (fun e => -(sv e))) ?_ ?_ (Sum.inl k₀) (by simpa using hk₀) ?_
  · intro k hk
    rcases k with k | e
    · exact hdeg k (by simpa using hk)
    · exact (hSv (by simpa using hk)).1
  · rw [Finset.sum_disjSum]
    simpa only [Sum.elim_inl, Sum.elim_inr, id_eq, smul_neg, Finset.sum_neg_distrib,
      ← sub_eq_add_neg] using hrel
  · intro k hk hkeq
    rcases k with k | e
    · exact congrArg Sum.inl (huniq k (by simpa using hk) (by simpa using hkeq))
    · obtain ⟨-, j, hj, hej⟩ := hSv (by simpa using hk)
      rw [show e = d k₀ from by simpa using hkeq] at hej
      exact absurd (hunmarked j hj) hej

/-- **Lemma 061R, in terms of the index data.** If `f_0, …, f_{c-1}` is `M`-quasi-regular,
`K` is generated by `f_0, …, f_{i-1}`, and `g` is the tail `f_i, …, f_{c-1}` read in `R/K` through
an indexing `emb` of `{j | i ≤ j}`, then the canonical map of tag 061N for `g` acting on `M/KM` is
injective. -/
private theorem injective_quotient (f : Fin c → R) (i : ℕ) (K : Ideal R) (g : Fin c' → R ⧸ K)
    (emb : Fin c' ↪ Fin c) (hinj : Function.Injective (quasiRegularCanonicalMap (M := M) f))
    (hgemb : ∀ j, g j = Ideal.Quotient.mk K (f (emb j)))
    (hembrange : ∀ j : Fin c, j ∈ Set.range emb ↔ i ≤ (j : ℕ))
    (hK : K = Ideal.span (f '' {j : Fin c | (j : ℕ) < i})) :
    Function.Injective (quasiRegularCanonicalMap (M := M ⧸ (K • (⊤ : Submodule R M))) g) := by
  classical
  have hmkJ : ∀ j : Fin c, Ideal.Quotient.mk K (f j) ∈ Jid g := by
    intro j
    by_cases hj : (j : ℕ) < i
    · rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hK ▸ Ideal.subset_span ⟨j, hj, rfl⟩)]
      exact Submodule.zero_mem _
    · obtain ⟨j', rfl⟩ := (hembrange j).mpr (by omega)
      rw [← hgemb j']
      exact Ideal.subset_span (Set.mem_range_self j')
  have hunmarked :
    ∀ (dd : Fin c' →₀ ℕ) (j : Fin c), (j : ℕ) < i → (Finsupp.embDomain emb dd) j = 0 :=
    fun dd j hj =>
    Finsupp.embDomain_of_notMem_range emb dd j fun hj' => absurd ((hembrange j).mp hj') (by omega)
  refine injective_of_mem_of_sum_fpow_smul_mem ?_
  intro n S' s' hdeg' hrel' d hd
  choose s hs using fun dd : Fin c' →₀ ℕ =>
    Submodule.Quotient.mk_surjective (K • (⊤ : Submodule R M)) (s' dd)
  have hdeg : ∀ dd ∈ S', qrMdeg (Finsupp.embDomain emb dd) = n := fun dd hdd =>
    (qrMdeg_embDomain emb dd).trans (hdeg' dd hdd)
  have hzmk :
    (Submodule.Quotient.mk (∑ dd ∈ S', fpow f (Finsupp.embDomain emb dd) • s dd) :
        M ⧸ (K • (⊤ : Submodule R M))) =
      ∑ dd ∈ S', fpow g dd • s' dd := by
    rw [mk_sum_smul]
    refine Finset.sum_congr rfl fun dd _ => ?_
    rw [← mk_fpow_embDomain K f g emb hgemb dd, ← hs dd]
  have hzmem : (∑ dd ∈ S', fpow f (Finsupp.embDomain emb dd) • s dd) ∈ JpowM M f n :=
    Submodule.sum_mem _ fun dd hdd => (hdeg dd hdd) ▸ fpow_smul_mem f _ (s dd)
  obtain ⟨v, hv, hrel⟩ :=
    exists_mem_monSub_markedIdx_of_mk_mem f i K g emb hinj hgemb hK n hzmem
      (by
        rw [hzmk]; exact hrel')
  rw [← hs d, ← JpowM_one]
  refine mk_mem_JpowM K f g hmkJ 1 ?_
  rw [JpowM_one]
  refine
    mem_smul_top_of_sum_sub_monSub_mem hinj i n S' (Finsupp.embDomain emb) s hdeg hv hrel d hd
      (fun dd _ hdd => Finsupp.embDomain_injective emb hdd) (hunmarked d)

end Descent

/-- The ideal generated by an initial segment of a list, read through the indexing of the whole
list by `Fin rs.length`. -/
private theorem ofList_take_eq_span {R : Type*} [CommRing R] (rs : List R) (i : ℕ) :
    Ideal.ofList (rs.take i) =
      Ideal.span ((fun j : Fin rs.length => rs[(j : ℕ)]) '' {j : Fin rs.length | (j : ℕ) < i}) :=
  le_antisymm
    (Ideal.span_le.mpr fun x hx => by
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
      rw [List.length_take] at hk
      exact Ideal.subset_span ⟨⟨k, by omega⟩, show k < i by omega, by simp [List.getElem_take]⟩)
    (Ideal.span_le.mpr fun x hx => by
      obtain ⟨j, hj, rfl⟩ := hx
      have hjt : (j : ℕ) < (rs.take i).length := by
        rw [List.length_take]; exact lt_min hj j.isLt
      exact Ideal.subset_span (by simpa [List.getElem_take] using List.getElem_mem hjt))

/-- **Stacks 061R.** Let `M` be a module over a commutative ring `R` and let `rs = f_1, …, f_c` be
an `M`-quasi-regular sequence in `R`. For any `i`, the images `f̄_{i+1}, …, f̄_c` of the remaining
elements in `R̄ = R/(f_1, …, f_i)` form an `M̄`-quasi-regular sequence, where
`M̄ = M/(f_1, …, f_i)M`. -/
public theorem solution {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {rs : List R}
    (reg : IsQuasiRegular M rs) (i : ℕ) :
    IsQuasiRegular (M ⧸ (Ideal.ofList (rs.take i) • ⊤ : Submodule R M))
      ((rs.drop i).map (Ideal.Quotient.mk (Ideal.ofList (rs.take i)))) := by
  classical
  have hlen :
    ((rs.drop i).map (Ideal.Quotient.mk (Ideal.ofList (rs.take i)))).length = rs.length - i := by
    simp
  refine
    ⟨injective_quotient (fun j : Fin rs.length => rs[(j : ℕ)]) i (Ideal.ofList (rs.take i)) _
        ⟨fun j =>
          ⟨i + (j : ℕ), by
            have := j.isLt; omega⟩,
          fun a b hab => ?_⟩
        reg.injective ?_ ?_ (ofList_take_eq_span rs i),
      quasiRegularCanonicalMap_surjective _⟩
  · have h' : i + (a : ℕ) = i + (b : ℕ) := congrArg Fin.val hab
    exact Fin.ext (by omega)
  · intro j
    change ((rs.drop i).map (Ideal.Quotient.mk (Ideal.ofList (rs.take i))))[(j : ℕ)] = _
    rw [List.getElem_map, List.getElem_drop]
    rfl
  · refine fun j =>
      ⟨?_, fun hj =>
        ⟨⟨(j : ℕ) - i, by
            rw [hlen]; have := j.isLt; omega⟩,
          ?_⟩⟩
    · rintro ⟨j', rfl⟩
      exact Nat.le_add_right i (j' : ℕ)
    · exact
        Fin.ext
          (by
            change i + ((j : ℕ) - i) = (j : ℕ); omega)

end Stacks.QuasiregularSequence.ModPrefix

end

/-!
# Quasi-regularity passes to the quotient by an initial segment of the sequence

Let `R` be a commutative ring, `M` an `R`-module and `f_1, …, f_c ∈ R` an `M`-quasi-regular
sequence, i.e. one for which the canonical map of graded `(R/J)[X_1, …, X_c]`-modules
`Φ_M : (R/J)[X_1, …, X_c] ⊗_{R/J} (M/JM) → ⨁_{n ≥ 0} JⁿM/J^{n+1}M`, `J = (f_1, …, f_c)`, is an
isomorphism. Fix an index `i` and pass to `R̄ = R/(f_1, …, f_i)` and `M̄ = M/(f_1, …, f_i)M`. Then
the images `f̄_{i+1}, …, f̄_c ∈ R̄` form an `M̄`-quasi-regular sequence.

For `i = 1` (the case the general one reduces to) the reason is that, with
`J̄ = (f̄_2, …, f̄_c) ⊆ R̄`,
`J̄ⁿM̄/J̄^{n+1}M̄ = (JⁿM + f_1M)/(J^{n+1}M + f_1M) = JⁿM/(J^{n+1}M + JⁿM ∩ f_1M)`,
and quasi-regularity of `f_1, …, f_c` gives `JⁿM ∩ f_1M = f_1J^{n-1}M`: an `m ∉ J^{n-1}M` has
`f_1m ∉ JⁿM`, since `⨁ JⁿM/J^{n+1}M` is the polynomial module `(M/JM)[X_1, …, X_c]`. Hence
`⨁_{n ≥ 0} J̄ⁿM̄/J̄^{n+1}M̄` is the quotient of `(M/JM)[X_1, …, X_c]` by `X_1`, which is the
associated graded module of `M̄` presented by the variables `X_2, …, X_c`.

## Main results

* `RingTheory.Sequence.IsQuasiRegular.quasiRegular_drop_mod_prev`: for an `M`-quasi-regular
  sequence `rs` and any `i`, the image of `rs.drop i` in `R ⧸ (rs.take i)` is a
  `M ⧸ (rs.take i) • ⊤`-quasi-regular sequence.

## Implementation notes

Faithfulness. (1) No dead hypothesis: the statement has exactly the source's data — the
quasi-regularity `reg` of `rs` and the index `i` — and both occur in the conclusion, `i` through
the split of `rs` into `rs.take i` and `rs.drop i`. (2) The scalars and base are the source's on
both sides: the hypothesis is quasi-regularity of `rs : List R` for the `R`-module `M`, while the
conclusion is a statement about the ring `R̄ = R ⧸ Ideal.ofList (rs.take i)` and the `R̄`-module
`M̄ = M ⧸ (Ideal.ofList (rs.take i) • ⊤)` — not about `R`-modules, the `R̄`-module structure on
`M̄` being the one that exists because `Ideal.ofList (rs.take i)` annihilates `M̄`. (3) The
canonical maps are pinned rather than asserted to exist: quasi-regularity is bijectivity of the
named map `quasiRegularCanonicalMap` of tag 061N, on both sides of the implication, and the
source's `f̄_{i+1}, …, f̄_c` is the reduction `Ideal.Quotient.mk` applied elementwise to
`rs.drop i`, in the same order. (4) The instantiation is not degenerate: for
`R = k[x_1, …, x_c]`, `M = R`, `rs = [x_1, …, x_c]` and `i = 1` the hypothesis holds and the
conclusion says that `x_2, …, x_c` is a quasi-regular sequence in `k[x_1, …, x_c]/(x_1)`.

The name mutates Mathlib's `RingTheory.Sequence.IsWeaklyRegular.regular_mod_prev`, which for a
weakly regular sequence gives `IsSMulRegular (M ⧸ Ideal.ofList (rs.take i) • ⊤) rs[i]`: the same
quotient by the preceding elements, with regularity of the single next element replaced by
quasi-regularity of the whole remaining sequence. Unlike there, the remaining elements have to be
transported along `R → R̄` explicitly, since a quasi-regular sequence for an `R̄`-module is a list
of elements of `R̄`; the spelling `(rs.drop i).map (Ideal.Quotient.mk (Ideal.ofList (rs.take i)))`
and the quotient `M ⧸ (Ideal.ofList (rs.take i) • ⊤)` are those of
`RingTheory.Sequence.isWeaklyRegular_append_iff'`, the append form of the same splitting.

The index `i : ℕ` is unrestricted, unlike in `regular_mod_prev`, where an element `rs[i]` is
named and `i < rs.length` is therefore needed: here, for `i ≥ rs.length`, the conclusion is
quasi-regularity of the empty sequence for `M/JM`, which holds. So the unbounded form is the
source's statement for `0 ≤ i ≤ c` together with a triviality.

## References

* [StacksProject 061R](https://stacks.math.columbia.edu/tag/061R), Lemma 10.69.5.
-/

@[expose] public section

namespace RingTheory.Sequence

/-- **Stacks 061R.** Let `M` be a module over a commutative ring `R` and let `rs = f_1, …, f_c` be
an `M`-quasi-regular sequence in `R`. For any `i`, the images `f̄_{i+1}, …, f̄_c` of the remaining
elements in `R̄ = R/(f_1, …, f_i)` form an `M̄`-quasi-regular sequence, where
`M̄ = M/(f_1, …, f_i)M`. -/
@[stacks 061R]
public theorem IsQuasiRegular.quasiRegular_drop_mod_prev {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {rs : List R} (reg : IsQuasiRegular M rs) (i : ℕ) :
    IsQuasiRegular (M ⧸ (Ideal.ofList (rs.take i) • ⊤ : Submodule R M))
      ((rs.drop i).map (Ideal.Quotient.mk (Ideal.ofList (rs.take i)))) :=
  Stacks.QuasiregularSequence.ModPrefix.solution reg i

end RingTheory.Sequence

end
