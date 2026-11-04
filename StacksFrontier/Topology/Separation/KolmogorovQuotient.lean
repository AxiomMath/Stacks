module

public import Mathlib.Topology.Separation.Basic

/-!
# Kolmogorov quotients by a relation with finite fibres (Stacks 06NA)

Stacks 06NA concerns continuous maps `s t : R → U` and `π : U → X` of topological spaces such
that (1) `π` is open, (2) `U` is sober, (3) both `s` and `t` have finite fibres,
(4) generalizations lift along `s` and `t`, and (5) the image of `(t, s) : R → U × U` is an
equivalence relation on `U` of which `X` is the quotient as a set; the conclusion is that `X` is
Kolmogorov, i.e. `T0Space X`.

`Topology.t0Space_of_isOpenMap_of_finite_fibres` below proves a statement strictly stronger than
06NA, and the deviation is deliberate. Of the five source hypotheses it retains only (1), the
finite-fibre condition on `t`, and (5) — the last recorded concretely as surjectivity of `π`
together with `π u = π u' ↔ Function.SourceTargetRel s t u u'`, which says exactly that `X` is
the quotient of `U` by the relation cut out by `(t, s)`. Three hypotheses are absent: soberness
of `U` (2) is weakened to `T0Space U`, finiteness of fibres (3) is demanded of `t` only and not
of `s`, and "generalizations lift along `s`, `t`" (4) is dropped outright. Continuity of `s` and
`t` is never used either, so `R` carries no topology at all here.

Nothing is lost by dropping them because the proof does not follow the source. Stacks uses
soberness and the lifting of generalizations to compare the closures of the finitely many lifts
of a point of `X`. Here openness of `π` alone lifts a specialization `π u ⤳ π v` to a
specialization `u₁ ⤳ v` with `u₁` in the `π`-fibre of `u`
(`Topology.exists_specializes_of_specializes_map`), and the `π`-fibres are finite because the
fibre over `π u` is contained in `s '' (t ⁻¹' {u})`
(`Topology.finite_preimage_singleton_of_sourceTargetRel`), so only the finite fibres of `t` are
needed. For two inseparable points of `X`, iterating the lifting produces two interleaved
specialization chains `u₀ ⟵ v₁ ⟵ u₁ ⟵ v₂ ⟵ ⋯` of lifts, staying inside the two finite fibres.
In a `T0Space` the specialization preorder is antisymmetric, so the chain of lifts of the first
point is eventually constant (`Topology.exists_eventually_const_of_specializes_seq`); at an index
`N` where it has stabilized, `u_N` and `v_{N+1}` specialize to one another, hence are equal, and
so the two points of `X` share a lift and coincide.
-/

@[expose] public section

open Set

namespace Function

/-- A map `f` *has finite fibres* if every fibre `f ⁻¹' {u}` is a finite set. -/
def HasFiniteFibres {R U : Type*} (f : R → U) : Prop :=
  ∀ u : U, (f ⁻¹' {u}).Finite

/-- The relation on `U` cut out by the image of `(t, s) : R → U × U`: two points are related
when some `r : R` has `t r` as its first and `s r` as its second coordinate. In Stacks 06NA this
is the relation whose quotient is the space `X`. -/
def SourceTargetRel {R U : Type*} (s t : R → U) (u u' : U) : Prop :=
  ∃ r : R, t r = u ∧ s r = u'

end Function

namespace Topology

/-- If `t` has finite fibres and `π` identifies exactly the pairs related by `(t, s)`, then every
fibre of `π` is finite: the fibre through `u` is contained in `s '' (t ⁻¹' {u})`. -/
lemma finite_preimage_singleton_of_sourceTargetRel {R U X : Type*} {s t : R → U} {π : U → X}
    (ht_fin : Function.HasFiniteFibres t)
    (hπ_rel : ∀ u u' : U, π u = π u' ↔ Function.SourceTargetRel s t u u') (u : U) :
    (π ⁻¹' {π u}).Finite := by
  apply Set.Finite.subset ((ht_fin u).image s)
  intro u' hu'
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hu'
  rw [Set.mem_image]
  obtain ⟨r, htr, hsr⟩ := (hπ_rel u u').mp hu'.symm
  exact ⟨r, by simp [Set.mem_preimage, htr], hsr⟩

/-- The lifting step: if `π` is open and its fibres are finite (guaranteed by the finite fibres
of `t`), then a specialization `π u ⤳ π v` downstairs is realized upstairs by a point `u₁` of the
`π`-fibre of `u` with `u₁ ⤳ v`.

Openness of `π` gives `v ∈ closure (π ⁻¹' {π u})`, and since that fibre is finite its closure is
the union of the closures of its points, one of which must therefore contain `v`. -/
lemma exists_specializes_of_specializes_map {R U X : Type*} [TopologicalSpace U]
    [TopologicalSpace X] {s t : R → U} {π : U → X} (hπ_open : IsOpenMap π)
    (ht_fin : Function.HasFiniteFibres t)
    (hπ_rel : ∀ u u' : U, π u = π u' ↔ Function.SourceTargetRel s t u u')
    (u v : U) (h : Specializes (π u) (π v)) :
    ∃ u₁ : U, π u₁ = π u ∧ Specializes u₁ v := by
  have hv_mem_closure : v ∈ closure (π ⁻¹' {π u}) := by
    rw [mem_closure_iff]
    intro O hO hv_in_O
    have hπu_in_πO : π u ∈ π '' O :=
      h.mem_open (hπ_open O hO) (Set.mem_image_of_mem π hv_in_O)
    obtain ⟨u', hu'_in_O, hπu'⟩ := hπu_in_πO
    exact ⟨u', hu'_in_O, show π u' ∈ {π u} from Set.mem_singleton_iff.mpr hπu'⟩
  have hfib : (π ⁻¹' {π u}).Finite := finite_preimage_singleton_of_sourceTargetRel ht_fin hπ_rel u
  have hset_eq : π ⁻¹' {π u} = ⋃ x ∈ (π ⁻¹' {π u}), {x} := by
    ext x; simp
  rw [hset_eq, hfib.closure_biUnion] at hv_mem_closure
  simp only [Set.mem_iUnion] at hv_mem_closure
  obtain ⟨u₁, hu₁_mem, hv_in_cl⟩ := hv_mem_closure
  exact ⟨u₁, Set.mem_preimage.mp hu₁_mem, specializes_iff_mem_closure.mpr hv_in_cl⟩

/-- Two points of `U` whose images in `X` specialize to one another generate two interleaved
specialization chains: sequences `u•` and `v•` staying inside the `π`-fibres of `u₀` and `v₀`
with `u_{n+1} ⤳ v_{n+1} ⤳ u_n` for every `n`.

Each step applies `Topology.exists_specializes_of_specializes_map` twice, once in each direction,
and the sequences are then built by recursion on the subtype of the `π`-fibre of `u₀`. -/
lemma exists_specializing_seqs_of_specializes {R U X : Type*} [TopologicalSpace U]
    [TopologicalSpace X] {s t : R → U} {π : U → X} (hπ_open : IsOpenMap π)
    (ht_fin : Function.HasFiniteFibres t)
    (hπ_rel : ∀ u u' : U, π u = π u' ↔ Function.SourceTargetRel s t u u')
    (u₀ v₀ : U) (hxy : Specializes (π u₀) (π v₀)) (hyx : Specializes (π v₀) (π u₀)) :
    ∃ u_seq v_seq : ℕ → U,
      u_seq 0 = u₀ ∧ v_seq 0 = v₀ ∧
      (∀ n, π (u_seq n) = π u₀) ∧ (∀ n, π (v_seq n) = π v₀) ∧
      (∀ n, Specializes (u_seq (n + 1)) (v_seq (n + 1))) ∧
      (∀ n, Specializes (v_seq (n + 1)) (u_seq n)) := by
  have step : ∀ u_n : U, π u_n = π u₀ →
      ∃ v_next u_next : U, π v_next = π v₀ ∧ π u_next = π u₀ ∧
        Specializes v_next u_n ∧ Specializes u_next v_next := by
    intro u_n hu_n
    obtain ⟨v_next, hv_π, hv_spec⟩ :=
      exists_specializes_of_specializes_map hπ_open ht_fin hπ_rel v₀ u_n (hu_n ▸ hyx)
    obtain ⟨u_next, hu_π, hu_spec⟩ :=
      exists_specializes_of_specializes_map hπ_open ht_fin hπ_rel u₀ v_next (hv_π ▸ hxy)
    exact ⟨v_next, u_next, hv_π, hu_π, hv_spec, hu_spec⟩
  let S := { u : U // π u = π u₀ }
  let s₀ : S := ⟨u₀, rfl⟩
  let next_v (a : S) : U := (step a.1 a.2).choose
  let next_s (a : S) : S := ⟨(step a.1 a.2).choose_spec.choose,
    (step a.1 a.2).choose_spec.choose_spec.2.1⟩
  have hnv_fib (a : S) : π (next_v a) = π v₀ :=
    (step a.1 a.2).choose_spec.choose_spec.1
  have hnv_spec (a : S) : Specializes (next_v a) a.1 :=
    (step a.1 a.2).choose_spec.choose_spec.2.2.1
  have hns_spec (a : S) : Specializes (next_s a).1 (next_v a) :=
    (step a.1 a.2).choose_spec.choose_spec.2.2.2
  let st : ℕ → S := fun n => Nat.rec s₀ (fun _ a => next_s a) n
  refine ⟨fun n => (st n).1, fun n => match n with | 0 => v₀ | n + 1 => next_v (st n),
    rfl, rfl, fun n => (st n).2, ?_, ?_, ?_⟩
  · intro n; match n with | 0 => rfl | n + 1 => exact hnv_fib (st n)
  · intro n; exact hns_spec (st n)
  · intro n; exact hnv_spec (st n)

/-- A sequence in a `T0Space` that descends for the specialization preorder and stays inside a
finite set is eventually constant.

In a `T0Space` specialization is antisymmetric, so a repeated value forces the sequence to be
constant in between; were the sequence never eventually constant one could extract a strictly
monotone reindexing along which the values are pairwise distinct, giving an infinite subset of a
finite set. -/
lemma exists_eventually_const_of_specializes_seq {U : Type*} [TopologicalSpace U] [T0Space U]
    {S : Set U} (hS : S.Finite) (f : ℕ → U) (hf_range : ∀ n, f n ∈ S)
    (hf_desc : ∀ n, Specializes (f (n + 1)) (f n)) :
    ∃ N, ∀ n, N ≤ n → f n = f N := by
  have hspec_trans : ∀ a b, a ≤ b → Specializes (f b) (f a) := by
    intro a b hab
    induction hab with
    | refl => exact specializes_refl _
    | step h ih => exact (hf_desc _).trans ih
  have key : ∀ i j, i ≤ j → f i = f j → (∀ k, i ≤ k → k ≤ j → f k = f i) := by
    intro i j hij hfij k hik hkj
    have h1 : Specializes (f j) (f k) := hspec_trans k j hkj
    have h2 : Specializes (f k) (f i) := hspec_trans i k hik
    have h3 : Specializes (f i) (f k) := hfij ▸ h1
    exact (h3.antisymm h2).eq.symm
  by_contra h_not_stab
  have h_not_stab' : ∀ N, ∃ n, N ≤ n ∧ f n ≠ f N := by
    intro N
    by_contra hc
    refine h_not_stab ⟨N, fun n hn => ?_⟩
    by_contra hne
    exact hc ⟨n, hn, hne⟩
  have step : ∀ n : ℕ, ∃ m, n < m ∧ f m ≠ f n := by
    intro n
    obtain ⟨m, hm1, hm2⟩ := h_not_stab' n
    exact ⟨m, hm1.lt_of_ne (by rintro rfl; exact hm2 rfl), hm2⟩
  let g : ℕ → ℕ := fun n => Nat.rec 0 (fun _ gk => (step gk).choose) n
  have hg_step : ∀ n, g n < g (n + 1) ∧ f (g (n + 1)) ≠ f (g n) := fun n => (step (g n)).choose_spec
  have hg_mono : StrictMono g := strictMono_nat_of_lt_succ (fun n => (hg_step n).1)
  have hne_of_lt : ∀ a b, a < b → f (g a) ≠ f (g b) := fun a b h hab =>
    (hg_step a).2 (key (g a) (g b) (hg_mono h).le hab (g (a + 1)) (hg_step a).1.le
      (hg_mono.monotone (Nat.succ_le_of_lt h)))
  have hfg_inj : Function.Injective (f ∘ g) := by
    intro a b (hab : f (g a) = f (g b))
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hne_of_lt a b h hab
    · exact hne_of_lt b a h hab.symm
  have hrange : Set.Finite (Set.range (f ∘ g)) :=
    Set.Finite.subset hS (fun x ⟨n, hn⟩ => hn ▸ hf_range (g n))
  exact (Set.infinite_range_of_injective hfg_inj).not_finite hrange

/-- If `π : U → X` is an open surjection from a `T0Space`, and `π` identifies exactly the pairs
related by the image of `(t, s) : R → U × U` for a map `t` with finite fibres, then `X` is
Kolmogorov.

This generalizes Stacks 06NA: soberness of `U` is weakened to `T0Space U`, only `t` is assumed to
have finite fibres, and the lifting of generalizations along `s` and `t` is not assumed. See the
module docstring. -/
@[stacks 06NA]
theorem t0Space_of_isOpenMap_of_finite_fibres {R U X : Type*} [TopologicalSpace U] [T0Space U]
    [TopologicalSpace X] (s t : R → U) (π : U → X) (hπ_open : IsOpenMap π)
    (ht_fin : Function.HasFiniteFibres t) (hπ_surj : Function.Surjective π)
    (hπ_rel : ∀ u u' : U, π u = π u' ↔ Function.SourceTargetRel s t u u') :
    T0Space X := by
  rw [t0Space_iff_inseparable]
  intro x y hxy
  have hxy_spec : Specializes x y := hxy.specializes
  have hyx_spec : Specializes y x := hxy.specializes'
  obtain ⟨u₀, hu₀⟩ := hπ_surj x
  obtain ⟨v₀, hv₀⟩ := hπ_surj y
  have hspec_uv : Specializes (π u₀) (π v₀) := hu₀ ▸ hv₀ ▸ hxy_spec
  have hspec_vu : Specializes (π v₀) (π u₀) := hv₀ ▸ hu₀ ▸ hyx_spec
  have hfib_u : (π ⁻¹' {π u₀}).Finite :=
    finite_preimage_singleton_of_sourceTargetRel ht_fin hπ_rel u₀
  obtain ⟨u_seq, v_seq, -, -, hu_fib, hv_fib, huv_spec, hvu_spec⟩ :=
    exists_specializing_seqs_of_specializes hπ_open ht_fin hπ_rel u₀ v₀ hspec_uv hspec_vu
  -- `u_seq` descends for the specialization order, through `u (n+1) ⤳ v (n+1) ⤳ u n`
  have hu_desc : ∀ n, Specializes (u_seq (n + 1)) (u_seq n) :=
    fun n => (huv_spec n).trans (hvu_spec n)
  have hu_in_fib : ∀ n, u_seq n ∈ π ⁻¹' {π u₀} :=
    fun n => Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr (hu_fib n))
  obtain ⟨N, hN⟩ := exists_eventually_const_of_specializes_seq hfib_u u_seq hu_in_fib hu_desc
  -- once `u_seq` is constant, `u_seq N` and `v_seq (N + 1)` specialize to one another
  have huN : u_seq (N + 1) = u_seq N := hN (N + 1) (Nat.le_succ N)
  have h_uv : Specializes (u_seq N) (v_seq (N + 1)) := huN ▸ huv_spec N
  have h_vu : Specializes (v_seq (N + 1)) (u_seq N) := hvu_spec N
  calc x = π u₀ := hu₀.symm
    _ = π (u_seq N) := (hu_fib N).symm
    _ = π (v_seq (N + 1)) := congrArg π (h_uv.antisymm h_vu).eq
    _ = π v₀ := hv_fib (N + 1)
    _ = y := hv₀

end Topology
