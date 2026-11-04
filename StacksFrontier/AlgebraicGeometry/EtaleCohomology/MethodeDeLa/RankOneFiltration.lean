module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Order.RelSeries
public import Mathlib.RepresentationTheory.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Rank one filtrations of representations over a prime field

Let `ℓ` be a prime and let `V` be a finite vector space over `F_ℓ = ZMod ℓ` carrying a linear
action of a finite group `G`. An `ℓ`-Sylow subgroup `H ⊆ G` has index prime to `ℓ`, and the
restriction of the representation to `H` has a finite filtration by `H`-stable subspaces whose
successive quotients are one dimensional with trivial `H`-action, that is, are copies of
`Z/ℓZ`.

## Main results

* `Representation.exists_relSeries_trivialRankOneStep`: a representation of a finite `ℓ`-group
  on a finite `F_ℓ`-vector space has a finite filtration running from `⊥` to `⊤` whose
  successive quotients are `Z/ℓZ` with trivial action.
* `Representation.exists_sylow_relSeries_trivialRankOneStep`: for a representation of an
  arbitrary finite group there is a subgroup whose index is prime to `ℓ` and whose restricted
  representation carries such a filtration.

## Implementation notes

A step of the filtration is recorded by `Representation.TrivialRankOneStep`: the pair
`(N₁, N₂)` satisfies `N₁ ≤ N₂`, every `g ∈ H` moves a vector of `N₂` by an element of `N₁`, and
`N₂` has exactly `ℓ` times as many elements as `N₁`. Over the field `F_ℓ` the last condition
says the quotient is one dimensional, so together the three say that the subquotient is `Z/ℓZ`
with trivial action. The filtration itself is a `RelSeries` for that relation running from `⊥`
to `⊤`, which packages the finiteness of the filtration together with the condition on every
successive quotient. Stability of the terms under `H` is not part of the relation because it
follows from it: the trivial-action clause gives `ρ g x = x + (ρ g x - x) ∈ N₂` for `x ∈ N₂`.
The cardinality clause is read under the standing hypothesis that `V` is finite, where every
subspace has positive cardinality and the equation therefore says that `N₁` has index exactly
`ℓ` in `N₂`.

The filtration is built from the bottom of the lattice upwards. Given an `H`-stable `W ≠ ⊤`,
the `ℓ`-group `H` acts on the finite quotient `V ⧸ W`, whose cardinality is divisible by `ℓ`
because it is a nonzero `F_ℓ`-vector space; the number of fixed points of a `p`-group action is
congruent to the cardinality of the whole set, so there is a fixed point other than the origin.
Lifting it to `x ∈ V` outside `W` makes `W ⊔ span {x}` an `H`-stable subspace one dimension
larger with trivial action on the quotient, and the construction continues from there. It
terminates because `Nat.card V - Nat.card W` drops at each step.

## References

* [Stacks Project, Tag 0A3R](https://stacks.math.columbia.edu/tag/0A3R)
-/

@[expose] public section

open scoped SetRel

namespace Representation

variable {ℓ : ℕ} {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod ℓ) V]

/-- One step of a filtration whose subquotient is a copy of `Z/ℓZ` with trivial action of the
subgroup `H`: the smaller subspace is contained in the larger, every `g ∈ H` moves a vector of
the larger subspace by an element of the smaller one, and the larger subspace has `ℓ` times as
many elements as the smaller. -/
def TrivialRankOneStep (H : Subgroup G) (ρ : Representation (ZMod ℓ) G V) :
    SetRel (Submodule (ZMod ℓ) V) (Submodule (ZMod ℓ) V) :=
  {p | p.1 ≤ p.2 ∧ (∀ g ∈ H, ∀ x ∈ p.2, ρ g x - x ∈ p.1) ∧ Nat.card p.2 = ℓ * Nat.card p.1}

/-- The larger subspace of a rank one step is stable under the group acting on it. -/
theorem TrivialRankOneStep.stable {H : Subgroup G} {ρ : Representation (ZMod ℓ) G V}
    {N₁ N₂ : Submodule (ZMod ℓ) V} (h : N₁ ~[TrivialRankOneStep H ρ] N₂)
    {g : G} (hg : g ∈ H) {x : V} (hx : x ∈ N₂) : ρ g x ∈ N₂ := by
  simpa using N₂.add_mem (h.1 (h.2.1 g hg x hx)) hx

/-- The action of a subgroup `H` on the quotient of `V` by an `H`-stable subspace. -/
@[instance_reducible]
private def quotMulAction {H : Subgroup G} (ρ : Representation (ZMod ℓ) G V)
    {W : Submodule (ZMod ℓ) V} (hW : ∀ g ∈ H, ∀ x ∈ W, ρ g x ∈ W) :
    MulAction H (V ⧸ W) where
  smul g q := W.mapQ W (ρ g) (fun x hx ↦ hW g g.2 x hx) q
  one_smul q := by
    induction q using Submodule.Quotient.induction_on with
    | H x =>
      change Submodule.Quotient.mk ((ρ ((1 : H) : G)) x) = Submodule.Quotient.mk x
      rw [Subgroup.coe_one, map_one]
      rfl
  mul_smul g h q := by
    induction q using Submodule.Quotient.induction_on with
    | H x =>
      change Submodule.Quotient.mk ((ρ ((g * h : H) : G)) x) =
        Submodule.Quotient.mk ((ρ (g : G)) ((ρ (h : G)) x))
      rw [Subgroup.coe_mul, map_mul]
      rfl

/-- A nonzero finite vector space over `F_ℓ` has cardinality divisible by `ℓ`: any nonzero
vector generates a subgroup of order `ℓ`. -/
private theorem prime_dvd_natCard [Fact ℓ.Prime] {M : Type*} [AddCommGroup M]
    [Module (ZMod ℓ) M] [Finite M] [Nontrivial M] : ℓ ∣ Nat.card M := by
  obtain ⟨q, hq⟩ := exists_ne (0 : M)
  have hz : ℓ • q = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod ℓ) ℓ q, ZMod.natCast_self, zero_smul]
  have h1 : addOrderOf q ≠ 1 := by simpa [AddMonoid.addOrderOf_eq_one_iff] using hq
  have he : addOrderOf q = ℓ :=
    (Nat.Prime.eq_one_or_self_of_dvd Fact.out _
      (addOrderOf_dvd_of_nsmul_eq_zero hz)).resolve_left h1
  exact he ▸ addOrderOf_dvd_natCard q

/-- Enlarging a subspace by a vector outside it multiplies the number of its elements by `ℓ`:
the sum is the image of `W × F_ℓ` under an injective linear map. -/
private theorem card_sup_span_singleton [Fact ℓ.Prime] [Finite V]
    (W : Submodule (ZMod ℓ) V) {x : V} (hx : x ∉ W) :
    Nat.card (W ⊔ Submodule.span (ZMod ℓ) {x} : Submodule (ZMod ℓ) V) = ℓ * Nat.card W := by
  classical
  set f : (W × ZMod ℓ) →ₗ[ZMod ℓ] V :=
    W.subtype ∘ₗ LinearMap.fst (ZMod ℓ) W (ZMod ℓ) +
      LinearMap.toSpanSingleton (ZMod ℓ) V x ∘ₗ LinearMap.snd (ZMod ℓ) W (ZMod ℓ) with hf
  have happ : ∀ p : W × ZMod ℓ, f p = (p.1 : V) + p.2 • x := by
    intro p
    simp [hf, LinearMap.toSpanSingleton_apply]
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨w, c⟩ hw
    have h0 : (w : V) + c • x = 0 := by simpa [happ] using hw
    have hc : c = 0 := by
      by_contra hc
      have hcx : c • x ∈ W := by
        rw [eq_neg_of_add_eq_zero_right h0]
        exact W.neg_mem w.2
      exact hx ((W.smul_mem_iff hc).1 hcx)
    subst hc
    simp only [zero_smul, add_zero] at h0
    have hw0 : w = 0 := by
      ext
      simpa using h0
    simp [hw0]
  have hrange : LinearMap.range f = W ⊔ Submodule.span (ZMod ℓ) {x} := by
    apply le_antisymm
    · rintro _ ⟨⟨w, c⟩, rfl⟩
      rw [happ]
      exact Submodule.add_mem _ (Submodule.mem_sup_left w.2)
        (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)))
    · refine sup_le (fun w hw ↦ ⟨(⟨w, hw⟩, 0), by simp [happ]⟩) ?_
      rw [Submodule.span_le, Set.singleton_subset_iff]
      exact ⟨(0, 1), by simp [happ]⟩
  have hcard := Nat.card_congr (LinearEquiv.ofInjective f hinj).toEquiv
  rw [hrange] at hcard
  rw [← hcard, Nat.card_prod, Nat.card_zmod, mul_comm]

/-- A finite `ℓ`-group acting on a finite `F_ℓ`-vector space fixes a vector outside any proper
stable subspace, modulo that subspace: the fixed points of its action on the quotient are more
numerous than the origin alone. -/
private theorem exists_notMem_sub_mem [Fact ℓ.Prime] [Finite V] {H : Subgroup G} [Finite H]
    (hH : IsPGroup ℓ H) (ρ : Representation (ZMod ℓ) G V) {W : Submodule (ZMod ℓ) V}
    (hW : ∀ g ∈ H, ∀ x ∈ W, ρ g x ∈ W) (htop : W ≠ ⊤) :
    ∃ x : V, x ∉ W ∧ ∀ g ∈ H, ρ g x - x ∈ W := by
  let _ := quotMulAction ρ hW
  have hsmul : ∀ (g : H) (y : V),
      (g • (Submodule.Quotient.mk y : V ⧸ W)) = Submodule.Quotient.mk ((ρ (g : G)) y) :=
    fun _ _ ↦ rfl
  have : Nontrivial (V ⧸ W) := Submodule.Quotient.nontrivial_iff.2 htop
  have : Finite (V ⧸ W) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective W)
  have hdvd : ℓ ∣ Nat.card (V ⧸ W) := prime_dvd_natCard
  have h0 : (0 : V ⧸ W) ∈ MulAction.fixedPoints H (V ⧸ W) := by
    intro g
    rw [← Submodule.Quotient.mk_zero W, hsmul]
    simp
  obtain ⟨b, hb, hb0⟩ := hH.exists_fixed_point_of_prime_dvd_card_of_fixed_point (V ⧸ W) hdvd h0
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective W b
  refine ⟨x, fun hxW ↦ hb0 ((Submodule.Quotient.mk_eq_zero W).2 hxW).symm, fun g hg ↦ ?_⟩
  have hfix : Submodule.Quotient.mk ((ρ g) x) = (Submodule.Quotient.mk x : V ⧸ W) := by
    rw [← hsmul ⟨g, hg⟩ x]
    exact hb ⟨g, hg⟩
  rw [← Submodule.Quotient.mk_eq_zero W, Submodule.Quotient.mk_sub, hfix, sub_self]

/-- The filtration of a representation of a finite `ℓ`-group, built upwards from an `H`-stable
subspace, with `Nat.card V - Nat.card W` as the termination measure. -/
@[sga "3 XVII 3.4" "special case"]
private theorem exists_relSeries_aux [Fact ℓ.Prime] [Finite V] {H : Subgroup G} [Finite H]
    (hH : IsPGroup ℓ H) (ρ : Representation (ZMod ℓ) G V) (n : ℕ) :
    ∀ W : Submodule (ZMod ℓ) V, Nat.card V - Nat.card W ≤ n →
      (∀ g ∈ H, ∀ x ∈ W, ρ g x ∈ W) →
        ∃ X : RelSeries (TrivialRankOneStep H ρ), X.head = W ∧ X.last = ⊤ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W hn hW
    by_cases htop : W = ⊤
    · exact ⟨RelSeries.singleton _ W, rfl, by simpa using htop⟩
    obtain ⟨x, hx, hfix⟩ := exists_notMem_sub_mem hH ρ hW htop
    set W' := W ⊔ Submodule.span (ZMod ℓ) {x} with hW'def
    have hcard : Nat.card W' = ℓ * Nat.card W := card_sup_span_singleton W hx
    have hstep : W ~[TrivialRankOneStep H ρ] W' := by
      refine ⟨le_sup_left, fun g hg y hy ↦ ?_, hcard⟩
      rw [hW'def, Submodule.mem_sup] at hy
      obtain ⟨w, hw, z, hz, rfl⟩ := hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
      have hexp : (ρ g) (w + c • x) - (w + c • x) =
          ((ρ g) w - w) + c • ((ρ g) x - x) := by
        rw [map_add, map_smul, smul_sub]
        abel
      rw [hexp]
      exact Submodule.add_mem _ (Submodule.sub_mem _ (hW g hg w hw) hw)
        (Submodule.smul_mem _ _ (hfix g hg))
    have hle : Nat.card W' ≤ Nat.card V := Nat.card_le_card_of_injective _ Subtype.val_injective
    have hgrow : Nat.card W < Nat.card W' := by
      rw [hcard]
      exact lt_mul_left Nat.card_pos (Fact.out : ℓ.Prime).one_lt
    obtain ⟨X, hhead, hlast⟩ :=
      ih (Nat.card V - Nat.card W') (by omega) W' le_rfl
        (fun g hg y hy ↦ TrivialRankOneStep.stable hstep hg hy)
    exact ⟨X.cons W (by rwa [hhead]), rfl, by simpa using hlast⟩

/-- **A representation of a finite `ℓ`-group on a finite `F_ℓ`-vector space is a successive
extension of trivial one dimensional representations.** The filtration runs from `⊥` to `⊤` and
each of its successive quotients is `Z/ℓZ` with trivial action. -/
theorem exists_relSeries_trivialRankOneStep (hℓ : ℓ.Prime) [Finite V] {H : Subgroup G}
    [Finite H] (hH : IsPGroup ℓ H) (ρ : Representation (ZMod ℓ) G V) :
    ∃ X : RelSeries (TrivialRankOneStep H ρ), X.head = ⊥ ∧ X.last = ⊤ := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  exact exists_relSeries_aux hH ρ (Nat.card V) ⊥ (by omega) (by simp)

/-- **The group-theoretic content of the method of the trace.** For a representation of a finite
group `G` on a finite `F_ℓ`-vector space there is a subgroup `H` whose index is prime to `ℓ` —
an `ℓ`-Sylow subgroup — such that the restriction of the representation to `H` has a finite
filtration running from `⊥` to `⊤` whose successive quotients are `Z/ℓZ` with trivial action. -/
theorem exists_sylow_relSeries_trivialRankOneStep (hℓ : ℓ.Prime) [Finite G] [Finite V]
    (ρ : Representation (ZMod ℓ) G V) :
    ∃ H : Subgroup G, ¬ ℓ ∣ H.index ∧
      ∃ X : RelSeries (TrivialRankOneStep H ρ), X.head = ⊥ ∧ X.last = ⊤ := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨P⟩ : Nonempty (Sylow ℓ G) := inferInstance
  exact ⟨(P : Subgroup G), P.not_dvd_index,
    exists_relSeries_trivialRankOneStep hℓ P.isPGroup' ρ⟩

end Representation

end
