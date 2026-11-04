module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.LinearAlgebra.DirectSum.CountablyGenerated

@[expose] public section

universe w

/-!
# Transfinite dévissage of modules

The notion of a *direct sum dévissage* of a module and the associated decomposition theorem,
from Section 10.84 of the Stacks Project.

## The definition

Let `R` be a commutative ring and `M` an `R`-module. A *direct sum dévissage* of `M` is a
family of submodules `(M_α)_{α ∈ S}`, indexed by an ordinal `S` (meaning the index ranges over
all ordinals `α < S`), that is increasing with respect to inclusion, i.e. `M_β ⊆ M_α` whenever
`β ≤ α < S`, and satisfies:

0. `M_0 = 0` (the zero submodule);
1. `M = ⋃_{α < S} M_α`;
2. if `α < S` is a limit ordinal, then `M_α = ⋃_{β < α} M_β`;
3. if `α + 1 < S`, then `M_α` is a direct summand of `M_{α+1}`, i.e. there is a submodule
   `C ⊆ M_{α+1}` with `M_{α+1} = M_α ⊕ C`.

This is Stacks tag 058U (Definition 10.84.1).

## The decomposition theorem

If `(M_α)_{α ∈ S}` is a direct sum dévissage of `M`, then there is an isomorphism of
`R`-modules `M ≅ ⨁_{α : α + 1 ∈ S} M_{α+1} / M_α`, the direct sum ranging over all ordinals
`α` with `α + 1 < S`, equivalently over the successor ordinals lying in `S`. This is Stacks
tag 058V (Lemma 10.84.2).

More precisely the isomorphism is the sum of the inclusions `ι_α : M_{α+1}/M_α → M` coming
from condition (3): since `M_α` is a direct summand of `M_{α+1}`, a complement `C` of `M_α` in
`M_{α+1}` maps isomorphically to `M_{α+1}/M_α`, and `C ⊆ M_{α+1} ⊆ M`. The isomorphism
statement does not depend on the choices of complements, so the conclusion is stated as the
existence of an `R`-linear isomorphism.
-/

@[expose] public section

universe u

variable {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]

/-- A *direct sum dévissage* of the `R`-module `N`: an increasing family of
submodules `M α` of `N`, indexed by the ordinals `α < S`, satisfying the four
Stacks conditions (0)–(3).

The family `M` is defined on all ordinals; only its values on `α < S` are
constrained, the values for `α ≥ S` being irrelevant (the standard "relaxed
domain" convention). The index set `{α : α < S}` is the Stacks meaning of
"indexed by the ordinal `S`". -/
structure DirectSumDevissage (R N : Type*) [CommRing R] [AddCommGroup N]
    [Module R N] where
  /-- The ordinal indexing the family; the index set is `{α : α < S}`. -/
  S : Ordinal.{u}
  /-- The increasing family of submodules. -/
  M : Ordinal.{u} → Submodule R N
  /-- The family is increasing with respect to inclusion on the index set. -/
  mono : ∀ ⦃β α : Ordinal.{u}⦄, β ≤ α → α < S → M β ≤ M α
  /-- Condition (0): `M_0 = 0`. -/
  zero_eq : M 0 = ⊥
  /-- Condition (1): `M = ⋃_{α < S} M_α`. -/
  iSup_eq : (⨆ α, ⨆ (_ : α < S), M α) = ⊤
  /-- Condition (2): at a limit ordinal `α < S`, `M_α = ⋃_{β < α} M_β`. -/
  limit : ∀ α : Ordinal.{u}, α < S → Order.IsSuccLimit α →
    M α = ⨆ β, ⨆ (_ : β < α), M β
  /-- Condition (3): if `α + 1 < S` then `M_α` is a direct summand of `M_{α+1}`,
  i.e. `M_α` (viewed inside `M_{α+1}`) has a complement `C` in `M_{α+1}`. -/
  summand : ∀ α : Ordinal.{u}, Order.succ α < S →
    ∃ C : Submodule R (M (Order.succ α)),
      IsCompl ((M α).submoduleOf (M (Order.succ α))) C

/-- **Stacks Tag 058V (Lemma 10.84.2).** Given a direct sum dévissage of `N`,
the module `N` is isomorphic to the direct sum of the successive quotients
`M_{α+1} / M_α` over all ordinals `α` with `α + 1 < S`.

Here the `α`-th summand `M_{α+1}/M_α` is realized as the quotient of the
submodule `M (Order.succ α)` of `N` by the image of `M α` inside it
(`(M α).submoduleOf (M (Order.succ α))`, which is `M α ⊓ M (succ α) = M α`
viewed as a submodule of `↥(M (succ α))`). -/
@[stacks 058V]
theorem devissage_iso (D : DirectSumDevissage.{u} R N) :
    Nonempty (N ≃ₗ[R] DirectSum {α : Ordinal.{u} // Order.succ α < D.S}
      (fun a => (D.M (Order.succ a.1)) ⧸ (D.M a.1).submoduleOf (D.M (Order.succ a.1)))) := by
  classical
  -- The index type of the direct sum.
  set T := {α : Ordinal.{u} // Order.succ α < D.S}
  -- For each successor index, choose a complement of `M α` inside `M (succ α)`.
  choose C hC using D.summand
  -- View the complement as a submodule of `N`.
  set Cn : Ordinal.{u} → Submodule R N :=
    fun α => if h : Order.succ α < D.S then
      Submodule.map (D.M (Order.succ α)).subtype (C α h) else ⊥ with hCn
  have hCn_eq : ∀ (α : Ordinal.{u}) (h : Order.succ α < D.S),
      Cn α = Submodule.map (D.M (Order.succ α)).subtype (C α h) := fun α h => by
    simp only [hCn, dite_eq_left h]
  have hCn_le : ∀ (α : Ordinal.{u}), Order.succ α < D.S → Cn α ≤ D.M (Order.succ α) :=
    fun α h => (hCn_eq α h).le.trans (Submodule.map_subtype_le _ _)
  -- Each step: `M (succ α) = M α ⊔ Cn α` and `M α ⊓ Cn α = ⊥`.
  have hstep : ∀ (α : Ordinal.{u}) (h : Order.succ α < D.S),
      D.M (Order.succ α) = D.M α ⊔ Cn α ∧ D.M α ⊓ Cn α = ⊥ := fun α h => by
    -- `map subtype (submoduleOf) = M (succ α) ⊓ M α = M α`
    have hmap : Submodule.map (D.M (Order.succ α)).subtype
        ((D.M α).submoduleOf (D.M (Order.succ α))) = D.M α := by
      unfold Submodule.submoduleOf
      rw [Submodule.map_comap_subtype,
        inf_eq_right.mpr (D.mono (le_of_lt (Order.lt_succ α)) h)]
    rw [hCn_eq α h]
    constructor
    · have := congrArg (Submodule.map (D.M (Order.succ α)).subtype) (hC α h).sup_eq_top
      rw [Submodule.map_sup, Submodule.map_subtype_top, hmap] at this
      exact this.symm
    · have := congrArg (Submodule.map (D.M (Order.succ α)).subtype) (hC α h).inf_eq_bot
      rwa [Submodule.map_inf _ (Submodule.injective_subtype _), Submodule.map_bot,
        hmap] at this
  -- Each `Cn a` is linearly isomorphic to the corresponding quotient summand.
  have hquot : ∀ a : T, ((D.M (Order.succ a.val) ⧸
      (D.M a.val).submoduleOf (D.M (Order.succ a.val))) ≃ₗ[R] (Cn a.val)) := by
    rintro ⟨α, h⟩
    exact (Submodule.quotientEquivOfIsCompl _ (C α h) (hC α h)).trans
      ((Submodule.equivMapOfInjective (D.M (Order.succ α)).subtype
        (Submodule.injective_subtype _) (C α h)).trans (LinearEquiv.ofEq _ _ (hCn_eq α h).symm))
  -- The partial sum of the `Cn` below `β` recovers `M β`, by transfinite induction on
  -- `β < S` (the first transfinite induction of the Stacks proof).
  have hpartial : ∀ β < D.S, (⨆ a : T, ⨆ (_ : a.val < β), Cn a.val) = D.M β := by
    intro β
    induction β using WellFoundedLT.induction with
    | _ β ih =>
      intro hβS
      rcases Ordinal.zero_or_succ_or_isSuccLimit β with rfl | ⟨γ, rfl⟩ | hlim
      · rw [D.zero_eq]
        exact le_antisymm (iSup₂_le fun a ha => absurd ha not_lt_zero) bot_le
      · rw [(hstep γ hβS).1, ← ih γ (Order.lt_succ γ) ((Order.lt_succ γ).trans hβS)]
        refine le_antisymm (iSup₂_le fun a ha => ?_) (sup_le
          (iSup₂_le fun a ha => le_iSup₂_of_le a (ha.trans (Order.lt_succ γ)) le_rfl)
          (le_iSup₂_of_le ⟨γ, hβS⟩ (Order.lt_succ γ) le_rfl))
        rcases (Order.lt_succ_iff.mp ha).lt_or_eq with hlt | heq
        · exact le_sup_of_le_left (le_iSup₂_of_le a hlt le_rfl)
        · exact (congrArg Cn heq).le.trans le_sup_right
      · rw [D.limit β hβS hlim]
        refine le_antisymm (iSup₂_le fun a ha => ?_) (iSup₂_le fun δ hδ => ?_)
        · exact (hCn_le a.val ((hlim.succ_lt ha).trans hβS)).trans
            (le_iSup₂_of_le (Order.succ a.val) (hlim.succ_lt ha) le_rfl)
        · rw [← ih δ hδ (hδ.trans hβS)]
          exact iSup₂_le fun a ha => le_iSup₂_of_le a (ha.trans hδ) le_rfl
  -- The family `fun a : T => Cn a.val` is an internal direct sum of `N`: it is independent,
  -- since each `Cn a.val` is disjoint from the supremum of the strictly-earlier summands (the
  -- lattice form of the second transfinite induction of the Stacks proof), and it spans `N`.
  have hInternal : DirectSum.IsInternal (fun a : T => Cn a.val) := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    refine ⟨Stacks.DirectSum.KaplanskySummand.iSupIndep_of_disjoint_biSup_lt fun a => ?_, ?_⟩
    · have hsup : (⨆ b < a, Cn b.val) = D.M a.val := by
        rw [← hpartial a.val ((Order.lt_succ _).trans a.property)]
        exact le_antisymm
          (iSup₂_le fun b hb => le_iSup₂_of_le b (Subtype.coe_lt_coe.mpr hb) le_rfl)
          (iSup₂_le fun b hb => le_iSup₂_of_le b (Subtype.coe_lt_coe.mp hb) le_rfl)
      rw [hsup, disjoint_iff, inf_comm]
      exact (hstep a.val a.property).2
    · rw [← D.iSup_eq]
      exact le_antisymm
        (iSup_le fun a => le_iSup₂_of_le (Order.succ a.val) a.property (hCn_le a.val a.property))
        (iSup₂_le fun α hα => (hpartial α hα).symm.le.trans
          (iSup₂_le fun a _ => le_iSup_of_le a le_rfl))
  -- Assemble the isomorphism `N ≃ ⨁ Cn a ≃ ⨁ quotient`.
  exact ⟨(LinearEquiv.ofBijective (DirectSum.coeLinearMap fun a : T => Cn a.val)
    hInternal).symm.trans (DFinsupp.mapRange.linearEquiv fun a => (hquot a).symm)⟩



/-!
# Transfinite dévissage of modules

Let `M` be a module over a semiring `R`. A *direct sum dévissage* of `M` is a family of submodules
`(M_α)`, indexed by the ordinals `α` below some ordinal `s` and increasing for inclusion, such that
`M_0 = 0`, such that `M` is the union of the `M_α`, such that `M_α = ⋃_{β < α} M_β` at every limit
ordinal `α`, and such that `M_α` is a direct summand of `M_{α+1}` whenever `α + 1` is again an
index. It is a *Kaplansky dévissage* if moreover every quotient `M_{α+1}/M_α` is countably
generated.

The terminology is justified by the fact that a direct sum dévissage exhibits `M` as the direct sum
`⨁_{α + 1 < s} M_{α+1}/M_α` (Stacks 058V), so that a Kaplansky dévissage exhibits `M` as a direct
sum of countably generated modules (Stacks 058W); that a projective module admits a Kaplansky
dévissage, and is therefore such a direct sum, is Kaplansky's theorem (Stacks 058X and 058Y), for
which these definitions are made.

## Main definitions

* `Submodule.IsDirectSumDevissage`: the family `N` of submodules of `M`, cut off at the ordinal
  `s`, is a direct sum dévissage of `M`, that is, it satisfies conditions (0)–(3) of the source.
* `Submodule.IsKaplanskyDevissage`: it is moreover a Kaplansky dévissage, that is, it satisfies the
  source's condition (4) as well.

## Implementation notes

The index ordinal `S` of the source is a bound `s : Ordinal` and the family is a function
`N : Ordinal → Submodule R M`; every condition is restricted to the indices `α < s`, which is what
`α ∈ S` means, so that the predicate says nothing about the values of `N` outside `Set.Iio s`. For
the same reason "increasing" is `MonotoneOn N (Set.Iio s)` rather than `Monotone N`. A limit
ordinal is `Order.IsSuccLimit`, Mathlib's spelling: nonzero and not a successor, so that condition
(2) does not overlap with condition (0). The universe of the index ordinal is left free: a
dévissage of a module in `Type u` can be taken with `s : Ordinal.{u}`, but nothing here needs that.

Condition (3), that `M_α` is a direct summand of `M_{α+1}`, is stated by an internal complement in
the submodule lattice of `M` — a submodule `P` with `Disjoint (N α) P` and `N α ⊔ P = N (α + 1)` —
rather than by `IsCompl` in the lattice of submodules of `N (α + 1)`, to which it corresponds along
the order isomorphism `Submodule.mapIic (N (α + 1))`. This is the form both sides use: 058X
produces its complements inside `M`, and 058V sums them inside `M`.

Condition (4), that `M_{α+1}/M_α` is countably generated, is stated as the existence of a countable
set `t ⊆ M` with `N (α + 1) = N α ⊔ span R t`: the images of `t` generate the quotient exactly when
this holds, so no quotient module has to be formed, and countability is `Set.Countable`, as in
`Filter.IsCountablyGenerated`, rather than a bound on `Submodule.spanRank`.

The hypotheses are `[Semiring R] [AddCommMonoid M] [Module R M]`, weaker than the source's
commutative ring: only the lattice of submodules, spans, and internal direct sums occur, and none
of these needs additive inverses or commutativity.

Faithfulness, on the four points a reader should check against the source.
(1) No hypothesis is dead: the definitions are predicates on the pair `(s, N)`, and each of the
five (respectively six) conditions constrains it — dropping (1) admits `N = ⊥` with `s = 1` for any
nonzero `M`, dropping (2) admits a family that jumps at `ω`, dropping (3) admits any increasing
exhaustive family, and dropping (4) is exactly the difference between the two definitions.
(2) The scalars and the base are the source's: the `M_α` are `R`-submodules of `M`, the complement
in (3) is an `R`-submodule, and the generating set in (4) spans over `R`; nothing is localized or
base changed.
(3) The source names no canonical map, and what is pinned instead is internal: the exhaustion (1)
and the limit condition (2) are equalities of submodules of `M`, and (3) asks for a complement of
`M_α` inside `M_{α+1}`, not for an abstract isomorphism `M_{α+1} ≅ M_α ⊕ (M_{α+1}/M_α)`.
(4) The instantiation is not degenerate: `N 0 = ⊥` and `N α = ⊤` for `α ≥ 1` with `s = 2` is a
direct sum dévissage of any `M`, and a Kaplansky dévissage exactly when `M` is countably generated,
so both notions are inhabited and the second is a restriction of the first; a free module on an
uncountable basis has a Kaplansky dévissage only for larger `s`, namely the one of 058W.

## References

* [Stacks 058U](https://stacks.math.columbia.edu/tag/058U)
-/



@[expose] public section

namespace Submodule

variable {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- A *direct sum dévissage* of an `R`-module `M` is an increasing family `N` of submodules of `M`,
indexed by the ordinals `α < s`, with `N 0 = 0`, with union `M`, continuous at limit ordinals, and
with `N α` a direct summand of `N (α + 1)` whenever `α + 1 < s`. -/
@[stacks 058U "direct sum devissage"]
public structure IsDirectSumDevissage (s : Ordinal.{w}) (N : Ordinal.{w} → Submodule R M) :
    Prop where
  /-- The family is increasing on its index set. -/
  monotoneOn : MonotoneOn N (Set.Iio s)
  /-- Condition (0): the family starts at the zero submodule. -/
  zero_eq_bot : N 0 = ⊥
  /-- Condition (1): the family exhausts `M`. -/
  iSup_eq_top : (⨆ α < s, N α) = ⊤
  /-- Condition (2): at a limit ordinal the family is the union of the earlier terms. -/
  eq_iSup_of_isSuccLimit : ∀ α < s, Order.IsSuccLimit α → N α = ⨆ β < α, N β
  /-- Condition (3): `N α` is a direct summand of `N (α + 1)`, that is, it has a complement `P`
  inside `N (α + 1)`. -/
  exists_disjoint_sup_eq_succ : ∀ α, α + 1 < s →
    ∃ P : Submodule R M, Disjoint (N α) P ∧ N α ⊔ P = N (α + 1)

/-- A *Kaplansky dévissage* of an `R`-module `M` is a direct sum dévissage all of whose quotients
`N (α + 1) / N α` are countably generated, which is to say that `N (α + 1)` is generated over `N α`
by countably many elements of `M`. -/
@[stacks 058U "Kaplansky devissage"]
public structure IsKaplanskyDevissage (s : Ordinal.{w}) (N : Ordinal.{w} → Submodule R M) : Prop
    extends IsDirectSumDevissage s N where
  /-- Condition (4): the quotient `N (α + 1) / N α` is countably generated. -/
  exists_countable_sup_span_eq_succ : ∀ α, α + 1 < s →
    ∃ t : Set M, t.Countable ∧ N (α + 1) = N α ⊔ span R t

end Submodule

end


@[expose] public section

universe v

/-!
# Direct sums of countably generated modules are exactly the modules with a Kaplansky dévissage

Let `M` be a module over a ring `R`. A Kaplansky dévissage of `M` is an increasing family of
submodules `(M_α)`, indexed by the ordinals below some ordinal, starting at `0`, exhausting `M`,
continuous at limit ordinals, and with `M_α` a direct summand of `M_{α+1}` with countably generated
quotient (`Submodule.IsKaplanskyDevissage`, Stacks 058U). This file proves that `M` is an internal
direct sum of countably generated submodules if and only if it has such a dévissage.

Both directions are constructions on the lattice of submodules of `M`. Given a dévissage, choosing
a complement `P α` of `M_α` in `M_{α+1}` for every `α` produces a family of submodules which is
independent, has supremum `M`, and consists of countably generated submodules; the set of its
values is the required decomposition. Conversely, given an independent set `S` of countably
generated submodules with supremum `M`, well-ordering `S` and taking the partial sums
`M_α = ⨆_{β < α} N_β` produces a dévissage of length `Ordinal.type r + 1`, where `r` is the
well-ordering.

## Main results

* `Stacks.Modules.KaplanskyDevissage.solution`: the proof of Stacks 058W, as stated in
  `Submodule.exists_sSupIndep_countable_span_iff_exists_isKaplanskyDevissage`.

## Implementation notes

The source deduces the "if" direction from Stacks 058V, the statement that a direct sum dévissage
exhibits `M` as the direct sum `⨁_{α+1 ∈ S} M_{α+1}/M_α`. Here the conclusion is internal — an
independent set of submodules of `M` with supremum `⊤` — so the successive quotients are replaced
by the complements `P α` chosen by condition (3), which are the submodules of `M` that 058V's
summands map to. This makes the "if" direction independent of 058V and shortens it: the exhaustion
is a transfinite induction on the dévissage, and the independence is the imported
`Stacks.DirectSum.KaplanskySummand.iSupIndep_of_disjoint_biSup_lt`, which reduces independence of a
family indexed by a linear order to disjointness of each term from the supremum of the earlier
ones.

The length of the dévissage constructed in the "only if" direction is `Ordinal.type r + 1`, one
more than the order type of the well-ordering, not `Ordinal.type r`: the family is indexed by the
ordinals `α < s`, and the term `M_{type r}`, the one that is all of `M`, has to be among them for
condition (1) to hold.

The two general lattice facts this proof needs are imported rather than reproved here: that a
family indexed by a linear order is independent once each term is disjoint from the supremum of the
earlier ones is `Stacks.DirectSum.KaplanskySummand.iSupIndep_of_disjoint_biSup_lt`, and the
modular-lattice fact that a subelement `Q ≤ P` of an element disjoint from `A` and with the same
join with `A` is all of `P` is
`Stacks.DirectSum.KaplanskySummand.eq_of_disjoint_of_le_of_sup_eq`.

## References

* [StacksProject 058W](https://stacks.math.columbia.edu/tag/058W)
-/

namespace Stacks.Modules.KaplanskyDevissage

open Ordinal Submodule

/-- A complement `P` of `A` inside `A ⊔ span R t` is generated by the components in `P` of the
elements of `t`; in particular it is countably generated if `t` is countable. -/
private lemma exists_countable_span_eq_of_disjoint {R : Type*} {M : Type*} [Ring R]
    [AddCommGroup M] [Module R M] {A P : Submodule R M} {t : Set M} (ht : t.Countable)
    (hd : Disjoint A P) (h : A ⊔ P = A ⊔ span R t) :
    ∃ t' : Set M, t'.Countable ∧ span R t' = P := by
  have hmem : ∀ x ∈ t, ∃ y ∈ A, ∃ z ∈ P, y + z = x := by
    intro x hx
    rw [← Submodule.mem_sup, h]
    exact Submodule.mem_sup_right (subset_span hx)
  choose! a ha p hp hap using hmem
  refine ⟨p '' t, ht.image p, ?_⟩
  have hle : span R (p '' t) ≤ P := span_le.2 (by rintro _ ⟨x, hx, rfl⟩; exact hp x hx)
  refine Stacks.DirectSum.KaplanskySummand.eq_of_disjoint_of_le_of_sup_eq hd hle
    (le_antisymm (sup_le_sup_left hle A) (h.trans_le (sup_le le_sup_left (span_le.2 ?_))))
  intro x hx
  have hx' : a x + p x ∈ A ⊔ span R (p '' t) :=
    add_mem (Submodule.mem_sup_left (ha x hx))
      (Submodule.mem_sup_right (subset_span ⟨x, hx, rfl⟩))
  rwa [hap x hx] at hx'

/-- The partial sums of an independent family `A` of countably generated submodules with supremum
`⊤`, taken along a well-ordering `r` of the index type, form a Kaplansky dévissage of length
`Ordinal.type r + 1`. -/
private lemma isKaplanskyDevissage_iSup_typein_lt {R : Type*} {M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] {ι : Type*} (r : ι → ι → Prop) [IsWellOrder ι r] (A : ι → Submodule R M)
    (hindep : iSupIndep A) (hsup : ⨆ i, A i = ⊤)
    (hcount : ∀ i, ∃ t : Set M, t.Countable ∧ span R t = A i) :
    IsKaplanskyDevissage (type r + 1) (fun α => ⨆ i, ⨆ _ : typein r i < α, A i) := by
  set F : Ordinal → Submodule R M := fun α => ⨆ i, ⨆ _ : typein r i < α, A i with hFdef
  have hmono : Monotone F := fun α β hαβ =>
    iSup_mono fun i => iSup_le fun hi => le_iSup_of_le (hi.trans_le hαβ) le_rfl
  have hle : ∀ (i : ι) (α : Ordinal), typein r i < α → A i ≤ F α := fun i α hi =>
    le_iSup_of_le i (le_iSup_of_le hi le_rfl)
  have hlt : ∀ α : Ordinal, α + 1 < type r + 1 → α < type r := fun α hα =>
    (lt_add_one α).trans_le (Order.lt_add_one_iff.1 hα)
  have hsucc : ∀ (α : Ordinal) (h : α < type r), F α ⊔ A (enum r ⟨α, h⟩) = F (α + 1) := by
    intro α h
    have hte : typein r (enum r ⟨α, h⟩) = α := typein_enum r h
    refine le_antisymm
      (sup_le (hmono (lt_add_one α).le) (hle _ (α + 1) (by rw [hte]; exact lt_add_one α))) ?_
    refine iSup_le fun i => iSup_le fun hi => ?_
    rcases lt_or_eq_of_le (Order.lt_add_one_iff.1 hi) with hlt | heq
    · exact le_sup_of_le_left (hle i α hlt)
    · exact le_sup_of_le_right (le_of_eq (congrArg A (typein_injective r (heq.trans hte.symm))))
  have hdisj : ∀ (α : Ordinal) (h : α < type r), Disjoint (F α) (A (enum r ⟨α, h⟩)) := by
    intro α h
    have hte : typein r (enum r ⟨α, h⟩) = α := typein_enum r h
    refine ((hindep (enum r ⟨α, h⟩)).mono_right (iSup_le fun i => iSup_le fun hi => ?_)).symm
    refine le_iSup_of_le i (le_iSup_of_le ?_ le_rfl)
    intro hij
    rw [hij, hte] at hi
    exact absurd hi (lt_irrefl α)
  refine
    { monotoneOn := hmono.monotoneOn _
      zero_eq_bot := by simp [hFdef]
      iSup_eq_top := le_antisymm le_top ?_
      eq_iSup_of_isSuccLimit := ?_
      exists_disjoint_sup_eq_succ := ?_
      exists_countable_sup_span_eq_succ := ?_ }
  · rw [← hsup]
    exact iSup_le fun i =>
      (hle i _ (typein_lt_type r i)).trans (le_biSup F (lt_add_one (type r)))
  · intro α _ hlim
    refine le_antisymm (iSup_le fun i => iSup_le fun hi => ?_) (iSup₂_le fun β hβ => hmono hβ.le)
    have h1 : typein r i + 1 < α := by
      simpa only [Order.succ_eq_add_one] using hlim.succ_lt hi
    exact (hle i _ (lt_add_one _)).trans (le_biSup F h1)
  · exact fun α hα => ⟨A (enum r ⟨α, hlt α hα⟩), hdisj α (hlt α hα), hsucc α (hlt α hα)⟩
  · intro α hα
    obtain ⟨t, ht, hts⟩ := hcount (enum r ⟨α, hlt α hα⟩)
    exact ⟨t, ht, by rw [hts, hsucc α (hlt α hα)]⟩


/-- **Stacks 058W.** Let `M` be a module over a ring `R`. Then `M` is a direct sum of countably
generated `R`-modules — that is, `M` is the internal direct sum of an independent set of countably
generated submodules — if and only if `M` admits a Kaplansky dévissage. -/
public theorem solution (R : Type v) (M : Type u) [Ring R] [AddCommGroup M] [Module R M] :
    (∃ S : Set (Submodule R M), sSupIndep S ∧ sSup S = ⊤ ∧
        ∀ N ∈ S, ∃ t : Set M, t.Countable ∧ span R t = N) ↔
      ∃ (s : Ordinal.{u}) (N : Ordinal.{u} → Submodule R M), IsKaplanskyDevissage s N := by
  constructor
  · rintro ⟨S, hindep, hsup, hcount⟩
    refine ⟨_, _, isKaplanskyDevissage_iSup_typein_lt
      (WellOrderingRel : ↥S → ↥S → Prop) (fun N => (N : Submodule R M))
      ((sSupIndep_iff S).1 hindep) ?_ fun N => hcount N N.2⟩
    rw [← hsup, sSup_eq_iSup']
  · rintro ⟨s, N, h⟩
    choose! P hP₁ hP₂ using h.exists_disjoint_sup_eq_succ
    choose! t ht hts using h.exists_countable_sup_span_eq_succ
    set g : Ordinal.{u} → Submodule R M := fun α => if α + 1 < s then P α else ⊥ with hgdef
    have hgP : ∀ α, α + 1 < s → g α = P α := fun α hα => by simp [hgdef, hα]
    have hgbot : ∀ α, ¬ α + 1 < s → g α = ⊥ := fun α hα => by simp [hgdef, hα]
    have hkey : ∀ α < s, (⨆ β < α, g β) ≤ N α := by
      intro α hα
      refine iSup₂_le fun β hβ => ?_
      by_cases hb : β + 1 < s
      · rw [hgP β hb]
        refine (le_sup_right.trans_eq (hP₂ β hb)).trans (h.monotoneOn hb hα ?_)
        rw [← Order.succ_eq_add_one]
        exact Order.succ_le_of_lt hβ
      · rw [hgbot β hb]; exact bot_le
    have hindep : iSupIndep g := by
      refine Stacks.DirectSum.KaplanskySummand.iSupIndep_of_disjoint_biSup_lt fun α => ?_
      by_cases hb : α + 1 < s
      · rw [hgP α hb]
        exact (hP₁ α hb).symm.mono_right (hkey α ((lt_add_one α).trans hb))
      · rw [hgbot α hb]; exact disjoint_bot_left
    refine ⟨Set.range g, hindep.sSupIndep_range, ?_, ?_⟩
    · have claim : ∀ β, β < s → N β ≤ ⨆ α, g α := by
        intro β
        induction β using Ordinal.limitRecOn with
        | zero => intro _; rw [h.zero_eq_bot]; exact bot_le
        | add_one γ ih =>
          intro hγ
          rw [← hP₂ γ hγ]
          refine sup_le (ih ((lt_add_one γ).trans hγ)) ?_
          rw [← hgP γ hγ]
          exact le_iSup g γ
        | limit γ hlim ih =>
          intro hγ
          rw [h.eq_iSup_of_isSuccLimit γ hγ hlim]
          exact iSup₂_le fun δ hδ => ih δ hδ (hδ.trans hγ)
      refine le_antisymm le_top ?_
      rw [sSup_range, ← h.iSup_eq_top]
      exact iSup₂_le claim
    · rintro Q ⟨α, rfl⟩
      by_cases hb : α + 1 < s
      · rw [hgP α hb]
        exact exists_countable_span_eq_of_disjoint (ht α hb) (hP₁ α hb)
          ((hP₂ α hb).trans (hts α hb))
      · rw [hgbot α hb]
        exact ⟨∅, Set.countable_empty, span_empty⟩

end Stacks.Modules.KaplanskyDevissage

/-!
# Kaplansky dévissages and direct sums of countably generated modules

Let `M` be a module over a ring `R`. Then `M` is a direct sum of countably generated `R`-modules if
and only if it admits a Kaplansky dévissage, that is, an increasing family of submodules of `M`,
indexed by the ordinals below some ordinal, starting at `0`, exhausting `M`, continuous at limit
ordinals, and with each term a direct summand of its successor with countably generated quotient
(`Submodule.IsKaplanskyDevissage`, Stacks 058U).

One direction is the fact that a direct sum dévissage exhibits `M` as the direct sum of its
successive quotients (Stacks 058V). For the other, a decomposition `M = ⨁_{i ∈ I} N_i` into
countably generated submodules is turned into a dévissage by well-ordering `I` and taking partial
sums `M_i = ⨆_{j < i} N_j`. Together with the fact that a direct summand of such a direct sum is
again one (Stacks 058X), this is the transfinite dévissage behind Kaplansky's theorem that a
projective module is a direct sum of countably generated modules (Stacks 058Y).

## Main results

* `Submodule.exists_sSupIndep_countable_span_iff_exists_isKaplanskyDevissage`: `M` is a direct sum
  of countably generated `R`-modules if and only if it admits a Kaplansky dévissage.

## Implementation notes

"`M` is a direct sum of countably generated `R`-modules" is stated internally, as the existence of
a set `S` of submodules of `M` which is independent and has supremum `⊤`, each member of which is
countably generated. Independence together with `sSup S = ⊤` says exactly that the canonical map
`⨁ N : S, N → M` is an isomorphism, by `sSupIndep_iff` and
`DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top`, so the internal form implies the
external one, and conversely the images of the summands under an isomorphism `M ≅ ⨁_{i ∈ I} P_i`
form such a set: distinct members of an independent family are distinct submodules unless both are
zero, so passing from a family to its set of values loses nothing.

A set of submodules rather than an indexed family also keeps the statement free of universe
bookkeeping: the indices of a dévissage of `M : Type u` are ordinals, which live one universe up,
while the submodules they name live in `Type u`, so only the set formulation states the two sides
in the same universe. The dévissage is indexed by `Ordinal.{u}`, the ordinals of `M`'s own
universe: this is where a dévissage always exists, since it is built from a well-ordering of a set
of submodules of `M`, a type in `Type u`, whereas `Ordinal.{w}` for a smaller `w` need contain no
ordinal long enough.

Countable generation of a submodule `N` is written as the existence of a countable `t : Set M` with
`span R t = N`, the spelling used for the quotients of a dévissage (Stacks 058U) and for countably
generated modules elsewhere in this development (Stacks 0590), rather than as the cardinal bound
`N.spanRank ≤ Cardinal.aleph0`, to which it is equivalent by `Submodule.spanRank_span_le_card` and
`Submodule.exists_span_set_card_eq_spanRank`.

The source's commutative ring is weakened to a ring: commutativity is nowhere used. Additive
inverses are not dropped, and this is not slack. They are the hypotheses of
`Submodule.IsKaplanskyDevissage`, whose condition (3) reads "`M_α` is a direct summand of
`M_{α + 1}`" as an internal complement, `Disjoint (N α) P` with `N α ⊔ P = N (α + 1)`; over a
semiring an internal complement need not split, so that reading would not say what the source
means. For instance `R = ℕ` and `M = ℕ∞` have the submodules `N = {0, ⊤}` and `P = ℕ`, disjoint
with supremum `⊤`, while `⊤ = ⊤ + 0 = ⊤ + 1` decomposes an element of `M` in two ways, so `M` is
not their direct sum. On the left hand side the same phenomenon would make `sSupIndep S` weaker
than independence of the family of summands.

Faithfulness. (1) No hypothesis is dead: the hypotheses are that `R` is a ring and `M` an
`R`-module, and nothing else, so there is no auxiliary condition making this a decorated special
case; both sides are conditions on that one module `M`, the left the source's "is a direct sum of
countably generated `R`-modules" and the right its "admits a Kaplansky dévissage".
(2) The scalars and the base are the source's: `S` consists of `R`-submodules of `M`, the
generating sets span over `R`, and the dévissage is a family of `R`-submodules of `M`; nothing is
localized or base changed. (3) The source names no canonical map. What is pinned instead is
internal to `M`: the decomposition is an independent set of submodules of `M` with supremum `⊤`
rather than an abstract isomorphism onto a direct sum, and the dévissage is a family of submodules
of `M`, so both sides are statements about the lattice of submodules of `M` and not merely about
its isomorphism class. (4) The instantiation is not degenerate and neither side is automatic: for
`M` countably generated both sides hold, with `S = {⊤}` and the dévissage `⊥, ⊤` of length `2`; for
`M = ⨁_{i ∈ I} R` free on an uncountable `I` both hold with `S` the set of coordinate lines and a
dévissage of length the order type of a well-ordering of `I`; and both fail for the Baer–Specker
group `M = ℤ^ℕ` over `ℤ`, whose countably generated subgroups are all free because `ℤ^ℕ` is
`ℵ₁`-free, so that countably generated summands would exhibit `ℤ^ℕ` as a direct sum of free modules
and hence as free, which Specker's theorem forbids.

## References

* [StacksProject 058W](https://stacks.math.columbia.edu/tag/058W)
* I. Kaplansky, *Projective modules*, Ann. of Math. (2) 68 (1958), 372–377
-/



namespace Submodule

/-- **Stacks 058W.** Let `M` be a module over a ring `R`. Then `M` is a direct sum of countably
generated `R`-modules — that is, `M` is the internal direct sum of an independent set of countably
generated submodules — if and only if `M` admits a Kaplansky dévissage. -/
@[stacks 058W "Countable generation written as a countable spanning set, and the direct sum
  decomposition internally, as an independent set of submodules of `M` with supremum `⊤`."]
public theorem exists_sSupIndep_countable_span_iff_exists_isKaplanskyDevissage
    (R : Type v) (M : Type u) [Ring R] [AddCommGroup M] [Module R M] :
    (∃ S : Set (Submodule R M), sSupIndep S ∧ sSup S = ⊤ ∧
        ∀ N ∈ S, ∃ t : Set M, t.Countable ∧ span R t = N) ↔
      ∃ (s : Ordinal.{u}) (N : Ordinal.{u} → Submodule R M),
        IsKaplanskyDevissage s N :=
  Stacks.Modules.KaplanskyDevissage.solution R M

end Submodule

end
