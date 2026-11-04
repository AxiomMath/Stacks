module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.DescentDatumFromGlueingAtTheOverlap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.HomGlueingAtThePairSubsystems
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.NonDegenerateCoveringCollection

/-!
# Tag 0D6A: the glueing of morphisms is read at named opens, not at every one

Let `(X, 𝒪_X)` be a ringed space and `S` a system of locally given derived objects on it, as in
Situation [Stacks, Tag 0D67].  After
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.HomGlueingAtThePairSubsystems` the
existence half of [Stacks, Tag 0D6A] rests on the sheaf condition of [Stacks, Tag 0D66] part (2)
at two *systems* — the given one and the subsystem carried by
`Stacks.DerivedGlueing.opensBelowPair S U V`.  At each of those it is still asked for at **every**
open which is a union of members.  That is more than the proof reads.

`Stacks.DerivedGlueing.nonempty_solutionOver_sup_of_glueing` consumes the uniqueness clause of
[Stacks, Tag 0D68] at exactly two places:

* for the given system, at the single open `U ⊓ V`;
* for the pair subsystem, at the *members* `W` of the collection contained in `U ⊔ V`, and at no
  other open.

This file rewrites the chain so that only those appear, and the narrowing pays for itself at
once: a glueing condition asked for only at opens which are members of the collection it is
asked about is `Stacks.DerivedGlueing.hasGluingForHomsAt_of_mem`, which is a theorem.

## What the narrowing buys — a witness with a covering collection that omits `⊤`

`Stacks.DerivedGlueing.HasGluingForHomsOver` has, in this development, exactly one source of
inhabitants, `Stacks.DerivedGlueing.hasGluingForHomsOver_of_covered_mem`, and for a collection
that covers the space that source forces `⊤` into the collection — whereupon
`Stacks.DerivedGlueing.exists_solution_of_top_mem` already proves the conclusion with nothing
assumed.  So every witness of the existence statement obtained from it is degenerate in the sense
recorded by
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.NonDegenerateCoveringCollection`:
`⊤ ∈ S.opens`.  The witness of
`Stacks.DerivedGlueing.nonempty_solution_botTop_single`, at the collection `{⊥, ⊤}`, is of
exactly that kind, and says so.

The narrowed hypotheses are not forced into it.  They hold for any system whose collection is
closed under meeting a member with a union of members
(`Stacks.DerivedGlueing.hasGluingForHomsAt_inf_pairs_of_inf_mem`) and whose members below the
union of such a pair lie below one of the two
(`Stacks.DerivedGlueing.hasGluingForHomsAt_opensBelowPair_of_split`), and `⊤` need not be a
member.  `Stacks.DerivedGlueing.idempotentPairCollection` — the three opens `⊥`, `D(e)` and
`D(1 - e)` of `Spec (ℤ × ℤ)` — is such a collection: it covers the space, its two proper members
are a finite cover of it, and it does **not** contain `⊤`, so
`Stacks.DerivedGlueing.exists_solution_of_top_mem` does not apply there.
`Stacks.DerivedGlueing.nonempty_solution_idempotentPair` instantiates every binder of the
narrowed existence statement at it, with no hypothesis on the sheaf of modules that prescribes
the objects.

What that witness does **not** escape is the other degeneracy, and this file claims no more: the
system is `Stacks.DerivedGlueing.locallyGivenOfGlobal`, so its objects come from a single global
one and `Stacks.DerivedGlueing.solutionOverOfGlobal` supplies a solution by other means.  No
system in this development prescribes objects that are not globally given, so no witness here
can be non-degenerate in that second sense.

## The narrowing is machine-checked, not asserted

Both new hypotheses sit in hypothesis position, so asking for less of them makes every statement
below **stronger**.
`Stacks.DerivedGlueing.hasGluingForHomsAt_pairs_of_hasGluingForHomsOver_pairs` derives them from
the pair-subsystem hypotheses of
`Stacks.DerivedGlueing.exists_solution_of_finite_cover_of_homs_pairs`, which
`Stacks.DerivedGlueing.hasGluingForHomsOver_pairs_of_subcollections` in turn derives from the
`∀ 𝒟 ⊆ S.opens` form.  So the three forms are ordered, and the ordering is checked.

## Main results

* `Stacks.DerivedGlueing.existsUnique_solutionOverIso_of_hasGluingForHomsAt`: the uniqueness
  clause of [Stacks, Tag 0D68] over one open, from the glueing of morphisms at that open alone.
* `Stacks.DerivedGlueing.nonempty_solutionOver_sup_of_glueingAt`: the two-open case of
  [Stacks, Tag 0D6A] from the uniqueness clause at the two places the argument reads it.
* `Stacks.DerivedGlueing.exists_solution_of_finite_cover_of_homs_at`: **[Stacks, Tag 0D6A],
  existence, from the glueing of morphisms at those opens alone.**
* `Stacks.DerivedGlueing.hasGluingForHomsAt_pairs_of_hasGluingForHomsOver_pairs`: the narrowed
  hypotheses follow from the previous ones.
* `Stacks.DerivedGlueing.hasGluingForHomsAt_inf_pairs_of_inf_mem` and
  `Stacks.DerivedGlueing.hasGluingForHomsAt_opensBelowPair_of_split`: both narrowed hypotheses
  discharged, with no appeal to [Stacks, Tag 0D66] part (2).
* `Stacks.DerivedGlueing.nonempty_solution_idempotentPair`: every binder of the narrowed
  existence statement instantiated at once, at a covering collection of `Spec (ℤ × ℤ)` that does
  not contain `⊤`.

## References

* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 0D6A](https://stacks.math.columbia.edu/tag/0D6A)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Stacks.DerivedGlueing

universe u

/-! ### A collection `{⊥, a, b}` for a complemented pair, in an abstract complete lattice -/

section ComplementedPair

variable {α : Type*} [CompleteLattice α] {a b : α}

/-- **An element which is the supremum of the members of `{⊥, a, b}` below it is one of four.**
Which of `a`, `b` it dominates decides it: both, and it is `⊤` because they join to `⊤`; one, and
it is that one; neither, and it is `⊥`.

The lattice is abstract on purpose.  Stated at `Opens` of the concrete carrier below, the
case bash that follows spends its whole recursion budget synthesising `OrderBot` through the
definition of that carrier. -/
theorem eq_of_sSup_botPair (hsup : a ⊔ b = ⊤) (V : α)
    (hV : V = sSup {W | W ∈ ({⊥, a, b} : Set α) ∧ W ≤ V}) :
    V = ⊥ ∨ V = a ∨ V = b ∨ V = ⊤ := by
  classical
  have key : ∀ c, (a ≤ V → a ≤ c) → (b ≤ V → b ≤ c) → V ≤ c := fun c ha hb =>
    hV.le.trans <| sSup_le <| by
      rintro W ⟨hW, hWV⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hW
      rcases hW with rfl | rfl | rfl
      exacts [bot_le, ha hWV, hb hWV]
  by_cases h1 : a ≤ V
  · by_cases h2 : b ≤ V
    · exact Or.inr (Or.inr (Or.inr (top_le_iff.mp (hsup.symm.trans_le (sup_le h1 h2)))))
    · exact Or.inr (Or.inl (le_antisymm (key a (fun _ => le_rfl) (absurd · h2)) h1))
  · by_cases h2 : b ≤ V
    · exact Or.inr (Or.inr (Or.inl (le_antisymm (key b (absurd · h1) (fun _ => le_rfl)) h2)))
    · exact Or.inl (le_bot_iff.mp (key ⊥ (absurd · h1) (absurd · h2)))

/-- **Meeting a member with a supremum of members gives a member.**  This is the hypothesis of
`Stacks.DerivedGlueing.hasGluingForHomsAt_inf_pairs_of_inf_mem` for such a collection. -/
theorem inf_mem_botPair (hsup : a ⊔ b = ⊤) (hinf : a ⊓ b = ⊥)
    {U : α} (hU : U ∈ ({⊥, a, b} : Set α)) {V : α}
    (hV : V = sSup {W | W ∈ ({⊥, a, b} : Set α) ∧ W ≤ V}) :
    U ⊓ V ∈ ({⊥, a, b} : Set α) := by
  have hinf' : b ⊓ a = ⊥ := (inf_comm b a).trans hinf
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hU ⊢
  rcases eq_of_sSup_botPair hsup V hV with rfl | rfl | rfl | rfl <;>
    rcases hU with rfl | rfl | rfl <;> simp [hinf, hinf']

/-- **A member below the join of a member and a supremum of members is below one of the two.**
This is the hypothesis of `Stacks.DerivedGlueing.hasGluingForHomsAt_opensBelowPair_of_split` for
such a collection.  `a` and `b` are incomparable and neither is `⊥`, so the thirty-six cases of
the two classifications leave nothing. -/
theorem split_botPair (hsup : a ⊔ b = ⊤) (hinf : a ⊓ b = ⊥) (ha : a ≠ ⊥) (hb : b ≠ ⊥)
    {U : α} (hU : U ∈ ({⊥, a, b} : Set α)) {V : α}
    (hV : V = sSup {W | W ∈ ({⊥, a, b} : Set α) ∧ W ≤ V})
    {W : α} (hW : W ∈ ({⊥, a, b} : Set α)) (hWUV : W ≤ U ⊔ V) :
    W ≤ U ∨ W ≤ V := by
  have hab : ¬ (a ≤ b) := fun h => ha ((inf_eq_left.mpr h).symm.trans hinf)
  have hba : ¬ (b ≤ a) := fun h => hb ((inf_eq_left.mpr h).symm.trans ((inf_comm b a).trans hinf))
  have hUc : U = ⊥ ∨ U = a ∨ U = b ∨ U = ⊤ := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hU
    tauto
  have hVc := eq_of_sSup_botPair hsup V hV
  have side : ∀ {x y : α}, ¬ x ≤ y → (U = ⊥ ∨ U = x ∨ U = y ∨ U = ⊤) →
      (V = ⊥ ∨ V = x ∨ V = y ∨ V = ⊤) → x ≤ U ⊔ V → x ≤ U ∨ x ≤ V := by
    intro x y hxy hUx hVx hx
    have h : ∀ {Z : α}, (Z = ⊥ ∨ Z = x ∨ Z = y ∨ Z = ⊤) → x ≤ Z ∨ Z ≤ y := by
      rintro Z (rfl | rfl | rfl | rfl)
      exacts [Or.inr bot_le, Or.inl le_rfl, Or.inr le_rfl, Or.inl le_top]
    rcases h hUx with h₁ | h₁
    · exact Or.inl h₁
    · rcases h hVx with h₂ | h₂
      · exact Or.inr h₂
      · exact absurd (hx.trans (sup_le h₁ h₂)) hxy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hW
  rcases hW with rfl | rfl | rfl
  · exact Or.inl bot_le
  · exact side hab hUc hVc hWUV
  · exact side hba (by tauto) (by tauto) hWUV

/-- The collection covers: its supremum is `⊤`. -/
theorem sSup_botPair (hsup : a ⊔ b = ⊤) : sSup ({⊥, a, b} : Set α) = ⊤ := by
  refine le_antisymm le_top (hsup.symm.trans_le (sup_le ?_ ?_))
  · exact le_sSup (by simp)
  · exact le_sSup (by simp)

/-- Hypothesis (2) of [Stacks, Tag 0D6A] for the collection: the meet of two members is itself a
member, hence the supremum of the members below it. -/
theorem inter_eq_sSup_botPair (hsup : a ⊔ b = ⊤) (hinf : a ⊓ b = ⊥) :
    ∀ A ∈ ({⊥, a, b} : Set α), ∀ B ∈ ({⊥, a, b} : Set α),
      A ⊓ B = sSup {W | W ∈ ({⊥, a, b} : Set α) ∧ W ≤ A ⊓ B} := by
  intro A hA B hB
  have hBsup : B = sSup {W | W ∈ ({⊥, a, b} : Set α) ∧ W ≤ B} :=
    le_antisymm (le_sSup ⟨hB, le_rfl⟩) (sSup_le fun _ h => h.2)
  exact le_antisymm (le_sSup ⟨inf_mem_botPair hsup hinf hA hBsup, le_rfl⟩)
    (sSup_le fun _ h => h.2)

/-- `⊤` is not a member, when neither of the three is `⊤`. -/
theorem top_notMem_botPair (hbot : (⊥ : α) ≠ ⊤) (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (⊤ : α) ∉ ({⊥, a, b} : Set α) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rintro (h | h | h)
  exacts [hbot h.symm, ha h.symm, hb h.symm]

end ComplementedPair

/-! ### The collection on `Spec (ℤ × ℤ)` -/

section Collection

/-- **The collection `{⊥, D(e), D(1 - e)}` of opens of `Spec (ℤ × ℤ)`.**  Its two proper members
are the basic opens of the two idempotents, which cover the space and meet in `⊥`; together with
`⊥` they form a collection closed under intersection and under meeting a member with a union of
members, and `⊤` is not one of them. -/
def idempotentPairCollection : Set (Opens (specULiftProdRingedSpace.{u}).carrier) :=
  {⊥, idempotentOpen.{u} ⟨(1, 0)⟩, idempotentOpen.{u} ⟨(0, 1)⟩}

/-- The empty open is not the whole space: the first basic open is contained in the latter and
is not empty. -/
theorem bot_ne_top_specULiftProd :
    (⊥ : Opens (specULiftProdRingedSpace.{u}).carrier) ≠ ⊤ := fun h =>
  idempotentOpen_fst_ne_bot.{u} (le_bot_iff.mp (le_of_le_of_eq le_top h.symm))

/-- `Stacks.DerivedGlueing.inf_mem_botPair` at the two idempotent opens. -/
theorem inf_mem_idempotentPairCollection
    {U : Opens (specULiftProdRingedSpace.{u}).carrier}
    (hU : U ∈ idempotentPairCollection.{u})
    {V : Opens (specULiftProdRingedSpace.{u}).carrier}
    (hV : V = sSup {W | W ∈ idempotentPairCollection.{u} ∧ W ≤ V}) :
    U ⊓ V ∈ idempotentPairCollection.{u} :=
  inf_mem_botPair (a := idempotentOpen.{u} ⟨(1, 0)⟩) (b := idempotentOpen.{u} ⟨(0, 1)⟩)
    sup_idempotentOpen_eq_top.{u} inf_idempotentOpen_eq_bot.{u} hU hV

/-- `Stacks.DerivedGlueing.split_botPair` at the two idempotent opens. -/
theorem split_idempotentPairCollection
    {U : Opens (specULiftProdRingedSpace.{u}).carrier}
    (hU : U ∈ idempotentPairCollection.{u})
    {V : Opens (specULiftProdRingedSpace.{u}).carrier}
    (hV : V = sSup {W | W ∈ idempotentPairCollection.{u} ∧ W ≤ V})
    {W : Opens (specULiftProdRingedSpace.{u}).carrier}
    (hW : W ∈ idempotentPairCollection.{u}) (hWUV : W ≤ U ⊔ V) :
    W ≤ U ∨ W ≤ V :=
  split_botPair (a := idempotentOpen.{u} ⟨(1, 0)⟩) (b := idempotentOpen.{u} ⟨(0, 1)⟩)
    sup_idempotentOpen_eq_top.{u} inf_idempotentOpen_eq_bot.{u}
    idempotentOpen_fst_ne_bot.{u} idempotentOpen_snd_ne_bot.{u} hU hV hW hWUV

/-- The collection covers `Spec (ℤ × ℤ)`. -/
theorem sSup_idempotentPairCollection : sSup idempotentPairCollection.{u} = ⊤ :=
  sSup_botPair (a := idempotentOpen.{u} ⟨(1, 0)⟩) (b := idempotentOpen.{u} ⟨(0, 1)⟩)
    sup_idempotentOpen_eq_top.{u}

/-- **`⊤` is not a member**, so `Stacks.DerivedGlueing.exists_solution_of_top_mem` does not apply
to the system this collection carries. -/
theorem top_notMem_idempotentPairCollection :
    (⊤ : Opens (specULiftProdRingedSpace.{u}).carrier) ∉ idempotentPairCollection.{u} :=
  top_notMem_botPair (a := idempotentOpen.{u} ⟨(1, 0)⟩) (b := idempotentOpen.{u} ⟨(0, 1)⟩)
    bot_ne_top_specULiftProd.{u} idempotentOpen_fst_ne_top.{u} idempotentOpen_snd_ne_top.{u}

/-- **The saturation hypothesis fails at this collection.**  `⊤` is the union of the members
contained in it and is not a member, so
`Stacks.DerivedGlueing.hasGluingForHomsOver_of_covered_mem` — the only source of inhabitants of
`Stacks.DerivedGlueing.HasGluingForHomsOver` in this development — cannot be applied here.  The
narrowing of the hypothesis is therefore not a convenience: without it this collection carries no
witness at all. -/
theorem not_covered_mem_idempotentPairCollection :
    ¬ (∀ O : Opens (specULiftProdRingedSpace.{u}).carrier,
        O = sSup {W | W ∈ idempotentPairCollection.{u} ∧ W ≤ O} →
      O ∈ idempotentPairCollection.{u}) := by
  intro h
  refine top_notMem_idempotentPairCollection.{u} (h ⊤ ?_)
  refine le_antisymm ?_ le_top
  exact sSup_idempotentPairCollection.{u}.symm.trans_le
    (sSup_le fun W hW => le_sSup ⟨hW, le_top⟩)

/-- Hypothesis (2) of [Stacks, Tag 0D6A] for the collection. -/
theorem inter_eq_sSup_idempotentPairCollection :
    ∀ A ∈ idempotentPairCollection.{u}, ∀ B ∈ idempotentPairCollection.{u},
      A ⊓ B = sSup {W | W ∈ idempotentPairCollection.{u} ∧ W ≤ A ⊓ B} :=
  inter_eq_sSup_botPair (a := idempotentOpen.{u} ⟨(1, 0)⟩) (b := idempotentOpen.{u} ⟨(0, 1)⟩)
    sup_idempotentOpen_eq_top.{u} inf_idempotentOpen_eq_bot.{u}

end Collection

section Narrowed

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-! ### The uniqueness clause of Tag 0D68 over a single open -/

/-! ### The two-open case from the opens the argument reads -/

/-- **A solution of the pair subsystem over `U ∪ V` is a solution of the system there, from the
uniqueness clause at the members of the collection below `U ∪ V` only.**

This is `Stacks.DerivedGlueing.nonempty_solutionOver_sup_of_subcollectionSolution` with its four
hypotheses on the system removed.  They served only to check, at each member `W` of the
collection below `U ⊔ V`, the two covering conditions and the negative self-Ext condition that
`Stacks.DerivedGlueing.HasUniqueSolutionOverIso` demands before it may be applied at `W`; the
hypothesis here is that application's conclusion, so none of them is needed. -/
theorem nonempty_solutionOver_sup_of_subcollectionSolutionAt (S : LocallyGiven X)
    (U V : Opens X.carrier)
    (huniqAt : ∀ (W : Opens X.carrier), W ∈ S.opens → W ≤ U ⊔ V →
      ∀ A B : SolutionOver (S.subcollection (opensBelowPair S U V)
          (opensBelowPair_subset S U V)) W,
        ∃! φ : A.obj ≅ B.obj, A.IsCompatibleHom B φ.hom)
    (FS : SolutionOver
      (S.subcollection (opensBelowPair S U V) (opensBelowPair_subset S U V)) (U ⊔ V)) :
    Nonempty (SolutionOver S (U ⊔ V)) := by
  have key : ∀ (W : Opens X.carrier) (hW : W ∈ S.opens) (hWP : W ≤ U ⊔ V),
      ∃! φ : (FS.restrictOpen W hWP).obj ≅
          (selfSolutionOverSubcollection S (opensBelowPair S U V)
            (opensBelowPair_subset S U V) W hW).obj,
        (FS.restrictOpen W hWP).IsCompatibleHom
          (selfSolutionOverSubcollection S (opensBelowPair S U V)
            (opensBelowPair_subset S U V) W hW) φ.hom :=
    fun W hW hWP => huniqAt W hW hWP (FS.restrictOpen W hWP)
      (selfSolutionOverSubcollection S (opensBelowPair S U V)
        (opensBelowPair_subset S U V) W hW)
  choose rho hrho hrhouniq using key
  refine ⟨{ obj := FS.obj, rho := rho, compatibility := ?_ }⟩
  intro V₀ W₀ hW₀V₀ hV₀ hW₀ hV₀P
  have hpsi := (restrictOpen_comparison_isCompatibleHom FS hV₀P hW₀V₀).comp
    (((hrho V₀ hV₀ hV₀P).restrictOpen hW₀V₀).comp
      (selfSolutionOverSubcollection_rho_isCompatibleHom S (opensBelowPair S U V)
        (opensBelowPair_subset S U V) V₀ W₀ hW₀V₀ hV₀ hW₀))
  exact congrArg (fun e => e.hom)
    (hrhouniq W₀ hW₀ (hW₀V₀.trans hV₀P)
      ((S.restrictionComp W₀ V₀ (U ⊔ V) hW₀V₀ hV₀P).app FS.obj ≪≫
        (S.restriction W₀ V₀ hW₀V₀).mapIso (rho V₀ hV₀ hV₀P) ≪≫
        S.rho W₀ V₀ hW₀V₀ hV₀ hW₀) hpsi)

/-- **The two-open case at one pair of opens, from the uniqueness clause of [Stacks, Tag 0D68]
at exactly the two places the argument reads it.**

`Stacks.DerivedGlueing.nonempty_solutionOver_sup_of_glueing` already isolates the two *systems*;
this isolates the opens as well.  The clause is read for the given system at the single open
`U ⊓ V`, to compare the two restrictions there, and for the pair subsystem at the members of the
collection contained in `U ⊔ V`.  Every other hypothesis of
`nonempty_solutionOver_sup_of_glueing` served only to license those two applications and is
therefore gone. -/
theorem nonempty_solutionOver_sup_of_glueingAt (S : LocallyGiven X) (U V : Opens X.carrier)
    (huniqS : ∀ A B : SolutionOver S (U ⊓ V),
      ∃! φ : A.obj ≅ B.obj, A.IsCompatibleHom B φ.hom)
    (huniqSubAt : ∀ (W : Opens X.carrier), W ∈ S.opens → W ≤ U ⊔ V →
      ∀ A B : SolutionOver (S.subcollection (opensBelowPair S U V)
          (opensBelowPair_subset S U V)) W,
        ∃! φ : A.obj ≅ B.obj, A.IsCompatibleHom B φ.hom)
    (hglue : ∀ (A : OpenDerivedCategory X U) (B : OpenDerivedCategory X V)
      (c : (S.restriction (U ⊓ V) U inf_le_left).obj A ≅
        (S.restriction (U ⊓ V) V inf_le_right).obj B),
      ∃ (F : OpenDerivedCategory X (U ⊔ V))
        (f : (S.restriction U (U ⊔ V) le_sup_left).obj F ≅ A)
        (g : (S.restriction V (U ⊔ V) le_sup_right).obj F ≅ B),
        (S.restrictionComp (U ⊓ V) U (U ⊔ V) inf_le_left le_sup_left).hom.app F ≫
            (S.restriction (U ⊓ V) U inf_le_left).map f.hom ≫ c.hom =
          (S.restrictionComp (U ⊓ V) V (U ⊔ V) inf_le_right le_sup_right).hom.app F ≫
            (S.restriction (U ⊓ V) V inf_le_right).map g.hom)
    (A : SolutionOver S U) (B : SolutionOver S V) :
    Nonempty (SolutionOver S (U ⊔ V)) := by
  obtain ⟨c, hc, -⟩ :=
    huniqS (A.restrictOpen (U ⊓ V) inf_le_left) (B.restrictOpen (U ⊓ V) inf_le_right)
  obtain ⟨F, f, g, hfg⟩ := hglue A.obj B.obj c
  exact nonempty_solutionOver_sup_of_subcollectionSolutionAt S U V huniqSubAt
    (glueSolutionOverSubcollection S U V F A B f g c hfg hc)

/-! ### Tag 0D6A, existence, from the glueing of morphisms at those opens -/

/-- **The two-open case of [Stacks, Tag 0D6A] from the glueing of morphisms at the opens the
argument reads.**  The uniqueness clause at each of the two places is
`Stacks.DerivedGlueing.existsUnique_solutionOverIso_of_hasGluingForHomsAt`, and the negative
self-Ext hypothesis it needs at the pair subsystem is the ambient one restricted along
`Stacks.DerivedGlueing.opensBelowPair_subset`. -/
theorem gluesAlongTwoOpens_of_hasGluingForHomsAt_pairs (S : LocallyGiven X)
    (hhomS : ∀ (U V : Opens X.carrier), U ∈ S.opens →
        V = sSup {W | W ∈ S.opens ∧ W ≤ V} →
        U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V} →
      HasGluingForHomsAt S (U ⊓ V))
    (hhomP : ∀ (U V : Opens X.carrier), U ∈ S.opens →
        V = sSup {W | W ∈ S.opens ∧ W ≤ V} →
        U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V} →
      ∀ W ∈ S.opens, W ≤ U ⊔ V →
        HasGluingForHomsAt (S.subcollection (opensBelowPair S U V)
          (opensBelowPair_subset S U V)) W)
    (hglue : GluesObjectsAlongTwoOpens S) :
    GluesAlongTwoOpens S := by
  intro U hU V hV hUV _hinter hExt A B
  refine nonempty_solutionOver_sup_of_glueingAt S U V (fun A' B' => ?_) (fun W hW hWP A' B' => ?_)
    (hglue U V) A B
  · exact Stacks.DerivedGlueing.existsUnique_solutionOverIso_of_hasGluingForHomsAt S
      (hhomS U V hU hV hUV) hExt A' B'
  · exact Stacks.DerivedGlueing.existsUnique_solutionOverIso_of_hasGluingForHomsAt _
      (hhomP U V hU hV hUV W hW hWP)
      (fun U' hU' i hi => hExt U' (opensBelowPair_subset S U V hU') i hi) A' B'

/-- **Existence of a solution over a finite cover, from the sheaf condition of
[Stacks, Tag 0D66] part (2) at the opens the proof reads.**

In Situation [Stacks, Tag 0D67], assume that `X = U_1 ∪ … ∪ U_n` with `U_i` in the collection,
that the intersection of two members of the collection is the union of the members contained in
it, that the prescribed objects have no negative self-Ext, and that the glueing of morphisms
holds for the system over the single open `U ⊓ V` and for the pair subsystem over the members of
the collection contained in `U ⊔ V`.  Then the system has a solution.  The compatibility clause
of the transport of [Stacks, Tag 08DG] is `Stacks.DerivedGlueing.gluesObjectsAlongTwoOpens`;
`Stacks.DerivedGlueing.nonempty_solution_idempotentPair` instantiates every binder at a covering
collection that does not contain `⊤`. -/
theorem exists_solution_of_finite_cover_of_homs_at (S : LocallyGiven X)
    (hhomS : ∀ (U V : Opens X.carrier), U ∈ S.opens →
        V = sSup {W | W ∈ S.opens ∧ W ≤ V} →
        U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V} →
      HasGluingForHomsAt S (U ⊓ V))
    (hhomP : ∀ (U V : Opens X.carrier), U ∈ S.opens →
        V = sSup {W | W ∈ S.opens ∧ W ≤ V} →
        U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V} →
      ∀ W ∈ S.opens, W ≤ U ⊔ V →
        HasGluingForHomsAt (S.subcollection (opensBelowPair S U V)
          (opensBelowPair_subset S U V)) W)
    (s : Finset (Opens X.carrier)) (hs : s.Nonempty) (hmem : ∀ U ∈ s, U ∈ S.opens)
    (hcover : s.sup id = ⊤)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i)) :
    Nonempty (Solution S) :=
  exists_solution_of_finite_cover S
    (gluesAlongTwoOpens_of_hasGluingForHomsAt_pairs S hhomS hhomP
      (gluesObjectsAlongTwoOpens S))
    s hs hmem hcover hinter hExt

/-! ### The narrowed hypotheses are weaker than the pair-subsystem ones -/

/-- **The narrowed hypotheses follow from the pair-subsystem form.**  For the system, the open
`U ⊓ V` is a union of members by the hypothesis `hUV` that the pair carries; for the subsystem, a
member of the collection below `U ⊔ V` is a union of members of the subsystem by
`Stacks.DerivedGlueing.mem_eq_sSup_opensBelowPair`, and the subsystem inherits the covering
condition on intersections by `Stacks.DerivedGlueing.inf_eq_sSup_opensBelowPair`.

So every statement above that carries the narrowed hypotheses is a strengthening of its partner
in `StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.HomGlueingAtThePairSubsystems`,
which is in turn a strengthening of the `∀ 𝒟 ⊆ S.opens` form by
`Stacks.DerivedGlueing.hasGluingForHomsOver_pairs_of_subcollections`. -/
theorem hasGluingForHomsAt_pairs_of_hasGluingForHomsOver_pairs (S : LocallyGiven X)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hhomS : HasGluingForHomsOver S)
    (hhomP : ∀ (U V : Opens X.carrier), U ∈ S.opens →
        V = sSup {W | W ∈ S.opens ∧ W ≤ V} →
        U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V} →
      HasGluingForHomsOver
        (S.subcollection (opensBelowPair S U V) (opensBelowPair_subset S U V))) :
    (∀ (U V : Opens X.carrier), U ∈ S.opens →
        V = sSup {W | W ∈ S.opens ∧ W ≤ V} →
        U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V} →
      HasGluingForHomsAt S (U ⊓ V)) ∧
    (∀ (U V : Opens X.carrier), U ∈ S.opens →
        V = sSup {W | W ∈ S.opens ∧ W ≤ V} →
        U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V} →
      ∀ W ∈ S.opens, W ≤ U ⊔ V →
        HasGluingForHomsAt (S.subcollection (opensBelowPair S U V)
          (opensBelowPair_subset S U V)) W) :=
  ⟨fun _U _V _hU _hV hUV => hhomS _ hUV hinter,
    fun U V hU hV hUV W hW hWP => hhomP U V hU hV hUV W
      (mem_eq_sSup_opensBelowPair S U V hU hV hinter W hW hWP)
      (inf_eq_sSup_opensBelowPair S U V hinter)⟩

/-! ### Both narrowed hypotheses, discharged -/

/-- **The glueing of morphisms for the system over `U ⊓ V`, when that open is a member.**  A
collection closed under meeting a member with a union of members satisfies the first narrowed
hypothesis outright, by `Stacks.DerivedGlueing.hasGluingForHomsAt_of_mem`: over a member there is
nothing to glue. -/
theorem hasGluingForHomsAt_inf_pairs_of_inf_mem (S : LocallyGiven X)
    (hmeet : ∀ U ∈ S.opens, ∀ V : Opens X.carrier,
      V = sSup {W | W ∈ S.opens ∧ W ≤ V} → U ⊓ V ∈ S.opens) :
    ∀ (U V : Opens X.carrier), U ∈ S.opens →
        V = sSup {W | W ∈ S.opens ∧ W ≤ V} →
        U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V} →
      HasGluingForHomsAt S (U ⊓ V) :=
  fun U V hU hV _ => hasGluingForHomsAt_of_mem S (hmeet U hU V hV)

/-- **The glueing of morphisms for the pair subsystem over the members below `U ⊔ V`, when those
members lie below one of the two opens.**  Such a member belongs to
`Stacks.DerivedGlueing.opensBelowPair`, so again there is nothing to glue.

The hypothesis is exactly `hsplit` of
`Stacks.DerivedGlueing.hasGluingForHomsOver_opensBelowPair_of_covered_mem`, restricted to the
pairs the two-open case is applied at; unlike that statement it needs no saturation of the
ambient collection, and so does not force `⊤` into it. -/
theorem hasGluingForHomsAt_opensBelowPair_of_split (S : LocallyGiven X)
    (hsplit : ∀ U ∈ S.opens, ∀ V : Opens X.carrier,
      V = sSup {W | W ∈ S.opens ∧ W ≤ V} →
      ∀ W ∈ S.opens, W ≤ U ⊔ V → W ≤ U ∨ W ≤ V) :
    ∀ (U V : Opens X.carrier), U ∈ S.opens →
        V = sSup {W | W ∈ S.opens ∧ W ≤ V} →
        U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V} →
      ∀ W ∈ S.opens, W ≤ U ⊔ V →
        HasGluingForHomsAt (S.subcollection (opensBelowPair S U V)
          (opensBelowPair_subset S U V)) W :=
  fun U V hU hV _ W hW hWP => hasGluingForHomsAt_of_mem _ ⟨hW, hsplit U hU V hV W hW hWP⟩

/-! ### Every binder at once -/

/-- **Situation [Stacks, Tag 0D67] on `Spec (ℤ × ℤ)`, over a covering collection that omits
`⊤`.**  The object prescribed on a member is the restriction to it of a sheaf of modules placed
in degree zero, which is what makes the negative self-Ext hypothesis hold for every member at
once. -/
def idempotentPairSystem
    (F : SheafOfModules.{u} (restrictedRingSheaf specULiftProdRingedSpace.{u} ⊤)) :
    LocallyGiven specULiftProdRingedSpace.{u} :=
  locallyGivenOfGlobal specULiftProdRingedSpace.{u} idempotentPairCollection.{u}
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (restrictedRingSheaf specULiftProdRingedSpace.{u} ⊤)) 0).obj F)

/-- The collection of opens of `idempotentPairSystem F` is `idempotentPairCollection`. -/
theorem idempotentPairSystem_opens
    (F : SheafOfModules.{u} (restrictedRingSheaf specULiftProdRingedSpace.{u} ⊤)) :
    (idempotentPairSystem.{u} F).opens = idempotentPairCollection.{u} :=
  locallyGivenOfGlobal_opens _ _ _

/-- The collection of the system covers the space. -/
theorem sSup_idempotentPairSystem_opens
    (F : SheafOfModules.{u} (restrictedRingSheaf specULiftProdRingedSpace.{u} ⊤)) :
    sSup (idempotentPairSystem.{u} F).opens = ⊤ :=
  (congrArg sSup (idempotentPairSystem_opens.{u} F)).trans sSup_idempotentPairCollection.{u}

/-- `⊤` is not a member of the collection of the system. -/
theorem top_notMem_idempotentPairSystem_opens
    (F : SheafOfModules.{u} (restrictedRingSheaf specULiftProdRingedSpace.{u} ⊤)) :
    (⊤ : Opens (specULiftProdRingedSpace.{u}).carrier) ∉ (idempotentPairSystem.{u} F).opens :=
  (idempotentPairSystem_opens.{u} F).symm ▸ top_notMem_idempotentPairCollection.{u}

/-- **Every binder of `Stacks.DerivedGlueing.exists_solution_of_finite_cover_of_homs_at`
instantiated at once, with nothing assumed.**

The carrier is `Spec (ℤ × ℤ)`, the collection is `{⊥, D(e), D(1 - e)}`, and the prescribed
objects are the restrictions of an arbitrary sheaf of modules `F` placed in degree zero.  Both
narrowed glueing hypotheses are discharged —
`Stacks.DerivedGlueing.inf_mem_idempotentPairCollection` and
`Stacks.DerivedGlueing.split_idempotentPairCollection` — as are the finite cover, the covering
condition on intersections and the negative self-Ext hypothesis.

Unlike `Stacks.DerivedGlueing.nonempty_solution_botTop_single`, the collection does **not**
contain `⊤` (`Stacks.DerivedGlueing.top_notMem_idempotentPairSystem_opens`) while still covering
the space (`Stacks.DerivedGlueing.sSup_idempotentPairSystem_opens`), so
`Stacks.DerivedGlueing.exists_solution_of_top_mem` does not prove the conclusion, and the finite
cover really has two members.

It remains degenerate in one respect, and the honest statement of it is this: the system is
`Stacks.DerivedGlueing.locallyGivenOfGlobal`, so its objects are the restrictions of one global
object and `Stacks.DerivedGlueing.solutionOverOfGlobal` already supplies a solution.  This
development carries no system whose prescribed objects are not globally given, so no witness in
it can avoid that. -/
theorem nonempty_solution_idempotentPair
    (F : SheafOfModules.{u} (restrictedRingSheaf specULiftProdRingedSpace.{u} ⊤)) :
    Nonempty (Solution (idempotentPairSystem.{u} F)) := by
  classical
  have hopens : (idempotentPairSystem.{u} F).opens = idempotentPairCollection.{u} :=
    idempotentPairSystem_opens.{u} F
  refine exists_solution_of_finite_cover_of_homs_at (idempotentPairSystem.{u} F)
    (hasGluingForHomsAt_inf_pairs_of_inf_mem _ ?_)
    (hasGluingForHomsAt_opensBelowPair_of_split _ ?_)
    ({idempotentOpen.{u} ⟨(1, 0)⟩, idempotentOpen.{u} ⟨(0, 1)⟩} : Finset _)
    ⟨idempotentOpen.{u} ⟨(1, 0)⟩, Finset.mem_insert_self _ _⟩ ?_ ?_ ?_
    (subsingleton_shiftedHom_locallyGivenOfGlobal_single specULiftProdRingedSpace.{u}
      idempotentPairCollection.{u} F)
  · intro U hU V hV
    rw [hopens] at hU hV ⊢
    exact inf_mem_idempotentPairCollection hU hV
  · intro U hU V hV W hW hWUV
    rw [hopens] at hU hV hW
    exact split_idempotentPairCollection hU hV hW hWUV
  · intro U hU
    rw [hopens]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hU
    rcases hU with rfl | rfl
    · simp [idempotentPairCollection]
    · simp [idempotentPairCollection]
  · rw [Finset.sup_insert, Finset.sup_singleton]
    exact sup_idempotentOpen_eq_top.{u}
  · intro A hA B hB
    rw [hopens] at hA hB ⊢
    exact inter_eq_sSup_idempotentPairCollection A hA B hB

end Narrowed

end Stacks.DerivedGlueing

end
