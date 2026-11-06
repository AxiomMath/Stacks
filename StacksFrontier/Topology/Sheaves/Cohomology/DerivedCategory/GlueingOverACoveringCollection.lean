module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingOverAWellOrderedCover

/-!
# Glueing locally given derived objects over a covering collection of opens, by Zorn's lemma

Let `(X, 𝒪_X)` be a ringed space and let `(ℬ, K_U, ρ^U_V)` be a system of locally given derived
objects on it, as in Situation 0D67, such that for `U, V ∈ ℬ` the intersection `U ∩ V` is the
union of the members of `ℬ` contained in it and `Ext^i(K_U, K_U) = 0` for `i < 0` and `U ∈ ℬ`.
Call an open subset of `X` *solved* when it is the union of the members of `ℬ` contained in it
and carries a solution of the system over it.  The empty open is solved; adjoining one member of
`ℬ` to a solved open gives a solved open when the two-open case
`Stacks.DerivedGlueing.GluesAlongTwoOpens` holds; and the union of a chain of solved opens is
solved when glueing along a chain `Stacks.DerivedGlueing.GluesAlongChain` holds.  Zorn's lemma
then produces a maximal solved open, and `X = ⋃_{U ∈ ℬ} U` forces it to be `X`.

Both properties hold for every system: `Stacks.DerivedGlueing.gluesAlongTwoOpens_unconditional`
and `Stacks.DerivedGlueing.gluesAlongChain_unconditional`.  [Stacks, Tag 0D6C] itself is
`Stacks.DerivedGlueing.exists_solution_and_unique_solutionIso_of_covers_unconditional`, in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.BBDGlueing`.

## Main definitions

* `Stacks.DerivedGlueing.GluesAlongChain`: glueing along a chain of opens.
* `Stacks.DerivedGlueing.solvedOpens`: the opens that are unions of members of `ℬ` and carry a
  solution of the system over them.

## Main results

* `Stacks.DerivedGlueing.bot_eq_sSup_covered`, `Stacks.DerivedGlueing.sup_eq_sSup_covered`,
  `Stacks.DerivedGlueing.sSup_eq_sSup_covered`: the opens that are unions of members of `ℬ` are
  stable under the empty open, under adjoining a member of `ℬ`, and under arbitrary unions.
* `Stacks.DerivedGlueing.inf_eq_sSup_covered`: the covering condition on intersections extends
  from a pair of members of `ℬ` to a member and an open that is a union of members.
* `Stacks.DerivedGlueing.solutionOverBot`: the empty open carries a solution of the system.
* `Stacks.DerivedGlueing.exists_solution_of_covers_of_compactSpace`: existence of a solution over
  a quasi-compact space from the two-open case, where finitely many members cover.
* `Stacks.DerivedGlueing.exists_upperBound_solvedOpens`,
  `Stacks.DerivedGlueing.exists_solutionOver_top`: the hypothesis of Zorn's lemma for
  `Stacks.DerivedGlueing.solvedOpens`, and the conclusion that `⊤` is solved.
* `Stacks.DerivedGlueing.exists_solution_of_covers`,
  `Stacks.DerivedGlueing.exists_glueing_of_covers`: existence of a solution from the two-open
  case and glueing along a chain.

## References

* [Stacks Project, Tag 0D6C](https://stacks.math.columbia.edu/tag/0D6C)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 0D6A](https://stacks.math.columbia.edu/tag/0D6A)
* [Stacks Project, Tag 0D6B](https://stacks.math.columbia.edu/tag/0D6B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Stacks.DerivedGlueing

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-! ### Opens that are unions of members of the collection -/

/-- An open contained in the union of the members of the collection it contains is that union. -/
private theorem eq_sSup_covered_of_le_sSup {S : LocallyGiven X} {O : Opens X.carrier}
    (h : O ≤ sSup {W | W ∈ S.opens ∧ W ≤ O}) : O = sSup {W | W ∈ S.opens ∧ W ≤ O} :=
  le_antisymm h (sSup_le fun _ hW => hW.2)

/-- The members of the collection contained in a smaller open have a smaller union. -/
private theorem sSup_covered_mono {S : LocallyGiven X} {O O' : Opens X.carrier} (h : O ≤ O') :
    sSup {W | W ∈ S.opens ∧ W ≤ O} ≤ sSup {W | W ∈ S.opens ∧ W ≤ O'} :=
  sSup_le_sSup fun _ hW => ⟨hW.1, hW.2.trans h⟩

/-- The empty open is the union of the members of the collection contained in it. -/
theorem bot_eq_sSup_covered (S : LocallyGiven X) :
    (⊥ : Opens X.carrier) = sSup {W | W ∈ S.opens ∧ W ≤ ⊥} :=
  eq_sSup_covered_of_le_sSup bot_le

/-- A union of opens, each the union of the members of the collection it contains, is again the
union of the members of the collection it contains. -/
theorem sSup_eq_sSup_covered (S : LocallyGiven X) (𝒞 : Set (Opens X.carrier))
    (h𝒞 : ∀ O ∈ 𝒞, O = sSup {W | W ∈ S.opens ∧ W ≤ O}) :
    sSup 𝒞 = sSup {W | W ∈ S.opens ∧ W ≤ sSup 𝒞} := by
  refine eq_sSup_covered_of_le_sSup (sSup_le fun O hO => ?_)
  exact (h𝒞 O hO).trans_le (sSup_covered_mono (le_sSup hO))

/-- Adjoining a member of the collection to an open that is the union of the members it contains
gives an open with the same property. -/
theorem sup_eq_sSup_covered (S : LocallyGiven X) {U O : Opens X.carrier} (hU : U ∈ S.opens)
    (hO : O = sSup {W | W ∈ S.opens ∧ W ≤ O}) :
    U ⊔ O = sSup {W | W ∈ S.opens ∧ W ≤ U ⊔ O} := by
  refine eq_sSup_covered_of_le_sSup (sup_le (le_sSup ⟨hU, le_sup_left⟩) ?_)
  exact hO.trans_le (sSup_covered_mono le_sup_right)

/-- **The covering condition on intersections passes to a union of members.** If the intersection
of two members of the collection is the union of the members contained in it, then so is the
intersection of a member with any open that is a union of members. -/
theorem inf_eq_sSup_covered (S : LocallyGiven X)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    {U O : Opens X.carrier} (hU : U ∈ S.opens)
    (hO : O = sSup {W | W ∈ S.opens ∧ W ≤ O}) :
    U ⊓ O = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ O} := by
  refine eq_sSup_covered_of_le_sSup fun x hx => ?_
  obtain ⟨hxU, hxO⟩ := hx
  rw [hO] at hxO
  obtain ⟨V, hV, hxV⟩ := Opens.mem_sSup.mp hxO
  have hxUV : x ∈ U ⊓ V := ⟨hxU, hxV⟩
  rw [hinter U hU V hV.1] at hxUV
  obtain ⟨W, hW, hxW⟩ := Opens.mem_sSup.mp hxUV
  exact sSup_covered_mono (inf_le_inf_left U hV.2) (Opens.mem_sSup.mpr ⟨W, hW, hxW⟩)

/-! ### The solution over the empty open -/

/-- **The empty open carries a solution.** The only member of the collection contained in the
empty open is the empty open itself, when it belongs to the collection; there the prescribed
object is a solution, and otherwise any object of the derived category is. -/
def solutionOverBot (S : LocallyGiven X) : SolutionOver S ⊥ := by
  by_cases h : (⊥ : Opens X.carrier) ∈ S.opens
  · exact selfSolutionOver S ⊥ h
  · have hnone : ∀ V : Opens X.carrier, V ∈ S.opens → V ≤ ⊥ → False :=
      fun V hV hVb => h (le_bot_iff.mp hVb ▸ hV)
    exact
      { obj := (Limits.HasZeroObject.zero (C := OpenDerivedCategory X ⊥)).choose
        rho := fun V hV hVb => (hnone V hV hVb).elim
        compatibility := fun V _ _ hV _ hVb => (hnone V hV hVb).elim }

/-! ### The quasi-compact case -/

/-- **Existence of a solution over a quasi-compact space, from the two-open case.** If `X` is
quasi-compact then finitely many members of the collection already cover it, so the induction of
[Stacks, Tag 0D6A] on the number of members applies and no glueing along a chain is needed. -/
theorem exists_solution_of_covers_of_compactSpace (S : LocallyGiven X)
    [CompactSpace X.carrier] (hglue : GluesAlongTwoOpens S) (hcover : sSup S.opens = ⊤)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i)) :
    Nonempty (Solution S) := by
  have hcompact : IsCompactElement (⊤ : Opens X.carrier) :=
    (Opens.isCompactElement_iff ⊤).mpr (by simpa using isCompact_univ)
  obtain ⟨t, hts, htsup⟩ :=
    (isCompactElement_iff_exists_le_sSup_of_le_sSup _).mp hcompact S.opens
      (le_of_eq hcover.symm)
  rcases t.eq_empty_or_nonempty with rfl | ht
  · have hbot : (⊥ : Opens X.carrier) = ⊤ := by simpa using top_le_iff.mp htsup
    exact ⟨(hbot ▸ solutionOverBot S).toSolution⟩
  · exact exists_solution_of_finite_cover S hglue t ht
      (fun U hU => hts (Finset.mem_coe.mpr hU)) (top_le_iff.mp htsup) hinter hExt

/-! ### Glueing along a chain -/

/-- **Glueing along a chain of opens.** Let `𝒞` be a nonempty collection of opens, totally
ordered by inclusion, each of them the union of the members of `ℬ` contained in it and each
carrying a solution of the system over it.  Then the union of `𝒞` carries a solution.

It holds for every system, by `Stacks.DerivedGlueing.gluesAlongChain_unconditional`. -/
def GluesAlongChain (S : LocallyGiven X) : Prop :=
  ∀ 𝒞 : Set (Opens X.carrier), 𝒞.Nonempty →
    (∀ O ∈ 𝒞, ∀ O' ∈ 𝒞, O ≤ O' ∨ O' ≤ O) →
    (∀ O ∈ 𝒞, O = sSup {W | W ∈ S.opens ∧ W ≤ O}) →
    (∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V}) →
    (∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i)) →
    (∀ O ∈ 𝒞, Nonempty (SolutionOver S O)) →
    Nonempty (SolutionOver S (sSup 𝒞))

/-! ### Existence of a solution, by Zorn's lemma -/

/-- **The opens over which the system is solved.** The open subsets of `X` that are unions of the
members of the collection they contain and carry a solution of the system over them. -/
def solvedOpens (S : LocallyGiven X) : Set (Opens X.carrier) :=
  {O | O = sSup {W | W ∈ S.opens ∧ W ≤ O} ∧ Nonempty (SolutionOver S O)}

/-- **The union of a chain of opens over which the system is solved is one**, from glueing
along a chain; the empty chain is covered by `Stacks.DerivedGlueing.solutionOverBot`. -/
theorem exists_upperBound_solvedOpens (S : LocallyGiven X) (hchain : GluesAlongChain S)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i))
    (c : Set (Opens X.carrier)) (hcP : c ⊆ solvedOpens S) (hc : IsChain (· ≤ ·) c) :
    ∃ ub ∈ solvedOpens S, ∀ z ∈ c, z ≤ ub := by
  rcases c.eq_empty_or_nonempty with rfl | hne
  · exact ⟨⊥, ⟨bot_eq_sSup_covered S, ⟨solutionOverBot S⟩⟩, fun _ hz => hz.elim⟩
  · refine ⟨sSup c, ⟨sSup_eq_sSup_covered S c fun O hO => (hcP hO).1, ?_⟩,
      fun _ hz => le_sSup hz⟩
    refine hchain c hne (fun O hO O' hO' => ?_) (fun O hO => (hcP hO).1) hinter hExt
      fun O hO => (hcP hO).2
    rcases eq_or_ne O O' with rfl | hne'
    · exact Or.inl le_rfl
    · exact hc hO hO' hne'

/-- **A maximal open over which the system is solved is the whole space.** From glueing along a
chain and glueing a member of the collection onto a solution, Zorn's lemma gives a maximal open
over which the system is solved, and `X = ⋃_{U ∈ ℬ} U` forces it to be `⊤`. -/
theorem exists_solutionOver_top (S : LocallyGiven X) (hglue : GluesAlongTwoOpens S)
    (hchain : GluesAlongChain S) (hcover : sSup S.opens = ⊤)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i)) :
    Nonempty (SolutionOver S ⊤) := by
  obtain ⟨M, hM⟩ := zorn_le₀ (solvedOpens S)
    fun c hcP hc => exists_upperBound_solvedOpens S hchain hinter hExt c hcP hc
  obtain ⟨hMsup, hMsol⟩ := hM.1
  have hMtop : M = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← hcover]
    refine sSup_le fun U hU => ?_
    by_contra hUM
    have hmem : U ⊔ M ∈ solvedOpens S :=
      ⟨sup_eq_sSup_covered S hU hMsup,
        hglue U hU M hMsup (inf_eq_sSup_covered S hinter hU hMsup) hinter hExt
          (selfSolutionOver S U hU) hMsol.some⟩
    exact hUM (le_sup_left.trans (hM.2 hmem le_sup_right))
  exact hMtop ▸ hMsol

/-- **Existence of a solution from glueing along a chain and the two-open case.** In Situation
0D67, assume the two-open case and glueing along a chain, that the members of the collection cover
`X`, that the intersection of two members is the union of the members contained in it, and that
the prescribed objects have no negative self-Ext.  Then the system has a solution: an object `K`
of `D(𝒪_X)` together with isomorphisms `K|_U ≅ K_U` for `U` in the collection, compatible with
the prescribed transitions. -/
theorem exists_solution_of_covers (S : LocallyGiven X) (hglue : GluesAlongTwoOpens S)
    (hchain : GluesAlongChain S) (hcover : sSup S.opens = ⊤)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i)) :
    Nonempty (Solution S) :=
  ⟨(exists_solutionOver_top S hglue hchain hcover hinter hExt).some.toSolution⟩

/-- **Existence of a solution, with the glued object displayed.** The content of
`Stacks.DerivedGlueing.exists_solution_of_covers`, with the object `K` of `D(𝒪_X)`, the
isomorphisms `ρ_U : K|_U ≅ K_U` and the compatibility `ρ^U_V ∘ ρ_U|_V = ρ_V` spelled out. -/
theorem exists_glueing_of_covers (S : LocallyGiven X) (hglue : GluesAlongTwoOpens S)
    (hchain : GluesAlongChain S) (hcover : sSup S.opens = ⊤)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i)) :
    ∃ (K : OpenDerivedCategory X ⊤)
      (rho : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens),
        (S.restriction U ⊤ le_top).obj K ≅ S.obj U hU),
      ∀ (V U : Opens X.carrier) (hVU : V ≤ U) (hU : U ∈ S.opens) (hV : V ∈ S.opens),
        (S.restrictionComp V U ⊤ hVU le_top).hom.app K ≫
            (S.restriction V U hVU).map (rho U hU).hom ≫ (S.rho V U hVU hU hV).hom =
          (rho V hV).hom := by
  obtain ⟨A⟩ := exists_solution_of_covers S hglue hchain hcover hinter hExt
  exact ⟨A.obj, A.rho, A.compatibility⟩

end Stacks.DerivedGlueing

end
