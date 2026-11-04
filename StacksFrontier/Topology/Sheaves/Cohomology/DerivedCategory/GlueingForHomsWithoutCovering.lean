module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.HomVanishingOverASubcollection
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingAtTopUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingOverACoveringCollection
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.FiniteCoverUniquenessUnconditional

/-!
# The glueing of morphisms needs no covering collection, and Tag 0D6A follows

Let `(X, 𝒪_X)` be a ringed space and let `S` be a system of locally given derived objects on it,
as in Situation [Stacks, Tag 0D67].  The sheaf condition of [Stacks, Tag 0D66] part (2) at an
open `O` which is the union of the members of the collection contained in it is carried by
`Stacks.DerivedGlueing.hasGluingForHomsAt_of_sSup_covered`, and that statement takes a hypothesis
`sSup S.opens = ⊤`: the collection covers the whole space.  **It does not need it.**  The
hypothesis is used in exactly one place, the branch `O = ⊤` of
`Stacks.DerivedGlueing.gluesHomsAt_of_sSup_covered_of_vanishing`, and in that branch the
hypothesis `hO` already says it: `⊤ = sSup {W | W ∈ S.opens ∧ W ≤ ⊤}` gives `sSup S.opens = ⊤`
because every member of the collection is below `⊤`.  This file re-runs the argument without the
hypothesis.

The consequence is not local.  `Stacks.DerivedGlueing.HasGluingForHomsOver` quantifies over the
open and binds both covering hypotheses on the collection itself, so once the covering of the
whole space is gone the glueing of morphisms holds for **every** system, with no hypotheses at
all; in particular it holds for every subcollection of a system, which is the shape
`Stacks.DerivedGlueing.exists_solution_of_finite_cover_of_homs` grants as its last remaining
input.  The existence half of [Stacks, Tag 0D6A] is therefore unconditional, on the source's own
hypotheses, and so is the two-open case `Stacks.DerivedGlueing.GluesAlongTwoOpens` out of which
the source's induction is built.

The two-open case is also the successor step of the transfinite induction proving
[Stacks, Tag 0D6C]; see
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.BBDGlueing`.  Over a quasi-compact space
finitely many members already cover, and the statement follows from Tag 0D6A directly.

## Main results

* `Stacks.DerivedGlueing.hasGluingForHomsAt_of_covers`: the sheaf condition of
  [Stacks, Tag 0D66] part (2) at every open the collection covers, with no hypothesis that the
  collection covers the space and nothing granted.
* `Stacks.DerivedGlueing.hasGluingForHomsOver_of_covers`:
  `Stacks.DerivedGlueing.HasGluingForHomsOver S` for every system `S`, with no hypotheses.
* `Stacks.DerivedGlueing.gluesAlongTwoOpens_unconditional`: the two-open case of
  [Stacks, Tag 0D6A], with no hypotheses.
* `Stacks.DerivedGlueing.exists_solution_of_finite_cover_unconditional`: **[Stacks, Tag 0D6A],
  existence, on the source's own hypotheses and with nothing granted.**
* `Stacks.DerivedGlueing.exists_solution_and_unique_solutionIso_of_finite_cover_unconditional`:
  **both halves of [Stacks, Tag 0D6A] in one statement**, existence and uniqueness up to unique
  isomorphism, on the source's own hypotheses and with nothing granted.
* `Stacks.DerivedGlueing.exists_solution_and_unique_solutionIso_of_covers_of_compactSpace_unconditional`:
  existence and uniqueness of a solution over a quasi-compact space, by way of Tag 0D6A.

## References

* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 0D6A](https://stacks.math.columbia.edu/tag/0D6A)
* [Stacks Project, Tag 0D6C](https://stacks.math.columbia.edu/tag/0D6C)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ExtensionByZeroModules
open Stacks.SheafOfModules (ringedSite)

namespace Stacks.DerivedGlueing

universe u

variable {X : RingedSpace.{u, u}}

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The covering of the whole space is not needed -/

/-- **The collection covers the whole space as soon as it covers `⊤`.** The hypothesis
`hO : ⊤ = sSup {W | W ∈ S.opens ∧ W ≤ ⊤}` of the statements below already says
`sSup S.opens = ⊤`, every member of the collection being below `⊤`. -/
theorem sSup_opens_eq_top_of_sSup_covered_top (S : LocallyGiven X)
    (hO : (⊤ : Opens X.carrier) = sSup {W | W ∈ S.opens ∧ W ≤ (⊤ : Opens X.carrier)}) :
    sSup S.opens = ⊤ :=
  top_le_iff.mp (hO.le.trans (sSup_le fun _ hW => le_sSup hW.1))

/-! ### Tag 0D6A, both halves, with nothing granted -/

/-- **The two-open case of [Stacks, Tag 0D6A], with nothing granted.**
`Stacks.DerivedGlueing.gluesAlongTwoOpens_of_hasGluingForHomsOver` grants the sheaf condition of
[Stacks, Tag 0D66] part (2) for every subsystem; each of those is an instance of
`Stacks.DerivedGlueing.hasGluingForHomsOver_of_covers`, whose statement has no hypotheses, so
the subsystems need no covering condition of their own — which is what blocked this discharge
while the covering of the whole space was still assumed. -/
theorem gluesAlongTwoOpens_unconditional (S : LocallyGiven X) : GluesAlongTwoOpens S :=
  gluesAlongTwoOpens_of_hasGluingForHomsOver S
    fun 𝒟 h𝒟 => Stacks.DerivedGlueing.hasGluingForHomsOver_of_covers (S.subcollection 𝒟 h𝒟)

/-- **[Stacks, Tag 0D6A], existence.**
In Situation 0D67, suppose that `X = U_1 ∪ … ∪ U_n` with the `U_i` in the displayed collection,
that the intersection of two members of the collection is the union of the members contained in
it, and that the prescribed objects have no negative self-`Ext`.  Then the system has a solution.

The proof applies `Stacks.DerivedGlueing.exists_solution_of_finite_cover_of_homs`; the sheaf
condition of [Stacks, Tag 0D66] part (2) for every subsystem is
`Stacks.DerivedGlueing.hasGluingForHomsOver_of_covers`, a theorem with no binder beyond the
system.  The nonemptiness `hs` of the cover is
used here: the induction of `Stacks.DerivedGlueing.exists_solutionOver_finsetSup` runs on
`Finset.Nonempty.cons_induction` and starts from a single member. -/
@[stacks 0D6A "existence: for X = U_1 ∪ … ∪ U_n with U_i in the collection, intersections of
  members covered by members, and no negative self-Ext of the prescribed objects, the system has
  a solution"]
theorem exists_solution_of_finite_cover_unconditional (S : LocallyGiven X)
    (s : Finset (Opens X.carrier)) (hs : s.Nonempty) (hmem : ∀ U ∈ s, U ∈ S.opens)
    (hcover : s.sup id = ⊤)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i)) :
    Nonempty (Solution S) :=
  exists_solution_of_finite_cover_of_homs S
    (fun 𝒟 h𝒟 => Stacks.DerivedGlueing.hasGluingForHomsOver_of_covers (S.subcollection 𝒟 h𝒟)) s hs
    hmem hcover hinter hExt

/-- **[Stacks, Tag 0D6A] in full**: under the conditions (1), (2) and (3) of the tag the
system has a solution, and any two solutions are identified by exactly one isomorphism of
solutions.

Both clauses of the tag in one statement, the existence clause above together with the
uniqueness clause of [Stacks, Tag 0D68] over the finite cover.  The conclusion
`Stacks.DerivedGlueing.Solution.IsCompatibleHom A B ψ.hom` is by definition
`∀ (U : Opens X.carrier) (hU : U ∈ S.opens), (S.restriction U ⊤ le_top).map ψ.hom ≫
(B.rho U hU).hom = (A.rho U hU).hom`, which is "compatible with the `ρ_U`" as the source means
it. -/
@[stacks 0D6A "the whole tag: for X = U_1 ∪ … ∪ U_n with U_i in the collection, intersections
  of members covered by members, and no negative self-Ext of the prescribed objects, a solution
  exists and is unique up to unique isomorphism"]
theorem exists_solution_and_unique_solutionIso_of_finite_cover_unconditional (S : LocallyGiven X)
    (s : Finset (Opens X.carrier)) (hs : s.Nonempty) (hmem : ∀ U ∈ s, U ∈ S.opens)
    (hcover : s.sup id = ⊤)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i)) :
    Nonempty (Solution S) ∧
      ∀ A B : Solution S, ∃! ψ : A.obj ≅ B.obj, A.IsCompatibleHom B ψ.hom :=
  ⟨exists_solution_of_finite_cover_unconditional S s hs hmem hcover hinter hExt,
    fun A B =>
      exists_unique_solutionIso_of_finite_cover_unconditional S s hs hmem hcover hinter hExt A B⟩

/-! ### A quasi-compact space -/

/-- **Existence of a solution over a quasi-compact space.**
`Stacks.DerivedGlueing.exists_solution_of_covers_of_compactSpace` with its hypothesis
`Stacks.DerivedGlueing.GluesAlongTwoOpens` discharged.  No glueing along a chain is needed: a
quasi-compact space is already covered by finitely many members, so the statement reduces to
[Stacks, Tag 0D6A]. -/
theorem exists_solution_of_covers_of_compactSpace_unconditional (S : LocallyGiven X)
    [CompactSpace X.carrier] (hcover : sSup S.opens = ⊤)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i)) :
    Nonempty (Solution S) :=
  exists_solution_of_covers_of_compactSpace S (gluesAlongTwoOpens_unconditional S) hcover hinter
    hExt

/-- **Existence and uniqueness of a solution over a quasi-compact space**: if the displayed
collection covers a quasi-compact `X`, if the intersection of two members is the union of the
members contained in it, and if the prescribed objects have no negative self-`Ext`, then the
system has a solution and any two solutions are identified by exactly one isomorphism of
solutions.  The case of [Stacks, Tag 0D6C] that the source deduces from [Stacks, Tag 0D6A];
the general case is
`Stacks.DerivedGlueing.exists_solution_and_unique_solutionIso_of_covers_unconditional`. -/
theorem exists_solution_and_unique_solutionIso_of_covers_of_compactSpace_unconditional
    (S : LocallyGiven X) [CompactSpace X.carrier] (hcover : sSup S.opens = ⊤)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i)) :
    Nonempty (Solution S) ∧
      ∀ A B : Solution S, ∃! ψ : A.obj ≅ B.obj, A.IsCompatibleHom B ψ.hom :=
  ⟨exists_solution_of_covers_of_compactSpace_unconditional S hcover hinter hExt,
    fun A B => exists_unique_solutionIso_of_covers_unconditional S hcover hinter hExt A B⟩

end Stacks.DerivedGlueing

end
