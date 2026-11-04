module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.DescentDatumOfLocallyGivenObjects
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.LocallyGivenOfGlobalObject
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.LocallyGivenNonVacuity

/-!
# Inputs for the two-open case of the glueing problem

Let `(X, 𝒪_X)` be a ringed space and `(ℬ, K_U, ρ^U_V)` a system of locally given derived objects
on it, as in Situation 0D67.  The induction of [Stacks, Tag 0D6A] rests on the case of a cover
by two opens, which this development carries as the hypothesis
`Stacks.DerivedGlueing.GluesAlongTwoOpens`: a solution over a member `U` of `ℬ` and a solution
over an open `V` that is the union of the members contained in it glue to a solution over
`U ∪ V`.

This file collects what that hypothesis needs and does **not** itself discharge it.  Three
things are supplied.

*The combinatorics of the two opens.*  Write `ℬ'` for the members of `ℬ` contained in `U` or in
`V`.  Then `U ∪ V` is the union of the members of `ℬ'`, every member of `ℬ` contained in
`U ∪ V` is the union of the members of `ℬ'` contained in it, and `ℬ'` again has the property
that the intersection of two of its members is the union of the members of `ℬ'` contained in it.
That is what makes the identification of a glued object over such a member a *glueing problem
for morphisms over `ℬ'`*, where every open in sight lies below `U` or below `V` and the two
given solutions apply directly.

*The subsystem on a subcollection.*  Shrinking the collection of a system of locally given
derived objects leaves a system, with the same restriction functors and comparisons; a solution
over an open for the big system is one for the subsystem, and the prescribed object on a member
of the big collection is a solution over that member for the subsystem.

*A system for which the two-open case holds outright.*  For a system prescribed by a single
global object the conclusion is immediate: that object restricts to a solution over *every*
open, in particular over `U ∪ V`.  So `Stacks.DerivedGlueing.GluesAlongTwoOpens` is satisfiable,
and satisfiable by a system whose collection does **not** contain `⊤`, which is the degenerate
case in which the glueing statements of Tags 0D6A to 0D6C are already unconditional
(`Stacks.DerivedGlueing.exists_solution_of_top_mem`).

## Main definitions

* `Stacks.DerivedGlueing.opensBelowPair`: the members of the collection contained in one of two
  given opens.
* `Stacks.DerivedGlueing.LocallyGiven.subcollection`: the subsystem carried by a subcollection.
* `Stacks.DerivedGlueing.solutionOverOfGlobal`: the solution over an arbitrary open of the
  system prescribed by a global object.

## Main results

* `Stacks.DerivedGlueing.sup_eq_sSup_opensBelowPair`, and
  `Stacks.DerivedGlueing.mem_eq_sSup_opensBelowPair`: the union of the two opens, and every
  member of the collection below it, are unions of members lying below one of the two.
* `Stacks.DerivedGlueing.inf_eq_sSup_opensBelowPair`: the covering condition on intersections is
  inherited by that subcollection.
* `Stacks.DerivedGlueing.gluesAlongTwoOpens_locallyGivenOfGlobal`: the two-open case holds for a
  system prescribed by a global object, with nothing assumed.
* `Stacks.DerivedGlueing.nonempty_solutionOver_sup_opensLE`: the same with *every* binder of the
  two-open case discharged from closed terms, at a collection that contains `⊤` only in the
  degenerate case — the non-degeneracy certificate for that hypothesis.
* `Stacks.DerivedGlueing.inf_eq_sSup_opensLE`: the covering condition on intersections for the
  collection of *all* opens contained in a fixed open, which does not contain `⊤` unless that
  open is `⊤`.
* `Stacks.DerivedGlueing.openModuleRestriction_eq`: the identification of restriction from an
  open `O` with extension by zero along `O` followed by the passage to the open-subspace model,
  for an arbitrary `O` — the generalization of
  `Stacks.DerivedGlueing.openModuleRestriction_top_eq` away from `O = ⊤`.
* `Stacks.DerivedGlueing.openModuleRestrictionIsoOfExtension` and
  `Stacks.DerivedGlueing.LocallyGiven.restrictionIsoOfExtension`: the consequence of that
  equality at an object — the restrictions of an object over `O` are the restrictions, read in
  the open-subspace model, of its extension by zero to the whole of `X`.  This is what
  relativizes from `⊤` to `O` an argument stated for objects on `X`, and it needs no passage to
  the ringed space `X|_O`: extension by zero along an arbitrary open is already faithful on
  derived categories, by `Stacks.DerivedGlueing.faithful_jShriek_mapDerivedCategory`.

## What is not here

`Stacks.DerivedGlueing.GluesAlongTwoOpens` itself is **not** proved, for any system other than
one prescribed by a global object.  Two inputs are missing, and neither is supplied below.

1. The isomorphism of [Stacks, Tag 0D69] over the overlap, which comes from the uniqueness
   clause of [Stacks, Tag 0D68]; in this development that clause is the predicate
   `Stacks.DerivedGlueing.HasUniqueSolutionOverIso`, which is not carried.  It is needed twice:
   once over `U ∩ V`, to compare the two given solutions there, and once over each member of the
   collection below `U ∪ V`, to identify the glued object with the prescribed one — and the
   second use is at the subsystem of this file, by
   `Stacks.DerivedGlueing.mem_eq_sSup_opensBelowPair`.
2. The glueing lemma [Stacks, Tag 08DG] itself, in the vocabulary of Situation 0D67.
   `Stacks.Cohomology.GlueingComplexes.exists_glueing` is stated for open immersions of ringed
   spaces and derived pullback; transporting it to the restriction functors of a
   `Stacks.DerivedGlueing.LocallyGiven` on the open subspace `U ∪ V` is a separate obligation,
   of which `Stacks.DerivedGlueing.openModuleRestriction_eq` below is one step.

So the module documentation of
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedCategory/GlueingOverAFiniteCover.lean`, which
says that "what remains missing for the two-open case is only the uniqueness clause of 0D68", is
incomplete: the naturality it reports as removing the obstruction identifies restriction along a
chain of open subspaces, and the glueing lemma is still stated about a different vocabulary.
The two missing statements are, as Lean types — both elaborate against this file:

`∀ (X : RingedSpace.{u, u}) (S : LocallyGiven X),`
`  HasUniqueSolutionOverIso S → GluesAlongTwoOpens S`

and

`∀ (X : RingedSpace.{u, u}) (S : LocallyGiven X) (U V : Opens X.carrier)`
`    (A : OpenDerivedCategory X U) (B : OpenDerivedCategory X V)`
`    (c : (S.restriction (U ⊓ V) U inf_le_left).obj A ≅`
`      (S.restriction (U ⊓ V) V inf_le_right).obj B),`
`  ∃ (F : OpenDerivedCategory X (U ⊔ V))`
`    (f : (S.restriction U (U ⊔ V) le_sup_left).obj F ≅ A)`
`    (g : (S.restriction V (U ⊔ V) le_sup_right).obj F ≅ B),`
`    (S.restrictionComp (U ⊓ V) U (U ⊔ V) inf_le_left le_sup_left).hom.app F ≫`
`        (S.restriction (U ⊓ V) U inf_le_left).map f.hom ≫ c.hom =`
`      (S.restrictionComp (U ⊓ V) V (U ⊔ V) inf_le_right le_sup_right).hom.app F ≫`
`        (S.restriction (U ⊓ V) V inf_le_right).map g.hom`

## References

* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 0D6A](https://stacks.math.columbia.edu/tag/0D6A)
* [Stacks Project, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ExtensionByZeroModules

namespace Stacks.DerivedGlueing

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-! ### The members of the collection below one of two opens -/

/-- **The members of the collection contained in `U` or in `V`.** Over these the two solutions
of the two-open case apply directly, and `U ∪ V` and every member of the collection below it are
unions of them. -/
def opensBelowPair (S : LocallyGiven X) (U V : Opens X.carrier) : Set (Opens X.carrier) :=
  {W | W ∈ S.opens ∧ (W ≤ U ∨ W ≤ V)}

/-- Every member of `opensBelowPair S U V` is a member of `S.opens`. -/
theorem opensBelowPair_subset (S : LocallyGiven X) (U V : Opens X.carrier) :
    opensBelowPair S U V ⊆ S.opens := fun _ hW => hW.1

/-- A member of `S.opens` contained in `U` lies in `opensBelowPair S U V`. -/
theorem mem_opensBelowPair_of_le_left {S : LocallyGiven X} {U V W : Opens X.carrier}
    (hW : W ∈ S.opens) (hWU : W ≤ U) : W ∈ opensBelowPair S U V := ⟨hW, Or.inl hWU⟩

/-- A member of `S.opens` contained in `V` lies in `opensBelowPair S U V`. -/
theorem mem_opensBelowPair_of_le_right {S : LocallyGiven X} {U V W : Opens X.carrier}
    (hW : W ∈ S.opens) (hWV : W ≤ V) : W ∈ opensBelowPair S U V := ⟨hW, Or.inr hWV⟩

/-- **The union of the two opens is the union of the members of the collection below one of
them.** The first is a member of the collection and the second is a union of members by
hypothesis. -/
theorem sup_eq_sSup_opensBelowPair (S : LocallyGiven X) (U V : Opens X.carrier)
    (hU : U ∈ S.opens) (hV : V = sSup {W | W ∈ S.opens ∧ W ≤ V}) :
    U ⊔ V = sSup (opensBelowPair S U V) := by
  refine le_antisymm (sup_le (le_sSup (mem_opensBelowPair_of_le_left hU le_rfl)) ?_)
    (sSup_le fun W hW => hW.2.elim (fun h => h.trans le_sup_left) fun h => h.trans le_sup_right)
  exact hV.le.trans
    (sSup_le fun W hW => le_sSup (mem_opensBelowPair_of_le_right hW.1 hW.2))

/-- **The covering condition on intersections is inherited by that subcollection.** The
intersection of two of its members is covered by members of the collection, and each of those is
contained in the first of the two, hence in `U` or in `V`. -/
theorem inf_eq_sSup_opensBelowPair (S : LocallyGiven X) (U V : Opens X.carrier)
    (hinter : ∀ U' ∈ S.opens, ∀ V' ∈ S.opens,
      U' ⊓ V' = sSup {W | W ∈ S.opens ∧ W ≤ U' ⊓ V'}) :
    ∀ U' ∈ opensBelowPair S U V, ∀ V' ∈ opensBelowPair S U V,
      U' ⊓ V' = sSup {W | W ∈ opensBelowPair S U V ∧ W ≤ U' ⊓ V'} := by
  intro U' hU' V' hV'
  have hset : {W | W ∈ S.opens ∧ W ≤ U' ⊓ V'} =
      {W | W ∈ opensBelowPair S U V ∧ W ≤ U' ⊓ V'} := by
    refine Set.ext fun W => ⟨fun hW => ⟨⟨hW.1, ?_⟩, hW.2⟩, fun hW => ⟨hW.1.1, hW.2⟩⟩
    exact hU'.2.imp (fun h => (hW.2.trans inf_le_left).trans h)
      fun h => (hW.2.trans inf_le_left).trans h
  rw [← hset]
  exact hinter U' hU'.1 V' hV'.1

/-- **Every member of the collection below the union of the two opens is the union of the
members below one of them that it contains.** A point of such a member `W` lies in `U` or in
`V`; in the first case the covering condition applied to the pair `W, U` produces a member of
the collection below `W ⊓ U` containing it, and in the second case `V` is first replaced by a
member of the collection below `V` containing the point. -/
theorem mem_eq_sSup_opensBelowPair (S : LocallyGiven X) (U V : Opens X.carrier)
    (hU : U ∈ S.opens) (hV : V = sSup {W | W ∈ S.opens ∧ W ≤ V})
    (hinter : ∀ U' ∈ S.opens, ∀ V' ∈ S.opens,
      U' ⊓ V' = sSup {W | W ∈ S.opens ∧ W ≤ U' ⊓ V'})
    (W : Opens X.carrier) (hW : W ∈ S.opens) (hWUV : W ≤ U ⊔ V) :
    W = sSup {T | T ∈ opensBelowPair S U V ∧ T ≤ W} := by
  refine le_antisymm (fun x hx => ?_) (sSup_le fun T hT => hT.2)
  rcases Opens.mem_sup.mp (hWUV hx) with hxU | hxV
  · have hxWU : x ∈ W ⊓ U := ⟨hx, hxU⟩
    rw [hinter W hW U hU] at hxWU
    obtain ⟨T, hT, hxT⟩ := Opens.mem_sSup.mp hxWU
    exact Opens.mem_sSup.mpr ⟨T, ⟨mem_opensBelowPair_of_le_left hT.1 (hT.2.trans inf_le_right),
      hT.2.trans inf_le_left⟩, hxT⟩
  · rw [hV] at hxV
    obtain ⟨V', hV', hxV'⟩ := Opens.mem_sSup.mp hxV
    have hxWV : x ∈ W ⊓ V' := ⟨hx, hxV'⟩
    rw [hinter W hW V' hV'.1] at hxWV
    obtain ⟨T, hT, hxT⟩ := Opens.mem_sSup.mp hxWV
    exact Opens.mem_sSup.mpr ⟨T, ⟨mem_opensBelowPair_of_le_right hT.1
      ((hT.2.trans inf_le_right).trans hV'.2), hT.2.trans inf_le_left⟩, hxT⟩

/-! ### The subsystem carried by a subcollection -/

/-- **The subsystem on a subcollection of the displayed opens.** Restriction, its factorization
through complexes, the comparison of restriction in two steps and its factorization are those of
the given system; the prescribed objects and transitions are its own, read on the smaller
collection. -/
def LocallyGiven.subcollection (S : LocallyGiven X) (𝒟 : Set (Opens X.carrier))
    (h𝒟 : 𝒟 ⊆ S.opens) : LocallyGiven X :=
  { S with
    opens := 𝒟
    obj := fun U hU => S.obj U (h𝒟 hU)
    rho := fun V U hVU hU hV => S.rho V U hVU (h𝒟 hU) (h𝒟 hV)
    cocycle := fun W V U hWV hVU hU hV hW =>
      S.cocycle W V U hWV hVU (h𝒟 hU) (h𝒟 hV) (h𝒟 hW) }

/-- The opens of `S.subcollection 𝒟 h𝒟` are the members of `𝒟`. -/
@[simp]
theorem LocallyGiven.subcollection_opens (S : LocallyGiven X) (𝒟 : Set (Opens X.carrier))
    (h𝒟 : 𝒟 ⊆ S.opens) : (S.subcollection 𝒟 h𝒟).opens = 𝒟 := rfl

/-- Restriction for `S.subcollection 𝒟 h𝒟` is the restriction of `S`. -/
@[simp]
theorem LocallyGiven.subcollection_restriction (S : LocallyGiven X) (𝒟 : Set (Opens X.carrier))
    (h𝒟 : 𝒟 ⊆ S.opens) (V U : Opens X.carrier) (hVU : V ≤ U) :
    (S.subcollection 𝒟 h𝒟).restriction V U hVU = S.restriction V U hVU := rfl

/-- The comparison of restriction in two steps for `S.subcollection 𝒟 h𝒟` is that of `S`. -/
@[simp]
theorem LocallyGiven.subcollection_restrictionComp (S : LocallyGiven X)
    (𝒟 : Set (Opens X.carrier)) (h𝒟 : 𝒟 ⊆ S.opens) (W V U : Opens X.carrier) (hWV : W ≤ V)
    (hVU : V ≤ U) :
    (S.subcollection 𝒟 h𝒟).restrictionComp W V U hWV hVU =
      S.restrictionComp W V U hWV hVU := rfl

/-- The object of `S.subcollection 𝒟 h𝒟` over a member `U` of `𝒟` is the object of `S` over `U`. -/
@[simp]
theorem LocallyGiven.subcollection_obj (S : LocallyGiven X) (𝒟 : Set (Opens X.carrier))
    (h𝒟 : 𝒟 ⊆ S.opens) (U : Opens X.carrier) (hU : U ∈ 𝒟) :
    (S.subcollection 𝒟 h𝒟).obj U hU = S.obj U (h𝒟 hU) := rfl

/-- A solution over an open for a system is a solution over that open for any subsystem: the
identifications over the members of the smaller collection are already there. -/
def SolutionOver.subcollection {S : LocallyGiven X} {𝒟 : Set (Opens X.carrier)}
    (h𝒟 : 𝒟 ⊆ S.opens) {O : Opens X.carrier} (A : SolutionOver S O) :
    SolutionOver (S.subcollection 𝒟 h𝒟) O where
  obj := A.obj
  rho W hW hWO := A.rho W (h𝒟 hW) hWO
  compatibility V W hWV hV hW hVO := A.compatibility V W hWV (h𝒟 hV) (h𝒟 hW) hVO

/-- **The prescribed object on a member of the collection is a solution over that member for any
subsystem.** This is `Stacks.DerivedGlueing.selfSolutionOver` with the membership of the member
itself taken in the *ambient* collection, which is what the two-open case needs: the member it
has to identify the glued object over need not belong to the subcollection
`Stacks.DerivedGlueing.opensBelowPair`. -/
def selfSolutionOverSubcollection (S : LocallyGiven X) (𝒟 : Set (Opens X.carrier))
    (h𝒟 : 𝒟 ⊆ S.opens) (W : Opens X.carrier) (hW : W ∈ S.opens) :
    SolutionOver (S.subcollection 𝒟 h𝒟) W where
  obj := S.obj W hW
  rho T hT hTW := S.rho T W hTW hW (h𝒟 hT)
  compatibility V T hTV hV hT hVW := (S.cocycle T V W hTV hVW hW (h𝒟 hV) (h𝒟 hT)).symm

/-! ### Restriction from an arbitrary open, in the open-subspace model -/

/-- **Restriction of modules from an open `O` to a smaller open `U`, as extension by zero from
`O` followed by restriction to the opens contained in `U` and the passage to the open-subspace
model.** This is `Stacks.DerivedGlueing.openModuleRestriction_top_eq` with `⊤` replaced by an
arbitrary open: the factorization of `j_U^*` through the open-subspace model does not depend on
the open the argument is extended from, so the generalization is again an equality of
functors. -/
theorem openModuleRestriction_eq (O U : Opens X.carrier) (hUO : U ≤ O) :
    jShriek O (underlyingRingSheaf X) ⋙
        (SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) U ⋙
          sliceToSubspace (underlyingRingSheaf X) U) =
      openModuleRestriction X U O hUO :=
  rfl

/-- **The restriction to `U` of the extension by zero of an object over `O`, read in the
open-subspace model, is its restriction from `O` to `U`.** This is
`Stacks.DerivedGlueing.Solution.canonicalRestrictionIso` with the global open `⊤` replaced by an
arbitrary open `O`, and it is what relativizes to `O` an argument stated for objects on the whole
of `X` and a collection of opens of `X`: an object over `O` is pushed to `X` by extension by
zero, which is faithful on derived categories for an arbitrary open
(`Stacks.DerivedGlueing.faithful_jShriek_mapDerivedCategory`), and its restrictions to the opens
below `O` are then its restrictions in the system.  No passage to the ringed space `X|_O` is
involved. -/
def openModuleRestrictionIsoOfExtension (O U : Opens X.carrier) (hUO : U ≤ O)
    (K : OpenDerivedCategory X O) :
    (sliceToSubspace (underlyingRingSheaf X) U).mapDerivedCategory.obj
        ((SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) U).mapDerivedCategory.obj
          ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K)) ≅
      (openModuleRestriction X U O hUO).mapDerivedCategory.obj K :=
  (mapDerivedCategoryCompIso (SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) U)
      (sliceToSubspace (underlyingRingSheaf X) U)).app
      ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K) ≪≫
    (mapDerivedCategoryCompIso (jShriek O (underlyingRingSheaf X))
      (SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) U ⋙
        sliceToSubspace (underlyingRingSheaf X) U)).app K ≪≫
    (mapDerivedCategoryCongr (eqToIso (openModuleRestriction_eq O U hUO))).app K

/-- **The displayed restriction of a system of locally given derived objects, computed on the
whole of `X`.** For an object over an open `O` and an open `U` below `O`, the restriction `K|_U`
displayed by the system is the restriction to `U`, in the open-subspace model, of the extension
by zero of `K` along `O`.

This is `Stacks.DerivedGlueing.Solution.restrictionIso` relativized from `⊤` to `O`, with the
prescribed object replaced by an arbitrary one: it is the comparison that a glueing statement
for morphisms over `O` needs in order to be read off a statement about objects on `X`. -/
def LocallyGiven.restrictionIsoOfExtension (S : LocallyGiven X) (O U : Opens X.carrier)
    (hUO : U ≤ O) (K : OpenDerivedCategory X O) :
    (sliceToSubspace (underlyingRingSheaf X) U).mapDerivedCategory.obj
        ((SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) U).mapDerivedCategory.obj
          ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K)) ≅
      (S.restriction U O hUO).obj K :=
  openModuleRestrictionIsoOfExtension O U hUO K ≪≫
    ((restrictionIsoMapDerivedCategory S U O hUO).app K).symm

/-- **The covering condition on intersections for the collection of all opens contained in a
fixed open.** The intersection of two opens contained in `P` is itself one, so it covers itself.

This collection contains `⊤` only when `P = ⊤`, so a system carried by it witnesses the
hypotheses of the glueing statements away from the case `⊤ ∈ ℬ`, where
`Stacks.DerivedGlueing.exists_solution_of_top_mem` already settles them. -/
theorem inf_eq_sSup_opensLE (P : Opens X.carrier) :
    ∀ U ∈ {W : Opens X.carrier | W ≤ P}, ∀ V ∈ {W : Opens X.carrier | W ≤ P},
      U ⊓ V = sSup {W | W ∈ {W' : Opens X.carrier | W' ≤ P} ∧ W ≤ U ⊓ V} := by
  intro U hU V _
  refine le_antisymm (le_sSup ⟨?_, le_rfl⟩) (sSup_le fun _ hW => hW.2)
  exact inf_le_left.trans (Set.mem_ofPred_eq ▸ hU)

/-- The collection of all opens contained in `P` contains `⊤` exactly when `P = ⊤`. -/
theorem top_mem_opensLE_iff (P : Opens X.carrier) :
    (⊤ : Opens X.carrier) ∈ {W : Opens X.carrier | W ≤ P} ↔ P = ⊤ :=
  ⟨fun h => top_le_iff.mp h, fun h => le_of_eq h.symm⟩

/-! ### A system for which the two-open case holds outright -/

section Global

variable (X)

/-- **The solution over an arbitrary open of the system prescribed by a global object.** Its
object is the restriction of the global object, its identification over a member of the
collection is the comparison of restriction in two steps, and the compatibility is the
associativity of those comparisons,
`Stacks.DerivedGlueing.LocallyGiven.restrictionComp_pentagon`. -/
def solutionOverOfGlobal (𝒞 : Set (Opens X.carrier)) (K : OpenDerivedCategory X ⊤)
    (O : Opens X.carrier) : SolutionOver (locallyGivenOfGlobal X 𝒞 K) O where
  obj := ((restrictionDatum X).restriction O ⊤ le_top).obj K
  rho W _ hWO := (((restrictionDatum X).restrictionComp W O ⊤ hWO le_top).app K).symm
  compatibility V W hWV _ _ hVO :=
    (Iso.inv_eq_of_sq
      (((restrictionDatum X).restrictionComp W O ⊤ (hWV.trans hVO) le_top).app K)
      (((restrictionDatum X).restrictionComp W V O hWV hVO).app
        (((restrictionDatum X).restriction O ⊤ le_top).obj K))
      (((restrictionDatum X).restrictionComp W V ⊤ hWV le_top).app K)
      (((restrictionDatum X).restriction W V hWV).mapIso
        (((restrictionDatum X).restrictionComp V O ⊤ hVO le_top).app K))
      ((restrictionDatum X).restrictionComp_pentagon W V O ⊤ hWV hVO le_top K)).symm

/-- **The two-open case of [Stacks, Tag 0D6A] holds, with nothing assumed, for a system
prescribed by a single global object.** Every open carries a solution — the restriction of the
global object — so in particular the union of the two does.

Nothing is tagged here: the two-open case is a step of the source's proof of Tag 0D6A and not a
clause of its statement, and what is proved is in any case only one instance of the hypothesis
`Stacks.DerivedGlueing.GluesAlongTwoOpens`.  Its purpose is that the theorems carrying that
hypothesis — `Stacks.DerivedGlueing.exists_solution_of_finite_cover` and its partners for Tags
0D6B and 0D6C — are not vacuous, and are not vacuous at a system whose collection does **not**
contain `⊤`; see `Stacks.DerivedGlueing.inf_eq_sSup_opensLE`. -/
theorem gluesAlongTwoOpens_locallyGivenOfGlobal (𝒞 : Set (Opens X.carrier))
    (K : OpenDerivedCategory X ⊤) : GluesAlongTwoOpens (locallyGivenOfGlobal X 𝒞 K) :=
  fun U _ V _ _ _ _ _ _ => ⟨solutionOverOfGlobal X 𝒞 K (U ⊔ V)⟩

/-- **The two-open case with every one of its binders discharged from closed terms, at a
collection that does not contain `⊤`.** Take the collection of *all* opens contained in a fixed
open `P` and prescribe on each of them the restriction of a sheaf of modules `F` placed in
degree zero.  Then for any two opens `U`, `V` below `P` the five hypotheses of
`Stacks.DerivedGlueing.GluesAlongTwoOpens` hold — the covering of `V` and of `U ∩ V` because
each is itself a member, the covering condition on intersections by
`Stacks.DerivedGlueing.inf_eq_sSup_opensLE`, the negative self-Ext hypothesis by
`Stacks.DerivedGlueing.subsingleton_shiftedHom_locallyGivenOfGlobal_single`, and the two
solutions by `Stacks.DerivedGlueing.solutionOverOfGlobal` — and the conclusion follows.

This is the non-degeneracy certificate for that hypothesis.  Nothing is assumed about `P`, `U`,
`V` or `F`: `U` and `V` may be distinct, incomparable and both proper, `F` may be nonzero, and
`⊤` belongs to the collection only when `P = ⊤`
(`Stacks.DerivedGlueing.top_mem_opensLE_iff`), which is the case in which the glueing statements
of Tags 0D6A to 0D6C are already unconditional. -/
theorem nonempty_solutionOver_sup_opensLE (P : Opens X.carrier)
    (F : SheafOfModules.{u} (restrictedRingSheaf X ⊤)) (U V : Opens X.carrier)
    (hUP : U ≤ P) (hVP : V ≤ P) :
    Nonempty (SolutionOver (locallyGivenOfGlobal X {W : Opens X.carrier | W ≤ P}
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (restrictedRingSheaf X ⊤)) 0).obj F)) (U ⊔ V)) :=
  gluesAlongTwoOpens_locallyGivenOfGlobal X {W : Opens X.carrier | W ≤ P}
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (restrictedRingSheaf X ⊤)) 0).obj F) U hUP V
    (le_antisymm (le_sSup ⟨hVP, le_rfl⟩) (sSup_le fun _ hW => hW.2))
    (le_antisymm (le_sSup ⟨inf_le_left.trans hUP, le_rfl⟩) (sSup_le fun _ hW => hW.2))
    (inf_eq_sSup_opensLE P)
    (fun W hW i hi =>
      subsingleton_shiftedHom_locallyGivenOfGlobal_single X {W : Opens X.carrier | W ≤ P} F W hW
        i hi)
    (solutionOverOfGlobal X {W : Opens X.carrier | W ≤ P} _ U)
    (solutionOverOfGlobal X {W : Opens X.carrier | W ≤ P} _ V)

end Global

end Stacks.DerivedGlueing

end
