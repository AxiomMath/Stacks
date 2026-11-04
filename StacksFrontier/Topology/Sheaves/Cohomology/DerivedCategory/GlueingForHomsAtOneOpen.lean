module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingOverACoveringCollection
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingForHomsOverAMember
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.TwoOpenGlueingInput

/-!
# The glueing of morphisms at one open, and uniqueness of a solution from it

Let `(X, 𝒪_X)` be a ringed space and let `(ℬ, K_U, ρ^U_V)` be a system of locally given derived
objects on it, as in Situation 0D67.  `Stacks.DerivedGlueing.HasGluingForHomsOver` is the sheaf
condition of [Stacks, Tag 0D66] part (2) read at *every* open subset that is a union of the
members of `ℬ` contained in it.  Its consumer
`Stacks.DerivedGlueing.hasUniqueSolutionOverIso_of_hasGluingForHomsOver` uses it at one open at a
time.  This file isolates that one-open instance, `Stacks.DerivedGlueing.HasGluingForHomsAt`, and
derives the uniqueness of a solution over an open from it at that open alone.

## Main definitions

* `Stacks.DerivedGlueing.HasGluingForHomsAt`: the glueing condition for morphisms at a single
  open subset — the body of `Stacks.DerivedGlueing.HasGluingForHomsOver` with its open, and the
  two hypotheses on the collection, removed.
* `Stacks.DerivedGlueing.GluesAlongProperChain`: glueing along a chain with no greatest element.

## Main results

* `Stacks.DerivedGlueing.hasGluingForHomsOver_iff_forall_hasGluingForHomsAt`: the two predicates
  agree, by `Iff.rfl`.
* `Stacks.DerivedGlueing.hasGluingForHomsAt_of_hasGluingForHomsOver`: the one-open form follows
  from the general one.
* `Stacks.DerivedGlueing.hasGluingForHomsAt_top_of_mem`: it holds at `⊤` whenever `⊤` is a member
  of the collection.
* `Stacks.DerivedGlueing.existsUnique_solutionOverIso_of_hasGluingForHomsAt`: two solutions over
  `O` are identified by a unique isomorphism of solutions, from the glueing condition at `O`
  alone, with no hypothesis on the collection.
* `Stacks.DerivedGlueing.hasUniqueSolutionOverIso_of_hasGluingForHomsAt`: the uniqueness clause of
  [Stacks, Tag 0D68], relativized, from the one-open form at each open.
* `Stacks.DerivedGlueing.exists_unique_solutionIso_of_hasGluingForHomsAtTop`: two solutions of the
  system are identified by a unique isomorphism of solutions, from the glueing of morphisms at
  `⊤`.
* `Stacks.DerivedGlueing.gluesAlongChain_of_gluesAlongProperChain`: glueing along a chain reduces
  to chains with no greatest element, a chain with a greatest element containing its own
  supremum.
* `Stacks.DerivedGlueing.gluesAlongChain_locallyGivenOfGlobal` and
  `Stacks.DerivedGlueing.chainCertificate_strictMono`: glueing along a chain for a system
  prescribed by a single global object, at a chain with no greatest element over a collection
  that does not contain `⊤`.

## References

* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 0D6C](https://stacks.math.columbia.edu/tag/0D6C)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Stacks.DerivedGlueing

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-! ### The glueing condition for morphisms at a single open -/

/-- **The sheaf condition of [Stacks, Tag 0D66] part (2) at one open subset.** Let `O` be an open
subset and let `K` and `L` be objects over `O` with `Ext^i(K|_W, L|_W) = 0` for `i < 0` and every
member `W` of the collection contained in `O`.  Then a family of morphisms `K|_W ⟶ L|_W`,
compatible with restriction between members, comes from a unique morphism `K ⟶ L`.

This is the body of `Stacks.DerivedGlueing.HasGluingForHomsOver` at a fixed `O`, with the two
hypotheses on the collection removed; `O` is *not* required to be the union of the members
contained in it. -/
def HasGluingForHomsAt (S : LocallyGiven X) (O : Opens X.carrier) : Prop :=
  ∀ K L : OpenDerivedCategory X O,
    (∀ (W : Opens X.carrier), W ∈ S.opens → ∀ hWO : W ≤ O, ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom ((S.restriction W O hWO).obj K)
        ((S.restriction W O hWO).obj L) i)) →
    ∀ φ : ∀ (W : Opens X.carrier), W ∈ S.opens → ∀ hWO : W ≤ O,
        (S.restriction W O hWO).obj K ⟶ (S.restriction W O hWO).obj L,
      (∀ (W T : Opens X.carrier) (hW : W ∈ S.opens) (hT : T ∈ S.opens) (hTW : T ≤ W)
          (hWO : W ≤ O), restrictHomBelow S hTW hWO (φ W hW hWO) = φ T hT (hTW.trans hWO)) →
      ∃! ψ : K ⟶ L, ∀ (W : Opens X.carrier) (hW : W ∈ S.opens) (hWO : W ≤ O),
        (S.restriction W O hWO).map ψ = φ W hW hWO

/-- **The one-open form is exactly the general one, open by open.** -/
theorem hasGluingForHomsOver_iff_forall_hasGluingForHomsAt (S : LocallyGiven X) :
    HasGluingForHomsOver S ↔
      ∀ (O : Opens X.carrier), O = sSup {W | W ∈ S.opens ∧ W ≤ O} →
        (∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V}) →
        HasGluingForHomsAt S O :=
  Iff.rfl

/-- **The one-open form is weaker than the general one.** This is the comparison that makes the
uniqueness statements below stronger than their partners in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UniquenessOverACover`. -/
theorem hasGluingForHomsAt_of_hasGluingForHomsOver (S : LocallyGiven X)
    (hglue : HasGluingForHomsOver S) (O : Opens X.carrier)
    (hO : O = sSup {W | W ∈ S.opens ∧ W ≤ O})
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V}) :
    HasGluingForHomsAt S O :=
  hglue O hO hinter

/-- **The glueing condition holds at `⊤` when `⊤` is a member of the collection**, by
`Stacks.DerivedGlueing.exists_unique_hom_of_mem`: over a member there is nothing to glue.  This is
the degenerate inhabitant, and it is the only one the development has; see the section *The
inhabitant is degenerate, and what a non-degenerate one would be* of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingForHomsOverAMember`. -/
theorem hasGluingForHomsAt_top_of_mem (S : LocallyGiven X)
    (htop : (⊤ : Opens X.carrier) ∈ S.opens) :
    HasGluingForHomsAt S ⊤ :=
  fun K L _ φ hφ => exists_unique_hom_of_mem S htop K L φ hφ

/-! ### The uniqueness argument, from the glueing condition at one open -/

/-- **Two solutions over `O` are identified by a unique isomorphism of solutions, granted the
glueing of morphisms at `O` alone.** This is the argument of
`Stacks.DerivedGlueing.hasUniqueSolutionOverIso_of_hasGluingForHomsOver`, which applies the
glueing condition only at the open it is reading, carried out from that single instance.

Nothing is assumed of the collection: `O` need not be the union of the members contained in it,
and the intersection of two members need not be a union of members.  Both hypotheses were
present in the partner statement only in order to *apply* the general predicate at `O`.

The comparison morphisms `Stacks.DerivedGlueing.SolutionOver.compHom` form a compatible family in
both directions, by `Stacks.DerivedGlueing.SolutionOver.restrictHomBelow_compHom`, and the
negative self-Ext hypothesis transports to the pairs formed from the two objects along the
identifications of a solution.  The two glued morphisms are mutually inverse because their
composites restrict to the identity on every member and the uniqueness of the glueing identifies
them with the identity; the same uniqueness shows the resulting isomorphism is the only
isomorphism of solutions. -/
theorem existsUnique_solutionOverIso_of_hasGluingForHomsAt (S : LocallyGiven X)
    {O : Opens X.carrier} (hglue : HasGluingForHomsAt S O)
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i))
    (A B : SolutionOver S O) :
    ∃! φ : A.obj ≅ B.obj, A.IsCompatibleHom B φ.hom := by
  -- The negative self-Ext hypothesis, transported to a pair of solutions over `O`.
  have hExt' : ∀ (C D : SolutionOver S O) (W : Opens X.carrier) (hW : W ∈ S.opens)
      (hWO : W ≤ O), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom ((S.restriction W O hWO).obj C.obj)
        ((S.restriction W O hWO).obj D.obj) i) := fun C D W hW hWO i hi =>
    subsingleton_shiftedHom_of_iso (C.rho W hW hWO) (D.rho W hW hWO) i (hExt W hW i hi)
  -- The glueing of the comparison morphisms, in both directions.
  obtain ⟨Φ, hΦ, -⟩ := hglue A.obj B.obj (hExt' A B) (A.compHom B)
    fun W T hW hT hTW hWO => A.restrictHomBelow_compHom B hW hT hTW hWO
  obtain ⟨Ψ, hΨ, -⟩ := hglue B.obj A.obj (hExt' B A) (B.compHom A)
    fun W T hW hT hTW hWO => B.restrictHomBelow_compHom A hW hT hTW hWO
  -- The uniqueness of the glueing of the identity family, for each of the two solutions.
  have hone : ∀ (C : SolutionOver S O) (ξ : C.obj ⟶ C.obj),
      (∀ (W : Opens X.carrier) (hW : W ∈ S.opens) (hWO : W ≤ O),
        (S.restriction W O hWO).map ξ = 𝟙 ((S.restriction W O hWO).obj C.obj)) → ξ = 𝟙 C.obj := by
    intro C ξ hξ
    exact (hglue C.obj C.obj (hExt' C C)
      (fun W _hW hWO => 𝟙 ((S.restriction W O hWO).obj C.obj))
      fun _W _T _hW _hT hTW hWO => restrictHomBelow_id S hTW hWO).unique hξ
      fun W _hW _hWO => CategoryTheory.Functor.map_id _ _
  have hΦΨ : Φ ≫ Ψ = 𝟙 A.obj := by
    refine hone A _ fun W hW hWO => ?_
    rw [Functor.map_comp, hΦ W hW hWO, hΨ W hW hWO, SolutionOver.compHom_comp_compHom]
  have hΨΦ : Ψ ≫ Φ = 𝟙 B.obj := by
    refine hone B _ fun W hW hWO => ?_
    rw [Functor.map_comp, hΨ W hW hWO, hΦ W hW hWO, SolutionOver.compHom_comp_compHom]
  -- The glued morphism is an isomorphism of solutions, and the only one.
  refine ⟨⟨Φ, Ψ, hΦΨ, hΨΦ⟩, fun W hW hWO => ?_, fun θ hθ => ?_⟩
  · rw [hΦ W hW hWO, SolutionOver.compHom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · refine Iso.ext ((hglue A.obj B.obj (hExt' A B) (A.compHom B)
      fun W T hW hT hTW hWO => A.restrictHomBelow_compHom B hW hT hTW hWO).unique ?_ hΦ)
    intro W hW hWO
    rw [SolutionOver.compHom, ← hθ W hW hWO, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **The uniqueness clause of [Stacks, Tag 0D68], relativized, from the glueing of morphisms at
each open.** The same statement as
`Stacks.DerivedGlueing.hasUniqueSolutionOverIso_of_hasGluingForHomsOver`, read through the
one-open form. -/
theorem hasUniqueSolutionOverIso_of_hasGluingForHomsAt (S : LocallyGiven X)
    (hglue : ∀ (O : Opens X.carrier), O = sSup {W | W ∈ S.opens ∧ W ≤ O} →
      (∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V}) →
      HasGluingForHomsAt S O) :
    HasUniqueSolutionOverIso S :=
  fun O hO hinter hExt A B =>
    existsUnique_solutionOverIso_of_hasGluingForHomsAt S (hglue O hO hinter) hExt A B

/-! ### Uniqueness of a solution, from the glueing of morphisms at the whole space -/

/-- **Uniqueness of a solution up to unique isomorphism, from the glueing of morphisms at `⊤`.**
In Situation 0D67, assume the sheaf condition of [Stacks, Tag 0D66] part (2) at the whole space
and that the prescribed objects have no negative self-Ext.  Then any two solutions are identified
by exactly one isomorphism of solutions.  No covering hypothesis on the collection is used. -/
theorem exists_unique_solutionIso_of_hasGluingForHomsAtTop (S : LocallyGiven X)
    (hglueTop : HasGluingForHomsAt S ⊤)
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i))
    (A B : Solution S) :
    ∃! φ : A.obj ≅ B.obj, A.IsCompatibleHom B φ.hom := by
  obtain ⟨φ, hφ, hφuniq⟩ := existsUnique_solutionOverIso_of_hasGluingForHomsAt S hglueTop hExt
    A.toSolutionOver B.toSolutionOver
  exact ⟨φ, Solution.isCompatibleHom_of_toSolutionOver hφ,
    fun ψ hψ => hφuniq ψ (Solution.isCompatibleHom_toSolutionOver hψ)⟩

/-! ### Glueing along a chain: the degenerate case, and a non-degenerate index shape -/

/-- **A chain with a greatest element glues for the degenerate reason.** If a chain has a greatest
element then it contains its own supremum, so a solution over each of its members is already a
solution over the supremum.  No glueing happens, and this is why
`Stacks.DerivedGlueing.GluesAlongChain` is only ever needed for a chain with no greatest
element. -/
theorem gluesAlongChain_of_isGreatest (S : LocallyGiven X) (𝒟 : Set (Opens X.carrier))
    {M : Opens X.carrier} (hM : M ∈ 𝒟) (hub : ∀ O ∈ 𝒟, O ≤ M)
    (hsol : ∀ O ∈ 𝒟, Nonempty (SolutionOver S O)) :
    Nonempty (SolutionOver S (sSup 𝒟)) := by
  have hsup : sSup 𝒟 = M := le_antisymm (sSup_le hub) (le_sSup hM)
  exact hsup ▸ hsol M hM

/-! ### Glueing along a chain with no greatest element is all the Zorn argument needs -/

/-- **Glueing along a chain with no greatest element.** The hypothesis
`Stacks.DerivedGlueing.GluesAlongChain` with the chain required to have no greatest element.

This is strictly weaker, and it is all that the Zorn argument of
`Stacks.DerivedGlueing.exists_solution_of_covers` consumes: a chain with a greatest element
contains its own supremum, so `Stacks.DerivedGlueing.gluesAlongChain_of_isGreatest` settles it.
`Stacks.DerivedGlueing.chainCertificate_strictMono` exhibits a chain of the shape this quantifies
over.  It holds for every system, by
`Stacks.DerivedGlueing.gluesAlongProperChain_unconditional`. -/
def GluesAlongProperChain (S : LocallyGiven X) : Prop :=
  ∀ 𝒟 : Set (Opens X.carrier), 𝒟.Nonempty →
    (∀ O ∈ 𝒟, ∃ O' ∈ 𝒟, ¬ O' ≤ O) →
    (∀ O ∈ 𝒟, ∀ O' ∈ 𝒟, O ≤ O' ∨ O' ≤ O) →
    (∀ O ∈ 𝒟, O = sSup {W | W ∈ S.opens ∧ W ≤ O}) →
    (∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V}) →
    (∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i)) →
    (∀ O ∈ 𝒟, Nonempty (SolutionOver S O)) →
    Nonempty (SolutionOver S (sSup 𝒟))

/-- **Glueing along a chain follows from glueing along a chain with no greatest element.** Either
the chain has a greatest element, and then `Stacks.DerivedGlueing.gluesAlongChain_of_isGreatest`
applies, or it does not, and then the hypothesis applies. -/
theorem gluesAlongChain_of_gluesAlongProperChain (S : LocallyGiven X)
    (hchain : GluesAlongProperChain S) : GluesAlongChain S := by
  intro 𝒟 hne htot hcov hinter hExt hsol
  by_cases hmax : ∃ M ∈ 𝒟, ∀ O ∈ 𝒟, O ≤ M
  · obtain ⟨M, hM, hub⟩ := hmax
    exact gluesAlongChain_of_isGreatest S 𝒟 hM hub hsol
  · refine hchain 𝒟 hne (fun O hO => ?_) htot hcov hinter hExt hsol
    by_contra hcon
    exact hmax ⟨O, hO, fun O' hO' => not_not.mp fun h => hcon ⟨O', hO', h⟩⟩

/-- **Existence of a solution from the two-open case and glueing along a chain with no greatest
element.** The content of `Stacks.DerivedGlueing.exists_solution_of_covers` with its chain
hypothesis restricted to chains that have no greatest element, by
`Stacks.DerivedGlueing.gluesAlongChain_of_gluesAlongProperChain`. -/
theorem exists_solution_of_covers_of_properChain (S : LocallyGiven X)
    (hglue : GluesAlongTwoOpens S) (hchain : GluesAlongProperChain S)
    (hcover : sSup S.opens = ⊤)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i)) :
    Nonempty (Solution S) :=
  exists_solution_of_covers S hglue (gluesAlongChain_of_gluesAlongProperChain S hchain) hcover
    hinter hExt

/-- **Existence of a solution with the glued object displayed, from the two-open case and glueing
along a chain with no greatest element.** The content of
`Stacks.DerivedGlueing.exists_glueing_of_covers` with the same restriction. -/
theorem exists_glueing_of_covers_of_properChain (S : LocallyGiven X)
    (hglue : GluesAlongTwoOpens S) (hchain : GluesAlongProperChain S)
    (hcover : sSup S.opens = ⊤)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i)) :
    ∃ (K : OpenDerivedCategory X ⊤)
      (rho : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens),
        (S.restriction U ⊤ le_top).obj K ≅ S.obj U hU),
      ∀ (V U : Opens X.carrier) (hVU : V ≤ U) (hU : U ∈ S.opens) (hV : V ∈ S.opens),
        (S.restrictionComp V U ⊤ hVU le_top).hom.app K ≫
            (S.restriction V U hVU).map (rho U hU).hom ≫ (S.rho V U hVU hU hV).hom =
          (rho V hV).hom :=
  exists_glueing_of_covers S hglue (gluesAlongChain_of_gluesAlongProperChain S hchain) hcover
    hinter hExt

section Global

variable (X)

/-- **Glueing along a chain holds, with nothing assumed, for a system prescribed by a single
global object.** Every open carries a solution — the restriction of the global object — so in
particular the union of a chain does.

Glueing along a chain holds for every system, by
`Stacks.DerivedGlueing.gluesAlongChain_unconditional`; here it holds because nothing needs to be
glued. -/
theorem gluesAlongChain_locallyGivenOfGlobal (𝒞 : Set (Opens X.carrier))
    (K : OpenDerivedCategory X ⊤) : GluesAlongChain (locallyGivenOfGlobal X 𝒞 K) :=
  fun 𝒟 _ _ _ _ _ _ => ⟨solutionOverOfGlobal X 𝒞 K (sSup 𝒟)⟩

/-- **The intersection of two opens each lying below a stage lies below a stage.** The
auxiliary covering condition for the collection of opens contained in some member of an
increasing sequence. -/
theorem inf_eq_sSup_stagesBelow (W : ℕ → Opens X.carrier) {U V : Opens X.carrier}
    (hU : ∃ n, U ≤ W n) :
    U ⊓ V = sSup {T : Opens X.carrier | (∃ n, T ≤ W n) ∧ T ≤ U ⊓ V} := by
  obtain ⟨n, hn⟩ := hU
  exact le_antisymm (le_sSup ⟨⟨n, inf_le_left.trans hn⟩, le_rfl⟩) (sSup_le fun _ hT => hT.2)

/-- **Every stage of an increasing sequence is the union of the opens below a stage that it
contains** — trivially, since it is itself one of them. -/
theorem stage_eq_sSup_stagesBelow (W : ℕ → Opens X.carrier) (n : ℕ) :
    W n = sSup {T : Opens X.carrier | (∃ m, T ≤ W m) ∧ T ≤ W n} :=
  le_antisymm (le_sSup ⟨⟨n, le_rfl⟩, le_rfl⟩) (sSup_le fun _ hT => hT.2)

/-- **A strictly increasing sequence of opens has no greatest element in its range.** -/
theorem not_isGreatest_range_of_strictMono (W : ℕ → Opens X.carrier) (hW : StrictMono W) :
    ∀ O ∈ Set.range W, ∃ O' ∈ Set.range W, ¬ O' ≤ O := by
  rintro O ⟨n, rfl⟩
  exact ⟨W (n + 1), ⟨n + 1, rfl⟩, fun h => absurd (hW (Nat.lt_succ_self n)) (not_lt_of_ge h)⟩

/-- **`⊤` is not an open below a stage when every stage is proper.** -/
theorem top_notMem_stagesBelow (W : ℕ → Opens X.carrier) (hproper : ∀ n, W n ≠ ⊤) :
    (⊤ : Opens X.carrier) ∉ {T : Opens X.carrier | ∃ n, T ≤ W n} := by
  rintro ⟨n, hn⟩
  exact hproper n (top_le_iff.mp hn)

/-- **Every hypothesis of `Stacks.DerivedGlueing.GluesAlongChain` is dischargeable at a chain with
no greatest element, over a collection that does not contain `⊤`.** Let `W` be a strictly
increasing sequence of proper open subsets of `X` whose union is `X`, let `F` be a sheaf of
`𝒪_X`-modules, and take the collection of all opens contained in some `W n`, with `F` placed in
degree zero prescribed on each of them.  Then the range of `W` is a nonempty chain, totally
ordered by inclusion, each of whose members is the union of the members of the collection it
contains, the collection satisfies the covering condition on intersections, the prescribed
objects have no negative self-Ext, each member of the chain carries a solution, and the union of
the chain carries one.  Moreover the chain has no greatest element and `⊤` is not a member of the
collection.

A chain with a greatest element is settled by `Stacks.DerivedGlueing.gluesAlongChain_of_isGreatest`
with no glueing at all, and a collection containing `⊤` has the solution given by the prescribed
object on `⊤`, by `Stacks.DerivedGlueing.exists_solution_of_top_mem`; the chain here is neither.
Since a nonempty finite linear order has a greatest element, such a chain is infinite and its
members are proper, so the carrier of `X` is not noetherian. -/
theorem chainCertificate_strictMono (W : ℕ → Opens X.carrier) (hW : StrictMono W)
    (hproper : ∀ n, W n ≠ ⊤) (hcover : (⨆ n, W n) = ⊤)
    (F : SheafOfModules.{u} (restrictedRingSheaf X ⊤)) :
    (Set.range W).Nonempty ∧
      (∀ O ∈ Set.range W, ∀ O' ∈ Set.range W, O ≤ O' ∨ O' ≤ O) ∧
      (∀ O ∈ Set.range W, ∃ O' ∈ Set.range W, ¬ O' ≤ O) ∧
      (⊤ : Opens X.carrier) ∉ {T : Opens X.carrier | ∃ n, T ≤ W n} ∧
      sSup (Set.range W) = ⊤ ∧
      Nonempty (SolutionOver
        (locallyGivenOfGlobal X {T : Opens X.carrier | ∃ n, T ≤ W n}
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (restrictedRingSheaf X ⊤)) 0).obj F))
        (sSup (Set.range W))) := by
  refine ⟨⟨W 0, 0, rfl⟩, ?_, not_isGreatest_range_of_strictMono X W hW,
    top_notMem_stagesBelow X W hproper, (sSup_range (f := W)).trans hcover, ?_⟩
  · rintro O ⟨a, rfl⟩ O' ⟨b, rfl⟩
    rcases le_total a b with h | h
    · exact Or.inl (hW.monotone h)
    · exact Or.inr (hW.monotone h)
  · refine gluesAlongChain_locallyGivenOfGlobal X _ _ (Set.range W) ⟨W 0, 0, rfl⟩
      (fun O hO O' hO' => ?_) (fun O hO => ?_) (fun U hU V _ => ?_) (fun U hU i hi => ?_)
      fun O _ => ⟨solutionOverOfGlobal X _ _ O⟩
    · obtain ⟨a, rfl⟩ := hO
      obtain ⟨b, rfl⟩ := hO'
      rcases le_total a b with h | h
      · exact Or.inl (hW.monotone h)
      · exact Or.inr (hW.monotone h)
    · obtain ⟨n, rfl⟩ := hO
      exact stage_eq_sSup_stagesBelow X W n
    · exact inf_eq_sSup_stagesBelow X W hU
    · exact subsingleton_shiftedHom_locallyGivenOfGlobal_single X
        {T : Opens X.carrier | ∃ n, T ≤ W n} F U hU i hi

end Global

end Stacks.DerivedGlueing

end
