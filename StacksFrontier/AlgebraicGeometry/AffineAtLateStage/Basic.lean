module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Filtered.Final
public import StacksCore.Tactic.StacksAttribute

/-!
# Affineness over the base at a late stage of a limit of schemes

Stacks Tag 09ZM says that if `X = lim X_i` is a directed limit of schemes over `S` with affine
transition morphisms, with `S` and every `X_i` quasi-compact and quasi-separated, and if
`X → S` is affine, then `X_i → S` is affine for `i` large enough.

This file carries the restatement of that result and its proof.

## The universe-general statement

With independent universes it reads

    universe uI uS
    lemma eventually_isAffineHom_of_isLimit
        {I : Type uI} [Category.{uI} I] [IsCofiltered I]
        {S : Scheme.{uS}} [CompactSpace S] [QuasiSeparatedSpace S]
        (D : I ⥤ Scheme.{uS}) (t : D ⟶ (Functor.const I).obj S)
        (c : Cone D) (hc : IsLimit c) (f : c.pt ⟶ S)
        (hf : c.π ≫ t = (Functor.const I).map f)
        [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
        [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g)] [IsAffineHom f] :
        ∃ i : I, ∀ {j : I} (_ : j ⟶ i), IsAffineHom (t.app j)

with the index universe `uI` free of the scheme universe `uS`, and with no smallness condition
on `I` of any kind.

## The hypothesis added

`{I : Type uI} [Category.{uI} I]` becomes `{I : Type u} [Category.{u} I]`, where `u` is the
universe of the schemes: the index category is required to live in the universe of the schemes.
Nothing else changes. In particular the cofilteredness, affine-transition, quasi-compactness and
quasi-separatedness hypotheses are exactly those above, the limit cone is still an arbitrary
limit cone presented by `IsLimit`, the structure morphisms are still recorded by a natural
transformation to the constant diagram, and no `Small`, `LocallySmall`, `InitiallySmall` or
`EssentiallySmall` instance is introduced.

## The Stacks text that justifies it

Unlike the sibling tags of the 081D family, Tag 09ZM does not refer to a situation; it carries
its own hypotheses, and the first of them is

> Let `S` be a scheme. Let `X = lim X_i` be a directed limit of schemes over `S` with affine
> transition morphisms.

"Directed limit" fixes the universe. The index of a directed system is a *directed set*: its
objects form a set and so do its morphisms, all in the one universe of sets of the source, which
has no universe hierarchy, and the schemes are objects of that same universe. Smallness is not a
separate standing convention being appealed to here; it is part of what the words "directed
limit" denote, and it is explicit in the source to exactly the extent that "directed" is. The
reading is the same one that was applied to Tag 06AC, which inherits the phrase from Situation
081D; here the phrase is in the tag's own statement.

The hypothesis `[IsCofiltered I]` in place of a directed set is kept. It is a
generalisation of the source rather than a weakening — a directed set, read as a category
through its opposite, is cofiltered — so the restated result is at least as strong as the
source's on this axis.

## Why no weaker form serves

Tag 09ZM is not merely proved *using* Tag 01Z6 (`AlgebraicGeometry.Scheme.exists_isAffine_of_`
`isLimit` in Mathlib, which is stated with `I : Type u` and `Category.{u} I`); the two are
equivalent, and the universe restriction is exactly where the content of that equivalence sits.
The forward direction is the source's own proof, carried out below. The converse is
`exists_isAffine_of_isLimit_of_eventually_isAffineHom`: it takes the universe-general statement with its
index universe free, applies it to the terminal scheme as base, and derives Tag 01Z6 with the
index universe equally free. So the universe-general form is not a form of Tag 09ZM that happens to be
harder to reach by this route — it is precisely as strong as a universe-free Tag 01Z6.

That rules out the alternatives:

* Weakening the conclusion — asking only for a property of the limit, or for an index in some
  larger category — changes what the source says and is excluded.
* `[LocallySmall.{u} I] [InitiallySmall.{u} I]` on the stated universes, which is the pair
  carried in `StacksFrontier/AlgebraicGeometry/LimitUniverse/AffineTransitionLimit.lean`,
  does lift the one input this proof needs: that
  file's `Scheme.exists_isAffine_of_isLimit_of_initiallySmall` is Tag 01Z6 with the index
  universe free under exactly those two instances. Such a form would be a *generalisation* of
  what is proved here, since a `u`-small category satisfies both, so restating to it later would
  strengthen this result and need no change downstream. It is not chosen because it replaces the
  source's plain "directed limit" — whose index universe is not a predicate at all — by two
  predicates the source does not write. It is also not free: the proof
  below applies Tag 01Z6 to the diagram of preimages indexed by `Over i₀`, so that route would
  additionally need the two instances transported to `Over i₀`, which is not checked here.
* `[Small.{u} I]` alone does not suffice: it bounds the objects of `I` and says nothing about
  its morphisms, so `I` need not be equivalent to a `u`-small category.
* Keeping the stated universe and recovering smallness by cofinality is not available:
  `CategoryTheory.initiallySmall_iff_exists_small_weakly_initial_set` makes that equivalent to
  `InitiallySmall.{u} I`, which is not a consequence of the stated hypotheses.

What is *not* claimed is that the literal statement is false. No counterexample to it is given
here, and the 06AC counterexample does not transpose: there the limit collapses to the empty
scheme and the conclusion fails at every stage, whereas here a collapsing limit makes the
conclusion easier rather than harder. What is established is the equivalence above, which places
the literal form exactly at the verified hard limit of this development — Mathlib's
`Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean` uses `{I : Type u} [Category.{u} I]`
throughout, and freeing that index universe breaks the synthesis of `PreservesColimit`,
`ReflectsColimit` and `HasLimit (F ⋙ Γ.rightOp)`, because `CommRingCat.{u}` has no colimits over
a larger index universe.

## Main results

* `AffineAtLateStage.exists_isAffineOpen_preimage`: over an affine open of the base, the preimage
  at some stage past a prescribed one is affine. This is the source's appeal to Tag 01Z6, applied
  to the diagram of preimages.
* `AffineAtLateStage.exists_isAffineHom`: the restated Tag 09ZM with the structure morphisms given
  as a compatible family rather than as a natural transformation.
* `AffineAtLateStage.eventually_isAffineHom_of_isLimit`: the restated Tag 09ZM itself — the
  statement with its index universe tied to the scheme universe.
* `AffineAtLateStage.exists_isAffine_of_isLimit_of_eventually_isAffineHom`: the converse
  reduction, deriving Tag 01Z6 over a free index universe from the universe-general statement over a free
  index universe.

## Implementation notes

The source covers `S` by finitely many affine opens `V_j`, observes that `f⁻¹(V_j)` is the limit
of the `f_i⁻¹(V_j)` and is affine, and concludes by Tag 01Z6 that each `f_i⁻¹(V_j)` is affine at
some stage; Tag 01S8 then makes `f_i` affine. Here the diagram of preimages and the fact that
its limit is the preimage in the limit are Mathlib's `AlgebraicGeometry.opensDiagram`,
`AlgebraicGeometry.opensCone` and `AlgebraicGeometry.isLimitOpensCone`, indexed by `Over i₀`;
Tag 01S8 is `AlgebraicGeometry.isAffineHom_of_forall_exists_isAffineOpen`. The single late stage
is produced by `CategoryTheory.IsCofiltered.inf_objs_exists` in `Over i₀`, which is cofiltered.
That the preimages of an affine open of `S` at the stages are quasi-compact is the source's
"since `S` is quasi-separated the morphisms `V_j → S` are quasi-compact": here it is
`AlgebraicGeometry.quasiCompact_of_compactSpace` applied to the structure morphism of the stage.

The helper statements take the structure morphisms as a family `p : ∀ i, D.obj i ⟶ S` together
with the compatibility `p j = D.map g ≫ p i`, which is the natural transformation `t` and its naturality. This
keeps the targets of those morphisms syntactically `S` rather than `((Functor.const I).obj S)`
`.obj i`, which instance synthesis does not see through.

## References

* [The Stacks Project, Tag 09ZM](https://stacks.math.columbia.edu/tag/09ZM)
* [The Stacks Project, Tag 01Z6](https://stacks.math.columbia.edu/tag/01Z6)
* [The Stacks Project, Tag 01S8](https://stacks.math.columbia.edu/tag/01S8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe uI u

namespace Stacks.AlgebraicGeometry.AffineAtLateStage

section Restated

variable {I : Type u} [Category.{u} I] {S : Scheme.{u}} (D : I ⥤ Scheme.{u}) (c : Cone D)
  (p : ∀ i, D.obj i ⟶ S)

variable [IsCofiltered I] [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] [QuasiSeparatedSpace S]

/-- **Stacks Project, Tag 09ZM, the appeal to Tag 01Z6.** Let `D` be a cofiltered diagram of
qcqs schemes over a quasi-separated base `S`, with affine transition morphisms, and let `f` be
the induced morphism from a limit of `D` to `S`. If `f` is affine, then for every affine open
`V` of `S` and every stage `i₀` there is a stage `i` over `i₀` at which the preimage of `V` is
affine.

The diagram of the preimages of `V` at the stages over `i₀` has the preimage of `V` in the limit
as its limit, and that preimage is affine because `f` is; so Tag 01Z6 applies to it. -/
theorem exists_isAffineOpen_preimage
    (hp : ∀ {i j : I} (g : j ⟶ i), p j = D.map g ≫ p i)
    (hc : IsLimit c) {f : c.pt ⟶ S} (hf : ∀ i, c.π.app i ≫ p i = f) [IsAffineHom f]
    (i₀ : I) {V : S.Opens} (hV : IsAffineOpen V) :
    ∃ (i : I) (_ : i ⟶ i₀), IsAffineOpen (p i ⁻¹ᵁ V) := by
  set U : (D.obj i₀).Opens := p i₀ ⁻¹ᵁ V with hU
  have hUc : IsCompact (U : Set (D.obj i₀)) := (p i₀).isCompact_preimage hV.isCompact
  have hcs (j : Over i₀) : CompactSpace ((opensDiagram D i₀ U).obj j) :=
    isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage _ U.2 hUc)
  have hqs (j : Over i₀) : QuasiSeparatedSpace ((opensDiagram D i₀ U).obj j) :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ (D.map _ ⁻¹ᵁ _).2).mp (.of_quasiSeparatedSpace _)
  have hpt : IsAffine (opensCone D c i₀ U).pt := by
    show IsAffine (c.π.app i₀ ⁻¹ᵁ U).toScheme
    rw [hU, ← Scheme.Hom.comp_preimage, hf i₀]
    exact hV.preimage f
  obtain ⟨j, hj⟩ := Scheme.exists_isAffine_of_isLimit (opensDiagram D i₀ U)
    (opensCone D c i₀ U) (isLimitOpensCone D c hc i₀ U)
  refine ⟨j.left, j.hom, ?_⟩
  rw [hp j.hom, Scheme.Hom.comp_preimage]
  exact hj

/-- **Stacks Project, Tag 09ZM, restated**, with the structure morphisms of the stages given as
a compatible family `p` rather than as a natural transformation to a constant diagram.

A finite affine open cover of `S` reduces this to `exists_isAffineOpen_preimage` at each member
of the cover; cofilteredness of the category of stages over a fixed one merges the finitely many
resulting stages into one, and Tag 01S8 turns affineness of the preimages of the cover into
affineness of the structure morphism there. -/
theorem exists_isAffineHom [CompactSpace S]
    (hp : ∀ {i j : I} (g : j ⟶ i), p j = D.map g ≫ p i)
    (hc : IsLimit c) {f : c.pt ⟶ S} (hf : ∀ i, c.π.app i ≫ p i = f) [IsAffineHom f] :
    ∃ i : I, ∀ {j : I} (_ : j ⟶ i), IsAffineHom (p j) := by
  classical
  obtain ⟨i₀⟩ : Nonempty I := IsCofiltered.nonempty
  choose W hWaff hxW _ using fun x : S ↦
    exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x : S ↦ (W x : Set S))
    (fun x ↦ (W x).isOpen) fun y _ ↦ Set.mem_iUnion.mpr ⟨y, hxW y⟩
  choose idx gidx hidx using fun x : S ↦
    exists_isAffineOpen_preimage D c p hp hc hf i₀ (hWaff x)
  obtain ⟨m, hm⟩ := IsCofiltered.inf_objs_exists (C := Over i₀)
    (s.image fun x ↦ Over.mk (gidx x))
  have key : IsAffineHom (p m.left) := by
    apply isAffineHom_of_forall_exists_isAffineOpen
    intro y
    obtain ⟨x, hxs, hyx⟩ : ∃ x ∈ s, y ∈ W x := by simpa using hs (Set.mem_univ y)
    obtain ⟨h⟩ := hm (Finset.mem_image_of_mem (fun x ↦ Over.mk (gidx x)) hxs)
    refine ⟨W x, hyx, hWaff x, ?_⟩
    rw [hp h.left, Scheme.Hom.comp_preimage]
    exact (hidx x).preimage _
  exact ⟨m.left, fun {j} g ↦ by rw [hp g]; infer_instance⟩

/-- **Stacks Project, Tag 09ZM, restated.** The universe-general statement, with its `{I : Type uI}` and
`[Category.{uI} I]` replaced by `{I : Type u}` and `[Category.{u} I]`, where `u` is the universe
of the schemes — the only change.

Let `X = lim X_i` be a cofiltered limit of quasi-compact and quasi-separated schemes over a
quasi-compact and quasi-separated base `S`, with affine transition morphisms. If the induced
morphism `X → S` is affine, then so is the structure morphism of every sufficiently late
stage.

No Stacks attribute is attached, and the reason is the paragraph above. The universe-general statement declares two
independent universes, binding its index category against a scheme universe it does not
constrain; this statement ties them, so it is strictly narrower than that statement. That narrowing
is real content and not an artefact — the companion theorem below takes the universe-general
form as an explicit hypothesis precisely to say so — so a tag here would claim the universe-general statement while
proving less than it. -/
theorem eventually_isAffineHom_of_isLimit [CompactSpace S]
    (t : D ⟶ (Functor.const I).obj S) (hc : IsLimit c) (f : c.pt ⟶ S)
    (hf : c.π ≫ t = (Functor.const I).map f) [IsAffineHom f] :
    ∃ i : I, ∀ {j : I} (_ : j ⟶ i), IsAffineHom (t.app j) :=
  exists_isAffineHom D c (fun i ↦ t.app i) (fun g ↦ by simp) hc
    (f := f) fun i ↦ by simpa using congrArg (fun α ↦ NatTrans.app α i) hf

end Restated

/-- The universe-general statement of Tag 09ZM, with its index universe free of the scheme universe,
implies Tag 01Z6 with the index universe equally free: a cofiltered limit of qcqs schemes with
affine transition morphisms which is itself affine has an affine stage.

Take the terminal scheme as the base `S`: every morphism to it is the unique one, so the
structure morphisms assemble into a natural transformation automatically, and a morphism between
affine schemes is affine. This is what makes the universe restriction in
`eventually_isAffineHom_of_isLimit` the content of that statement rather than an artefact of the
route taken to it. -/
theorem exists_isAffine_of_isLimit_of_eventually_isAffineHom
    {I : Type uI} [Category.{uI} I] [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (hc : IsLimit c) [IsAffine c.pt]
    (H : ∀ {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
      (t : D ⟶ (Functor.const I).obj S) (_ : IsLimit c) (f : c.pt ⟶ S),
      c.π ≫ t = (Functor.const I).map f → IsAffineHom f →
      ∃ i : I, ∀ {j : I} (_ : j ⟶ i), IsAffineHom (t.app j)) :
    ∃ i : I, IsAffine (D.obj i) := by
  let t : D ⟶ (Functor.const I).obj (⊤_ Scheme.{u}) :=
    { app := fun _ ↦ terminal.from _, naturality := fun _ _ _ ↦ terminal.hom_ext _ _ }
  obtain ⟨i, hi⟩ := H t hc (terminal.from _)
    (NatTrans.ext (funext fun _ ↦ terminal.hom_ext _ _)) inferInstance
  have hti : IsAffineHom (terminal.from (D.obj i)) := hi (𝟙 i)
  exact ⟨i, isAffine_of_isAffineHom (terminal.from (D.obj i))⟩

end Stacks.AlgebraicGeometry.AffineAtLateStage
