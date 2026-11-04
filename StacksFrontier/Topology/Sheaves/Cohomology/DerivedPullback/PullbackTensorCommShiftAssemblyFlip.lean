module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorCommShiftAssembly
public import StacksFrontier.CategoryTheory.Shift.CommShiftAssocChain
import StacksCore.Tactic.StacksAttribute

/-!
# The first comparison of Tag 079U in the first variable, and `LeftComparisonCommShift₂`

`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPullback/PullbackTensorCommShiftAssembly.lean`
assembles the *second*-variable half of
`Stacks.Cohomology.DerivedPullbackTensor.LeftComparisonCommShift₂` out of the one obligation
`DerivedToTensorCommShift₂ Y` that the two comparisons of [Stacks, Tag 079U] share, and reduces
the whole proposition to a single named statement,
`Stacks.Cohomology.DerivedPullbackTensor.LeftComparisonCommShiftFlipApp` — the mirror in the first
variable, for which that file writes no chain.  **This file writes that chain and proves that
statement**, so `LeftComparisonCommShift₂ f` now follows from `DerivedToTensorCommShift₂ Y` and
nothing else.

## Main results

* `Stacks.Cohomology.DerivedPullbackTensor.derivedToTensorPinnedFlipApp`,
  `derivedToTensorPinnedFlipApp_app` and `derivedToTensorPinnedFlipApp_commShift`: **the
  first-variable component of `derivedToTensorNatTrans` at the pinned spelling, its components,
  and its shift compatibility from `DerivedToTensorCommShift₂`** — the mirror of
  `derivedToTensorPinnedApp` and its two lemmas.
* `Stacks.Cohomology.DerivedPullbackTensor.leftComparisonPinnedFlipApp` and
  `leftComparisonPinnedFlipApp_commShift`: **the flipped four-factor chain and its shift
  compatibility**, the latter by one application of
  `CategoryTheory.NatTrans.commShift_assocChain`.
* `Stacks.Cohomology.DerivedPullbackTensor.leftComparisonPinnedFlipApp_eq_curryFlipApp`: **the
  flipped chain is the first-variable component of the curried comparison**, conjugated by the
  flips of the two pinning isomorphisms.
* `Stacks.Cohomology.DerivedPullbackTensor.leftComparisonCurryFlipApp_commShift` and
  `leftComparisonCommShiftFlipApp_of_derivedToTensor`: **the `commShift_flipApp` field of
  `LeftComparisonCommShift₂`, i.e. `LeftComparisonCommShiftFlipApp f`.**
* `Stacks.Cohomology.DerivedPullbackTensor.leftComparisonCommShift₂`: **the first comparison of
  [Stacks, Tag 079U] is compatible with the shifts in both variables, granted the one shared
  obligation `DerivedToTensorCommShift₂ Y`.**

## Implementation notes

**Everything is the mirror of the second-variable assembly, with one simplification.**  The
flipped datum of a `CategoryTheory.Functor.CommShift₂` closure instance is
`CategoryTheory.Functor.CommShift₂.postcomp_commShiftFlipObj`,
`precomp₁_commShiftFlipObj` and `precomp₂_commShiftFlipObj` where the unflipped assembly used
`postcomp_commShiftObj` and friends, and all six hold by `rfl`; the flip of an isomorphism of
bifunctors is `CategoryTheory.Functor.CommShift₂.flipIso`, whose components at `L` are exactly the
isomorphisms `CategoryTheory.Functor.CommShift₂.ofIso` transports the flipped data along, so
`CategoryTheory.Functor.CommShift.ofIso_compatibility` crosses between the `Functor.curry.obj`
spelling and the pinned one here for the same reason it does there.

The simplification is that the four factors and the three junctions of the chain are *not* seven
separate declarations here.  They are one application of
`CategoryTheory.NatTrans.commShift_assocChain`, which states the whole chain over an abstract
category with every category, functor and transformation a variable: there every junction matches
on the nose, and the identification of the closure instances' fields with the
`CategoryTheory.Functor.CommShift.comp` that the associators demand — the identification that the
unflipped assembly pays with `CategoryTheory.NatTrans.commShift_comp_of_eq_data` at two junctions
— is discharged by the single `isDefEq` of the `exact`, at `default` transparency, where
`postcompInt`, `precomp₁` and `precomp₂` unfold.  So the whole flipped chain's
compatibility is one `exact`.

**What this file costs, and the one shape that reduced it.**  Checked on its own against unchanged
imports, it took 9.4 and 9.5 min with the conjugation stated as its own lemma and 8.2, 8.2 and
8.3 min with that lemma folded into `leftComparisonCurryFlipApp_commShift`, the two contents
interleaved in a single series so that run order cannot account for the gap — the slowest folded
run is still a minute faster than the fastest unfolded one.  Built instead from the module's
imports rather than edited, where the two phases are reported apart, it was 3.9 min to elaborate
and 6.2 min for the kernel to re-check unfolded, against 3.1 min and 5.0 min folded: the saving is
about a fifth of each phase, and elaboration is a third of the cost here, not the few percent this
family was assumed to spend outside the kernel.

Where that cost sits: with the imports, the opens and the `implicit_reducible` rung above it and no
declaration at all, this file checks in 1.0 s, so none of the time is spent loading what it
imports.  Cut off just above the folded lemma it is 6.1 min and with the lemma 7.5 min, so that one
declaration alone was 1.4 min — and folding it took off rather more than that, because the use site
stops instantiating the constant's type as well.

What the fold removes is a *statement*, not a proof.  `curry_map_leftComparison_flipApp_eq` used
to state `leftComparisonPinnedFlipApp_eq_curryFlipApp` backwards and was used exactly once, so the
kernel validated a statement naming `Functor.curry.map (leftComparison f)` and both flipped
pinning isomorphisms twice over — once to admit the lemma, once at the use site.  Applying
`eq_inv_comp_comp_hom` inline pays for it once.  The companion measurement in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPullback/PullbackTensorCommShiftFlipApp.lean` is
the same trade in the other direction, where naming a conjugate or the `CommShift` data cost
8-17 s each time it was introduced; the two agree that in this family a name for an expensive type
is itself the expense.

Timing this file needs care: a probe comment appended at the *end* of it does not re-time
anything.  Lean's warm server reuses every command before the first change, so the check comes
back in under a second.  A probe comment has to sit above the declarations — immediately after the
imports — for the file to be elaborated and re-checked in full.

**What is still owed for Tag 079U.**
`Stacks.Cohomology.DerivedPullbackTensor.RightComparisonCommShift₂` is untouched and owes both of
its fields.  Its chain has three factors rather than two — the derived pullback in each variable,
which is `CategoryTheory.NatTrans.CommShift₂.whiskerRight_bifunctor` and `whiskerLeft_bifunctor`
at the first leg, the obligation at `X`, and
`CategoryTheory.Functor.mapBifunctorTotalBifunctorIso_commShift₂` at
`pullbackTensorComplexNatIso` — and the last of those still needs the identification of
`pullbackTensorComplexNatIso` with `totalComplexPairTransport`'s bundled form read as a
transformation of *curried* bifunctors, which no declaration in this development states.

**Nothing here carries a tag.**  All of it is a step of the proof of the shift compatibility
[Stacks, Tag 0B54] needs for its dévissage, not a clause of the statement of any tag.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DerivedPullbackTensor

universe u

attribute [local instance] HasDerivedCategory.standard

open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback (Modules)
open Stacks.Cohomology.KFlatDerivedPullback (derivedPullback_commShift)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

/-! ### The obligation, read in the first variable at the pinned spelling -/

section OneSpace

variable (Z : RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (L : CochainComplex (Modules Z) ℤ)

/-- **The component of `derivedToTensorNatTrans Z` in the first variable, at a fixed cochain
complex `L` in the second, written between the two pinned bifunctors.**  The mirror of
`derivedToTensorPinnedApp`: it is the curried component in the flipped variable, conjugated by the
flips of the two isomorphisms that pin the spellings, so its components are those of
`derivedToTensorNatTrans Z` and nothing is changed but the commutation data its shift
compatibility is read at. -/
def derivedToTensorPinnedFlipApp :
    (curriedComplexesDerivedTensor Z).flip.obj L ⟶ (curriedComplexesTotal Z).flip.obj L :=
  ((Functor.CommShift₂.flipIso (curryComplexesDerivedTensorIso Z)).app L).hom ≫
    (Functor.curry.map (derivedToTensorNatTrans Z)).flipApp L ≫
      ((Functor.CommShift₂.flipIso (curryComplexesTotalIso Z)).app L).inv

/-- **The components of `derivedToTensorPinnedFlipApp` are those of `derivedToTensorNatTrans`.**
Each component of the flip of an isomorphism of bifunctors is a component of that isomorphism, and
every component of the two pinning isomorphisms is `CategoryTheory.Iso.refl`, so the component at
`K` is the composite of `𝟙` with `(derivedToTensorNatTrans Z).app (K, L)` and `𝟙`.

This is a step of the proof of `leftComparisonPinnedFlipApp_eq_curryFlipApp`, not a clause of any
tag, so it carries no tag attribute. -/
theorem derivedToTensorPinnedFlipApp_app (K : CochainComplex (Modules Z) ℤ) :
    (derivedToTensorPinnedFlipApp Z L).app K = (derivedToTensorNatTrans Z).app (K, L) :=
  id_comp_id ((derivedToTensorNatTrans Z).app (K, L))

/-- **The one obligation of [Stacks, Tag 079U], read in the first variable at the pinned data.**
The mirror of `derivedToTensorPinnedApp_commShift`: `DerivedToTensorCommShift₂ Z` is stated at the
`Functor.curry.obj` spelling, whose flipped commutation data are
`CategoryTheory.Functor.CommShift.ofIso` at the components of the flips of
`curryComplexesDerivedTensorIso` and `curryComplexesTotalIso`, and those components are
shift-compatible *for the transported data* by
`CategoryTheory.Functor.CommShift.ofIso_compatibility`.

The chain is taken in two named steps, this one and `derivedToTensorPinnedFlipApp_commShift`,
rather than as one instance search: the single search's term is one the kernel cannot re-check
inside its budget, exactly as in the second variable. -/
theorem derivedToTensorPinnedFlipAppTail_commShift (h : DerivedToTensorCommShift₂ Z) :
    (letI := curriedComplexesTotal_commShift₂Int Z
    letI := curryComplexesDerivedTensor_commShift₂Int Z
    NatTrans.CommShift ((Functor.curry.map (derivedToTensorNatTrans Z)).flipApp L ≫
      ((Functor.CommShift₂.flipIso (curryComplexesTotalIso Z)).app L).inv) ℤ) := by
  letI := curriedComplexesTotal_commShift₂Int Z
  letI := curryComplexesDerivedTensor_commShift₂Int Z
  letI := curryComplexesTotal_commShift₂Int Z
  letI := Functor.CommShift.ofIso_compatibility
    ((Functor.CommShift₂.flipIso (curryComplexesTotalIso Z)).app L) ℤ
  letI := (h : NatTrans.CommShift₂Int
    (Functor.curry.map (derivedToTensorNatTrans Z))).commShift_flipApp L
  infer_instance

/-- **The one obligation of [Stacks, Tag 079U], read in the first variable at the pinned data**,
with its last two factors taken as `derivedToTensorPinnedFlipAppTail_commShift`, so that only the
first junction is left here. -/
theorem derivedToTensorPinnedFlipApp_commShift (h : DerivedToTensorCommShift₂ Z) :
    (letI := curriedComplexesDerivedTensor_commShift₂Int Z
    letI := curriedComplexesTotal_commShift₂Int Z
    NatTrans.CommShift (derivedToTensorPinnedFlipApp Z L) ℤ) := by
  letI := curriedComplexesDerivedTensor_commShift₂Int Z
  letI := curriedComplexesTotal_commShift₂Int Z
  letI := curryComplexesDerivedTensor_commShift₂Int Z
  letI := Functor.CommShift.ofIso_compatibility
    ((Functor.CommShift₂.flipIso (curryComplexesDerivedTensorIso Z)).app L) ℤ
  letI := derivedToTensorPinnedFlipAppTail_commShift Z L h
  unfold derivedToTensorPinnedFlipApp
  infer_instance

end OneSpace

/-! ### The chain for the first comparison in the first variable -/

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (L : CochainComplex (Modules Y) ℤ)

/-- **The first-variable component of `leftComparison f`, as a four-factor chain between the
pinned bifunctors.**  The mirror of `leftComparisonPinnedApp`: the obligation in the flipped
variable whiskered by the derived pullback, the first leg whiskered by `Tot(- ⊗ L)`, and the two
reassociations those whiskerings need.

That this typechecks says that `(curriedComplexesPullbackOfTensor f).flip.obj L` *is*
`Q ⋙ ((Q(-) ⊗^𝐋 QL) ⋙ Lf^*)` and `(curriedComplexesTotalPullback f).flip.obj L` *is*
`Tot(- ⊗ L) ⋙ (f^* ⋙ Q)`, definitionally. -/
def leftComparisonPinnedFlipApp :
    (curriedComplexesPullbackOfTensor f).flip.obj L ⟶
      (curriedComplexesTotalPullback f).flip.obj L :=
  (Functor.associator DerivedCategory.Q
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).flip.obj
        (DerivedCategory.Q.obj L)) (derivedPullback f)).inv ≫
    Functor.whiskerRight (derivedToTensorPinnedFlipApp Y L) (derivedPullback f) ≫
      (Functor.associator ((tensorComplexBifunctor (Y := Y)).flip.obj L) DerivedCategory.Q
        (derivedPullback f)).hom ≫
        Functor.whiskerLeft ((tensorComplexBifunctor (Y := Y)).flip.obj L)
          (derivedPullbackNatTrans f)

/-- **The first-variable component of `leftComparison f`, at the pinned spelling, is
shift-compatible.**  All three junctions of the flipped four-factor chain close at once, by
`CategoryTheory.NatTrans.commShift_assocChain`: at an abstract instantiation each junction matches
on the nose, and the identifications
`CategoryTheory.Functor.CommShift₂.postcomp_commShiftFlipObj`,
`precomp₁_commShiftFlipObj` and `precomp₂_commShiftFlipObj` — all `rfl` — are discharged by the
`isDefEq` of this `exact` rather than being asked of instance search.

So the one obligation `DerivedToTensorCommShift₂ Y` and the first leg are all this component
needs, exactly as in the second variable. -/
theorem leftComparisonPinnedFlipApp_commShift (h : DerivedToTensorCommShift₂ Y) :
    (letI := curriedComplexesPullbackOfTensor_commShift₂Int f
    letI := curriedComplexesTotalPullback_commShift₂Int f
    NatTrans.CommShift (leftComparisonPinnedFlipApp f L) ℤ) := by
  letI := derivedPullback_commShift f
  letI : ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).flip.obj
      (DerivedCategory.Q.obj L)).CommShift ℤ :=
    (derivedTensorCommShift₂Int Y).commShiftFlipObj _
  letI : ((tensorComplexBifunctor (Y := Y)).flip.obj L).CommShift ℤ :=
    (inferInstance : (tensorComplexBifunctor (Y := Y)).CommShift₂Int).commShiftFlipObj L
  letI := curriedComplexesDerivedTensor_commShift₂Int Y
  letI := curriedComplexesTotal_commShift₂Int Y
  exact NatTrans.commShift_assocChain DerivedCategory.Q
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).flip.obj
      (DerivedCategory.Q.obj L)) (derivedPullback f)
    ((tensorComplexBifunctor (Y := Y)).flip.obj L) DerivedCategory.Q
    (pullbackComplex f ⋙ DerivedCategory.Q) (derivedToTensorPinnedFlipApp Y L)
    (derivedPullbackNatTrans f) (derivedToTensorPinnedFlipApp_commShift Y L h)
    (derivedPullbackNatTrans_commShift f)

/-! ### The flipped chain *is* the flipped component of the curried comparison -/

/-- **The flipped four-factor chain is the first-variable component of `Functor.curry.map
(leftComparison f)`, conjugated by the flips of the two pinning isomorphisms.**  The mirror of
`leftComparisonPinnedApp_eq_curryApp`, with the same content: both sides are
`Lf^*((derivedToTensorNatTrans Y).app (K, L)) ≫ (derivedPullbackNatTrans f).app (Tot(K ⊗ L))` with
identities interleaved, and the one step that is not definitional is that the chain applies `Lf^*`
to the identity-wrapped composite where the curried comparison applies it to the bare component.

This is a step of the proof of `LeftComparisonCommShift₂`, not a clause of any tag, so it carries
no tag attribute. -/
theorem leftComparisonPinnedFlipApp_eq_curryFlipApp :
    leftComparisonPinnedFlipApp f L =
      ((Functor.CommShift₂.flipIso (curryComplexesPullbackOfTensorIso f)).app L).hom ≫
        (Functor.curry.map (leftComparison f)).flipApp L ≫
          ((Functor.CommShift₂.flipIso (curryComplexesTotalPullbackIso f)).app L).inv := by
  ext K
  exact id_paste
    ((derivedPullbackNatTrans f).app (((tensorComplexBifunctor (Y := Y)).flip.obj L).obj K))
    (congrArg (fun v => (derivedPullback f).map v) (derivedToTensorPinnedFlipApp_app Y L K))

/-! ### `LeftComparisonCommShiftFlipApp`, and `LeftComparisonCommShift₂` -/

/-- **The `commShift_flipApp` half of `LeftComparisonCommShift₂` at a fixed `L`**: the
first-variable component of `Functor.curry.map (leftComparison f)` is shift-compatible, at the
data `LeftComparisonCommShift₂` is stated at, granted the one obligation
`DerivedToTensorCommShift₂ Y`.  The mirror of `leftComparisonCurryApp_commShift`.

This is a step of the proof of `LeftComparisonCommShift₂`, not a clause of any tag, so it carries
no tag attribute. -/
theorem leftComparisonCurryFlipApp_commShift (h : DerivedToTensorCommShift₂ Y) :
    (letI := curryComplexesPullbackOfTensor_commShift₂Int f
    letI := curryComplexesTotalPullback_commShift₂Int f
    NatTrans.CommShift ((Functor.curry.map (leftComparison f)).flipApp L) ℤ) := by
  letI := curryComplexesPullbackOfTensor_commShift₂Int f
  letI := curryComplexesTotalPullback_commShift₂Int f
  letI := curriedComplexesPullbackOfTensor_commShift₂Int f
  letI := curriedComplexesTotalPullback_commShift₂Int f
  letI := Functor.CommShift.ofIso_compatibility
    ((Functor.CommShift₂.flipIso (curryComplexesPullbackOfTensorIso f)).app L) ℤ
  letI := Functor.CommShift.ofIso_compatibility
    ((Functor.CommShift₂.flipIso (curryComplexesTotalPullbackIso f)).app L) ℤ
  letI := leftComparisonPinnedFlipApp_commShift f L h
  exact NatTrans.commShift_of_eq
    (eq_inv_comp_comp_hom
      ((Functor.CommShift₂.flipIso (curryComplexesPullbackOfTensorIso f)).app L)
      ((Functor.CommShift₂.flipIso (curryComplexesTotalPullbackIso f)).app L)
      (leftComparisonPinnedFlipApp_eq_curryFlipApp f L))

/-- **`LeftComparisonCommShiftFlipApp f` holds**, granted the one obligation
`DerivedToTensorCommShift₂ Y`: this is the statement
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPullback/PullbackTensorCommShiftAssembly.lean`
names and leaves open, the mirror in the first variable of everything that file does in the
second.

This is a step of the proof of 0B54, not a clause of any tag, so it carries no tag attribute. -/
theorem leftComparisonCommShiftFlipApp_of_derivedToTensor (h : DerivedToTensorCommShift₂ Y) :
    LeftComparisonCommShiftFlipApp f :=
  fun L' => leftComparisonCurryFlipApp_commShift f L' h

/-- **The first comparison of [Stacks, Tag 079U] is compatible with the shifts in both variables,
granted the single obligation the two comparisons share.**  Its `commShift_app` field is
`leftComparisonCurryApp_commShift` and its `commShift_flipApp` field is
`leftComparisonCurryFlipApp_commShift`; `leftComparisonCommShift₂_of_flipApp` assembles the two.

So `LeftComparisonCommShift₂` is no longer an obligation of [Stacks, Tag 079U]:
`DerivedToTensorCommShift₂ Y` is, and `RightComparisonCommShift₂` is.

This is a step of the proof of 0B54, not a clause of any tag, so it carries no tag attribute. -/
theorem leftComparisonCommShift₂ (h : DerivedToTensorCommShift₂ Y) :
    LeftComparisonCommShift₂ f :=
  leftComparisonCommShift₂_of_flipApp f h (leftComparisonCommShiftFlipApp_of_derivedToTensor f h)

end Stacks.Cohomology.DerivedPullbackTensor

end
