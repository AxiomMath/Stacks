module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorCommShiftOnKFlat
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorCommShiftAssembly
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorCommShiftAssemblyFlip
import StacksCore.Tactic.StacksAttribute

/-!
# The second condition of Tag 079U's obligation on the K-flat complexes, and the obligation itself

`Stacks.Cohomology.DerivedPullbackTensor.DerivedToTensorCommShiftOnKFlat` is a conjunction of two
one-variable shift compatibilities.  Its first half,
`Stacks.Cohomology.DerivedPullbackTensor.commShift_app_of_kFlat`, is proved in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPullback/PullbackTensorCommShiftOnKFlat.lean`,
together with every shift input of the second half — `thetaFirst_commShift`,
`sourceFirstIso_commShift` and `targetFirstIso_commShift`.  What remains is the
*bookkeeping* identity saying that the chain `thetaFirst` is the conjugate of the transformation
the second half is about.  This file proves it, and with it the second half, the whole of
`DerivedToTensorCommShiftOnKFlat` and — through the reduction
`derivedToTensorCommShift₂_of_kFlat` — the whole of
`Stacks.Cohomology.DerivedPullbackTensor.DerivedToTensorCommShift₂`, which is the single
obligation the two comparisons of [Stacks, Tag 079U] share.

## Main results

* `Stacks.Cohomology.DerivedPullbackTensor.thetaFirst_eq`: **the chain of
  `PullbackTensorCommShiftOnKFlat` is the second-variable-flipped component of the canonical map
  of [Stacks, Tag 06YU], conjugated by its two reassociations.**
* `Stacks.Cohomology.DerivedPullbackTensor.commShift_flipApp_of_kFlat`: **the second of the two
  conditions**, by `CategoryTheory.NatTrans.commShift_of_eq_conj`.
* `Stacks.Cohomology.DerivedPullbackTensor.derivedToTensorCommShiftOnKFlat` and
  `derivedToTensorCommShift₂`: **the obligation of [Stacks, Tag 079U], unconditionally.**
* `Stacks.Cohomology.DerivedPullbackTensor.leftComparisonCurryApp_commShift_of_kFlat` and
  `leftComparisonCommShift₂_of_flipApp'`: the two consumers in
  `PullbackTensorCommShiftAssembly.lean` with their `DerivedToTensorCommShift₂` hypothesis
  **discharged**.
* `Stacks.Cohomology.DerivedPullbackTensor.leftComparisonCommShift₂'`: **the first comparison of
  [Stacks, Tag 079U], unconditionally.**  Its remaining hypothesis
  `LeftComparisonCommShiftFlipApp` is supplied by
  `leftComparisonCommShiftFlipApp_of_derivedToTensor` of
  `PullbackTensorCommShiftAssemblyFlip.lean`, which asks only for the same shared obligation
  proved here, so the first comparison needs nothing further and `RightComparisonCommShift₂` is
  the whole of what the tag still needs.

The second comparison's two one-variable halves and the reduction of
`Stacks.Cohomology.DerivedPullbackTensor.RightComparisonCommShift₂` to exactly them live beside
that statement, in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPullback/PullbackTensorCommShiftComparisons.lean`;
the note there explains why.

## Implementation notes

**Where the kernel cost lies.**  The kernel's deterministic timeout is not caused by the
cancellation of the identity which `(DerivedCategory.Q ⋙ derivedBifunctor (tensorOn Z)).flip.obj _`
puts on the component of `CategoryTheory.ObjectProperty.liftCompιIso`, nor by the difference
between `derivedBifunctor` — a `CategoryTheory.Localization.lift₂` — and
`CochainComplex.KFlatBifunctor.totalBifunctor`, a `map₂HomologicalComplex`.  Instead:

* the crossing `(kFlatComplexesLeft (tensorOn Z)).ι.obj ((kFlatToLeftOn Z).obj K)` =
  `(kFlatComplexesOn Z).ι.obj K` **with nothing applied to it at all** is a kernel deterministic
  timeout when it is asked by `rfl`;
* the **same statement** closes at once when it is
  `CategoryTheory.ObjectProperty.ι_obj_lift_obj` instantiated by name;
* the crossing under `(DerivedCategory.Q ⋙ derivedBifunctor (tensorOn Z)).flip.obj _).obj` is no
  worse: pure `Functor.comp` unfolding under that functor is free, and the whole cancellation of
  the alleged culprit factor against `comparisonFirst`'s component closes in one application of
  `chainFourLiftCompEq` below.

So the cost is not `derivedBifunctor`, not the `.obj`-versus-`.map` position and not the number of
crossings; it is **`rfl` at this file's concrete instantiation**, whatever is or is not applied.
Every identification here is therefore an all-variables lemma applied by name, which is the
chapter's standing cure.

**Read the seconds below against the run-to-run spread.**  Three identical runs of one
declaration of this file span 137 s, 203 s and 161 s -- a factor of 1.48, wider than most gaps
between two different shapes -- so a difference of that size is noise, and a shape that exhausts
the 200000-heartbeat budget is judged by pass-or-fail alone, not by how long it takes to reach
the wall.

**Why the reduction of the second comparison is not in this file.**
`rightComparisonCommShift₂_of` is `CategoryTheory.NatTrans.CommShift₂.mk` applied to the two
one-variable halves and nothing else, and written in this file it is a kernel deterministic
timeout in every spelling; the spellings, and the cure, are in the docstring of that reduction in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPullback/PullbackTensorCommShiftComparisons.lean`,
where it and the two halves live beside `RightComparisonCommShift₂` itself.  The figures for
*this* file: `mk` takes seventeen arguments before
its two fields -- three types, three `Category`, the shift monoid and its `AddCommMonoid`, three
`HasShift`, the two bifunctors, the transformation, the setup and the two
`CategoryTheory.Functor.CommShift₂` data -- of which seven are instance arguments whose towers
the kernel re-validates one by one; a single
`NatTrans.CommShift ((Functor.curry.map (rightComparison f)).app K) ℤ` costs the kernel 31-34 s
here, which is what each half costs as a `def`, and the whole `mk` costs 143-160 s.  The statement
is where the cost is, not the proof: each half checks alone, in 76 s and 85 s, and only the
`.mk` holding both fails.

**Why the identity is assembled componentwise and in term mode.**  The two sides agree at every
object and the reassociations are the identity there, so `CategoryTheory.NatTrans.ext` after
`funext` reduces it to a composite of established facts: `whiskerLeft_curry_flipApp` and
`derivedToTensorNatTrans_app_eq_comparison` compute the left side, `thetaFirstLegOne_app_factors`
and `thetaFirstLegTwo_app` the two legs of the right one, `comparisonFirst_hom_app` gives the
second leg's value as the comparison at `(kFlatToLeftOn Z).obj K`, and `chainFourLiftCompEq`
cancels the first leg's three identities and both legs' lift crossings in one step, which is where
that object is identified with `(kFlatComplexesOn Z).ι.obj K`.  Term mode because
`rw` and `simp` re-check the goal at `implicit` transparency, where
`Stacks.SheafOfModules.Tensor.ringSheaf` of this ringed space's structure sheaf is not
type-correct.

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

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback

attribute [local instance] derivedTensorCommShift₂Int
  curriedComplexesDerivedTensor_commShift₂Int curriedComplexesTotal_commShift₂Int
  curryComplexesDerivedTensor_commShift₂Int curryComplexesTotal_commShift₂Int

attribute [local instance] kFlatQOn_isLocalization kFlatQLeftOn_isLocalization
attribute [local instance] kFlatToLeftOn_commShift

/-- **Cancel a four-factor chain's three identities and both legs' `liftCompιIso` crossings
against a morphism stated at the lifted spelling, rewriting both surviving factors in one step.**

Every object, functor and morphism is a variable, and the two spellings
`(P.lift F hF ⋙ P.ι).obj X` and `F.obj X` meet only here, where they are one delta step apart.
That is the whole point: asked at the concrete instantiation of this chapter the same
identification is a kernel deterministic timeout, asked abstractly it is free, and instantiating
this lemma by name costs nothing.  The second leg's crossing, the image under `G'` of the
component of `liftCompιIso` after `w`, is cancelled here too: `thetaFirstLegTwo_app` keeps it,
because cancelling it at the concrete instantiation is the same timeout.  `hv` and `hw` are taken
as hypotheses rather than rewritten at the call site because a `rw` there re-checks the goal at
`implicit` transparency. -/
private theorem chainFourLiftCompEq {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (P : ObjectProperty D) (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) (G G' : D ⥤ E) (X : C)
    {W : E} (v v' : W ⟶ G.obj (F.obj X))
    (w : G.obj ((P.lift F hF ⋙ P.ι).obj X) ⟶ G'.obj ((P.lift F hF ⋙ P.ι).obj X))
    (w' : G.obj (F.obj X) ⟶ G'.obj (F.obj X)) (hv : v = v') (hw : w = w') :
    (𝟙 W ≫ v ≫ 𝟙 (G.obj (F.obj X)) ≫ G.map ((P.liftCompιIso F hF).inv.app X)) ≫
        w ≫ G'.map ((P.liftCompιIso F hF).hom.app X) = v' ≫ w' := by
  have h : G.map ((P.liftCompιIso F hF).inv.app X) = 𝟙 (G.obj (F.obj X)) := G.map_id _
  have h' : G'.map ((P.liftCompιIso F hF).hom.app X) = 𝟙 (G'.obj (F.obj X)) := G'.map_id _
  rw [h, h', hv, hw]
  simp

variable (Z : RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

variable (P : (kFlatComplexesOn Z).FullSubcategory)

/-- The defining equation of `thetaFirst`, so that the two legs can be rewritten separately
without a `rfl` at this file's concrete spelling.

**Writing the unfolding out does not help.**  This `rfl` is one delta step of `thetaFirst`, and
the kernel spends 5-6 s on it.  The explicit `Eq.refl (thetaFirstLegOne Z P ≫ thetaFirstLegTwo Z P)`
is slower (11.9 s against 9.3 s, with the explicit term in the favourable first position of the
run), and so is splitting `thetaFirst_app`'s first step into a declaration of its own (9.0 s
against 7.3 s). -/
theorem thetaFirst_def : thetaFirst Z P = thetaFirstLegOne Z P ≫ thetaFirstLegTwo Z P := rfl

/-- **The component of `thetaFirst`**: the comparison of [Stacks, Tag 06YU] on the pair
`(K, P)`, conjugated by the comparison of the two derived tensor bifunctors — exactly the right
side of `derivedToTensorNatTrans_app_eq_comparison`.

The two legs are rewritten by their componentwise forms and then `chainFourLiftCompEq`
removes the first leg's three identities and both legs' lift crossings.  The second leg's value
is `comparisonFirst_hom_app` at `(kFlatToLeftOn Z).obj K`, the comparison at that object's
underlying complex `((kFlatToLeftOn Z).obj K).obj`, which the kernel identifies with the
comparison at `(kFlatComplexesOn Z).ι.obj K` by reducing the lift.  That is cheap because the
first complex is spelled one projection ahead of the second; the crossing the note at the end of
`PullbackTensorCommShiftOnKFlat.lean` finds unaffordable is between two spellings that reduce in
step.  Stated on its own, the identification is a kernel deterministic timeout, because its two
sides' types then meet that crossing inside the total complex of the target. -/
theorem thetaFirst_app (K : (kFlatComplexesOn Z).FullSubcategory) :
    (thetaFirst Z P).app K =
      (((derivedTensorIsoOn Z).app
            (DerivedCategory.Q.obj ((kFlatComplexesOn Z).ι.obj K))).app
          (DerivedCategory.Q.obj ((kFlatComplexesOn Z).ι.obj P))).inv ≫
        (CochainComplex.KFlatBifunctor.comparison (tensorOn Z)
          ((kFlatComplexesOn Z).ι.obj K) ((kFlatComplexesOn Z).ι.obj P)
          (Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat Z.sheaf K.2) P.2).hom :=
  (congrArg (fun t ↦ t.app K) (thetaFirst_def Z P)).trans
    ((NatTrans.comp_app (thetaFirstLegOne Z P) (thetaFirstLegTwo Z P) K).trans
      ((congrArg₂ (fun x y ↦ x ≫ y) (thetaFirstLegOne_app_factors Z P K)
          (thetaFirstLegTwo_app Z P K)).trans
        (chainFourLiftCompEq
          (CochainComplex.KFlatBifunctor.kFlatComplexesLeft (tensorOn Z))
          (kFlatComplexesOn Z).ι
          (fun P ↦ Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat Z.sheaf P.2)
          (DerivedCategory.Q ⋙
            (CochainComplex.KFlatBifunctor.derivedBifunctor (tensorOn Z)).flip.obj
              (DerivedCategory.Q.obj ((kFlatComplexesOn Z).ι.obj P)))
          ((CochainComplex.KFlatBifunctor.totalBifunctor (tensorOn Z)).flip.obj
            ((kFlatComplexesOn Z).ι.obj P) ⋙ DerivedCategory.Q) K _ _ _ _
          (derivedTensorFlipIsoOn_inv_app Z
            (DerivedCategory.Q.obj ((kFlatComplexesOn Z).ι.obj P))
            (DerivedCategory.Q.obj ((kFlatComplexesOn Z).ι.obj K)))
          (CochainComplex.KFlatBifunctor.comparisonFirst_hom_app (tensorOn Z)
            ((kFlatComplexesOn Z).ι.obj P) P.2 ((kFlatToLeftOn Z).obj K)))))

/-- **The transformation of the second condition is the conjugate of `thetaFirst`.**  Both
reassociations are the identity on every object, so this is `thetaFirst_app` against
`derivedToTensorNatTrans_app_eq_comparison` componentwise.  This is the one identity the second
condition of `DerivedToTensorCommShiftOnKFlat` was missing. -/
theorem thetaFirst_eq :
    Functor.whiskerLeft (kFlatComplexesOn Z).ι
        ((Functor.curry.map (derivedToTensorNatTrans Z)).flipApp
          ((kFlatComplexesOn Z).ι.obj P)) =
      (sourceFirstIso Z P).hom ≫ thetaFirst Z P ≫ (targetFirstIso Z P).inv :=
  NatTrans.ext (funext fun K ↦
    ((whiskerLeft_curry_flipApp Z P K).trans
        (derivedToTensorNatTrans_app_eq_comparison Z ((kFlatComplexesOn Z).ι.obj K)
          ((kFlatComplexesOn Z).ι.obj P) K.2 P.2)).trans
      (((conjFirst_app_factors Z P K).trans
          ((Category.id_comp _).trans (Category.comp_id _))).trans
        (thetaFirst_app Z P K)).symm)

/-- **The second of the two conditions of `DerivedToTensorCommShiftOnKFlat`**: at a fixed K-flat
complex in the second variable, the canonical map of [Stacks, Tag 06YU] restricted to the K-flat
complexes in the first is compatible with the shift.  Every shift input is proved in
`PullbackTensorCommShiftOnKFlat.lean`; `thetaFirst_eq` is what lets
`CategoryTheory.NatTrans.commShift_of_eq_conj` consume them.

**What this declaration and `thetaFirst_eq` cost.**  The kernel spends about 3 s here and 5-6 s
on `thetaFirst_eq`, the two declarations above costing 5-6 s and about 8 s.  With
`curryComplexesTotalIso` spelled through the reducible `tensorComplexBifunctorOn`, as described at
the end of this note, it spends 66-75 s here and 41-46 s on `thetaFirst_eq`, 85% of this section's
130 s, and no proof shape moves them; the rest of this note records the timings in that setting.
What separates these two from the declarations above is that they name a component of
`CategoryTheory.Functor.curryObjUncurryObjCompIso`, and these two do, through `targetFirstIso`
and `curryComplexesTotalIso`.

**The cost is in the two statements, not the chains.**  Restated with the proof replaced by a
single named application of the very same fact, this one still costs 17.3 s and `thetaFirst_eq`
17.0 s.  That much is the types and no proof can reach it.  What remains divides into the
`CategoryTheory.NatTrans.ext`-after-`funext` wrapper for `thetaFirst_eq` — with its body reduced
to two named applications it still costs 40.5 s against that 17.0 s floor, which is why rewriting
the `Eq.trans` chain inside it changes nothing — and, here, the four
`CategoryTheory.Functor.CommShift` instance arguments of `commShift_of_eq_conj`.

Eight alternative shapes, each timed in the same run as the form it replaces, give no
improvement:

* splitting the component identity out of `thetaFirst_eq`: 52.1 s against 42.1 s; splitting it
  into a left and a right half instead: 57.4 s against 44.4 s.  Each new statement re-pays 8-17 s
  for naming the conjugate, which exceeds what the split saves.
* the conjugate's two identities cancelled by one all-variables lemma applied to its morphism
  explicitly, in place of `Category.id_comp` and `Category.comp_id` with four inferred object
  arguments: 39.4 s against 42.0 s, inside the run-to-run spread.
* `Eq.trans` and `Eq.symm` written out in place of the projection notation: 41.3 s against
  41.3 s.
* this declaration in term mode with `letI` in place of the tactic block: 68.5 s against 66.7 s.
* `CategoryTheory.NatTrans.commShift_of_eq`, which takes two instance arguments where
  `commShift_of_eq_conj` takes four and two and one, with the junction assembled as a named step:
  that last step does fall to 53.6 s, but the step's own statement costs 34.6 s, so 88.2 s
  against 66.3 s.  With the junction assembled by an inline `haveI`, so that only one statement
  is paid for: 68.3 s against 66.0 s.
* `sourceFirstIso` and `targetFirstIso` given explicit types — this chapter's standing cure,
  a `def` with an explicit type fixing the spelling of its own type: 43.6 s and 75.2 s against
  46.3 s and 71.1 s, no change, and the ascribed `targetFirstIso`'s own shift compatibility then
  costs 96.4 s where the unascribed one is free.

That last comparison nevertheless locates the cost, in another file.  The
two ascriptions are structurally identical and differ only in which pinning isomorphism they
name, and they cost 1.2 s and 31.1 s.  `curryComplexesDerivedTensorIso` is a handwritten
`NatIso.ofComponents` over `Iso.refl`; `curryComplexesTotalIso` is `curryObjUncurryObjCompIso` of
`tensorComplexBifunctorOn`, which is an `abbrev`, hence reducible, so every kernel defeq through
it unfolds `Stacks.SheafOfModules.Tensor.sheafTensor`.  With the other side of
`curryComplexesTotalIso`, `totalComplexPair`, a reducible `def` of
`CategoryTheory.Functor.map₂HomologicalComplexReg`, these two declarations cost the figures at
the top of this note. -/
theorem commShift_flipApp_of_kFlat :
    NatTrans.CommShift (Functor.whiskerLeft (kFlatComplexesOn Z).ι
      ((Functor.curry.map (derivedToTensorNatTrans Z)).flipApp
        ((kFlatComplexesOn Z).ι.obj P))) ℤ := by
  have := sourceFirstIso_commShift Z P
  have := targetFirstIso_commShift Z P
  have := thetaFirst_commShift Z P
  exact NatTrans.commShift_of_eq_conj (sourceFirstIso Z P) (targetFirstIso Z P)
    (thetaFirst Z P) (thetaFirst_eq Z P)

/-- **The two one-variable conditions over the K-flat cochain complexes hold**, which is the
statement `PullbackTensorCommShiftOnKFlat.lean`'s `## Main results` advertises and did not
prove. -/
theorem derivedToTensorCommShiftOnKFlat : DerivedToTensorCommShiftOnKFlat Z :=
  ⟨commShift_app_of_kFlat Z, commShift_flipApp_of_kFlat Z⟩

/-- **`derivedToTensorNatTrans Z`, curried, is compatible with the shifts in each variable** — the
single obligation the two comparisons of [Stacks, Tag 079U] share, over *all* pairs of cochain
complexes and with no hypothesis.  This is `derivedToTensorCommShift₂_of_kFlat` applied to
`derivedToTensorCommShiftOnKFlat`. -/
theorem derivedToTensorCommShift₂ : DerivedToTensorCommShift₂ Z :=
  derivedToTensorCommShift₂_of_kFlat Z (derivedToTensorCommShiftOnKFlat Z)

/-! ### The two consumers of the obligation, now unconditional -/

section Comparison

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The `commShift_app` half of `LeftComparisonCommShift₂`, unconditionally**:
`leftComparisonCurryApp_commShift` with its `DerivedToTensorCommShift₂ Y` hypothesis discharged by
`derivedToTensorCommShift₂`. -/
theorem leftComparisonCurryApp_commShift_of_kFlat (K : CochainComplex (Modules Y) ℤ) :
    letI := curryComplexesPullbackOfTensor_commShift₂Int f
    letI := curryComplexesTotalPullback_commShift₂Int f
    NatTrans.CommShift ((Functor.curry.map (leftComparison f)).app K) ℤ :=
  leftComparisonCurryApp_commShift f K (derivedToTensorCommShift₂ Y)

/-- **`LeftComparisonCommShift₂` now rests on `LeftComparisonCommShiftFlipApp` alone.**  The
shared obligation of [Stacks, Tag 079U] is no longer a hypothesis of the reduction: what the first
comparison still owes is the mirror of `PullbackTensorCommShiftAssembly.lean` in the first
variable, and nothing else. -/
theorem leftComparisonCommShift₂_of_flipApp' (hflip : LeftComparisonCommShiftFlipApp f) :
    LeftComparisonCommShift₂ f :=
  leftComparisonCommShift₂_of_flipApp f (derivedToTensorCommShift₂ Y) hflip

/-- **The first comparison of [Stacks, Tag 079U] is compatible with the shifts in both variables,
unconditionally.**  Both hypotheses of
`Stacks.Cohomology.DerivedPullbackTensor.leftComparisonCommShift₂` are now discharged: the shared
obligation `DerivedToTensorCommShift₂ Y` by `derivedToTensorCommShift₂` above, and the
first-variable half `LeftComparisonCommShiftFlipApp f` by
`leftComparisonCommShiftFlipApp_of_derivedToTensor`, which takes only that same obligation.

So of the two comparisons of [Stacks, Tag 079U] the first owes nothing further, and
`Stacks.Cohomology.DerivedPullbackTensor.RightComparisonCommShift₂` is the whole of what the tag
still owes.

This is a step of the proof of 0B54, not a clause of any tag, so it carries no tag attribute. -/
theorem leftComparisonCommShift₂' : LeftComparisonCommShift₂ f :=
  leftComparisonCommShift₂ f (derivedToTensorCommShift₂ Y)

end Comparison

end Stacks.Cohomology.DerivedPullbackTensor

end
