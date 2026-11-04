module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorCommShiftDerivedToTensor
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorCommShiftLegs
public import StacksFrontier.CategoryTheory.Shift.CommShiftTwoDataTransport
import StacksCore.Tactic.StacksAttribute

/-!
# Assembling the first comparison of Tag 079U out of the one obligation and the first leg

`Stacks.Cohomology.DerivedPullbackTensor.LeftComparisonCommShift₂` is the shift compatibility of
`leftComparison`, curried, in each variable.  `leftComparison f` is

`Functor.whiskerRight (derivedToTensorNatTrans Y) Lf^*  ≫
  Functor.whiskerLeft (totalComplexPair _) (derivedPullbackNatTrans f)`

so each of its two one-variable components is a composite of two whiskerings: one of
`DerivedToTensorCommShift₂ Y` — the single obligation both comparisons of [Stacks, Tag 079U]
share — and one of `derivedPullbackNatTrans_commShift`, the first leg.  This file does that
assembly **one variable at a time**, in the second variable, and records exactly where it stops.

## Main results

* `Stacks.Cohomology.DerivedPullbackTensor.derivedToTensorPinnedApp` and
  `derivedToTensorPinnedApp_commShift`: **the one-variable component of `derivedToTensorNatTrans`
  at the pinned spelling, and its shift compatibility from `DerivedToTensorCommShift₂`.**  The
  obligation is stated at `Functor.curry.obj` of a functor on a product, whose commutation data
  are `CategoryTheory.Functor.CommShift₂.ofIsoInt`-transported; the pinned bifunctors
  `curriedComplexesDerivedTensor`/`curriedComplexesTotal` carry the untransported ones.  Crossing
  between the two costs nothing: `CategoryTheory.Functor.CommShift.ofIso_compatibility` says
  precisely that the transporting isomorphism is shift-compatible *for the transported datum*,
  and `CategoryTheory.NatTrans.CommShift.of_iso_inv` gives the other direction.
* `Stacks.Cohomology.DerivedPullbackTensor.leftComparisonPinnedApp`: **the four-factor chain for
  the second-variable component of `leftComparison`, at the pinned spelling** — two associators,
  the whiskering of the obligation by `Lf^*`, and the whiskering of the first leg.  That this
  typechecks is itself a measurement: the source and target of the component *are*
  `Q ⋙ (Rf^*E ⊗^𝐋 Q(-)) ⋙ Lf^*` and `Tot(K ⊗ -) ⋙ (f^* ⋙ Q)`, definitionally.
* `leftSecondAssocLeft_commShift`, `leftSecondObligation_commShift`,
  `leftSecondAssocRight_commShift`, `leftSecondLeg_commShift`: **each of the four factors is
  shift-compatible**, with a named reason, and `leftSecondAssocRightLeg_commShift` composes the
  last two.
* `leftSecondObligationAssocRightLeg_commShift` and
  `Stacks.Cohomology.DerivedPullbackTensor.leftComparisonPinnedApp_commShift`: **the second
  junction, and with it the whole chain.**  The second junction is the one that needed a transport
  of the commutation data rather than a seating, and
  `CategoryTheory.NatTrans.commShift_comp_of_eq_data` supplies it.
* `Stacks.Cohomology.DerivedPullbackTensor.leftComparisonPinnedApp_eq_curryApp`: **the chain is
  the second-variable component of the curried comparison**, conjugated by the two pinning
  isomorphisms — the bookkeeping identity that the chain is about the right transformation.
* `Stacks.Cohomology.DerivedPullbackTensor.leftComparisonCurryApp_commShift`: **the
  `commShift_app` field of `LeftComparisonCommShift₂`**, granted the one obligation.  Its
  companion field `commShift_flipApp` is the mirror of this file in the first variable and is not
  written.
* `Stacks.Cohomology.DerivedPullbackTensor.LeftComparisonCommShiftFlipApp` and
  `leftComparisonCommShift₂_of_flipApp`: **that missing mirror, named, and the reduction of
  `LeftComparisonCommShift₂` to it together with the shared obligation** — so what the first
  comparison of [Stacks, Tag 079U] still owes is exactly one statement.

## Implementation notes

**How the second junction closes.**  At that junction the same functor `Tot(K ⊗ -) ⋙ Q` is
reached twice:

* from the obligation's target, as `(curriedComplexesTotal Y).obj K`, whose datum is the
  `commShiftObj` **field** of `CategoryTheory.Functor.CommShift₂.postcompInt`;
* from `CategoryTheory.Functor.associator`, which asks for `CategoryTheory.Functor.CommShift.comp`
  of the two factors.

The field is *defined* to be that `comp`, so the two are definitionally equal — but
`CategoryTheory.Functor.CommShift₂.postcompInt` is an `instance` rather than an
`instance_reducible` definition, so instance search does not unfold it, and
`CategoryTheory.NatTrans.CommShift` takes the two data as instance arguments.  In both
directions:

* stated at `(curriedComplexesTotal Y).obj K`, `derivedToTensorPinnedApp_commShift` closes by
  `infer_instance` and the second junction fails under `infer_instance`;
* restated with the target ascribed as `(tensorComplexBifunctorOn Y).obj K ⋙ DerivedCategory.Q`,
  the second junction's two sides agree and `derivedToTensorPinnedApp_commShift` itself fails —
  the `ofIso_compatibility` bridge no longer matches.

So the cure cannot be a re-ascription; it is a transport.  The two data are *equal*
(`CategoryTheory.Functor.CommShift₂.postcomp_commShiftObj`, in
`StacksFrontier/CategoryTheory/Shift/CommShiftTwoDataTransport.lean`), and
`CategoryTheory.NatTrans.commShift_comp_of_eq_data` composes two shift-compatible transformations
across a junction whose middle datum is spelled two equal ways, discharging the equality once by
`rfl` instead of asking instance search for it.  With that the second junction closes in seconds
and the first and third were already closed here.

**The three remaining components, and one obstruction that is not a junction.**  The mirror of
this chain in the first variable is `commShift_flipApp`, and `rightComparison` has three factors
rather than two (`CategoryTheory.NatTrans.CommShift₂.whiskerRight_bifunctor` and
`whiskerLeft_bifunctor` at the first leg in each variable, the obligation at `X`, and
`mapBifunctorTotalBifunctorIso_commShift₂`).  At the level of the *commutation data* those
junctions are the same situation as this one: the flipped datum of `postcompInt` is
`postcomp_commShiftFlipObj`, and the data `whiskerRight_bifunctor`/`whiskerLeft_bifunctor` meet
are the `precomp₁`/`precomp₂` fields, which are `precomp₁_commShiftObj`,
`precomp₁_commShiftFlipObj`, `precomp₂_commShiftObj`, `precomp₂_commShiftFlipObj` in the same
file.  The passage from `rightComparison` to its inverse is
`CategoryTheory.NatTrans.CommShift₂.of_iso_invInt`.

**The chain is not *definitionally* the component of `Functor.curry.map (leftComparison f)`**, and
that was a separate obligation nobody had recorded.  `derivedToTensorPinnedApp` is *defined* as
the conjugate of `(Functor.curry.map (derivedToTensorNatTrans Z)).app K` by the two pinning
isomorphisms, so for it the crossing between the `Functor.curry.obj` spelling (whose data are
`CategoryTheory.Functor.CommShift₂.ofIsoInt`-transported) and the pinned one is free.
`leftComparisonPinnedApp` is instead defined as the four-factor chain, and the identity

`leftComparisonPinnedApp f K = ((curryComplexesPullbackOfTensorIso f).app K).hom ≫
    (Functor.curry.map (leftComparison f)).app K ≫ ((curryComplexesTotalPullbackIso f).app K).inv`

is **not** definitional: `rfl` fails on it, and a blanket `simp` after `ext L` does not terminate.
It is `leftComparisonPinnedApp_eq_curryApp`, and its whole content is that the chain applies `Lf^*`
to the identity-wrapped composite `𝟙 ≫ (derivedToTensorNatTrans Y).app (K, L) ≫ 𝟙` where the
curried comparison applies it to the bare component: one `CategoryTheory.Category.id_comp` under
`Lf^*`, stated in `derivedToTensorPinnedApp_app` and pasted by the three private bookkeeping
lemmas above, each of which has every object a variable.  With it,
`leftComparisonCurryApp_commShift` carries `leftComparisonPinnedApp_commShift` across the pinning
isomorphisms and **is the `commShift_app` field of
`Stacks.Cohomology.DerivedPullbackTensor.LeftComparisonCommShift₂`**.  What that proposition still
lacks is its other field, `commShift_flipApp` — the mirror of everything here in the first
variable, for which no chain is written.

**What this file costs, and what reading that identity backwards used to cost.**  Re-elaborated
and re-checked against unchanged imports, it took 11.5 and 11.8 min while the backwards reading of
`leftComparisonPinnedApp_eq_curryApp` was a lemma of its own and 10.4 and 10.3 min with
`eq_inv_comp_comp_hom` applied inline in `leftComparisonCurryApp_commShift`, the two contents
interleaved in a single series; every folded run came out ahead of every unfolded one.  That
removed lemma was stated once and used once, and the kernel validated its statement — which names
`Functor.curry.map (leftComparison f)` and both pinning isomorphisms — twice over, once to admit
it and once at the use site.

Where the rest of the time goes, by cutting the file short: up to and including
`leftComparisonPinnedApp_eq_curryApp` it is 6.2 min (2.6 elaborating, 3.6 in the kernel); adding
the backwards reading alone made it 7.2 min, so that one declaration was a minute by itself; the
last three declarations are the remaining 4.7 min.  So the fold is worth about a tenth of the file
and the floor beneath it is `leftComparisonPinnedApp_commShift` and
`leftComparisonCurryApp_commShift`, whose own statements name the `CommShift` data this file
exists to move; nothing short of changing those statements reaches it, and they are the content.

A warning about measuring this: a `--` comment is trivia, so adding one does not make Lean
re-elaborate what follows it — a probe has to change a real command, this module docstring for
instance, or the check comes back in under a second having reused everything.

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

/-! ### Two bookkeeping shapes, with every object a variable

Both are pure `CategoryTheory.Category.id_comp` arithmetic, and both are stated over an abstract
category with every object a variable so that the single identification they are applied across is
one `isDefEq` rather than a dozen keyed rewrites.

They are public rather than private because the mirror of this file in the first variable,
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPullback/PullbackTensorCommShiftAssemblyFlip.lean`,
applies the same three shapes to the flipped chain; a private lemma cannot be used in the body of
a public declaration there. -/

/-- A morphism wrapped in two identities, as it comes out of a chain whose associators are
identity-valued and whose pinning isomorphisms have `CategoryTheory.Iso.refl` components. -/
lemma id_comp_id {D : Type*} [Category D] {A B : D} (g : A ⟶ B) :
    𝟙 A ≫ g ≫ 𝟙 B = g := by
  simp

/-- Two factors of a chain, each wrapped in identities, against their composite wrapped in
identities — with the first factor replaced along a given equality. -/
lemma id_paste {D : Type*} [Category D] {A B C : D} {g g' : A ⟶ B} (u : B ⟶ C)
    (h : g = g') : 𝟙 A ≫ g ≫ 𝟙 B ≫ u = 𝟙 A ≫ (g' ≫ u) ≫ 𝟙 C := by
  rw [h]
  simp

/-- Reading a conjugation by two isomorphisms backwards. -/
lemma eq_inv_comp_comp_hom {D : Type*} [Category D] {A A' B B' : D}
    (a : A ≅ A') (b : B ≅ B') {x : A ⟶ B} {y : A' ⟶ B'}
    (h : x = a.hom ≫ y ≫ b.inv) : y = a.inv ≫ x ≫ b.hom := by
  rw [h]
  simp

/-! ### The obligation, read one variable at a time at the pinned spelling -/

section OneSpace

variable (Z : RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (K : CochainComplex (Modules Z) ℤ)

/-- **The component of `derivedToTensorNatTrans Z` in the second variable, at a fixed cochain
complex `K` in the first, written between the two pinned bifunctors.**  It is the curried
component conjugated by the two isomorphisms that pin the spellings, so its components are those
of `derivedToTensorNatTrans Z` and nothing is changed but the commutation data its shift
compatibility is read at. -/
def derivedToTensorPinnedApp :
    (curriedComplexesDerivedTensor Z).obj K ⟶ (curriedComplexesTotal Z).obj K :=
  ((curryComplexesDerivedTensorIso Z).app K).hom ≫
    (Functor.curry.map (derivedToTensorNatTrans Z)).app K ≫
      ((curryComplexesTotalIso Z).app K).inv

/-- **The components of `derivedToTensorPinnedApp` are those of `derivedToTensorNatTrans`.**  The
conjugation by the two pinning isomorphisms changes nothing: each of their components is
`CategoryTheory.Iso.refl`, so the component at `L` is the composite of `𝟙` with
`(derivedToTensorNatTrans Z).app (K, L)` and `𝟙`.

This is a step of the proof of `leftComparisonPinnedApp_eq_curryApp`, not a clause of any tag, so
it carries no tag attribute. -/
theorem derivedToTensorPinnedApp_app (L : CochainComplex (Modules Z) ℤ) :
    (derivedToTensorPinnedApp Z K).app L = (derivedToTensorNatTrans Z).app (K, L) :=
  id_comp_id ((derivedToTensorNatTrans Z).app (K, L))

/-- **The last two factors of the conjugate compose**: the curried component of the obligation in
the second variable, followed by the inverse of the pinning isomorphism of the target.  Its two
inputs are the `commShift_app` field of the obligation and
`CategoryTheory.Functor.CommShift.ofIso_compatibility` at the target's pinning isomorphism.

It is a named step rather than one junction of a single instance search so that the kernel checks
it apart from the first factor; see the implementation note on the kernel budget.

This is a step of the proof of 079U, not a clause of any tag, so it carries no tag attribute. -/
theorem derivedToTensorPinnedAppTail_commShift (h : DerivedToTensorCommShift₂ Z) :
    (letI := curriedComplexesTotal_commShift₂Int Z
    letI := curryComplexesDerivedTensor_commShift₂Int Z
    NatTrans.CommShift ((Functor.curry.map (derivedToTensorNatTrans Z)).app K ≫
      ((curryComplexesTotalIso Z).app K).inv) ℤ) := by
  letI := curriedComplexesTotal_commShift₂Int Z
  letI := curryComplexesDerivedTensor_commShift₂Int Z
  letI := curryComplexesTotal_commShift₂Int Z
  letI := Functor.CommShift.ofIso_compatibility ((curryComplexesTotalIso Z).app K) ℤ
  letI := (h : NatTrans.CommShift₂Int
    (Functor.curry.map (derivedToTensorNatTrans Z))).commShift_app K
  infer_instance

/-- **The one obligation of [Stacks, Tag 079U], read in the second variable at the pinned
data.**  `DerivedToTensorCommShift₂ Z` is stated at the `Functor.curry.obj` spelling, whose
commutation data are transported along `curryComplexesDerivedTensorIso` and
`curryComplexesTotalIso`; the two transporting isomorphisms are shift-compatible *for the
transported data* by `CategoryTheory.Functor.CommShift.ofIso_compatibility`, which is what makes
the crossing free in both directions.  The last two of the three factors are taken as the
already-proved `derivedToTensorPinnedAppTail_commShift`, so only one junction is left here. -/
theorem derivedToTensorPinnedApp_commShift (h : DerivedToTensorCommShift₂ Z) :
    (letI := curriedComplexesDerivedTensor_commShift₂Int Z
    letI := curriedComplexesTotal_commShift₂Int Z
    NatTrans.CommShift (derivedToTensorPinnedApp Z K) ℤ) := by
  letI := curriedComplexesDerivedTensor_commShift₂Int Z
  letI := curriedComplexesTotal_commShift₂Int Z
  letI := curryComplexesDerivedTensor_commShift₂Int Z
  letI := Functor.CommShift.ofIso_compatibility ((curryComplexesDerivedTensorIso Z).app K) ℤ
  letI := derivedToTensorPinnedAppTail_commShift Z K h
  unfold derivedToTensorPinnedApp
  infer_instance

end OneSpace

/-! ### The chain for the first comparison in the second variable -/

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (K : CochainComplex (Modules Y) ℤ)

/-- **The second-variable component of `leftComparison f`, as a four-factor chain between the
pinned bifunctors.**  Reading `leftComparison` one variable at a time turns its two whiskerings
into: the obligation whiskered by the derived pullback, and the first leg whiskered by
`Tot(K ⊗ -)`; the two associators are the reassociations those whiskerings need, and are the
identity on every object.

That this typechecks says that `(curriedComplexesPullbackOfTensor f).obj K` *is*
`Q ⋙ ((Rf^*E ⊗^𝐋 Q(-)) ⋙ Lf^*)` and `(curriedComplexesTotalPullback f).obj K` *is*
`Tot(K ⊗ -) ⋙ (f^* ⋙ Q)`, definitionally. -/
def leftComparisonPinnedApp :
    (curriedComplexesPullbackOfTensor f).obj K ⟶ (curriedComplexesTotalPullback f).obj K :=
  (Functor.associator DerivedCategory.Q
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).obj
        (DerivedCategory.Q.obj K)) (derivedPullback f)).inv ≫
    Functor.whiskerRight (derivedToTensorPinnedApp Y K) (derivedPullback f) ≫
      (Functor.associator ((tensorComplexBifunctor (Y := Y)).obj K) DerivedCategory.Q
        (derivedPullback f)).hom ≫
        Functor.whiskerLeft ((tensorComplexBifunctor (Y := Y)).obj K)
          (derivedPullbackNatTrans f)

/-- The first factor — the reassociation `Q ⋙ (T ⋙ Lf^*) ⟶ (Q ⋙ T) ⋙ Lf^*` — is
shift-compatible: `CategoryTheory.NatTrans.CommShift.associator` and
`CategoryTheory.NatTrans.CommShift.of_iso_inv`. -/
theorem leftSecondAssocLeft_commShift :
    letI := derivedPullback_commShift f
    letI : ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).obj
        (DerivedCategory.Q.obj K)).CommShift ℤ :=
      (derivedTensorCommShift₂Int Y).commShiftObj _
    NatTrans.CommShift (Functor.associator DerivedCategory.Q
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).obj
        (DerivedCategory.Q.obj K)) (derivedPullback f)).inv ℤ := by
  infer_instance

/-- The second factor — the obligation whiskered by the derived pullback — is shift-compatible:
`CategoryTheory.NatTrans.CommShift.whiskerRight` at `derivedToTensorPinnedApp_commShift`. -/
theorem leftSecondObligation_commShift (h : DerivedToTensorCommShift₂ Y) :
    (letI := curriedComplexesDerivedTensor_commShift₂Int Y
    letI := curriedComplexesTotal_commShift₂Int Y
    letI := derivedPullback_commShift f
    NatTrans.CommShift
      (Functor.whiskerRight (derivedToTensorPinnedApp Y K) (derivedPullback f)) ℤ) := by
  letI := derivedToTensorPinnedApp_commShift Y K h
  infer_instance

/-- The third factor — the reassociation `(Tot(K ⊗ -) ⋙ Q) ⋙ Lf^* ⟶ Tot(K ⊗ -) ⋙ (Q ⋙ Lf^*)` —
is shift-compatible, by `CategoryTheory.NatTrans.CommShift.associator`. -/
theorem leftSecondAssocRight_commShift :
    letI := derivedPullback_commShift f
    letI : ((tensorComplexBifunctor (Y := Y)).obj K).CommShift ℤ :=
      (inferInstance : (tensorComplexBifunctor (Y := Y)).CommShift₂Int).commShiftObj K
    NatTrans.CommShift (Functor.associator ((tensorComplexBifunctor (Y := Y)).obj K)
      DerivedCategory.Q (derivedPullback f)).hom ℤ := by
  infer_instance

/-- The fourth factor — the first leg whiskered by `Tot(K ⊗ -)` — is shift-compatible:
`CategoryTheory.NatTrans.CommShift.whiskerLeft` at `derivedPullbackNatTrans_commShift`. -/
theorem leftSecondLeg_commShift :
    letI := derivedPullback_commShift f
    letI : ((tensorComplexBifunctor (Y := Y)).obj K).CommShift ℤ :=
      (inferInstance : (tensorComplexBifunctor (Y := Y)).CommShift₂Int).commShiftObj K
    NatTrans.CommShift (Functor.whiskerLeft ((tensorComplexBifunctor (Y := Y)).obj K)
      (derivedPullbackNatTrans f)) ℤ := by
  letI := derivedPullback_commShift f
  letI : ((tensorComplexBifunctor (Y := Y)).obj K).CommShift ℤ :=
    (inferInstance : (tensorComplexBifunctor (Y := Y)).CommShift₂Int).commShiftObj K
  letI := derivedPullbackNatTrans_commShift f
  infer_instance

/-- **The third junction closes**: the last two factors compose, their common functor
`Tot(K ⊗ -) ⋙ (Q ⋙ Lf^*)` carrying the same `CategoryTheory.Functor.CommShift.comp` datum on
both sides.  The second junction does not; see the implementation note. -/
theorem leftSecondAssocRightLeg_commShift :
    letI := curriedComplexesTotalPullback_commShift₂Int f
    letI := derivedPullback_commShift f
    letI : ((tensorComplexBifunctor (Y := Y)).obj K).CommShift ℤ :=
      (inferInstance : (tensorComplexBifunctor (Y := Y)).CommShift₂Int).commShiftObj K
    NatTrans.CommShift ((Functor.associator ((tensorComplexBifunctor (Y := Y)).obj K)
      DerivedCategory.Q (derivedPullback f)).hom ≫
      Functor.whiskerLeft ((tensorComplexBifunctor (Y := Y)).obj K)
        (derivedPullbackNatTrans f)) ℤ := by
  letI := curriedComplexesTotalPullback_commShift₂Int f
  letI := derivedPullback_commShift f
  letI : ((tensorComplexBifunctor (Y := Y)).obj K).CommShift ℤ :=
    (inferInstance : (tensorComplexBifunctor (Y := Y)).CommShift₂Int).commShiftObj K
  letI := leftSecondAssocRight_commShift f K
  letI := leftSecondLeg_commShift f K
  infer_instance

/-- **The second junction closes too**, by transport of the commutation data rather than by
instance search: the datum the obligation delivers on `Tot(K ⊗ -) ⋙ Q` is the `commShiftObj`
field of `CategoryTheory.Functor.CommShift₂.postcompInt`, the datum the associator demands is
`CategoryTheory.Functor.CommShift.comp`, and the two are equal — by
`CategoryTheory.Functor.CommShift₂.postcomp_commShiftObj` — but not identified by instance search.
`CategoryTheory.NatTrans.commShift_comp_of_eq_data` pays that identification once, here. -/
theorem leftSecondObligationAssocRightLeg_commShift (h : DerivedToTensorCommShift₂ Y) :
    (letI := curriedComplexesDerivedTensor_commShift₂Int Y
    letI := curriedComplexesTotalPullback_commShift₂Int f
    letI := derivedPullback_commShift f
    letI : ((tensorComplexBifunctor (Y := Y)).obj K).CommShift ℤ :=
      (inferInstance : (tensorComplexBifunctor (Y := Y)).CommShift₂Int).commShiftObj K
    NatTrans.CommShift
      (Functor.whiskerRight (derivedToTensorPinnedApp Y K) (derivedPullback f) ≫
        ((Functor.associator ((tensorComplexBifunctor (Y := Y)).obj K) DerivedCategory.Q
            (derivedPullback f)).hom ≫
          Functor.whiskerLeft ((tensorComplexBifunctor (Y := Y)).obj K)
            (derivedPullbackNatTrans f))) ℤ) :=
  NatTrans.commShift_comp_of_eq_data _ _
    (leftSecondObligation_commShift f K h) (leftSecondAssocRightLeg_commShift f K)

/-- **The second-variable component of `leftComparison f`, at the pinned spelling, is
shift-compatible.**  All three junctions of the four-factor chain `leftComparisonPinnedApp` close,
so the one obligation `DerivedToTensorCommShift₂ Y` and the first leg are all that the component
needs.  The commutation data are the `commShiftObj` fields of
`curriedComplexesPullbackOfTensor_commShift₂Int` and `curriedComplexesTotalPullback_commShift₂Int`
at `K`, i.e. the ones the pinned bifunctors carry. -/
theorem leftComparisonPinnedApp_commShift (h : DerivedToTensorCommShift₂ Y) :
    (letI := curriedComplexesPullbackOfTensor_commShift₂Int f
    letI := curriedComplexesTotalPullback_commShift₂Int f
    NatTrans.CommShift (leftComparisonPinnedApp f K) ℤ) :=
  NatTrans.commShift_comp_of_eq_data _ _ (leftSecondAssocLeft_commShift f K)
    (leftSecondObligationAssocRightLeg_commShift f K h)

/-! ### The chain *is* the component of the curried comparison -/

/-- **The four-factor chain is the second-variable component of `Functor.curry.map
(leftComparison f)`, conjugated by the two pinning isomorphisms.**

Both sides are `Lf^*((derivedToTensorNatTrans Y).app (K, L)) ≫ (derivedPullbackNatTrans f).app
(Tot(K ⊗ L))` with identities interleaved: every component of `curryComplexesPullbackOfTensorIso`
and of `curryComplexesTotalPullbackIso` is `CategoryTheory.Iso.refl`, and both
`CategoryTheory.Functor.associator`s are identity-valued.  It is nonetheless *not* definitional —
`rfl` fails on it — because the chain applies `Lf^*` to the identity-wrapped composite
`𝟙 ≫ (derivedToTensorNatTrans Y).app (K, L) ≫ 𝟙` whereas the curried comparison applies it to the
bare component, and a functor's action on a composite is not definitionally its action on the
factors.  So the whole content is one `CategoryTheory.Category.id_comp` for
`derivedToTensorPinnedApp_app` under `Lf^*`, pasted by `id_paste`.

This is a step of the proof of `LeftComparisonCommShift₂`, not a clause of any tag, so it carries
no tag attribute. -/
theorem leftComparisonPinnedApp_eq_curryApp :
    leftComparisonPinnedApp f K =
      ((curryComplexesPullbackOfTensorIso f).app K).hom ≫
        (Functor.curry.map (leftComparison f)).app K ≫
          ((curryComplexesTotalPullbackIso f).app K).inv := by
  ext L
  exact id_paste
    ((derivedPullbackNatTrans f).app (((tensorComplexBifunctor (Y := Y)).obj K).obj L))
    (congrArg (fun v => (derivedPullback f).map v) (derivedToTensorPinnedApp_app Y K L))

/-- **The `commShift_app` half of `LeftComparisonCommShift₂`**: the second-variable component of
`Functor.curry.map (leftComparison f)` is shift-compatible, at the data
`curryComplexesPullbackOfTensor_commShift₂Int` and `curryComplexesTotalPullback_commShift₂Int`
that `LeftComparisonCommShift₂` is stated at, granted the one obligation
`DerivedToTensorCommShift₂ Y`.

The chain is shift-compatible at the *pinned* data by `leftComparisonPinnedApp_commShift`;
`eq_inv_comp_comp_hom` reads `leftComparisonPinnedApp_eq_curryApp` backwards to identify the
component with that chain conjugated by the two pinning isomorphisms, and those are
shift-compatible for the transported data by
`CategoryTheory.Functor.CommShift.ofIso_compatibility` and
`CategoryTheory.NatTrans.CommShift.of_iso_inv`, which is what makes the crossing free *once the
identity is available*.  `CategoryTheory.NatTrans.commShift_of_eq` consumes the identity.

What is still missing for `LeftComparisonCommShift₂` is the other field,
`commShift_flipApp`: the mirror of this whole development in the first variable, for which no
chain is written — there is no flipped companion of `derivedToTensorPinnedApp` and no flipped
four-factor chain.

This is a step of the proof of `LeftComparisonCommShift₂`, not a clause of any tag, so it carries
no tag attribute. -/
theorem leftComparisonCurryApp_commShift (h : DerivedToTensorCommShift₂ Y) :
    (letI := curryComplexesPullbackOfTensor_commShift₂Int f
    letI := curryComplexesTotalPullback_commShift₂Int f
    NatTrans.CommShift ((Functor.curry.map (leftComparison f)).app K) ℤ) := by
  letI := curryComplexesPullbackOfTensor_commShift₂Int f
  letI := curryComplexesTotalPullback_commShift₂Int f
  letI := curriedComplexesPullbackOfTensor_commShift₂Int f
  letI := curriedComplexesTotalPullback_commShift₂Int f
  letI := Functor.CommShift.ofIso_compatibility ((curryComplexesPullbackOfTensorIso f).app K) ℤ
  letI := Functor.CommShift.ofIso_compatibility ((curryComplexesTotalPullbackIso f).app K) ℤ
  letI := leftComparisonPinnedApp_commShift f K h
  exact NatTrans.commShift_of_eq
    (eq_inv_comp_comp_hom ((curryComplexesPullbackOfTensorIso f).app K)
      ((curryComplexesTotalPullbackIso f).app K) (leftComparisonPinnedApp_eq_curryApp f K))

/-! ### What `LeftComparisonCommShift₂` still needs, and nothing more -/

/-- **The other field of `LeftComparisonCommShift₂`, as a proposition**: the *first*-variable
components of `Functor.curry.map (leftComparison f)` — the transformations natural in `K` at a
fixed `L` — are shift-compatible, at the data `LeftComparisonCommShift₂` is stated at.

This is the mirror in the first variable of everything this file does in the second, and no part
of it is written: there is no flipped companion of `derivedToTensorPinnedApp`, and no flipped
four-factor chain.  At the level of the commutation data the mirror junctions are the same
situation as the ones closed here — `CategoryTheory.Functor.CommShift₂.postcomp_commShiftFlipObj`
in place of `postcomp_commShiftObj` — so the cure is available; it is the chain that is missing.

Naming it is what makes `leftComparisonCommShift₂_of_flipApp` a reduction of
`LeftComparisonCommShift₂` to one obligation rather than two. -/
def LeftComparisonCommShiftFlipApp : Prop :=
  letI := curryComplexesPullbackOfTensor_commShift₂Int f
  letI := curryComplexesTotalPullback_commShift₂Int f
  ∀ L : CochainComplex (Modules Y) ℤ,
    NatTrans.CommShift ((Functor.curry.map (leftComparison f)).flipApp L) ℤ

/-- **`LeftComparisonCommShift₂` reduces to the one obligation of [Stacks, Tag 079U] together
with its own flipped half, and to nothing else.**  Its `commShift_app` field is
`leftComparisonCurryApp_commShift`, which this file proves from `DerivedToTensorCommShift₂ Y` and
the first leg; its `commShift_flipApp` field is `LeftComparisonCommShiftFlipApp f`, for which no
chain is written.

So the first comparison of [Stacks, Tag 079U] is shift-compatible as soon as the shared obligation
and the mirror of this file in the first variable are available.

This is a step of the proof of 0B54, not a clause of any tag, so it carries no tag attribute. -/
theorem leftComparisonCommShift₂_of_flipApp (h : DerivedToTensorCommShift₂ Y)
    (hflip : LeftComparisonCommShiftFlipApp f) : LeftComparisonCommShift₂ f :=
  letI := curryComplexesPullbackOfTensor_commShift₂Int f
  letI := curryComplexesTotalPullback_commShift₂Int f
  { commShift_app K := leftComparisonCurryApp_commShift f K h
    commShift_flipApp L := hflip L }

end Stacks.Cohomology.DerivedPullbackTensor

end
