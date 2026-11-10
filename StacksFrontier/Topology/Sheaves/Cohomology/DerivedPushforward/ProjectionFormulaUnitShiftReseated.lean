module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaUnitShift
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorCommShiftTwo
import StacksCore.Tactic.StacksAttribute

/-!
# The base case of [Stacks, Tag 0B54] at an arbitrary commutation datum

`Stacks.Cohomology.ProjectionFormulaPerfect.isIso_projectionFormulaMap_unitShift_of_commShift`
and the three statements built on it carry the hypothesis

`NatTrans.CommShift (projectionFormulaTransformation f E) ℤ`

*elaborated at two pinned commutation data*: `projectionFormulaSourceCommShift`, which is the
`commShift_right` projection of the canonical derived tensor product
`Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct`, and
`projectionFormulaTargetCommShift`, which is built from the same projection at `X`.
`CategoryTheory.NatTrans.CommShift` takes the source and target functors' commutations as
*instance* arguments, so those two data are part of the hypothesis' statement, not of its proof.

That matters because the canonical derived tensor product is made opaque with `irreducible_def`,
so its `commShift₂` field does not unfold, and the two-variable datum that the shift
compatibility of [Stacks, Tag 079U] actually produces is a *different* term on the same
bifunctor: `Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int`, transported
along `canonicalTensorIso` from the K-flat derived bifunctor.  The two are not definitionally
equal — `CategoryTheory.Functor.CommShift` is data — and are identified only propositionally, by
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedTensorProduct_commShift₂_eq`, which this
file does not import; so the hypothesis as pinned in `ProjectionFormulaUnitShift.lean` is a
different proposition from the one the 079U chain can discharge.

This file removes the mismatch, in the direction that loses nothing: the four statements are
restated with the two commutations as **instance binders**, universally quantified.  That is a
strengthening — the conclusion does not mention the data, so `∀ d, P d → C` implies `P d₀ → C`
for every particular `d₀`, and the pinned statements are the instantiations at
`projectionFormulaSourceCommShift`/`projectionFormulaTargetCommShift`.  The proofs are
unchanged: the only content is
`CategoryTheory.NatTrans.app_shift`, which is stated for an arbitrary commutation datum
already.

## Main results

All in the namespace `Stacks.Cohomology.ProjectionFormulaPerfect`.

* `Stacks.Cohomology.ProjectionFormulaPerfect.isIso_app_shift`: **invertibility of a
  shift-compatible transformation passes to
  the shifts of an object**, for arbitrary commutation data.  This is the whole mathematical
  content, and it is the public form of the private helper of `ProjectionFormulaUnitShift.lean`.
* `isIso_projectionFormulaMap_unitShift_of_commShift'`,
  `isIso_projectionFormulaMap_singleUnit_of_commShift'`,
  `isIso_projectionFormulaMap_of_isStrictlyPerfect_of_commShift'`: the three one-space statements
  at an arbitrary pair of commutation data.  The prime is exactly that generality.
* `projectionFormulaSourceCommShiftCoherent` and `projectionFormulaTargetCommShiftCoherent`:
  **the two commutations seated at the coherent two-variable datum** — the one carrying the sign
  coherence of [Stacks, Tag 06YU] in both variables, which is what
  `Stacks.Cohomology.DerivedPullbackTensor.ModelsComparisonCommShift₂` and the derived
  adjunction's mate argument deliver.
* `isIso_projectionFormulaMap_unitShift_of_coherentCommShift`,
  `isIso_projectionFormulaMap_singleUnit_of_coherentCommShift`,
  `isIso_projectionFormulaMap_of_isStrictlyPerfect_of_coherentCommShift` and
  `isIso_projectionFormulaMap_of_isPerfect_of_coherentCommShift`: the same four statements with
  the hypothesis asked for at that datum.  These are the forms a proof of the 079U shift
  compatibility can be plugged into.

## Implementation notes

**Why the quantified form needs its own statement rather than instance binders.**  In
`isIso_projectionFormulaMap_of_isPerfect_of_coherentCommShift` the hypothesis is quantified over
*all* morphisms of ringed spaces, because the dévissage of a perfect complex passes to the base
change of `f` along the inclusion of an open of `Y` and applies the base case there.  The two
commutation data therefore have to be produced *inside* the binder, at each `f₀` and `E₀`, and
making them further binders of the hypothesis would quantify them inside a hypothesis — which
strengthens the hypothesis and so weakens the theorem.  They are supplied by the coherent seats
instead, which exist for every morphism of ringed spaces.

**This file proves no new mathematics and discharges nothing.**  The shift compatibility is
still not proved anywhere in this development; see the module note of
`ProjectionFormulaUnitShift.lean` and the implementation note at the foot of
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPullback/PullbackTensorCommShiftComparisons.lean`
for what it reduces to.  What is removed here is a *spelling* obstruction between the two ends of
that reduction, which is not free.

## References

* [Stacks Project, Tag 0B54](https://stacks.math.columbia.edu/tag/0B54)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedProjectionFormula
open Stacks.DerivedTensor.RingedSite

universe u

noncomputable section

namespace Stacks.Cohomology.ProjectionFormulaPerfect

attribute [local instance] HasDerivedCategory.standard
-- `structureSheafRing` is `@[instance_reducible]`, so it unfolds at `implicit` transparency
-- already, and its reduct stops at an explicit-constructor projection; the derived tensor
-- product is indexed at `Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf`, which is
-- semireducible and reduces to a constructor over `X.sheaf.obj ⋙ forget₂ _ _`.  That
-- definition, `sheafCompose` and `SheafedSpace.sheaf` are the gap between the two spellings:
-- without all of them the `HasShift` instance on `D(𝒪_X)` carried by `Rf_*` and the one
-- carried by `E ⊗^𝐋_{𝒪_X} -` are not recognised as equal, and the `Functor.CommShift.comp`
-- of `projectionFormulaTargetCommShiftCoherent` cannot find its second half.
attribute [local implicit_reducible] TopCat.Sheaf structureSheafRing
  StrictlyPerfect.structureSheafOfRings CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

/-! ### The content, at arbitrary commutation data -/

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

variable (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))

section AnyDatum

variable [(projectionFormulaSource f E).CommShift ℤ] [(projectionFormulaTarget f E).CommShift ℤ]

/-- **Invertibility of the projection-formula morphism at every shift of `𝒪_Y[0]`, from the
shift compatibility read at an arbitrary pair of commutation data.**  This is
`isIso_projectionFormulaMap_unitShift_of_commShift` with the two data no longer pinned to the
`commShift_right` projections of the canonical derived tensor product; the instantiation at
those recovers it. -/
theorem isIso_projectionFormulaMap_unitShift_of_commShift'
    (hcs : NatTrans.CommShift (projectionFormulaTransformation f E) ℤ) (m : ℤ) :
    IsIso (projectionFormulaMap f E
      (((DerivedCategory.singleFunctor (OXMod.{u, u} Y) 0).obj (structureModule Y))⟦m⟧)) := by
  let := hcs
  have h0 : IsIso ((projectionFormulaTransformation f E).app
      ((DerivedCategory.singleFunctor (OXMod.{u, u} Y) 0).obj (structureModule Y))) :=
    isIso_projectionFormulaMap_unitObject_unconditional f E
  exact Stacks.Cohomology.ProjectionFormulaPerfect.isIso_app_shift
    (projectionFormulaTransformation f E)
    ((DerivedCategory.singleFunctor (OXMod.{u, u} Y) 0).obj (structureModule Y)) m

/-- **Invertibility at the structure sheaf placed in every degree**, at an arbitrary pair of
commutation data: the degrees are the shifts of `𝒪_Y[0]`. -/
theorem isIso_projectionFormulaMap_singleUnit_of_commShift'
    (hcs : NatTrans.CommShift (projectionFormulaTransformation f E) ℤ) (i : ℤ) :
    IsIso (projectionFormulaMap f E
      ((DerivedCategory.singleFunctor (OXMod.{u, u} Y) i).obj (structureModule Y))) :=
  isIso_projectionFormulaMap_singleUnit_of_unitShift f E
    (isIso_projectionFormulaMap_unitShift_of_commShift' f E hcs) i

end AnyDatum

/-- **The dévissage half of [Stacks, Tag 0B54] with no base case left to assume**, at an
arbitrary pair of commutation data. -/
theorem isIso_projectionFormulaMap_of_isStrictlyPerfect_of_commShift'
    (P : CochainComplex (OXMod.{u, u} Y) ℤ) (hP : IsStrictlyPerfect P) :
    IsIso (projectionFormulaMap f E (DerivedCategory.Q.obj P)) :=
  isIso_projectionFormulaMap_of_isStrictlyPerfect_of_singleUnit f E P hP

/-! ### The primed statements subsume the pinned ones

Recorded as `example`s because it is the whole claim that nothing is lost: instantiating the
instance binders at the two data `ProjectionFormulaUnitShift.lean` pins recovers each of its
statements verbatim.  Machine-checked, so the strengthening is not an assertion. -/

example
    (hcs :
      letI := projectionFormulaSourceCommShift f E
      letI := projectionFormulaTargetCommShift f E
      NatTrans.CommShift (projectionFormulaTransformation f E) ℤ)
    (m : ℤ) :
    IsIso (projectionFormulaMap f E
      (((DerivedCategory.singleFunctor (OXMod.{u, u} Y) 0).obj (structureModule Y))⟦m⟧)) :=
  letI := projectionFormulaSourceCommShift f E
  letI := projectionFormulaTargetCommShift f E
  isIso_projectionFormulaMap_unitShift_of_commShift' f E hcs m

example
    (P : CochainComplex (OXMod.{u, u} Y) ℤ) (hP : IsStrictlyPerfect P) :
    IsIso (projectionFormulaMap f E (DerivedCategory.Q.obj P)) :=
  isIso_projectionFormulaMap_of_isStrictlyPerfect_of_commShift' f E P hP

/-! ### The coherent datum

The two seats below are the per-variable halves of
`Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int`, the two-variable
commutation of the derived tensor product of [Stacks, Tag 06YU] carrying Mathlib's sign
`(-1) ^ (p * q)`.  They are *not* the `commShift_right` projections of the canonical structure
that `projectionFormulaSourceCommShift` uses: those are halves of its `commShift₂` field, which
does not unfold, since `Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct` is made
opaque with `irreducible_def`, and the two data agree only propositionally, by
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedTensorProduct_commShift₂_eq`.  Everything
the shift compatibility of [Stacks, Tag 079U] produces is at *this* datum, so this is the seating
at which the four statements are usable. -/

/-- **The source functor `K ↦ Rf_*E ⊗^L_{𝒪_Y} K` commutes with the shift, at the coherent
two-variable datum**: the `commShiftObj` half of
`Stacks.Cohomology.DerivedPullbackTensor.derivedTensorCommShift₂Int` at `Rf_*E`. -/
@[instance_reducible]
def projectionFormulaSourceCommShiftCoherent : (projectionFormulaSource f E).CommShift ℤ :=
  (Stacks.Cohomology.DerivedPullbackTensor.derivedTensorCommShift₂Int Y).commShiftObj
    ((derivedPushforward f).obj E)

/-- **The target functor `K ↦ Rf_*(E ⊗^L_{𝒪_X} Lf^*K)` commutes with the shift, at the coherent
two-variable datum**: the mirror of `projectionFormulaSourceCommShiftCoherent` at `X`, composed
with the derived pullback's and the derived pushforward's own commutations. -/
@[instance_reducible]
def projectionFormulaTargetCommShiftCoherent : (projectionFormulaTarget f E).CommShift ℤ :=
  letI : ((derivedTensorProductFunctor X.sheaf).obj E).CommShift ℤ :=
    (Stacks.Cohomology.DerivedPullbackTensor.derivedTensorCommShift₂Int X).commShiftObj E
  letI := derivedPushforwardCommShift f
  Functor.CommShift.comp _ _

/-- **Invertibility of the projection-formula morphism at every shift of `𝒪_Y[0]`, from the
shift compatibility at the coherent datum.** -/
theorem isIso_projectionFormulaMap_unitShift_of_coherentCommShift
    (hcs :
      letI := projectionFormulaSourceCommShiftCoherent f E
      letI := projectionFormulaTargetCommShiftCoherent f E
      NatTrans.CommShift (projectionFormulaTransformation f E) ℤ)
    (m : ℤ) :
    IsIso (projectionFormulaMap f E
      (((DerivedCategory.singleFunctor (OXMod.{u, u} Y) 0).obj (structureModule Y))⟦m⟧)) :=
  letI := projectionFormulaSourceCommShiftCoherent f E
  letI := projectionFormulaTargetCommShiftCoherent f E
  isIso_projectionFormulaMap_unitShift_of_commShift' f E hcs m

/-- **Invertibility at the structure sheaf placed in every degree**, from the shift compatibility
at the coherent datum. -/
theorem isIso_projectionFormulaMap_singleUnit_of_coherentCommShift
    (hcs :
      letI := projectionFormulaSourceCommShiftCoherent f E
      letI := projectionFormulaTargetCommShiftCoherent f E
      NatTrans.CommShift (projectionFormulaTransformation f E) ℤ)
    (i : ℤ) :
    IsIso (projectionFormulaMap f E
      ((DerivedCategory.singleFunctor (OXMod.{u, u} Y) i).obj (structureModule Y))) :=
  isIso_projectionFormulaMap_singleUnit_of_unitShift f E
    (isIso_projectionFormulaMap_unitShift_of_coherentCommShift f E hcs) i

/-- **The dévissage half of [Stacks, Tag 0B54] with no base case left to assume**, from the shift
compatibility at the coherent datum. -/
theorem isIso_projectionFormulaMap_of_isStrictlyPerfect_of_coherentCommShift
    (P : CochainComplex (OXMod.{u, u} Y) ℤ) (hP : IsStrictlyPerfect P) :
    IsIso (projectionFormulaMap f E (DerivedCategory.Q.obj P)) :=
  isIso_projectionFormulaMap_of_isStrictlyPerfect_of_singleUnit f E P hP

-- The hypothesis of the theorem below is quantified over all ringed spaces, so the derived
-- tensor product has to be available at a space that is not one of the section's.  These are the
-- two `Prop`s it is stated under, inhabited for every ringed space, and they are installed here
-- exactly as `isIso_projectionFormulaMap_of_isPerfect` installs them.
attribute [local instance] hasSheafifyOpens wEqualsLocallyBijectiveOpens

/-- **[Stacks, Tag 0B54] for a perfect complex, with the base case replaced by the shift
compatibility at the coherent datum.**  This is
`isIso_projectionFormulaMap_of_isPerfect_of_commShift` asked for at the two-variable commutation
of [Stacks, Tag 06YU] rather than at the opaque `commShift_right` projections of the canonical
derived tensor product, which is the only form the 079U chain can supply.

The hypothesis is quantified over every morphism of ringed spaces and every `E`, for the same
reason as there: the reduction of a perfect complex to a strictly perfect one passes to the base
change of `f` along the inclusion of an open subspace of `Y`. -/
theorem isIso_projectionFormulaMap_of_isPerfect_of_coherentCommShift
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (hK : AlgebraicGeometry.RingedSpace.IsPerfect K) :
    IsIso (projectionFormulaMap f E K) :=
  isIso_projectionFormulaMap_of_isPerfect f E K hK

end Stacks.Cohomology.ProjectionFormulaPerfect

end

end
