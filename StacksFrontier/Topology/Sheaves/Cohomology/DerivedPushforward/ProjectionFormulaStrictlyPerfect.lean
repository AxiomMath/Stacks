module

public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormula
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaUnitShifts
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.ComponentwiseInvertibilityOnStrictlyPerfect

/-!
# The projection formula for a strictly perfect complex

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces, `E ∈ D(𝒪_X)`, and let `P` be a
strictly perfect complex of `𝒪_Y`-modules.  The projection-formula morphism of
[Stacks, Tag 0B53] is invertible for `P`, with no hypothesis: the base case of the dévissage,
invertibility at every shift of the structure sheaf of `Y` placed in every degree, is discharged
here from [Stacks, Tag 08EU] at every degree
(`Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_singleUnit_degree`, in
`ProjectionFormulaUnitShifts`) and `singleUnitShiftIso`.

## Main results

* `Stacks.Cohomology.ProjectionFormulaPerfect.isIso_projectionFormulaMap_of_isStrictlyPerfect`:
  the statement above.
* `isIso_projectionFormulaMap_of_isStrictlyPerfect_of_singleUnit`, in the same namespace: the
  same statement under the weaker base-case hypothesis, at the *unshifted* structure sheaf in
  each degree.  That hypothesis is now redundant — the theorem above assumes nothing — and the
  declaration is kept only because consumers hold it in that shape.
* `Stacks.Cohomology.ProjectionFormulaPerfect.projectionFormulaTransformation`: the
  projection-formula morphism read as a natural transformation of the two functors of `K` whose
  components it is.
* `Stacks.Cohomology.ProjectionFormulaPerfect.singleUnitShiftIso`: `𝒪_Y[i]⟦n⟧ ≅ 𝒪_Y[i - n]`, the
  isomorphism that makes the shifts in the base case redundant.
* `Stacks.Cohomology.ProjectionFormulaPerfect.singleUnitDegreeIso`: `𝒪_Y[0]⟦-i⟧ ≅ 𝒪_Y[i]`, the
  same isomorphism read in the direction that makes the *degrees* in the base case the shifts of
  one object, and `isIso_projectionFormulaMap_singleUnit_iff_unitShift`, which is the resulting
  equivalence of the two shapes of the base case.

## Implementation notes

This is the dévissage half of [Stacks, Tag 0B54]: "since the statement is true for
`K = K₁ ⊕ K₂` if and only if it is true for `K₁` and `K₂`, and by a simple argument involving
stupid truncations, we reduce to `K = 𝒪_Y[n]`".  What is carried, and named in the attribute's
clause, is the case `K = 𝒪_Y[n]` itself and the localization on `Y` that reduces a perfect
complex to a strictly perfect one.

The dévissage is
`Stacks.Cohomology.StrictlyPerfectInvertibility.isIso_app_of_isStrictlyPerfect`, which needs the
projection-formula morphism as a natural transformation between *exact* functors
`D(𝒪_Y) ⥤ D(𝒪_Y)`:

* naturality in `K` is the lemma `projectionFormulaMap_natural_right` of
  `Stacks.Cohomology.DerivedProjectionFormula`;
* the source functor `- ↦ Rf_*E ⊗^L_{𝒪_Y} -` is exact because tensoring with a fixed object in
  the second variable is, which is the `commShift_right` and `exact_right` data of the derived
  tensor product of [Stacks, Tag 06YU];
* the target functor `- ↦ Rf_*(E ⊗^L_{𝒪_X} Lf^*-)` is a composite of three exact functors:
  `Lf^*` by [Stacks, Tag 06YJ], the tensor factor again by Tag 06YU, and `Rf_*` because it is
  the right adjoint of an exact functor in the derived adjunction of [Stacks, Tag 079W].

Three spellings of the structure sheaf of rings of a ringed space meet here:
`structureSheafRing Y`, in which Tag 0B53 is stated, `StrictlyPerfect.structureSheafOfRings Y`,
in which the strictly perfect vocabulary of Tag 08C4 is, and
`Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf`, at which the derived tensor product of
Tag 06YU is indexed.  They are the same sheaf of rings, but all three are semireducible, so a
goal mixing them is not type-correct at `implicit` transparency; as in
`StacksFrontier/Topology/Sheaves/Cohomology/PerfectComplexes/ClosedSupportPerfect.lean`, all three
are made reducible at that transparency by `attribute [local implicit_reducible]` rather than by
relaxing transparency globally.  The third is what makes the two `HasShift` instances on
`D(𝒪_X)` — the one `Rf_*` is stated against and the one `E ⊗^𝐋_{𝒪_X} -` is — recognised as
equal, and so the one that makes the exactness section's `Functor.CommShift.comp` find its two
halves.

## References

* [Stacks Project, Tag 0B54](https://stacks.math.columbia.edu/tag/0B54)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 08C4](https://stacks.math.columbia.edu/tag/08C4)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
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
attribute [local implicit_reducible] structureSheafRing
  StrictlyPerfect.structureSheafOfRings CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The functor `K ↦ Rf_*E ⊗^L_{𝒪_Y} K`, the source of the projection-formula morphism. -/
abbrev projectionFormulaSource
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) :=
  (derivedTensorProductFunctor Y.sheaf).obj ((derivedPushforward f).obj E)

/-- The functor `K ↦ Rf_*(E ⊗^L_{𝒪_X} Lf^*K)`, the target of the projection-formula
morphism. -/
abbrev projectionFormulaTarget
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) :=
  derivedPullback f ⋙ (derivedTensorProductFunctor X.sheaf).obj E ⋙ derivedPushforward f

/-- **The projection-formula morphism of [Stacks, Tag 0B53] as a natural transformation.**  Its
component at `K` is `Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap f E K`, and
its naturality is `projectionFormulaMap_natural_right`. -/
@[stacks 0B53 "the map as a natural transformation in the target complex"]
def projectionFormulaTransformation
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    projectionFormulaSource f E ⟶ projectionFormulaTarget f E where
  app := projectionFormulaMap f E
  naturality _ _ k := projectionFormulaMap_natural_right f E k

/-- The component of `projectionFormulaTransformation f E` at `K` is
`projectionFormulaMap f E K`. -/
@[simp]
lemma projectionFormulaTransformation_app
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    (projectionFormulaTransformation f E).app K = projectionFormulaMap f E K :=
  rfl

section Exactness

variable (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))

/-- The target functor `K ↦ Rf_*(E ⊗^L_{𝒪_X} Lf^*K)` commutes with the shift: it is a composite
of three functors that do. -/
@[instance_reducible]
def projectionFormulaTargetCommShift : (projectionFormulaTarget f E).CommShift ℤ :=
  letI : ((derivedTensorProductFunctor X.sheaf).obj E).CommShift ℤ :=
    (canonicalDerivedTensorProduct X.sheaf).commShift_right _
  letI := derivedPushforwardCommShift f
  Functor.CommShift.comp _ _

/-- The target functor is exact: it is a composite of three exact functors. -/
theorem projectionFormulaTarget_isTriangulated :
    letI := projectionFormulaTargetCommShift f E
    (projectionFormulaTarget f E).IsTriangulated :=
  letI : ((derivedTensorProductFunctor X.sheaf).obj E).CommShift ℤ :=
    (canonicalDerivedTensorProduct X.sheaf).commShift_right _
  letI : ((derivedTensorProductFunctor X.sheaf).obj E).IsTriangulated :=
    (canonicalDerivedTensorProduct X.sheaf).exact_right _
  letI := derivedPushforwardCommShift f
  letI := derivedPushforward_isTriangulated f
  letI : ((derivedTensorProductFunctor X.sheaf).obj E ⋙ derivedPushforward f).CommShift ℤ :=
    Functor.CommShift.comp _ _
  inferInstance

/-- **The projection formula for a strictly perfect complex.**  For a morphism of ringed spaces
`f`, an arbitrary `E ∈ D(𝒪_X)` and a strictly perfect complex `P` of `𝒪_Y`-modules, the
projection-formula morphism

`Rf_*E ⊗^L_{𝒪_Y} P ⟶ Rf_*(E ⊗^L_{𝒪_X} Lf^*P)`

of [Stacks, Tag 0B53] is invertible.  The proof is the dévissage of the source's proof of
[Stacks, Tag 0B54] — direct sums, split retracts and stupid truncations — from the base case
`𝒪_Y[i]⟦n⟧`, which is `isIso_projectionFormulaMap_singleUnit_degree` together with the degree
identification `𝒪_Y[i]⟦n⟧ ≅ 𝒪_Y[i-n]` of `DerivedCategory.singleFunctors`.  The statement for a
perfect complex is
`Stacks.Cohomology.ProjectionFormulaPerfect.isIso_projectionFormulaMap_of_isPerfect`. -/
theorem isIso_projectionFormulaMap_of_isStrictlyPerfect
    (P : CochainComplex (OXMod.{u, u} Y) ℤ) (hP : IsStrictlyPerfect P) :
    IsIso (projectionFormulaMap f E (DerivedCategory.Q.obj P)) :=
  isIso_projectionFormulaMap_of_iso_right f E
    ((shiftFunctorZero _ ℤ).app (DerivedCategory.Q.obj P))
    (Stacks.Cohomology.StrictlyPerfectInvertibility.isIso_app_of_isStrictlyPerfect
      (projectionFormulaSource f E) (projectionFormulaTarget f E)
      ((canonicalDerivedTensorProduct Y.sheaf).commShift_right _)
      (projectionFormulaTargetCommShift f E)
      ((canonicalDerivedTensorProduct Y.sheaf).exact_right _)
      (projectionFormulaTarget_isTriangulated f E)
      (projectionFormulaTransformation f E)
      (fun i n => isIso_projectionFormulaMap_of_iso_right f E
        ((((DerivedCategory.singleFunctors (OXMod.{u, u} Y)).shiftIso n (i - n) i
          (by omega)).app (structureModule Y)).symm)
        (isIso_projectionFormulaMap_singleUnit_degree f E (i - n)))
      P hP 0)

/-! ### The shifts in the base case are redundant -/

/-- **A shift of the structure sheaf placed in a degree is the structure sheaf placed in another
degree**: `𝒪_Y[i]⟦n⟧ ≅ 𝒪_Y[i - n]`.

It is the component at the structure sheaf of the shift isomorphism carried by the
`CategoryTheory.SingleFunctors` structure that `DerivedCategory.singleFunctors` installs on the
family of single functors; no computation is involved, only the choice of degrees. -/
def singleUnitShiftIso (i n : ℤ) :
    (((DerivedCategory.singleFunctor (OXMod.{u, u} Y) i).obj (structureModule Y))⟦n⟧) ≅
      (DerivedCategory.singleFunctor (OXMod.{u, u} Y) (i - n)).obj (structureModule Y) :=
  ((DerivedCategory.singleFunctors (OXMod.{u, u} Y)).shiftIso n (i - n) i (by omega)).app
    (structureModule Y)

/-- **The shifts of the structure sheaf carry no information beyond its degrees.**  If the
projection-formula morphism of [Stacks, Tag 0B53] is invertible at the structure sheaf of `Y`
placed in every degree, then it is invertible at every shift of the structure sheaf placed in
every degree.

This is `singleUnitShiftIso` together with `CategoryTheory.NatTrans.isIso_app_iff_of_iso`, and it
uses nothing about the projection-formula morphism — in particular no compatibility with the
shift, which is exactly what is not available for it. -/
theorem isIso_projectionFormulaMap_singleUnit_shift
    (hunit : ∀ i : ℤ, IsIso (projectionFormulaMap f E
      ((DerivedCategory.singleFunctor (OXMod.{u, u} Y) i).obj (structureModule Y))))
    (i n : ℤ) :
    IsIso (projectionFormulaMap f E
      (((DerivedCategory.singleFunctor (OXMod.{u, u} Y) i).obj (structureModule Y))⟦n⟧)) :=
  isIso_projectionFormulaMap_of_iso_right f E (singleUnitShiftIso (Y := Y) i n).symm (hunit (i - n))

/-- **The dévissage half of [Stacks, Tag 0B54], with its base case asked for only at the
unshifted structure sheaf in each degree.**  This is
`isIso_projectionFormulaMap_of_isStrictlyPerfect` with the shifts removed from the hypothesis by
`isIso_projectionFormulaMap_singleUnit_shift`.

The two hypotheses are equivalent — the families of objects `{𝒪_Y[i]⟦n⟧}` and `{𝒪_Y[j]}` coincide
up to isomorphism, and `singleUnitShiftIso` is that coincidence — so nothing is weakened and
nothing is gained in strength.  What changes is the *shape* the base case is asked for in, and
with it which computation discharges it.  Over the two parameters the hypothesis invites being
met by invertibility at `𝒪_Y[0]` together with a `CategoryTheory.NatTrans.CommShift` for the
projection-formula morphism; that compatibility is a shift compatibility of the comparison of
[Stacks, Tag 079U], which `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso` —
built by `CategoryTheory.Localization.liftNatIso` — does not come with, and which is not proved
anywhere in this development.  Over the one parameter the hypothesis asks instead for
invertibility at the structure sheaf in each degree, uniformly in the degree, and `𝒪_Y[j]` is a
K-flat complex with flat terms, so the comparison of [Stacks, Tag 079U] at it is computed
degreewise and no derived-category shift compatibility is involved. -/
theorem isIso_projectionFormulaMap_of_isStrictlyPerfect_of_singleUnit
    (hunit : ∀ i : ℤ, IsIso (projectionFormulaMap f E
      ((DerivedCategory.singleFunctor (OXMod.{u, u} Y) i).obj (structureModule Y))))
    (P : CochainComplex (OXMod.{u, u} Y) ℤ) (hP : IsStrictlyPerfect P) :
    IsIso (projectionFormulaMap f E (DerivedCategory.Q.obj P)) :=
  isIso_projectionFormulaMap_of_isStrictlyPerfect f E P hP

/-! ### The degrees in the base case are the shifts of one object -/

/-- **The structure sheaf placed in the degree `i` is the shift by `-i` of the structure sheaf
placed in degree zero**: `𝒪_Y[0]⟦-i⟧ ≅ 𝒪_Y[i]`.

Like `singleUnitShiftIso` this is a component of the shift isomorphism carried by the
`CategoryTheory.SingleFunctors` structure of `DerivedCategory.singleFunctors`, at the degrees
that run the identification in the direction which *produces* a degree rather than removing a
shift.  The two together say that the two-parameter family `{𝒪_Y[i]⟦n⟧}` and the one-parameter
family `{𝒪_Y[0]⟦m⟧}` consist of the same objects up to isomorphism. -/
def singleUnitDegreeIso (i : ℤ) :
    (((DerivedCategory.singleFunctor (OXMod.{u, u} Y) 0).obj (structureModule Y))⟦(-i : ℤ)⟧) ≅
      (DerivedCategory.singleFunctor (OXMod.{u, u} Y) i).obj (structureModule Y) :=
  ((DerivedCategory.singleFunctors (OXMod.{u, u} Y)).shiftIso (-i) i 0 (by omega)).app
    (structureModule Y)

/-- **The degrees of the structure sheaf carry no information beyond the shifts of one object.**
If the projection-formula morphism of [Stacks, Tag 0B53] is invertible at every shift of the
structure sheaf of `Y` placed in degree zero, then it is invertible at the structure sheaf placed
in every degree.

This is `singleUnitDegreeIso` together with `CategoryTheory.NatTrans.isIso_app_iff_of_iso`, and
like `isIso_projectionFormulaMap_singleUnit_shift` it uses nothing about the projection-formula
morphism. -/
theorem isIso_projectionFormulaMap_singleUnit_of_unitShift
    (hunit : ∀ m : ℤ, IsIso (projectionFormulaMap f E
      (((DerivedCategory.singleFunctor (OXMod.{u, u} Y) 0).obj (structureModule Y))⟦m⟧)))
    (i : ℤ) :
    IsIso (projectionFormulaMap f E
      ((DerivedCategory.singleFunctor (OXMod.{u, u} Y) i).obj (structureModule Y))) :=
  isIso_projectionFormulaMap_of_iso_right f E (singleUnitDegreeIso (Y := Y) i) (hunit (-i))

/-- **The base case of the dévissage is one statement about the shifts of one object.**  The
two-parameter family `𝒪_Y[i]⟦n⟧` that `isIso_projectionFormulaMap_of_isStrictlyPerfect` asks for
and the one-parameter family `𝒪_Y[0]⟦m⟧` request invertibility at the same objects up to
isomorphism, so the two hypotheses are equivalent and neither side is weaker.

Both sides are now theorems, not obligations:
`Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_unitShift_unconditional`
([Stacks, Tag 08EU] at `𝒪_Y[0]⟦m⟧`) proves the right-hand side for every `m` with no hypothesis,
and `isIso_projectionFormulaMap_of_isStrictlyPerfect` above therefore assumes nothing.  What the
right-hand side buys is that it names the shape in which that was discharged: invertibility at
each shift of one object, each shift handled on its own.

Nothing here transports invertibility *along* a shift.  That reading — invertibility at an object
inherited by its shifts — is a `CategoryTheory.NatTrans.CommShift` for the projection-formula
morphism, hence a shift compatibility of the comparison of [Stacks, Tag 079U], and that datum is
indeed absent from this development; see the note on
`isIso_projectionFormulaMap_of_isStrictlyPerfect_of_singleUnit` and the head of
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/ProjectionFormulaUnitShifts.lean`,
which records that the route taken there needs only the `CommShift₂` of the *bifunctor* of
[Stacks, Tag 06YU] and the right unit constraint of [Stacks, Tag 0FPT] as a natural isomorphism,
both of which are available. -/
theorem isIso_projectionFormulaMap_singleUnit_iff_unitShift :
    (∀ i n : ℤ, IsIso (projectionFormulaMap f E
        (((DerivedCategory.singleFunctor (OXMod.{u, u} Y) i).obj (structureModule Y))⟦n⟧))) ↔
      ∀ m : ℤ, IsIso (projectionFormulaMap f E
        (((DerivedCategory.singleFunctor (OXMod.{u, u} Y) 0).obj (structureModule Y))⟦m⟧)) :=
  ⟨fun h m => h 0 m, fun h i n =>
    isIso_projectionFormulaMap_singleUnit_shift f E
      (isIso_projectionFormulaMap_singleUnit_of_unitShift f E h) i n⟩

end Exactness

end Stacks.Cohomology.ProjectionFormulaPerfect

end

end
