module

public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectPushforward
public import StacksFrontier.AlgebraicGeometry.Perfect.TensorFinitelyPresentedPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.AlgebraicFlatness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UnitFinitePresentationSite
import StacksCore.Tactic.StacksAttribute

/-!
# The complexes of Stacks 0B91, as complexes Stacks 0A1H admits

Let `f : X ⟶ S` be a proper morphism of finite presentation. [Stacks, Tag 0B91] has two
clauses, each asserting two things:

1. if `E ∈ D(𝒪_X)` is perfect and `f` is flat, then `Rf_*E` is a perfect object of `D(𝒪_S)` and
   its formation commutes with arbitrary base change;
2. if `𝒢` is an `𝒪_X`-module of finite presentation, flat over `S`, then `Rf_*𝒢` is a perfect
   object of `D(𝒪_S)` and its formation commutes with arbitrary base change.

The source's proof is one line: both are special cases of [Stacks, Tag 0A1H], clause (1) taken
with `𝒢^•` equal to `𝒪_X` in degree `0` and clause (2) taken with `E = 𝒪_X` and `𝒢^•` equal to
`𝒢` in degree `0`. This file produces the two complexes and proves that each satisfies
`AlgebraicGeometry.FlatProperSupportFinitelyPresented`, the hypothesis of
[Stacks, Tag 0A1H] on `𝒢^•`. The base-change halves of the two clauses are
`AlgebraicGeometry.ProperFlatBaseChange.isIso_derivedBaseChangeMap_of_isPerfect` and
`…ProperFlatBaseChange.isIso_derivedBaseChangeComp_singleDegree_of_isFinitePresentation`.

## Main definitions

* `AlgebraicGeometry.ProperFlatBaseChange.singleDegreeComplex` is an `𝒪_X`-module placed in
  degree zero, as a complex in the spelling `AlgebraicGeometry.Scheme.Modules` of the category
  of `𝒪_X`-modules that the base-change map of [Stacks, Tag 08HY] is written at.

## Main results

* `AlgebraicGeometry.ProperFlatBaseChange.flatProperSupportFinitelyPresented_singleDegreeComplex`
  is the whole content of the source's reduction: for a proper `f` and an `𝒪_X`-module of finite
  presentation, flat over `S`, the complex with that module in degree zero is bounded, finitely
  presented and flat over `S` in each degree, and supported on `⊤`, which is proper over `S`
  because `f` is.
* `AlgebraicGeometry.ProperFlatBaseChange.flatProperSupportFinitelyPresented_structure` is its
  instance at `𝒪_X`, for `f` flat.

## References

* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Stacks Project, Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H)
* [Stacks Project, Tag 0A1D](https://stacks.math.columbia.edu/tag/0A1D)
* [Stacks Project, Tag 0B6F](https://stacks.math.columbia.edu/tag/0B6F)
* [Stacks Project, Tag 0CYM](https://stacks.math.columbia.edu/tag/0CYM)
* [Stacks Project, Tag 02N3](https://stacks.math.columbia.edu/tag/02N3)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 01BW](https://stacks.math.columbia.edu/tag/01BW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedPullbackTensor (pullbackComplex)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open Stacks.Cohomology.PerfectPushforward (isFlatOver_structureModule isProperOver_top_of_isProper)

universe u

namespace AlgebraicGeometry.ProperFlatBaseChange

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback StrictlyPerfect.structureSheafOfRings
  StrictlyPerfect.structureModule

/-! ### A module in degree zero -/

/-- An `𝒪_X`-module placed in degree zero, as a complex of `𝒪_X`-modules. This is the complex
`𝒢^•` of [Stacks, Tag 0A1H] in the two cases [Stacks, Tag 0B91] needs, and it is written at
`AlgebraicGeometry.Scheme.Modules`, which is the spelling the base-change map of
[Stacks, Tag 08HY] is carried at. -/
public abbrev singleDegreeComplex {X : Scheme.{u}} (M : X.Modules) :
    CochainComplex X.Modules ℤ :=
  (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj M

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **Every term of `M` in degree zero is of finite presentation** when `M` is: in degree zero
the term is `M` itself and in every other degree it is a zero object, which is of finite
presentation by `AlgebraicGeometry.isFinitePresentation_of_isZero`. -/
public theorem isFinitePresentation_singleDegreeComplex (M : X.Modules)
    (hM : M.IsFinitePresentation) (i : ℤ) :
    ((singleDegreeComplex M).X i).IsFinitePresentation := by
  by_cases hi : i = 0
  · subst hi
    exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) M).symm hM
  · exact isFinitePresentation_of_isZero _
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M i hi)

/-- **Every term of `M` in degree zero is quasi-coherent** when `M` is of finite presentation,
by [Stacks, Tag 01BW]. -/
public theorem isQuasicoherent_singleDegreeComplex (M : X.Modules)
    (hM : M.IsFinitePresentation) (i : ℤ) :
    ((singleDegreeComplex M).X i).IsQuasicoherent :=
  have := isFinitePresentation_singleDegreeComplex M hM i
  isQuasicoherent_of_isFinitePresentation ((singleDegreeComplex M).X i)

/-- **Every term of `M` in degree zero is flat over `S`** when `M` is: in degree zero the term
is `M` itself, and in every other degree it is a zero object, flat over any base by
`AlgebraicGeometry.isFlatOver_of_isZero`. -/
public theorem isFlatOver_singleDegreeComplex (M : X.Modules)
    (hM : IsFlatOver f.toLRSHom.toShHom M) (i : ℤ) :
    IsFlatOver f.toLRSHom.toShHom ((singleDegreeComplex M).X i) := by
  by_cases hi : i = 0
  · subst hi
    rw [isFlatOver_iff_of_moduleIso f.toLRSHom.toShHom
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) M)]
    exact hM
  · exact isFlatOver_of_isZero f _
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M i hi)

/-- **The reduction of [Stacks, Tag 0B91] to [Stacks, Tag 0A1H].** For a proper `f` and an
`𝒪_X`-module `M` of finite presentation, flat over `S`, the complex with `M` in degree zero is
a complex of the kind [Stacks, Tag 0A1H] admits: it is bounded (it is concentrated in degree
zero), its terms are of finite presentation and flat over `S`, and all of them are supported on
`⊤`, which is proper over `S` because `f` is
(`Stacks.Cohomology.PerfectPushforward.isProperOver_top_of_isProper`).

Both clauses of [Stacks, Tag 0B91] are an instance of this: clause (1) at `M = 𝒪_X`, whose
finite presentation is [Stacks, Tag 03DL] and whose flatness over `S` is flatness of `f`
([Stacks, Tag 02N3]); clause (2) at the module `𝒢` the clause names, both of whose properties
are hypotheses of that clause. -/
public theorem flatProperSupportFinitelyPresented_singleDegreeComplex
    [LocallyOfFinitePresentation f] [IsProper f] (M : X.Modules)
    (hfp : M.IsFinitePresentation) (hflat : IsFlatOver f.toLRSHom.toShHom M) :
    FlatProperSupportFinitelyPresented f (singleDegreeComplex M) where
  bounded := ⟨0, 0, inferInstance, inferInstance⟩
  isFinitePresentation := isFinitePresentation_singleDegreeComplex M hfp
  isFlatOver := isFlatOver_singleDegreeComplex f M hflat
  properSupport := ⟨⊤, isProperOver_top_of_isProper f, fun _ => by simp⟩

/-! ### The structure sheaf in degree zero -/

/-- **`𝒪_X` is of finite presentation**, at the spelling `AlgebraicGeometry.Scheme.Modules` of
the category of `𝒪_X`-modules. This is [Stacks, Tag 03DL], proved as
`Stacks.SheafOfModules.Site.unit_isFinitePresentation` for `SheafOfModules.unit`; the structure
module `StrictlyPerfect.structureModule` of a ringed space is that object. -/
public theorem isFinitePresentation_structureModule (X : Scheme.{u}) :
    (StrictlyPerfect.structureModule X.toRingedSpace : X.Modules).IsFinitePresentation :=
  inferInstanceAs (SheafOfModules.unit X.ringCatSheaf).IsFinitePresentation

/-- **`𝒪_X` in degree zero is a complex of the kind [Stacks, Tag 0A1H] admits**, for a proper
flat morphism of finite presentation: this is the complex clause (1) of [Stacks, Tag 0B91]
specialises [Stacks, Tag 0A1H] to. -/
public theorem flatProperSupportFinitelyPresented_structure
    [LocallyOfFinitePresentation f] [IsProper f] [Flat f] :
    FlatProperSupportFinitelyPresented f
      (singleDegreeComplex (StrictlyPerfect.structureModule X.toRingedSpace : X.Modules)) :=
  flatProperSupportFinitelyPresented_singleDegreeComplex f _
    (isFinitePresentation_structureModule X) (isFlatOver_structureModule f)

end AlgebraicGeometry.ProperFlatBaseChange

end
