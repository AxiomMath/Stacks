module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LocalNatureGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectnessCriterion
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.PerfectnessCriterionGeneral
public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.RestrictionGeneral

/-!
# Pseudo-coherent with locally finite Tor dimension implies perfect, on the diagonal

Let `(C, O)` be a ringed site. Stacks 08G8 says that an object of `D(O)` is perfect if and only
if it is pseudo-coherent and locally has finite Tor dimension. The base proves it, in
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectnessCriterion`, at
`RingedSite.{0, 0, 0}`. This file proves the implication (2) ⟹ (1) on the diagonal
`RingedSite.{u, u, u}`, the seat of the monoidal development of Stacks 0FPT, where Stacks 0FPY
needs it; the base statement is unchanged, the general form being a new declaration.

## Main results

* `isPerfect_of_isPseudoCoherent_of_locallyHasFiniteTorDimension_general` (in the namespace
  `Stacks.SheafOfModules.DerivedTensorProduct`): a pseudo-coherent object of `D(O)` which locally
  has finite Tor dimension is perfect.

## Implementation notes

The route is the base one (see the implementation notes of
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectnessCriterion`): local finite Tor
dimension gives a covering on whose members `E` has Tor amplitude in some `[a, b]`,
pseudo-coherence restricts to the members, Stacks 08G7 on each slice
(`Stacks.SheafOfModules.DerivedTensorProduct.torAmplitudePerfectnessCriterion_general`) makes the
restrictions perfect, and perfectness descends
(`AlgebraicGeometry.RingedSite.isPerfect_of_locally_general`). The section variables and the
local instances which present the data of the slices and iterated slices at the spellings
instance search needs are those of the base file.

## References

* [Stacks Project, Tag 08G8](https://stacks.math.columbia.edu/tag/08G8)
* [Stacks Project, Tag 08G7](https://stacks.math.columbia.edu/tag/08G7)
* [Stacks Project, Tag 08FU](https://stacks.math.columbia.edu/tag/08FU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u d

namespace Stacks.SheafOfModules.DerivedTensorProduct

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {Z : RingedSite.{u, u, u}}
  [HasSheafify Z.J AddCommGrpCat.{u}]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : Z.C, HasSheafify (Z.J.over U) AddCommGrpCat.{u}]
  [∀ U : Z.C, (Z.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (U : Z.C) (W : Over U), HasSheafify ((Z.J.over U).over W) AddCommGrpCat.{u}]
  [∀ (U : Z.C) (W : Over U),
    ((Z.J.over U).over W).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-! ### The sheafification data of the slices, at the spellings instance search needs -/

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits

/-- Sheafification on a slice of a slice, at the localized spelling. -/
local instance critGenIterHasSheafify (V : Z.C) (U : (Z.over V).C) :
    HasSheafify ((Z.over V).J.over U) AddCommGrpCat.{u} :=
  (inferInstance : ∀ (U : Z.C) (W : Over U),
    HasSheafify ((Z.J.over U).over W) AddCommGrpCat.{u}) V U

/-- Local bijectivity of the weak equivalences on a slice of a slice. -/
local instance critGenIterWEq (V : Z.C) (U : (Z.over V).C) :
    ((Z.over V).J.over U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  (inferInstance : ∀ (U : Z.C) (W : Over U),
    ((Z.J.over U).over W).WEqualsLocallyBijective AddCommGrpCat.{u}) V U

/-- Sheafification on a threefold slice, transported from the twofold slice along the
iterated-slice equivalence of sites. -/
local instance critGenTripleHasSheafify (V : Z.C) (U : (Z.over V).C) (W : Over U) :
    HasSheafify (((Z.over V).J.over U).over W) AddCommGrpCat.{u} :=
  Stacks.SheafOfModules.iteratedSliceHasSheafify AddCommGrpCat.{u} (J := (Z.over V).J) W

/-- Local bijectivity of the weak equivalences on a threefold slice. -/
local instance critGenTripleWEq (V : Z.C) (U : (Z.over V).C) (W : Over U) :
    (((Z.over V).J.over U).over W).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  Stacks.SheafOfModules.iteratedSliceWEqualsLocallyBijective AddCommGrpCat.{u}
    (J := (Z.over V).J) W

/-! ### The derived categories and the tensor data -/

variable [HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} Z)]
  [hCritGenSliceDerived : ∀ U : Z.C,
    HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} (Z.over U))]
  [hCritGenIterDerived : ∀ (U : Z.C) (W : (Z.over U).C),
    HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} ((Z.over U).over W))]

attribute [local instance] RingedSite.sliceHasDerivedCategory sliceDerived

/-- The derived category of the modules on a slice of a slice, at the localized spelling. -/
local instance critGenIterDerived (V : Z.C) (U : (Z.over V).C) :
    HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} ((Z.over V).over U)) :=
  hCritGenIterDerived V U

/-- The derived category of the modules on a slice of a slice, at the spelling in which
restriction produces them. -/
local instance critGenIterRingSheafDerived (V : Z.C) (U : (Z.over V).C) :
    HasDerivedCategory.{d}
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (Z.over V).O).over U)) :=
  hCritGenIterDerived V U

variable
  [∀ U : Z.C, (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Z.over U).O).Additive]
  [∀ (U : Z.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Z.over U).O).obj M).Additive]
  [∀ (U : Z.C) (K L : CochainComplex (RingedSite.Modules.{u, u, u} (Z.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (Z.over U).O) (ComplexShape.up ℤ)]
  [hCritGenIterTensor : ∀ (U : Z.C) (W : (Z.over U).C),
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((Z.over U).over W).O).Additive]
  [hCritGenIterTensorObj : ∀ (U : Z.C) (W : (Z.over U).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ((Z.over U).over W).O).obj M).Additive]
  [hCritGenIterBifunctor : ∀ (U : Z.C) (W : (Z.over U).C)
    (K L : CochainComplex (RingedSite.Modules.{u, u, u} ((Z.over U).over W)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor ((Z.over U).over W).O) (ComplexShape.up ℤ)]

attribute [local instance] sliceTensorAdditive sliceTensorObjAdditive sliceHasMapBifunctor

/-- The tensor bifunctor of a slice of a slice is additive. -/
local instance critGenIterTensorAdditive (V : Z.C) (U : (Z.over V).C) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((Z.over V).over U).O).Additive :=
  hCritGenIterTensor V U

/-- The tensor bifunctor of a slice of a slice is additive in its second variable. -/
local instance critGenIterTensorObjAdditive (V : Z.C) (U : (Z.over V).C)
    (M : RingedSite.Modules.{u, u, u} ((Z.over V).over U)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ((Z.over V).over U).O).obj M).Additive :=
  hCritGenIterTensorObj V U M

/-- Total complexes of the tensor bifunctor of a slice of a slice exist. -/
local instance critGenIterHasMapBifunctor (V : Z.C) (U : (Z.over V).C)
    (K L : CochainComplex (RingedSite.Modules.{u, u, u} ((Z.over V).over U)) ℤ) :
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor ((Z.over V).over U).O) (ComplexShape.up ℤ) :=
  hCritGenIterBifunctor V U K L

/-! ### Stacks 08G8, the implication (2) ⟹ (1) -/

/-- **The implication (2) ⟹ (1) of Stacks 08G8, on the diagonal.** An object of `D(O)` which is
pseudo-coherent and locally has finite Tor dimension is perfect.

This is `isPerfect_of_isPseudoCoherent_of_locallyHasFiniteTorDimension`, proved on the base at
`RingedSite.{0, 0, 0}`, at `RingedSite.{u, u, u}`; the proof is the same, through
`torAmplitudePerfectnessCriterion_general` on each slice, the restriction of pseudo-coherence
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_derivedRestriction_general` and the descent
of perfectness `AlgebraicGeometry.RingedSite.isPerfect_of_locally_general`. -/
theorem isPerfect_of_isPseudoCoherent_of_locallyHasFiniteTorDimension_general
    (T : ∀ U : Z.C, DerivedTensorProduct.{u, u, u, d} (Z.over U))
    (E : RingedSite.DerivedModules.{u, u, u, d} Z) (hpc : Z.IsPseudoCoherent E)
    (htor : LocallyHasFiniteTorDimension T E) :
    Z.IsPerfect E := by
  refine RingedSite.isPerfect_of_locally_general Z E fun U => ?_
  obtain ⟨S, hS, hdata⟩ := htor U
  refine ⟨S, hS, fun {V} f hf => ?_⟩
  obtain ⟨a, b, hab, hamp⟩ := (hasFiniteTorDimension_iff (T V) _).1 (hdata f hf)
  obtain ⟨K, hK, eK⟩ := hpc
  exact torAmplitudePerfectnessCriterion_general (T V) _ a b hab hamp
    (RingedSite.isPseudoCoherentFrom_derivedRestriction_general Z E (a - 1)
      ⟨K, hK (a - 1), eK⟩ V)

end Stacks.SheafOfModules.DerivedTensorProduct

end
