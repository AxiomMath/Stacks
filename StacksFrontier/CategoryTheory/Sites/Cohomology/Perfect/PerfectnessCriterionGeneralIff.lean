module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectnessCriterionGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PseudoCoherenceAndTorAmplitudeGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PseudoCoherenceAndTorAmplitude
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence

/-!
# Perfect = pseudo-coherent + locally finite Tor dimension, on the diagonal

Let `(C, O)` be a ringed site. Stacks 08G8 says that an object of `D(O)` is perfect if and only
if it is pseudo-coherent and locally has finite Tor dimension. The implication (2) ⟹ (1) on the
diagonal `RingedSite.{u, u, u}` is
`isPerfect_of_isPseudoCoherent_of_locallyHasFiniteTorDimension_general`; this file adds the
converse, from Stacks 08FU and 08G6 (`RingedSite.isPseudoCoherent_of_isPerfect_general` and
`locallyHasFiniteTorDimension_of_isPerfect_anyUniverse`), and assembles the equivalence.

## Main results

* `isPerfect_slice_of_hasTorAmplitude_general`: Stacks 08G7 read on a slice.
* `isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension_general'`: the equivalence,
  for a family of derived tensor products on the slices.
* `isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension_general`: **Stacks 08G8**,
  with locally finite Tor dimension measured against the derived tensor product of Stacks 06YU
  on each slice, so that no derived-tensor-product parameter occurs in the statement.

## References

* [Stacks Project, Tag 08G8](https://stacks.math.columbia.edu/tag/08G8)
* [Stacks Project, Tag 08G7](https://stacks.math.columbia.edu/tag/08G7)
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

/-! ### The sheafification data of the slices -/

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits

attribute [local instance] critGenIterHasSheafify critGenIterWEq critGenTripleHasSheafify
  critGenTripleWEq

/-! ### The derived categories and the tensor data -/

variable [HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} Z)]
  [hCritGenSliceDerived : ∀ U : Z.C,
    HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} (Z.over U))]
  [hCritGenIterDerived : ∀ (U : Z.C) (W : (Z.over U).C),
    HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} ((Z.over U).over W))]

attribute [local instance] RingedSite.sliceHasDerivedCategory sliceDerived

attribute [local instance] critGenIterDerived critGenIterRingSheafDerived

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

attribute [local instance] critGenIterTensorAdditive critGenIterTensorObjAdditive
  critGenIterHasMapBifunctor

/-! ### Stacks 08G8 -/

omit [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} Z)] in
/-- **Stacks 08G7 read on a slice.** The perfectness criterion applied on the localized ringed
site `(C/V, O|_V)`: an object of `D(O|_V)` with Tor amplitude in `[a, b]` for the datum `T V`,
with `a ≤ b`, which is `(a - 1)`-pseudo-coherent, is perfect on `C/V`. -/
theorem isPerfect_slice_of_hasTorAmplitude_general (V : Z.C)
    (T : DerivedTensorProduct.{u, u, u, d} (Z.over V))
    (F : RingedSite.DerivedModules.{u, u, u, d} (Z.over V)) (a b : ℤ) (hab : a ≤ b)
    (hamp : HasTorAmplitude T F a b)
    (hpc : (Z.over V).IsPseudoCoherentFrom F (a - 1)) :
    (Z.over V).IsPerfect F :=
  torAmplitudePerfectnessCriterion_general T F a b hab hamp hpc

/-- **Stacks 08G8 for an arbitrary family of derived tensor products.** Let `(C, O)` be a ringed
site and let `T` assign a derived tensor product to each slice `(C/U, O|_U)`. An object of `D(O)`
is perfect if and only if it is pseudo-coherent and locally has finite Tor dimension measured
against `T`.

Specialized to the derived tensor product of Stacks 06YU, this is
`isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension_general`. -/
theorem isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension_general'
    (T : ∀ U : Z.C, DerivedTensorProduct.{u, u, u, d} (Z.over U))
    (E : RingedSite.DerivedModules.{u, u, u, d} Z) :
    Z.IsPerfect E ↔ Z.IsPseudoCoherent E ∧ LocallyHasFiniteTorDimension T E :=
  ⟨fun hE => ⟨RingedSite.isPseudoCoherent_of_isPerfect_general Z hE,
      locallyHasFiniteTorDimension_of_isPerfect_anyUniverse T E hE⟩,
    fun ⟨hpc, htor⟩ =>
      isPerfect_of_isPseudoCoherent_of_locallyHasFiniteTorDimension_general T E hpc htor⟩

/-- **Stacks 08G8.** Let `(C, O)` be a ringed site. An object of `D(O)` is perfect if and only
if it is pseudo-coherent and locally has finite Tor dimension.

Locally finite Tor dimension is measured, on each slice `(C/U, O|_U)`, against *the* derived
tensor product of that slice — `Stacks.SheafOfModules.canonicalDerivedTensorProduct`, the one
Stacks 06YU constructs — so the statement carries no derived-tensor-product parameter. -/
theorem isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension_general
    (E : RingedSite.DerivedModules.{u, u, u, d} Z) :
    Z.IsPerfect E ↔ Z.IsPseudoCoherent E ∧
      LocallyHasFiniteTorDimension
        (fun U : Z.C => canonicalDerivedTensorProduct.{u, u, d} (Z.over U)) E :=
  isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension_general' _ E

end Stacks.SheafOfModules.DerivedTensorProduct

end
