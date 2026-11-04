module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LocalNature
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PseudoCoherenceAndTorAmplitude
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.Restriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.PerfectnessCriterion
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# Perfect = pseudo-coherent + locally finite Tor dimension

Let `(C, O)` be a ringed site. An object of `D(O)` is perfect if and only if it is
pseudo-coherent and locally has finite Tor dimension.

## Main results

All in the namespace `Stacks.SheafOfModules.DerivedTensorProduct`.

* `isPerfect_slice_of_hasTorAmplitude`: on a slice `(C/V, O|_V)`, an `(a - 1)`-pseudo-coherent
  object with Tor amplitude in `[a, b]` is perfect.
* `isPerfect_of_isPseudoCoherent_of_locallyHasFiniteTorDimension`: a pseudo-coherent object which
  locally has finite Tor dimension, measured against a family `T` of derived tensor products on
  the slices, is perfect.
* `isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension'`: the equivalence, for such a
  family `T`.
* `isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension`: the equivalence, with locally
  finite Tor dimension measured against the canonical derived tensor product
  `Stacks.SheafOfModules.canonicalDerivedTensorProduct` on each slice.

## References

* [Stacks Project, Tag 08G8](https://stacks.math.columbia.edu/tag/08G8)
* [Stacks Project, Tag 08G7](https://stacks.math.columbia.edu/tag/08G7)
* [Stacks Project, Tag 08FU](https://stacks.math.columbia.edu/tag/08FU)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe d

namespace Stacks.SheafOfModules.DerivedTensorProduct

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {Z : RingedSite.{0, 0, 0}}
  [HasSheafify Z.J AddCommGrpCat.{0}]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  [∀ U : Z.C, HasSheafify (Z.J.over U) AddCommGrpCat.{0}]
  [∀ U : Z.C, (Z.J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}]
  [∀ (U : Z.C) (W : Over U), HasSheafify ((Z.J.over U).over W) AddCommGrpCat.{0}]
  [∀ (U : Z.C) (W : Over U),
    ((Z.J.over U).over W).WEqualsLocallyBijective AddCommGrpCat.{0}]

/-! ### The sheafification data of the slices -/

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits

/-- Sheafification on a slice of a slice. -/
local instance critIterHasSheafify (V : Z.C) (U : (Z.over V).C) :
    HasSheafify ((Z.over V).J.over U) AddCommGrpCat.{0} :=
  (inferInstance : ∀ (U : Z.C) (W : Over U),
    HasSheafify ((Z.J.over U).over W) AddCommGrpCat.{0}) V U

/-- Local bijectivity of the weak equivalences on a slice of a slice. -/
local instance critIterWEq (V : Z.C) (U : (Z.over V).C) :
    ((Z.over V).J.over U).WEqualsLocallyBijective AddCommGrpCat.{0} :=
  (inferInstance : ∀ (U : Z.C) (W : Over U),
    ((Z.J.over U).over W).WEqualsLocallyBijective AddCommGrpCat.{0}) V U

/-- Sheafification on a threefold slice. -/
local instance critTripleHasSheafify (V : Z.C) (U : (Z.over V).C) (W : Over U) :
    HasSheafify (((Z.over V).J.over U).over W) AddCommGrpCat.{0} :=
  Stacks.SheafOfModules.iteratedSliceHasSheafify AddCommGrpCat.{0} (J := (Z.over V).J) W

/-- Local bijectivity of the weak equivalences on a threefold slice. -/
local instance critTripleWEq (V : Z.C) (U : (Z.over V).C) (W : Over U) :
    (((Z.over V).J.over U).over W).WEqualsLocallyBijective AddCommGrpCat.{0} :=
  Stacks.SheafOfModules.iteratedSliceWEqualsLocallyBijective AddCommGrpCat.{0}
    (J := (Z.over V).J) W

/-! ### The derived categories and the tensor data -/

variable [HasDerivedCategory.{d} (RingedSite.Modules.{0, 0, 0} Z)]
  [hCritSliceDerived : ∀ U : Z.C,
    HasDerivedCategory.{d} (RingedSite.Modules.{0, 0, 0} (Z.over U))]
  [hCritIterDerived : ∀ (U : Z.C) (W : (Z.over U).C),
    HasDerivedCategory.{d} (RingedSite.Modules.{0, 0, 0} ((Z.over U).over W))]

attribute [local instance] RingedSite.sliceHasDerivedCategory sliceDerived

/-- The derived category of the modules on a slice of a slice. -/
local instance critIterDerived (V : Z.C) (U : (Z.over V).C) :
    HasDerivedCategory.{d} (RingedSite.Modules.{0, 0, 0} ((Z.over V).over U)) :=
  hCritIterDerived V U

/-- The derived category of the modules over the restriction of the structure sheaf of a slice
to a further slice. -/
local instance critIterRingSheafDerived (V : Z.C) (U : (Z.over V).C) :
    HasDerivedCategory.{d}
      (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf (Z.over V).O).over U)) :=
  hCritIterDerived V U

variable
  [∀ U : Z.C, (Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} (Z.over U).O).Additive]
  [∀ (U : Z.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} (Z.over U).O).obj M).Additive]
  [∀ (U : Z.C) (K L : CochainComplex (RingedSite.Modules.{0, 0, 0} (Z.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (Z.over U).O) (ComplexShape.up ℤ)]
  [hCritIterTensor : ∀ (U : Z.C) (W : (Z.over U).C),
    (Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} ((Z.over U).over W).O).Additive]
  [hCritIterTensorObj : ∀ (U : Z.C) (W : (Z.over U).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0}
      ((Z.over U).over W).O).obj M).Additive]
  [hCritIterBifunctor : ∀ (U : Z.C) (W : (Z.over U).C)
    (K L : CochainComplex (RingedSite.Modules.{0, 0, 0} ((Z.over U).over W)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor ((Z.over U).over W).O) (ComplexShape.up ℤ)]

attribute [local instance] sliceTensorAdditive sliceTensorObjAdditive sliceHasMapBifunctor

/-- The tensor bifunctor of a slice of a slice is additive. -/
local instance critIterTensorAdditive (V : Z.C) (U : (Z.over V).C) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} ((Z.over V).over U).O).Additive :=
  hCritIterTensor V U

/-- The tensor bifunctor of a slice of a slice is additive in its second variable. -/
local instance critIterTensorObjAdditive (V : Z.C) (U : (Z.over V).C)
    (M : RingedSite.Modules.{0, 0, 0} ((Z.over V).over U)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0}
      ((Z.over V).over U).O).obj M).Additive :=
  hCritIterTensorObj V U M

/-- Total complexes of the tensor bifunctor of a slice of a slice exist. -/
local instance critIterHasMapBifunctor (V : Z.C) (U : (Z.over V).C)
    (K L : CochainComplex (RingedSite.Modules.{0, 0, 0} ((Z.over V).over U)) ℤ) :
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor ((Z.over V).over U).O) (ComplexShape.up ℤ) :=
  hCritIterBifunctor V U K L

/-! ### Perfect objects are the pseudo-coherent ones of locally finite Tor dimension -/

omit [HasSheafify Z.J AddCommGrpCat.{0}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{0, 0, 0} Z)] in
/-- On the localized ringed site `(C/V, O|_V)`, an object of `D(O|_V)` with Tor amplitude in
`[a, b]` for the datum `T`, with `a ≤ b`, which is `(a - 1)`-pseudo-coherent, is perfect. -/
theorem isPerfect_slice_of_hasTorAmplitude (V : Z.C)
    (T : DerivedTensorProduct.{0, 0, 0, d} (Z.over V))
    (F : RingedSite.DerivedModules.{0, 0, 0, d} (Z.over V)) (a b : ℤ) (hab : a ≤ b)
    (hamp : HasTorAmplitude T F a b)
    (hpc : (Z.over V).IsPseudoCoherentFrom F (a - 1)) :
    (Z.over V).IsPerfect F :=
  torAmplitudePerfectnessCriterion T F a b hab hamp hpc

/-- An object of `D(O)` which is pseudo-coherent and locally has finite Tor dimension, measured
against the family `T` of derived tensor products on the slices, is perfect. -/
theorem isPerfect_of_isPseudoCoherent_of_locallyHasFiniteTorDimension
    (T : ∀ U : Z.C, DerivedTensorProduct.{0, 0, 0, d} (Z.over U))
    (E : RingedSite.DerivedModules.{0, 0, 0, d} Z) (hpc : Z.IsPseudoCoherent E)
    (htor : LocallyHasFiniteTorDimension T E) :
    Z.IsPerfect E := by
  refine RingedSite.isPerfect_of_locally Z E fun U => ?_
  obtain ⟨S, hS, hdata⟩ := htor U
  refine ⟨S, hS, fun {V} f hf => ?_⟩
  obtain ⟨a, b, hab, hamp⟩ := (hasFiniteTorDimension_iff (T V) _).1 (hdata f hf)
  obtain ⟨K, hK, eK⟩ := hpc
  exact isPerfect_slice_of_hasTorAmplitude V (T V) _ a b hab hamp
    (RingedSite.isPseudoCoherentFrom_derivedRestriction Z E (a - 1) ⟨K, hK (a - 1), eK⟩ V)

/-- Let `(C, O)` be a ringed site and let `T` assign a derived tensor product to each slice
`(C/U, O|_U)`. An object of `D(O)` is perfect if and only if it is pseudo-coherent and locally has
finite Tor dimension measured against `T`. -/
theorem isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension'
    (T : ∀ U : Z.C, DerivedTensorProduct.{0, 0, 0, d} (Z.over U))
    (E : RingedSite.DerivedModules.{0, 0, 0, d} Z) :
    Z.IsPerfect E ↔ Z.IsPseudoCoherent E ∧ LocallyHasFiniteTorDimension T E :=
  ⟨fun hE => ⟨RingedSite.isPseudoCoherent_of_isPerfect Z hE,
      locallyHasFiniteTorDimension_of_isPerfect T E hE⟩,
    fun ⟨hpc, htor⟩ =>
      isPerfect_of_isPseudoCoherent_of_locallyHasFiniteTorDimension T E hpc htor⟩

/-- Let `(C, O)` be a ringed site. An object of `D(O)` is perfect if and only if it is
pseudo-coherent and locally has finite Tor dimension, measured on each slice `(C/U, O|_U)` against
the derived tensor product `Stacks.SheafOfModules.canonicalDerivedTensorProduct`. -/
@[stacks 08G8, sga "6 I 5.8.1"]
theorem isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension
    (E : RingedSite.DerivedModules.{0, 0, 0, d} Z) :
    Z.IsPerfect E ↔ Z.IsPseudoCoherent E ∧
      LocallyHasFiniteTorDimension
        (fun U : Z.C => canonicalDerivedTensorProduct.{0, 0, d} (Z.over U)) E :=
  isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension' _ E

end Stacks.SheafOfModules.DerivedTensorProduct

end
