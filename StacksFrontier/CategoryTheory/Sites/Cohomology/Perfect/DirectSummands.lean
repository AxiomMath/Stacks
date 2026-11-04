module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectnessCriterion
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.Summands
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.DirectSummands
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# Perfectness passes to the direct summands of a biproduct

Let `(C, O)` be a ringed site and let `K` and `L` be objects of `D(O)`. If the biproduct
`K ⊞ L` is perfect, then so are `K` and `L`. This is Stacks 08GA.

## Main results

* `locallyHasFiniteTorDimension_left_of_biprod` and
  `locallyHasFiniteTorDimension_right_of_biprod`, in the namespace
  `Stacks.SheafOfModules.DerivedTensorProduct`: locally finite Tor dimension passes to the
  summands of a biproduct.
* `isPerfect_left_of_biprod` and `isPerfect_right_of_biprod`, in the same namespace: **Stacks
  08GA**.

## Implementation notes

The source's proof is three steps, and so is this one: read the perfectness of `K ⊞ L` through
Stacks 08G8, pass each of the two conditions to the summand — pseudo-coherence by Stacks 08FW
(`AlgebraicGeometry.RingedSite.isPseudoCoherent_left_of_biprod`), locally finite Tor dimension
by Stacks 08G3 (`Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_biprod`) — and
read the two conditions back through Stacks 08G8.

The only thing needing an argument is that Stacks 08G3, a statement about one site, applies to
the restriction of a biproduct. Locally finite Tor dimension is a condition on the restrictions
`(K ⊞ L)|_V`, while Stacks 08G3 wants a biproduct in `D(O|_V)`; the two are identified by
`CategoryTheory.Functor.mapBiprod` for `AlgebraicGeometry.RingedSite.derivedRestriction`, which
is additive and therefore preserves the biproduct.

Stacks 08G8 is read against a family of derived tensor products on the slices, which is what
makes locally finite Tor dimension expressible. That family does not occur in the statement of
Stacks 08GA, so it is not a parameter here: it is the derived tensor product of Stacks 06YU,
`Stacks.SheafOfModules.canonicalDerivedTensorProduct`, which exists on every ringed site
satisfying the hypotheses already in force. The conclusion is therefore the source's own,
conditional on nothing.

## References

* [Stacks Project, Tag 08GA](https://stacks.math.columbia.edu/tag/08GA)
* [Stacks Project, Tag 08G8](https://stacks.math.columbia.edu/tag/08G8)
* [Stacks Project, Tag 08FW](https://stacks.math.columbia.edu/tag/08FW)
* [Stacks Project, Tag 08G3](https://stacks.math.columbia.edu/tag/08G3)
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

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits
  critIterHasSheafify critIterWEq critTripleHasSheafify critTripleWEq

variable [HasDerivedCategory.{d} (RingedSite.Modules.{0, 0, 0} Z)]
  [∀ U : Z.C, HasDerivedCategory.{d} (RingedSite.Modules.{0, 0, 0} (Z.over U))]
  [∀ (U : Z.C) (W : (Z.over U).C),
    HasDerivedCategory.{d} (RingedSite.Modules.{0, 0, 0} ((Z.over U).over W))]

attribute [local instance] RingedSite.sliceHasDerivedCategory sliceDerived
  critIterDerived critIterRingSheafDerived

/-- **Restriction to a slice is additive on derived categories.** It is the functor induced by
an exact functor, hence triangulated, hence additive; stated as an instance because
`AlgebraicGeometry.RingedSite.derivedRestriction` is a definition which instance search does not
unfold. -/
local instance derivedRestrictionAdditive (V : Z.C) :
    (RingedSite.derivedRestriction.{0, 0, 0, d} Z V).Additive :=
  inferInstanceAs ((SheafOfModules.overFunctor.{0}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{0, 0, 0} Z.O) V).mapDerivedCategory).Additive

/-- **Restriction to a slice preserves binary biproducts on derived categories**, being
additive. -/
local instance derivedRestrictionPreservesBinaryBiproducts (V : Z.C) :
    PreservesBinaryBiproducts (RingedSite.derivedRestriction.{0, 0, 0, d} Z V) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

variable
  [∀ U : Z.C, (Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} (Z.over U).O).Additive]
  [∀ (U : Z.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} (Z.over U).O).obj M).Additive]
  [∀ (U : Z.C) (K L : CochainComplex (RingedSite.Modules.{0, 0, 0} (Z.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (Z.over U).O) (ComplexShape.up ℤ)]
  [∀ (U : Z.C) (W : (Z.over U).C),
    (Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} ((Z.over U).over W).O).Additive]
  [∀ (U : Z.C) (W : (Z.over U).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0}
      ((Z.over U).over W).O).obj M).Additive]
  [∀ (U : Z.C) (W : (Z.over U).C)
    (K L : CochainComplex (RingedSite.Modules.{0, 0, 0} ((Z.over U).over W)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor ((Z.over U).over W).O) (ComplexShape.up ℤ)]

attribute [local instance] sliceTensorAdditive sliceTensorObjAdditive sliceHasMapBifunctor
  critIterTensorAdditive critIterTensorObjAdditive critIterHasMapBifunctor

omit [∀ (U : Z.C) (W : Over U), HasSheafify ((Z.J.over U).over W) AddCommGrpCat.{0}]
  [∀ (U : Z.C) (W : Over U),
    ((Z.J.over U).over W).WEqualsLocallyBijective AddCommGrpCat.{0}]
  [∀ (U : Z.C) (W : (Z.over U).C),
    HasDerivedCategory.{d} (RingedSite.Modules.{0, 0, 0} ((Z.over U).over W))]
  [∀ (U : Z.C) (W : (Z.over U).C),
    (Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} ((Z.over U).over W).O).Additive]
  [∀ (U : Z.C) (W : (Z.over U).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0}
      ((Z.over U).over W).O).obj M).Additive]
  [∀ (U : Z.C) (W : (Z.over U).C)
    (K L : CochainComplex (RingedSite.Modules.{0, 0, 0} ((Z.over U).over W)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor ((Z.over U).over W).O) (ComplexShape.up ℤ)] in
/-- **Locally finite Tor dimension passes to the first summand of a biproduct.** Restriction to
a slice is additive, hence carries the biproduct `K ⊞ L` to the biproduct of the restrictions,
and Stacks 08G3 applies on the slice. -/
theorem locallyHasFiniteTorDimension_left_of_biprod
    (T : ∀ U : Z.C, DerivedTensorProduct.{0, 0, 0, d} (Z.over U))
    (K L : RingedSite.DerivedModules.{0, 0, 0, d} Z)
    (h : LocallyHasFiniteTorDimension T (K ⊞ L)) :
    LocallyHasFiniteTorDimension T K := by
  intro U
  obtain ⟨S, hS, hdata⟩ := h U
  refine ⟨S, hS, fun {V} f hf => ?_⟩
  obtain ⟨a, b, hamp⟩ := hdata f hf
  exact ⟨a, b, (hasTorAmplitude_of_biprod (T V) _ _ a b
    (hamp.of_iso ((RingedSite.derivedRestriction.{0, 0, 0, d} Z V).mapBiprod K L))).1⟩

omit [∀ (U : Z.C) (W : Over U), HasSheafify ((Z.J.over U).over W) AddCommGrpCat.{0}]
  [∀ (U : Z.C) (W : Over U),
    ((Z.J.over U).over W).WEqualsLocallyBijective AddCommGrpCat.{0}]
  [∀ (U : Z.C) (W : (Z.over U).C),
    HasDerivedCategory.{d} (RingedSite.Modules.{0, 0, 0} ((Z.over U).over W))]
  [∀ (U : Z.C) (W : (Z.over U).C),
    (Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} ((Z.over U).over W).O).Additive]
  [∀ (U : Z.C) (W : (Z.over U).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0}
      ((Z.over U).over W).O).obj M).Additive]
  [∀ (U : Z.C) (W : (Z.over U).C)
    (K L : CochainComplex (RingedSite.Modules.{0, 0, 0} ((Z.over U).over W)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor ((Z.over U).over W).O) (ComplexShape.up ℤ)] in
/-- **Locally finite Tor dimension passes to the second summand of a biproduct**, by exchanging
the two summands. -/
theorem locallyHasFiniteTorDimension_right_of_biprod
    (T : ∀ U : Z.C, DerivedTensorProduct.{0, 0, 0, d} (Z.over U))
    (K L : RingedSite.DerivedModules.{0, 0, 0, d} Z)
    (h : LocallyHasFiniteTorDimension T (K ⊞ L)) :
    LocallyHasFiniteTorDimension T L := by
  intro U
  obtain ⟨S, hS, hdata⟩ := h U
  refine ⟨S, hS, fun {V} f hf => ?_⟩
  obtain ⟨a, b, hamp⟩ := hdata f hf
  exact ⟨a, b, (hasTorAmplitude_of_biprod (T V) _ _ a b
    (hamp.of_iso ((RingedSite.derivedRestriction.{0, 0, 0, d} Z V).mapBiprod K L))).2⟩

/-- **Stacks 08GA.** Let `(C, O)` be a ringed site and let `K` and `L` be objects of `D(O)`. If
`K ⊞ L` is perfect, then so is `K`.

By Stacks 08G8 the biproduct is pseudo-coherent and locally has finite Tor dimension; Stacks
08FW gives the first condition for `K` and Stacks 08G3 the second, and Stacks 08G8 read
backwards gives perfectness. Stacks 08G8 is read against the derived tensor product of Stacks
06YU on the slices and on the iterated slices; neither occurs in the statement. -/
@[stacks 08GA "first summand"]
theorem isPerfect_left_of_biprod
    (K L : RingedSite.DerivedModules.{0, 0, 0, d} Z) (h : Z.IsPerfect (K ⊞ L)) :
    Z.IsPerfect K := by
  let T : ∀ U : Z.C, DerivedTensorProduct.{0, 0, 0, d} (Z.over U) := fun U =>
    _root_.Stacks.SheafOfModules.canonicalDerivedTensorProduct.{0, 0, d} (Z.over U)
  obtain ⟨hpc, htor⟩ :=
    (isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension' T (K ⊞ L)).1 h
  exact (isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension' T K).2
    ⟨RingedSite.isPseudoCoherent_left_of_biprod Z K L hpc,
      locallyHasFiniteTorDimension_left_of_biprod T K L htor⟩

/-- **Stacks 08GA.** If `K ⊞ L` is perfect, then so is `L`. -/
@[stacks 08GA "second summand"]
theorem isPerfect_right_of_biprod
    (K L : RingedSite.DerivedModules.{0, 0, 0, d} Z) (h : Z.IsPerfect (K ⊞ L)) :
    Z.IsPerfect L := by
  let T : ∀ U : Z.C, DerivedTensorProduct.{0, 0, 0, d} (Z.over U) := fun U =>
    _root_.Stacks.SheafOfModules.canonicalDerivedTensorProduct.{0, 0, d} (Z.over U)
  obtain ⟨hpc, htor⟩ :=
    (isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension' T (K ⊞ L)).1 h
  exact (isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension' T L).2
    ⟨RingedSite.isPseudoCoherent_right_of_biprod Z K L hpc,
      locallyHasFiniteTorDimension_right_of_biprod T K L htor⟩

end Stacks.SheafOfModules.DerivedTensorProduct

end
