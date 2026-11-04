module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectnessCriterionGeneralIff
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.Summands
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.DirectSummands
import StacksCore.Tactic.StacksAttribute

/-!
# Perfectness passes to the direct summands of a biproduct, at arbitrary universes

This file is the universe-general form of
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DirectSummands`, which states its results with
the sections of the modules (and, where the ring universe enters, of the structure sheaf) in
universe `0`. The statements and proofs below are those of that file at the universes given
in each declaration; each declaration has the name of its counterpart there with the suffix
`_general` (`General` for definitions and instances).

Let `(C, O)` be a ringed site and let `K` and `L` be objects of `D(O)`. If the biproduct
`K ⊞ L` is perfect, then so are `K` and `L`. This is Stacks 08GA.

## Main results

* `locallyHasFiniteTorDimension_left_of_biprod_general` and
  `locallyHasFiniteTorDimension_right_of_biprod_general`, in the namespace
  `Stacks.SheafOfModules.DerivedTensorProduct`: locally finite Tor dimension passes to the
  summands of a biproduct.
* `isPerfect_left_of_biprod_general` and `isPerfect_right_of_biprod_general`, in the same
  namespace: perfectness passes to the summands of a biproduct, **Stacks 08GA**.

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

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits
  critGenIterHasSheafify critGenIterWEq critGenTripleHasSheafify critGenTripleWEq

variable [HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} Z)]
  [∀ U : Z.C, HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} (Z.over U))]
  [∀ (U : Z.C) (W : (Z.over U).C),
    HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} ((Z.over U).over W))]

attribute [local instance] RingedSite.sliceHasDerivedCategory sliceDerived
  critGenIterDerived critGenIterRingSheafDerived

/-- **Restriction to a slice is additive on derived categories.** It is the functor induced by
an exact functor, hence triangulated, hence additive; stated as an instance because
`AlgebraicGeometry.RingedSite.derivedRestriction` is a definition which instance search does not
unfold. -/
local instance derivedRestrictionAdditiveGeneral (V : Z.C) :
    (RingedSite.derivedRestriction.{u, u, u, d} Z V).Additive :=
  inferInstanceAs ((SheafOfModules.overFunctor.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.O) V).mapDerivedCategory).Additive

/-- **Restriction to a slice preserves binary biproducts on derived categories**, being
additive. -/
local instance derivedRestrictionPreservesBinaryBiproductsGeneral (V : Z.C) :
    PreservesBinaryBiproducts (RingedSite.derivedRestriction.{u, u, u, d} Z V) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

variable
  [∀ U : Z.C, (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Z.over U).O).Additive]
  [∀ (U : Z.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Z.over U).O).obj M).Additive]
  [∀ (U : Z.C) (K L : CochainComplex (RingedSite.Modules.{u, u, u} (Z.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (Z.over U).O) (ComplexShape.up ℤ)]
  [∀ (U : Z.C) (W : (Z.over U).C),
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((Z.over U).over W).O).Additive]
  [∀ (U : Z.C) (W : (Z.over U).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ((Z.over U).over W).O).obj M).Additive]
  [∀ (U : Z.C) (W : (Z.over U).C)
    (K L : CochainComplex (RingedSite.Modules.{u, u, u} ((Z.over U).over W)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor ((Z.over U).over W).O) (ComplexShape.up ℤ)]

attribute [local instance] sliceTensorAdditive sliceTensorObjAdditive sliceHasMapBifunctor
  critGenIterTensorAdditive critGenIterTensorObjAdditive critGenIterHasMapBifunctor

omit [∀ (U : Z.C) (W : Over U), HasSheafify ((Z.J.over U).over W) AddCommGrpCat.{u}]
  [∀ (U : Z.C) (W : Over U),
    ((Z.J.over U).over W).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (U : Z.C) (W : (Z.over U).C),
    HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} ((Z.over U).over W))]
  [∀ (U : Z.C) (W : (Z.over U).C),
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((Z.over U).over W).O).Additive]
  [∀ (U : Z.C) (W : (Z.over U).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ((Z.over U).over W).O).obj M).Additive]
  [∀ (U : Z.C) (W : (Z.over U).C)
    (K L : CochainComplex (RingedSite.Modules.{u, u, u} ((Z.over U).over W)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor ((Z.over U).over W).O) (ComplexShape.up ℤ)] in
/-- **Locally finite Tor dimension passes to the first summand of a biproduct.** Restriction to
a slice is additive, hence carries the biproduct `K ⊞ L` to the biproduct of the restrictions,
and Stacks 08G3 applies on the slice. -/
theorem locallyHasFiniteTorDimension_left_of_biprod_general
    (T : ∀ U : Z.C, DerivedTensorProduct.{u, u, u, d} (Z.over U))
    (K L : RingedSite.DerivedModules.{u, u, u, d} Z)
    (h : LocallyHasFiniteTorDimension T (K ⊞ L)) :
    LocallyHasFiniteTorDimension T K := by
  intro U
  obtain ⟨S, hS, hdata⟩ := h U
  refine ⟨S, hS, fun {V} f hf => ?_⟩
  obtain ⟨a, b, hamp⟩ := hdata f hf
  exact ⟨a, b, (hasTorAmplitude_of_biprod (T V) _ _ a b
    (hamp.of_iso ((RingedSite.derivedRestriction.{u, u, u, d} Z V).mapBiprod K L))).1⟩

omit [∀ (U : Z.C) (W : Over U), HasSheafify ((Z.J.over U).over W) AddCommGrpCat.{u}]
  [∀ (U : Z.C) (W : Over U),
    ((Z.J.over U).over W).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (U : Z.C) (W : (Z.over U).C),
    HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} ((Z.over U).over W))]
  [∀ (U : Z.C) (W : (Z.over U).C),
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((Z.over U).over W).O).Additive]
  [∀ (U : Z.C) (W : (Z.over U).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ((Z.over U).over W).O).obj M).Additive]
  [∀ (U : Z.C) (W : (Z.over U).C)
    (K L : CochainComplex (RingedSite.Modules.{u, u, u} ((Z.over U).over W)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor ((Z.over U).over W).O) (ComplexShape.up ℤ)] in
/-- **Locally finite Tor dimension passes to the second summand of a biproduct**, by exchanging
the two summands. -/
theorem locallyHasFiniteTorDimension_right_of_biprod_general
    (T : ∀ U : Z.C, DerivedTensorProduct.{u, u, u, d} (Z.over U))
    (K L : RingedSite.DerivedModules.{u, u, u, d} Z)
    (h : LocallyHasFiniteTorDimension T (K ⊞ L)) :
    LocallyHasFiniteTorDimension T L := by
  intro U
  obtain ⟨S, hS, hdata⟩ := h U
  refine ⟨S, hS, fun {V} f hf => ?_⟩
  obtain ⟨a, b, hamp⟩ := hdata f hf
  exact ⟨a, b, (hasTorAmplitude_of_biprod (T V) _ _ a b
    (hamp.of_iso ((RingedSite.derivedRestriction.{u, u, u, d} Z V).mapBiprod K L))).2⟩

/-- **Stacks 08GA.** Let `(C, O)` be a ringed site and let `K` and `L` be objects of `D(O)`. If
`K ⊞ L` is perfect, then so is `K`.

By Stacks 08G8 the biproduct is pseudo-coherent and locally has finite Tor dimension; Stacks
08FW gives the first condition for `K` and Stacks 08G3 the second, and Stacks 08G8 read
backwards gives perfectness. Stacks 08G8 is read against the derived tensor product of Stacks
06YU on the slices and on the iterated slices; neither occurs in the statement. -/
theorem isPerfect_left_of_biprod_general
    (K L : RingedSite.DerivedModules.{u, u, u, d} Z) (h : Z.IsPerfect (K ⊞ L)) :
    Z.IsPerfect K := by
  let T : ∀ U : Z.C, DerivedTensorProduct.{u, u, u, d} (Z.over U) := fun U =>
    _root_.Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u, u, d} (Z.over U)
  obtain ⟨hpc, htor⟩ :=
    (isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension_general' T (K ⊞ L)).1 h
  exact (isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension_general' T K).2
    ⟨RingedSite.isPseudoCoherent_left_of_biprod_general Z K L hpc,
      locallyHasFiniteTorDimension_left_of_biprod_general T K L htor⟩

/-- **Stacks 08GA.** If `K ⊞ L` is perfect, then so is `L`. -/
theorem isPerfect_right_of_biprod_general
    (K L : RingedSite.DerivedModules.{u, u, u, d} Z) (h : Z.IsPerfect (K ⊞ L)) :
    Z.IsPerfect L := by
  let T : ∀ U : Z.C, DerivedTensorProduct.{u, u, u, d} (Z.over U) := fun U =>
    _root_.Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u, u, d} (Z.over U)
  obtain ⟨hpc, htor⟩ :=
    (isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension_general' T (K ⊞ L)).1 h
  exact (isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension_general' T L).2
    ⟨RingedSite.isPseudoCoherent_right_of_biprod_general Z K L hpc,
      locallyHasFiniteTorDimension_right_of_biprod_general T K L htor⟩

end Stacks.SheafOfModules.DerivedTensorProduct

end
