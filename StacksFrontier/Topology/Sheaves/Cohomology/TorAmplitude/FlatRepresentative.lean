module

public import StacksFrontier.Homology.KFlat.BifunctorSingleSecondFactor
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.OnARingedSpace

/-!
# A bounded flat representative gives Tor amplitude

Tag 08CI characterises Tor amplitude in `[a, b]` of an object of `D(O_X)` by the existence of a
representative which is a complex of flat `O_X`-modules concentrated in `[a, b]`. This file
proves the easy direction: such a representative gives Tor amplitude in `[a, b]`.

## Main results

* `Stacks.TorAmplitude.FlatRepresentative.hasTorAmplitude_of_flat_representative`: an object of
  `D(O_X)` represented by a complex of flat `O_X`-modules which vanishes outside `[a, b]` has Tor
  amplitude in `[a, b]` (Tag 08CI, the easy direction).

## Implementation notes

Tor amplitude is `Stacks.Cohomology.TorAmplitude.HasTorAmplitude`, stated against the derived
tensor product `Stacks.Cohomology.TorAmplitude.derTensor` of Tag 06YU, so this file lives beside
it rather than with Tags 08CG–08CK.

A bounded above complex `K` of flat modules is K-flat (Tag 06YQ on a ringed space,
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.kFlat_of_boundedAbove_of_flat`), so by
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.comparisonLeft` the derived tensor product
with `F[0]` is computed by the total tensor complex `Tot(K ⊗_{O_X} F[0])`. Its cohomology vanishes
outside `[a, b]` by `CochainComplex.KFlatBifunctor.isZero_homology_mapBifunctor_single`.

The `HasDerivedCategory` instance at the `Stacks.DerivedTensor.RingedSite.Modules X.sheaf`
spelling is re-seated here: it is a `local instance` where `HasTorAmplitude` is defined, and an
instance at one spelling of a non-reducible definition does not fire at the other even though
the two types are equal by `rfl`.

The space, its structure sheaf and its modules share one universe, as in
`Stacks.Cohomology.TorAmplitude.HasTorAmplitude` and in the Tag 08CI statement; the hom universe
of the derived category is independent.

## References

* [Stacks Project, Tag 08CI](https://stacks.math.columbia.edu/tag/08CI)
* [Stacks Project, Tag 08CG](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect

namespace Stacks.TorAmplitude.FlatRepresentative

universe u d

section RingedSpace

variable {X : RingedSpace.{u, u}} [HasDerivedCategory.{d} (OXMod.{u} X)]

-- `HasDerivedCategory` at the spelling of Stacks 06YU: the type is `OXMod X` by `rfl`, but
-- `structureSheafOfRings` is not reducible, so an instance at one spelling does not fire at the
-- other.
attribute [local instance] _root_.Stacks.Cohomology.TorAmplitude.hasDerivedCategoryModules

/-- **Tag 08CI, the easy direction.** An object of `D(O_X)` represented by a complex of flat
`O_X`-modules which vanishes in every degree outside `[a, b]` has Tor amplitude in `[a, b]`. -/
theorem hasTorAmplitude_of_flat_representative
    (E : DerivedCategory (OXMod.{u} X)) (a b : ℤ)
    (K : CochainComplex (OXMod.{u} X) ℤ)
    (hflat : ∀ i : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) (K.X i))
    (hzero : ∀ i : ℤ, i ∉ Set.Icc a b → IsZero (K.X i))
    (e : DerivedCategory.Q.obj K ≅ E) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude X E a b := by
  have hKflat := RingedSpace.KFlatDerivedPullback.kFlat_of_boundedAbove_of_flat X K
    ⟨b, (CochainComplex.isStrictlyLE_iff K b).2 fun i hi =>
      hzero i (by simp only [Set.mem_Icc]; omega)⟩ hflat
  intro F i hi
  exact ((CochainComplex.KFlatBifunctor.isZero_homology_mapBifunctor_single
      (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) K F i (hzero i hi)).of_iso
    ((DerivedCategory.homologyFunctorFactors (RingedSpace.KFlatDerivedPullback.Modules X) i).app
      _)).of_iso
    ((DerivedCategory.homologyFunctor (RingedSpace.KFlatDerivedPullback.Modules X) i).mapIso
      ((((Stacks.Cohomology.TorAmplitude.derTensor X).tensor.mapIso e).app _).symm ≪≫
        (Stacks.Cohomology.TorAmplitude.derTensor X).comparisonLeft K _ hKflat))

end RingedSpace

end Stacks.TorAmplitude.FlatRepresentative

end
