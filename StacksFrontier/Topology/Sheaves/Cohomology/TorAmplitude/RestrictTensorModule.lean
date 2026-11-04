module

public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.LocalTorAmplitude

/-!
# Restricting the derived tensor product with a module to an open subspace

Let `X` be a ringed space, `U ⊆ X` open, `E` an object of `D(𝒪_X)` and `F` an `𝒪_X`-module. The
restriction to `U` of a cohomology sheaf of `E ⊗^L_{𝒪_X} F[0]` is the corresponding cohomology
sheaf of `E|_U ⊗^L_{𝒪_U} (F|_U)[0]`; in particular the vanishing of the first implies the
vanishing of the second.

This is the step with which every passage from a global Tor-amplitude-style hypothesis to its
local form begins. The assembly is already carried out inside the proof of
`Stacks.Cohomology.TorAmplitude.hasTorAmplitude_of_iSup_eq_top`, where it is used in the
direction "all restrictions vanish, hence the sheaf vanishes"; this file records it as a
statement so that the other direction is available too.

## Main results

* `Stacks.Cohomology.TorAmplitude.isZero_homologyFunctor_derTensor_restrictModules`: if
  `H^n(E ⊗^L F[0])` vanishes then so does `H^n(E|_U ⊗^L (F|_U)[0])`.

## Implementation notes

The object `E` is replaced by a K-flat complex `K` (Tag 06YS on a ringed space), which is what
makes the derived tensor product computable from the total tensor complex and hence compatible
with restriction: `Stacks.Cohomology.TorAmplitude.derivedTensorRestrictIsoOfKFlatLeft` asks
K-flatness of the *left* argument only, so the module placed in degree zero needs no resolution
and need not be flat. Nothing else in the chain is a comparison: restriction commutes with the
localization functor, with the degree-zero single functor and with the cohomology sheaf
functors, and sends a zero object to a zero object.

No relation between `a` and `b`, and no hypothesis on `n`, enters: the statement is about one
degree at a time.

## References

* [Stacks Project, Definition 20.48.1 (Tag 08CG)](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YC](https://stacks.math.columbia.edu/tag/06YC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect AlgebraicGeometry.RingedSpace.KFlatDerivedPullback

namespace Stacks.Cohomology.TorAmplitude

universe u d

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u}) (U : Opens X.carrier)
  [HasDerivedCategory.{d} (OXMod.{u, u} X)]

attribute [local instance] _root_.Stacks.Cohomology.TorAmplitude.hasDerivedCategoryModules

/-- **The vanishing of a cohomology sheaf of `E ⊗^L F[0]` is inherited by the restriction to an
open subspace.** If `H^n(E ⊗^L_{𝒪_X} F[0])` is zero, then `H^n(E|_U ⊗^L_{𝒪_U} (F|_U)[0])` is
zero.

The restriction of the cohomology sheaf is the cohomology sheaf of the restriction, and the
restriction of the derived tensor product is the derived tensor product of the restrictions once
`E` is written as a K-flat complex — which is
`Stacks.Cohomology.TorAmplitude.derivedTensorRestrictIsoOfKFlatLeft`. -/
theorem isZero_homologyFunctor_derTensor_restrictModules
    (E : DerivedCategory (OXMod.{u, u} X)) (F : OXMod.{u, u} X) (n : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) n).obj
      (((derTensor X).tensor.obj E).obj
        ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F)))) :
    IsZero ((DerivedCategory.homologyFunctor
        (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) n).obj
      (((derTensor (X.restrict U.isOpenEmbedding)).tensor.obj
          ((AlgebraicGeometry.RingedSpace.derivedRestrictModules X U).obj E)).obj
        ((DerivedCategory.singleFunctor (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) 0).obj
          ((AlgebraicGeometry.RingedSpace.restrictModules X U).obj F)))) := by
  obtain ⟨K, hKflat, ⟨eK⟩⟩ := exists_kFlat_representative (X := X) E
  let SF := (HomologicalComplex.single (OXMod.{u, u} X) (ComplexShape.up ℤ) 0).obj F
  let Z : DerivedCategory (OXMod.{u, u} X) :=
    ((derTensor X).tensor.obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj SF)
  have hZ : IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) n).obj Z) :=
    h.of_iso ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) n).mapIso
      (((derTensor X).tensor.mapIso eK).app
        ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F)) :
      (DerivedCategory.homologyFunctor (OXMod.{u, u} X) n).obj Z ≅
        (DerivedCategory.homologyFunctor (OXMod.{u, u} X) n).obj
          (((derTensor X).tensor.obj E).obj
            ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F)))
  have hZU : IsZero ((DerivedCategory.homologyFunctor
      (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) n).obj
      ((AlgebraicGeometry.RingedSpace.derivedRestrictModules X U).obj Z)) :=
    ((AlgebraicGeometry.RingedSpace.restrictModules X U).map_isZero hZ).of_iso
      ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
        (AlgebraicGeometry.RingedSpace.restrictModules X U) n).app Z)
  refine hZU.of_iso ((DerivedCategory.homologyFunctor
    (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) n).mapIso ?_)
  exact (derivedTensorRestrictIsoOfKFlatLeft X U K SF hKflat ≪≫
    ((derTensor (X.restrict U.isOpenEmbedding)).tensor.mapIso
        ((AlgebraicGeometry.RingedSpace.derivedRestrictModulesObjQIso X U K).symm ≪≫
          (AlgebraicGeometry.RingedSpace.derivedRestrictModules X U).mapIso eK)).app _ ≪≫
      ((derTensor (X.restrict U.isOpenEmbedding)).tensor.obj _).mapIso
        (restrictSingleComplexIso X U F)).symm

end Stacks.Cohomology.TorAmplitude

end
