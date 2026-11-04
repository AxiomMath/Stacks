module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.TensorProductCompatibility
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.DerivedPullback
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedRestrict
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExistenceOnARingedSite

/-!
# Restriction to an open subspace and the tensor product

Let `X` be a ringed space and `U` an open subspace.  Restriction of `𝒪_X`-modules to `U` is
pullback along the open immersion `j_U : (U, 𝒪_X|_U) ⟶ (X, 𝒪_X)`, so the compatibility of
pullback with the tensor product specializes to restriction.  This file records that
specialization, at the level of complexes and at the level of the derived tensor product:

* `Tot(K ⊗_{𝒪_X} L)|_U ≅ Tot(K|_U ⊗_{𝒪_X|_U} L|_U)`;
* `(K ⊗^L L)|_U ≅ K|_U ⊗^L L|_U` for K-flat representatives.

## Main results

* `Stacks.Cohomology.RestrictionTensor.restrictComplexTensorIso`: restriction to an open
  subspace carries the total tensor complex of two complexes of `𝒪_X`-modules to the total
  tensor complex of their restrictions.  Unconditional.
* `Stacks.Cohomology.RestrictionTensor.derivedTensorRestrictIsoOfKFlat`: for K-flat
  representatives, restriction to an open subspace carries the derived tensor product to the
  derived tensor product of the restrictions.
* `Stacks.Cohomology.RestrictionTensor.kFlat_restrictComplex_tensorComplex`: the restriction of
  the total tensor complex of two K-flat complexes is K-flat.

## Implementation notes

The statement of `Stacks.Cohomology.RestrictionTensor.restrictComplexTensorIso` mentions only
`AlgebraicGeometry.RingedSpace.restrictComplex` and
`Stacks.SheafOfModules.Tensor.tensorComplex`; the open immersion and the pullback functor occur
only in its proof.  That is deliberate: the two spellings of pullback along `j_U`
(`RingedSpaceModuleAdjunction.modulePullback` and `StacksDraft.KFlat.modulePullback`, equal by
`rfl`) and the two spellings of the structure sheaf of an open subspace reach the `Preadditive`
instance of the category of modules by different routes, so a statement naming the pullback
functor forces a consumer to seat instances that this file seats once.

The two `PreservesZeroMorphisms` arguments of the degreewise comparison
`Stacks.Cohomology.RestrictionTensor.restrictMapComplexIso` are written out rather than
synthesized, and so is the additivity its own instance is built from: at `instances`
transparency search does not cross the two spellings of the structure sheaf, and the instance
found for the goal is not the one a declared instance is stated against.  This is the pattern
of `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.kFlat_restrictComplex`.

The derived statement is at K-flat representatives, which is where
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.comparison` identifies the derived tensor
product with the total tensor complex, and is what an argument that has chosen K-flat
resolutions has in hand.  It is stated for an arbitrary derived tensor product on `X` and on
`U` rather than for the canonical one, since only the `comparison` field is used; the canonical
one is a special case.  No derived category of `X` occurs in it: both sides are objects of
`D(𝒪_X|_U)`, and that derived category is the standard one, which is also how
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIsoOfKFlat` reads the derived
categories of open subspaces.  Keeping its universe a parameter instead would put a
metavariable in the hom universe of `D(𝒪_X|_U)` at the two spellings of the category of
modules, which instance search does not cross.

All universes of the ringed space coincide, as they must for
`Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf` to be stated.

## References

* [Stacks Project, Lemma 20.26.4 (Tag 079U)](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Lemma 17.16.3 (Tag 01CD)](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Lemma 20.26.3 (Tag 079R)](https://stacks.math.columbia.edu/tag/079R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback
open Stacks.Cohomology.DerivedPullbackTensor
open Stacks.Cohomology.HigherDirectImage
open RingedSpaceModuleAdjunction

namespace Stacks.Cohomology.RestrictionTensor

universe u

variable (X : RingedSpace.{u, u}) (U : Opens X.carrier)

/-! ### Restriction to an open subspace is degreewise pullback -/

/-- Pullback along the open immersion `j_U` preserves zero morphisms, being additive.  The
additivity instance is applied rather than searched for: the goal reaches the `Preadditive`
instance of the category of modules on `U` through the `StrictlyPerfect.structureSheafOfRings`
spelling of the structure sheaf and the instance reaches it through the
`structureSheafRing` spelling. -/
instance pullbackOpenImmersion_preservesZeroMorphisms :
    (StacksDraft.KFlat.modulePullback (openSubspaceInclusion X U)).PreservesZeroMorphisms :=
  @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
    (modulePullback_additive (openSubspaceInclusion X U))

/-- **Restriction to `U` is degreewise pullback along `j_U`, on cochain complexes.**  Both
functors are left adjoints of pushforward along `j_U`, so they are canonically isomorphic
(`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.restrictModulesIsoPullback`), and a
natural isomorphism of additive functors induces one of the functors they induce on complexes.

The two `PreservesZeroMorphisms` arguments of
`CategoryTheory.NatIso.mapHomologicalComplex` are supplied rather than synthesized. -/
def restrictMapComplexIso :
    (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X U).mapHomologicalComplex
        (ComplexShape.up ℤ) ≅
      (StacksDraft.KFlat.modulePullback
        (openSubspaceInclusion X U)).mapHomologicalComplex (ComplexShape.up ℤ) :=
  @NatIso.mapHomologicalComplex ℤ _ _ _ _ _ _ _ _
    (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
      (moduleRestriction_additive X U))
    (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
      (modulePullback_additive (openSubspaceInclusion X U)))
    (restrictModulesIsoPullback X U) (ComplexShape.up ℤ)

/-! ### The total tensor complex -/

/-- **Restriction to an open subspace commutes with the total tensor complex.**

`Tot(K ⊗_{𝒪_X} L)|_U ≅ Tot(K|_U ⊗_{𝒪_X|_U} L|_U)`.

Restriction to `U` is pullback along the open immersion `j_U`, and pullback along any morphism
of ringed spaces carries the total tensor complex to the total tensor complex
(`Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexIsoOfIsIso`, which is Tag 079U's
complex level assembled from the degreewise comparison of Tag 01CD).  No hypothesis on `K` or
`L`. -/
def restrictComplexTensorIso
    (K L : CochainComplex (RingedSpace.KFlatDerivedPullback.Modules X) ℤ) :
    AlgebraicGeometry.RingedSpace.restrictComplex
        (((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj K).obj L) U ≅
      ((Stacks.SheafOfModules.Tensor.tensorComplex
            (X.restrict U.isOpenEmbedding).sheaf).obj
          (AlgebraicGeometry.RingedSpace.restrictComplex K U)).obj
        (AlgebraicGeometry.RingedSpace.restrictComplex L U) :=
  (restrictMapComplexIso X U).app _ ≪≫
    pullbackTensorComplexIsoOfIsIso (openSubspaceInclusion X U) K L ≪≫
    ((Stacks.SheafOfModules.Tensor.tensorComplex
          (X.restrict U.isOpenEmbedding).sheaf).mapIso
        ((restrictMapComplexIso X U).app K).symm).app _ ≪≫
    ((Stacks.SheafOfModules.Tensor.tensorComplex
          (X.restrict U.isOpenEmbedding).sheaf).obj
        (AlgebraicGeometry.RingedSpace.restrictComplex K U)).mapIso
      ((restrictMapComplexIso X U).app L).symm

/-- **The restriction of the total tensor complex of two K-flat complexes is K-flat.**  The
total tensor complex of two K-flat complexes is K-flat (Tag 079R) and restriction to an open
subspace preserves K-flatness (Tag 06YC at `j_U`). -/
theorem kFlat_restrictComplex_tensorComplex
    (K L : CochainComplex (RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
    (hK : KFlat X K) (hL : KFlat X L) :
    KFlat (restrictToOpen X U)
      (AlgebraicGeometry.RingedSpace.restrictComplex
        (((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj K).obj L) U) :=
  AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.kFlat_restrictComplex U _
    (kFlat_tensorComplex X K L hK hL)

/-! ### The derived tensor product -/

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **Restriction to an open subspace commutes with the derived tensor product, on K-flat
representatives.**

For K-flat complexes `K` and `L` of `𝒪_X`-modules,
`Q(Tot(K ⊗_{𝒪_X} L)|_U) ≅ Q(K|_U) ⊗^L_{𝒪_X|_U} Q(L|_U)`.

The restriction of the total tensor complex is the total tensor complex of the restrictions
(`Stacks.Cohomology.RestrictionTensor.restrictComplexTensorIso`), and the restrictions of `K`
and `L` are K-flat (Tag 06YC at `j_U`), so
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.comparison` on `U` identifies the latter
with the derived tensor product of their classes.

Only the `comparison` field of the derived tensor product is used, so the statement is for an
arbitrary one on `U`; the canonical derived tensor product is a special case.  No derived
category of `X` occurs: both sides are objects of `D(𝒪_X|_U)`. -/
def derivedTensorRestrictIsoOfKFlat
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct
      (X.restrict U.isOpenEmbedding).sheaf)
    (K L : CochainComplex (RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
    (hK : KFlat X K) (hL : KFlat X L) :
    DerivedCategory.Q.obj
        (AlgebraicGeometry.RingedSpace.restrictComplex
          (((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj K).obj L) U) ≅
      (T.tensor.obj (DerivedCategory.Q.obj
            (AlgebraicGeometry.RingedSpace.restrictComplex K U))).obj
        (DerivedCategory.Q.obj (AlgebraicGeometry.RingedSpace.restrictComplex L U)) :=
  DerivedCategory.Q.mapIso (restrictComplexTensorIso X U K L) ≪≫
    (T.comparison _ _
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.kFlat_restrictComplex U K hK)
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.kFlat_restrictComplex U L hL)).symm

end Derived

end Stacks.Cohomology.RestrictionTensor

end
