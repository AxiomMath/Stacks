module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedModuleSumFormula
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleProjection
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleProjectionTargetSum

/-!
# Stacks 0D9E (2) with the projection map and the direct-sum formula discharged

Let `S` be a simplicial-site situation (Stacks 09WE) and `O` a sheaf of commutative rings on its
total site all of whose structure-sheaf transitions `f_φ^{-1}O_n ⟶ O_m` are flat. Stacks 0D9E (2)
says that an object `K` of `D(O)` is cartesian exactly when the canonical map
`g_{n!}K_n ⟶ g_{n!}O_n ⊗^L_O K` is an isomorphism for every simplicial degree `n`.

The source's proof restricts that map to a degree `m` and identifies the two sides with direct
sums over the simplex maps `φ : [n] ⟶ [m]`. Unless qualified, the names below are in the
namespace `CategoryTheory.SimplicialSiteSituation`. The canonical map is `moduleProjection`. The
identification of the *source* is `derivedModuleSumFormula`, the componentwise direct-sum formula
of Stacks 0D72 (6) on unbounded derived categories. The identification of the *target* is
`moduleProjectionTargetIso`.

## Main results

* `isCartesianDerivedModule_iff_isIso_moduleProjection`: the criterion of Stacks 0D9E (2) under
  the flatness hypothesis and the summandwise comparison `proj_restrict`, with the canonical map
  and the direct-sum identifications of the restrictions to a degree of its source and its target
  supplied.

## Implementation notes

The summandwise comparison `proj_restrict` states that under the two direct-sum identifications
the restriction to degree `m` of the canonical map is the direct sum of the derived transitions
`K(φ)`. It holds for every `K`, by `moduleProjection_restrict_of_adjunctSquare`, and Stacks
0D9E (2) under the flatness hypothesis alone is
`isCartesianDerivedModule_iff_forall_isIso_moduleProjection`.

The canonical map and the target identification are constructed on sheaves: `g_{n!}O_n` is flat
(`isFlat_componentModuleLowerShriek_unit`), so `g_{n!}O_n ⊗^L_O -` is the derived functor of the
exact endofunctor `g_{n!}O_n ⊗_O -` of sheaves of modules
(`componentModuleLowerShriekUnitTensorDerivedIso`), and on sheaves the tensor product distributes
over direct sums.

## References

* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward
open Stacks.Sheaves.RingedToposModules

universe u

namespace CategoryTheory.SimplicialSiteSituation

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyComponent

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

variable [∀ (m n : SimplexCategory) (φ : m ⟶ n),
  (pullbackOnHomotopy (S.transitionRingedToposHom O φ)).HasLeftDerivedFunctor
    (targetQuasiIso (S.componentRingedTopos O m))]

/-- **The criterion of Stacks 0D9E (2), granted the summandwise comparison.** Let `O` be a
sheaf of rings on `𝒞_total` whose transition morphisms `f_φ^{-1}O_n ⟶ O_m` are all flat, and let
`K` be an object of `D(O)` for which `proj_restrict` holds: under the direct-sum identifications
of its source `g_{n!}K_n` with `⨁_φ Lf_φ^*K_n`
(`CategoryTheory.SimplicialSiteSituation.derivedModuleSumFormula`) and of its target
`g_{n!}O_n ⊗^L_O K` with `⨁_φ K_m`
(`CategoryTheory.SimplicialSiteSituation.moduleProjectionTargetIso`), the restriction to degree
`m` of the canonical map `g_{n!}K_n ⟶ g_{n!}O_n ⊗^L_O K` is the direct sum of the derived
transitions `K(φ) : Lf_φ^*K_n ⟶ K_m` of Stacks 07TF (4). Then `K` is cartesian if and only if
the canonical map is an isomorphism for every simplicial degree `n`.

This is `isCartesianDerivedModule_iff_isIso_moduleProjection_of_sourceIso` with the canonical
map `moduleProjection` and both direct-sum identifications supplied.
-/
theorem isCartesianDerivedModule_iff_isIso_moduleProjection
    (hflat : ∀ (n m : SimplexCategory) (φ : n ⟶ m), (S.transitionRingedToposHom O φ).IsFlat)
    (K : DerivedCategory (S.totalRingedTopos O).Modules)
    (proj_restrict : ∀ n m : SimplexCategory,
      (S.derivedComponentModuleRestriction O m).map (S.moduleProjection O n (hflat n) K) ≫
          (S.moduleProjectionTargetIso O n m K).hom =
        (S.derivedModuleSumFormula O n m (hflat n)
            ((S.derivedComponentModuleRestriction O n).obj K)).hom ≫
          Limits.biproduct.map fun φ : n ⟶ m =>
            (S.derivedComponentModuleTransition O φ).app K) :
    S.IsCartesianDerivedModule O K ↔
      ∀ n : SimplexCategory, IsIso (S.moduleProjection O n (hflat n) K) :=
  S.isCartesianDerivedModule_iff_isIso_moduleProjection_of_sourceIso O hflat K
    (fun n => S.moduleProjection O n (hflat n) K)
    (fun n m => S.derivedModuleSumFormula O n m (hflat n)
      ((S.derivedComponentModuleRestriction O n).obj K))
    (fun n m => S.moduleProjectionTargetIso O n m K) proj_restrict

end CategoryTheory.SimplicialSiteSituation

end
