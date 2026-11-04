module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.DerivedTensorProductGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.LocallyFiniteTorDimension

/-!
# The derived tensor product commutes with restriction to a slice, above the module universe

Let `(C, O)` be a ringed site whose objects form a type one universe above its morphisms and the
sections of its structure sheaf, as the small étale site of an algebraic space does, and let `V`
be an object of `C`. For objects `K` and `L` of `D(O)` this file identifies

`(K ⊗^L_O L)|_V ≅ K|_V ⊗^L_{O|_V} L|_V`

in `D(O|_V)`, for arbitrary derived tensor products of Stacks 06YU on `C` and on `C/V`.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.nonempty_derivedTensor_restriction_iso_general`:
  the statement above.

## Implementation notes

`Stacks.DerivedTensor.SliceRestriction.derivedTensorRestrictIso` is the same statement on a
`RingedSite.{u, u, u}`, whose objects, morphisms and sections share one universe; that excludes
the small étale site of an algebraic space. The argument is the same: both factors are replaced
by K-flat complexes whose restrictions to every slice stay K-flat
(`Stacks.SheafOfModules.DerivedTensorProduct.exists_sliceKFlat_representative_general`, the
resolutions of Stacks 06YS in their colimit presentation), on which both derived tensor products
are total tensor complexes, and restriction commutes with the total tensor complex
(`AlgebraicGeometry.RingedSite.tensorComplexOverIso`). The representatives are chosen by an
existence statement, so the comparison is stated as the existence of an isomorphism; that is all
an isomorphism-invariant property, such as Tor amplitude, consumes.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SheafOfModules.Tensor

namespace Stacks.SheafOfModules.DerivedTensorProduct

universe u d

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable (X : AlgebraicGeometry.RingedSite.{u + 1, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, u} X)]
  [(sheafTensor.{u + 1, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u + 1, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u + 1, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (sheafTensor.{u + 1, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits

variable [hSliceDerived : ∀ U : X.C,
  HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, u} (X.over U))]

attribute [local instance] RingedSite.sliceHasDerivedCategory sliceDerived

variable
  [∀ U : X.C, (sheafTensor.{u + 1, u, u, u, u} (X.over U).O).Additive]
  [∀ (U : X.C) M, ((sheafTensor.{u + 1, u, u, u, u} (X.over U).O).obj M).Additive]
  [∀ (U : X.C) (K L : CochainComplex (RingedSite.Modules.{u + 1, u, u} (X.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (sheafTensor.{u + 1, u, u, u, u} (X.over U).O) (ComplexShape.up ℤ)]

attribute [local instance] sliceTensorAdditive sliceTensorObjAdditive sliceHasMapBifunctor

-- The same three instances at the spelling `X.O.over U`, in which the restriction of the total
-- tensor complex is stated.
attribute [local instance] pcgSliceTensorAdditive' pcgSliceTensorObjAdditive'
  pcgSliceHasMapBifunctor'

/-- **The derived tensor product commutes with restriction to a slice, above the module
universe.** Let `(C, O)` be a ringed site whose objects form a type one universe above its
morphisms and sections, `V` an object of `C`, `T` a derived tensor product on `C` and `TV` one on
`C/V`. For objects `K` and `L` of `D(O)` there is an isomorphism

`(K ⊗^L_O L)|_V ≅ K|_V ⊗^L_{O|_V} L|_V`

in `D(O|_V)`. Both factors are represented by K-flat complexes whose restrictions to `C/V` are
K-flat; on those both derived tensor products are the total tensor complexes, and restriction to
`C/V` commutes with the total tensor complex. -/
theorem nonempty_derivedTensor_restriction_iso_general
    (T : DerivedTensorProduct.{u + 1, u, u, d} X)
    (V : X.C) (TV : DerivedTensorProduct.{u + 1, u, u, d} (X.over V))
    (K L : RingedSite.DerivedModules.{u + 1, u, u, d} X) :
    Nonempty ((_root_.SheafOfModules.overFunctor.{u} (Tensor.ringSheaf.{u + 1, u, u} X.O)
        V).mapDerivedCategory.obj ((T.tensor.obj K).obj L) ≅
      (TV.tensor.obj ((_root_.SheafOfModules.overFunctor.{u}
          (Tensor.ringSheaf.{u + 1, u, u} X.O) V).mapDerivedCategory.obj K)).obj
        ((_root_.SheafOfModules.overFunctor.{u}
          (Tensor.ringSheaf.{u + 1, u, u} X.O) V).mapDerivedCategory.obj L)) := by
  obtain ⟨A, hA, hAW, ⟨eA⟩⟩ := exists_sliceKFlat_representative_general X K
  obtain ⟨B, hB, hBW, ⟨eB⟩⟩ := exists_sliceKFlat_representative_general X L
  let F := _root_.SheafOfModules.overFunctor.{u} (Tensor.ringSheaf.{u + 1, u, u} X.O) V
  exact ⟨F.mapDerivedCategory.mapIso
      (((T.tensor.mapIso eA).app L).symm ≪≫
        ((T.tensor.obj (DerivedCategory.Q.obj A)).mapIso eB).symm ≪≫
        T.comparison A B hA hB) ≪≫
    F.mapDerivedCategoryFactors.app (((tensorComplex X.O).obj A).obj B) ≪≫
    DerivedCategory.Q.mapIso (RingedSite.tensorComplexOverIso.{u + 1, u, u} X V A B) ≪≫
    (TV.comparison (X.restrictComplex A V) (X.restrictComplex B V) (hAW V) (hBW V)).symm ≪≫
    (TV.tensor.mapIso ((F.mapDerivedCategoryFactors.app A).symm ≪≫
      F.mapDerivedCategory.mapIso eA)).app _ ≪≫
    (TV.tensor.obj (F.mapDerivedCategory.obj K)).mapIso
      ((F.mapDerivedCategoryFactors.app B).symm ≪≫ F.mapDerivedCategory.mapIso eB)⟩

end Stacks.SheafOfModules.DerivedTensorProduct

end
