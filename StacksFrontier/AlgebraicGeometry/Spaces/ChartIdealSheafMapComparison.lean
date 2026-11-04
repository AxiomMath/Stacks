module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleStructureModulePullbackMap
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedIdealSheafMapDefiningIso

/-!
# The chart comparison of defining ideal sheaves is the map of [Stacks Project, Tag 04CP]

Let `Z ⊆ X` be a closed subspace of an algebraic space over a scheme `S` contained in a big fppf
site `B`, and let `φ : h_V ⟶ X` be an étale scheme chart of `X`, represented by an object `V` of
the big fppf category. The isomorphism
`AlgebraicGeometry.Space.chartModulePullbackDefiningIdealSheafIso` between the chart inverse image
`φ^*𝓘_Z` and `ε^*` of a Zariski sheaf of ideals of the chart scheme is the map
`φ^*𝓘_Z ⟶ 𝓘_{φ^{-1}Z}` of defining ideal sheaves of [Stacks Project, Tag 04CP], transported along
the represented comparison:

```
(chartModulePullbackDefiningIdealSheafIso …).hom =
  idealSheafMap … ≫ (representedDefiningIdealSheafIso …).inv
```

## Main results

* `AlgebraicGeometry.Space.etaleModulePullback_map_definingIdealSheaf_ι`: the étale restriction
  of the inclusion `𝓘_Z ⊆ 𝒪_X` is the comparison of [Stacks Project, Tag 04CO] followed by the
  inclusion `𝓘_{φ^{-1}Z} ⊆ 𝒪_{h_V}`.
* `AlgebraicGeometry.Space.chartModulePullbackDefiningIdealSheafIso_hom_comp_comparison`:
  the chart comparison followed by the comparison map `ε^*I ⟶ 𝒪_{h_V}` is the inverse image of
  the inclusion `𝓘_Z ⊆ 𝒪_X` followed by `AlgebraicGeometry.Space.structureModulePullbackMap`.
* `AlgebraicGeometry.Space.chartModulePullbackDefiningIdealSheafIso_hom_eq_idealSheafMap`:
  the chart comparison of defining ideal sheaves is the map of [Stacks Project, Tag 04CP].

## References

* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The comparison of [Stacks Project, Tag 04CO] against the structure sheaf -/

/-- **The étale restriction of the inclusion of a defining ideal sheaf.** For an étale morphism
`φ : U ⟶ X` of algebraic spaces and a closed subspace `Z ⊆ X`, the étale restriction of the
inclusion `𝓘_Z ⊆ 𝒪_X` is the comparison of [Stacks Project, Tag 04CO] followed by the inclusion
`𝓘_{φ^{-1}Z} ⊆ 𝒪_U`. -/
theorem etaleModulePullback_map_definingIdealSheaf_ι {U X : AlgebraicSpaces B S hS} (φ : U ⟶ X)
    (hφ : IsEtale B S hS φ.hom) (Z : ClosedSubspaces B S hS X.1) :
    (etaleModulePullback.{u, u} B S hS φ hφ).map (definingIdealSheaf B S hS X Z).ι =
      (etaleIdealSheafRestrictionIso B S hS φ hφ Z).hom ≫
        (definingIdealSheaf B S hS U (⟨Z.1.preimage φ.hom,
          isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩ :
          ClosedSubspaces B S hS U.1)).ι :=
  modulesHom_ext (fun _ _ ↦ rfl)

/-! ### The chart comparison is the map of defining ideal sheaves -/

variable {X : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (V : BigFppfOver B S hS) (hF : IsAlgebraicSpace B S hS (yoneda.obj V))
  (φ : (⟨yoneda.obj V, hF⟩ : AlgebraicSpaces B S hS) ⟶ X) (hφ : IsEtale B S hS φ.hom)

/-- **The chart comparison against the comparison map `ε^*I ⟶ 𝒪_{h_V}`.** The isomorphism
`AlgebraicGeometry.Space.chartModulePullbackDefiningIdealSheafIso`, followed by
`AlgebraicGeometry.Space.representedIdealComparison`, is the inverse image along `φ` of the
inclusion `𝓘_Z ⊆ 𝒪_X` read in `𝒪_{h_V}` through
`AlgebraicGeometry.Space.structureModulePullbackMap`. -/
theorem chartModulePullbackDefiningIdealSheafIso_hom_comp_comparison :
    (chartModulePullbackDefiningIdealSheafIso B S hS Z V hF φ hφ).hom ≫
        representedIdealComparison B S hS V hF
          (schemeSpaceIdeal B S hS V ⟨Z.1.preimage φ.hom,
            isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 hF Z.2⟩) =
      (modulePullback B S hS φ).map (definingIdealSheaf B S hS X Z).ι ≫
        structureModulePullbackMap B S hS φ :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun t => (modulePullbackIsoEtaleModulePullback B S hS φ hφ).hom.app
            (definingIdealSheaf B S hS X Z).toSheafOfModules ≫ t)
        ((Category.assoc _ _ _).trans
          ((congrArg (fun t => (etaleIdealSheafRestrictionIso B S hS φ hφ Z).hom ≫ t)
              (representedDefiningIdealSheafIso_inv_comp_representedIdealComparison
                B S hS V hF (⟨Z.1.preimage φ.hom,
                  isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 hF Z.2⟩ :
                  ClosedSubspaces B S hS
                    (⟨yoneda.obj V, hF⟩ : AlgebraicSpaces B S hS).1))).trans
            (etaleModulePullback_map_definingIdealSheaf_ι B S hS φ hφ Z).symm))).trans
      (((modulePullbackIsoEtaleModulePullback B S hS φ hφ).hom.naturality
            (definingIdealSheaf B S hS X Z).ι).symm.trans
        (congrArg (fun t => (modulePullback B S hS φ).map
            (definingIdealSheaf B S hS X Z).ι ≫ t)
          (modulePullbackIsoEtaleModulePullback_hom_app_unit_eq B S hS φ hφ))))

/-- **The chart comparison of defining ideal sheaves is the map of [Stacks Project, Tag 04CP].**
For a commutative square exhibiting `φ^{-1}Z ⊆ h_V` over `Z ⊆ X` along an étale scheme chart
`φ : h_V ⟶ X`, the isomorphism
`AlgebraicGeometry.Space.chartModulePullbackDefiningIdealSheafIso` is the map `φ^*𝓘_Z ⟶
𝓘_{φ^{-1}Z}` of defining ideal sheaves, transported along
`AlgebraicGeometry.Space.representedDefiningIdealSheafIso`. -/
theorem chartModulePullbackDefiningIdealSheafIso_hom_eq_idealSheafMap
    (f : (⟨(⟨Z.1.preimage φ.hom,
        isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 hF Z.2⟩ :
        ClosedSubspaces B S hS (⟨yoneda.obj V, hF⟩ : AlgebraicSpaces B S hS).1).1.toFunctor,
      (⟨Z.1.preimage φ.hom,
        isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 hF Z.2⟩ :
        ClosedSubspaces B S hS
          (⟨yoneda.obj V, hF⟩ : AlgebraicSpaces B S hS).1).2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS ⟨yoneda.obj V, hF⟩ (⟨Z.1.preimage φ.hom,
          isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 hF Z.2⟩ :
          ClosedSubspaces B S hS (⟨yoneda.obj V, hF⟩ : AlgebraicSpaces B S hS).1) ≫ φ =
      f ≫ subspaceInclusion B S hS X Z) :
    (chartModulePullbackDefiningIdealSheafIso B S hS Z V hF φ hφ).hom =
      idealSheafMap B S hS (⟨Z.1.preimage φ.hom,
          isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 hF Z.2⟩ :
          ClosedSubspaces B S hS (⟨yoneda.obj V, hF⟩ : AlgebraicSpaces B S hS).1) Z φ f hsq ≫
        (representedDefiningIdealSheafIso B S hS V hF (⟨Z.1.preimage φ.hom,
          isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 hF Z.2⟩ :
          ClosedSubspaces B S hS (⟨yoneda.obj V, hF⟩ : AlgebraicSpaces B S hS).1)).inv :=
  eq_idealSheafMap_comp_representedDefiningIdealSheafIso_inv B S hS V hF _ Z φ f hsq _
    (chartModulePullbackDefiningIdealSheafIso_hom_comp_comparison
      B S hS Z V hF φ hφ)

end AlgebraicGeometry.Space

end
