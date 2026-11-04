module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSheafMapComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleComposition

/-!
# The chart restriction of the map of defining ideal sheaves is the map of the composite

Let `Z ⊆ X` and `Z' ⊆ X'` be closed subspaces of algebraic spaces over a scheme `S` contained in a
big fppf site `B`, let `g : X ⟶ X'` carry `Z` into `Z'`, and let `φ : h_V ⟶ X` be an étale scheme
chart of the *source* ambient space. Consider the chart inverse image

```
φ^*(idealSheafMap …) : φ^*g^*𝓘_{Z'} ⟶ φ^*𝓘_Z
```

of the map of defining ideal sheaves of [Stacks Project, Tag 04CP]. Its target is identified by
`AlgebraicGeometry.Space.chartModulePullbackDefiningIdealSheafIso`; its source is the inverse image
along `g ∘ φ`, which need not be étale (for the conormal sequences of [Stacks Project, Tag 06BD]
and [Stacks Project, Tag 06BF] the morphism `g` is a closed immersion).

Read through the chart identification of its target, that map **is the map of
[Stacks Project, Tag 04CP] of the composite `φ ≫ g`**, transported along the represented
comparison:

```
φ^*(idealSheafMap Z Z' g f hsq) ≫ (chartModulePullbackDefiningIdealSheafIso …).hom =
  (modulePullbackCompIso φ g).hom.app 𝓘_{Z'} ≫
    idealSheafMap (φ⁻¹Z) Z' (φ ≫ g) … ≫ (representedDefiningIdealSheafIso …).inv
```

The source of `idealSheafMap (φ⁻¹Z) Z' (φ ≫ g) …` is the inverse image along a morphism out of a
represented algebraic space.

## Main results

* `AlgebraicGeometry.Space.modulePullback_idealSheafMap_comp_chartDefiningIdealSheafIso`: the
  identity above.

## Implementation notes

The horizontal morphism `fV` of the square the chart cuts out and its commutativity `hsqV` are
hypotheses, and so is the commutativity `hsqOuter` of the outer rectangle along `φ ≫ g`, so that
the statement commits to no particular spelling of the composite morphism of subspaces.

## References

* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 06BD](https://stacks.math.columbia.edu/tag/06BD)
* [Stacks Project, Tag 06BF](https://stacks.math.columbia.edu/tag/06BF)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X X' : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (Z' : ClosedSubspaces B S hS X'.1) (g : X ⟶ X')
  (V : BigFppfOver B S hS) (hF : IsAlgebraicSpace B S hS (yoneda.obj V))
  (φ : (⟨yoneda.obj V, hF⟩ : AlgebraicSpaces B S hS) ⟶ X) (hφ : IsEtale B S hS φ.hom)

/-- **The chart inverse image of the map of defining ideal sheaves is the map of the composite.**

For a closed subspace `Z ⊆ X` carried into `Z' ⊆ X'` by `g : X ⟶ X'` and an étale scheme chart
`φ : h_V ⟶ X`, the inverse image along `φ` of the map `g^*𝓘_{Z'} ⟶ 𝓘_Z` of
[Stacks Project, Tag 04CP], followed by the chart identification
`AlgebraicGeometry.Space.chartModulePullbackDefiningIdealSheafIso` of its target, is the
composition comparison of [Stacks Project, Tag 03LU] followed by the map of
[Stacks Project, Tag 04CP] attached to the outer rectangle `φ⁻¹Z ⊆ h_V` over `Z' ⊆ X'` along
`φ ≫ g`, transported along the represented comparison. -/
theorem modulePullback_idealSheafMap_comp_chartDefiningIdealSheafIso
    (fV : (⟨(⟨Z.1.preimage φ.hom,
          isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 hF Z.2⟩ :
          ClosedSubspaces B S hS
            (⟨yoneda.obj V, hF⟩ : AlgebraicSpaces B S hS).1).1.toFunctor,
        (⟨Z.1.preimage φ.hom,
          isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 hF Z.2⟩ :
          ClosedSubspaces B S hS
            (⟨yoneda.obj V, hF⟩ : AlgebraicSpaces B S hS).1).2.1⟩ :
        AlgebraicSpaces B S hS) ⟶
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (hsqV : subspaceInclusion B S hS ⟨yoneda.obj V, hF⟩ (⟨Z.1.preimage φ.hom,
          isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 hF Z.2⟩ :
          ClosedSubspaces B S hS
            (⟨yoneda.obj V, hF⟩ : AlgebraicSpaces B S hS).1) ≫ φ =
        fV ≫ subspaceInclusion B S hS X Z)
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')
    (hsqOuter : subspaceInclusion B S hS ⟨yoneda.obj V, hF⟩ (⟨Z.1.preimage φ.hom,
          isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 hF Z.2⟩ :
          ClosedSubspaces B S hS
            (⟨yoneda.obj V, hF⟩ : AlgebraicSpaces B S hS).1) ≫ φ ≫ g =
        (fV ≫ f) ≫ subspaceInclusion B S hS X' Z') :
    (modulePullback B S hS φ).map (idealSheafMap B S hS Z Z' g f hsq) ≫
        (chartModulePullbackDefiningIdealSheafIso B S hS Z V hF φ hφ).hom =
      (modulePullbackCompIso B S hS φ g).hom.app
          (definingIdealSheaf B S hS X' Z').toSheafOfModules ≫
        idealSheafMap B S hS (⟨Z.1.preimage φ.hom,
              isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 hF Z.2⟩ :
              ClosedSubspaces B S hS
                (⟨yoneda.obj V, hF⟩ : AlgebraicSpaces B S hS).1)
            Z' (φ ≫ g) (fV ≫ f) hsqOuter ≫
          (representedDefiningIdealSheafIso B S hS V hF (⟨Z.1.preimage φ.hom,
            isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 hF Z.2⟩ :
            ClosedSubspaces B S hS
              (⟨yoneda.obj V, hF⟩ : AlgebraicSpaces B S hS).1)).inv := by
  have hc := idealSheafMap_comp B S hS φ g (⟨Z.1.preimage φ.hom,
      isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 hF Z.2⟩ :
      ClosedSubspaces B S hS (⟨yoneda.obj V, hF⟩ : AlgebraicSpaces B S hS).1)
    Z Z' fV f hsqV hsq hsqOuter
  have hchart := chartModulePullbackDefiningIdealSheafIso_hom_eq_idealSheafMap
    B S hS Z V hF φ hφ fV hsqV
  have hho := (congrArg (fun t => (modulePullbackCompIso B S hS φ g).hom.app
        (definingIdealSheaf B S hS X' Z').toSheafOfModules ≫ t) hc).trans
    ((Category.assoc _ _ _).symm.trans
      ((eq_whisker ((modulePullbackCompIso B S hS φ g).hom_inv_id_app
          (definingIdealSheaf B S hS X' Z').toSheafOfModules) _).trans
        (Category.id_comp _)))
  exact (congrArg (fun t => (modulePullback B S hS φ).map
        (idealSheafMap B S hS Z Z' g f hsq) ≫ t) hchart).trans
    ((Category.assoc _ _ _).symm.trans
      ((eq_whisker hho.symm _).trans (Category.assoc _ _ _)))

end AlgebraicGeometry.Space

end
