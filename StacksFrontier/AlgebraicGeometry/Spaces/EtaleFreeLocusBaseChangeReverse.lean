module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricFibreEtaleFreeLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricFibreStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams

/-!
# The reverse inclusion of the base-change clause of Stacks 0CZT

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which is
locally of finite presentation, let `F` be a finitely presented `𝒪_X`-module flat over `Y`, and let

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

be a cartesian square.  Stacks 0CZT says that the locus

```
W = {x ∈ |X| : F is free in an étale neighbourhood of x}
```

commutes with the base change, that is `W' = |g'|⁻¹(W)`.  This file proves the inclusion
`W' ⊆ |g'|⁻¹(W)` at the finite-free reading `AlgebraicGeometry.Space.etaleFiniteFreeLocus` of `W`,
with membership upstairs read at a geometric point of `X'` in the source's own Zariski-chart sense
of clause (4) of Stacks 0CZS.  The other inclusion, `|g'|⁻¹(W) ⊆ W'`, is
`AlgebraicGeometry.Space.preimage_etaleFreeLocus_subset`.

## Main results

* `mem_etaleFiniteFreeLocus_of_isFiniteFreeNearGeometricPoint_modulePullback`: the inclusion
  `W' ⊆ |g'|⁻¹(W)` of the base-change clause of Stacks 0CZT.

## References

* [Stacks Project, Tag 0CZT](https://stacks.math.columbia.edu/tag/0CZT)
* [Stacks Project, Tag 0CZS](https://stacks.math.columbia.edu/tag/0CZS)
* [Stacks Project, Tag 05WY](https://stacks.math.columbia.edu/tag/05WY)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The reverse inclusion of the base-change clause.**  Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` which is locally of finite presentation, let `F` be a quasi-coherent
`𝒪_X`-module of finite presentation on charts which is flat over `Y`, and let

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

be a cartesian square.  If the inverse image `(g')^*F` is finite free in an étale neighbourhood of
a geometric point `x̄'` of `X'` — clause (4) of Stacks 0CZS in the source's Zariski-chart reading —
then the image of `x̄'` in `|X|` lies in the finite-free étale locus of `F`. -/
@[stacks 0CZT "the reverse inclusion W' ⊆ |g'|^{-1}(W) of the base-change clause, with membership \
in W' read at a geometric point xbar' of X' in the source's own Zariski-chart reading of clause \
(4) of Stacks 0CZS -- a Zariski open of an etale SCHEME chart of X' on which the chart restriction \
of (g')^*F is finite free -- and W the locus of points of |X| admitting an etale morphism of \
algebraic spaces through them along which the inverse image of F is finite free in the sense of \
03DE(2)"]
theorem mem_etaleFiniteFreeLocus_of_isFiniteFreeNearGeometricPoint_modulePullback
    {X Y X' Y' : AlgebraicSpaces B S hS} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (hpb : IsPullback g' f' f g) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (hfp : IsFinitePresentationOnCharts B S hS X.2 F)
    (hF : IsFlatOver B S hS X.2 f.hom F) (xbar' : GeometricPoint B S hS X'.1)
    (h : IsFiniteFreeNearGeometricPoint B S hS xbar' ((modulePullback B S hS g').obj F)) :
    pointsMap B S hS X'.1 g'.hom xbar'.image ∈ etaleFiniteFreeLocus B S hS F := by
  have : ((modulePullback B S hS g').obj F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g' F inferInstance
  have h1 : Module.Flat (geometricFibreLocalRing B S hS f' xbar')
      (geometricFibreModuleStalk B S hS f' ((modulePullback B S hS g').obj F) xbar') :=
    flat_geometricFibreModuleStalk_of_free B S hS f' _ xbar'
      (free_geometricFibreModuleStalk_of_isFiniteFreeNearGeometricPoint B S hS f' _ xbar' h)
  have h2 := (flat_geometricFibreModuleStalk_modulePullback_iff B S hS hpb F xbar').2 h1
  have hres := mem_etaleFiniteFreeLocus_of_flat_geometricFibreModuleStalk B S hS f F hf hfp
    (geometricPointMap g'.hom xbar')
    ((isFlatOver_iff_forall_isFlatOverAtGeometricPoint B S hS f F).mp hF _) h2
  rwa [geometricPointMap_image] at hres

end AlgebraicGeometry.Space

end
