module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackIsAlgebraic
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedStackAlgebraicMorphismAssembly
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProperLimitOfFinitePresentationEmbedding

/-!
# The forgetful 1-morphism `Polarized ⟶ Spaces'_{fp, flat, proper}` is algebraic

Stacks 0D41 says that the forgetful functor of Stacks 0D3Y

```text
  Polarized ⟶ Spaces'_{fp, flat, proper},   (X ⟶ S, ℒ) ↦ (X ⟶ S)
```

is a 1-morphism of stacks in groupoids over `Sch_fppf` which is algebraic in the sense of
Stacks 06CF: for every scheme `S` and every object `ξ = (X ⟶ S)` of
`Spaces'_{fp, flat, proper}` over `S`, the 2-fibre product
`(Sch/S)_{fppf} ×_{ξ, Spaces'_{fp, flat, proper}} Polarized` is an algebraic stack.

The absolute site `Sch_fppf` is the big fppf site of the terminal scheme `Spec ℤ`, over which
`AlgebraicGeometry.polarizedStackInGroupoids` (with the stack condition of Stacks 0D40,
`AlgebraicGeometry.polarizedProjection_isStack`) and
`AlgebraicGeometry.properFlatSpacesStackInGroupoids` (Stacks 0D1G) present the two stacks, and
`AlgebraicGeometry.forgetPolarizationBased` is the forgetful functor of Stacks 0D3Y.

The proof is the one of the source. At a scheme-valued point `X₀ ⟶ V₀`, the base change of
`Polarized` is equivalent over the site to the relatively ample locus of the Picard stack
`Picardstack_{X₀/V₀}`
(`AlgebraicGeometry.isAlgebraicMorphism_forgetPolarizationBased_of_picard`). That locus is open by
Stacks 0D3D
(`AlgebraicGeometry.Space.exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_isProper`), and
`Picardstack_{X₀/V₀}` is an algebraic stack by Stacks 0D04
(`AlgebraicGeometry.Space.isAlgebraicStack_picardCFG`).

## Main results

* `AlgebraicGeometry.isAlgebraicMorphism_forgetPolarizationOneMorphism`: **Stacks 0D41**.

## References

* [Stacks Project, Tag 0D41](https://stacks.math.columbia.edu/tag/0D41)
* [Stacks Project, Tag 0D3Y](https://stacks.math.columbia.edu/tag/0D3Y)
* [Stacks Project, Tag 0D40](https://stacks.math.columbia.edu/tag/0D40)
* [Stacks Project, Tag 0D1G](https://stacks.math.columbia.edu/tag/0D1G)
* [Stacks Project, Tag 0D04](https://stacks.math.columbia.edu/tag/0D04)
* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
* [Stacks Project, Tag 06CF](https://stacks.math.columbia.edu/tag/06CF)
-/

@[expose] public noncomputable section

universe w u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u})

/-- **Stacks 0D41.** The forgetful functor of Stacks 0D3Y, `(X ⟶ S, ℒ) ↦ (X ⟶ S)`, defines a
1-morphism `Polarized ⟶ Spaces'_{fp, flat, proper}` of stacks in groupoids over the big fppf site
of `Spec ℤ` (Stacks 0D40, 0D1G) which is algebraic in the sense of Stacks 06CF: its 2-fibre
product with every scheme-valued point of `Spaces'_{fp, flat, proper}` is an algebraic stack. -/
@[stacks 0D41]
theorem isAlgebraicMorphism_forgetPolarizationOneMorphism :
    Stack.IsAlgebraicMorphism.{u, w, w, w} B integerBase B.contains_integerBase
      (𝒳 := polarizedStackInGroupoids.{w} B (polarizedProjection_isStack B))
      (𝒴 := properFlatSpacesStackInGroupoids.{w} B integerBase B.contains_integerBase)
      (forgetPolarizationBased B) :=
  isAlgebraicMorphism_forgetPolarizationBased_of_picard B
    (fun X₀ => Space.isAlgebraicStack_picardCFG (properFlatCoherentSituation X₀)
      (properFlatCoherentSituation_isFlat X₀) (properFlatCoherentSituation_isProper X₀))
    (@fun _ _ _ hf _ hL => Space.exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_isProper
      B integerBase B.contains_integerBase hf hL)

end AlgebraicGeometry

end
