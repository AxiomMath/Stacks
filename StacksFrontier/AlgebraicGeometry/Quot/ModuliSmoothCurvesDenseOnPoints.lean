module

public import StacksFrontier.AlgebraicGeometry.Quot.ModuliSmoothCurvesStable
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedInducedSubstackLocallyClosed

/-!
# `|𝓜_g|` is dense in `|𝓜̄_g|`, read on the points of `𝓜̄_g` (towards Stacks 0E87)

Stacks 0E87 says that for `g ≥ 2` the inclusion `|𝓜_g| ⊂ |𝓜̄_g|` is that of an open dense subset.
`AlgebraicGeometry.isOpen_dense_pointSet_moduliSmoothOfGenus_in_stableOfGenus_of_two_le` states
it with `|𝓜̄_g|` read as its point set inside `|Curves|`, the range of the map on points of the
inclusion of the open substack. This file restates its density part with `|𝓜̄_g|` read as the
topological space of points of the algebraic stack `𝓜̄_g` itself.

The two readings agree because the map on points of an open immersion of algebraic stacks is an
embedding (Stacks 04XL with Stacks 0ABJ, read through an immersion): it is a homeomorphism of
`|𝓜̄_g|` onto its point set in `|Curves|`, and a homeomorphism preserves dense subsets.

## Main results

* `AlgebraicGeometry.Stack.OpenSubstack.dense_preimage_pointsMap_inclusion_iff`: for an open
  substack `𝒲` of an algebraic stack `𝒳` and a set `T` of points of `𝒳`, the points of `𝒲` mapping
  into `T` are dense in `|𝒲|` exactly when `T` is dense in the point set of `𝒲` inside `|𝒳|`.
* `AlgebraicGeometry.dense_preimage_pointSet_moduliSmoothOfGenus_of_two_le`: the density part of
  Stacks 0E87 on the points of `𝓜̄_g`, given the algebraicity of the stack of curves (`h`,
  Stacks 0D5A), the openness of `𝓜̄_g` and of `𝓜_g` (`hP`, Stacks 0E78; `hQ`, Stacks 0E83), and
  the genus of the fibres of a prestable family of genus `g` (`h0E6V`, what Stacks 0E6V gives).

## References

* [Stacks Project, Tag 0E87](https://stacks.math.columbia.edu/tag/0E87)
* [Stacks Project, Tag 0E9A](https://stacks.math.columbia.edu/tag/0E9A)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 0ABJ](https://stacks.math.columbia.edu/tag/0ABJ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w

namespace AlgebraicGeometry

namespace Stack.OpenSubstack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Density on the points of an open substack.** Let `𝒲` be an open substack of an algebraic
stack `𝒳` and `T` a set of points of `𝒳`. The points of `𝒲` whose image lies in `T` are dense in
`|𝒲|` exactly when `T` is dense in the point set `|𝒲| ⊂ |𝒳|` of `𝒲`. -/
theorem dense_preimage_pointsMap_inclusion_iff {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (W : OpenSubstack 𝒳) (T : Set (AlgebraicStacks.points B S hS 𝒳)) :
    letI := pointTopology B S hS 𝒳.val
    @Dense _ (pointTopology B S hS W.toAlgebraicStack.val)
        (AlgebraicStacks.pointsMap B S hS W.inclusion ⁻¹' T) ↔
      Dense (Subtype.val ⁻¹' T : Set (W.pointSet B S hS)) := by
  let := pointTopology B S hS 𝒳.val
  let := pointTopology B S hS W.toAlgebraicStack.val
  have he := AlgebraicStacks.isEmbedding_pointsMap_of_isImmersion B S hS W.inclusion
    (AlgebraicStacks.isImmersion_of_isOpenImmersion B S hS _ W.isOpenImmersion)
  let φ := he.toHomeomorph
  have hpre : AlgebraicStacks.pointsMap B S hS W.inclusion ⁻¹' T =
      φ ⁻¹' (Subtype.val ⁻¹' T : Set (W.pointSet B S hS)) := rfl
  rw [hpre]
  exact φ.isOpenQuotientMap.dense_preimage_iff

end Stack.OpenSubstack

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)

/-- **The density of `|𝓜_g|` in `|𝓜̄_g|`, on the points of `𝓜̄_g`** (the density part of Stacks
0E87). Let `g ≥ 2` and let `𝓜̄_g` and `𝓜_g` be
the open substacks of the small model of the stack of curves cut out by being stable of genus `g`
(`hP`) and by being smooth with `f_*𝒪_X = 𝒪_S` universally and of genus `g` (`hQ`). Then the points
of `𝓜̄_g` lying in `𝓜_g` are dense in the topological space `|𝓜̄_g|`. Here `h0E6V` is the
genus of the fibres of a prestable family of genus `g`, what Stacks 0E6V gives. -/
theorem dense_preimage_pointSet_moduliSmoothOfGenus_of_two_le (g : ℕ) (hg : 2 ≤ g)
    (h0E6V : ∀ F : CurveFamily B hZ, IsPrestableCurveFamily B hZ F →
      CurveFamily.HasGenus B hZ F g →
      ∀ (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace F.base).obj)
        (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject)
        (q : yoneda.obj V ⟶ F.total.obj),
        IsPullback q (yoneda.map v) F.toBase.hom (yonedaEquiv.symm p.value) →
          genus ((BigFppfOver.toScheme B integerBase hZ).map v) = g)
    (hP : IsOpenCurvesLocus B hZ (IsStableCurveFamilyOfGenus B hZ g))
    (hQ : IsOpenCurvesLocus B hZ
      (fun X => IsSmoothH0Family B hZ X ∧ CurveFamily.HasGenus B hZ X g)) :
    @Dense _ (Stack.pointTopology B integerBase hZ
        (curvesSmallOpenSubstack B hZ h hP).toAlgebraicStack.val)
      (Stack.AlgebraicStacks.pointsMap B integerBase hZ
          (curvesSmallOpenSubstack B hZ h hP).inclusion ⁻¹'
        (curvesSmallOpenSubstack B hZ h hQ).pointSet B integerBase hZ) :=
  (Stack.OpenSubstack.dense_preimage_pointsMap_inclusion_iff B integerBase hZ _ _).2
    (isOpen_dense_pointSet_moduliSmoothOfGenus_in_stableOfGenus_of_two_le B hZ h g hg h0E6V hP
      hQ).2.2

end AlgebraicGeometry

end
