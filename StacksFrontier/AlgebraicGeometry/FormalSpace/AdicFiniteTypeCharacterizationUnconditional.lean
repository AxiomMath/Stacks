module

public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import
  StacksFrontier.AlgebraicGeometry.FormalSpace.AdicFiniteTypeCharacterizationWeaklyAdmissible
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineEtaleChartTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeCharacterizationRefined

/-!
# Characterising finite type morphisms of locally adic\* formal algebraic spaces, unconditionally

Let `S` be a scheme contained in a big fppf site `B`. **Stacks 0GC0** says that for a morphism
`f : X ⟶ Y` of locally adic\* formal algebraic spaces over `S` the four conditions listed in
`StacksFrontier.AlgebraicGeometry.FormalSpace.AdicFiniteTypeCharacterization` are equivalent. This
file proves it at the source's hypotheses, by the source's proof: the equivalence of conditions
(1) and (2) of Stacks 0GBW on charts together with Stacks 0ANW.

## Main results

* `AlgebraicGeometry.FormalSpace.chartPresentationIsAdicStarOfWeaklyAdmissible`: every weakly
  admissible topological ring presenting an affine formal algebraic space representable étale
  over a locally adic\* formal algebraic space is adic\*, from Stacks 0AKX for the adic\*
  property (`hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty_of_mem`) and
  Stacks 0AIC.
* `AlgebraicGeometry.FormalSpace.isLocallyOfFiniteType_tfae_of_isLocallyAdicStar`:
  **Stacks 0GC0**. It supersedes
  `AlgebraicGeometry.FormalSpace.isLocallyOfFiniteType_adicStar_tfae'` of
  `StacksFrontier.AlgebraicGeometry.FormalSpace.AdicFiniteTypeCharacterizationRefined`, which takes
  as `hchart` the statement that every ring presenting an affine chart is adic\*; only the
  weakly admissible presentations are needed, and for those it is
  `chartPresentationIsAdicStarOfWeaklyAdmissible`.

## References

* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AKX](https://stacks.math.columbia.edu/tag/0AKX)
* [Stacks Project, Tag 0ANW](https://stacks.math.columbia.edu/tag/0ANW)
* [Stacks Project, Tag 0GBW](https://stacks.math.columbia.edu/tag/0GBW)
* [Stacks Project, Tag 0GC0](https://stacks.math.columbia.edu/tag/0GC0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable (B S hS) in
/-- **The ring-level chart-type input, from Stacks 0AKX for the adic\* property.** Every
weakly admissible topological ring presenting an affine formal algebraic space representable
étale over a locally adic\* formal algebraic space over `S` is adic\*.

A locally adic\* formal algebraic space has an atlas of adic\* affine formal algebraic spaces,
so by the implication (2) ⟹ (1) of Stacks 0AKX
(`hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty_of_mem`, at the adic\*
property) every affine chart representable étale over it is adic\*; then every weakly
admissible ring presenting that chart is adic\* by `isAdicStar_presentation`, that is by
Stacks 0AIC. -/
theorem chartPresentationIsAdicStarOfWeaklyAdmissible :
    ChartPresentationIsAdicStarOfWeaklyAdmissible B S hS :=
  fun Z hZ U a hU ha A _ _ _ _ hA E e ↦
    isAdicStar_presentation
      ((hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty_of_mem B S hS Z hZ.1 _
        (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).2 hZ.2 U a hU ha) A hA E e

/-- **Stacks 0GC0.** Let `f : X ⟶ Y` be a morphism of locally adic\* formal algebraic spaces
over `S`. The following are equivalent:

1. for every commutative square with `U`, `V` affine formal algebraic spaces and `U ⟶ X`,
   `V ⟶ Y` representable by algebraic spaces and étale, the morphism `U ⟶ V` corresponds to an
   arrow of `WAdm^{adic*}` which is adic and topologically of finite type;
2. there are a covering `{Yⱼ ⟶ Y}` as in Definition 0AIM and for each `j` a covering
   `{Xⱼᵢ ⟶ Yⱼ ×_Y X}` as in Definition 0AIM such that each `Xⱼᵢ ⟶ Yⱼ` corresponds to an arrow
   of `WAdm^{adic*}` which is adic and topologically of finite type;
3. there are a covering `{Xᵢ ⟶ X}` as in Definition 0AIM and for each `i` a factorization
   `Xᵢ ⟶ Yᵢ ⟶ Y` where `Yᵢ` is an affine formal algebraic space, `Yᵢ ⟶ Y` is representable by
   algebraic spaces and étale, and `Xᵢ ⟶ Yᵢ` corresponds to an arrow of `WAdm^{adic*}` which
   is adic and topologically of finite type;
4. `f` is locally of finite type.

This is the source's proof. By Stacks 0AKX for the adic\* property together with Stacks 0AIC
(`chartPresentationIsAdicStarOfWeaklyAdmissible`) every weakly admissible ring presenting an
affine chart of `X` or `Y` is adic\*, so on each chart the adic, topologically of finite type
condition and the taut, topologically of finite type condition agree by Stacks 0GBW
(`hasPropertyOnAffineChartMap_adicStar_iff_of_isWeaklyAdmissible`); and Stacks 0ANW
(`isLocallyOfFiniteType_tfae'`), for the locally countably indexed spaces `X` and `Y`,
identifies the three resulting conditions with `f` being locally of finite type. -/
@[stacks 0GC0]
theorem isLocallyOfFiniteType_tfae_of_isLocallyAdicStar {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hX : IsLocallyAdicStar B S hS X) (hY : IsLocallyAdicStar B S hS Y) :
    List.TFAE
      [HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar
          TopologicalRing.IsAdicTopologicallyOfFiniteTypeHom f,
        HasPropertyAfterTargetCover B S hS TopologicalRing.IsAdicStar
          TopologicalRing.IsAdicTopologicallyOfFiniteTypeHom f,
        HasPropertyAfterSourceCover B S hS TopologicalRing.IsAdicStar
          TopologicalRing.IsAdicTopologicallyOfFiniteTypeHom f,
        IsLocallyOfFiniteType B S hS f] := by
  have hchart := chartPresentationIsAdicStarOfWeaklyAdmissible B S hS
  have hcount := isLocallyOfFiniteType_tfae' f
    (isLocallyCountablyIndexed_of_isLocallyAdicStar hX)
    (isLocallyCountablyIndexed_of_isLocallyAdicStar hY)
  tfae_have 1 ↔ 4 :=
    (hasPropertyOnEveryAffineEtaleDiagram_adicStar_iff_of_isWeaklyAdmissible hchart f hX hY).trans
      (hcount.out 1 4)
  tfae_have 2 ↔ 4 :=
    (hasPropertyAfterTargetCover_adicStar_iff_of_isWeaklyAdmissible hchart f hX hY).trans
      (hcount.out 2 4)
  tfae_have 3 ↔ 4 :=
    (hasPropertyAfterSourceCover_adicStar_iff_of_isWeaklyAdmissible hchart f hX hY).trans
      (hcount.out 3 4)
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
