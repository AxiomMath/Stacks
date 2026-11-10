module

public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceFibreChartScheme
public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociatedTensorPullbackNecessity
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesMonoidal

/-!
# Transporting Bourbaki's formula from a chart diagram to an algebraic space

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, let `𝓕` be an `𝒪_X`-module and
`𝓖` an `𝒪_Y`-module. A *chart diagram* for `f` (`AlgebraicGeometry.Space.ChartDiagram`) is a
commuting square consisting of an étale chart `U` of `X`, an étale chart `V` of `Y` and a morphism
of the underlying schemes `q : U ⟶ V` over `f`. On such a square both sides of Bourbaki's formula
become *Zariski* statements about the schemes `U` and `V`: the left-hand side is weak association
in the sense of Stacks 056L at a point of `U`, and the right-hand side is weak association on `V`
together with membership in the Zariski relative assassin of `q`.

This file shows that, given the Zariski biconditional on the square, the étale biconditional holds
on the algebraic space, using the chart description of weak association of Stacks 0CTW.

## Main definitions

* `AlgebraicGeometry.Space.chartDiagramTensorPullback`: the Zariski module `𝓕|_U ⊗_{𝒪_U} q^*(𝓖|_V)`
  attached to a chart diagram.

## Main results

* `Stacks.Divisors.isWeaklyAssociatedPoint_iff_of_iso`: Zariski weak association at a point of a
  scheme is invariant under an isomorphism of `𝒪_X`-modules.
* `AlgebraicGeometry.Space.chartSchemeToPoints_chartDiagram`: a chart diagram commutes on points —
  the point of `Y` cut out by the image of `w` in the target chart scheme is the image under `|f|`
  of the point of `X` cut out by `w`.
* `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_tensor_modulePullback_iff_of_chartDiagram`:
  given the Zariski biconditional on a chart diagram and the comparison of `(𝓕 ⊗_{𝒪_X} f^*𝓖)|_U`
  with `𝓕|_U ⊗_{𝒪_U} q^*(𝓖|_V)`, Bourbaki's formula holds at the point of `X` cut out by `w`.

## Implementation notes

Quasi-coherence of `𝓕 ⊗_{𝒪_X} f^*𝓖` on the small étale site is an instance hypothesis, needed to
apply Stacks 0CTW on the left-hand side.

The module universe is that of the structure rings, which is the universe at which the tensor
product of `AlgebraicGeometry.Space.Modules` and Stacks 0CTW both exist.

## References

* [Stacks Project, Tag 0CTW](https://stacks.math.columbia.edu/tag/0CTW)
* [Stacks Project, Tag 0CTX](https://stacks.math.columbia.edu/tag/0CTX)
* [Stacks Project, Tag 0CUZ](https://stacks.math.columbia.edu/tag/0CUZ)
* [Stacks Project, Tag 0CV0](https://stacks.math.columbia.edu/tag/0CV0)
* [Stacks Project, Tag 056L](https://stacks.math.columbia.edu/tag/056L)
* [Stacks Project, Tag 05AV](https://stacks.math.columbia.edu/tag/05AV)
* [Stacks Project, Tag 03L6](https://stacks.math.columbia.edu/tag/03L6)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe u

namespace Stacks.Divisors

/-- Zariski weak association of a point of a scheme, in the sense of Stacks 056L, is invariant
under an isomorphism of `𝒪_X`-modules. -/
theorem isWeaklyAssociatedPoint_iff_of_iso {X : AlgebraicGeometry.Scheme.{u}}
    {F G : X.Modules} (e : F ≅ G) (x : X) :
    IsWeaklyAssociatedPoint F x ↔ IsWeaklyAssociatedPoint G x := by
  have key : ∀ {F G : X.Modules} (e : F ≅ G) (x : X),
      IsWeaklyAssociatedPoint F x → IsWeaklyAssociatedPoint G x := by
    intro F G e x hx
    let f : (F : OXModule X.toRingedSpace) ⟶ (G : OXModule X.toRingedSpace) := e.hom
    let g : (G : OXModule X.toRingedSpace) ⟶ (F : OXModule X.toRingedSpace) := e.inv
    have hf : Mono f := mono_of_mono_fac (show f ≫ g = 𝟙 _ from e.hom_inv_id)
    change IsWeaklyAssociatedPrime _ (OXModule.stalk F x) _ at hx
    change IsWeaklyAssociatedPrime _ (OXModule.stalk G x) _
    exact Module.weaklyAssociatedPrimes_subset_of_injective
      (f := OXModule.stalkLinearMap F G f x)
      (@OXModule.stalkMapAdd_injective_of_mono _ F G f hf x) hx
  exact ⟨key e x, key e.symm x⟩

end Stacks.Divisors

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- A chart diagram commutes on points: the point of `Y` determined by the image of `w` under the
vertical morphism of chart schemes is the image under `|f|` of the point of `X` determined by `w`.
-/
theorem chartSchemeToPoints_chartDiagram (f : X ⟶ Y)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (w : chartScheme d.U) :
    chartSchemeToPoints B S hS Y.1 d.V ((BigFppfOver.toScheme B S hS).map d.g w) =
      pointsMap B S hS X.1 f.hom (chartSchemeToPoints B S hS X.1 d.U w) := by
  set p := (canonicalSiteFieldPoint B S hS ((SmallEtale.toOver B S hS X.1).obj d.U) w).class B S hS
    (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj d.U))
  have h := congrFun (pointsMap_comp B S hS
    (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj d.U)) d.U.obj.hom f.hom) p
  rw [d.comm] at h
  rw [chartSchemeToPoints_eq_pointsMap, chartSchemeToPoints_eq_pointsMap,
    ← pointsMap_yoneda_map_class_canonicalSiteFieldPoint B S hS d.g w]
  exact (congrFun (pointsMap_comp B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj d.U))
    (yoneda.map d.g) d.V.obj.hom) p).symm.trans h

/-- The vertical morphism of chart schemes of a chart diagram. -/
noncomputable abbrev chartDiagramSchemeMap (f : X ⟶ Y)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) : chartScheme d.U ⟶ chartScheme d.V :=
  (BigFppfOver.toScheme B S hS).map d.g

/-- The restriction of an `𝒪_X`-module to the source chart of a chart diagram, read as a
module on the chart scheme. -/
noncomputable abbrev chartDiagramRestrictSource (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    (chartScheme d.U).Modules :=
  restrictToChart B S hS X.2 F d.U

/-- The restriction of an `𝒪_Y`-module to the target chart of a chart diagram, read as a
module on the chart scheme. -/
noncomputable abbrev chartDiagramRestrictTarget (f : X ⟶ Y)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    (chartScheme d.V).Modules :=
  restrictToChart B S hS Y.2 G d.V

/-- The Zariski `𝒪_U`-module `𝓕|_U ⊗_{𝒪_U} q^*(𝓖|_V)` attached to a chart diagram `d` for
`f : X ⟶ Y`, where `q` is the vertical morphism of chart schemes. -/
noncomputable abbrev chartDiagramTensorPullback (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) : (chartScheme d.U).Modules :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨(((chartScheme d.U).toRingedSpace)).presheaf,
      (((chartScheme d.U).toRingedSpace)).IsSheaf⟩).obj
    ((chartDiagramRestrictSource B S hS f F d))).obj
    (((Scheme.Modules.pullback (chartDiagramSchemeMap B S hS f d)).obj
      (chartDiagramRestrictTarget B S hS f G d))))

/-- Let `d` be a chart diagram for `f : X ⟶ Y` with vertical morphism of chart schemes `q`, and let
`w` be a point of the source chart scheme. Given the Zariski biconditional `hchart` on the square,
and the comparison `cmp` of `(𝓕 ⊗_{𝒪_X} f^*𝓖)|_U` with `𝓕|_U ⊗_{𝒪_U} q^*(𝓖|_V)`, the point of `X`
determined by `w` is weakly associated to `𝓕 ⊗_{𝒪_X} f^*𝓖` exactly when its image is weakly
associated to `𝓖` and it lies in the relative weak assassin `WeakAss_{X/Y}(𝓕)` of Stacks 0CV0. -/
theorem isWeaklyAssociatedPoint_tensor_modulePullback_iff_of_chartDiagram (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (G : Modules.{u, u} B S hS Y.1 Y.2)
    [(F ⊗ (modulePullback B S hS f).obj G).IsQuasicoherentOnSite] [G.IsQuasicoherentOnSite]
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (w : chartScheme d.U)
    (cmp : restrictToChart B S hS X.2 (F ⊗ (modulePullback B S hS f).obj G) d.U ≅
      chartDiagramTensorPullback B S hS f F G d)
    (hchart : Stacks.Divisors.IsWeaklyAssociatedPoint
          (chartDiagramTensorPullback B S hS f F G d) w ↔
        (Stacks.Divisors.IsWeaklyAssociatedPoint (chartDiagramRestrictTarget B S hS f G d)
            (chartDiagramSchemeMap B S hS f d w) ∧
          w ∈ Stacks.Divisors.relativeAssassin (chartDiagramSchemeMap B S hS f d)
            (chartDiagramRestrictSource B S hS f F d)))
    (hrel : w ∈ Stacks.Divisors.relativeAssassin (chartDiagramSchemeMap B S hS f d)
          (chartDiagramRestrictSource B S hS f F d) ↔
        IsRelativeWeaklyAssociatedPoint B S hS f F (chartSchemeToPoints B S hS X.1 d.U w)) :
    IsWeaklyAssociatedPoint B S hS X (F ⊗ (modulePullback B S hS f).obj G)
        (chartSchemeToPoints B S hS X.1 d.U w) ↔
      (IsWeaklyAssociatedPoint B S hS Y G
          (pointsMap B S hS X.1 f.hom (chartSchemeToPoints B S hS X.1 d.U w)) ∧
        IsRelativeWeaklyAssociatedPoint B S hS f F (chartSchemeToPoints B S hS X.1 d.U w)) := by
  have hV := isWeaklyAssociatedPoint_restrictToChart_iff_isWeaklyAssociatedPoint B S hS Y G d.V
      (chartDiagramSchemeMap B S hS f d w)
  rw [chartSchemeToPoints_chartDiagram B S hS f d w] at hV
  exact ((isWeaklyAssociatedPoint_restrictToChart_iff_isWeaklyAssociatedPoint B S hS X
      (F ⊗ (modulePullback B S hS f).obj G) d.U w).symm.trans
    ((Stacks.Divisors.isWeaklyAssociatedPoint_iff_of_iso cmp w).trans
      (hchart.trans (and_congr hV hrel))))

end AlgebraicGeometry.Space

end
