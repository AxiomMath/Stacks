module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceThetaMul
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartSourceMulShrink

/-!
# The chart maps of `θ` of Stacks 0D2Z are multiplicative: the scheme factor and the assembly

Let `w : W ⟶ U(ψ)` be a scheme point of the open subspace `U(ψ)` of Stacks 0D2Z.  The chart map
`χ_w = σ_w ≫ m_w ≫ τ_w` of `θ` at `w` (`…InvertibleTwistingRestriction.chartMap`) has as middle
factor `m_w` the module attached (Stacks 03DX (2)) to the map `θ` of [Stacks, Tag 01O9] on `W`,
read along the section `c_w : W ⟶ W ×_Y Proj_Y(𝒜)`
(`…InvertibleTwistingRestriction.chartSchemeTheta`).  This file carries the multiplicativity of
`…chartSchemeTheta` as morphisms of quasi-coherent modules on `W` to the represented algebraic
space of `W`, and deduces that the chart maps of `θ` are multiplicative.

## Main results

* `…InvertibleTwistingRestriction.representedTensorChartMul_comp_chartSchemeTheta_of_qcoh`: **the
  middle factor of the chart map is multiplicative at the represented level, from its
  quasi-coherent form**, between the multiplication to which the source factor carries the
  multiplication of the source of `θ` (`…chartSourceIso_hom_mul_shrink`) and the multiplication
  which the target factor carries to the multiplication of the target of `θ`
  (`AlgebraicGeometry.Space.pointTargetIso_symm_trans_hom_mul`).
* `…InvertibleTwistingRestriction.modulePullback_map_thetaSourceMul_comp_chartMap_of_qcoh`: **the
  chart maps are multiplicative**, from the same quasi-coherent hypothesis.

## Implementation notes

The statement is spelled over `s.shrink.site`, the site of the chart maps, with the multiplication
of the source in exactly the spelling of `…chartSourceIso_hom_mul_shrink`, so that the two squares
compose in `AlgebraicGeometry.Space.mul_of_factor_squares` without comparing two spellings of a
composite.  The proof is
`AlgebraicGeometry.Space.representedTensorChartMul_comp_map_hom_of_comp_eq` at the quasi-coherent
square.  `CategoryTheory.yoneda` is locally irreducible.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u m

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

namespace RelativeProjSituation.InvertibleTwistingRestriction

attribute [local irreducible] CategoryTheory.yoneda

section Represented

variable {s : RelativeProjSituation.{u, m}}
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} {f : X ⟶ s.shrink.space}
  {L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O)}
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  {ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L)}
  {W : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase}
  (w : yoneda.obj W ⟶ (locusSpaceOfUnitalHom s f L ψ).obj)

/-- **The middle factor of the chart map of `θ` is multiplicative, from its quasi-coherent form**
(Stacks 0D2Z): at a scheme point `w : W ⟶ U(ψ)`, if
`…InvertibleTwistingRestriction.chartSchemeTheta` carries the pullback along the section `c_w` of
the multiplication of the twists of Stacks 01NR, read through Stacks 03EL, to the multiplication
of the Laurent algebra `⨁_d (w^*ℒ)^{⊗ d}`, as morphisms of quasi-coherent modules on `W`, then
the attached modules (Stacks 03DX (2)) satisfy
`μ_M ≫ m_{i+j} = (m_i ⊗ m_j) ≫ μ_N`, with `μ_M` and `μ_N` the morphisms
`AlgebraicGeometry.Space.representedTensorChartMul` of the two multiplications. -/
theorem representedTensorChartMul_comp_chartSchemeTheta_of_qcoh (i j : ℤ)
    (hQ : ((quasicoherentPullbackTensorIso s.site s.base s.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
          (s.twistPieceQcoh W (locusPoint w ≫ f.hom) i)
          (s.twistPieceQcoh W (locusPoint w ≫ f.hom) j)).inv ≫
        quasicoherentPullbackMap s.site s.base s.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
          (s.twistPieceMul W (locusPoint w ≫ f.hom) i j)) ≫
        chartSchemeTheta s f L ψ (locusPoint w) (locusOpen_locusPoint w) (i + j) =
      quasicoherentTensorHom s.site s.base s.containsBase W
          (chartSchemeTheta s f L ψ (locusPoint w) (locusOpen_locusPoint w) i)
          (chartSchemeTheta s f L ψ (locusPoint w) (locusOpen_locusPoint w) j) ≫
        pointLaurentPieceMul L W (locusPoint w) i j) :
    representedTensorChartMul s.shrink.site s.shrink.base s.shrink.containsBase
        ((quasicoherentPullbackTensorIso s.shrink.site s.shrink.base s.shrink.containsBase
            ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
            (s.twistPieceQcoh W (locusPoint w ≫ f.hom) i)
            (s.twistPieceQcoh W (locusPoint w ≫ f.hom) j)).inv ≫
          quasicoherentPullbackMap s.shrink.site s.shrink.base s.shrink.containsBase
            ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
            (s.twistPieceMul W (locusPoint w ≫ f.hom) i j)) ≫
      ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
          s.shrink.containsBase W).functor.map
        (chartSchemeTheta s f L ψ (locusPoint w) (locusOpen_locusPoint w) (i + j))).hom =
    MonoidalCategoryStruct.tensorHom (C := Modules.{u, u} s.shrink.site s.shrink.base
        s.shrink.containsBase (yoneda.obj W)
        (isAlgebraicSpace_yoneda s.shrink.site s.shrink.base s.shrink.containsBase W))
      ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
          s.shrink.containsBase W).functor.map
        (chartSchemeTheta s f L ψ (locusPoint w) (locusOpen_locusPoint w) i)).hom
      ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
          s.shrink.containsBase W).functor.map
        (chartSchemeTheta s f L ψ (locusPoint w) (locusOpen_locusPoint w) j)).hom ≫
      representedTensorChartMul s.shrink.site s.shrink.base s.shrink.containsBase
        (pointLaurentPieceMul L W (locusPoint w) i j) :=
  representedTensorChartMul_comp_map_hom_of_comp_eq _ _ _ _ _ hQ

variable (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)

/-- **The chart map of `θ` is multiplicative, from the quasi-coherent multiplicativity of its
scheme factor** (Stacks 0D2Z): at a scheme point `w : W ⟶ U(ψ)`, the chart maps
`χ_w = σ_w ≫ m_w ≫ τ_w` (`…InvertibleTwistingRestriction.chartMap`) carry the inverse image along
`w` of the multiplication of the source of `θ` (`…InvertibleTwistingRestriction.thetaSourceMul`)
to the inverse image along `w` of the multiplication
`ℒ^{⊗ i}|_{U(ψ)} ⊗ ℒ^{⊗ j}|_{U(ψ)} ≅ (ℒ^{⊗ i} ⊗ ℒ^{⊗ j})|_{U(ψ)} ⟶ ℒ^{⊗ (i + j)}|_{U(ψ)}` of the
target, through the comparisons of Stacks 03EL, as soon as `…chartSchemeTheta` is multiplicative
as morphisms of quasi-coherent modules on `W` (`hQ`). -/
theorem modulePullback_map_thetaSourceMul_comp_chartMap_of_qcoh (i j : ℤ)
    (hQ : ((quasicoherentPullbackTensorIso s.site s.base s.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
          (s.twistPieceQcoh W (locusPoint w ≫ f.hom) i)
          (s.twistPieceQcoh W (locusPoint w ≫ f.hom) j)).inv ≫
        quasicoherentPullbackMap s.site s.base s.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
          (s.twistPieceMul W (locusPoint w ≫ f.hom) i j)) ≫
        chartSchemeTheta s f L ψ (locusPoint w) (locusOpen_locusPoint w) (i + j) =
      quasicoherentTensorHom s.site s.base s.containsBase W
          (chartSchemeTheta s f L ψ (locusPoint w) (locusOpen_locusPoint w) i)
          (chartSchemeTheta s f L ψ (locusPoint w) (locusOpen_locusPoint w) j) ≫
        pointLaurentPieceMul L W (locusPoint w) i j) :
    (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase
        (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w)).map
        (thetaSourceMul (ofUnitalHom s f L ψ) X.property Px i j :
          (thetaSourceOfUnitalHom s f L ψ Px i).obj ⊗ (thetaSourceOfUnitalHom s f L ψ Px j).obj ⟶
            (thetaSourceOfUnitalHom s f L ψ Px (i + j)).obj) ≫ chartMap Px w (i + j) =
      (modulePullbackTensorIso s.shrink.site s.shrink.base s.shrink.containsBase
          (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w)
          (thetaSourceOfUnitalHom s f L ψ Px i).obj (thetaSourceOfUnitalHom s f L ψ Px j).obj).hom ≫
        (chartMap Px w i ⊗ₘ chartMap Px w j) ≫
        (modulePullbackTensorIso s.shrink.site s.shrink.base s.shrink.containsBase
          (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w)
          (thetaTarget s f L ψ i).obj (thetaTarget s f L ψ j).obj).inv ≫
        (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase
          (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w)).map (thetaTargetMul s f L ψ i j) :=
  mul_of_factor_squares _ _ _ _ (chartSourceIso_hom_mul_shrink Px w i j)
    (representedTensorChartMul_comp_chartSchemeTheta_of_qcoh w i j hQ)
    (pointTargetIso_symm_trans_hom_mul_restrict L (locusInclusionOfUnitalHom s f L ψ) w
      (locusPoint w) (pointHom_locusPoint w) i j rfl rfl rfl)

end Represented

end RelativeProjSituation.InvertibleTwistingRestriction

end AlgebraicGeometry.Space

end
