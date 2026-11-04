module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartSourceMul

/-!
# The source factor of the chart maps of `θ` of Stacks 0D2Z is unital, over `s.shrink.site`

The chart maps `χ_w = σ_w ≫ m_w ≫ τ_w` of `θ` of [Stacks, Tag 0D2Z]
(`…InvertibleTwistingRestriction.chartMap`) are morphisms of modules over the site
`s.shrink.site`, while the unitality of their source factor `σ_w`
(`…InvertibleTwistingRestriction.chartSourceIso_hom_one`) is stated over `s.site`.  The two sites
are equal by definition (`…RelativeProjSituation.shrink_site`), but a statement read in one
spelling and checked in the other is expensive.  This file restates the unitality of `σ_w` over
`s.shrink.site`, the spelling of the hypothesis `hσ` of
`AlgebraicGeometry.Space.one_of_factor_squares` for a chart map.

## Main results

* `…InvertibleTwistingRestriction.unitChartSquare_of_heq`: **the bridge**: the square
  `(U_a⁻¹ ≫ a^*x) ≫ σ = (U_c⁻¹ ≫ c^*u)^a` (the conclusion of
  `…InvertibleTwistingRestriction.compTransportFibreToSpace_hom_one`) over a site `B₁` gives the
  same square over a site `B₂ = B₁`, for heterogeneously equal leaves.
* `…InvertibleTwistingRestriction.chartSourceIso_hom_one_shrink`: **the source identification of
  the chart maps is unital, over `s.shrink.site`**.
* `…InvertibleTwistingRestriction.modulePullback_map_thetaSourceUnit_chartMap_of_squares`:
  `AlgebraicGeometry.Space.one_of_factor_squares` for a chart map, with its source square
  discharged: the chart map carries the unit of the source of `θ` to a given morphism as soon as
  its middle and target factors do.

## Implementation notes

As in `…InvertibleTwistingRestriction.chartSourceShapedIso_heq`, the two spellings of the site are
compared only at the leaves (objects and morphisms of the site, algebraic spaces and their
morphisms, modules and their morphisms), each of which is the same term in both readings; the
bridge is proved by `subst`.  `CategoryTheory.yoneda` is locally irreducible in the instance, so
that the unifier, comparing the represented algebraic space of `W` in the two spellings, unfolds
the reducible constants around it rather than `yoneda` (as in
`…InvertibleTwistingRestriction.compTransportFibreToSpace_hom_one`); without it the comparison of
the instance with the bridge times out.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u m

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

section Bridge

/-- **The unit square of a source identification, read over a second spelling of the site.**
For a morphism `a : T ⟶ Y` of algebraic spaces with `T` represented, a morphism
`x : 𝒪_Y ⟶ M`, a morphism `c : T ⟶ F` of the site, a morphism `u : 𝒪_F ⟶ N` of quasi-coherent
modules on the scheme of `F` and an identification `σ : a^*M ≅ (c^*N)^a`, the square
`(U_a⁻¹ ≫ a^*x) ≫ σ = (U_c⁻¹ ≫ c^*u)^a` (Stacks 03LU, Stacks 03DX (2)) over the site `B₁` gives
the same square over a site `B₂ = B₁`, for heterogeneously equal leaves. -/
theorem unitChartSquare_of_heq {B₁ B₂ : BigFppfSite.{u}} (hB : B₁ = B₂) {S₁ S₂ : Scheme.{u}}
    (hSS : S₁ = S₂) {hS₁ : B₁.Contains S₁} {hS₂ : B₂.Contains S₂}
    {T₁ F₁ : BigFppfOver B₁ S₁ hS₁} {Y₁ : AlgebraicSpaces B₁ S₁ hS₁}
    {a₁ : (⟨yoneda.obj T₁, isAlgebraicSpace_yoneda B₁ S₁ hS₁ T₁⟩ : AlgebraicSpaces B₁ S₁ hS₁) ⟶ Y₁}
    {M₁ : Modules.{u, u} B₁ S₁ hS₁ Y₁.1 Y₁.2}
    {x₁ : SheafOfModules.unit (structureRingSheaf B₁ S₁ hS₁ Y₁) ⟶ M₁} {c₁ : T₁ ⟶ F₁}
    {N₁ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B₁ S₁ hS₁).obj F₁).ringCatSheaf).FullSubcategory}
    {u₁ : quasicoherentUnitObj B₁ S₁ hS₁ F₁ ⟶ N₁}
    {σ₁ : (modulePullback B₁ S₁ hS₁ a₁).obj M₁ ≅
      ((representedQuasicoherentSchemeEquivalence B₁ S₁ hS₁ T₁).functor.obj
        (quasicoherentPullbackObj B₁ S₁ hS₁ c₁ N₁)).obj}
    (H : ((modulePullbackUnitIso B₁ S₁ hS₁ a₁).inv ≫ (modulePullback B₁ S₁ hS₁ a₁).map x₁) ≫
        σ₁.hom =
      representedUnitChartHom B₁ S₁ hS₁
        ((quasicoherentPullbackUnitIso B₁ S₁ hS₁ c₁).inv ≫
          quasicoherentPullbackMap B₁ S₁ hS₁ c₁ u₁))
    {T₂ F₂ : BigFppfOver B₂ S₂ hS₂} {Y₂ : AlgebraicSpaces B₂ S₂ hS₂}
    (a₂ : (⟨yoneda.obj T₂, isAlgebraicSpace_yoneda B₂ S₂ hS₂ T₂⟩ : AlgebraicSpaces B₂ S₂ hS₂) ⟶ Y₂)
    {M₂ : Modules.{u, u} B₂ S₂ hS₂ Y₂.1 Y₂.2}
    (x₂ : SheafOfModules.unit (structureRingSheaf B₂ S₂ hS₂ Y₂) ⟶ M₂) (c₂ : T₂ ⟶ F₂)
    {N₂ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B₂ S₂ hS₂).obj F₂).ringCatSheaf).FullSubcategory}
    (u₂ : quasicoherentUnitObj B₂ S₂ hS₂ F₂ ⟶ N₂)
    (σ₂ : (modulePullback B₂ S₂ hS₂ a₂).obj M₂ ≅
      ((representedQuasicoherentSchemeEquivalence B₂ S₂ hS₂ T₂).functor.obj
        (quasicoherentPullbackObj B₂ S₂ hS₂ c₂ N₂)).obj)
    (hT : HEq T₁ T₂) (hF : HEq F₁ F₂) (hY : HEq Y₁ Y₂) (ha : HEq a₁ a₂) (hM : HEq M₁ M₂)
    (hx : HEq x₁ x₂) (hc : HEq c₁ c₂) (hN : HEq N₁ N₂) (hu : HEq u₁ u₂) (hσ : HEq σ₁ σ₂) :
    ((modulePullbackUnitIso B₂ S₂ hS₂ a₂).inv ≫ (modulePullback B₂ S₂ hS₂ a₂).map x₂) ≫
        σ₂.hom =
      representedUnitChartHom B₂ S₂ hS₂
        ((quasicoherentPullbackUnitIso B₂ S₂ hS₂ c₂).inv ≫
          quasicoherentPullbackMap B₂ S₂ hS₂ c₂ u₂) := by
  subst hB hSS
  obtain rfl : hS₁ = hS₂ := rfl
  subst hT hF hY
  subst ha hM hc hN
  subst hx hu hσ
  exact H

end Bridge

attribute [local irreducible] CategoryTheory.yoneda

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
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)
  {W : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase}
  (w : yoneda.obj W ⟶ (locusSpaceOfUnitalHom s f L ψ).obj)


/-- **The identification of the source of the chart map is unital, over `s.shrink.site`**
(Stacks 084D and 0D2Z): at a scheme point `w : W ⟶ U(ψ)`, the identification
`w^*(r^*𝒪(0)) ≅ (c_w^*𝒪(0))^a` (`…InvertibleTwistingRestriction.chartSourceIso`) carries the
inverse image along `w` of the unit of the source of `θ`
(`…InvertibleTwistingRestriction.thetaSourceUnit`), read through Stacks 03LU, to the morphism
attached (Stacks 03DX (2)) to the pullback along the section `c_w : W ⟶ W ×_Y Proj_Y(𝒜)` of the
unit of the twists of Stacks 01NR on `W ×_Y Proj_Y(𝒜)`; every functor and comparison is taken over
`s.shrink.site`, the site of the chart maps `…InvertibleTwistingRestriction.chartMap`.  This is the
hypothesis `hσ` of `AlgebraicGeometry.Space.one_of_factor_squares` for the source factor of a
chart map.  The `s.site` reading is `…InvertibleTwistingRestriction.chartSourceIso_hom_one`. -/
theorem chartSourceIso_hom_one_shrink :
    ((modulePullbackUnitIso s.shrink.site s.shrink.base s.shrink.containsBase
          (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w)).inv ≫
        (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase
          (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w)).map
          (thetaSourceUnit (ofUnitalHom s f L ψ) X.property Px)) ≫
      (chartSourceIso Px w (locusOpen_locusPoint w) 0).hom =
    representedUnitChartHom s.shrink.site s.shrink.base s.shrink.containsBase
      ((quasicoherentPullbackUnitIso s.shrink.site s.shrink.base s.shrink.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))).inv ≫
        quasicoherentPullbackMap s.shrink.site s.shrink.base s.shrink.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
          (s.twistPieceUnit W (locusPoint w ≫ f.hom))) :=
  unitChartSquare_of_heq s.shrink_site.symm s.shrink_base.symm (chartSourceIso_hom_one Px w)
    (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w)
    (thetaSourceUnit (ofUnitalHom s f L ψ) X.property Px)
    ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
    (s.twistPieceUnit W (locusPoint w ≫ f.hom))
    (chartSourceIso Px w (locusOpen_locusPoint w) 0)
    HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl

/-- **The chart map carries the unit of the source of `θ` to a given morphism, from the squares
of its middle and target factors** (Stacks 0D2Z): at a scheme point `w : W ⟶ U(ψ)`, if the middle
factor of `χ_w` (`…InvertibleTwistingRestriction.chartSchemeTheta`, read through Stacks 03DX (2))
carries the morphism attached to the pullback along `c_w` of the unit of the twists to `ν`, and
the target factor (`…InvertibleTwistingRestriction.chartTargetIso`) carries `ν` to
`U⁻¹ ≫ x` (`U` the comparison of Stacks 03LU along `w`), then the inverse image along `w` of the
unit of the source of `θ` (`…InvertibleTwistingRestriction.thetaSourceUnit`), followed by `χ_w`,
is `x`.  This is `AlgebraicGeometry.Space.one_of_factor_squares` for
`χ_w = σ_w ≫ m_w ≫ τ_w` with the source square `hσ` discharged by
`…InvertibleTwistingRestriction.chartSourceIso_hom_one_shrink`; with `x` the inverse image of the
unit of the target, it is the hypothesis of
`AlgebraicGeometry.Space.comp_pointFamilyDescendedHom_eq` at `w`. -/
theorem modulePullback_map_thetaSourceUnit_chartMap_of_squares
    {ν : SheafOfModules.unit (representedStructureRingSheaf s.shrink.site s.shrink.base
        s.shrink.containsBase W) ⟶
      ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
        s.shrink.containsBase W).functor.obj (pointLaurentPieceQcoh L W (locusPoint w) 0)).obj}
    {x : (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase
        (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w)).obj
        (SheafOfModules.unit (structureRingSheaf s.shrink.site s.shrink.base s.shrink.containsBase
          (locusSpaceOfUnitalHom s f L ψ))) ⟶
      (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase
        (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w)).obj (thetaTarget s f L ψ 0).obj}
    (hm : representedUnitChartHom s.shrink.site s.shrink.base s.shrink.containsBase
        ((quasicoherentPullbackUnitIso s.shrink.site s.shrink.base s.shrink.containsBase
            ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))).inv ≫
          quasicoherentPullbackMap s.shrink.site s.shrink.base s.shrink.containsBase
            ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
            (s.twistPieceUnit W (locusPoint w ≫ f.hom))) ≫
        ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
          s.shrink.containsBase W).functor.map
          (chartSchemeTheta s f L ψ (locusPoint w) (locusOpen_locusPoint w) 0)).hom = ν)
    (hτ : ν ≫ (chartTargetIso w 0).hom =
      (modulePullbackUnitIso s.shrink.site s.shrink.base s.shrink.containsBase
        (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w)).inv ≫ x) :
    (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase
        (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w)).map
        (thetaSourceUnit (ofUnitalHom s f L ψ) X.property Px) ≫ chartMap Px w 0 = x :=
  one_of_factor_squares
    (modulePullbackUnitIso s.shrink.site s.shrink.base s.shrink.containsBase
      (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w)).symm
    (modulePullbackUnitIso s.shrink.site s.shrink.base s.shrink.containsBase
      (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w)).symm _ x
    (chartSourceIso_hom_one_shrink Px w : _) hm hτ rfl

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
