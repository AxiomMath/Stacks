module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceThetaMul

/-!
# The scheme factor of the chart maps of `θ` of Stacks 0D2Z is unital at the represented level

Let `w : W ⟶ U(ψ)` be a scheme point of the open subspace `U(ψ)` of Stacks 0D2Z.  The chart map
`χ_w = σ_w ≫ m_w ≫ τ_w` of `θ` at `w` (`…InvertibleTwistingRestriction.chartMap`) has as middle
factor `m_w` the module attached (Stacks 03DX (2)) to the map `θ` of [Stacks, Tag 01O9] on `W`,
read along the section `c_w : W ⟶ W ×_Y Proj_Y(𝒜)`
(`…InvertibleTwistingRestriction.chartSchemeTheta`).  Its unitality on the schemes is
`…InvertibleTwistingRestriction.pullbackUnitIso_inv_comp_map_oneHom_comp_chartTheta`; this file
carries it to the quasi-coherent modules on `W` and to the represented algebraic space of `W`,
where it is the middle square `hm` of `AlgebraicGeometry.Space.one_of_factor_squares` for the
chart maps.

## Main results

* `AlgebraicGeometry.Space.quasicoherentPullbackUnit_comp_eq_of_heq`: the gluing of a unital
  triangle of quasi-coherent modules from its scheme-level form, at free variables, with the leaves
  of a second spelling (that of `…GradedPowerMap`) heterogeneously equal to those of the first.
* `…InvertibleTwistingRestriction.quasicoherentPullbackUnit_comp_chartSchemeTheta`: **`θ` at a
  scheme point is unital, as morphisms of quasi-coherent modules on `W`**:
  `…chartSchemeTheta` in degree `0` carries the pullback along `c_w` of the unit of the twists of
  Stacks 01NR to the unit of the Laurent algebra `⨁_d (w^*ℒ)^{⊗ d}`.
* `…InvertibleTwistingRestriction.representedUnitChartHom_comp_chartSchemeTheta`: **the middle
  factor of the chart map is unital at the represented level**: the hypothesis `hm` of
  `AlgebraicGeometry.Space.one_of_factor_squares` for `…chartMap`, between the unit of the source
  factor (`…chartSourceIso_hom_one`) and the unit of the target factor
  (`AlgebraicGeometry.Space.pointTargetIso_symm_trans_hom_one`).

## Implementation notes

The quasi-coherent statement is glued from the scheme-level one by
`AlgebraicGeometry.Space.quasicoherentPullbackUnit_comp_eq_of_heq`, whose leaves on the two
sides — the scheme `Proj_W((f ∘ w)^*𝒜)` in the spelling of `…chartSchemeTheta`
(`s.shrink.pointAlgebra`) and in that of `…GradedPowerMap` (`s.relativeProjPoints.algebra`), the
maps, the twists and the units — are variables tied by `rfl` and `HEq.rfl` at the instance, and
substituted inside; the value of `…chartSchemeTheta` is its defining equation, matched against the
pattern of the gluing lemma, so that no two spellings of a whole composite are compared.  The
composites are taken in the category of sheaves of modules over `W.ringCatSheaf`, the ambient
category of the quasi-coherent modules.  The represented statement is the quasi-coherent one
through `AlgebraicGeometry.Space.representedUnitChartHom_comp_map_hom_of_comp_eq`.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.ProjChartGradedTriple (laurentOn)
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u m

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective



namespace AlgebraicGeometry.Space

section UnitGlue

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {W F : BigFppfOver B S hS}
  (c : W ⟶ F)

/-- **The unital triangle of a chart map's scheme factor, as morphisms of quasi-coherent
modules, from its scheme-level form in a second spelling of the twists.**  For a morphism
`c : W ⟶ F` of the site and `t : F ⟶ P`, the composite of Stacks 03LU (`𝒪_W ≅ c^*𝒪_F`), the
pullback along `c` of a unit `U : 𝒪_F ⟶ t^*M` and a map `z = (c^*t^*M ≅ (c ≫ t)^*M = ρ^*M ⟶ K)` is
`ν`, as soon as the underlying scheme-level equation `H` holds for heterogeneously equal leaves
`P₂, t₂, G₂, ρ₂, Θ₂, ν₂` (the spelling in which `θ` is multiplicative and unital over
`Proj_W((f ∘ w)^*𝒜)`); at free variables, each leaf substituted inside. -/
theorem quasicoherentPullbackUnit_comp_eq_of_heq {P₁ P₂ : Scheme.{u}} (eP : P₁ = P₂)
    {t₁ : (BigFppfOver.toScheme B S hS).obj F ⟶ P₁} {t₂ : (BigFppfOver.toScheme B S hS).obj F ⟶ P₂}
    (et : HEq t₁ t₂) {M₁ : P₁.Modules}
    {G₂ : Stacks.AlgebraicGeometry.RelativeProjTwists.SchemeGradedAlgebra P₂}
    (eM : HEq M₁ (G₂.piece 0))
    (hq : SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj F).ringCatSheaf
      ((Scheme.Modules.pullback t₁).obj M₁))
    {ρ₁ : (BigFppfOver.toScheme B S hS).obj W ⟶ P₁} {ρ₂ : (BigFppfOver.toScheme B S hS).obj W ⟶ P₂}
    (eρ : HEq ρ₁ ρ₂) (h₁ : (BigFppfOver.toScheme B S hS).map c ≫ t₁ = ρ₁)
    (h₂ : (BigFppfOver.toScheme B S hS).map c ≫ t₂ = ρ₂)
    {K : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj W).ringCatSheaf).FullSubcategory}
    {Z₂ : ((BigFppfOver.toScheme B S hS).obj W).Modules} (eZ : K.obj = Z₂)
    {Θ₁ : (Scheme.Modules.pullback ρ₁).obj M₁ ⟶ K.obj}
    {Θ₂ : (Scheme.Modules.pullback ρ₂).obj (G₂.piece 0) ⟶ Z₂} (eΘ : HEq Θ₁ Θ₂)
    {u₁ : SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj F).ringCatSheaf ⟶
      (Scheme.Modules.pullback t₁).obj M₁}
    (eu : HEq u₁ (SheafOfModules.GradedAlgebra.oneHom
      (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pbAlgS t₂ G₂)))
    {U : quasicoherentUnitObj B S hS F ⟶ ⟨(Scheme.Modules.pullback t₁).obj M₁, hq⟩}
    (hU : U = ObjectProperty.homMk u₁)
    {z : quasicoherentPullbackObj B S hS c ⟨(Scheme.Modules.pullback t₁).obj M₁, hq⟩ ⟶ K}
    (hz : z = ObjectProperty.homMk
      ((Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map c) t₁).hom.app M₁ ≫
        (Scheme.Modules.pullbackCongr h₁).hom.app M₁ ≫ Θ₁))
    {ν : quasicoherentUnitObj B S hS W ⟶ K} {ν' : SheafOfModules.unit
      ((BigFppfOver.toScheme B S hS).obj W).ringCatSheaf ⟶ K.obj}
    (hν : ν = ObjectProperty.homMk ν')
    {ν₂ : SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj W).ringCatSheaf ⟶ Z₂}
    (eν : HEq ν' ν₂)
    (H : @CategoryStruct.comp (SheafOfModules
          ((BigFppfOver.toScheme B S hS).obj W).ringCatSheaf) _ _ _ _
        (Scheme.Modules.pullbackUnitIso ((BigFppfOver.toScheme B S hS).map c)).inv
        (@CategoryStruct.comp (SheafOfModules
            ((BigFppfOver.toScheme B S hS).obj W).ringCatSheaf) _ _ _ _
          ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map c)).map
            (SheafOfModules.GradedAlgebra.oneHom
              (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pbAlgS t₂ G₂)))
          (@CategoryStruct.comp (SheafOfModules
              ((BigFppfOver.toScheme B S hS).obj W).ringCatSheaf) _ _ _ _
            ((Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map c) t₂).hom.app
              (G₂.piece 0))
            (@CategoryStruct.comp (SheafOfModules
                ((BigFppfOver.toScheme B S hS).obj W).ringCatSheaf) _ _ _ _
              ((Scheme.Modules.pullbackCongr h₂).hom.app (G₂.piece 0)) Θ₂))) = ν₂) :
    ((quasicoherentPullbackUnitIso B S hS c).inv ≫ quasicoherentPullbackMap B S hS c U) ≫ z =
      ν := by
  subst eP eZ
  obtain rfl := eq_of_heq eν
  obtain rfl := eq_of_heq et
  obtain rfl := eq_of_heq eM
  obtain rfl := eq_of_heq eρ
  obtain rfl := eq_of_heq eΘ
  obtain rfl := eq_of_heq eu
  subst hU hz hν
  exact comp_comp_eq_of_hom_eq _ _ _ _ H (ObjectProperty.homMk_hom _)
    ((ObjectProperty.homMk_hom _).trans
      (congrArg (Scheme.Modules.pullback _).map (ObjectProperty.homMk_hom _)))
    (ObjectProperty.homMk_hom _) (ObjectProperty.homMk_hom _)

end UnitGlue

end AlgebraicGeometry.Space


namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism


section Chart

variable (s : RelativeProjSituation.{u, m})
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} (f : X ⟶ s.shrink.space)
  (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O))
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  (ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L))
  {W : BigFppfOver s.site s.base s.containsBase} (x : yoneda.obj W ⟶ X.1)
  (hx : (ofUnitalHom s f L ψ).locusOpen W x = ⊤)

/-- **`θ` at a scheme point `w` of `U(ψ)` is unital, as morphisms of quasi-coherent modules on
`W`** (Stacks 0D2Z): the identification `𝒪_W ≅ c_w^*𝒪` of Stacks 03LU, followed by the pullback
along the section `c_w : W ⟶ W ×_Y Proj_Y(𝒜)` of the unit of the twists of Stacks 01NR and by
`…InvertibleTwistingRestriction.chartSchemeTheta` in degree `0`, is the unit of the Laurent
algebra `⨁_d (w^*ℒ)^{⊗ d}`.  This is
`…InvertibleTwistingRestriction.pullbackUnitIso_inv_comp_map_oneHom_comp_chartTheta` read through
`AlgebraicGeometry.Space.quasicoherentPullbackUnit_comp_eq_of_heq`, the values of the unit of the
twists, of `…chartSchemeTheta` and of the unit of the Laurent algebra supplied by their defining
equations. -/
theorem quasicoherentPullbackUnit_comp_chartSchemeTheta :
    ((quasicoherentPullbackUnitIso s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection x hx)).inv ≫
      quasicoherentPullbackMap s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection x hx) (s.twistPieceUnit W (x ≫ f.hom))) ≫
      chartSchemeTheta s f L ψ x hx 0 =
    pointLaurentPieceUnit L W x := by
  refine quasicoherentPullbackUnit_comp_eq_of_heq (B := s.site) (S := s.base)
    (hS := s.containsBase) _ ?eP ?et ?eM _ ?eρ _ _ ?eZ ?eΘ ?eu
    (RelativeProjSituation.twistPieceUnit.eq_1 s W (x ≫ f.hom))
    (chartSchemeTheta.eq_1 s f L ψ x hx 0) (pointLaurentPieceUnit.eq_1 L W x) ?eν
    (pullbackUnitIso_inv_comp_map_oneHom_comp_chartTheta (ofUnitalHom s f L ψ) x hx
      ((ofUnitalHom s f L ψ).chartSection x hx)
      (toScheme_map_chartSection_toRelativeProj s f L ψ x hx))
  case eP => exact rfl
  case eZ => exact rfl
  all_goals exact HEq.rfl

end Chart


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

/-- **The middle factor of the chart map of `θ` is unital** (Stacks 0D2Z): at a scheme point
`w : W ⟶ U(ψ)`, the module attached (Stacks 03DX (2)) to `θ` on `W` in degree `0`
(`…InvertibleTwistingRestriction.chartSchemeTheta`, the middle factor `m_w` of
`…InvertibleTwistingRestriction.chartMap`) carries the morphism attached to the pullback along the
section `c_w` of the unit of the twists of Stacks 01NR (the unit to which the source factor
carries the unit of the source of `θ`, `…chartSourceIso_hom_one`) to the morphism attached to the
unit of the Laurent algebra of `w^*ℒ` (the unit which the target factor carries to the unit of
the target of `θ`, `AlgebraicGeometry.Space.pointTargetIso_symm_trans_hom_one`).  This is the
hypothesis `hm` of `AlgebraicGeometry.Space.one_of_factor_squares` for the chart maps. -/
theorem representedUnitChartHom_comp_chartSchemeTheta :
    representedUnitChartHom s.shrink.site s.shrink.base s.shrink.containsBase
        ((quasicoherentPullbackUnitIso s.site s.base s.containsBase
            ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))).inv ≫
          quasicoherentPullbackMap s.site s.base s.containsBase
            ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
            (s.twistPieceUnit W (locusPoint w ≫ f.hom))) ≫
      ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
          s.shrink.containsBase W).functor.map
        (chartSchemeTheta s f L ψ (locusPoint w) (locusOpen_locusPoint w) 0)).hom =
    representedUnitChartHom s.shrink.site s.shrink.base s.shrink.containsBase
      (pointLaurentPieceUnit L W (locusPoint w)) :=
  representedUnitChartHom_comp_map_hom_of_comp_eq _ _ _
    (quasicoherentPullbackUnit_comp_chartSchemeTheta s f L ψ (locusPoint w)
      (locusOpen_locusPoint w))

end Represented

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
