module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartMapNatural

/-!
# The site of `s.shrink` and the site of `s` in one spelling, for the chart maps of Stacks 0D2Z

The situation `s.shrink` (`AlgebraicGeometry.Space.RelativeProjSituation.shrink`) has the same
site, base and algebraic space as `s`: `s.shrink.site` is `s.site` by definition
(`…RelativeProjSituation.shrink_site`, `rfl`), but not syntactically.  The chart maps of `θ` of
[Stacks, Tag 0D2Z] (`…InvertibleTwistingRestriction.chartMap`) and their compatibility live over
`s.shrink.site`, while their source identification
(`…InvertibleTwistingRestriction.chartSourceIso`) and everything on the schemes of the site live
over `s.site`.

A statement mixing the two spellings is expensive for the kernel: it has no reducibility
setting, and it compares a projection (`Prefunctor.obj`, `CategoryStruct.comp`, `Iso.hom`, ...)
of two differently spelled structures by reducing both structures, rather than by comparing their
arguments.  The cure is to compare the two spellings only at their leaves -- objects and
morphisms of the site, algebraic spaces, morphisms of algebraic spaces, modules -- each of which is
the same term in both readings: a statement at variables over two sites `B₁ = B₂`, with the
leaves heterogeneously equal, proved by `subst`.

## Main results

* `…InvertibleTwistingRestriction.chartSourceShapedIso_heq`: **the bridge**: the source
  identification `(a^*b^* ≅ a'^*b'^*) ≪≫ a'^*E ≪≫ (a'^*(N^a) ≅ (c^*N)^a)` (the shape of
  `…InvertibleTwistingRestriction.chartSourceIso`) over a site `B₁` is heterogeneously equal to the
  same identification over `B₂ = B₁`, for heterogeneously equal leaves.
* `…InvertibleTwistingRestriction.chartSourceIso_eq_shrink`: **`chartSourceIso` in the spelling
  of `s.shrink.site`**: its value with every functor and comparison taken over `s.shrink.site`,
  the spelling of the chart maps (the hypothesis `hJ` of
  `AlgebraicGeometry.Space.chartSourceShaped_square` at `B = s.shrink.site`).
* `…InvertibleTwistingRestriction.chartSource_square_of_point_shrink`: the square of the source
  factor at variables (`AlgebraicGeometry.Space.chartSourceShaped_square`) instantiated at
  `B = s.shrink.site` and `J = …chartSourceIso`, with `hJ = …chartSourceIso_eq_shrink`.

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

/-- **The source identification of the chart maps, read over a second spelling of the site.**
For morphisms of algebraic spaces `a ≫ b = a' ≫ b'` with `a' = (c : T ⟶ F)` represented, a module
`M` and an identification `E : b'^*M ≅ N^a`, the identification
`(a^*b^*M ≅ a'^*b'^*M) ≪≫ a'^*E ≪≫ (a'^*(N^a) ≅ (c^*N)^a)` over the site `B₁` is heterogeneously
equal to the same identification over a site `B₂ = B₁`, for heterogeneously equal leaves. -/
theorem chartSourceShapedIso_heq {B₁ B₂ : BigFppfSite.{u}} (hB : B₁ = B₂) {S₁ S₂ : Scheme.{u}}
    (hSS : S₁ = S₂) {hS₁ : B₁.Contains S₁} {hS₂ : B₂.Contains S₂}
    {T₁ F₁ : BigFppfOver B₁ S₁ hS₁} {Y₁ P₁ : AlgebraicSpaces B₁ S₁ hS₁}
    {a₁ : (⟨yoneda.obj T₁, isAlgebraicSpace_yoneda B₁ S₁ hS₁ T₁⟩ : AlgebraicSpaces B₁ S₁ hS₁) ⟶ Y₁}
    {b₁ : Y₁ ⟶ P₁} {c₁ : T₁ ⟶ F₁}
    {b₁' : (⟨yoneda.obj F₁, isAlgebraicSpace_yoneda B₁ S₁ hS₁ F₁⟩ : AlgebraicSpaces B₁ S₁ hS₁) ⟶ P₁}
    {h₁ : a₁ ≫ b₁ = representedSpaceMap B₁ S₁ hS₁ c₁ ≫ b₁'}
    {M₁ : Modules.{u, u} B₁ S₁ hS₁ P₁.1 P₁.2}
    {N₁ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B₁ S₁ hS₁).obj F₁).ringCatSheaf).FullSubcategory}
    {E₁ : (modulePullback B₁ S₁ hS₁ b₁').obj M₁ ≅
      ((representedQuasicoherentSchemeEquivalence B₁ S₁ hS₁ F₁).functor.obj N₁).obj}
    {T₂ F₂ : BigFppfOver B₂ S₂ hS₂} {Y₂ P₂ : AlgebraicSpaces B₂ S₂ hS₂}
    (a₂ : (⟨yoneda.obj T₂, isAlgebraicSpace_yoneda B₂ S₂ hS₂ T₂⟩ : AlgebraicSpaces B₂ S₂ hS₂) ⟶ Y₂)
    (b₂ : Y₂ ⟶ P₂) (c₂ : T₂ ⟶ F₂)
    (b₂' : (⟨yoneda.obj F₂, isAlgebraicSpace_yoneda B₂ S₂ hS₂ F₂⟩ : AlgebraicSpaces B₂ S₂ hS₂) ⟶ P₂)
    (h₂ : a₂ ≫ b₂ = representedSpaceMap B₂ S₂ hS₂ c₂ ≫ b₂')
    (M₂ : Modules.{u, u} B₂ S₂ hS₂ P₂.1 P₂.2)
    (N₂ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B₂ S₂ hS₂).obj F₂).ringCatSheaf).FullSubcategory)
    (E₂ : (modulePullback B₂ S₂ hS₂ b₂').obj M₂ ≅
      ((representedQuasicoherentSchemeEquivalence B₂ S₂ hS₂ F₂).functor.obj N₂).obj)
    (hT : HEq T₁ T₂) (hF : HEq F₁ F₂) (hY : HEq Y₁ Y₂) (hP : HEq P₁ P₂) (ha : HEq a₁ a₂)
    (hb : HEq b₁ b₂) (hc : HEq c₁ c₂) (hb' : HEq b₁' b₂') (hM : HEq M₁ M₂) (hN : HEq N₁ N₂)
    (hE : HEq E₁ E₂) :
    HEq (modulePullbackCompTransportIso a₁ b₁ (representedSpaceMap B₁ S₁ hS₁ c₁) b₁' h₁ M₁ ≪≫
        (modulePullback B₁ S₁ hS₁ (representedSpaceMap B₁ S₁ hS₁ c₁)).mapIso E₁ ≪≫
        modulePullbackRepresentedQuasicoherentIso B₁ S₁ hS₁ c₁ N₁)
      (modulePullbackCompTransportIso a₂ b₂ (representedSpaceMap B₂ S₂ hS₂ c₂) b₂' h₂ M₂ ≪≫
        (modulePullback B₂ S₂ hS₂ (representedSpaceMap B₂ S₂ hS₂ c₂)).mapIso E₂ ≪≫
        modulePullbackRepresentedQuasicoherentIso B₂ S₂ hS₂ c₂ N₂) := by
  subst hB hSS
  obtain rfl : hS₁ = hS₂ := rfl
  subst hT hF hY hP
  subst ha hb hc hb' hM hN
  subst hE
  rfl

end Bridge

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
  {T : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase}
  (w : yoneda.obj T ⟶ (locusSpaceOfUnitalHom s f L ψ).obj)

/-- **The source identification `w^*(r^*𝒪(d)) ≅ (c_w^*𝒪(d))^a` in the spelling of
`s.shrink.site`**: `…InvertibleTwistingRestriction.chartSourceIso` is the comparison of
Stacks 03LU for the two factorisations of `r ∘ w`, the inverse image along `c_w` of the base
change identification of Stacks 084D and Stacks 03DX (2), each functor and comparison taken over
`s.shrink.site` -- the spelling of the chart maps `…InvertibleTwistingRestriction.chartMap` and of
the hypothesis `hJ` of `AlgebraicGeometry.Space.chartSourceShaped_square` at
`B = s.shrink.site`.  Proved through `…InvertibleTwistingRestriction.chartSourceShapedIso_heq`,
which compares the two spellings at the leaves only. -/
theorem chartSourceIso_eq_shrink (d : ℤ) :
    @Eq ((modulePullback s.shrink.site s.shrink.base s.shrink.containsBase
          (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w :
            (⟨yoneda.obj T, isAlgebraicSpace_yoneda s.shrink.site s.shrink.base
              s.shrink.containsBase T⟩ :
                AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase) ⟶ _)).obj
          ((modulePullback s.shrink.site s.shrink.base s.shrink.containsBase
            ((ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property)).obj
            (s.twistModule Px d).obj) ≅
        ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
            s.shrink.containsBase T).functor.obj
          (quasicoherentPullbackObj s.shrink.site s.shrink.base s.shrink.containsBase
            ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
            (s.twistPieceQcoh T (locusPoint w ≫ f.hom) d))).obj)
      (chartSourceIso Px w (locusOpen_locusPoint w) d)
      (modulePullbackCompTransportIso (B := s.shrink.site) (S := s.shrink.base)
          (hS := s.shrink.containsBase)
          (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w :
            (⟨yoneda.obj T, isAlgebraicSpace_yoneda s.shrink.site s.shrink.base
              s.shrink.containsBase T⟩ :
                AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase) ⟶ _)
          ((ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property)
          (representedSpaceMap s.shrink.site s.shrink.base s.shrink.containsBase
            ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w)))
          (s.fibreToSpaceHom T (locusPoint w ≫ f.hom))
          (pointHom_comp_invertibleSpaceMorphism w) (s.twistModule Px d).obj ≪≫
        (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase
          (representedSpaceMap s.shrink.site s.shrink.base s.shrink.containsBase
            ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w)))).mapIso
          (s.fibreToSpaceTwistModuleIso Px T (locusPoint w ≫ f.hom) d) ≪≫
        modulePullbackRepresentedQuasicoherentIso s.shrink.site s.shrink.base s.shrink.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
          (s.twistPieceQcoh T (locusPoint w ≫ f.hom) d)) :=
  eq_of_heq (chartSourceShapedIso_heq s.shrink_site.symm s.shrink_base.symm
    (a₁ := pointHom (X := (ofUnitalHom s f L ψ).locusSpace X.property) w)
    (b₁ := (ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property)
    (c₁ := (ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
    (b₁' := s.fibreToSpaceHom T (locusPoint w ≫ f.hom))
    (h₁ := pointHom_comp_invertibleSpaceMorphism w) (M₁ := (s.twistModule Px d).obj)
    (N₁ := s.twistPieceQcoh T (locusPoint w ≫ f.hom) d)
    (E₁ := s.fibreToSpaceTwistModuleIso Px T (locusPoint w ≫ f.hom) d)
    (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w)
    ((ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property)
    ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
    (s.fibreToSpaceHom T (locusPoint w ≫ f.hom)) (pointHom_comp_invertibleSpaceMorphism w)
    (s.twistModule Px d).obj (s.twistPieceQcoh T (locusPoint w ≫ f.hom) d)
    (s.fibreToSpaceTwistModuleIso Px T (locusPoint w ≫ f.hom) d)
    HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl)

/-- **`AlgebraicGeometry.Space.chartSourceShaped_square` at the source identification
`…InvertibleTwistingRestriction.chartSourceIso` at `w`, over `s.shrink.site`**: the instance at
`B = s.shrink.site`, the site of the chart maps, with the value of `…chartSourceIso` supplied by
`…InvertibleTwistingRestriction.chartSourceIso_eq_shrink`.  The `s.site` reading is
`…InvertibleTwistingRestriction.chartSource_square_of_point`. -/
theorem chartSource_square_of_point_shrink (d : ℤ) :
    type_of% (@AlgebraicGeometry.Space.chartSourceShaped_square s.shrink.site s.shrink.base
      s.shrink.containsBase
      _ _ _ _ _ _ _ _ _ (chartSourceIso Px w (locusOpen_locusPoint w) d) _
      (pointHom_comp_invertibleSpaceMorphism w) _ (chartSourceIso_eq_shrink Px w d)) :=
  @AlgebraicGeometry.Space.chartSourceShaped_square s.shrink.site s.shrink.base
      s.shrink.containsBase
      _ _ _ _ _ _ _ _ _ (chartSourceIso Px w (locusOpen_locusPoint w) d) _
      (pointHom_comp_invertibleSpaceMorphism w) _ (chartSourceIso_eq_shrink Px w d)

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
