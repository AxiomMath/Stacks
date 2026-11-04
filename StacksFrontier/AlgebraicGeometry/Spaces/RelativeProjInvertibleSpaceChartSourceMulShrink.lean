module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartSourceMul
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceShrinkSiteBridge

/-!
# The source factor of the chart maps of `θ` of Stacks 0D2Z is multiplicative, over `s.shrink.site`

The chart maps `χ_w = σ_w ≫ m_w ≫ τ_w` of `θ` of [Stacks, Tag 0D2Z]
(`…InvertibleTwistingRestriction.chartMap`) are morphisms of modules over the site `s.shrink.site`,
and so is the descent of their multiplicativity
(`AlgebraicGeometry.Space.mul_comp_pointFamilyDescendedHom` at `B = s.shrink.site`, through
`AlgebraicGeometry.Space.mul_of_factor_squares`).  The source
identification `σ_w` (`…InvertibleTwistingRestriction.chartSourceIso`), the multiplication of the
source of `θ` (`…InvertibleTwistingRestriction.thetaSourceMul`), and the square
`…InvertibleTwistingRestriction.chartSourceIso_hom_mul` they satisfy are stated over `s.site`.
The two sites are equal by definition (`…RelativeProjSituation.shrink_site`), but a comparison of
the two spellings of a whole composite is very expensive for the kernel (see
`StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceShrinkSiteBridge`).  This file
reads the square in the spelling of the chart maps, comparing the two spellings at the leaves only.

## Main results

* `…InvertibleTwistingRestriction.modulePullbackTensorIso_inv_comp_map_comp_eq_of_site_heq`: **the
  bridge**: a square `(h^*T_i ⊗ h^*T_j ≅ h^*(T_i ⊗ T_j) ⟶ h^*T_k) ≫ e_k = (e_i ⊗ e_j) ≫ μ_G` over
  a site `B₁` gives the same square over a site `B₂ = B₁`, for heterogeneously equal leaves;
  proved by `subst`.
* `…InvertibleTwistingRestriction.chartSourceIso_hom_mul_shrink`: **the source identification of
  the chart maps is multiplicative, over `s.shrink.site`**: the hypothesis `hσ` of
  `AlgebraicGeometry.Space.mul_of_factor_squares` for the source factor of a chart map, in the
  spelling of the chart maps.

## Implementation notes

The statement of `…chartSourceIso_hom_mul_shrink` is the type of its proof, the instance of the
bridge at `B₁ = s.site`, `B₂ = s.shrink.site` and `…chartSourceIso_hom_mul`; its leaves over
`s.shrink.site` are given with their types over `s.shrink.site` (the scheme point `w` as a morphism
from `⟨yoneda.obj T, _⟩`, `θ`'s multiplication as a morphism out of the tensor product over
`s.shrink.site`, and `σ_w` between modules over `s.shrink.site`), so that every functor,
composition and tensor product of the statement is taken over `s.shrink.site`.
`CategoryTheory.yoneda` is locally irreducible, as in
`StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartSourceMul` (without it the
instance exceeds its budget).

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
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

section Bridge

/-- **A multiplication square through Stacks 03EL, read over a second spelling of the site**:
`(h^*T_i ⊗ h^*T_j ≅ h^*(T_i ⊗ T_j) ⟶ h^*T_k) ≫ e_k = (e_i ⊗ e_j) ≫ μ_G` over a site `B₁` gives the
same square over a site `B₂ = B₁`, for heterogeneously equal leaves.  The square has the shape of
the hypothesis `hσ` of `AlgebraicGeometry.Space.mul_of_factor_squares`. -/
theorem modulePullbackTensorIso_inv_comp_map_comp_eq_of_site_heq {B₁ B₂ : BigFppfSite.{u}}
    (hB : B₁ = B₂) {S₁ S₂ : Scheme.{u}} (hSS : S₁ = S₂) {hS₁ : B₁.Contains S₁}
    {hS₂ : B₂.Contains S₂}
    {Z₁ X₁ : AlgebraicSpaces B₁ S₁ hS₁} {h₁ : Z₁ ⟶ X₁}
    {Ti₁ Tj₁ Tk₁ : Modules.{u, u} B₁ S₁ hS₁ X₁.1 X₁.2} {μ₁ : Ti₁ ⊗ Tj₁ ⟶ Tk₁}
    {Gi₁ Gj₁ Gk₁ : Modules.{u, u} B₁ S₁ hS₁ Z₁.1 Z₁.2}
    {ei₁ : (modulePullback B₁ S₁ hS₁ h₁).obj Ti₁ ⟶ Gi₁}
    {ej₁ : (modulePullback B₁ S₁ hS₁ h₁).obj Tj₁ ⟶ Gj₁}
    {ek₁ : (modulePullback B₁ S₁ hS₁ h₁).obj Tk₁ ⟶ Gk₁} {μG₁ : Gi₁ ⊗ Gj₁ ⟶ Gk₁}
    (H : ((modulePullbackTensorIso B₁ S₁ hS₁ h₁ Ti₁ Tj₁).inv ≫
        (modulePullback B₁ S₁ hS₁ h₁).map μ₁) ≫ ek₁ = (ei₁ ⊗ₘ ej₁) ≫ μG₁)
    {Z₂ X₂ : AlgebraicSpaces B₂ S₂ hS₂} (h₂ : Z₂ ⟶ X₂)
    (Ti₂ Tj₂ Tk₂ : Modules.{u, u} B₂ S₂ hS₂ X₂.1 X₂.2) (μ₂ : Ti₂ ⊗ Tj₂ ⟶ Tk₂)
    (Gi₂ Gj₂ Gk₂ : Modules.{u, u} B₂ S₂ hS₂ Z₂.1 Z₂.2)
    (ei₂ : (modulePullback B₂ S₂ hS₂ h₂).obj Ti₂ ⟶ Gi₂)
    (ej₂ : (modulePullback B₂ S₂ hS₂ h₂).obj Tj₂ ⟶ Gj₂)
    (ek₂ : (modulePullback B₂ S₂ hS₂ h₂).obj Tk₂ ⟶ Gk₂) (μG₂ : Gi₂ ⊗ Gj₂ ⟶ Gk₂)
    (hZ : HEq Z₁ Z₂) (hX : HEq X₁ X₂) (hh : HEq h₁ h₂) (hTi : HEq Ti₁ Ti₂) (hTj : HEq Tj₁ Tj₂)
    (hTk : HEq Tk₁ Tk₂) (hμ : HEq μ₁ μ₂) (hGi : HEq Gi₁ Gi₂) (hGj : HEq Gj₁ Gj₂)
    (hGk : HEq Gk₁ Gk₂) (hei : HEq ei₁ ei₂) (hej : HEq ej₁ ej₂) (hek : HEq ek₁ ek₂)
    (hμG : HEq μG₁ μG₂) :
    ((modulePullbackTensorIso B₂ S₂ hS₂ h₂ Ti₂ Tj₂).inv ≫
        (modulePullback B₂ S₂ hS₂ h₂).map μ₂) ≫ ek₂ = (ei₂ ⊗ₘ ej₂) ≫ μG₂ := by
  subst hB hSS
  obtain rfl : hS₁ = hS₂ := rfl
  subst hZ hX
  subst hh hTi hTj hTk hGi hGj hGk
  subst hμ hei hej hek hμG
  exact H

end Bridge

section ChartSource

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

/-- **The identification of the source of the chart map is multiplicative, over
`s.shrink.site`** (Stacks 084D and 0D2Z): at a scheme point `w : W ⟶ U(ψ)`, the identification
`σ_d : w^*(r^*𝒪(d)) ≅ (c_w^*𝒪(d))^a` (`…InvertibleTwistingRestriction.chartSourceIso`) carries
the inverse image along `w` of the multiplication of the source of `θ`
(`…InvertibleTwistingRestriction.thetaSourceMul`), read through Stacks 03EL, to the morphism
attached (Stacks 03DX (2)) to the pullback along the section `c_w : W ⟶ W ×_Y Proj_Y(𝒜)` of the
multiplication of the twists of Stacks 01NR on `W ×_Y Proj_Y(𝒜)`:
`((w^*G_i ⊗ w^*G_j ≅ w^*(G_i ⊗ G_j)) ≫ w^*μ_G) ≫ σ_{i+j} = (σ_i ⊗ σ_j) ≫ μ_M`, with `G_d` the
source `…InvertibleTwistingRestriction.thetaSourceOfUnitalHom` of `θ` and `μ_M` the morphism
`AlgebraicGeometry.Space.representedTensorChartMul` of
`c_w^*𝒪(i) ⊗ c_w^*𝒪(j) ≅ c_w^*(𝒪(i) ⊗ 𝒪(j)) ⟶ c_w^*𝒪(i + j)`.

This is the hypothesis `hσ` of `AlgebraicGeometry.Space.mul_of_factor_squares` for the source
factor of a chart map `…InvertibleTwistingRestriction.chartMap`, with every functor, comparison,
composition and tensor product taken over `s.shrink.site`, the site of the chart maps;
`…InvertibleTwistingRestriction.chartSourceIso_hom_mul` is the reading over `s.site`, and this is
its instance of
`…InvertibleTwistingRestriction.modulePullbackTensorIso_inv_comp_map_comp_eq_of_site_heq`. -/
theorem chartSourceIso_hom_mul_shrink (i j : ℤ) :
    type_of% (modulePullbackTensorIso_inv_comp_map_comp_eq_of_site_heq s.shrink_site.symm
        s.shrink_base.symm
        (h₁ := pointHom (X := (ofUnitalHom s f L ψ).locusSpace X.property) w)
        (Ti₁ := ((ofUnitalHom s f L ψ).thetaSource X.property Px i).obj)
        (Tj₁ := ((ofUnitalHom s f L ψ).thetaSource X.property Px j).obj)
        (Tk₁ := ((ofUnitalHom s f L ψ).thetaSource X.property Px (i + j)).obj)
        (μ₁ := thetaSourceMul (ofUnitalHom s f L ψ) X.property Px i j)
        (ei₁ := (chartSourceIso Px w (locusOpen_locusPoint w) i).hom)
        (ej₁ := (chartSourceIso Px w (locusOpen_locusPoint w) j).hom)
        (ek₁ := (chartSourceIso Px w (locusOpen_locusPoint w) (i + j)).hom)
        (μG₁ := (representedTensorChartMul s.site s.base s.containsBase
          ((quasicoherentPullbackTensorIso s.site s.base s.containsBase
              ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
              (s.twistPieceQcoh T (locusPoint w ≫ f.hom) i)
              (s.twistPieceQcoh T (locusPoint w ≫ f.hom) j)).inv ≫
            quasicoherentPullbackMap s.site s.base s.containsBase
              ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
              (s.twistPieceMul T (locusPoint w ≫ f.hom) i j))))
        (chartSourceIso_hom_mul Px w i j)
        (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w :
          (⟨yoneda.obj T, isAlgebraicSpace_yoneda s.shrink.site s.shrink.base
            s.shrink.containsBase T⟩ :
            AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase) ⟶ _)
        (thetaSourceOfUnitalHom s f L ψ Px i).obj (thetaSourceOfUnitalHom s f L ψ Px j).obj
        (thetaSourceOfUnitalHom s f L ψ Px (i + j)).obj
        (thetaSourceMul (ofUnitalHom s f L ψ) X.property Px i j :
          (thetaSourceOfUnitalHom s f L ψ Px i).obj ⊗ (thetaSourceOfUnitalHom s f L ψ Px j).obj ⟶
            (thetaSourceOfUnitalHom s f L ψ Px (i + j)).obj)
        ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
            s.shrink.containsBase T).functor.obj
          (quasicoherentPullbackObj s.shrink.site s.shrink.base s.shrink.containsBase
            ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
            (s.twistPieceQcoh T (locusPoint w ≫ f.hom) i))).obj
        ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
            s.shrink.containsBase T).functor.obj
          (quasicoherentPullbackObj s.shrink.site s.shrink.base s.shrink.containsBase
            ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
            (s.twistPieceQcoh T (locusPoint w ≫ f.hom) j))).obj
        ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
            s.shrink.containsBase T).functor.obj
          (quasicoherentPullbackObj s.shrink.site s.shrink.base s.shrink.containsBase
            ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
            (s.twistPieceQcoh T (locusPoint w ≫ f.hom) (i + j)))).obj
        ((chartSourceIso Px w (locusOpen_locusPoint w) i).hom :
        (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase
            (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w :
              (⟨yoneda.obj T, isAlgebraicSpace_yoneda s.shrink.site s.shrink.base
                s.shrink.containsBase T⟩ :
                  AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase) ⟶ _)).obj
            (thetaSourceOfUnitalHom s f L ψ Px i).obj ⟶
          ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
              s.shrink.containsBase T).functor.obj
            (quasicoherentPullbackObj s.shrink.site s.shrink.base s.shrink.containsBase
              ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
              (s.twistPieceQcoh T (locusPoint w ≫ f.hom) i))).obj)
        ((chartSourceIso Px w (locusOpen_locusPoint w) j).hom :
        (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase
            (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w :
              (⟨yoneda.obj T, isAlgebraicSpace_yoneda s.shrink.site s.shrink.base
                s.shrink.containsBase T⟩ :
                  AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase) ⟶ _)).obj
            (thetaSourceOfUnitalHom s f L ψ Px j).obj ⟶
          ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
              s.shrink.containsBase T).functor.obj
            (quasicoherentPullbackObj s.shrink.site s.shrink.base s.shrink.containsBase
              ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
              (s.twistPieceQcoh T (locusPoint w ≫ f.hom) j))).obj)
        ((chartSourceIso Px w (locusOpen_locusPoint w) (i + j)).hom :
        (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase
            (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w :
              (⟨yoneda.obj T, isAlgebraicSpace_yoneda s.shrink.site s.shrink.base
                s.shrink.containsBase T⟩ :
                  AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase) ⟶ _)).obj
            (thetaSourceOfUnitalHom s f L ψ Px (i + j)).obj ⟶
          ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
              s.shrink.containsBase T).functor.obj
            (quasicoherentPullbackObj s.shrink.site s.shrink.base s.shrink.containsBase
              ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
              (s.twistPieceQcoh T (locusPoint w ≫ f.hom) (i + j)))).obj)
        (representedTensorChartMul s.shrink.site s.shrink.base s.shrink.containsBase
          ((quasicoherentPullbackTensorIso s.shrink.site s.shrink.base s.shrink.containsBase
              ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
              (s.twistPieceQcoh T (locusPoint w ≫ f.hom) i)
              (s.twistPieceQcoh T (locusPoint w ≫ f.hom) j)).inv ≫
            quasicoherentPullbackMap s.shrink.site s.shrink.base s.shrink.containsBase
              ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
              (s.twistPieceMul T (locusPoint w ≫ f.hom) i j)))
        HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
        HEq.rfl HEq.rfl HEq.rfl) :=
  modulePullbackTensorIso_inv_comp_map_comp_eq_of_site_heq s.shrink_site.symm
    s.shrink_base.symm
    (h₁ := pointHom (X := (ofUnitalHom s f L ψ).locusSpace X.property) w)
    (Ti₁ := ((ofUnitalHom s f L ψ).thetaSource X.property Px i).obj)
    (Tj₁ := ((ofUnitalHom s f L ψ).thetaSource X.property Px j).obj)
    (Tk₁ := ((ofUnitalHom s f L ψ).thetaSource X.property Px (i + j)).obj)
    (μ₁ := thetaSourceMul (ofUnitalHom s f L ψ) X.property Px i j)
    (ei₁ := (chartSourceIso Px w (locusOpen_locusPoint w) i).hom)
    (ej₁ := (chartSourceIso Px w (locusOpen_locusPoint w) j).hom)
    (ek₁ := (chartSourceIso Px w (locusOpen_locusPoint w) (i + j)).hom)
    (μG₁ := (representedTensorChartMul s.site s.base s.containsBase
      ((quasicoherentPullbackTensorIso s.site s.base s.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
          (s.twistPieceQcoh T (locusPoint w ≫ f.hom) i)
          (s.twistPieceQcoh T (locusPoint w ≫ f.hom) j)).inv ≫
        quasicoherentPullbackMap s.site s.base s.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
          (s.twistPieceMul T (locusPoint w ≫ f.hom) i j))))
    (chartSourceIso_hom_mul Px w i j)
    (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w :
      (⟨yoneda.obj T, isAlgebraicSpace_yoneda s.shrink.site s.shrink.base
        s.shrink.containsBase T⟩ :
        AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase) ⟶ _)
    (thetaSourceOfUnitalHom s f L ψ Px i).obj (thetaSourceOfUnitalHom s f L ψ Px j).obj
    (thetaSourceOfUnitalHom s f L ψ Px (i + j)).obj
    (thetaSourceMul (ofUnitalHom s f L ψ) X.property Px i j :
      (thetaSourceOfUnitalHom s f L ψ Px i).obj ⊗ (thetaSourceOfUnitalHom s f L ψ Px j).obj ⟶
        (thetaSourceOfUnitalHom s f L ψ Px (i + j)).obj)
    ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
        s.shrink.containsBase T).functor.obj
      (quasicoherentPullbackObj s.shrink.site s.shrink.base s.shrink.containsBase
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
        (s.twistPieceQcoh T (locusPoint w ≫ f.hom) i))).obj
    ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
        s.shrink.containsBase T).functor.obj
      (quasicoherentPullbackObj s.shrink.site s.shrink.base s.shrink.containsBase
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
        (s.twistPieceQcoh T (locusPoint w ≫ f.hom) j))).obj
    ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
        s.shrink.containsBase T).functor.obj
      (quasicoherentPullbackObj s.shrink.site s.shrink.base s.shrink.containsBase
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
        (s.twistPieceQcoh T (locusPoint w ≫ f.hom) (i + j)))).obj
    ((chartSourceIso Px w (locusOpen_locusPoint w) i).hom :
    (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase
        (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w :
          (⟨yoneda.obj T, isAlgebraicSpace_yoneda s.shrink.site s.shrink.base
            s.shrink.containsBase T⟩ :
              AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase) ⟶ _)).obj
        (thetaSourceOfUnitalHom s f L ψ Px i).obj ⟶
      ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
          s.shrink.containsBase T).functor.obj
        (quasicoherentPullbackObj s.shrink.site s.shrink.base s.shrink.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
          (s.twistPieceQcoh T (locusPoint w ≫ f.hom) i))).obj)
    ((chartSourceIso Px w (locusOpen_locusPoint w) j).hom :
    (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase
        (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w :
          (⟨yoneda.obj T, isAlgebraicSpace_yoneda s.shrink.site s.shrink.base
            s.shrink.containsBase T⟩ :
              AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase) ⟶ _)).obj
        (thetaSourceOfUnitalHom s f L ψ Px j).obj ⟶
      ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
          s.shrink.containsBase T).functor.obj
        (quasicoherentPullbackObj s.shrink.site s.shrink.base s.shrink.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
          (s.twistPieceQcoh T (locusPoint w ≫ f.hom) j))).obj)
    ((chartSourceIso Px w (locusOpen_locusPoint w) (i + j)).hom :
    (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase
        (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w :
          (⟨yoneda.obj T, isAlgebraicSpace_yoneda s.shrink.site s.shrink.base
            s.shrink.containsBase T⟩ :
              AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase) ⟶ _)).obj
        (thetaSourceOfUnitalHom s f L ψ Px (i + j)).obj ⟶
      ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
          s.shrink.containsBase T).functor.obj
        (quasicoherentPullbackObj s.shrink.site s.shrink.base s.shrink.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
          (s.twistPieceQcoh T (locusPoint w ≫ f.hom) (i + j)))).obj)
    (representedTensorChartMul s.shrink.site s.shrink.base s.shrink.containsBase
      ((quasicoherentPullbackTensorIso s.shrink.site s.shrink.base s.shrink.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
          (s.twistPieceQcoh T (locusPoint w ≫ f.hom) i)
          (s.twistPieceQcoh T (locusPoint w ≫ f.hom) j)).inv ≫
        quasicoherentPullbackMap s.shrink.site s.shrink.base s.shrink.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
          (s.twistPieceMul T (locusPoint w ≫ f.hom) i j)))
    HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
    HEq.rfl HEq.rfl HEq.rfl

end ChartSource

end RelativeProjSituation.InvertibleTwistingRestriction

end AlgebraicGeometry.Space

end
