module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.FunctorialityTwistGlue

/-!
# The glued morphism `r_ψ^*𝒟₁ ⟶ ι^*𝒟₂` on `U(ψ)`

Let `ψ` be a map of graded algebras read over the scheme points of the base
(`AlgebraicGeometry.Space.RelativeProjHomPoints`), `U(ψ) ⊆ Q` its open subspace with
`r_ψ : U(ψ) ⟶ P` and `ι : U(ψ) ⟶ Q`, and `𝒟₁`, `𝒟₂` the modules descended from scheme modules
`M₁`, `M₂` with transitions `τ₁`, `τ₂` along the presentations of `P` and `Q`. A morphism `θ_U` of
the chart pullbacks of `M₁` and `M₂` compatible with the pulled-back transitions glues to a unique
morphism `r_ψ^*𝒟₁ ⟶ ι^*𝒟₂` (`…RelativeProjHomPoints.descendedChartHom`).

When each transition is a comparison along the target followed by the inverse of a comparison
along the source, `τᵢ = aᵢ ≫ bᵢ⁻¹`, the compatibility of `θ_U` reduces to two squares, one over
each projection of the relation, against a morphism `θ_R` on the chart of the relation
(`…RelativeProjHomPoints.chartTransitionsCompatible_of_legs`).

On the chart `U(ψ)_U` over a scheme point `u : U ⟶ X`, `θ_n` is the degree-`n` component of the
map `θ` of Tag 07ZG for `ψ|_U`, read on `U(ψ) ×_X U ≅ U(ψ|_U)`
(`…RelativeProjSituation.twistChartMap`).

## Main definitions

* `Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistHom`: `θ` read on a chart `C ⟶ U(ψ)`.
* `AlgebraicGeometry.Space.RelativeProjHomPoints.chartTwistMap` and
  `AlgebraicGeometry.Space.RelativeProjSituation.twistChartMap`: `θ_n` on the chart of `U(ψ)`.
* `AlgebraicGeometry.Space.schemeTransitionLeg`: the pullback to `R'` of a comparison
  `h^*M ≅ N` along a square `h' ≫ fU = fR ≫ h`.
* `AlgebraicGeometry.Space.RelativeProjHomPoints.descendedChartHom`: the glued morphism.

## Main results

* `AlgebraicGeometry.Space.schemeTransitionPullback_comp_of_legs`: the compatibility of a chart
  morphism with pulled-back transitions, from the two squares of the legs.
* `AlgebraicGeometry.Space.RelativeProjHomPoints.isDescendedChartHom_descendedChartHom` and
  `…eq_descendedChartHom`: the glued morphism is `θ_U` on the chart, and it is the only one.
* `AlgebraicGeometry.Space.RelativeProjSituation.existsUnique_isDescendedChartHom_twistChartMap`:
  the gluing for the twists `𝒪_P(n)`, `𝒪_Q(n)` and the chart map `θ_n`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.Tag07ZGMorphism

universe u m

/-! ### The map `θ` of Tag 07ZG read on a chart of `U(ψ)` -/

namespace Stacks.AlgebraicGeometry.Tag07ZGTwist

variable {S₀ : Scheme.{u}} {A B : SheafGradedAlgebra S₀} (ψ : SheafGradedAlgebraHom A B)
  {C P Q : Scheme.{u}} (a : C ⟶ P) (b : C ⟶ Q) (p : P ⟶ (relativeProj A).scheme)
  (q : Q ⟶ (relativeProj B).scheme) (e : C ⟶ ψ.relativeMapDomain.toScheme)
  (ha : a ≫ p = e ≫ relativeMapHom ψ) (hb : b ≫ q = e ≫ ψ.relativeMapDomain.ι)

/-- **A map of graded algebras on the twists over `U(ψ)`, read on a chart**: for `e : C ⟶ U(ψ)`
and morphisms `a : C ⟶ P`, `b : C ⟶ Q` lying over `r_ψ` and `ι` through `p : P ⟶ Proj(A)` and
`q : Q ⟶ Proj(B)`, the degree-`n` component `a^*p^*𝒪(n) ⟶ b^*q^*𝒪(n)` of `e^*θ`. -/
def chartTwistHom (θ : SheafOfModules.GradedAlgebra.Hom
      (Stacks.RingedSpace.pullbackGradedAlgebra (relativeMapHom ψ).toLRSHom.toShHom
        (twistAlgebra A))
      (Stacks.RingedSpace.pullbackGradedAlgebra ψ.relativeMapDomain.ι.toLRSHom.toShHom
        (twistAlgebra B))) (n : ℤ) :
    (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback p).obj ((twistAlgebra A).piece n)) ⟶
      (Scheme.Modules.pullback b).obj
        ((Scheme.Modules.pullback q).obj ((twistAlgebra B).piece n)) :=
  (Scheme.Modules.pullbackComp a p).hom.app _ ≫ (Scheme.Modules.pullbackCongr ha).hom.app _ ≫
    (Scheme.Modules.pullbackComp e (relativeMapHom ψ)).inv.app _ ≫
    (Scheme.Modules.pullback e).map (θ.app n) ≫
    (Scheme.Modules.pullbackComp e ψ.relativeMapDomain.ι).hom.app _ ≫
    (Scheme.Modules.pullbackCongr hb).inv.app _ ≫ (Scheme.Modules.pullbackComp b q).inv.app _

end Stacks.AlgebraicGeometry.Tag07ZGTwist

namespace AlgebraicGeometry.Space

attribute [local irreducible] CategoryTheory.yoneda

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The legs of a transition -/

section Legs

/-- **The leg of a transition along a square**: for `h : R ⟶ U`, `h' : R' ⟶ U'`, `fU : U' ⟶ U`,
`fR : R' ⟶ R` with `h' ≫ fU = fR ≫ h` and a comparison `a : h^*M ≅ N`, the isomorphism
`h'^*(fU^*M) ≅ (h' ≫ fU)^*M = (fR ≫ h)^*M ≅ fR^*(h^*M) ≅ fR^*N`. -/
def schemeTransitionLeg {U R U' R' : BigFppfOver B S hS} (h : R ⟶ U) (h' : R' ⟶ U')
    (fU : U' ⟶ U) (fR : R' ⟶ R) (hh : h' ≫ fU = fR ≫ h)
    {M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    {N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj R).ringCatSheaf).FullSubcategory}
    (a : quasicoherentPullbackObj B S hS h M ≅ N) :
    quasicoherentPullbackObj B S hS h' (quasicoherentPullbackObj B S hS fU M) ≅
      quasicoherentPullbackObj B S hS fR N :=
  quasicoherentPullbackCompIso B S hS h' fU M ≪≫
    eqToIso (congrArg (fun k => quasicoherentPullbackObj B S hS k M) hh) ≪≫
    (quasicoherentPullbackCompIso B S hS fR h M).symm ≪≫ quasicoherentPullbackMapIso B S hS fR a

variable {U R U' R' : BigFppfOver B S hS} (t s : R ⟶ U) (t' s' : R' ⟶ U') (fU : U' ⟶ U)
  (fR : R' ⟶ R) (ht : t' ≫ fU = fR ≫ t) (hs : fR ≫ s = s' ≫ fU)
  {M : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
  {N : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj R).ringCatSheaf).FullSubcategory}
  (a : quasicoherentPullbackObj B S hS t M ≅ N) (b : quasicoherentPullbackObj B S hS s M ≅ N)

/-- **The pullback of a transition `a ≫ b⁻¹` is the leg of `a` followed by the inverse of the leg
of `b`.** -/
theorem schemeTransitionPullback_eq_leg :
    schemeTransitionPullback B S hS t s t' s' fU fR ht hs M (a.hom ≫ b.inv) =
      (schemeTransitionLeg t t' fU fR ht a).hom ≫
        (schemeTransitionLeg s s' fU fR hs.symm b).inv := by
  rw [schemeTransitionPullback, schemeTransitionReindex, quasicoherentPullbackMap_comp]
  simp only [schemeTransitionLeg, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    eqToIso.hom, eqToIso.inv, Category.assoc]
  rfl

end Legs

section LegSquares

variable {U₁ R₁ U₂ R₂ U' R' : BigFppfOver B S hS} (t₁ s₁ : R₁ ⟶ U₁) (t₂ s₂ : R₂ ⟶ U₂)
  (t' s' : R' ⟶ U') (fU₁ : U' ⟶ U₁) (fR₁ : R' ⟶ R₁) (ht₁ : t' ≫ fU₁ = fR₁ ≫ t₁)
  (hs₁ : fR₁ ≫ s₁ = s' ≫ fU₁) (fU₂ : U' ⟶ U₂) (fR₂ : R' ⟶ R₂) (ht₂ : t' ≫ fU₂ = fR₂ ≫ t₂)
  (hs₂ : fR₂ ≫ s₂ = s' ≫ fU₂)
  {M₁ : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj U₁).ringCatSheaf).FullSubcategory}
  {N₁ : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj R₁).ringCatSheaf).FullSubcategory}
  (a₁ : quasicoherentPullbackObj B S hS t₁ M₁ ≅ N₁)
  (b₁ : quasicoherentPullbackObj B S hS s₁ M₁ ≅ N₁)
  {M₂ : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj U₂).ringCatSheaf).FullSubcategory}
  {N₂ : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj R₂).ringCatSheaf).FullSubcategory}
  (a₂ : quasicoherentPullbackObj B S hS t₂ M₂ ≅ N₂)
  (b₂ : quasicoherentPullbackObj B S hS s₂ M₂ ≅ N₂)
  (θU : quasicoherentPullbackObj B S hS fU₁ M₁ ⟶ quasicoherentPullbackObj B S hS fU₂ M₂)
  (θR : quasicoherentPullbackObj B S hS fR₁ N₁ ⟶ quasicoherentPullbackObj B S hS fR₂ N₂)

/-- **A chart morphism compatible with pulled-back transitions, from the squares of the legs**:
if `θ_U` and `θ_R` commute with the legs of the comparisons along the targets and along the
sources, then `θ_U` carries the pullback of `a₁ ≫ b₁⁻¹` to the pullback of `a₂ ≫ b₂⁻¹`. -/
theorem schemeTransitionPullback_comp_of_legs
    (hlT : (schemeTransitionLeg t₁ t' fU₁ fR₁ ht₁ a₁).hom ≫ θR =
      quasicoherentPullbackMap B S hS t' θU ≫ (schemeTransitionLeg t₂ t' fU₂ fR₂ ht₂ a₂).hom)
    (hlS : (schemeTransitionLeg s₁ s' fU₁ fR₁ hs₁.symm b₁).hom ≫ θR =
      quasicoherentPullbackMap B S hS s' θU ≫
        (schemeTransitionLeg s₂ s' fU₂ fR₂ hs₂.symm b₂).hom) :
    schemeTransitionPullback B S hS t₁ s₁ t' s' fU₁ fR₁ ht₁ hs₁ M₁ (a₁.hom ≫ b₁.inv) ≫
        quasicoherentPullbackMap B S hS s' θU =
      quasicoherentPullbackMap B S hS t' θU ≫
        schemeTransitionPullback B S hS t₂ s₂ t' s' fU₂ fR₂ ht₂ hs₂ M₂ (a₂.hom ≫ b₂.inv) := by
  rw [schemeTransitionPullback_eq_leg, schemeTransitionPullback_eq_leg]
  have hS' : θR ≫ (schemeTransitionLeg s₂ s' fU₂ fR₂ hs₂.symm b₂).inv =
      (schemeTransitionLeg s₁ s' fU₁ fR₁ hs₁.symm b₁).inv ≫
        quasicoherentPullbackMap B S hS s' θU := by
    rw [Iso.eq_inv_comp, ← Category.assoc, hlS, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [Category.assoc, ← hS', ← Category.assoc, hlT, Category.assoc]

end LegSquares

namespace RelativeProjHomPoints

variable {X : AlgebraicSpaces B S hS} {P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {πP : P ⟶ X.obj}
  {πQ : Q ⟶ X.obj} {dP : RelativeProjPoints B S hS πP} {dQ : RelativeProjPoints B S hS πQ}
  (hψ : RelativeProjHomPoints dP dQ) (Px : Presentation B S hS X.obj X.property)
  (hG : IsAlgebraicSpace B S hS hψ.relativeMapSubfunctor.toFunctor)
  (hP : IsAlgebraicSpace B S hS P) (hQ : IsAlgebraicSpace B S hS Q)

/-! ### The compatibility on `U(ψ)` from the squares of the legs -/

section Legs

variable
  {M₁ : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
    (dP.fibre Px.U Px.toSpace)).ringCatSheaf).FullSubcategory}
  {N₁ : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
    (dP.fibre Px.R (RelativeProjPoints.relationPoint Px))).ringCatSheaf).FullSubcategory}
  (a₁ : quasicoherentPullbackObj B S hS (dP.spaceTarget Px hP) M₁ ≅ N₁)
  (b₁ : quasicoherentPullbackObj B S hS (dP.spaceSource Px hP) M₁ ≅ N₁)
  {M₂ : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
    (dQ.fibre Px.U Px.toSpace)).ringCatSheaf).FullSubcategory}
  {N₂ : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
    (dQ.fibre Px.R (RelativeProjPoints.relationPoint Px))).ringCatSheaf).FullSubcategory}
  (a₂ : quasicoherentPullbackObj B S hS (dQ.spaceTarget Px hQ) M₂ ≅ N₂)
  (b₂ : quasicoherentPullbackObj B S hS (dQ.spaceSource Px hQ) M₂ ≅ N₂)
  (θU : quasicoherentPullbackObj B S hS (hψ.chartMapHom Px.U Px.toSpace) M₁ ⟶
    quasicoherentPullbackObj B S hS (hψ.chartIncl Px.U Px.toSpace) M₂)
  (θR : quasicoherentPullbackObj B S hS
      (hψ.chartMapHom Px.R (RelativeProjPoints.relationPoint Px)) N₁ ⟶
    quasicoherentPullbackObj B S hS (hψ.chartIncl Px.R (RelativeProjPoints.relationPoint Px)) N₂)

/-- **The compatibility of `θ_U` with the pulled-back transitions `a₁ ≫ b₁⁻¹` and `a₂ ≫ b₂⁻¹`,
from two squares**: one over the target projections and one over the source projections of the
relation of `U(ψ)`, against a morphism `θ_R` on the chart of the relation. -/
theorem chartTransitionsCompatible_of_legs
    (hlT : (schemeTransitionLeg (dP.spaceTarget Px hP) (hψ.presentationOfBase Px hG).target
        (hψ.chartMapHom Px.U Px.toSpace)
        (hψ.chartMapHom Px.R (RelativeProjPoints.relationPoint Px))
        (hψ.presentationOfBase_target_comp_chartMapHom_spaceTarget Px hG hP) a₁).hom ≫ θR =
      quasicoherentPullbackMap B S hS (hψ.presentationOfBase Px hG).target θU ≫
        (schemeTransitionLeg (dQ.spaceTarget Px hQ) (hψ.presentationOfBase Px hG).target
          (hψ.chartIncl Px.U Px.toSpace)
          (hψ.chartIncl Px.R (RelativeProjPoints.relationPoint Px))
          (hψ.presentationOfBase_target_comp_chartIncl_spaceTarget Px hG hQ) a₂).hom)
    (hlS : (schemeTransitionLeg (dP.spaceSource Px hP) (hψ.presentationOfBase Px hG).source
        (hψ.chartMapHom Px.U Px.toSpace)
        (hψ.chartMapHom Px.R (RelativeProjPoints.relationPoint Px))
        (hψ.chartMapHom_spaceSource_comp_presentationOfBase_source Px hG hP).symm b₁).hom ≫ θR =
      quasicoherentPullbackMap B S hS (hψ.presentationOfBase Px hG).source θU ≫
        (schemeTransitionLeg (dQ.spaceSource Px hQ) (hψ.presentationOfBase Px hG).source
          (hψ.chartIncl Px.U Px.toSpace)
          (hψ.chartIncl Px.R (RelativeProjPoints.relationPoint Px))
          (hψ.chartIncl_spaceSource_comp_presentationOfBase_source Px hG hQ).symm b₂).hom) :
    hψ.ChartTransitionsCompatible Px hG hP hQ M₁ (a₁.hom ≫ b₁.inv) M₂ (a₂.hom ≫ b₂.inv) θU :=
  schemeTransitionPullback_comp_of_legs (dP.spaceTarget Px hP) (dP.spaceSource Px hP)
    (dQ.spaceTarget Px hQ) (dQ.spaceSource Px hQ) (hψ.presentationOfBase Px hG).target
    (hψ.presentationOfBase Px hG).source (hψ.chartMapHom Px.U Px.toSpace)
    (hψ.chartMapHom Px.R (RelativeProjPoints.relationPoint Px))
    (hψ.presentationOfBase_target_comp_chartMapHom_spaceTarget Px hG hP)
    (hψ.chartMapHom_spaceSource_comp_presentationOfBase_source Px hG hP)
    (hψ.chartIncl Px.U Px.toSpace) (hψ.chartIncl Px.R (RelativeProjPoints.relationPoint Px))
    (hψ.presentationOfBase_target_comp_chartIncl_spaceTarget Px hG hQ)
    (hψ.chartIncl_spaceSource_comp_presentationOfBase_source Px hG hQ) a₁ b₁ a₂ b₂ θU θR hlT hlS

/-- **The compatibility of `θ_U` with the pulled-back transitions, from the squares of the legs
over every square of charts**: `chartTransitionsCompatible_of_legs`, with the two squares asked for
every morphism `t'` of the charts of `U(ψ)` over the target (resp. source) projections. -/
theorem chartTransitionsCompatible_of_chartLegs
    (hlT : ∀ (t' : hψ.chartObj Px.R (RelativeProjPoints.relationPoint Px) ⟶
        hψ.chartObj Px.U Px.toSpace)
      (ht₁ : t' ≫ hψ.chartMapHom Px.U Px.toSpace =
        hψ.chartMapHom Px.R (RelativeProjPoints.relationPoint Px) ≫ dP.spaceTarget Px hP)
      (ht₂ : t' ≫ hψ.chartIncl Px.U Px.toSpace =
        hψ.chartIncl Px.R (RelativeProjPoints.relationPoint Px) ≫ dQ.spaceTarget Px hQ),
      (schemeTransitionLeg (dP.spaceTarget Px hP) t' (hψ.chartMapHom Px.U Px.toSpace)
          (hψ.chartMapHom Px.R (RelativeProjPoints.relationPoint Px)) ht₁ a₁).hom ≫ θR =
        quasicoherentPullbackMap B S hS t' θU ≫
          (schemeTransitionLeg (dQ.spaceTarget Px hQ) t' (hψ.chartIncl Px.U Px.toSpace)
            (hψ.chartIncl Px.R (RelativeProjPoints.relationPoint Px)) ht₂ a₂).hom)
    (hlS : ∀ (t' : hψ.chartObj Px.R (RelativeProjPoints.relationPoint Px) ⟶
        hψ.chartObj Px.U Px.toSpace)
      (ht₁ : t' ≫ hψ.chartMapHom Px.U Px.toSpace =
        hψ.chartMapHom Px.R (RelativeProjPoints.relationPoint Px) ≫ dP.spaceSource Px hP)
      (ht₂ : t' ≫ hψ.chartIncl Px.U Px.toSpace =
        hψ.chartIncl Px.R (RelativeProjPoints.relationPoint Px) ≫ dQ.spaceSource Px hQ),
      (schemeTransitionLeg (dP.spaceSource Px hP) t' (hψ.chartMapHom Px.U Px.toSpace)
          (hψ.chartMapHom Px.R (RelativeProjPoints.relationPoint Px)) ht₁ b₁).hom ≫ θR =
        quasicoherentPullbackMap B S hS t' θU ≫
          (schemeTransitionLeg (dQ.spaceSource Px hQ) t' (hψ.chartIncl Px.U Px.toSpace)
            (hψ.chartIncl Px.R (RelativeProjPoints.relationPoint Px)) ht₂ b₂).hom) :
    hψ.ChartTransitionsCompatible Px hG hP hQ M₁ (a₁.hom ≫ b₁.inv) M₂ (a₂.hom ≫ b₂.inv) θU :=
  hψ.chartTransitionsCompatible_of_legs Px hG hP hQ a₁ b₁ a₂ b₂ θU θR
    (hlT (hψ.presentationOfBase Px hG).target
      (hψ.presentationOfBase_target_comp_chartMapHom_spaceTarget Px hG hP)
      (hψ.presentationOfBase_target_comp_chartIncl_spaceTarget Px hG hQ))
    (hlS (hψ.presentationOfBase Px hG).source
      (hψ.chartMapHom_spaceSource_comp_presentationOfBase_source Px hG hP).symm
      (hψ.chartIncl_spaceSource_comp_presentationOfBase_source Px hG hQ).symm)

end Legs

/-! ### The map `θ` of Tag 07ZG on the chart `U(ψ)_U` -/

section ChartTwist

variable (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X.obj)

/-- On the chart, `r_ψ` lies over `r_{ψ|_T}` through any morphism equal to the identification of
`P ×_X T` with `Proj_T(𝒜|_T)`. -/
theorem toScheme_map_chartMapHom_comp_of_eq
    (p : (BigFppfOver.toScheme B S hS).obj (dP.fibre T f) ⟶ (relativeProj (dP.algebra T f)).scheme)
    (hp : p = (dP.fibreIso T f).hom) :
    (BigFppfOver.toScheme B S hS).map (hψ.chartMapHom T f) ≫ p =
      (hψ.chartSchemeIso T f).hom ≫ relativeMapHom (hψ.hom T f) :=
  hp ▸ hψ.toScheme_map_chartMapHom T f

/-- On the chart, `ι` lies over the inclusion of `U(ψ|_T)` through any morphism equal to the
identification of `Q ×_X T` with `Proj_T(ℬ|_T)`. -/
theorem toScheme_map_chartIncl_comp_of_eq
    (q : (BigFppfOver.toScheme B S hS).obj (dQ.fibre T f) ⟶ (relativeProj (dQ.algebra T f)).scheme)
    (hq : q = (dQ.fibreIso T f).hom) :
    (BigFppfOver.toScheme B S hS).map (hψ.chartIncl T f) ≫ q =
      (hψ.chartSchemeIso T f).hom ≫ (hψ.hom T f).relativeMapDomain.ι :=
  hq ▸ (hψ.chartSchemeIso_hom_ι T f).symm

variable (n : ℤ)
  {M₁ : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
    (dP.fibre T f)).ringCatSheaf).FullSubcategory}
  (p : (BigFppfOver.toScheme B S hS).obj (dP.fibre T f) ⟶ (relativeProj (dP.algebra T f)).scheme)
  (hp : p = (dP.fibreIso T f).hom)
  (c₁ : @Iso (SheafOfModules.{u} ((BigFppfOver.toScheme B S hS).obj
      (dP.fibre T f)).ringCatSheaf) _ M₁.obj
    ((Scheme.Modules.pullback p).obj
      ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dP.algebra T f)).piece n)))
  {M₂ : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
    (dQ.fibre T f)).ringCatSheaf).FullSubcategory}
  (q : (BigFppfOver.toScheme B S hS).obj (dQ.fibre T f) ⟶ (relativeProj (dQ.algebra T f)).scheme)
  (hq : q = (dQ.fibreIso T f).hom)
  (c₂ : @Iso (SheafOfModules.{u} ((BigFppfOver.toScheme B S hS).obj
      (dQ.fibre T f)).ringCatSheaf) _ M₂.obj
    ((Scheme.Modules.pullback q).obj
      ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dQ.algebra T f)).piece n)))

/-- **The map `θ_n` of Tag 07ZG for `ψ|_T`, read on the chart of `U(ψ)` over `T`**: for modules
`M₁`, `M₂` identified (by `c₁`, `c₂`) with the twists `𝒪(n)` of `Proj_T(𝒜|_T)` and
`Proj_T(ℬ|_T)`, the morphism `r_ψ^*M₁ ⟶ ι^*M₂` on the chart whose underlying morphism is the
degree-`n` component of the inverse image of `θ` along `U(ψ) ×_X T ≅ U(ψ|_T)`. -/
def chartTwistMap :
    quasicoherentPullbackObj B S hS (hψ.chartMapHom T f) M₁ ⟶
      quasicoherentPullbackObj B S hS (hψ.chartIncl T f) M₂ :=
  ObjectProperty.homMk
    ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map (hψ.chartMapHom T f))).map
        c₁.hom ≫
      Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistHom (hψ.hom T f)
        ((BigFppfOver.toScheme B S hS).map (hψ.chartMapHom T f))
        ((BigFppfOver.toScheme B S hS).map (hψ.chartIncl T f)) p q (hψ.chartSchemeIso T f).hom
        (hψ.toScheme_map_chartMapHom_comp_of_eq T f p hp)
        (hψ.toScheme_map_chartIncl_comp_of_eq T f q hq)
        (Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistAlgebraHom (hψ.hom T f)) n ≫
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map (hψ.chartIncl T f))).map
        c₂.inv)

end ChartTwist

/-! ### The glued morphism -/

section Descended

variable
  (M₁ : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
    (dP.fibre Px.U Px.toSpace)).ringCatSheaf).FullSubcategory)
  (τ₁ : quasicoherentPullbackObj B S hS (dP.spaceTarget Px hP) M₁ ⟶
    quasicoherentPullbackObj B S hS (dP.spaceSource Px hP) M₁)
  (hτ₁ : PresentationSchemeCocycle (dP.spacePresentation Px hP) M₁ τ₁)
  (hu₁ : PresentationSchemeUnit (dP.spacePresentation Px hP) M₁ τ₁)
  (M₂ : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
    (dQ.fibre Px.U Px.toSpace)).ringCatSheaf).FullSubcategory)
  (τ₂ : quasicoherentPullbackObj B S hS (dQ.spaceTarget Px hQ) M₂ ⟶
    quasicoherentPullbackObj B S hS (dQ.spaceSource Px hQ) M₂)
  (hτ₂ : PresentationSchemeCocycle (dQ.spacePresentation Px hQ) M₂ τ₂)
  (hu₂ : PresentationSchemeUnit (dQ.spacePresentation Px hQ) M₂ τ₂)
  (θU : quasicoherentPullbackObj B S hS (hψ.chartMapHom Px.U Px.toSpace) M₁ ⟶
    quasicoherentPullbackObj B S hS (hψ.chartIncl Px.U Px.toSpace) M₂)
  (hθU : hψ.ChartTransitionsCompatible Px hG hP hQ M₁ τ₁ M₂ τ₂ θU)

/-- **The morphism `r_ψ^*𝒟₁ ⟶ ι^*𝒟₂` glued from `θ_U`**, for the modules `𝒟ᵢ` descended from
`(Mᵢ, τᵢ)` and a chart morphism `θ_U` compatible with the pulled-back transitions. -/
def descendedChartHom :
    (modulePullback B S hS (ObjectProperty.homMk hψ.relativeMapSpaceHom :
        (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨P, hP⟩)).obj
        (presentationDescendedModule (dP.spacePresentation Px hP) M₁ τ₁ hτ₁ hu₁).obj ⟶
      (modulePullback B S hS (ObjectProperty.homMk hψ.relativeMapSubfunctor.ι :
        (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Q, hQ⟩)).obj
        (presentationDescendedModule (dQ.spacePresentation Px hQ) M₂ τ₂ hτ₂ hu₂).obj :=
  (hψ.existsUnique_isDescendedChartHom Px hG hP hQ M₁ τ₁ hτ₁ hu₁ M₂ τ₂ hτ₂ hu₂ θU
    hθU).exists.choose

/-- **The glued morphism is `θ_U` on the chart `U(ψ)_U`.** -/
theorem isDescendedChartHom_descendedChartHom :
    hψ.IsDescendedChartHom Px hG hP hQ M₁ τ₁ hτ₁ hu₁ M₂ τ₂ hτ₂ hu₂ θU
      (hψ.descendedChartHom Px hG hP hQ M₁ τ₁ hτ₁ hu₁ M₂ τ₂ hτ₂ hu₂ θU hθU) :=
  (hψ.existsUnique_isDescendedChartHom Px hG hP hQ M₁ τ₁ hτ₁ hu₁ M₂ τ₂ hτ₂ hu₂ θU
    hθU).exists.choose_spec

/-- **The glued morphism is the only morphism which is `θ_U` on the chart.** -/
theorem eq_descendedChartHom
    {χ : (modulePullback B S hS (ObjectProperty.homMk hψ.relativeMapSpaceHom :
        (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨P, hP⟩)).obj
        (presentationDescendedModule (dP.spacePresentation Px hP) M₁ τ₁ hτ₁ hu₁).obj ⟶
      (modulePullback B S hS (ObjectProperty.homMk hψ.relativeMapSubfunctor.ι :
        (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Q, hQ⟩)).obj
        (presentationDescendedModule (dQ.spacePresentation Px hQ) M₂ τ₂ hτ₂ hu₂).obj}
    (hχ : hψ.IsDescendedChartHom Px hG hP hQ M₁ τ₁ hτ₁ hu₁ M₂ τ₂ hτ₂ hu₂ θU χ) :
    χ = hψ.descendedChartHom Px hG hP hQ M₁ τ₁ hτ₁ hu₁ M₂ τ₂ hτ₂ hu₂ θU hθU :=
  (hψ.existsUnique_isDescendedChartHom Px hG hP hQ M₁ τ₁ hτ₁ hu₁ M₂ τ₂ hτ₂ hu₂ θU
    hθU).unique hχ (hψ.isDescendedChartHom_descendedChartHom Px hG hP hQ M₁ τ₁ hτ₁ hu₁ M₂ τ₂
      hτ₂ hu₂ θU hθU)

end Descended

end RelativeProjHomPoints

namespace RelativeProjSituation

/-! ### The twists of Situation 0849 as inverse images of the twists of Tag 01NR -/

section Generic

variable (s : RelativeProjSituation.{u, m}) (V : BigFppfOver s.site s.base s.containsBase)
  (v : yoneda.obj V ⟶ s.space.1)

/-- The reading of the scheme of `V ×_X P` as `Proj_V(v^*𝒜)` is the identification of the second
assertion of Stacks 084B. -/
theorem toRelativeProj_eq_fibreIso_hom :
    s.toRelativeProj V v = (s.relativeProjPoints.fibreIso V v).hom :=
  rfl

/-- **The twist `𝒪(n)` on the scheme of `V ×_X P` is the inverse image of the twist of Tag 01NR**
along `AlgebraicGeometry.Space.RelativeProjSituation.toRelativeProj`: the identity. -/
def twistPieceQcohObjIso (n : ℤ) :
    @Iso (SheafOfModules.{u} ((BigFppfOver.toScheme s.site s.base s.containsBase).obj
        (s.relativeProjPoints.fibre V v)).ringCatSheaf) _ (s.twistPieceQcoh V v n).obj
      ((Scheme.Modules.pullback (s.toRelativeProj V v)).obj
        ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra
          (s.relativeProjPoints.algebra V v)).piece n)) :=
  Iso.refl _

end Generic

/-! ### The map `θ_n` of Tag 07ZG on the chart of `U(ψ)`, for a map of graded algebras -/

section Map

variable {X : AlgebraicSpaces B S hS}
  {𝒜₁ 𝒜₂ : SheafOfModules.GradedAlgebra.{u, m, u, u + 1} (structureRingSheaf B S hS X)}
  (h₁c : ∀ (i j : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : (𝒜₁.piece i).val.obj U)
    (b : (𝒜₁.piece j).val.obj U), HEq ((𝒜₁.mul i j).app U a b) ((𝒜₁.mul j i).app U b a))
  (h₁n : ∀ n : ℤ, n < 0 → Limits.IsZero (𝒜₁.piece n))
  (h₁q : ∀ n : ℤ, (𝒜₁.piece n).IsQuasicoherentOnSite)
  (h₁k : ∀ (n : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ),
    HasCardinalLT ↥((𝒜₁.piece n).val.obj U) B.cutoff)
  (h₂c : ∀ (i j : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : (𝒜₂.piece i).val.obj U)
    (b : (𝒜₂.piece j).val.obj U), HEq ((𝒜₂.mul i j).app U a b) ((𝒜₂.mul j i).app U b a))
  (h₂n : ∀ n : ℤ, n < 0 → Limits.IsZero (𝒜₂.piece n))
  (h₂q : ∀ n : ℤ, (𝒜₂.piece n).IsQuasicoherentOnSite)
  (h₂k : ∀ (n : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ),
    HasCardinalLT ↥((𝒜₂.piece n).val.obj U) B.cutoff)
  (ψ : SheafOfModules.GradedAlgebra.UnitalHom 𝒜₁ 𝒜₂)
  (Px : Presentation B S hS X.1 X.2)

local notation "𝔰₁" => RelativeProjSituation.mk B S hS X 𝒜₁ h₁c h₁n h₁q h₁k
local notation "𝔰₂" => RelativeProjSituation.mk B S hS X 𝒜₂ h₂c h₂n h₂q h₂k
local notation "𝔥" => homPoints h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ
local notation "𝒢" => relativeMapSpace h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ

/-- **The map `θ_n : r_ψ^*𝒪_P(n) ⟶ ι^*𝒪_Q(n)` of Stacks 085F on the chart `U(ψ)_U`** over a scheme
point `u : U ⟶ X`: the degree-`n` component of Tag 07ZG's `θ` for `ψ|_U`, read on
`U(ψ) ×_X U ≅ U(ψ|_U)`. -/
def twistChartMap (U : BigFppfOver B S hS) (u : yoneda.obj U ⟶ X.1) (n : ℤ) :
    quasicoherentPullbackObj B S hS ((𝔥).chartMapHom U u) ((𝔰₁).twistPieceQcoh U u n) ⟶
      quasicoherentPullbackObj B S hS ((𝔥).chartIncl U u) ((𝔰₂).twistPieceQcoh U u n) :=
  (𝔥).chartTwistMap U u n ((𝔰₁).toRelativeProj U u) ((𝔰₁).toRelativeProj_eq_fibreIso_hom U u)
    ((𝔰₁).twistPieceQcohObjIso U u n) ((𝔰₂).toRelativeProj U u)
    ((𝔰₂).toRelativeProj_eq_fibreIso_hom U u) ((𝔰₂).twistPieceQcohObjIso U u n)

/-- **Gluing `θ_n` from the chart `U(ψ)_U`**: once the chart map `θ_n` of Tag 07ZG is compatible
with the transitions of the twists `𝒪_P(n)` and `𝒪_Q(n)`, there is a unique morphism
`r_ψ^*𝒪_P(n) ⟶ ι^*𝒪_Q(n)` which is `θ_n` on the chart. -/
theorem existsUnique_isDescendedChartHom_twistChartMap (n : ℤ)
    (hθU : (𝔥).ChartTransitionsCompatible Px (𝒢).2 (𝔰₁).isAlgebraicSpace_relativeProjFunctor
      (𝔰₂).isAlgebraicSpace_relativeProjFunctor ((𝔰₁).twistPieceQcoh Px.U Px.toSpace n)
      ((𝔰₁).twistTransition Px n) ((𝔰₂).twistPieceQcoh Px.U Px.toSpace n)
      ((𝔰₂).twistTransition Px n)
      (twistChartMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px.U Px.toSpace n)) :
    ∃! χ, (𝔥).IsDescendedChartHom Px (𝒢).2 (𝔰₁).isAlgebraicSpace_relativeProjFunctor
      (𝔰₂).isAlgebraicSpace_relativeProjFunctor ((𝔰₁).twistPieceQcoh Px.U Px.toSpace n)
      ((𝔰₁).twistTransition Px n) ((𝔰₁).presentationSchemeCocycle_twistTransition Px n)
      ((𝔰₁).presentationSchemeUnit_twistTransition Px n)
      ((𝔰₂).twistPieceQcoh Px.U Px.toSpace n)
      ((𝔰₂).twistTransition Px n) ((𝔰₂).presentationSchemeCocycle_twistTransition Px n)
      ((𝔰₂).presentationSchemeUnit_twistTransition Px n)
      (twistChartMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px.U Px.toSpace n) χ :=
  (𝔥).existsUnique_isDescendedChartHom Px (𝒢).2 (𝔰₁).isAlgebraicSpace_relativeProjFunctor
      (𝔰₂).isAlgebraicSpace_relativeProjFunctor ((𝔰₁).twistPieceQcoh Px.U Px.toSpace n)
      ((𝔰₁).twistTransition Px n) ((𝔰₁).presentationSchemeCocycle_twistTransition Px n)
      ((𝔰₁).presentationSchemeUnit_twistTransition Px n)
      ((𝔰₂).twistPieceQcoh Px.U Px.toSpace n)
      ((𝔰₂).twistTransition Px n) ((𝔰₂).presentationSchemeCocycle_twistTransition Px n)
      ((𝔰₂).presentationSchemeUnit_twistTransition Px n)
      (twistChartMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px.U Px.toSpace n) hθU

end Map

end RelativeProjSituation

end AlgebraicGeometry.Space

end
