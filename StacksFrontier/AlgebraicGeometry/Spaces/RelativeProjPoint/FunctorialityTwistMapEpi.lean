module

public import StacksFrontier.AlgebraicGeometry.Morphism.TwistEventual
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.FunctorialityClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.FunctorialityTwistGlueLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.FunctorialityTwistMap

/-!
# The chart map `θ_n` of Stacks 085F is surjective, resp. bijective, when Tag 07ZG's is

The map `θ_n : r_ψ^*𝒪_P(n) ⟶ ι^*𝒪_Q(n)` of Stacks 085F is glued from its chart on `U(ψ)_U`: the
morphism of quasi-coherent modules on a scheme
`AlgebraicGeometry.Space.RelativeProjHomPoints.chartTwistMap`,
which is Tag 07ZG's `θ_n` for `ψ|_T` conjugated by isomorphisms, read on the small étale site of
the chart through Stacks 03DX
(`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`). This file transports
surjectivity and bijectivity of Tag 07ZG's `θ_n` to that étale chart map, which is the form
consumed by `AlgebraicGeometry.Space.Presentation.IsAtlasMapComp.epi_iff` and `….isIso_iff`.

## Main results

* `Stacks.AlgebraicGeometry.Tag07ZGTwist.epi_chartTwistHom`, `…isIso_chartTwistHom`.
* `AlgebraicGeometry.Space.epi_representedQuasicoherentSchemeEquivalence_map_hom` and
  `…isIso_…`: Stacks 03DX's equivalence preserves surjectivity and bijectivity.
* `AlgebraicGeometry.Space.RelativeProjHomPoints.epi_equivalence_map_chartTwistMap` and
  `…isIso_…`: the étale chart map of `θ_n` from Tag 07ZG's `θ_n`.
* `AlgebraicGeometry.Space.RelativeProjSituation.epi_equivalence_map_twistChartMap`: for a map
  `ψ : 𝒜₁ ⟶ 𝒜₂` surjective in high degree, the étale chart map is an epimorphism (the chart
  form of Stacks 085H (3), via Stacks 07ZI (3)).
* `AlgebraicGeometry.Space.RelativeProjSituation.epi_of_isDescendedChartHom_twistChartMap`: every
  morphism `r_ψ^*𝒪_P(n) ⟶ ι^*𝒪_Q(n)` which is that chart map on `U(ψ)_U` is an epimorphism.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry Filter
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.Tag07ZGMorphism

universe u m

namespace Stacks.AlgebraicGeometry.Tag07ZGTwist

variable {S₀ : Scheme.{u}} {A B : SheafGradedAlgebra S₀} (ψ : SheafGradedAlgebraHom A B)
  {C P Q : Scheme.{u}} (a : C ⟶ P) (b : C ⟶ Q) (p : P ⟶ (relativeProj A).scheme)
  (q : Q ⟶ (relativeProj B).scheme) (e : C ⟶ ψ.relativeMapDomain.toScheme)
  (ha : a ≫ p = e ≫ relativeMapHom ψ) (hb : b ≫ q = e ≫ ψ.relativeMapDomain.ι)
  (θ : SheafOfModules.GradedAlgebra.Hom
      (Stacks.RingedSpace.pullbackGradedAlgebra (relativeMapHom ψ).toLRSHom.toShHom
        (twistAlgebra A))
      (Stacks.RingedSpace.pullbackGradedAlgebra ψ.relativeMapDomain.ι.toLRSHom.toShHom
        (twistAlgebra B))) (n : ℤ)

/-- The chart reading of `θ` as an isomorphism, then the inverse image of `θ` along `e`, then an
isomorphism. -/
theorem chartTwistHom_eq_isoComp :
    chartTwistHom ψ a b p q e ha hb θ n =
      ((Scheme.Modules.pullbackComp a p).app _ ≪≫ (Scheme.Modules.pullbackCongr ha).app _ ≪≫
          ((Scheme.Modules.pullbackComp e (relativeMapHom ψ)).app _).symm).hom ≫
        (Scheme.Modules.pullback e).map (θ.app n) ≫
        ((Scheme.Modules.pullbackComp e ψ.relativeMapDomain.ι).app _ ≪≫
          ((Scheme.Modules.pullbackCongr hb).app _).symm ≪≫
          ((Scheme.Modules.pullbackComp b q).app _).symm).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rfl

/-- The chart reading of `θ` is an epimorphism when `θ` is in degree `n`. -/
theorem epi_chartTwistHom (h : Epi (θ.app n)) : Epi (chartTwistHom ψ a b p q e ha hb θ n) := by
  have := (Scheme.Modules.pullbackPushforwardAdjunction e).isLeftAdjoint
  have h1 : Epi ((Scheme.Modules.pullback e).map (θ.app n)) :=
    @Functor.map_epi _ _ _ _ _ inferInstance _ _ _ h
  rw [chartTwistHom_eq_isoComp]
  exact @epi_comp _ _ _ _ _ _ (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom _)) _
    (@epi_comp _ _ _ _ _ _ h1 _ (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom _)))

/-- The chart reading of `θ` is an isomorphism when `θ` is in degree `n`. -/
theorem isIso_chartTwistHom (h : IsIso (θ.app n)) :
    IsIso (chartTwistHom ψ a b p q e ha hb θ n) := by
  have h1 : IsIso ((Scheme.Modules.pullback e).map (θ.app n)) :=
    @Functor.map_isIso _ _ _ _ _ _ _ _ h
  rw [chartTwistHom_eq_isoComp]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _)
    (@IsIso.comp_isIso _ _ _ _ _ _ _ h1 (Iso.isIso_hom _))

end Stacks.AlgebraicGeometry.Tag07ZGTwist

namespace AlgebraicGeometry.Space

attribute [local irreducible] CategoryTheory.yoneda

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 03DX's equivalence `QCoh(𝒪_U) ≌ QCoh(U_étale)` preserves epimorphisms**, read on
the underlying modules: its functor is the associated-module functor, a left adjoint, followed by
an equivalence of module categories. -/
theorem epi_representedQuasicoherentSchemeEquivalence_map_hom (U : BigFppfOver B S hS)
    {M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    (θ : M ⟶ N) (h : Epi θ.hom) :
    Epi ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map θ).hom := by
  have h1 : Epi ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).map θ.hom) :=
    have := (_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U)
      U.left.property).isLeftAdjoint
    @Functor.map_epi _ _ _ _ _ (Functor.preservesEpimorphisms_of_isLeftAdjoint _) _ _ _ h
  have := (representedSmallEtaleModuleEquivalence B S hS U).toAdjunction.isLeftAdjoint
  exact @Functor.map_epi _ _ _ _ (representedSmallEtaleModuleEquivalence B S hS U).functor
    (Functor.preservesEpimorphisms_of_isLeftAdjoint _) _ _ _ h1

/-- **Stacks 03DX's equivalence preserves isomorphisms**, read on the underlying modules. -/
theorem isIso_representedQuasicoherentSchemeEquivalence_map_hom (U : BigFppfOver B S hS)
    {M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    (θ : M ⟶ N) (h : IsIso θ.hom) :
    IsIso ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map θ).hom := by
  have h1 : IsIso ((_root_.AlgebraicGeometry.SmallEtale.associatedModule
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property).map
        θ.hom) :=
    Iso.isIso_hom ((_root_.AlgebraicGeometry.SmallEtale.associatedModule
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property).mapIso
        (@asIso _ _ _ _ θ.hom h))
  exact Iso.isIso_hom ((representedSmallEtaleModuleEquivalence B S hS U).functor.mapIso
    (@asIso _ _ _ _ _ h1))

namespace RelativeProjHomPoints

variable {X : AlgebraicSpaces B S hS} {P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {πP : P ⟶ X.obj}
  {πQ : Q ⟶ X.obj} {dP : RelativeProjPoints B S hS πP} {dQ : RelativeProjPoints B S hS πQ}
  (hψ : RelativeProjHomPoints dP dQ) (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X.obj) (n : ℤ)
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

/-- **The chart map `θ_n` is an epimorphism when Tag 07ZG's `θ_n` for `ψ|_T` is.** -/
theorem epi_chartTwistMap_hom
    (h : Epi (Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistMap (hψ.hom T f) n)) :
    Epi (hψ.chartTwistMap T f n p hp c₁ q hq c₂).hom := by
  have h2 := Stacks.AlgebraicGeometry.Tag07ZGTwist.epi_chartTwistHom (hψ.hom T f)
    ((BigFppfOver.toScheme B S hS).map (hψ.chartMapHom T f))
    ((BigFppfOver.toScheme B S hS).map (hψ.chartIncl T f)) p q (hψ.chartSchemeIso T f).hom
    (hψ.toScheme_map_chartMapHom_comp_of_eq T f p hp)
    (hψ.toScheme_map_chartIncl_comp_of_eq T f q hq)
    (Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistAlgebraHom (hψ.hom T f)) n h
  have h1 := Iso.isIso_hom ((Scheme.Modules.pullback
    ((BigFppfOver.toScheme B S hS).map (hψ.chartMapHom T f))).mapIso c₁)
  have h3 := Iso.isIso_hom ((Scheme.Modules.pullback
    ((BigFppfOver.toScheme B S hS).map (hψ.chartIncl T f))).mapIso c₂.symm)
  exact @epi_comp _ _ _ _ _ _ (@IsIso.epi_of_iso _ _ _ _ _ h1) _
    (@epi_comp _ _ _ _ _ _ h2 _ (@IsIso.epi_of_iso _ _ _ _ _ h3))

/-- **The chart map `θ_n` is an isomorphism when Tag 07ZG's `θ_n` for `ψ|_T` is.** -/
theorem isIso_chartTwistMap_hom
    (h : IsIso (Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistMap (hψ.hom T f) n)) :
    IsIso (hψ.chartTwistMap T f n p hp c₁ q hq c₂).hom := by
  have h2 := Stacks.AlgebraicGeometry.Tag07ZGTwist.isIso_chartTwistHom (hψ.hom T f)
    ((BigFppfOver.toScheme B S hS).map (hψ.chartMapHom T f))
    ((BigFppfOver.toScheme B S hS).map (hψ.chartIncl T f)) p q (hψ.chartSchemeIso T f).hom
    (hψ.toScheme_map_chartMapHom_comp_of_eq T f p hp)
    (hψ.toScheme_map_chartIncl_comp_of_eq T f q hq)
    (Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistAlgebraHom (hψ.hom T f)) n h
  have h1 := Iso.isIso_hom ((Scheme.Modules.pullback
    ((BigFppfOver.toScheme B S hS).map (hψ.chartMapHom T f))).mapIso c₁)
  have h3 := Iso.isIso_hom ((Scheme.Modules.pullback
    ((BigFppfOver.toScheme B S hS).map (hψ.chartIncl T f))).mapIso c₂.symm)
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 (@IsIso.comp_isIso _ _ _ _ _ _ _ h2 h3)

/-- **The étale chart map of `θ_n` is an epimorphism when Tag 07ZG's `θ_n` for `ψ|_T` is**: the
chart map read on the small étale site of the chart through Stacks 03DX. -/
theorem epi_equivalence_map_chartTwistMap
    (h : Epi (Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistMap (hψ.hom T f) n)) :
    Epi ((representedQuasicoherentSchemeEquivalence B S hS _).functor.map
      (hψ.chartTwistMap T f n p hp c₁ q hq c₂)).hom :=
  epi_representedQuasicoherentSchemeEquivalence_map_hom _ _
    (hψ.epi_chartTwistMap_hom T f n p hp c₁ q hq c₂ h)

/-- **The étale chart map of `θ_n` is an isomorphism when Tag 07ZG's `θ_n` for `ψ|_T` is.** -/
theorem isIso_equivalence_map_chartTwistMap
    (h : IsIso (Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistMap (hψ.hom T f) n)) :
    IsIso ((representedQuasicoherentSchemeEquivalence B S hS _).functor.map
      (hψ.chartTwistMap T f n p hp c₁ q hq c₂)).hom :=
  isIso_representedQuasicoherentSchemeEquivalence_map_hom _ _
    (hψ.isIso_chartTwistMap_hom T f n p hp c₁ q hq c₂ h)

end RelativeProjHomPoints

namespace RelativeProjSituation

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

/-- **The étale chart map of the `θ_n` of Stacks 085F is an epimorphism** when `ψ_d` is
surjective for `d ≫ 0`: Tag 07ZG's `θ_n` for `ψ|_U` is, by Stacks 07ZI (3). This is the chart
form of the surjectivity in Stacks 085H (3). -/
theorem epi_equivalence_map_twistChartMap
    (hsurj : ∀ᶠ d : ℕ in atTop, Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X.1)
      ((PresheafOfModules.toPresheaf _).map (ψ.app (d : ℤ)).val))
    (U : BigFppfOver B S hS) (u : yoneda.obj U ⟶ X.1) (n : ℤ) :
    Epi ((representedQuasicoherentSchemeEquivalence B S hS _).functor.map
      (twistChartMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ U u n)).hom :=
  RelativeProjHomPoints.epi_equivalence_map_chartTwistMap _ U u n _ _ _ _ _ _
    (Stacks.AlgebraicGeometry.Tag07ZGTwist.epi_relativeTwistMap_of_eventually_epi _
      (hsurj.mono fun d hd => epi_restrictHom_app h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ d hd U u) n)

local notation "𝔰₁" => RelativeProjSituation.mk B S hS X 𝒜₁ h₁c h₁n h₁q h₁k
local notation "𝔰₂" => RelativeProjSituation.mk B S hS X 𝒜₂ h₂c h₂n h₂q h₂k
local notation "𝔥" => homPoints h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ
local notation "𝒢" => relativeMapSpace h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ

/-- **Stacks 085H (3), surjectivity, for every morphism glued from the chart map `θ_n`**: if
`ψ_d` is surjective for `d ≫ 0`, every morphism `r_ψ^*𝒪_P(n) ⟶ ι^*𝒪_Q(n)` which is Tag 07ZG's
`θ_n` on the chart `U(ψ)_U` (in particular the glued `θ_n` of Stacks 085F) is an epimorphism. -/
theorem epi_of_isDescendedChartHom_twistChartMap
    (hsurj : ∀ᶠ d : ℕ in atTop, Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X.1)
      ((PresheafOfModules.toPresheaf _).map (ψ.app (d : ℤ)).val))
    (Px : Presentation B S hS X.1 X.2) (n : ℤ) {χ}
    (hχ : (𝔥).IsDescendedChartHom Px (𝒢).2 (𝔰₁).isAlgebraicSpace_relativeProjFunctor
      (𝔰₂).isAlgebraicSpace_relativeProjFunctor ((𝔰₁).twistPieceQcoh Px.U Px.toSpace n)
      ((𝔰₁).twistTransition Px n) ((𝔰₁).presentationSchemeCocycle_twistTransition Px n)
      ((𝔰₁).presentationSchemeUnit_twistTransition Px n)
      ((𝔰₂).twistPieceQcoh Px.U Px.toSpace n)
      ((𝔰₂).twistTransition Px n) ((𝔰₂).presentationSchemeCocycle_twistTransition Px n)
      ((𝔰₂).presentationSchemeUnit_twistTransition Px n)
      (twistChartMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px.U Px.toSpace n) χ) :
    Epi χ := by
  unfold RelativeProjHomPoints.IsDescendedChartHom RelativeProjHomPoints.IsChartHom at hχ
  exact (@Presentation.IsAtlasMapComp.epi_iff _ _ _ _ _ _ _ _ _ _ _ _ _ hχ
    (Iso.isIso_hom _)).2
    (epi_equivalence_map_twistChartMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ hsurj Px.U Px.toSpace n)

end RelativeProjSituation

end AlgebraicGeometry.Space

end
