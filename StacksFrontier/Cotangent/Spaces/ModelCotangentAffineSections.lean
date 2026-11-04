module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleFibreProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDenseSubsite
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RepresentableQC.AffineEtaleLiftedCartesian
public import StacksFrontier.AlgebraicGeometry.Topologies.AffineSiteCartesianRingIso
public import StacksFrontier.Cotangent.SheavesOfRings.PresheafBaseCohomologyRestriction
public import StacksFrontier.Cotangent.Spaces.ModelCotangentAffineBase

/-!
# The cohomology presheaves of `U ↦ L_{𝒪(U)/Λ}` on the model are sheaves on affine charts

Let `f : X ⟶ T` be a morphism from an algebraic space to an object `T` of the big fppf site with
affine underlying scheme, `Λ = Γ(T, 𝒪_T)`. On the model of the small étale site of `X` the
presheaf base form of Tag 08SX (`AlgebraicGeometry.Sheaf.presheafBaseCohomologySheafIso`)
presents the cohomology sheaves of `L_{X/T}` as the sheafifications of the presheaves of modules
`W ↦ H^i(L_{𝒪(W)/Λ})` (`AlgebraicGeometry.Space.modelPresheafBaseHomology`). This file proves that
the sheafification does not change the sections of these presheaves over the objects of the
model lying over the affine étale charts of `X`
(`AlgebraicGeometry.Space.isIso_toSheafify_modelPresheafBaseHomology_app`): restricted to the
affine charts they are sheaves (`AlgebraicGeometry.Space.isSheaf_modelPresheafBaseHomology`).

The latter is faithfully flat descent: along a morphism of affine étale charts the base change
comparison `𝒪(V) ⊗_{𝒪(U)} H^i(L_{𝒪(U)/Λ}) ⟶ H^i(L_{𝒪(V)/Λ})` is an isomorphism, the ring map
being étale (`AlgebraicGeometry.Sheaf.isIso_presheafBaseHomologyRestrictionAdjoint`), so the
presheaf is cartesian, and a cartesian presheaf of modules on the affine étale site is a sheaf
(`Stacks.AffineSiteBaseChange.isSheaf_of_isIso_restrictionBaseChange_of_iso`, over the rings of
the model, which are those of the charts up to the comparison of the model with `X_et`).

## Main definitions

* `AlgebraicGeometry.Space.modelAffineChartFunctor`: the affine étale charts, as objects of the
  model.
* `AlgebraicGeometry.Space.modelPresheafBaseHomology`: the presheaf `W ↦ H^i(L_{𝒪(W)/Λ})`.

## Main results

* `CategoryTheory.Presheaf.isIso_toSheafify_app_of_isCocontinuous_of_isContinuous`
* `AlgebraicGeometry.Space.isIso_restrictionAdjoint_modelPresheafBaseHomology`
* `AlgebraicGeometry.Space.isSheaf_modelPresheafBaseHomology`
* `AlgebraicGeometry.Space.isIso_toSheafify_modelPresheafBaseHomology_app`

## References

* [Stacks Project, Tag 08SX](https://stacks.math.columbia.edu/tag/08SX)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Presheaf

universe w v'' v' v u'' u' u

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {A : Type u''} [Category.{v''} A] {FA : A → A → Type*} {CA : A → Type w}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA]

/-- **Sheafification does not change the sections over the image of a continuous and cocontinuous
functor** on whose source the restriction of the presheaf is already a sheaf. -/
theorem isIso_toSheafify_app_of_isCocontinuous_of_isContinuous (J' : GrothendieckTopology D)
    (J : GrothendieckTopology C) (I : D ⥤ C) [I.IsCocontinuous J' J] [I.IsContinuous J' J]
    [HasWeakSheafify J A] [J.WEqualsLocallyBijective A]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [J'.HasSheafCompose (CategoryTheory.forget A)]
    (P : Cᵒᵖ ⥤ A) (hP : Presheaf.IsSheaf J' (I.op ⋙ P)) (U : D) :
    IsIso ((toSheafify J P).app (op (I.obj U))) := by
  set q := toSheafify J P
  let _ : Presheaf.IsLocallyInjective J q := (J.W_toSheafify P).isLocallyInjective
  let _ : Presheaf.IsLocallySurjective J q := (J.W_toSheafify P).isLocallySurjective
  let q' : (⟨I.op ⋙ P, hP⟩ : Sheaf J' A) ⟶
      (I.sheafPushforwardContinuous A J' J).obj ((presheafToSheaf J A).obj P) :=
    ⟨I.op.whiskerLeft q⟩
  have _ : IsIso q' := (Sheaf.isLocallyBijective_iff_isIso q').mp
    ⟨Presheaf.isLocallyInjective_whisker J' J I q, Presheaf.isLocallySurjective_whisker J' J I q⟩
  have _ : IsIso q'.hom := inferInstanceAs (IsIso ((sheafToPresheaf J' A).map q'))
  exact inferInstanceAs (IsIso (q'.hom.app (op U)))

end CategoryTheory.Presheaf

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T : BigFppfOver B S hS}
  {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace T)

/-! ### The affine étale charts on the model -/

variable (X) in
/-- The affine étale charts of `X`, as objects of the model of its small étale site. -/
abbrev modelAffineChartFunctor : AffineEtale B S hS X.1 ⥤ (modelTopos X).C :=
  AffineEtale.inclusion B S hS X.1 ⋙ (smallEtaleModelEquiv B S hS X).functor

variable (X) in
/-- The rings of the model over the affine étale charts are the rings of global functions of the
charts, through the unit of the comparison of the model with `X_et`. -/
def modelAffineChartRingIso :
    Stacks.AffineSiteBaseChange.rings (AffineEtale.toScheme B S hS X.1) ≅
      (modelAffineChartFunctor X).op ⋙ (modelTopos X).O.obj :=
  Functor.isoWhiskerRight (NatIso.op (Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (AffineEtale.inclusion B S hS X.1)
      (smallEtaleModelEquiv B S hS X).unitIso)
    (SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS))).symm Scheme.Γ

/-- The restriction maps of the rings of the model along the affine étale charts are those of the
charts, read through `AlgebraicGeometry.Space.modelAffineChartRingIso`. -/
theorem modelAffineChart_map_eq {U V : AffineEtale B S hS X.1} (g : U ⟶ V) :
    ((modelAffineChartFunctor X).op ⋙ (modelTopos X).O.obj).map g.op =
      (modelAffineChartRingIso X).inv.app (op V) ≫
        (Stacks.AffineSiteBaseChange.rings (AffineEtale.toScheme B S hS X.1)).map g.op ≫
          (modelAffineChartRingIso X).hom.app (op U) := by
  rw [(modelAffineChartRingIso X).hom.naturality g.op, Iso.inv_hom_id_app_assoc]

/-- The ring map of a morphism of affine étale charts is étale. -/
theorem etale_appTop_affineEtale {U V : AffineEtale B S hS X.1} (g : U ⟶ V) :
    ((AffineEtale.toScheme B S hS X.1).map g).appTop.hom.Etale := by
  exact HasRingHomProperty.appTop (P := @Etale) _ (AffineEtale.etale_toScheme_map B S hS X.1 g)

/-- The restriction maps of the rings of the model along the affine étale charts are étale. -/
theorem etale_modelAffineChart_map {U V : AffineEtale B S hS X.1} (g : U ⟶ V) :
    (((modelAffineChartFunctor X).op ⋙ (modelTopos X).O.obj).map g.op).hom.Etale := by
  have hΓ : ((Stacks.AffineSiteBaseChange.rings (AffineEtale.toScheme B S hS X.1)).map
      g.op).hom.Etale := etale_appTop_affineEtale g
  have h1 := RingHom.Etale.respectsIso.1 _
    ((modelAffineChartRingIso X).app (op U)).commRingCatIsoToRingEquiv hΓ
  have h2 := RingHom.Etale.respectsIso.2 _
    ((modelAffineChartRingIso X).app (op V)).symm.commRingCatIsoToRingEquiv h1
  rw [modelAffineChart_map_eq]
  exact h2

/-! ### The presheaves `W ↦ H^i(L_{𝒪(W)/Λ})` -/

/-- The composite `f⁻¹Λ̲ ⟶ f⁻¹𝒪_T ⟶ 𝒪_X` of the tower on the model. -/
abbrev modelTowerMap : modelTowerBase f ⟶ (modelTopos X).O :=
  modelTowerLower f ≫ (modelRingedToposHom f).fSharpInverseImage

/-- The complex of presheaves of `𝒪_X`-modules `W ↦ L_{𝒪(W)/Λ}` on the model, `Λ = Γ(T, 𝒪_T)`,
whose sheafification is `L_{𝒪_X/f⁻¹Λ̲}` (Tag 08SX over the constant presheaf `Λ`). -/
abbrev modelPresheafBaseComplex :=
  CategoryTheory.Sheaf.presheafBaseCotangentModuleComplex.{u, u, u} (modelTopos X).J
    (modelTowerMap f) (modelConstantBaseMap f)

/-- **The presheaf `W ↦ H^i(L_{𝒪(W)/Λ})`** of `𝒪_X`-modules on the model. -/
abbrev modelPresheafBaseHomology (i : ℤ) :=
  (modelPresheafBaseComplex f).homology i

/-- **Along a morphism of affine étale charts, `W ↦ H^i(L_{𝒪(W)/Λ})` is a base change**: the ring
map is étale and the base `Λ` does not change. -/
theorem isIso_restrictionAdjoint_modelPresheafBaseHomology (i : ℤ)
    {U V : AffineEtale B S hS X.1} (g : U ⟶ V) :
    IsIso (PresheafOfModules.homologyRestrictionAdjoint (modelTopos X).O
      (modelPresheafBaseComplex f) i ((modelAffineChartFunctor X).map g).op) :=
  CategoryTheory.Sheaf.isIso_presheafBaseHomologyRestrictionAdjoint (modelTopos X).J
    (modelTowerMap f) (modelConstantBaseMap f) i _ (etale_modelAffineChart_map g)
    Function.bijective_id

/-- **`W ↦ H^i(L_{𝒪(W)/Λ})` is a sheaf on the affine étale charts**: it is cartesian there, and a
cartesian presheaf of modules on a flatly cofinal site of affine schemes is a sheaf. -/
theorem isSheaf_modelPresheafBaseHomology (i : ℤ) :
    Presheaf.IsSheaf (AffineEtale.topology B S hS X.1)
      ((modelAffineChartFunctor X).op ⋙ (modelPresheafBaseHomology f i).presheaf) :=
  Stacks.AffineSiteBaseChange.isSheaf_of_isIso_restrictionBaseChange_of_iso.{u}
    (AffineEtale.toScheme B S hS X.1) (AffineEtale.isFlatCofinal B S hS X.1)
    (modelAffineChartRingIso X)
    ((PresheafOfModules.pushforward₀ (modelAffineChartFunctor X) _).obj
      (modelPresheafBaseHomology f i))
    (fun {_ _} g => isIso_restrictionAdjoint_modelPresheafBaseHomology f i g.unop)

/-- The comparison of the affine étale charts with the model is cocontinuous. -/
instance isCocontinuous_modelAffineChartFunctor :
    (modelAffineChartFunctor X).IsCocontinuous (AffineEtale.topology B S hS X.1)
      (modelTopos X).J :=
  haveI := (AffineEtale.inclusion_isSpecialCocontinuous B S hS X.1 X.2).1
  CategoryTheory.isCocontinuous_comp (AffineEtale.inclusion B S hS X.1)
    (smallEtaleModelEquiv B S hS X).functor (AffineEtale.topology B S hS X.1)
    (SmallEtale.topology B S hS X.1)

/-- The comparison of the affine étale charts with the model is continuous. -/
instance isContinuous_modelAffineChartFunctor :
    (modelAffineChartFunctor X).IsContinuous (AffineEtale.topology B S hS X.1)
      (modelTopos X).J :=
  haveI := (AffineEtale.inclusion_isSpecialCocontinuous B S hS X.1 X.2).2
  Functor.isContinuous_comp _ _ _ (SmallEtale.topology B S hS X.1) _

/-- **Sheafification does not change `W ↦ H^i(L_{𝒪(W)/Λ})` over the affine étale charts.** -/
theorem isIso_toSheafify_modelPresheafBaseHomology_app (i : ℤ) (U : AffineEtale B S hS X.1) :
    IsIso ((toSheafify (modelTopos X).J (modelPresheafBaseHomology f i).presheaf).app
      (op ((modelAffineChartFunctor X).obj U))) := by
  have : (AffineEtale.topology B S hS X.1).HasSheafCompose
      (CategoryTheory.forget AddCommGrpCat.{u}) :=
    ⟨fun _ hP ↦ Presheaf.isSheaf_comp_of_isSheaf _ _ _ hP⟩
  exact Presheaf.isIso_toSheafify_app_of_isCocontinuous_of_isContinuous
    (AffineEtale.topology B S hS X.1) (modelTopos X).J (modelAffineChartFunctor X) _
    (isSheaf_modelPresheafBaseHomology f i) U

end AlgebraicGeometry.Space

end
