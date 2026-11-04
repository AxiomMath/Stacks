module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardDenseSubsiteFullyFaithful
public import StacksFrontier.CategoryTheory.Adjunction.UniversalArrowTransport
public import StacksFrontier.Deformation.ToposThickening.ExtensionProblemRebase
public import StacksFrontier.Deformation.ToposThickening.SolutionSiteTransport

/-!
# Universality of the prescribed map, under rebasing and site transport

The prescribed map `c : f⁻¹𝒥 ⟶ 𝒢` of a square-zero extension problem ([Stacks Project,
Tag 08UF]) is *universal* when every `f⁻¹𝒪_B`-linear map from `f⁻¹𝒥` to an `𝒪_X`-module factors
uniquely through it, that is when `𝒢 = 𝒪_X ⊗_{f⁻¹𝒪_B} f⁻¹𝒥` with `c` the unit. This holds for the
problem of a deformation, `c` being the unit of extension of scalars (Stacks 03CZ). This file
shows that universality survives moving the problem to another base along an identification of
the lower rows (`RingedToposExtensionProblem.rebase`) and transporting it to an equivalent site
(`RingedToposExtensionProblem.siteTransport`).

## Main definitions

* `Deformation.ToposThickening.RingedToposExtensionProblem.PrescribedMapUniversal`

## Main results

* `Deformation.ToposThickening.RingedToposExtensionProblem.prescribedMapUniversal_rebase`
* `Deformation.ToposThickening.RingedToposExtensionProblem.prescribedMapUniversal_siteTransport`

## References

* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

universe v u w v₁ u₁ w₁ v₂ u₂ w₂ v' u'

namespace Deformation.ToposThickening.RingedToposExtensionProblem

section Universal

variable {X : RingedTopos.{v, u, w}} {B : RingedTopos.{v₁, u₁, w₁}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [B.J.HasSheafCompose (forget RingCat.{w₁})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]

/-- **The prescribed map is universal**: every `f⁻¹𝒪_B`-linear map from the ideal `f⁻¹𝒥` to an
`𝒪_X`-module `M` factors uniquely as `c` followed by an `𝒪_X`-linear map `𝒢 ⟶ M`. -/
def PrescribedMapUniversal (S : RingedToposExtensionProblem X B) : Prop :=
  ∀ M : SheafOfModules.{w} ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O),
    Function.Bijective fun k : S.G ⟶ M =>
      S.c ≫ (SheafOfModules.restrictScalars ((sheafCompose X.J
        (forget₂ CommRingCat.{w} RingCat.{w})).map S.f.fSharpInverseImage)).map k

end Universal

/-! ### Rebasing -/

section Rebase

variable {X : RingedTopos.{v, u, w}} {B₁ : RingedTopos.{v₁, u₁, w₁}}
  {B₂ : RingedTopos.{v₂, u₂, w₂}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [B₁.J.HasSheafCompose (forget RingCat.{w₁})]
  [B₂.J.HasSheafCompose (forget RingCat.{w₂})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B₁.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [B₂.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]
  (S : RingedToposExtensionProblem X B₁) (f : RingedToposHom X B₂)
  {E : Sheaf B₂.J CommRingCat.{w₂}} (r : E ⟶ B₂.O)
  (θ : (inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension ≅
    (inverseImageCommRingFunctor f.toToposHom).obj E)
  (μ : (inverseImageCommRingFunctor S.f.toToposHom).obj B₁.O ≅
    (inverseImageCommRingFunctor f.toToposHom).obj B₂.O)
  (hθ : θ.hom ≫ (inverseImageCommRingFunctor f.toToposHom).map r =
    (inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction ≫ μ.hom)
  (hμ : μ.hom ≫ f.fSharpInverseImage = S.f.fSharpInverseImage)
  {G : SheafOfModules.{w} ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O)}
  (β : S.G ≅ G)
  (hr : Presheaf.IsLocallySurjective B₂.J r.hom)
  (hsq : ∀ U : B₂.Cᵒᵖ, (RingHom.ker (r.hom.app U).hom) ^ 2 = ⊥)

include hμ in
/-- A map out of the ideal of the rebased problem, read as a map out of the ideal of `S`: the same
map on sections. -/
def rebaseIdealHomOfHom
    {M : SheafOfModules.{w} ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O)}
    (d : S.rebaseIdeal f μ ⟶ (SheafOfModules.restrictScalars ((sheafCompose X.J
      (forget₂ CommRingCat.{w} RingCat.{w})).map f.fSharpInverseImage)).obj M) :
    S.I ⟶ (SheafOfModules.restrictScalars ((sheafCompose X.J
      (forget₂ CommRingCat.{w} RingCat.{w})).map S.f.fSharpInverseImage)).obj M where
  val :=
    { app := fun U => ModuleCat.ofHom
        (X := S.I.val.obj U)
        (Y := ((SheafOfModules.restrictScalars ((sheafCompose X.J
          (forget₂ CommRingCat.{w} RingCat.{w})).map S.f.fSharpInverseImage)).obj M).val.obj U)
        { toFun := fun a => d.val.app U a
          map_add' := fun a b => map_add (ConcreteCategory.hom (d.val.app U)) a b
          map_smul' := fun s a => by
            have hs : μ.inv.hom.app U (μ.hom.hom.app U s) = s :=
              congrArg (fun k => k.hom.app U s) μ.hom_inv_id
            have hf : f.fSharpInverseImage.hom.app U (μ.hom.hom.app U s) =
                S.f.fSharpInverseImage.hom.app U s :=
              congrArg (fun k => k.hom.app U s) hμ
            have h := (ConcreteCategory.hom (d.val.app U)).map_smul (μ.hom.hom.app U s) a
            change d.val.app U ((show ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
                ((inverseImageCommRingFunctor S.f.toToposHom).obj B₁.O)).obj.obj U from
                  μ.inv.hom.app U (μ.hom.hom.app U s)) • (show S.I.val.obj U from a)) =
              (show ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O).obj.obj U
                from f.fSharpInverseImage.hom.app U (μ.hom.hom.app U s)) •
                (show M.val.obj U from d.val.app U a) at h
            rw [hs, hf] at h
            exact h }
      naturality := fun {U V} g => by
        ext a
        exact PresheafOfModules.naturality_apply d.val g a }

/-- **Rebasing preserves universality of the prescribed map.** -/
theorem prescribedMapUniversal_rebase (hS : S.PrescribedMapUniversal) :
    (S.rebase f r θ μ hθ hμ β hr hsq).PrescribedMapUniversal := by
  intro M
  refine ⟨fun k₁ k₂ hk => ?_, fun d => ?_⟩
  · exact (cancel_epi β.hom).1 ((hS M).1 (a₁ := β.hom ≫ k₁) (a₂ := β.hom ≫ k₂)
      (SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
        ModuleCat.hom_ext (LinearMap.ext fun a => congrArg (fun t => t.val.app U a) hk))))
  · obtain ⟨k₀, hk₀⟩ := (hS M).2 (S.rebaseIdealHomOfHom f μ hμ d)
    refine ⟨β.inv ≫ k₀, SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
      ModuleCat.hom_ext (LinearMap.ext fun a => ?_))⟩
    have h := congrArg (fun t => t.val.app U a) hk₀
    refine Eq.trans ?_ h
    exact congrArg (fun y => k₀.val.app U y)
      (congrArg (fun t : S.G ⟶ S.G => t.val.app U (S.c.val.app U a)) β.hom_inv_id)

end Rebase

/-! ### Site transport -/

section SiteTransport

variable {X : RingedTopos.{w₁, v₁, u}} {B : RingedTopos.{v', u', u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [B.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {D : Type v₂} [Category.{w₂} D] (K : GrothendieckTopology D) (e : X.C ≌ D)
  [e.inverse.IsDenseSubsite K X.J]
  [K.HasSheafCompose (forget RingCat.{u})] [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(e.inverse.sheafPushforwardContinuous AddCommGrpCat.{u} K X.J).IsEquivalence]
  (S : RingedToposExtensionProblem X B)

/-- `f'⁻¹𝒪_B ≅ G^s(f⁻¹𝒪_B)`, as sheaves of rings. -/
def siteTransportIdealRingIso :
    (sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((inverseImageCommRingFunctor (siteTransportHom K e S.f).toToposHom).obj B.O) ≅
      (e.inverse.sheafPushforwardContinuous RingCat.{u} K X.J).obj
        ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj
          ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O)) :=
  (sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).mapIso
    ((siteTransportInverseImageIso K e S.f.toToposHom).app B.O) ≪≫ Iso.refl _

omit [(e.inverse.sheafPushforwardContinuous AddCommGrpCat.{u} K X.J).IsEquivalence] in
/-- The forward map of `siteTransportIdealRingIso` is the image under `sheafCompose` of the
inverse-image comparison `siteTransportInverseImageIso` at `𝒪_B`. -/
theorem siteTransportIdealRingIso_hom :
    (siteTransportIdealRingIso K e S).hom =
      (sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).map
        ((siteTransportInverseImageIso K e S.f.toToposHom).hom.app B.O) :=
  Category.comp_id _

omit [(e.inverse.sheafPushforwardContinuous AddCommGrpCat.{u} K X.J).IsEquivalence] in
/-- The structure map of the transported morphism, read through `f'⁻¹𝒪_B ≅ G^s(f⁻¹𝒪_B)`, is the
restriction of that of `f`, as maps of sheaves of rings. -/
theorem siteTransport_fSharp_square :
    (sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).map
        (siteTransportHom K e S.f).fSharpInverseImage ≫
        𝟙 ((e.inverse.sheafPushforwardContinuous RingCat.{u} K X.J).obj
          ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj X.O)) =
      (siteTransportIdealRingIso K e S).hom ≫
        (e.inverse.sheafPushforwardContinuous RingCat.{u} K X.J).map
          ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).map
            S.f.fSharpInverseImage) := by
  rw [siteTransportIdealRingIso_hom]
  exact (Category.comp_id _).trans ((congrArg (sheafCompose K
    (forget₂ CommRingCat.{u} RingCat.{u})).map (siteTransportHom_fSharpInverseImage K e S.f)).trans
      (Functor.map_comp _ _ _))

/-- Restriction to the equivalent site commutes with restriction of scalars along the structure
maps. -/
def siteTransportResSquare :=
  SheafOfModules.pushforwardRestrictScalarsIso (F := e.inverse)
    ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).map S.f.fSharpInverseImage)
    ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).map
      (siteTransportHom K e S.f).fSharpInverseImage)
    (𝟙 ((e.inverse.sheafPushforwardContinuous RingCat.{u} K X.J).obj
      ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj X.O)))
    (siteTransportIdealRingIso K e S).hom (siteTransport_fSharp_square K e S)

/-- **Site transport preserves universality of the prescribed map.** -/
theorem prescribedMapUniversal_siteTransport (hS : S.PrescribedMapUniversal) :
    (S.siteTransport K e).PrescribedMapUniversal := by
  intro M
  have : (Deformation.AlgebraExtension.moduleRes K e.inverse X.O).Full :=
    SheafOfModules.full_pushforward_of_iso _ (Iso.refl _)
  have : (Deformation.AlgebraExtension.moduleRes K e.inverse X.O).Faithful :=
    SheafOfModules.faithful_pushforward_of_iso _ (Iso.refl _)
  have : (Deformation.AlgebraExtension.moduleRes K e.inverse X.O).EssSurj :=
    SheafOfModules.essSurj_pushforward_of_iso _ (Iso.refl _)
  have : (SheafOfModules.pushforward.{u} (F := e.inverse)
      (siteTransportIdealRingIso K e S).hom).Full :=
    SheafOfModules.full_pushforward_of_iso _ (siteTransportIdealRingIso K e S)
  have : (SheafOfModules.pushforward.{u} (F := e.inverse)
      (siteTransportIdealRingIso K e S).hom).Faithful :=
    SheafOfModules.faithful_pushforward_of_iso _ (siteTransportIdealRingIso K e S)
  have h := bijective_comp_map_of_transport_of_fullyFaithful
    (Φ := Deformation.AlgebraExtension.moduleRes K e.inverse X.O) (siteTransportResSquare K e S)
    (Functor.FullyFaithful.ofFullyFaithful _) S.c hS (Iso.refl _) M
  refine (congrArg Function.Bijective (funext fun k => ?_)).mp h
  exact SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun a => rfl))

end SiteTransport

end Deformation.ToposThickening.RingedToposExtensionProblem

end
