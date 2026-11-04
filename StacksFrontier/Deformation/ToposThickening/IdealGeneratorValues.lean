module

public import StacksFrontier.Deformation.ToposThickening.RebaseSiteTransportGenerators

/-!
# Global sections of the ideal of an extension problem, read in the thickened base

The ideal `f⁻¹𝒥` of a square-zero extension problem `S` comes with an inclusion into
`f⁻¹𝒪_{B'}`, injective on sections (`idealUniversal`). A global section `σ : 𝒪 ⟶ f⁻¹𝒥` is
therefore determined by the sections `ι(σ(1))` of the sheaf of rings `f⁻¹𝒪_{B'}`
(`Deformation.ToposThickening.RingedToposExtensionProblem.idealGeneratorValue`). This file records
that, and how these values change when the problem is moved to another base
(`Deformation.ToposThickening.RingedToposExtensionProblem.rebase`) or to an equivalent site
(`Deformation.ToposThickening.RingedToposExtensionProblem.siteTransport`).

Only sections of sheaves of rings are compared here, never sections of modules over two
different sheaves of rings.

## References

* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

universe v u w v₁ u₁ w₁ v₂ u₂ w₂ v' u'

namespace Deformation.ToposThickening.RingedToposExtensionProblem

section Values

variable {X : RingedTopos.{v, u, w}} {B : RingedTopos.{v₁, u₁, w₁}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [B.J.HasSheafCompose (forget RingCat.{w₁})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  (P : RingedToposExtensionProblem X B)

/-- **The value of a global section of the ideal in the thickened base**: the image of `σ(1)`
under the inclusion `f⁻¹𝒥 ⟶ f⁻¹𝒪_{B'}`, over `U`. -/
def idealGeneratorValue
    (σ : SheafOfModules.unit ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
      ((inverseImageCommRingFunctor P.f.toToposHom).obj B.O)) ⟶ P.I) (U : X.Cᵒᵖ) :
    ((inverseImageCommRingFunctor P.f.toToposHom).obj P.baseExtension).obj.obj U :=
  P.idealInclusion.val.app U (σ.val.app U (1 : ((sheafCompose X.J
    (forget₂ CommRingCat.{w} RingCat.{w})).obj
      ((inverseImageCommRingFunctor P.f.toToposHom).obj B.O)).obj.obj U))

/-- **A global section of the ideal is determined by its values in the thickened base.** -/
theorem eq_of_idealGeneratorValue
    {σ σ' : SheafOfModules.unit ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
      ((inverseImageCommRingFunctor P.f.toToposHom).obj B.O)) ⟶ P.I}
    (h : ∀ U : X.Cᵒᵖ, P.idealGeneratorValue σ U = P.idealGeneratorValue σ' U) : σ = σ' :=
  unit_hom_ext fun U => by
    obtain ⟨m, _, hu⟩ := P.idealUniversal U (P.idealGeneratorValue σ' U)
      (P.idealZero U _)
    exact (hu _ (h U)).trans (hu _ rfl).symm

end Values

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

/-- **The values of a global section of the ideal of the rebase** are those of `S`, read
through `θ`. -/
theorem idealGeneratorValue_rebaseIdealGenerator
    (σ : SheafOfModules.unit ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
      ((inverseImageCommRingFunctor S.f.toToposHom).obj B₁.O)) ⟶ S.I) (U : X.Cᵒᵖ) :
    (S.rebase f r θ μ hθ hμ β hr hsq).idealGeneratorValue
        (S.rebaseIdealGenerator f r θ μ hθ hμ β hr hsq σ) U =
      θ.hom.hom.app U (S.idealGeneratorValue σ U) :=
  congrArg (fun a => θ.hom.hom.app U (S.idealInclusion.val.app U a))
    (S.rebaseIdealGenerator_val_app_one f r θ μ hθ hμ β hr hsq σ U)

end Rebase

section SiteTransport

variable {X : RingedTopos.{w₁, v₁, u}} {B₁ : RingedTopos.{v', u', u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [B₁.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B₁.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {D : Type v₂} [Category.{w₂} D] (K : GrothendieckTopology D) (e : X.C ≌ D)
  [e.inverse.IsDenseSubsite K X.J]
  [K.HasSheafCompose (forget RingCat.{u})] [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (S : RingedToposExtensionProblem X B₁)

/-- **The values of a global section of the ideal of the transported problem** are those of `S`
over the corresponding objects, read through the identification of inverse images. -/
theorem idealGeneratorValue_siteTransportIdealGenerator
    (σ : SheafOfModules.unit ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj
      ((inverseImageCommRingFunctor S.f.toToposHom).obj B₁.O)) ⟶ S.I) (V : Dᵒᵖ) :
    (S.siteTransport K e).idealGeneratorValue (S.siteTransportIdealGenerator K e σ) V =
      ((siteTransportInverseImageIso K e S.f.toToposHom).app S.baseExtension).inv.hom.app V
        (S.idealGeneratorValue σ (e.inverse.op.obj V)) :=
  congrArg (fun a => ((siteTransportInverseImageIso K e S.f.toToposHom).app
      S.baseExtension).inv.hom.app V (S.idealInclusion.val.app (e.inverse.op.obj V) a))
    (S.siteTransportIdealGenerator_val_app_one K e σ V)

end SiteTransport

end Deformation.ToposThickening.RingedToposExtensionProblem
