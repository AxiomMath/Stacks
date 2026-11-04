module

public import StacksFrontier.Deformation.ToposThickening.ExtensionProblemRebase
public import StacksFrontier.Deformation.ToposThickening.SolutionSiteTransport
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatSpacesChartDeformation

/-!
# The inclusion and the prescribed map of rebased and transported problems, on sections

The extension problems `Deformation.ToposThickening.RingedToposExtensionProblem.rebase` (moved to
another base along identifications of the lower rows) and
`Deformation.ToposThickening.RingedToposExtensionProblem.siteTransport` (moved to an equivalent
site) have, on sections, the inclusion of the ideal and the prescribed map of the original
problem followed by the identifications.

## References

* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

universe v u w v₁ u₁ w₁ v₂ u₂ w₂ v' u'

namespace Deformation.ToposThickening

namespace RingedToposExtensionProblem

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

variable (hr : Presheaf.IsLocallySurjective B₂.J r.hom)
  (hsq : ∀ U : B₂.Cᵒᵖ, (RingHom.ker (r.hom.app U).hom) ^ 2 = ⊥)

/-- The prescribed map of the rebased problem, on sections. -/
theorem rebase_c_val_app (U : X.Cᵒᵖ) (x : (S.rebase f r θ μ hθ hμ β hr hsq).I.val.obj U) :
    (S.rebase f r θ μ hθ hμ β hr hsq).c.val.app U x = β.hom.val.app U (S.c.val.app U x) :=
  rfl

/-- The inclusion of the ideal of the rebased problem, on sections. -/
theorem rebase_idealInclusion_val_app (U : X.Cᵒᵖ)
    (x : (S.rebase f r θ μ hθ hμ β hr hsq).I.val.obj U) :
    (show ((inverseImageCommRingFunctor f.toToposHom).obj E).obj.obj U from
      (S.rebase f r θ μ hθ hμ β hr hsq).idealInclusion.val.app U x) =
      θ.hom.hom.app U (S.idealInclusion.val.app U x) :=
  rfl

end Rebase

end RingedToposExtensionProblem

section SiteTransport

variable {X : RingedTopos.{w₁, v₁, u}} {B₁ B₂ : RingedTopos.{v', u', u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [B₁.J.HasSheafCompose (forget RingCat.{u})]
  [B₂.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B₁.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B₂.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {D : Type v₂} [Category.{w₂} D] (K : GrothendieckTopology D) (e : X.C ≌ D)
  [e.inverse.IsDenseSubsite K X.J]
  [K.HasSheafCompose (forget RingCat.{u})] [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]


/-- The prescribed map of the transported problem, on sections. -/
theorem RingedToposExtensionProblem.siteTransport_c_val_app (S : RingedToposExtensionProblem X B₁)
    (V : Dᵒᵖ) (x : (S.siteTransport K e).I.val.obj V) :
    (S.siteTransport K e).c.val.app V x = S.c.val.app (e.inverse.op.obj V) x :=
  rfl

/-- The inclusion of the ideal of the transported problem, on sections. -/
theorem RingedToposExtensionProblem.siteTransport_idealInclusion_val_app
    (S : RingedToposExtensionProblem X B₁) (V : Dᵒᵖ) (x : (S.siteTransport K e).I.val.obj V) :
    (show ((inverseImageCommRingFunctor (S.siteTransport K e).f.toToposHom).obj
        S.baseExtension).obj.obj V from (S.siteTransport K e).idealInclusion.val.app V x) =
      ((RingedToposExtensionProblem.siteTransportInverseImageIso K e S.f.toToposHom).app
        S.baseExtension).inv.hom.app V (S.idealInclusion.val.app (e.inverse.op.obj V) x) :=
  rfl

/-- The transported identification of inverse images, on sections. -/
theorem siteTransportInverseImageRingIso_hom_hom_app (f₁ : RingedToposHom X B₁)
    (f₂ : RingedToposHom X B₂) {F₁ : Sheaf B₁.J CommRingCat.{u}} {F₂ : Sheaf B₂.J CommRingCat.{u}}
    (a : (inverseImageCommRingFunctor f₁.toToposHom).obj F₁ ≅
      (inverseImageCommRingFunctor f₂.toToposHom).obj F₂) (V : Dᵒᵖ)
    (y : ((inverseImageCommRingFunctor
      (RingedToposExtensionProblem.siteTransportHom K e f₁).toToposHom).obj F₁).obj.obj V) :
    (siteTransportInverseImageRingIso K e f₁ f₂ a).hom.hom.app V y =
      ((RingedToposExtensionProblem.siteTransportInverseImageIso K e f₂.toToposHom).app
          F₂).inv.hom.app V
        (a.hom.hom.app (e.inverse.op.obj V)
          (((RingedToposExtensionProblem.siteTransportInverseImageIso K e
            f₁.toToposHom).app F₁).hom.hom.app V y)) :=
  rfl

end SiteTransport

end Deformation.ToposThickening
