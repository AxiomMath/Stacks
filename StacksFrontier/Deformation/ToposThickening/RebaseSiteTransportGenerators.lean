module

public import StacksFrontier.Deformation.ToposThickening.RebaseSiteTransportSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseChangeUnitor

/-!
# Global sections of the ideal of a rebased or transported problem, and the prescribed map

A global section of the ideal of a square-zero extension problem `S` is a morphism
`σ : 𝒪 ⟶ f⁻¹𝒥` out of the free module of rank one. Suppose that the prescribed map carries it to
the restriction of a global section `τ : 𝒪_X ⟶ 𝒢` of the prescribed module, in the sense that
`σ ≫ c = u ≫ τ`, where `u : f⁻¹𝒪_B ⟶ 𝒪_X` is read on the free modules of rank one
(`Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit`).

This file shows that the same then holds for the problem moved to another base
(`Deformation.ToposThickening.RingedToposExtensionProblem.rebase`), with `τ` followed by the
identification of prescribed modules, and for the problem moved to an equivalent site
(`Deformation.ToposThickening.RingedToposExtensionProblem.siteTransport`), with both sections
restricted along the equivalence. The statements are equations of morphisms, so that a concrete
instance never compares sections of modules over different sheaves of rings.

## Main results

* `Deformation.ToposThickening.RingedToposExtensionProblem.rebaseIdealGenerator_comp_rebase_c`
* `Deformation.ToposThickening.RingedToposExtensionProblem.siteTransportIdealGenerator_comp_c`

## References

* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)
open Stacks.SheafOfModules.ChangeOfRings (unitToRestrictScalarsUnit
  unitToRestrictScalarsUnit_val_app_one)

universe v u w v₁ u₁ w₁ v₂ u₂ w₂ v' u'

namespace Deformation.ToposThickening

/-! ### Morphisms out of the free module of rank one -/

section Unit

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- Two morphisms out of the free module of rank one agree when they agree on `1` over every
object. -/
theorem unit_hom_ext {M : SheafOfModules.{w} R} {a b : SheafOfModules.unit R ⟶ M}
    (h : ∀ U : Cᵒᵖ, a.val.app U (1 : R.obj.obj U) = b.val.app U (1 : R.obj.obj U)) : a = b :=
  (SheafOfModules.unitHomEquiv M).injective (PresheafOfModules.sections_ext _ _ h)

/-- The morphism out of the free module of rank one attached to a global section takes the value
of the section on `1`. -/
theorem unitHomEquiv_symm_val_app_one {M : SheafOfModules.{w} R} (s : M.sections) (U : Cᵒᵖ) :
    ((SheafOfModules.unitHomEquiv M).symm s).val.app U (1 : R.obj.obj U) = s.val U :=
  congrArg (fun t : M.sections => t.val U) ((SheafOfModules.unitHomEquiv M).apply_symm_apply s)

/-- A morphism out of the free module of rank one is the restriction of scalars of a global
section `τ` (followed by `c`) exactly when `c` carries it to `τ` on `1` over every object. -/
private theorem comp_eq_unitToRestrictScalarsUnit_comp_iff {R' : Sheaf J RingCat.{w}} (α : R ⟶ R')
    {M : SheafOfModules.{w} R} {G : SheafOfModules.{w} R'} (a : SheafOfModules.unit R ⟶ M)
    (c : M ⟶ (SheafOfModules.restrictScalars.{w} α).obj G) (τ : SheafOfModules.unit R' ⟶ G) :
    a ≫ c = unitToRestrictScalarsUnit α ≫ (SheafOfModules.restrictScalars.{w} α).map τ ↔
      ∀ U : Cᵒᵖ, c.val.app U (a.val.app U (1 : R.obj.obj U)) = τ.val.app U (1 : R'.obj.obj U) := by
  have key (U : Cᵒᵖ) : ((a ≫ c).val.app U (1 : R.obj.obj U) =
      ((unitToRestrictScalarsUnit α ≫ (SheafOfModules.restrictScalars.{w} α).map τ).val.app U
        (1 : R.obj.obj U))) ↔ c.val.app U (a.val.app U (1 : R.obj.obj U)) =
          τ.val.app U (1 : R'.obj.obj U) := by
    change c.val.app U (a.val.app U (1 : R.obj.obj U)) =
      τ.val.app U ((unitToRestrictScalarsUnit α).val.app U (1 : R.obj.obj U)) ↔ _
    rw [unitToRestrictScalarsUnit_val_app_one]
  exact ⟨fun h U => (key U).1 (congrArg (fun m => m.val.app U (1 : R.obj.obj U)) h),
    fun h => unit_hom_ext fun U => (key U).2 (h U)⟩

end Unit

/-! ### Moving to another base -/

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
  (hr : Presheaf.IsLocallySurjective B₂.J r.hom)
  (hsq : ∀ U : B₂.Cᵒᵖ, (RingHom.ker (r.hom.app U).hom) ^ 2 = ⊥)

/-- **A global section of the ideal of `S`, as one of the ideal of its rebase**: the ideal of the
rebase is that of `S`, read over `f₂⁻¹𝒪_{B₂}` through `μ`. -/
def rebaseIdealGenerator
    (σ : SheafOfModules.unit ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
      ((inverseImageCommRingFunctor S.f.toToposHom).obj B₁.O)) ⟶ S.I) :
    SheafOfModules.unit ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
        ((inverseImageCommRingFunctor f.toToposHom).obj B₂.O)) ⟶
      (S.rebase f r θ μ hθ hμ β hr hsq).I :=
  unitToRestrictScalarsUnit ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map μ.inv) ≫
    (SheafOfModules.restrictScalars
      ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map μ.inv)).map σ

/-- `RingedToposExtensionProblem.rebaseIdealGenerator` on `1`. -/
theorem rebaseIdealGenerator_val_app_one
    (σ : SheafOfModules.unit ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
      ((inverseImageCommRingFunctor S.f.toToposHom).obj B₁.O)) ⟶ S.I) (U : X.Cᵒᵖ) :
    (S.rebaseIdealGenerator f r θ μ hθ hμ β hr hsq σ).val.app U (1 : ((sheafCompose X.J
        (forget₂ CommRingCat.{w} RingCat.{w})).obj
        ((inverseImageCommRingFunctor f.toToposHom).obj B₂.O)).obj.obj U) =
      σ.val.app U (1 : ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
          ((inverseImageCommRingFunctor S.f.toToposHom).obj B₁.O)).obj.obj U) :=
  congrArg (σ.val.app U) (unitToRestrictScalarsUnit_val_app_one
    ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map μ.inv) U)

/-- **The prescribed map of the rebase on a global section of the ideal.** If the prescribed map
of `S` carries `σ` to the global section `τ` of `𝒢`, then that of the rebase carries `σ` to
`β ∘ τ`. -/
theorem rebaseIdealGenerator_comp_rebase_c
    (σ : SheafOfModules.unit ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
      ((inverseImageCommRingFunctor S.f.toToposHom).obj B₁.O)) ⟶ S.I)
    (τ : SheafOfModules.unit ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O) ⟶
      S.G)
    (hσ : σ ≫ S.c = unitToRestrictScalarsUnit
        ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map S.f.fSharpInverseImage) ≫
      (SheafOfModules.restrictScalars ((sheafCompose X.J
        (forget₂ CommRingCat.{w} RingCat.{w})).map S.f.fSharpInverseImage)).map τ) :
    S.rebaseIdealGenerator f r θ μ hθ hμ β hr hsq σ ≫ (S.rebase f r θ μ hθ hμ β hr hsq).c =
      unitToRestrictScalarsUnit
          ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map f.fSharpInverseImage) ≫
        (SheafOfModules.restrictScalars ((sheafCompose X.J
          (forget₂ CommRingCat.{w} RingCat.{w})).map f.fSharpInverseImage)).map (τ ≫ β.hom) := by
  refine (comp_eq_unitToRestrictScalarsUnit_comp_iff _ _ _ _).2 fun U => ?_
  have h := (comp_eq_unitToRestrictScalarsUnit_comp_iff _ _ _ _).1 hσ U
  exact (congrArg (fun x => β.hom.val.app U (S.c.val.app U x))
    (rebaseIdealGenerator_val_app_one S f r θ μ hθ hμ β hr hsq σ U)).trans
      (congrArg (β.hom.val.app U) h)

end Rebase

end RingedToposExtensionProblem

/-! ### Moving to an equivalent site -/

section SiteTransport

variable {X : RingedTopos.{w₁, v₁, u}} {B₁ : RingedTopos.{v', u', u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [B₁.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B₁.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {D : Type v₂} [Category.{w₂} D] (K : GrothendieckTopology D) (e : X.C ≌ D)
  [e.inverse.IsDenseSubsite K X.J]
  [K.HasSheafCompose (forget RingCat.{u})] [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- **A global section restricted along the equivalence**: the restriction along `e.inverse` of a
morphism out of the free module of rank one. -/
def moduleResUnitHom {T : Sheaf X.J CommRingCat.{u}}
    {M : SheafOfModules.{u} ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj T)}
    (τ : SheafOfModules.unit ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj T) ⟶
      M) :
    SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((Deformation.AlgebraExtension.ringRes K e.inverse).obj T)) ⟶
      (Deformation.AlgebraExtension.moduleRes K e.inverse T).obj M :=
  (SheafOfModules.unitHomEquiv _).symm
    (PresheafOfModules.sectionsMk (fun V => τ.val.app (e.inverse.op.obj V) (1 : ((sheafCompose X.J
        (forget₂ CommRingCat.{u} RingCat.{u})).obj T).obj.obj (e.inverse.op.obj V)))
      (fun _ _ g => (PresheafOfModules.naturality_apply τ.val (e.inverse.op.map g) (1 :
          ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj T).obj.obj
          (e.inverse.op.obj _))).symm.trans
        (congrArg (τ.val.app _) ((((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj
          T).obj.map (e.inverse.op.map g)).hom.map_one))))

omit [X.J.HasSheafCompose (forget RingCat.{u})] [K.HasSheafCompose (forget RingCat.{u})] in
/-- `moduleResUnitHom` on `1`. -/
theorem moduleResUnitHom_val_app_one {T : Sheaf X.J CommRingCat.{u}}
    {M : SheafOfModules.{u} ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj T)}
    (τ : SheafOfModules.unit ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj T) ⟶
      M) (V : Dᵒᵖ) :
    (moduleResUnitHom K e τ).val.app V (1 : ((sheafCompose K
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((Deformation.AlgebraExtension.ringRes K e.inverse).obj T)).obj.obj V) =
      τ.val.app (e.inverse.op.obj V) (1 : ((sheafCompose X.J
          (forget₂ CommRingCat.{u} RingCat.{u})).obj T).obj.obj (e.inverse.op.obj V)) :=
  unitHomEquiv_symm_val_app_one _ V

omit [X.J.HasSheafCompose (forget RingCat.{u})] [K.HasSheafCompose (forget RingCat.{u})] in
/-- `moduleResUnitHom` is compatible with composition by a morphism of modules. -/
theorem moduleResUnitHom_comp_map {T : Sheaf X.J CommRingCat.{u}}
    {M N : SheafOfModules.{u} ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj T)}
    (τ : SheafOfModules.unit ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj T) ⟶
      M) (b : M ⟶ N) :
    moduleResUnitHom K e τ ≫ (Deformation.AlgebraExtension.moduleRes K e.inverse T).map b =
      moduleResUnitHom K e (τ ≫ b) :=
  unit_hom_ext fun V => (congrArg (b.val.app (e.inverse.op.obj V))
    (moduleResUnitHom_val_app_one K e τ V)).trans (moduleResUnitHom_val_app_one K e (τ ≫ b) V).symm

omit [X.J.HasSheafCompose (forget RingCat.{u})] [K.HasSheafCompose (forget RingCat.{u})] in
/-- `moduleResUnitHom` is compatible with composition by an isomorphism of modules. -/
theorem moduleResUnitHom_comp_mapIso_hom {T : Sheaf X.J CommRingCat.{u}}
    {M N : SheafOfModules.{u} ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj T)}
    (τ : SheafOfModules.unit ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj T) ⟶
      M) (b : M ≅ N) :
    moduleResUnitHom K e τ ≫ ((Deformation.AlgebraExtension.moduleRes K e.inverse T).mapIso b).hom =
      moduleResUnitHom K e (τ ≫ b.hom) :=
  moduleResUnitHom_comp_map K e τ b.hom

omit [X.J.HasSheafCompose (forget RingCat.{u})] [K.HasSheafCompose (forget RingCat.{u})] in
/-- **A restricted global section through `G^s(b) ≪≫ c`**: if `τ ≫ b = σ` and the restriction of
`σ` followed by `c` is `d`, then the restriction of `τ` followed by `G^s(b) ≪≫ c` is `d`. -/
theorem moduleResUnitHom_comp_mapIso_trans_hom {T : Sheaf X.J CommRingCat.{u}}
    {M N : SheafOfModules.{u} ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj T)}
    {P : SheafOfModules.{u} ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj
      ((Deformation.AlgebraExtension.ringRes K e.inverse).obj T))}
    (τ : SheafOfModules.unit ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj T) ⟶
      M) (b : M ≅ N) (c : (Deformation.AlgebraExtension.moduleRes K e.inverse T).obj N ≅ P)
    {σ : SheafOfModules.unit ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj T) ⟶
      N}
    {d : SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj
      ((Deformation.AlgebraExtension.ringRes K e.inverse).obj T)) ⟶ P}
    (hσ : τ ≫ b.hom = σ) (hd : moduleResUnitHom K e σ ≫ c.hom = d) :
    moduleResUnitHom K e τ ≫
        ((Deformation.AlgebraExtension.moduleRes K e.inverse T).mapIso b ≪≫ c).hom = d := by
  subst hσ hd
  rw [Iso.trans_hom, ← Category.assoc, moduleResUnitHom_comp_mapIso_hom]

omit [X.J.HasSheafCompose (forget RingCat.{u})] [K.HasSheafCompose (forget RingCat.{u})] in
/-- `moduleResUnitHom` is compatible with a cast along an equality of modules. -/
theorem moduleResUnitHom_comp_eqToHom {T : Sheaf X.J CommRingCat.{u}}
    {M N : SheafOfModules.{u} ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj T)}
    (τ : SheafOfModules.unit ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj T) ⟶
      M) (h : M = N) :
    moduleResUnitHom K e τ ≫ eqToHom (congrArg
      (Deformation.AlgebraExtension.moduleRes K e.inverse T).obj h) =
      moduleResUnitHom K e (τ ≫ eqToHom h) := by
  subst h
  simp only [eqToHom_refl, Category.comp_id]

namespace RingedToposExtensionProblem

variable (S : RingedToposExtensionProblem X B₁)

/-- **A global section of the ideal of `S`, restricted to the equivalent site**: a global section
of the ideal of `S.siteTransport K e`. -/
def siteTransportIdealGenerator
    (σ : SheafOfModules.unit ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj
      ((inverseImageCommRingFunctor S.f.toToposHom).obj B₁.O)) ⟶ S.I) :
    SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((inverseImageCommRingFunctor (S.siteTransport K e).f.toToposHom).obj B₁.O)) ⟶
      (S.siteTransport K e).I :=
  (SheafOfModules.unitHomEquiv _).symm
    (PresheafOfModules.sectionsMk (fun V => σ.val.app (e.inverse.op.obj V) (1 : ((sheafCompose X.J
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((inverseImageCommRingFunctor S.f.toToposHom).obj B₁.O)).obj.obj (e.inverse.op.obj V)))
      (fun _ _ g => (PresheafOfModules.naturality_apply σ.val (e.inverse.op.map g) (1 :
          ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj
          ((inverseImageCommRingFunctor S.f.toToposHom).obj B₁.O)).obj.obj
          (e.inverse.op.obj _))).symm.trans
        (congrArg (σ.val.app _) ((((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj
          ((inverseImageCommRingFunctor S.f.toToposHom).obj B₁.O)).obj.map
            (e.inverse.op.map g)).hom.map_one))))

/-- `siteTransportIdealGenerator` on `1`. -/
theorem siteTransportIdealGenerator_val_app_one
    (σ : SheafOfModules.unit ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj
      ((inverseImageCommRingFunctor S.f.toToposHom).obj B₁.O)) ⟶ S.I) (V : Dᵒᵖ) :
    (S.siteTransportIdealGenerator K e σ).val.app V (1 : ((sheafCompose K
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((inverseImageCommRingFunctor (S.siteTransport K e).f.toToposHom).obj B₁.O)).obj.obj V) =
      σ.val.app (e.inverse.op.obj V) (1 : ((sheafCompose X.J
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
          ((inverseImageCommRingFunctor S.f.toToposHom).obj B₁.O)).obj.obj (e.inverse.op.obj V)) :=
  unitHomEquiv_symm_val_app_one _ V

/-- **The prescribed map of the transported problem on a global section of the ideal.** If the
prescribed map of `S` carries `σ` to the global section `τ` of `𝒢`, then that of
`S.siteTransport K e` carries the restriction of `σ` to the restriction of `τ`. -/
theorem siteTransportIdealGenerator_comp_c
    (σ : SheafOfModules.unit ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj
      ((inverseImageCommRingFunctor S.f.toToposHom).obj B₁.O)) ⟶ S.I)
    (τ : SheafOfModules.unit ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj X.O) ⟶
      S.G)
    (hσ : σ ≫ S.c = unitToRestrictScalarsUnit
        ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).map S.f.fSharpInverseImage) ≫
      (SheafOfModules.restrictScalars ((sheafCompose X.J
        (forget₂ CommRingCat.{u} RingCat.{u})).map S.f.fSharpInverseImage)).map τ) :
    S.siteTransportIdealGenerator K e σ ≫ (S.siteTransport K e).c =
      unitToRestrictScalarsUnit ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).map
          (S.siteTransport K e).f.fSharpInverseImage) ≫
        (SheafOfModules.restrictScalars ((sheafCompose K
          (forget₂ CommRingCat.{u} RingCat.{u})).map
            (S.siteTransport K e).f.fSharpInverseImage)).map (moduleResUnitHom K e τ) := by
  refine (comp_eq_unitToRestrictScalarsUnit_comp_iff _ _ _ _).2 fun V => ?_
  have h := (comp_eq_unitToRestrictScalarsUnit_comp_iff _ _ _ _).1 hσ (e.inverse.op.obj V)
  rw [siteTransportIdealGenerator_val_app_one, moduleResUnitHom_val_app_one]
  exact h

end RingedToposExtensionProblem

end SiteTransport

end Deformation.ToposThickening
