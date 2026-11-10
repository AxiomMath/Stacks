module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.RightAdjointComparison

/-!
# Comparing the two right adjoints of a pushforward of sheaves of modules

A continuous functor of sites which is a left adjoint induces, through
`SheafOfModules.pushforwardPushforwardAdj`, an adjunction between pushforwards of sheaves of
modules. The comparison `CategoryTheory.Adjunction.rightAdjointUniq` of two right adjoints of a
pushforward obtained in this way is computed by the corresponding comparison of right adjoints of
the functors of sites:

* for two adjunctions of one and the same functor of sites, the comparison of the two induced
  right adjoints of the pushforward is the transport of the comparison of the two right adjoints
  of the functor of sites;
* a composite of two such induced adjunctions is the induced adjunction of the composite of the
  two functors of sites, the comparison being the contraction of the iterated pushforward.

## Main results

* `Stacks.Mates.unit_comp_rightAdjointUniq_inv_app`: the comparison of two right adjoints
  carries the unit of the second adjunction to the unit of the first.
* `Stacks.Mates.rightAdjointUniq_of_heq`: the comparison of two right adjoints is insensitive to
  a transport of the left adjoint along an equality of functors.
* `Stacks.SheafOfModules.rightAdjointUniq_pushforwardPushforwardAdj`: the comparison of the two
  right adjoints of a pushforward of sheaves of modules is the transport along the comparison of
  the two right adjoints of the functor of sites.
* `Stacks.SheafOfModules.rightAdjointUniq_comp_pushforwardPushforwardAdj`: a composite of two
  induced adjunctions is the induced adjunction of the composite, up to the contraction
  `SheafOfModules.pushforwardComp` of the iterated pushforward.

## References

* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 04IR](https://stacks.math.columbia.edu/tag/04IR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃ u v

namespace Stacks.Mates

variable {C₀ : Type u₁} {C₁ : Type u₂} [Category.{v₁} C₀] [Category.{v₂} C₁]

/-- For `adj₁ : L ⊣ R₁` and `adj₂ : L ⊣ R₂`, the unit of `adj₂` followed by the inverse of
`CategoryTheory.Adjunction.rightAdjointUniq adj₁ adj₂` at `L.obj X` is the unit of `adj₁`. -/
public theorem unit_comp_rightAdjointUniq_inv_app {L : C₀ ⥤ C₁} {R₁ R₂ : C₁ ⥤ C₀}
    (adj₁ : L ⊣ R₁) (adj₂ : L ⊣ R₂) (X : C₀) :
    adj₂.unit.app X ≫ (Adjunction.rightAdjointUniq adj₁ adj₂).inv.app (L.obj X) =
      adj₁.unit.app X := by
  rw [← Adjunction.unit_rightAdjointUniq_hom_app adj₁ adj₂ X, Category.assoc,
    Iso.hom_inv_id_app]
  exact Category.comp_id _

/-- If `L = L'` and the two adjunctions of `L` are heterogeneously equal to two adjunctions of
`L'` with the same right adjoints, the two comparisons of right adjoints agree. -/
public theorem rightAdjointUniq_of_heq {L : C₀ ⥤ C₁} {L' : C₀ ⥤ C₁} {R₁ R₂ : C₁ ⥤ C₀}
    (h : L = L') (adj₁ : L ⊣ R₁) (adj₂ : L ⊣ R₂) (adj₁' : L' ⊣ R₁) (adj₂' : L' ⊣ R₂)
    (e₁ : HEq adj₁ adj₁') (e₂ : HEq adj₂ adj₂') :
    Adjunction.rightAdjointUniq adj₁ adj₂ = Adjunction.rightAdjointUniq adj₁' adj₂' := by
  subst h
  obtain rfl : adj₁ = adj₁' := eq_of_heq e₁
  obtain rfl : adj₂ = adj₂' := eq_of_heq e₂
  rfl

end Stacks.Mates

namespace Stacks.SheafOfModules

/-! ### Two adjunctions of one functor of sites -/

section Uniq

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D} {G₁ G₂ : D ⥤ C}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K] [Functor.IsContinuous G₁ K J] [Functor.IsContinuous G₂ K J]

/-- Let `F` be a continuous functor of sites which is a left adjoint in two ways, `adj₁ : F ⊣ G₁`
and `adj₂ : F ⊣ G₂`, and let `φ`, `ψ₁`, `ψ₂` be comparisons of structure sheaves making the
pushforwards along `F`, `G₁` and `G₂` into adjunctions of sheaves of modules by
`SheafOfModules.pushforwardPushforwardAdj`. If `ψ₁` and `ψ₂` are compatible with the comparison
`CategoryTheory.Adjunction.rightAdjointUniq adj₁ adj₂` of the two right adjoints downstairs, then
the comparison of the two right adjoints of `SheafOfModules.pushforward φ` is the transport
`SheafOfModules.pushforwardCongr₂` along that comparison. -/
public theorem rightAdjointUniq_pushforwardPushforwardAdj (adj₁ : F ⊣ G₁) (adj₂ : F ⊣ G₂)
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    (ψ₁ : R ⟶ (G₁.sheafPushforwardContinuous RingCat.{u} K J).obj S)
    (ψ₂ : R ⟶ (G₂.sheafPushforwardContinuous RingCat.{u} K J).obj S)
    (H₁ : Functor.whiskerRight (NatTrans.op adj₁.counit) R.obj =
      ψ₁.hom ≫ G₁.op.whiskerLeft φ.hom)
    (H₂ : φ.hom ≫ F.op.whiskerLeft ψ₁.hom ≫
      Functor.whiskerRight (NatTrans.op adj₁.unit) S.obj = 𝟙 S.obj)
    (H₁' : Functor.whiskerRight (NatTrans.op adj₂.counit) R.obj =
      ψ₂.hom ≫ G₂.op.whiskerLeft φ.hom)
    (H₂' : φ.hom ≫ F.op.whiskerLeft ψ₂.hom ≫
      Functor.whiskerRight (NatTrans.op adj₂.unit) S.obj = 𝟙 S.obj)
    (he : ψ₁ ≫ (Functor.sheafPushforwardContinuousNatTrans
        (Adjunction.rightAdjointUniq adj₁ adj₂).inv RingCat.{u} K J).app S = ψ₂) :
    Adjunction.rightAdjointUniq
        (SheafOfModules.pushforwardPushforwardAdj.{v} adj₁ φ ψ₁ H₁ H₂)
        (SheafOfModules.pushforwardPushforwardAdj.{v} adj₂ φ ψ₂ H₁' H₂') =
      SheafOfModules.pushforwardCongr₂.{v} ψ₁
        (Adjunction.rightAdjointUniq adj₁ adj₂).symm he := by
  refine (Stacks.Mates.rightAdjointUniq_eq_of_counit _ _ _ fun M => ?_).symm
  ext U x
  change (M.val.presheaf.map
      ((Adjunction.rightAdjointUniq adj₁ adj₂).inv.app (F.obj U.unop)).op ≫
      M.val.presheaf.map (adj₂.unit.app U.unop).op) _ = _
  rw [← Functor.map_comp, ← op_comp,
    Stacks.Mates.unit_comp_rightAdjointUniq_inv_app adj₁ adj₂ U.unop]
  exact (SheafOfModules.pushforwardPushforwardAdj_counit_app_val_app
    adj₁ φ ψ₁ H₁ H₂ M U x).symm

end Uniq

/-! ### A composite of two induced adjunctions -/

section Comp

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {L : GrothendieckTopology E}
  {F₁ : D ⥤ E} {G₁ : E ⥤ D} {F₂ : C ⥤ D} {G₂ : D ⥤ C}
  {RC : Sheaf J RingCat.{u}} {RD : Sheaf K RingCat.{u}} {RE : Sheaf L RingCat.{u}}
  [Functor.IsContinuous F₁ K L] [Functor.IsContinuous G₁ L K]
  [Functor.IsContinuous F₂ J K] [Functor.IsContinuous G₂ K J]
  [Functor.IsContinuous (F₂ ⋙ F₁) J L] [Functor.IsContinuous (G₁ ⋙ G₂) L J]

/-- A composite of two adjunctions of pushforwards is the adjunction of the composite of the two
functors of sites, the comparison of the two right adjoints being the contraction
`SheafOfModules.pushforwardComp` of the iterated pushforward. -/
public theorem rightAdjointUniq_comp_pushforwardPushforwardAdj (adj₁ : F₁ ⊣ G₁) (adj₂ : F₂ ⊣ G₂)
    (φ₁ : RD ⟶ (F₁.sheafPushforwardContinuous RingCat.{u} K L).obj RE)
    (ψ₁ : RE ⟶ (G₁.sheafPushforwardContinuous RingCat.{u} L K).obj RD)
    (φ₂ : RC ⟶ (F₂.sheafPushforwardContinuous RingCat.{u} J K).obj RD)
    (ψ₂ : RD ⟶ (G₂.sheafPushforwardContinuous RingCat.{u} K J).obj RC)
    (A₁ : Functor.whiskerRight (NatTrans.op adj₁.counit) RE.obj =
      ψ₁.hom ≫ G₁.op.whiskerLeft φ₁.hom)
    (A₂ : φ₁.hom ≫ F₁.op.whiskerLeft ψ₁.hom ≫
      Functor.whiskerRight (NatTrans.op adj₁.unit) RD.obj = 𝟙 RD.obj)
    (B₁ : Functor.whiskerRight (NatTrans.op adj₂.counit) RD.obj =
      ψ₂.hom ≫ G₂.op.whiskerLeft φ₂.hom)
    (B₂ : φ₂.hom ≫ F₂.op.whiskerLeft ψ₂.hom ≫
      Functor.whiskerRight (NatTrans.op adj₂.unit) RC.obj = 𝟙 RC.obj)
    (C₁ : Functor.whiskerRight (NatTrans.op (adj₂.comp adj₁).counit) RE.obj =
      (ψ₁ ≫ (G₁.sheafPushforwardContinuous RingCat.{u} L K).map ψ₂).hom ≫
        (G₁ ⋙ G₂).op.whiskerLeft
          (φ₂ ≫ (F₂.sheafPushforwardContinuous RingCat.{u} J K).map φ₁).hom)
    (C₂ : (φ₂ ≫ (F₂.sheafPushforwardContinuous RingCat.{u} J K).map φ₁).hom ≫
      (F₂ ⋙ F₁).op.whiskerLeft (ψ₁ ≫
          (G₁.sheafPushforwardContinuous RingCat.{u} L K).map ψ₂).hom ≫
      Functor.whiskerRight (NatTrans.op (adj₂.comp adj₁).unit) RC.obj = 𝟙 RC.obj) :
    Adjunction.rightAdjointUniq
        ((SheafOfModules.pushforwardPushforwardAdj.{v} adj₁ φ₁ ψ₁ A₁ A₂).comp
          (SheafOfModules.pushforwardPushforwardAdj.{v} adj₂ φ₂ ψ₂ B₁ B₂))
        (SheafOfModules.pushforwardPushforwardAdj.{v} (adj₂.comp adj₁)
          (φ₂ ≫ (F₂.sheafPushforwardContinuous RingCat.{u} J K).map φ₁)
          (ψ₁ ≫ (G₁.sheafPushforwardContinuous RingCat.{u} L K).map ψ₂) C₁ C₂) =
      SheafOfModules.pushforwardComp.{v} ψ₁ ψ₂ := by
  refine (Stacks.Mates.rightAdjointUniq_eq_of_counit _ _ _ fun M => ?_).symm
  ext U x
  change M.val.presheaf.map ((adj₂.comp adj₁).unit.app U.unop).op x =
      (M.val.presheaf.map (G₂.map (adj₁.unit.app (F₂.obj U.unop))).op ≫
        M.val.presheaf.map (adj₂.unit.app U.unop).op) x
  rw [Adjunction.comp_unit_app, op_comp, Functor.map_comp]

end Comp

end Stacks.SheafOfModules

end
