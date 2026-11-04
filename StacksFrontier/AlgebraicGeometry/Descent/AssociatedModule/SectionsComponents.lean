module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.PentagonGeneralSectionsIso

/-!
# Sections of the factors of the comparison of Stacks 03DV

`AlgebraicGeometry.BigFppfOver.objRestrictSectionsIso_eq_explicit` writes the comparison of
sections of Stacks 03DV as a composite of eleven factors, each of which is a
`SheafOfModules.pushforwardComp`, a `SheafOfModules.pushforwardCongr₂`, a
`SheafOfModules.pushforwardCongr`, a unit of the reindexing equivalence of Stacks 06WI, or a
structural associator or unitor.  Every such factor is given on sections by *restriction along a
morphism of the site*, and this file records that, one lemma per factor shape: the component of
the factor at a sheaf of modules `M` and an object `U` of the site is
`M.val.map u.op` for an explicit arrow `u`.

With these the component of a composite of such factors collapses, by
`Stacks.SectionsComponents.val_map_map`, to a single restriction
`M.val.map u.op`; and two restrictions along arrows with the same source and target in the big
fppf site over a scheme, whose target is an open of that scheme, agree, because
`AlgebraicGeometry.BigFppfOver.subsingleton_hom_opensObj` says there is at most one such arrow.
That is how `AlgebraicGeometry.BigFppfOver.SectionsCocycle` is discharged.

## Main results

* `Stacks.SectionsComponents.val_map_map`: two successive restrictions are one.
* `Stacks.SectionsComponents.pushforwardCongr₂_hom_app_val_app` and the companion lemmas: the
  components of each factor shape.

## Implementation notes

Nothing here carries a `stacks` attribute: these are the sections of structural comparisons of
pushforwards.

Every lemma is stated at an arbitrary site, with the arrows of the site as variables, and is
proved by `rfl` or by substituting an equality of arrows.  That is deliberate: the instances at
the big fppf site are then obtained without re-elaborating anything, and the cost of the
same statements written concretely at that site exceeds the heartbeat budget.

## References

* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ v₂ v₃ u₁ u₂ u₃ w m u

namespace Stacks.SectionsComponents

/-! ### Restriction inside a pushforward -/

section Generic

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{w}} {R : Sheaf K RingCat.{w}} [F.IsContinuous J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R)

/-- **Sections of a pushed-forward morphism.**  Pushing a morphism forward along a continuous
functor reindexes its components. -/
@[simp] public theorem pushforward_map_val_app {X Y : SheafOfModules.{m} R} (f : X ⟶ Y) (U : Cᵒᵖ)
    (x : ((SheafOfModules.pushforward.{m} φ).obj X).val.obj U) :
    ((SheafOfModules.pushforward.{m} φ).map f).val.app U x =
      f.val.app (op (F.obj U.unop)) x := rfl

/-- **Restriction inside a pushed-forward module** is restriction along the image arrow. -/
@[simp] public theorem pushforward_obj_val_map (M : SheafOfModules.{m} R) {A A' : Cᵒᵖ} (w : A ⟶ A')
    (x : ((SheafOfModules.pushforward.{m} φ).obj M).val.obj A) :
    ((SheafOfModules.pushforward.{m} φ).obj M).val.map w x =
      M.val.map (F.map w.unop).op x := rfl

end Generic

section Collapse

variable {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D} {R : Sheaf K RingCat.{w}}

/-- **Two successive restrictions are one.**  This is functoriality of the underlying presheaf,
in the orientation that collapses a composite of components of factors of the comparison of
sections into a single restriction. -/
@[simp] public theorem val_map_map (M : SheafOfModules.{m} R) {A A' A'' : D} (f : A ⟶ A')
    (g : A' ⟶ A'') (x : M.val.obj (op A'')) :
    M.val.map f.op (M.val.map g.op x) = M.val.map (f ≫ g).op x := by
  rw [op_comp]
  exact (M.val.map_comp_apply g.op f.op x).symm

/-- **Restricting along the identity does nothing.** -/
@[simp] public theorem val_map_id (M : SheafOfModules.{m} R) {A : D} (x : M.val.obj (op A)) :
    M.val.map (𝟙 A).op x = x := by
  rw [op_id, M.val.map_id]
  rfl

end Collapse

/-! ### The transport along an isomorphism of sites -/

section Congr₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F G : C ⥤ D}
  {T : Sheaf J RingCat.{w}} {S : Sheaf K RingCat.{w}}
  [F.IsContinuous J K] [G.IsContinuous J K]
  (φ : T ⟶ (G.sheafPushforwardContinuous RingCat.{w} J K).obj S)

/-- **Sections of the transport of a pushforward along an isomorphism of sites.** -/
@[simp] public theorem pushforwardCongr₂_hom_app_val_app
    {ψ : T ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj S} (e : F ≅ G)
    (he : φ ≫ (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{w} J K).app S = ψ)
    (M : SheafOfModules.{m} S) (U : Cᵒᵖ)
    (x : ((SheafOfModules.pushforward.{m} φ).obj M).val.obj U) :
    ((SheafOfModules.pushforwardCongr₂.{m} φ e he).hom.app M).val.app U x =
      M.val.map (e.hom.app U.unop).op x := rfl

/-- **Sections of the inverse transport of a pushforward along an isomorphism of sites.** -/
@[simp] public theorem pushforwardCongr₂_inv_app_val_app
    {ψ : T ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj S} (e : F ≅ G)
    (he : φ ≫ (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{w} J K).app S = ψ)
    (M : SheafOfModules.{m} S) (U : Cᵒᵖ)
    (x : ((SheafOfModules.pushforward.{m} ψ).obj M).val.obj U) :
    ((SheafOfModules.pushforwardCongr₂.{m} φ e he).inv.app M).val.app U x =
      M.val.map (e.inv.app U.unop).op x := rfl

end Congr₂

/-! ### The reindexing equivalence -/

section Reindex

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₁} [Category.{v₁} C']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
  (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  (R : Sheaf J RingCat.{w})

/-- **Sections of the unit of the inverse reindexing equivalence of Stacks 06WI.** -/
@[simp] public theorem reindexEquivalence_symm_unitIso_hom_app_val_app
    (M : SheafOfModules.{m} (Stacks.SheafOfModules.reindexRing J' e R)) (U : C'ᵒᵖ)
    (x : M.val.obj U) :
    ((Stacks.SheafOfModules.reindexEquivalence.{_, m, _, _, _, _} e R).symm.unitIso.hom.app
        M).val.app U
        x = M.val.map (e.unitIso.inv.app U.unop).op x := rfl

/-- **Sections of the inverse unit of the inverse reindexing equivalence of Stacks 06WI.** -/
@[simp] public theorem reindexEquivalence_symm_unitIso_inv_app_val_app
    (M : SheafOfModules.{m} (Stacks.SheafOfModules.reindexRing J' e R)) (U : C'ᵒᵖ)
    (x : (((Stacks.SheafOfModules.reindexEquivalence.{_, m, _, _, _, _} e R).symm.functor ⋙
      (Stacks.SheafOfModules.reindexEquivalence.{_, m, _, _, _, _} e R).symm.inverse).obj
          M).val.obj U) :
    ((Stacks.SheafOfModules.reindexEquivalence.{_, m, _, _, _, _} e R).symm.unitIso.inv.app
        M).val.app U
        x = M.val.map (e.unitIso.hom.app U.unop).op x := rfl

end Reindex

/-! ### The four pushforwards of the comparison, as functors -/

section Bridges

variable {C : Type u₁} [Category.{v₁} C] [Limits.HasPullbacks C]
  {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w}) {U V : C}

/-- **Sections of a morphism restricted along an arrow of the site.** -/
@[simp] public theorem overPullback_map_val_app (f : U ⟶ V)
    {M N : SheafOfModules.{m} (R.over U)} (g : M ⟶ N) (A : (Over V)ᵒᵖ)
    (x : ((SheafOfModules.overPullback.{m} R f).obj M).val.obj A) :
    ((SheafOfModules.overPullback.{m} R f).map g).val.app A x =
      g.val.app (op ((Over.pullback f).obj A.unop)) x := rfl

/-- **Restriction inside a module restricted along an arrow of the site.** -/
@[simp] public theorem overPullback_obj_val_map (f : U ⟶ V)
    (M : SheafOfModules.{m} (R.over U)) {A A' : (Over V)ᵒᵖ} (w : A ⟶ A')
    (x : ((SheafOfModules.overPullback.{m} R f).obj M).val.obj A) :
    ((SheafOfModules.overPullback.{m} R f).obj M).val.map w x =
      M.val.map ((Over.pullback f).map w.unop).op x := rfl

end Bridges

section ReindexBridge

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₁} [Category.{v₁} C']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
  (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  (R : Sheaf J RingCat.{w})

/-- **Restriction inside a module reindexed back along the equivalence of Stacks 06WI.** -/
@[simp] public theorem reindexEquivalence_inverse_obj_val_map
    (M : SheafOfModules.{m} (Stacks.SheafOfModules.reindexRing J' e R)) {A A' : Cᵒᵖ} (w : A ⟶ A')
    (x : ((Stacks.SheafOfModules.reindexEquivalence.{_, m, _, _, _, _} e R).inverse.obj
        M).val.obj A) :
    ((Stacks.SheafOfModules.reindexEquivalence.{_, m, _, _, _, _} e R).inverse.obj M).val.map w x =
      M.val.map (e.inverse.map w.unop).op x := rfl

/-- **Sections of a morphism reindexed back along the equivalence of Stacks 06WI.** -/
@[simp] public theorem reindexEquivalence_inverse_map_val_app
    {M N : SheafOfModules.{m} (Stacks.SheafOfModules.reindexRing J' e R)} (g : M ⟶ N) (A : Cᵒᵖ)
    (x : ((Stacks.SheafOfModules.reindexEquivalence.{_, m, _, _, _, _} e R).inverse.obj
        M).val.obj A) :
    ((Stacks.SheafOfModules.reindexEquivalence.{_, m, _, _, _, _} e R).inverse.map g).val.app A x =
      g.val.app (op (e.inverse.obj A.unop)) x := rfl

end ReindexBridge

/-! ### The pushforward of modules on schemes -/

section Schemes

open _root_.AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- **Sections of a pushed-forward morphism of modules on schemes.** -/
@[simp] public theorem schemePushforward_map_val_app (f : X ⟶ Y) {M N : X.Modules} (g : M ⟶ N)
    (A : (TopologicalSpace.Opens ↥Y)ᵒᵖ)
    (x : ((Scheme.Modules.pushforward f).obj M).val.obj A) :
    ((Scheme.Modules.pushforward f).map g).val.app A x =
      g.val.app (op ((TopologicalSpace.Opens.map f.base).obj A.unop)) x := rfl

/-- **Restriction inside a pushed-forward module on a scheme.** -/
@[simp] public theorem schemePushforward_obj_val_map (f : X ⟶ Y) (M : X.Modules)
    {A A' : (TopologicalSpace.Opens ↥Y)ᵒᵖ} (w : A ⟶ A')
    (x : ((Scheme.Modules.pushforward f).obj M).val.obj A) :
    ((Scheme.Modules.pushforward f).obj M).val.map w x =
      M.val.map ((TopologicalSpace.Opens.map f.base).map w.unop).op x := rfl

/-- **Sections of the contraction of an iterated pushforward of modules on schemes.** -/
@[simp] public theorem schemePushforwardComp_hom_app_val_app {Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (M : X.Modules) (A : (TopologicalSpace.Opens ↥Z)ᵒᵖ)
    (x : ((Scheme.Modules.pushforward f ⋙ Scheme.Modules.pushforward g).obj M).val.obj A) :
    ((Scheme.Modules.pushforwardComp f g).hom.app M).val.app A x = x := rfl

/-- **Sections of the inverse contraction of an iterated pushforward of modules on schemes.** -/
@[simp] public theorem schemePushforwardComp_inv_app_val_app {Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (M : X.Modules) (A : (TopologicalSpace.Opens ↥Z)ᵒᵖ)
    (x : ((Scheme.Modules.pushforward (f ≫ g)).obj M).val.obj A) :
    ((Scheme.Modules.pushforwardComp f g).inv.app M).val.app A x = x := rfl

/-- **Sections of the transport of a pushforward of modules on schemes along an equality of
morphisms.** -/
@[simp] public theorem eqToIso_schemePushforward_hom_app_val_app {k₁ k₂ : X ⟶ Y} (h : k₁ = k₂)
    (M : X.Modules) (A : (TopologicalSpace.Opens ↥Y)ᵒᵖ)
    (x : ((Scheme.Modules.pushforward k₁).obj M).val.obj A) :
    ((eqToIso (congrArg (fun k : X ⟶ Y => Scheme.Modules.pushforward k) h)).hom.app
        M).val.app A x =
      M.val.map (eqToHom (congrArg
        (fun k : X ⟶ Y => (TopologicalSpace.Opens.map k.base).obj A.unop)
          h.symm)).op x := by
  subst h
  exact (val_map_id _ x).symm

/-- **Sections of the inverse transport of a pushforward of modules on schemes along an equality
of morphisms.** -/
@[simp] public theorem eqToIso_schemePushforward_inv_app_val_app {k₁ k₂ : X ⟶ Y} (h : k₁ = k₂)
    (M : X.Modules) (A : (TopologicalSpace.Opens ↥Y)ᵒᵖ)
    (x : ((Scheme.Modules.pushforward k₂).obj M).val.obj A) :
    ((eqToIso (congrArg (fun k : X ⟶ Y => Scheme.Modules.pushforward k) h)).inv.app
        M).val.app A x =
      M.val.map (eqToHom (congrArg
        (fun k : X ⟶ Y => (TopologicalSpace.Opens.map k.base).obj A.unop)
          h)).op x := by
  subst h
  exact (val_map_id _ x).symm

end Schemes

/-! ### Restriction to the small Zariski site of the big fppf site -/

section RestrictModule

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Sections of a morphism restricted to the small Zariski site.** -/
@[simp] public theorem restrictModule_map_val_app
    {M N : SheafOfModules.{u} (structureSheaf B S hS)} (f : M ⟶ N)
    (A : (TopologicalSpace.Opens ↥S)ᵒᵖ)
    (x : ((restrictModule B S hS).obj M).val.obj A) :
    ((restrictModule B S hS).map f).val.app A x =
      f.val.app (op ((opensToBig B S hS).obj A.unop)) x := rfl

/-- **Restriction inside a module restricted to the small Zariski site.** -/
@[simp] public theorem restrictModule_obj_val_map
    (M : SheafOfModules.{u} (structureSheaf B S hS))
    {A A' : (TopologicalSpace.Opens ↥S)ᵒᵖ} (w : A ⟶ A')
    (x : ((restrictModule B S hS).obj M).val.obj A) :
    ((restrictModule B S hS).obj M).val.map w x =
      M.val.map ((opensToBig B S hS).map w.unop).op x := rfl

end RestrictModule

/-! ### Restriction along equal arrows, and the comparison of the two right adjoints -/

section OverPullback

attribute [local instance] Over.ConstructProducts.over_binaryProduct_of_pullback

variable {C : Type u₁} [Category.{v₁} C] [Limits.HasPullbacks C]
  {J : GrothendieckTopology C} {U V : C} (R : Sheaf J RingCat.{w})

/-- **Sections of the transport of a restriction along an equality of arrows.** -/
@[simp] public theorem overPullbackCongr_hom_app_val_app {a b : V ⟶ U} (e : a = b)
    (M : SheafOfModules.{w} (R.over V)) (A : (Over U)ᵒᵖ)
    (x : ((SheafOfModules.overPullback.{w} R a).obj M).val.obj A) :
    ((Stacks.SheafOfModules.overPullbackCongr R e).hom.app M).val.app A x =
      M.val.map (eqToHom (congrArg
        (fun k : V ⟶ U => (Over.pullback k).obj A.unop) e.symm)).op x := by
  subst e
  exact (val_map_id M x).symm

/-- **Sections of the inverse transport of a restriction along an equality of arrows.** -/
@[simp] public theorem overPullbackCongr_inv_app_val_app {a b : V ⟶ U} (e : a = b)
    (M : SheafOfModules.{w} (R.over V)) (A : (Over U)ᵒᵖ)
    (x : ((SheafOfModules.overPullback.{w} R b).obj M).val.obj A) :
    ((Stacks.SheafOfModules.overPullbackCongr R e).inv.app M).val.app A x =
      M.val.map (eqToHom (congrArg
        (fun k : V ⟶ U => (Over.pullback k).obj A.unop) e)).op x := by
  subst e
  exact (val_map_id M x).symm

end OverPullback

end Stacks.SectionsComponents

end
