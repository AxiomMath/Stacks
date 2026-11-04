module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomSiteEquivalenceAnyUniverse
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowCoreflection
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryEquivalence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SectionsComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHomChart
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomGluingTransport
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.CoveringSetTransport

/-!
# Restriction to an étale chart through the slice of the model

Let `X` be an algebraic space and `A` an étale chart of `X`. Restriction of `𝒪_X`-modules to
`A` is restriction to the slice of the equi-universe model of the small étale site of `X` at the
object corresponding to `A`, read on the small étale site of the chart along the comparison of
Stacks 04M0. For a morphism of charts `c : C ⟶ A`, reading the slice at `A` and then restricting
along `c` is restricting along the corresponding morphism of slices and then reading the slice
at `C`.

## Main definitions

* `Stacks.SheafOfModules.ChartSliceTransport.moduleIso`: for a functor `G : C_A ⥤ M/A'` and
  `τ : G ⋙ forget ⋙ e ≅ p`, restriction to the slice at `A'` read along `G` is the direct image
  along `p`.
* `Stacks.SheafOfModules.ChartSliceTransport.transportRestrictIso`: the compatibility of these
  readings with a morphism of charts, given a 2-cell between the site functors.
* `AlgebraicGeometry.Space.chartModelSliceTransport`,
  `AlgebraicGeometry.Space.chartModelSliceTransportIso`:
  the case of an étale chart of an algebraic space.

## References

* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.SheafOfModules.ChartSliceTransport

universe w v₁ v₂ v₃ u₁ u₂ u₃

variable {CA : Type u₁} [Category.{v₁} CA] {DX : Type u₂} [Category.{v₂} DX]
  {M : Type u₃} [Category.{v₃} M]
  {JA : GrothendieckTopology CA} {KX : GrothendieckTopology DX} {JM : GrothendieckTopology M}
  (eX : M ≌ DX) [hX : eX.functor.IsContinuous JM KX] [hX' : eX.inverse.IsContinuous KX JM]
  (RX : Sheaf KX RingCat.{w})
  (pA : CA ⥤ DX) [hpA : pA.IsContinuous JA KX]
  (A' : M) (GA : CA ⥤ Over A') [hGA : GA.IsContinuous JA (JM.over A')]
  (τA : GA ⋙ Over.forget A' ⋙ eX.functor ≅ pA)

/-- The structure map of the reading of the slice at `A'` on `CA` along `GA`. -/
def ringMap :
    (pA.sheafPushforwardContinuous RingCat.{w} JA KX).obj RX ⟶
      (GA.sheafPushforwardContinuous RingCat.{w} JA (JM.over A')).obj
        ((Stacks.SheafOfModules.reindexRing JM eX RX).over A') :=
  haveI : (Over.forget A' ⋙ eX.functor).IsContinuous (JM.over A') KX :=
    Functor.isContinuous_comp _ _ _ JM _
  haveI : (GA ⋙ Over.forget A' ⋙ eX.functor).IsContinuous JA KX :=
    Functor.isContinuous_comp _ _ _ (JM.over A') _
  (Functor.sheafPushforwardContinuousNatTrans τA.hom RingCat.{w} JA KX).app RX

/-- Modules on the slice at `A'`, read on `CA` along `GA`. -/
abbrev transport :
    SheafOfModules.{w} ((Stacks.SheafOfModules.reindexRing JM eX RX).over A') ⥤
      SheafOfModules.{w} ((pA.sheafPushforwardContinuous RingCat.{w} JA KX).obj RX) :=
  SheafOfModules.pushforward.{w} (ringMap eX RX pA A' GA τA)

/-- The slice-side composite, as one direct image. -/
def sliceSideIso :
    (Stacks.SheafOfModules.reindexEquivalence (J' := JM) eX RX).functor ⋙
        SheafOfModules.overFunctor (Stacks.SheafOfModules.reindexRing JM eX RX) A' ⋙
          transport eX RX pA A' GA τA ≅
      haveI : (GA ⋙ Over.forget A').IsContinuous JA JM :=
        Functor.isContinuous_comp _ _ _ (JM.over A') _
      haveI : ((GA ⋙ Over.forget A') ⋙ eX.functor).IsContinuous JA KX :=
        Functor.isContinuous_comp _ _ _ JM _
      SheafOfModules.pushforward.{w} (F := (GA ⋙ Over.forget A') ⋙ eX.functor)
        ((ringMap eX RX pA A' GA τA ≫
          (GA.sheafPushforwardContinuous RingCat.{w} JA (JM.over A')).map
            (𝟙 ((Stacks.SheafOfModules.reindexRing JM eX RX).over A'))) ≫
          ((GA ⋙ Over.forget A').sheafPushforwardContinuous RingCat.{w} JA JM).map
            (𝟙 (Stacks.SheafOfModules.reindexRing JM eX RX))) :=
  haveI : (GA ⋙ Over.forget A').IsContinuous JA JM :=
    Functor.isContinuous_comp _ _ _ (JM.over A') _
  Functor.isoWhiskerLeft
      (SheafOfModules.pushforward.{w} (𝟙 (Stacks.SheafOfModules.reindexRing JM eX RX)))
      (SheafOfModules.pushforwardComp (ringMap eX RX pA A' GA τA)
        (𝟙 ((Stacks.SheafOfModules.reindexRing JM eX RX).over A'))) ≪≫
    SheafOfModules.pushforwardComp _ _

/-- **Restriction to the slice at `A'` read on `CA` is the direct image along `pA`.** -/
def moduleIso :
    (Stacks.SheafOfModules.reindexEquivalence (J' := JM) eX RX).functor ⋙
        SheafOfModules.overFunctor (Stacks.SheafOfModules.reindexRing JM eX RX) A' ⋙
          transport eX RX pA A' GA τA ≅
      SheafOfModules.pushforward.{w}
        (𝟙 ((pA.sheafPushforwardContinuous RingCat.{w} JA KX).obj RX)) :=
  haveI : (GA ⋙ Over.forget A').IsContinuous JA JM :=
    Functor.isContinuous_comp _ _ _ (JM.over A') _
  haveI : ((GA ⋙ Over.forget A') ⋙ eX.functor).IsContinuous JA KX :=
    Functor.isContinuous_comp _ _ _ JM _
  sliceSideIso eX RX pA A' GA τA ≪≫
    SheafOfModules.pushforwardCongr₂ _ τA.symm (by
      ext W : 3
      simp only [ringMap, CategoryTheory.Functor.map_id]
      change RX.obj.map (τA.hom.app W.unop).op ≫ RX.obj.map (τA.inv.app W.unop).op = 𝟙 _
      rw [← RX.obj.map_comp, ← op_comp, Iso.inv_hom_id_app, op_id, RX.obj.map_id])

/-- The structure map of the reading of the slice is invertible. -/
instance isIso_ringMap : IsIso (ringMap (JA := JA) (JM := JM) (KX := KX) eX RX pA A' GA τA) := by
  have : (Over.forget A' ⋙ eX.functor).IsContinuous (JM.over A') KX :=
    Functor.isContinuous_comp _ _ _ JM _
  have : (GA ⋙ Over.forget A' ⋙ eX.functor).IsContinuous JA KX :=
    Functor.isContinuous_comp _ _ _ (JM.over A') _
  exact inferInstanceAs
    (IsIso ((Functor.sheafPushforwardContinuousIso τA.symm RingCat.{w} JA KX).app RX).hom)

section Restrict

variable {CC : Type u₁} [Category.{v₁} CC] {JC : GrothendieckTopology CC}
  (pC : CC ⥤ DX) [hpC : pC.IsContinuous JC KX]
  (C' : M) (GC : CC ⥤ Over C') [hGC : GC.IsContinuous JC (JM.over C')]
  (τC : GC ⋙ Over.forget C' ⋙ eX.functor ≅ pC)
  (pc : CC ⥤ CA) [hpc : pc.IsContinuous JC JA] (κ : pc ⋙ pA ≅ pC)
  (a : C' ⟶ A') (σ : GC ⋙ Over.map a ≅ pc ⋙ GA)

/-- The structure map of the direct image along `pc`, read through `κ`. -/
def restrictRingMap :
    (pC.sheafPushforwardContinuous RingCat.{w} JC KX).obj RX ⟶
      (pc.sheafPushforwardContinuous RingCat.{w} JC JA).obj
        ((pA.sheafPushforwardContinuous RingCat.{w} JA KX).obj RX) :=
  haveI : (pc ⋙ pA).IsContinuous JC KX := Functor.isContinuous_comp _ _ _ JA _
  (Functor.sheafPushforwardContinuousNatTrans κ.hom RingCat.{w} JC KX).app RX

/-- The direct image along `pc`. -/
abbrev restrict :
    SheafOfModules.{w} ((pA.sheafPushforwardContinuous RingCat.{w} JA KX).obj RX) ⥤
      SheafOfModules.{w} ((pC.sheafPushforwardContinuous RingCat.{w} JC KX).obj RX) :=
  SheafOfModules.pushforward.{w} (restrictRingMap (JA := JA) (JC := JC) (KX := KX) RX pA pC pc κ)

/-- The direct image along `pA` followed by the direct image along `pc` is the direct image
along `pC`. -/
def restrictIso :
    SheafOfModules.pushforward.{w} (𝟙 ((pA.sheafPushforwardContinuous RingCat.{w} JA KX).obj RX)) ⋙
        restrict (JA := JA) (JC := JC) (KX := KX) RX pA pC pc κ ≅
      SheafOfModules.pushforward.{w}
        (𝟙 ((pC.sheafPushforwardContinuous RingCat.{w} JC KX).obj RX)) :=
  haveI : (pc ⋙ pA).IsContinuous JC KX := Functor.isContinuous_comp _ _ _ JA _
  SheafOfModules.pushforwardComp _ _ ≪≫
    SheafOfModules.pushforwardCongr₂ _ κ.symm (by
      ext W : 3
      simp only [restrictRingMap, CategoryTheory.Functor.map_id]
      change RX.obj.map (κ.hom.app W.unop).op ≫ RX.obj.map (κ.inv.app W.unop).op = 𝟙 _
      rw [← RX.obj.map_comp, ← op_comp, Iso.inv_hom_id_app, op_id, RX.obj.map_id])

variable (H : ∀ W : CC, eX.functor.map (σ.hom.app W).left ≫ τA.hom.app (pc.obj W) ≫
  κ.hom.app W = τC.hom.app W)

include H in
/-- **Reading the slice at `A'` on `CA` and then restricting along `pc` is restricting along
`a` and then reading the slice at `C'` on `CC`.** -/
def transportRestrictIso :
    transport eX RX pA A' GA τA ⋙ restrict (JA := JA) (JC := JC) (KX := KX) RX pA pC pc κ ≅
      SheafOfModules.overMap.{w} (Stacks.SheafOfModules.reindexRing JM eX RX) a ⋙
        transport eX RX pC C' GC τC :=
  haveI : (pc ⋙ GA).IsContinuous JC (JM.over A') := Functor.isContinuous_comp _ _ _ JA _
  haveI : (GC ⋙ Over.map a).IsContinuous JC (JM.over A') :=
    Functor.isContinuous_comp _ _ _ (JM.over C') _
  SheafOfModules.pushforwardComp _ _ ≪≫
    SheafOfModules.pushforwardCongr₂ _ σ (by
      ext W : 3
      simp only [restrictRingMap, ringMap]
      change RX.obj.map (κ.hom.app W.unop).op ≫ RX.obj.map (τA.hom.app (pc.obj W.unop)).op ≫
          RX.obj.map (eX.functor.map (σ.hom.app W.unop).left).op =
        RX.obj.map (τC.hom.app W.unop).op ≫ 𝟙 _
      rw [Category.comp_id, ← RX.obj.map_comp, ← RX.obj.map_comp, ← op_comp, ← op_comp,
        Category.assoc, H]) ≪≫
    (SheafOfModules.pushforwardComp _ _).symm

/-- The component of `moduleIso` at `Mmod` acts on sections over `W` as restriction along
`τA.inv.app W`. -/
theorem moduleIso_hom_app_val_app (Mmod : SheafOfModules.{w} RX) (W : CA)
    (y : (Mmod.val.obj (op ((GA ⋙ Over.forget A' ⋙ eX.functor).obj W)))) :
    ModuleCat.Hom.hom (((moduleIso (JA := JA) (JM := JM) (KX := KX) eX RX pA A' GA τA).hom.app
      Mmod).val.app (op W)) y =
      ModuleCat.Hom.hom (Mmod.val.map (τA.inv.app W).op) y := rfl

/-- The component of `restrictIso` at `Mmod` acts on sections over `W` as restriction along
`κ.inv.app W`. -/
theorem restrictIso_hom_app_val_app (Mmod : SheafOfModules.{w} RX) (W : CC)
    (y : (Mmod.val.obj (op ((pc ⋙ pA).obj W)))) :
    ModuleCat.Hom.hom (((restrictIso (JA := JA) (JC := JC) (KX := KX) RX pA pC pc κ).hom.app
      Mmod).val.app (op W)) y =
      ModuleCat.Hom.hom (Mmod.val.map (κ.inv.app W).op) y := rfl

omit hX' in
include H in
/-- The component of `transportRestrictIso` at `N` acts on sections over `W` as restriction
along `σ.hom.app W`. -/
theorem transportRestrictIso_hom_app_val_app
    (N : SheafOfModules.{w} ((Stacks.SheafOfModules.reindexRing JM eX RX).over A')) (W : CC)
    (y : (N.val.obj (op ((pc ⋙ GA).obj W)))) :
    ModuleCat.Hom.hom (((transportRestrictIso (JA := JA) (JC := JC) (JM := JM) (KX := KX)
      eX RX pA A' GA τA pC C' GC τC pc κ a σ H).hom.app N).val.app (op W)) y =
      ModuleCat.Hom.hom (N.val.map (σ.hom.app W).op) y := rfl

/-- The direct image along `pc` of a morphism `f` acts on sections over `W` as `f` acts on
sections over `pc.obj W`. -/
theorem restrict_map_val_app {N N' : SheafOfModules.{w}
      ((pA.sheafPushforwardContinuous RingCat.{w} JA KX).obj RX)} (f : N ⟶ N') (W : CC)
    (y : N.val.obj (op (pc.obj W))) :
    ModuleCat.Hom.hom (((restrict (JA := JA) (JC := JC) (KX := KX) RX pA pC pc κ).map f).val.app
      (op W)) y = ModuleCat.Hom.hom (f.val.app (op (pc.obj W))) y := rfl

/-- Read on `CC` along `GC`, the component of `SheafOfModules.overFunctorMap` along `a` acts as
the identity on sections. -/
theorem transport_map_overFunctorMap_hom_app_val_app (Mmod : SheafOfModules.{w} RX) (W : CC)
    (y : ((transport eX RX pC C' GC τC).obj ((SheafOfModules.overFunctor
      (Stacks.SheafOfModules.reindexRing JM eX RX) C').obj
        ((Stacks.SheafOfModules.reindexEquivalence (J' := JM) eX RX).functor.obj Mmod))).val.obj
          (op W)) :
    ModuleCat.Hom.hom (((transport (JA := JC) (JM := JM) (KX := KX) eX RX pC C' GC τC).map
      ((SheafOfModules.overFunctorMap (Stacks.SheafOfModules.reindexRing JM eX RX) a).hom.app
        ((Stacks.SheafOfModules.reindexEquivalence eX RX).functor.obj Mmod))).val.app (op W)) y =
      y := rfl

/-- The identity morphism of a sheaf of modules acts as the identity on sections. -/
theorem sheafOfModules_id_val_app_apply {R : Sheaf JC RingCat.{w}} (N : SheafOfModules.{w} R)
    (W : CC) (y : N.val.obj (op W)) :
    ModuleCat.Hom.hom ((𝟙 N : N ⟶ N).val.app (op W)) y = y := rfl

include H in
/-- The element form of the chart-map compatibility. -/
theorem transportRestrictIso_compat_aux (Mmod : SheafOfModules.{w} RX) (W : CC)
    (y : Mmod.val.obj (op (eX.functor.obj ((pc ⋙ GA).obj W).left))) :
    ModuleCat.Hom.hom (Mmod.val.map (τC.inv.app W).op)
        (ModuleCat.Hom.hom (Mmod.val.map (eX.functor.map (σ.hom.app W).left).op) y) =
      ModuleCat.Hom.hom (Mmod.val.map (κ.inv.app W).op)
        (ModuleCat.Hom.hom (Mmod.val.map (τA.inv.app (pc.obj W) :
          pA.obj (pc.obj W) ⟶ eX.functor.obj ((pc ⋙ GA).obj W).left).op) y) := by
  have key : τC.inv.app W ≫ eX.functor.map (σ.hom.app W).left =
      κ.inv.app W ≫ τA.inv.app (pc.obj W) := by
    rw [← cancel_mono (τA.hom.app (pc.obj W) ≫ κ.hom.app W), Category.assoc, H]
    simp
  have hcomp : ∀ {P Q R' : DXᵒᵖ} (f : P ⟶ Q) (g : Q ⟶ R') (z : Mmod.val.obj P),
      ModuleCat.Hom.hom (Mmod.val.map g) (ModuleCat.Hom.hom (Mmod.val.map f) z) =
        ModuleCat.Hom.hom (Mmod.val.map (f ≫ g)) z := by
    intros
    rw [Mmod.val.map_comp]
    rfl
  have k2 : (eX.functor.map (σ.hom.app W).left).op ≫ (τC.inv.app W).op =
      (τA.inv.app (pc.obj W) : pA.obj (pc.obj W) ⟶ eX.functor.obj ((pc ⋙ GA).obj W).left).op ≫
        (κ.inv.app W).op := by
    rw [← op_comp, ← op_comp, key]
  have hmap : ∀ {P Q : DXᵒᵖ} {f g : P ⟶ Q} (_ : f = g) (z : Mmod.val.obj P),
      ModuleCat.Hom.hom (Mmod.val.map f) z = ModuleCat.Hom.hom (Mmod.val.map g) z := by
    intro P Q f g h z
    rw [h]
  exact (hcomp _ _ y).trans ((hmap k2 y).trans (hcomp
    (τA.inv.app (pc.obj W) : pA.obj (pc.obj W) ⟶ eX.functor.obj ((pc ⋙ GA).obj W).left).op
    (κ.inv.app W).op y).symm)

include H in
/-- **The chart-map compatibility**, on modules: the two identifications of the restriction of
`𝒪_X`-modules along `pA` and then `pc` with the restriction along `pC` agree. -/
theorem transportRestrictIso_compat :
    Functor.isoWhiskerLeft
        ((Stacks.SheafOfModules.reindexEquivalence (J' := JM) eX RX).functor ⋙
          SheafOfModules.overFunctor (Stacks.SheafOfModules.reindexRing JM eX RX) A')
        (transportRestrictIso eX RX pA A' GA τA pC C' GC τC pc κ a σ H) ≪≫
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (Functor.isoWhiskerLeft
            (Stacks.SheafOfModules.reindexEquivalence (J' := JM) eX RX).functor
            (SheafOfModules.overFunctorMap (Stacks.SheafOfModules.reindexRing JM eX RX) a))
          (transport eX RX pC C' GC τC) ≪≫ moduleIso eX RX pC C' GC τC) =
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (moduleIso eX RX pA A' GA τA)
        (restrict (JA := JA) (JC := JC) (KX := KX) RX pA pC pc κ) ≪≫
      restrictIso (JA := JA) (JC := JC) (KX := KX) RX pA pC pc κ := by
  apply Iso.ext
  ext Mmod ⟨W⟩ x
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Iso.symm_hom, Functor.associator_inv_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.hom_comp, LinearMap.comp_apply, sheafOfModules_id_val_app_apply,
    moduleIso_hom_app_val_app, restrictIso_hom_app_val_app, transportRestrictIso_hom_app_val_app,
    restrict_map_val_app, transport_map_overFunctorMap_hom_app_val_app]
  exact transportRestrictIso_compat_aux eX RX pA A' GA τA pC C' GC τC pc κ a σ H Mmod W x

end Restrict

/-- Conjugating an inverse pair `m ≫ k = 𝟙` by the counit of an equivalence. -/
theorem equivalence_counit_compat {M D : Type*} [Category M] [Category D] (e : M ≌ D) {P Q : D}
    (m : P ⟶ Q) (k : Q ⟶ P) (h : m ≫ k = 𝟙 P) :
    e.functor.map (e.inverse.map m) ≫ (e.counitIso.hom.app Q ≫ 𝟙 Q) ≫ k =
      e.counitIso.hom.app P ≫ 𝟙 P := by
  have : e.functor.map (e.inverse.map m) ≫ e.counit.app Q = e.counit.app P ≫ m :=
    e.counit.naturality m
  have hQ : e.counitIso.hom.app Q ≫ 𝟙 Q = e.counit.app Q := Category.comp_id _
  have hP : e.counitIso.hom.app P ≫ 𝟙 P = e.counit.app P := Category.comp_id _
  rw [hQ, hP, ← Category.assoc, this, Category.assoc, h]
  exact Category.comp_id _

end Stacks.SheafOfModules.ChartSliceTransport

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] chartModelSliceTail_functor_isContinuous

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- The object of the model of the small étale site of `X` attached to a chart `A`. -/
abbrev chartModelObj (A : SmallEtale B S hS X.1) : SmallEtaleModel B S hS X.1 :=
  (smallEtaleModelEquivalence B S hS X.1).inverse.obj A

/-- The functor of `chartModelSliceTail` from the small étale site of a chart to the slice of
the model at that chart is continuous. -/
instance chartModelSliceTail_functor_isContinuous' (A : SmallEtale B S hS X.1) :
    (chartModelSliceTail B S hS X A).functor.IsContinuous
      (SmallEtale.topology B S hS (chartSpace B S hS X A).1)
      ((smallEtaleModelRingedSite B S hS X.1 X.2).over (chartModelObj B S hS X A)).J :=
  chartModelSliceTail_functor_isContinuous B S hS X A

/-- The functor of `chartModelSliceTail` is continuous for the topology of the small étale
ringed site of the chart. -/
instance chartModelSliceTail_functor_isContinuous'' (A : SmallEtale B S hS X.1) :
    (chartModelSliceTail B S hS X A).functor.IsContinuous
      (smallEtaleRingedSite B S hS (chartSpace B S hS X A).1 (chartSpace B S hS X A).2).J
      ((smallEtaleModelRingedSite B S hS X.1 X.2).over (chartModelObj B S hS X A)).J :=
  chartModelSliceTail_functor_isContinuous B S hS X A

/-- The comparison of Stacks 04M0 into the slice of the model, followed by the slice projection
and the model equivalence, is postcomposition with the chart. -/
def chartModelSliceTailForgetIso (A : SmallEtale B S hS X.1) :
    (chartModelSliceTail B S hS X A).functor ⋙ Over.forget (chartModelObj B S hS X A) ⋙
        (smallEtaleModelEquivalence B S hS X.1).functor ≅
      smallEtalePostcomp B S hS (chartToSpace B S hS X A) (isEtale_chartToSpace B S hS X A) :=
  Functor.isoWhiskerLeft
      (smallEtalePostcomp B S hS (chartToSpace B S hS X A) (isEtale_chartToSpace B S hS X A))
      (smallEtaleModelEquivalence B S hS X.1).counitIso ≪≫ Functor.rightUnitor _

/-- The functor of `chartModelSliceTail`, followed by the slice projection and the model
equivalence, is continuous. -/
instance chartModelSliceTailForget_isContinuous (A : SmallEtale B S hS X.1) :
    ((chartModelSliceTail B S hS X A).functor ⋙ Over.forget (chartModelObj B S hS X A) ⋙
        (smallEtaleModelEquivalence B S hS X.1).functor).IsContinuous
      (SmallEtale.topology B S hS (chartSpace B S hS X A).1) (SmallEtale.topology B S hS X.1) :=
  @Functor.isContinuous_comp _ _ _ _ _ _ _ _
    (SmallEtale.topology B S hS (chartSpace B S hS X A).1)
    ((smallEtaleModelTopology B S hS X.1).over (chartModelObj B S hS X A))
    (SmallEtale.topology B S hS X.1) inferInstance
    (@Functor.isContinuous_comp _ _ _ _ _ _ _ _ _ (smallEtaleModelTopology B S hS X.1) _
      inferInstance (smallEtaleModelEquivalence_functor_isContinuous B S hS _))

/-- Modules on the slice of the model of `X` at a chart, read on the small étale site of the
chart. -/
abbrev chartModelSliceTransport (A : SmallEtale B S hS X.1) :
    SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          ((smallEtaleModelRingedSite B S hS X.1 X.2).over (chartModelObj B S hS X A)).O) ⥤
      SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X A)) :=
  Stacks.SheafOfModules.ChartSliceTransport.transport
    (JA := SmallEtale.topology B S hS (chartSpace B S hS X A).1)
    (KX := SmallEtale.topology B S hS X.1)
    (JM := smallEtaleModelTopology B S hS X.1)
    (hX := smallEtaleModelEquivalence_functor_isContinuous B S hS _)
    (hpA := smallEtalePostcomp_isContinuous B S hS _ _)
    (hGA := chartModelSliceTail_functor_isContinuous B S hS X A)
    (smallEtaleModelEquivalence B S hS X.1)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
    (smallEtalePostcomp B S hS (chartToSpace B S hS X A) (isEtale_chartToSpace B S hS X A))
    (chartModelObj B S hS X A) (chartModelSliceTail B S hS X A).functor
    (chartModelSliceTailForgetIso B S hS X A)

/-- **Restriction of `𝒪_X`-modules to the slice of the model at a chart, read on the chart, is
restriction to the chart.** -/
def chartModelSliceTransportIso (A : SmallEtale B S hS X.1) :
    (smallEtaleModelModulesEquivalence B S hS X).functor ⋙
        SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS X.1 X.2).O)
          (chartModelObj B S hS X A) ⋙ chartModelSliceTransport B S hS X A ≅
      chartModules B S hS X A :=
  Stacks.SheafOfModules.ChartSliceTransport.moduleIso
    (JA := SmallEtale.topology B S hS (chartSpace B S hS X A).1)
    (KX := SmallEtale.topology B S hS X.1)
    (JM := smallEtaleModelTopology B S hS X.1)
    (hX := smallEtaleModelEquivalence_functor_isContinuous B S hS _)
    (hX' := smallEtaleModelEquivalence_inverse_isContinuous B S hS _)
    (hpA := smallEtalePostcomp_isContinuous B S hS _ _)
    (hGA := chartModelSliceTail_functor_isContinuous B S hS X A)
    (smallEtaleModelEquivalence B S hS X.1)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
    (smallEtalePostcomp B S hS (chartToSpace B S hS X A) (isEtale_chartToSpace B S hS X A))
    (chartModelObj B S hS X A) (chartModelSliceTail B S hS X A).functor
    (chartModelSliceTailForgetIso B S hS X A)

variable {X} in
/-- Postcomposition with a morphism of charts `c : C ⟶ A`, followed by postcomposition with the
chart `A`, is postcomposition with the chart `C`. -/
def chartPostcompIso {C A : SmallEtale B S hS X.1} (c : C ⟶ A) :
    smallEtalePostcomp B S hS (chartMap B S hS X c) (isEtale_chartMap B S hS X c) ⋙
        smallEtalePostcomp B S hS (chartToSpace B S hS X A) (isEtale_chartToSpace B S hS X A) ≅
      smallEtalePostcomp B S hS (chartToSpace B S hS X C) (isEtale_chartToSpace B S hS X C) :=
  Functor.isoWhiskerRight (chartLocalizationPostcompIso B S hS X c)
    (Over.forget A)

variable {X} in
/-- The comparisons of Stacks 04M0 into the slices of the model at two charts `C ⟶ A` turn
postcomposition with the morphism of charts into `Over.map` along the corresponding morphism of
the model. -/
def chartModelSliceTailMapIso {C A : SmallEtale B S hS X.1} (c : C ⟶ A) :
    (chartModelSliceTail B S hS X C).functor ⋙
        Over.map ((smallEtaleModelEquivalence B S hS X.1).inverse.map c) ≅
      smallEtalePostcomp B S hS (chartMap B S hS X c) (isEtale_chartMap B S hS X c) ⋙
        (chartModelSliceTail B S hS X A).functor :=
  NatIso.ofComponents
    (fun W => Over.isoMk ((smallEtaleModelEquivalence B S hS X.1).inverse.mapIso
      ((Over.forget A).mapIso ((chartLocalizationPostcompIso B S hS X c).app W)).symm)
      (((smallEtaleModelEquivalence B S hS X.1).inverse.map_comp _ _).symm.trans
        ((congrArg (smallEtaleModelEquivalence B S hS X.1).inverse.map
          (Over.w ((chartLocalizationPostcompIso B S hS X c).inv.app W))).trans
          ((smallEtaleModelEquivalence B S hS X.1).inverse.map_comp _ _))))
    (fun {_W _W'} g => Over.OverMorphism.ext
      (((smallEtaleModelEquivalence B S hS X.1).inverse.map_comp _ _).symm.trans
        ((congrArg (smallEtaleModelEquivalence B S hS X.1).inverse.map
          (congrArg CommaMorphism.left
            ((chartLocalizationPostcompIso B S hS X c).inv.naturality g))).trans
          ((smallEtaleModelEquivalence B S hS X.1).inverse.map_comp _ _))))

variable {X} in
/-- The underlying morphism of a component of `chartModelSliceTailMapIso` is the image under the
inverse of the model equivalence of the corresponding component of the inverse of
`chartLocalizationPostcompIso`. -/
theorem chartModelSliceTailMapIso_hom_app_left {C A : SmallEtale B S hS X.1} (c : C ⟶ A)
    (W : SmallEtale B S hS (chartSpace B S hS X C).1) :
    ((chartModelSliceTailMapIso B S hS c).hom.app W).left =
      (smallEtaleModelEquivalence B S hS X.1).inverse.map
        ((chartLocalizationPostcompIso B S hS X c).inv.app W).left := rfl

variable {X} in
/-- The 2-cell between the readings of the slices of the model at two charts `C ⟶ A`. -/
theorem chartModelSliceTailMapIso_compat {C A : SmallEtale B S hS X.1} (c : C ⟶ A)
    (W : SmallEtale B S hS (chartSpace B S hS X C).1) :
    (smallEtaleModelEquivalence B S hS X.1).functor.map
        ((chartModelSliceTailMapIso B S hS c).hom.app W).left ≫
      (chartModelSliceTailForgetIso B S hS X A).hom.app
        ((smallEtalePostcomp B S hS (chartMap B S hS X c) (isEtale_chartMap B S hS X c)).obj W) ≫
        (chartPostcompIso B S hS c).hom.app W =
      (chartModelSliceTailForgetIso B S hS X C).hom.app W := by
  have h2 : ((chartLocalizationPostcompIso B S hS X c).inv.app W).left ≫
      ((chartLocalizationPostcompIso B S hS X c).hom.app W).left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id_app]
    rfl
  exact Stacks.SheafOfModules.ChartSliceTransport.equivalence_counit_compat
    (smallEtaleModelEquivalence B S hS X.1) _ _ h2

variable {X} in
/-- Restriction of modules along a morphism of charts `c : C ⟶ A`: the direct image along
postcomposition with `c`, read through `AlgebraicGeometry.Space.chartPostcompIso`. -/
abbrev chartRestrictModules {C A : SmallEtale B S hS X.1} (c : C ⟶ A) :
    SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X A)) ⥤
      SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X C)) :=
  Stacks.SheafOfModules.ChartSliceTransport.restrict
    (JA := SmallEtale.topology B S hS (chartSpace B S hS X A).1)
    (JC := SmallEtale.topology B S hS (chartSpace B S hS X C).1)
    (KX := SmallEtale.topology B S hS X.1)
    (hpc := smallEtalePostcomp_isContinuous B S hS _ _)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
    (smallEtalePostcomp B S hS (chartToSpace B S hS X A) (isEtale_chartToSpace B S hS X A))
    (smallEtalePostcomp B S hS (chartToSpace B S hS X C) (isEtale_chartToSpace B S hS X C))
    (smallEtalePostcomp B S hS (chartMap B S hS X c) (isEtale_chartMap B S hS X c))
    (chartPostcompIso B S hS c)

variable {X} in
/-- Restricting to the chart `A` and then along `c : C ⟶ A` is restricting to the chart `C`. -/
def chartRestrictModulesIso {C A : SmallEtale B S hS X.1} (c : C ⟶ A) :
    chartModules B S hS X A ⋙ chartRestrictModules B S hS c ≅ chartModules B S hS X C :=
  Stacks.SheafOfModules.ChartSliceTransport.restrictIso
    (JA := SmallEtale.topology B S hS (chartSpace B S hS X A).1)
    (JC := SmallEtale.topology B S hS (chartSpace B S hS X C).1)
    (KX := SmallEtale.topology B S hS X.1)
    (hpA := smallEtalePostcomp_isContinuous B S hS _ _)
    (hpC := smallEtalePostcomp_isContinuous B S hS _ _)
    (hpc := smallEtalePostcomp_isContinuous B S hS _ _)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
    (smallEtalePostcomp B S hS (chartToSpace B S hS X A) (isEtale_chartToSpace B S hS X A))
    (smallEtalePostcomp B S hS (chartToSpace B S hS X C) (isEtale_chartToSpace B S hS X C))
    (smallEtalePostcomp B S hS (chartMap B S hS X c) (isEtale_chartMap B S hS X c))
    (chartPostcompIso B S hS c)

variable {X} in
/-- Reading the slice of the model at `A` on the chart `A` and then restricting along
`c : C ⟶ A` is restricting along the corresponding morphism of the model and then reading the
slice at `C`. -/
def chartModelSliceTransportRestrictIso {C A : SmallEtale B S hS X.1} (c : C ⟶ A) :
    chartModelSliceTransport B S hS X A ⋙ chartRestrictModules B S hS c ≅
      SheafOfModules.overMap.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS X.1 X.2).O)
          ((smallEtaleModelEquivalence B S hS X.1).inverse.map c) ⋙
        chartModelSliceTransport B S hS X C :=
  Stacks.SheafOfModules.ChartSliceTransport.transportRestrictIso
    (JA := SmallEtale.topology B S hS (chartSpace B S hS X A).1)
    (JC := SmallEtale.topology B S hS (chartSpace B S hS X C).1)
    (KX := SmallEtale.topology B S hS X.1)
    (JM := smallEtaleModelTopology B S hS X.1)
    (hX := smallEtaleModelEquivalence_functor_isContinuous B S hS _)
    (hpA := smallEtalePostcomp_isContinuous B S hS _ _)
    (hGA := chartModelSliceTail_functor_isContinuous B S hS X A)
    (hpC := smallEtalePostcomp_isContinuous B S hS _ _)
    (hGC := chartModelSliceTail_functor_isContinuous B S hS X C)
    (hpc := smallEtalePostcomp_isContinuous B S hS _ _)
    (smallEtaleModelEquivalence B S hS X.1)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
    (smallEtalePostcomp B S hS (chartToSpace B S hS X A) (isEtale_chartToSpace B S hS X A))
    (chartModelObj B S hS X A) (chartModelSliceTail B S hS X A).functor
    (chartModelSliceTailForgetIso B S hS X A)
    (smallEtalePostcomp B S hS (chartToSpace B S hS X C) (isEtale_chartToSpace B S hS X C))
    (chartModelObj B S hS X C) (chartModelSliceTail B S hS X C).functor
    (chartModelSliceTailForgetIso B S hS X C)
    (smallEtalePostcomp B S hS (chartMap B S hS X c) (isEtale_chartMap B S hS X c))
    (chartPostcompIso B S hS c) ((smallEtaleModelEquivalence B S hS X.1).inverse.map c)
    (chartModelSliceTailMapIso B S hS c) (chartModelSliceTailMapIso_compat B S hS c)

variable {X} in
/-- **The chart-map compatibility for an algebraic space**, on modules. -/
theorem chartModelSliceTransportIso_compat {C A : SmallEtale B S hS X.1} (c : C ⟶ A) :
    Functor.isoWhiskerLeft
        ((smallEtaleModelModulesEquivalence B S hS X).functor ⋙
          SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS X.1 X.2).O)
            (chartModelObj B S hS X A))
        (chartModelSliceTransportRestrictIso B S hS c) ≪≫
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (Functor.isoWhiskerLeft (smallEtaleModelModulesEquivalence B S hS X).functor
            (SheafOfModules.overFunctorMap
              (Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleModelRingedSite B S hS X.1 X.2).O)
              ((smallEtaleModelEquivalence B S hS X.1).inverse.map c)))
          (chartModelSliceTransport B S hS X C) ≪≫ chartModelSliceTransportIso B S hS X C) =
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (chartModelSliceTransportIso B S hS X A)
        (chartRestrictModules B S hS c) ≪≫
      chartRestrictModulesIso B S hS c :=
  Stacks.SheafOfModules.ChartSliceTransport.transportRestrictIso_compat
    (JA := SmallEtale.topology B S hS (chartSpace B S hS X A).1)
    (JC := SmallEtale.topology B S hS (chartSpace B S hS X C).1)
    (KX := SmallEtale.topology B S hS X.1)
    (JM := smallEtaleModelTopology B S hS X.1)
    (hX := smallEtaleModelEquivalence_functor_isContinuous B S hS _)
    (hX' := smallEtaleModelEquivalence_inverse_isContinuous B S hS _)
    (hpA := smallEtalePostcomp_isContinuous B S hS _ _)
    (hGA := chartModelSliceTail_functor_isContinuous B S hS X A)
    (hpC := smallEtalePostcomp_isContinuous B S hS _ _)
    (hGC := chartModelSliceTail_functor_isContinuous B S hS X C)
    (hpc := smallEtalePostcomp_isContinuous B S hS _ _)
    (smallEtaleModelEquivalence B S hS X.1)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
    (smallEtalePostcomp B S hS (chartToSpace B S hS X A) (isEtale_chartToSpace B S hS X A))
    (chartModelObj B S hS X A) (chartModelSliceTail B S hS X A).functor
    (chartModelSliceTailForgetIso B S hS X A)
    (smallEtalePostcomp B S hS (chartToSpace B S hS X C) (isEtale_chartToSpace B S hS X C))
    (chartModelObj B S hS X C) (chartModelSliceTail B S hS X C).functor
    (chartModelSliceTailForgetIso B S hS X C)
    (smallEtalePostcomp B S hS (chartMap B S hS X c) (isEtale_chartMap B S hS X c))
    (chartPostcompIso B S hS c) ((smallEtaleModelEquivalence B S hS X.1).inverse.map c)
    (chartModelSliceTailMapIso B S hS c) (chartModelSliceTailMapIso_compat B S hS c)

variable {X} in
/-- The structure map of `AlgebraicGeometry.Space.chartRestrictModules` is the identity. -/
theorem chartRestrictModules_ringMap_eq {C A : SmallEtale B S hS X.1} (c : C ⟶ A) :
    Stacks.SheafOfModules.ChartSliceTransport.restrictRingMap
      (JA := SmallEtale.topology B S hS (chartSpace B S hS X A).1)
      (JC := SmallEtale.topology B S hS (chartSpace B S hS X C).1)
      (KX := SmallEtale.topology B S hS X.1)
      (hpA := smallEtalePostcomp_isContinuous B S hS _ _)
      (hpC := smallEtalePostcomp_isContinuous B S hS _ _)
      (hpc := smallEtalePostcomp_isContinuous B S hS _ _)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
      (smallEtalePostcomp B S hS (chartToSpace B S hS X A) (isEtale_chartToSpace B S hS X A))
      (smallEtalePostcomp B S hS (chartToSpace B S hS X C) (isEtale_chartToSpace B S hS X C))
      (smallEtalePostcomp B S hS (chartMap B S hS X c) (isEtale_chartMap B S hS X c))
      (chartPostcompIso B S hS c) =
    𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS (chartSpace B S hS X C).1 (chartSpace B S hS X C).2).O) :=
  rfl

/-- The inverse of the equivalence `chartModelSliceTail` is continuous for the topologies of the
two ringed sites. -/
instance chartModelSliceTail_inverse_isContinuous' (A : SmallEtale B S hS X.1) :
    (chartModelSliceTail B S hS X A).inverse.IsContinuous
      ((smallEtaleModelRingedSite B S hS X.1 X.2).over (chartModelObj B S hS X A)).J
      (smallEtaleRingedSite B S hS (chartSpace B S hS X A).1 (chartSpace B S hS X A).2).J :=
  chartModelSliceTail_inverse_isContinuous B S hS X A

/-- The structure map of `AlgebraicGeometry.Space.chartModelSliceTransport`, in the spelling of the
two ringed sites. -/
abbrev chartModelSliceTransportRingMap (A : SmallEtale B S hS X.1) :
    (Stacks.SheafOfModules.Tensor.ringSheaf
  (smallEtaleRingedSite B S hS (chartSpace B S hS X A).1 (chartSpace B S hS X A).2).O) ⟶
      ((chartModelSliceTail B S hS X A).functor.sheafPushforwardContinuous RingCat.{u}
        (smallEtaleRingedSite B S hS (chartSpace B S hS X A).1 (chartSpace B S hS X A).2).J
        ((smallEtaleModelRingedSite B S hS X.1 X.2).over (chartModelObj B S hS X A)).J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf
          ((smallEtaleModelRingedSite B S hS X.1 X.2).over (chartModelObj B S hS X A)).O) :=
  Stacks.SheafOfModules.ChartSliceTransport.ringMap
    (JA := SmallEtale.topology B S hS (chartSpace B S hS X A).1)
    (KX := SmallEtale.topology B S hS X.1)
    (JM := smallEtaleModelTopology B S hS X.1)
    (hX := smallEtaleModelEquivalence_functor_isContinuous B S hS _)
    (hpA := smallEtalePostcomp_isContinuous B S hS _ _)
    (hGA := chartModelSliceTail_functor_isContinuous B S hS X A)
    (smallEtaleModelEquivalence B S hS X.1)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
    (smallEtalePostcomp B S hS (chartToSpace B S hS X A) (isEtale_chartToSpace B S hS X A))
    (chartModelObj B S hS X A) (chartModelSliceTail B S hS X A).functor
    (chartModelSliceTailForgetIso B S hS X A)

/-- The structure map `chartModelSliceTransportRingMap` is an isomorphism. -/
instance isIso_chartModelSliceTransportRingMap (A : SmallEtale B S hS X.1) :
    IsIso (chartModelSliceTransportRingMap B S hS X A) :=
  Stacks.SheafOfModules.ChartSliceTransport.isIso_ringMap
    (JA := SmallEtale.topology B S hS (chartSpace B S hS X A).1)
    (KX := SmallEtale.topology B S hS X.1)
    (JM := smallEtaleModelTopology B S hS X.1)
    (hX := smallEtaleModelEquivalence_functor_isContinuous B S hS _)
    (hpA := smallEtalePostcomp_isContinuous B S hS _ _)
    (hGA := chartModelSliceTail_functor_isContinuous B S hS X A)
    (smallEtaleModelEquivalence B S hS X.1)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
    (smallEtalePostcomp B S hS (chartToSpace B S hS X A) (isEtale_chartToSpace B S hS X A))
    (chartModelObj B S hS X A) (chartModelSliceTail B S hS X A).functor
    (chartModelSliceTailForgetIso B S hS X A)

/-- Reading modules on the slice of the model at a chart on the chart is an equivalence. -/
def chartModelSliceTransportEquivalence (A : SmallEtale B S hS X.1) :
    SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          ((smallEtaleModelRingedSite B S hS X.1 X.2).over (chartModelObj B S hS X A)).O) ≌
      SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
  (smallEtaleRingedSite B S hS (chartSpace B S hS X A).1 (chartSpace B S hS X A).2).O) :=
  @SheafOfModules.pushforwardPushforwardEquivalence _ _ _ _
    (smallEtaleRingedSite B S hS (chartSpace B S hS X A).1 (chartSpace B S hS X A).2).J
    ((smallEtaleModelRingedSite B S hS X.1 X.2).over (chartModelObj B S hS X A)).J
    (chartModelSliceTail B S hS X A) _ _
    (chartModelSliceTail_functor_isContinuous'' B S hS X A)
    (chartModelSliceTail_inverse_isContinuous' B S hS X A)
    (chartModelSliceTransportRingMap B S hS X A)
    (@Stacks.SheafOfModules.InternalHom.AnyUniverse.psiOfIso
      ((smallEtaleModelRingedSite B S hS X.1 X.2).over (chartModelObj B S hS X A))
      (smallEtaleRingedSite B S hS (chartSpace B S hS X A).1 (chartSpace B S hS X A).2)
      (chartModelSliceTail B S hS X A) (chartModelSliceTail_functor_isContinuous'' B S hS X A)
      (chartModelSliceTail_inverse_isContinuous' B S hS X A)
      (chartModelSliceTransportRingMap B S hS X A)
      (isIso_chartModelSliceTransportRingMap B S hS X A))
    (@Stacks.SheafOfModules.InternalHom.AnyUniverse.psiOfIso_counit
      ((smallEtaleModelRingedSite B S hS X.1 X.2).over (chartModelObj B S hS X A))
      (smallEtaleRingedSite B S hS (chartSpace B S hS X A).1 (chartSpace B S hS X A).2)
      (chartModelSliceTail B S hS X A) (chartModelSliceTail_functor_isContinuous'' B S hS X A)
      (chartModelSliceTail_inverse_isContinuous' B S hS X A)
      (chartModelSliceTransportRingMap B S hS X A)
      (isIso_chartModelSliceTransportRingMap B S hS X A))
    (@Stacks.SheafOfModules.InternalHom.AnyUniverse.psiOfIso_unit
      ((smallEtaleModelRingedSite B S hS X.1 X.2).over (chartModelObj B S hS X A))
      (smallEtaleRingedSite B S hS (chartSpace B S hS X A).1 (chartSpace B S hS X A).2)
      (chartModelSliceTail B S hS X A) (chartModelSliceTail_functor_isContinuous'' B S hS X A)
      (chartModelSliceTail_inverse_isContinuous' B S hS X A)
      (chartModelSliceTransportRingMap B S hS X A)
      (isIso_chartModelSliceTransportRingMap B S hS X A))

/-- Reading modules on the slice of the model at a chart on the chart is an equivalence. -/
instance chartModelSliceTransport_isEquivalence (A : SmallEtale B S hS X.1) :
    (chartModelSliceTransport B S hS X A).IsEquivalence :=
  (chartModelSliceTransportEquivalence B S hS X A).isEquivalence_functor

section Derived

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable {X}

/-- Restriction of modules along a morphism of charts is additive. -/
instance chartRestrictModules_additive {C A : SmallEtale B S hS X.1} (c : C ⟶ A) :
    (chartRestrictModules B S hS c).Additive :=
  etaleModulePullback_additive B S hS _ _

/-- Restriction of modules along a morphism of charts preserves finite limits. -/
instance chartRestrictModules_preservesFiniteLimits {C A : SmallEtale B S hS X.1} (c : C ⟶ A) :
    PreservesFiniteLimits (chartRestrictModules B S hS c) :=
  preservesFiniteLimits_etaleModulePullback B S hS _ _

/-- Restriction of modules along a morphism of charts preserves finite colimits. -/
instance chartRestrictModules_preservesFiniteColimits {C A : SmallEtale B S hS X.1} (c : C ⟶ A) :
    PreservesFiniteColimits (chartRestrictModules B S hS c) :=
  preservesFiniteColimits_etaleModulePullback B S hS _ _

/-- Reading modules on the slice of the model at a chart on the chart is additive. -/
instance chartModelSliceTransport_additive (A : SmallEtale B S hS X.1) :
    (chartModelSliceTransport B S hS X A).Additive :=
  SheafOfModules.pushforward_additive _

/-- Reading modules on the slice of the model at a chart on the chart preserves finite limits. -/
instance chartModelSliceTransport_preservesFiniteLimits (A : SmallEtale B S hS X.1) :
    PreservesFiniteLimits (chartModelSliceTransport B S hS X A) :=
  PreservesLimitsOfSize.preservesFiniteLimits.{u, u} _

/-- Reading modules on the slice of the model at a chart on the chart preserves finite
colimits. -/
instance chartModelSliceTransport_preservesFiniteColimits (A : SmallEtale B S hS X.1) :
    PreservesFiniteColimits (chartModelSliceTransport B S hS X A) :=
  PreservesColimitsOfSize.preservesFiniteColimits.{u, u} _

end Derived

section Gluing

/-- Sheaves of modules on the small étale ringed topos of an algebraic space form an abelian
category. -/
local instance (priority := 5000) instAbelianSpaceModules (Y : AlgebraicSpaces B S hS) :
    Abelian (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) :=
  SheafOfModules.instAbelian _

variable {X}

/-- The functor induced on derived categories by reading modules on the slice of the model at a
chart on the chart is an equivalence. -/
instance chartModelSliceTransport_mapDerivedCategory_isEquivalence (A : SmallEtale B S hS X.1) :
    (chartModelSliceTransport B S hS X A).mapDerivedCategory.IsEquivalence :=
  Stacks.Injectives.mapDerivedCategory_isEquivalence _

/-- If `R𝓗om(P, I)` lies in `D^{≥ 0}` on `X`, then so does the derived internal Hom of the images
of `P` and `I` on the model of the small étale site. -/
theorem isGEDerivedSheafHomMap_of_isGE
    {P I : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ}
    (h : (((smallEtaleDerivedSheafHom B S hS X).obj (op (DerivedCategory.Q.obj P))).obj
      (DerivedCategory.Q.obj I)).IsGE 0) :
    RingedSite.IsGEDerivedSheafHomMap (smallEtaleModelRingedSite B S hS X.1 X.2)
      (smallEtaleModelModulesEquivalence B S hS X).functor P I := by
  let E := smallEtaleModelModulesEquivalence B S hS X
  let H := RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2)
  let M := (H.obj (op (E.functor.mapDerivedCategory.obj (DerivedCategory.Q.obj P)))).obj
    (E.functor.mapDerivedCategory.obj (DerivedCategory.Q.obj I))
  have : (((smallEtaleModelDerivedEquivalence B S hS X).inverse ⋙
      (smallEtaleModelDerivedEquivalence B S hS X).functor).obj M).IsGE 0 :=
    E.functor.isGE_obj_mapDerivedCategory _ 0 h
  have : M.IsGE 0 := DerivedCategory.TStructure.t.isGE_of_iso
    ((smallEtaleModelDerivedEquivalence B S hS X).counitIso.app M) 0
  exact DerivedCategory.TStructure.t.isGE_of_iso (X := M)
    ((H.mapIso (E.functor.mapDerivedCategoryFactors.app P).symm.op).app _ ≪≫
      (H.obj _).mapIso (E.functor.mapDerivedCategoryFactors.app I)) 0

/-- **Gluing morphisms of `D(𝒪_X)` along étale charts.** Let `P`, `I` be complexes of
`𝒪_X`-modules with `R𝓗om(P, I)` in `D^{≥ 0}`, and let `A i` be étale charts covering `X`. A family
of morphisms `P|_{A i} ⟶ I|_{A i}` of the `D(𝒪_{A i})` whose restrictions along any two morphisms
of charts `C ⟶ A i`, `C ⟶ A j` agree is the family of restrictions of a unique morphism
`P ⟶ I` of `D(𝒪_X)`. -/
theorem existsUnique_restrictQMap_chartModules_eq
    {P I : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ}
    (hPI : (((smallEtaleDerivedSheafHom B S hS X).obj (op (DerivedCategory.Q.obj P))).obj
      (DerivedCategory.Q.obj I)).IsGE 0)
    {ι : Type*} {A : ι → SmallEtale B S hS X.1} (hA : (SmallEtale.topology B S hS X.1).CoversTop A)
    (α : ∀ i, DerivedCategory.Q.obj
        (((chartModules B S hS X (A i)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
      DerivedCategory.Q.obj
        (((chartModules B S hS X (A i)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I))
    (hα : ∀ (C : SmallEtale B S hS X.1) (i j : ι) (c : C ⟶ A i) (c' : C ⟶ A j),
      Stacks.DerivedCategoryComparisons.transportQMap (chartRestrictModulesIso B S hS c) (α i) =
        Stacks.DerivedCategoryComparisons.transportQMap (chartRestrictModulesIso B S hS c') (α j)) :
    ∃! d : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj I,
      ∀ i, Stacks.DerivedCategoryComparisons.restrictQMap (chartModules B S hS X (A i)) d = α i :=
  RingedSite.existsUnique_restrictQMap_eq_of_transport (smallEtaleModelRingedSite B S hS X.1 X.2)
    (smallEtaleModelModulesEquivalence B S hS X).functor
    (smallEtaleModelEquivalence B S hS X.1).symm
    (fun A => chartModelSliceTransport B S hS X A) (fun A => chartModules B S hS X A)
    (fun A => chartModelSliceTransportIso B S hS X A) (fun c => chartRestrictModules B S hS c)
    (fun c => chartRestrictModulesIso B S hS c)
    (fun c => chartModelSliceTransportRestrictIso B S hS c)
    (fun c => chartModelSliceTransportIso_compat B S hS c)
    (hEadd := smallEtaleModelModulesEquivalence_functor_additive B S hS X)
    (hTadd := fun A => chartModelSliceTransport_additive B S hS A)
    (hRadd := fun A => chartModules_additive B S hS X A)
    (hρadd := fun c => chartRestrictModules_additive B S hS c)
    (hTpfl := fun A => chartModelSliceTransport_preservesFiniteLimits B S hS A)
    (hTpfc := fun A => chartModelSliceTransport_preservesFiniteColimits B S hS A)
    (hTfull := fun A => (chartModelSliceTransport_mapDerivedCategory_isEquivalence B S hS A).full)
    (hTfaith := fun A =>
      (chartModelSliceTransport_mapDerivedCategory_isEquivalence B S hS A).faithful)
    (isGEDerivedSheafHomMap_of_isGE B S hS hPI)
    (GrothendieckTopology.coversTop_inverse_obj (J' := smallEtaleModelTopology B S hS X.1)
      (smallEtaleModelEquivalence B S hS X.1) hA) α hα

end Gluing

end AlgebraicGeometry.Space

end
