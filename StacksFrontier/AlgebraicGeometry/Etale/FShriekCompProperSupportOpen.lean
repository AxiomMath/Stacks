module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekCompProperSupportIso

import StacksCore.Tactic.StacksAttribute

/-!
# The isomorphism of Stacks 0F79 and covariance with respect to open embeddings

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be as in Stacks 0F79 and let `jY : Y₁ ⟶ Y` be an open immersion,
with inverse image `jX : X₁ ⟶ X` and restriction `f₁ : X₁ ⟶ Y₁` of `f`. This file proves part
(a) of Stacks 0F79: the map `c'` is compatible with the covariance of Stacks 0F6S for `jX` and
the extension by zero of Stacks 0F53 for `jY`, the restriction of `f_! F` to `Y₁` being identified
with `f₁_!(F|_{X₁})` by the base-change isomorphism of Stacks 0F5J.

The extension by zero of Stacks 0F53 is computed on germs first
(`AlgebraicGeometry.SmallEtale.etaleGerm_openInclusionShriekMap` and
`AlgebraicGeometry.SmallEtale.etaleGerm_openInclusionShriekMap_eq_zero`): at a point of the
geometric fibre of `g` which lies on `Y₁` the germ of the extension is the germ of the section, and
at the other points it vanishes. The compatibility is then checked on the germs at the points of
the geometric fibres, where every map involved is explicit.

## Main results

* `AlgebraicGeometry.SmallEtale.sepCompShriekMap_openCovariance` — **Stacks 0F79, part (a)**.

## References

* [Stacks Project, Tag 0F79](https://stacks.math.columbia.edu/tag/0F79)
* [Stacks Project, Tag 0F53](https://stacks.math.columbia.edu/tag/0F53)
* [Stacks Project, Tag 0F6S](https://stacks.math.columbia.edu/tag/0F6S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

open scoped DirectSum

universe u v

namespace AlgebraicGeometry.SmallEtale

section OpenInclusionGerm

variable (B : BigEtaleSite.{u}) {Y₁ Y Z : B.Scheme} (j : Y₁ ⟶ Y) (g : Y ⟶ Z)
  [IsOpenImmersion (B.inclusion.map j)] [IsSeparated (B.inclusion.map g)]
  [LocallyOfFiniteType (B.inclusion.map g)]
  (H : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v})
  (s : GeometricPoint Z.obj)

/-- **The extension by zero of Stacks 0F53 on germs at the points of `Y₁`.** At a point of the
geometric fibre of `g` lying on the open `Y₁`, the germ of the extension by zero of a section of
`(j ≫ g)_!(H|_{Y₁})` is the germ of the section. -/
public theorem etaleGerm_openInclusionShriekMap (V : SmallEtale B Z.obj Z.property)
    (w : (geometricPointFiber B Z.obj Z.property s).obj V)
    (a : ((properSupportFunctor.{u, max (u + 1) v} B (j ≫ g)).obj
      ((openRestriction.{u, v} B j).obj H)).obj.obj (op V))
    (y₁ : GeometricFiberPoint B (j ≫ g) s) :
    etaleGerm B Y.obj Y.property ((openFiberPoint B j g s y₁).toGeometricPoint B g s) H.obj
        (baseChange B g V) (fiberPointElement B g s V w (openFiberPoint B j g s y₁))
        (properSupportSection B g H V
          (((openInclusionShriekMap.{u, max (u + 1) v} B j g H).val.hom.app (op V)) a)) =
      (openFiberStalkIso.{u, v} B j g H s y₁).hom
        (etaleGerm B Y₁.obj Y₁.property (y₁.toGeometricPoint B (j ≫ g) s)
          ((openRestriction.{u, v} B j).obj H).obj (baseChange B (j ≫ g) V)
          (fiberPointElement B (j ≫ g) s V w y₁)
          (properSupportSection B (j ≫ g) ((openRestriction.{u, v} B j).obj H) V a)) := by
  obtain ⟨hres, -⟩ := (openInclusionShriekMap.{u, max (u + 1) v} B j g H).property.2 V a
  let y := openFiberPoint B j g s y₁
  let x : GeometricFiberPoint B j (y.toGeometricPoint B g s) := ⟨y₁.1, rfl⟩
  let q := fiberPointElement B j (y.toGeometricPoint B g s) (baseChange B g V)
    (fiberPointElement B g s V w y) x
  have hq := etaleGerm_map B Y₁.obj Y₁.property (y₁.toGeometricPoint B (j ≫ g) s)
    ((openRestriction.{u, v} B j).obj H).obj
    ((smallEtaleBaseChange_compIso B Y₁ Y Z j g).val.hom.app V) _ q
    (fiberPointElement_compIso B j g s V w y x)
    (properSupportSection B (j ≫ g) ((openRestriction.{u, v} B j).obj H) V a)
  refine Eq.trans ?_ (congrArg (openFiberStalkIso.{u, v} B j g H s y₁).hom hq)
  simp only at hres
  refine Eq.trans ?_ (congrArg (fun z => (openFiberStalkIso.{u, v} B j g H s y₁).hom
    (etaleGerm B Y₁.obj Y₁.property (y₁.toGeometricPoint B (j ≫ g) s)
      ((openRestriction.{u, v} B j).obj H).obj _ q z)) hres.symm)
  have hp := etaleGerm_pullbackSectionAlongHom B j H (y₁.toGeometricPoint B (j ≫ g) s)
    (baseChange B g V) (fiberPointElement B g s V w y) _ q (𝟙 _)
    (by rw [CategoryTheory.Functor.map_id, Category.id_comp]
        exact fiberPointLift_comp_fst B j _ _ _ x)
    (properSupportSection B g H V
      (((openInclusionShriekMap.{u, max (u + 1) v} B j g H).val.hom.app (op V)) a))
  have hpb : pullbackSectionAlongHom B j AddCommGrpCat.{max (u + 1) v} H (baseChange B g V) _ (𝟙 _)
      (properSupportSection B g H V
        (((openInclusionShriekMap.{u, max (u + 1) v} B j g H).val.hom.app (op V)) a)) =
      (((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B Y₁.obj Y₁.property)).unit.app H).hom.app (op (baseChange B g V))
        (properSupportSection B g H V
          (((openInclusionShriekMap.{u, max (u + 1) v} B j g H).val.hom.app (op V)) a)) := by
    refine (ConcreteCategory.comp_apply _ _ _).trans ?_
    refine (ConcreteCategory.congr_hom ((((smallEtaleBaseChange B j).sheafPullback
      AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B Y₁.obj Y₁.property)).obj H).obj.map_id _) _).trans ?_
    exact ConcreteCategory.id_apply _
  rw [hpb] at hp
  exact hp.symm

/-- **The extension by zero of Stacks 0F53 vanishes off `Y₁` on germs.** At a point of the
geometric fibre of `g` which does not lie on the open `Y₁`, the germ of the extension by zero of a
section of `(j ≫ g)_!(H|_{Y₁})` is zero: the support of the extension is the image of the support
of the section, which lies in the open `Y₁ ×_Y (V ×_Z Y)`, and a geometric point of `V ×_Z Y` with
image in that open factors through it. -/
public theorem etaleGerm_openInclusionShriekMap_eq_zero (V : SmallEtale B Z.obj Z.property)
    (w : (geometricPointFiber B Z.obj Z.property s).obj V)
    (a : ((properSupportFunctor.{u, max (u + 1) v} B (j ≫ g)).obj
      ((openRestriction.{u, v} B j).obj H)).obj.obj (op V))
    (y : GeometricFiberPoint B g s) (hy : ∀ y₁, openFiberPoint B j g s y₁ ≠ y) :
    etaleGerm B Y.obj Y.property (y.toGeometricPoint B g s) H.obj
        (baseChange B g V) (fiberPointElement B g s V w y)
        (properSupportSection B g H V
          (((openInclusionShriekMap.{u, max (u + 1) v} B j g H).val.hom.app (op V)) a)) = 0 := by
  obtain ⟨-, hsupp⟩ := (openInclusionShriekMap.{u, max (u + 1) v} B j g H).property.2 V a
  refine etaleGerm_eq_zero_of_notMem_supportSection B Y.obj Y.property _ H _ _ _ fun hmem => ?_
  change (fiberPointLift B g s V w y) default ∈ _ at hmem
  obtain ⟨z, -, hz⟩ := hsupp.subset hmem
  let ℓ := fiberPointLift B g s V w y
  let fst := B.inclusion.map (pullback.fst (baseChange B g V).obj.hom j)
  have hpb := (IsPullback.of_hasPullback (baseChange B g V).obj.hom j).map B.inclusion
  have : IsOpenImmersion fst := MorphismProperty.of_isPullback hpb.flip inferInstance
  have hr : Set.range ℓ.base ⊆ Set.range fst.base := by
    rintro _ ⟨p, rfl⟩
    rw [Subsingleton.elim p default]
    exact ⟨z, hz⟩
  let r := IsOpenImmersion.lift fst ℓ hr
  have hrl : r ≫ fst = ℓ := IsOpenImmersion.lift_fac _ _ _
  have h1 : (r ≫ B.inclusion.map (pullback.snd (baseChange B g V).obj.hom j)) ≫
      B.inclusion.map j = y.1 := by
    rw [Category.assoc, ← hpb.w, ← Category.assoc, hrl]
    exact fiberPointLift_comp_snd B g s V w y
  refine hy ⟨r ≫ B.inclusion.map (pullback.snd (baseChange B g V).obj.hom j), ?_⟩
    (Subtype.ext h1)
  rw [Functor.map_comp, ← Category.assoc, h1]
  exact y.2

end OpenInclusionGerm

section Covariance

variable (B : BigEtaleSite.{u}) {X Y Z X₁ Y₁ : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  (jX : X₁ ⟶ X) (f₁ : X₁ ⟶ Y₁) (jY : Y₁ ⟶ Y)
  [IsSeparated (B.inclusion.map g)] [LocallyOfFiniteType (B.inclusion.map g)]
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyQuasiFinite (B.inclusion.map (f ≫ g))] [IsOpenImmersion (B.inclusion.map jX)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- The covariance map of Stacks 0F6S followed by `c'`, on the components of the germs at the
points of the geometric fibres. -/
public theorem fShriekStalkIso_germ_sepCompShriekMap_openCovariance (s : GeometricPoint Z.obj)
    (W : SmallEtale B Z.obj Z.property) (w : (geometricPointFiber B Z.obj Z.property s).obj W)
    (σ : ((openShriekPushforward.{u, v} B jX (f ≫ g)).obj F).obj.obj (op W))
    (y : GeometricFiberPoint B g s) (x : GeometricFiberPoint B f (y.toGeometricPoint B g s)) :
    ((fShriekStalkIso.{u, v} B f (y.toGeometricPoint B g s) F).hom
        (etaleGerm B Y.obj Y.property (y.toGeometricPoint B g s)
          ((fShriekFunctor.{u, v} B f).obj F).obj (baseChange B g W)
          (fiberPointElement B g s W w y)
          (properSupportSection B g ((fShriekFunctor.{u, v} B f).obj F) W
            ((sepCompShriekMap B f g F).hom.app (op W)
              (((openCovarianceShriekMap.{u, v} B jX (f ≫ g)).app F).hom.app (op W) σ)))) :
        fiberStalks.{u, max (u + 1) v} B f _ F) x =
      ((openCovarianceFiberStalksMap B jX (f ≫ g) F s)
        ((fShriekStalkIso.{u, v} B (jX ≫ f ≫ g) s ((openRestriction.{u, v} B jX).obj F)).hom
          (etaleGerm B Z.obj Z.property s
            ((openShriekPushforward.{u, v} B jX (f ≫ g)).obj F).obj W w σ)) :
        fiberStalks.{u, max (u + 1) v} B (f ≫ g) s F) (compFiberPointOf B f g s y x) := by
  refine (isSepCompMap_sepCompShriekMap B f g F s W w _ y x).trans ?_
  refine congrArg (fun m => (m : fiberStalks.{u, max (u + 1) v} B (f ≫ g) s F)
    (compFiberPointOf B f g s y x)) ?_
  have h1 := colim_map_etaleGerm B s ((openCovarianceShriekMap.{u, v} B jX (f ≫ g)).app F).hom W w σ
  refine (congrArg (fShriekStalkIso.{u, v} B (f ≫ g) s F).hom h1.symm).trans ?_
  change _ = (fShriekStalkIso.{u, v} B (f ≫ g) s F).hom
    (((geometricPointSitePoint B Z.obj Z.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).map
          ((openCovarianceShriekMap.{u, v} B jX (f ≫ g)).app F)
      ((fShriekStalkIso.{u, v} B (jX ≫ f ≫ g) s ((openRestriction.{u, v} B jX).obj F)).inv
        ((fShriekStalkIso.{u, v} B (jX ≫ f ≫ g) s ((openRestriction.{u, v} B jX).obj F)).hom
          (etaleGerm B Z.obj Z.property s
            ((openShriekPushforward.{u, v} B jX (f ≫ g)).obj F).obj W w σ))))
  rw [Iso.hom_inv_id_apply]
  rfl

end Covariance

section BaseChangeGerm

variable (B : BigEtaleSite.{u}) {X Y Z X₁ Y₁ : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  (jX : X₁ ⟶ X) (f₁ : X₁ ⟶ Y₁) (jY : Y₁ ⟶ Y) (sq : IsPullback jX f₁ f jY)
  [IsSeparated (B.inclusion.map g)] [LocallyOfFiniteType (B.inclusion.map g)]
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map f₁)] [LocallyQuasiFinite (B.inclusion.map f₁)]
  [IsOpenImmersion (B.inclusion.map jY)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})

/-- The extension by zero of Stacks 0F53 of the image of a section of `(jY ≫ g)_!(f₁_! F|_{X₁})`
under the base-change isomorphism of Stacks 0F5J, on the components of the germs at the points of
the geometric fibres lying over `Y₁`. -/
public theorem fShriekStalkIso_germ_openInclusionShriekMap_baseChange (s : GeometricPoint Z.obj)
    (W : SmallEtale B Z.obj Z.property) (w : (geometricPointFiber B Z.obj Z.property s).obj W)
    (τ : ((properSupportFunctor.{u, u + 1} B (jY ≫ g)).obj
      ((fShriekFunctor.{u, u + 1} B f₁).obj ((abPullback.{u, u + 1} B jX).obj F))).obj.obj (op W))
    (y₁ : GeometricFiberPoint B (jY ≫ g) s)
    (x₁ : GeometricFiberPoint B f₁ (y₁.toGeometricPoint B (jY ≫ g) s)) :
    ((fShriekStalkIso.{u, u + 1} B f ((openFiberPoint B jY g s y₁).toGeometricPoint B g s) F).hom
        (etaleGerm B Y.obj Y.property ((openFiberPoint B jY g s y₁).toGeometricPoint B g s)
          ((fShriekFunctor.{u, u + 1} B f).obj F).obj (baseChange B g W)
          (fiberPointElement B g s W w (openFiberPoint B jY g s y₁))
          (properSupportSection B g ((fShriekFunctor.{u, u + 1} B f).obj F) W
            (((openInclusionShriekMap.{u, u + 1} B jY g
              ((fShriekFunctor.{u, u + 1} B f).obj F)).val.hom.app (op W))
              (((properSupportFunctor.{u, u + 1} B (jY ≫ g)).map
                ((fShriekBaseChangeNatIso.{u} B jX f₁ f jY sq).inv.app F)).hom.app (op W) τ)))) :
        fiberStalks.{u, u + 1} B f _ F) (fiberPointBaseChange B jX f₁ f jY sq _ x₁) =
      (etaleStalkSmallEtalePullObjIso B jX (x₁.toGeometricPoint B f₁ _)
          AddCommGrpCat.{u + 1} F).hom
        (((fShriekStalkIso.{u, u + 1} B f₁ (y₁.toGeometricPoint B (jY ≫ g) s)
          ((abPullback.{u, u + 1} B jX).obj F)).hom
          (etaleGerm B Y₁.obj Y₁.property (y₁.toGeometricPoint B (jY ≫ g) s)
            ((fShriekFunctor.{u, u + 1} B f₁).obj ((abPullback.{u, u + 1} B jX).obj F)).obj
            (baseChange B (jY ≫ g) W) (fiberPointElement B (jY ≫ g) s W w y₁)
            (properSupportSection B (jY ≫ g) _ W τ)) :
          fiberStalks.{u, u + 1} B f₁ _ _) x₁) := by
  let t := y₁.toGeometricPoint B (jY ≫ g) s
  let γ := fShriekBaseChangeNatIso.{u} B jX f₁ f jY sq
  let G₁ := (fShriekFunctor.{u, u + 1} B f₁).obj ((abPullback.{u, u + 1} B jX).obj F)
  let z := properSupportSection B (jY ≫ g) G₁ W τ
  let Zg := etaleGerm B Y₁.obj Y₁.property t G₁.obj (baseChange B (jY ≫ g) W)
    (fiberPointElement B (jY ≫ g) s W w y₁) z
  let φ := (etaleStalkPresheafFunctor B Y₁.obj Y₁.property t AddCommGrpCat.{u + 1}).map
    (γ.inv.app F).hom
  have h1 := etaleGerm_openInclusionShriekMap.{u, u + 1} B jY g
    ((fShriekFunctor.{u, u + 1} B f).obj F) s W w
    (((properSupportFunctor.{u, u + 1} B (jY ≫ g)).map (γ.inv.app F)).hom.app (op W) τ) y₁
  have h2 : properSupportSection B (jY ≫ g)
      ((openRestriction.{u, u + 1} B jY).obj ((fShriekFunctor.{u, u + 1} B f).obj F)) W
      (((properSupportFunctor.{u, u + 1} B (jY ≫ g)).map (γ.inv.app F)).hom.app (op W) τ) =
      (γ.inv.app F).hom.app (op (baseChange B (jY ≫ g) W)) z :=
    properSupportSection_map B (jY ≫ g) (γ.inv.app F) W τ
  have h3 : etaleGerm B Y₁.obj Y₁.property t
      ((openRestriction.{u, u + 1} B jY).obj ((fShriekFunctor.{u, u + 1} B f).obj F)).obj
      (baseChange B (jY ≫ g) W) (fiberPointElement B (jY ≫ g) s W w y₁)
      ((γ.inv.app F).hom.app (op (baseChange B (jY ≫ g) W)) z) = φ Zg :=
    (colim_map_etaleGerm.{u, u + 1} B t (γ.inv.app F).hom _ _ z).symm
  have hst := ConcreteCategory.congr_hom (fShriekBaseChangeNatIso_stalk.{u} B jX f₁ f jY sq t F)
    (φ Zg)
  have hid : (etaleStalkPresheafFunctor B Y₁.obj Y₁.property t AddCommGrpCat.{u + 1}).map
      (γ.hom.app F).hom (φ Zg) = Zg := by
    have e : (γ.inv.app F).hom ≫ (γ.hom.app F).hom = 𝟙 _ :=
      congrArg (fun k => k.hom) (γ.inv_hom_id_app F)
    have e2 := congrArg (etaleStalkPresheafFunctor B Y₁.obj Y₁.property t
      AddCommGrpCat.{u + 1}).map e
    rw [Functor.map_comp, CategoryTheory.Functor.map_id] at e2
    exact (ConcreteCategory.comp_apply _ _ _).symm.trans
      ((ConcreteCategory.congr_hom e2 Zg).trans (ConcreteCategory.id_apply _))
  replace hst : (fShriekStalkIso.{u, u + 1} B f₁ t ((abPullback.{u, u + 1} B jX).obj F)).hom Zg =
      fiberStalksBaseChangeEquiv.{u, u + 1} B jX f₁ f jY sq t F
        ((fShriekStalkIso.{u, u + 1} B f (t.map (B.inclusion.map jY)) F).hom
          ((etaleStalkSmallEtalePullObjIso B jY t AddCommGrpCat.{u + 1}
            ((fShriekFunctor.{u, u + 1} B f).obj F)).hom (φ Zg))) := by
    calc _ = (fShriekStalkIso.{u, u + 1} B f₁ t ((abPullback.{u, u + 1} B jX).obj F)).hom
          ((etaleStalkPresheafFunctor B Y₁.obj Y₁.property t AddCommGrpCat.{u + 1}).map
            (γ.hom.app F).hom (φ Zg)) := by rw [hid]
      _ = _ := hst
  have hx := congrArg (fun m => (m : fiberStalks.{u, u + 1} B f₁ t _) x₁) hst
  simp only at hx
  rw [fiberStalksBaseChangeEquiv_apply.{u, u + 1}] at hx
  refine Eq.trans ?_ (congrArg (etaleStalkSmallEtalePullObjIso B jX (x₁.toGeometricPoint B f₁ t)
    AddCommGrpCat.{u + 1} F).hom hx.symm)
  refine Eq.trans ?_ (Iso.inv_hom_id_apply (etaleStalkSmallEtalePullObjIso B jX
    (x₁.toGeometricPoint B f₁ t) AddCommGrpCat.{u + 1} F) _).symm
  have hg : etaleGerm B Y.obj Y.property ((openFiberPoint B jY g s y₁).toGeometricPoint B g s)
      ((fShriekFunctor.{u, u + 1} B f).obj F).obj (baseChange B g W)
      (fiberPointElement B g s W w (openFiberPoint B jY g s y₁))
      (properSupportSection B g ((fShriekFunctor.{u, u + 1} B f).obj F) W
        (((openInclusionShriekMap.{u, u + 1} B jY g
          ((fShriekFunctor.{u, u + 1} B f).obj F)).val.hom.app (op W))
          (((properSupportFunctor.{u, u + 1} B (jY ≫ g)).map (γ.inv.app F)).hom.app (op W) τ))) =
      (etaleStalkSmallEtalePullObjIso B jY t AddCommGrpCat.{u + 1}
        ((fShriekFunctor.{u, u + 1} B f).obj F)).hom (φ Zg) :=
    h1.trans (congrArg (etaleStalkSmallEtalePullObjIso B jY t AddCommGrpCat.{u + 1}
      ((fShriekFunctor.{u, u + 1} B f).obj F)).hom
      ((congrArg (etaleGerm B Y₁.obj Y₁.property t
        ((openRestriction.{u, u + 1} B jY).obj ((fShriekFunctor.{u, u + 1} B f).obj F)).obj
        (baseChange B (jY ≫ g) W) (fiberPointElement B (jY ≫ g) s W w y₁)) h2).trans h3))
  exact congrArg (fun m => ((fShriekStalkIso.{u, u + 1} B f (t.map (B.inclusion.map jY)) F).hom m :
    fiberStalks.{u, u + 1} B f _ F) (fiberPointBaseChange B jX f₁ f jY sq t x₁)) hg

end BaseChangeGerm

section PartA

variable (B : BigEtaleSite.{u}) {X Y Z X₁ Y₁ : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  (jX : X₁ ⟶ X) (f₁ : X₁ ⟶ Y₁) (jY : Y₁ ⟶ Y) (sq : IsPullback jX f₁ f jY)
  [IsSeparated (B.inclusion.map g)] [LocallyOfFiniteType (B.inclusion.map g)]
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyQuasiFinite (B.inclusion.map (f ≫ g))] [IsOpenImmersion (B.inclusion.map jY)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})

/-- Part (a) of Stacks 0F79, with the finiteness and separation conditions on the restricted
morphisms supplied as instances. -/
public theorem sepCompShriekMap_openCovariance_of_instances [IsOpenImmersion (B.inclusion.map jX)]
    [LocallyOfFiniteType (B.inclusion.map f₁)] [LocallyQuasiFinite (B.inclusion.map f₁)]
    [IsSeparated (B.inclusion.map (jY ≫ g))] [LocallyOfFiniteType (B.inclusion.map (jY ≫ g))]
    [LocallyQuasiFinite (B.inclusion.map (f₁ ≫ jY ≫ g))] (hcomp : jX ≫ f ≫ g = f₁ ≫ jY ≫ g) :
    (openCovarianceShriekMap.{u, u + 1} B jX (f ≫ g)).app F ≫ sepCompShriekMap.{u, u + 1} B f g F =
      eqToHom (congrArg (fun G => G.obj ((openRestriction.{u, u + 1} B jX).obj F))
        (fShriekFunctor_congr.{u, u + 1} B hcomp)) ≫
      sepCompShriekMap.{u, u + 1} B f₁ (jY ≫ g) ((openRestriction.{u, u + 1} B jX).obj F) ≫
      (properSupportFunctor.{u, u + 1} B (jY ≫ g)).map
        ((fShriekBaseChangeNatIso.{u} B jX f₁ f jY sq).inv.app F) ≫
      (openInclusionShriekMap.{u, u + 1} B jY g ((fShriekFunctor.{u, u + 1} B f).obj F)).val := by
  let e : (fShriekFunctor.{u, u + 1} B (jX ≫ f ≫ g)).obj ((openRestriction.{u, u + 1} B jX).obj F) ⟶
      (fShriekFunctor.{u, u + 1} B (f₁ ≫ jY ≫ g)).obj ((openRestriction.{u, u + 1} B jX).obj F) :=
    eqToHom (congrArg (fun G => G.obj ((openRestriction.{u, u + 1} B jX).obj F))
      (fShriekFunctor_congr.{u, u + 1} B hcomp))
  refine properSupportFunctor_hom_ext.{u, u + 1} B g _ fun s W w σ y => ?_
  refine (AddCommGrpCat.mono_iff_injective (fShriekStalkIso.{u, u + 1} B f
    (y.toGeometricPoint B g s) F).hom).1 inferInstance (DFinsupp.ext fun x => ?_)
  refine Eq.trans (fShriekStalkIso_germ_sepCompShriekMap_openCovariance.{u, u + 1} B f g jX F
    s W w σ y x) ?_
  by_cases hy : ∃ y₁, openFiberPoint B jY g s y₁ = y
  · obtain ⟨y₁, rfl⟩ := hy
    obtain ⟨x₁, rfl⟩ := (fiberPointBaseChange_bijective B jX f₁ f jY sq
      (y₁.toGeometricPoint B (jY ≫ g) s)).2 x
    let x₁' : GeometricFiberPoint B (jX ≫ f ≫ g) s := ⟨x₁.1, by
      rw [hcomp, Functor.map_comp, Functor.map_comp, ← Category.assoc, x₁.2]
      exact y₁.2⟩
    refine (openCovarianceFiberStalksMap_apply.{u, u + 1} B jX (f ≫ g) F s _ x₁').trans ?_
    let σ' := e.hom.app (op W) σ
    refine Eq.trans ?_ (fShriekStalkIso_germ_openInclusionShriekMap_baseChange B f g jX f₁ jY sq F
      s W w ((sepCompShriekMap.{u, u + 1} B f₁ (jY ≫ g)
        ((openRestriction.{u, u + 1} B jX).obj F)).hom.app (op W) σ') y₁ x₁).symm
    refine Eq.trans ?_ (congrArg (etaleStalkSmallEtalePullObjIso B jX _ AddCommGrpCat.{u + 1} F).hom
      (isSepCompMap_sepCompShriekMap.{u, u + 1} B f₁ (jY ≫ g)
        ((openRestriction.{u, u + 1} B jX).obj F)
        s W w σ' y₁ x₁).symm)
    have hc := ConcreteCategory.congr_hom (fShriekStalkIso_congr.{u, u + 1} B hcomp s
      ((openRestriction.{u, u + 1} B jX).obj F))
      (etaleGerm B Z.obj Z.property s
        ((openShriekPushforward.{u, u + 1} B jX (f ≫ g)).obj F).obj W w σ)
    have hm := colim_map_etaleGerm.{u, u + 1} B s e.hom W w σ
    have hc' : (fShriekStalkIso.{u, u + 1} B (f₁ ≫ jY ≫ g) s
        ((openRestriction.{u, u + 1} B jX).obj F)).hom
        (etaleGerm B Z.obj Z.property s
          ((fShriekFunctor.{u, u + 1} B (f₁ ≫ jY ≫ g)).obj
            ((openRestriction.{u, u + 1} B jX).obj F)).obj W w σ') =
        DirectSum.equivCongrLeft (geometricFiberPointCongr B hcomp s)
          ((fShriekStalkIso.{u, u + 1} B (jX ≫ f ≫ g) s
            ((openRestriction.{u, u + 1} B jX).obj F)).hom
            (etaleGerm B Z.obj Z.property s
              ((openShriekPushforward.{u, u + 1} B jX (f ≫ g)).obj F).obj W w σ)) :=
      (congrArg _ hm.symm).trans hc
    rw [hc']
    rfl
  · have hx : ∀ x₁' : GeometricFiberPoint B (jX ≫ f ≫ g) s,
        openFiberPoint B jX (f ≫ g) s x₁' ≠ compFiberPointOf B f g s y x := by
      intro x₁' he
      have hxv : x.1 = x₁'.1 ≫ B.inclusion.map jX := (congrArg Subtype.val he).symm
      refine hy ⟨⟨x₁'.1 ≫ B.inclusion.map f₁, ?_⟩, Subtype.ext ?_⟩
      · rw [Category.assoc, ← Functor.map_comp, ← hcomp]
        exact x₁'.2
      · change (x₁'.1 ≫ B.inclusion.map f₁) ≫ B.inclusion.map jY = y.1
        have hw : B.inclusion.map jX ≫ B.inclusion.map f =
            B.inclusion.map f₁ ≫ B.inclusion.map jY := by
          rw [← Functor.map_comp, ← Functor.map_comp, sq.w]
        exact (Category.assoc _ _ _).trans ((congrArg (x₁'.1 ≫ ·) hw.symm).trans
          ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ B.inclusion.map f) hxv.symm).trans
            x.2)))
    rw [openCovarianceFiberStalksMap_apply_eq_zero.{u, u + 1} B jX (f ≫ g) F s _ _ hx]
    have h0 := etaleGerm_openInclusionShriekMap_eq_zero.{u, u + 1} B jY g
      ((fShriekFunctor.{u, u + 1} B f).obj F) s W w
      (((properSupportFunctor.{u, u + 1} B (jY ≫ g)).map
        ((fShriekBaseChangeNatIso.{u} B jX f₁ f jY sq).inv.app F)).hom.app (op W)
        ((sepCompShriekMap.{u, u + 1} B f₁ (jY ≫ g)
          ((openRestriction.{u, u + 1} B jX).obj F)).hom.app (op W)
          (e.hom.app (op W) σ))) y
      (fun y₁ hy₁ => hy ⟨y₁, hy₁⟩)
    refine Eq.trans ?_ (congrArg (fun m => ((fShriekStalkIso.{u, u + 1} B f
      (y.toGeometricPoint B g s) F).hom m : fiberStalks.{u, u + 1} B f _ F) x) h0).symm
    rw [map_zero]
    rfl

/-- **Stacks 0F79, part (a).** Let `f : X ⟶ Y` and `g : Y ⟶ Z` be as in Stacks 0F79, let
`jY : Y₁ ⟶ Y` be an open immersion, and let `X₁ = X ×_Y Y₁` with projections `jX : X₁ ⟶ X` and
`f₁ : X₁ ⟶ Y₁`. Then the isomorphism `c'` of Stacks 0F79 is compatible with covariance with
respect to open embeddings: the composite of the covariance map
`(jX ≫ f ≫ g)_!(F|_{X₁}) ⟶ (f ≫ g)_! F` of Stacks 0F6S with `c' : (f ≫ g)_! F ⟶ g_!(f_! F)`
equals the composite of `c'` for `f₁` and `jY ≫ g`,
`(f₁ ≫ jY ≫ g)_!(F|_{X₁}) ⟶ (jY ≫ g)_!(f₁_!(F|_{X₁}))`, the identification
`f₁_!(F|_{X₁}) ≅ (f_! F)|_{Y₁}` of Stacks 0F5J ("the construction of `f_!` is local on the base")
and the extension by zero `(jY ≫ g)_!((f_! F)|_{Y₁}) ⟶ g_!(f_! F)` of Stacks 0F53. -/
@[stacks 0F79 "part (a), compatibility with covariance for open embeddings, Remarks 0F53, 0F6S"]
public theorem sepCompShriekMap_openCovariance :
    letI : IsOpenImmersion (B.inclusion.map jX) :=
      MorphismProperty.of_isPullback (sq.flip.map B.inclusion) inferInstance
    letI := locallyOfFiniteType_of_isPullback B jX f₁ f jY sq
    letI := locallyQuasiFinite_of_isPullback B jX f₁ f jY sq
    letI : IsSeparated (B.inclusion.map (jY ≫ g)) := by
      rw [Functor.map_comp]
      infer_instance
    letI : LocallyQuasiFinite (B.inclusion.map (f₁ ≫ jY ≫ g)) := by
      rw [show f₁ ≫ jY ≫ g = jX ≫ f ≫ g by rw [← Category.assoc, ← sq.w, Category.assoc]]
      infer_instance
    (openCovarianceShriekMap.{u, u + 1} B jX (f ≫ g)).app F ≫ sepCompShriekMap.{u, u + 1} B f g F =
      eqToHom (congrArg (fun G => G.obj ((openRestriction.{u, u + 1} B jX).obj F))
        (fShriekFunctor_congr.{u, u + 1} B
          (show jX ≫ f ≫ g = f₁ ≫ jY ≫ g by rw [← Category.assoc, sq.w, Category.assoc]))) ≫
      sepCompShriekMap.{u, u + 1} B f₁ (jY ≫ g) ((openRestriction.{u, u + 1} B jX).obj F) ≫
      (properSupportFunctor.{u, u + 1} B (jY ≫ g)).map
        ((fShriekBaseChangeNatIso.{u} B jX f₁ f jY sq).inv.app F) ≫
      (openInclusionShriekMap.{u, u + 1} B jY g ((fShriekFunctor.{u, u + 1} B f).obj F)).val := by
  have hcomp : jX ≫ f ≫ g = f₁ ≫ jY ≫ g := by rw [← Category.assoc, sq.w, Category.assoc]
  have : IsOpenImmersion (B.inclusion.map jX) :=
    MorphismProperty.of_isPullback (sq.flip.map B.inclusion) inferInstance
  have := locallyOfFiniteType_of_isPullback B jX f₁ f jY sq
  have := locallyQuasiFinite_of_isPullback B jX f₁ f jY sq
  have : IsSeparated (B.inclusion.map (jY ≫ g)) := by
    rw [Functor.map_comp]
    infer_instance
  have : LocallyQuasiFinite (B.inclusion.map (f₁ ≫ jY ≫ g)) := by
    rw [← hcomp]
    infer_instance
  exact sepCompShriekMap_openCovariance_of_instances B f g jX f₁ jY sq F hcomp

end PartA

end AlgebraicGeometry.SmallEtale

end
