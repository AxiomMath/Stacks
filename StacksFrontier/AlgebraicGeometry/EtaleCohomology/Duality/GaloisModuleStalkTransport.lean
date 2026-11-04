module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.StrictHenselizationStalkGalois
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BoundaryInertiaInvariantsModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PullbackStalkFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StalkComparisonNaturality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisActionStalks.GeometricPointAction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.EtaleStalkModules

/-!
# Transporting the action of automorphisms of a geometric point along stalk identifications

The Galois module of an abelian sheaf `F` on the small étale site of the spectrum of a field `K`
at a geometric point `t̄` (Stacks 04JQ) is the stalk `F_{t̄}`, and a Galois automorphism `σ`,
lifted to an automorphism `τ` of the field of `t̄`, acts on it as the map of Tag 04FN along the
automorphism `Spec τ` of `t̄` (Stacks 03QT). This file records how that map moves along the
identifications of stalks used to compute such a Galois module:

* the Galois module and the abelian stalk on the bounded site of Tag 021B
  (`Stacks.EtaleCohomology.continuousGModuleCounitAddEquiv_rho`,
  `Stacks.EtaleCohomology.etaleGaloisModuleAddEquivStalk_rho`);
* the abelian stalks of the bounded site and of Mathlib's small étale site
  (`Stacks.EtaleCohomology.pointSmallEtaleSheafFiberIsoAb_hom_naturality`);
* the abelian stalk of an inverse image, Stacks 03Q1
  (`Stacks.EtaleCohomology.smallEtalePointHom_sheafFiber_comp_smallEtaleStalkPullbackAbIso_inv`);
* the abelian stalk of the underlying abelian sheaf of a sheaf of modules
  (`Stacks.EtaleCohomology.sheafFiber_app_sheafFiberCompIso_forget₂`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] GeometricPoint.residueFieldAlgebra

/-! ### The Galois module and the abelian stalk -/

section GaloisModule

variable (B : BigEtaleSite.{u}) (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (sbar : GeometricPoint (Spec (.of K)))
  (F : Sheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{u + 1})

/-- The counit of `continuousGModuleEquivContinuousGAddCommGrp` on underlying abelian groups. -/
def continuousGModuleCounitAddEquiv {G : Type u} [Group G] [TopologicalSpace G]
    (E : ContinuousGAddCommGrp.{u, u + 1} G) :
    ((continuousGModuleEquivContinuousGAddCommGrp.{u, u + 1} G).inverse.obj E).obj.obj.V ≃+
      E.obj.obj.V :=
  Iso.addCommGroupIsoToAddEquiv ((ContinuousGAddCommGrp.forget G).mapIso
    ((continuousGModuleEquivContinuousGAddCommGrp.{u, u + 1} G).counitIso.app E))

/-- The counit of `continuousGModuleEquivContinuousGAddCommGrp` is equivariant. -/
theorem continuousGModuleCounitAddEquiv_rho {G : Type u} [Group G] [TopologicalSpace G]
    (E : ContinuousGAddCommGrp.{u, u + 1} G) (g : G)
    (v : ((continuousGModuleEquivContinuousGAddCommGrp.{u, u + 1} G).inverse.obj E).obj.obj.V) :
    continuousGModuleCounitAddEquiv E
        ((((continuousGModuleEquivContinuousGAddCommGrp.{u, u + 1} G).inverse.obj E).obj.obj.ρ
          g).hom v) =
      ConcreteCategory.hom (E.obj.obj.ρ g) (continuousGModuleCounitAddEquiv E v) :=
  ConcreteCategory.congr_hom
    (((continuousGModuleEquivContinuousGAddCommGrp.{u, u + 1} G).counitIso.hom.app E).hom.hom.comm
      g) v

/-- **The Galois action on the module of Tag 04JQ is the map of Tag 04FN on the abelian stalk**:
if `τ` extends `σ` and `a` is the automorphism `Spec τ` of the geometric point. -/
theorem etaleGaloisModuleAddEquivStalk_rho (σ : GeometricPoint.absoluteGaloisGroup sbar)
    (τ : Gal(sbar.residueField / (Spec (.of K)).residueField (sbar.hom default)))
    (hτ : ∀ a : GeometricPoint.separableClosure sbar,
      (σ a : sbar.residueField) = τ (a : sbar.residueField))
    (a : GeometricPoint.Hom sbar sbar) (ha : a.hom = Spec.map (CommRingCat.ofHom τ.toRingHom))
    (w : (etaleGaloisModule.{u, u + 1} B K hK sbar F).obj.obj.V) :
    etaleGaloisModuleAddEquivStalk.{u, u + 1} B K hK sbar F
        (ConcreteCategory.hom ((etaleGaloisModule.{u, u + 1} B K hK sbar F).obj.obj.ρ σ) w) =
      ConcreteCategory.hom ((geometricPointStalkMap B (Spec (.of K)) hK a
        AddCommGrpCat.{u + 1}).app F.obj)
        (etaleGaloisModuleAddEquivStalk.{u, u + 1} B K hK sbar F w) := by
  have hfib : PreservesColimitsOfShape (geometricPointFiber B (Spec (.of K)) hK sbar).Elementsᵒᵖ
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    forget_preservesFiberColimits.{u, u + 1} B (Spec (.of K)) hK sbar
  show ConcreteCategory.hom ((abelianEtaleStalkForgetIso.{u, u + 1} B (Spec (.of K)) hK
      sbar).hom.app F) (ConcreteCategory.hom (etaleStalkSmul.{u, u + 1} B K hK sbar
        (abelianEtaleSheafOfSets.{u, u + 1} B K hK F) σ) w) =
    ConcreteCategory.hom ((geometricPointStalkMap B (Spec (.of K)) hK a
      AddCommGrpCat.{u + 1}).app F.obj)
      (ConcreteCategory.hom ((abelianEtaleStalkForgetIso.{u, u + 1} B (Spec (.of K)) hK
        sbar).hom.app F) w)
  rw [etaleStalkSmul_eq_geometricPointStalkMap.{u, u + 1} B K hK sbar _ σ τ hτ a ha]
  have hpre := geometricPointStalkMap_preservesColimitIso B (Spec (.of K)) hK
    (CategoryTheory.forget AddCommGrpCat.{u + 1}) a F.obj
  let P := preservesColimitIso (CategoryTheory.forget AddCommGrpCat.{u + 1})
    ((CategoryOfElements.π (geometricPointFiber B (Spec (.of K)) hK sbar)).op ⋙ F.obj)
  let g := (geometricPointStalkMap B (Spec (.of K)) hK a AddCommGrpCat.{u + 1}).app F.obj
  let g' := (geometricPointStalkMap B (Spec (.of K)) hK a (Type (u + 1))).app
    (F.obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1})
  have h1 : ∀ z, ConcreteCategory.hom P.hom
      (ConcreteCategory.hom ((CategoryTheory.forget AddCommGrpCat.{u + 1}).map g) z) =
      ConcreteCategory.hom g' (ConcreteCategory.hom P.hom z) :=
    fun z => ConcreteCategory.congr_hom hpre z
  have h3 : ConcreteCategory.hom P.hom (ConcreteCategory.hom P.inv w) = w :=
    ConcreteCategory.congr_hom P.inv_hom_id w
  have h4 : ∀ z, ConcreteCategory.hom P.inv (ConcreteCategory.hom P.hom z) = z :=
    fun z => ConcreteCategory.congr_hom P.hom_inv_id z
  have h2 := h1 (ConcreteCategory.hom P.inv w)
  rw [h3] at h2
  show ConcreteCategory.hom P.inv (ConcreteCategory.hom g' w) =
    ConcreteCategory.hom ((CategoryTheory.forget AddCommGrpCat.{u + 1}).map g)
      (ConcreteCategory.hom P.inv w)
  rw [← h2]
  exact h4 _

end GaloisModule

/-! ### Abelian stalks of the two small étale sites -/

section SiteAb

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The abelian stalk at `x` of a sheaf on the bounded site, read on Mathlib's site, is its
stalk at `x`. -/
def sheafEquivFunctorSheafFiberIsoAb (x : GeometricPoint S) :
    (SmallEtale.sheafEquiv B S hS AddCommGrpCat.{u + 1}).functor ⋙
        (pointSmallEtale x.hom).sheafFiber (A := AddCommGrpCat.{u + 1}) ≅
      (geometricPointSitePoint B S hS x).sheafFiber :=
  sheafFiberIsoOfAdjOfFiberIso (geometricPointSitePoint B S hS x) (pointSmallEtale x.hom)
    (SmallEtale.toEtaleSite B S hS) (toEtaleSiteFiberIso B S hS x)
    (SmallEtale.sheafEquiv B S hS AddCommGrpCat.{u + 1}).toAdjunction

/-- The inverse of `sheafEquivFunctorSheafFiberIsoAb` sends the image in the stalk of a section
over `U` at a point `y` of the fibre to the image, in the stalk on Mathlib's site, of the
corresponding section of the sheaf transported along `SmallEtale.sheafEquiv`. -/
theorem toPresheafFiber_sheafEquivFunctorSheafFiberIsoAb_inv (x : GeometricPoint S)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u + 1})
    (U : SmallEtale B S hS) (y : (geometricPointFiber B S hS x).obj U) :
    (geometricPointSitePoint B S hS x).toPresheafFiber U y F.obj ≫
        (sheafEquivFunctorSheafFiberIsoAb B S hS x).inv.app F =
      ((SmallEtale.sheafEquiv B S hS AddCommGrpCat.{u + 1}).unit.app F).hom.app (op U) ≫
        (pointSmallEtale x.hom).toPresheafFiber ((SmallEtale.toEtaleSite B S hS).obj U)
          ((toEtaleSiteFiberIso B S hS x).inv.app U y)
          ((SmallEtale.sheafEquiv B S hS AddCommGrpCat.{u + 1}).functor.obj F).obj :=
  (congrArg ((geometricPointSitePoint B S hS x).toPresheafFiber U y F.obj ≫ ·)
      (Category.id_comp _)).symm.trans
    (toPresheafFiber_sheafFiberIsoOfAdjOfFiberIso_inv (geometricPointSitePoint B S hS x)
      (pointSmallEtale x.hom) (SmallEtale.toEtaleSite B S hS)
      (SmallEtale.sheafEquiv B S hS AddCommGrpCat.{u + 1}).toAdjunction
      (toEtaleSiteFiberIso B S hS x) F U y)

/-- Naturality of the abelian stalk comparison in the geometric point. -/
theorem sheafEquivFunctorSheafFiberIsoAb_inv_naturality {x y : GeometricPoint S}
    (a : GeometricPoint.Hom x y) (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u + 1}) :
    (sheafEquivFunctorSheafFiberIsoAb B S hS y).inv.app F ≫
        (smallEtalePointHom S a).sheafFiber.app
          ((SmallEtale.sheafEquiv B S hS AddCommGrpCat.{u + 1}).functor.obj F) =
      (geometricPointStalkMap B S hS a AddCommGrpCat.{u + 1}).app F.obj ≫
        (sheafEquivFunctorSheafFiberIsoAb B S hS x).inv.app F := by
  refine (geometricPointSitePoint B S hS y).presheafFiber_hom_ext (fun U z => ?_)
  let L := (SmallEtale.sheafEquiv B S hS AddCommGrpCat.{u + 1}).functor
  have h2 := (pointSmallEtale y.hom).toPresheafFiber_presheafFiberDesc
    (A := AddCommGrpCat.{u + 1}) (P := (L.obj F).obj)
    (fun V v => (pointSmallEtale x.hom).toPresheafFiber V
      ((smallEtalePointHom S a).hom.app V v) (L.obj F).obj)
    (fun V W g v => ((pointSmallEtale x.hom).toPresheafFiber_w g _ _).trans (by congr 1))
    ((SmallEtale.toEtaleSite B S hS).obj U) ((toEtaleSiteFiberIso B S hS y).inv.app U z)
  have hl := (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (smallEtalePointHom S a).sheafFiber.app (L.obj F))
      (toPresheafFiber_sheafEquivFunctorSheafFiberIsoAb_inv B S hS y F U z)).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h2)))
  have hr := (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (sheafEquivFunctorSheafFiberIsoAb B S hS x).inv.app F)
      (colimit.ι_pre ((CategoryOfElements.π (geometricPointFiber B S hS x)).op ⋙
        F.obj) (neighborhoodFunctor B S hS a).op (op ⟨U, z⟩))).trans
    (toPresheafFiber_sheafEquivFunctorSheafFiberIsoAb_inv B S hS x F U _))
  refine hl.trans (Eq.trans ?_ hr.symm)
  congr 2

/-- **The abelian stalk comparison of the two small étale sites, for sheaves on Mathlib's
site**: the stalk at `x` of an abelian sheaf on Mathlib's small étale site is the stalk at `x` of
its restriction to the bounded site. -/
def pointSmallEtaleSheafFiberIsoAb (x : GeometricPoint S) :
    (pointSmallEtale x.hom).sheafFiber (A := AddCommGrpCat.{u + 1}) ≅
      (SmallEtale.sheafEquiv B S hS AddCommGrpCat.{u + 1}).inverse ⋙
        (geometricPointSitePoint B S hS x).sheafFiber :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (SmallEtale.sheafEquiv B S hS AddCommGrpCat.{u + 1}).counitIso.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (sheafEquivFunctorSheafFiberIsoAb B S hS x)

/-- The component at `F` of `pointSmallEtaleSheafFiberIsoAb` is the stalk of the inverse counit
of `SmallEtale.sheafEquiv` at `F` followed by the component of
`sheafEquivFunctorSheafFiberIsoAb`. -/
theorem pointSmallEtaleSheafFiberIsoAb_hom_app (x : GeometricPoint S)
    (F : Sheaf (smallEtaleTopology S) AddCommGrpCat.{u + 1}) :
    (pointSmallEtaleSheafFiberIsoAb B S hS x).hom.app F =
      (pointSmallEtale x.hom).sheafFiber.map
          ((SmallEtale.sheafEquiv B S hS AddCommGrpCat.{u + 1}).counitIso.inv.app F) ≫
        (sheafEquivFunctorSheafFiberIsoAb B S hS x).hom.app
          ((SmallEtale.sheafEquiv B S hS AddCommGrpCat.{u + 1}).inverse.obj F) := by
  simp [pointSmallEtaleSheafFiberIsoAb]

/-- Naturality in the geometric point of `pointSmallEtaleSheafFiberIsoAb`. -/
theorem pointSmallEtaleSheafFiberIsoAb_hom_naturality {x y : GeometricPoint S}
    (a : GeometricPoint.Hom x y) (F : Sheaf (smallEtaleTopology S) AddCommGrpCat.{u + 1}) :
    (pointSmallEtaleSheafFiberIsoAb B S hS y).hom.app F ≫
        (geometricPointStalkMap B S hS a AddCommGrpCat.{u + 1}).app
          ((SmallEtale.sheafEquiv B S hS AddCommGrpCat.{u + 1}).inverse.obj F).obj =
      (smallEtalePointHom S a).sheafFiber.app F ≫
        (pointSmallEtaleSheafFiberIsoAb B S hS x).hom.app F := by
  let E := SmallEtale.sheafEquiv B S hS AddCommGrpCat.{u + 1}
  have h1 := sheafEquivFunctorSheafFiberIsoAb_inv_naturality B S hS a (E.inverse.obj F)
  have e1 := (Iso.inv_comp_eq ((sheafEquivFunctorSheafFiberIsoAb B S hS y).app
    (E.inverse.obj F))).1 h1
  have h1' := ((Iso.eq_comp_inv ((sheafEquivFunctorSheafFiberIsoAb B S hS x).app
    (E.inverse.obj F))).1 (e1.trans (Category.assoc _ _ _).symm)).symm
  have h2 := ((smallEtalePointHom S a).sheafFiber (A := AddCommGrpCat.{u + 1})).naturality
    (E.counitIso.inv.app F)
  rw [pointSmallEtaleSheafFiberIsoAb_hom_app, pointSmallEtaleSheafFiberIsoAb_hom_app]
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h1').trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h2).trans (Category.assoc _ _ _))))

end SiteAb

/-! ### The abelian stalk of an inverse image, naturally in the geometric point -/

section PullbackAb

variable {X X' : Scheme.{u}} (g : X' ⟶ X) {s t : GeometricPoint X'} (a : GeometricPoint.Hom s t)

/-- **The stalk of an inverse image of abelian sheaves is natural in the geometric point.** -/
theorem smallEtalePointHom_sheafFiber_comp_smallEtaleStalkPullbackAbIso_inv
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    (smallEtalePointHom X (a.map g)).sheafFiber.app F ≫
        (smallEtaleStalkPullbackAbIso g s.hom).inv.app F =
      (smallEtaleStalkPullbackAbIso g t.hom).inv.app F ≫
        (smallEtalePointHom X' a).sheafFiber.app ((smallEtalePullbackAb g).obj F) := by
  refine Point.presheafFiber_hom_ext _ (fun W v => ?_)
  have h₁ : (Scheme.pointSmallEtale (t.hom ≫ g)).toPresheafFiber W v F.obj ≫
      (smallEtalePointHom X (a.map g)).sheafFiber.app F =
        (Scheme.pointSmallEtale (s.hom ≫ g)).toPresheafFiber W
          ((smallEtalePointHom X (a.map g)).hom.app W v) F.obj := by
    show _ ≫ Point.presheafFiberDesc (A := AddCommGrpCat.{u + 1}) _ _ _ = _
    exact Point.toPresheafFiber_presheafFiberDesc _ _ _ _ _
  have h₂ := toPresheafFiber_comp_smallEtaleStalkPullbackAbIso_inv g s.hom F W
    ((smallEtalePointHom X (a.map g)).hom.app W v)
  have h₃ := toPresheafFiber_comp_smallEtaleStalkPullbackAbIso_inv g t.hom F W v
  have h₄ : (Scheme.pointSmallEtale t.hom).toPresheafFiber ((smallEtaleBaseChange g).obj W)
      ((pointSmallEtaleComapFiberIso g t.hom).hom.app W v)
      ((smallEtalePullbackAb g).obj F).obj ≫
        (smallEtalePointHom X' a).sheafFiber.app ((smallEtalePullbackAb g).obj F) =
      (Scheme.pointSmallEtale s.hom).toPresheafFiber ((smallEtaleBaseChange g).obj W)
        ((smallEtalePointHom X' a).hom.app ((smallEtaleBaseChange g).obj W)
          ((pointSmallEtaleComapFiberIso g t.hom).hom.app W v))
        ((smallEtalePullbackAb g).obj F).obj := by
    show _ ≫ Point.presheafFiberDesc (A := AddCommGrpCat.{u + 1}) _ _ _ = _
    exact Point.toPresheafFiber_presheafFiberDesc _ _ _ _ _
  rw [pointSmallEtaleComapFiberIso_hom_app_smallEtalePointHom] at h₂
  exact ((reassoc_of% h₁) _).trans (h₂.trans (by
    rw [← h₄]
    exact ((reassoc_of% h₃) _).symm))

end PullbackAb

/-! ### The abelian stalk of the underlying abelian sheaf of a sheaf of modules -/

section ForgetAb

variable (Λ : Type) [Ring Λ] {Y : Scheme.{u}}

/-- The forgetful functor from modules to abelian groups preserves filtered colimits indexed by
categories of the size of the small étale site. -/
instance forget₂_moduleCat_preservesFilteredColimitsOfSize_small :
    PreservesFilteredColimitsOfSize.{u, u} (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
  preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _

/-- **The comparison of the abelian stalk of the underlying abelian sheaf with the underlying
abelian group of the module stalk is natural in morphisms of points.** -/
theorem sheafFiber_app_sheafFiberCompIso_forget₂ {Φ Ψ : (smallEtaleTopology Y).Point.{u}}
    (f : Φ ⟶ Ψ) (G : Sheaf (smallEtaleTopology Y) (ModuleCat.{u + 1} Λ)) :
    (Point.Hom.sheafFiber f).app ((sheafCompose _
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G) ≫
        (Φ.sheafFiberCompIso (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).hom.app G =
      (Ψ.sheafFiberCompIso (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).hom.app G ≫
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
          ((Point.Hom.sheafFiber f).app G) := by
  refine Ψ.presheafFiber_hom_ext (fun X x => ?_)
  have h1 : Ψ.toPresheafFiber X x (G.obj ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ≫
      f.presheafFiber.app (G.obj ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) =
      Φ.toPresheafFiber X (f.hom.app X x)
        (G.obj ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) := by
    rw [Point.Hom.presheafFiber_app]
    exact Point.toPresheafFiber_presheafFiberDesc _ _ _ _ _
  have h2 : Ψ.toPresheafFiber X x G.obj ≫ f.presheafFiber.app G.obj =
      Φ.toPresheafFiber X (f.hom.app X x) G.obj := by
    rw [Point.Hom.presheafFiber_app]
    exact Point.toPresheafFiber_presheafFiberDesc _ _ _ _ _
  have h3 := Φ.toPresheafFiber_presheafFiberCompIso_hom_app
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) X (f.hom.app X x) G.obj
  have h4 := Ψ.toPresheafFiber_presheafFiberCompIso_hom_app
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) X x G.obj
  show Ψ.toPresheafFiber X x _ ≫ f.presheafFiber.app _ ≫
      ((Φ.presheafFiberCompIso (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).hom.app
        G.obj ≫ 𝟙 _) =
    Ψ.toPresheafFiber X x _ ≫ ((Ψ.presheafFiberCompIso
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).hom.app G.obj ≫ 𝟙 _) ≫
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map (f.presheafFiber.app G.obj)
  simp only [Category.comp_id]
  refine ((reassoc_of% h1) _).trans (h3.trans ?_)
  rw [← h2, Functor.map_comp, ← h4]
  exact Category.assoc _ _ _

end ForgetAb

end Stacks.EtaleCohomology

end
