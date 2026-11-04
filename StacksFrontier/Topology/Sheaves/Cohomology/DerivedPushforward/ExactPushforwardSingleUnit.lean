module

public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit
public import StacksFrontier.CategoryTheory.Localization.MapHomotopyCategoryAdjunctionCounit
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ExactPushforwardSingle

/-!
# The derived unit at a module placed in degree zero, along an exact direct image

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces along which `f_*` is exact, and let
`F` be an `𝒪_Y`-module. The unit of `Lf^* ⊣ Rf_*` at `F[0]`, followed by `Rf_*` of the comparison
`Lf^*(F[0]) ⟶ (f^*F)[0]` of the derived with the ordinary pullback, is the unit of `f^* ⊣ f_*` at
`F` placed in degree zero, followed by the isomorphism `(f_* f^* F)[0] ≅ Rf_*((f^*F)[0])` of
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardSingleIso`.

## Main definitions

* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackSingleComparison`: the
  comparison `Lf^*(F[0]) ⟶ (f^*F)[0]`.

## Main results

* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_unit_app_single_comp`:
  the compatibility of the two units.
* `CategoryTheory.Adjunction.singleFunctor_map_unit_comp_mapHomotopyCategorySingleFunctorIso_inv`:
  the same compatibility on homotopy categories, for an arbitrary adjunction of additive functors.

## Implementation notes

The derived unit is read on the homotopy category by
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_unit_fac`; what is left is a
naturality chase, carried out in bare categories
(`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.unit_comp_singleComparison_of_fac`) because on
the ringed-space functors a single rewrite exhausts the heartbeat budget, and the homotopy-level
identity above, which is
`CategoryTheory.Adjunction.mapHomologicalComplexAdjunction_unit_app_single` read through the
quotient.

The comparison is defined with the body used by the level transition maps of
[Stacks, Tag 0CTE]: through `DerivedCategory.singleFunctorIsoCompQ`,
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans` and the commutation
`HomologicalComplex.singleMapHomologicalComplex` of `StacksDraft.KFlat.modulePullback` with
`(-)[0]`. It lives at the standard model `HasDerivedCategory.standard`, the model of
`derivedPullbackNatTrans`, installed for each declaration only.

## References

* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0CTE](https://stacks.math.columbia.edu/tag/0CTE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

-- Sheafification on the opens of a space is the instance of the small site here, as in the files
-- of the derived functors this is compared with; the instance for enlarged coefficients would make
-- the derived categories built from it differ by unfolding.
attribute [-instance] Stacks.Cohomology.SpectralLimit.hasSheafifyOpensMax

namespace CategoryTheory.Adjunction

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]

/-- **The unit on homotopy categories at a single complex.** For an adjunction `G ⊣ F` of
additive functors, the unit at `M` placed in degree `0`, followed by the commutation of `F` with
`(-)[0]`, is the unit of the induced adjunction on homotopy categories at `M[0]` followed by `F`
of the commutation of `G` with `(-)[0]`. -/
theorem singleFunctor_map_unit_comp_mapHomotopyCategorySingleFunctorIso_inv (adj : G ⊣ F)
    (M : B) :
    (HomotopyCategory.singleFunctor B 0).map (adj.unit.app M) ≫
        (F.mapHomotopyCategorySingleFunctorIso 0).inv.app (G.obj M) =
      (mapHomotopyCategoryAdjunction adj (ComplexShape.up ℤ)).unit.app
          ((HomotopyCategory.singleFunctor B 0).obj M) ≫
        (F.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((G.mapHomotopyCategorySingleFunctorIso 0).hom.app M) := by
  have hu := mapHomologicalComplexAdjunction_unit_app_single adj (ComplexShape.up ℤ) 0 M
  have hcx : (HomologicalComplex.single B (ComplexShape.up ℤ) 0).map (adj.unit.app M) ≫
      (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app (G.obj M) =
      (mapHomologicalComplexAdjunction adj (ComplexShape.up ℤ)).unit.app
          ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj M) ≫
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).hom.app M) :=
    (Iso.comp_inv_eq ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ)
      0).app (G.obj M))).2 (hu.symm.trans (Category.assoc _ _ _).symm)
  have hI : (G.mapHomotopyCategorySingleFunctorIso 0).hom.app M =
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).hom.app M) :=
    (Iso.inv_eq_inv ((G.mapHomotopyCategorySingleFunctorIso 0).app M)
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).app M))).1
      (G.mapHomotopyCategorySingleFunctorIso_inv_app 0 M)
  have hq := congrArg (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map hcx
  rw [Functor.map_comp, Functor.map_comp, ← Functor.mapHomotopyCategory_map] at hq
  refine (congrArg (_ ≫ ·) (F.mapHomotopyCategorySingleFunctorIso_inv_app 0 (G.obj M))).trans
    (hq.trans ?_)
  exact congrArg (fun t => _ ≫ (F.mapHomotopyCategory (ComplexShape.up ℤ)).map t)
    hI.symm

end CategoryTheory.Adjunction

namespace Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

noncomputable section

section Abstract

variable {AY AX HY HX DY DX : Type*} [Category* AY] [Category* AX] [Category* HY] [Category* HX]
  [Category* DY] [Category* DX]
  {P : AY ⥤ AX} {Pst : AX ⥤ AY} {HsY : AY ⥤ HY} {HsX : AX ⥤ HX} {QhY : HY ⥤ DY} {QhX : HX ⥤ DX}
  {SY : AY ⥤ DY} {SX : AX ⥤ DX} {MP : HY ⥤ HX} {MPst : HX ⥤ HY} {Lf : DY ⥤ DX} {Rf : DX ⥤ DY}

/-- **The chase behind `derivedAdjunction_unit_app_single_comp`, in bare categories.** Let
`adj : Lf ⊣ Rf` be a derived adjunction whose unit, read on homotopy categories through the
comparisons `c` and `u`, is the unit of `hadj : MP ⊣ MPst` (`hunit`), and let the unit of `hadj` at
`F[0]` be the unit of `madj : P ⊣ Pst` at `F` placed in degree `0` (`hH`). Then the derived unit at
`F[0]`, followed by `Rf` of the comparison `Lf(F[0]) ⟶ (PF)[0]`, is `(-)[0]` of the unit of `madj`
followed by the isomorphism `(Pst P F)[0] ≅ Rf((PF)[0])`. -/
theorem unit_comp_singleComparison_of_fac (adj : Lf ⊣ Rf) (madj : P ⊣ Pst) (hadj : MP ⊣ MPst)
    (c : QhY ⋙ Lf ⟶ MP ⋙ QhX) (u : MPst ⋙ QhY ⟶ QhX ⋙ Rf)
    (σY : SY ≅ HsY ⋙ QhY) (σX : SX ≅ HsX ⋙ QhX)
    (hsP : HsY ⋙ MP ≅ P ⋙ HsX) (hsPst : HsX ⋙ MPst ≅ Pst ⋙ HsY) (F : AY)
    (hunit : adj.unit.app (QhY.obj (HsY.obj F)) ≫ Rf.map (c.app (HsY.obj F)) =
      QhY.map (hadj.unit.app (HsY.obj F)) ≫ u.app (MP.obj (HsY.obj F)))
    (hH : HsY.map (madj.unit.app F) ≫ hsPst.inv.app (P.obj F) =
      hadj.unit.app (HsY.obj F) ≫ MPst.map (hsP.hom.app F)) :
    adj.unit.app (SY.obj F) ≫ Rf.map (Lf.map (σY.hom.app F) ≫ c.app (HsY.obj F) ≫
        QhX.map (hsP.hom.app F) ≫ σX.inv.app (P.obj F)) =
      SY.map (madj.unit.app F) ≫ (σY.hom.app (Pst.obj (P.obj F)) ≫
        QhY.map (hsPst.inv.app (P.obj F)) ≫ u.app (HsX.obj (P.obj F)) ≫
          Rf.map (σX.inv.app (P.obj F))) := by
  have n1 := adj.unit.naturality (σY.hom.app F)
  have n2 := u.naturality (hsP.hom.app F)
  have n3 := σY.hom.naturality (madj.unit.app F)
  simp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj] at n1 n2 n3
  have hQ : QhY.map (hadj.unit.app (HsY.obj F)) ≫ QhY.map (MPst.map (hsP.hom.app F)) =
      QhY.map (HsY.map (madj.unit.app F)) ≫ QhY.map (hsPst.inv.app (P.obj F)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hH]
  simp only [Functor.map_comp]
  rw [← reassoc_of% n1, reassoc_of% hunit, ← reassoc_of% n2, reassoc_of% n3, reassoc_of% hQ]

/-- **The comparison `Lf(F[0]) ⟶ (PF)[0]` read on homotopy categories, in bare categories.** The
comparison built on complexes, from `τ : S ≅ single ⋙ Q`, `ν : Q ⋙ Lf ⟶ CP ⋙ Q` and the commutation
`smP` of `P` with `single`, is the comparison built on homotopy categories, from
`σ : S ≅ Hs ⋙ Qh`, `c : Qh ⋙ Lf ⟶ MP ⋙ Qh` and the commutation `hsP` of `P` with `Hs`, as soon as
the pieces are related through `q : quot ⋙ Qh ≅ Q` and `e : single ⋙ quot ≅ Hs`. -/
theorem singleComparison_eq_of_fac {CY CX : Type*} [Category* CY] [Category* CX]
    {singY : AY ⥤ CY} {singX : AX ⥤ CX} {quotY : CY ⥤ HY} {quotX : CX ⥤ HX}
    {QY : CY ⥤ DY} {QX : CX ⥤ DX} {CP : CY ⥤ CX}
    (τY : SY ≅ singY ⋙ QY) (τX : SX ≅ singX ⋙ QX) (qY : quotY ⋙ QhY ≅ QY)
    (qX : quotX ⋙ QhX ≅ QX) (σY : SY ≅ HsY ⋙ QhY) (σX : SX ≅ HsX ⋙ QhX)
    (eY : singY ⋙ quotY ≅ HsY) (eX : singX ⋙ quotX ≅ HsX)
    (ν : QY ⋙ Lf ⟶ CP ⋙ QX) (c : QhY ⋙ Lf ⟶ MP ⋙ QhX) (fac : quotY ⋙ MP ≅ CP ⋙ quotX)
    (smP : singY ⋙ CP ≅ P ⋙ singX) (hsP : HsY ⋙ MP ≅ P ⋙ HsX) (F : AY)
    (hν : ν.app (singY.obj F) = Lf.map (qY.inv.app (singY.obj F)) ≫
      c.app (quotY.obj (singY.obj F)) ≫ QhX.map (fac.hom.app (singY.obj F)) ≫
        qX.hom.app (CP.obj (singY.obj F)))
    (hσY : σY.hom.app F ≫ QhY.map (eY.inv.app F) = τY.hom.app F ≫ qY.inv.app (singY.obj F))
    (hσX : QhX.map (eX.hom.app (P.obj F)) ≫ σX.inv.app (P.obj F) =
      qX.hom.app (singX.obj (P.obj F)) ≫ τX.inv.app (P.obj F))
    (hhs : MP.map (eY.inv.app F) ≫ fac.hom.app (singY.obj F) ≫ quotX.map (smP.hom.app F) ≫
      eX.hom.app (P.obj F) = hsP.hom.app F) :
    Lf.map (τY.hom.app F) ≫ ν.app (singY.obj F) ≫ QX.map (smP.hom.app F) ≫
        τX.inv.app (P.obj F) =
      Lf.map (σY.hom.app F) ≫ c.app (HsY.obj F) ≫ QhX.map (hsP.hom.app F) ≫
        σX.inv.app (P.obj F) := by
  have nc := c.naturality (eY.inv.app F)
  have nq := qX.hom.naturality (smP.hom.app F)
  simp only [Functor.comp_map, Functor.comp_obj] at nc nq
  have hL : Lf.map (τY.hom.app F) ≫ Lf.map (qY.inv.app (singY.obj F)) =
      Lf.map (σY.hom.app F) ≫ Lf.map (QhY.map (eY.inv.app F)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hσY]
  rw [hν]
  simp only [Category.assoc]
  rw [reassoc_of% hL, reassoc_of% nc, ← reassoc_of% nq, ← hσX, ← hhs]
  simp only [Functor.map_comp, Category.assoc]

end Abstract

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The comparison `Lf^*(F[0]) ⟶ (f^*F)[0]`** of the derived with the ordinary pullback of a
module placed in degree `0`: the comparison
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans` at the complex `F[0]`, followed
by the commutation of `f^*` with `(-)[0]` on complexes. Stated at the standard model
`HasDerivedCategory.standard`, installed for this declaration only. -/
def derivedPullbackSingleComparison (F : SheafOfModules.{u} (structureSheafRing Y)) :
    (derivedPullback f).obj ((DerivedCategory.singleFunctor _ 0).obj F) ⟶
      (DerivedCategory.singleFunctor _ 0).obj ((modulePullback f).obj F) :=
  (derivedPullback f).map ((DerivedCategory.singleFunctorIsoCompQ _ 0).hom.app F) ≫
    (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans f).app
      ((CochainComplex.singleFunctor _ 0).obj F) ≫
    DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex
      (StacksDraft.KFlat.modulePullback f) (ComplexShape.up ℤ) 0).hom.app F) ≫
    (DerivedCategory.singleFunctorIsoCompQ _ 0).inv.app ((StacksDraft.KFlat.modulePullback f).obj F)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- `derivedPullbackSingleComparison` read on the homotopy category: the comparison
`derivedPullbackComparison` at `F[0]`, between the commutation of `f^*` with `(-)[0]` on homotopy
categories and the two identifications `DerivedCategory.singleFunctorIsoCompQh`. -/
theorem derivedPullbackSingleComparison_eq (F : SheafOfModules.{u} (structureSheafRing Y)) :
    derivedPullbackSingleComparison f F =
      (derivedPullback f).map ((DerivedCategory.singleFunctorIsoCompQh _ 0).hom.app F) ≫
        (derivedPullbackComparison f).app ((HomotopyCategory.singleFunctor _ 0).obj F) ≫
        DerivedCategory.Qh.map
          (((modulePullback f).mapHomotopyCategorySingleFunctorIso 0).hom.app F) ≫
        (DerivedCategory.singleFunctorIsoCompQh _ 0).inv.app ((modulePullback f).obj F) := by
  have hI : ((modulePullback f).mapHomotopyCategorySingleFunctorIso 0).hom.app F =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex (modulePullback f)
          (ComplexShape.up ℤ) 0).hom.app F) :=
    (Iso.inv_eq_inv (((modulePullback f).mapHomotopyCategorySingleFunctorIso 0).app F)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex (modulePullback f)
          (ComplexShape.up ℤ) 0).app F))).1
      ((modulePullback f).mapHomotopyCategorySingleFunctorIso_inv_app 0 F)
  have hσY : (DerivedCategory.singleFunctorIsoCompQh
      (SheafOfModules.{u} (structureSheafRing Y)) 0).hom.app F ≫
      DerivedCategory.Qh.map ((HomotopyCategory.singleFunctorPostcompQuotientIso
        (SheafOfModules.{u} (structureSheafRing Y)) 0).hom.app F) =
      (DerivedCategory.singleFunctorIsoCompQ
        (SheafOfModules.{u} (structureSheafRing Y)) 0).hom.app F ≫
        (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing Y))).inv.app
          ((CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj F) :=
    ((congrArg (_ ≫ ·) (CategoryTheory.Functor.map_id DerivedCategory.Qh _)).trans
      (Category.comp_id _)).trans
        ((Stacks.DerivedIndexing.singleFunctorIsoCompQh_hom_app 0 F).trans
          (Category.id_comp _).symm)
  have hσX : DerivedCategory.Qh.map ((HomotopyCategory.singleFunctorPostcompQuotientIso
        (SheafOfModules.{u} (structureSheafRing X)) 0).inv.app ((modulePullback f).obj F)) ≫
      (DerivedCategory.singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing X)) 0).inv.app
        ((modulePullback f).obj F) =
      (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X))).hom.app
          ((CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj
            ((modulePullback f).obj F)) ≫
        (DerivedCategory.singleFunctorIsoCompQ
          (SheafOfModules.{u} (structureSheafRing X)) 0).inv.app
          ((modulePullback f).obj F) := by
    have hσ := (Iso.inv_eq_inv ((DerivedCategory.singleFunctorIsoCompQh
        (SheafOfModules.{u} (structureSheafRing X)) 0).app ((modulePullback f).obj F))
      ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X))).app
        ((CochainComplex.singleFunctor _ 0).obj ((modulePullback f).obj F))).symm).2
      (Stacks.DerivedIndexing.singleFunctorIsoCompQh_hom_app 0 _)
    exact ((congrArg (· ≫ _) (CategoryTheory.Functor.map_id DerivedCategory.Qh _)).trans
      (Category.id_comp _)).trans (hσ.trans (Category.comp_id _).symm)
  have hhs : ((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((HomotopyCategory.singleFunctorPostcompQuotientIso
          (SheafOfModules.{u} (structureSheafRing Y)) 0).hom.app F) ≫
      ((modulePullback f).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app
        ((CochainComplex.singleFunctor _ 0).obj F) ≫
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex (modulePullback f)
          (ComplexShape.up ℤ) 0).hom.app F) ≫
      (HomotopyCategory.singleFunctorPostcompQuotientIso
          (SheafOfModules.{u} (structureSheafRing X)) 0).inv.app ((modulePullback f).obj F) =
      ((modulePullback f).mapHomotopyCategorySingleFunctorIso 0).hom.app F := by
    have h0 : ((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((HomotopyCategory.singleFunctorPostcompQuotientIso
          (SheafOfModules.{u} (structureSheafRing Y)) 0).hom.app F) = 𝟙 _ :=
      CategoryTheory.Functor.map_id _ _
    rw [h0]
    exact (Category.id_comp _).trans
      (((Category.id_comp _).trans (Category.comp_id _)).trans hI.symm)
  have hν : (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans f).app
        ((CochainComplex.singleFunctor _ 0).obj F) =
      (derivedPullback f).map ((DerivedCategory.quotientCompQhIso _).inv.app
          ((CochainComplex.singleFunctor _ 0).obj F)) ≫
        (derivedPullbackComparison f).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor _ 0).obj F)) ≫
        DerivedCategory.Qh.map (((modulePullback f).mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)).hom.app ((CochainComplex.singleFunctor _ 0).obj F)) ≫
        (DerivedCategory.quotientCompQhIso _).hom.app
          ((Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex f).obj
            ((CochainComplex.singleFunctor _ 0).obj F)) := by
    unfold Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    rfl
  exact singleComparison_eq_of_fac
    (DerivedCategory.singleFunctorIsoCompQ (SheafOfModules.{u} (structureSheafRing Y)) 0)
    (DerivedCategory.singleFunctorIsoCompQ (SheafOfModules.{u} (structureSheafRing X)) 0)
    (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing Y)))
    (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X)))
    (DerivedCategory.singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing Y)) 0)
    (DerivedCategory.singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing X)) 0)
    (HomotopyCategory.singleFunctorPostcompQuotientIso
      (SheafOfModules.{u} (structureSheafRing Y)) 0).symm
    (HomotopyCategory.singleFunctorPostcompQuotientIso
      (SheafOfModules.{u} (structureSheafRing X)) 0).symm
    (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans f)
    (derivedPullbackComparison f)
    ((modulePullback f).mapHomotopyCategoryFactors (ComplexShape.up ℤ))
    (HomologicalComplex.singleMapHomologicalComplex (StacksDraft.KFlat.modulePullback f)
      (ComplexShape.up ℤ) 0)
    ((modulePullback f).mapHomotopyCategorySingleFunctorIso 0) F hν hσY hσX hhs


attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The derived unit at `F[0]` along an exact direct image.** For a morphism of ringed spaces
`f : X ⟶ Y` along which `f_*` is exact and an `𝒪_Y`-module `F`, the unit of `Lf^* ⊣ Rf_*` at
`F[0]` followed by `Rf_*` of the comparison `Lf^*(F[0]) ⟶ (f^*F)[0]`
(`derivedPullbackSingleComparison`) is the unit of `f^* ⊣ f_*` at `F` placed in degree `0`
followed by the isomorphism `(f_* f^* F)[0] ≅ Rf_*((f^*F)[0])` of `derivedPushforwardSingleIso`.

Stated at the standard model `HasDerivedCategory.standard`, the model of
`derivedPullbackSingleComparison`, installed for this declaration only. -/
theorem derivedAdjunction_unit_app_single_comp [PreservesFiniteColimits (modulePushforward f)]
    (F : SheafOfModules.{u} (structureSheafRing Y)) :
    (derivedAdjunction f).unit.app ((DerivedCategory.singleFunctor _ 0).obj F) ≫
        (derivedPushforward f).map (derivedPullbackSingleComparison f F) =
      (DerivedCategory.singleFunctor _ 0).map ((modulePullbackPushforwardAdjunction f).unit.app F) ≫
        (derivedPushforwardSingleIso f).hom.app ((modulePullback f).obj F) := by
  simp only [derivedPullbackSingleComparison_eq, derivedPushforwardSingleIso_hom_app]
  exact unit_comp_singleComparison_of_fac (derivedAdjunction f)
    (modulePullbackPushforwardAdjunction f) (homotopyPullbackPushforwardAdjunction f)
    (derivedPullbackComparison f) (derivedPushforwardUnit f)
    (DerivedCategory.singleFunctorIsoCompQh _ 0) (DerivedCategory.singleFunctorIsoCompQh _ 0)
    ((modulePullback f).mapHomotopyCategorySingleFunctorIso 0)
    ((modulePushforward f).mapHomotopyCategorySingleFunctorIso 0) F
    (derivedAdjunction_unit_fac f _)
    (Adjunction.singleFunctor_map_unit_comp_mapHomotopyCategorySingleFunctorIso_inv
      (modulePullbackPushforwardAdjunction f) F)
end

end Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

end
