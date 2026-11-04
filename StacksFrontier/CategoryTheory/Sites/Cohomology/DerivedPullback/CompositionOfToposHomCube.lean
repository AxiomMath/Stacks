module

public import StacksFrontier.CategoryTheory.Functor.Derived.LeftDerivedComparisonCube
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackModulesIsoDerivedPullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOfToposHomSquare

/-!
# Derived pullbacks of ringed topoi around a cube

Two commutative squares of morphisms of ringed topoi, `p ≫ q = r ≫ s` (top) and
`p₀ ≫ q₀ = r₀ ≫ s₀` (bottom), joined by four vertical morphisms `ε` and four squares `θ` of
pullbacks of modules, give four squares of derived pullbacks (Stacks 0D6D). If the cube of
pullbacks of modules commutes, so does the cube of derived pullbacks.

## Main results

* `Stacks.Cohomology.DerivedPullbackCompositionOfToposHom.derivedPullbackSquareIso_cube`: the
  cube of derived pullbacks.
* `Stacks.Cohomology.DerivedPullbackCompositionOfToposHom.pullbackMapHomotopySquareIso_cube`: the
  cube of degreewise pullbacks on homotopy categories.
* `Stacks.Cohomology.DerivedPullbackCompositionOfToposHom.mapHomotopyCategory_cube`: the same for
  additive functors.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackOfToposHom

namespace Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

universe v u w v₀ u₀ w₀

attribute [local instance] HasDerivedCategory.standard

noncomputable section

section Degreewise

variable {AT AW AT' AW' BT BW BT' BW' : Type*}
  {cAT : Category AT} {cAW : Category AW} {cAT' : Category AT'} {cAW' : Category AW'}
  {cBT : Category BT} {cBW : Category BW} {cBT' : Category BT'} {cBW' : Category BW'}
  {aAT : Preadditive AT} {aAW : Preadditive AW} {aAT' : Preadditive AT'} {aAW' : Preadditive AW'}
  {aBT : Preadditive BT} {aBW : Preadditive BW} {aBT' : Preadditive BT'} {aBW' : Preadditive BW'}
  (c : ComplexShape ℤ)
  {qe : AT ⥤ AW} {pe : AW ⥤ AW'} {se : AT ⥤ AT'} {re : AT' ⥤ AW'}
  {qz : BT ⥤ BW} {pz : BW ⥤ BW'} {sz : BT ⥤ BT'} {rz : BT' ⥤ BW'}
  {eT : BT ⥤ AT} {eW : BW ⥤ AW} {eT' : BT' ⥤ AT'} {eW' : BW' ⥤ AW'}
  {Gq Hq : BT ⥤ AW} {Gp Hp : BW ⥤ AW'} {Gs Hs : BT ⥤ AT'}
  {Gr Hr : BT' ⥤ AW'} {Gpq Hi Grs : AT ⥤ AW'} {Gz₁ Gz₂ : BT ⥤ BW'}
  {hqe : qe.Additive} {hpe : pe.Additive} {hse : se.Additive} {hre : re.Additive}
  {hqz : qz.Additive} {hpz : pz.Additive} {hsz : sz.Additive} {hrz : rz.Additive}
  {heT : eT.Additive} {heW : eW.Additive} {heT' : eT'.Additive} {heW' : eW'.Additive}
  {hHi : Hi.Additive}
  [hGq : Gq.Additive] [hHq : Hq.Additive] [hGp : Gp.Additive] [hHp : Hp.Additive]
  [hGs : Gs.Additive] [hHs : Hs.Additive] [hGr : Gr.Additive] [hHr : Hr.Additive]
  [hGpq : Gpq.Additive] [hGrs : Grs.Additive] [hGz₁ : Gz₁.Additive] [hGz₂ : Gz₂.Additive]

/-- **A cube of additive functors, on homotopy categories.** If the cube built from four squares
`θ_g` of additive functors (read through compositors `c_g`, `d_g`), the top 2-cell
`t_{rs}⁻¹ ∘ t_{pq}` and the bottom 2-cell `Zu` commutes objectwise, the induced cube of homotopy
categories commutes. -/
theorem mapHomotopyCategory_cube
    (cq : Gq ≅ eT ⋙ qe) (θq : Gq ≅ Hq) (dq : Hq ≅ qz ⋙ eW)
    (cp : Gp ≅ eW ⋙ pe) (θp : Gp ≅ Hp) (dp : Hp ≅ pz ⋙ eW')
    (cs : Gs ≅ eT ⋙ se) (θs : Gs ≅ Hs) (ds : Hs ≅ sz ⋙ eT')
    (cr : Gr ≅ eT' ⋙ re) (θr : Gr ≅ Hr) (dr : Hr ≅ rz ⋙ eW')
    (cpq : Gpq ≅ qe ⋙ pe) (tpq : Gpq ≅ Hi) (crs : Grs ≅ se ⋙ re) (trs : Grs ≅ Hi)
    (cz₁ : Gz₁ ≅ qz ⋙ pz) (cz₂ : Gz₂ ≅ sz ⋙ rz) (Zu : qz ⋙ pz ≅ sz ⋙ rz)
    (hu : ∀ M, pe.map (cq.inv.app M ≫ θq.hom.app M ≫ dq.hom.app M) ≫
        (cp.inv.app (qz.obj M) ≫ θp.hom.app (qz.obj M) ≫ dp.hom.app (qz.obj M)) ≫
            eW'.map (Zu.hom.app M) =
      (cpq.inv.app (eT.obj M) ≫ tpq.hom.app (eT.obj M) ≫ trs.inv.app (eT.obj M) ≫
          crs.hom.app (eT.obj M)) ≫
        re.map (cs.inv.app M ≫ θs.hom.app M ≫ ds.hom.app M) ≫ (cr.inv.app (sz.obj M) ≫
            θr.hom.app (sz.obj M) ≫ dr.hom.app (sz.obj M)))
    (Hqe : HomotopyCategory AT c ⥤ HomotopyCategory AW c) (hHqe : Hqe = qe.mapHomotopyCategory c)
    (Hpe : HomotopyCategory AW c ⥤ HomotopyCategory AW' c) (hHpe : Hpe = pe.mapHomotopyCategory c)
    (Hse : HomotopyCategory AT c ⥤ HomotopyCategory AT' c) (hHse : Hse = se.mapHomotopyCategory c)
    (Hre : HomotopyCategory AT' c ⥤ HomotopyCategory AW' c) (hHre : Hre = re.mapHomotopyCategory c)
    (Hqz : HomotopyCategory BT c ⥤ HomotopyCategory BW c) (hHqz : Hqz = qz.mapHomotopyCategory c)
    (Hpz : HomotopyCategory BW c ⥤ HomotopyCategory BW' c) (hHpz : Hpz = pz.mapHomotopyCategory c)
    (Hsz : HomotopyCategory BT c ⥤ HomotopyCategory BT' c) (hHsz : Hsz = sz.mapHomotopyCategory c)
    (Hrz : HomotopyCategory BT' c ⥤ HomotopyCategory BW' c) (hHrz : Hrz = rz.mapHomotopyCategory c)
    (HeT : HomotopyCategory BT c ⥤ HomotopyCategory AT c) (hHeT : HeT = eT.mapHomotopyCategory c)
    (HeW : HomotopyCategory BW c ⥤ HomotopyCategory AW c) (hHeW : HeW = eW.mapHomotopyCategory c)
    (HeT' : HomotopyCategory BT' c ⥤ HomotopyCategory AT' c) (hHeT' : HeT' =
        eT'.mapHomotopyCategory c)
    (HeW' : HomotopyCategory BW' c ⥤ HomotopyCategory AW' c) (hHeW' : HeW' =
        eW'.mapHomotopyCategory c)
    (HHi : HomotopyCategory AT c ⥤ HomotopyCategory AW' c) (hHHi : HHi = Hi.mapHomotopyCategory c)
    (σq : HeT ⋙ Hqe ≅ Hqz ⋙ HeW)
    (hσq : HEq σq ((Functor.mapHomotopyCategoryCompIso cq.symm c) ≪≫
        (Stacks.Homology.mapHomotopyCategoryIso θq c) ≪≫
        (Functor.mapHomotopyCategoryCompIso dq.symm c).symm))
    (σp : HeW ⋙ Hpe ≅ Hpz ⋙ HeW')
    (hσp : HEq σp ((Functor.mapHomotopyCategoryCompIso cp.symm c) ≪≫
        (Stacks.Homology.mapHomotopyCategoryIso θp c) ≪≫
        (Functor.mapHomotopyCategoryCompIso dp.symm c).symm))
    (σs : HeT ⋙ Hse ≅ Hsz ⋙ HeT')
    (hσs : HEq σs ((Functor.mapHomotopyCategoryCompIso cs.symm c) ≪≫
        (Stacks.Homology.mapHomotopyCategoryIso θs c) ≪≫
        (Functor.mapHomotopyCategoryCompIso ds.symm c).symm))
    (σr : HeT' ⋙ Hre ≅ Hrz ⋙ HeW')
    (hσr : HEq σr ((Functor.mapHomotopyCategoryCompIso cr.symm c) ≪≫
        (Stacks.Homology.mapHomotopyCategoryIso θr c) ≪≫
        (Functor.mapHomotopyCategoryCompIso dr.symm c).symm))
    (σz : Hqz ⋙ Hpz ≅ Hsz ⋙ Hrz)
    (hσz : HEq σz ((Functor.mapHomotopyCategoryCompIso cz₁.symm c) ≪≫
        (Stacks.Homology.mapHomotopyCategoryIso (cz₁ ≪≫ Zu ≪≫ cz₂.symm) c) ≪≫
        (Functor.mapHomotopyCategoryCompIso cz₂.symm c).symm))
    (βpq : Hqe ⋙ Hpe ≅ HHi) (hβpq : HEq βpq ((Functor.mapHomotopyCategoryCompIso cpq.symm c) ≪≫
        (Stacks.Homology.mapHomotopyCategoryIso tpq c)))
    (βrs : Hse ⋙ Hre ≅ HHi) (hβrs : HEq βrs ((Functor.mapHomotopyCategoryCompIso crs.symm c) ≪≫
        (Stacks.Homology.mapHomotopyCategoryIso trs c)))
    (κ : HHi ≅ HHi) (hκ : κ = Iso.refl _)
    (K : HomotopyCategory BT c) :
    Hpe.map (σq.hom.app K) ≫ σp.hom.app (Hqz.obj K) ≫ HeW'.map (σz.hom.app K) =
      (βpq.hom ≫ κ.hom ≫ βrs.inv).app (HeT.obj K) ≫ Hre.map (σs.hom.app K) ≫
        σr.hom.app (Hsz.obj K) := by
  subst hHqe hHpe hHse hHre hHqz hHpz hHsz hHrz hHeT hHeW hHeT' hHeW' hHHi
  subst hκ
  obtain rfl := eq_of_heq hσq
  obtain rfl := eq_of_heq hσp
  obtain rfl := eq_of_heq hσs
  obtain rfl := eq_of_heq hσr
  obtain rfl := eq_of_heq hσz
  obtain rfl := eq_of_heq hβpq
  obtain rfl := eq_of_heq hβrs
  rcases K with ⟨C⟩
  have key : (pe.mapHomologicalComplex c).map ((NatTrans.mapHomologicalComplex cq.inv c).app C ≫
      (NatTrans.mapHomologicalComplex θq.hom c).app C ≫
      (NatTrans.mapHomologicalComplex dq.hom c).app C) ≫
        ((NatTrans.mapHomologicalComplex cp.inv c).app ((qz.mapHomologicalComplex c).obj C) ≫
            (NatTrans.mapHomologicalComplex θp.hom c).app ((qz.mapHomologicalComplex c).obj C) ≫
            (NatTrans.mapHomologicalComplex dp.hom c).app ((qz.mapHomologicalComplex c).obj C)) ≫
        (eW'.mapHomologicalComplex c).map ((NatTrans.mapHomologicalComplex cz₁.inv c).app C ≫
            (NatTrans.mapHomologicalComplex (cz₁ ≪≫ Zu ≪≫ cz₂.symm).hom c).app C ≫
            (NatTrans.mapHomologicalComplex cz₂.hom c).app C) =
      (((NatTrans.mapHomologicalComplex cpq.inv c).app ((eT.mapHomologicalComplex c).obj C) ≫
          (NatTrans.mapHomologicalComplex tpq.hom c).app ((eT.mapHomologicalComplex c).obj C)) ≫
          𝟙 _ ≫ ((NatTrans.mapHomologicalComplex trs.inv c).app ((eT.mapHomologicalComplex c).obj
          C) ≫ (NatTrans.mapHomologicalComplex crs.hom c).app ((eT.mapHomologicalComplex c).obj
          C))) ≫
        (re.mapHomologicalComplex c).map ((NatTrans.mapHomologicalComplex cs.inv c).app C ≫
            (NatTrans.mapHomologicalComplex θs.hom c).app C ≫
            (NatTrans.mapHomologicalComplex ds.hom c).app C) ≫
        ((NatTrans.mapHomologicalComplex cr.inv c).app ((sz.mapHomologicalComplex c).obj C) ≫
            (NatTrans.mapHomologicalComplex θr.hom c).app ((sz.mapHomologicalComplex c).obj C) ≫
            (NatTrans.mapHomologicalComplex dr.hom c).app ((sz.mapHomologicalComplex c).obj C)) :=
            by
    ext n
    have hn := hu (C.X n)
    simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
      Functor.mapHomologicalComplex_map_f, Category.id_comp,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
          Functor.mapHomologicalComplex_obj_X,
      Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id] at hn ⊢
    exact hn
  have := congrArg (HomotopyCategory.quotient _ c).map key
  simp only [(HomotopyCategory.quotient AW' c).map_comp] at this
  exact this

end Degreewise

section Cube

variable {ET EW ET' EW' : RingedTopos.{v, u, w}} {ZT ZW ZT' ZW' : RingedTopos.{v₀, u₀, w₀}}
  [ET.J.HasSheafCompose (forget RingCat.{w})]
  [ET.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [ET.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasSheafify ET.J AddCommGrpCat.{w}] [ET.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify ET.J (Type w)]
  [EW.J.HasSheafCompose (forget RingCat.{w})]
  [EW.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [EW.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasSheafify EW.J AddCommGrpCat.{w}] [EW.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify EW.J (Type w)]
  [ET'.J.HasSheafCompose (forget RingCat.{w})]
  [ET'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [ET'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasSheafify ET'.J AddCommGrpCat.{w}] [ET'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify ET'.J (Type w)]
  [EW'.J.HasSheafCompose (forget RingCat.{w})]
  [EW'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [EW'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasSheafify EW'.J AddCommGrpCat.{w}] [EW'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify EW'.J (Type w)]
  [ZT.J.HasSheafCompose (forget RingCat.{w₀})]
  [ZT.J.HasSheafCompose (forget₂ CommRingCat.{w₀} RingCat.{w₀})]
  [ZT.J.HasSheafCompose (forget AddCommGrpCat.{w₀})]
  [HasSheafify ZT.J AddCommGrpCat.{w₀}] [ZT.J.WEqualsLocallyBijective AddCommGrpCat.{w₀}]
  [HasSheafify ZT.J (Type w₀)]
  [ZW.J.HasSheafCompose (forget RingCat.{w₀})]
  [ZW.J.HasSheafCompose (forget₂ CommRingCat.{w₀} RingCat.{w₀})]
  [ZW.J.HasSheafCompose (forget AddCommGrpCat.{w₀})]
  [HasSheafify ZW.J AddCommGrpCat.{w₀}] [ZW.J.WEqualsLocallyBijective AddCommGrpCat.{w₀}]
  [HasSheafify ZW.J (Type w₀)]
  [ZT'.J.HasSheafCompose (forget RingCat.{w₀})]
  [ZT'.J.HasSheafCompose (forget₂ CommRingCat.{w₀} RingCat.{w₀})]
  [ZT'.J.HasSheafCompose (forget AddCommGrpCat.{w₀})]
  [HasSheafify ZT'.J AddCommGrpCat.{w₀}] [ZT'.J.WEqualsLocallyBijective AddCommGrpCat.{w₀}]
  [HasSheafify ZT'.J (Type w₀)]
  [ZW'.J.HasSheafCompose (forget RingCat.{w₀})]
  [ZW'.J.HasSheafCompose (forget₂ CommRingCat.{w₀} RingCat.{w₀})]
  [ZW'.J.HasSheafCompose (forget AddCommGrpCat.{w₀})]
  [HasSheafify ZW'.J AddCommGrpCat.{w₀}] [ZW'.J.WEqualsLocallyBijective AddCommGrpCat.{w₀}]
  [HasSheafify ZW'.J (Type w₀)]
  (q₀ : RingedToposHom ZW ZT) (p₀ : RingedToposHom ZW' ZW) (s₀ : RingedToposHom ZT' ZT)
  (r₀ : RingedToposHom ZW' ZT')
  (q : RingedToposHom EW ET) (p : RingedToposHom EW' EW) (s : RingedToposHom ET' ET)
  (r : RingedToposHom EW' ET')
  (εT : RingedToposHom ET ZT) (εW : RingedToposHom EW ZW) (εT' : RingedToposHom ET' ZT')
  (εW' : RingedToposHom EW' ZW')

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

omit [HasSheafify ET.J (Type w)] [HasSheafify EW.J (Type w)] [HasSheafify ET'.J (Type w)]
  [HasSheafify EW'.J (Type w)] [HasSheafify ZT.J AddCommGrpCat] [ZT.J.WEqualsLocallyBijective
  AddCommGrpCat] [HasSheafify ZT.J (Type w₀)] [HasSheafify ZW.J (Type w₀)]
  [HasSheafify ZT'.J (Type w₀)] [HasSheafify ZW'.J (Type w₀)] in
/-- **Pullbacks of complexes around a cube of ringed topoi.** If the cube of pullbacks of
modules attached to squares `θ_g` commutes, so does the induced cube of degreewise pullbacks on
homotopy categories. -/
theorem pullbackMapHomotopySquareIso_cube
    (θq : (εT.comp q).toModulesHom.pullbackModules ≅ (q₀.comp εW).toModulesHom.pullbackModules)
    (θp : (εW.comp p).toModulesHom.pullbackModules ≅
      (p₀.comp εW').toModulesHom.pullbackModules)
    (θs : (εT.comp s).toModulesHom.pullbackModules ≅
      (s₀.comp εT').toModulesHom.pullbackModules)
    (θr : (εT'.comp r).toModulesHom.pullbackModules ≅
      (r₀.comp εW').toModulesHom.pullbackModules)
    {ι : Type*} (h : ι → RingedToposHom EW' ET) {i j : ι} (hij : i = j)
    (tpq : (q.comp p).toModulesHom.pullbackModules ≅ (h i).toModulesHom.pullbackModules)
    (trs : (s.comp r).toModulesHom.pullbackModules ≅ (h j).toModulesHom.pullbackModules)
    (Zu : q₀.toModulesHom.pullbackModules ⋙ p₀.toModulesHom.pullbackModules ≅
      s₀.toModulesHom.pullbackModules ⋙ r₀.toModulesHom.pullbackModules)
    (hu : ∀ M, p.toModulesHom.pullbackModules.map
          ((RingedToposHom.pullbackModulesCompIso q εT).inv.app M ≫
          θq.hom.app M ≫ (RingedToposHom.pullbackModulesCompIso εW q₀).hom.app M) ≫
        ((RingedToposHom.pullbackModulesCompIso p εW).inv.app
            (q₀.toModulesHom.pullbackModules.obj M) ≫
          θp.hom.app (q₀.toModulesHom.pullbackModules.obj M) ≫
          (RingedToposHom.pullbackModulesCompIso εW' p₀).hom.app
            (q₀.toModulesHom.pullbackModules.obj M)) ≫
        εW'.toModulesHom.pullbackModules.map (Zu.hom.app M) =
      ((RingedToposHom.pullbackModulesCompIso p q).inv.app
            (εT.toModulesHom.pullbackModules.obj M) ≫
          tpq.hom.app (εT.toModulesHom.pullbackModules.obj M) ≫
          (eqToIso (congrArg (fun k => (h k).toModulesHom.pullbackModules) hij)).hom.app
            (εT.toModulesHom.pullbackModules.obj M) ≫
          trs.inv.app (εT.toModulesHom.pullbackModules.obj M) ≫
          (RingedToposHom.pullbackModulesCompIso r s).hom.app
            (εT.toModulesHom.pullbackModules.obj M)) ≫
        r.toModulesHom.pullbackModules.map
          ((RingedToposHom.pullbackModulesCompIso s εT).inv.app M ≫
          θs.hom.app M ≫ (RingedToposHom.pullbackModulesCompIso εT' s₀).hom.app M) ≫
        ((RingedToposHom.pullbackModulesCompIso r εT').inv.app
            (s₀.toModulesHom.pullbackModules.obj M) ≫
          θr.hom.app (s₀.toModulesHom.pullbackModules.obj M) ≫
          (RingedToposHom.pullbackModulesCompIso εW' r₀).hom.app
            (s₀.toModulesHom.pullbackModules.obj M)))
    (K : HomotopyCategory
      (SheafOfModules.{w₀} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := ZT.J) ZT.O)))
      (ComplexShape.up ℤ)) :
    (DerivedPushforward.pullbackMapHomotopy p).map ((pullbackMapHomotopySquareIso q εT εW q₀
        θq).hom.app K) ≫
        (pullbackMapHomotopySquareIso p εW εW' p₀ θp).hom.app
            ((DerivedPushforward.pullbackMapHomotopy q₀).obj K) ≫
        (DerivedPushforward.pullbackMapHomotopy εW').map ((pullbackMapHomotopySquareIso p₀ q₀ r₀
            s₀ ((RingedToposHom.pullbackModulesCompIso p₀ q₀) ≪≫ Zu ≪≫
            (RingedToposHom.pullbackModulesCompIso r₀ s₀).symm)).hom.app K) =
      ((pullbackMapHomotopyCompIso p q ≪≫
          Stacks.Homology.mapHomotopyCategoryIso tpq (ComplexShape.up ℤ)).hom ≫
        (eqToIso (congrArg (fun k => (DerivedPushforward.pullbackMapHomotopy (h k))) hij)).hom ≫
        (pullbackMapHomotopyCompIso r s ≪≫
          Stacks.Homology.mapHomotopyCategoryIso trs (ComplexShape.up ℤ)).inv).app
              ((DerivedPushforward.pullbackMapHomotopy εT).obj K) ≫
        (DerivedPushforward.pullbackMapHomotopy r).map ((pullbackMapHomotopySquareIso s εT εT' s₀
            θs).hom.app K) ≫
        (pullbackMapHomotopySquareIso r εT' εW' r₀ θr).hom.app
            ((DerivedPushforward.pullbackMapHomotopy s₀).obj K) := by
  subst hij
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp] at hu
  exact mapHomotopyCategory_cube _ (RingedToposHom.pullbackModulesCompIso q εT) θq
      (RingedToposHom.pullbackModulesCompIso εW q₀)
    (RingedToposHom.pullbackModulesCompIso p εW) θp (RingedToposHom.pullbackModulesCompIso εW' p₀)
        (RingedToposHom.pullbackModulesCompIso s εT) θs (RingedToposHom.pullbackModulesCompIso εT'
        s₀)
    (RingedToposHom.pullbackModulesCompIso r εT') θr (RingedToposHom.pullbackModulesCompIso εW'
        r₀) (RingedToposHom.pullbackModulesCompIso p q) tpq (RingedToposHom.pullbackModulesCompIso
        r s) trs
    (RingedToposHom.pullbackModulesCompIso p₀ q₀)
        (RingedToposHom.pullbackModulesCompIso r₀ s₀) Zu hu
    (DerivedPushforward.pullbackMapHomotopy q) rfl (DerivedPushforward.pullbackMapHomotopy p) rfl
        (DerivedPushforward.pullbackMapHomotopy s) rfl (DerivedPushforward.pullbackMapHomotopy r)
        rfl (DerivedPushforward.pullbackMapHomotopy q₀) rfl
        (DerivedPushforward.pullbackMapHomotopy p₀) rfl (DerivedPushforward.pullbackMapHomotopy
        s₀) rfl (DerivedPushforward.pullbackMapHomotopy r₀) rfl
        (DerivedPushforward.pullbackMapHomotopy εT) rfl (DerivedPushforward.pullbackMapHomotopy
        εW) rfl (DerivedPushforward.pullbackMapHomotopy εT') rfl
        (DerivedPushforward.pullbackMapHomotopy εW') rfl (DerivedPushforward.pullbackMapHomotopy
        (h i)) rfl
    (pullbackMapHomotopySquareIso q εT εW q₀ θq) HEq.rfl
    (pullbackMapHomotopySquareIso p εW εW' p₀ θp) HEq.rfl
    (pullbackMapHomotopySquareIso s εT εT' s₀ θs) HEq.rfl
    (pullbackMapHomotopySquareIso r εT' εW' r₀ θr) HEq.rfl
    (pullbackMapHomotopySquareIso p₀ q₀ r₀ s₀ ((RingedToposHom.pullbackModulesCompIso p₀ q₀) ≪≫
        Zu ≪≫ (RingedToposHom.pullbackModulesCompIso r₀ s₀).symm)) HEq.rfl
    (pullbackMapHomotopyCompIso p q ≪≫
        Stacks.Homology.mapHomotopyCategoryIso tpq (ComplexShape.up ℤ)) HEq.rfl
    (pullbackMapHomotopyCompIso r s ≪≫
        Stacks.Homology.mapHomotopyCategoryIso trs (ComplexShape.up ℤ)) HEq.rfl
    (eqToIso (congrArg (fun k => DerivedPushforward.pullbackMapHomotopy (h k)) (rfl : i =
        i))) (eqToIso_refl _) K

/-- **Derived pullbacks around a cube of ringed topoi.** The four squares
`ρ_g : Lε^* ⋙ Lg^* ≅ Lg₀^* ⋙ Lε'^*` of Stacks 0D6D attached to squares `θ_g` of pullbacks of
modules, the 2-cell `Lp^* ∘ Lq^* ≅ L(h i)^* = L(h j)^* ≅ Lr^* ∘ Ls^*` on the top face and the
2-cell `Z` attached to `Zu` on the bottom face form a commutative cube as soon as the cube of
pullbacks of modules commutes; the faces of that cube are given componentwise, as any morphisms
heterogeneously equal to the components of the squares `θ_g`, of `Zu` and of the top 2-cell. -/
theorem derivedPullbackSquareIso_cube
    (θq : (εT.comp q).toModulesHom.pullbackModules ≅ (q₀.comp εW).toModulesHom.pullbackModules)
    (θp : (εW.comp p).toModulesHom.pullbackModules ≅
      (p₀.comp εW').toModulesHom.pullbackModules)
    (θs : (εT.comp s).toModulesHom.pullbackModules ≅
      (s₀.comp εT').toModulesHom.pullbackModules)
    (θr : (εT'.comp r).toModulesHom.pullbackModules ≅
      (r₀.comp εW').toModulesHom.pullbackModules)
    {ι : Type*} (h : ι → RingedToposHom EW' ET) {i j : ι} (hij : i = j)
    (tpq : (q.comp p).toModulesHom.pullbackModules ≅ (h i).toModulesHom.pullbackModules)
    (trs : (s.comp r).toModulesHom.pullbackModules ≅ (h j).toModulesHom.pullbackModules)
    (Zu : q₀.toModulesHom.pullbackModules ⋙ p₀.toModulesHom.pullbackModules ≅
      s₀.toModulesHom.pullbackModules ⋙ r₀.toModulesHom.pullbackModules)
    {DZT : Type (max u₀ v₀ (w₀ + 1))} {iDZT : Category.{max u₀ v₀ (w₀ + 1)} DZT}
    {DZW : Type (max u₀ v₀ (w₀ + 1))} {iDZW : Category.{max u₀ v₀ (w₀ + 1)} DZW}
    {DZT' : Type (max u₀ v₀ (w₀ + 1))} {iDZT' : Category.{max u₀ v₀ (w₀ + 1)} DZT'}
    {DZW' : Type (max u₀ v₀ (w₀ + 1))} {iDZW' : Category.{max u₀ v₀ (w₀ + 1)} DZW'}
    {DET : Type (max u v (w + 1))} {iDET : Category.{max u v (w + 1)} DET}
    {DEW : Type (max u v (w + 1))} {iDEW : Category.{max u v (w + 1)} DEW}
    {DET' : Type (max u v (w + 1))} {iDET' : Category.{max u v (w + 1)} DET'}
    {DEW' : Type (max u v (w + 1))} {iDEW' : Category.{max u v (w + 1)} DEW'}
    (Lq₀ : DZT ⥤ DZW) (hLq₀ : HEq Lq₀ (derivedPullback q₀))
    (Lp₀ : DZW ⥤ DZW') (hLp₀ : HEq Lp₀ (derivedPullback p₀))
    (Ls₀ : DZT ⥤ DZT') (hLs₀ : HEq Ls₀ (derivedPullback s₀))
    (Lr₀ : DZT' ⥤ DZW') (hLr₀ : HEq Lr₀ (derivedPullback r₀))
    (Lq : DET ⥤ DEW) (hLq : HEq Lq (derivedPullback q))
    (Lp : DEW ⥤ DEW') (hLp : HEq Lp (derivedPullback p))
    (Ls : DET ⥤ DET') (hLs : HEq Ls (derivedPullback s))
    (Lr : DET' ⥤ DEW') (hLr : HEq Lr (derivedPullback r))
    (LεT : DZT ⥤ DET) (hLεT : HEq LεT (derivedPullback εT))
    (LεW : DZW ⥤ DEW) (hLεW : HEq LεW (derivedPullback εW))
    (LεT' : DZT' ⥤ DET') (hLεT' : HEq LεT' (derivedPullback εT'))
    (LεW' : DZW' ⥤ DEW') (hLεW' : HEq LεW' (derivedPullback εW'))
    (Lhi : DET ⥤ DEW') (hLhi : HEq Lhi (derivedPullback (h i)))
    (Lhj : DET ⥤ DEW') (hLhj : HEq Lhj (derivedPullback (h j)))
    (hDZT : DZT = DerivedCategory
      (SheafOfModules.{w₀} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := ZT.J) ZT.O))))
    (hiDZT : HEq iDZT (inferInstance : Category (DerivedCategory
      (SheafOfModules.{w₀} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := ZT.J) ZT.O))))))
    (hDZW : DZW = DerivedCategory
      (SheafOfModules.{w₀} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := ZW.J) ZW.O))))
    (hiDZW : HEq iDZW (inferInstance : Category (DerivedCategory
      (SheafOfModules.{w₀} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := ZW.J) ZW.O))))))
    (hDZT' : DZT' = DerivedCategory
      (SheafOfModules.{w₀} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := ZT'.J) ZT'.O))))
    (hiDZT' : HEq iDZT' (inferInstance : Category (DerivedCategory
      (SheafOfModules.{w₀} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := ZT'.J) ZT'.O))))))
    (hDZW' : DZW' = DerivedCategory
      (SheafOfModules.{w₀} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := ZW'.J) ZW'.O))))
    (hiDZW' : HEq iDZW' (inferInstance : Category (DerivedCategory
      (SheafOfModules.{w₀} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := ZW'.J) ZW'.O))))))
    (hDET : DET = DerivedCategory
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := ET.J) ET.O))))
    (hiDET : HEq iDET (inferInstance : Category (DerivedCategory
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := ET.J) ET.O))))))
    (hDEW : DEW = DerivedCategory
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := EW.J) EW.O))))
    (hiDEW : HEq iDEW (inferInstance : Category (DerivedCategory
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := EW.J) EW.O))))))
    (hDET' : DET' = DerivedCategory
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := ET'.J) ET'.O))))
    (hiDET' : HEq iDET' (inferInstance : Category (DerivedCategory
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := ET'.J) ET'.O))))))
    (hDEW' : DEW' = DerivedCategory
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := EW'.J) EW'.O))))
    (hiDEW' : HEq iDEW' (inferInstance : Category (DerivedCategory
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := EW'.J) EW'.O))))))
    (ρq : LεT ⋙ Lq ≅ Lq₀ ⋙ LεW)
    (hρq : HEq ρq (derivedPullbackCompIso q εT ≪≫ derivedPullbackIsoOfPullbackModulesIso θq ≪≫
      (derivedPullbackCompIso εW q₀).symm))
    (ρp : LεW ⋙ Lp ≅ Lp₀ ⋙ LεW')
    (hρp : HEq ρp (derivedPullbackCompIso p εW ≪≫ derivedPullbackIsoOfPullbackModulesIso θp ≪≫
      (derivedPullbackCompIso εW' p₀).symm))
    (ρs : LεT ⋙ Ls ≅ Ls₀ ⋙ LεT')
    (hρs : HEq ρs (derivedPullbackCompIso s εT ≪≫ derivedPullbackIsoOfPullbackModulesIso θs ≪≫
      (derivedPullbackCompIso εT' s₀).symm))
    (ρr : LεT' ⋙ Lr ≅ Lr₀ ⋙ LεW')
    (hρr : HEq ρr (derivedPullbackCompIso r εT' ≪≫ derivedPullbackIsoOfPullbackModulesIso θr ≪≫
      (derivedPullbackCompIso εW' r₀).symm))
    (cpq : Lq ⋙ Lp ≅ Lhi)
    (hcpq : HEq cpq (derivedPullbackCompIso p q ≪≫ derivedPullbackIsoOfPullbackModulesIso tpq))
    (crs : Ls ⋙ Lr ≅ Lhj)
    (hcrs : HEq crs (derivedPullbackCompIso r s ≪≫ derivedPullbackIsoOfPullbackModulesIso trs))
    (c : Lhi ≅ Lhj)
    (hc : HEq c (eqToIso (congrArg (fun k => derivedPullback (h k)) hij)))
    (Z : Lq₀ ⋙ Lp₀ ≅ Ls₀ ⋙ Lr₀)
    (hZ : HEq Z (derivedPullbackCompIso p₀ q₀ ≪≫
      derivedPullbackIsoOfPullbackModulesIso (RingedToposHom.pullbackModulesCompIso p₀ q₀ ≪≫ Zu ≪≫
        (RingedToposHom.pullbackModulesCompIso r₀ s₀).symm) ≪≫
      (derivedPullbackCompIso r₀ s₀).symm))
    (tq : ∀ M, q.toModulesHom.pullbackModules.obj (εT.toModulesHom.pullbackModules.obj M) ⟶
      εW.toModulesHom.pullbackModules.obj (q₀.toModulesHom.pullbackModules.obj M))
    (htq : ∀ M, HEq (tq M) ((RingedToposHom.pullbackModulesCompIso q εT).inv.app M ≫
      θq.hom.app M ≫ (RingedToposHom.pullbackModulesCompIso εW q₀).hom.app M))
    (tp : ∀ M, p.toModulesHom.pullbackModules.obj (εW.toModulesHom.pullbackModules.obj M) ⟶
      εW'.toModulesHom.pullbackModules.obj (p₀.toModulesHom.pullbackModules.obj M))
    (htp : ∀ M, HEq (tp M) ((RingedToposHom.pullbackModulesCompIso p εW).inv.app M ≫
      θp.hom.app M ≫ (RingedToposHom.pullbackModulesCompIso εW' p₀).hom.app M))
    (ts : ∀ M, s.toModulesHom.pullbackModules.obj (εT.toModulesHom.pullbackModules.obj M) ⟶
      εT'.toModulesHom.pullbackModules.obj (s₀.toModulesHom.pullbackModules.obj M))
    (hts : ∀ M, HEq (ts M) ((RingedToposHom.pullbackModulesCompIso s εT).inv.app M ≫
      θs.hom.app M ≫ (RingedToposHom.pullbackModulesCompIso εT' s₀).hom.app M))
    (tr : ∀ M, r.toModulesHom.pullbackModules.obj (εT'.toModulesHom.pullbackModules.obj M) ⟶
      εW'.toModulesHom.pullbackModules.obj (r₀.toModulesHom.pullbackModules.obj M))
    (htr : ∀ M, HEq (tr M) ((RingedToposHom.pullbackModulesCompIso r εT').inv.app M ≫
      θr.hom.app M ≫ (RingedToposHom.pullbackModulesCompIso εW' r₀).hom.app M))
    (zu : ∀ M, p₀.toModulesHom.pullbackModules.obj (q₀.toModulesHom.pullbackModules.obj M) ⟶
      r₀.toModulesHom.pullbackModules.obj (s₀.toModulesHom.pullbackModules.obj M))
    (hzu : ∀ M, HEq (zu M) (Zu.hom.app M))
    (a : ∀ M, p.toModulesHom.pullbackModules.obj
        (q.toModulesHom.pullbackModules.obj (εT.toModulesHom.pullbackModules.obj M)) ⟶
      r.toModulesHom.pullbackModules.obj
        (s.toModulesHom.pullbackModules.obj (εT.toModulesHom.pullbackModules.obj M)))
    (ha : ∀ M, HEq (a M) ((RingedToposHom.pullbackModulesCompIso p q).inv.app
        (εT.toModulesHom.pullbackModules.obj M) ≫
          tpq.hom.app (εT.toModulesHom.pullbackModules.obj M) ≫
      (eqToIso (congrArg (fun k => (h k).toModulesHom.pullbackModules) hij)).hom.app
        (εT.toModulesHom.pullbackModules.obj M) ≫
          trs.inv.app (εT.toModulesHom.pullbackModules.obj M) ≫
      (RingedToposHom.pullbackModulesCompIso r s).hom.app (εT.toModulesHom.pullbackModules.obj M)))
    (hu : ∀ M, p.toModulesHom.pullbackModules.map (tq M) ≫
        tp (q₀.toModulesHom.pullbackModules.obj M) ≫
        εW'.toModulesHom.pullbackModules.map (zu M) =
      a M ≫ r.toModulesHom.pullbackModules.map (ts M) ≫ tr (s₀.toModulesHom.pullbackModules.obj M))
    (Y : DZT) :
    ρp.inv.app (Lq₀.obj Y) ≫ Lp.map (ρq.inv.app Y) ≫
        (cpq.hom ≫ c.hom ≫ crs.inv).app (LεT.obj Y) =
      LεW'.map (Z.hom.app Y) ≫ ρr.inv.app (Ls₀.obj Y) ≫ Lr.map (ρs.inv.app Y) := by
  obtain rfl : tq = _ := funext fun M => eq_of_heq (htq M)
  obtain rfl : tp = _ := funext fun M => eq_of_heq (htp M)
  obtain rfl : ts = _ := funext fun M => eq_of_heq (hts M)
  obtain rfl : tr = _ := funext fun M => eq_of_heq (htr M)
  obtain rfl : zu = _ := funext fun M => eq_of_heq (hzu M)
  obtain rfl : a = _ := funext fun M => eq_of_heq (ha M)
  subst hDZT hDZW hDZT' hDZW' hDET hDEW hDET' hDEW'
  obtain rfl := eq_of_heq hiDZT
  obtain rfl := eq_of_heq hiDZW
  obtain rfl := eq_of_heq hiDZT'
  obtain rfl := eq_of_heq hiDZW'
  obtain rfl := eq_of_heq hiDET
  obtain rfl := eq_of_heq hiDEW
  obtain rfl := eq_of_heq hiDET'
  obtain rfl := eq_of_heq hiDEW'
  obtain rfl := eq_of_heq hLq₀
  obtain rfl := eq_of_heq hLp₀
  obtain rfl := eq_of_heq hLs₀
  obtain rfl := eq_of_heq hLr₀
  obtain rfl := eq_of_heq hLq
  obtain rfl := eq_of_heq hLp
  obtain rfl := eq_of_heq hLs
  obtain rfl := eq_of_heq hLr
  obtain rfl := eq_of_heq hLεT
  obtain rfl := eq_of_heq hLεW
  obtain rfl := eq_of_heq hLεT'
  obtain rfl := eq_of_heq hLεW'
  obtain rfl := eq_of_heq hLhi
  obtain rfl := eq_of_heq hLhj
  obtain rfl := eq_of_heq hρq
  obtain rfl := eq_of_heq hρp
  obtain rfl := eq_of_heq hρs
  obtain rfl := eq_of_heq hρr
  obtain rfl := eq_of_heq hcpq
  obtain rfl := eq_of_heq hcrs
  obtain rfl := eq_of_heq hc
  obtain rfl := eq_of_heq hZ
  subst hij
  have fac_rs := fun M => Stacks.Cohomology.DerivedBaseChangeComposition.trans_hom_app_fac
      (derivedPullbackCompIso r s) (derivedPullbackIsoOfPullbackModulesIso trs) _ _
      (derivedPullbackCompComparison_app_comp_isoOfPullbackModulesIso_comparison_app r s trs M)
  refine Stacks.Cohomology.DerivedBaseChangeComposition.leftDerived_comparison_cube
    (Fq₀ := DerivedPushforward.pullbackMapHomotopy q₀)
        (Fp₀ := DerivedPushforward.pullbackMapHomotopy p₀)
        (Fs₀ := DerivedPushforward.pullbackMapHomotopy s₀)
        (Fr₀ := DerivedPushforward.pullbackMapHomotopy r₀)
        (FεT := DerivedPushforward.pullbackMapHomotopy εT)
        (FεW := DerivedPushforward.pullbackMapHomotopy εW)
        (FεT' := DerivedPushforward.pullbackMapHomotopy εT')
        (FεW' := DerivedPushforward.pullbackMapHomotopy εW')
        (Fq := DerivedPushforward.pullbackMapHomotopy q)
        (Fp := DerivedPushforward.pullbackMapHomotopy p)
        (Fs := DerivedPushforward.pullbackMapHomotopy s)
        (Fr := DerivedPushforward.pullbackMapHomotopy r)
    (αq₀ := derivedPullbackComparison q₀) (αp₀ := derivedPullbackComparison p₀)
    (αs₀ := derivedPullbackComparison s₀) (αr₀ := derivedPullbackComparison r₀)
    (αεT := derivedPullbackComparison εT) (αεW := derivedPullbackComparison εW)
    (αεT' := derivedPullbackComparison εT') (αεW' := derivedPullbackComparison εW')
    (αq := derivedPullbackComparison q) (αp := derivedPullbackComparison p)
    (αs := derivedPullbackComparison s) (αr := derivedPullbackComparison r)
    (θq := pullbackMapHomotopySquareIso q εT εW q₀ θq)
    (θp := pullbackMapHomotopySquareIso p εW εW' p₀ θp)
    (θs := pullbackMapHomotopySquareIso s εT εT' s₀ θs)
    (θr := pullbackMapHomotopySquareIso r εT' εW' r₀ θr)
    (ρq := _) (ρp := _) (ρs := _) (ρr := _)
    (facq := derivedPullbackSquareIso_hom_app_comparison q εT εW q₀ θq)
    (facp := derivedPullbackSquareIso_hom_app_comparison p εW εW' p₀ θp)
    (facs := derivedPullbackSquareIso_hom_app_comparison s εT εT' s₀ θs)
    (facr := derivedPullbackSquareIso_hom_app_comparison r εT' εW' r₀ θr)
    (Θu := (pullbackMapHomotopyCompIso p q ≪≫
        Stacks.Homology.mapHomotopyCategoryIso tpq (ComplexShape.up ℤ)).hom ≫
      (eqToIso (congrArg (fun k => DerivedPushforward.pullbackMapHomotopy (h k))
        (rfl : i = i))).hom ≫
      (pullbackMapHomotopyCompIso r s ≪≫
        Stacks.Homology.mapHomotopyCategoryIso trs (ComplexShape.up ℤ)).inv)
    (Θ := _) (facΘ := Stacks.Cohomology.DerivedBaseChangeComposition.fac_vcomp_inv
      (fun M => Stacks.Cohomology.DerivedBaseChangeComposition.trans_hom_app_fac
        (derivedPullbackCompIso p q) (derivedPullbackIsoOfPullbackModulesIso tpq) _ _
        (derivedPullbackCompComparison_app_comp_isoOfPullbackModulesIso_comparison_app p q tpq M))
      (Stacks.Cohomology.DerivedBaseChangeComposition.eqToIso_congr_fac
        (fun k => derivedPullback (h k)) (fun k => DerivedPushforward.pullbackMapHomotopy (h k))
        (fun k => derivedPullbackComparison (h k)) (rfl : i = i))
      fac_rs)
    (Zu := (pullbackMapHomotopySquareIso p₀ q₀ r₀ s₀ _).hom)
    (Z := _) (facZ := derivedPullbackSquareIso_hom_app_comparison p₀ q₀ r₀ s₀ _)
    (αrs := derivedPullbackComparison (h i))
    (u₁ := (pullbackMapHomotopyCompIso r s ≪≫
        Stacks.Homology.mapHomotopyCategoryIso trs (ComplexShape.up ℤ)).hom)
    (e₁ := _) (fac₁ := fac_rs)
    (αH := derivedPullbackComparison (εT.comp (h i)))
    (W := HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
    (e₂ := derivedPullbackCompIso (h i) εT) (u₂ := (pullbackMapHomotopyCompIso (h i) εT).hom)
    (fac₂ := derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app (h i) εT)
    (hu := pullbackMapHomotopySquareIso_cube q₀ p₀ s₀ r₀ q p s r εT εW εT' εW' θq θp θs θr h rfl
      tpq trs Zu hu) (Y := Y)

end Cube

end

end Stacks.Cohomology.DerivedPullbackCompositionOfToposHom
