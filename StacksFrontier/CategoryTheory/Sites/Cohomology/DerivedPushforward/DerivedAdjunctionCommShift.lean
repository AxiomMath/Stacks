module

public import Mathlib.Algebra.Homology.BifunctorShift
public import StacksFrontier.Algebra.Homology.HomotopyCategory.AdjunctionCommShift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.DerivedAdjunctionOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PullbackInvertsQuasiIsoOfToposHom

/-!
# The derived adjunction of a morphism of ringed topoi commutes with the shift

Let `f` be a morphism of ringed topoi. The adjunction `Lf^* ⊣ Rf_*` of Stacks 07A6
(`Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction`) is compatible with the shifts
of the two derived categories, for the shifts `Lf^*` and `Rf_*` carry as total derived functors.
On a K-flat complex `M` with flat terms the unit at `M` is the degreewise unit followed by the
comparison maps of `Rf_*` and of `Lf^*`, the latter invertible there; each of these commutes
with the shift, the K-flat complexes with flat terms are stable under translation, and every
object of the derived category is the image of one.

## Main results

* `CochainComplex.KFlatBifunctor.kFlat_shift`: a translate of a K-flat complex is K-flat.
* `Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.isKFlat_isStableUnderShift`: the
  K-flat complexes with flat terms are stable under translation.
* `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction_unit_commShift` and
  `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction_commShift`: the unit of
  `Lf^* ⊣ Rf_*` commutes with the shift, so the adjunction is compatible with the shifts.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (IsKFlat hasResolutions_isKFlat)

noncomputable section

namespace CochainComplex.KFlatBifunctor

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Preadditive A] [Preadditive B] [HasZeroObject B] [HasBinaryBiproducts B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]

omit [HasZeroObject B] [HasBinaryBiproducts B] in
/-- A translate of a complex which is K-flat for `F` is K-flat for `F`: the total complex of
`F(G, K[n])` is the translate of that of `F(G, K)`. -/
theorem kFlat_shift {K : CochainComplex B ℤ} (hK : KFlat F K) (n : ℤ) : KFlat F (K⟦n⟧) := by
  intro G hG
  have h := hK G hG
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at h ⊢
  refine (HomotopyCategory.subcategoryAcyclic D).prop_of_iso ?_
    ((HomotopyCategory.subcategoryAcyclic D).le_shift n _ h)
  exact ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).commShiftIso n).symm.app _ ≪≫
    (HomotopyCategory.quotient D (ComplexShape.up ℤ)).mapIso
      (CochainComplex.mapBifunctorShift₂Iso G K F n).symm

end CochainComplex.KFlatBifunctor

universe v u w v' u' w'

namespace Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

variable {Y : RingedTopos.{v', u', w'}}
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [HasSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]

/-- The K-flat complexes with flat terms are stable under translation. -/
instance isKFlat_isStableUnderShift : (IsKFlat (Y := Y)).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun M hM => by
    have e : (M⟦n⟧).as = M.as⟦n⟧ := by
      cases M
      with_unfolding_all rfl
    change IsKFlat (M⟦n⟧)
    unfold IsKFlat
    rw [e]
    exact ⟨CochainComplex.KFlatBifunctor.kFlat_shift _ hM.1 n, fun i => hM.2 (i + n)⟩⟩

end Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

namespace Stacks.Cohomology.DerivedPullbackOfToposHom

open AlgebraicGeometry.RingedToposHom

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w')]
  [IsGrothendieckAbelian.{w}
    (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)))]

attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

/-- Every object of `D(𝒪')` is the image of a K-flat complex with flat terms. -/
instance essSurj_isKFlat_ι_comp_Qh :
    ((IsKFlat (Y := Y)).ι ⋙ DerivedCategory.Qh).EssSurj where
  mem_essImage Z := by
    obtain ⟨M, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := DerivedCategory.Qh) Z
    obtain ⟨K, hK, s, hs⟩ := hasResolutions_isKFlat (Y := Y) M
    exact ⟨⟨K, hK⟩, ⟨Localization.isoOfHom DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ _) s hs ≪≫ e⟩⟩

omit [IsGrothendieckAbelian.{w}
  (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))] in
/-- The comparison map `Lf^* ∘ Q ⟶ Q ∘ f^*` is invertible on a K-flat complex with flat terms. -/
private theorem isIso_derivedPullbackComparison_app_of_isKFlat (f : RingedToposHom X Y)
    {M : HomotopyCategory
      (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))
      (ComplexShape.up ℤ)} (hM : IsKFlat M) :
    IsIso ((derivedPullbackComparison f).app M) :=
  isIso_derivedPullbackComparison_app f IsKFlat (fun N => hasResolutions_isKFlat (Y := Y) N)
    (pullbackInvertsQuasiIso_isKFlat f) M hM

/-- Where the comparison map is invertible, the unit of `Lf^* ⊣ Rf_*` is the degreewise unit
followed by the comparison maps of `Rf_*` and of `Lf^*`. -/
private theorem derivedAdjunction_unit_app_eq (f : RingedToposHom X Y)
    (M : HomotopyCategory
      (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))
      (ComplexShape.up ℤ)) [IsIso ((derivedPullbackComparison f).app M)] :
    (derivedAdjunction f).unit.app (DerivedCategory.Qh.obj M) =
      DerivedCategory.Qh.map ((pullbackAdjPushforwardMapHomotopy f).unit.app M) ≫
        ((pushforwardOnHomotopy (X := X) (Y := Y) f).totalRightDerivedUnit DerivedCategory.Qh
          (sourceQuasiIso X)).app ((pullbackMapHomotopy f).obj M) ≫
        inv ((derivedPushforward (X := X) (Y := Y) f).map
          ((derivedPullbackComparison f).app M)) := by
  rw [← Category.assoc, IsIso.eq_comp_inv]
  exact derivedPullbackPushforwardAdjunction_unit_fac f (kFlatLeftDerivedPullback f) M

/-- **The unit of `Lf^* ⊣ Rf_*` commutes with the shift.** -/
instance derivedAdjunction_unit_commShift (f : RingedToposHom X Y) :
    NatTrans.CommShift (derivedAdjunction f).unit ℤ := by
  let P := IsKFlat (Y := Y)
  let Qh := (DerivedCategory.Qh : HomotopyCategory
    (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))
    (ComplexShape.up ℤ) ⥤ _)
  let QhX := (DerivedCategory.Qh : HomotopyCategory
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))
    (ComplexShape.up ℤ) ⥤ _)
  let pb := pullbackMapHomotopy f
  let pf := pushforwardMapHomotopy f
  let Lf := derivedPullback f
  let Rf := derivedPushforward (X := X) (Y := Y) f
  let α := derivedPullbackComparison f
  let β := (pushforwardOnHomotopy (X := X) (Y := Y) f).totalRightDerivedUnit DerivedCategory.Qh
    (sourceQuasiIso X)
  let C := Functor.whiskerLeft P.ι (Functor.whiskerRight α Rf)
  have hα : ∀ M : P.FullSubcategory, IsIso (α.app M.obj) := fun M =>
    isIso_derivedPullbackComparison_app_of_isKFlat f M.property
  have : IsIso C := by
    have : ∀ M, IsIso (C.app M) := fun M => by
      have := hα M
      exact inferInstanceAs (IsIso (Rf.map (α.app M.obj)))
    exact NatIso.isIso_of_isIso_app _
  have : NatTrans.CommShift (inv C) ℤ := NatTrans.CommShift.of_isIso C ℤ
  have : NatTrans.CommShift (pullbackAdjPushforwardMapHomotopy f).unit ℤ :=
    Adjunction.commShift_mapHomotopyCategory_unit (pullbackAdjPushforwardModules f)
  refine NatTrans.commShift_of_whiskerLeft (P.ι ⋙ Qh) _ ?_
  refine NatTrans.commShift_of_eq (θ :=
    (P.ι ⋙ Qh).rightUnitor.hom ≫ Functor.whiskerLeft P.ι Qh.leftUnitor.inv ≫
      Functor.whiskerLeft P.ι (Functor.whiskerRight (pullbackAdjPushforwardMapHomotopy f).unit Qh) ≫
      Functor.whiskerLeft P.ι (Functor.associator pb pf Qh).hom ≫
      Functor.whiskerLeft P.ι (Functor.whiskerLeft pb β) ≫
      Functor.whiskerLeft P.ι (Functor.associator pb QhX Rf).inv ≫
      inv C ≫
      Functor.whiskerLeft P.ι (Functor.associator Qh Lf Rf).hom ≫
      (Functor.associator P.ι Qh (Lf ⋙ Rf)).inv) ?_
  ext M
  have := hα M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.rightUnitor_hom_app,
    Functor.leftUnitor_inv_app, NatIso.isIso_inv_app]
  refine (derivedAdjunction_unit_app_eq f M.obj).trans ?_
  let DY := DerivedCategory
    (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))
  exact ((Category.id_comp (obj := DY) _).trans ((Category.id_comp (obj := DY) _).trans
    (congrArg (_ ≫ ·) ((Category.id_comp (obj := DY) _).trans (congrArg (_ ≫ ·)
      ((Category.id_comp (obj := DY) _).trans (Category.comp_id (obj := DY) _))))))).symm

/-- **The adjunction `Lf^* ⊣ Rf_*` of Stacks 07A6 is compatible with the shifts** of the two
derived categories, for the shifts `Lf^*` and `Rf_*` carry as total derived functors. -/
instance derivedAdjunction_commShift (f : RingedToposHom X Y) :
    (derivedAdjunction f).CommShift ℤ :=
  Adjunction.CommShift.mk' _ _ inferInstance

end Stacks.Cohomology.DerivedPullbackOfToposHom
