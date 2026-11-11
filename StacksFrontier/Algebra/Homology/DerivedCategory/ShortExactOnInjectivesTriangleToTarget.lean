module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedShortExactOnInjectivesTriangle
import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.UnboundedTriangle

/-!
# The distinguished triangle of a sequence of functors exact on injectives, to another category

Let `A` be a Grothendieck abelian category and `B` an abelian category, both with chosen
unbounded derived categories, and let `F ⟶ G ⟶ H` be a short complex of additive functors
`A ⥤ B` whose short complex is short exact at every *injective* object of `A`.  For arbitrary
right derived functors `RF`, `RG`, `RH : D(A) ⥤ D(B)` of `F`, `G`, `H` this file produces maps
`RF ⟶ RG ⟶ RH`, pinned down as the derived versions of the two given maps, and a connecting map
`δ : RH ⟶ RF ⋙ (-)⟦1⟧` such that

`RF(K) ⟶ RG(K) ⟶ RH(K) ⟶ RF(K)⟦1⟧`

is distinguished for every object `K` of `D(A)`.

This is `Stacks.ShortExactOnInjectives.exists_derivedTriangle_of_shortExactOnInjectives` with
the endofunctors of `A` replaced by functors to a second abelian category, which is what a
triangle of derived *global sections* functors `D(A) ⥤ D(Ab)` needs.  The argument is the same:
the functorial K-injective resolution of Tag 079P has injective terms, so the three functors
applied degreewise to it give a short exact sequence of complexes in `B`, whose triangle in
`D(B)` is transported to the chosen right derived functors.

## Main definitions

* `Stacks.ShortExactOnInjectivesToTarget.complexDerivedUnit`: the derived unit of an additive
  functor `A ⥤ B`, read on cochain complexes.
* `Stacks.ShortExactOnInjectivesToTarget.resolutionDerivedIso`: a chosen right derived functor,
  evaluated on a complex, is computed by the functorial K-injective resolution.

## Main results

* `Stacks.ShortExactOnInjectivesToTarget.resolutionDerivedIso_fac`: the comparison isomorphisms
  are compatible with a map of the underlying functors.
* `Stacks.ShortExactOnInjectivesToTarget.exists_derivedTriangle_of_shortExactOnInjectives`: the
  maps and the distinguished triangle, from the right-derived-functor data alone.

## References

* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe w t t' v v' u u'

namespace Stacks.ShortExactOnInjectivesToTarget

variable (A : Type u) [Category.{v} A] [Abelian A] (B : Type u') [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{t} A] [HasDerivedCategory.{t'} B]

/-- The derived unit of `F : A ⥤ B`, read on cochain complexes rather than on the homotopy
category. -/
public def complexDerivedUnitHomotopy
    (F : A ⥤ B) [F.Additive]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF) :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (HomotopyCategory.quotient B (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⟶
      (HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⋙ RF where
  app K := α.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)
  naturality _ _ f := α.naturality ((HomotopyCategory.quotient _ _).map f)

/-- The derived unit of `F : A ⥤ B`, read on cochain complexes and transported to the
localization functors `DerivedCategory.Q`. -/
public def complexDerivedUnit
    (F : A ⥤ B) [F.Additive]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF) :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RF :=
  Functor.whiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso B).inv ≫
    complexDerivedUnitHomotopy A B F RF α ≫
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso A).hom RF

/-- The three factors of `complexDerivedUnit`, spelled out. -/
public lemma complexDerivedUnit_app
    (F : A ⥤ B) [F.Additive]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    (K : CochainComplex A ℤ) :
    (complexDerivedUnit A B F RF α).app K =
      (DerivedCategory.quotientCompQhIso B).inv.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        α.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
          RF.map ((DerivedCategory.quotientCompQhIso A).hom.app K) :=
  rfl

/-- The derived units are compatible with a map of the underlying functors. -/
public lemma complexDerivedUnit_fac
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    {RF RG : DerivedCategory A ⥤ DerivedCategory B}
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    (β : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RG)
    (τ : F ⟶ G) (r : RF ⟶ RG)
    (h : α ≫ Functor.whiskerLeft DerivedCategory.Qh r =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ))
        DerivedCategory.Qh ≫ β) :
    complexDerivedUnit A B F RF α ≫ Functor.whiskerLeft DerivedCategory.Q r =
      Functor.whiskerRight (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ))
        DerivedCategory.Q ≫ complexDerivedUnit A B G RG β := by
  refine NatTrans.ext (funext fun K => ?_)
  have hn : RF.map ((DerivedCategory.quotientCompQhIso A).hom.app K) ≫
        r.app (DerivedCategory.Q.obj K) =
      r.app (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) ≫
        RG.map ((DerivedCategory.quotientCompQhIso A).hom.app K) :=
    r.naturality ((DerivedCategory.quotientCompQhIso A).hom.app K)
  have hh : α.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
        r.app (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K)) ≫
        β.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) :=
    congr_app h ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)
  have hi : DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K) ≫
        (DerivedCategory.quotientCompQhIso B).inv.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      (DerivedCategory.quotientCompQhIso B).inv.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K)) :=
    (DerivedCategory.quotientCompQhIso B).inv.naturality
      ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K)
  exact Stacks.Cohomology.RestrictionCover.comp_square_chase _ _ _ _ _ _ _ _ _ _ hn hh hi

section

variable [IsGrothendieckAbelian.{w} A]

/-- The derived unit of `F` is invertible on a K-injective complex, read at the level of
cochain complexes. -/
public lemma complexDerivedUnit_app_isIso_of_isKInjective
    (F : A ⥤ B) [F.Additive]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (I : CochainComplex A ℤ) [I.IsKInjective] :
    IsIso ((complexDerivedUnit A B F RF α).app I) := by
  have hα : IsIso (α.app ((HomotopyCategory.quotient _ _).obj I)) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (Stacks.ShortExactOnInjectives.exists_quasiIso_kInjective A)).2
      DerivedCategory.Qh RF α I inferInstance
  rw [complexDerivedUnit_app]
  exact IsIso.comp_isIso'
    ((DerivedCategory.quotientCompQhIso B).symm.app _).isIso_hom
    (IsIso.comp_isIso' hα
      (RF.mapIso ((DerivedCategory.quotientCompQhIso A).app I)).isIso_hom)

/-- A chosen right derived functor is computed by the functorial K-injective resolution:
applying `F` degreewise to the resolution and localizing agrees with `RF`. -/
public def resolutionDerivedIso
    (F : A ⥤ B) [F.Additive]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] :
    Stacks.Injectives.kInjectiveResolutionFunctor A ⋙
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ RF := by
  have ha : ∀ K, IsIso ((Functor.whiskerLeft
      (Stacks.Injectives.kInjectiveResolutionFunctor A)
      (complexDerivedUnit A B F RF α)).app K) := fun K =>
    complexDerivedUnit_app_isIso_of_isKInjective A B F RF α _
  have hb : ∀ K, IsIso ((Functor.whiskerRight
      (Stacks.Injectives.kInjectiveResolutionInclusion A)
      (DerivedCategory.Q ⋙ RF)).app K) := by
    intro K
    exact RF.map_isIso (DerivedCategory.Q.map
      ((Stacks.Injectives.kInjectiveResolutionInclusion A).app K))
  have : IsIso (Functor.whiskerLeft
      (Stacks.Injectives.kInjectiveResolutionFunctor A)
      (complexDerivedUnit A B F RF α)) := NatIso.isIso_of_isIso_app _
  have : IsIso (Functor.whiskerRight
      (Stacks.Injectives.kInjectiveResolutionInclusion A)
      (DerivedCategory.Q ⋙ RF)) := NatIso.isIso_of_isIso_app _
  exact asIso (Functor.whiskerLeft
      (Stacks.Injectives.kInjectiveResolutionFunctor A)
      (complexDerivedUnit A B F RF α)) ≪≫
    (asIso (Functor.whiskerRight
      (Stacks.Injectives.kInjectiveResolutionInclusion A)
      (DerivedCategory.Q ⋙ RF))).symm

/-- The two legs of `resolutionDerivedIso`, spelled out. -/
public lemma resolutionDerivedIso_hom_app
    (F : A ⥤ B) [F.Additive]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (K : CochainComplex A ℤ) :
    (resolutionDerivedIso A B F RF α).hom.app K =
      (complexDerivedUnit A B F RF α).app
          ((Stacks.Injectives.kInjectiveResolutionFunctor A).obj K) ≫
        inv (RF.map (DerivedCategory.Q.map
          ((Stacks.Injectives.kInjectiveResolutionInclusion A).app K))) := by
  simp [resolutionDerivedIso, NatIso.isIso_inv_app]

/-- The comparison isomorphisms are compatible with a map of the underlying functors. -/
public lemma resolutionDerivedIso_fac
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    {RF RG : DerivedCategory A ⥤ DerivedCategory B}
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    (β : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RG)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    [RG.IsRightDerivedFunctor β (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (τ : F ⟶ G) (r : RF ⟶ RG)
    (h : α ≫ Functor.whiskerLeft DerivedCategory.Qh r =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ))
        DerivedCategory.Qh ≫ β)
    (K : CochainComplex A ℤ) :
    (resolutionDerivedIso A B F RF α).hom.app K ≫ r.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app
        ((Stacks.Injectives.kInjectiveResolutionFunctor A).obj K)) ≫
        (resolutionDerivedIso A B G RG β).hom.app K := by
  rw [resolutionDerivedIso_hom_app, resolutionDerivedIso_hom_app]
  exact Stacks.Cohomology.RestrictionCover.comp_inv_chase _ _ _ _ _ _ _
    (Stacks.Cohomology.RestrictionCover.inv_comp_comm _ _ _ _ (r.naturality (DerivedCategory.Q.map
      ((Stacks.Injectives.kInjectiveResolutionInclusion A).app K))))
    (congr_app (complexDerivedUnit_fac A B α β τ r h)
      ((Stacks.Injectives.kInjectiveResolutionFunctor A).obj K))

omit [HasDerivedCategory A] [HasDerivedCategory B] [IsGrothendieckAbelian.{w, v, u} A] in
/-- The maps of complexes induced by natural transformations composing to zero compose to zero. -/
public lemma mapHomologicalComplex_app_comp_eq_zero {F G H : A ⥤ B}
    [F.Additive] [G.Additive] [H.Additive]
    {f : F ⟶ G} {g : G ⟶ H} (hfg : f ≫ g = 0) (K : CochainComplex A ℤ) :
    (NatTrans.mapHomologicalComplex f (ComplexShape.up ℤ)).app K ≫
      (NatTrans.mapHomologicalComplex g (ComplexShape.up ℤ)).app K = 0 := by
  ext n : 1
  exact NatTrans.congr_app hfg (K.X n)

omit [HasDerivedCategory A] [HasDerivedCategory B] in
/-- A sequence of additive functors which is short exact at every injective object is short
exact on the K-injective resolution of every complex. -/
public lemma shortExact_mapHomologicalComplex_kInjectiveResolution
    (F G H : A ⥤ B) [F.Additive] [G.Additive] [H.Additive]
    (f : F ⟶ G) (g : G ⟶ H) (hfg : f ≫ g = 0)
    (hS : ∀ (I : A) [Injective I],
      (ShortComplex.mk (f.app I) (g.app I) (NatTrans.congr_app hfg I)).ShortExact)
    (K : CochainComplex A ℤ) :
    (ShortComplex.mk
      ((NatTrans.mapHomologicalComplex f (ComplexShape.up ℤ)).app
        ((Stacks.Injectives.kInjectiveResolutionFunctor A).obj K))
      ((NatTrans.mapHomologicalComplex g (ComplexShape.up ℤ)).app
        ((Stacks.Injectives.kInjectiveResolutionFunctor A).obj K))
      (mapHomologicalComplex_app_comp_eq_zero A B hfg _)).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  exact fun n => hS _

/-- Given three additive functors `A ⥤ B`, maps `f : F ⟶ G`, `g : G ⟶ H` composing to zero
whose short complex is short exact at every injective object, and chosen right derived functors
identified on K-injective resolutions by `eF`, `eG`, `eH`, there is a connecting map making the
triangle of the derived maps distinguished at every object. -/
public def derivedTriangleOfShortExactOnInjectives
    (F G H : A ⥤ B) [F.Additive] [G.Additive] [H.Additive]
    (f : F ⟶ G) (g : G ⟶ H) (hfg : f ≫ g = 0)
    (hS : ∀ (I : A) [Injective I],
      (ShortComplex.mk (f.app I) (g.app I) (NatTrans.congr_app hfg I)).ShortExact)
    (RF RG RH : DerivedCategory A ⥤ DerivedCategory B)
    (eF : Stacks.Injectives.kInjectiveResolutionFunctor A ⋙
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ RF)
    (eG : Stacks.Injectives.kInjectiveResolutionFunctor A ⋙
      G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ RG)
    (eH : Stacks.Injectives.kInjectiveResolutionFunctor A ⋙
      H.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ RH)
    (rf : RF ⟶ RG) (rg : RG ⟶ RH)
    (hf : ∀ K, eF.hom.app K ≫ rf.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex f (ComplexShape.up ℤ)).app
        ((Stacks.Injectives.kInjectiveResolutionFunctor A).obj K)) ≫
          eG.hom.app K)
    (hg : ∀ K, eG.hom.app K ≫ rg.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex g (ComplexShape.up ℤ)).app
        ((Stacks.Injectives.kInjectiveResolutionFunctor A).obj K)) ≫
          eH.hom.app K) :
    {δ : RH ⟶ RF ⋙ shiftFunctor (DerivedCategory B) (1 : ℤ) //
      ∀ K, Triangle.mk (rf.app K) (rg.app K) (δ.app K) ∈
        distTriang (DerivedCategory B)} := by
  have hs := shortExact_mapHomologicalComplex_kInjectiveResolution A B F G H f g hfg hS
  let d : Stacks.Injectives.kInjectiveResolutionFunctor A ⋙
      H.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      (Stacks.Injectives.kInjectiveResolutionFunctor A ⋙
        F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙
        shiftFunctor (DerivedCategory B) (1 : ℤ) :=
    { app := fun K => DerivedCategory.triangleOfSESδ (hs K)
      naturality := fun K L k =>
        (DerivedCategory.triangleOfSESδ_naturality (hs K) (hs L)
          { τ₁ := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
              ((Stacks.Injectives.kInjectiveResolutionFunctor A).map k)
            τ₂ := (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
              ((Stacks.Injectives.kInjectiveResolutionFunctor A).map k)
            τ₃ := (H.mapHomologicalComplex (ComplexShape.up ℤ)).map
              ((Stacks.Injectives.kInjectiveResolutionFunctor A).map k)
            comm₁₂ := (NatTrans.mapHomologicalComplex f (ComplexShape.up ℤ)).naturality
              ((Stacks.Injectives.kInjectiveResolutionFunctor A).map k)
            comm₂₃ := (NatTrans.mapHomologicalComplex g (ComplexShape.up ℤ)).naturality
              ((Stacks.Injectives.kInjectiveResolutionFunctor A).map k) }).symm }
  let b : DerivedCategory.Q ⋙ RH ⟶
      DerivedCategory.Q ⋙ (RF ⋙ shiftFunctor (DerivedCategory B) (1 : ℤ)) :=
    eH.inv ≫ d ≫ Functor.whiskerRight eF.hom (shiftFunctor (DerivedCategory B) (1 : ℤ))
  let E := (Functor.whiskeringLeft (CochainComplex A ℤ)
    (DerivedCategory A) (DerivedCategory B)).obj DerivedCategory.Q
  have : E.Full := Localization.full_whiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) _
  let δ : RH ⟶ RF ⋙ shiftFunctor (DerivedCategory B) (1 : ℤ) := E.preimage b
  have hd (K : CochainComplex A ℤ) :
      δ.app (DerivedCategory.Q.obj K) = b.app K :=
    NatTrans.congr_app (E.map_preimage b) K
  have hdist (K : CochainComplex A ℤ) :
      Triangle.mk (rf.app (DerivedCategory.Q.obj K)) (rg.app (DerivedCategory.Q.obj K))
        (δ.app (DerivedCategory.Q.obj K)) ∈ distTriang (DerivedCategory B) := by
    refine isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished (hs K)) _
      (Iso.symm (Triangle.isoMk _ _ (eF.app K) (eG.app K) (eH.app K) (hf K).symm (hg K).symm ?_))
    dsimp [DerivedCategory.triangleOfSES]
    rw [hd]
    dsimp [b, d]
    simp only [Iso.hom_inv_id_app_assoc]
  refine ⟨δ, fun K => ?_⟩
  exact isomorphic_distinguished _ (hdist (DerivedCategory.Q.objPreimage K)) _
    (Iso.symm (Triangle.isoMk _ _ (RF.mapIso (DerivedCategory.Q.objObjPreimageIso K))
      (RG.mapIso (DerivedCategory.Q.objObjPreimageIso K))
      (RH.mapIso (DerivedCategory.Q.objObjPreimageIso K))
      (rf.naturality (DerivedCategory.Q.objObjPreimageIso K).hom).symm
      (rg.naturality (DerivedCategory.Q.objObjPreimageIso K).hom).symm
      (δ.naturality (DerivedCategory.Q.objObjPreimageIso K).hom).symm))

/-- **The distinguished triangle of a short complex of functors exact on injectives**, from the
right-derived-functor data alone.  Given additive functors `F ⟶ G ⟶ H : A ⥤ B` composing to
zero and short exact at every injective object of `A`, and arbitrary right derived functors
`RF`, `RG`, `RH : D(A) ⥤ D(B)` with units `αF`, `αG`, `αH`, there are maps `rf : RF ⟶ RG` and
`rg : RG ⟶ RH` — pinned down as the derived versions of `f` and `g` by their composites with
the units — and a connecting map `δ : RH ⟶ RF⟦1⟧` making
`RF(K) ⟶ RG(K) ⟶ RH(K) ⟶ RF(K)⟦1⟧` distinguished for every `K`. -/
public theorem exists_derivedTriangle_of_shortExactOnInjectives
    (F G H : A ⥤ B) [F.Additive] [G.Additive] [H.Additive]
    (f : F ⟶ G) (g : G ⟶ H) (hfg : f ≫ g = 0)
    (hS : ∀ (I : A) [Injective I],
      (ShortComplex.mk (f.app I) (g.app I) (NatTrans.congr_app hfg I)).ShortExact)
    (RF RG RH : DerivedCategory A ⥤ DerivedCategory B)
    (αF : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    (αG : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RG)
    (αH : H.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RH)
    [RF.IsRightDerivedFunctor αF (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    [RG.IsRightDerivedFunctor αG (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    [RH.IsRightDerivedFunctor αH (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] :
    ∃ (rf : RF ⟶ RG) (rg : RG ⟶ RH)
      (δ : RH ⟶ RF ⋙ shiftFunctor (DerivedCategory B) (1 : ℤ)),
      Functor.whiskerRight (NatTrans.mapHomotopyCategory f (ComplexShape.up ℤ))
          DerivedCategory.Qh ≫ αG =
        αF ≫ Functor.whiskerLeft DerivedCategory.Qh rf ∧
      Functor.whiskerRight (NatTrans.mapHomotopyCategory g (ComplexShape.up ℤ))
          DerivedCategory.Qh ≫ αH =
        αG ≫ Functor.whiskerLeft DerivedCategory.Qh rg ∧
      ∀ K, Triangle.mk (rf.app K) (rg.app K) (δ.app K) ∈ distTriang (DerivedCategory B) := by
  let rf := RF.rightDerivedNatTrans RG αF αG
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory f (ComplexShape.up ℤ))
      DerivedCategory.Qh)
  let rg := RG.rightDerivedNatTrans RH αG αH
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory g (ComplexShape.up ℤ))
      DerivedCategory.Qh)
  have hrf : Functor.whiskerRight (NatTrans.mapHomotopyCategory f (ComplexShape.up ℤ))
        DerivedCategory.Qh ≫ αG = αF ≫ Functor.whiskerLeft DerivedCategory.Qh rf := by
    simp [rf]
  have hrg : Functor.whiskerRight (NatTrans.mapHomotopyCategory g (ComplexShape.up ℤ))
        DerivedCategory.Qh ≫ αH = αG ≫ Functor.whiskerLeft DerivedCategory.Qh rg := by
    simp [rg]
  obtain ⟨δ, hδ⟩ := derivedTriangleOfShortExactOnInjectives A B F G H f g hfg hS RF RG RH
    (resolutionDerivedIso A B F RF αF) (resolutionDerivedIso A B G RG αG)
    (resolutionDerivedIso A B H RH αH) rf rg
    (fun K => resolutionDerivedIso_fac A B αF αG f rf hrf.symm K)
    (fun K => resolutionDerivedIso_fac A B αG αH g rg hrg.symm K)
  exact ⟨rf, rg, δ, hrf, hrg, hδ⟩

end

end Stacks.ShortExactOnInjectivesToTarget

end
