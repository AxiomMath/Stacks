module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.OnePointCupProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalCupProductThroughThePoint

/-!
# The naive cup product on global sections and the global cup product

Let `(S, 𝒪_S)` be a ringed space, `A = Γ(S, 𝒪_S)` and `π : S ⟶ ({*}, A)` the morphism to the
coefficient point.  This file reads [Stacks, Tag 0FP3] for `π` on global sections over the
point.

## Main results

* `Stacks.Cohomology.DerivedGlobalCupProduct.pointNaiveCupProduct_relativeCupProduct`:
  derived global sections on the point of Stacks 0FP3 for `π`, precomposed with the unit
  `Γ ⟶ RΓ` and with the canonical map to the total tensor complex of the sections.

## Implementation notes

The total tensor complex in the last factor of `pointNaiveCupProduct_relativeCupProduct` is
written `Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} S.sheaf`.  That is the spelling
of the sheaf of rings carried by `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules`,
which is what indexes `K` and `M`, and by the target of
`Stacks.Cohomology.DerivedPullbackTensor.derivedToTensorNatTrans` — the other side of the same
equation.  It must be written out and not left to be recovered: the tensor product's instance
arguments fix its ring sheaf, so an argument given in any other spelling of the same sheaf is a
metavariable until the total complex is unified with the type of `K` and `M`, and that
unification is not first order.  Giving the sheaf of rings as `⟨S.presheaf, S.IsSheaf⟩` here
costs more than 200 000 heartbeats in `whnf` and the statement does not elaborate.
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedPullbackTensor
open Stacks.Cohomology.DerivedRelativeCupProduct
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.DerivedSectionsOnAPoint
open Stacks.Cohomology.GlobalKunneth
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces
open Stacks.DerivedTensor.RingedSite
open CochainComplex.DerivedTensor.ToTotal (canonicalDerivedToTensorNatTrans)
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedGlobalCupProduct

attribute [local instance] HasDerivedCategory.standard

/-- A functor on a product category sends a composite of pairs of morphisms to the composite. -/
private theorem map_comp_mkHom {C D : Type*} [Category* C] [Category* D] (A : C × C ⥤ D)
    {x y z x' y' z' : C} (f : x ⟶ y) (g : y ⟶ z) (f' : x' ⟶ y') (g' : y' ⟶ z') :
    A.map ((f ≫ g) ×ₘ (f' ≫ g')) = A.map (f ×ₘ f') ≫ A.map (g ×ₘ g') :=
  A.map_comp (f ×ₘ f') (g ×ₘ g')

/-- The paste behind `pointNaiveCupProduct_relativeCupProduct`, with every object and morphism
a variable. -/
theorem paste_naive_relative {C D : Type*} [Category* C] [Category* D]
    (A : C × C ⥤ C) (R : D ⥤ C) (B : D × D ⥤ D)
    {a b S0 S1 S2 : C} {G G' H H' T T' W Z : D}
    (ηa : a ⟶ R.obj G) (ηb : b ⟶ R.obj G') (pfK : G ⟶ H) (pfM : G' ⟶ H')
    (obG : A.obj (R.obj G, R.obj G') ⟶ R.obj (B.obj (G, G')))
    (obH : A.obj (R.obj H, R.obj H') ⟶ R.obj (B.obj (H, H')))
    (tX : B.obj (G, G') ⟶ T) (qnv : T ⟶ T') (pfT : T' ⟶ Z) (rel : B.obj (H, H') ⟶ W)
    (rτ : W ⟶ Z) (tY : A.obj (a, b) ⟶ S0) (ν : S0 ⟶ S1) (ηT : S1 ⟶ R.obj T) (qΓnv : S1 ⟶ S2)
    (ηT' : S2 ⟶ R.obj T')
    (hPG : tY ≫ ν ≫ ηT = A.map (ηa ×ₘ ηb) ≫ obG ≫ R.map tX)
    (h0FP3 : tX ≫ qnv ≫ pfT = B.map (pfK ×ₘ pfM) ≫ rel ≫ rτ)
    (hnatB : A.map (R.map pfK ×ₘ R.map pfM) ≫ obH = obG ≫ R.map (B.map (pfK ×ₘ pfM)))
    (hη : qΓnv ≫ ηT' = ηT ≫ R.map qnv) :
    A.map ((ηa ≫ R.map pfK) ×ₘ (ηb ≫ R.map pfM)) ≫ obH ≫ R.map rel ≫ R.map rτ =
      tY ≫ ν ≫ qΓnv ≫ ηT' ≫ R.map pfT :=
  calc A.map ((ηa ≫ R.map pfK) ×ₘ (ηb ≫ R.map pfM)) ≫ obH ≫ R.map rel ≫ R.map rτ
      = A.map (ηa ×ₘ ηb) ≫ (A.map (R.map pfK ×ₘ R.map pfM) ≫ obH) ≫ R.map rel ≫ R.map rτ := by
        rw [map_comp_mkHom]
        simp only [Category.assoc]
    _ = A.map (ηa ×ₘ ηb) ≫ obG ≫ R.map (B.map (pfK ×ₘ pfM) ≫ rel ≫ rτ) := by
        rw [hnatB]
        simp only [Category.assoc, R.map_comp]
    _ = (tY ≫ ν ≫ ηT) ≫ R.map qnv ≫ R.map pfT := by
        rw [← h0FP3, hPG]
        simp only [Category.assoc, R.map_comp]
    _ = tY ≫ ν ≫ qΓnv ≫ ηT' ≫ R.map pfT := by
        rw [reassoc_of% hη]
        simp only [Category.assoc]

variable (S : RingedSpace.{u, u})
  (K M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules S) ℤ)

/-- **The unit `Γ(S, K) ⟶ RΓ(S, K)` read on the point**: the unit of sections on the point at
`π_* K`, followed by the comparison `π_* ⟶ Rπ_*`. -/
abbrev pointSectionsUnit
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules S) ℤ) :
    DerivedCategory.Q.obj (((sectionsOverOpen (coeffPt S) ⊤).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj ((pushforwardComplex (toCoeffPoint S)).obj K)) ⟶
      (baseSections (coeffPt S)).obj
        ((derivedPushforward (toCoeffPoint S)).obj (DerivedCategory.Q.obj K)) :=
  sectionsUnitQ (coeffPt S) ⊤ ((pushforwardComplex (toCoeffPoint S)).obj K) ≫
    (baseSections (coeffPt S)).map (pushforwardComparisonQ (toCoeffPoint S) K)

/-- **Stacks 0FP3 for `π : S ⟶ ({*}, A)`, read on global sections over the point.**  The unit
in each factor, followed by the one-point cup product at `(Rπ_*K, Rπ_*M)`, `RΓ` of the relative
cup product of Stacks 0B68 and `RΓ Rπ_*` of the canonical map to the total tensor complex, is
the canonical map at the two complexes of sections, the naive cup product on the point, `Γ` of
the naive cup product of `π`, and the unit at `π_*Tot(K ⊗ M)`. -/
theorem pointNaiveCupProduct_relativeCupProduct :
    (coeffTensor S).map (pointSectionsUnit S K ×ₘ pointSectionsUnit S M) ≫
        adjunctionBitensorMap (onePointDerivedAdjunction ↥(baseRing S)) (coeffTensor S)
          (pointTensor S) (onePointDerivedTensorIso ↥(baseRing S)).hom
          ((derivedPushforward (toCoeffPoint S)).obj (DerivedCategory.Q.obj K))
          ((derivedPushforward (toCoeffPoint S)).obj (DerivedCategory.Q.obj M)) ≫
        (baseSections (coeffPt S)).map (relativeCupProduct (toCoeffPoint S)
          (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj M)) ≫
        (baseSections (coeffPt S)).map ((derivedPushforward (toCoeffPoint S)).map
          ((derivedToTensorNatTrans S).app (K, M))) =
      (canonicalDerivedToTensorNatTrans ↥(baseRing (coeffPt S))).app
          (((onePointSections ↥(baseRing S)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((pushforwardComplex (toCoeffPoint S)).obj K),
            ((onePointSections ↥(baseRing S)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((pushforwardComplex (toCoeffPoint S)).obj M)) ≫
        DerivedCategory.Q.map (onePointSectionsTotalIso ↥(baseRing S)
          ((pushforwardComplex (toCoeffPoint S)).obj K)
          ((pushforwardComplex (toCoeffPoint S)).obj M)).inv ≫
        DerivedCategory.Q.map (((sectionsOverOpen (coeffPt S) ⊤).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (naiveCupProduct (toCoeffPoint S) K M)) ≫
        pointSectionsUnit S ((totalComplexPair
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} S.sheaf)).obj (K, M)) :=
  paste_naive_relative (coeffTensor S) (baseSections (coeffPt S)) (pointTensor S)
    (sectionsUnitQ (coeffPt S) ⊤ ((pushforwardComplex (toCoeffPoint S)).obj K))
    (sectionsUnitQ (coeffPt S) ⊤ ((pushforwardComplex (toCoeffPoint S)).obj M))
    (pushforwardComparisonQ (toCoeffPoint S) K) (pushforwardComparisonQ (toCoeffPoint S) M)
    _ _ _ _ _ _ _ _ _ _ _ _
    (onePointCupProduct_naive ↥(baseRing S) ((pushforwardComplex (toCoeffPoint S)).obj K)
      ((pushforwardComplex (toCoeffPoint S)).obj M))
    (naiveCupProduct_relativeCupProduct (toCoeffPoint S) K M)
    (adjunctionBitensorMap_natural _ _ _ _ _ _)
    (sectionsUnitQ_naturality (coeffPt S) ⊤ (naiveCupProduct (toCoeffPoint S) K M))

/-! ### The unit `Γ ⟶ RΓ` across the Leray identification -/

open Stacks.Cohomology.SiteCohomologyPresheaf in
/-- The identification `RΓ(S, -) ⋙ res ≅ RΓ(π⁻¹⊤, -)` on units. -/
theorem derivedPreimageSectionsIso_unit
    (X : HomotopyCategory (SheafOfModules.{u} (structureSheafRing S)) (ComplexShape.up ℤ)) :
    (coeffRestrict S).mapDerivedCategory.map ((derivedSectionsOverOpenUnit S ⊤).app X) ≫
        (derivedPreimageSectionsIso S).hom.app (DerivedCategory.Qh.obj X) =
      (mapDerivedCategorySourceIso (sectionsOverOpen S ⊤) (coeffRestrict S)).hom.app X ≫
        (derivedPreimageSectionsUnit (toCoeffPoint S) ⊤).app X := by
  have := isRightDerivedFunctor_totalRightDerived_comp
    (A := SheafOfModules.{u} (structureSheafRing S)) (homotopySectionsOverOpen S ⊤)
    (coeffRestrict S).mapDerivedCategory
  have h := Functor.rightDerivedNatTrans_app _ _
    (totalRightDerivedCompUnit (homotopySectionsOverOpen S ⊤) (coeffRestrict S).mapDerivedCategory)
    (derivedPreimageSectionsUnit (toCoeffPoint S) ⊤)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing S)) (ComplexShape.up ℤ))
    (mapDerivedCategorySourceIso (sectionsOverOpen S ⊤) (coeffRestrict S)).hom X
  rwa [totalRightDerivedCompUnit_app] at h

/-- The Leray comparison on units. -/
theorem lerayComparison_unit
    (X : HomotopyCategory (SheafOfModules.{u} (structureSheafRing S)) (ComplexShape.up ℤ)) :
    (derivedPreimageSectionsUnit (toCoeffPoint S) ⊤).app X ≫
        (lerayComparison (toCoeffPoint S) ⊤).app (DerivedCategory.Qh.obj X) =
      (lerayUnit (toCoeffPoint S) ⊤).app X :=
  NatTrans.congr_app (lerayComparison_fac (toCoeffPoint S) ⊤) X

/-- The Leray unit at the class of a complex. -/
theorem lerayUnit_app_quotient (X : CochainComplex (SheafOfModules.{u} (structureSheafRing S)) ℤ) :
    (lerayUnit (toCoeffPoint S) ⊤).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj X) =
      (derivedSectionsOverOpenUnit (coeffPt S) ⊤).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            (((RingedSpaceModuleAdjunction.modulePushforward (toCoeffPoint S)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj X)) ≫
        (derivedSectionsOverOpen (coeffPt S) ⊤).map
          ((derivedPushforwardUnit (toCoeffPoint S)).app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj X)) := by
  have hid : DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
      (pushforwardPreimageSectionsIso (toCoeffPoint S) ⊤) (ComplexShape.up ℤ)).inv.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj X)) = 𝟙 _ :=
    DerivedCategory.Qh.map_id _
  change DerivedCategory.Qh.map _ ≫ _ ≫ _ = _
  rw [hid]
  exact Category.id_comp _

private theorem bridge_cancel {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {x y : C} {a c : D} (e : x ≅ y) (φ : G.obj y ≅ a) (fh : G.obj x ⟶ c) (qi : a ⟶ c)
    (m : c ⟶ c) (hm : m = 𝟙 c) (hh : fh = G.map e.hom ≫ φ.hom ≫ qi ≫ 𝟙 c) :
    φ.inv ≫ G.map e.inv ≫ fh ≫ m = qi := by
  rw [hm, hh]
  simp [← Functor.map_comp_assoc]

open Stacks.Cohomology.SiteCohomologyPresheaf in
/-- The comparison of sources of the two derived functors of `res ∘ Γ`, at the class of a
complex. -/
theorem mapDerivedCategorySourceIso_hom_app_quotient
    (X : CochainComplex (SheafOfModules.{u} (structureSheafRing S)) ℤ) :
    (coeffRestrict S).mapDerivedCategoryFactors.inv.app
          (((sectionsOverOpen S ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫
        (coeffRestrict S).mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso _).inv.app
          (((sectionsOverOpen S ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj X)) ≫
        (mapDerivedCategorySourceIso (sectionsOverOpen S ⊤) (coeffRestrict S)).hom.app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj X) =
      (DerivedCategory.quotientCompQhIso _).inv.app
        (((coeffRestrict S).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((sectionsOverOpen S ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj X)) := by
  have hh := (coeffRestrict S).mapDerivedCategoryFactorsh_hom_app
    (((sectionsOverOpen S ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj X)
  have hid₁ : DerivedCategory.Qh.map
      (((coeffRestrict S).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app
        (((sectionsOverOpen S ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj X)) = 𝟙 _ :=
    DerivedCategory.Qh.map_id _
  have hid₂ : DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
      (Iso.refl (sectionsOverOpen S ⊤ ⋙ coeffRestrict S)) (ComplexShape.up ℤ)).hom.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj X)) = 𝟙 _ :=
    DerivedCategory.Qh.map_id _
  rw [hid₁] at hh
  change _ ≫ _ ≫ (coeffRestrict S).mapDerivedCategoryFactorsh.hom.app _ ≫
    DerivedCategory.Qh.map _ = _
  exact bridge_cancel _ ((DerivedCategory.quotientCompQhIso _).app _)
    ((coeffRestrict S).mapDerivedCategoryFactors.app _) _ _ _ hid₂ hh

private theorem unit_paste {C : Type*} [Category* C]
    {y0 y1 y2 y3 y4 y5 y6 y3' y6' y7 y9 : C}
    (fi : y0 ⟶ y1) (rq : y1 ⟶ y2) (rU : y2 ⟶ y3) (rR : y3 ⟶ y4) (dH : y4 ⟶ y5) (lc : y5 ⟶ y6)
    (dHh : y3 ⟶ y3') (dPSm : y3' ⟶ y5) (lch : y3' ⟶ y6') (Gm : y6' ⟶ y6) (sI : y2 ⟶ y7)
    (uPre : y7 ⟶ y3') (lU : y7 ⟶ y6') (qi : y0 ⟶ y7) (uP : y7 ⟶ y9) (RdPU : y9 ⟶ y6')
    (pSU : y0 ⟶ y6)
    (h1 : rR ≫ dH = dHh ≫ dPSm) (h2 : dPSm ≫ lc = lch ≫ Gm) (h3 : rU ≫ dHh = sI ≫ uPre)
    (h4 : uPre ≫ lch = lU) (h5 : lU = uP ≫ RdPU) (h6 : fi ≫ rq ≫ sI = qi)
    (hpSU : pSU = qi ≫ uP ≫ RdPU ≫ Gm) :
    pSU = fi ≫ rq ≫ rU ≫ rR ≫ dH ≫ lc := by
  rw [reassoc_of% h1, h2, reassoc_of% h3, reassoc_of% h4, h5, hpSU, ← h6]
  simp only [Category.assoc]

private theorem map_cancel_mid {C D : Type*} [Category* C] [Category* D] (R : C ⥤ D)
    {w x : D} {p q r t : C} (a : w ⟶ x) (b : x ⟶ R.obj p) (c : p ⟶ q) (ci : q ⟶ p)
    (d : p ⟶ r) (e : r ⟶ t) (h : c ≫ ci = 𝟙 p) :
    (a ≫ b ≫ R.map c) ≫ R.map (ci ≫ d ≫ e) = a ≫ b ≫ R.map d ≫ R.map e := by
  simp only [Category.assoc, ← R.map_comp, reassoc_of% h]

/-- `pointSectionsUnit`, written out on the homotopy category. -/
theorem pointSectionsUnit_eq
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing S)) ℤ) :
    pointSectionsUnit S K =
      (DerivedCategory.quotientCompQhIso _).inv.app
          (((sectionsOverOpen (coeffPt S) ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((pushforwardComplex (toCoeffPoint S)).obj K)) ≫
        (derivedSectionsOverOpenUnit (coeffPt S) ⊤).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            ((pushforwardComplex (toCoeffPoint S)).obj K)) ≫
        (derivedSectionsOverOpen (coeffPt S) ⊤).map
          ((derivedPushforwardUnit (toCoeffPoint S)).app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) ≫
        (derivedSectionsOverOpen (coeffPt S) ⊤).map ((derivedPushforward (toCoeffPoint S)).map
          ((DerivedCategory.quotientCompQhIso _).hom.app K)) :=
  map_cancel_mid (derivedSectionsOverOpen (coeffPt S) ⊤) _ _ _ _ _ _
    (Iso.hom_inv_id_app (DerivedCategory.quotientCompQhIso _)
      ((pushforwardComplex (toCoeffPoint S)).obj K))

private theorem cancel_two {C : Type*} [Category* C] {y0 y1 y2 y3 y4 y5 y6 : C}
    (pSU : y0 ⟶ y6) (a : y0 ⟶ y1) (b : y1 ⟶ y2) (c : y2 ⟶ y3) (d : y3 ⟶ y4) (dH : y4 ≅ y5)
    (lc : y5 ≅ y6) (h : pSU = a ≫ b ≫ c ≫ d ≫ dH.hom ≫ lc.hom) :
    pSU ≫ lc.inv ≫ dH.inv = a ≫ b ≫ c ≫ d := by
  rw [h]
  simp

/-- **The unit `Γ ⟶ RΓ` read through the point**: `pointSectionsUnit` followed by the Leray
identification `Rπ_* ⋙ RΓ({*}, -) ≅ RΓ(S, -) ⋙ res` is the unit of `RΓ(S, -)` after restriction of
scalars along `π^♯`. -/
theorem pointSectionsUnit_comp_lerayIso
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing S)) ℤ) :
    pointSectionsUnit S K ≫ ((lerayIso (toCoeffPoint S)).hom.app (DerivedCategory.Q.obj K) ≫
        (derivedPreimageSectionsIso S).inv.app (DerivedCategory.Q.obj K)) =
      (coeffRestrict S).mapDerivedCategoryFactors.inv.app
          (((sectionsOverOpen S ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        (coeffRestrict S).mapDerivedCategory.map (sectionsUnitQ S ⊤ K) := by
  have := isIso_lerayComparison (toCoeffPoint S) ⊤
  have main := unit_paste _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ((derivedPreimageSectionsIso S).hom.naturality
      ((DerivedCategory.quotientCompQhIso _).hom.app K))
    ((lerayComparison (toCoeffPoint S) ⊤).naturality
      ((DerivedCategory.quotientCompQhIso _).hom.app K))
    (derivedPreimageSectionsIso_unit S ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
    (lerayComparison_unit S ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
    (lerayUnit_app_quotient S K) (mapDerivedCategorySourceIso_hom_app_quotient S K)
    (pointSectionsUnit_eq S K)
  have hc := cancel_two _ _ _ _ _ ((derivedPreimageSectionsIso S).app (DerivedCategory.Q.obj K))
    ((lerayIso (toCoeffPoint S)).symm.app (DerivedCategory.Q.obj K)) main
  refine hc.trans ?_
  rw [sectionsUnitQ, Functor.map_comp]
  exact congrArg (fun z => _ ≫ _ ≫ z)
    ((coeffRestrict S).mapDerivedCategory.map_comp _ _).symm

/-! ### Transport along an equality of rings -/

section TransportHEq

variable {A₀ A : CommRingCat.{u}}

private theorem comp_id_id {C : Type*} [Category* C] {x y : C} (a : x ⟶ y) (b c : y ⟶ y)
    (hb : b = 𝟙 y) (hc : c = 𝟙 y) : a ≫ b ≫ 𝟙 y ≫ c = a := by
  rw [hb, hc]
  simp

/-- `restrictScalarsIdMapDerivedCategoryIso` at the image of a complex is the factorization
isomorphism of restriction of scalars along the identity. -/
theorem restrictScalarsIdMapDerivedCategoryIso_hom_app (Y : CochainComplex (ModuleCat.{u} A) ℤ) :
    (restrictScalarsIdMapDerivedCategoryIso A).hom.app (DerivedCategory.Q.obj Y) =
      (ModuleCat.restrictScalars.{u} (RingHom.id ↥A)).mapDerivedCategoryFactors.hom.app Y := by
  dsimp only [restrictScalarsIdMapDerivedCategoryIso, mapDerivedCategoryIdIso,
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso, Iso.trans_hom,
    NatTrans.comp_app, Localization.liftNatIso]
  rw [Localization.liftNatTrans_app, Localization.liftNatTrans_app]
  simp only [Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Category.assoc, Iso.inv_hom_id_app_assoc]
  have h1 : DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
      (Iso.refl (ModuleCat.restrictScalars.{u} (RingHom.id ↥A))) (ComplexShape.up ℤ)).hom.app Y) =
        𝟙 _ := DerivedCategory.Q.map_id _
  have h2 : (Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) DerivedCategory.Q
      (𝟭 (DerivedCategory (ModuleCat.{u} A)))).inv.app Y = 𝟙 _ := rfl
  exact comp_id_id _ _ _ h1 h2

variable {S}

/-- The transported identification of `RΓ(S, -) ⋙ res` with `RΓ(S, -)`, along an equality of rings
which makes the ring map the identity. -/
abbrev sectionsIsoOfLeray {A₀ : CommRingCat.{u}} (h : A₀ = baseRing S)
    (ψ : ↥A₀ →+* ↥(baseRing S)) (hψ : HEq ψ (RingHom.id ↥A₀))
    {G : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
      DerivedCategory (ModuleCat.{u} A₀)}
    (lam : G ≅ baseSections S ⋙ (ModuleCat.restrictScalars.{u} ψ).mapDerivedCategory) :
    transportFunctor h G ≅ baseSections S :=
  transportIso h lam ≪≫ transportCompIsoId h ((ModuleCat.restrictScalars.{u} ψ).mapDerivedCategory)
    (transportRestrictScalarsIsoId h ψ hψ) (baseSections S)

private theorem inv_hom_id_comp {C : Type*} [Category* C] {x y z : C} (e : x ≅ y) (f : y ⟶ z) :
    (e.inv ≫ e.hom) ≫ (𝟭 C).map f = f := by
  simp

/-- After substituting the equality of rings, the transported identification is `lam` followed
by the identification of restriction of scalars along the identity with the identity. -/
theorem sectionsIsoOfLeray_rfl_hom_app
    {G : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
      DerivedCategory (ModuleCat.{u} (baseRing S))}
    (lam : G ≅ baseSections S ⋙
      (ModuleCat.restrictScalars.{u} (RingHom.id ↥(baseRing S))).mapDerivedCategory)
    (Y : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) :
    (sectionsIsoOfLeray rfl (RingHom.id ↥(baseRing S)) HEq.rfl lam).hom.app Y =
      lam.hom.app Y ≫ (restrictScalarsIdMapDerivedCategoryIso (baseRing S)).hom.app
        ((baseSections S).obj Y) := by
  simp only [transportFunctor_rfl, sectionsIsoOfLeray, transportIso, transportCompIsoId,
    transportRestrictScalarsIsoId, Iso.trans_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.comp_obj, Functor.id_obj, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    Category.comp_id, NatIso.cancel_natIso_hom_left]
  exact Category.id_comp _

/-- The units over `A₀`, transported, are the units of `RΓ(S, -)`. -/
theorem unit_comp_sectionsIsoOfLeray
    {G : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
      DerivedCategory (ModuleCat.{u} (baseRing S))}
    (lam : G ≅ baseSections S ⋙
      (ModuleCat.restrictScalars.{u} (RingHom.id ↥(baseRing S))).mapDerivedCategory)
    (X : CochainComplex (SheafOfModules.{u} (structureSheafRing S)) ℤ)
    (u' : DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars.{u} (RingHom.id ↥(baseRing S))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (((sectionsOverOpen S ⊤).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj X)) ⟶ G.obj (DerivedCategory.Q.obj X))
    (hu' : u' ≫ lam.hom.app (DerivedCategory.Q.obj X) =
        (ModuleCat.restrictScalars.{u} (RingHom.id ↥(baseRing S))).mapDerivedCategoryFactors.inv.app
            (((sectionsOverOpen S ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫
          (ModuleCat.restrictScalars.{u} (RingHom.id ↥(baseRing S))).mapDerivedCategory.map
            (sectionsUnitQ S ⊤ X)) :
    u' ≫ (sectionsIsoOfLeray rfl (RingHom.id ↥(baseRing S)) HEq.rfl lam).hom.app
        (DerivedCategory.Q.obj X) = sectionsUnitQ S ⊤ X := by
  rw [sectionsIsoOfLeray_rfl_hom_app, reassoc_of% hu']
  have hn := (restrictScalarsIdMapDerivedCategoryIso (baseRing S)).hom.naturality
    (sectionsUnitQ S ⊤ X)
  rw [hn, ← Category.assoc, restrictScalarsIdMapDerivedCategoryIso_hom_app]
  exact inv_hom_id_comp
    ((ModuleCat.restrictScalars.{u} (RingHom.id ↥(baseRing S))).mapDerivedCategoryFactors.app
      (((sectionsOverOpen S ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj X))
    (sectionsUnitQ S ⊤ X)

/-- The global cup product of `d.toComparison` after substituting the equality of rings. -/
theorem globalCupProduct_toComparison_rfl_app
    {G : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
      DerivedCategory (ModuleCat.{u} (baseRing S))}
    (d : PointPresentation S (baseRing S) G) (e : transportFunctor rfl G ≅ baseSections S)
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) :
    (Functor.uncurry.obj (tensorBase S)).map (e.hom.app K ×ₘ e.hom.app M) ≫
        (globalCupProduct (d.toComparison S rfl e)).app (K, M) =
      adjunctionBitensorMap d.adjunction (Functor.uncurry.obj (tensorBase S)) (spaceTensor S)
          d.tensorIso.hom K M ≫ e.hom.app ((spaceTensor S).obj (K, M)) :=
  adjunctionBitensorMap_ofNatIsoRight d.adjunction e
    (Functor.uncurry.obj (tensorBase S)) (spaceTensor S) d.tensorIso.hom K M

/-- `Γ(S, -)`, with values in modules over the commutative ring `Γ(S, 𝒪_S)`. -/
abbrev globalSections (S : RingedSpace.{u, u}) :
    SheafOfModules.{u} (structureSheafRing S) ⥤ ModuleCat.{u} ↥(baseRing S) :=
  sectionsOverOpen S ⊤

/-- The global sections functor `Γ(S, -)` is additive. -/
instance globalSections_additive (S : RingedSpace.{u, u}) : (globalSections S).Additive :=
  inferInstanceAs (sectionsOverOpen S ⊤).Additive

/-- Two maps out of a total tensor complex, one over restriction of scalars along the identity,
agree as soon as they agree on pure tensors. -/
theorem eq_of_ι_tmul {A : CommRingCat.{u}} (X Y Z : CochainComplex (ModuleCat.{u} ↥A) ℤ)
    (f₀ : HomologicalComplex.mapBifunctor
        (((ModuleCat.restrictScalars.{u} (RingHom.id ↥A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj X)
        (((ModuleCat.restrictScalars.{u} (RingHom.id ↥A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj Y)
        (MonoidalCategory.curriedTensor (ModuleCat.{u} ↥A)) (ComplexShape.up ℤ) ⟶
      ((ModuleCat.restrictScalars.{u} (RingHom.id ↥A)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Z)
    (f : HomologicalComplex.mapBifunctor X Y (MonoidalCategory.curriedTensor (ModuleCat.{u} ↥A))
      (ComplexShape.up ℤ) ⟶ Z)
    (h : ∀ (p q n : ℤ) (hpq : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (p, q) = n) (x : X.X p) (y : Y.X q),
      (f₀.f n).hom ((HomologicalComplex.ιMapBifunctor _ _
          (MonoidalCategory.curriedTensor (ModuleCat.{u} ↥A)) (ComplexShape.up ℤ) p q n hpq).hom
          (x ⊗ₜ y)) =
        (f.f n).hom ((HomologicalComplex.ιMapBifunctor _ _
          (MonoidalCategory.curriedTensor (ModuleCat.{u} ↥A)) (ComplexShape.up ℤ)
            p q n hpq).hom (x ⊗ₜ y))) :
    f = f₀ := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine HomologicalComplex.mapBifunctor.hom_ext fun p q hpq => ?_
  refine ModuleCat.MonoidalCategory.tensor_ext fun x y => ?_
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply]
  exact (h p q n hpq x y).symm

/-- The canonical map to the total tensor complex at complexes restricted along the identity. -/
theorem canonicalDerivedToTensor_restrictScalars_id {A : CommRingCat.{u}}
    (X Y Z : CochainComplex (ModuleCat.{u} ↥A) ℤ)
    (f : HomologicalComplex.mapBifunctor X Y (MonoidalCategory.curriedTensor (ModuleCat.{u} ↥A))
      (ComplexShape.up ℤ) ⟶ Z) :
    (canonicalDerivedToTensorNatTrans ↥A).app
        (((ModuleCat.restrictScalars.{u} (RingHom.id ↥A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj X,
          ((ModuleCat.restrictScalars.{u} (RingHom.id ↥A)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Y) ≫ DerivedCategory.Q.map f =
      (canonicalDerivedToTensorNatTrans ↥A).app (X, Y) ≫ DerivedCategory.Q.map f :=
  rfl

/-- The algebra of `globalCupProduct_naive_of_presentation` once the ring equality is
substituted, with every object and morphism a variable. -/
theorem gen_core {C D : Type*} [Category* C] [Category* D] (A : C × C ⥤ C) (RΓ G : D ⥤ C)
    (e : G ≅ RΓ) {k m b t : D} (tX : b ⟶ t) (μ : A.obj (RΓ.obj k, RΓ.obj m) ⟶ RΓ.obj b)
    (ob : A.obj (G.obj k, G.obj m) ⟶ G.obj b)
    (hμ : A.map (e.hom.app k ×ₘ e.hom.app m) ≫ μ = ob ≫ e.hom.app b)
    {qx qy qz s : C} (uX : qx ⟶ RΓ.obj k) (u'X : qx ⟶ G.obj k) (hX : u'X ≫ e.hom.app k = uX)
    (uY : qy ⟶ RΓ.obj m) (u'Y : qy ⟶ G.obj m) (hY : u'Y ≫ e.hom.app m = uY)
    (uZ : qz ⟶ RΓ.obj t) (u'Z : qz ⟶ G.obj t) (hZ : u'Z ≫ e.hom.app t = uZ)
    {s' : C} (τ : A.obj (qx, qy) ⟶ s) (nvQ : s ⟶ qz) (τ' : A.obj (qx, qy) ⟶ s')
    (nvQ' : s' ⟶ qz) (hτ : τ' ≫ nvQ' = τ ≫ nvQ)
    (hP : A.map (u'X ×ₘ u'Y) ≫ ob ≫ G.map tX = τ' ≫ nvQ' ≫ u'Z) :
    A.map (uX ×ₘ uY) ≫ μ ≫ RΓ.map tX = τ ≫ nvQ ≫ uZ := by
  rw [← reassoc_of% hτ, ← hX, ← hY, ← hZ, map_comp_mkHom, Category.assoc,
    reassoc_of% hμ, ← e.hom.naturality tX]
  simp only [← Category.assoc]
  rw [show (A.map (u'X ×ₘ u'Y) ≫ ob) ≫ G.map tX = (τ' ≫ nvQ') ≫ u'Z by
    simpa only [Category.assoc] using hP]

/-- **The naive cup product square for the global cup product of a point presentation.**  Let
`d` be a presentation over a ring `A₀`, equal to `Γ(S, 𝒪_S)` by `h`, whose right adjoint is
identified by `lam` with `RΓ(S, -)` followed by restriction of scalars along a ring map `ψ` which
`h` makes the identity.  Suppose that units `u'` over `A₀` restrict the unit of `RΓ(S, -)`, that
over `A₀` the doubled-counit adjunction morphism of `d` satisfies the naive cup product square
for a naive cup product `nv₀`, and that `nv₀` agrees with `nv` on pure tensors.  Then the global
cup product of the one-point comparison produced by `d` satisfies the naive cup product square
over `Γ(S, 𝒪_S)`. -/
theorem globalCupProduct_naive_of_presentation {A₀ : CommRingCat.{u}} (h : A₀ = baseRing S)
    (ψ : ↥A₀ →+* ↥(baseRing S)) (hψ : HEq ψ (RingHom.id ↥A₀))
    {G : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
      DerivedCategory (ModuleCat.{u} A₀)}
    (d : PointPresentation S A₀ G)
    (lam : G ≅ baseSections S ⋙ (ModuleCat.restrictScalars.{u} ψ).mapDerivedCategory)
    (K M T : CochainComplex (SheafOfModules.{u} (structureSheafRing S)) ℤ)
    (tX : (spaceTensor S).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj M) ⟶
      DerivedCategory.Q.obj T)
    (u' : ∀ X : CochainComplex (SheafOfModules.{u} (structureSheafRing S)) ℤ,
      DerivedCategory.Q.obj (((ModuleCat.restrictScalars.{u} ψ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (((sectionsOverOpen S ⊤).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj X)) ⟶ G.obj (DerivedCategory.Q.obj X))
    (hu' : ∀ X : CochainComplex (SheafOfModules.{u} (structureSheafRing S)) ℤ,
      u' X ≫ lam.hom.app (DerivedCategory.Q.obj X) =
        (ModuleCat.restrictScalars.{u} ψ).mapDerivedCategoryFactors.inv.app
            (((globalSections S).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫
          (ModuleCat.restrictScalars.{u} ψ).mapDerivedCategory.map (sectionsUnitQ S ⊤ X))
    (nv₀ : HomologicalComplex.mapBifunctor
        (((ModuleCat.restrictScalars.{u} ψ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((globalSections S).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
        (((ModuleCat.restrictScalars.{u} ψ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((globalSections S).mapHomologicalComplex (ComplexShape.up ℤ)).obj M))
        (MonoidalCategory.curriedTensor (ModuleCat.{u} A₀)) (ComplexShape.up ℤ) ⟶
      ((ModuleCat.restrictScalars.{u} ψ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((globalSections S).mapHomologicalComplex (ComplexShape.up ℤ)).obj T))
    (nv : HomologicalComplex.mapBifunctor
        (((globalSections S).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (((globalSections S).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
        (MonoidalCategory.curriedTensor (ModuleCat.{u} (baseRing S))) (ComplexShape.up ℤ) ⟶
      ((globalSections S).mapHomologicalComplex (ComplexShape.up ℤ)).obj T)
    (hnv : ∀ (p q n : ℤ) (hpq : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (p, q) = n)
        (x : (((globalSections S).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).X p)
        (y : (((globalSections S).mapHomologicalComplex (ComplexShape.up ℤ)).obj M).X q),
      (nv₀.f n).hom ((HomologicalComplex.ιMapBifunctor _ _
          (MonoidalCategory.curriedTensor (ModuleCat.{u} A₀)) (ComplexShape.up ℤ) p q n hpq).hom
          (x ⊗ₜ y)) =
        (nv.f n).hom ((HomologicalComplex.ιMapBifunctor _ _
          (MonoidalCategory.curriedTensor (ModuleCat.{u} (baseRing S))) (ComplexShape.up ℤ)
            p q n hpq).hom (x ⊗ₜ y)))
    (hP₀ : (Functor.uncurry.obj (CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor
          ↥A₀)).map (u' K ×ₘ u' M) ≫
        adjunctionBitensorMap d.adjunction (Functor.uncurry.obj
            (CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor ↥A₀))
          (spaceTensor S) d.tensorIso.hom (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj M) ≫
        G.map tX =
      (canonicalDerivedToTensorNatTrans ↥A₀).app
          (((ModuleCat.restrictScalars.{u} ψ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((globalSections S).mapHomologicalComplex (ComplexShape.up ℤ)).obj K),
          ((ModuleCat.restrictScalars.{u} ψ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((globalSections S).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) ≫
        DerivedCategory.Q.map nv₀ ≫ u' T) :
    (Functor.uncurry.obj (tensorBase S)).map (sectionsUnitQ S ⊤ K ×ₘ sectionsUnitQ S ⊤ M) ≫
        (globalCupProduct (d.toComparison S h (sectionsIsoOfLeray h ψ hψ lam))).app
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj M) ≫
        (baseSections S).map tX =
      (canonicalDerivedToTensorNatTrans ↥(baseRing S)).app
          (((globalSections S).mapHomologicalComplex (ComplexShape.up ℤ)).obj K,
            ((globalSections S).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
        DerivedCategory.Q.map nv ≫ sectionsUnitQ S ⊤ T := by
  subst h
  obtain rfl : ψ = RingHom.id _ := eq_of_heq hψ
  have hnv' : nv = nv₀ := eq_of_ι_tmul _ _ _ nv₀ nv hnv
  subst hnv'
  have hμ := globalCupProduct_toComparison_rfl_app d
    (sectionsIsoOfLeray rfl (RingHom.id ↥(baseRing S)) hψ lam)
    (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj M)
  have hK := unit_comp_sectionsIsoOfLeray lam K (u' K) (hu' K)
  have hM := unit_comp_sectionsIsoOfLeray lam M (u' M) (hu' M)
  have hT := unit_comp_sectionsIsoOfLeray lam T (u' T) (hu' T)
  have hτ := canonicalDerivedToTensor_restrictScalars_id
    (((globalSections S).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    (((globalSections S).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
    (((globalSections S).mapHomologicalComplex (ComplexShape.up ℤ)).obj T) nv
  have key := gen_core (Functor.uncurry.obj (tensorBase S)) (baseSections S) G
    (sectionsIsoOfLeray rfl (RingHom.id ↥(baseRing S)) hψ lam) tX _ _ hμ
    _ _ hK _ _ hM _ _ hT _ _ _ _ hτ hP₀
  exact key

end TransportHEq

end Stacks.Cohomology.DerivedGlobalCupProduct
