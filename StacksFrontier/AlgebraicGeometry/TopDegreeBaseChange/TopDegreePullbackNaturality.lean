module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedPullbackSingleNaturality
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreePullbackIdentity
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TruncGESingleHomology
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreeCompositionSingle
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreeTensorNaturality

/-!
# Naturality of the top-degree pullback comparison
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Category AlgebraicGeometry
open RingedSpaceModuleAdjunction

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

open _root_.DerivedCategory

universe u

attribute [local instance] HasDerivedCategory.standard

section Generic

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- **The canonical map `κ : K ⟶ H^d(K)[-d]`** of an object with no cohomology above `d`: the
truncation projection followed by `truncGEIsoSingleHomology`. -/
def topDegreeSingleMap (K : DerivedCategory C) (d : ℤ) (hK : TStructure.t.IsLE K d) :
    K ⟶ (singleFunctor C d).obj ((homologyFunctor C d).obj K) :=
  (TStructure.t.truncGEπ d).app K ≫ (truncGEIsoSingleHomology K d hK).hom

/-- `κ` is the inverse of the identification of `H^d` of a single complex, on `H^d`. -/
theorem homologyMap_topDegreeSingleMap (K : DerivedCategory C) (d : ℤ)
    (hK : TStructure.t.IsLE K d) :
    (homologyFunctor C d).map (topDegreeSingleMap K d hK) =
      (singleFunctorCompHomologyFunctorIso C d).inv.app ((homologyFunctor C d).obj K) := by
  have h := Stacks.TruncGESingleHomology.homologyMap_truncGEπ_truncGELTIso K d
    ((TStructure.t.isLE_iff_isIso_truncLTι_app d (d + 1) rfl K).1 hK)
  exact (Iso.comp_hom_eq_id ((singleFunctorCompHomologyFunctorIso C d).app _)).1 h

/-- **Maps into a single complex out of an object with no cohomology above `d` are determined by
their effect on `H^d`.** -/
theorem hom_ext_singleFunctor_of_isLE (K : DerivedCategory C) (d : ℤ)
    (hK : TStructure.t.IsLE K d) (M : C) {φ₁ φ₂ : K ⟶ (singleFunctor C d).obj M}
    (h : (homologyFunctor C d).map φ₁ = (homologyFunctor C d).map φ₂) : φ₁ = φ₂ := by
  have key : ∀ φ : K ⟶ (singleFunctor C d).obj M, φ = topDegreeSingleMap K d hK ≫
      (singleFunctor C d).map (((singleFunctorCompHomologyFunctorIso C d).inv.app _ ≫
        (homologyFunctor C d).map ((truncGEIsoSingleHomology K d hK).inv ≫
          TStructure.t.descTruncGE φ d)) ≫
        (singleFunctorCompHomologyFunctorIso C d).hom.app M) := by
    intro φ
    obtain ⟨v, hv⟩ := (singleFunctor C d).map_surjective
      ((truncGEIsoSingleHomology K d hK).inv ≫ TStructure.t.descTruncGE φ d)
    have hφ : φ = topDegreeSingleMap K d hK ≫ (singleFunctor C d).map v := by
      rw [hv, topDegreeSingleMap, assoc, Iso.hom_inv_id_assoc, TStructure.t.π_descTruncGE]
    have hnat : (homologyFunctor C d).map ((singleFunctor C d).map v) ≫
        (singleFunctorCompHomologyFunctorIso C d).hom.app M =
        (singleFunctorCompHomologyFunctorIso C d).hom.app _ ≫ v := by
      simpa using (singleFunctorCompHomologyFunctorIso C d).hom.naturality v
    have hv' : v = (singleFunctorCompHomologyFunctorIso C d).inv.app _ ≫
        (homologyFunctor C d).map ((singleFunctor C d).map v) ≫
          (singleFunctorCompHomologyFunctorIso C d).hom.app M := by
      rw [hnat, Iso.inv_hom_id_app_assoc]
    rw [← hv, assoc, ← hv']
    exact hφ
  rw [key φ₁, key φ₂]
  have e₁ : (homologyFunctor C d).map ((truncGEIsoSingleHomology K d hK).inv ≫
      TStructure.t.descTruncGE φ₁ d) = (homologyFunctor C d).map
        ((truncGEIsoSingleHomology K d hK).inv ≫ TStructure.t.descTruncGE φ₂ d) := by
    have hm : ∀ φ : K ⟶ (singleFunctor C d).obj M, (homologyFunctor C d).map φ =
        (homologyFunctor C d).map (topDegreeSingleMap K d hK) ≫ (homologyFunctor C d).map
          ((truncGEIsoSingleHomology K d hK).inv ≫ TStructure.t.descTruncGE φ d) := by
      intro φ
      rw [← Functor.map_comp, topDegreeSingleMap, assoc, Iso.hom_inv_id_assoc,
        TStructure.t.π_descTruncGE]
    have h' := (hm φ₁).symm.trans (h.trans (hm φ₂))
    rw [homologyMap_topDegreeSingleMap] at h'
    exact (cancel_epi _).1 h'
  rw [e₁]

/-- **`κ` is natural.** -/
theorem topDegreeSingleMap_naturality {K L : DerivedCategory C} (φ : K ⟶ L) (d : ℤ)
    (hK : TStructure.t.IsLE K d) (hL : TStructure.t.IsLE L d) :
    topDegreeSingleMap K d hK ≫ (singleFunctor C d).map ((homologyFunctor C d).map φ) =
      φ ≫ topDegreeSingleMap L d hL := by
  refine hom_ext_singleFunctor_of_isLE K d hK _ ?_
  rw [Functor.map_comp, Functor.map_comp, homologyMap_topDegreeSingleMap,
    homologyMap_topDegreeSingleMap]
  exact ((singleFunctorCompHomologyFunctorIso C d).inv.naturality
    ((homologyFunctor C d).map φ)).symm

/-- **`κ` at a single complex** is the inverse of the identification of its `H^d`, placed in
degree `d`. -/
theorem topDegreeSingleMap_singleFunctor (M : C) (d : ℤ) :
    topDegreeSingleMap ((singleFunctor C d).obj M) d inferInstance =
      (singleFunctor C d).map ((singleFunctorCompHomologyFunctorIso C d).inv.app M) := by
  refine hom_ext_singleFunctor_of_isLE _ d inferInstance _ ?_
  rw [homologyMap_topDegreeSingleMap]
  have hnat := (singleFunctorCompHomologyFunctorIso C d).inv.naturality
    ((singleFunctorCompHomologyFunctorIso C d).inv.app M)
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hnat
  exact (cancel_epi _).1 hnat

end Generic



section Chain

variable {𝒞 : Type*} [Category 𝒞]

/-- The rearrangement behind `derivedPullbackTopDegreeIsoPullback_comp_singleFunctor`, at
variables. -/
theorem transverse_comp_chain {A B C T D E T' P Q : 𝒞}
    (cmpH : A ⟶ B) (dab : B ⟶ C) (chiab : C ⟶ T) (Hdb : A ⟶ D) (da : D ⟶ E) (Hs : E ⟶ C)
    (chi' : E ⟶ T') (comp : T' ⟶ T) (thS : D ⟶ P) (achi : P ⟶ T') (thL : A ⟶ Q) (aHd : Q ⟶ P)
    (h1 : cmpH ≫ dab = Hdb ≫ da ≫ Hs) (h2 : Hs ≫ chiab = chi' ≫ comp)
    (h3 : da ≫ chi' = thS ≫ achi) (h4 : Hdb ≫ thS = thL ≫ aHd)
    {sab : B ⟶ T} {sb : Q ⟶ T'} (h5 : sab = dab ≫ chiab) (h6 : sb = aHd ≫ achi) :
    cmpH ≫ sab = thL ≫ sb ≫ comp := by
  rw [h5, h6, ← assoc, h1, assoc, assoc, h2, ← assoc da, h3, ← assoc, ← assoc, h4]
  simp only [assoc]

/-- The rearrangement behind `derivedPullbackTopDegreeIsoPullback_comp`, at variables. -/
theorem transverse_comp_general {A0 A1 A2 A3 B1 B2 B3 B4 B6 B7 B8 : 𝒞}
    (cK : A0 ⟶ A1) (ψabK : A1 ⟶ B1) (ψaK : A0 ⟶ B2) (aψbK : B2 ⟶ B3) (pcK : B3 ⟶ B1)
    (Hκab : B1 ⟶ B4) (χab : B4 ⟶ B1) (Lκab : A1 ⟶ A2) (ψabS : A2 ⟶ B4) (sab : A2 ⟶ B1)
    (Lκba : A0 ⟶ A3) (cS : A3 ⟶ A2) (ψaS : A3 ⟶ B6) (asb : B6 ⟶ B7) (pcM : B7 ⟶ B1)
    (bκ : B3 ⟶ B8) (bχ : B8 ⟶ B7) (aHLbκ : B2 ⟶ B6) (aψbS : B6 ⟶ B8)
    (e1 : Hκab ≫ χab = 𝟙 _) (n1 : Lκab ≫ ψabS = ψabK ≫ Hκab) (n4 : ψabS ≫ χab = sab)
    (n2 : Lκba ≫ cS = cK ≫ Lκab) (n3 : cS ≫ sab = ψaS ≫ asb ≫ pcM)
    (n8 : bκ ≫ bχ ≫ pcM = pcK ≫ Hκab ≫ χab) (n6 : aHLbκ ≫ aψbS = aψbK ≫ bκ)
    (n5 : aψbS ≫ bχ = asb) (n7 : Lκba ≫ ψaS = ψaK ≫ aHLbκ) :
    cK ≫ ψabK = ψaK ≫ aψbK ≫ pcK := by
  have hL : cK ≫ ψabK = Lκba ≫ ψaS ≫ asb ≫ pcM := by
    rw [← comp_id ψabK, ← e1, ← assoc ψabK, ← n1, assoc, n4, ← assoc, ← n2, assoc, n3]
  have hR : ψaK ≫ aψbK ≫ pcK = Lκba ≫ ψaS ≫ asb ≫ pcM := by
    rw [← comp_id pcK, ← e1, ← n8, ← assoc aψbK, ← n6, assoc, ← assoc aψbS, n5, ← assoc,
      ← n7, assoc]
  rw [hL, hR]

end Chain

section Geometry

attribute [local instance 10000] HasDerivedCategory.standard

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedPullback.Composition

variable {X Y Z : RingedSpace.{u, u}}

/-- The top-degree comparison is `H^d(Lf^* κ)` followed by the comparison at the single complex. -/
theorem derivedPullbackTopDegreeIsoPullback_hom_eq (f : X ⟶ Y)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) (d : ℤ)
    (hK : TStructure.t.IsLE K d) :
    (derivedPullbackTopDegreeIsoPullback f K d hK).hom =
      (homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).map
          ((derivedPullback f).map (topDegreeSingleMap K d hK)) ≫
        homologyDerivedPullbackSingleMap f
          ((homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).obj K) d :=
  derivedPullbackTopDegreeIsoPullback_hom f K d hK

/-- **The top-degree comparison at a single complex** is the comparison
`H^d(Lf^*(M[-d])) ⟶ f^*M`, up to the identification of `H^d` of the single complex. -/
theorem derivedPullbackTopDegreeIsoPullback_hom_singleFunctor (f : X ⟶ Y)
    (M : SheafOfModules.{u} (structureSheafRing Y)) (d : ℤ) :
    (derivedPullbackTopDegreeIsoPullback f
        ((singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).obj M) d inferInstance).hom ≫
      (modulePullback f).map
        ((singleFunctorCompHomologyFunctorIso (SheafOfModules.{u} (structureSheafRing Y)) d).hom.app
          M) =
      homologyDerivedPullbackSingleMap f M d := by
  rw [derivedPullbackTopDegreeIsoPullback_hom_eq, assoc, topDegreeSingleMap_singleFunctor,
    ← assoc]
  have hn := homologyDerivedPullbackSingleMap_naturality f
    ((singleFunctorCompHomologyFunctorIso (SheafOfModules.{u} (structureSheafRing Y)) d).inv.app M)
    d
  refine (congrArg (fun t => t ≫ (modulePullback f).map
    ((singleFunctorCompHomologyFunctorIso (SheafOfModules.{u} (structureSheafRing Y)) d).hom.app
      M)) hn).trans ?_
  rw [assoc, ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  exact comp_id _

/-- `Lf^*` keeps an object with no cohomology above `d` in that range. -/
theorem isLE_derivedPullback_obj' (f : X ⟶ Y)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) (d : ℤ)
    (hK : TStructure.t.IsLE K d) : TStructure.t.IsLE ((derivedPullback f).obj K) d :=
  isLE_derivedPullback_obj f K d hK

/-- `homologyDerivedPullbackSingleMap` unfolded to `H^d` of `derivedToOrdinaryPullbackSingle`
followed by the identification of `H^d` of a single complex. -/
private theorem homologyDerivedPullbackSingleMap_eq_map_comp (f : X ⟶ Y)
    (M : SheafOfModules.{u} (structureSheafRing Y)) (d : ℤ) :
    homologyDerivedPullbackSingleMap f M d =
      (homologyFunctor _ d).map (derivedToOrdinaryPullbackSingle f M d) ≫
        (singleFunctorCompHomologyFunctorIso _ d).hom.app ((modulePullback f).obj M) := by
  rw [homologyDerivedPullbackSingleMap, homologySingleIso_hom]

variable (a : X ⟶ Y) (b : Y ⟶ Z)

/-- **The top-degree comparison is compatible with composition, at a single complex.** -/
theorem derivedPullbackTopDegreeIsoPullback_comp_singleFunctor
    (M : SheafOfModules.{u} (structureSheafRing Z)) (d : ℤ) :
    (homologyFunctor _ d).map ((derivedPullbackCompIsoCanonical a b).hom.app
        ((singleFunctor (SheafOfModules.{u} (structureSheafRing Z)) d).obj M)) ≫
      homologyDerivedPullbackSingleMap (a ≫ b) M d =
    (derivedPullbackTopDegreeIsoPullback a ((derivedPullback b).obj
        ((singleFunctor (SheafOfModules.{u} (structureSheafRing Z)) d).obj M)) d
        (isLE_derivedPullback_obj' b _ d inferInstance)).hom ≫
      (modulePullback a).map (homologyDerivedPullbackSingleMap b M d) ≫
      (Stacks.DerivedPullback.Composition.modulePullbackComp a b).hom.app M := by
  have hP := derivedPullbackTopDegreeIsoPullback_hom_naturality a
    (derivedToOrdinaryPullbackSingle b M d) d
    (isLE_derivedPullback_obj' b _ d inferInstance) inferInstance
  have hS := derivedPullbackTopDegreeIsoPullback_hom_singleFunctor a ((modulePullback b).obj M) d
  have hpaste :=
    derivedPullbackCompIsoCanonical_hom_app_comp_derivedToOrdinaryPullbackSingle_of_degree a b M d
  have hχ := (singleFunctorCompHomologyFunctorIso
      (SheafOfModules.{u} (structureSheafRing X)) d).hom.naturality
    ((Stacks.DerivedPullback.Composition.modulePullbackComp a b).hom.app M)
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hχ
  have h1 := congrArg (homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).map hpaste
  simp only [Functor.map_comp] at h1
  exact transverse_comp_chain _ _ _ _ _ _ _ _ _ _ _ _ h1 hχ
    ((homologyDerivedPullbackSingleMap_eq_map_comp a _ d).symm.trans hS.symm) hP
    (homologyDerivedPullbackSingleMap_eq_map_comp (a ≫ b) M d)
    ((congrArg (modulePullback a).map (homologyDerivedPullbackSingleMap_eq_map_comp b M d)).trans
      (Functor.map_comp _ _ _))

/-- **The top-degree comparison is compatible with composition.** For `K` with no cohomology
above `d`, the comparison for `a ≫ b`, read through the composition isomorphism of
[Stacks, Tag 0D5S], is the comparison for `a` at `Lb^*K` followed by `a^*` of the comparison for
`b` and the composition isomorphism of ordinary pullbacks. -/
theorem derivedPullbackTopDegreeIsoPullback_comp
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z))) (d : ℤ)
    (hK : TStructure.t.IsLE K d) :
    (homologyFunctor _ d).map ((derivedPullbackCompIsoCanonical a b).hom.app K) ≫
      (derivedPullbackTopDegreeIsoPullback (a ≫ b) K d hK).hom =
    (derivedPullbackTopDegreeIsoPullback a ((derivedPullback b).obj K) d
        (isLE_derivedPullback_obj' b K d hK)).hom ≫
      (modulePullback a).map (derivedPullbackTopDegreeIsoPullback b K d hK).hom ≫
      (Stacks.DerivedPullback.Composition.modulePullbackComp a b).hom.app
        ((homologyFunctor _ d).obj K) := by
  set M := (homologyFunctor (SheafOfModules.{u} (structureSheafRing Z)) d).obj K
  set κ := topDegreeSingleMap K d hK
  have hS : TStructure.t.IsLE
      ((singleFunctor (SheafOfModules.{u} (structureSheafRing Z)) d).obj M) d := inferInstance
  have e0 : (homologyFunctor _ d).map κ ≫
      (singleFunctorCompHomologyFunctorIso (SheafOfModules.{u} (structureSheafRing Z)) d).hom.app
        M = 𝟙 _ := by
    rw [homologyMap_topDegreeSingleMap, Iso.inv_hom_id_app]
    rfl
  have e1 := ((modulePullback (a ≫ b)).map_comp _ _).symm.trans
    ((congrArg (modulePullback (a ≫ b)).map e0).trans ((modulePullback (a ≫ b)).map_id _))
  have n1 := derivedPullbackTopDegreeIsoPullback_hom_naturality (a ≫ b) κ d hK hS
  have n4 := derivedPullbackTopDegreeIsoPullback_hom_singleFunctor (a ≫ b) M d
  have n2 := congrArg (homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).map
    ((derivedPullbackCompIsoCanonical a b).hom.naturality κ)
  simp only [Functor.map_comp, Functor.comp_map] at n2
  have n3 := derivedPullbackTopDegreeIsoPullback_comp_singleFunctor a b M d
  have n8 := (Stacks.DerivedPullback.Composition.modulePullbackComp a b).hom.naturality
    ((homologyFunctor _ d).map κ ≫
      (singleFunctorCompHomologyFunctorIso (SheafOfModules.{u} (structureSheafRing Z)) d).hom.app
        M)
  simp only [Functor.comp_map, Functor.map_comp, assoc] at n8
  have n6 := congrArg (modulePullback a).map
    (derivedPullbackTopDegreeIsoPullback_hom_naturality b κ d hK hS)
  simp only [Functor.map_comp] at n6
  have n5 := congrArg (modulePullback a).map
    (derivedPullbackTopDegreeIsoPullback_hom_singleFunctor b M d)
  simp only [Functor.map_comp] at n5
  have n7 := derivedPullbackTopDegreeIsoPullback_hom_naturality a ((derivedPullback b).map κ) d
    (isLE_derivedPullback_obj' b K d hK) (isLE_derivedPullback_obj' b _ d hS)
  exact transverse_comp_general _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e1 n1 n4 n2 n3 n8 n6 n5 n7

end Geometry

end Stacks.AlgebraicGeometry.TopDegreeBaseChange
