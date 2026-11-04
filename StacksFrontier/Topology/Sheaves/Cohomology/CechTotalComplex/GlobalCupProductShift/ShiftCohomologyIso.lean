module

public import StacksFrontier.AlgebraicGeometry.Cohomology.FlasqueReductionOfTheCupProductSquare
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.GlobalCupProductCocycles
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CupPairingNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.NaiveCupProductShift

/-!
# The global cup product and the shift

Let `(S, 𝒪_S)` be a ringed space and `A = Γ(S, 𝒪_S)`.  Derived global sections
`RΓ(S, -) : D(𝒪_S) ⥤ D(A)` commute with the shift, and the unit `Γ ⟶ RΓ` is compatible with that
commutation; so for a complex `𝒦^•` of `𝒪_S`-modules there are canonical identifications

`Hᵃ(S, 𝒦^•[n]) ≅ Hⁿ⁺ᵃ(S, 𝒦^•)`

which on the class of a global cocycle `z ∈ Zᵃ(Γ(S, 𝒦^•[n])) = Zⁿ⁺ᵃ(Γ(S, 𝒦^•))` are the identity.
This file constructs them and proves that last property.

## Main definitions

* `Stacks.Cohomology.DerivedGlobalCupProduct.sectionsUnitNat`: the unit `Γ ⟶ RΓ` as a natural
  transformation compatible with the shift.
* `Stacks.Cohomology.DerivedGlobalCupProduct.shiftCohomologyIso`: the identification
  `Hᵃ(S, 𝒦^•[n]) ≅ Hⁿ⁺ᵃ(S, 𝒦^•)`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.shiftCycles`: a cocycle of `Y[n]` in degree `a`, read
  as a cocycle of `Y` in degree `n + a`.

## Main results

* `Stacks.Cohomology.DerivedGlobalCupProduct.sectionsUnitNat_app`: its components are the units.
* `Stacks.Cohomology.DerivedGlobalCupProduct.globalCycleClass_shiftCohomologyIso`: **the
  identification sends the class of a global cocycle of `𝒦^•[n]` to the class of the same
  cocycle of `𝒦^•`.**
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.GlobalKunneth
open Stacks.SheafOfModules.Tensor (ringSheaf sheafTensor)
open Stacks.Cohomology.DerivedSectionsLeray (sectionsUnitQ derivedSectionsOverOpen
  derivedSectionsOverOpenUnit sectionsOverOpen)
open RingTheory.TorProducts (cycleClass)
open scoped CategoryTheory.Prod Stacks.Topology.SheafTensorAdditiveOnOpens

universe u

namespace Stacks.Cohomology.DerivedGlobalCupProduct

attribute [local instance] HasDerivedCategory.standard

/-! ### The unit `Γ ⟶ RΓ` commutes with the shift -/

section Unit

variable (X : RingedSpace.{u, u}) (U : Opens X.carrier)

/-- **The unit `Γ(U, -) ⟶ RΓ(U, -)`** as a natural transformation of functors from cochain
complexes of `𝒪_X`-modules to `D(𝒪_X(U))`, assembled from the unit of the total right derived
functor on the homotopy category. -/
def sectionsUnitNat :
    (sectionsOverOpen X U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ derivedSectionsOverOpen X U :=
  Functor.whiskerLeft ((sectionsOverOpen X U).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso _).inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight ((sectionsOverOpen X U).mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (HomotopyCategory.quotient _ _) (derivedSectionsOverOpenUnit X U) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).hom (derivedSectionsOverOpen X U)

/-- The unit `Γ ⟶ RΓ` is compatible with the shift. -/
instance : NatTrans.CommShift (sectionsUnitNat X U) ℤ := by
  unfold sectionsUnitNat
  infer_instance

/-- The components of `sectionsUnitNat` are the units `sectionsUnitQ`. -/
theorem sectionsUnitNat_app (N : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    (sectionsUnitNat X U).app N = sectionsUnitQ X U N := by
  simp only [sectionsUnitNat, sectionsUnitQ, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Category.id_comp, Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift,
    NatIso.ofComponents_inv_app, Iso.refl_inv]
  exact congrArg (_ ≫ ·) ((congrArg (· ≫ _) (DerivedCategory.Qh.map_id _)).trans
    (Category.id_comp _))

/-- **The unit commutes with the shift**, at one complex: shifting the unit of `N` is the unit of
`N[n]`, read through the commutations of `Γ`, `Q` and `RΓ` with the shift. -/
theorem sectionsUnitQ_shift
    (N : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (n : ℤ) :
    sectionsUnitQ X U (N⟦n⟧) ≫
        ShiftedHom.map ((DerivedCategory.Q.commShiftIso n).hom.app N)
            (derivedSectionsOverOpen X U) =
      ShiftedHom.map (((sectionsOverOpen X U).mapHomologicalComplex
          (ComplexShape.up ℤ)).commShiftIso
          n |>.hom.app N) DerivedCategory.Q ≫ (sectionsUnitQ X U N)⟦n⟧' := by
  have h := NatTrans.shift_app_comm (sectionsUnitNat X U) n N
  rw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app,
    sectionsUnitNat_app, sectionsUnitNat_app] at h
  simp only [ShiftedHom.map, Category.assoc] at h ⊢
  exact h.symm

end Unit

/-! ### The identification `Hᵃ(S, 𝒦^•[n]) ≅ Hⁿ⁺ᵃ(S, 𝒦^•)` -/

variable {S : RingedSpace.{u, u}}

/-- On the class of a global cocycle `z` of `𝒦^•[n]` in degree `a`, the shift map of `H⁰`
applied to the commutation of `Γ(S, -)` with the shift is the class of the shifted cocycle. -/
theorem cycleClass_shiftMap_shiftIso {M : ModuleCat.{u} (baseRing S)}
    (N : CochainComplex (SheafOfModules.{u} (structureSheafRing S)) ℤ) (n a a' : ℤ) (h : n + a = a')
    (z : M ⟶ (sectionsComplex S (N⟦n⟧)).cycles a) :
    cycleClass z ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) a).map
        (ShiftedHom.map ((((globalSections S).mapHomologicalComplex
          (ComplexShape.up ℤ)).commShiftIso n).hom.app N) DerivedCategory.Q) ≫
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) 0).shiftIso n a a'
          h).hom.app _ =
      shiftCycles (sectionsComplex S N) a' h (z ≫ HomologicalComplex.cyclesMap
        ((((globalSections S).mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).hom.app N)
          a) ≫
        (sectionsComplex S N).homologyπ a' ≫
          (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} (baseRing S)) a').inv.app
            (sectionsComplex S N) := by
  let g := (((globalSections S).mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).hom.app N
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S))
  let fac := DerivedCategory.homologyFunctorFactors (ModuleCat.{u} (baseRing S))
  let cH := HomologicalComplex.homologyFunctor (ModuleCat.{u} (baseRing S)) (ComplexShape.up ℤ)
  have e2 := DerivedCategory.shiftMap_homologyFunctor_map_Q g a a' h
  have e2' : (fac a).inv.app _ ≫ (H a).map (ShiftedHom.map g DerivedCategory.Q) ≫
        ((H 0).shiftIso n a a' h).hom.app _ =
      ((cH a).map g ≫ ((cH 0).shiftIso n a a' h).hom.app (sectionsComplex S N)) ≫
        (fac a').inv.app (sectionsComplex S N) :=
    (Iso.inv_comp_eq ((fac a).app _)).mpr e2
  have e4 : z ≫ (sectionsComplex S (N⟦n⟧)).homologyπ a ≫ (cH a).map g =
      (z ≫ HomologicalComplex.cyclesMap g a) ≫ ((sectionsComplex S N)⟦n⟧).homologyπ a :=
    (congrArg (z ≫ ·) (HomologicalComplex.homologyπ_naturality g a)).trans
      (Category.assoc z (HomologicalComplex.cyclesMap g a) _).symm
  have e5 := homologyπ_shiftIso (sectionsComplex S N) a' h (z ≫ HomologicalComplex.cyclesMap g a)
  have e6 : z ≫ (sectionsComplex S (N⟦n⟧)).homologyπ a ≫ (cH a).map g ≫
        ((cH 0).shiftIso n a a' h).hom.app (sectionsComplex S N) =
      shiftCycles (sectionsComplex S N) a' h (z ≫ HomologicalComplex.cyclesMap g a) ≫
        (sectionsComplex S N).homologyπ a' := by
    have e4' := congrArg (· ≫ ((cH 0).shiftIso n a a' h).hom.app (sectionsComplex S N)) e4
    simp only [Category.assoc] at e4' e5
    exact e4'.trans e5
  let π₁ := (sectionsComplex S (N⟦n⟧)).homologyπ a
  let T := (H a).map (ShiftedHom.map g DerivedCategory.Q) ≫ ((H 0).shiftIso n a a' h).hom.app _
  have s1 : cycleClass z ≫ T = z ≫ π₁ ≫ ((fac a).inv.app _ ≫ T) :=
    (Category.assoc _ _ _).trans (congrArg (z ≫ ·) (Category.assoc _ _ _))
  have s2 := congrArg (fun t => z ≫ π₁ ≫ t) e2'
  have s3 : z ≫ π₁ ≫ (((cH a).map g ≫ ((cH 0).shiftIso n a a' h).hom.app (sectionsComplex S N)) ≫
        (fac a').inv.app (sectionsComplex S N)) =
      (z ≫ π₁ ≫ (cH a).map g ≫ ((cH 0).shiftIso n a a' h).hom.app (sectionsComplex S N)) ≫
        (fac a').inv.app (sectionsComplex S N) :=
    (congrArg (z ≫ ·) ((congrArg (π₁ ≫ ·) (Category.assoc _ _ _)).trans
      (Category.assoc _ _ _).symm)).trans (Category.assoc _ _ _).symm |>.trans
        (congrArg (· ≫ (fac a').inv.app (sectionsComplex S N))
          ((Category.assoc _ _ _).trans (congrArg (z ≫ ·) (Category.assoc _ _ _))))
  have s4 := (congrArg (· ≫ (fac a').inv.app (sectionsComplex S N)) e6).trans
    (Category.assoc _ _ _)
  exact s1.trans (s2.trans (s3.trans s4))

/-- **The identification `Hᵃ(S, 𝒦^•[n]) ≅ Hⁿ⁺ᵃ(S, 𝒦^•)`**, for `n + a = a'`: the commutations of
`Q` and of `RΓ(S, -)` with the shift, followed by the identification of `Hᵃ` of a shift with
`Hⁿ⁺ᵃ` in `D(A)`. -/
def shiftCohomologyIso (N : CochainComplex (SheafOfModules.{u} (structureSheafRing S)) ℤ)
    (n a a' : ℤ) (h : n + a = a') :
    cohomologyModule (DerivedCategory.Q.obj (N⟦n⟧)) a ≅ cohomologyModule
        (DerivedCategory.Q.obj N) a' :=
  (DerivedCategory.homologyFunctor _ a).mapIso ((baseSections S).mapIso
      ((DerivedCategory.Q.commShiftIso n).app N) ≪≫ ((baseSections S).commShiftIso n).app
        (DerivedCategory.Q.obj N)) ≪≫
    ((DerivedCategory.homologyFunctor _ 0).shiftIso n a a' h).app _

/-- The forward map of `shiftCohomologyIso` is the shift map of `H⁰` applied to the image under
`RΓ(S, -)` of the commutation of `Q` with the shift. -/
theorem shiftCohomologyIso_hom (N : CochainComplex (SheafOfModules.{u} (structureSheafRing S)) ℤ)
    (n a a' : ℤ) (h : n + a = a') :
    (shiftCohomologyIso N n a a' h).hom = (DerivedCategory.homologyFunctor _ 0).shiftMap
      (ShiftedHom.map ((DerivedCategory.Q.commShiftIso n).hom.app N) (baseSections S)) a a' h :=
  rfl

/-- **The identification `Hᵃ(S, 𝒦^•[n]) ≅ Hⁿ⁺ᵃ(S, 𝒦^•)` on the class of a global cocycle**: the
class of a global cocycle `z` of `𝒦^•[n]` in degree `a` is sent to the class of the same cocycle,
read in `Γ(S, 𝒦^•)` in degree `n + a`. -/
theorem globalCycleClass_shiftCohomologyIso {M : ModuleCat.{u} (baseRing S)}
    (N : CochainComplex (SheafOfModules.{u} (structureSheafRing S)) ℤ) (n a a' : ℤ) (h : n + a = a')
    (z : M ⟶ (sectionsComplex S (N⟦n⟧)).cycles a) :
    globalCycleClass z ≫ (shiftCohomologyIso N n a a' h).hom =
      globalCycleClass (shiftCycles (sectionsComplex S N) a' h (z ≫ HomologicalComplex.cyclesMap
        ((((globalSections S).mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).hom.app N)
          a)) := by
  let g := (((globalSections S).mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).hom.app N
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S))
  have hu := sectionsUnitQ_shift S ⊤ N n
  have e1 : globalCycleClass z ≫ (shiftCohomologyIso N n a a' h).hom =
      cycleClass z ≫ (H a).map (ShiftedHom.map g DerivedCategory.Q) ≫
        ((H 0).shiftIso n a a' h).hom.app _ ≫ (H a').map (sectionsUnitQ S ⊤ N) := by
    rw [globalCycleClass, shiftCohomologyIso_hom, Functor.shiftMap]
    refine (Category.assoc _ _ _).trans (congrArg (cycleClass z ≫ ·) ?_)
    have hu' := congrArg (H a).map hu
    rw [(H a).map_comp, (H a).map_comp] at hu'
    exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hu')).trans
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
        (((H 0).shiftIso n a a' h).hom.naturality (sectionsUnitQ S ⊤ N))))
  refine e1.trans ?_
  have e7 := cycleClass_shiftMap_shiftIso N n a a' h z
  have e9 : cycleClass z ≫ (H a).map (ShiftedHom.map g DerivedCategory.Q) ≫
        ((H 0).shiftIso n a a' h).hom.app _ ≫ (H a').map (sectionsUnitQ S ⊤ N) =
      (cycleClass z ≫ ((H a).map (ShiftedHom.map g DerivedCategory.Q) ≫
        ((H 0).shiftIso n a a' h).hom.app _)) ≫ (H a').map (sectionsUnitQ S ⊤ N) :=
    (congrArg (cycleClass z ≫ ·) (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm
  exact e9.trans ((congrArg (· ≫ (H a').map (sectionsUnitQ S ⊤ N)) e7).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))))

/-! ### Naturality, and classes on a flasque complex -/

open Stacks.Cohomology.DerivedPullbackTensor (derivedToTensorNatTrans totalComplexPair) in
/-- **The cup product followed by the canonical map to the total tensor complex is natural** in
chain maps of the two complexes. -/
theorem totalCupPairing_naturality
    {K K' M M' : CochainComplex (SheafOfModules.{u} (structureSheafRing S)) ℤ}
    (f : K ⟶ K') (g : M ⟶ M') (i j : ℤ)
    (ξ : ModuleCat.of (baseRing S) (baseRing S) ⟶ cohomologyModule (DerivedCategory.Q.obj K) i)
    (η : ModuleCat.of (baseRing S) (baseRing S) ⟶ cohomologyModule (DerivedCategory.Q.obj M) j) :
    (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        ((ξ ≫ (DerivedCategory.homologyFunctor _ i).map
            ((baseSections S).map (DerivedCategory.Q.map f))) ⊗ₘ
          (η ≫ (DerivedCategory.homologyFunctor _ j).map
            ((baseSections S).map (DerivedCategory.Q.map g)))) ≫ totalCupPairing K' M' i j =
      (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (ξ ⊗ₘ η) ≫ totalCupPairing K M i j ≫
        (DerivedCategory.homologyFunctor _ (i + j)).map ((baseSections S).map
          (DerivedCategory.Q.map ((totalComplexPair (sheafTensor S.sheaf)).map (f ×ₘ g)))) := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)
  have h1 := cupPairing_naturality (cupProductOnSpace S) (DerivedCategory.Q.map f)
    (DerivedCategory.Q.map g) i j ξ η
  let Tm := (Functor.uncurry.obj
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.sheaf)).map
      (DerivedCategory.Q.map f ×ₘ DerivedCategory.Q.map g)
  have hn : Tm ≫ (derivedToTensorNatTrans S).app (K', M') =
      (derivedToTensorNatTrans S).app (K, M) ≫
        DerivedCategory.Q.map ((totalComplexPair (sheafTensor S.sheaf)).map (f ×ₘ g)) :=
    (derivedToTensorNatTrans S).naturality (X := (K, M)) (Y := (K', M')) (f ×ₘ g)
  have h2 : H.map ((baseSections S).map Tm) ≫
        H.map ((baseSections S).map ((derivedToTensorNatTrans S).app (K', M'))) =
      H.map ((baseSections S).map ((derivedToTensorNatTrans S).app (K, M))) ≫
        H.map ((baseSections S).map (DerivedCategory.Q.map
          ((totalComplexPair (sheafTensor S.sheaf)).map (f ×ₘ g)))) :=
    (H.map_comp _ _).symm.trans ((congrArg H.map ((baseSections S).map_comp _ _).symm).trans
      ((congrArg (fun t => H.map ((baseSections S).map t)) hn).trans
        ((congrArg H.map ((baseSections S).map_comp _ _)).trans (H.map_comp _ _))))
  have h1' := congrArg (· ≫ H.map ((baseSections S).map
    ((derivedToTensorNatTrans S).app (K', M')))) h1
  refine Eq.trans ?_ (h1'.trans ?_)
  · exact (congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans
      (Category.assoc _ _ _).symm)).trans (Category.assoc _ _ _).symm
  · refine ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h2)))))).trans ?_
    exact congrArg (_ ≫ ·) (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm)

open Stacks.Cohomology.CechSheaf (abSheaf) in
/-- **On a bounded below complex of flasque modules every class is the class of a global
cocycle.** The unit `Γ ⟶ RΓ` is invertible there, and the free module of rank one is projective,
so a class lifts through the projection from cocycles to cohomology. -/
theorem exists_globalCycleClass_eq_of_isFlasque
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing S)) ℤ)
        (hK : ∃ n : ℤ, K.IsStrictlyGE n)
    (hfl : ∀ n : ℤ, TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (ringSheaf.{u, u, u} S.sheaf)).obj (K.X n))) (i : ℤ)
    (ξ : ModuleCat.of (baseRing S) (baseRing S) ⟶ cohomologyModule (DerivedCategory.Q.obj K) i) :
    ∃ z : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S K).cycles i,
      globalCycleClass z = ξ := by
  let Kp : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) :=
    ⟨K, (CochainComplex.plus_iff _ K).mpr hK⟩
  have hiso : IsIso (sectionsUnitQ S ⊤ K) := by
    have := Stacks.Cech.CupProductSquare.isIso_sectionsToBaseSections_app_of_isFlasque S Kp hfl
    rwa [Stacks.Cech.CupProductSquare.sectionsToBaseSections_app_eq] at this
  let ξ' : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S K).homology i :=
    ξ ≫ (DerivedCategory.homologyFunctor _ i).map (inv (sectionsUnitQ S ⊤ K)) ≫
      (DerivedCategory.homologyFunctorFactors _ i).hom.app (sectionsComplex S K)
  have : Module.Projective (baseRing S) (ModuleCat.of (baseRing S) (baseRing S)) :=
    inferInstanceAs (Module.Projective (baseRing S) (baseRing S))
  have : Projective (ModuleCat.of (baseRing S) (baseRing S)) :=
    ModuleCat.projective_of_categoryTheory_projective _
  refine ⟨Projective.factorThru ξ' ((sectionsComplex S K).homologyπ i), ?_⟩
  rw [globalCycleClass, RingTheory.TorProducts.cycleClass_def]
  have e := Projective.factorThru_comp ξ' ((sectionsComplex S K).homologyπ i)
  have e' := congrArg (· ≫ (DerivedCategory.homologyFunctorFactors _ i).inv.app
    (sectionsComplex S K) ≫ (DerivedCategory.homologyFunctor _ i).map (sectionsUnitQ S ⊤ K)) e
  simp only [Category.assoc] at e' ⊢
  refine e'.trans ?_
  have k : (DerivedCategory.homologyFunctor _ i).map (inv (sectionsUnitQ S ⊤ K)) ≫
      ((DerivedCategory.homologyFunctorFactors _ i).hom.app (sectionsComplex S K) ≫
        ((DerivedCategory.homologyFunctorFactors _ i).inv.app (sectionsComplex S K) ≫
          (DerivedCategory.homologyFunctor _ i).map (sectionsUnitQ S ⊤ K))) = 𝟙 _ := by
    rw [Iso.hom_inv_id_app_assoc, ← Functor.map_comp, IsIso.inv_hom_id,
      CategoryTheory.Functor.map_id]
  exact (Category.assoc _ _ _).trans ((congrArg (ξ ≫ ·) ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans k))).trans (Category.comp_id ξ))

/-- The pasting of three commutative squares behind `totalCupPairing_shift₂_transport_lhs`. -/
theorem paste_transport {C : Type*} [Category* C] {P₀ P₁ P₂ P₃ P₄ P₅ P₆ P₂' P₃' P₄' : C}
    (l : P₀ ⟶ P₁) (x : P₁ ⟶ P₂) (T : P₂ ⟶ P₃) (X : P₃ ⟶ P₄) (σ : P₄ ⟶ P₅) (F : P₅ ⟶ P₆)
    (x' : P₁ ⟶ P₂') (T₁ : P₂' ⟶ P₃') (X₁ : P₃' ⟶ P₄') (σ₁ : P₄' ⟶ P₆) (G : P₄ ⟶ P₄')
    (Y : P₃ ⟶ P₃') (e₁ : G ≫ σ₁ = σ ≫ F) (e₂ : X ≫ G = Y ≫ X₁)
    (e₃ : l ≫ x ≫ T ≫ Y = l ≫ x' ≫ T₁) :
    (l ≫ x ≫ T ≫ X ≫ σ) ≫ F = l ≫ x' ≫ T₁ ≫ X₁ ≫ σ₁ := by
  simp only [Category.assoc]
  rw [← e₁, ← Category.assoc X, e₂, Category.assoc, ← Category.assoc T, ← Category.assoc x,
    ← Category.assoc l, e₃]
  simp only [Category.assoc]

/-! ### Naturality of the shift identifications -/

section Naturality

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [HasZeroMorphisms C₁] [Preadditive C₂] [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁ : C₁, (F.obj X₁).Additive]

/-- **`mapBifunctorShift₂Iso` is natural in the first variable.** -/
theorem mapBifunctorShift₂Iso_hom_naturality₁ {K₁ L₁ : CochainComplex C₁ ℤ} (f₁ : K₁ ⟶ L₁)
    (K₂ : CochainComplex C₂ ℤ) (y : ℤ) [CochainComplex.HasMapBifunctor K₁ K₂ F]
    [CochainComplex.HasMapBifunctor L₁ K₂ F] :
    HomologicalComplex.mapBifunctorMap f₁ (𝟙 (K₂⟦y⟧)) F (ComplexShape.up ℤ) ≫
        (CochainComplex.mapBifunctorShift₂Iso L₁ K₂ F y).hom =
      (CochainComplex.mapBifunctorShift₂Iso K₁ K₂ F y).hom ≫
        (HomologicalComplex.mapBifunctorMap f₁ (𝟙 K₂) F (ComplexShape.up ℤ))⟦y⟧' := by
  ext n p q h
  simp [CochainComplex.ι_mapBifunctorShift₂Iso_hom_f _ _ _ _ _ _ _ _ (q + y) (n + y) rfl rfl,
    CochainComplex.ι_mapBifunctorShift₂Iso_hom_f_assoc _ _ _ _ _ _ _ _ (q + y) (n + y) rfl rfl]

/-- A morphism of total complexes is the composite of its two one-sided parts. -/
theorem mapBifunctorMap_comp_id_comp {K₁ L₁ : CochainComplex C₁ ℤ} {K₂ L₂ : CochainComplex C₂ ℤ}
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) [CochainComplex.HasMapBifunctor K₁ K₂ F]
    [CochainComplex.HasMapBifunctor L₁ K₂ F] [CochainComplex.HasMapBifunctor L₁ L₂ F] :
    HomologicalComplex.mapBifunctorMap f₁ (𝟙 K₂) F (ComplexShape.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap (𝟙 L₁) f₂ F (ComplexShape.up ℤ) =
      HomologicalComplex.mapBifunctorMap f₁ f₂ F (ComplexShape.up ℤ) := by
  ext
  simp [HomologicalComplex.ι_mapBifunctorMap]

/-- **`mapBifunctorShift₂Iso` is natural in both variables.** -/
theorem mapBifunctorShift₂Iso_hom_naturality {K₁ L₁ : CochainComplex C₁ ℤ}
    {K₂ L₂ : CochainComplex C₂ ℤ} (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (y : ℤ)
    [CochainComplex.HasMapBifunctor K₁ K₂ F] [CochainComplex.HasMapBifunctor L₁ K₂ F]
    [CochainComplex.HasMapBifunctor L₁ L₂ F] :
    HomologicalComplex.mapBifunctorMap f₁ (f₂⟦y⟧') F (ComplexShape.up ℤ) ≫
        (CochainComplex.mapBifunctorShift₂Iso L₁ L₂ F y).hom =
      (CochainComplex.mapBifunctorShift₂Iso K₁ K₂ F y).hom ≫
        (HomologicalComplex.mapBifunctorMap f₁ f₂ F (ComplexShape.up ℤ))⟦y⟧' := by
  rw [← mapBifunctorMap_comp_id_comp F f₁ (f₂⟦y⟧'), ← mapBifunctorMap_comp_id_comp F f₁ f₂,
    Functor.map_comp, Category.assoc, CochainComplex.mapBifunctorShift₂Iso_hom_naturality₂,
    ← Category.assoc, mapBifunctorShift₂Iso_hom_naturality₁, Category.assoc]

end Naturality

section NaturalityOne

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X₁ : C₁, (F.obj X₁).Additive]

/-- **`mapBifunctorShift₁Iso` is natural in the second variable.** -/
theorem mapBifunctorShift₁Iso_hom_naturality₂ (K₁ : CochainComplex C₁ ℤ)
    {K₂ L₂ : CochainComplex C₂ ℤ} (f₂ : K₂ ⟶ L₂) (x : ℤ) [CochainComplex.HasMapBifunctor K₁ K₂ F]
    [CochainComplex.HasMapBifunctor K₁ L₂ F] :
    HomologicalComplex.mapBifunctorMap (𝟙 (K₁⟦x⟧)) f₂ F (ComplexShape.up ℤ) ≫
        (CochainComplex.mapBifunctorShift₁Iso K₁ L₂ F x).hom =
      (CochainComplex.mapBifunctorShift₁Iso K₁ K₂ F x).hom ≫
        (HomologicalComplex.mapBifunctorMap (𝟙 K₁) f₂ F (ComplexShape.up ℤ))⟦x⟧' := by
  ext n p q h
  simp [CochainComplex.ι_mapBifunctorShift₁Iso_hom_f _ _ _ _ _ _ _ _ (p + x) (n + x) rfl rfl,
    CochainComplex.ι_mapBifunctorShift₁Iso_hom_f_assoc _ _ _ _ _ _ _ _ (p + x) (n + x) rfl rfl]

/-- **`mapBifunctorShift₁Iso` is natural in both variables.** -/
theorem mapBifunctorShift₁Iso_hom_naturality {K₁ L₁ : CochainComplex C₁ ℤ}
    {K₂ L₂ : CochainComplex C₂ ℤ} (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (x : ℤ)
    [CochainComplex.HasMapBifunctor K₁ K₂ F] [CochainComplex.HasMapBifunctor L₁ K₂ F]
    [CochainComplex.HasMapBifunctor L₁ L₂ F] :
    HomologicalComplex.mapBifunctorMap (f₁⟦x⟧') f₂ F (ComplexShape.up ℤ) ≫
        (CochainComplex.mapBifunctorShift₁Iso L₁ L₂ F x).hom =
      (CochainComplex.mapBifunctorShift₁Iso K₁ K₂ F x).hom ≫
        (HomologicalComplex.mapBifunctorMap f₁ f₂ F (ComplexShape.up ℤ))⟦x⟧' := by
  rw [← mapBifunctorMap_comp_id_comp F (f₁⟦x⟧') f₂, ← mapBifunctorMap_comp_id_comp F f₁ f₂,
    Functor.map_comp, Category.assoc, mapBifunctorShift₁Iso_hom_naturality₂,
    ← Category.assoc, CochainComplex.mapBifunctorShift₁Iso_hom_naturality₁, Category.assoc]

end NaturalityOne

end Stacks.Cohomology.DerivedGlobalCupProduct

end
