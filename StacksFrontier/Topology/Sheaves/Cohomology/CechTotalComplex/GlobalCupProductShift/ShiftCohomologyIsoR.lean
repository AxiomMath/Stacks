module

public import StacksFrontier.AlgebraicGeometry.Cohomology.FlasqueReductionOfTheCupProductSquare
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.GlobalCupProductCocycles
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CupPairingNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.NaiveCupProductShift
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.GlobalCupProductShift.ShiftCohomologyIso

/-!
# The global cup product and the shift: the identifications on cocycles

Auxiliary results for the compatibility of the cup product with the shift. Let `(S, 𝒪_S)` be a
ringed space. The identification `Hᵃ(S, 𝒦^•[n]) ≅ Hⁿ⁺ᵃ(S, 𝒦^•)` is natural in the complex, and is
read for the shift of complexes of modules over the sheaf of rings `ringSheaf S.sheaf` of `S`; the
tensoring of cocycles of two complexes of global sections is written in the spelling of the naive
cup product.

## Main definitions

* `Stacks.Cohomology.DerivedGlobalCupProduct.shiftBridge`: the two shifts of a complex of
  `𝒪_S`-modules agree.
* `Stacks.Cohomology.DerivedGlobalCupProduct.shiftR`: the shift of a complex of modules over the
  sheaf of rings `ringSheaf S.sheaf` of `S`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.shiftCohomologyIsoR`: the identification
  `Hᵃ(S, 𝒦^•[n]) ≅ Hⁿ⁺ᵃ(S, 𝒦^•)` for the shift `shiftR`.

## Main results

* `Stacks.Cohomology.DerivedGlobalCupProduct.shiftCohomologyIso_naturality`: the identification
  `Hᵃ(S, 𝒦^•[n]) ≅ Hⁿ⁺ᵃ(S, 𝒦^•)` is natural in the complex.
* `Stacks.Cohomology.DerivedGlobalCupProduct.globalCycleClass_shiftCohomologyIsoR`:
  `shiftCohomologyIsoR` on the class of a global cocycle is the identity on the cocycle.
* `Stacks.Cohomology.DerivedGlobalCupProduct.totalCupPairing_globalCycleClass_naive`:
  `totalCupPairing_globalCycleClass` in the spelling of the naive cup product.
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

variable {S : RingedSpace.{u, u}}

section ShiftTwo

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose

open Stacks.Cohomology.DerivedPullbackTensor (derivedToTensorNatTrans totalComplexPair)

variable (K M : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ)

/-- A functor sends an equality of composites to the equality of the composites of the images. -/
private theorem map_comp_eq_of_comp_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y Z W : C} {f : X ⟶ Y} {g : Y ⟶ W} {f' : X ⟶ Z} {g' : Z ⟶ W} (e : f ≫ g = f' ≫ g') :
    F.map f ≫ F.map g = F.map f' ≫ F.map g' := by
  rw [← F.map_comp, ← F.map_comp, e]

/-- **The identification `Hᵃ(S, 𝒦^•[n]) ≅ Hⁿ⁺ᵃ(S, 𝒦^•)` is natural** in the complex. -/
theorem shiftCohomologyIso_naturality
    {N N' : CochainComplex (SheafOfModules.{u} (structureSheafRing S)) ℤ} (f : N ⟶ N')
    (n a a' : ℤ) (h : n + a = a') :
    (DerivedCategory.homologyFunctor _ a).map ((baseSections S).map
        (DerivedCategory.Q.map (f⟦n⟧'))) ≫ (shiftCohomologyIso N' n a a' h).hom =
      (shiftCohomologyIso N n a a' h).hom ≫ (DerivedCategory.homologyFunctor _ a').map
        ((baseSections S).map (DerivedCategory.Q.map f)) := by
  have e1 := DerivedCategory.Q.commShiftIso_hom_naturality f n
  have e2 := (baseSections S).commShiftIso_hom_naturality (DerivedCategory.Q.map f) n
  have e3 := (DerivedCategory.homologyFunctor (ModuleCat.{u}
      (baseRing S)) 0).shiftIso_hom_naturality
    n a a' h ((baseSections S).map (DerivedCategory.Q.map f))
  have inner : (baseSections S).map (DerivedCategory.Q.map (f⟦n⟧')) ≫
      ((baseSections S).map ((DerivedCategory.Q.commShiftIso n).hom.app N') ≫
        ((baseSections S).commShiftIso n).hom.app (DerivedCategory.Q.obj N')) =
      ((baseSections S).map ((DerivedCategory.Q.commShiftIso n).hom.app N) ≫
        ((baseSections S).commShiftIso n).hom.app (DerivedCategory.Q.obj N)) ≫
        ((baseSections S).map (DerivedCategory.Q.map f))⟦n⟧' :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
      (map_comp_eq_of_comp_eq (baseSections S) e1)).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) e2).trans (Category.assoc _ _ _).symm)))
  let Ha := DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) a
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) ((Ha.map_comp _ _).symm.trans
    ((congrArg Ha.map inner).trans (Ha.map_comp _ _)))).trans
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) e3)))

/-- `mapBifunctorShift₂Iso` is natural, read on cohomology. -/
theorem homology_map_mapBifunctorShift₂Iso_naturality {K₁ M₁ : (CochainComplex (SheafOfModules.{u}
    (ringSheaf.{u, u, u} S.sheaf)) ℤ)} (a : K ⟶ K₁) (b : M ⟶ M₁)
    (t n : ℤ) :
    (DerivedCategory.homologyFunctor _ n).map ((baseSections S).map (DerivedCategory.Q.map
        (CochainComplex.mapBifunctorShift₂Iso K M (sheafTensor S.sheaf) t).hom)) ≫
        (DerivedCategory.homologyFunctor _ n).map ((baseSections S).map (DerivedCategory.Q.map
            ((CategoryTheory.shiftFunctor (CochainComplex (SheafOfModules.{u}
            (ringSheaf.{u, u, u} S.sheaf)) ℤ) t).map (HomologicalComplex.mapBifunctorMap a b
            (sheafTensor S.sheaf) (ComplexShape.up ℤ))))) =
      (DerivedCategory.homologyFunctor _ n).map ((baseSections S).map (DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap a ((CategoryTheory.shiftFunctor (CochainComplex
          (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) t).map b) (sheafTensor S.sheaf)
          (ComplexShape.up ℤ)))) ≫ (DerivedCategory.homologyFunctor _ n).map ((baseSections S).map
          (DerivedCategory.Q.map (CochainComplex.mapBifunctorShift₂Iso K₁ M₁
          (sheafTensor S.sheaf) t).hom)) := by
  let Hn := DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) n
  have e := mapBifunctorShift₂Iso_hom_naturality (sheafTensor S.sheaf) a b t
  exact map_comp_eq_of_comp_eq (DerivedCategory.Q ⋙ baseSections S ⋙ Hn) e.symm

/-- `totalCupPairing_naturality`, with the map of total complexes written as `mapBifunctorMap`. -/
theorem totalCupPairing_naturality' {K K' M M' : (CochainComplex (SheafOfModules.{u}
    (ringSheaf.{u, u, u} S.sheaf)) ℤ)} (f : K ⟶ K') (g : M ⟶ M') (i j : ℤ)
    (ξ : ModuleCat.of (baseRing S) (baseRing S) ⟶ cohomologyModule (DerivedCategory.Q.obj K) i)
    (η : ModuleCat.of (baseRing S) (baseRing S) ⟶ cohomologyModule (DerivedCategory.Q.obj M) j) :
    (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (ξ ⊗ₘ η) ≫ totalCupPairing K M i j ≫
        (DerivedCategory.homologyFunctor _ (i + j)).map ((baseSections S).map (DerivedCategory.Q.map
            (HomologicalComplex.mapBifunctorMap f g (sheafTensor S.sheaf) (ComplexShape.up ℤ)))) =
      (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
          ((ξ ≫ (DerivedCategory.homologyFunctor _ i).map ((baseSections S).map
          (DerivedCategory.Q.map f))) ⊗ₘ (η ≫ (DerivedCategory.homologyFunctor _ j).map
          ((baseSections S).map (DerivedCategory.Q.map g)))) ≫ totalCupPairing K' M' i j := by
  refine Eq.trans ?_ (totalCupPairing_naturality f g i j ξ η).symm
  exact congrArg (fun x => (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (ξ ⊗ₘ η) ≫
      totalCupPairing K M i j ≫
    (DerivedCategory.homologyFunctor _ (i + j)).map ((baseSections S).map
        (DerivedCategory.Q.map x)))
    (Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair_map (sheafTensor S.sheaf) f g).symm

/-- The shift of a bounded below complex of flasque modules is one. -/
theorem isFlasque_shift {K : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    (hfl : ∀ n : ℤ, TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (ringSheaf.{u, u, u} S.sheaf)).obj (K.X n))) (t : ℤ) (n : ℤ) :
    TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf (ringSheaf.{u, u, u} S.sheaf)).obj
      ((K⟦t⟧).X n)) :=
  hfl (n + t)

/-- The shift of a bounded below complex is bounded below. -/
theorem isStrictlyGE_shift {K : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    (hK : ∃ n : ℤ, K.IsStrictlyGE n) (t : ℤ) : ∃ n : ℤ, (K⟦t⟧).IsStrictlyGE n := by
  obtain ⟨n, hn⟩ := hK
  exact ⟨n - t, K.isStrictlyGE_shift n t (n - t) (by omega)⟩

/-- Global sections of the identification `(T[t])ⁿ ≅ Tⁿ⁺ᵗ` are the identification for the complex
of global sections. -/
theorem sections_shiftFunctorObjXIso_hom
    (T : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) (t n n' : ℤ)
    (h : n' = n + t) :
    (SheafOfModules.evaluation (ringSheaf.{u, u, u} S.sheaf) (op ⊤)).map
        (T.shiftFunctorObjXIso t n n' h).hom =
      ((sectionsComplex S T).shiftFunctorObjXIso t n n' h).hom := by
  subst h
  simp [CochainComplex.shiftFunctorObjXIso]
  rfl

/-- Global sections of the inverse of the identification `(T[t])ⁿ ≅ Tⁿ⁺ᵗ` are the inverse of the
identification for the complex of global sections. -/
theorem sections_shiftFunctorObjXIso_inv
    (T : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) (t n n' : ℤ)
    (h : n' = n + t) :
    (SheafOfModules.evaluation (ringSheaf.{u, u, u} S.sheaf) (op ⊤)).map
        (T.shiftFunctorObjXIso t n n' h).inv =
      ((sectionsComplex S T).shiftFunctorObjXIso t n n' h).inv := by
  subst h
  simp [CochainComplex.shiftFunctorObjXIso]
  rfl

/-- The tensoring of cocycles of two complexes of global sections, in the spelling of the naive cup
product. -/
theorem tensorCycles_naive (P Q : CochainComplex (SheafOfModules.{u}
    (ringSheaf.{u, u, u} S.sheaf)) ℤ)
    (i j : ℤ)
    (z₀ : (sectionsComplex S P).cycles i ⊗ (sectionsComplex S Q).cycles j ⟶
      (sectionsComplex S P ⊗ sectionsComplex S Q).cycles (i + j))
    (hz₀ : z₀ ≫ (sectionsComplex S P ⊗ sectionsComplex S Q).iCycles (i + j) =
      ((sectionsComplex S P).iCycles i ⊗ₘ (sectionsComplex S Q).iCycles j) ≫
        HomologicalComplex.ιTensorObj (sectionsComplex S P) (sectionsComplex S Q) i j (i + j) rfl) :
    z₀ ≫ (HomologicalComplex.mapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ P)
        (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ Q)
        (Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing S.sheaf ⊤))
        (ComplexShape.up ℤ)).iCycles (i + j) =
      Stacks.Cech.SheafTensorPairing.tensorMap S.sheaf ⊤
          ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ P).iCycles i)
          ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ Q).iCycles j) ≫
        HomologicalComplex.ιMapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ P)
          (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ Q)
          (Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing S.sheaf ⊤))
          (ComplexShape.up ℤ) i j (i + j) rfl := by
  rw [Stacks.Cech.SheafTensorPairing.tensorMap_eq_tensorHom]
  exact hz₀

/-- `globalCycleClass` is additive in the family of cocycles, in particular compatible with
signs. -/
theorem globalCycleClass_units_smul {M : ModuleCat.{u} (baseRing S)}
    {K : CochainComplex (SheafOfModules.{u} (structureSheafRing S)) ℤ} {i : ℤ} (e : ℤˣ)
    (z : M ⟶ (sectionsComplex S K).cycles i) :
    globalCycleClass (e • z) = e • globalCycleClass z := by
  rw [globalCycleClass, globalCycleClass, RingTheory.TorProducts.cycleClass_def,
    RingTheory.TorProducts.cycleClass_def, Linear.units_smul_comp, Linear.units_smul_comp]

/-- **The two shifts of a complex of `𝒪_S`-modules agree.** `ringSheaf S.sheaf` and
`structureSheafRing S` are two spellings of the structure sheaf of rings of `S`; the shifts of a
complex in the two categories of complexes they give have the same terms, and this is the
identification, degreewise the identity. -/
def shiftBridge (N : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) (n : ℤ) :
    ((CategoryTheory.shiftFunctor (CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf))
        ℤ) n).obj N : CochainComplex (SheafOfModules.{u} (structureSheafRing S)) ℤ) ≅
      (CategoryTheory.shiftFunctor (CochainComplex (SheafOfModules.{u} (structureSheafRing S)) ℤ)
        n).obj N :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (fun _ _ _ => by
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl)

/-- The components of `shiftBridge` are identities. -/
@[simp]
theorem shiftBridge_hom_f (N : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ)
    (n k : ℤ) : (shiftBridge N n).hom.f k = 𝟙 _ := rfl

/-- The shift of a complex of modules over the sheaf of rings `ringSheaf S.sheaf` of `S`. -/
abbrev shiftR (N : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) (n : ℤ) :
    CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ :=
  (CategoryTheory.shiftFunctor (CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf))
    ℤ) n).obj N

/-- **The identification `Hᵃ(S, 𝒦^•[n]) ≅ Hⁿ⁺ᵃ(S, 𝒦^•)` for the shift `shiftR`**:
`shiftCohomologyIso` read through `shiftBridge`. -/
def shiftCohomologyIsoR (N : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ)
    (n a a' : ℤ) (h : n + a = a') :
    cohomologyModule (DerivedCategory.Q.obj (shiftR N n)) a ≅
      cohomologyModule (DerivedCategory.Q.obj N) a' :=
  (DerivedCategory.homologyFunctor _ a).mapIso ((baseSections S).mapIso
      (DerivedCategory.Q.mapIso (shiftBridge N n))) ≪≫ shiftCohomologyIso N n a a' h

/-- The bridge between the two shifts is natural, after localization. -/
theorem Q_map_shiftBridge_naturality
    {N N' : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ} (f : N ⟶ N')
    (n : ℤ) :
    DerivedCategory.Q.map ((CategoryTheory.shiftFunctor (CochainComplex (SheafOfModules.{u}
        (ringSheaf.{u, u, u} S.sheaf)) ℤ) n).map f) ≫
        DerivedCategory.Q.map (shiftBridge N' n).hom =
      DerivedCategory.Q.map (shiftBridge N n).hom ≫
        DerivedCategory.Q.map ((CategoryTheory.shiftFunctor (CochainComplex (SheafOfModules.{u}
          (structureSheafRing S)) ℤ) n).map f) := by
  have hchain : @CategoryStruct.comp (CochainComplex (SheafOfModules.{u} (structureSheafRing S)) ℤ)
      _ _ _ _ ((CategoryTheory.shiftFunctor (CochainComplex (SheafOfModules.{u}
        (ringSheaf.{u, u, u} S.sheaf)) ℤ) n).map f) (shiftBridge N' n).hom =
      (shiftBridge N n).hom ≫ (CategoryTheory.shiftFunctor (CochainComplex (SheafOfModules.{u}
        (structureSheafRing S)) ℤ) n).map f := by
    refine HomologicalComplex.Hom.ext (funext fun k => ?_)
    refine (HomologicalComplex.comp_f _ _ k).trans (Eq.trans ?_
        (HomologicalComplex.comp_f _ _ k).symm)
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  exact map_comp_eq_of_comp_eq DerivedCategory.Q hchain

/-- **The identification `shiftCohomologyIsoR` is natural** in the complex. -/
theorem shiftCohomologyIsoR_naturality
    {N N' : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ} (f : N ⟶ N')
    (n a a' : ℤ) (h : n + a = a') :
    (DerivedCategory.homologyFunctor _ a).map ((baseSections S).map
        (DerivedCategory.Q.map ((CategoryTheory.shiftFunctor (CochainComplex (SheafOfModules.{u}
          (ringSheaf.{u, u, u} S.sheaf)) ℤ) n).map f))) ≫ (shiftCohomologyIsoR N' n a a' h).hom =
      (shiftCohomologyIsoR N n a a' h).hom ≫ (DerivedCategory.homologyFunctor _ a').map
        ((baseSections S).map (DerivedCategory.Q.map f)) := by
  let Ha := DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) a
  have eb := map_comp_eq_of_comp_eq (baseSections S ⋙ Ha)
    (Q_map_shiftBridge_naturality f n)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (shiftCohomologyIso N' n a a' h).hom)
    eb).trans ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (shiftCohomologyIso_naturality f n a a' h)).trans (Category.assoc _ _ _).symm)))

/-- The bridge followed by the commutation of global sections with the shift is the commutation
of global sections over `ringSheaf S.sheaf` with the shift, on cycles. -/
theorem cyclesMap_shiftBridge_commShiftIso
    (N : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) (n a : ℤ) :
    HomologicalComplex.cyclesMap (((globalSections S).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (shiftBridge N n).hom) a ≫
      HomologicalComplex.cyclesMap ((((globalSections S).mapHomologicalComplex
        (ComplexShape.up ℤ)).commShiftIso n).hom.app N) a =
      HomologicalComplex.cyclesMap ((((SheafOfModules.evaluation (ringSheaf.{u, u, u} S.sheaf)
        (op ⊤)).mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).hom.app N) a := by
  rw [← HomologicalComplex.cyclesMap_comp]
  congr 1

/-- **`shiftCohomologyIsoR` on the class of a global cocycle** is the identity on the cocycle. -/
theorem globalCycleClass_shiftCohomologyIsoR {M : ModuleCat.{u} (baseRing S)}
    (N : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) (n a a' : ℤ)
    (h : n + a = a') (z : M ⟶ (sectionsComplex S (shiftR N n)).cycles a) :
    globalCycleClass z ≫ (shiftCohomologyIsoR N n a a' h).hom =
      globalCycleClass (shiftCycles (sectionsComplex S N) a' h (z ≫ HomologicalComplex.cyclesMap
        ((((SheafOfModules.evaluation (ringSheaf.{u, u, u} S.sheaf) (op ⊤)).mapHomologicalComplex
          (ComplexShape.up ℤ)).commShiftIso n).hom.app N) a)) := by
  have e1 := globalCycleClass_map z (shiftBridge N n).hom
  have e2 := globalCycleClass_shiftCohomologyIso N n a a' h (z ≫ HomologicalComplex.cyclesMap
    (((globalSections S).mapHomologicalComplex (ComplexShape.up ℤ)).map (shiftBridge N n).hom) a)
  have e3 := congrArg (fun x => globalCycleClass (shiftCycles (sectionsComplex S N) a' h (z ≫ x)))
    (cyclesMap_shiftBridge_commShiftIso N n a)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (shiftCohomologyIso N n a a' h).hom)
    e1).trans (e2.trans ((congrArg (fun x => globalCycleClass (shiftCycles
        (sectionsComplex S N) a' h
      x)) (Category.assoc _ _ _)).trans e3)))

/-- The class of a cocycle of a tensor product of complexes of sections, carried by the naive
cup product and the unit, is the class of the global cocycle obtained by the naive cup product. -/
theorem cycleClass_naive_unit (P Q : CochainComplex (SheafOfModules.{u}
    (ringSheaf.{u, u, u} S.sheaf)) ℤ)
    (n : ℤ) {T : ModuleCat.{u} (baseRing S)}
    (y : T ⟶ (sectionsComplex S P ⊗ sectionsComplex S Q).cycles n) :
    cycleClass y ≫ (DerivedCategory.homologyFunctor _ n).map
        (DerivedCategory.Q.map (Stacks.Cech.SheafTensorPairing.naiveCupProductEval S.sheaf ⊤ P Q) ≫
          sectionsUnitQ S ⊤ ((totalComplexPair (sheafTensor S.sheaf)).obj (P, Q))) =
      globalCycleClass (y ≫ HomologicalComplex.cyclesMap
        (Stacks.Cech.SheafTensorPairing.naiveCupProductEval S.sheaf ⊤ P Q) n) := by
  refine (congrArg (cycleClass y ≫ ·) (Functor.map_comp _ _ _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (· ≫ _) (RingTheory.TorProducts.cycleClass_comp_map y _)

/-- `totalCupPairing_globalCycleClass`, with the right hand side read as one global cocycle
class. -/
theorem totalCupPairing_globalCycleClass_eq
    (P Q : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) {i j : ℤ}
    (z : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S P).cycles i)
    (w : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S Q).cycles j)
    (z₀ : (sectionsComplex S P).cycles i ⊗ (sectionsComplex S Q).cycles j ⟶
      (sectionsComplex S P ⊗ sectionsComplex S Q).cycles (i + j))
    (hz₀ : z₀ ≫ (sectionsComplex S P ⊗ sectionsComplex S Q).iCycles (i + j) =
      ((sectionsComplex S P).iCycles i ⊗ₘ (sectionsComplex S Q).iCycles j) ≫
        HomologicalComplex.ιTensorObj (sectionsComplex S P) (sectionsComplex S Q) i j (i + j)
          rfl) :
    (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        (globalCycleClass z ⊗ₘ globalCycleClass w) ≫ totalCupPairing P Q i j =
      globalCycleClass ((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (z ⊗ₘ w) ≫ z₀ ≫
        HomologicalComplex.cyclesMap
          (Stacks.Cech.SheafTensorPairing.naiveCupProductEval S.sheaf ⊤ P Q) (i + j)) := by
  refine (totalCupPairing_globalCycleClass z w z₀ hz₀).trans ?_
  refine (congrArg (fun x => (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (z ⊗ₘ w) ≫ x)
    (cycleClass_naive_unit P Q (i + j) z₀)).trans ?_
  exact (congrArg (_ ≫ ·) (comp_globalCycleClass _ _)).trans (comp_globalCycleClass _ _)

/-- The tensoring of cocycles of two complexes of global sections exists in the spelling of the
naive cup product. -/
theorem exists_tensorCycles_naive
    (P Q : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) (i j : ℤ) :
    ∃ z₀ : ((Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing
        S.sheaf ⊤)).obj ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ P).cycles i)).obj
        ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ Q).cycles j) ⟶
        (HomologicalComplex.mapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ P)
            (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ Q)
            (Stacks.Cech.CupProduct.tensorModules
            (Stacks.Cech.ModuleCupProduct.CoeffRing S.sheaf ⊤))
          (ComplexShape.up ℤ)).cycles (i + j),
      z₀ ≫ (HomologicalComplex.mapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ P)
          (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ Q)
          (Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing S.sheaf ⊤))
          (ComplexShape.up ℤ)).iCycles (i + j) =
        Stacks.Cech.SheafTensorPairing.tensorMap S.sheaf ⊤
            ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ P).iCycles i)
            ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ Q).iCycles j) ≫
          HomologicalComplex.ιMapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ P)
              (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ Q)
              (Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing
              S.sheaf ⊤)) (ComplexShape.up ℤ) i j (i + j)
            rfl := by
  obtain ⟨z₀, hz₀⟩ := RingTheory.TorProducts.exists_tensorCycles (sectionsComplex S P)
    (sectionsComplex S Q) i j
  exact ⟨z₀, tensorCycles_naive P Q i j z₀ hz₀⟩

/-- `globalCycleClass_map` for complexes over `ringSheaf S.sheaf`, with the map on cocycles
written through evaluation at `⊤`. -/
theorem globalCycleClass_mapR {T : ModuleCat.{u} (baseRing S)}
    {P P' : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ} {i : ℤ}
    (z : T ⟶ (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ P).cycles i) (f : P ⟶ P') :
    globalCycleClass z ≫ (DerivedCategory.homologyFunctor _ i).map
        ((baseSections S).map (DerivedCategory.Q.map f)) =
      globalCycleClass (z ≫ HomologicalComplex.cyclesMap
          (((SheafOfModules.evaluation (ringSheaf.{u, u, u} S.sheaf) (op ⊤)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map f) i) :=
  globalCycleClass_map z f

/-- `globalCycleClass_mapR` followed by an arbitrary morphism. -/
theorem globalCycleClass_mapR_assoc {T : ModuleCat.{u} (baseRing S)}
    {P P' : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ} {i : ℤ}
    (z : T ⟶ (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ P).cycles i) (f : P ⟶ P')
        {Z : ModuleCat.{u} (baseRing S)}
    (h : cohomologyModule (DerivedCategory.Q.obj P') i ⟶ Z) :
    globalCycleClass z ≫ (DerivedCategory.homologyFunctor _ i).map
        ((baseSections S).map (DerivedCategory.Q.map f)) ≫ h =
      globalCycleClass (z ≫ HomologicalComplex.cyclesMap
          (((SheafOfModules.evaluation (ringSheaf.{u, u, u} S.sheaf) (op ⊤)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map f) i) ≫ h :=
  (Category.assoc _ _ _).symm.trans (congrArg (· ≫ h) (globalCycleClass_map z f))

/-- `totalCupPairing_globalCycleClass` in the spelling of the naive cup product, with the right
hand side read as one global cocycle class. -/
theorem totalCupPairing_globalCycleClass_naive
    (P Q : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) {i j : ℤ}
    (z : ModuleCat.of (baseRing S) (baseRing S) ⟶
        (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ P).cycles i)
    (w : ModuleCat.of (baseRing S) (baseRing S) ⟶
        (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ Q).cycles j)
    (z₀ : ((Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing
        S.sheaf ⊤)).obj ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ P).cycles i)).obj
        ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ Q).cycles j) ⟶
        (HomologicalComplex.mapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ P)
            (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ Q)
            (Stacks.Cech.CupProduct.tensorModules
            (Stacks.Cech.ModuleCupProduct.CoeffRing S.sheaf ⊤))
          (ComplexShape.up ℤ)).cycles (i + j))
    (hz₀ : z₀ ≫ (HomologicalComplex.mapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex
        S.sheaf ⊤ P) (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ Q)
        (Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing S.sheaf ⊤))
          (ComplexShape.up ℤ)).iCycles (i + j) =
        Stacks.Cech.SheafTensorPairing.tensorMap S.sheaf ⊤
            ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ P).iCycles i)
            ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ Q).iCycles j) ≫
          HomologicalComplex.ιMapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ P)
              (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ Q)
              (Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing
              S.sheaf ⊤)) (ComplexShape.up ℤ) i j (i + j)
            rfl) :
    (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        (globalCycleClass z ⊗ₘ globalCycleClass w) ≫ totalCupPairing P Q i j =
      globalCycleClass ((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        Stacks.Cech.SheafTensorPairing.tensorMap S.sheaf ⊤ z w ≫ z₀ ≫
        HomologicalComplex.cyclesMap
          (Stacks.Cech.SheafTensorPairing.naiveCupProductEval S.sheaf ⊤ P Q) (i + j)) := by
  rw [Stacks.Cech.SheafTensorPairing.tensorMap_eq_tensorHom] at hz₀
  refine (totalCupPairing_globalCycleClass_eq P Q z w z₀ hz₀).trans ?_
  exact congrArg (fun x => globalCycleClass ((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
    x ≫ z₀ ≫ HomologicalComplex.cyclesMap
      (Stacks.Cech.SheafTensorPairing.naiveCupProductEval S.sheaf ⊤ P Q) (i + j)))
    (Stacks.Cech.SheafTensorPairing.tensorMap_eq_tensorHom S.sheaf ⊤ z w).symm

/-- `totalCupPairing_globalCycleClass_naive` followed by an arbitrary morphism. -/
theorem totalCupPairing_globalCycleClass_naive_assoc
    (P Q : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) {i j : ℤ}
    (z : ModuleCat.of (baseRing S) (baseRing S) ⟶
        (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ P).cycles i)
    (w : ModuleCat.of (baseRing S) (baseRing S) ⟶
        (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ Q).cycles j)
    (z₀ : ((Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing
        S.sheaf ⊤)).obj ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ P).cycles i)).obj
        ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ Q).cycles j) ⟶
        (HomologicalComplex.mapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ P)
            (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ Q)
            (Stacks.Cech.CupProduct.tensorModules
            (Stacks.Cech.ModuleCupProduct.CoeffRing S.sheaf ⊤))
          (ComplexShape.up ℤ)).cycles (i + j))
    (hz₀ : z₀ ≫ (HomologicalComplex.mapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex
        S.sheaf ⊤ P) (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ Q)
        (Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing S.sheaf ⊤))
          (ComplexShape.up ℤ)).iCycles (i + j) =
        Stacks.Cech.SheafTensorPairing.tensorMap S.sheaf ⊤
            ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ P).iCycles i)
            ((Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ Q).iCycles j) ≫
          HomologicalComplex.ιMapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ P)
              (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ Q)
              (Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing
              S.sheaf ⊤)) (ComplexShape.up ℤ) i j (i + j)
            rfl) {Z : ModuleCat.{u} (baseRing S)}
    (h : cohomologyModule (DerivedCategory.Q.obj
      ((totalComplexPair (sheafTensor S.sheaf)).obj (P, Q))) (i + j) ⟶ Z) :
    (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        (globalCycleClass z ⊗ₘ globalCycleClass w) ≫ totalCupPairing P Q i j ≫ h =
      globalCycleClass ((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        Stacks.Cech.SheafTensorPairing.tensorMap S.sheaf ⊤ z w ≫ z₀ ≫
        HomologicalComplex.cyclesMap
          (Stacks.Cech.SheafTensorPairing.naiveCupProductEval S.sheaf ⊤ P Q) (i + j)) ≫ h := by
  have e := congrArg (· ≫ h) (totalCupPairing_globalCycleClass_naive P Q z w z₀ hz₀)
  simp only [Category.assoc] at e
  exact e

/-- `globalCycleClass_shiftCohomologyIsoR` with the cocycles written through evaluation at
`⊤`. -/
theorem globalCycleClass_shiftCohomologyIsoR' {T : ModuleCat.{u} (baseRing S)}
    (N : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) (n a a' : ℤ)
    (h : n + a = a') (z : T ⟶ (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤
        (shiftR N n)).cycles a) :
    globalCycleClass z ≫ (shiftCohomologyIsoR N n a a' h).hom =
      globalCycleClass (shiftCycles (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ N) a' h
          (z ≫ HomologicalComplex.cyclesMap
        ((((SheafOfModules.evaluation (ringSheaf.{u, u, u} S.sheaf) (op ⊤)).mapHomologicalComplex
            (ComplexShape.up ℤ)).commShiftIso n).hom.app N) a)) :=
  globalCycleClass_shiftCohomologyIsoR N n a a' h z

/-- `shiftCycles` commutes with precomposition, with the cocycle written as a composite of five
morphisms in two bracketings. -/
theorem shiftCycles_paste {R : Type u} [Ring R] (Y : CochainComplex (ModuleCat.{u} R) ℤ)
    {n a : ℤ} (a' : ℤ) (h : n + a = a') {T T₁ A₁ B C D : ModuleCat.{u} R} (l : T ⟶ T₁)
    (x₁ : T₁ ⟶ A₁) (x₂ : A₁ ⟶ B) (x₃ : B ⟶ C) (x₄ : C ⟶ D) (x₅ : D ⟶ (Y⟦n⟧).cycles a) :
    shiftCycles Y a' h (((l ≫ x₁ ≫ x₂ ≫ x₃) ≫ x₄) ≫ x₅) =
      l ≫ shiftCycles Y a' h (x₁ ≫ x₂ ≫ x₃ ≫ x₄ ≫ x₅) := by
  rw [shiftCycles, shiftCycles]
  simp only [Category.assoc]
  exact Category.assoc _ _ _

/-- A sign in front of a family of cocycles of the tensor square of the free module of rank one
comes out of its class. -/
theorem globalCycleClass_unitor_units_smul
    {N : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ} {n : ℤ} (e : ℤˣ)
    (Y : ((Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing
        S.sheaf ⊤)).obj (ModuleCat.of (baseRing S) (baseRing S))).obj
        (ModuleCat.of (baseRing S) (baseRing S)) ⟶
            (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ N).cycles n) :
    globalCycleClass ((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (e • Y)) =
      e • globalCycleClass ((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ Y) :=
  (congrArg globalCycleClass (Linear.comp_units_smul _ _ _)).trans
    (globalCycleClass_units_smul e _)

end ShiftTwo

end Stacks.Cohomology.DerivedGlobalCupProduct

end
