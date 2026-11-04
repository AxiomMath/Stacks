module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.ResidueBoundaryClosedForms

/-!
# The boundary of the residue sequence through closed one-forms
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.LineBundle

attribute [local instance 5000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus

variable (D : Situation.{u})

open Stacks.Cohomology.Leray (AbelianSheaf sectionsFunctor)
open Stacks.Cohomology.RealizationShift (shiftHomologyIso)
open Stacks.Cohomology.RealizationBoundary (mapPlus)

/-- The shifted residue sequence of abelian sheaves. -/
abbrev Situation.residueAbelianSequence :
    ShortComplex (CochainComplex.Plus (AbelianSheaf D.baseSpace.carrier)) :=
  mapPlus (SheafOfModules.toSheaf (structureSheafRing D.baseSpace)) D.residuePlusSequence

/-- The inclusion of the closed forms into `Ω^•[1]`, translated by the identification of the
first term of the residue sequence, as a morphism into the translate of `Ω^•`. -/
abbrev Situation.closedFormsShiftHom :
    (Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj D.closedForms ⟶
      D.deRhamAbelianPlus⟦(1 : ℤ)⟧ :=
  Stacks.Cohomology.RightDerivedBoundary.cyclesSingleHom D.deRhamShiftAbelianPlus ≫
    (SheafOfModules.toSheaf (structureSheafRing D.baseSpace)).mapCochainComplexPlus.map
      D.residuePlusShiftHom ≫
    ((SheafOfModules.toSheaf (structureSheafRing D.baseSpace)).mapCochainComplexPlus.commShiftIso
      (1 : ℤ)).hom.app D.deRhamPlus

/-- A morphism killing a map kills its multiples, with every object and morphism a variable. -/
private theorem units_smul_zero {C : Type*} [Category* C] [Preadditive C] {p q r : C}
    (a : p ⟶ q) (d : q ⟶ r) (n : ℤ) (h : (a ≫ 𝟙 q) ≫ d = 0) : a ≫ (n.negOnePow • d) = 0 := by
  rw [Category.comp_id] at h
  rw [Units.smul_def, Preadditive.comp_zsmul, h, smul_zero]

/-- A functor applied to a three-fold composite, two factors cancelling, with every object and
morphism a variable. -/
private theorem map_three_paste {C D' : Type*} [Category* C] [Category* D'] (G : C ⥤ D')
    {p q r s : C} {t : D'} (a : p ⟶ q) (b : q ⟶ r) (c : r ⟶ s) (σ : G.obj s ⟶ t)
    (x : G.obj r ⟶ G.obj q) (y : G.obj q ⟶ t) (hc : G.map c ≫ σ = x ≫ y)
    (he : G.map b ≫ x = 𝟙 _) :
    G.map (a ≫ b ≫ c) ≫ σ = G.map a ≫ y := by
  rw [G.map_comp, G.map_comp, Category.assoc, Category.assoc, hc, reassoc_of% he]

/-- The inclusion of the closed forms into the translate, on cochain complexes. -/
theorem Situation.closedForms_shift_d :
    ∀ k, (ComplexShape.up ℤ).Rel 0 k → (D.deRhamShiftAbelianPlus.obj.iCycles 0 :
      D.closedForms ⟶ (D.deRhamAbelianPlus.obj⟦(1 : ℤ)⟧).X 0) ≫
        (D.deRhamAbelianPlus.obj⟦(1 : ℤ)⟧).d 0 k = 0 := by
  intro k hk
  obtain rfl : k = 1 := by simp at hk; omega
  exact units_smul_zero _ _ _ (D.closedForms_d 2 (by simp))

/-- The inclusion of the closed forms into `Ω^•`, from degree one, on cochain complexes. -/
theorem Situation.closedForms_d' :
    ∀ k, (ComplexShape.up ℤ).Rel 1 k → (D.deRhamShiftAbelianPlus.obj.iCycles 0 :
      D.closedForms ⟶ D.deRhamAbelianPlus.obj.X 1) ≫ D.deRhamAbelianPlus.obj.d 1 k = 0 :=
  fun k hk => (Category.comp_id _).symm.trans (D.closedForms_d k hk)

/-- **The translated inclusion of the closed forms, on cochain complexes**: the inclusion of the
cycles in degree zero. -/
theorem Situation.ι_map_closedFormsShiftHom :
    (CochainComplex.Plus.ι _).map D.closedFormsShiftHom ≫
      ((CochainComplex.Plus.ι _).commShiftIso (1 : ℤ)).hom.app D.deRhamAbelianPlus =
    HomologicalComplex.mkHomFromSingle (K := D.deRhamAbelianPlus.obj⟦(1 : ℤ)⟧) (j := 0)
      (D.deRhamShiftAbelianPlus.obj.iCycles 0) D.closedForms_shift_d := by
  have hc := AlgebraicGeometry.SheafOfModules.ι_map_mapCochainComplexPlus_commShiftIso_hom_app
    (SheafOfModules.toSheaf (structureSheafRing D.baseSpace)) (1 : ℤ) D.deRhamPlus
  have he : (CochainComplex.Plus.ι _).map
      ((SheafOfModules.toSheaf (structureSheafRing D.baseSpace)).mapCochainComplexPlus.map
        D.residuePlusShiftHom) ≫
      ((SheafOfModules.toSheaf (structureSheafRing D.baseSpace)).mapHomologicalComplex _).map
        (((CochainComplex.Plus.ι _).commShiftIso (1 : ℤ)).hom.app D.deRhamPlus) = 𝟙 _ := by
    show ((SheafOfModules.toSheaf (structureSheafRing D.baseSpace)).mapHomologicalComplex _).map
        (((CochainComplex.Plus.ι _).commShiftIso (1 : ℤ)).inv.app D.deRhamPlus) ≫ _ = _
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
    rfl
  refine (map_three_paste _ _ _ _ _ _ _ hc he).trans ?_
  refine HomologicalComplex.from_single_hom_ext ?_
  refine (HomologicalComplex.comp_f _ _ 0).trans ?_
  simp only [Functor.mapHomologicalComplex_commShiftIso_hom_app_f]
  exact (Stacks.Cohomology.RightDerivedBoundary.cyclesSingleHom_f D.deRhamShiftAbelianPlus).trans
    (HomologicalComplex.mkHomFromSingle_f (K := D.deRhamAbelianPlus.obj⟦(1 : ℤ)⟧) (j := 0)
      (D.deRhamShiftAbelianPlus.obj.iCycles 0) D.closedForms_shift_d).symm

/-- The translated inclusion of the closed forms, as the preimage of a morphism of complexes. -/
theorem Situation.closedFormsShiftHom_eq :
    D.closedFormsShiftHom = (CochainComplex.Plus.ι _).preimage
      (HomologicalComplex.mkHomFromSingle (K := D.deRhamAbelianPlus.obj⟦(1 : ℤ)⟧) (j := 0)
        (D.deRhamShiftAbelianPlus.obj.iCycles 0) D.closedForms_shift_d ≫
        ((CochainComplex.Plus.ι _).commShiftIso (1 : ℤ)).inv.app D.deRhamAbelianPlus) := by
  apply (CochainComplex.Plus.ι _).map_injective
  rw [Functor.map_preimage, ← D.ι_map_closedFormsShiftHom, Category.assoc, Iso.hom_inv_id_app]
  exact (Category.comp_id _).symm

/-- The algebra of `shiftHomologyIso_cyclesRightDerivedOneMap`, with every object and morphism a
variable. -/
private theorem ch_paste {C : Type*} [Category* C] {p q r s t u : C} (a : p ⟶ q) (b : q ⟶ r)
    (sh : r ⟶ t) (c : r ⟶ s) (sh' : s ⟶ t) (m : p ⟶ s) (σ : p ⟶ u) (ι : u ⟶ t)
    (hs : sh = c ≫ sh') (hm : a ≫ b ≫ c = m) (hS : m ≫ sh' = σ ≫ ι) :
    a ≫ b ≫ sh = σ ≫ ι := by
  rw [hs, ← hS, ← hm]
  simp only [Category.assoc]

/-- **The shift bookkeeping of the abelian boundary of the residue sequence**: a class of `R¹Γ`
of the closed forms, carried into `H¹(X, Ω^•[1])` by the inclusion of the cycles and then to
`H²(X, Ω^•)`, is its image under `H¹(X, Z) ≅ H²(X, Z[-1])` followed by the inclusion
`Z[-1] ⟶ Ω^•`. -/
theorem Situation.shiftHomologyIso_cyclesRightDerivedOneMap :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 1).map
        ((sectionsFunctor D.baseSpace.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map
            (Stacks.Cohomology.RightDerivedBoundary.cyclesSingleHom D.deRhamShiftAbelianPlus))) ≫
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 1).map
        (D.abelianSections.map D.residuePlusShiftHom) ≫
      (shiftHomologyIso D.abelianSections D.deRhamPlus 1 1 2 (by omega)).hom =
    ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso
        (sectionsFunctor D.baseSpace.carrier ⊤).rightDerivedFunctorPlus 1 1).app
          D.closedForms).inv ≫
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (1 + 1)).map
        ((DerivedCategory.Plus.Q ⋙
            (sectionsFunctor D.baseSpace.carrier ⊤).rightDerivedFunctorPlus).map
          (ObjectProperty.homMk (HomologicalComplex.mkHomFromSingle (K := D.deRhamAbelianPlus.obj)
            (j := 1) (D.deRhamShiftAbelianPlus.obj.iCycles 0) D.closedForms_d') :
              (Stacks.DerivedIndexing.singlePlusFunctor _ 1).obj D.closedForms ⟶
                D.deRhamAbelianPlus)) := by
  have hs := Stacks.Cohomology.RealizationShift.shiftHomologyIso_comp
    (SheafOfModules.toSheaf (structureSheafRing D.baseSpace)).mapCochainComplexPlus
    (DerivedCategory.Plus.Q ⋙ (sectionsFunctor D.baseSpace.carrier ⊤).rightDerivedFunctorPlus)
    D.deRhamPlus 1 1 2 (by omega)
  have hS := AlgebraicGeometry.SheafOfModules.homology_map_comp_shiftHomologyIso_eq_of_cochain
    (sectionsFunctor D.baseSpace.carrier ⊤).rightDerivedFunctorPlus D.closedForms
    D.deRhamAbelianPlus
    (HomologicalComplex.mkHomFromSingle (K := D.deRhamAbelianPlus.obj⟦(1 : ℤ)⟧) (j := 0)
        (D.deRhamShiftAbelianPlus.obj.iCycles 0) D.closedForms_shift_d)
    (HomologicalComplex.mkHomFromSingle (K := D.deRhamAbelianPlus.obj) (j := 1)
        (D.deRhamShiftAbelianPlus.obj.iCycles 0) D.closedForms_d')
    (CochainComplex.singleFunctors_shiftIso_inv_comp_shift_mkHomFromSingle _ _ _ _)
  rw [← D.closedFormsShiftHom_eq] at hS
  refine ch_paste _ _ _ _ _ _ _ _ hs ?_ hS
  simp only [← Functor.map_comp]
  show (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 1).map
    ((DerivedCategory.Plus.Q ⋙ (sectionsFunctor D.baseSpace.carrier ⊤).rightDerivedFunctorPlus).map
      (Stacks.Cohomology.RightDerivedBoundary.cyclesSingleHom D.deRhamShiftAbelianPlus) ≫
    (DerivedCategory.Plus.Q ⋙ (sectionsFunctor D.baseSpace.carrier ⊤).rightDerivedFunctorPlus).map
      ((SheafOfModules.toSheaf (structureSheafRing D.baseSpace)).mapCochainComplexPlus.map
        D.residuePlusShiftHom) ≫
    (DerivedCategory.Plus.Q ⋙ (sectionsFunctor D.baseSpace.carrier ⊤).rightDerivedFunctorPlus).map
      (((SheafOfModules.toSheaf (structureSheafRing D.baseSpace)).mapCochainComplexPlus.commShiftIso
        (1 : ℤ)).hom.app D.deRhamPlus)) = _
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

/-- The two spellings of the inclusion of the closed forms agree. -/
theorem Situation.closedFormsInclusion_eq_mkHomFromSingle :
    D.closedFormsInclusion = HomologicalComplex.mkHomFromSingle (K := D.deRhamAbelianPlus.obj)
      (j := 1) (D.deRhamShiftAbelianPlus.obj.iCycles 0) D.closedForms_d' := by
  refine HomologicalComplex.from_single_hom_ext ?_
  refine (HomologicalComplex.mkHomFromSingle_f _ D.closedForms_d).trans ?_
  exact (congrArg (_ ≫ ·) (Category.comp_id _)).trans
    (HomologicalComplex.mkHomFromSingle_f (K := D.deRhamAbelianPlus.obj) (j := 1) _
      D.closedForms_d').symm

/-- The algebra of `logarithmicDifferentialComplexBase_homology`, with every object and morphism
a variable. -/
private theorem cd_paste {C D' : Type*} [Category* C] [Category* D'] (H : C ⥤ D')
    {p q : D'} {a b c : C} (σu : p ⟶ H.obj a) (g : p ⟶ q) (σZ : q ⟶ H.obj b) (f : a ⟶ b)
    (i : b ⟶ c) (hσ : g ≫ σZ = σu ≫ H.map f) :
    σu ≫ H.map (f ≫ i) = g ≫ σZ ≫ H.map i := by
  rw [H.map_comp, ← Category.assoc, ← hσ, Category.assoc]

open AlgebraicGeometry.SheafOfModules (sheafCohomologyOneIsoShiftedCohomologyTwo) in
/-- **`d log` on degree-two hypercohomology, through the closed forms**: on
`H²(X, 𝒪_X^*[-1]) = H¹(X, 𝒪_X^*)`, the map induced by `d log : 𝒪_X^*[-1] ⟶ Ω^•` is the map
induced on `H¹` by `d log : 𝒪_X^* ⟶ Z`, followed by `H¹(X, Z) = H²(X, Z[-1])` and the inclusion
`Z[-1] ⟶ Ω^•`. -/
theorem Situation.logarithmicDifferentialComplexBase_homology (x : ((sectionsFunctor
    D.baseSpace.carrier ⊤).rightDerived 1).obj D.unitsSheafBase) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 2).map
        ((sectionsFunctor D.baseSpace.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map D.logarithmicDifferentialComplexBase))
        ((sheafCohomologyOneIsoShiftedCohomologyTwo D.baseSpace.carrier D.unitsSheafBase).hom x) =
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 2).map
        ((sectionsFunctor D.baseSpace.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map (ObjectProperty.homMk D.closedFormsInclusion :
            (Stacks.DerivedIndexing.singlePlusFunctor _ 1).obj D.closedForms ⟶
              D.deRhamAbelianPlus)))
        ((sheafCohomologyOneIsoShiftedCohomologyTwo D.baseSpace.carrier D.closedForms).hom
          (((sectionsFunctor D.baseSpace.carrier ⊤).rightDerived 1).map
            D.logarithmicDifferentialClosed x)) := by
  have hn :=
    AlgebraicGeometry.SheafOfModules.sheafCohomologyOneIsoShiftedCohomologyTwo_hom_naturality
      D.logarithmicDifferentialClosed
  have key := cd_paste (DerivedCategory.Plus.Q ⋙
    (sectionsFunctor D.baseSpace.carrier ⊤).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 2) _ _ _
    (ObjectProperty.homMk ((CochainComplex.singleFunctor _ 1).map
        D.logarithmicDifferentialClosed) :
      D.unitsComplexBase ⟶ (Stacks.DerivedIndexing.singlePlusFunctor _ 1).obj D.closedForms)
    (ObjectProperty.homMk D.closedFormsInclusion) hn
  rw [D.logarithmicDifferentialComplexBase_eq]
  exact ConcreteCategory.congr_hom key x

/-- **The two readings of `d log : 𝒪_X^*[-1] ⟶ Ω^•` agree**: the morphism of Tag 0FLE into the
abelian de Rham complex, followed by its identification with the complex underlying the de Rham
complex of sheaves of `f^{-1}𝒪_S`-modules, is `logarithmicDifferentialComplexBase`. -/
theorem Situation.logarithmicDifferentialComplexMapPlus_comp_iso :
    (AlgebraicGeometry.SheafOfModules.logarithmicDifferentialComplexMapPlus
        (Scheme.Hom.deRhamAlgebras D.f)
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f)) ≫
      (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlusIso (Scheme.Hom.deRhamAlgebras D.f)
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))).hom :
      D.unitsComplexBase ⟶ D.deRhamAbelianPlus) = D.logarithmicDifferentialComplexBase := by
  refine ObjectProperty.hom_ext _ (HomologicalComplex.from_single_hom_ext ?_)
  exact Category.assoc _ _ _

open AlgebraicGeometry.SheafOfModules (sheafCohomologyOneIsoShiftedCohomologyTwo) in
/-- `H¹(X, F) ≅ H²(X, F[-1])` through the comparison of the two indexings of the right derived
functors. -/
theorem sheafCohomologyOneIsoShiftedCohomologyTwo_hom_apply {Y : TopCat.{u}} (F : AbelianSheaf Y)
    (y : ((sectionsFunctor Y ⊤).rightDerived 1).obj F) :
    (sheafCohomologyOneIsoShiftedCohomologyTwo Y F).hom y =
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso
        (sectionsFunctor Y ⊤).rightDerivedFunctorPlus 1 1).app F).inv
        ((Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard
          (sectionsFunctor Y ⊤) 1).inv.app F y) := by
  have h : (Stacks.DerivedIndexing.rightDerivedIso (sectionsFunctor Y ⊤) 1).hom.app F =
      (Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard
        (sectionsFunctor Y ⊤) 1).inv.app F := by
    have e : Stacks.DerivedIndexing.rightDerivedIso (sectionsFunctor Y ⊤) 1 =
        (Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard
          (sectionsFunctor Y ⊤) 1).symm :=
      Iso.ext (by
        rw [← Iso.inv_eq_inv, Iso.symm_inv, Stacks.DerivedIndexing.rightDerivedIso_inv_eq])
    rw [e]
    rfl
  show ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso
      (sectionsFunctor Y ⊤).rightDerivedFunctorPlus 1 1).app F).inv
      ((Stacks.DerivedIndexing.rightDerivedIso (sectionsFunctor Y ⊤) 1).hom.app F y) = _
  rw [h]

attribute [local instance] Stacks.Cohomology.Generators.picardGroupAddCommGroup

/-- A functor into abelian groups applied to a composite, on an element, with every object and
morphism a variable. -/
private theorem map_comp_apply_eq {C : Type*} [Category* C] (F : C ⥤ AddCommGrpCat.{u}) {a b c : C}
    (f : a ⟶ b) (g : b ⟶ c) (x : F.obj a) : F.map (f ≫ g) x = F.map g (F.map f x) := by
  rw [F.map_comp, ConcreteCategory.comp_apply]

open Stacks.Cohomology.RightDerivedBoundary (shortExactBoundary)
open Stacks.Cohomology.RealizationBoundary (toSC_mapPlus_shortExact)
open AlgebraicGeometry.SheafOfModules (sheafCohomologyOneIsoShiftedCohomologyTwo) in
/-- **The abelian boundary of the residue sequence is the de Rham first Chern class, from Čech
data.** Let `t` be a global section of the image of the degree-zero cycles of the residue
sequence, lifting on an open covering to local cocycles `eᵢ` of the middle term, and let `z` be a
Čech `1`-cocycle of `𝒪_X^*` whose image under `d log` is a cocycle `ω` of closed forms carried to
the differences of the lifts. If `z` represents the Picard class `p`, then the boundary map of the
residue sequence carries the class of `t` to `c₁^{dR}(p)`. -/
theorem Situation.abelianBoundary_eq_chernClass
    (p : Stacks.SheafOfModules.Picard.PicardGroup D.X.toRingedSpace.sheaf.obj
      (_root_.structureSheaf D.X.toRingedSpace.sheaf).property)
    (t : (HomologicalComplex.shortExactCycles
      (Stacks.Cohomology.RightDerivedBoundary.toSC D.residueAbelianSequence) 0).X₃.val.obj (op ⊤))
    {I : Type u} (Ui : I → Opens D.baseSpace.carrier)
    (hUi : (⊤ : Opens D.baseSpace.carrier) = ⨆ i, Ui i)
    (e : CechCochains.Cochain Ui (HomologicalComplex.shortExactCycles
      (Stacks.Cohomology.RightDerivedBoundary.toSC D.residueAbelianSequence) 0).X₂.val 0)
    (he : ∀ i : Fin 1 → I, (HomologicalComplex.shortExactCycles
        (Stacks.Cohomology.RightDerivedBoundary.toSC D.residueAbelianSequence) 0).g.hom.app
        (op (CechCochains.inter Ui i)) (e i) =
      (HomologicalComplex.shortExactCycles
        (Stacks.Cohomology.RightDerivedBoundary.toSC D.residueAbelianSequence) 0).X₃.val.map
        (homOfLE le_top).op t)
    (z : CechCochains.cocycles1 Ui D.unitsSheafBase.val)
    (ω : CechCochains.cocycles1 Ui (HomologicalComplex.shortExactCycles
      (Stacks.Cohomology.RightDerivedBoundary.toSC D.residueAbelianSequence) 0).X₁.val)
    (hωz : ∀ i : Fin 2 → I, ω.val i =
      D.logarithmicDifferentialClosed.hom.app (op (CechCochains.inter Ui i)) (z.val i))
    (hω : ∀ i : Fin 2 → I, (HomologicalComplex.shortExactCycles
        (Stacks.Cohomology.RightDerivedBoundary.toSC D.residueAbelianSequence) 0).f.hom.app
        (op (CechCochains.inter Ui i)) (ω.val i) =
      CechCochains.cechD Ui (HomologicalComplex.shortExactCycles
        (Stacks.Cohomology.RightDerivedBoundary.toSC D.residueAbelianSequence) 0).X₂.val 0 e i)
    (hz : Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections D.baseSpace.carrier ⊤ Ui hUi
        D.unitsSheafBase (CechCochains.cls Ui _ z) =
      (Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup D.X.toRingedSpace).symm p) :
    (shiftHomologyIso D.abelianSections D.deRhamPlus 1 1 2 (by omega)).hom
        ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 1).map
          (D.abelianSections.map D.residuePlusShiftHom)
          (shortExactBoundary (sectionsFunctor D.baseSpace.carrier ⊤) D.residueAbelianSequence
            (toSC_mapPlus_shortExact _ _ D.residuePlusSequence_shortExact) 0 1 rfl
            (Stacks.DerivedIndexing.imageCycleClass (sectionsFunctor D.baseSpace.carrier ⊤)
              D.residueAbelianSequence t))) =
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 2).map
        ((sectionsFunctor D.baseSpace.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map
            (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlusIso
              (Scheme.Hom.deRhamAlgebras D.f)
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential
                (Scheme.Hom.deRhamAlgebras D.f))).hom))
        (AlgebraicGeometry.SheafOfModules.deRhamFirstChernClassAbelian
          (Scheme.Hom.deRhamAlgebras D.f)
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))
          p) := by
  have h₁ := Stacks.Cohomology.CechOne.shortExactBoundary_imageCycleClass
    (S := D.residueAbelianSequence)
    (toSC_mapPlus_shortExact _ _ D.residuePlusSequence_shortExact) t Ui hUi e he ω hω
  have hnat := Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections_naturality.{u, u, u}
    _ ⊤ Ui hUi D.logarithmicDifferentialClosed z ω hωz
  rw [h₁]
  have hA := ConcreteCategory.congr_hom D.shiftHomologyIso_cyclesRightDerivedOneMap
    ((Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard
      (sectionsFunctor D.baseSpace.carrier ⊤) 1).inv.app D.closedForms
      (Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections D.baseSpace.carrier ⊤ Ui hUi
        D.closedForms (CechCochains.cls Ui _ ω)))
  rw [← D.closedFormsInclusion_eq_mkHomFromSingle] at hA
  refine hA.trans ?_
  erw [ConcreteCategory.comp_apply, ← sheafCohomologyOneIsoShiftedCohomologyTwo_hom_apply]
  rw [← hnat, hz]
  refine (D.logarithmicDifferentialComplexBase_homology
    ((Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup D.X.toRingedSpace).symm
      p)).symm.trans ?_
  rw [← D.logarithmicDifferentialComplexMapPlus_comp_iso]
  exact map_comp_apply_eq (DerivedCategory.Plus.Q ⋙
    (sectionsFunctor D.baseSpace.carrier ⊤).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 2) _ _ _

end Stacks.LineBundle

end
