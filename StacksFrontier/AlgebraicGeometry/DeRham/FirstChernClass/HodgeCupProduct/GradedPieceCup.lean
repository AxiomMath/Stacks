module

public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.HodgeCupProduct.AbelianShift

/-!
# The cup product on the graded pieces is the Hodge cup product

The module identification of a graded piece through the realization, the agreement of the
abelian and module identifications of a graded piece, the identification
`hodgeCohomologyIsoGradedPiece` of Hodge cohomology with the cohomology of the graded pieces,
the comparison of the cup product on the graded pieces with `hodgeCup` up to sign
(`hodgeCohomologyIsoGradedPiece_gradedPieceCup`), and additivity of `hodgeCup` in the second
variable (`hodgeCup_units_smul_right`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.Cohomology.Leray (AbelianSheaf sectionsFunctor)
open Stacks.SheafOfModules.Tensor (sheafTensor)

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
attribute [local instance] abelianModules hasSheafifyOpens wEqualsLocallyBijectiveOpens

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-! ### The module identification of a graded piece through the realization -/

section ModuleShift

open Stacks.Cohomology.GlobalKunneth Stacks.Cohomology.DerivedGlobalCupProduct

/-- The algebra of `gradedPieceModuleShiftIso_hom_eq`, with every object and morphism a
variable. -/
lemma moduleShift_paste {V : Type*} [Category* V] {P Q R S U : V} (t : P ⟶ Q) (b : Q ⟶ R)
    (Sc : R ⟶ U) (θ : P ⟶ S) (c : S ⟶ R) (Sh : S ⟶ U) (hθ : θ ≫ c = t ≫ b)
    (hS : Sh = c ≫ Sc) : t ≫ b ≫ Sc = θ ≫ Sh := by
  rw [hS, ← Category.assoc θ, hθ, Category.assoc]

/-- The algebra of the shift identification of a composite with the inclusion. -/
lemma shiftIncl_paste {V : Type*} [Category* V] {P Q R S U : V} (X₀ : P ⟶ R) (x : P ⟶ Q)
    (y : Q ⟶ R) (z : R ⟶ S) (w : S ⟶ U) (Y₀ : Q ⟶ S) (hX : X₀ = x ≫ y) (hY : Y₀ = y ≫ z) :
    X₀ ≫ z ≫ w = x ≫ (Y₀ ≫ w) := by
  rw [hX, hY]
  simp only [Category.assoc]

/-- `gradedPiecePlusShift` read in complexes and followed by the commutation of the inclusion with
the shift is `gradedPieceShiftIso` followed by the identification of the two shifts. -/
lemma gradedPiecePlusShift_comp (a : ℕ) :
    @CategoryStruct.comp (CochainComplex (_root_.SheafOfModules.{u}
      (structureSheafRing (baseRingedSpace A))) ℤ) _ _ _ _
      ((CochainComplex.Plus.ι (_root_.SheafOfModules.{u}
      (structureSheafRing (baseRingedSpace A)))).map (gradedPiecePlusShift B D a))
      (((CochainComplex.Plus.ι (_root_.SheafOfModules.{u}
      (structureSheafRing (baseRingedSpace A)))).commShiftIso (-(a : ℤ))).hom.app
      (moduleComplexPlus (X := X) (A := A) (hodgeSingle (X := X) (A := A) (φ := φ) B D a))) =
      @CategoryStruct.comp (CochainComplex (_root_.SheafOfModules.{u}
        (structureSheafRing (baseRingedSpace A))) ℤ) _ _ _ _ (gradedPieceShiftIso B D a).hom
        (shiftBridge (S := baseRingedSpace A)
        ((hodgeSingle (X := X) (A := A) (φ := φ) B D a).extend embeddingUpNat) (-(a : ℤ))).hom :=
  map_preimage_comp_hom (CochainComplex.Plus.ι
      (_root_.SheafOfModules.{u} (structureSheafRing (baseRingedSpace A)))) _ _ _ _
      (Iso.inv_hom_id_app _ _)

/-- **The module identification of a graded piece is the shift identification of the derived
global sections**, read through `gradedPiecePlusShift`. -/
theorem gradedPieceModuleShiftIso_hom_eq (a : ℕ) (n i : ℤ) (h : -(a : ℤ) + n = i) :
    (gradedPieceModuleShiftIso B D a n i h).hom =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (baseRingedSpace A))) n).map
        ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen (baseRingedSpace A) ⊤).map
        (DerivedCategory.Q.map ((CochainComplex.Plus.ι
        (_root_.SheafOfModules.{u} (structureSheafRing (baseRingedSpace A)))).map
        (gradedPiecePlusShift B D a)))) ≫
        (Stacks.Cohomology.RealizationShift.shiftHomologyIsoU
          (((CochainComplex.Plus.ι (_root_.SheafOfModules.{u}
          (structureSheafRing (baseRingedSpace A)))) ⋙ DerivedCategory.Q) ⋙
          Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen (baseRingedSpace A) ⊤)
          (moduleComplexPlus (X := X) (A := A) (hodgeSingle (X := X) (A := A) (φ := φ) B D a))
          (-(a : ℤ)) n i h).hom := by
  have hθ : (DerivedCategory.Q ⋙ (Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen
      (baseRingedSpace A) ⊤) ⋙ (DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (baseRingedSpace A))) n)).map
      ((CochainComplex.Plus.ι (_root_.SheafOfModules.{u}
      (structureSheafRing (baseRingedSpace A)))).map (gradedPiecePlusShift B D a)) ≫
      (DerivedCategory.Q ⋙ (Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen
      (baseRingedSpace A) ⊤) ⋙ (DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (baseRingedSpace A))) n)).map
      (((CochainComplex.Plus.ι (_root_.SheafOfModules.{u}
      (structureSheafRing (baseRingedSpace A)))).commShiftIso (-(a : ℤ))).hom.app
      (moduleComplexPlus (X := X) (A := A) (hodgeSingle (X := X) (A := A) (φ := φ) B D a))) =
      (DerivedCategory.Q ⋙ (Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen
        (baseRingedSpace A) ⊤) ⋙ (DerivedCategory.homologyFunctor
        (ModuleCat.{u} (baseRing (baseRingedSpace A))) n)).map (gradedPieceShiftIso B D a).hom ≫
        (DerivedCategory.Q ⋙ (Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen
        (baseRingedSpace A) ⊤) ⋙ (DerivedCategory.homologyFunctor
        (ModuleCat.{u} (baseRing (baseRingedSpace A))) n)).map
        (shiftBridge (S := baseRingedSpace A)
        ((hodgeSingle (X := X) (A := A) (φ := φ) B D a).extend embeddingUpNat) (-(a : ℤ))).hom :=
    ((DerivedCategory.Q ⋙ (Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen
      (baseRingedSpace A) ⊤) ⋙ (DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (baseRingedSpace A))) n)).map_comp _ _).symm.trans
      ((congrArg (DerivedCategory.Q ⋙
      (Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen (baseRingedSpace A) ⊤) ⋙
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (baseRingedSpace A))) n)).map
      (gradedPiecePlusShift_comp B D a)).trans
        ((DerivedCategory.Q ⋙ (Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen
        (baseRingedSpace A) ⊤) ⋙ (DerivedCategory.homologyFunctor
        (ModuleCat.{u} (baseRing (baseRingedSpace A))) n)).map_comp _ _))
  have hS := Stacks.Cohomology.RealizationShift.shiftHomologyIsoU_comp_hom
    ((CochainComplex.Plus.ι (_root_.SheafOfModules.{u} (structureSheafRing (baseRingedSpace A)))) ⋙
      DerivedCategory.Q) (Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen
      (baseRingedSpace A) ⊤) (moduleComplexPlus (X := X) (A := A)
      (hodgeSingle (X := X) (A := A) (φ := φ) B D a)) (-(a : ℤ)) n i h
  refine (gradedPieceModuleShiftIso_hom B D a n i h).trans ?_
  refine moduleShift_paste _ _ _ _ _ _ hθ (hS.trans (shiftIncl_paste _ _ _ _ _ _ ?_
    (Functor.map_comp _ _ _)))
  exact (congrArg ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen
      (baseRingedSpace A) ⊤) ⋙ (DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (baseRingedSpace A))) n)).map
    (Functor.commShiftIso_comp_hom_app (CochainComplex.Plus.ι
      (_root_.SheafOfModules.{u} (structureSheafRing (baseRingedSpace A)))) DerivedCategory.Q
      (-(a : ℤ)) (moduleComplexPlus (X := X) (A := A)
      (hodgeSingle (X := X) (A := A) (φ := φ) B D a)))).trans
    (((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen (baseRingedSpace A) ⊤) ⋙
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (baseRingedSpace A)))
      n)).map_comp _ _)

end ModuleShift

/-! ### The abelian and the module identifications of a graded piece agree -/

section Agree

open Stacks.Cohomology.GlobalKunneth

/-- The algebra of `gradedPieceCohomologyIso_shift`, with every object and morphism a variable. -/
lemma agree_paste {V : Type*} [Category* V] {P Q R S S₀ S₁ U Vt Z₁ Z₂ Z₃ W₁ : V}
    (g : P ⟶ Q) (sF : Q ⟶ S) (ci : Q ⟶ R) (sx : R ⟶ S) (p₀ : S ⟶ S₀) (p₁ : S₀ ⟶ S₁)
    (p₂ : S₁ ⟶ U) (Pφ : S ⟶ U) (MS : S₀ ⟶ Vt) (rS : U ⟶ Vt) (m : P ⟶ Z₁) (tθ : Z₁ ⟶ Z₂)
    (sf : Z₂ ⟶ U) (rT : Z₂ ⟶ W₁) (fs : W₁ ⟶ Vt) (rG : Z₁ ⟶ Z₃) (fθ : Z₃ ⟶ W₁) (MG : P ⟶ Z₃)
    (Fρ : Z₃ ⟶ Vt) (hsF : sF = ci ≫ sx) (hφ : Pφ = p₀ ≫ p₁ ≫ p₂)
    (hA : g ≫ (ci ≫ sx) ≫ Pφ = m ≫ tθ ≫ sf) (hshift : rT ≫ fs = sf ≫ rS)
    (hnat : tθ ≫ rT = rG ≫ fθ) (hMS : MS = p₁ ≫ p₂ ≫ rS) (hMG : MG = m ≫ rG)
    (hρ : Fρ = fθ ≫ fs) : g ≫ sF ≫ p₀ ≫ MS = MG ≫ Fρ := by
  have hA' : g ≫ (ci ≫ sx) ≫ p₀ ≫ p₁ ≫ p₂ = m ≫ tθ ≫ sf := by rw [← hφ, hA]
  rw [hsF, hMS, hMG, hρ]
  calc g ≫ (ci ≫ sx) ≫ p₀ ≫ p₁ ≫ p₂ ≫ rS = (g ≫ (ci ≫ sx) ≫ p₀ ≫ p₁ ≫ p₂) ≫ rS := by
        simp only [Category.assoc]
    _ = (m ≫ rG) ≫ fθ ≫ fs := by
        rw [hA', Category.assoc, Category.assoc, ← hshift, ← Category.assoc tθ, hnat]
        simp only [Category.assoc]

/-- **The abelian and the module identifications `H^{i + a}(X, Ω^a[-a]) ≅ H^i(X, Ω^a[0])` agree**
through the realization comparison `moduleHypercohomologyIso` of Tag 01F1: the abelian one is
`DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso`, the module one
`gradedPieceModuleShiftIso`, built from the shift identification of cohomology modules. -/
theorem gradedPieceCohomologyIso_shift (a : ℕ) (i : ℤ) :
    (gradedPieceCohomologyIso B D a (i + a)).hom ≫
        ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso
          (sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus i (a : ℤ)).app
          ((deRhamAbelianComplexInt B D).X (a : ℤ))).hom ≫
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} i).map
          ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map
          ((Stacks.DerivedIndexing.singlePlusFunctor (AbelianSheaf X.carrier) 0).map
            (deRhamAbelianIntXIsoNat B D a).hom))) ≫
        ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} i).map
          ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map (hodgeSinglePlusIso B D a).hom)) ≫
          (moduleHypercohomologyIso (hodgeSingle B D a) i).hom) =
      (moduleHypercohomologyIso (deRhamGradedPiece B D a) (i + a)).hom ≫
        (forget₂ (ModuleCat.{u} (baseRing (baseRingedSpace A))) AddCommGrpCat.{u}).map
          (gradedPieceModuleShiftIso B D a (i + a) i (by omega)).hom :=
  agree_paste _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (singleFunctorCompHomologyFunctorShiftIso_app_hom
      (sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus i (a : ℤ)
      ((deRhamAbelianComplexInt B D).X (a : ℤ)))
    ((((DerivedCategory.Plus.Q ⋙ (sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus) ⋙
      DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} i).map_comp _ _).trans
      (congrArg (_ ≫ ·) (((DerivedCategory.Plus.Q ⋙
      (sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus) ⋙
      DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} i).map_comp _ _)))
    (gradedPiece_shift_abelian B D a i)
    (Stacks.Cohomology.RealizationShift.realizationIsoAt_shift (baseRingedSpace A)
      (moduleComplexPlus (X := X) (A := A) (hodgeSingle (X := X) (A := A) (φ := φ) B D a))
      (-(a : ℤ)) (i + a) i (by omega))
    (Stacks.Cohomology.RealizationShift.realizationIsoAt_naturality (baseRingedSpace A)
      (gradedPiecePlusShift B D a) (i + a))
    rfl rfl
    ((congrArg (forget₂ (ModuleCat.{u} (baseRing (baseRingedSpace A))) AddCommGrpCat.{u}).map
      (gradedPieceModuleShiftIso_hom_eq B D a (i + a) i (by omega))).trans
      ((forget₂ (ModuleCat.{u} (baseRing (baseRingedSpace A))) AddCommGrpCat.{u}).map_comp _ _))

end Agree

/-! ### Hodge cohomology and the graded pieces -/

section HodgeGraded

open Stacks.Cohomology.GlobalKunneth

/-- **`H^i(X, Ω^a) ≅ H^{i + a}(X, Ω^a[-a])`**: the degree-`i` cohomology of `Ω^a` is the
degree-`(i + a)` hypercohomology of `Ω^a` placed in degree `a`, through the comparison
`Stacks.DerivedIndexing.rightDerivedIso` of the two indexings of the right derived functors and
`DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso`. For `i = a` this is
`AlgebraicGeometry.SheafOfModules.gradedPieceCohomologyIsoHodgeCohomology`. The degree is a
parameter constrained by `hn`, so that it can be read off a sum. -/
def hodgeCohomologyIsoGradedPiece (a i : ℕ) (n : ℤ) (hn : (i : ℤ) + (a : ℤ) = n) :
    ((sectionsFunctor X.carrier ⊤).rightDerived i).obj ((deRhamAbelianComplex B D).X a) ≅
      gradedPieceCohomology B D (a : ℤ) n := by
  subst hn
  exact ((sectionsFunctor X.carrier ⊤).rightDerived i).mapIso
      (deRhamAbelianIntXIsoNat B D a).symm ≪≫
    (Stacks.DerivedIndexing.rightDerivedIso (sectionsFunctor X.carrier ⊤) i).app _ ≪≫
    ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso
      (sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus (i : ℤ) (a : ℤ)).app
      ((deRhamAbelianComplexInt B D).X (a : ℤ))).symm

/-- The algebra of `hodgeCohomologyIsoGradedPiece_inv_comp`. -/
lemma invComp_paste {V : Type*} [Category* V] {P Q R S T U : V} (s : P ⟶ Q) (i' : Q ⟶ R)
    (m : R ⟶ S) (h' : S ⟶ T) (E : T ⟶ U) (h'' : R ⟶ Q) (p : Q ⟶ T) (hm : m ≫ h' = h'' ≫ p)
    (hi : i' ≫ h'' = 𝟙 Q) : s ≫ (i' ≫ m) ≫ (h' ≫ E) = s ≫ p ≫ E := by
  rw [Category.assoc, ← Category.assoc m, hm, Category.assoc, ← Category.assoc i', hi,
    Category.id_comp]

/-- The inverse of `hodgeCohomologyIsoGradedPiece`, followed by `hodgeSingleCohomologyIso`. -/
lemma hodgeCohomologyIsoGradedPiece_inv_comp (a i : ℕ) :
    (hodgeCohomologyIsoGradedPiece B D a i ((i : ℤ) + (a : ℤ)) rfl).inv ≫
        (hodgeSingleCohomologyIso B D a i (i : ℤ) rfl).hom =
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso
        (sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus (i : ℤ) (a : ℤ)).app
          ((deRhamAbelianComplexInt B D).X (a : ℤ))).hom ≫
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (i : ℤ)).map
          ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map
          ((Stacks.DerivedIndexing.singlePlusFunctor (AbelianSheaf X.carrier) 0).map
            (deRhamAbelianIntXIsoNat B D a).hom))) ≫
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (i : ℤ)).map
          ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map (hodgeSinglePlusIso B D a).hom)) := by
  have e := (Stacks.DerivedIndexing.rightDerivedIso (sectionsFunctor X.carrier ⊤) i).hom.naturality
    (deRhamAbelianIntXIsoNat B D a).hom
  show (((DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso
      (sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus (i : ℤ)
      (a : ℤ)).app ((deRhamAbelianComplexInt B D).X (a : ℤ))).hom ≫
      ((Stacks.DerivedIndexing.rightDerivedIso (sectionsFunctor X.carrier ⊤) i).inv.app _ ≫
        ((sectionsFunctor X.carrier ⊤).rightDerived i).map (deRhamAbelianIntXIsoNat B D a).hom)) ≫
      ((Stacks.DerivedIndexing.rightDerivedIso (sectionsFunctor X.carrier ⊤) i).hom.app _ ≫ _) = _
  exact invComp_paste _ _ _ _ _ _ _ e (Iso.inv_hom_id_app _ _)

/-- The algebra of `hodgeSingleCohomologyIso_gradedPieceCohomologyIso`. -/
lemma keyK_paste {V : Type*} [Category* V] {P Q R S T U W Z : V} (g : P ⟶ Q) (ιi : Q ⟶ R)
    (E : R ⟶ U) (sF : Q ⟶ S) (s₀ : S ⟶ T) (sH : T ⟶ U) (M : U ⟶ W) (MG : P ⟶ Z) (Fρ : Z ⟶ W)
    (e₂ : ιi ≫ E = sF ≫ s₀ ≫ sH) (C : g ≫ sF ≫ s₀ ≫ (sH ≫ M) = MG ≫ Fρ) :
    g ≫ ιi ≫ E ≫ M = MG ≫ Fρ := by
  rw [← C, ← Category.assoc ιi, e₂]
  simp only [Category.assoc]

/-- **The abelian and the module readings of Hodge cohomology agree on the graded pieces**: a
class of `H^N(X, Ω^a[-a])`, moved to `H^I(X, Ω^a)` by `hodgeCohomologyIsoGradedPiece` and read
in modules by `hodgeSingleCohomologyIso` and `moduleHypercohomologyIso`, is the class moved by
`gradedPieceModuleShiftIso` on cohomology modules. -/
theorem hodgeSingleCohomologyIso_gradedPieceCohomologyIso (a i : ℕ) (I N : ℤ) (hI : (i : ℤ) = I)
    (hN : I + (a : ℤ) = N) (t : moduleHypercohomology (A := A) (deRhamGradedPiece B D a) N) :
    (moduleHypercohomologyIso (hodgeSingle B D a) I).hom.hom
        ((hodgeSingleCohomologyIso B D a i I hI).hom.hom
          ((hodgeCohomologyIsoGradedPiece B D a i N (by omega)).inv.hom
            ((gradedPieceCohomologyIso B D a N).hom.hom t))) =
      (gradedPieceModuleShiftIso B D a N I (by omega)).hom.hom
        ((moduleHypercohomologyIso (deRhamGradedPiece B D a) N).hom.hom t) := by
  subst hI hN
  have key := keyK_paste _ _ _ _ _ _ _ _ _ (hodgeCohomologyIsoGradedPiece_inv_comp B D a i)
    (gradedPieceCohomologyIso_shift B D a (i : ℤ))
  exact ConcreteCategory.congr_hom key t

end HodgeGraded

/-! ### The cup product on the graded pieces is the Hodge cup product, up to sign -/

section GradedPieceCup

open Stacks.Cohomology.GlobalKunneth

/-- The inverse of an isomorphism of abelian groups undoes its forward map on elements. -/
private lemma iso_inv_hom_apply_eq {P Q : AddCommGrpCat.{u}} (e : P ≅ Q) (x : P) :
    ConcreteCategory.hom e.inv (ConcreteCategory.hom e.hom x) = x :=
  ConcreteCategory.congr_hom e.hom_inv_id x

/-- An isomorphism of abelian groups is injective on elements. -/
lemma eq_of_iso_hom_apply_eq {P Q : AddCommGrpCat.{u}} (e : P ≅ Q) {x y : P}
    (h : e.hom.hom x = e.hom.hom y) : x = y :=
  (iso_inv_hom_apply_eq e x).symm.trans ((congrArg e.inv.hom h).trans (iso_inv_hom_apply_eq e y))

/-- The forward map of an isomorphism of abelian groups undoes its inverse on elements. -/
lemma iso_hom_inv_apply_eq {P Q : AddCommGrpCat.{u}} (e : P ≅ Q) (x : Q) :
    ConcreteCategory.hom e.hom (ConcreteCategory.hom e.inv x) = x :=
  ConcreteCategory.congr_hom e.inv_hom_id x

/-- **The cup product on the graded pieces of the Hodge filtration is the cup product on Hodge
cohomology of Tag 0FM4, up to the sign `(-1)^{{ib}}`**: for `x ∈ H^{{i + a}}(X, Ω^a[-a])` and
`y ∈ H^{{j + b}}(X, Ω^b[-b])`, read in `H^i(X, Ω^a)` and `H^j(X, Ω^b)` through
`hodgeCohomologyIsoGradedPiece`,

`∪(x, y) = (-1)^{{ib}} · (x ∪_{{Hodge}} y)` in `H^{{i + j}}(X, Ω^{{a + b}})`.

The sign is that of moving the shift `[-b]` of the second factor past the class of degree `i` of
the first (`totalCupPairing_shift₂`). -/
theorem hodgeCohomologyIsoGradedPiece_gradedPieceCup (a b i j : ℕ) (n m : ℤ)
    (hn : (i : ℤ) + (a : ℤ) = n) (hm : (j : ℤ) + (b : ℤ) = m)
    (x : gradedPieceCohomology B D (a : ℤ) n) (y : gradedPieceCohomology B D (b : ℤ) m) :
    (hodgeCohomologyIsoGradedPiece B D (a + b) (i + j) (n + m) (by push_cast; omega)).inv.hom
        (TruncationCupProduct.cupGradedPiece B D truncationCupProduct a b (a : ℤ)
          (b : ℤ) rfl rfl n m
          x y) =
      ((i : ℤ) * (b : ℤ)).negOnePow • hodgeCup B D a b (a + b) rfl i j (i + j) rfl
        ((hodgeCohomologyIsoGradedPiece B D a i n hn).inv.hom x)
        ((hodgeCohomologyIsoGradedPiece B D b j m hm).inv.hom y) := by
  subst hn hm
  obtain ⟨z, rfl⟩ : ∃ z, (gradedPieceCohomologyIso B D a ((i : ℤ) + (a : ℤ))).hom.hom z = x :=
    ⟨_, iso_hom_inv_apply_eq _ x⟩
  obtain ⟨w, rfl⟩ : ∃ w, (gradedPieceCohomologyIso B D b ((j : ℤ) + (b : ℤ))).hom.hom w = y :=
    ⟨_, iso_hom_inv_apply_eq _ y⟩
  have hzw := TruncationCupProduct.cupGradedPiece_natCast B D truncationCupProduct a b
    ((i : ℤ) + (a : ℤ)) ((j : ℤ) + (b : ℤ)) ((gradedPieceCohomologyIso B D a _).hom.hom z)
    ((gradedPieceCohomologyIso B D b _).hom.hom w)
  rw [iso_inv_hom_apply_eq, iso_inv_hom_apply_eq] at hzw
  rw [hzw]
  refine eq_of_iso_hom_apply_eq ((hodgeSingleCohomologyIso B D (a + b) (i + j) ((i : ℤ) + (j : ℤ))
    (by push_cast; rfl)) ≪≫ moduleHypercohomologyIso (hodgeSingle B D (a + b))
      ((i : ℤ) + (j : ℤ))) ?_
  simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
  have kL := hodgeSingleCohomologyIso_gradedPieceCohomologyIso B D (a + b) (i + j)
    ((i : ℤ) + (j : ℤ)) (((i : ℤ) + (a : ℤ)) + ((j : ℤ) + (b : ℤ))) (by push_cast; rfl)
    (by push_cast; ring)
    (canonicalPairing (gradedPieceWedge B D a b) ((i : ℤ) + (a : ℤ)) ((j : ℤ) + (b : ℤ)) z w)
  refine kL.trans ?_
  have hL : (moduleHypercohomologyIso (deRhamGradedPiece B D (a + b))
      (((i : ℤ) + (a : ℤ)) + ((j : ℤ) + (b : ℤ)))).hom.hom
      (canonicalPairing (gradedPieceWedge B D a b) ((i : ℤ) + (a : ℤ)) ((j : ℤ) + (b : ℤ)) z w) =
      (canonicalPairingModule (gradedPieceWedge B D a b) ((i : ℤ) + (a : ℤ))
        ((j : ℤ) + (b : ℤ))).hom
        ((moduleHypercohomologyIso (deRhamGradedPiece B D a) _).hom.hom z ⊗ₜ
          (moduleHypercohomologyIso (deRhamGradedPiece B D b) _).hom.hom w) :=
    ConcreteCategory.congr_hom (moduleHypercohomologyIso (deRhamGradedPiece B D (a + b))
      _).inv_hom_id _
  rw [hL, canonicalPairingModule_gradedPieceWedge_apply B D a b _ _ (i : ℤ) (j : ℤ) (by omega)
    (by omega)]
  have kz := hodgeSingleCohomologyIso_gradedPieceCohomologyIso B D a i (i : ℤ) ((i : ℤ) + (a : ℤ))
    rfl rfl z
  have kw := hodgeSingleCohomologyIso_gradedPieceCohomologyIso B D b j (j : ℤ) ((j : ℤ) + (b : ℤ))
    rfl rfl w
  rw [← kz, ← kw]
  have hsm : ∀ {P Q : AddCommGrpCat.{u}} (f : P ⟶ Q) (e : ℤˣ) (v : P),
      ConcreteCategory.hom f (e • v) = e • ConcreteCategory.hom f v := fun f e v => by
    rw [Units.smul_def, Units.smul_def, map_zsmul]
  rw [hsm, hsm, mul_neg, Int.negOnePow_neg]
  refine congrArg (((i : ℤ) * (b : ℤ)).negOnePow • ·) ?_
  rw [hodgeCup_eq, iso_hom_inv_apply_eq]
  unfold canonicalPairing
  rw [iso_hom_inv_apply_eq]

end GradedPieceCup

/-! ### The Hodge cup product is additive in the second variable -/

section HodgeCupSmul

open Stacks.Cohomology.GlobalKunneth

/-- **The Hodge cup product commutes with signs in the second variable.** -/
theorem hodgeCup_units_smul_right (p q r : ℕ) (hr : p + q = r) (i j l : ℕ) (hl : i + j = l)
    (x : ((sectionsFunctor X.carrier ⊤).rightDerived i).obj ((deRhamAbelianComplex B D).X p))
    (e : ℤˣ)
    (y : ((sectionsFunctor X.carrier ⊤).rightDerived j).obj ((deRhamAbelianComplex B D).X q)) :
    hodgeCup B D p q r hr i j l hl x (e • y) = e • hodgeCup B D p q r hr i j l hl x y := by
  subst hr hl
  rw [hodgeCup_eq, hodgeCup_eq]
  unfold canonicalPairing
  simp only [Units.smul_def, map_zsmul, TensorProduct.tmul_smul]

end HodgeCupSmul

end AlgebraicGeometry.SheafOfModules

end
