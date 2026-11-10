module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologyDerivedSingleIsoNaturality
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.CanonicalCupProduct
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.DeRham.Cohomology.DegreeZeroCupProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.DerivedSectionsModelComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAndResolutions.KInjectiveRestriction

/-!
# The cohomology groups `H^q(X, F)` as the modules of the cup product of Section 0FKU

The Hodge and Gysin maps of this library are stated on the cohomology groups `Hgroup` of sheaves
of modules on a ringed space `X`, while the cup product of Cohomology, Section 0FKU
(`AlgebraicGeometry.SheafOfModules.canonicalPairingModule`) is stated on the cohomology modules
of the derived global sections over the base ring. This file builds the bridge between the two.

## Main definitions

* `singleTensorMult`: the multiplication `Tot(F[-a] ⊗ G[-b]) ⟶ H[-n]` of complexes induced by a
  multiplication of sheaves `F ⊗ G ⟶ H`, for `a + b = n`.
* `hgroupModuleShiftIso F c q m`: the bridge `H^q(X, F) ≅ H^m(RΓ(X, F[-c]))` for `q + c = m`. It
  uses the sign-free identification of the cohomology of a shift.
* `rightMulTensor`, `sectionClass`, `moduleDerivedMap`: right multiplication by a global section,
  the degree-zero class of a global section, and the action of a morphism of the derived
  category through the bridge.
* `EdgeTensorMatching`: the compatibility of two multiplications with two Gysin edge morphisms.

## Main results

* `hgroupModuleShiftIso_cohomologyMapOfSingleHom`: the bridge carries the map on cohomology of a
  morphism `A[-c] ⟶ F[0]` to the action of that morphism.
* `hgroupModuleShiftIso_naturality`: the bridge is natural in the sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.DeRham.CohomologicalGysin
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.Cohomology.GlobalKunneth (baseSections baseRing)
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule)
open AlgebraicGeometry.SheafOfModules (moduleDerived canonicalPairingModule tensorBifunctorNat
  baseRingedSpace multiplicationInt)

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose structureSheafRing
  AlgebraicGeometry.SheafedSpace.sheaf AlgebraicGeometry.SheafOfModules.baseRingedSpace
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.DeRham.GysinCupHodge

open DerivedCategory

/-- Cancelling an isomorphism at the front of a composite. -/
private lemma inv_hom_comp_eq {C : Type*} [Category* C] {P Q R : C} (e : P ≅ Q) (f : Q ⟶ R) :
    e.inv ≫ e.hom ≫ f = f := by
  simp

/-- Two composites through isomorphisms agree when the squares `φ ≫ hF = hA ≫ ψ` and
`fA ≫ g = ψ ≫ fF` commute. -/
private lemma bridge_chase {C : Type*} [Category* C] {P₀ P₁ P₂ P₃ P₄ P₅ P₆ P₇ : C}
    (i : P₁ ≅ P₀) (φ : P₁ ⟶ P₂) (j j' : P₂ ≅ P₃) (hj : j = j') (hF : P₂ ⟶ P₄) (fF : P₄ ⟶ P₅)
    (hA : P₁ ⟶ P₆) (fA : P₆ ⟶ P₇) (g : P₇ ⟶ P₅) (ψ : P₆ ⟶ P₄)
    (hN : φ ≫ hF = hA ≫ ψ) (hg : fA ≫ g = ψ ≫ fF) :
    (i.inv ≫ φ ≫ j.hom) ≫ j'.inv ≫ hF ≫ fF = (i.inv ≫ hA ≫ fA) ≫ g := by
  subst hj
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% hN, hg]

/-- Two composites through isomorphisms agree when the three squares `hN₀`, `hN` and `hg`
commute. -/
private lemma naturality_chase {C : Type*} [Category* C] {P₀ P₁ P₀' P₁' P₂ P₂' P₃ P₃' : C}
    (i : P₁ ≅ P₀) (i' : P₁' ≅ P₀') (a : P₀ ⟶ P₀') (b : P₁ ⟶ P₁') (hF : P₁ ⟶ P₂) (hF' : P₁' ⟶ P₂')
    (f : P₂ ⟶ P₃) (f' : P₂' ⟶ P₃') (g : P₂ ⟶ P₂') (k : P₃ ⟶ P₃')
    (hN₀ : b ≫ i'.hom = i.hom ≫ a) (hN : b ≫ hF' = hF ≫ g) (hg : f ≫ k = g ≫ f') :
    a ≫ i'.inv ≫ hF' ≫ f' = (i.inv ≫ hF ≫ f) ≫ k := by
  have h₁ : a ≫ i'.inv = i.inv ≫ b := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hN₀, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [reassoc_of% h₁, reassoc_of% hN, ← hg]
  simp only [Category.assoc]

section StandardModel

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules
  AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens

variable {X : RingedSpace.{u, u}}

/-- A sheaf of `𝒪_X`-modules placed in degree `n` of an `ℕ`-indexed complex, read over the ring
sheaf the cup product of Section 0FKU is formed over. -/
abbrev singleNat
    (F : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf))
    (n : ℕ) :
    CochainComplex
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)) ℕ :=
  (HomologicalComplex.single _ (ComplexShape.up ℕ) n).obj F

/-- The total tensor complex of two sheaves placed in degrees `a` and `b` vanishes outside the
degree `a + b`. -/
lemma isZero_singleNatTensor_X
    (F G : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf))
    (a b n : ℕ) (hn : n ≠ a + b) :
    IsZero
      ((((tensorBifunctorNat (A := X.sheaf)).obj (singleNat F a)).obj (singleNat G b)).X n) := by
  change IsZero ((HomologicalComplex.mapBifunctor (singleNat F a) (singleNat G b)
    (sheafTensor.{u, u, u, u, u} X.sheaf) (ComplexShape.up ℕ)).X n)
  refine HomologicalComplex₂.isZero_total_X_of_isZero _ _ n fun a' b' hab => ?_
  have hab' : a' + b' = n := hab
  change IsZero (((sheafTensor.{u, u, u, u, u} X.sheaf).obj ((singleNat F a).X a')).obj
    ((singleNat G b).X b'))
  by_cases ha : a' = a
  · exact AlgebraicGeometry.SheafOfModules.isZero_tensorFunctor_obj_obj_of_right _
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) b _ b' (by omega))
  · exact AlgebraicGeometry.SheafOfModules.isZero_tensorFunctor_obj_obj_of_left
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) a _ a' ha) _

/-- The component on the `(a', b')` summand of a multiplication of two sheaves placed in degrees
`a` and `b`: zero unless `a' = a` and `b' = b`, where it is `μ`. -/
def singleTensorMultSummand
    {F G H : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)}
    (μ : ((sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj G ⟶ H) (a b : ℕ) (a' b' : ℕ) :
    ((sheafTensor.{u, u, u, u, u} X.sheaf).obj ((singleNat F a).X a')).obj
        ((singleNat G b).X b') ⟶ H :=
  if h : a' = a ∧ b' = b then
    ((sheafTensor.{u, u, u, u, u} X.sheaf).obj ((singleNat F a).X a')).map
        (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℕ) b G b' h.2).hom ≫
      ((sheafTensor.{u, u, u, u, u} X.sheaf).map
          (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℕ) a F a' h.1).hom).app G ≫ μ
  else 0

/-- **The multiplication `Tot(F[-a] ⊗ G[-b]) ⟶ H[-n]` of `ℕ`-indexed complexes induced by a
morphism `μ : F ⊗ G ⟶ H`**, for `a + b = n`: the sheaves are placed in single degrees, so the
total complex is `F ⊗ G` in degree `n` and zero elsewhere, and the multiplication is `μ` there,
with no sign. -/
def singleTensorMult
    {F G H : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)}
    (μ : ((sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj G ⟶ H) (a b n : ℕ) (hn : a + b = n) :
    ((tensorBifunctorNat (A := X.sheaf)).obj (singleNat F a)).obj (singleNat G b) ⟶ singleNat H n :=
  HomologicalComplex.mkHomToSingle
    (HomologicalComplex.mapBifunctorDesc fun a' b' _ => singleTensorMultSummand μ a b a' b')
    fun i hi => by
      have hi' : i + 1 = n := hi
      exact (isZero_singleNatTensor_X F G a b i (by omega)).eq_of_src _ _

/-- Sections over the whole space, read as abelian groups, is the cohomological functor `secF`. -/
def sectionsForgetIso (X : RingedSpace.{u, u}) :
    Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen X ⊤ ⋙
        forget₂ (ModuleCat.{u} (baseRing X)) AddCommGrpCat.{u} ≅
      secF (structureSheafRing X) (⊤ : Opens X.carrier) :=
  Iso.refl _

/-- The unit of `RΓ(X, -)` over the base ring, read in abelian groups. -/
def forgetUnit (X : RingedSpace.{u, u}) :
    Stacks.DerivedFunctor.homotopyMap (secF (structureSheafRing X) (⊤ : Opens X.carrier)) ⟶
      DerivedCategory.Qh ⋙ (baseSections X ⋙
        (forget₂ (ModuleCat.{u} (baseRing X)) AddCommGrpCat.{u}).mapDerivedCategory) :=
  Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso (sectionsForgetIso X)
      (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _
      (forget₂ (ModuleCat.{u} (baseRing X)) AddCommGrpCat.{u}).mapDerivedCategoryFactorsh.inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpenUnit X ⊤)
      (forget₂ (ModuleCat.{u} (baseRing X)) AddCommGrpCat.{u}).mapDerivedCategory ≫
    (Functor.associator _ _ _).hom

/-- The comparison from derived global sections in abelian groups. -/
def derivedGlobalSectionsForget (X : RingedSpace.{u, u}) :
    derivedGlobalSections X ⟶
      baseSections X ⋙
        (forget₂ (ModuleCat.{u} (baseRing X)) AddCommGrpCat.{u}).mapDerivedCategory :=
  Functor.rightDerivedDesc (derivedGlobalSections X) (derivedGlobalSectionsUnit X)
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) _ (forgetUnit X)

/-- The unit of derived global sections followed by `derivedGlobalSectionsForget` is
`forgetUnit`. -/
theorem derivedGlobalSectionsForget_fac_app (X : RingedSpace.{u, u})
    (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (derivedGlobalSectionsUnit X).app K ≫
        (derivedGlobalSectionsForget X).app (DerivedCategory.Qh.obj K) = (forgetUnit X).app K :=
  Functor.rightDerived_fac_app _ _ _ _ _ K

/-- The component of `forgetUnit` at a K-injective complex is an isomorphism. -/
theorem isIso_forgetUnit_app (X : RingedSpace.{u, u})
    (I : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (hI : I.IsKInjective) :
    IsIso ((forgetUnit X).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) := by
  have :=
    Stacks.Cohomology.DerivedSectionsModels.isIso_derivedSectionsOverOpenUnit_app_of_isKInjective
      X ⊤ I hI
  simp only [forgetUnit, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp]
  infer_instance

/-- The comparison `derivedGlobalSectionsForget` is an isomorphism. -/
instance isIso_derivedGlobalSectionsForget (X : RingedSpace.{u, u}) :
    IsIso (derivedGlobalSectionsForget X) := by
  refine Stacks.Cohomology.isIso_of_isIso_on_kInjectives
    (exists_isKInjective_quasiIso_moduleSheaves X) _ fun I hI => ?_
  have h1 : IsIso ((derivedGlobalSectionsUnit X).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) := by
    have := hI
    exact Stacks.DerivedFunctor.isIso_totalRightDerivedUnit_app_of_isKInjective _ I
  have h2 := isIso_forgetUnit_app X I hI
  rw [← derivedGlobalSectionsForget_fac_app] at h2
  exact IsIso.of_isIso_comp_left ((derivedGlobalSectionsUnit X).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) _

/-- **Derived global sections in abelian groups are derived global sections over the base ring,
read in abelian groups.** -/
def derivedGlobalSectionsForgetIso (X : RingedSpace.{u, u}) :
    derivedGlobalSections X ≅
      baseSections X ⋙
        (forget₂ (ModuleCat.{u} (baseRing X)) AddCommGrpCat.{u}).mapDerivedCategory :=
  asIso (derivedGlobalSectionsForget X)

/-- A sheaf placed in degree `c` of an `ℕ`-indexed complex, extended by zero and read in the
derived category, is the sheaf placed in degree `c`. -/
def moduleDerivedSingleIso (F : _root_.SheafOfModules.{u} (structureSheafRing X)) (c : ℕ) :
    moduleDerived (A := X.sheaf) (singleNat F c) ≅
      (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) (c : ℤ)).obj F :=
  DerivedCategory.Q.mapIso (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F c
    (c : ℤ) rfl)

/-- The degree-`m` cohomology of derived global sections in abelian groups is the degree-`m`
cohomology of derived global sections over the base ring, read in abelian groups, naturally in
the complex. -/
def homologyForgetIso (X : RingedSpace.{u, u}) (m : ℤ)
    (K : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X))) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).obj ((derivedGlobalSections X).obj K) ≅
      (forget₂ (ModuleCat.{u} (baseRing X)) AddCommGrpCat.{u}).obj (cohomologyModule K m) :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).mapIso
      ((derivedGlobalSectionsForgetIso X).app K) ≪≫
    ((forget₂ (ModuleCat.{u} (baseRing X)) AddCommGrpCat.{u}).mapDerivedCategoryHomologyIso
      m).app ((baseSections X).obj K)

/-- The isomorphism `homologyForgetIso` is natural in the complex. -/
theorem homologyForgetIso_hom_naturality (X : RingedSpace.{u, u}) (m : ℤ)
    {K L : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X))} (φ : K ⟶ L) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).map ((derivedGlobalSections X).map φ) ≫
        (homologyForgetIso X m L).hom =
      (homologyForgetIso X m K).hom ≫
        (forget₂ (ModuleCat.{u} (baseRing X)) AddCommGrpCat.{u}).map
          ((DerivedCategory.homologyFunctor _ m).map ((baseSections X).map φ)) := by
  have h₁ := (derivedGlobalSectionsForgetIso X).hom.naturality φ
  have h₂ := ((forget₂ (ModuleCat.{u} (baseRing X)) AddCommGrpCat.{u}).mapDerivedCategoryHomologyIso
      m).hom.naturality
    ((baseSections X).map φ)
  dsimp only [Functor.comp_map, Functor.comp_obj] at h₁ h₂
  simp only [homologyForgetIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  rw [← Category.assoc, ← Functor.map_comp, h₁, Functor.map_comp, Category.assoc, h₂,
    Category.assoc]

/-- **The bridge** between the cohomology group `H^q(X, F)` and the module
`H^m(RΓ(X, F[-c]))` the cup product of Section 0FKU is stated on, for `q + c = m`. -/
def hgroupModuleShiftIso (F : _root_.SheafOfModules.{u} (structureSheafRing X)) (c q : ℕ)
    (m : ℤ) (h : (q : ℤ) + (c : ℤ) = m) :
    Hgroup (structureSheafRing X) ⊤ q F ≅
      (forget₂ (ModuleCat.{u} (baseRing X)) AddCommGrpCat.{u}).obj
        (cohomologyModule (moduleDerived (A := X.sheaf) (singleNat F c)) m) :=
  (cohomologyDerivedSingleIso X F (c : ℤ) m q (by omega)).symm ≪≫
    homologyForgetIso X m _ ≪≫
    (forget₂ (ModuleCat.{u} (baseRing X)) AddCommGrpCat.{u}).mapIso
      ((DerivedCategory.homologyFunctor _ m).mapIso
        ((baseSections (baseRingedSpace X.sheaf)).mapIso (moduleDerivedSingleIso F c).symm))

/-! ### The bridge on maps -/

/-- The bilinear map of sections underlying a morphism out of a tensor product sheaf. -/
def tensorBilinear
    {F G H : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)}
    (μ : ((sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj G ⟶ H) :
    Stacks.BilinearMap F.val G.val H.val :=
  PresheafOfModules.toBilinear (PresheafOfModules.tensorSheafUnit F G ≫ μ.val)

/-- Right multiplication by a global section of the second factor, along a morphism out of a
tensor product sheaf. -/
def rightMulTensor
    {F G H : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)}
    (μ : ((sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj G ⟶ H) (u : G.val.sections) : F ⟶ H :=
  Stacks.Cohomology.rightMulHom (tensorBilinear μ) u

/-- The degree-zero cohomology class of a global section. -/
def sectionClass {G : _root_.SheafOfModules.{u} (structureSheafRing X)} (s : G.val.sections) :
    Hgroup (structureSheafRing X) ⊤ 0 G :=
  ((secF (structureSheafRing X) (⊤ : Opens X.carrier)).toRightDerivedZero.app G).hom
    (s.eval (op ⊤))

/-- The bridge followed by the action of a morphism of the derived category, as maps of
modules. -/
def moduleDerivedMap {A F : _root_.SheafOfModules.{u} (structureSheafRing X)} {a b : ℕ}
    (φ : (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) (a : ℤ)).obj A ⟶
      (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) (b : ℤ)).obj F) :
    moduleDerived (A := X.sheaf) (singleNat A a) ⟶ moduleDerived (A := X.sheaf) (singleNat F b) :=
  (moduleDerivedSingleIso A a).hom ≫ φ ≫ (moduleDerivedSingleIso F b).inv

/-- The square comparing `moduleDerivedMap φ` with `φ` through the identifications
`moduleDerivedSingleIso`, after applying derived global sections and cohomology. -/
private lemma moduleDerivedMap_square (X : RingedSpace.{u, u})
    {A F : _root_.SheafOfModules.{u} (structureSheafRing X)} {a b : ℕ}
    (φ : (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) (a : ℤ)).obj A ⟶
      (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) (b : ℤ)).obj F)
    (m : ℤ) :
    (forget₂ (ModuleCat.{u} (baseRing X)) AddCommGrpCat.{u}).map
        ((DerivedCategory.homologyFunctor _ m).map
          ((baseSections X).map (moduleDerivedSingleIso A a).inv)) ≫
      (forget₂ (ModuleCat.{u} (baseRing X)) AddCommGrpCat.{u}).map
        ((DerivedCategory.homologyFunctor _ m).map ((baseSections X).map (moduleDerivedMap φ))) =
      (forget₂ (ModuleCat.{u} (baseRing X)) AddCommGrpCat.{u}).map
        ((DerivedCategory.homologyFunctor _ m).map ((baseSections X).map φ)) ≫
      (forget₂ (ModuleCat.{u} (baseRing X)) AddCommGrpCat.{u}).map
        ((DerivedCategory.homologyFunctor _ m).map
          ((baseSections X).map (moduleDerivedSingleIso F b).inv)) := by
  have hD : (moduleDerivedSingleIso A a).inv ≫ moduleDerivedMap φ =
      φ ≫ (moduleDerivedSingleIso F b).inv :=
    inv_hom_comp_eq (moduleDerivedSingleIso A a) _
  simp only [← Functor.map_comp, hD]

/-- The bridge carries the map on cohomology of a morphism `φ : A[-c] ⟶ F[0]` to the map induced
by `moduleDerivedMap φ` on the cohomology of derived global sections over the base ring. -/
theorem hgroupModuleShiftIso_cohomologyMapOfSingleHom
    (A F : _root_.SheafOfModules.{u} (structureSheafRing X)) (c q : ℕ) (m : ℤ)
    (h : (q : ℤ) + (c : ℤ) = m) (h₀ : ((q + c : ℕ) : ℤ) + ((0 : ℕ) : ℤ) = m)
    (φ : (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) (c : ℤ)).obj A ⟶
      (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) ((0 : ℕ) : ℤ)).obj F)
    (x : Hgroup (structureSheafRing X) ⊤ q A) :
    (hgroupModuleShiftIso F 0 (q + c) m h₀).hom (cohomologyMapOfSingleHom X A F c q φ x) =
      ((DerivedCategory.homologyFunctor _ m).map
        ((baseSections (baseRingedSpace X.sheaf)).map (moduleDerivedMap φ))).hom
        ((hgroupModuleShiftIso A c q m h).hom x) := by
  subst h
  have hN := homologyForgetIso_hom_naturality X ((q : ℤ) + (c : ℤ)) φ
  have hg := moduleDerivedMap_square X φ ((q : ℤ) + (c : ℤ))
  have key := bridge_chase
    (cohomologyDerivedSingleIso X A (c : ℤ) ((q : ℤ) + (c : ℤ)) q (by omega))
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} ((q : ℤ) + (c : ℤ))).map
      ((derivedGlobalSections X).map φ))
    (cohomologyDerivedSingleIso X F (0 : ℤ) ((q : ℤ) + (c : ℤ)) (q + c) (by omega))
    (cohomologyDerivedSingleIso X F ((0 : ℕ) : ℤ) ((q : ℤ) + (c : ℤ)) (q + c) (by omega)) rfl
    _ _ _ _ _ _ hN hg
  exact ConcreteCategory.congr_hom key x

/-- The compatibility of the multiplications `w` and `μ` with the edge morphisms `eL` and `eM`. -/
def EdgeTensorMatching
    {F L M G GM :
      _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)}
    (c : ℕ) (w : ((sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj L ⟶ M)
    (μ : ((sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj G ⟶ GM)
    (eL : (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) (c : ℤ)).obj G ⟶
      (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) ((0 : ℕ) : ℤ)).obj L)
    (eM : (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) (c : ℤ)).obj GM ⟶
      (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) ((0 : ℕ) : ℤ)).obj M) :
    Prop :=
  ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor (baseRingedSpace X.sheaf).sheaf).obj
        (moduleDerived (A := X.sheaf) (singleNat F 0))).map (moduleDerivedMap eL) ≫
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
          (baseRingedSpace X.sheaf).sheaf).toTensor
        ((singleNat F 0).extend ComplexShape.embeddingUpNat)
        ((singleNat L 0).extend ComplexShape.embeddingUpNat) ≫
      DerivedCategory.Q.map (multiplicationInt (singleTensorMult w 0 0 0 rfl)) =
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
        (baseRingedSpace X.sheaf).sheaf).toTensor
        ((singleNat F 0).extend ComplexShape.embeddingUpNat)
        ((singleNat G c).extend ComplexShape.embeddingUpNat) ≫
      DerivedCategory.Q.map (multiplicationInt (singleTensorMult μ 0 c c (zero_add c))) ≫
      moduleDerivedMap eM

/-- The bridge is natural in the sheaf. -/
theorem hgroupModuleShiftIso_naturality {F F' : _root_.SheafOfModules.{u} (structureSheafRing X)}
    (ψ : F ⟶ F') (c q : ℕ) (m : ℤ) (h : (q : ℤ) + (c : ℤ) = m)
    (x : Hgroup (structureSheafRing X) ⊤ q F) :
    (hgroupModuleShiftIso F' c q m h).hom ((Hfunctor (structureSheafRing X) ⊤ q).map ψ x) =
      ((DerivedCategory.homologyFunctor _ m).map ((baseSections (baseRingedSpace X.sheaf)).map
        (moduleDerivedMap ((singleFunctor _ (c : ℤ)).map ψ)))).hom
        ((hgroupModuleShiftIso F c q m h).hom x) := by
  subst h
  have hN₀ := cohomologyDerivedSingleIso_hom_naturality X ψ (c : ℤ) ((q : ℤ) + (c : ℤ)) q
    (by omega)
  have hN := homologyForgetIso_hom_naturality X ((q : ℤ) + (c : ℤ))
    ((singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) (c : ℤ)).map ψ)
  have hg := moduleDerivedMap_square X ((singleFunctor _ (c : ℤ)).map ψ) ((q : ℤ) + (c : ℤ))
  have key := naturality_chase _ _ _ _ _ _ _ _ _ _ hN₀ hN hg
  exact ConcreteCategory.congr_hom key x

end StandardModel

end Stacks.DeRham.GysinCupHodge
