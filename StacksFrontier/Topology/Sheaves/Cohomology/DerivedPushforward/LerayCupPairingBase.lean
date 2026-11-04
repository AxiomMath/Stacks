module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayCupPairing

/-!
# The relative cup product on cohomology, at classes of global cocycles

Let `f : X ⟶ Y` be a morphism of ringed spaces.  For K-flat complexes `P`, `Q` of
`𝒪_X`-modules and global cocycles `s`, `t`, this file proves that the Leray identification
carries the cup product on `Y` of the classes of `s` and `t` in `Hⁱ(Y, Rf_*P)` and `Hʲ(Y, Rf_*Q)`,
followed by the relative cup product of Tag 0B68, to the cup product on `X` of the classes of `s`
and `t` (`lerayCohomologyIso_relativeCupProduct_pushClass`).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.GlobalKunneth
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.SiteCohomologyPresheaf
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.LerayCupPairing

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-! ### The relative cup product on classes of global cocycles -/

section Universal

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
open scoped Stacks.Topology.SheafTensorAdditiveOnOpens
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces Stacks.RingedSpace
open Stacks.Cohomology.DerivedPullbackTensor (derivedToTensorNatTrans totalComplexPair)
open Stacks.Cohomology.DerivedRelativeCupProduct (relativeCupProduct)
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces
open _root_.PresheafOfModules
open scoped TensorProduct

/-- A cocycle of `Γ(X, N)`, read as a cocycle of `Γ(Y, f_*N) = Γ(X, N)`. -/
def pushCycle (N : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
    (n : ℤ) (c : (sectionsComplex X N).cycles n) :
    (sectionsComplex Y ((pushforwardComplex f).obj N)).cycles n :=
  (((sectionsComplex X N).sc n).mapCyclesIso (restrictGlobal f)).inv.hom c

/-- The underlying section of `pushCycle f N n c` is that of `c`. -/
theorem iCycles_pushCycle
    (N : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
    (n : ℤ) (c : (sectionsComplex X N).cycles n) :
    ((sectionsComplex Y ((pushforwardComplex f).obj N)).iCycles n).hom (pushCycle f N n c) =
      ((sectionsComplex X N).iCycles n).hom c := by
  have h := ConcreteCategory.congr_hom
    (((sectionsComplex X N).sc n).mapCyclesIso_hom_iCycles (restrictGlobal f))
    (pushCycle f N n c)
  refine h.symm.trans ?_
  have h2 := ConcreteCategory.congr_hom
    (((sectionsComplex X N).sc n).mapCyclesIso (restrictGlobal f)).inv_hom_id c
  exact congrArg ((sectionsComplex X N).iCycles n).hom h2

/-- The class in `Hⁿ(Y, Rf_*N)` of a global cocycle `c` of `N`: the class of `c` read on
`Γ(Y, f_*N)`, pushed along the comparison `f_* ⟶ Rf_*`. -/
abbrev pushClass
    (N : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
    (n : ℤ) (c : (sectionsComplex X N).cycles n) :
    cohomologyModule ((derivedPushforward f).obj (DerivedCategory.Q.obj N)) n :=
  ((DerivedCategory.homologyFunctor _ n).map
    ((baseSections Y).map (pushforwardComparisonQ f N))).hom
      (globalClass ((pushforwardComplex f).obj N) n (pushCycle f N n c))

/-- The Leray identification sends `pushClass f N n c` to the class of `c`. -/
theorem lerayCohomologyIso_pushClass
    (N : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
    (n : ℤ) (c : (sectionsComplex X N).cycles n) :
    (lerayCohomologyIso f (DerivedCategory.Q.obj N) n).hom (pushClass f N n c) =
      globalClass N n c :=
  lerayCohomologyIso_globalClass f N n _ c (iCycles_pushCycle f N n c)

/-- A functor to modules applied to a threefold composite, evaluated at an element. -/
theorem functor_map_comp₃_apply {C : Type*} [Category* C] {R : CommRingCat.{u}}
    (G : C ⥤ ModuleCat.{u} R) {a b c d : C} (x : a ⟶ b) (y : b ⟶ c) (z : c ⟶ d) (w : G.obj a) :
    (G.map (x ≫ y ≫ z)).hom w = (G.map z).hom ((G.map y).hom ((G.map x).hom w)) := by
  simp

/-- A functor to modules applied to a composite, evaluated at an element. -/
theorem functor_map_comp₂_apply {C : Type*} [Category* C] {R : CommRingCat.{u}}
    (G : C ⥤ ModuleCat.{u} R) {a b c : C} (x : a ⟶ b) (y : b ⟶ c) (w : G.obj a) :
    (G.map (x ≫ y)).hom w = (G.map y).hom ((G.map x).hom w) := by
  simp

/-- On cohomology of global sections, the relative cup product of the cup product on `Y` of the
images of `a` and `b` under the comparison `f_* ⟶ Rf_*`, followed by `Rf_*` of the canonical map
to the total tensor complex, is the image of the total cup pairing of `a` and `b` under the naive
cup product and the comparison `f_* ⟶ Rf_*`. -/
theorem relativeCupProduct_cupPairing_pushforwardComparisonQ
    (P Q : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
    (i j : ℤ) (a : cohomologyModule (DerivedCategory.Q.obj ((pushforwardComplex f).obj P)) i)
    (b : cohomologyModule (DerivedCategory.Q.obj ((pushforwardComplex f).obj Q)) j) :
    ((DerivedCategory.homologyFunctor _ (i + j)).map ((baseSections Y).map
      ((derivedPushforward f).map ((derivedToTensorNatTrans X).app (P, Q))))).hom
      (((DerivedCategory.homologyFunctor _ (i + j)).map ((baseSections Y).map
        (relativeCupProduct f (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)))).hom
        ((cupPairing (cupProductOnSpace Y) _ _ i j).hom
          (((DerivedCategory.homologyFunctor _ i).map
            ((baseSections Y).map (pushforwardComparisonQ f P))).hom a ⊗ₜ
           ((DerivedCategory.homologyFunctor _ j).map
            ((baseSections Y).map (pushforwardComparisonQ f Q))).hom b))) =
      ((DerivedCategory.homologyFunctor _ (i + j)).map ((baseSections Y).map
        (DerivedCategory.Q.map (naiveCupProduct f P Q) ≫
          pushforwardComparisonQ f ((totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)).obj (P, Q))))).hom
        ((totalCupPairing ((pushforwardComplex f).obj P) ((pushforwardComplex f).obj Q) i j).hom
          (a ⊗ₜ b)) := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing Y)) (i + j)
  let R := baseSections Y
  have hcup := cupPairing_naturality_apply (cupProductOnSpace Y) (pushforwardComparisonQ f P)
    (pushforwardComparisonQ f Q) i j a b
  have h03 := naiveCupProduct_relativeCupProduct f P Q
  have e1 := congrArg (fun z => (H.map (R.map ((derivedPushforward f).map
      ((derivedToTensorNatTrans X).app (P, Q))))).hom ((H.map (R.map
        (relativeCupProduct f (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)))).hom z)) hcup
  refine e1.trans ?_
  have e2 := congrArg (fun φ => ((R ⋙ H).map φ).hom
    ((cupPairing (cupProductOnSpace Y) _ _ i j).hom (a ⊗ₜ b))) h03
  refine (functor_map_comp₃_apply (R ⋙ H) _ _ _ _).symm.trans ?_
  refine e2.symm.trans ?_
  exact functor_map_comp₂_apply (R ⋙ H) _ _ _

open _root_.PresheafOfModules in
/-- The naive cup product on global sections carries the naive cup product on `Y` of a pure
tensor `x ⊗ y` to the naive cup product on `X` of `x ⊗ y`. -/
theorem naiveCupProduct_naiveCupProductEval_tmul
    (P Q : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
    (i j : ℤ) (x : (Stacks.Cech.SheafTensorPairing.evalComplex X.sheaf ⊤ P).X i)
    (y : (Stacks.Cech.SheafTensorPairing.evalComplex X.sheaf ⊤ Q).X j) :
    (((naiveCupProduct f P Q).f (i + j)).val.app (op ⊤)).hom
      ((HomologicalComplex.ιMapBifunctor
          (Stacks.Cech.SheafTensorPairing.evalComplex Y.sheaf ⊤ ((pushforwardComplex f).obj P))
          (Stacks.Cech.SheafTensorPairing.evalComplex Y.sheaf ⊤ ((pushforwardComplex f).obj Q))
          (Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing Y.sheaf ⊤))
          (ComplexShape.up ℤ) i j (i + j) rfl ≫
        (Stacks.Cech.SheafTensorPairing.naiveCupProductEval Y.sheaf ⊤
          ((pushforwardComplex f).obj P) ((pushforwardComplex f).obj Q)).f (i + j)).hom
        (x ⊗ₜ y)) =
      (HomologicalComplex.ιMapBifunctor
          (Stacks.Cech.SheafTensorPairing.evalComplex X.sheaf ⊤ P)
          (Stacks.Cech.SheafTensorPairing.evalComplex X.sheaf ⊤ Q)
          (Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing X.sheaf ⊤))
          (ComplexShape.up ℤ) i j (i + j) rfl ≫
        (Stacks.Cech.SheafTensorPairing.naiveCupProductEval X.sheaf ⊤ P Q).f (i + j)).hom
        (x ⊗ₜ y) := by
  refine (congrArg (((naiveCupProduct f P Q).f (i + j)).val.app (op ⊤)).hom
    (naiveCupProductEval_ι_tmul Y ((pushforwardComplex f).obj P) ((pushforwardComplex f).obj Q)
      i j (i + j) rfl x y)).trans ?_
  refine Eq.trans ?_ (naiveCupProductEval_ι_tmul X P Q i j (i + j) rfl x y).symm
  exact naiveCupProduct_unit_tmul f P Q i j (i + j) rfl x y

/-- `tensorMap a b ≫ g` sends a pure tensor `x ⊗ y` to `g (a x ⊗ b y)`. -/
theorem tensorMap_comp_tmul (Z : RingedSpace.{u, u}) {A A' B B' : ModuleCat.{u}
      (Stacks.Cech.ModuleCupProduct.CoeffRing Z.sheaf ⊤)} {C : ModuleCat.{u}
      (Stacks.Cech.ModuleCupProduct.CoeffRing Z.sheaf ⊤)}
    (a : A ⟶ A') (b : B ⟶ B') (g : ((Stacks.Cech.CupProduct.tensorModules
      (Stacks.Cech.ModuleCupProduct.CoeffRing Z.sheaf ⊤)).obj A').obj B' ⟶ C) (x : A) (y : B) :
    (Stacks.Cech.SheafTensorPairing.tensorMap Z.sheaf ⊤ a b ≫ g).hom (x ⊗ₜ y) =
      g.hom (a.hom x ⊗ₜ b.hom y) := by
  rw [Stacks.Cech.SheafTensorPairing.tensorMap_eq_tensorHom]
  rfl

/-- `tensorMap a b` sends a pure tensor `x ⊗ y` to `a x ⊗ b y`. -/
theorem tensorMap_tmul (Z : RingedSpace.{u, u}) {A A' B B' : ModuleCat.{u}
      (Stacks.Cech.ModuleCupProduct.CoeffRing Z.sheaf ⊤)}
    (a : A ⟶ A') (b : B ⟶ B') (x : A) (y : B) :
    (Stacks.Cech.SheafTensorPairing.tensorMap Z.sheaf ⊤ a b).hom (x ⊗ₜ y) = a.hom x ⊗ₜ b.hom y := by
  rw [Stacks.Cech.SheafTensorPairing.tensorMap_eq_tensorHom]
  rfl

/-- The Leray identification, then `RΓ(X, -)` of the canonical map to the total tensor complex, of
the relative cup product on `Y` is the Leray identification of the image of the total cup pairing
on `Y` under the naive cup product and the comparison `f_* ⟶ Rf_*`. -/
theorem lerayCohomologyIso_relativeCupProduct_eq
    (P Q : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
    (i j : ℤ) (a : cohomologyModule (DerivedCategory.Q.obj ((pushforwardComplex f).obj P)) i)
    (b : cohomologyModule (DerivedCategory.Q.obj ((pushforwardComplex f).obj Q)) j) :
    ((DerivedCategory.homologyFunctor _ (i + j)).map
        ((baseSections X).map ((derivedToTensorNatTrans X).app (P, Q)))).hom
      ((lerayCohomologyIso f (((derivedTensorProductFunctor X.sheaf).obj
        (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj Q)) (i + j)).hom
      (((DerivedCategory.homologyFunctor _ (i + j)).map ((baseSections Y).map
        (relativeCupProduct f (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)))).hom
        ((cupPairing (cupProductOnSpace Y) _ _ i j).hom
          (((DerivedCategory.homologyFunctor _ i).map
            ((baseSections Y).map (pushforwardComparisonQ f P))).hom a ⊗ₜ
           ((DerivedCategory.homologyFunctor _ j).map
            ((baseSections Y).map (pushforwardComparisonQ f Q))).hom b)))) =
      (lerayCohomologyIso f _ (i + j)).hom
        (((DerivedCategory.homologyFunctor _ (i + j)).map ((baseSections Y).map
        (DerivedCategory.Q.map (naiveCupProduct f P Q) ≫
          pushforwardComparisonQ f ((totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)).obj (P, Q))))).hom
        ((totalCupPairing ((pushforwardComplex f).obj P) ((pushforwardComplex f).obj Q) i j).hom
          (a ⊗ₜ b))) :=
  (lerayCohomologyIso_naturality_apply f ((derivedToTensorNatTrans X).app (P, Q)) (i + j)
    _).symm.trans (congrArg (lerayCohomologyIso f _ (i + j)).hom
      (relativeCupProduct_cupPairing_pushforwardComparisonQ f P Q i j a b))

/-- The image under the naive cup product and the comparison `f_* ⟶ Rf_*` of the class of a global
cocycle `c` of `Tot(f_*P ⊗ f_*Q)` is carried by the Leray identification to the class of any
global cocycle of `Tot(P ⊗ Q)` with the same underlying section as the naive cup product of
`c`. -/
theorem lerayCohomologyIso_naive_globalClass
    (P Q : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
    (n : ℤ) (c : (sectionsComplex Y ((totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).obj
          ((pushforwardComplex f).obj P, (pushforwardComplex f).obj Q))).cycles n)
    (c' : (sectionsComplex X ((totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)).obj (P, Q))).cycles n)
    (h : (((naiveCupProduct f P Q).f n).val.app (op ⊤)).hom
        (((sectionsComplex Y _).iCycles n).hom c) =
      ((sectionsComplex X _).iCycles n).hom c') :
    (lerayCohomologyIso f _ n).hom
        (((DerivedCategory.homologyFunctor _ n).map ((baseSections Y).map
        (DerivedCategory.Q.map (naiveCupProduct f P Q) ≫
          pushforwardComparisonQ f ((totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)).obj (P, Q))))).hom
        (globalClass _ n c)) = globalClass _ n c' := by
  refine (congrArg (lerayCohomologyIso f _ n).hom (functor_map_comp₂_apply
    (baseSections Y ⋙ DerivedCategory.homologyFunctor _ n) _ _ _)).trans ?_
  refine (congrArg (fun z => (lerayCohomologyIso f _ n).hom
    (((DerivedCategory.homologyFunctor _ n).map ((baseSections Y).map
      (pushforwardComparisonQ f ((totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)).obj
              (P, Q))))).hom z))
    (globalClass_map Y (naiveCupProduct f P Q) n c)).trans ?_
  exact lerayCohomologyIso_globalClass f _ n _ c'
    ((ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i _ n) c).trans h)

/-- On K-flat complexes `RΓ(X, -)` of the canonical map to the total tensor complex is injective on
cohomology. -/
theorem injective_derivedToTensorNatTrans
    (P Q : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
    (hP : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat X P)
    (hQ : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat X Q) (n : ℤ) :
    Function.Injective ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) n).map
      ((baseSections X).map ((derivedToTensorNatTrans X).app (P, Q)))).hom := by
  have hiso : IsIso ((derivedToTensorNatTrans X).app (P, Q)) := by
    rw [DerivedPullbackTensor.derivedToTensorNatTrans_app_eq_canonicalComparisonHom X P Q hP hQ]
    exact Stacks.Cohomology.DerivedPullbackTensor.isIso_canonicalComparisonHom X P Q hP hQ
  exact ((DerivedCategory.homologyFunctor _ n).mapIso ((baseSections X).mapIso
    (@asIso _ _ _ _ ((derivedToTensorNatTrans X).app (P, Q)) hiso))).toLinearEquiv.injective

/-- There is a map from the tensor product of the `i`-cocycles of `Γ(Z, K)` and the `j`-cocycles
of `Γ(Z, M)` to the `(i + j)`-cocycles of the total complex of their tensor product lifting the
tensor product of the two inclusions of cocycles followed by the inclusion of the `(i, j)`
summand. -/
theorem exists_tensorCycles_naive' (Z : RingedSpace.{u, u})
    (K M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ)
    (i j : ℤ) :
    ∃ z₀ : ((Stacks.Cech.CupProduct.tensorModules
          (Stacks.Cech.ModuleCupProduct.CoeffRing Z.sheaf ⊤)).obj
          ((Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ K).cycles i)).obj
          ((Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ M).cycles j) ⟶
        (HomologicalComplex.mapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ K)
          (Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ M)
          (Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing Z.sheaf ⊤))
          (ComplexShape.up ℤ)).cycles (i + j),
      z₀ ≫ (HomologicalComplex.mapBifunctor
          (Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ K)
          (Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ M)
          (Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing Z.sheaf ⊤))
          (ComplexShape.up ℤ)).iCycles (i + j) =
        Stacks.Cech.SheafTensorPairing.tensorMap Z.sheaf ⊤
            ((Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ K).iCycles i)
            ((Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ M).iCycles j) ≫
          HomologicalComplex.ιMapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ K)
            (Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ M)
            (Stacks.Cech.CupProduct.tensorModules
              (Stacks.Cech.ModuleCupProduct.CoeffRing Z.sheaf ⊤)) (ComplexShape.up ℤ) i j (i + j)
            rfl :=
  exists_tensorCycles_naive (S := Z) K M i j

/-- A chosen tensoring of cocycles of two complexes of global sections. -/
noncomputable def tensorCyclesChoice (Z : RingedSpace.{u, u})
    (K M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ)
    (i j : ℤ) :
    ((Stacks.Cech.CupProduct.tensorModules
          (Stacks.Cech.ModuleCupProduct.CoeffRing Z.sheaf ⊤)).obj
          ((Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ K).cycles i)).obj
          ((Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ M).cycles j) ⟶
        (HomologicalComplex.mapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ K)
          (Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ M)
          (Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing Z.sheaf ⊤))
          (ComplexShape.up ℤ)).cycles (i + j) :=
  Classical.choose (exists_tensorCycles_naive' Z K M i j)

/-- `tensorCyclesChoice Z K M i j`, followed by the inclusion of cocycles, is the tensor product of
the two inclusions of cocycles followed by the inclusion of the `(i, j)` summand. -/
theorem tensorCyclesChoice_spec (Z : RingedSpace.{u, u})
    (K M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ)
    (i j : ℤ) :
    tensorCyclesChoice Z K M i j ≫ (HomologicalComplex.mapBifunctor
          (Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ K)
          (Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ M)
          (Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing Z.sheaf ⊤))
          (ComplexShape.up ℤ)).iCycles (i + j) =
        Stacks.Cech.SheafTensorPairing.tensorMap Z.sheaf ⊤
            ((Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ K).iCycles i)
            ((Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ M).iCycles j) ≫
          HomologicalComplex.ιMapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ K)
            (Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ M)
            (Stacks.Cech.CupProduct.tensorModules
              (Stacks.Cech.ModuleCupProduct.CoeffRing Z.sheaf ⊤)) (ComplexShape.up ℤ) i j (i + j)
            rfl :=
  Classical.choose_spec (exists_tensorCycles_naive' Z K M i j)

/-- The underlying section of the total cup pairing of cocycles `x`, `y`, computed with
`tensorCyclesChoice`, is the image of the pure tensor of their underlying sections. -/
private theorem iCycles_tensorCyclesChoice_tmul (Z : RingedSpace.{u, u})
    (K M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ)
    (i j : ℤ) (x : (sectionsComplex Z K).cycles i) (y : (sectionsComplex Z M).cycles j) :
    ((sectionsComplex Z ((totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)).obj (K, M))).iCycles
          (i + j)).hom
        ((tensorCyclesChoice Z K M i j ≫ HomologicalComplex.cyclesMap
          (Stacks.Cech.SheafTensorPairing.naiveCupProductEval Z.sheaf ⊤ K M) (i + j)).hom
            (x ⊗ₜ y)) =
      (HomologicalComplex.ιMapBifunctor
          (Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ K)
          (Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ M)
          (Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing Z.sheaf ⊤))
          (ComplexShape.up ℤ) i j (i + j) rfl ≫
        (Stacks.Cech.SheafTensorPairing.naiveCupProductEval Z.sheaf ⊤ K M).f (i + j)).hom
        ((((sectionsComplex Z K).iCycles i).hom x) ⊗ₜ (((sectionsComplex Z M).iCycles j).hom y)) :=
  (ConcreteCategory.congr_hom (iCycles_totalCupPairing_cycle Z K M i j
    (tensorCyclesChoice Z K M i j) (tensorCyclesChoice_spec Z K M i j)) _).trans
      (tensorMap_comp_tmul Z _ _ _ _ _)

/-- The naive cup product carries the underlying section of the chosen tensoring of
`pushCycle f P i s` and `pushCycle f Q j t` to that of the chosen tensoring of `s` and `t`. -/
theorem naiveCupProduct_iCycles_cycle_eq
    (P Q : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
    (i j : ℤ) (s : (sectionsComplex X P).cycles i) (t : (sectionsComplex X Q).cycles j) :
    (((naiveCupProduct f P Q).f (i + j)).val.app (op ⊤)).hom
        (((sectionsComplex Y _).iCycles (i + j)).hom
          ((tensorCyclesChoice Y ((pushforwardComplex f).obj P) ((pushforwardComplex f).obj Q) i j ≫
            HomologicalComplex.cyclesMap
            (Stacks.Cech.SheafTensorPairing.naiveCupProductEval Y.sheaf ⊤
              ((pushforwardComplex f).obj P) ((pushforwardComplex f).obj Q)) (i + j)).hom
            (pushCycle f P i s ⊗ₜ pushCycle f Q j t))) =
      ((sectionsComplex X _).iCycles (i + j)).hom
        ((tensorCyclesChoice X P Q i j ≫ HomologicalComplex.cyclesMap
          (Stacks.Cech.SheafTensorPairing.naiveCupProductEval X.sheaf ⊤ P Q) (i + j)).hom
            (s ⊗ₜ t)) := by
  refine (congrArg (((naiveCupProduct f P Q).f (i + j)).val.app (op ⊤)).hom
    (iCycles_tensorCyclesChoice_tmul Y _ _ i j _ _)).trans
      (Eq.trans ?_ (iCycles_tensorCyclesChoice_tmul X P Q i j s t).symm)
  rw [iCycles_pushCycle, iCycles_pushCycle]
  exact naiveCupProduct_naiveCupProductEval_tmul f P Q i j _ _

/-- After `RΓ(X, -)` of the canonical map to the total tensor complex, the Leray identification of
the relative cup product of the cup product on `Y` of `pushClass f P i s` and `pushClass f Q j t`
is the cup product on `X` of the classes of `s` and `t`. -/
theorem lerayCohomologyIso_relativeCupProduct_pushClass_aux
    (P Q : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
    (i j : ℤ) (s : (sectionsComplex X P).cycles i) (t : (sectionsComplex X Q).cycles j) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) (i + j)).map
        ((baseSections X).map ((derivedToTensorNatTrans X).app (P, Q)))).hom
      ((lerayCohomologyIso f (((derivedTensorProductFunctor X.sheaf).obj
        (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj Q)) (i + j)).hom
      (((DerivedCategory.homologyFunctor _ (i + j)).map ((baseSections Y).map
        (relativeCupProduct f (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)))).hom
        ((cupPairing (cupProductOnSpace Y) _ _ i j).hom
          (pushClass f P i s ⊗ₜ pushClass f Q j t)))) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) (i + j)).map
        ((baseSections X).map ((derivedToTensorNatTrans X).app (P, Q)))).hom
      ((cupPairing (cupProductOnSpace X) (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
        i j).hom (globalClass P i s ⊗ₜ globalClass Q j t)) :=
  (lerayCohomologyIso_relativeCupProduct_eq f P Q i j
      (globalClass _ i (pushCycle f P i s)) (globalClass _ j (pushCycle f Q j t))).trans <|
    (congrArg (fun z => (lerayCohomologyIso f _ (i + j)).hom
      (((DerivedCategory.homologyFunctor _ (i + j)).map ((baseSections Y).map
        (DerivedCategory.Q.map (naiveCupProduct f P Q) ≫
          pushforwardComparisonQ f ((totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)).obj
              (P, Q))))).hom z))
      (totalCupPairing_globalClass Y ((pushforwardComplex f).obj P) ((pushforwardComplex f).obj Q)
        i j (pushCycle f P i s) (pushCycle f Q j t)
        (tensorCyclesChoice Y ((pushforwardComplex f).obj P) ((pushforwardComplex f).obj Q) i j)
        (tensorCyclesChoice_spec Y ((pushforwardComplex f).obj P) ((pushforwardComplex f).obj Q)
          i j))).trans <|
    (lerayCohomologyIso_naive_globalClass f P Q (i + j) _ _
      (naiveCupProduct_iCycles_cycle_eq f P Q i j s t)).trans
      ((totalCupPairing_globalClass X P Q i j s t (tensorCyclesChoice X P Q i j)
          (tensorCyclesChoice_spec X P Q i j)).symm.trans
        (ConcreteCategory.comp_apply _ _ _))

/-- For K-flat complexes `P`, `Q` and global cocycles `s`, `t`, the Leray identification carries
the relative cup product of the cup product on `Y` of `pushClass f P i s` and `pushClass f Q j t`
to the cup product on `X` of the classes of `s` and `t`. -/
theorem lerayCohomologyIso_relativeCupProduct_pushClass
    (P Q : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
    (hP : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat X P)
    (hQ : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat X Q) (i j : ℤ)
    (s : (sectionsComplex X P).cycles i) (t : (sectionsComplex X Q).cycles j) :
    (lerayCohomologyIso f (((derivedTensorProductFunctor X.sheaf).obj
        (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj Q)) (i + j)).hom
      (((DerivedCategory.homologyFunctor _ (i + j)).map ((baseSections Y).map
        (relativeCupProduct f (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)))).hom
        ((cupPairing (cupProductOnSpace Y) _ _ i j).hom
          (pushClass f P i s ⊗ₜ pushClass f Q j t))) =
      (cupPairing (cupProductOnSpace X) (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
        i j).hom (globalClass P i s ⊗ₜ globalClass Q j t) :=
  injective_derivedToTensorNatTrans P Q hP hQ (i + j)
    (lerayCohomologyIso_relativeCupProduct_pushClass_aux f P Q i j s t)

end Universal

end Stacks.Cohomology.LerayCupPairing

end
