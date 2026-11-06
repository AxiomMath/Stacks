module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceLevelBaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceSystemIso
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceDerivedLimitSections
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceLevelMaps
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistencePerfectTwist
public import StacksFrontier.AlgebraicGeometry.Perfect.GlobalSectionsTensorFlatProperSupport
public import StacksFrontier.CategoryTheory.Triangulated.DerivedLimitTriangulatedTower
public import StacksFrontier.AlgebraicGeometry.AffineDerivedBaseChangeGeneral
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.CoherentTorSheaves
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPushforwardBaseChangeCanonical

/-!
# Grothendieck's existence theorem: twisting `K` by a perfect complex, part (1)

In Situation [Stacks, Tag 0CTC] let `K = DQ_X(R lim Fₙ)` be as in [Stacks, Tag 0CTD], given by the
data `d` of `AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.DerivedLimitQCoh`, and let
`E` be a perfect object of `D(𝒪_X)`. This file proves part (1) of [Stacks, Tag 0CTE]:
`M = RΓ(X, K ⊗^𝐋 E)` is a perfect object of `D(A)`, and for every `n` the canonical map
`M ⊗^𝐋_A Aₙ ⟶ RΓ(Xₙ, ℱₙ ⊗^𝐋 E|_{Xₙ})` is an isomorphism.

## The proof

It is the source's. The level objects `Mₙ = RΓ_{Aₙ}(Xₙ, ℱₙ ⊗^𝐋 Eₙ)` form a tower over the rings
`Aₙ` (`AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.levelTensorTransition`); they are
perfect and their formation commutes with base change by [Stacks, Tag 0A1H]. The object `M` is the
derived limit of the tower read over `A`: `RΓ_A(X, -)` and `- ⊗^𝐋 E` carry the derived limit
`L = R lim Fₙ` to a derived limit, `K ⟶ L` becomes an isomorphism after them, and the terms
`RΓ_A(X, iₙ,* ℱₙ ⊗^𝐋 E)` are the restrictions of the `Mₙ`. Then [Stacks, Tag 0CQG] applies.

## Implementation notes

As [Stacks, Tag 0A1H] and [Stacks, Tag 0CQG], the statements are at
`CategoryTheory.HasDerivedCategory.standard`, scoped to each declaration.

The canonical map is stated for an arbitrary cone `p : L ⟶ ∏ iₙ,* ℱₙ` exhibiting `L` as the
derived limit, so that the maps `K ⟶ iₙ,* ℱₙ` it is built from
(`AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.levelMap`) are the ones the later
tags of the section use.

## References

* [Stacks Project, Tag 0CTE](https://stacks.math.columbia.edu/tag/0CTE)
* [Stacks Project, Tag 0CTD](https://stacks.math.columbia.edu/tag/0CTD)
* [Stacks Project, Tag 0CQG](https://stacks.math.columbia.edu/tag/0CQG)
* [Stacks Project, Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward
  derivedAdjunction)
open StacksDraft.DerivedInverseLimit

universe u

namespace AlgebraicGeometry.GrothendieckExistence

section Transport

variable {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **A derived-limit triangle transports along an isomorphism of towers.** If
`K ⟶ ∏ Yₙ ⟶ ∏ Yₙ ⟶ K[1]` is distinguished, with the difference map of the transitions `tₙ` in the
middle, and `fₙ : Yₙ ≅ Y'ₙ` intertwines `tₙ` with `t'ₙ`, then so is the triangle obtained by
composing with `∏ fₙ`. -/
theorem distTriang_comp_piMap_of_iso {Y Y' : ℕ → D} [HasProduct Y] [HasProduct Y']
    {t : ∀ n : ℕ, Y (n + 1) ⟶ Y n} {t' : ∀ n : ℕ, Y' (n + 1) ⟶ Y' n} (f : ∀ n, Y n ≅ Y' n)
    (hf : ∀ n, (f (n + 1)).hom ≫ t' n = t n ≫ (f n).hom) {K : D} (p : K ⟶ ∏ᶜ Y)
    (δ : (∏ᶜ Y) ⟶ K⟦(1 : ℤ)⟧)
    (hT : Triangle.mk p (Pi.lift fun n : ℕ => Pi.π Y n - Pi.π Y (n + 1) ≫ t n) δ ∈ distTriang D) :
    Triangle.mk (p ≫ Limits.Pi.map fun n => (f n).hom)
      (Pi.lift fun n : ℕ => Pi.π Y' n - Pi.π Y' (n + 1) ≫ t' n)
      (Limits.Pi.map (fun n => (f n).inv) ≫ δ) ∈ distTriang D := by
  let e : (∏ᶜ Y) ≅ ∏ᶜ Y' :=
    { hom := Limits.Pi.map fun n => (f n).hom
      inv := Limits.Pi.map fun n => (f n).inv
      hom_inv_id := Pi.hom_ext _ _ fun n => by simp
      inv_hom_id := Pi.hom_ext _ _ fun n => by simp }
  have he := piMap_familyDifference (Y := Y) (Y' := Y') (t := t) (t' := t')
    (fun n => (f n).hom) hf
  refine isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ (Iso.refl _) e.symm e.symm ?_ ?_ ?_)
  · show (p ≫ e.hom) ≫ e.inv = 𝟙 _ ≫ p
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · show familyDifference _ _ ≫ e.inv = e.inv ≫ familyDifference _ _
    rw [Iso.comp_inv_eq, Category.assoc, ← he, Iso.inv_hom_id_assoc]
  · show (e.inv ≫ δ) ≫ (𝟙 K)⟦(1 : ℤ)⟧' = e.inv ≫ δ
    rw [CategoryTheory.Functor.map_id, Category.comp_id]

end Transport

/-- A functor carries an equality of composites to an equality of composites. -/
private theorem functor_map_comp_eq_of_comp_eq {C E : Type*} [Category C] [Category E] (G : C ⥤ E)
    {X Y Z W : C} {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X ⟶ W} {g' : W ⟶ Z} (h : f ≫ g = f' ≫ g') :
    G.map f ≫ G.map g = G.map f' ≫ G.map g' :=
  (G.map_comp _ _).symm.trans ((congrArg G.map h).trans (G.map_comp _ _))

namespace ExistenceSituation

variable (S : ExistenceSituation.{u})

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The level objects are perfect** ([Stacks, Tag 0A1H] for the proper flat family `ℱₙ` over
`Spec Aₙ`): `Mₙ = RΓ_{Aₙ}(Xₙ, ℱₙ ⊗^𝐋 Eₙ)` is a perfect object of `D(Aₙ)` for perfect `E`. -/
theorem isPerfect_levelTensor (n : ℕ) (E : DerivedCategory S.X.left.Modules)
    (hE : RingedSpace.IsPerfect (X := S.X.left.toRingedSpace) E) :
    StacksDraft.Perfect.IsPerfect (S.levelTensor n E) :=
  have := S.finitelyPresented n
  isPerfect_derivedGlobalSectionsOver_tensor_single (S.levelStructure n)
    (S.finitePresentation_levelStructure n) (S.F n) (S.flat n) (S.properSupport n)
    ((S.levelPullback n).obj E)
    (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ E hE)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The assembly of [Stacks, Tag 0CTE] (1) through [Stacks, Tag 0CQG]**, from the two facts
about the level tower that remain to be supplied: that its formation commutes with base change,
and that the pushed-forward system twisted by `E` is the restricted level tower compatibly with
the transitions. -/
theorem DerivedLimitQCoh.isPerfect_and_isIso_baseChange_of (d : S.DerivedLimitQCoh)
    (E : DerivedCategory S.X.left.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.X.left.toRingedSpace) E)
    (p : d.L ⟶ ∏ᶜ fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩)
    (hp : S.IsDerivedLimitCone p)
    (hBC : ∀ n : ℕ, IsIso (derivedBaseChangeComparison (S.ringTransition n)
      (S.levelTensorTransition n E)))
    (hComm : ∀ n : ℕ, (derivedGlobalSectionsOver S.X.hom).map
        (((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).map
          (S.derivedPushforwardSystemOfModel.map (homOfLE (Nat.le_succ n)).op)).app E) ≫
        (S.levelTensorRestrictionIso n E hE).hom =
      (S.levelTensorRestrictionIso (n + 1) E hE).hom ≫
        S.towerTransition (fun m => S.levelTensor m E) (fun m => S.levelTensorTransition m E) n) :
    StacksDraft.Perfect.IsPerfect ((derivedGlobalSectionsOver S.X.hom).obj
        (((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).obj d.K).obj E)) ∧
      ∀ n : ℕ, IsIso (derivedBaseChangeComparison (S.limitProjection n)
        ((derivedGlobalSectionsOver S.X.hom).map
          (((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).map
            (S.levelMap d p n)).app E) ≫ (S.levelTensorRestrictionIso n E hE).hom)) := by
  obtain ⟨hprod, δ, hT⟩ := S.derivedLimitTriangle_globalSectionsTensor_of_isPerfect d E hE p hp
  let := hprod
  have : HasProduct (S.towerRestriction fun m => S.levelTensor m E) :=
    hasLimit_of_iso (F := Discrete.functor fun n : ℕ => (derivedGlobalSectionsOver S.X.hom).obj
      (((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).obj
        (S.derivedPushforwardSystemOfModel.obj ⟨n⟩)).obj E))
      (Discrete.natIso fun n => S.levelTensorRestrictionIso n.as E hE)
  have hT' := distTriang_comp_piMap_of_iso (fun n => S.levelTensorRestrictionIso n E hE)
    (fun n => (hComm n).symm) _ δ hT
  let T : S.DerivedLimitTower (fun m => S.levelTensor m E)
      ((derivedGlobalSectionsOver S.X.hom).obj
        (((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).obj d.K).obj E)) :=
    { transition := fun n => S.levelTensorTransition n E
      isPerfect := fun n => S.isPerfect_levelTensor n E hE
      comparison_isIso := hBC
      p := _
      δ := _
      triangle := hT' }
  obtain ⟨h1, h2⟩ := DerivedLimitTower.isPerfect_and_isIso_baseChange S _ _ T
  refine ⟨h1, fun n => ?_⟩
  convert h2 n using 2
  have hs : (derivedGlobalSectionsOver S.X.hom).map
      (((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).map
        ((d.ε ≫ p) ≫ Pi.π (fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩) n)).app E) =
      (derivedGlobalSectionsOver S.X.hom).map
        (((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).map (d.ε ≫ p)).app E) ≫
      (derivedGlobalSectionsOver S.X.hom).map
        (((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).map
          (Pi.π (fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩) n)).app E) :=
    (congrArg (fun m => (derivedGlobalSectionsOver S.X.hom).map (m.app E))
      ((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).map_comp (d.ε ≫ p)
        (Pi.π (fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩) n))).trans
      ((congrArg (derivedGlobalSectionsOver S.X.hom).map (NatTrans.comp_app _ _ E)).trans
        ((derivedGlobalSectionsOver S.X.hom).map_comp _ _))
  simp only [T, levelMap]
  refine (congrArg (· ≫ (S.levelTensorRestrictionIso n E hE).hom)
    ((congrArg (fun m => (derivedGlobalSectionsOver S.X.hom).map
      (((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).map m).app E))
      (Category.assoc d.ε p _).symm).trans hs)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.symm ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (Limits.Pi.map_π (fun n => (S.levelTensorRestrictionIso n E hE).hom) n)).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_))))
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (Limits.Pi.lift_comp_π _ n))

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The formation of the level objects commutes with base change**: for perfect `E`, the
derived base change `Mₙ₊₁ ⊗^𝐋_{Aₙ₊₁} Aₙ ⟶ Mₙ` of the transition of the level tower is an
isomorphism. It is [Stacks, Tag 0A1H] for the cartesian square
`tₙ ≫ fₙ₊₁ = fₙ ≫ Spec (Aₙ₊₁ ⟶ Aₙ)`
(`...ExistenceSituation.isIso_derivedBaseChangeMap_comp_levelTensorSheafPullbackMap`),
read on derived global sections over the affine bases. -/
theorem isIso_derivedBaseChangeComparison_levelTensorTransition (n : ℕ)
    (E : DerivedCategory S.X.left.Modules)
    (hE : RingedSpace.IsPerfect (X := S.X.left.toRingedSpace) E) :
    IsIso (derivedBaseChangeComparison (S.ringTransition n) (S.levelTensorTransition n E)) := by
  have hfp := S.finitePresentation_levelStructure (n + 1)
  have : QuasiCompact (S.levelStructure (n + 1)) := hfp.quasiCompact
  have : QuasiSeparated (S.levelStructure (n + 1)) := hfp.quasiSeparated
  have := S.finitelyPresented (n + 1)
  have hF : (S.F (n + 1)).IsQuasicoherent := isQuasicoherent_of_isFinitePresentation _
  have hE' : RingedSpace.IsPerfect (X := (schemeAt S.system S.X (n + 1)).toRingedSpace)
      ((S.levelPullback (n + 1)).obj E) :=
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ E hE
  have hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj
      (S.levelTensorSheaf (n + 1) E)).IsQuasicoherent := fun i =>
    AlgebraicGeometry.TorFormula.isQuasicoherent_homology_derivedTensor _ _ _
      (Stacks.Duality.DerivedPushforward.derivedCategoryB_singleFunctor_obj _ hF)
      (AlgebraicGeometry.ProperFlatBaseChange.isQuasicoherent_homology_of_isPerfect _ hE') i
  exact isIso_derivedBaseChangeComparison_of_isIso_derivedBaseChangeMap (S.ringTransition n)
    (S.levelStructure (n + 1)) (S.levelStructure n) (S.transitionScheme n)
    (S.transitionScheme_comp_levelStructure n) (S.levelTensorSheaf (n + 1) E) hK
    (S.levelTensorSheaf n E) (S.levelTensorSheafPullbackMap n E)
    (S.isIso_derivedBaseChangeMap_comp_levelTensorSheafPullbackMap n E hE)

/-! ### The canonical map, natural in `E` -/

attribute [local instance 10000] HasDerivedCategory.standard in
/-- `RΓ_A(X, iₙ,* ℱₙ ⊗^𝐋 E) ⟶ RΓ_{Aₙ}(Xₙ, ℱₙ ⊗^𝐋 Eₙ)` read over `A`, for an arbitrary `E`: the
single-object comparison and the projection-formula map of [Stacks, Tag 0B53], then the linear
Leray identification. For perfect `E` it is the isomorphism
`AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.levelTensorRestrictionIso`. -/
def levelRestrictionMap (n : ℕ) (E : DerivedCategory S.X.left.Modules) :
    (derivedGlobalSectionsOver S.X.hom).obj
        (((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).obj
          (S.derivedPushforwardSystemOfModel.obj ⟨n⟩)).obj E) ⟶
      S.towerRestriction (fun m => S.levelTensor m E) n :=
  (derivedGlobalSectionsOver S.X.hom).map
      (((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).map
        ((closedImmersionDerivedPushforwardSingleIso (S.closedImmersion n)).hom.app
          (S.F n))).app E) ≫
    (derivedGlobalSectionsOver S.X.hom).map
      (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap
        (S.closedImmersion n).toLRSHom.toShHom (S.levelSheafStandard n) E) ≫
    (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso (S.closedImmersion n)
      S.X.hom (S.levelStructure n) (S.limitProjection n)
        (S.closedImmersion_comp_hom n)).hom.app (S.levelTensorSheaf n E)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- For perfect `E`, `levelRestrictionMap` is the isomorphism `levelTensorRestrictionIso`. -/
theorem levelRestrictionMap_eq (n : ℕ) (E : DerivedCategory S.X.left.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.X.left.toRingedSpace) E) :
    S.levelRestrictionMap n E = (S.levelTensorRestrictionIso n E hE).hom :=
  (S.levelTensorRestrictionIso_hom n E hE).symm

attribute [local instance 10000] HasDerivedCategory.standard in
/-- `levelRestrictionMap` is natural in `E`. -/
theorem levelRestrictionMap_naturality (n : ℕ) {E E' : DerivedCategory S.X.left.Modules}
    (u : E ⟶ E') :
    (derivedGlobalSectionsOver S.X.hom).map
        (((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).obj
          (S.derivedPushforwardSystemOfModel.obj ⟨n⟩)).map u) ≫ S.levelRestrictionMap n E' =
      S.levelRestrictionMap n E ≫
        (ModuleCat.restrictScalars (S.limitProjection n)).mapDerivedCategory.map
          (S.levelTensorMap n u) := by
  have h₁ : ((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).obj
        (S.derivedPushforwardSystemOfModel.obj ⟨n⟩)).map u ≫
      ((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).map
        ((closedImmersionDerivedPushforwardSingleIso (S.closedImmersion n)).hom.app
          (S.F n))).app E' =
      ((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).map
        ((closedImmersionDerivedPushforwardSingleIso (S.closedImmersion n)).hom.app
          (S.F n))).app E ≫
      ((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).obj
        ((derivedPushforward (S.closedImmersion n).toLRSHom.toShHom).obj
          (S.levelSheafStandard n))).map u :=
    ((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).map
      ((closedImmersionDerivedPushforwardSingleIso (S.closedImmersion n)).hom.app
        (S.F n))).naturality u
  have h₂ := Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_natural_right
    (S.closedImmersion n).toLRSHom.toShHom (S.levelSheafStandard n) u
  have h₃ := (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso (S.closedImmersion n)
    S.X.hom (S.levelStructure n) (S.limitProjection n)
      (S.closedImmersion_comp_hom n)).hom.naturality
      (((derivedTensorProductFunctor (schemeAt S.system S.X n).toRingedSpace.sheaf).obj
        (S.levelSheafStandard n)).map ((S.levelPullback n).map u))
  have S1 := functor_map_comp_eq_of_comp_eq (derivedGlobalSectionsOver S.X.hom) h₁
  have S2 := functor_map_comp_eq_of_comp_eq (derivedGlobalSectionsOver S.X.hom) h₂
  exact ((reassoc_of% S1) _).trans ((congrArg _ (((reassoc_of% S2) _).trans
    (congrArg _ h₃))).trans
      ((Category.assoc _ _ _).trans (congrArg _ (Category.assoc _ _ _))).symm)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The map `RΓ(X, K ⊗^𝐋 E) ⟶ RΓ(Xₙ, ℱₙ ⊗^𝐋 Eₙ)` read over `A`, for an arbitrary `E`: `RΓ` of
`levelMap ⊗ E` followed by `levelRestrictionMap`. -/
def DerivedLimitQCoh.tensorLevelMap (d : S.DerivedLimitQCoh)
    (p : d.L ⟶ ∏ᶜ fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩) (n : ℕ)
    (E : DerivedCategory S.X.left.Modules) :
    (derivedGlobalSectionsOver S.X.hom).obj
        (((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).obj d.K).obj E) ⟶
      S.towerRestriction (fun m => S.levelTensor m E) n :=
  (derivedGlobalSectionsOver S.X.hom).map
      (((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).map (S.levelMap d p n)).app E) ≫
    S.levelRestrictionMap n E

attribute [local instance 10000] HasDerivedCategory.standard in
/-- `DerivedLimitQCoh.tensorLevelMap` is natural in `E`. -/
theorem DerivedLimitQCoh.tensorLevelMap_naturality (d : S.DerivedLimitQCoh)
    (p : d.L ⟶ ∏ᶜ fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩) (n : ℕ)
    {E E' : DerivedCategory S.X.left.Modules} (u : E ⟶ E') :
    (derivedGlobalSectionsOver S.X.hom).map
        (((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).obj d.K).map u) ≫
      DerivedLimitQCoh.tensorLevelMap S d p n E' =
    DerivedLimitQCoh.tensorLevelMap S d p n E ≫
      (ModuleCat.restrictScalars (S.limitProjection n)).mapDerivedCategory.map
        (S.levelTensorMap n u) := by
  have h := ((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).map
    (S.levelMap d p n)).naturality u
  have S1 := functor_map_comp_eq_of_comp_eq (derivedGlobalSectionsOver S.X.hom) h
  exact ((reassoc_of% S1) _).trans ((congrArg _ (S.levelRestrictionMap_naturality n u)).trans
    (Category.assoc _ _ _).symm)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The canonical map of [Stacks, Tag 0CTE] (1), as a natural transformation in `E`** over all
of `D(𝒪_X)`: `RΓ(X, K ⊗^𝐋 E) ⊗^𝐋_A Aₙ ⟶ RΓ(Xₙ, ℱₙ ⊗^𝐋 Eₙ)`, the derived base change of
`tensorLevelMap`. It is an isomorphism for perfect `E`
(`...ExistenceSituation.DerivedLimitQCoh.isIso_tensorBaseChange_app`). -/
def DerivedLimitQCoh.tensorBaseChange (d : S.DerivedLimitQCoh)
    (p : d.L ⟶ ∏ᶜ fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩) (n : ℕ) :
    ((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).obj d.K ⋙
        derivedGlobalSectionsOver S.X.hom ⋙
        (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, u, u}
          (S.limitProjection n)).functor) ⟶
      (S.levelPullback n ⋙
        (derivedTensorProductFunctor (schemeAt S.system S.X n).toRingedSpace.sheaf).obj
          (S.levelSheafStandard n) ⋙ derivedGlobalSectionsOver (S.levelStructure n)) where
  app E :=
    derivedBaseChangeComparison (S.limitProjection n) (DerivedLimitQCoh.tensorLevelMap S d p n E)
  naturality _ _ u :=
    (Adjunction.homEquiv_naturality_left_symm _ _ _).symm.trans
      ((congrArg _ (DerivedLimitQCoh.tensorLevelMap_naturality S d p n u)).trans
        (Adjunction.homEquiv_naturality_right_symm _ _ _))

/-! ### [Stacks, Tag 0CTE] -/

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **[Stacks, Tag 0CTE] (1), perfectness**: for `K` as in [Stacks, Tag 0CTD] and `E` perfect,
`M = RΓ(X, K ⊗^𝐋 E)` is a perfect object of `D(A)`. -/
theorem DerivedLimitQCoh.isPerfect_globalSectionsTensor (d : S.DerivedLimitQCoh)
    (E : DerivedCategory S.X.left.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.X.left.toRingedSpace) E) :
    StacksDraft.Perfect.IsPerfect ((derivedGlobalSectionsOver S.X.hom).obj
      (((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).obj d.K).obj E)) :=
  have ⟨p, hp⟩ := DerivedLimitQCoh.exists_isDerivedLimitCone S d
  (DerivedLimitQCoh.isPerfect_and_isIso_baseChange_of S d E hE p hp
    (fun n => S.isIso_derivedBaseChangeComparison_levelTensorTransition n E hE)
    (fun n => S.levelTensorRestrictionIso_comm n E hE)).1

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **[Stacks, Tag 0CTE] (1), the canonical isomorphism**: the canonical map
`RΓ(X, K ⊗^𝐋 E) ⊗^𝐋_A Aₙ ⟶ RΓ(Xₙ, ℱₙ ⊗^𝐋 E|_{Xₙ})` is an isomorphism for perfect `E`. -/
theorem DerivedLimitQCoh.isIso_tensorBaseChange_app (d : S.DerivedLimitQCoh)
    (p : d.L ⟶ ∏ᶜ fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩)
    (hp : S.IsDerivedLimitCone p) (n : ℕ) (E : DerivedCategory S.X.left.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.X.left.toRingedSpace) E) :
    IsIso ((DerivedLimitQCoh.tensorBaseChange S d p n).app E) := by
  have h := (DerivedLimitQCoh.isPerfect_and_isIso_baseChange_of S d E hE p hp
    (fun n => S.isIso_derivedBaseChangeComparison_levelTensorTransition n E hE)
    (fun n => S.levelTensorRestrictionIso_comm n E hE)).2 n
  exact h

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **Stacks Project, Tag 0CTE, part (1).** In Situation [Stacks, Tag 0CTC] let `K` be as in
[Stacks, Tag 0CTD] and let `E` be a perfect object of `D(𝒪_X)`. Then
`M = RΓ(X, K ⊗^𝐋 E)` is a perfect object of `D(A)`, and the canonical map
`M ⊗^𝐋_A Aₙ ⟶ RΓ(Xₙ, ℱₙ ⊗^𝐋 E|_{Xₙ})` is an isomorphism in `D(Aₙ)` for every `n`, with
`E|_{Xₙ}` the derived pullback.

Here `K` is given by the data `d` of
`AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.DerivedLimitQCoh`, the canonical map is
`(DerivedLimitQCoh.tensorBaseChange S d p n).app E`, built from a cone `p` exhibiting
`L = R lim ℱₙ`, and the index `n` stands for the level `n + 1` of the source. Stated at
`HasDerivedCategory.standard` (scoped to this declaration). -/
@[stacks 0CTE "(1)"]
theorem DerivedLimitQCoh.isPerfect_and_isIso_tensorBaseChange (d : S.DerivedLimitQCoh)
    (E : DerivedCategory S.X.left.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.X.left.toRingedSpace) E) :
    StacksDraft.Perfect.IsPerfect ((derivedGlobalSectionsOver S.X.hom).obj
        (((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).obj d.K).obj E)) ∧
      ∀ (p : d.L ⟶ ∏ᶜ fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩),
        S.IsDerivedLimitCone p → ∀ n : ℕ,
          IsIso ((DerivedLimitQCoh.tensorBaseChange S d p n).app E) :=
  ⟨DerivedLimitQCoh.isPerfect_globalSectionsTensor S d E hE,
    fun p hp n => DerivedLimitQCoh.isIso_tensorBaseChange_app S d p hp n E hE⟩

end ExistenceSituation

end AlgebraicGeometry.GrothendieckExistence

end
