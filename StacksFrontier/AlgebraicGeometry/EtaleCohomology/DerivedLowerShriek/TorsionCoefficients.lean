module
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowNaturalTransformations
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowTruncation
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.HigherDerivedFunctors
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedBoundedCohomologicalDimension
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Adjunction
public import StacksFrontier.AlgebraicGeometry.AffineMorphismCohomology.AcyclicQuasiIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.Compactifications
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TrivialityAndGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.SheafifiedCohomologyPresheaf

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CohomologicalBound
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CompactObjects.ExtensionByZeroIsCompact
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.DerivedAdjunction
public import StacksFrontier.Homology.Injectives.Spaltenstein.RightDerivedFunctor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModuleTensor.ProjectionFormulaProper
public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedOfExactFunctor

/-!
# The derived lower shriek on `D(X_étale, Λ)` for a torsion ring `Λ`

Let `f : X ⟶ Y` be a separated morphism of finite type with `Y` quasi-compact, `j` a
compactification of `f` and `Λ` a torsion ring. [Stacks, Tag 0G2A] says that the derived lower
shriek `Rf_! = Rf̄_* ∘ Rj_!` (`Stacks.EtaleCohomology.derivedLowerShriekUnbounded`) has finite
cohomological amplitude on the whole of `D(X_étale, Λ)`. The bounded below case is
`Stacks.EtaleCohomology.exists_bound_derivedLowerShriekUnbounded`; this file treats unbounded
objects. For a torsion ring every sheaf of `Λ`-modules is torsion, so `R^q f̄_* = 0` for
`q > 2d` on the whole category of sheaves of `Λ`-modules (Tag 095U), and [Stacks, Tag 07K7]
bounds `Rf̄_*` on unbounded objects.

## Main results

All names below are in the namespace `Stacks.EtaleCohomology`.

* `isLE_rightDerived_obj_of_isZero_rightDerived`: [Stacks, Tag 07K7] (4)(c)
  on the right, for any right derived functor of a left exact functor out of a category with
  enough injectives whose `n`-th right derived functor vanishes.
* `etaleModuleDerivedDirectImageUnboundedUnitH`: `Rf_*` on `D(-_étale, Λ)`
  as a right derived functor along the localization of the homotopy category.
* `isLE_derivedLowerShriekUnbounded_obj_of_isAddTorsion`: for a torsion
  ring, `E ≤ b` implies `Rf_! E ≤ b + 2d`, granted Tag 095U.
* `isIso_homologyMap_derivedLowerShriekUnbounded_map_truncGEπ_of_isAddTorsion`:
  part (2) of Tag 0G2A on `D(X_étale, Λ)`, granted Tag 095U.

## References

* [Stacks Project, Tag 0G2A](https://stacks.math.columbia.edu/tag/0G2A)
* [Stacks Project, Tag 07K7](https://stacks.math.columbia.edu/tag/07K7)
* [Stacks Project, Tag 095U](https://stacks.math.columbia.edu/tag/095U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u r

attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace Stacks.EtaleCohomology

/-! ### Stacks 07K7 (4) on the right -/

section Generic

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D] [EnoughInjectives C]

/-- **[Stacks, Tag 07K7] (4)(c), the bound on the right.** Let `F : C ⥤ D` be a left exact
functor out of an abelian category with enough injectives such that `R^n F = 0`. For any right
derived functor `RF : D(C) ⥤ D(D)` of `F` and any `E ≤ b`, `RF(E) ≤ b + n - 1`. -/
theorem isLE_rightDerived_obj_of_isZero_rightDerived (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] (n : ℕ) (hn : ∀ A : C, IsZero ((F.rightDerived n).obj A))
    (RF : DerivedCategory C ⥤ DerivedCategory D)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    (E : DerivedCategory C) (b : ℤ) (hE : E.IsLE b) : (RF.obj E).IsLE (b + n - 1) := by
  have := Stacks.Cohomology.CompactExtensionByZero.hasRightDerivedFunctorPlus F
  have hn' : ∀ A : C, IsZero ((DerivedCategory.Plus.homologyFunctor D (n : ℤ)).obj
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj A))) :=
    fun A => (hn A).of_iso
      ((Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard F n).app A)
  exact ((((Functor.hasRightDerivedFunctor_of_isZero_rightDerived F F.rightDerivedFunctorPlus
    F.rightDerivedFunctorPlusUnit F.rightAcyclic
    (Stacks.Cohomology.CompactExtensionByZero.rightAcyclic_iff_computesRightDerived F)
    (Stacks.Cohomology.CompactExtensionByZero.exists_mono_rightAcyclic F) n hn').2.2
      RF α).2 E).2.2.2 b hE)

end Generic

/-! ### `Rf_*` along the homotopy category -/

section DirectImage

variable (Λ : Type r) [Ring Λ] {S T : Scheme.{u}} (p : S ⟶ T)

/-- The derivation unit of `Rf_*` on `D(-_étale, Λ)` read on the homotopy category: the unit
`f_*(K) ⟶ Rf_*(K)` of `Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnbounded`, which is
defined on cochain complexes, descends along the quotient to the homotopy category. -/
def etaleModuleDerivedDirectImageUnboundedUnitH :
    (etaleModuleDirectImage.{u, r} Λ p).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ etaleModuleDerivedDirectImageUnbounded.{u, r} Λ p :=
  CategoryTheory.Quotient.natTransLift _
    (((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((etaleModuleDirectImage.{u, r} Λ p).mapHomotopyCategoryFactors (ComplexShape.up ℤ))
        DerivedCategory.Qh ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso _)).hom ≫
      etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ p ≫
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _).symm _ ≪≫
        Functor.associator _ _ _).hom)

/-- **`Rf_*` on `D(-_étale, Λ)` is a right derived functor along the homotopy category**: its unit
there is invertible at K-injective complexes. -/
instance etaleModuleDerivedDirectImageUnbounded_isRightDerivedFunctorH :
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ p).IsRightDerivedFunctor
      (etaleModuleDerivedDirectImageUnboundedUnitH.{u, r} Λ p)
      (HomotopyCategory.quasiIso (EtaleModules.{u, r} Λ S) (ComplexShape.up ℤ)) := by
  refine
    Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_of_isIso_app_quotient_isKInjective
      Stacks.DerivedFunctor.exists_quasiIso_isKInjective _ _ _ fun I hI ↦ ?_
  have := isIso_etaleModuleDerivedDirectImageUnboundedUnit_app.{u, r} Λ p I hI
  dsimp only [etaleModuleDerivedDirectImageUnboundedUnitH, CategoryTheory.Quotient.natTransLift]
  have h₁ := Iso.isIso_hom (Iso.app ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((etaleModuleDirectImage.{u, r} Λ p).mapHomotopyCategoryFactors (ComplexShape.up ℤ))
        DerivedCategory.Qh ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso (EtaleModules.{u, r} Λ T))) I)
  have h₂ := Iso.isIso_hom (Iso.app
    (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso (EtaleModules.{u, r} Λ S)).symm
        (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ p) ≪≫
      Functor.associator (HomotopyCategory.quotient (EtaleModules.{u, r} Λ S) (ComplexShape.up ℤ))
        DerivedCategory.Qh (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ p)) I)
  exact IsIso.comp_isIso' h₁ (IsIso.comp_isIso' this h₂)

end DirectImage

/-! ### Torsion coefficients -/

section Torsion

variable (Λ : Type r) [Ring Λ]

/-- **Over a torsion ring every sheaf of `Λ`-modules is torsion**: a positive integer `n` kills
`Λ`, hence every section. -/
theorem isTorsionEtaleModule_of_isAddTorsion (hΛ : IsAddTorsion Λ) {X : Scheme.{u}}
    (F : EtaleModules.{u, r} Λ X) : IsTorsionEtaleModule Λ X F := by
  obtain ⟨n, hn, hn0⟩ := exists_nat_cast_eq_zero_of_isTorsion hΛ
  intro V x
  refine ⟨⊤, X.smallEtaleTopology.top_mem V, fun W g _ ↦ ⟨n, hn, ?_⟩⟩
  rw [← Nat.cast_smul_eq_nsmul Λ n, hn0, zero_smul]

/-- **`Rf_*` along a proper morphism has finite cohomological amplitude on `D(-_étale, Λ)` for a
torsion ring `Λ`**, granted Tag 095U. If the fibres of `p` have dimension `≤ d` and `E ≤ b`,
then `Rp_* E ≤ b + 2d`: every sheaf of `Λ`-modules is torsion, so `R^q p_* = 0` for `q > 2d`
on the whole category of sheaves of `Λ`-modules, and Tag 07K7 (4) applies. -/
theorem isLE_etaleModuleDerivedDirectImageUnbounded_obj_of_isAddTorsion
    (h095U : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p] (N : ℕ),
      (∀ t : T, topologicalKrullDim (p.fiber t) ≤ N) →
        ∀ F : Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) r},
          Stacks.Torsion.torsionSheafProperty S.smallEtaleTopology F → ∀ q : ℕ, 2 * N < q →
            IsZero (((etaleAbelianDirectImage.{u, r} p).rightDerived q).obj F))
    (hΛ : IsAddTorsion Λ) {S T : Scheme.{u}} (p : S ⟶ T) [IsProper p] (d : ℕ)
    (hd : ∀ t : T, topologicalKrullDim (p.fiber t) ≤ d)
    (E : DerivedCategory (EtaleModules.{u, r} Λ S)) (b : ℤ) [E.IsLE b] :
    ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ p).obj E).IsLE (b + 2 * d) := by
  have hn : ∀ G : EtaleModules.{u, r} Λ S,
      IsZero (((etaleModuleDirectImage.{u, r} Λ p).rightDerived (2 * d + 1)).obj G) := by
    intro G
    have hG := isLE_etaleModuleDerivedDirectImageUnbounded_singleFunctor_obj.{u, r} Λ h095U p d
      hd G ((isTorsionEtaleModule_iff_torsionSheafProperty_unconditional Λ G).1
        (isTorsionEtaleModule_of_isAddTorsion Λ hΛ G)) 0
    refine (DerivedCategory.isZero_of_isLE ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ p).obj
      ((DerivedCategory.singleFunctor _ 0).obj G)) (0 + 2 * d) ((2 * d + 1 : ℕ) : ℤ)
      (by push_cast; omega)).of_iso ?_
    exact ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
      (etaleModuleDirectImage.{u, r} Λ p) (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ p)
      (etaleModuleDerivedDirectImageUnboundedUnitH.{u, r} Λ p)
      Stacks.DerivedFunctor.exists_quasiIso_isKInjective (2 * d + 1)).app G).symm
  have := isLE_rightDerived_obj_of_isZero_rightDerived (etaleModuleDirectImage.{u, r} Λ p)
    (2 * d + 1) hn (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ p)
    (etaleModuleDerivedDirectImageUnboundedUnitH.{u, r} Λ p) E b inferInstance
  exact DerivedCategory.TStructure.t.isLE_of_le _ (b + ((2 * d + 1 : ℕ) : ℤ) - 1) _
    (by push_cast; omega)

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (j : CompactificationOf (Over.mk f))

/-- The torsion bound on the right for `Rf̄_* ∘ j_!` applied to `E ≤ b`. -/
private theorem isLE_mapDerivedCategory_comp_directImage_obj_of_isAddTorsion
    (h095U : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p] (N : ℕ),
      (∀ t : T, topologicalKrullDim (p.fiber t) ≤ N) →
        ∀ F : Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) r},
          Stacks.Torsion.torsionSheafProperty S.smallEtaleTopology F → ∀ q : ℕ, 2 * N < q →
            IsZero (((etaleAbelianDirectImage.{u, r} p).rightDerived q).obj F))
    (hΛ : IsAddTorsion Λ) (d : ℕ) (hd : ∀ y : Y, topologicalKrullDim (j.toBase.fiber y) ≤ d)
    (E : DerivedCategory (EtaleModules.{u, r} Λ X)) (b : ℤ) [E.IsLE b] :
    (((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapDerivedCategory ⋙
      etaleModuleDerivedDirectImageUnbounded.{u, r} Λ j.toBase).obj E).IsLE (b + 2 * d) := by
  have : ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapDerivedCategory.obj E).IsLE b :=
    Stacks.Homology.isLE_mapDerivedCategory_obj _ E b
  exact isLE_etaleModuleDerivedDirectImageUnbounded_obj_of_isAddTorsion Λ h095U hΛ j.toBase d hd
    ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapDerivedCategory.obj E) b

/-- **[Stacks, Tag 0G2A] part (3), the bound on the right, on `D(X_étale, Λ)` for a torsion ring
`Λ`**, granted Tag 095U. Let `d` bound the dimensions of the fibres of `f̄ : X̄ ⟶ Y`. For every
`E ≤ b` in `D(X_étale, Λ)`, `Rf_! E ≤ b + 2d`. -/
theorem isLE_derivedLowerShriekUnbounded_obj_of_isAddTorsion
    (h095U : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p] (N : ℕ),
      (∀ t : T, topologicalKrullDim (p.fiber t) ≤ N) →
        ∀ F : Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) r},
          Stacks.Torsion.torsionSheafProperty S.smallEtaleTopology F → ∀ q : ℕ, 2 * N < q →
            IsZero (((etaleAbelianDirectImage.{u, r} p).rightDerived q).obj F))
    (hΛ : IsAddTorsion Λ) (d : ℕ) (hd : ∀ y : Y, topologicalKrullDim (j.toBase.fiber y) ≤ d)
    (E : DerivedCategory (EtaleModules.{u, r} Λ X)) (b : ℤ) [E.IsLE b] :
    ((derivedLowerShriekUnbounded.{u, r} f j Λ).obj E).IsLE (b + 2 * d) := by
  have := isLE_mapDerivedCategory_comp_directImage_obj_of_isAddTorsion Λ j h095U hΛ d hd E b
  exact DerivedCategory.TStructure.t.isLE_of_iso
    ((derivedLowerShriekUnboundedIsoMapDerivedCategory.{u, r} Λ j).app E).symm _

/-- **[Stacks, Tag 0G2A] part (2) on `D(X_étale, Λ)` for a torsion ring `Λ`**, granted
Tag 095U. With `d` as in `isLE_derivedLowerShriekUnbounded_obj_of_isAddTorsion`, for every `E`
in `D(X_étale, Λ)` and `i ≥ b` the map `H^i(Rf_! E) ⟶ H^i(Rf_!(τ_{≥ b - 2d} E))` is an
isomorphism: in the image under `Rf_!` of the truncation triangle
`τ_{< b - 2d} E ⟶ E ⟶ τ_{≥ b - 2d} E ⟶` the first vertex lives in degrees `≤ b - 1`. -/
theorem isIso_homologyMap_derivedLowerShriekUnbounded_map_truncGEπ_of_isAddTorsion
    (h095U : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p] (N : ℕ),
      (∀ t : T, topologicalKrullDim (p.fiber t) ≤ N) →
        ∀ F : Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) r},
          Stacks.Torsion.torsionSheafProperty S.smallEtaleTopology F → ∀ q : ℕ, 2 * N < q →
            IsZero (((etaleAbelianDirectImage.{u, r} p).rightDerived q).obj F))
    (hΛ : IsAddTorsion Λ) (d : ℕ) (hd : ∀ y : Y, topologicalKrullDim (j.toBase.fiber y) ≤ d)
    (E : DerivedCategory (EtaleModules.{u, r} Λ X)) (b i : ℤ) (hi : b ≤ i) :
    IsIso ((DerivedCategory.homologyFunctor _ i).map
      ((derivedLowerShriekUnbounded.{u, r} f j Λ).map
        ((DerivedCategory.TStructure.t.truncGEπ (b - 2 * d)).app E))) := by
  let := etaleModuleDerivedDirectImageUnboundedCommShift.{u, r} Λ j.toBase
  have := etaleModuleDerivedDirectImageUnbounded_isTriangulated.{u, r} Λ j.toBase
  let G := (etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapDerivedCategory ⋙
    etaleModuleDerivedDirectImageUnbounded.{u, r} Λ j.toBase
  refine (NatIso.isIso_map_iff (Functor.isoWhiskerRight
    (derivedLowerShriekUnboundedIsoMapDerivedCategory.{u, r} Λ j)
    (DerivedCategory.homologyFunctor _ i))
      ((DerivedCategory.TStructure.t.truncGEπ (b - 2 * d)).app E)).2 ?_
  let T := (DerivedCategory.TStructure.t.triangleLTGE (b - 2 * d)).obj E
  have hT : G.mapTriangle.obj T ∈ distTriang _ := G.map_distinguished _
    (DerivedCategory.TStructure.t.triangleLTGE_distinguished (b - 2 * d) E)
  have : ((DerivedCategory.TStructure.t.truncLT (b - 2 * d)).obj E).IsLE (b - 2 * d - 1) :=
    DerivedCategory.TStructure.t.isLE_truncLT_obj E (b - 2 * d) (b - 2 * d - 1) (by omega)
  have hLE' : (G.mapTriangle.obj T).obj₁.IsLE (b - 1) := by
    have : DerivedCategory.TStructure.t.IsLE (G.mapTriangle.obj T).obj₁ (b - 2 * d - 1 + 2 * d) :=
      isLE_mapDerivedCategory_comp_directImage_obj_of_isAddTorsion Λ j h095U hΛ d hd
      ((DerivedCategory.TStructure.t.truncLT (b - 2 * d)).obj E) (b - 2 * d - 1)
    exact DerivedCategory.TStructure.t.isLE_of_le _ (b - 2 * d - 1 + 2 * d) (b - 1) (by omega)
  exact DerivedCategory.isIso_homologyMap_mor₂_of_isLE₁ _ hT i (b - 1) hLE' (by omega)

end Torsion

end Stacks.EtaleCohomology

end
