module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModulesConstantRing
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowCoreflection
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowTruncation
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Triangulated
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.IteratedRefinement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.Compactifications
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TrivialityAndGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.LowerShriekComposition
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedCohomologicalDimensionPlus
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedSerreInducedTStructure
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModules
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowNaturalTransformations
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Bounded
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness

/-!
# The derived lower shriek has finite cohomological amplitude

Let `f : X ⟶ Y` be a separated morphism of finite type with `Y` quasi-compact, `j : X ⟶ X̄` a
compactification of `X` over `Y` and `Λ` a ring. [Stacks, Tag 0G2A] says that the derived lower
shriek `Rf_! = Rf̄_* ∘ Rj_!` (`Stacks.EtaleCohomology.derivedLowerShriekUnbounded`) is bounded:
there is an integer `N` such that for `E` in `D⁺_{tors}(X_étale, Λ)`

1. `H^i(Rf_!(τ_{≤ a} E)) ⟶ H^i(Rf_! E)` is an isomorphism for `i ≤ a`,
2. `H^i(Rf_! E) ⟶ H^i(Rf_!(τ_{≥ b - N} E))` is an isomorphism for `i ≥ b`,
3. if `H^i(E) = 0` for `i ∉ [a, b]`, then `H^i(Rf_! E) = 0` for `i ∉ [a, b + N]`.

Part (1), and the lower half of part (3), hold for every object of `D(X_étale, Λ)` and need no
input: `Rj_!` is exact and `Rf̄_*` is a right derived functor. The upper half of part (3), and
part (2), rest on the vanishing `R^q f̄_* F = 0` for torsion abelian sheaves `F` and `q > 2d`,
`d` a bound for the dimensions of the fibres of `f̄` (Tags 0A3V and 095U); `N = 2d`.

## Main results

* `Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnbounded_obj_isGE`: `Rf_*` on
  `D(-_étale, Λ)` preserves the objects which are `≥ n`.
* `Stacks.EtaleCohomology.isIso_homologyMap_derivedLowerShriekUnbounded_map_truncLEι`: part (1).
* `Stacks.EtaleCohomology.isLE_etaleModuleDerivedDirectImageUnbounded_singleFunctor_obj`:
  granted Tag 095U, `Rf̄_*` of a torsion sheaf placed in degree `q` lives in degrees `≤ q + 2d`.
* `Stacks.EtaleCohomology.exists_bound_derivedLowerShriekUnbounded`: Tag 0G2A on `D⁺_{tors}`,
  granted Tag 095U.

## References

* [Stacks Project, Tag 0G2A](https://stacks.math.columbia.edu/tag/0G2A)
* [Stacks Project, Tag 095U](https://stacks.math.columbia.edu/tag/095U)
* [Stacks Project, Tag 0A3V](https://stacks.math.columbia.edu/tag/0A3V)
* [Stacks Project, Tag 07K7](https://stacks.math.columbia.edu/tag/07K7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.CompactificationOf

attribute [local instance] HasDerivedCategory.standard

universe u r

attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ]

/-! ### Forgetting the module structure detects bounds -/

section Forget

variable {S : Scheme.{u}}

/-- A cohomology object of `D(S_étale, Λ)` vanishes as soon as the corresponding cohomology
object of the underlying complex of abelian sheaves does: forgetting the module structure is
exact, additive and reflects isomorphisms. -/
theorem isZero_homology_of_isZero_homology_etaleModuleForgetDerived
    (K : DerivedCategory (EtaleModules.{u, r} Λ S)) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((etaleModuleForgetDerived.{u, r} Λ S).obj K))) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj K) := by
  have h' : IsZero ((etaleModuleForgetAb.{u, r} Λ S).obj
      ((DerivedCategory.homologyFunctor _ i).obj K)) :=
    h.of_iso (((etaleModuleForgetAb.{u, r} Λ S).mapDerivedCategoryHomologyIso i).app K).symm
  have h₁ : IsIso ((etaleModuleForgetAb.{u, r} Λ S).map
      (0 : (DerivedCategory.homologyFunctor _ i).obj K ⟶
        (DerivedCategory.homologyFunctor _ i).obj K)) := by
    rw [Functor.map_zero, ← (IsZero.iff_id_eq_zero _).mp h']
    infer_instance
  have h₂ := isIso_of_reflects_iso (0 : (DerivedCategory.homologyFunctor _ i).obj K ⟶
    (DerivedCategory.homologyFunctor _ i).obj K)
    (etaleModuleForgetAb.{u, r} Λ S)
  rw [IsZero.iff_id_eq_zero, ← IsIso.hom_inv_id (0 : (DerivedCategory.homologyFunctor _ i).obj K ⟶
    (DerivedCategory.homologyFunctor _ i).obj K), zero_comp]

/-- An object of `D(S_étale, Λ)` is `≥ n` as soon as its underlying complex of abelian sheaves
is. -/
theorem isGE_of_isGE_etaleModuleForgetDerived (K : DerivedCategory (EtaleModules.{u, r} Λ S))
    (n : ℤ) (h : ((etaleModuleForgetDerived.{u, r} Λ S).obj K).IsGE n) : K.IsGE n := by
  rw [DerivedCategory.isGE_iff] at h ⊢
  exact fun i hi ↦ isZero_homology_of_isZero_homology_etaleModuleForgetDerived Λ K i (h i hi)

/-- An object of `D(S_étale, Λ)` is `≤ n` as soon as its underlying complex of abelian sheaves
is. -/
theorem isLE_of_isLE_etaleModuleForgetDerived (K : DerivedCategory (EtaleModules.{u, r} Λ S))
    (n : ℤ) (h : ((etaleModuleForgetDerived.{u, r} Λ S).obj K).IsLE n) : K.IsLE n := by
  rw [DerivedCategory.isLE_iff] at h ⊢
  exact fun i hi ↦ isZero_homology_of_isZero_homology_etaleModuleForgetDerived Λ K i (h i hi)

end Forget

/-! ### Left t-exactness of `Rf_*` -/

/-- **`Rf_*` on `D(-_étale, Λ)` is left t-exact**: it carries objects `≥ n` to objects `≥ n`.
Forgetting the module structure commutes with `Rf_*`
(`Stacks.EtaleCohomology.etaleModuleDerivedDirectImageForgetIsoUnconditional`), and the unbounded
derived direct image of abelian sheaves is left t-exact. -/
theorem etaleModuleDerivedDirectImageUnbounded_obj_isGE {S T : Scheme.{u}} (p : S ⟶ T)
    (K : DerivedCategory (EtaleModules.{u, r} Λ S)) (n : ℤ) [K.IsGE n] :
    ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ p).obj K).IsGE n := by
  apply isGE_of_isGE_etaleModuleForgetDerived
  have : ((etaleModuleForgetDerived.{u, r} Λ S).obj K).IsGE n :=
    Functor.isGE_obj_mapDerivedCategory (etaleModuleForgetAb.{u, r} Λ S) K n inferInstance
  have : ((etaleModuleForgetDerived.{u, r} Λ S ⋙ etaleAbelianDerivedDirectImage.{u, r} p).obj
      K).IsGE n :=
    Stacks.DerivedFunctor.isGE_totalRightDerived_obj (etaleAbelianDirectImage.{u, r} p)
      ((etaleModuleForgetDerived.{u, r} Λ S).obj K) n
  exact DerivedCategory.TStructure.t.isGE_of_iso
    ((etaleModuleDerivedDirectImageForgetIsoUnconditional.{u, r} Λ p).app K).symm n

/-! ### `Rf_!` as an exact functor -/

section LowerShriek

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (j : CompactificationOf (Over.mk f))

/-- `Rf_! = Rf̄_* ∘ Rj_!` with `Rj_!` replaced by extension by zero applied degreewise. -/
def derivedLowerShriekUnboundedIsoMapDerivedCategory :
    derivedLowerShriekUnbounded.{u, r} f j Λ ≅
      (etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapDerivedCategory ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, r} Λ j.toBase :=
  Functor.isoWhiskerRight (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ j.immersion) _

/-- The `Rf_!` of a morphism has an invertible `i`-th cohomology iff the `i`-th cohomology of
the same morphism under `Rf̄_* ∘ (j_!)` does. -/
private theorem isIso_homologyMap_derivedLowerShriekUnbounded_map_iff
    {K L : DerivedCategory (EtaleModules.{u, r} Λ X)} (φ : K ⟶ L) (i : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor _ i).map
      ((derivedLowerShriekUnbounded.{u, r} f j Λ).map φ)) ↔
    IsIso ((DerivedCategory.homologyFunctor _ i).map
      (((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapDerivedCategory ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, r} Λ j.toBase).map φ)) :=
  NatIso.isIso_map_iff (Functor.isoWhiskerRight
    (derivedLowerShriekUnboundedIsoMapDerivedCategory.{u, r} Λ j)
    (DerivedCategory.homologyFunctor _ i)) φ

/-- `Rf̄_* ∘ (j_!)` carries objects `≥ n` of `D(X_étale, Λ)` to objects `≥ n`. -/
private theorem isGE_obj_extensionByZero_comp_directImage
    (K : DerivedCategory (EtaleModules.{u, r} Λ X)) (n : ℤ) [K.IsGE n] :
    (((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapDerivedCategory ⋙
      etaleModuleDerivedDirectImageUnbounded.{u, r} Λ j.toBase).obj K).IsGE n :=
  have : ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapDerivedCategory.obj K).IsGE n :=
    Functor.isGE_obj_mapDerivedCategory _ K n inferInstance
  etaleModuleDerivedDirectImageUnbounded_obj_isGE.{u, r} Λ j.toBase _ n

/-- **`Rf_!` is left t-exact**: it carries objects `≥ n` of `D(X_étale, Λ)` to objects `≥ n`. -/
theorem isGE_derivedLowerShriekUnbounded_obj (K : DerivedCategory (EtaleModules.{u, r} Λ X))
    (n : ℤ) [K.IsGE n] : ((derivedLowerShriekUnbounded.{u, r} f j Λ).obj K).IsGE n := by
  have := isGE_obj_extensionByZero_comp_directImage.{u, r} Λ j K n
  exact DerivedCategory.TStructure.t.isGE_of_iso
    ((derivedLowerShriekUnboundedIsoMapDerivedCategory.{u, r} Λ j).app K).symm n

/-- **[Stacks, Tag 0G2A], part (1).** For every `E` in `D(X_étale, Λ)` and every `i ≤ a`, the map
`H^i(Rf_!(τ_{≤ a} E)) ⟶ H^i(Rf_! E)` is an isomorphism: in the image under `Rf_!` of the
truncation triangle `τ_{≤ a} E ⟶ E ⟶ τ_{≥ a + 1} E ⟶`, the third vertex is `≥ a + 1`. -/
theorem isIso_homologyMap_derivedLowerShriekUnbounded_map_truncLEι
    (E : DerivedCategory (EtaleModules.{u, r} Λ X)) (a i : ℤ) (hi : i ≤ a) :
    IsIso ((DerivedCategory.homologyFunctor _ i).map
      ((derivedLowerShriekUnbounded.{u, r} f j Λ).map
        ((DerivedCategory.TStructure.t.truncLEι a).app E))) := by
  let G := (etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapDerivedCategory ⋙
    etaleModuleDerivedDirectImageUnbounded.{u, r} Λ j.toBase
  let := etaleModuleDerivedDirectImageUnboundedCommShift.{u, r} Λ j.toBase
  have := etaleModuleDerivedDirectImageUnbounded_isTriangulated.{u, r} Λ j.toBase
  refine (isIso_homologyMap_derivedLowerShriekUnbounded_map_iff.{u, r} Λ j _ i).2 ?_
  let T := (DerivedCategory.TStructure.t.triangleLEGE a (a + 1) rfl).obj E
  have hT : G.mapTriangle.obj T ∈ distTriang _ := G.map_distinguished _
    (DerivedCategory.TStructure.t.triangleLEGE_distinguished a (a + 1) rfl E)
  have hGE : (G.mapTriangle.obj T).obj₃.IsGE (a + 1) :=
    isGE_obj_extensionByZero_comp_directImage.{u, r} Λ j
      ((DerivedCategory.TStructure.t.truncGE (a + 1)).obj E) (a + 1)
  exact DerivedCategory.isIso_homologyMap_mor₁_of_isGE₃ _ hT i (a + 1) hGE (by omega)

end LowerShriek

/-! ### The bound on the right, granted Tag 095U -/

section Bound

/-- **`Rf_*` of a torsion sheaf placed in degree `q` lives in degrees `≤ q + 2d`**, granted
Tag 095U (`h095U`), for a proper morphism `p : S ⟶ T` all of whose fibres have dimension
`≤ d`: on underlying abelian complexes `H^i(Rp_*(F[0])) = R^i p_* F`, which vanishes for
`i > 2d`. -/
theorem isLE_etaleModuleDerivedDirectImageUnbounded_singleFunctor_obj
    (h095U : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p] (N : ℕ),
      (∀ t : T, topologicalKrullDim (p.fiber t) ≤ N) →
        ∀ F : Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) r},
          Stacks.Torsion.torsionSheafProperty S.smallEtaleTopology F → ∀ q : ℕ, 2 * N < q →
            IsZero (((etaleAbelianDirectImage.{u, r} p).rightDerived q).obj F))
    {S T : Scheme.{u}} (p : S ⟶ T) [IsProper p] (d : ℕ)
    (hd : ∀ t : T, topologicalKrullDim (p.fiber t) ≤ d) (F : EtaleModules.{u, r} Λ S)
    (hF : Stacks.Torsion.torsionSheafProperty S.smallEtaleTopology
      ((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ S).obj F)) (q : ℤ) :
    ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ p).obj
      ((DerivedCategory.singleFunctor _ q).obj F)).IsLE (q + 2 * d) := by
  let := etaleModuleDerivedDirectImageUnboundedCommShift.{u, r} Λ p
  -- the case `q = 0`
  have h0 : ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ p).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)).IsLE (2 * d) := by
    apply isLE_of_isLE_etaleModuleForgetDerived
    rw [DerivedCategory.isLE_iff]
    intro i hi
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, (m : ℤ) = i := ⟨i.toNat, by omega⟩
    refine (h095U p d hd _ hF m (by omega)).of_iso ?_
    exact (DerivedCategory.homologyFunctor _ (m : ℤ)).mapIso
        (((etaleModuleDerivedDirectImageForgetIsoUnconditional.{u, r} Λ p).app _) ≪≫
          (etaleAbelianDerivedDirectImage.{u, r} p).mapIso
            (((etaleModuleForgetAb.{u, r} Λ S).mapDerivedCategorySingleFunctor 0).app F)) ≪≫
      (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
        (etaleAbelianDirectImage.{u, r} p) (etaleAbelianDerivedDirectImage.{u, r} p)
        (etaleAbelianDerivedDirectImageUnit.{u, r} p)
        Stacks.DerivedFunctor.exists_quasiIso_isKInjective m).app
          ((etaleModuleForgetAb.{u, r} Λ S).obj F)
  -- shift to degree `q`
  have hshift : DerivedCategory.TStructure.t.IsLE
      ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ p ⋙
        shiftFunctor (DerivedCategory (EtaleModules.{u, r} Λ T)) (-q)).obj
          (((DerivedCategory.singleFunctors _).functor 0).obj F)) (q + 2 * d) :=
    DerivedCategory.TStructure.t.isLE_shift
    ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ p).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)) (2 * d) (-q) (q + 2 * d) (by omega)
  exact DerivedCategory.TStructure.t.isLE_of_iso
    ((((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ p).commShiftIso (-q)).app _).symm ≪≫
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ p).mapIso
        (((DerivedCategory.singleFunctors _).shiftIso (-q) q 0 (by omega)).app F))
    (q + 2 * d)

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (j : CompactificationOf (Over.mk f))

/-- **[Stacks, Tag 0G2A], part (3), the bound on the right, granted Tag 095U.** Let `d` bound the
dimensions of the fibres of `f̄ : X̄ ⟶ Y`. For `E` in `D⁺_{tors}(X_étale, Λ)` with `E ≤ b`,
`Rf_! E ≤ b + 2d`.

The proof is by induction on the length of `E`, through the truncation triangles
(`Stacks.BoundedCohomologicalDimension.isLE_map_obj_of_cohomology_mem`): for a torsion sheaf
`M` placed in degree `q`, `Rf_!(M[-q]) = Rf̄_*((j_! M)[-q])` lives in degrees `≤ q + 2d` because
`j_! M` is torsion (`isLE_etaleModuleDerivedDirectImageUnbounded_singleFunctor_obj`). -/
theorem isLE_derivedLowerShriekUnbounded_obj_of_fibreBound
    (h095U : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p] (N : ℕ),
      (∀ t : T, topologicalKrullDim (p.fiber t) ≤ N) →
        ∀ F : Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) r},
          Stacks.Torsion.torsionSheafProperty S.smallEtaleTopology F → ∀ q : ℕ, 2 * N < q →
            IsZero (((etaleAbelianDirectImage.{u, r} p).rightDerived q).obj F))
    (d : ℕ) (hd : ∀ y : Y, topologicalKrullDim (j.toBase.fiber y) ≤ d)
    (E : DerivedCategory (EtaleModules.{u, r} Λ X))
    (hE : DerivedCategoryB.derivedCategoryBPlus (IsTorsionEtaleModule.{u, r} Λ X) E) (b : ℤ)
    [E.IsLE b] : ((derivedLowerShriekUnbounded.{u, r} f j Λ).obj E).IsLE (b + 2 * d) := by
  obtain ⟨⟨a, ha⟩, hB⟩ := hE
  have hGE : E.IsGE a := (DerivedCategory.isGE_iff E a).2 ha
  let := etaleModuleDerivedDirectImageUnboundedCommShift.{u, r} Λ j.toBase
  have := etaleModuleDerivedDirectImageUnbounded_isTriangulated.{u, r} Λ j.toBase
  let G := (etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapDerivedCategory ⋙
    etaleModuleDerivedDirectImageUnbounded.{u, r} Λ j.toBase
  suffices h : (G.obj E).IsLE (b + 2 * d) from
    DerivedCategory.TStructure.t.isLE_of_iso
      ((derivedLowerShriekUnboundedIsoMapDerivedCategory.{u, r} Λ j).app E).symm _
  by_cases hab : b < a
  · exact DerivedCategory.TStructure.t.isLE_of_isZero
      (G.map_isZero (DerivedCategory.TStructure.t.isZero E b a hab)) _
  have hSingle : ∀ (q : ℤ) (M : EtaleModules.{u, r} Λ X), IsTorsionEtaleModule.{u, r} Λ X M →
      ((DerivedCategory.Plus.ι ⋙ G).obj
        ((DerivedCategory.Plus.singleFunctor _ q).obj M)).IsLE (q + 2 * d) := by
    intro q M hM
    have hM' : Stacks.Torsion.torsionSheafProperty j.space.smallEtaleTopology
        ((etaleModuleForgetAb.{u, r} Λ j.space).obj
          ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).obj M)) :=
      Stacks.Torsion.torsionSheafProperty_of_iso _
        (asIso ((etaleModuleExtensionByZeroForget.{u, r} Λ j.immersion).app M))
        (torsionSheafProperty_extensionByZero.{u, r} j.immersion
          ((etaleModuleForgetAb.{u, r} Λ X).obj M) hM)
    have : ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ j.toBase).obj
        ((etaleModuleExtensionByZero.{u, r} Λ j.immersion ⋙
          DerivedCategory.singleFunctor _ q).obj M)).IsLE (q + 2 * d) :=
      isLE_etaleModuleDerivedDirectImageUnbounded_singleFunctor_obj.{u, r} Λ h095U
        j.toBase d hd _ hM' q
    exact DerivedCategory.TStructure.t.isLE_of_iso
      ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ j.toBase).mapIso
        (((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapDerivedCategorySingleFunctor
          q).app M)).symm _
  have key := Stacks.BoundedCohomologicalDimension.isLE_map_obj_of_cohomology_mem
    (DerivedCategory.Plus.ι ⋙ G) (IsTorsionEtaleModule.{u, r} Λ X)
    (isWeakSerreClass_isTorsionEtaleModule.{u, r} Λ (X := X)).toIsClosedUnderIsomorphisms (2 * d)
    hSingle
  obtain ⟨n, hn⟩ : ∃ n : ℕ, a + n = b := ⟨(b - a).toNat, by omega⟩
  let E' : DerivedCategory.Plus (EtaleModules.{u, r} Λ X) := ⟨E, a, hGE⟩
  have h₁ : E'.IsGE a := (DerivedCategory.Plus.isGE_ι_obj_iff E' a).1 hGE
  have h₂ : E'.IsLE (a + n) := (DerivedCategory.Plus.isLE_ι_obj_iff E' _).1 (by
    rw [hn]
    change E.IsLE b
    infer_instance)
  have h := key a n E' h₁ h₂ (fun q _ _ ↦ hB q)
  rw [hn] at h
  exact h

/-- **[Stacks, Tag 0G2A], part (2), granted Tag 095U.** With `d` as in
`isLE_derivedLowerShriekUnbounded_obj_of_fibreBound`, for `E` in `D⁺_{tors}(X_étale, Λ)` and
`i ≥ b` the map `H^i(Rf_! E) ⟶ H^i(Rf_!(τ_{≥ b - 2d} E))` is an isomorphism: in the image
under `Rf_!` of the truncation triangle `τ_{< b - 2d} E ⟶ E ⟶ τ_{≥ b - 2d} E ⟶` the first vertex
lives in degrees `≤ b - 1` by part (3). -/
theorem isIso_homologyMap_derivedLowerShriekUnbounded_map_truncGEπ
    (h095U : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p] (N : ℕ),
      (∀ t : T, topologicalKrullDim (p.fiber t) ≤ N) →
        ∀ F : Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) r},
          Stacks.Torsion.torsionSheafProperty S.smallEtaleTopology F → ∀ q : ℕ, 2 * N < q →
            IsZero (((etaleAbelianDirectImage.{u, r} p).rightDerived q).obj F))
    (d : ℕ) (hd : ∀ y : Y, topologicalKrullDim (j.toBase.fiber y) ≤ d)
    (E : DerivedCategory (EtaleModules.{u, r} Λ X))
    (hE : DerivedCategoryB.derivedCategoryBPlus (IsTorsionEtaleModule.{u, r} Λ X) E)
    (b i : ℤ) (hi : b ≤ i) :
    IsIso ((DerivedCategory.homologyFunctor _ i).map
      ((derivedLowerShriekUnbounded.{u, r} f j Λ).map
        ((DerivedCategory.TStructure.t.truncGEπ (b - 2 * d)).app E))) := by
  let := etaleModuleDerivedDirectImageUnboundedCommShift.{u, r} Λ j.toBase
  have := etaleModuleDerivedDirectImageUnbounded_isTriangulated.{u, r} Λ j.toBase
  let G := (etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapDerivedCategory ⋙
    etaleModuleDerivedDirectImageUnbounded.{u, r} Λ j.toBase
  refine (isIso_homologyMap_derivedLowerShriekUnbounded_map_iff.{u, r} Λ j _ i).2 ?_
  let T := (DerivedCategory.TStructure.t.triangleLTGE (b - 2 * d)).obj E
  have hT : G.mapTriangle.obj T ∈ distTriang _ := G.map_distinguished _
    (DerivedCategory.TStructure.t.triangleLTGE_distinguished (b - 2 * d) E)
  obtain ⟨⟨a, ha⟩, hB⟩ := hE
  have hGE : E.IsGE a := (DerivedCategory.isGE_iff E a).2 ha
  have hT₁ : DerivedCategoryB.derivedCategoryBPlus (IsTorsionEtaleModule.{u, r} Λ X)
      ((DerivedCategory.TStructure.t.truncLT (b - 2 * d)).obj E) :=
    ⟨⟨a, (DerivedCategory.isGE_iff _ a).1 inferInstance⟩,
      DerivedCategoryB.derivedCategoryB_truncLT_obj _
        (@WeakSerre.isWeakSerre_of_isWeakSerreClass _ _ _ _
          (isWeakSerreClass_isTorsionEtaleModule.{u, r} Λ (X := X))) _ E hB⟩
  have hLE := isLE_derivedLowerShriekUnbounded_obj_of_fibreBound.{u, r} Λ j h095U d hd _ hT₁
    (b - 2 * d - 1)
  have hLE' : (G.mapTriangle.obj T).obj₁.IsLE (b - 1) := by
    have : (G.obj ((DerivedCategory.TStructure.t.truncLT (b - 2 * d)).obj E)).IsLE
        (b - 2 * d - 1 + 2 * d) :=
      DerivedCategory.TStructure.t.isLE_of_iso
        ((derivedLowerShriekUnboundedIsoMapDerivedCategory.{u, r} Λ j).app
          ((DerivedCategory.TStructure.t.truncLT (b - 2 * d)).obj E)) _
    have : DerivedCategory.TStructure.t.IsLE ((G.mapTriangle.obj T).obj₁)
        (b - 2 * d - 1 + 2 * d) := this
    exact DerivedCategory.TStructure.t.isLE_of_le _ (b - 2 * d - 1 + 2 * d) (b - 1) (by omega)
  exact DerivedCategory.isIso_homologyMap_mor₂_of_isLE₁ _ hT i (b - 1) hLE' (by omega)

end Bound

/-! ### The statement of the tag -/

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- **[Stacks, Tag 0G2A] on `D⁺_{tors}`, granted Tag 095U.** Let `f : X ⟶ Y` be a separated
morphism of finite type with `Y` quasi-compact, `j` a compactification of `f` and `Λ` a ring.
There is an integer `N` such that for every `E` in `D⁺_{tors}(X_étale, Λ)`:

1. `H^i(Rf_!(τ_{≤ a} E)) ⟶ H^i(Rf_! E)` is an isomorphism for `i ≤ a`;
2. `H^i(Rf_! E) ⟶ H^i(Rf_!(τ_{≥ b - N} E))` is an isomorphism for `i ≥ b`;
3. if `H^i(E) = 0` for `i ∉ [a, b]` with `-∞ ≤ a ≤ b ≤ ∞`, then `H^i(Rf_! E) = 0` for
   `i ∉ [a, b + N]` — stated as the two halves `E ≥ a ⟹ Rf_! E ≥ a` and
   `E ≤ b ⟹ Rf_! E ≤ b + N`, an infinite end point being the absence of the corresponding half.

`N = 2d` for `d` a bound on the fibre dimensions of `f̄ : X̄ ⟶ Y` (Tag 0A3V). The case of
`D(X_étale, Λ)` for a torsion ring `Λ` is not covered here.

`h095U` is Stacks Tag 095U (a proper morphism with fibres of dimension `≤ N` has `R^q f_* F = 0`
for torsion `F` and `q > 2N`). -/
theorem exists_bound_derivedLowerShriekUnbounded [CompactSpace Y]
    (h095U : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p] (N : ℕ),
      (∀ t : T, topologicalKrullDim (p.fiber t) ≤ N) →
        ∀ F : Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) r},
          Stacks.Torsion.torsionSheafProperty S.smallEtaleTopology F → ∀ q : ℕ, 2 * N < q →
            IsZero (((etaleAbelianDirectImage.{u, r} p).rightDerived q).obj F))
    (j : CompactificationOf (Over.mk f)) :
    ∃ N : ℕ, ∀ E : DerivedCategory (EtaleModules.{u, r} Λ X),
      DerivedCategoryB.derivedCategoryBPlus (IsTorsionEtaleModule.{u, r} Λ X) E →
      (∀ a i : ℤ, i ≤ a → IsIso ((DerivedCategory.homologyFunctor _ i).map
        ((derivedLowerShriekUnbounded.{u, r} f j Λ).map
          ((DerivedCategory.TStructure.t.truncLEι a).app E)))) ∧
      (∀ b i : ℤ, b ≤ i → IsIso ((DerivedCategory.homologyFunctor _ i).map
        ((derivedLowerShriekUnbounded.{u, r} f j Λ).map
          ((DerivedCategory.TStructure.t.truncGEπ (b - N)).app E)))) ∧
      (∀ a : ℤ, E.IsGE a → ((derivedLowerShriekUnbounded.{u, r} f j Λ).obj E).IsGE a) ∧
      (∀ b : ℤ, E.IsLE b → ((derivedLowerShriekUnbounded.{u, r} f j Λ).obj E).IsLE (b + N)) := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_fiber_le j.toBase
  refine ⟨2 * d, fun E hE ↦ ⟨fun a i hi ↦ ?_, fun b i hi ↦ ?_, fun a ha ↦ ?_, fun b hb ↦ ?_⟩⟩
  · exact isIso_homologyMap_derivedLowerShriekUnbounded_map_truncLEι.{u, r} Λ j E a i hi
  · exact_mod_cast isIso_homologyMap_derivedLowerShriekUnbounded_map_truncGEπ.{u, r} Λ j h095U d
      hd E hE b i hi
  · exact isGE_derivedLowerShriekUnbounded_obj.{u, r} Λ j E a
  · exact_mod_cast isLE_derivedLowerShriekUnbounded_obj_of_fibreBound.{u, r} Λ j h095U d hd E
      hE b

end Stacks.EtaleCohomology

end
