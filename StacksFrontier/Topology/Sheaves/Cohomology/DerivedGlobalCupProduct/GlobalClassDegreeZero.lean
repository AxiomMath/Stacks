module

public import Mathlib.Algebra.Homology.Factorizations.CM5a
public import StacksFrontier.Algebra.Homology.RightDerivedCoEdge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionExact
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedGlobalCupProduct.UnitEvaluation

/-!
# Derived global sections in degree zero

Let `(X, 𝒪_X)` be a ringed space and `N` a complex of `𝒪_X`-modules concentrated in degrees
`≥ 0`. Global sections are left exact, so the degree-zero cohomology of the derived global
sections `RΓ(X, N)` is the kernel of `Γ(X, N⁰) ⟶ Γ(X, N¹)`: the comparison `Γ(X, N) ⟶ RΓ(X, N)`
is an isomorphism on `H⁰`, and the class map from global cocycles of `N` in degree `0` to
`H⁰(X, N)` is bijective.

The proof is the usual one: `N` has a quasi-isomorphism `N ⟶ I` into a complex of injectives
concentrated in degrees `≥ 0`, which computes `RΓ`, and a left exact functor sends the
quasi-isomorphism `N ⟶ I` of complexes in degrees `≥ 0` to a map that is bijective on `H⁰`, both
`H⁰` being kernels of the first differential.

## Main results

* `HomologicalComplex.isIso_homologyMap_mapHomologicalComplex_zero_of_isStrictlyGE`: a left
  exact additive functor carries a quasi-isomorphism in degree `0` between complexes in degrees
  `≥ 0` to an isomorphism on `H⁰`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.isIso_homologyMap_sectionsUnitQ_zero`: the
  comparison `Γ(X, N) ⟶ RΓ(X, N)` is an isomorphism on `H⁰` for `N` in degrees `≥ 0`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.globalClass_smul`: the class map is linear.
* `Stacks.Cohomology.DerivedGlobalCupProduct.bijective_globalClass_zero`: every class of
  `H⁰(X, N)` is the class of a unique global cocycle of `N` in degree `0`.

## References

* [Stacks Project, Tag 013K](https://stacks.math.columbia.edu/tag/013K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.GlobalKunneth Stacks.Cohomology.DerivedSectionsLeray

universe u

namespace HomologicalComplex

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

/-- In a complex concentrated in degrees `≥ 0` the projection from the cycles in degree `0` to the
homology is an isomorphism. -/
theorem isIso_homologyπ_zero (K : CochainComplex C ℤ) (h : K.d (-1) 0 = 0) :
    IsIso (K.homologyπ 0) :=
  K.isIso_homologyπ (-1) 0 (by simp) h

/-- The differential into degree `0` of a complex concentrated in degrees `≥ 0` vanishes. -/
private theorem d_neg_one_zero_of_isStrictlyGE (K : CochainComplex C ℤ) [K.IsStrictlyGE 0] :
    K.d (-1) 0 = 0 :=
  (K.isZero_of_isStrictlyGE 0 (-1) (by omega)).eq_of_src _ _

/-- The image of a complex in degrees `≥ 0` under an additive functor has `H⁰` equal to its
degree-zero cycles. -/
private theorem isIso_homologyπ_zero_map (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℤ)
    [K.IsStrictlyGE 0] :
    IsIso (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homologyπ 0) :=
  isIso_homologyπ_zero _ (by
    change F.map (K.d (-1) 0) = 0
    rw [d_neg_one_zero_of_isStrictlyGE, F.map_zero])

/-- **A left exact functor is bijective on `H⁰` along a quasi-isomorphism of complexes in degrees
`≥ 0`.** Both `H⁰` are the kernels of the first differential, which the functor preserves. -/
theorem isIso_homologyMap_mapHomologicalComplex_zero_of_isStrictlyGE (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] {K L : CochainComplex C ℤ} [K.IsStrictlyGE 0] [L.IsStrictlyGE 0]
    (φ : K ⟶ L) [QuasiIsoAt φ 0] :
    IsIso (homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) 0) := by
  have := isIso_homologyπ_zero K (d_neg_one_zero_of_isStrictlyGE K)
  have := isIso_homologyπ_zero L (d_neg_one_zero_of_isStrictlyGE L)
  have := isIso_homologyπ_zero_map F K
  have := isIso_homologyπ_zero_map F L
  have hc : IsIso (cyclesMap φ 0) := by
    have e : cyclesMap φ 0 = K.homologyπ 0 ≫ homologyMap φ 0 ≫ inv (L.homologyπ 0) := by
      rw [homologyπ_naturality_assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [e]
    infer_instance
  have hFc : IsIso (cyclesMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) 0) := by
    have e := Stacks.Cohomology.RightDerivedCoEdge.mapCyclesIso_inv_naturality F φ 0
    have e' : cyclesMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) 0 =
        (Stacks.Cohomology.RightDerivedCoEdge.mapCyclesIso F K 0).inv ≫
          F.map (cyclesMap φ 0) ≫
            (Stacks.Cohomology.RightDerivedCoEdge.mapCyclesIso F L 0).hom := by
      rw [← Category.assoc, ← e, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [e']
    infer_instance
  have e : homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) 0 =
      inv (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homologyπ 0) ≫
        cyclesMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) 0 ≫
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).homologyπ 0 := by
    rw [← homologyπ_naturality, IsIso.inv_hom_id_assoc]
  rw [e]
  infer_instance

end HomologicalComplex

namespace Stacks.Cohomology.DerivedGlobalCupProduct

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u})

/-- **Derived global sections in degree zero**: for a complex `N` of `𝒪_X`-modules concentrated
in degrees `≥ 0`, the comparison `Γ(X, N) ⟶ RΓ(X, N)` is an isomorphism on `H⁰`. -/
theorem isIso_homologyMap_sectionsUnitQ_zero
    (N : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) [N.IsStrictlyGE 0] :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) 0).map
      (sectionsUnitQ X ⊤ N)) := by
  obtain ⟨I, i, hi, hI, hIge⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective N 0
  have hKI : I.IsKInjective := CochainComplex.isKInjective_of_injective I 0
  have hu := isIso_sectionsUnitQ_of_isKInjective I hKI
  have hQi : IsIso (DerivedCategory.Q.map i) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact hi
  have hRi : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) 0).map
      ((derivedSectionsOverOpen X ⊤).map (DerivedCategory.Q.map i))) := inferInstance
  have hΓ : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) 0).map
      (DerivedCategory.Q.map (((sectionsOverOpen X ⊤).mapHomologicalComplex
        (ComplexShape.up ℤ)).map i))) := by
    have h := HomologicalComplex.isIso_homologyMap_mapHomologicalComplex_zero_of_isStrictlyGE
      (sectionsOverOpen X ⊤) i
    exact (NatIso.isIso_map_iff
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} (baseRing X)) 0) _).2 h
  have nat := sectionsUnitQ_naturality X ⊤ i
  have e : (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) 0).map
      (sectionsUnitQ X ⊤ N) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) 0).map
          (DerivedCategory.Q.map (((sectionsOverOpen X ⊤).mapHomologicalComplex
            (ComplexShape.up ℤ)).map i)) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) 0).map
          (sectionsUnitQ X ⊤ I) ≫
        inv ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) 0).map
          ((derivedSectionsOverOpen X ⊤).map (DerivedCategory.Q.map i))) := by
    rw [← Functor.map_comp_assoc, nat, Functor.map_comp_assoc, IsIso.hom_inv_id,
      Category.comp_id]
  rw [e]
  infer_instance

/-- The class of a global cocycle is linear in the cocycle over `Γ(X, 𝒪_X)`. -/
theorem globalClass_smul (N : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (n : ℤ) (a : baseRing X) (s : (sectionsComplex X N).cycles n) :
    globalClass N n (a • s) = a • globalClass N n s := by
  unfold globalClass
  exact map_smul _ a s

/-- **`H⁰(X, N)` is the module of global cocycles in degree `0`** for a complex `N` of
`𝒪_X`-modules concentrated in degrees `≥ 0`: the class map is bijective. -/
theorem bijective_globalClass_zero
    (N : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) [N.IsStrictlyGE 0] :
    Function.Bijective (globalClass N 0) := by
  have hπ := HomologicalComplex.isIso_homologyπ_zero_map (globalSections X) N
  have hu := isIso_homologyMap_sectionsUnitQ_zero X N
  have : IsIso ((sectionsComplex X N).homologyπ 0 ≫
      (DerivedCategory.homologyFunctorFactors _ 0).inv.app (sectionsComplex X N) ≫
        (DerivedCategory.homologyFunctor _ 0).map (sectionsUnitQ X ⊤ N)) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ hπ (@IsIso.comp_isIso _ _ _ _ _ _ _
      (Iso.isIso_inv ((DerivedCategory.homologyFunctorFactors _ 0).app (sectionsComplex X N))) hu)
  exact ConcreteCategory.bijective_of_isIso _

end Stacks.Cohomology.DerivedGlobalCupProduct
