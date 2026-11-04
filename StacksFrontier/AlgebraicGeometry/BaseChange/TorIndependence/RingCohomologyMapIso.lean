module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapConstruction
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.StalkCohomologyMapTransport

/-!
# Naturality of the base-change map on cohomology in the data

Let `R → A`, `R → R'`, `A → A'`, `R' → A'` be a commutative square of commutative rings. The
base-change map of Stacks 0DJ7

`A' ⊗_{A ⊗_R R'} H^n(K ⊗ᴸ_R R') ⟶ H^n(K')`

attached to `K ∈ D(A)`, `K' ∈ D(A')` and `φ : K ⊗ᴸ_A A' ⟶ K'` is
`RingTheory.TorIndependence.ringBaseChangeCohomologyMap`. This file proves that it is natural in
the data: morphisms `K ⟶ K₁` and `K' ⟶ K₁'` compatible with `φ` and `φ₁` make the two
base-change maps form a commutative square.

## Main definitions

* `RingTheory.TorIndependence.baseChangeCohomologyCatMap`: the map
  `H^n(K ⊗ᴸ_R R') ⟶ H^n(K₁ ⊗ᴸ_R R')` of `A ⊗_R R'`-modules induced by a morphism `K ⟶ K₁`.

## Main results

* `RingTheory.TorIndependence.ringBaseChangeCohomologyMap_naturality`: the base-change maps for
  compatible data form a commutative square.

## References

* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open scoped ChangeOfRings

universe u

namespace RingTheory.TorIndependence

attribute [local instance] HasDerivedCategory.standard

variable {R A R' A' : Type u}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  [Algebra R A] [Algebra R R'] [Algebra R A']
  [Algebra A A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']

section Functoriality

variable {K K₁ : DerivedCategory (ModuleCat.{u} A)} (α : K ⟶ K₁) (n : ℤ)

/-- The induced map commutes with the action of `A` by derived base change of scalar
multiplication. -/
theorem baseChangeCohomologyOverBaseMap_action (a : A)
    (m : baseChangeCohomologyOverBase (R := R) (R' := R') K n) :
    (baseChangeCohomologyOverBaseMap (R := R) (R' := R') _ _ α n).hom
        (baseChangeCohomologyAction (R := R) (R' := R') K n a m) =
      baseChangeCohomologyAction (R := R) (R' := R') K₁ n a
        ((baseChangeCohomologyOverBaseMap (R := R) (R' := R') _ _ α n).hom m) := by
  let G := (ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory ⋙
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap R R')).functor ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} R') n
  have hα : (a • 𝟙 K) ≫ α = α ≫ (a • 𝟙 K₁) := by
    rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]
  have h := congrArg (fun f => f.hom m) (congrArg G.map hα)
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

/-- **The induced map on the source of the base-change map.** The map
`H^n(K ⊗ᴸ_R R') ⟶ H^n(K₁ ⊗ᴸ_R R')` induced by `α : K ⟶ K₁`, as a map of
`A ⊗_R R'`-modules. -/
def baseChangeCohomologyCatMap :
    baseChangeCohomologyCat (R := R) (R' := R') K n ⟶
      baseChangeCohomologyCat (R := R) (R' := R') K₁ n :=
  letI := baseChangeCohomologyModule (R := R) (R' := R') K n
  letI := baseChangeCohomologyModule (R := R) (R' := R') K₁ n
  let q := baseChangeCohomologyOverBaseMap (R := R) (R' := R') _ _ α n
  ModuleCat.ofHom (X := baseChangeCohomologyCat (R := R) (R' := R') K n)
      (Y := baseChangeCohomologyCat (R := R) (R' := R') K₁ n)
    (show baseChangeCohomologyCat (R := R) (R' := R') K n →ₗ[A ⊗[R] R']
        baseChangeCohomologyCat (R := R) (R' := R') K₁ n from
      { toFun := fun m => q.hom m
        map_add' := fun x y => q.hom.map_add x y
        map_smul' := fun t m => by
          let H₁ := baseChangeCohomologyOverBase (R := R) (R' := R') K₁ n
          change q.hom (t • m) = t • (q.hom m : H₁)
          induction t using TensorProduct.induction_on with
          | zero =>
            rw [zero_smul, zero_smul]
            exact q.hom.map_zero
          | add x y hx hy =>
            rw [add_smul, add_smul]
            exact (q.hom.map_add _ _).trans (congrArg₂ (· + ·) hx hy)
          | tmul a r =>
            have ht : a ⊗ₜ[R] r =
                (Algebra.TensorProduct.includeLeft (R := R) (S := R) a : A ⊗[R] R') *
                  Algebra.TensorProduct.includeRight r := by
              change a ⊗ₜ[R] r = (a ⊗ₜ[R] 1) * (1 ⊗ₜ[R] r)
              rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
            rw [ht, mul_smul, mul_smul]
            calc q.hom ((Algebra.TensorProduct.includeLeft (R := R) (S := R) a : A ⊗[R] R') •
                  ((Algebra.TensorProduct.includeRight r : A ⊗[R] R') • m))
                = q.hom (baseChangeCohomologyAction (R := R) (R' := R') K n a
                    ((Algebra.TensorProduct.includeRight r : A ⊗[R] R') • m)) :=
                  congrArg q.hom (baseChangeCohomologyModule_includeLeft_smul
                    (R := R) (R' := R') K n a _)
              _ = q.hom (baseChangeCohomologyAction (R := R) (R' := R') K n a
                    (r • (@id (baseChangeCohomologyOverBase (R := R) (R' := R') K n) m))) :=
                  congrArg (fun z => q.hom (baseChangeCohomologyAction (R := R) (R' := R') K n a z))
                    (baseChangeCohomologyModule_includeRight_smul (R := R) (R' := R') K n r m)
              _ = baseChangeCohomologyAction (R := R) (R' := R') K₁ n a
                    (q.hom (r • (@id (baseChangeCohomologyOverBase (R := R) (R' := R') K n) m))) :=
                  baseChangeCohomologyOverBaseMap_action (R := R) (R' := R') α n a _
              _ = baseChangeCohomologyAction (R := R) (R' := R') K₁ n a (r • q.hom m) :=
                  congrArg _ (q.hom.map_smul r m)
              _ = baseChangeCohomologyAction (R := R) (R' := R') K₁ n a
                    ((Algebra.TensorProduct.includeRight r : A ⊗[R] R') • (q.hom m : H₁)) :=
                  congrArg _ (baseChangeCohomologyModule_includeRight_smul
                    (R := R) (R' := R') K₁ n r _).symm
              _ = (Algebra.TensorProduct.includeLeft (R := R) (S := R) a : A ⊗[R] R') •
                    ((Algebra.TensorProduct.includeRight r : A ⊗[R] R') • (q.hom m : H₁)) :=
                  (baseChangeCohomologyModule_includeLeft_smul (R := R) (R' := R') K₁ n a _).symm })

/-- On elements, `baseChangeCohomologyCatMap` is the map of `R'`-modules it is built from. -/
theorem baseChangeCohomologyCatMap_apply
    (m : baseChangeCohomologyCat (R := R) (R' := R') K n) :
    (baseChangeCohomologyCatMap (R := R) (R' := R') α n).hom m =
      (baseChangeCohomologyOverBaseMap (R := R) (R' := R') _ _ α n).hom m :=
  rfl

end Functoriality

section Naturality

variable {K K₁ : DerivedCategory (ModuleCat.{u} A)} {K' K₁' : DerivedCategory (ModuleCat.{u} A')}
  (φ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor.obj K ⟶ K')
  (φ₁ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor.obj K₁ ⟶ K₁')
  (α : K ⟶ K₁) (α' : K' ⟶ K₁')
  (h : φ ≫ α' = (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor.map α ≫ φ₁)
  (n : ℤ)

include h in
/-- The comparison of Stacks 065Z followed by `φ` is natural in compatible data. -/
theorem cohomologyComparisonMap_naturality :
    baseChangeCohomologyOverBaseMap (R := R) (R' := R') _ _ α n ≫
        cohomologyComparisonMap (R := R) (R' := R') K₁ K₁' φ₁ n =
      cohomologyComparisonMap (R := R) (R' := R') K K' φ n ≫
        (ModuleCat.restrictScalars (algebraMap R' A')).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).map α') := by
  let J := DerivedCategory.homologyFunctor (ModuleCat.{u} R') n
  let C := (ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory
  let τ := squareDerivedComparison (R := R) (A := A) (R' := R') (A' := A')
  have hτ := τ.naturality α
  have hn := ((ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategoryHomologyIso
    n).hom.naturality α'
  simp only [Functor.comp_map] at hτ hn
  have key : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (algebraMap R R')).functor.map
          ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.map α) ≫
        (τ.app K₁ ≫ C.map φ₁) = (τ.app K ≫ C.map φ) ≫ C.map α' := by
    rw [← Category.assoc, hτ, Category.assoc, ← C.map_comp, ← h, C.map_comp, Category.assoc]
  dsimp only [cohomologyComparisonMap, baseChangeCohomologyOverBaseMap]
  rw [Category.assoc, ← hn, ← Category.assoc (J.map _) (J.map (C.map α')), ← J.map_comp,
    ← Category.assoc, ← J.map_comp, key]

include h in
/-- **The base-change maps of compatible data form a commutative square.** -/
theorem ringBaseChangeCohomologyMap_naturality :
    (ModuleCat.extendScalars
          (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A'))).map
        (baseChangeCohomologyCatMap (R := R) (R' := R') α n) ≫
      ringBaseChangeCohomologyMap (R := R) (R' := R') K₁ K₁' φ₁ n =
    ringBaseChangeCohomologyMap (R := R) (R' := R') K K' φ n ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).map α' := by
  refine ModuleCat.ExtendScalars.hom_ext fun m => ?_
  have h₁ := ringBaseChangeCohomologyMap_one_tmul (R := R) (R' := R') K₁ K₁' φ₁ n
    ((baseChangeCohomologyCatMap (R := R) (R' := R') α n).hom m)
  have h₂ := ringBaseChangeCohomologyMap_one_tmul (R := R) (R' := R') K K' φ n m
  have h₃ := congrArg (fun f => f.hom m)
    (cohomologyComparisonMap_naturality (R := R) (R' := R') φ φ₁ α α' h n)
  simp only [ModuleCat.hom_comp] at h₃ ⊢
  refine Eq.trans ?_ (h₃.trans ?_)
  · exact h₁
  · exact congrArg (fun z => ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).map α').hom z)
      h₂.symm

end Naturality

end RingTheory.TorIndependence

end
