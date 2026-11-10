module

public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleComparison
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleChange

/-!
# Further results

Results complementing `StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleComparison`.
-/

@[expose] public section

universe u v w x y

namespace Stacks.Discriminant

open scoped TensorProduct

/-- **The canonical comparison along a morphism of factorizations.** Let `r : G' → F'` be a map
between the intermediate algebras of two finite-open factorizations of `A → B`, compatible with
the maps to `B`, such that `F' ⊗_{G'} B = B`. Then the comparison of Tag 0BT1 is
`φ ⊗ b ↦ (φ ∘ r) ⊗ b`. Unlike `dualizingModuleEquiv_tmul`, the map `F' → B` need not be
injective. -/
theorem dualizingModuleEquiv_tmul_of_isPushout
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (G : FiniteOpenFactorization.{u, v, x} A B)
    (r : G.middle →ₐ[A] F.middle)
    (hr : ∀ c, algebraMap F.middle B (r c) = algebraMap G.middle B c)
    (hpush :
      letI : Algebra G.middle F.middle := r.toAlgebra
      letI : IsScalarTower G.middle F.middle B :=
        IsScalarTower.of_algebraMap_eq fun c => (hr c).symm
      Algebra.IsPushout G.middle B F.middle B)
    (φ : Module.Dual A F.middle) (b : B) :
    dualizingModuleEquiv F G (dualizingModule.tmul F φ b) =
      dualizingModule.tmul G (φ.comp r.toLinearMap) b := by
  let : Algebra G.middle F.middle := r.toAlgebra
  let : IsScalarTower G.middle F.middle B :=
    IsScalarTower.of_algebraMap_eq fun c => (hr c).symm
  let : IsScalarTower A G.middle F.middle := IsScalarTower.of_algebraMap_eq' (by
    ext a
    change algebraMap A F.middle a = r (algebraMap A G.middle a)
    exact (r.commutes a).symm)
  let : Module.Flat G.middle B := finiteOpenFactorization_flat G
  let : Module.Finite A F.middle := F.finite_middle
  let : Module.Finite G.middle F.middle :=
    Module.Finite.of_restrictScalars_finite A G.middle F.middle
  let : Module.Finite A G.middle := G.finite_middle
  let : IsNoetherianRing G.middle := IsNoetherianRing.of_finite A G.middle
  let : Module.FinitePresentation G.middle F.middle :=
    Module.finitePresentation_of_finite G.middle F.middle
  -- the comparison computed through `F'` itself
  let ν := dualizingModule_commonChange (A := A) hpush
  have hν : ∀ (ψ : Module.Dual A F.middle) (c : B),
      ν (dualizingModule.tmul F ψ c) = dualizingModule.tmul G (ψ.comp r.toLinearMap) c :=
    fun ψ c => dualizingModule_commonChange_tmul (A := A) hpush ψ c
  -- the comparison computed through the common subalgebra of the target
  let D := commonSubalgebra F G
  let hfin : Module.Finite A D := commonSubalgebra_finite F G
  have hinj : Function.Injective (algebraMap D B) := Subtype.val_injective
  have hcompF : (IsScalarTower.toAlgHom A D B).comp (commonSubalgebra_fromF F G) =
      IsScalarTower.toAlgHom A F.middle B := commonSubalgebra_fromF_comp_val F G
  have hcompG : (IsScalarTower.toAlgHom A D B).comp (commonSubalgebra_fromG F G) =
      IsScalarTower.toAlgHom A G.middle B := commonSubalgebra_fromG_comp_val F G
  have hFG := dualizingModuleEquiv_finiteAlgebraChangeToF F G hfin hinj
    (commonSubalgebra_fromF F G) (commonSubalgebra_fromG F G) hcompF hcompG
  let : Module D (Module.Dual A D) := algebraDualModule A D
  have hrD : ∀ c : G.middle,
      commonSubalgebra_fromF F G (r c) = commonSubalgebra_fromG F G c := fun c =>
    Subtype.ext (hr c)
  have key : ∀ z : Module.Dual A D ⊗[D] B,
      ν (finiteAlgebraChangeToF F hfin (commonSubalgebra_fromF F G) hcompF hinj z) =
        finiteAlgebraChangeToF G hfin (commonSubalgebra_fromG F G) hcompG hinj z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul χ c =>
      rw [finiteAlgebraChangeToF_tmul, finiteAlgebraChangeToF_tmul]
      change ν (dualizingModule.tmul F _ c) = dualizingModule.tmul G _ c
      rw [hν]
      congr 1
      exact LinearMap.ext fun c' => congrArg χ (hrD c')
    | add z z' hz hz' =>
      exact (congrArg ν (map_add _ z z')).trans ((ν.map_add _ _).trans
        ((congrArg₂ (· + ·) hz hz').trans (map_add _ z z').symm))
  obtain ⟨z, hz⟩ := (finiteAlgebraChangeToF F hfin (commonSubalgebra_fromF F G) hcompF
    hinj).surjective (dualizingModule.tmul F φ b)
  rw [← hz, hFG z, ← key z, hz, hν]

-- The comparison is characterized by `dualizingModuleEquiv_tmul`, `dualizingModuleEquiv_refl`
-- and `dualizingModuleEquiv_trans`; consumers should use those rather than its construction,
-- which unification cannot unfold at a reasonable cost.
end Stacks.Discriminant
