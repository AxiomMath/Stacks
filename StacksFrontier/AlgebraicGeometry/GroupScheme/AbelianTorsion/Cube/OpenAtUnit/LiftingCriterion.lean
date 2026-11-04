module

public import StacksFrontier.AlgebraicGeometry.FormalFunctions.IdealPowerCohomologySequence

/-!
# Lifting global sections through a short exact sequence, tested on faces

Let `0 → K → M → Q → 0` be a short exact sequence of `𝒪_X`-modules on a scheme `X`, mapping to a
family of short exact sequences `0 → Kᵢ → Mᵢ → Qᵢ → 0`. If every `H⁰(Mᵢ) → H⁰(Qᵢ)` is
surjective and the maps `H¹(K) → H¹(Kᵢ)` are jointly injective, then `H⁰(M) → H⁰(Q)` is
surjective: the obstruction `δ(q) ∈ H¹(K)` to lifting `q` maps to the obstruction to lifting the
image of `q` in each `Qᵢ`, which vanishes.

This is the abstract step of the thickening induction of the cube proof
(step 1(a)), where `M → Q` is `ℒ / 𝔪ⁿ⁺²ℒ → ℒ / 𝔪ⁿ⁺¹ℒ` and the family is the
same sequence on the two faces.

## Main results

* `Stacks.CubeOpenAtUnit.surjective_H0_of_faces`: the lifting criterion.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.CubeOpenAtUnit

open Stacks.Cohomology.FormalFunctions (cohomologyDeltaFunctor)

variable {X : Scheme.{u}}

/-- The `n`-th cohomology `Hⁿ(X, -)` of sheaves of modules, valued in `Γ(X, ⊤)`-modules: the
`n`-th functor of `Stacks.Cohomology.FormalFunctions.cohomologyDeltaFunctor`, which is the
`n`-th right derived functor of global sections. -/
abbrev H (X : Scheme.{u}) (n : ℕ) : X.Modules ⥤ ModuleCat.{u} Γ(X, ⊤) :=
  (cohomologyDeltaFunctor X).functor n

/-- **The lifting criterion.** Let `S : 0 → K → M → Q → 0` be short exact and `τ i : S ⟶ T i`
morphisms to short exact sequences. If `H⁰(T i).g` is surjective for every `i` and the maps
`H¹(K) → H¹((T i).X₁)` are jointly injective, then `H⁰(S.g)` is surjective. -/
theorem surjective_H0_of_faces {S : ShortComplex X.Modules} (hS : S.ShortExact) {ι : Type*}
    {T : ι → ShortComplex X.Modules} (hT : ∀ i, (T i).ShortExact) (τ : ∀ i, S ⟶ T i)
    (hsurj : ∀ i, Function.Surjective ((H X 0).map (T i).g).hom)
    (hinj : ∀ c : (H X 1).obj S.X₁, (∀ i, ((H X 1).map (τ i).τ₁).hom c = 0) → c = 0) :
    Function.Surjective ((H X 0).map S.g).hom := by
  intro q
  let E := cohomologyDeltaFunctor X
  refine ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (E.exact_δ₁ hS 0) q).1
    (hinj _ fun i => ?_)
  obtain ⟨y, hy⟩ := hsurj i (((H X 0).map (τ i).τ₃).hom q)
  have hnat := congrArg (fun φ => φ.hom q) (E.δ_naturality hS (hT i) (τ i) 0)
  have hz := congrArg (fun φ => φ.hom y) (E.map_g_δ (hT i) 0)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] at hnat hz
  change ((E.functor (0 + 1)).map (τ i).τ₁).hom ((E.δ hS 0).hom q) = 0
  rw [← hnat]
  change (E.δ (hT i) 0).hom (((H X 0).map (τ i).τ₃).hom q) = 0
  rwa [← hy]

/-- **Joint injectivity along a decomposition.** Let `K` be a module with maps `p j : K ⟶ Q` and
`e j : Q ⟶ K` (`j` in a finite type) with `∑ j, p j ≫ e j = 𝟙 K`, and let `κ i : K ⟶ K' i` and
`τ i : Q ⟶ Q' i` be compatible with maps `p' i j : K' i ⟶ Q' i`: `κ i ≫ p' i j = p j ≫ τ i`. If
the maps `H¹(τ i)` are jointly injective on `H¹(Q)`, the maps `H¹(κ i)` are jointly injective
on `H¹(K)`. -/
theorem jointlyInjective_H1_of_decomposition {K Q : X.Modules} {J : Type*} [Fintype J]
    (p : J → (K ⟶ Q)) (e : J → (Q ⟶ K)) (he : ∑ j, p j ≫ e j = 𝟙 K) {ι : Type*}
    {K' Q' : ι → X.Modules} (κ : ∀ i, K ⟶ K' i) (τ : ∀ i, Q ⟶ Q' i)
    (p' : ∀ i, J → (K' i ⟶ Q' i)) (hp : ∀ i j, κ i ≫ p' i j = p j ≫ τ i)
    (hinj : ∀ c : (H X 1).obj Q, (∀ i, ((H X 1).map (τ i)).hom c = 0) → c = 0)
    (c : (H X 1).obj K) (hc : ∀ i, ((H X 1).map (κ i)).hom c = 0) : c = 0 := by
  have hcomp : ∀ j, ((H X 1).map (p j)).hom c = 0 := fun j => by
    refine hinj _ fun i => ?_
    have h := congrArg (fun φ => ((H X 1).map φ).hom c) (hp i j)
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [← h, hc i, map_zero]
  have htot : ((H X 1).map (∑ j, p j ≫ e j)).hom c = c := by
    rw [he, CategoryTheory.Functor.map_id]
    rfl
  rw [Functor.map_sum, ModuleCat.hom_sum, LinearMap.sum_apply] at htot
  rw [← htot]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, hcomp j, map_zero]

/-- Surjectivity of the value of a functor on a morphism is invariant under natural
isomorphism. -/
theorem surjective_map_iff_of_iso {C : Type*} [Category* C] {A : Type u} [Ring A]
    {F G : C ⥤ ModuleCat.{u} A} (e : F ≅ G) {M N : C} (φ : M ⟶ N) :
    Function.Surjective (F.map φ).hom ↔ Function.Surjective (G.map φ).hom := by
  have h : G.map φ = e.inv.app M ≫ F.map φ ≫ e.hom.app N := by
    rw [← Category.assoc, ← e.inv.naturality, Category.assoc, Iso.inv_hom_id_app,
      Category.comp_id]
  have h1 : Function.Bijective (e.inv.app M).hom :=
    ConcreteCategory.bijective_of_isIso (e.inv.app M)
  have h2 : Function.Bijective (e.hom.app N).hom :=
    ConcreteCategory.bijective_of_isIso (e.hom.app N)
  rw [h, ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.coe_comp, LinearMap.coe_comp]
  exact ⟨fun hs => h2.2.comp (hs.comp h1.2), fun hs => hs.of_comp.of_comp_left h2.1⟩

/-- On `H⁰`, surjectivity is surjectivity on global sections. -/
theorem surjective_H0_map_iff {M N : X.Modules} (φ : M ⟶ N) :
    Function.Surjective ((H X 0).map φ).hom ↔ Function.Surjective (φ.app ⊤) :=
  surjective_map_iff_of_iso (F := H X 0)
    (G := Stacks.Cohomology.AffineBase.moduleGlobalSections X)
    (Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerivedZeroIsoSelf φ

end Stacks.CubeOpenAtUnit

end
