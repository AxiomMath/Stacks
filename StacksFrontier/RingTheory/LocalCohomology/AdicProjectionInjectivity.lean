module

public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.CompletedLocalCohomologyProjections
public import StacksFrontier.RingTheory.LocalCohomology.ArtinianOverLocalRing
public import StacksFrontier.RingTheory.LocalCohomology.CompletedLimitComparison

/-!
# Eventual injectivity of the projections `Hⁱ_𝔪(M) → Hⁱ_𝔪(M/IⁿM)`

Let `(A, 𝔪)` be a Noetherian local ring, `I ⊆ A` an ideal and `M` a finite `A`-module. The
canonical maps `Hⁱ_𝔪(M) ⟶ Hⁱ_𝔪(M/IⁿM)` have kernels that decrease with `n`, and
`Hⁱ_𝔪(M)` is Artinian, so the chain of kernels stabilizes. If moreover the canonical map to the
inverse limit `Hⁱ_𝔪(M) ⟶ lim Hⁱ_𝔪(M/IⁿM)` is injective, the stable value is the zero submodule
and the projections are injective from some index on.

This is the argument that part (1) of [Stacks, Tag 0EFY] needs at `T = {𝔪}`. The input it
consumes is a derived-limit presentation of the tower `n ↦ RΓ_𝔪(M/IⁿM)` **with its
projections** — `NoetherianAdicCompletion.IsDerivedLimitWithProjections` — together with a map
from `RΓ_𝔪(M)` whose composites with those projections are the canonical maps and which is
invertible on cohomology in the degrees considered. That last clause is the isomorphism
assertion of [Stacks, Tag 0EFR] read against pinned projections; the bare
`CategoryTheory.Pretriangulated.IsDerivedLimit` of the library's Tag 0EFR pins no cone, which is
why the reduction is stated against the pinned predicate.

## Main results

* `Stacks.LocalCohomology.exists_forall_injective_of_isArtinian` — a cone of `A`-modules over
  `ℕᵒᵖ` with Artinian vertex and jointly injective projections has injective projections from
  some index on.
* `Stacks.LocalCohomology.exists_injective_homology_localCohomologyAdicQuotientMap` — the
  single-degree statement, from a pinned derived-limit presentation.
* `Stacks.LocalCohomology.exists_forall_injective_homology_localCohomologyAdicQuotientMap` — the
  same with one index `m₀` valid for all degrees `i ≤ s` at once, which is the shape part (1) of
  [Stacks, Tag 0EFY] asks for.

## Implementation notes

The single index valid for all `i ≤ s` is a finite supremum over `0 ≤ i ≤ s`; in negative
degrees `Hⁱ_𝔪(M)` vanishes, so injectivity there is automatic and no hypothesis is needed.

## References

* [Stacks Project, Tag 0EFY](https://stacks.math.columbia.edu/tag/0EFY)
* [Stacks Project, Tag 0EFR](https://stacks.math.columbia.edu/tag/0EFR)
* [Stacks Project, Tag 0DX0](https://stacks.math.columbia.edu/tag/0DX0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

attribute [local instance] HasDerivedCategory.standard
  Dualizing.hasProductsOfShape_nat_derivedCategory

universe u

namespace Stacks.LocalCohomology

/-! ### The descending chain of kernels in an Artinian module -/

/-- **Eventual injectivity from the descending chain condition.** Let `c n : N ⟶ Gₙ` be a cone on
an inverse system of `A`-modules indexed by `ℕᵒᵖ`, with `N` Artinian, and suppose the `c n` are
jointly injective. Then `c n` is injective for all sufficiently large `n`.

The kernels decrease, because `c n` factors through `c m` for `n ≤ m`; the descending chain
condition makes them constant from some `m₀` on; the constant value lies in every kernel, hence
is zero by joint injectivity. -/
theorem exists_forall_injective_of_isArtinian {A : Type u} [CommRing A]
    {N : ModuleCat.{u} A} (hN : IsArtinian A N) {G : ℕᵒᵖ ⥤ ModuleCat.{u} A}
    (c : ∀ n : ℕ, N ⟶ G.obj (op n))
    (hc : ∀ (n m : ℕ) (h : n ≤ m), c m ≫ G.map (homOfLE h).op = c n)
    (hinj : ∀ x : N, (∀ n : ℕ, (c n).hom x = 0) → x = 0) :
    ∃ m₀ : ℕ, ∀ n : ℕ, m₀ ≤ n → Function.Injective (c n).hom := by
  have hmono : ∀ (n m : ℕ), n ≤ m →
      LinearMap.ker (c m).hom ≤ LinearMap.ker (c n).hom := by
    intro n m h x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← hc n m h, ModuleCat.hom_comp, LinearMap.comp_apply, hx, map_zero]
  let f : ℕ →o (Submodule A N)ᵒᵈ :=
    { toFun := fun n ↦ (LinearMap.ker (c n).hom : Submodule A N)
      monotone' := fun a b hab ↦ hmono a b hab }
  obtain ⟨m₀, hm₀⟩ := IsArtinian.monotone_stabilizes f
  have hker : ∀ k : ℕ, m₀ ≤ k → LinearMap.ker (c m₀).hom = LinearMap.ker (c k).hom := hm₀
  refine ⟨m₀, fun n hn ↦ ?_⟩
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  have hx₀ : x ∈ LinearMap.ker (c m₀).hom := by rwa [hker n hn]
  refine hinj x fun k ↦ ?_
  rw [← LinearMap.mem_ker]
  rcases le_total k m₀ with hk | hk
  · exact hmono k m₀ hk hx₀
  · rwa [← hker k hk]

/-! ### The projections of the local cohomology tower -/

section Local

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  (I : Ideal A) (M : ModuleCat.{u} A) [Module.Finite A M]

/-- The tower `n ↦ RΓ_𝔪(M/IⁿM)` at the maximal ideal of a Noetherian local ring. -/
abbrev adicQuotientTowerAtMaximalIdeal : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A) :=
  Dualizing.adicQuotientLocalCohomologySystem A I (maximalIdeal A)
    (Ideal.fg_of_isNoetherianRing _) M

/-- The object `RΓ_𝔪(M)` of `D(A)`. -/
abbrev localCohomologyDerivedAtMaximalIdeal : DerivedCategory (ModuleCat.{u} A) :=
  (localCohomologyDerived A (maximalIdeal A) (Ideal.fg_of_isNoetherianRing _)).obj
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)

/-- **The single-degree statement.** Given a derived-limit presentation of the tower
`n ↦ RΓ_𝔪(M/IⁿM)` with projections `π`, and a map `u : RΓ_𝔪(M) ⟶ K` whose composites with the
projections are the canonical maps and which is invertible on degree-`i` cohomology, the
canonical map `Hⁱ_𝔪(M) ⟶ Hⁱ_𝔪(M/IⁿM)` is injective for all sufficiently large `n`.

The comparison `Hⁱ(K) ⟶ lim Hⁱ_𝔪(M/IⁿM)` built from the projections is invertible because the
inverse system one degree below is Mittag-Leffler — the modules `M/IⁿM` being finite over a
Noetherian local ring — so the canonical maps `Hⁱ_𝔪(M) ⟶ Hⁱ_𝔪(M/IⁿM)` are jointly injective,
and `Hⁱ_𝔪(M)` is Artinian. -/
theorem exists_injective_homology_localCohomologyAdicQuotientMap
    (K : DerivedCategory (ModuleCat.{u} A))
    (π : ∀ n : ℕ, K ⟶ (adicQuotientTowerAtMaximalIdeal A I M).obj (op n))
    (hK : NoetherianAdicCompletion.IsDerivedLimitWithProjections
      (adicQuotientTowerAtMaximalIdeal A I M) K π)
    (u : localCohomologyDerivedAtMaximalIdeal A M ⟶ K)
    (hu : ∀ n : ℕ, u ≫ π n = Dualizing.localCohomologyAdicQuotientMap A I (maximalIdeal A)
      (Ideal.fg_of_isNoetherianRing _) M n)
    (i : ℤ) (hiso : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map u)) :
    ∃ m₀ : ℕ, ∀ n : ℕ, m₀ ≤ n →
      Function.Injective ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
        (Dualizing.localCohomologyAdicQuotientMap A I (maximalIdeal A)
          (Ideal.fg_of_isNoetherianRing _) M n)).hom := by
  obtain ⟨q, hqiso, hq⟩ :=
    NoetherianAdicCompletion.IsDerivedLimitWithProjections.exists_isIso_comp_limit_π A
      (adicQuotientTowerAtMaximalIdeal A I M) K π hK i
      (isMittagLefflerCategorical_homologyAdicQuotientLocalCohomology A I M (i - 1))
  have hart : IsArtinian A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      (localCohomologyDerivedAtMaximalIdeal A M)) :=
    isArtinian_localCohomology_maximalIdeal A M i
  refine exists_forall_injective_of_isArtinian hart
    (G := adicQuotientTowerAtMaximalIdeal A I M ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} A) i)
    (fun n ↦ (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      (Dualizing.localCohomologyAdicQuotientMap A I (maximalIdeal A)
        (Ideal.fg_of_isNoetherianRing _) M n)) (fun n m h ↦ ?_) (fun x hx ↦ ?_)
  · rw [Functor.comp_map, ← (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map_comp,
      Dualizing.localCohomologyAdicQuotientMap_comp_map A I (maximalIdeal A)
      (Ideal.fg_of_isNoetherianRing _) M h]
  · have hinj : Function.Injective
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map u ≫ q)).hom :=
      (ModuleCat.mono_iff_injective _).1 inferInstance
    have hzero : (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map u ≫ q)).hom x = 0 := by
      refine Limits.Concrete.limit_ext (adicQuotientTowerAtMaximalIdeal A I M ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) i) _ _ fun j ↦ ?_
      obtain ⟨n⟩ := j
      have hcomp : ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map u ≫ q) ≫
          limit.π (adicQuotientTowerAtMaximalIdeal A I M ⋙
            DerivedCategory.homologyFunctor (ModuleCat.{u} A) i) (op n) =
          (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
            (Dualizing.localCohomologyAdicQuotientMap A I (maximalIdeal A)
              (Ideal.fg_of_isNoetherianRing _) M n) := by
        rw [Category.assoc, hq n,
          ← (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map_comp, hu n]
      have h1 : (limit.π (adicQuotientTowerAtMaximalIdeal A I M ⋙
            DerivedCategory.homologyFunctor (ModuleCat.{u} A) i) (op n)).hom
            ((((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map u ≫ q)).hom x) =
          ((((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map u ≫ q) ≫
            limit.π (adicQuotientTowerAtMaximalIdeal A I M ⋙
              DerivedCategory.homologyFunctor (ModuleCat.{u} A) i) (op n))).hom x := rfl
      rw [h1, hcomp, hx n, map_zero]
    exact hinj (a₁ := x) (a₂ := 0) (by rw [hzero, map_zero])

/-- **Part (1) of [Stacks, Tag 0EFY] at `T = {𝔪}`, from a pinned derived-limit presentation.**
There is a single integer `m₀` such that for every `i ≤ s` and every `n ≥ m₀` the canonical map
`Hⁱ_𝔪(M) ⟶ Hⁱ_𝔪(M/IⁿM)` is injective.

The hypotheses are a derived-limit presentation of the tower with its projections, a map
`u : RΓ_𝔪(M) ⟶ K` over the canonical maps, and the invertibility of `Hⁱ(u)` for `i ≤ s`. The
uniform `m₀` is a finite supremum over the degrees `0 ≤ i ≤ s`; for `i < 0` the module
`Hⁱ_𝔪(M)` vanishes and injectivity is automatic. -/
theorem exists_forall_injective_homology_localCohomologyAdicQuotientMap (s : ℤ)
    (K : DerivedCategory (ModuleCat.{u} A))
    (π : ∀ n : ℕ, K ⟶ (adicQuotientTowerAtMaximalIdeal A I M).obj (op n))
    (hK : NoetherianAdicCompletion.IsDerivedLimitWithProjections
      (adicQuotientTowerAtMaximalIdeal A I M) K π)
    (u : localCohomologyDerivedAtMaximalIdeal A M ⟶ K)
    (hu : ∀ n : ℕ, u ≫ π n = Dualizing.localCohomologyAdicQuotientMap A I (maximalIdeal A)
      (Ideal.fg_of_isNoetherianRing _) M n)
    (hiso : ∀ i : ℤ, i ≤ s →
      IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map u)) :
    ∃ m₀ : ℕ, ∀ i : ℤ, i ≤ s → ∀ n : ℕ, m₀ ≤ n →
      Function.Injective ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
        (Dualizing.localCohomologyAdicQuotientMap A I (maximalIdeal A)
          (Ideal.fg_of_isNoetherianRing _) M n)).hom := by
  have hdeg : ∀ j : ℕ, ∃ k : ℕ, (j : ℤ) ≤ s → ∀ n : ℕ, k ≤ n →
      Function.Injective ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (j : ℤ)).map
        (Dualizing.localCohomologyAdicQuotientMap A I (maximalIdeal A)
          (Ideal.fg_of_isNoetherianRing _) M n)).hom := by
    intro j
    by_cases hj : (j : ℤ) ≤ s
    · obtain ⟨k, hk⟩ := exists_injective_homology_localCohomologyAdicQuotientMap A I M K π hK u hu
        (j : ℤ) (hiso (j : ℤ) hj)
      exact ⟨k, fun _ ↦ hk⟩
    · exact ⟨0, fun hcon ↦ absurd hcon hj⟩
  choose g hg using hdeg
  refine ⟨(Finset.range (s.toNat + 1)).sup g, fun i hi n hn ↦ ?_⟩
  by_cases hneg : i < 0
  · exact fun x y _ ↦ (ModuleCat.isZero_iff_subsingleton.mp
      (isZero_localCohomologyModule_of_neg A (maximalIdeal A)
        (Ideal.fg_of_isNoetherianRing _) M i hneg)).elim x y
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = (j : ℤ) :=
      ⟨i.toNat, (Int.toNat_of_nonneg (not_lt.mp hneg)).symm⟩
    exact hg j hi n ((Finset.le_sup (Finset.mem_range.2 (by omega))).trans hn)

end Local

end Stacks.LocalCohomology

end
