module

public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerCohomologyReesFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyAdicUniformBounds
public import StacksFrontier.AlgebraicGeometry.Spaces.FirstCohomologyVanishingCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperModuleCohomologyFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalSections.Finiteness
public import StacksFrontier.RingTheory.AdicCompletion.IntertwinedFiltrationEventualRange
public import StacksFrontier.RingTheory.AdicCompletion.TateModule.FiniteComplete

/-!
# The uniform bounds of the theorem on formal functions for a proper algebraic space

In Situation 08AV — a Noetherian ring `A`, an ideal `I ⊆ A`, a proper algebraic space
`X ⟶ Spec A` and a coherent `𝒪_X`-module `F` — fix `p ≥ 0`.  [Stacks, Tag 08AY] gives a `c` with

1. `ker (Hᵖ(X, F) ⟶ Hᵖ(X, F / Iⁿ F)) ⊆ Iⁿ⁻ᶜ Hᵖ(X, F)` for `n ≥ c`, and
3. for every `n` a `c₂ ≥ n` with `im (Hᵖ(X, F / Iᵏ F) ⟶ Hᵖ(X, F / Iⁿ F)) =
   im (Hᵖ(X, F) ⟶ Hᵖ(X, F / Iⁿ F))` for `k ≥ c₂`,

and clause (2), the Mittag-Leffler condition, is a consequence of clause (3).  The base proves
the commutative algebra of the source's argument for arbitrary towers of modules
(`Stacks.AdicCohomologyBound.ker_le_pow_smul_top`,
`Stacks.AdicCohomologyBound.exists_range_transition_eq_range_proj`), taking the geometric
inputs as hypotheses.  This file supplies those inputs for a proper algebraic space, so the
bounds hold outright:

* the long exact cohomology sequence of `0 ⟶ Iⁿ F ⟶ F ⟶ F / Iⁿ F ⟶ 0`, from the cohomological
  `δ`-functor `AlgebraicGeometry.Space.firstCohomologyDeltaFunctor` of the module universe of the
  structure rings;
* [Stacks, Tag 08AX], which is
  `AlgebraicGeometry.Space.exists_surjective_cohomologyIdealPowerMul_and_range_le`;
* the finiteness [Stacks, Tag 08AS] of `Hᵖ⁺¹(X, Iⁿ F)`, which is
  `AlgebraicGeometry.Space.moduleFinite_cohomology_of_isProper`, `Iⁿ F` being coherent;
* the annihilation of `Hᵖ(X, F / Iⁿ F)` by `Iⁿ`.

The theorem on formal functions [Stacks, Tag 08AZ] in this vocabulary, its identification as the
map assembled from the projections, and its reformulation [Stacks, Tag 08B0] over a complete base
follow.

Everything is stated at the module universe `u` of the structure rings, in the vocabulary of
`StacksFrontier/AlgebraicGeometry/Spaces/IdealMultipleModule.lean` (`Iⁿ F` is
`AlgebraicGeometry.Space.idealMultiple`) and of
`StacksFrontier/AlgebraicGeometry/Spaces/IdealPowerCohomologyReesFinite.lean` (cohomology over `A`
is `AlgebraicGeometry.Space.cohomologyRes`), which is where [Stacks, Tag 08AX] is stated.

## Main definitions

* `AlgebraicGeometry.Space.adicCohomology` — the tower `n ↦ Hᵖ(X, F / Iⁿ F)`, with its transition
  maps `adicCohomologyMap` and the maps `adicCohomologyProj` out of `Hᵖ(X, F)`.
* `AlgebraicGeometry.Space.adicCohomologyBoundary` — the connecting maps
  `Hᵖ(X, F / Iⁿ F) ⟶ Hᵖ⁺¹(X, Iⁿ F)`.
* `AlgebraicGeometry.Space.adicCohomologyLimit` — the limit `limₙ Hᵖ(X, F / Iⁿ F)`.
* `AlgebraicGeometry.Space.formalFunctionsEquivOfIsProper` — **Stacks 08AZ** (the isomorphism of
  `A`-modules) at the module universe of the structure rings.

## Main results

* `AlgebraicGeometry.Space.exists_adicCohomology_bounds` — **Stacks 08AY**, clauses (1) and (3),
  with one `c` for clause (1).
* `AlgebraicGeometry.Space.formalFunctionsEquivOfIsProper_proj_of` — the isomorphism of Stacks 08AZ
  is the one defined by the projections.
* `AlgebraicGeometry.Space.bijective_adicCohomologyLimitMap_of_isAdicComplete` — **Stacks 08B0**:
  over a complete Noetherian base, `Hᵖ(X, F) ⟶ limₙ Hᵖ(X, F / Iⁿ F)` is bijective.

None of these declarations carries a `@[stacks]` attribute: the tags are owned elsewhere, and the
results are provided here for use by the Grothendieck existence theorem for algebraic spaces.

## References

* [Stacks Project, Tag 08AY](https://stacks.math.columbia.edu/tag/08AY)
* [Stacks Project, Tag 08AZ](https://stacks.math.columbia.edu/tag/08AZ)
* [Stacks Project, Tag 08B0](https://stacks.math.columbia.edu/tag/08B0)
* [Stacks Project, Tag 08AX](https://stacks.math.columbia.edu/tag/08AX)
* [Stacks Project, Tag 08AS](https://stacks.math.columbia.edu/tag/08AS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules
open scoped IsMulCommutative

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] hasInjectiveResolutions_modules

section Tower

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  {A : Type u} [CommRing A]
  (φ : A →+* ↥(GlobalSectionRing
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))))
  (F : Modules.{u, u} B S hS X.1 X.2) (I : Ideal A) (p : ℕ)

/-- The `n`-th term `Hᵖ(X, F / Iⁿ F)` of the tower of the theorem on formal functions. -/
abbrev adicCohomology (n : ℕ) : ModuleCat.{u + 1} A :=
  cohomologyRes φ p (idealQuotient φ F (I ^ n))

/-- The map `Hᵖ(X, F) ⟶ Hᵖ(X, F / Iⁿ F)`. -/
abbrev adicCohomologyProj (n : ℕ) : cohomologyRes φ p F →ₗ[A] adicCohomology φ F I p n :=
  cohomologyResMap φ p (idealQuotientπ φ F (I ^ n))

/-- The transition map `Hᵖ(X, F / Iⁿ F) ⟶ Hᵖ(X, F / Iᵐ F)` for `m ≤ n`. -/
abbrev adicCohomologyMap (m n : ℕ) (h : m ≤ n) :
    adicCohomology φ F I p n →ₗ[A] adicCohomology φ F I p m :=
  cohomologyResMap φ p (idealQuotientMap φ F (Ideal.pow_le_pow_right h))

/-- The transition map `Hᵖ(X, F / Iⁿ F) ⟶ Hᵖ(X, F / Iᵐ F)` composed with the map
`Hᵖ(X, F) ⟶ Hᵖ(X, F / Iⁿ F)` is the map `Hᵖ(X, F) ⟶ Hᵖ(X, F / Iᵐ F)`. -/
theorem adicCohomologyMap_comp_proj (m n : ℕ) (h : m ≤ n) :
    (adicCohomologyMap φ F I p m n h).comp (adicCohomologyProj φ F I p n) =
      adicCohomologyProj φ F I p m :=
  LinearMap.ext fun x => by
    rw [LinearMap.comp_apply, cohomologyResMap_comp_apply, idealQuotientπ_idealQuotientMap]

/-- The connecting map `Hᵖ(X, F / Iⁿ F) ⟶ Hᵖ⁺¹(X, Iⁿ F)` of the long exact cohomology sequence of
`0 ⟶ Iⁿ F ⟶ F ⟶ F / Iⁿ F ⟶ 0`, as an `A`-linear map. -/
def adicCohomologyBoundary (n : ℕ) :
    adicCohomology φ F I p n →ₗ[A] cohomologyIdealPower φ F I (p + 1) n :=
  ((ModuleCat.restrictScalars φ).map
    ((firstCohomologyDeltaFunctor B S hS X).δ (idealShortComplex_shortExact φ F (I ^ n)) p)).hom

/-- Exactness of the long exact sequence at `Hᵖ(X, F)`: a class dying in `Hᵖ(X, F / Iⁿ F)` comes
from `Hᵖ(X, Iⁿ F)`. -/
theorem ker_adicCohomologyProj_le (n : ℕ) :
    LinearMap.ker (adicCohomologyProj φ F I p n) ≤
      LinearMap.range (cohomologyIdealPowerProj φ F I p n) := by
  exact fun x hx => (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1
    ((firstCohomologyDeltaFunctor B S hS X).exact_map
      (idealShortComplex_shortExact φ F (I ^ n)) p) hx

/-- Exactness of the long exact sequence at `Hᵖ(X, F / Iⁿ F)`: a class killed by the connecting
map comes from `Hᵖ(X, F)`. -/
theorem ker_adicCohomologyBoundary_le (n : ℕ) :
    LinearMap.ker (adicCohomologyBoundary φ F I p n) ≤
      LinearMap.range (adicCohomologyProj φ F I p n) := by
  exact fun x hx => (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1
    ((firstCohomologyDeltaFunctor B S hS X).exact_δ₁
      (idealShortComplex_shortExact φ F (I ^ n)) p) hx

/-- The connecting maps form a ladder with the transition maps of the two towers. -/
theorem adicCohomologyBoundary_comp_map (m n : ℕ) (h : m ≤ n) :
    (adicCohomologyBoundary φ F I p m).comp (adicCohomologyMap φ F I p m n h) =
      (cohomologyIdealPowerTr φ F I (p + 1) h).comp (adicCohomologyBoundary φ F I p n) := by
  have hnat := (firstCohomologyDeltaFunctor B S hS X).δ_naturality
    (idealShortComplex_shortExact φ F (I ^ n)) (idealShortComplex_shortExact φ F (I ^ m))
    (idealShortComplexMap φ F (Ideal.pow_le_pow_right h)) p
  have h2 := congrArg (fun g => ((ModuleCat.restrictScalars φ).map g).hom) hnat
  simp only [Functor.map_comp, ModuleCat.hom_comp] at h2
  exact h2

/-- **`Iⁿ` annihilates `Hᵖ(X, F / Iⁿ F)`.** -/
theorem pow_smul_top_adicCohomology_eq_bot (n : ℕ) :
    I ^ n • (⊤ : Submodule A (adicCohomology φ F I p n)) = ⊥ := by
  refine eq_bot_iff.2 (Submodule.smul_le.2 fun a ha y _ => ?_)
  rw [Submodule.mem_bot, ← cohomologyResMap_globalSmul,
    globalSmul_idealQuotient_eq_zero φ F (I ^ n) ha, cohomologyResMap_zero]
  rfl

/-- `Iⁿ Hᵖ(X, F)` dies in `Hᵖ(X, F / Iⁿ F)`. -/
theorem pow_smul_top_le_ker_adicCohomologyProj (n : ℕ) :
    I ^ n • (⊤ : Submodule A (cohomologyRes φ p F)) ≤
      LinearMap.ker (adicCohomologyProj φ F I p n) := by
  refine Submodule.smul_le.2 fun a ha x _ => ?_
  rw [LinearMap.mem_ker, map_smul, ← Submodule.mem_bot A,
    ← pow_smul_top_adicCohomology_eq_bot φ F I p n]
  exact Submodule.smul_mem_smul ha Submodule.mem_top

/-- The map `Hᵖ(X, Iⁿ F) ⟶ Hᵖ(X, F)` factors through `Hᵖ(X, I⁰ F)`. -/
theorem cohomologyIdealPowerProj_eq_comp (n : ℕ) :
    cohomologyIdealPowerProj φ F I p n =
      (cohomologyIdealPowerProj φ F I p 0).comp
        (cohomologyIdealPowerTr φ F I p (Nat.zero_le n)) :=
  LinearMap.ext fun x => by
    rw [LinearMap.comp_apply, cohomologyResMap_comp_apply,
      idealMultipleMap_one_ι φ F (Ideal.pow_le_pow_right (Nat.zero_le n))]

/-- [Stacks, Tag 08AX] part (2) in the form used below: for `k ≤ l` with `k + c ≤ l` the image of
`Hᵖ(X, Iˡ F) ⟶ Hᵖ(X, Iᵏ F)` lies in `Iˡ⁻ᵏ⁻ᶜ Hᵖ(X, Iᵏ F)`, for any `c` at least the constant of
Tag 08AX. -/
theorem range_cohomologyIdealPowerTr_le {c c' : ℕ} (hcc' : c ≤ c')
    (h08AX : ∀ n m : ℕ, c ≤ m →
      LinearMap.range (cohomologyIdealPowerTr φ F I p (Nat.le_add_right n m)) ≤
        I ^ (m - c) • (⊤ : Submodule A (cohomologyIdealPower φ F I p n)))
    (k l : ℕ) (h : k ≤ l) (hl : k + c' ≤ l) :
    LinearMap.range (cohomologyIdealPowerTr φ F I p h) ≤
      I ^ (l - k - c') • (⊤ : Submodule A (cohomologyIdealPower φ F I p k)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  exact (h08AX k m (by omega)).trans (Submodule.smul_mono_left
    (Ideal.pow_le_pow_right (by omega)))

end Tower

/-! ### Completeness of finite modules in any universe -/

/-- A finite module over a Noetherian ring complete with respect to `I` is `I`-adically complete,
in any universe: `AdicCompletion.of` is bijective.  The universe of the module is arbitrary
because the cohomology modules of an algebraic space lie one universe above the base ring; the
statement is transported through `Shrink` from
`AdicCompletion.isAdicComplete_of_finite_of_isNoetherianRing`. -/
theorem bijective_adicCompletion_of_of_finite {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsAdicComplete I R] (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] : Function.Bijective (AdicCompletion.of I M) := by
  have : Small.{u} M := Module.Finite.small.{u} R M
  let e := Shrink.linearEquiv.{u} R M
  have : Module.Finite R (Shrink.{u} M) := Module.Finite.equiv e.symm
  have key : ⇑(AdicCompletion.of I M) =
      ⇑(AdicCompletion.congr I e) ∘ ⇑(AdicCompletion.of I (Shrink.{u} M)) ∘ ⇑e.symm := by
    funext x
    change _ = AdicCompletion.map I e.toLinearMap (AdicCompletion.of I _ (e.symm x))
    rw [AdicCompletion.map_of]
    simp
  rw [key]
  exact (AdicCompletion.congr I e).bijective.comp ((AdicCompletion.of_bijective_iff.2
    (AdicCompletion.isAdicComplete_of_finite_of_isNoetherianRing I (Shrink.{u} M))).comp
      e.symm.bijective)

/-! ### Stacks 08AY for a proper algebraic space -/

section Proper

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  (X : AlgebraicSpaces B (Spec (.of A)) hA)

variable [IsNoetherianRing A]
  (hX : IsProper B (Spec (.of A)) hA ((isTerminal_yoneda_obj_base B _ hA).from X.1))
  (F : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) [IsCoherent B (Spec (.of A)) hA X.1 X.2 F]
  (I : Ideal A) (p : ℕ)

/-- The structure morphism of a proper algebraic space over `Spec A`, as a morphism to the
algebraic space of the base object, in the form [Stacks, Tag 08AX] takes. -/
abbrev toBaseObjectSpace : X ⟶ schemeSpace (baseObject A B hA) :=
  ObjectProperty.homMk ((isTerminal_yoneda_obj_base B _ hA).from X.1)

include hX in
/-- [Stacks, Tag 08AX] for the proper algebraic space `X`, read off the base theorem. -/
theorem exists_range_cohomologyIdealPowerTr_le (q : ℕ) :
    ∃ c : ℕ, ∀ n m : ℕ, c ≤ m →
      LinearMap.range
          (cohomologyIdealPowerTr (baseRingHom A B hA X.1 X.2) F I q (Nat.le_add_right n m)) ≤
        I ^ (m - c) •
          (⊤ : Submodule A (cohomologyIdealPower (baseRingHom A B hA X.1 X.2) F I q n)) :=
  (exists_surjective_cohomologyIdealPowerMul_and_range_le (toBaseObjectSpace X) hX F I q).imp
    fun _ => And.right

include hX in
/-- `Iⁿ F` is coherent on the proper, hence Noetherian, algebraic space `X`. -/
theorem isCoherent_idealMultiple_of_isProper (J : Ideal A) :
    IsCoherent B (Spec (.of A)) hA X.1 X.2 (idealMultiple (baseRingHom A B hA X.1 X.2) F J) := by
  have : Fact (HasEtaleLocalProperty B (Spec (.of A)) hA X.1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
    ⟨(isNoetherian_of_isProper_toBase A X hX).2.2⟩
  exact isCoherent_idealMultiple (baseRingHom A B hA X.1 X.2) F J inferInstance

include hX in
/-- [Stacks, Tag 08AS] for the modules `Iⁿ F`: their cohomology is finite over `A`. -/
theorem moduleFinite_cohomologyIdealPower (q n : ℕ) :
    Module.Finite A (cohomologyIdealPower (baseRingHom A B hA X.1 X.2) F I q n) := by
  have := isCoherent_idealMultiple_of_isProper X hX F (I ^ n)
  exact moduleFinite_cohomology_of_isProper X.1 X.2
    ((isTerminal_yoneda_obj_base B _ hA).from X.1) hX
    (idealMultiple (baseRingHom A B hA X.1 X.2) F (I ^ n)) q

include hX in
/-- **Stacks 08AY**, clauses (1) and (3), for a proper algebraic space over a Noetherian ring.

There is a `c` such that for `n ≥ c` the kernel of `Hᵖ(X, F) ⟶ Hᵖ(X, F / Iⁿ F)` lies in
`Iⁿ⁻ᶜ Hᵖ(X, F)`, and for every `n` there is a `c₂ ≥ n` such that for `k ≥ c₂` the image of
`Hᵖ(X, F / Iᵏ F) ⟶ Hᵖ(X, F / Iⁿ F)` is the image of `Hᵖ(X, F) ⟶ Hᵖ(X, F / Iⁿ F)`.  Clause (2),
the Mittag-Leffler condition, follows from clause (3) by
`Stacks.AdicCohomologyBound.exists_range_transition_stable`. -/
theorem exists_adicCohomology_bounds :
    ∃ c : ℕ, (∀ n : ℕ, c ≤ n →
        LinearMap.ker (adicCohomologyProj (baseRingHom A B hA X.1 X.2) F I p n) ≤
        I ^ (n - c) • (⊤ : Submodule A (cohomologyRes (baseRingHom A B hA X.1 X.2) p F))) ∧
      ∀ n : ℕ, ∃ c₂ : ℕ, n ≤ c₂ ∧ ∀ (k : ℕ) (h : n ≤ k), c₂ ≤ k →
        LinearMap.range (adicCohomologyMap (baseRingHom A B hA X.1 X.2) F I p n k h) =
          LinearMap.range (adicCohomologyProj (baseRingHom A B hA X.1 X.2) F I p n) := by
  obtain ⟨c₀, hc₀⟩ := exists_range_cohomologyIdealPowerTr_le X hX F I p
  obtain ⟨c₁, hc₁⟩ := exists_range_cohomologyIdealPowerTr_le X hX F I (p + 1)
  refine ⟨max c₀ c₁, ?_, fun n => ?_⟩
  · refine Stacks.AdicCohomologyBound.ker_le_pow_smul_top I
      (cohomologyIdealPowerProj (baseRingHom A B hA X.1 X.2) F I p)
      (adicCohomologyProj (baseRingHom A B hA X.1 X.2) F I p) (max c₀ c₁)
      (ker_adicCohomologyProj_le (baseRingHom A B hA X.1 X.2) F I p) fun n hn => ?_
    rw [cohomologyIdealPowerProj_eq_comp, LinearMap.range_comp]
    refine (Submodule.map_mono (range_cohomologyIdealPowerTr_le (baseRingHom A B hA X.1 X.2) F I p
      (le_max_left c₀ c₁) hc₀ 0 n (Nat.zero_le n) (by omega))).trans ?_
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  · exact Stacks.AdicCohomologyBound.exists_range_transition_eq_range_proj I
      (adicCohomologyProj (baseRingHom A B hA X.1 X.2) F I p)
      (adicCohomologyMap (baseRingHom A B hA X.1 X.2) F I p)
      (adicCohomologyBoundary (baseRingHom A B hA X.1 X.2) F I p)
      (fun m n h => cohomologyIdealPowerTr (baseRingHom A B hA X.1 X.2) F I (p + 1) h) (max c₀ c₁)
      (moduleFinite_cohomologyIdealPower X hX F I (p + 1))
      (adicCohomologyMap_comp_proj (baseRingHom A B hA X.1 X.2) F I p)
      (adicCohomologyBoundary_comp_map (baseRingHom A B hA X.1 X.2) F I p)
      (ker_adicCohomologyBoundary_le (baseRingHom A B hA X.1 X.2) F I p)
      (pow_smul_top_adicCohomology_eq_bot (baseRingHom A B hA X.1 X.2) F I p)
      (range_cohomologyIdealPowerTr_le (baseRingHom A B hA X.1 X.2) F I (p + 1)
        (le_max_right c₀ c₁) hc₁) n

/-! ### Stacks 08AZ and Stacks 08B0 -/

/-- The limit `limₙ Hᵖ(X, F / Iⁿ F)` of the tower of the theorem on formal functions. -/
abbrev adicCohomologyLimit :=
  Stacks.IntertwinedFiltration.towerLimit
    (fun n => adicCohomology (baseRingHom A B hA X.1 X.2) F I p n)
    (adicCohomologyMap (baseRingHom A B hA X.1 X.2) F I p)

/-- The map `Hᵖ(X, F) ⟶ limₙ Hᵖ(X, F / Iⁿ F)` assembled from the projections. -/
def adicCohomologyLimitMap :
    cohomologyRes (baseRingHom A B hA X.1 X.2) p F →ₗ[A] adicCohomologyLimit X F I p where
  toFun x := ⟨fun n => adicCohomologyProj (baseRingHom A B hA X.1 X.2) F I p n x,
    fun m n h => by
      rw [← LinearMap.comp_apply, adicCohomologyMap_comp_proj]⟩
  map_add' x y := Subtype.ext (funext fun n => map_add _ x y)
  map_smul' a x := Subtype.ext (funext fun n => map_smul _ a x)

include hX in
/-- **Stacks 08AZ**, the isomorphism of `A`-modules, for a proper algebraic space over a
Noetherian ring: `Hᵖ(X, F)^∧ ≅ limₙ Hᵖ(X, F / Iⁿ F)`.  That it is the map defined by the system
of maps `Hᵖ(X, F) / Iⁿ Hᵖ(X, F) ⟶ Hᵖ(X, F / Iⁿ F)` is
`AlgebraicGeometry.Space.formalFunctionsEquivOfIsProper_proj_of`.

The bounds of [Stacks, Tag 08AY] are `AlgebraicGeometry.Space.exists_adicCohomology_bounds`, and
the passage from them to the isomorphism is
`Stacks.IntertwinedFiltration.adicCompletionEquivTowerLimitOfEventualRange`.  The claim of the
tag that the isomorphism is a homeomorphism for the limit topologies is not asserted here. -/
def formalFunctionsEquivOfIsProper :
    AdicCompletion I (cohomologyRes (baseRingHom A B hA X.1 X.2) p F) ≃ₗ[A]
      adicCohomologyLimit X F I p :=
  have h := exists_adicCohomology_bounds X hX F I p
  Stacks.IntertwinedFiltration.adicCompletionEquivTowerLimitOfEventualRange
    (fun n => adicCohomology (baseRingHom A B hA X.1 X.2) F I p n)
    (adicCohomologyMap (baseRingHom A B hA X.1 X.2) F I p)
    (adicCohomologyProj (baseRingHom A B hA X.1 X.2) F I p) I h.choose
    (adicCohomologyMap_comp_proj (baseRingHom A B hA X.1 X.2) F I p)
    (pow_smul_top_le_ker_adicCohomologyProj (baseRingHom A B hA X.1 X.2) F I p)
    h.choose_spec.1 h.choose_spec.2

/-- **The isomorphism of Stacks 08AZ is the canonical one**: on the image of a class
`x ∈ Hᵖ(X, F)` in the completion it is the family of images of `x` in the `Hᵖ(X, F / Iⁿ F)`. -/
theorem formalFunctionsEquivOfIsProper_of (x : cohomologyRes (baseRingHom A B hA X.1 X.2) p F) :
    formalFunctionsEquivOfIsProper X hX F I p
        (AdicCompletion.of I (cohomologyRes (baseRingHom A B hA X.1 X.2) p F) x) =
      adicCohomologyLimitMap X F I p x :=
  rfl

/-- The `n`-th component of the isomorphism of Stacks 08AZ carries the image of a class `x` to the
image of `x` in `Hᵖ(X, F / Iⁿ F)`. -/
theorem formalFunctionsEquivOfIsProper_proj_of (n : ℕ)
    (x : cohomologyRes (baseRingHom A B hA X.1 X.2) p F) :
    Stacks.IntertwinedFiltration.towerLimit.proj n
        (formalFunctionsEquivOfIsProper X hX F I p
          (AdicCompletion.of I (cohomologyRes (baseRingHom A B hA X.1 X.2) p F) x)) =
      adicCohomologyProj (baseRingHom A B hA X.1 X.2) F I p n x :=
  rfl

include hX in
/-- **Stacks 08B0**: over a Noetherian ring complete with respect to `I`, the map
`Hᵖ(X, F) ⟶ limₙ Hᵖ(X, F / Iⁿ F)` is bijective, for a proper algebraic space `X` and a coherent
`F`.  The module `Hᵖ(X, F)` is finite ([Stacks, Tag 08AS]), hence `I`-adically complete
([Stacks, Tag 00MA]), so the completion in [Stacks, Tag 08AZ] is not necessary. -/
theorem bijective_adicCohomologyLimitMap_of_isAdicComplete [IsAdicComplete I A] :
    Function.Bijective (adicCohomologyLimitMap X F I p) := by
  have hfin : Module.Finite A (cohomologyRes (baseRingHom A B hA X.1 X.2) p F) :=
    moduleFinite_cohomology_of_isProper X.1 X.2
      ((isTerminal_yoneda_obj_base B _ hA).from X.1) hX F p
  have e : ⇑(adicCohomologyLimitMap X F I p) =
      ⇑(formalFunctionsEquivOfIsProper X hX F I p) ∘
        ⇑(AdicCompletion.of I (cohomologyRes (baseRingHom A B hA X.1 X.2) p F)) :=
    funext fun x => (formalFunctionsEquivOfIsProper_of X hX F I p x).symm
  rw [e]
  exact (formalFunctionsEquivOfIsProper X hX F I p).bijective.comp
    (bijective_adicCompletion_of_of_finite I _)

/-- **Stacks 08B0**, as an isomorphism: over a complete Noetherian base,
`Hᵖ(X, F) ≅ limₙ Hᵖ(X, F / Iⁿ F)`, the map being the one assembled from the projections. -/
def formalFunctionsCompleteEquivOfIsProper [IsAdicComplete I A] :
    cohomologyRes (baseRingHom A B hA X.1 X.2) p F ≃ₗ[A] adicCohomologyLimit X F I p :=
  LinearEquiv.ofBijective _ (bijective_adicCohomologyLimitMap_of_isAdicComplete X hX F I p)

end Proper

end AlgebraicGeometry.Space

end
