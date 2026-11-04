module

public import Mathlib.RingTheory.Filtration
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyAdicUniformBounds
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerCohomologyReesFinite
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Uniform bounds for the cohomology of the adic quotients of a coherent sheaf

Let `A` be a Noetherian ring, `I ⊆ A` an ideal, `f : X ⟶ Spec A` a proper morphism of algebraic
spaces and `F` a coherent `𝒪_X`-module. Fix `p ≥ 0` and write `M = Hᵖ(X, F)` and
`Qₙ = Hᵖ(X, F / Iⁿ F)`. Then:

1. there is a `c₁ ≥ 0` with `ker (M ⟶ Qₙ) ⊆ Iⁿ⁻ᶜ¹ M` for all `n ≥ c₁`;
2. the inverse system `(Qₙ)` satisfies the Mittag-Leffler condition;
3. for every `n` there is a `c₂(n) ≥ n` with `im (Qₖ ⟶ Qₙ) = im (M ⟶ Qₙ)` for all `k ≥ c₂(n)`.

## Main definitions

* `AlgebraicGeometry.Space.C1573.idealQuotientTower`: the inverse system `n ↦ F / Iⁿ F`.
* `AlgebraicGeometry.Space.C1573.cohomologyIdealQuotientTower`: the inverse system
  `n ↦ Hᵖ(X, F / Iⁿ F)` of `A`-modules.
* `AlgebraicGeometry.Space.C1573.cohomologyIdealPowerDelta`: the connecting map
  `Hᵖ(X, F / Iⁿ F) ⟶ Hᵖ⁺¹(X, Iⁿ F)`.

## Main results

* `AlgebraicGeometry.Space.C1573.exists_ker_cohomologyIdealQuotientProj_le`: clause (1).
* `AlgebraicGeometry.Space.C1573.isMittagLefflerCategorical_cohomologyIdealQuotientTower`:
  clause (2).
* `AlgebraicGeometry.Space.C1573.exists_range_cohomologyIdealQuotientTr_eq`: clause (3).

## Implementation notes

The three clauses are deduced from the results on abstract towers in `Stacks.AdicCohomologyBound`,
applied to the long exact cohomology sequences of `0 ⟶ Iⁿ F ⟶ F ⟶ F / Iⁿ F ⟶ 0` and their
naturality in `n`, the uniform bounds of [Stacks, Tag 08AX] for `Hᵖ` and `Hᵖ⁺¹`, and the
finiteness of `Hᵖ⁺¹(X, Iⁿ F)` ([Stacks, Tag 08AS]).

## References

* [Stacks Project, Tag 08AY](https://stacks.math.columbia.edu/tag/08AY)
* [Stacks Project, Tag 08AX](https://stacks.math.columbia.edu/tag/08AX)
* [Stacks Project, Tag 08AS](https://stacks.math.columbia.edu/tag/08AS)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
attribute [local instance] ModuleCat.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u v w

/-! ## The cohomology of an algebraic space -/

namespace AlgebraicGeometry.Space.C1573

open CategoryTheory.Limits Stacks.Cohomology.SiteModules
open scoped IsMulCommutative

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] hasInjectiveResolutions_modules HasDerivedCategory.standard

section Tower

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} {A : Type u} [CommRing A]
  (φ : A →+*
    ↥(GlobalSectionRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))))
  (F : Modules.{u, u} B S hS X.1 X.2) (I : Ideal A) (p : ℕ)

/-- The inverse system `n ↦ F / Iⁿ F` of `𝒪_X`-modules. -/
def idealQuotientTower : ℕᵒᵖ ⥤ Modules.{u, u} B S hS X.1 X.2 where
  obj n := idealQuotient φ F (I ^ n.unop)
  map g := idealQuotientMap φ F (Ideal.pow_le_pow_right (leOfHom g.unop))
  map_id _ := idealQuotientMap_refl φ F
  map_comp _ _ := (idealQuotientMap_comp φ F _ _).symm

/-- The inverse system `n ↦ Hᵖ(X, F / Iⁿ F)` of `A`-modules. -/
abbrev cohomologyIdealQuotientTower : ℕᵒᵖ ⥤ ModuleCat.{u + 1} A :=
  idealQuotientTower φ F I ⋙ spaceCohomology B S hS X p ⋙ ModuleCat.restrictScalars φ

/-- `Hᵖ(X, F / Iⁿ F)`, as an `A`-module. -/
abbrev cohomologyIdealQuotient (n : ℕ) : ModuleCat.{u + 1} A :=
  cohomologyRes φ p (idealQuotient φ F (I ^ n))

/-- The map `Hᵖ(X, F) ⟶ Hᵖ(X, F / Iⁿ F)`. -/
abbrev cohomologyIdealQuotientProj (n : ℕ) :
    cohomologyRes φ p F →ₗ[A] cohomologyIdealQuotient φ F I p n :=
  cohomologyResMap φ p (idealQuotientπ φ F (I ^ n))

/-- The transition map `Hᵖ(X, F / Iⁿ F) ⟶ Hᵖ(X, F / Iᵐ F)` of the tower, for `m ≤ n`. -/
abbrev cohomologyIdealQuotientTr {m n : ℕ} (h : m ≤ n) :
    cohomologyIdealQuotient φ F I p n →ₗ[A] cohomologyIdealQuotient φ F I p m :=
  cohomologyResMap φ p (idealQuotientMap φ F (Ideal.pow_le_pow_right h))

/-- The long exact cohomology sequence of `𝒪_X`-modules, as a cohomological `δ`-functor. -/
def spaceCohomologyDeltaFunctor :
    DeltaFunctor (Modules.{u, u} B S hS X.1 X.2)
      (ModuleCat.{u + 1}
        ↥(GlobalSectionRing
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)))) :=
  haveI := enoughInjectives_modules B S hS X.1 X.2
  Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (globalSectionsFunctor.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)))

/-- The `n`-th functor of `spaceCohomologyDeltaFunctor` is `Hⁿ(X, -)`. -/
theorem spaceCohomologyDeltaFunctor_functor (n : ℕ) :
    (spaceCohomologyDeltaFunctor (X := X)).functor n = spaceCohomology B S hS X n :=
  rfl

/-- The connecting map `Hᵖ(X, F / Iⁿ F) ⟶ Hᵖ⁺¹(X, Iⁿ F)` of the long exact cohomology sequence of
`0 ⟶ Iⁿ F ⟶ F ⟶ F / Iⁿ F ⟶ 0`. -/
def cohomologyIdealPowerDelta (n : ℕ) :
    cohomologyIdealQuotient φ F I p n →ₗ[A] cohomologyIdealPower φ F I (p + 1) n :=
  ((ModuleCat.restrictScalars φ).map ((spaceCohomologyDeltaFunctor (X := X)).δ
    (idealShortComplex_shortExact φ F (I ^ n)) p)).hom

/-- Exactness of `Hᵖ(X, Iⁿ F) ⟶ Hᵖ(X, F) ⟶ Hᵖ(X, F / Iⁿ F)`. -/
theorem ker_cohomologyIdealQuotientProj_le (n : ℕ) :
    LinearMap.ker (cohomologyIdealQuotientProj φ F I p n) ≤
      LinearMap.range (cohomologyIdealPowerProj φ F I p n) := fun x hx =>
  (ShortComplex.moduleCat_exact_iff _).1
    ((spaceCohomologyDeltaFunctor (X := X)).exact_map
      (idealShortComplex_shortExact φ F (I ^ n)) p) x hx

/-- Exactness of `Hᵖ(X, F) ⟶ Hᵖ(X, F / Iⁿ F) ⟶ Hᵖ⁺¹(X, Iⁿ F)`. -/
theorem ker_cohomologyIdealPowerDelta_le (n : ℕ) :
    LinearMap.ker (cohomologyIdealPowerDelta φ F I p n) ≤
      LinearMap.range (cohomologyIdealQuotientProj φ F I p n) := fun x hx =>
  (ShortComplex.moduleCat_exact_iff _).1
    ((spaceCohomologyDeltaFunctor (X := X)).exact_δ₁
      (idealShortComplex_shortExact φ F (I ^ n)) p) x hx

/-- The connecting maps are natural in `n`. -/
theorem cohomologyIdealPowerDelta_comp_tr {m n : ℕ} (h : m ≤ n) :
    (cohomologyIdealPowerDelta φ F I p m).comp (cohomologyIdealQuotientTr φ F I p h) =
      (cohomologyIdealPowerTr φ F I (p + 1) h).comp (cohomologyIdealPowerDelta φ F I p n) := by
  have := (spaceCohomologyDeltaFunctor (X := X)).δ_naturality
    (idealShortComplex_shortExact φ F (I ^ n)) (idealShortComplex_shortExact φ F (I ^ m))
    (idealShortComplexMap φ F (Ideal.pow_le_pow_right h)) p
  exact LinearMap.ext fun x => congrArg (fun g : (spaceCohomology B S hS X p).obj
    (idealQuotient φ F (I ^ n)) ⟶ (spaceCohomology B S hS X (p + 1)).obj
      (idealMultiple φ F (I ^ m)) => g.hom x) this

/-- The maps from `Hᵖ(X, F)` are compatible with the transitions. -/
theorem cohomologyIdealQuotientTr_comp_proj {m n : ℕ} (h : m ≤ n) :
    (cohomologyIdealQuotientTr φ F I p h).comp (cohomologyIdealQuotientProj φ F I p n) =
      cohomologyIdealQuotientProj φ F I p m :=
  LinearMap.ext fun x => (cohomologyResMap_comp_apply φ p _ _ x).trans (by
    rw [idealQuotientπ_idealQuotientMap])

/-- `Iⁿ` kills `Hᵖ(X, F / Iⁿ F)`. -/
theorem pow_smul_top_cohomologyIdealQuotient (n : ℕ) :
    I ^ n • (⊤ : Submodule A (cohomologyIdealQuotient φ F I p n)) = ⊥ := by
  refine eq_bot_iff.2 (Submodule.smul_le.2 fun a ha x _ => ?_)
  rw [Submodule.mem_bot, ← cohomologyResMap_globalSmul, globalSmul_idealQuotient_eq_zero φ F _ ha,
    cohomologyResMap_zero, LinearMap.zero_apply]

/-- The image of `Hᵖ(X, Iᴺ F) ⟶ Hᵖ(X, F)` lies in `Iᵏ Hᵖ(X, F)` as soon as the image of
`Hᵖ(X, Iᴺ F) ⟶ Hᵖ(X, I⁰ F)` lies in `Iᵏ Hᵖ(X, I⁰ F)`. -/
theorem range_cohomologyIdealPowerProj_le {N k : ℕ}
    (h : LinearMap.range (cohomologyIdealPowerTr φ F I p (Nat.zero_le N)) ≤
      I ^ k • (⊤ : Submodule A (cohomologyIdealPower φ F I p 0))) :
    LinearMap.range (cohomologyIdealPowerProj φ F I p N) ≤
      I ^ k • (⊤ : Submodule A (cohomologyRes φ p F)) := by
  have e : cohomologyIdealPowerProj φ F I p N =
      (cohomologyIdealPowerProj φ F I p 0).comp (cohomologyIdealPowerTr φ F I p (Nat.zero_le N)) :=
    LinearMap.ext fun x => ((cohomologyResMap_comp_apply φ p _ _ x).trans (by
      rw [idealMultipleMap_one_ι φ F (Ideal.pow_le_pow_right (Nat.zero_le N))])).symm
  rw [e, LinearMap.range_comp]
  refine (Submodule.map_mono h).trans ?_
  rw [Submodule.map_le_iff_le_comap]
  refine Submodule.smul_le.2 fun a ha x _ => ?_
  rw [Submodule.mem_comap, map_smul]
  exact Submodule.smul_mem_smul ha Submodule.mem_top

end Tower

section OverAffine

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {V : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] {A : Type u} [CommRing A]
  (α : A ≃+* Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) {X : AlgebraicSpaces B S hS}

/-- The scheme of an affine object whose functions are identified with a Noetherian ring is
locally Noetherian. -/
private theorem isLocallyNoetherian_toScheme [IsNoetherianRing A]
    (α : A ≃+* Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) :=
  have : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
    isNoetherianRing_of_ringEquiv A α
  isLocallyNoetherian_of_isOpenImmersion ((BigFppfOver.toScheme B S hS).obj V).isoSpec.hom

/-- For a proper morphism to an affine object `V` of the site whose functions are identified with
the Noetherian ring `A` by `α`, the cohomology of a coherent module is a finite `A`-module. -/
theorem moduleFinite_cohomologyRes_of_isAffine [IsNoetherianRing A]
    (f : X ⟶ schemeSpace V) (hf : IsProper B S hS f.hom)
    (φ : A →+*
      ↥(GlobalSectionRing
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))))
    (hφ : ∀ a, φ a = pullbackToGlobalFunctions B S hS X V f (α a))
    (F : Modules.{u, u} B S hS X.1 X.2) [IsCoherent B S hS X.1 X.2 F] (p : ℕ) :
    Module.Finite A (cohomologyRes φ p F) := by
  have := isLocallyNoetherian_toScheme α
  have h := moduleFinite_cohomology_of_isProper_of_isAffine B V f hf F p
  have : RingHomSurjective α.toRingHom := ⟨α.surjective⟩
  let l : @LinearMap _ _ _ _ α.toRingHom (cohomologyRes φ p F)
      ((ModuleCat.restrictScalars (pullbackRingHom B V f)).obj
        ((spaceCohomology B S hS X p).obj F)) _ _ _ _ :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' a x := congrArg (· • (x : (spaceCohomology B S hS X p).obj F)) (hφ a) }
  exact (l.finite_iff_of_bijective Function.bijective_id).2 h

/-- Let `f : X ⟶ V` be a proper morphism to an affine object `V` of the site whose functions are
identified with the Noetherian ring `A` by `α`, and `F` a coherent `𝒪_X`-module. For every `p`
there is a `c₁ ≥ 0` such that `ker (Hᵖ(X, F) ⟶ Hᵖ(X, F / Iⁿ F)) ⊆ Iⁿ⁻ᶜ¹ Hᵖ(X, F)` for all
`n ≥ c₁`. -/
theorem exists_ker_cohomologyIdealQuotientProj_le_of_isAffine [IsNoetherianRing A]
    (f : X ⟶ schemeSpace V) (hf : IsProper B S hS f.hom)
    (φ : A →+*
      ↥(GlobalSectionRing
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))))
    (hφ : ∀ a, φ a = pullbackToGlobalFunctions B S hS X V f (α a))
    (F : Modules.{u, u} B S hS X.1 X.2) [IsCoherent B S hS X.1 X.2 F] (I : Ideal A) (p : ℕ) :
    ∃ c₁ : ℕ, ∀ n : ℕ, c₁ ≤ n →
      LinearMap.ker (cohomologyIdealQuotientProj φ F I p n) ≤
        I ^ (n - c₁) • (⊤ : Submodule A (cohomologyRes φ p F)) := by
  obtain ⟨c, -, hc⟩ := exists_cohomologyIdealPower_bounds_of_isReesFinite _ F I p
    (isReesFinite_cohomologyIdealPowerSystem_of_isAffine α f hf φ hφ F I p)
  refine ⟨c, Stacks.AdicCohomologyBound.ker_le_pow_smul_top I _ _ c
    (ker_cohomologyIdealQuotientProj_le _ F I p) fun n hn => ?_⟩
  refine range_cohomologyIdealPowerProj_le _ F I p ?_
  simpa using hc 0 n (Nat.zero_le n) (by lia)

/-- Let `f : X ⟶ V` be a proper morphism to an affine object `V` of the site whose functions are
identified with the Noetherian ring `A` by `α`, and `F` a coherent `𝒪_X`-module. For every `p` and
every `n` there is a `c₂(n) ≥ n` such that
`im (Hᵖ(X, F / Iᵏ F) ⟶ Hᵖ(X, F / Iⁿ F)) = im (Hᵖ(X, F) ⟶ Hᵖ(X, F / Iⁿ F))` for all `k ≥ c₂(n)`. -/
theorem exists_range_cohomologyIdealQuotientTr_eq_of_isAffine [IsNoetherianRing A]
    (f : X ⟶ schemeSpace V) (hf : IsProper B S hS f.hom)
    (φ : A →+*
      ↥(GlobalSectionRing
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))))
    (hφ : ∀ a, φ a = pullbackToGlobalFunctions B S hS X V f (α a))
    (F : Modules.{u, u} B S hS X.1 X.2) [hF : IsCoherent B S hS X.1 X.2 F] (I : Ideal A)
    (p n : ℕ) :
    ∃ c₂ : ℕ, n ≤ c₂ ∧ ∀ (k : ℕ) (h : n ≤ k), c₂ ≤ k →
      LinearMap.range (cohomologyIdealQuotientTr φ F I p h) =
        LinearMap.range (cohomologyIdealQuotientProj φ F I p n) := by
  obtain ⟨c, -, hc⟩ := exists_cohomologyIdealPower_bounds_of_isReesFinite _ F I (p + 1)
    (isReesFinite_cohomologyIdealPowerSystem_of_isAffine α f hf φ hφ F I (p + 1))
  have : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
    isNoetherianRing_of_ringEquiv A α
  have := isLocallyNoetherian_toScheme α
  have hN := isNoetherian_of_isProper_toAffine B S hS V inferInstance f hf
  have : Fact (HasEtaleLocalProperty B S hS X.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hN.2.2⟩
  exact Stacks.AdicCohomologyBound.exists_range_transition_eq_range_proj I _
    (fun m n h => cohomologyIdealQuotientTr _ F I p h) (cohomologyIdealPowerDelta _ F I p)
    (fun m n h => cohomologyIdealPowerTr _ F I (p + 1) h) c
    (fun n => by
      have := isCoherent_idealMultiple φ F (I ^ n) hF
      exact moduleFinite_cohomologyRes_of_isAffine α f hf φ hφ _ (p + 1))
    (fun m n h => cohomologyIdealQuotientTr_comp_proj _ F I p h)
    (fun m n h => cohomologyIdealPowerDelta_comp_tr _ F I p h)
    (ker_cohomologyIdealPowerDelta_le _ F I p)
    (pow_smul_top_cohomologyIdealQuotient _ F I p) hc n

end OverAffine

section Situation

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  {X : AlgebraicSpaces B (Spec (.of A)) hA}

/-- Let `A` be a Noetherian ring, `I ⊆ A` an ideal, `f : X ⟶ Spec A` a proper morphism of
algebraic spaces and `F` a coherent `𝒪_X`-module. For every `p` there is a `c₁ ≥ 0` such that
`ker (Hᵖ(X, F) ⟶ Hᵖ(X, F / Iⁿ F)) ⊆ Iⁿ⁻ᶜ¹ Hᵖ(X, F)` for all `n ≥ c₁`. -/
theorem exists_ker_cohomologyIdealQuotientProj_le [IsNoetherianRing A]
    (f : X ⟶ schemeSpace (baseObject A B hA)) (hf : IsProper B (Spec (.of A)) hA f.hom)
    (F : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) [IsCoherent B (Spec (.of A)) hA X.1 X.2 F]
    (I : Ideal A) (p : ℕ) :
    ∃ c₁ : ℕ, ∀ n : ℕ, c₁ ≤ n →
      LinearMap.ker (cohomologyIdealQuotientProj (baseRingHom A B hA X.1 X.2) F I p n) ≤
        I ^ (n - c₁) • (⊤ : Submodule A (cohomologyRes (baseRingHom A B hA X.1 X.2) p F)) :=
  have : IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj (baseObject A B hA)) :=
    inferInstanceAs (IsAffine (Spec (.of A)))
  exists_ker_cohomologyIdealQuotientProj_le_of_isAffine (V := baseObject A B hA)
    (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv f hf _
    (fun a => (pullbackToGlobalFunctions_baseObject B A hA f a).symm) F I p

/-- Let `A` be a Noetherian ring, `I ⊆ A` an ideal, `f : X ⟶ Spec A` a proper morphism of
algebraic spaces and `F` a coherent `𝒪_X`-module. For every `p` and every `n` there is a
`c₂(n) ≥ n` such that `im (Hᵖ(X, F / Iᵏ F) ⟶ Hᵖ(X, F / Iⁿ F)) = im (Hᵖ(X, F) ⟶ Hᵖ(X, F / Iⁿ F))`
for all `k ≥ c₂(n)`. -/
theorem exists_range_cohomologyIdealQuotientTr_eq [IsNoetherianRing A]
    (f : X ⟶ schemeSpace (baseObject A B hA)) (hf : IsProper B (Spec (.of A)) hA f.hom)
    (F : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) [hF : IsCoherent B (Spec (.of A)) hA X.1 X.2 F]
    (I : Ideal A) (p n : ℕ) :
    ∃ c₂ : ℕ, n ≤ c₂ ∧ ∀ (k : ℕ) (h : n ≤ k), c₂ ≤ k →
      LinearMap.range (cohomologyIdealQuotientTr (baseRingHom A B hA X.1 X.2) F I p h) =
        LinearMap.range (cohomologyIdealQuotientProj (baseRingHom A B hA X.1 X.2) F I p n) :=
  have : IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj (baseObject A B hA)) :=
    inferInstanceAs (IsAffine (Spec (.of A)))
  exists_range_cohomologyIdealQuotientTr_eq_of_isAffine (V := baseObject A B hA)
    (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv f hf _
    (fun a => (pullbackToGlobalFunctions_baseObject B A hA f a).symm) F I p n

/-- Let `A` be a Noetherian ring, `I ⊆ A` an ideal, `f : X ⟶ Spec A` a proper morphism of
algebraic spaces and `F` a coherent `𝒪_X`-module. For every `p` the inverse system
`(Hᵖ(X, F / Iⁿ F))ₙ` satisfies the Mittag-Leffler condition. -/
theorem isMittagLefflerCategorical_cohomologyIdealQuotientTower [IsNoetherianRing A]
    (f : X ⟶ schemeSpace (baseObject A B hA)) (hf : IsProper B (Spec (.of A)) hA f.hom)
    (F : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) [IsCoherent B (Spec (.of A)) hA X.1 X.2 F]
    (I : Ideal A) (p : ℕ) :
    IsMittagLefflerCategorical
      (cohomologyIdealQuotientTower (baseRingHom A B hA X.1 X.2) F I p) :=
  Stacks.AdicCohomologyBound.isMittagLefflerCategorical_of_exists_range_eq_range_proj _
    (cohomologyIdealQuotientProj _ F I p)
    (fun n => exists_range_cohomologyIdealQuotientTr_eq f hf F I p n)

end Situation

end AlgebraicGeometry.Space.C1573

end
