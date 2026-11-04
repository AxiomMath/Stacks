module

public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerCohomologyReesFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperModuleCohomologyFiniteAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyAdicUniformBounds
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionLiftGluing
public import StacksFrontier.RingTheory.AdicCompletion.IntertwinedFiltrationEventualRange
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# The theorem on formal functions in degree zero for a proper algebraic space

Let `V` be an affine locally Noetherian object of the big fppf site over a scheme `S`, write
`A = Γ(V, 𝒪_V)`, let `f : X ⟶ V` be a proper morphism of algebraic spaces, `F` a coherent
`𝒪_X`-module and `I ⊆ A` an ideal.  Write `Iⁿ F` for the image of `∐_{a ∈ Iⁿ} F ⟶ F` and
`F / Iⁿ F` for its cokernel (`AlgebraicGeometry.Space.idealQuotient`).  This file proves that
the maps `H⁰(X, F) ⟶ H⁰(X, F / Iⁿ F)` induce an isomorphism of `A`-modules
`H⁰(X, F)^∧_I ≅ limₙ H⁰(X, F / Iⁿ F)`, the case `p = 0` of the theorem on formal functions
(Stacks 08AZ), with no hypothesis beyond the source's.

The proof is the source's (Stacks 08AY and 08AZ).  The long exact cohomology sequences of the
short exact sequences `0 ⟶ Iⁿ F ⟶ F ⟶ F / Iⁿ F ⟶ 0` (the `δ`-functor structure of the right
derived functors of the global sections, Stacks 010Q) together with the uniform bounds of
Stacks 08AX for `H⁰` and `H¹` of the modules `Iⁿ F`, and the finiteness of `H¹(X, Iⁿ F)`
(Stacks 08AS), give the two clauses of Stacks 08AY that the comparison needs; the comparison
itself is `Stacks.IntertwinedFiltration.adicCompletionEquivTowerLimitOfEventualRange`.

## Main definitions

* `AlgebraicGeometry.Space.sectionsTower`: `n ↦ H⁰(X, F / Iⁿ F)`, with transition maps
  `sectionsTowerMap` and projections `sectionsTowerProj` from `H⁰(X, F)`.
* `AlgebraicGeometry.Space.adicCompletionSectionsEquiv`: the isomorphism
  `H⁰(X, F)^∧_I ≅ limₙ H⁰(X, F / Iⁿ F)`.

## Main results

* `AlgebraicGeometry.Space.adicCompletionSectionsEquiv_of`: the isomorphism is the one defined
  by the projections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] hasInjectiveResolutions_modules

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Tower

variable {X : AlgebraicSpaces B S hS} {A : Type u} [CommRing A]
  (φ : A →+* ↥(GlobalSectionRing ((Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS X.1 X.2).O))))
  (F : Modules.{u, u} B S hS X.1 X.2) (I : Ideal A)

/-- The `n`-th term `H⁰(X, F / Iⁿ F)` of the tower of the theorem on formal functions. -/
abbrev sectionsTower (n : ℕ) : ModuleCat.{u + 1} A :=
  cohomologyRes φ 0 (idealQuotient φ F (I ^ n))

/-- The transition map `H⁰(X, F / Iⁿ F) ⟶ H⁰(X, F / Iᵐ F)` for `m ≤ n`. -/
abbrev sectionsTowerMap (m n : ℕ) (h : m ≤ n) :
    sectionsTower φ F I n →ₗ[A] sectionsTower φ F I m :=
  cohomologyResMap φ 0 (idealQuotientMap φ F (Ideal.pow_le_pow_right h : I ^ n ≤ I ^ m))

/-- The map `H⁰(X, F) ⟶ H⁰(X, F / Iⁿ F)`. -/
abbrev sectionsTowerProj (n : ℕ) : cohomologyRes φ 0 F →ₗ[A] sectionsTower φ F I n :=
  cohomologyResMap φ 0 (idealQuotientπ φ F (I ^ n))

/-- For `m ≤ n`, the composite map `H⁰(X, F) ⟶ H⁰(X, F / Iⁿ F) ⟶ H⁰(X, F / Iᵐ F)` is the map
`H⁰(X, F) ⟶ H⁰(X, F / Iᵐ F)`. -/
theorem sectionsTowerMap_comp_proj (m n : ℕ) (h : m ≤ n) :
    (sectionsTowerMap φ F I m n h).comp (sectionsTowerProj φ F I n) =
      sectionsTowerProj φ F I m := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, cohomologyResMap_comp_apply, idealQuotientπ_idealQuotientMap]

/-- An element of `Iⁿ` acts by zero on `H⁰(X, F / Iⁿ F)`. -/
private theorem smul_sectionsTower_eq_zero {n : ℕ} {a : A} (ha : a ∈ I ^ n)
    (x : sectionsTower φ F I n) : a • x = 0 := by
  rw [← cohomologyResMap_globalSmul, globalSmul_idealQuotient_eq_zero φ F _ ha,
    cohomologyResMap_zero, LinearMap.zero_apply]

/-- The submodule `Iⁿ H⁰(X, F)` lies in the kernel of `H⁰(X, F) ⟶ H⁰(X, F / Iⁿ F)`. -/
theorem pow_smul_top_le_ker_sectionsTowerProj (n : ℕ) :
    I ^ n • (⊤ : Submodule A (cohomologyRes φ 0 F)) ≤
      LinearMap.ker (sectionsTowerProj φ F I n) :=
  Submodule.smul_le.2 fun _ ha x _ => by
    rw [LinearMap.mem_ker, map_smul, smul_sectionsTower_eq_zero φ F I ha]

/-- The `A`-module `H⁰(X, F / Iⁿ F)` is annihilated by `Iⁿ`. -/
theorem pow_smul_top_sectionsTower_eq_bot (n : ℕ) :
    I ^ n • (⊤ : Submodule A (sectionsTower φ F I n)) = ⊥ :=
  eq_bot_iff.2 (Submodule.smul_le.2 fun _ ha x _ => smul_sectionsTower_eq_zero φ F I ha x)

/-- The map `H¹(X, Iⁿ F) ⟶ H¹(X, Iᵐ F)` induced by the inclusion, for `m ≤ n`, as the transition
of `n ↦ H¹(X, Iⁿ F)`. -/
abbrev connectingTowerMap (m n : ℕ) (h : m ≤ n) :
    cohomologyIdealPower φ F I 1 n →ₗ[A] cohomologyIdealPower φ F I 1 m :=
  cohomologyIdealPowerTr φ F I 1 h

/-- **The long exact sequences of the short exact sequences `0 ⟶ Iⁿ F ⟶ F ⟶ F / Iⁿ F ⟶ 0`**, in
the three places the theorem on formal functions in degree zero uses them: there are connecting
maps `δₙ : H⁰(X, F / Iⁿ F) ⟶ H¹(X, Iⁿ F)`, natural in `n`, with
`ker δₙ ⊆ im (H⁰(X, F) ⟶ H⁰(X, F / Iⁿ F))`, and
`ker (H⁰(X, F) ⟶ H⁰(X, F / Iⁿ F)) ⊆ im (H⁰(X, Iⁿ F) ⟶ H⁰(X, F))`. -/
theorem exists_sectionsTower_connecting :
    ∃ δ : ∀ n, sectionsTower φ F I n →ₗ[A] cohomologyIdealPower φ F I 1 n,
      (∀ (m n : ℕ) (h : m ≤ n), (δ m).comp (sectionsTowerMap φ F I m n h) =
        (connectingTowerMap φ F I m n h).comp (δ n)) ∧
      (∀ n, LinearMap.ker (δ n) ≤ LinearMap.range (sectionsTowerProj φ F I n)) ∧
      (∀ n, LinearMap.ker (sectionsTowerProj φ F I n) ≤
        LinearMap.range (cohomologyIdealPowerProj φ F I 0 n)) := by
  have := enoughInjectives_modules B S hS X.1 X.2
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
  let := HasDerivedCategory.standard (ModuleCat.{u + 1} ↥(GlobalSectionRing
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))))
  let Δ := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (globalSectionsFunctor.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)))
  refine ⟨fun n => ((ModuleCat.restrictScalars φ).map
    (Δ.δ (idealShortComplex_shortExact φ F (I ^ n)) 0)).hom, ?_, ?_, ?_⟩
  · intro m n h
    exact LinearMap.ext fun x => congrArg (fun g => g.hom x)
      (Δ.δ_naturality (idealShortComplex_shortExact φ F (I ^ n))
        (idealShortComplex_shortExact φ F (I ^ m))
        (idealShortComplexMap φ F (Ideal.pow_le_pow_right h : I ^ n ≤ I ^ m)) 0)
  · intro n x hx
    have hex := Δ.exact_δ₁ (idealShortComplex_shortExact φ F (I ^ n)) 0
    rw [ShortComplex.moduleCat_exact_iff] at hex
    exact hex x hx
  · intro n x hx
    have hex := Δ.exact_map (idealShortComplex_shortExact φ F (I ^ n)) 0
    rw [ShortComplex.moduleCat_exact_iff] at hex
    exact hex x hx

end Tower

section OverAffine

variable (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [_root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
  {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace V) (hf : IsProper B S hS f.hom)
  (F : Modules.{u, u} B S hS X.1 X.2) [IsCoherent B S hS X.1 X.2 F]
  (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))

/-- The ring `Γ(V, 𝒪_V)` of global sections of an affine locally Noetherian `V` is Noetherian. -/
instance isNoetherianRing_globalSections_of_isAffine :
    IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
  _root_.AlgebraicGeometry.IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] in
include hf in
/-- An algebraic space proper over an affine locally Noetherian object of the site is
étale-locally Noetherian. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_of_isProper_of_isAffine :
    HasEtaleLocalProperty B S hS X.1
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian T) :=
  hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType B S hS X.2
    (isAlgebraicSpace_yoneda B S hS V) f.hom hf.2.1.1
    (hasEtaleLocalProperty_isLocallyNoetherian_yoneda inferInstance)

include hf in
/-- **The two clauses of Stacks 08AY used by the theorem on formal functions in degree zero**:
there is a `c` with `ker (H⁰(X, F) ⟶ H⁰(X, F / Iⁿ F)) ⊆ I^(n - c) H⁰(X, F)` for `n ≥ c`, and for
every `n` the images of `H⁰(X, F / Iᵏ F) ⟶ H⁰(X, F / Iⁿ F)` equal the image of `H⁰(X, F)` for
all large `k`. -/
theorem exists_sectionsTower_bounds :
    ∃ c : ℕ, (∀ n, c ≤ n → LinearMap.ker (sectionsTowerProj (pullbackRingHom B V f) F I n) ≤
        I ^ (n - c) • (⊤ : Submodule _ (cohomologyRes (pullbackRingHom B V f) 0 F))) ∧
      ∀ n : ℕ, ∃ c₂ : ℕ, n ≤ c₂ ∧ ∀ (k : ℕ) (h : n ≤ k), c₂ ≤ k →
        LinearMap.range (sectionsTowerMap (pullbackRingHom B V f) F I n k h) =
          LinearMap.range (sectionsTowerProj (pullbackRingHom B V f) F I n) := by
  have : Fact (HasEtaleLocalProperty B S hS X.1
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian T)) :=
    ⟨hasEtaleLocalProperty_isLocallyNoetherian_of_isProper_of_isAffine V f hf⟩
  let φ := pullbackRingHom B V f
  have hrees : ∀ p, (cohomologyIdealPowerSystem φ F I p).IsReesFinite := fun p =>
    isReesFinite_cohomologyIdealPowerSystem_of_isAffine (RingEquiv.refl _) f hf φ (fun _ => rfl)
      F I p
  obtain ⟨c₀, -, h₀⟩ := exists_cohomologyIdealPower_bounds_of_isReesFinite φ F I 0 (hrees 0)
  obtain ⟨c₁, -, h₁⟩ := exists_cohomologyIdealPower_bounds_of_isReesFinite φ F I 1 (hrees 1)
  obtain ⟨δ, hladder, hexact, hexactM⟩ := exists_sectionsTower_connecting φ F I
  refine ⟨c₀, fun n hn => ?_, fun n => ?_⟩
  · intro x hx
    obtain ⟨y, rfl⟩ := hexactM n hx
    have hy : cohomologyIdealPowerTr φ F I 0 (Nat.zero_le n) y ∈
        I ^ (n - 0 - c₀) • (⊤ : Submodule _ (cohomologyIdealPower φ F I 0 0)) :=
      h₀ 0 n (Nat.zero_le n) (by omega) ⟨y, rfl⟩
    have hι : cohomologyIdealPowerProj φ F I 0 n y = cohomologyResMap φ 0
        (idealMultipleι φ F (I ^ 0)) (cohomologyIdealPowerTr φ F I 0 (Nat.zero_le n) y) := by
      rw [cohomologyResMap_comp_apply,
        idealMultipleMap_one_ι φ F (Ideal.pow_le_pow_right (Nat.zero_le n))]
    rw [hι, show n - c₀ = n - 0 - c₀ by omega]
    have hmap :=
      Submodule.mem_map_of_mem (f := cohomologyResMap φ 0 (idealMultipleι φ F (I ^ 0))) hy
    rw [Submodule.map_smul''] at hmap
    exact Submodule.smul_mono le_rfl le_top hmap
  · have := isCoherent_idealMultiple φ F
    exact Stacks.AdicCohomologyBound.exists_range_transition_eq_range_proj I
      (sectionsTowerProj φ F I) (sectionsTowerMap φ F I) δ (connectingTowerMap φ F I) c₁
      (fun k => by
        have := isCoherent_idealMultiple φ F (I ^ k) inferInstance
        exact moduleFinite_cohomology_of_isProper_of_isAffine B V f hf _ 1)
      (sectionsTowerMap_comp_proj φ F I) hladder hexact (pow_smul_top_sectionsTower_eq_bot φ F I)
      h₁ n

/-- **The theorem on formal functions in degree zero** for a proper algebraic space over an
affine locally Noetherian object `V` of the site: for a coherent `𝒪_X`-module `F` and an ideal
`I` of `A = Γ(V, 𝒪_V)`, the maps `H⁰(X, F) ⟶ H⁰(X, F / Iⁿ F)` induce an isomorphism
`H⁰(X, F)^∧_I ≅ limₙ H⁰(X, F / Iⁿ F)` of `A`-modules. -/
def adicCompletionSectionsEquiv :
    AdicCompletion I (cohomologyRes (pullbackRingHom B V f) 0 F)
      ≃ₗ[Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
      Stacks.IntertwinedFiltration.towerLimit
        (fun n : ℕ => (sectionsTower (pullbackRingHom B V f) F I n : Type (u + 1)))
        (sectionsTowerMap (pullbackRingHom B V f) F I) :=
  Stacks.IntertwinedFiltration.adicCompletionEquivTowerLimitOfEventualRange _ _ _ I
    (exists_sectionsTower_bounds V f hf F I).choose
    (sectionsTowerMap_comp_proj _ F I) (pow_smul_top_le_ker_sectionsTowerProj _ F I)
    (exists_sectionsTower_bounds V f hf F I).choose_spec.1
    (exists_sectionsTower_bounds V f hf F I).choose_spec.2

/-- **The isomorphism of the theorem on formal functions is the one defined by the projections**:
it carries the image in the completion of `x ∈ H⁰(X, F)` to the family of its images in the
`H⁰(X, F / Iⁿ F)`. -/
theorem adicCompletionSectionsEquiv_of (x : cohomologyRes (pullbackRingHom B V f) 0 F) (n : ℕ) :
    Stacks.IntertwinedFiltration.towerLimit.proj n
        (adicCompletionSectionsEquiv V f hf F I (AdicCompletion.of I _ x)) =
      sectionsTowerProj (pullbackRingHom B V f) F I n x :=
  rfl

end OverAffine

end AlgebraicGeometry.Space
