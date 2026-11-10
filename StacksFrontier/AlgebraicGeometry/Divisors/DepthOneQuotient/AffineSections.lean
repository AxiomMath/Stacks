module

public import StacksFrontier.AlgebraicGeometry.Divisors.DepthOneQuotient.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.Norm.NonvanishingLocus
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.RingTheory.LocalCohomology.SupportedSectionsProZero
public import StacksFrontier.RingTheory.Serre.Defs

/-!
# Sections of the kernel of a depth-one quotient over an affine open

Let `X` be a scheme, `T ⊆ X` a subset and `φ : ℱ ⟶ ℱ'` a depth-one quotient along `T`
(`AlgebraicGeometry.IsDepthOneQuotient`): `ℱ'` is coherent, `φ` is surjective, an isomorphism on
stalks outside `T`, and `ℱ'` has depth at least one at the points of `T`. On an affine open
`U = Spec Γ(X, U)` the kernel of `φ` on sections over `U` is the submodule of sections with
support in `T`, that is, `H⁰_T(Γ(ℱ, U))` with `T` read as a set of primes of `Γ(X, U)`
(Stacks, Tag 0DX3 and its proof).

A section killed by `φ` has zero germ at every point outside `T`, where `φ` is an isomorphism on
stalks, so a function not vanishing at the point kills it. Conversely the image of a section
supported in `T` is supported in `T`; were it nonzero, a minimal prime over its annihilator would
be an associated prime lying in `T`, hence, localizing, the maximal ideal of the local ring would
be an associated prime of the stalk of `ℱ'` there, contradicting depth at least one.

## Main definitions

* `AlgebraicGeometry.IsAffineOpen.primesOf` — the primes of `Γ(X, U)` whose points lie in a
  given subset of `X`.

## Main results

* `AlgebraicGeometry.ker_sectionsLinearMap_eq_sectionsWithSupportIn` — the kernel on sections
  over an affine open of a depth-one quotient map.

## References

* [Stacks Project, Tag 0DX3](https://stacks.math.columbia.edu/tag/0DX3)
* [Stacks Project, Tag 0EJE](https://stacks.math.columbia.edu/tag/0EJE)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace Stacks.LocalCohomology
open Stacks.ModuleStalkSpecialization Module.associatedPrimes

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

namespace IsAffineOpen

variable {U : X.Opens} (hU : IsAffineOpen U)

/-- The primes of `Γ(X, U)` whose points lie in a subset `T` of `X`. -/
def primesOf (T : Set X) : Set (PrimeSpectrum Γ(X, U)) := {p | hU.fromSpec p ∈ T}

/-- The primes of a specialization-stable subset form a specialization-stable set of primes. -/
theorem stableUnderSpecialization_primesOf {T : Set X} (hT : StableUnderSpecialization T) :
    StableUnderSpecialization (hU.primesOf T) := fun _ _ h hp =>
  hT (h.map hU.fromSpec.continuous) hp

end IsAffineOpen

/-- **The kernel on affine sections of a depth-one quotient map is the submodule of sections with
support in `T`.** -/
theorem ker_sectionsLinearMap_eq_sectionsWithSupportIn [IsLocallyNoetherian X] (T : Set X)
    {E E' : X.Modules} [E.IsQuasicoherent] (φ : E ⟶ E') (hφ : IsDepthOneQuotient T φ)
    {U : X.Opens} (hU : IsAffineOpen U) :
    LinearMap.ker (Scheme.Modules.sectionsLinearMap φ U) =
      sectionsWithSupportIn Γ(X, U) (hU.primesOf T) Γ(E, U) := by
  have : E'.IsCoherent := hφ.1
  have : E'.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent E').1
  have : E'.IsFiniteType :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent E').2
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  ext s
  rw [LinearMap.mem_ker, Scheme.Modules.sectionsLinearMap_apply, mem_sectionsWithSupportIn_iff]
  constructor
  · intro hs p hp
    by_contra hpT
    have hyU := hU.fromSpec_mem p
    have hiso := hφ.2.2.1 _ hpT
    have hinj : Function.Injective
        ((TopCat.Presheaf.stalkFunctor Ab.{u} (hU.fromSpec p)).map φ.mapPresheaf) :=
      ((ConcreteCategory.isIso_iff_bijective _).mp hiso).1
    have hgerm : E.presheaf.germ U _ hyU s = E.presheaf.germ U _ hyU 0 := by
      apply hinj
      rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, TopCat.Presheaf.stalkFunctor_map_germ_apply,
        map_zero]
      change E'.presheaf.germ U _ hyU (φ.app U s) = _
      rw [hs, map_zero]
    obtain ⟨c, hc, hcs⟩ := exists_smul_eq_of_germ_eq E hU hyU s 0 hgerm
    rw [smul_zero, hU.primeIdealOf_fromSpec _ (hU.fromSpec_mem p)] at *
    exact hc (hp ((Ideal.mem_torsionOf_iff s c).mpr hcs))
  · intro hs
    have hu : φ.app U s ∈ sectionsWithSupportIn Γ(X, U) (hU.primesOf T) Γ(E', U) :=
      map_mem_sectionsWithSupportIn _ (Scheme.Modules.sectionsLinearMap φ U)
        ((mem_sectionsWithSupportIn_iff _ _ _ _).mpr hs)
    by_contra hne
    have htop : Ideal.torsionOf Γ(X, U) Γ(E', U) (φ.app U s) ≠ ⊤ := by
      intro h
      have h1 := (Ideal.mem_torsionOf_iff (φ.app U s) 1).mp (h ▸ Submodule.mem_top)
      exact hne (by simpa using h1)
    obtain ⟨⟨p₀, hp₀⟩⟩ := Ideal.nonempty_minimalPrimes htop
    have hp₀prime : p₀.IsPrime := hp₀.1.1
    let p : PrimeSpectrum Γ(X, U) := ⟨p₀, hp₀prime⟩
    have hpT : hU.fromSpec p ∈ T :=
      (mem_sectionsWithSupportIn_iff _ _ _ _).mp hu hp₀.1.2
    have hass : p₀ ∈ associatedPrimes Γ(X, U) Γ(E', U) :=
      mem_associatedPrimes_of_mem_minimalPrimes_torsionOf _ hp₀
    have hyU := hU.fromSpec_mem p
    set y := hU.fromSpec p
    let := stalkModule E' y
    let := sectionsStalkModule E' hyU
    let : Algebra Γ(X, U) (X.presheaf.stalk y) := (X.presheaf.germ U y hyU).hom.toAlgebra
    have := isScalarTower_sectionsStalk E' hyU
    have hloc : IsLocalization.AtPrime (X.presheaf.stalk y) (hU.primeIdealOf ⟨y, hyU⟩).asIdeal :=
      hU.isLocalization_stalk ⟨y, hyU⟩
    have hlocM := isLocalizedModule_germₗ E' hU hyU
    rw [hU.primeIdealOf_fromSpec _ hyU] at hloc hlocM
    have hmax : IsLocalRing.maximalIdeal (X.presheaf.stalk y) ∈
        associatedPrimes (X.presheaf.stalk y) (E'.presheaf.stalk y) := by
      apply mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
        p.asIdeal.primeCompl (germₗ E' hyU)
      have h := IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk y) p.asIdeal
      simp only [Ideal.under] at h
      rw [h]
      exact hass
    have : Module.Finite (X.presheaf.stalk y) (E'.presheaf.stalk y) :=
      _root_.SheafOfModules.finite_stalk X.sheaf E' y
    have hdepth : (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk y)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) (E'.presheaf.stalk y) := hφ.2.2.2 y hpT
    have h0 := (Module.depth_eq_zero_iff_maximalIdeal_mem_associatedPrimes).mpr hmax
    rw [h0] at hdepth
    exact absurd hdepth (by simp)

end AlgebraicGeometry

end
