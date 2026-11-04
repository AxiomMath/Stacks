module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistCohomologyMonomial
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.ZeroTwist

/-!
# The global functions on projective space are the coefficients

Let `R` be a commutative ring and `ℙⁿ_R = Proj R[T₀, …, Tₙ]`. The structure morphism
`ℙⁿ_R ⟶ Spec R` pulls a coefficient back to a global function, giving the ring homomorphism
`Stacks.ProjectiveSpace.Cohomology.coeffToGlobalSections`. This file shows it is an isomorphism:

`R ≅ Γ(ℙⁿ_R, 𝒪)`.

The two inputs are Serre's computation `H⁰(ℙⁿ_R, 𝒪) = R`, already available as
`Stacks.ProjectiveSpace.Cohomology.twistCohomologyIsoHomogeneous` in degree `0` for the twist
`𝒪(0)`, and the fact that sections over an open are left exact, so their zeroth right derived
functor is themselves: `CategoryTheory.Functor.rightDerivedZeroIsoSelf`. Together they make
`Γ(ℙⁿ_R, 𝒪)` free of rank one as an `R`-module, and a commutative ring that is free of rank one
over `R` through a ring homomorphism has that homomorphism bijective.

## Main definitions

* `Stacks.ProjectiveSpace.Cohomology.twistCohomologyZeroIsoGlobalSections` — the degree-zero
  cohomology of `𝒪(0)` is the ring of global functions, as a module over the coefficients.
* `Stacks.ProjectiveSpace.Cohomology.globalSectionsLinearEquivCoeff` — the global functions on
  `ℙⁿ_R` are free of rank one as an `R`-module.
* `Stacks.ProjectiveSpace.Cohomology.coeffRingEquivGlobalSections` — **`Γ(ℙⁿ_R, 𝒪) = R`**, as
  rings.

## Main results

* `Stacks.ProjectiveSpace.Cohomology.bijective_of_addEquiv_smul` — a commutative ring free of
  rank one over `R` through a ring homomorphism has that homomorphism bijective.
* `Stacks.ProjectiveSpace.Cohomology.bijective_coeffToGlobalSections` — the pullback of
  coefficients to global functions is bijective.

## Implementation notes

Left exactness of sections enters only as the `PreservesFiniteLimits` instance
`Stacks.Cohomology.preservesFiniteLimits_sectionsFunctor`, which is what
`CategoryTheory.Functor.rightDerivedZeroIsoSelf` asks for; no explicit exactness hypothesis is
carried.

The `R`-module structure on the global functions is the one `twistCohomology` already uses,
namely restriction of scalars along `Stacks.ProjectiveSpace.Cohomology.coeffScalar`, which is
`coeffToGlobalSections` with its target spelled through the sheaf of rings that the twists are
modules over. The sections of `CategoryTheory.SheafOfModules.unit` over an open *are* the ring of
sections there, by definition, so the passage from `𝒪(0)` to `𝒪` is the single isomorphism
`Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit`.

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ProjEulerSequence Stacks.ProjectiveCohomology

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.ProjectiveSpace.Cohomology

/-! ### Rank one forces the structure map to be an isomorphism -/

/-- **A commutative ring free of rank one over `R` has its structure map bijective.** If
`φ : R →+* S` makes `S` free of rank one as an `R`-module, then a generator `x` satisfies
`1 = φ u * x` and `x * x = φ c * x` for unique `u, c : R`, and comparing coefficients of `x` in
`x = φ (u * c) * x` gives `u * c = 1`; since `e ∘ φ` is multiplication by `u`, it is bijective. -/
theorem bijective_of_addEquiv_smul {R : Type u} {S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (e : S ≃+ R) (he : ∀ (r : R) (x : S), e (φ r * x) = r * e x) :
    Function.Bijective φ := by
  obtain ⟨x, hex⟩ : ∃ x : S, e x = 1 := ⟨e.symm 1, e.apply_symm_apply 1⟩
  have hgen : ∀ y : S, y = φ (e y) * x := fun y => e.injective (by rw [he, hex, mul_one])
  obtain ⟨u, hu⟩ : ∃ u : R, (1 : S) = φ u * x := ⟨_, hgen 1⟩
  obtain ⟨c, hc⟩ : ∃ c : R, x * x = φ c * x := ⟨_, hgen _⟩
  have heone : e 1 = u := by rw [hu, he, hex, mul_one]
  have hcomp : ∀ r : R, e (φ r) = r * u := fun r => by
    have h := he r 1
    rwa [mul_one, heone] at h
  have huc : u * c = 1 := by
    have h := congrArg e (show x = φ (u * c) * x by
      rw [map_mul]
      linear_combination x * hu + φ u * hc)
    rw [he, hex, mul_one] at h
    exact h.symm
  refine ⟨fun a b hab => ?_, fun s => ⟨e s * c, e.injective ?_⟩⟩
  · have h : a * u = b * u := by rw [← hcomp, ← hcomp, hab]
    linear_combination c * h - (a - b) * huc
  · rw [hcomp]
    linear_combination e s * huc

/-! ### The global functions as a module over the coefficients -/

variable (R : Type u) [CommRing R] (n : ℕ)

/-- **`H⁰(ℙⁿ_R, 𝒪(0))` is the ring of global functions**, as a module over the coefficients:
sections over an open are left exact, so their zeroth right derived functor is themselves, and
the zeroth twist is the structure sheaf. -/
def twistCohomologyZeroIsoGlobalSections :
    twistCohomology R n 0 0 ≅
      (ModuleCat.restrictScalars.{u} (coeffScalar R n)).obj
        (ModuleCat.of Γ(AlgebraicGeometry.Proj (polyGrading R n), ⊤)
          Γ(AlgebraicGeometry.Proj (polyGrading R n), ⊤)) :=
  (ModuleCat.restrictScalars.{u} (coeffScalar R n)).mapIso
    ((Stacks.Cohomology.sectionsFunctor (AlgebraicGeometry.Proj (polyGrading R n))
        ⊤).rightDerivedZeroIsoSelf.app _ ≪≫
      (Stacks.Cohomology.sectionsFunctor (AlgebraicGeometry.Proj (polyGrading R n)) ⊤).mapIso
        (twistingSheafZeroIsoUnit (polyGrading R n)))

/-- **`H⁰(ℙⁿ_R, 𝒪(0))` is `R`**: the degree-`0` row of [Stacks, Tag 01XT] at the zeroth twist,
where the degree-zero homogeneous polynomials are the constants. -/
def twistCohomologyZeroIsoCoeff : twistCohomology R n 0 0 ≅ ModuleCat.of R R :=
  twistCohomologyIsoHomogeneous R n 0 le_rfl ≪≫
    LinearEquiv.toModuleIso
      ((LinearEquiv.ofEq _ _ (by
          rw [show ((0 : ℤ)).toNat = 0 from rfl, MvPolynomial.homogeneousSubmodule_zero,
            Submodule.one_eq_range])).trans
        (LinearEquiv.ofInjective (Algebra.linearMap R (MvPolynomial (Fin (n + 1)) R))
          (fun _ _ hxy => MvPolynomial.C_injective _ _ hxy)).symm)

/-- **The global functions on `ℙⁿ_R` are free of rank one as an `R`-module**, the coefficients
acting through the structure morphism `ℙⁿ_R ⟶ Spec R`. -/
def globalSectionsLinearEquivCoeff :
    (ModuleCat.restrictScalars.{u} (coeffScalar R n)).obj
        (ModuleCat.of Γ(AlgebraicGeometry.Proj (polyGrading R n), ⊤)
          Γ(AlgebraicGeometry.Proj (polyGrading R n), ⊤)) ≃ₗ[R] R :=
  ((twistCohomologyZeroIsoGlobalSections R n).symm ≪≫
    twistCohomologyZeroIsoCoeff R n).toLinearEquiv

/-! ### The ring isomorphism -/

/-- **The pullback of coefficients to global functions on `ℙⁿ_R` is bijective.** The global
functions are free of rank one over `R`, and the pullback of a coefficient is that coefficient
acting on `1`. -/
theorem bijective_coeffToGlobalSections :
    Function.Bijective (coeffToGlobalSections R n) :=
  bijective_of_addEquiv_smul (coeffToGlobalSections R n)
    (globalSectionsLinearEquivCoeff R n).toAddEquiv
    fun r x => (globalSectionsLinearEquivCoeff R n).map_smul r x

/-- **`Γ(ℙⁿ_R, 𝒪) = R`.** The global functions on projective space over `R` are the
coefficients, through the structure morphism `ℙⁿ_R ⟶ Spec R`. -/
def coeffRingEquivGlobalSections :
    R ≃+* Γ(AlgebraicGeometry.Proj (polyGrading R n), ⊤) :=
  RingEquiv.ofBijective (coeffToGlobalSections R n) (bijective_coeffToGlobalSections R n)

end Stacks.ProjectiveSpace.Cohomology

end
