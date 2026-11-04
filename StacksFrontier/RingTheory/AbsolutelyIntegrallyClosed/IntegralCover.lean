module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import StacksFrontier.RingTheory.AbsolutelyIntegrallyClosed.Absolute

/-!
# An absolutely integrally closed integral cover of an arbitrary ring

Every commutative ring `A` admits an integral ring map `A → B` with `B` absolutely integrally
closed whose map on spectra is surjective: writing `A = ℤ[x_a]/J`, with one variable for every
element of `A`, and letting `R` be the absolute integral closure of the domain `ℤ[x_a]`, the
ring `B = R/JR` works.

## Main results

* `exists_isAbsolutelyIntegrallyClosed_isIntegral_comap_surjective`: the cover exists.

## References

* [Stacks Project, Tag 09ZD](https://stacks.math.columbia.edu/tag/09ZD)
-/

@[expose] public section

universe u

open Polynomial

namespace Stacks.AbsolutelyIntegrallyClosed

variable (A : Type u) [CommRing A]

/-- The evaluation `ℤ[x_a]_{a ∈ A} → A`, `x_a ↦ a`, presenting `A` as a quotient of a domain. -/
noncomputable def polynomialPresentation : MvPolynomial A ℤ →+* A :=
  MvPolynomial.eval₂Hom (Int.castRingHom A) id

/-- The presentation `ℤ[x_a]_{a ∈ A} → A` is surjective. -/
theorem polynomialPresentation_surjective :
    Function.Surjective (polynomialPresentation A) :=
  fun a => ⟨MvPolynomial.X a, MvPolynomial.eval₂Hom_X' _ _ a⟩

/-- The extension `JR` to the absolute integral closure `R` of `ℤ[x_a]` of the kernel `J` of the
presentation. -/
noncomputable abbrev integralCoverIdeal : Ideal (absoluteIntegralClosure (MvPolynomial A ℤ)) :=
  (RingHom.ker (polynomialPresentation A)).map (algebraMap _ _)

/-- The ring `R/JR`, an absolutely integrally closed integral cover of `A`. -/
abbrev IntegralCover : Type u :=
  absoluteIntegralClosure (MvPolynomial A ℤ) ⧸ integralCoverIdeal A

/-- The structure map `A = ℤ[x_a]/J → R/JR`. -/
noncomputable def integralCoverMap : A →+* IntegralCover A :=
  RingHom.comp (Ideal.quotientMap (integralCoverIdeal A)
      (algebraMap (MvPolynomial A ℤ) (absoluteIntegralClosure (MvPolynomial A ℤ)))
      (Ideal.le_comap_map (I := RingHom.ker (polynomialPresentation A))))
    ((RingHom.quotientKerEquivOfSurjective
      (polynomialPresentation_surjective A)).symm : A →+* _)

/-- The structure map `A → R/JR` sends the image of `p ∈ ℤ[x_a]` in `A` to the class of `p`. -/
theorem integralCoverMap_polynomialPresentation (p : MvPolynomial A ℤ) :
    integralCoverMap A (polynomialPresentation A p) =
      Ideal.Quotient.mk (integralCoverIdeal A) (algebraMap _ _ p) := by
  have h : (RingHom.quotientKerEquivOfSurjective (polynomialPresentation_surjective A)).symm
      (polynomialPresentation A p) = Ideal.Quotient.mk _ p :=
    RingEquiv.symm_apply_eq _ |>.mpr
      (RingHom.quotientKerEquivOfSurjective_apply_mk _ p).symm
  simp only [integralCoverMap, RingHom.comp_apply, RingHom.coe_coe, h, Ideal.quotientMap_mk]

/-- The ring `R/JR` is absolutely integrally closed. -/
theorem isAbsolutelyIntegrallyClosed_integralCover :
    IsAbsolutelyIntegrallyClosed (IntegralCover A) :=
  isAbsolutelyIntegrallyClosed_quotient _ _
    (absoluteIntegralClosure.isAbsolutelyIntegrallyClosed (MvPolynomial A ℤ))

/-- The structure map `A → R/JR` is integral. -/
theorem integralCoverMap_isIntegral : (integralCoverMap A).IsIntegral := by
  have hι : (algebraMap (MvPolynomial A ℤ)
      (absoluteIntegralClosure (MvPolynomial A ℤ))).IsIntegral :=
    fun r => Algebra.IsIntegral.isIntegral (R := MvPolynomial A ℤ) r
  have h₂ : (Ideal.quotientMap (integralCoverIdeal A)
      (algebraMap (MvPolynomial A ℤ) (absoluteIntegralClosure (MvPolynomial A ℤ)))
      (Ideal.le_comap_map (I := RingHom.ker (polynomialPresentation A)))).IsIntegral := by
    refine RingHom.IsIntegral.tower_top (Ideal.Quotient.mk _) _ ?_
    rw [Ideal.quotientMap_comp_mk]
    exact RingHom.IsIntegral.trans _ _ hι
      (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective)
  have h₁ : ((RingHom.quotientKerEquivOfSurjective (polynomialPresentation_surjective A)).symm :
      A →+* MvPolynomial A ℤ ⧸ RingHom.ker (polynomialPresentation A)).IsIntegral :=
    RingHom.isIntegral_of_surjective _ (RingEquiv.surjective _)
  exact RingHom.IsIntegral.trans _ _ h₁ h₂

/-- Every prime of `A` is the contraction of a prime of `R/JR`. -/
theorem exists_comap_integralCoverMap_eq (𝔭 : Ideal A) [𝔭.IsPrime] :
    ∃ Q : Ideal (IntegralCover A), Q.IsPrime ∧ Q.comap (integralCoverMap A) = 𝔭 := by
  let π := polynomialPresentation A
  let ι := algebraMap (MvPolynomial A ℤ) (absoluteIntegralClosure (MvPolynomial A ℤ))
  let 𝔮 : Ideal (MvPolynomial A ℤ) := 𝔭.comap π
  have h𝔮J : RingHom.ker π ≤ 𝔮 := fun p hp => by
    simp only [𝔮, Ideal.mem_comap, (RingHom.mem_ker).mp hp, Submodule.zero_mem]
  have hker : RingHom.ker ι ≤ 𝔮 := (RingHom.injective_iff_ker_eq_bot ι).mp
    (absoluteIntegralClosure.algebraMap_injective (MvPolynomial A ℤ)) ▸ bot_le
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (S := absoluteIntegralClosure (MvPolynomial A ℤ)) 𝔮 ⊥ (by rwa [← RingHom.ker_eq_comap_bot])
  have hJQ : integralCoverIdeal A ≤ Q := Ideal.map_le_iff_le_comap.mpr (hQc ▸ h𝔮J)
  refine ⟨Q.map (Ideal.Quotient.mk _), Ideal.map_isPrime_of_surjective
    Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker]), ?_⟩
  ext a
  obtain ⟨p, rfl⟩ := polynomialPresentation_surjective A a
  rw [Ideal.mem_comap, integralCoverMap_polynomialPresentation,
    Ideal.mem_quotient_iff_mem hJQ]
  show p ∈ Q.comap ι ↔ p ∈ 𝔮
  rw [hQc]

/-- **An absolutely integrally closed integral cover.** For every commutative ring `A` there is
an `A`-algebra `B` which is absolutely integrally closed and integral over `A`, and such that
every prime of `A` is the contraction of a prime of `B`. -/
theorem exists_isAbsolutelyIntegrallyClosed_isIntegral_comap_surjective :
    ∃ (B : Type u) (_ : CommRing B) (φ : A →+* B),
      IsAbsolutelyIntegrallyClosed B ∧ φ.IsIntegral ∧
        ∀ 𝔭 : Ideal A, 𝔭.IsPrime → ∃ Q : Ideal B, Q.IsPrime ∧ Q.comap φ = 𝔭 :=
  ⟨IntegralCover A, inferInstance, integralCoverMap A,
    isAbsolutelyIntegrallyClosed_integralCover A, integralCoverMap_isIntegral A,
    fun 𝔭 _ => exists_comap_integralCoverMap_eq A 𝔭⟩

end Stacks.AbsolutelyIntegrallyClosed
