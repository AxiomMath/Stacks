module

public import StacksFrontier.Homology.RelativelyPerfect.JacobsonFibre
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleLocalization.TorAmplitudeHenselization

/-!
# Tor amplitude at a geometric point from the derived fibre at a specialization

Let `A` be flat and of finite presentation over `R`, presented by `d` variables, let `q ⊆ q₀` be
primes of `A` and let `M` be a pseudo-coherent complex of `A`-modules whose derived fibre at `q₀`
has Tor amplitude in `[a, b]`, in the sense of
`PseudoCoherence.hasTorAmplitudeAt_of_derivedFibre_of_le`. Let `A_q → B` be faithfully flat, and
let `Λ` be a ring under `R_{q ∩ R}` and over `B` along which flatness descends: a `Λ`-module is
flat over `R_{q ∩ R}` exactly when it is flat over `Λ`. Then `M ⊗_A B`, read over `Λ`, has Tor
amplitude in `[a - d, b]`.

This is the algebra of the proof of Stacks 0DL5 at a geometric point `x̄` of `X`: there `B` is the
étale local ring of `X` at `x̄`, faithfully flat over the local ring of an affine étale chart, and
`Λ` is the étale local ring of the base at the image of `x̄`, a strict henselization of
`R_{q ∩ R}`, along which flatness descends by Stacks 05VL.

## Main results

* `PseudoCoherence.hasTorAmplitudeCanonical_restrictScalars_of_derivedFibre_of_le`: the statement
  above.

## References

* [Stacks Project, Lemma 15.85.9 (Tag 0DJH)](https://stacks.math.columbia.edu/tag/0DJH)
* [Stacks Project, Lemma 15.68.18 (Tag 0DJF)](https://stacks.math.columbia.edu/tag/0DJF)
* [Stacks Project, Lemma 76.54.5 (Tag 0DL5)](https://stacks.math.columbia.edu/tag/0DL5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars StacksDraft.TorAmplitude

namespace PseudoCoherence

universe u

attribute [local instance] HasDerivedCategory.standard

/-- **Tor amplitude at a geometric point from the derived fibre at a specialization.** Let `A` be
flat and of finite presentation over `R`, presented by `d` variables, let `q ⊆ q₀` be primes of
`A` and let `M` be a pseudo-coherent complex of `A`-modules. Suppose the derived base change along
`h : R_{p₀} → R₀` of `M_{q₀}`, read over `R_{p₀}`, has Tor amplitude in `[a, b]`, where `R₀`
carries a module which, read over `R_{p₀}`, is the residue field at `p₀ = q₀ ∩ R`. Let
`A_q → B` be faithfully flat and let `ρ : R_{q ∩ R} → Λ` and `μ : Λ → B` be ring maps whose
composite is the structure map, along `ρ` of which flatness descends. Then `M ⊗_A B`, read over
`Λ`, has Tor amplitude in `[a - d, b]`. -/
theorem hasTorAmplitudeCanonical_restrictScalars_of_derivedFibre_of_le
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    (d : ℕ) (presentation : MvPolynomial (Fin d) R →ₐ[R] A)
    (hpresentation : Function.Surjective presentation)
    (q₀ q : Ideal A) [q₀.IsPrime] [q.IsPrime] (hq : q ≤ q₀)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : StacksDraft.PseudoCoherence.IsPseudoCoherent (DerivedCategory.Q.obj M)) (a b : ℤ)
    {R₀ : Type u} [CommRing R₀] (h : Localization.AtPrime (q₀.under R) →+* R₀)
    (N : ModuleCat.{u} R₀)
    (eN : (ModuleCat.restrictScalars h).obj N ≅
      ModuleCat.of (Localization.AtPrime (q₀.under R)) (q₀.under R).ResidueField)
    (hfib :
      letI : Algebra (Localization.AtPrime (q₀.under R)) (Localization.AtPrime q₀) :=
        Localization.AtPrime.algebraOfLiesOver (q₀.under R) q₀
      HasTorAmplitudeCanonical R₀
        ((totalDerivedExtensionScalars.{u, u, u} h).functor.obj
          ((ModuleCat.restrictScalars
            (algebraMap (Localization.AtPrime (q₀.under R))
              (Localization.AtPrime q₀))).mapDerivedCategory.obj
            ((totalDerivedExtensionScalars.{u, u, u}
              (algebraMap A (Localization.AtPrime q₀))).functor.obj
                (DerivedCategory.Q.obj M)))) a b)
    {B : Type u} [CommRing B] [Algebra (Localization.AtPrime q) B]
    [Module.FaithfullyFlat (Localization.AtPrime q) B]
    {Λ : Type u} [CommRing Λ] (ρ : Localization.AtPrime (q.under R) →+* Λ) (μ : Λ →+* B)
    (hcomp :
      letI : Algebra (Localization.AtPrime (q.under R)) (Localization.AtPrime q) :=
        Localization.AtPrime.algebraOfLiesOver (q.under R) q
      μ.comp ρ =
        (algebraMap (Localization.AtPrime q) B).comp
          (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q)))
    (hflat : ∀ N : ModuleCat.{u} Λ,
      Module.Flat (Localization.AtPrime (q.under R)) ((ModuleCat.restrictScalars ρ).obj N) ↔
        Module.Flat Λ N) :
    HasTorAmplitudeCanonical Λ
      (DerivedCategory.Q.obj ((CochainComplex.restrictScalars μ).obj
        ((CochainComplex.extendScalars (algebraMap (Localization.AtPrime q) B)).obj
          ((CochainComplex.extendScalars (algebraMap A (Localization.AtPrime q))).obj M))))
      (a - (d : ℤ)) b := by
  let : Algebra (Localization.AtPrime (q.under R)) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver (q.under R) q
  let : Algebra (Localization.AtPrime (q.under R)) B := (μ.comp ρ).toAlgebra
  have : IsScalarTower (Localization.AtPrime (q.under R)) (Localization.AtPrime q) B :=
    IsScalarTower.of_algebraMap_eq' hcomp
  -- Stacks 0DJH at `q₀`, localised to `q`.
  have hAt : HasTorAmplitudeAt R M q (a - (d : ℤ)) b :=
    hasTorAmplitudeAt_of_derivedFibre_of_le d presentation hpresentation q₀ q hq M hM a b h N eN
      hfib
  -- Stacks 0DJF along the faithfully flat `A_q → B`.
  have hB := (FaithfullyFlat.hasTorAmplitudeIn_iff_extendScalars
    (Localization.AtPrime (q.under R)) (Localization.AtPrime q) B
    ((CochainComplex.extendScalars (algebraMap A (Localization.AtPrime q))).obj M)
    (a - (d : ℤ)) b).mp hAt
  -- Flatness descends along `ρ`.
  refine (hasTorAmplitudeCanonical_restrictScalars_iff_of_flat_iff ρ hflat _ _ _).mp ?_
  exact
    (AlgebraicGeometry.AffineRelativeTorAmplitude.hasTorAmplitudeCanonical_iff_hasTorAmplitude0DJF
      _ _ _).mpr hB

end PseudoCoherence

end
