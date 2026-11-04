module

public import StacksFrontier.Homology.RelativelyPerfect.JacobsonFibreHenselization

/-!
# Tor amplitude at a prime and over a ring dominating its local ring

Let `R → A` be a ring map, `q` a prime of `A`, and `M` a complex of `A`-modules. Let `A_q → B` be
faithfully flat and let `ρ : R_{q ∩ R} → Λ`, `μ : Λ → B` be ring maps whose composite is the
structure map `R_{q ∩ R} → A_q → B`, along `ρ` of which flatness descends: a `Λ`-module is flat
over `R_{q ∩ R}` exactly when it is flat over `Λ`. Then `M_q` has Tor amplitude in `[a, b]` over
`R_{q ∩ R}` exactly when `M ⊗_A B`, read over `Λ`, has Tor amplitude in `[a, b]`.

This is the translation, at one geometric point of an algebraic space, between the Tor amplitude
of a geometric stalk over the stalk of the inverse image of the structure sheaf of the base and
the Tor amplitude of a chart model at the corresponding prime. In that situation `B` is the
geometric stalk ring of the chart, faithfully flat over the local ring of the chart (Stacks 04KF),
and `Λ` is the strict henselization of the local ring of the base, along which flatness descends
(Stacks 05VL).

## Main results

* `PseudoCoherence.hasTorAmplitudeAt_iff_hasTorAmplitudeCanonical_restrictScalars`: the
  statement above.

## References

* [Stacks Project, Lemma 15.68.18 (Tag 0DJF)](https://stacks.math.columbia.edu/tag/0DJF)
* [Stacks Project, Lemma 76.54.5 (Tag 0DL5)](https://stacks.math.columbia.edu/tag/0DL5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open StacksDraft.TorAmplitude

namespace PseudoCoherence

universe u

attribute [local instance] HasDerivedCategory.standard

/-- **Tor amplitude at a prime is Tor amplitude over a ring dominating its local ring.** Let `q`
be a prime of the `R`-algebra `A`, let `M` be a complex of `A`-modules, let `A_q → B` be
faithfully flat and let `ρ : R_{q ∩ R} → Λ` and `μ : Λ → B` be ring maps whose composite is the
structure map, along `ρ` of which flatness descends. Then `M_q` has Tor amplitude in `[a, b]`
over `R_{q ∩ R}` exactly when `M ⊗_A B`, read over `Λ`, has. -/
theorem hasTorAmplitudeAt_iff_hasTorAmplitudeCanonical_restrictScalars
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] (q : Ideal A) [q.IsPrime]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ)
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
    HasTorAmplitudeAt R M q a b ↔
      HasTorAmplitudeCanonical Λ
        (DerivedCategory.Q.obj ((CochainComplex.restrictScalars μ).obj
          ((CochainComplex.extendScalars (algebraMap (Localization.AtPrime q) B)).obj
            ((CochainComplex.extendScalars (algebraMap A (Localization.AtPrime q))).obj M))))
        a b := by
  let : Algebra (Localization.AtPrime (q.under R)) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver (q.under R) q
  let : Algebra (Localization.AtPrime (q.under R)) B := (μ.comp ρ).toAlgebra
  have : IsScalarTower (Localization.AtPrime (q.under R)) (Localization.AtPrime q) B :=
    IsScalarTower.of_algebraMap_eq' hcomp
  have hB := FaithfullyFlat.hasTorAmplitudeIn_iff_extendScalars
    (Localization.AtPrime (q.under R)) (Localization.AtPrime q) B
    ((CochainComplex.extendScalars (algebraMap A (Localization.AtPrime q))).obj M) a b
  refine hB.trans (Iff.trans ?_
    (hasTorAmplitudeCanonical_restrictScalars_iff_of_flat_iff ρ hflat _ _ _))
  exact
    (AlgebraicGeometry.AffineRelativeTorAmplitude.hasTorAmplitudeCanonical_iff_hasTorAmplitude0DJF
      _ _ _).symm

end PseudoCoherence

end
