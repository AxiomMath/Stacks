module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedRetractAugmentation
public import StacksFrontier.AlgebraicGeometry.Crystalline.EnvelopeRetract

/-!
# The factorization of [Stacks, Tag 07LH] at the round trip of the retract of [Stacks, Tag 07L5]

`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedEnvelopeFactorization.lean` factors a
divided power `A`-algebra endomorphism `ρ` of `D` compatible with the augmentation as
`D --σ--> D⟨ξ_i⟩^∧ --τ--> D`, which is the first step of the source's proof of
[Stacks, Lemma 60.21.4, Tag 07LH].  There `ρ` is a hypothesis, exactly as the source states it.

The `ρ` the source's proof applies this to is the round trip `b ∘ a` of the retract of the first
assertion of [Stacks, Lemma 60.17.5, Tag 07L5], and *that* it is an `A`-algebra map compatible
with the augmentation is something the retract has to be asked for.  It now supplies both:
`Crystalline.exists_completedEnvelopeRetract` records that `b` is a map over `A` and that the
divided power ideal of `D` is the full preimage of that of `D'` under the canonical map `ρ_{07HB}`.
This module turns those into the two hypotheses of the factorization, through
`Crystalline.isAugmentationCompatible_comp_of_retract` and
`Crystalline.map_algebraMap_comp_of_retract`, and then runs the factorization at `b ∘ a`.

## Main results

* `Crystalline.comp_comp_envelopeCompletionStructureMap_of_retract` — `hrhoA` for `b ∘ a`: the
  round trip is a divided power `A`-algebra map.
* `Crystalline.isAugmentationCompatible_comp_of_envelopeRetract` — `hrhoaug` for `b ∘ a`: the
  round trip is compatible with the augmentation.
* `Crystalline.exists_factorization_of_retract` — **the factorization `b ∘ a = τ ∘ σ` with
  `α ∘ σ = ν` and `τ ∘ ν = id_D`, for the round trip of a retract.**
* `Crystalline.exists_factorization_of_presentationRetract` — the same for the retract that
  `Crystalline.exists_completedEnvelopeRetract` produces, with nothing assumed about the maps:
  for a polynomial presentation `A → A[x_i] → C` factoring a smooth one through a surjection
  `q`, the round trip of the retract of [Stacks, Tag 07L5] is an augmentation-compatible divided
  power `A`-algebra endomorphism of `D` and factors as the source's proof of
  [Stacks, Tag 07LH] says.

No tag attribute is placed on anything here: these are steps towards the proof of
[Stacks, Tag 07LH] — the construction of the factorization at the particular endomorphism the
source applies it to — and none of them states that lemma.  What [Stacks, Tag 07LH] still needs
beyond them is the factorization read on the completed de Rham complexes and the completed
clause of [Stacks, Lemma 60.20.2, Tag 07LD]; see
`Crystalline.GlobalCrystallineSituation.SmallSite.computes07LH_of_computes07LG_of_factorization`.

## References

* [Stacks Project, Lemma 60.17.5, Tag 07L5](https://stacks.math.columbia.edu/tag/07L5)
* [Stacks Project, Lemma 60.21.4, Tag 07LH](https://stacks.math.columbia.edu/tag/07LH)
-/

@[expose] public noncomputable section

namespace Crystalline

open DividedPowers

universe u v

section EnvelopeRoundTrip

variable {A : DividedPowerRing.{u}} {ι : Type u} {J : Ideal (MvPolynomial ι A)}
  {hJ : A.ideal.map (algebraMap A (MvPolynomial ι A)) ≤ J}
  (E : DividedPowerEnvelope A (algebraMap A (MvPolynomial ι A)) J hJ) (p : ℕ)
  (hp : IsNilpotent (Ideal.Quotient.mk E.object.ideal (p : E.object)))
  (E' : DividedPowerRing.{u})
  (hp' : IsNilpotent (Ideal.Quotient.mk E'.ideal (p : E')))
  (sm' : DPMorphism A.dividedPowers E'.dividedPowers)
  (rho0 : DPMorphism E.object.dividedPowers E'.dividedPowers)
  (a : DPMorphism (envelopeCompletion E p hp).dividedPowers
    (completedDividedPowers E'.ideal E'.dividedPowers p hp').1)
  (b : DPMorphism (completedDividedPowers E'.ideal E'.dividedPowers p hp').1
    (envelopeCompletion E p hp).dividedPowers)
  (haρ : ∀ x : E.object, a.toRingHom
      (algebraMap (E.object : Type u) (envelopeCompletion E p hp : Type u) x) =
    algebraMap (E' : Type u) (AdicCompletion (pAdicIdeal (A := (E' : Type u)) p) (E' : Type u))
      (rho0.toRingHom x))

include haρ in
/-- **`hrhoA` for the round trip of a completed retract**: `b ∘ a` is a divided power
`A`-algebra endomorphism of `D`.

The structure map `A → D` of a completed envelope is the envelope's structure map followed by
the completion, so this is `Crystalline.map_algebraMap_comp_of_retract` read at
`sm := A → D_{P,γ}(J)` and `sm' := A → D'`: the hypotheses are that `a` is the completion of
`ρ_{07HB}`, that `ρ_{07HB}` is compatible with the two structure maps, and that `b` is a map
over `A`.  The last of these is a conclusion of
`Crystalline.exists_completedEnvelopeRetract`. -/
public theorem comp_comp_envelopeCompletionStructureMap_of_retract
    (hrho0 : rho0.comp E.structureMap = sm')
    (hb : ∀ y : (A : Type u), b.toRingHom
        (algebraMap (E' : Type u)
          (AdicCompletion (pAdicIdeal (A := (E' : Type u)) p) (E' : Type u))
          (sm'.toRingHom y)) =
      algebraMap (E.object : Type u) (envelopeCompletion E p hp : Type u)
        (E.structureMap.toRingHom y)) :
    (b.comp a).comp (envelopeCompletionStructureMap E p hp) =
      envelopeCompletionStructureMap E p hp := by
  apply DPMorphism.ext
  funext y
  exact map_algebraMap_comp_of_retract E.object.ideal E.object.dividedPowers E'.ideal
    E'.dividedPowers p hp hp' a rho0 b E.structureMap.toRingHom sm'.toRingHom haρ
    (congrArg DPMorphism.toRingHom hrho0) hb y

include haρ in
/-- **`hrhoaug` for the round trip of a completed retract**: `b ∘ a` is compatible with the
augmentation of `D`.

This is `Crystalline.isAugmentationCompatible_comp_of_retract`, whose one hypothesis beyond the
retract identity `a ∘ b = id` is that the divided power ideal of the envelope is the **full
preimage** of that of `D'` under `ρ_{07HB}` — a conclusion of
`Crystalline.exists_completedEnvelopeRetract`.  Nothing about `b` beyond `a ∘ b = id` is
used. -/
public theorem isAugmentationCompatible_comp_of_envelopeRetract
    (hab : a.comp b = DPMorphism.id (completedDividedPowers E'.ideal E'.dividedPowers p hp').1)
    (hrho0pre : ∀ u : E.object, rho0.toRingHom u ∈ E'.ideal → u ∈ E.object.ideal) :
    IsAugmentationCompatible (b.comp a) :=
  isAugmentationCompatible_comp_of_retract E.object.ideal E.object.dividedPowers E'.ideal
    E'.dividedPowers p hp hp' a rho0 b hab haρ hrho0pre

include haρ in
/-- **The factorization of [Stacks, Lemma 60.21.4, Tag 07LH] at the round trip of a completed
retract.**

The source's proof of that lemma applies its factorization to `ρ = b ∘ a`, where `a`, `b` are
the maps of the first assertion of [Stacks, Lemma 60.17.5, Tag 07L5].  Putting the two previous
results together with
`Crystalline.exists_factorization_of_isAugmentationCompatible` gives exactly that: `b ∘ a` is an
augmentation-compatible divided power `A`-algebra endomorphism of `D`, and so

`D --σ--> D⟨ξ_i⟩^∧ --τ--> D`,  `τ ∘ σ = b ∘ a`,  `α ∘ σ = ν`,  `τ ∘ ν = id_D`.

The three displayed identities are the ones the source's argument uses; the values of the maps
on the coordinates and the invertibility of `α` are in
`Crystalline.exists_factorization_of_isAugmentationCompatible`, which this applies. -/
public theorem exists_factorization_of_retract [Fact p.Prime]
    [Algebra (IntegersAtPrime p) (E.object : Type u)]
    (hrho0 : rho0.comp E.structureMap = sm')
    (hrho0pre : ∀ u : E.object, rho0.toRingHom u ∈ E'.ideal → u ∈ E.object.ideal)
    (hab : a.comp b = DPMorphism.id (completedDividedPowers E'.ideal E'.dividedPowers p hp').1)
    (hb : ∀ y : (A : Type u), b.toRingHom
        (algebraMap (E' : Type u)
          (AdicCompletion (pAdicIdeal (A := (E' : Type u)) p) (E' : Type u))
          (sm'.toRingHom y)) =
      algebraMap (E.object : Type u) (envelopeCompletion E p hp : Type u)
        (E.structureMap.toRingHom y)) :
    ∃ hrhoaug : IsAugmentationCompatible (b.comp a),
      (b.comp a).comp (envelopeCompletionStructureMap E p hp) =
          envelopeCompletionStructureMap E p hp ∧
        (envelopeCompletionTau E p hp (b.comp a) hrhoaug).comp
              (envelopeCompletionSigma E p hp) = b.comp a ∧
          (envelopeCompletionAlpha E p hp).comp (envelopeCompletionSigma E p hp) =
              envelopeCompletionNu E p hp ∧
            (envelopeCompletionTau E p hp (b.comp a) hrhoaug).comp
                (envelopeCompletionNu E p hp) =
              DPMorphism.id (envelopeCompletion E p hp).dividedPowers := by
  have hrhoA : (b.comp a).comp (envelopeCompletionStructureMap E p hp) =
      envelopeCompletionStructureMap E p hp :=
    comp_comp_envelopeCompletionStructureMap_of_retract E p hp E' hp' sm' rho0 a b haρ hrho0 hb
  exact ⟨isAugmentationCompatible_comp_of_envelopeRetract E p hp E' hp' rho0 a b haρ hab
    hrho0pre, hrhoA, envelopeCompletionTau_comp_sigma E p hp (b.comp a) hrhoA _,
    envelopeCompletionAlpha_comp_sigma E p hp, envelopeCompletionTau_comp_nu E p hp (b.comp a) _⟩

end EnvelopeRoundTrip

/-! ### The factorization at the retract of a polynomial presentation -/

section PresentationRoundTrip

variable (s : AffineCrystallineSituation.{u, v}) {ι : Type u} {P' : Type u} [CommRing P']
  [Algebra (s.A : Type u) P']
  (q : MvPolynomial ι (s.A : Type u) →ₐ[(s.A : Type u)] P')
  (f' : P' →ₐ[(s.A : Type u)] s.C) [Algebra.Smooth (s.A : Type u) P']
  (hq : Function.Surjective q) (hf' : Function.Surjective f')

include hq hf' in
/-- **The factorization of [Stacks, Lemma 60.21.4, Tag 07LH] at the retract of
[Stacks, Lemma 60.17.5, Tag 07L5], with nothing assumed about the maps.**

Let `A → P' → C` be a smooth presentation in the affine situation of [Stacks, Tag 07MD] and let
`q : A[x_i] ↠ P'` be a surjection of `A`-algebras, so that `A → A[x_i] → C` is a polynomial
presentation of `C`.  Write `D` for the `p`-adic completion of the divided power envelope of the
second presentation.  Then there is a divided power `A`-algebra endomorphism `ρ` of `D`
compatible with the augmentation to `C` — the round trip `b ∘ a` of the retract — together with
the factorization

`D --σ--> D⟨ξ_i⟩^∧ --τ--> D`,  `τ ∘ σ = ρ`,  `α ∘ σ = ν`,  `τ ∘ ν = id_D`

of the source's proof of [Stacks, Tag 07LH].

The polynomial presentation is what the factorization needs: `σ` is defined by the universal
property of `D` on the coordinates `x_i`, and `D⟨ξ_i⟩^∧` has one variable `ξ_i` for each of
them.  The `A`-algebra and augmentation compatibility of `ρ` are *not* hypotheses here; they are
`Crystalline.comp_comp_envelopeCompletionStructureMap_of_retract` and
`Crystalline.isAugmentationCompatible_comp_of_envelopeRetract` at the retract that
`Crystalline.exists_completedEnvelopeRetract` produces. -/
public theorem exists_factorization_of_presentationRetract
    [Algebra (IntegersAtPrime s.p)
      ((presentationEnvelope s (f'.comp q)).object : Type u)] :
    ∃ (rho : DPMorphism
        (envelopeCompletion (presentationEnvelope s (f'.comp q)) s.p
          (presentationEnvelope_prime_nilpotent s (f'.comp q) (hf'.comp hq))).dividedPowers
        (envelopeCompletion (presentationEnvelope s (f'.comp q)) s.p
          (presentationEnvelope_prime_nilpotent s (f'.comp q) (hf'.comp hq))).dividedPowers)
      (hrhoaug : IsAugmentationCompatible rho),
      rho.comp (envelopeCompletionStructureMap (presentationEnvelope s (f'.comp q)) s.p
            (presentationEnvelope_prime_nilpotent s (f'.comp q) (hf'.comp hq))) =
          envelopeCompletionStructureMap (presentationEnvelope s (f'.comp q)) s.p
            (presentationEnvelope_prime_nilpotent s (f'.comp q) (hf'.comp hq)) ∧
        (envelopeCompletionTau (presentationEnvelope s (f'.comp q)) s.p
                (presentationEnvelope_prime_nilpotent s (f'.comp q) (hf'.comp hq)) rho
                hrhoaug).comp
              (envelopeCompletionSigma (presentationEnvelope s (f'.comp q)) s.p
                (presentationEnvelope_prime_nilpotent s (f'.comp q) (hf'.comp hq))) = rho ∧
          (envelopeCompletionAlpha (presentationEnvelope s (f'.comp q)) s.p
                  (presentationEnvelope_prime_nilpotent s (f'.comp q) (hf'.comp hq))).comp
                (envelopeCompletionSigma (presentationEnvelope s (f'.comp q)) s.p
                  (presentationEnvelope_prime_nilpotent s (f'.comp q) (hf'.comp hq))) =
              envelopeCompletionNu (presentationEnvelope s (f'.comp q)) s.p
                (presentationEnvelope_prime_nilpotent s (f'.comp q) (hf'.comp hq)) ∧
            (envelopeCompletionTau (presentationEnvelope s (f'.comp q)) s.p
                    (presentationEnvelope_prime_nilpotent s (f'.comp q) (hf'.comp hq)) rho
                    hrhoaug).comp
                  (envelopeCompletionNu (presentationEnvelope s (f'.comp q)) s.p
                    (presentationEnvelope_prime_nilpotent s (f'.comp q) (hf'.comp hq))) =
                DPMorphism.id
                  (envelopeCompletion (presentationEnvelope s (f'.comp q)) s.p
                    (presentationEnvelope_prime_nilpotent s (f'.comp q)
                      (hf'.comp hq))).dividedPowers := by
  classical
  obtain ⟨rho0, hrho0struct, -, -, hrho0pre, a, b, hab, haρ, hb⟩ :=
    exists_completedEnvelopeRetract s q f' hq hf'
  exact ⟨b.comp a, exists_factorization_of_retract (presentationEnvelope s (f'.comp q)) s.p
    (presentationEnvelope_prime_nilpotent s (f'.comp q) (hf'.comp hq))
    (presentationEnvelope s f').object (presentationEnvelope_prime_nilpotent s f' hf')
    (presentationEnvelope s f').structureMap rho0 a b haρ hrho0struct hrho0pre hab hb⟩

end PresentationRoundTrip

end Crystalline

end
