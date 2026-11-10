module

public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.ArtinApproximationMorphism
public import StacksFrontier.RingTheory.Localization.ClosedPointOfSpecialFibre
public import StacksFrontier.RingTheory.Smoothing.ApproximationGRingEtale

/-!
# The last application of Artin approximation in the proof of Stacks Tag 0CAW

The proof of Stacks Tag 0CAW ends by applying Tag 0CAU "one more time", and the ring map it
applies it to is **not** the given `σ : C → R^∧` but the smooth stage `ρ : R' → R^∧` through
which `σ` has been factored. That distinction is the whole point of the step: a `V` and a `τ`
chosen without reference to `φ` can make clause (5) of the tag unsatisfiable, and the stage `R'`
is where `φ` has already been absorbed. Concretely the input is a ring map

`ρ : R' → (R_𝔭)^∧`

of `R`-algebras out of an `R`-algebra of finite type, and the output is the ring `D` of the
source — étale over the chart ring `R` at a prime over `𝔭` with the same residue field — together
with an `R`-algebra map `R' → D` whose composite `R' → D → D^∧ = (R_𝔭)^∧` agrees with `ρ` modulo
the `N`-th power of the maximal ideal. This file performs that application.

## Main results

* `StacksDraft.ArtinApproximation.exists_etaleApproximation_of_ringHom_completion`: the step
  above, i.e. `StacksDraft.ArtinApproximation.exists_etaleApproximation` at `A := R`,
  `B := R'` and `𝔮 := ρ⁻¹(𝔪)`, with the local homomorphism `𝑅'_𝔮 → (R_𝔭)^∧` that Tag 0CAU's
  affine case asks for constructed from `ρ`.
* `StacksDraft.ArtinApproximation.exists_etaleApproximation_mem_maximalIdeal_pow`: the same with
  the congruence read on `R'` itself rather than on its localization, which is the form the
  chase of clause (5) consumes.

## Implementation notes

*Why this is not a restatement of the affine case.* `StacksDraft.ArtinApproximation.exists_
etaleApproximation` asks for a local homomorphism `B_𝔮 → (A_𝔭)^∧`, because that is what Tag 0CAU
is about, while the step of the source's proof carried out here is handed a ring map `R' → R^∧`
with no prime of `R'` named at all. What is done below is therefore the two things the affine
case does not do: it *produces* the prime `𝔮` — the contraction of the maximal ideal of
`(R_𝔭)^∧`, which is what makes the lifted homomorphism local — and it lifts `ρ` across the
localization, by `IsLocalization.lift` together with
`lift_isLocalHom_of_comap`. Nothing of the approximation itself is reproved.

*No hypothesis beyond the source's is carried.* Tag 0CAR enters through the unconditional
`StacksDraft.ArtinApproximation.artinApproximationGRing`, so the only hypotheses are the
source's: `R` Noetherian, `R'` of finite type over `R`, and `R_𝔭` a G-ring. The last is what Tag
0CAW assumes of `𝒪_{S, s}`.

*The prime is produced with its defining equation.* The consumer needs `𝔮 = ρ⁻¹(𝔪)` and not only
the existence of some prime: it is through that equation that residual triviality of `ρ` at the
maximal ideal of `(R_𝔭)^∧` is stated, which is what
`Ideal.exists_isPrime_comap_eq_and_residueField_map_bijective_of_descent_algEquiv` consumes on
the stage side. So the equation is part of the conclusion rather than being hidden in the choice.

*The `W` of the source needs no declaration of its own, and must not be given one.* Once `D` is
in hand the source's `W = Spec(B ⊗_C D)` is, with the replacement of `C` by `R'` and `B` by `B''`
undone, the spectrum of `(B ⊗_C D) ⊗_{B ⊗_C R'} B''`, and the cancellation of that to the
source's own spelling `B'' ⊗_{R'} D` is already in the library:
`Stacks.Etale.ColimitSpreadOut.isPushout_tensorProduct`
(`StacksFrontier/RingTheory/Etale/ColimitBaseChange.lean`), read at `R := C`, `S := B`, `B := R'`,
`C := D`, gives `Algebra.IsPushout R' (B ⊗_C R') D (B ⊗_C D)` from exactly the algebra structure
`Algebra.TensorProduct.map (AlgHom.id C B) (IsScalarTower.toAlgHom C R' D)` that
`Stacks.Smoothing.exists_smooth_stage_etale_map_tensorProduct_of_indSmooth` supplies, and
`Algebra.IsPushout.cancelBaseChangeAlg` on its `Algebra.IsPushout.symm` is then
`(B ⊗_C D) ⊗_{B ⊗_C R'} B'' ≃ₐ[D] D ⊗_{R'} B''`. Étaleness of that algebra over `B ⊗_C D` is
Mathlib's `Algebra.Etale.baseChange` instance. So nothing is stated here for the `W` side: a
wrapper would duplicate `isPushout_tensorProduct`, which is why that lemma is no longer private.

*Nothing here is registered for Tag 0CAW.* This is a step of the source's proof, not one of its
clauses; clauses (4) and (5) are not established by it. The two clause-wise registrations of Tag
0CAW remain `StacksDraft.ArtinApproximation.exists_elementaryEtaleNeighborhood_baseApproximation`
and `StacksDraft.ArtinApproximation.exists_elementaryEtaleNeighborhood_relativeApproximation`.

## References

* [Stacks Project, Tag 0CAW](https://stacks.math.columbia.edu/tag/0CAW)
* [Stacks Project, Tag 0CAU](https://stacks.math.columbia.edu/tag/0CAU)
-/

@[expose] public section

open IsLocalRing AdicCompletion

universe u

namespace StacksDraft.ArtinApproximation

/-- **The last application of Tag 0CAU in the proof of Stacks Tag 0CAW.** Let `R` be a Noetherian
ring, let `𝔭` be a prime of `R` with `R_𝔭` a G-ring, let `E` be an `R`-algebra of finite type and
let `ρ : E → (R_𝔭)^∧` be a homomorphism of `R`-algebras. Then for every `N ≥ 1` the prime
`𝔮 = ρ⁻¹(𝔪)` of `E` and the local homomorphism `E_𝔮 → (R_𝔭)^∧` that `ρ` induces admit the
conclusion of the affine case of Tag 0CAU with `A := R`: an étale `R`-algebra `D`, a prime of `D`
over `𝔭` with the same residue field, and an `R`-algebra map `E → D` carrying that prime back to
`𝔮` whose induced map of local rings agrees with `ρ` modulo `𝔪^N`.

Read at Stacks Tag 0CAW this is the source's own last step, "we apply Lemma 0CAU one more time to
`Spec(R')` and `Spec(R)` over `Spec(R)` and the map `R' → R^∧`", with `E = R'` the smooth stage
through which `σ : C → R^∧` has been factored and `D` the ring whose spectrum is the `V` of the
tag. The stage, and not `C`, is the right source: clause (5) of the tag can be made unsatisfiable
by a `V` chosen before `φ` has entered the problem.

Nothing beyond the source's hypotheses is assumed: Tag 0CAR enters through the unconditional
`StacksDraft.ArtinApproximation.artinApproximationGRing`. Nothing here is registered for Tag
0CAW; this is a step of its proof and not one of its clauses. -/
theorem exists_etaleApproximation_of_ringHom_completion {R E : Type u} [CommRing R] [CommRing E]
    [IsNoetherianRing R] [Algebra R E] [Algebra.FiniteType R E]
    (p : Ideal R) [p.IsPrime] (hG : IsGRing (Localization.AtPrime p)) (N : ℕ) (hN : 1 ≤ N)
    (ρ : E →+* Completion p) (hρ : ρ.comp (algebraMap R E) = toCompletion p) :
    ∃ (q : Ideal E) (_ : q.IsPrime) (_ : q = (maximalIdeal (Completion p)).comap ρ)
      (φ : Localization.AtPrime q →+* Completion p),
      (∀ e : E, φ (algebraMap E (Localization.AtPrime q) e) = ρ e) ∧
        Nonempty (EtaleApproximation R R E p q N φ) := by
  have hpnoeth : IsNoetherianRing (Localization.AtPrime p) :=
    IsLocalization.isNoetherianRing p.primeCompl (Localization.AtPrime p) inferInstance
  -- The prime of `E` that makes the lifted homomorphism local.
  set q : Ideal E := (maximalIdeal (Completion p)).comap ρ with hqdef
  have hqprime : q.IsPrime := Ideal.comap_isPrime _ _
  -- Away from `𝔮` the map `ρ` takes unit values, so it lifts across the localization.
  have hu : ∀ y : q.primeCompl, IsUnit (ρ (y : E)) := by
    intro y
    exact notMem_maximalIdeal.mp fun hmem => y.2 (Ideal.mem_comap.mpr hmem)
  set φ : Localization.AtPrime q →+* Completion p :=
    IsLocalization.lift (S := Localization.AtPrime q) hu with hφdef
  have hφapply : ∀ e : E, φ (algebraMap E (Localization.AtPrime q) e) = ρ e := fun e =>
    RingHom.congr_fun (IsLocalization.lift_comp (S := Localization.AtPrime q) hu) e
  have hφloc : IsLocalHom φ := lift_isLocalHom_of_comap ρ q hqdef hu
  -- The hypothesis of the affine case, over the base `R` read through `A := R`.
  have hbase : φ.comp ((algebraMap E (Localization.AtPrime q)).comp (algebraMap R E)) =
      (toCompletion p).comp (algebraMap R R) := by
    refine RingHom.ext fun r => ?_
    change φ (algebraMap E (Localization.AtPrime q) (algebraMap R E r)) = toCompletion p r
    rw [hφapply]
    exact RingHom.congr_fun hρ r
  exact ⟨q, hqprime, hqdef, φ, hφapply,
    exists_etaleApproximation artinApproximationGRing p q hG N hN φ hφloc hbase⟩

/-- **The same congruence, read on the stage ring itself.** In the situation of
`StacksDraft.ArtinApproximation.exists_etaleApproximation_of_ringHom_completion`, the agreement
of the two maps out of `E_𝔮` specialises to the agreement of the two maps out of `E`: for every
`e : E` the difference of `ρ e`, pushed into the completion of the local ring of `D` at the
chosen prime, and the image of `E → D → (D_{𝔭'})^∧` lies in the `N`-th power of the maximal
ideal.

This is the form the chase of clause (5) of Stacks Tag 0CAW consumes — there `E = R'` is the
smooth stage and the congruence is the one through which `R' → D → D^∧ = R^∧` is compared with
`ρ`. The localized form is the one `StacksDraft.ArtinApproximation.EtaleApproximation` carries,
because that is the shape Tag 0CAU's conclusion has. -/
theorem exists_etaleApproximation_mem_maximalIdeal_pow {R E : Type u} [CommRing R] [CommRing E]
    [IsNoetherianRing R] [Algebra R E] [Algebra.FiniteType R E]
    (p : Ideal R) [p.IsPrime] (hG : IsGRing (Localization.AtPrime p)) (N : ℕ) (hN : 1 ≤ N)
    (ρ : E →+* Completion p) (hρ : ρ.comp (algebraMap R E) = toCompletion p) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D) (_ : Algebra.Etale R D)
      (pD : Ideal D) (_ : pD.IsPrime) (hpD : p = pD.comap (algebraMap R D)),
      Function.Bijective (Ideal.ResidueField.map p pD (algebraMap R D) hpD) ∧
        ∃ χ : E →+* D,
          χ.comp (algebraMap R E) = algebraMap R D ∧
            (maximalIdeal (Completion p)).comap ρ = pD.comap χ ∧
            ∀ e : E,
              completionComparison p pD (algebraMap R D) hpD (ρ e) -
                  toCompletion pD (χ e) ∈ completionIdeal pD N := by
  obtain ⟨q, hqprime, hqdef, φ, hφapply, ⟨Ea⟩⟩ :=
    exists_etaleApproximation_of_ringHom_completion p hG N hN ρ hρ
  refine ⟨Ea.carrier, Ea.commRing, Ea.algebra, Ea.etale, Ea.prime, Ea.isPrime, Ea.comap_prime,
    Ea.residueField_bijective, Ea.toCarrier, ?_, ?_, fun e => ?_⟩
  · refine (RingHom.ext fun r => ?_).trans (RingHom.comp_id (algebraMap R Ea.carrier))
    exact RingHom.congr_fun Ea.toCarrier_base r
  · rw [← hqdef]; exact Ea.comap_toCarrier
  · have h := Ea.agree (algebraMap E (Localization.AtPrime q) e)
    rw [hφapply e, Localization.localRingHom_to_map] at h
    exact h

end StacksDraft.ArtinApproximation

end
