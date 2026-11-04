module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BaseThresholdInitialForms
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupDualSection
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupGeneratorBound
public import StacksFrontier.RingTheory.RigSmooth.ComparisonAlgHomAboveExponent

/-!
# Stacks 0GAR: a rig-smooth quotient is determined by its equations modulo a power of `I`

Let `I` be an ideal of a Noetherian ring `A`, `P = A[x₁, …, x_r]^∧` and
`P^⊕t --K--> P^⊕m --(g₁, …, g_m)--> P → B → 0` a resolution with `B` rig-smooth over `(A, I)`.
Stacks 0GAR: there is an `n` such that every complex congruent to it modulo `IⁿP` presents an
`A`-algebra isomorphic to `B`. This is `Rig.PerturbedPresentation.exists_algEquiv_of_perturbation`.

The lifting lemma Stacks 0GAQ (`Rig.exists_algHom_lift_of_dualSituation'`) needs, for the target
`B' = P/(g'₁, …, g'_m)`, the dual situations of Local Cohomology, Section 0GA6, with invariants
`d` and `q₀` that may not depend on the perturbation, since `n` is chosen before it. Here:

* `liftingInputsOfIsBaseThreshold`: the inputs of the lifting lemma, built on the blowup of
  `Spec(B')` for any `q₀` with the defining property of `q(S)` and with `d` read off a generating
  family of `I` (the blowup is a closed subscheme of `𝐏^d`), which is uniform;
* `exists_perturbationBound_sameInitialForms`: step (B) of the source's proof in the form of an
  equality of initial forms, from Stacks 07VE and 07VF;
* `isBaseThreshold_quotIdeal_of_sameInitialForms`: step (C) — `q₀ = q(Gr_I(B))` serves for `B'`,
  because `q(S)` only depends on `S = Gr_I` (`Stacks.LocalCohomology.UniformityIII`
  `.isBaseThreshold_iff_of_sameInitialForms`).

The precision at which the lifting lemma concludes is immaterial: the final step
(`exists_perturbationBound_algEquiv_of_algHom`) absorbs any fixed loss in the choice of `n`.

## References

* [Stacks Project, Tag 0GAR](https://stacks.math.columbia.edu/tag/0GAR)
* [Stacks Project, Tag 0GAQ](https://stacks.math.columbia.edu/tag/0GAQ)
* [Stacks Project, Tag 0GA6](https://stacks.math.columbia.edu/tag/0GA6)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.LocalCohomology.UniformityIII

universe u

namespace Rig.PerturbedPresentation

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (r : ℕ)

/-- **The inputs of the lifting lemma, on the blowup.** For `b ⊆ P` and a `q₀` with the defining
property of `q(S)` for `(P ⧸ b, I · (P ⧸ b))`, the blowup of `Spec(P ⧸ b)` in `I · (P ⧸ b)`
carries the dual situations of Local Cohomology, Section 0GA6, at every thickness `m ≥ c`
(`blowupDualSituationOfBound`), with invariant `q₀` and with invariant `d` the vanishing degree
read off a generating family `x₀, …, x_d` of `I` (`subsingleton_blowupHmod_of_span`); and the
duality input of Tag 0GAC is `exists_blowupEv_eq`. Both invariants are independent of `m`. -/
def liftingInputsOfIsBaseThreshold (b : Ideal (completedPolynomialAlgebra I r)) {d : ℕ}
    (x : Fin (d + 1) → A) (hx : ∀ j, x j ∈ I) (hspan : I = Ideal.span (Set.range x))
    (n c q₀ : ℕ) (hq : IsBaseThreshold (quotIdeal A I r b) q₀) :
    LiftingInputsAboveExponent A I r b n c d q₀ where
  dualSituation m hm := blowupDualSituationOfBound (quotIdeal A I r b)
    (fun F _ _ hi => subsingleton_blowupHmod_of_span (quotIdeal A I r b)
      (fun j => algebraMap A (quotRing A I r b) (x j))
      (fun j => Ideal.mem_map_of_mem _ (hx j))
      ((congrArg (Ideal.map (algebraMap A (quotRing A I r b))) hspan).trans
        (by rw [Ideal.map_span, ← Set.range_comp]; rfl)) F hi) q₀ hq m c hm
  dim_eq _ _ := rfl
  bound_eq _ _ := rfl
  openDuality m _ hm _ hem hq' M ϕ :=
    exists_blowupEv_eq (quotIdeal A I r b) q₀ hq hm hem hq' M ϕ

/-- **Step (B) of the proof of Stacks 0GAR, graded half, as an equality of initial forms.** For a
resolution `P^⊕t --K--> P^⊕m --g--> P` there is an `n₀` such that every complex congruent to it
modulo `(IP)ⁿ`, `n ≥ n₀`, is again a resolution and has the same initial forms. -/
theorem exists_perturbationBound_sameInitialForms {t m : ℕ}
    (K : (Fin t → completedPolynomialAlgebra I r) →ₗ[completedPolynomialAlgebra I r]
      (Fin m → completedPolynomialAlgebra I r))
    (g : (Fin m → completedPolynomialAlgebra I r) →ₗ[completedPolynomialAlgebra I r]
      completedPolynomialAlgebra I r)
    (hexact : LinearMap.ker g = LinearMap.range K) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ (K' : (Fin t → completedPolynomialAlgebra I r) →ₗ[completedPolynomialAlgebra I r]
          (Fin m → completedPolynomialAlgebra I r))
        (g' : (Fin m → completedPolynomialAlgebra I r) →ₗ[completedPolynomialAlgebra I r]
          completedPolynomialAlgebra I r),
      g'.comp K' = 0 →
      CongruentModPow (I.map (algebraMap A (completedPolynomialAlgebra I r))) K K' n →
      CongruentModPow (I.map (algebraMap A (completedPolynomialAlgebra I r))) g g' n →
        SameInitialForms (I.map (algebraMap A (completedPolynomialAlgebra I r)))
          (LinearMap.range g) (LinearMap.range g') := by
  obtain ⟨c, hK, hg⟩ := exists_isArtinReesConstant_pair
    (I.map (algebraMap A (completedPolynomialAlgebra I r))) K g
  refine ⟨c + 1, fun n hn K' g' hcomplex hKK' hgg' k => ?_⟩
  have hg' := (artinRees_stability _ (map_algebraMap_le_jacobson_bot A I r) K K' g g' c hcomplex
    hK hg hexact (hKK'.mono hn) (hgg'.mono hn)).1
  exact presentation_denominator_eq _ g g' c k hg hg' (hgg'.mono hn)

omit [IsNoetherianRing A] in
/-- `I · (P ⧸ b)` is the image of `IP` in `P ⧸ b`. -/
theorem quotIdeal_eq_map (b : Ideal (completedPolynomialAlgebra I r)) :
    quotIdeal A I r b =
      (I.map (algebraMap A (completedPolynomialAlgebra I r))).map (Ideal.Quotient.mk b) := by
  rw [Ideal.map_map]
  rfl

/-- **Step (C) of the proof of Stacks 0GAR: the threshold `q(S)` of the perturbed quotient.**
If `J` and `J'` have the same initial forms for `IP` — as the two ideals of a resolution and of a
nearby complex do, by step (B) (`exists_perturbationBound_sameInitialForms`) — then every `q₀`
with the defining property of `q(Gr_I(P ⧸ J))` has the defining property of
`q(Gr_I(P ⧸ J'))`: the property only depends on `Gr_I`
(`Stacks.LocalCohomology.UniformityIII.isBaseThreshold_iff_of_sameInitialForms`). -/
theorem isBaseThreshold_quotIdeal_of_sameInitialForms
    {J J' : Ideal (completedPolynomialAlgebra I r)}
    (h : SameInitialForms (I.map (algebraMap A (completedPolynomialAlgebra I r))) J J')
    {q₀ : ℕ} (hq : IsBaseThreshold (quotIdeal A I r J) q₀) :
    IsBaseThreshold (quotIdeal A I r J') q₀ := by
  rw [quotIdeal_eq_map] at hq ⊢
  exact (isBaseThreshold_iff_of_sameInitialForms _ h q₀).1 hq

/-- **Stacks 0GAR.** Let `I` be an ideal of a Noetherian ring `A`, `r ≥ 0` and
`P = A[x₁, …, x_r]^∧` the `I`-adic completion. Let `P^⊕t --K--> P^⊕m --(g₁, …, g_m)--> P → B → 0`
be a resolution of the quotient `B = P/(g₁, …, g_m)`, and assume `B` is rig-smooth over `(A, I)`.
Then there is an integer `n₀` such that for every `n ≥ n₀` and every complex
`P^⊕t --K'--> P^⊕m --(g'₁, …, g'_m)--> P` with `gᵢ - g'ᵢ ∈ IⁿP` and
`K - K' ∈ Iⁿ Mat(m × t, P)` there is an isomorphism of `A`-algebras `B ≅ B' = P/(g'₁, …, g'_m)`;
moreover the perturbed complex is again a resolution.

The proof is the source's.
* (A) `I^c` annihilates `Ext¹_B(NL^∧_{B/A}, -)` for some `c`, by rig-smoothness
  (`exists_extAnnihilated_of_isRigSmooth`).
* (B) For `n` beyond an Artin-Rees constant of the resolution the perturbed complex is a
  resolution (Stacks 07VE) and `Gr_I(B) ≅ Gr_I(B')` — as the equality of initial forms of the
  two ideals (Stacks 07VF, `exists_perturbationBound_sameInitialForms`).
* (C) The invariants of Local Cohomology, Section 0GA6 are those of `B`: `q₀ = q(Gr_I(B))` serves
  for `B'` because `q` only depends on `Gr_I` (`isBaseThreshold_quotIdeal_of_sameInitialForms`),
  and the vanishing degree `d` is read off a generating family of `I`, so it serves for every
  quotient of `P` (`subsingleton_blowupHmod_of_span`).
* Lemma 0GAQ (`Rig.exists_algHom_lift_of_dualSituation'`, via
  `exists_comparison_algHom_of_liftingInputsAboveExponent`) lifts
  the canonical `B → B'/IⁿB'` to an `A`-algebra map `φ : B → B'` congruent to it modulo a fixed
  power of `I`; its inputs are the blowup's dual situations and the duality input of Tag 0GAC
  (`liftingInputsOfIsBaseThreshold`).
* The final paragraph: such a `φ` is an isomorphism (`exists_perturbationBound_algEquiv_of_algHom`,
  by Artin-Rees and Nakayama).

The integer `n₀` absorbs the precision loss of the lifting lemma, so its exact value is
immaterial; the source's choice is `max(c₁ + 1, q₀ + (d₀ + 1)c, 2(d₀ + 1)c + 1)`. -/
@[stacks 0GAR]
public theorem exists_algEquiv_of_perturbation {t m : ℕ}
    (K : (Fin t → completedPolynomialAlgebra I r) →ₗ[completedPolynomialAlgebra I r]
      (Fin m → completedPolynomialAlgebra I r))
    (g : (Fin m → completedPolynomialAlgebra I r) →ₗ[completedPolynomialAlgebra I r]
      completedPolynomialAlgebra I r)
    (hexact : LinearMap.ker g = LinearMap.range K)
    (hB : IsRigSmooth (quotientObj A I r (LinearMap.range g))) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ (K' : (Fin t → completedPolynomialAlgebra I r) →ₗ[completedPolynomialAlgebra I r]
          (Fin m → completedPolynomialAlgebra I r))
        (g' : (Fin m → completedPolynomialAlgebra I r) →ₗ[completedPolynomialAlgebra I r]
          completedPolynomialAlgebra I r),
      g'.comp K' = 0 →
      CongruentModPow (I.map (algebraMap A (completedPolynomialAlgebra I r))) K K' n →
      CongruentModPow (I.map (algebraMap A (completedPolynomialAlgebra I r))) g g' n →
        LinearMap.ker g' = LinearMap.range K' ∧
        Nonempty
          ((completedPolynomialAlgebra I r ⧸
              (LinearMap.range g : Ideal (completedPolynomialAlgebra I r))) ≃ₐ[A]
            (completedPolynomialAlgebra I r ⧸
              (LinearMap.range g' : Ideal (completedPolynomialAlgebra I r)))) := by
  -- step (A): the exponent `c`
  obtain ⟨c, hc⟩ := exists_extAnnihilated_of_isRigSmooth A I r (LinearMap.range g) hB
  -- step (C): the invariants, `d` from a generating family of `I` and `q₀ = q(S)` of `B`
  obtain ⟨d, x, hx, hspan⟩ := exists_fin_succ_span_eq I
  set q₀ := qS (quotIdeal A I r (LinearMap.range g))
  have hq₀ : IsBaseThreshold (quotIdeal A I r (LinearMap.range g)) q₀ := isBaseThreshold_qS _
  set k := max d 1 - 1
  have hk : max d 1 = k + 1 := (Nat.sub_add_cancel (le_max_right d 1)).symm
  -- step (B), and the final paragraph of the source's proof
  obtain ⟨n₁, hn₁⟩ := exists_perturbationBound_algEquiv_of_algHom A I r ((k + 3) * c) K g hexact
  obtain ⟨n₂, hn₂⟩ := exists_perturbationBound_sameInitialForms A I r K g hexact
  refine ⟨max (max n₁ n₂) (max (q₀ + (k + 2) * c) (2 * ((k + 3) * c) + 1)),
    fun n hn K' g' hcomplex hKK' hgg' => ?_⟩
  obtain ⟨hker, hbound⟩ := hn₁ n (by omega) K' g' hcomplex hKK' hgg'
  have hq₀' := isBaseThreshold_quotIdeal_of_sameInitialForms A I r
    (hn₂ n (by omega) K' g' hcomplex hKK' hgg') hq₀
  -- Lemma 0GAQ: the comparison map
  obtain ⟨φ, hφ⟩ := exists_comparison_algHom_of_congruentModPow_of_liftingInputsAboveExponent
    A I r g g' n c d q₀ k hgg'
    (hc c le_rfl) (liftingInputsOfIsBaseThreshold A I r _ x hx hspan n c q₀ hq₀') hk
    (by omega) (by omega)
  exact ⟨hker, hbound φ hφ⟩

end Rig.PerturbedPresentation

end
