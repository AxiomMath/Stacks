module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SquareZeroDerivation
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SquareZeroLiftStage
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.TwistedDerivation

/-! # The differential of the square-zero lift

Let `q : R' → R` be a surjection of commutative rings and let `(A, 𝒜, γ, d)` be a graded divided
power polynomial algebra over `R` with a compatible differential. The algebra `B` lifting `A`
along `q`, together with the comparison morphism `π : B → A`, is built in
`StacksFrontier/RingTheory/DividedPowers/TateResolution/SquareZeroLiftData.lean` as the colimit of
an `ω`-tower. This file equips `B` with the operator `D` lifting `d`.

The operator is built one stage of the tower at a time. On the base of the tower there is nothing
to do: the base is concentrated in degree zero, so the zero map is a graded derivation there, and
it lifts `d` because `d` kills degree zero. The step from the `n`-th stage to the next adjoins the
variables of degree `n + 1`, and a graded derivation extends across such a step once a value of
degree `n` is prescribed for each new variable; the value prescribed is a preimage under `π` of
the differential of the corresponding variable of `A`, which exists by
`DividedPowers.TateResolution.exists_mem_grade_liftStage`. The stagewise operators are then
assembled into one operator on the colimit.

That the assembled operator lifts `d` is *not* automatic from the prescription: it has to be
propagated through each step. The two candidates `π ∘ D` and `d ∘ π` have the same values on the
coefficients and on the new variables, and their difference is a derivation along `π`, so they
agree by `DividedPowers.TateResolution.eq_zero_of_twisted_graded_leibniz`.

Note that `D` is *not* square-zero, and nothing here claims it is: its square is exactly the
obstruction from which Tag 09PS reads off a derivation of degree minus two.

## Main definitions

* `DividedPowers.TateResolution.IsLiftStageDerivation` — the clauses carried through the inductive
  construction: a graded derivation of a stage, compatible with the divided powers of that stage
  and lifting `d` along the comparison morphism.
* `DividedPowers.TateResolution.liftDerivation` — the operator `D` on the lifted algebra.

## Main results

* `DividedPowers.TateResolution.liftDerivation_eq_zero`,
  `DividedPowers.TateResolution.liftDerivation_mem_grade` and
  `DividedPowers.TateResolution.liftDerivation_leibniz` — `D` vanishes in degree zero, lowers
  every positive degree by one and obeys the signed Leibniz rule. These are the clauses
  `D_eq_zero`, `D_mem_grade` and `D_leibniz` of
  `DividedPowers.TateResolution.IsSquareZeroLift`.
* `DividedPowers.TateResolution.liftRingHom_liftDerivation` — `π` carries `D` to `d`. This is the
  clause `map_D`.
* `DividedPowers.TateResolution.liftDerivation_dpow` — `D` obeys the divided power Leibniz rule.
  This is the clause `D_dpow` of
  `DividedPowers.TateResolution.IsDividedPowerSquareZeroLift`.
* `DividedPowers.TateResolution.exists_isLiftStageDerivation_succ` — the inductive step, and
  `DividedPowers.TateResolution.exists_liftTowerDerivation` — the family of stagewise operators it
  produces.

## Implementation notes

The stagewise operators are built by `Nat.rec` into a subtype, rather than by recursion on the
underlying maps alone: the extension across a step consumes the hypotheses that the previous
operator is a graded derivation compatible with the divided powers, so the property has to travel
with the data.

The derivation is assembled from the stages as an *additive* map, by
`DividedPowers.TateResolution.chainColimit_existsUnique_addHom`, and upgraded to a linear map
afterwards by `DividedPowers.TateResolution.gradedDerivationToLinearMap`: a graded derivation
needs no linearity hypothesis to be linear, because the structure map lands in degree zero.

The Koszul sign is handled by `DividedPowers.TateResolution.neg_one_pow_smul_eq_mul`, which turns
the scalar action of `(-1 : R')` into multiplication by `(-1)` in the algebra. That is what lets
the sign of the Leibniz rule for `D`, over `R'`, be compared with the sign of the Leibniz rule for
`d`, over `R`: both become the same power of `-1` in `A`, so no compatibility between the two
scalar actions is needed.

## References

* [Stacks Project, Tag 09PK](https://stacks.math.columbia.edu/tag/09PK)
* [Stacks Project, Tag 09PS](https://stacks.math.columbia.edu/tag/09PS)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w z

attribute [local instance] GradedDPAlgebra.ring GradedDPAlgebra.algebra
  GradedDPAlgebra.graded GradedDPAlgebra.strict

attribute [local instance] gradedLimitGradedAlgebra gradedLimitStrictlyGradedComm

section Zero

/-- The zero operator is a graded derivation: all three axioms are vacuous for it. -/
public theorem isGradedDerivation_zero {R₀ : Type u} [CommRing R₀]
    (B : GradedDPAlgebra.{u, v} R₀) :
    IsGradedDerivation B.grade (0 : B.carrier →ₗ[R₀] B.carrier) where
  d_grade_zero := fun _ => LinearMap.zero_apply _
  d_mem := fun _ => by rw [LinearMap.zero_apply]; exact Submodule.zero_mem _
  leibniz := fun _ _ => by simp

/-- The zero operator is compatible with any divided power structure. -/
public theorem isCompatibleWithDifferential_zero {R₀ : Type u} [CommRing R₀]
    (B : GradedDPAlgebra.{u, v} R₀) :
    IsCompatibleWithDifferential B.gamma (0 : B.carrier →ₗ[R₀] B.carrier) where
  d_dpow := fun _ _ => by rw [LinearMap.zero_apply, LinearMap.zero_apply, zero_mul]

end Zero

section Differential

variable {R' : Type u} {R : Type v} {A : Type w} {σ : Type z}
  [CommRing R'] [CommRing R] [Ring A] [Algebra R A]
  (q : R' →+* R) {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
  {γ : DividedPowerStructure 𝒜} {ι : MvPolynomial σ R →ₐ[R] A}
  (hpoly : GradedDividedPowerPolynomial 𝒜 γ ι)
  (d : A →ₗ[R] A) [IsGradedDerivation 𝒜 d] [IsCompatibleWithDifferential γ d]

/-- The clauses carried through the inductive construction of the lifted differential: at the
`n`-th stage of the tower, a graded derivation compatible with the divided powers of that stage
and lifting `d` along the comparison morphism. -/
public structure IsLiftStageDerivation (n : ℕ)
    (D : (liftTowerStage (R' := R') hpoly n).carrier →ₗ[R']
      (liftTowerStage (R' := R') hpoly n).carrier) : Prop where
  /-- The operator is a graded derivation of the stage. -/
  graded : IsGradedDerivation (liftTowerStage (R' := R') hpoly n).grade D
  /-- The operator is compatible with the divided powers of the stage. -/
  compat : IsCompatibleWithDifferential (liftTowerStage (R' := R') hpoly n).gamma D
  /-- The comparison morphism carries the operator to the differential of `A`. -/
  map : ∀ y : (liftTowerStage (R' := R') hpoly n).carrier,
    liftStageRingHom q hpoly n (D y) = d (liftStageRingHom q hpoly n y)

omit [IsCompatibleWithDifferential γ d] in
/-- The base of the induction: the zero operator is a lift of `d` on the base of the tower. The
base is concentrated in degree zero, where both the Leibniz rule and the divided power formula are
vacuous and where `d` itself vanishes. -/
public theorem isLiftStageDerivation_zero : IsLiftStageDerivation q hpoly d 0 0 where
  graded := isGradedDerivation_zero (liftTowerStage (R' := R') hpoly 0)
  compat := isCompatibleWithDifferential_zero (liftTowerStage (R' := R') hpoly 0)
  map := by
    intro y
    rw [LinearMap.zero_apply, map_zero]
    exact (IsGradedDerivation.d_grade_zero (𝒜 := 𝒜) (d := d)
      (liftStageRingHom_mem_grade q hpoly 0 0 y
        (mem_liftTowerStage_zero_grade_zero (R' := R') hpoly y))).symm

/-- The inductive step: a lift of `d` on the `n`-th stage of the tower extends to one on the
stage `n + 1`, compatibly with the step.

The new variables are given the values furnished by
`DividedPowers.TateResolution.exists_mem_grade_liftStage`, and the extension exists by
`DividedPowers.TateResolution.existsUnique_gradedDerivation_setVariableExtension`. That the
extension again lifts `d` is proved by comparing `π ∘ D` with `d ∘ π`: their difference is a
derivation along `π` vanishing on the coefficients, on the new variables and on the divided powers
of the new variables, hence zero. -/
public theorem exists_isLiftStageDerivation_succ (hq : Function.Surjective q) (n : ℕ)
    (Dn : (liftTowerStage (R' := R') hpoly n).carrier →ₗ[R']
      (liftTowerStage (R' := R') hpoly n).carrier)
    (hDn : IsLiftStageDerivation q hpoly d n Dn) :
    ∃ Dn1 : (liftTowerStage (R' := R') hpoly (n + 1)).carrier →ₗ[R']
        (liftTowerStage (R' := R') hpoly (n + 1)).carrier,
      IsLiftStageDerivation q hpoly d (n + 1) Dn1 ∧
        ∀ y : (liftTowerStage (R' := R') hpoly n).carrier,
          Dn1 ((liftTowerStep (R' := R') hpoly n).hom y) =
            (liftTowerStep (R' := R') hpoly n).hom (Dn y) := by
  classical
  let _ : IsGradedDerivation (liftTowerStage (R' := R') hpoly n).grade Dn := hDn.graded
  let _ : IsCompatibleWithDifferential (liftTowerStage (R' := R') hpoly n).gamma Dn := hDn.compat
  have hdgen : ∀ j : liftIndex hpoly n, d (hpoly.generator ⟨n, j.down⟩) ∈ 𝒜 n := fun j =>
    IsGradedDerivation.d_mem (𝒜 := 𝒜) (d := d) (hpoly.generator_mem ⟨n, j.down⟩)
  choose ev hev hevmap using fun j : liftIndex hpoly n =>
    exists_mem_grade_liftStage q hpoly hq n (hdgen j)
  obtain ⟨D1, hD1, -⟩ := existsUnique_gradedDerivation_setVariableExtension
    (liftTowerStage (R' := R') hpoly n).grade (liftTowerStage (R' := R') hpoly n).gamma
    (liftTowerStage (R' := R') hpoly (n + 1)).grade
    (liftTowerStage (R' := R') hpoly (n + 1)).gamma (liftTowerStep (R' := R') hpoly n).hom
    (liftTowerGenerator (R' := R') hpoly n) (n + 1) n.succ_pos
    (liftTowerStage_isSetVariableExtension (R' := R') hpoly n) Dn ev (by simpa using hev)
  let _ : IsGradedDerivation (liftTowerStage (R' := R') hpoly (n + 1)).grade D1 := hD1.1
  let _ : IsCompatibleWithDifferential (liftTowerStage (R' := R') hpoly (n + 1)).gamma D1 :=
    hD1.2.2.2
  -- The difference of the two candidate lifts, as a map on the next stage.
  have hFadd : ∀ a b : (liftTowerStage (R' := R') hpoly (n + 1)).carrier,
      liftStageRingHom q hpoly (n + 1) (D1 (a + b)) -
          d (liftStageRingHom q hpoly (n + 1) (a + b)) =
        (liftStageRingHom q hpoly (n + 1) (D1 a) - d (liftStageRingHom q hpoly (n + 1) a)) +
          (liftStageRingHom q hpoly (n + 1) (D1 b) -
            d (liftStageRingHom q hpoly (n + 1) b)) := by
    intro a b
    simp only [map_add]
    abel
  have hFzero : ∀ x : (liftTowerStage (R' := R') hpoly (n + 1)).carrier,
      x ∈ (liftTowerStage (R' := R') hpoly (n + 1)).grade 0 →
        liftStageRingHom q hpoly (n + 1) (D1 x) -
          d (liftStageRingHom q hpoly (n + 1) x) = 0 := by
    intro x hx
    rw [IsGradedDerivation.d_grade_zero
        (𝒜 := (liftTowerStage (R' := R') hpoly (n + 1)).grade) (d := D1) hx, map_zero,
      IsGradedDerivation.d_grade_zero (𝒜 := 𝒜) (d := d)
        (liftStageRingHom_mem_grade q hpoly (n + 1) 0 x hx), sub_zero]
  have hFleib : ∀ (i k : ℕ) (x y : (liftTowerStage (R' := R') hpoly (n + 1)).carrier),
      x ∈ (liftTowerStage (R' := R') hpoly (n + 1)).grade i →
      y ∈ (liftTowerStage (R' := R') hpoly (n + 1)).grade k →
        liftStageRingHom q hpoly (n + 1) (D1 (x * y)) -
            d (liftStageRingHom q hpoly (n + 1) (x * y)) =
          (liftStageRingHom q hpoly (n + 1) (D1 x) -
              d (liftStageRingHom q hpoly (n + 1) x)) *
                liftStageRingHom q hpoly (n + 1) y +
            (-1 : A) ^ i * (liftStageRingHom q hpoly (n + 1) x *
              (liftStageRingHom q hpoly (n + 1) (D1 y) -
                d (liftStageRingHom q hpoly (n + 1) y))) := by
    intro i k x y hx hy
    rw [IsGradedDerivation.leibniz
        (𝒜 := (liftTowerStage (R' := R') hpoly (n + 1)).grade) (d := D1) hx hy,
      map_mul (liftStageRingHom q hpoly (n + 1)) x y,
      IsGradedDerivation.leibniz (𝒜 := 𝒜) (d := d)
        (liftStageRingHom_mem_grade q hpoly (n + 1) i x hx)
        (liftStageRingHom_mem_grade q hpoly (n + 1) k y hy),
      neg_one_pow_smul_eq_mul (R := R') i (x * D1 y),
      neg_one_pow_smul_eq_mul (R := R) i (liftStageRingHom q hpoly (n + 1) x *
        d (liftStageRingHom q hpoly (n + 1) y))]
    simp only [map_add, map_mul, map_pow, map_neg, map_one, sub_mul, mul_sub]
    abel
  have hFcoeff : ∀ a : (liftTowerStage (R' := R') hpoly n).carrier,
      liftStageRingHom q hpoly (n + 1) (D1 ((liftTowerStep (R' := R') hpoly n).hom a)) -
        d (liftStageRingHom q hpoly (n + 1) ((liftTowerStep (R' := R') hpoly n).hom a)) = 0 := by
    intro a
    rw [hD1.2.1 a, liftStageRingHom_step, liftStageRingHom_step, hDn.map a, sub_self]
  have hTj : ∀ j : liftIndex hpoly n,
      liftStageRingHom q hpoly (n + 1) (liftTowerGenerator (R' := R') hpoly n j) =
        hpoly.generator ⟨n, j.down⟩ := by
    intro j
    rw [liftStageRingHom_apply]
    exact liftRingHom_variable q hpoly n j.down
  have hFgen : ∀ j : liftIndex hpoly n,
      liftStageRingHom q hpoly (n + 1) (D1 (liftTowerGenerator (R' := R') hpoly n j)) -
        d (liftStageRingHom q hpoly (n + 1) (liftTowerGenerator (R' := R') hpoly n j)) = 0 := by
    intro j
    rw [hD1.2.2.1 j, liftStageRingHom_step, hTj j, hevmap j, sub_self]
  have hFdp : ∀ (j : liftIndex hpoly n) (m : ℕ),
      liftStageRingHom q hpoly (n + 1)
          (D1 ((liftTowerStage (R' := R') hpoly (n + 1)).gamma.dpow m
            (liftTowerGenerator (R' := R') hpoly n j))) -
        d (liftStageRingHom q hpoly (n + 1)
          ((liftTowerStage (R' := R') hpoly (n + 1)).gamma.dpow m
            (liftTowerGenerator (R' := R') hpoly n j))) = 0 := by
    intro j m
    by_cases hpe : liftTowerGenerator (R' := R') hpoly n j ∈
        positiveEvenPart (liftTowerStage (R' := R') hpoly (n + 1)).grade
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · rw [(liftTowerStage (R' := R') hpoly (n + 1)).gamma.dpow_zero hpe]
        exact hFzero 1 (SetLike.one_mem_graded _)
      · have hm' : m ≠ 0 := by omega
        have hpe' : liftStageRingHom q hpoly (n + 1) (liftTowerGenerator (R' := R') hpoly n j) ∈
            positiveEvenPart 𝒜 :=
          mem_positiveEvenPart_of_ringHom (liftTowerStage (R' := R') hpoly (n + 1)).grade 𝒜
            (liftStageRingHom q hpoly (n + 1))
            (fun l b hb => liftStageRingHom_mem_grade q hpoly (n + 1) l b hb) hpe
        rw [IsCompatibleWithDifferential.d_dpow
            (γ := (liftTowerStage (R' := R') hpoly (n + 1)).gamma) (d := D1) hm' hpe,
          liftStageRingHom_dpow q hpoly (n + 1) m _ hpe,
          IsCompatibleWithDifferential.d_dpow (γ := γ) (d := d) hm' hpe',
          map_mul, liftStageRingHom_dpow q hpoly (n + 1) (m - 1) _ hpe, sub_eq_zero.1 (hFgen j),
          sub_self]
    · rw [(liftTowerStage (R' := R') hpoly (n + 1)).gamma.dpow_null hpe]
      simp
  have hmapsucc : ∀ z : (liftTowerStage (R' := R') hpoly (n + 1)).carrier,
      liftStageRingHom q hpoly (n + 1) (D1 z) = d (liftStageRingHom q hpoly (n + 1) z) := by
    intro z
    refine sub_eq_zero.1 ?_
    exact eq_zero_of_twisted_graded_leibniz
      (liftTowerStage_isSetVariableExtension (R' := R') hpoly n)
      (liftStageRingHom q hpoly (n + 1))
      (AddMonoidHom.mk' (fun w => liftStageRingHom q hpoly (n + 1) (D1 w) -
        d (liftStageRingHom q hpoly (n + 1) w)) hFadd)
      hFzero hFleib hFcoeff hFgen hFdp z
  exact ⟨D1, ⟨hD1.1, hD1.2.2.2, hmapsucc⟩, hD1.2.1⟩

/-- The family of lifts of `d` along the tower, one for each stage, compatible with the steps. -/
public theorem exists_liftTowerDerivation (hq : Function.Surjective q) :
    ∃ D : (n : ℕ) → (liftTowerStage (R' := R') hpoly n).carrier →ₗ[R']
        (liftTowerStage (R' := R') hpoly n).carrier,
      (∀ n : ℕ, IsLiftStageDerivation q hpoly d n (D n)) ∧
        ∀ (n : ℕ) (y : (liftTowerStage (R' := R') hpoly n).carrier),
          D (n + 1) ((liftTowerStep (R' := R') hpoly n).hom y) =
            (liftTowerStep (R' := R') hpoly n).hom (D n y) := by
  classical
  let F : (n : ℕ) → {D : (liftTowerStage (R' := R') hpoly n).carrier →ₗ[R']
      (liftTowerStage (R' := R') hpoly n).carrier // IsLiftStageDerivation q hpoly d n D} :=
    fun n => Nat.rec (motive := fun n => {D : (liftTowerStage (R' := R') hpoly n).carrier →ₗ[R']
        (liftTowerStage (R' := R') hpoly n).carrier // IsLiftStageDerivation q hpoly d n D})
      ⟨0, isLiftStageDerivation_zero q hpoly d⟩
      (fun k Fk => ⟨(exists_isLiftStageDerivation_succ q hpoly d hq k Fk.1 Fk.2).choose,
        (exists_isLiftStageDerivation_succ q hpoly d hq k Fk.1 Fk.2).choose_spec.1⟩) n
  exact ⟨fun n => (F n).1, fun n => (F n).2, fun n y =>
    (exists_isLiftStageDerivation_succ q hpoly d hq n (F n).1 (F n).2).choose_spec.2 y⟩

/-- The operator `D` of Tag 09PS exists on the lifted algebra: a graded derivation of degree minus
one, compatible with the divided powers, which the comparison morphism carries to the differential
of `A`.

The five clauses are, in order, `D_eq_zero`, `D_mem_grade`, `D_leibniz` and `map_D` of
`DividedPowers.TateResolution.IsSquareZeroLift`, and `D_dpow` of
`DividedPowers.TateResolution.IsDividedPowerSquareZeroLift`. -/
public theorem exists_liftDerivation (hq : Function.Surjective q) :
    ∃ D : (liftAlgebra (R' := R') hpoly).carrier →ₗ[R']
        (liftAlgebra (R' := R') hpoly).carrier,
      (∀ b : (liftAlgebra (R' := R') hpoly).carrier,
          b ∈ (liftAlgebra (R' := R') hpoly).grade 0 → D b = 0) ∧
        (∀ (n : ℕ) (b : (liftAlgebra (R' := R') hpoly).carrier),
          b ∈ (liftAlgebra (R' := R') hpoly).grade (n + 1) →
            D b ∈ (liftAlgebra (R' := R') hpoly).grade n) ∧
        (∀ (i k : ℕ) (b c : (liftAlgebra (R' := R') hpoly).carrier),
          b ∈ (liftAlgebra (R' := R') hpoly).grade i →
          c ∈ (liftAlgebra (R' := R') hpoly).grade k →
            D (b * c) = D b * c + (-1 : R') ^ i • (b * D c)) ∧
        (∀ b : (liftAlgebra (R' := R') hpoly).carrier,
          liftRingHom q hpoly (D b) = d (liftRingHom q hpoly b)) ∧
        ∀ (n : ℕ) (b : (liftAlgebra (R' := R') hpoly).carrier), n ≠ 0 →
          b ∈ positiveEvenPart (liftAlgebra (R' := R') hpoly).grade →
            D ((liftAlgebra (R' := R') hpoly).gamma.dpow n b) =
              D b * (liftAlgebra (R' := R') hpoly).gamma.dpow (n - 1) b := by
  classical
  obtain ⟨DS, hDS, hDSstep⟩ := exists_liftTowerDerivation q hpoly d hq
  obtain ⟨G, hG, -⟩ := chainColimit_existsUnique_addHom (liftTowerStage (R' := R') hpoly)
    (liftTowerStep (R' := R') hpoly)
    (fun n => (liftTowerInclusion (R' := R') hpoly n).hom.toAddMonoidHom.comp
      (DS n).toAddMonoidHom)
    (by
      intro n x
      change (liftTowerInclusion (R' := R') hpoly (n + 1)).hom
          (DS (n + 1) ((liftTowerStep (R' := R') hpoly n).hom x)) =
        (liftTowerInclusion (R' := R') hpoly n).hom (DS n x)
      rw [hDSstep n x]
      exact chainColimitInclusion_step (liftTowerStage (R' := R') hpoly)
        (liftTowerStep (R' := R') hpoly) n (DS n x))
  have hGstage : ∀ (n : ℕ) (x : (liftTowerStage (R' := R') hpoly n).carrier),
      G ((liftTowerInclusion (R' := R') hpoly n).hom x) =
        (liftTowerInclusion (R' := R') hpoly n).hom (DS n x) := fun n x => hG n x
  have hzero : ∀ x : (liftAlgebra (R' := R') hpoly).carrier,
      x ∈ (liftAlgebra (R' := R') hpoly).grade 0 → G x = 0 := by
    intro x hx
    obtain ⟨n, u, hu, rfl⟩ := (chainColimit_mem_grade_iff (liftTowerStage (R' := R') hpoly)
      (liftTowerStep (R' := R') hpoly) 0 x).1 hx
    rw [hGstage n u,
      IsGradedDerivation.d_grade_zero (𝒜 := (liftTowerStage (R' := R') hpoly n).grade)
        (d := DS n) (self := (hDS n).graded) hu, map_zero]
  have hmem : ∀ (m : ℕ) (x : (liftAlgebra (R' := R') hpoly).carrier),
      x ∈ (liftAlgebra (R' := R') hpoly).grade (m + 1) →
        G x ∈ (liftAlgebra (R' := R') hpoly).grade m := by
    intro m x hx
    obtain ⟨n, u, hu, rfl⟩ := (chainColimit_mem_grade_iff (liftTowerStage (R' := R') hpoly)
      (liftTowerStep (R' := R') hpoly) (m + 1) x).1 hx
    rw [hGstage n u]
    exact (liftTowerInclusion (R' := R') hpoly n).map_grade m _
      (IsGradedDerivation.d_mem (𝒜 := (liftTowerStage (R' := R') hpoly n).grade) (d := DS n)
        (self := (hDS n).graded) hu)
  have hleib : ∀ (i k : ℕ) (x y : (liftAlgebra (R' := R') hpoly).carrier),
      x ∈ (liftAlgebra (R' := R') hpoly).grade i →
      y ∈ (liftAlgebra (R' := R') hpoly).grade k →
        G (x * y) = G x * y + (-1 : R') ^ i • (x * G y) := by
    intro i k x y hx hy
    obtain ⟨N, u, v, hu, hv, rfl, rfl⟩ := exists_stage_pair_mem_grade hpoly i k hx hy
    rw [← map_mul (liftTowerInclusion (R' := R') hpoly N).hom u v, hGstage N (u * v),
      hGstage N u, hGstage N v,
      IsGradedDerivation.leibniz (𝒜 := (liftTowerStage (R' := R') hpoly N).grade) (d := DS N)
        (self := (hDS N).graded) hu hv,
      map_add, map_mul, map_smul, map_mul]
  refine ⟨gradedDerivationToLinearMap (liftAlgebra (R' := R') hpoly).grade G hzero hleib,
    fun b hb => hzero b hb, fun n b hb => hmem n b hb, fun i k b c hb hc => hleib i k b c hb hc,
    ?_, ?_⟩
  · intro b
    obtain ⟨n, u, rfl⟩ := chainColimit_exists_stage (liftTowerStage (R' := R') hpoly)
      (liftTowerStep (R' := R') hpoly) b
    rw [gradedDerivationToLinearMap_apply, hGstage n u]
    exact (hDS n).map u
  · intro m b hm hb
    obtain ⟨n, u, rfl⟩ := chainColimit_exists_stage (liftTowerStage (R' := R') hpoly)
      (liftTowerStep (R' := R') hpoly) b
    have hu : u ∈ positiveEvenPart (liftTowerStage (R' := R') hpoly n).grade :=
      mem_positiveEvenPart_of_map_mem_positiveEvenPart
        (liftTowerStage (R' := R') hpoly n).grade (liftAlgebra (R' := R') hpoly).grade
        (liftTowerInclusion (R' := R') hpoly n).hom
        (fun l a ha => (liftTowerInclusion (R' := R') hpoly n).map_grade l a ha)
        (towerInclusion_injective.{u, max v w z, w} (liftBase R' σ R A) (liftIndex hpoly) n) hb
    rw [chainColimitInclusion_dpow (liftTowerStage (R' := R') hpoly)
        (liftTowerStep (R' := R') hpoly) n m u hu,
      chainColimitInclusion_dpow (liftTowerStage (R' := R') hpoly)
        (liftTowerStep (R' := R') hpoly) n (m - 1) u hu,
      gradedDerivationToLinearMap_apply, gradedDerivationToLinearMap_apply,
      hGstage n _, hGstage n u,
      IsCompatibleWithDifferential.d_dpow
        (γ := (liftTowerStage (R' := R') hpoly n).gamma) (d := DS n)
        (self := (hDS n).compat) hm hu,
      map_mul]

/-- The operator `D` of Tag 09PS on the lifted algebra: a graded derivation of degree minus one
lifting the differential of `A`. It is not square-zero; its square is the obstruction from which
the tag reads off a derivation of degree minus two. -/
public noncomputable def liftDerivation (hq : Function.Surjective q) :
    (liftAlgebra (R' := R') hpoly).carrier →ₗ[R'] (liftAlgebra (R' := R') hpoly).carrier :=
  (exists_liftDerivation q hpoly d hq).choose

/-- The lifted operator vanishes in degree zero. This is the clause `D_eq_zero` of
`DividedPowers.TateResolution.IsSquareZeroLift`. -/
public theorem liftDerivation_eq_zero (hq : Function.Surjective q)
    (b : (liftAlgebra (R' := R') hpoly).carrier)
    (hb : b ∈ (liftAlgebra (R' := R') hpoly).grade 0) : liftDerivation q hpoly d hq b = 0 :=
  (exists_liftDerivation q hpoly d hq).choose_spec.1 b hb

/-- The lifted operator lowers every positive degree by one. This is the clause `D_mem_grade` of
`DividedPowers.TateResolution.IsSquareZeroLift`. -/
public theorem liftDerivation_mem_grade (hq : Function.Surjective q) (n : ℕ)
    (b : (liftAlgebra (R' := R') hpoly).carrier)
    (hb : b ∈ (liftAlgebra (R' := R') hpoly).grade (n + 1)) :
    liftDerivation q hpoly d hq b ∈ (liftAlgebra (R' := R') hpoly).grade n :=
  (exists_liftDerivation q hpoly d hq).choose_spec.2.1 n b hb

/-- The lifted operator satisfies the signed Leibniz rule on homogeneous elements. This is the
clause `D_leibniz` of `DividedPowers.TateResolution.IsSquareZeroLift`. -/
public theorem liftDerivation_leibniz (hq : Function.Surjective q) (i k : ℕ)
    (b c : (liftAlgebra (R' := R') hpoly).carrier)
    (hb : b ∈ (liftAlgebra (R' := R') hpoly).grade i)
    (hc : c ∈ (liftAlgebra (R' := R') hpoly).grade k) :
    liftDerivation q hpoly d hq (b * c) =
      liftDerivation q hpoly d hq b * c + (-1 : R') ^ i • (b * liftDerivation q hpoly d hq c) :=
  (exists_liftDerivation q hpoly d hq).choose_spec.2.2.1 i k b c hb hc

/-- The comparison morphism carries the lifted operator to the differential of `A`. This is the
clause `map_D` of `DividedPowers.TateResolution.IsSquareZeroLift`. -/
public theorem liftRingHom_liftDerivation (hq : Function.Surjective q)
    (b : (liftAlgebra (R' := R') hpoly).carrier) :
    liftRingHom q hpoly (liftDerivation q hpoly d hq b) = d (liftRingHom q hpoly b) :=
  (exists_liftDerivation q hpoly d hq).choose_spec.2.2.2.1 b

/-- The lifted operator obeys the divided power Leibniz rule. This is the clause `D_dpow` of
`DividedPowers.TateResolution.IsDividedPowerSquareZeroLift`. -/
public theorem liftDerivation_dpow (hq : Function.Surjective q) (n : ℕ)
    (b : (liftAlgebra (R' := R') hpoly).carrier) (hn : n ≠ 0)
    (hb : b ∈ positiveEvenPart (liftAlgebra (R' := R') hpoly).grade) :
    liftDerivation q hpoly d hq ((liftAlgebra (R' := R') hpoly).gamma.dpow n b) =
      liftDerivation q hpoly d hq b * (liftAlgebra (R' := R') hpoly).gamma.dpow (n - 1) b :=
  (exists_liftDerivation q hpoly d hq).choose_spec.2.2.2.2 n b hn hb

end Differential

end DividedPowers.TateResolution

end
