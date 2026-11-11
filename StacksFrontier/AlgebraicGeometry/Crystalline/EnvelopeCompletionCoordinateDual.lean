module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedFormsOfCompletion
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDifferentialsDual
public import StacksFrontier.AlgebraicGeometry.Crystalline.CoordinateDualRetractPairs
public import StacksFrontier.AlgebraicGeometry.Crystalline.EnvelopeRetractPairs

/-!
# Topological coordinates on the completed envelope of a polynomial presentation

Let `E = D_{P,γ}(J)` be the divided power envelope of a polynomial presentation
`P = A[x_i : i ∈ ι] ⊇ J`, for **any** family of variables, and `D` its `p`-adic completion.  This
module proves that `D` with its completed divided power forms `Ω̂^*_D` carries the topological
coordinates `Crystalline.CompletedCoordinateDualData` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CoordinateDualRetractPairs.lean`, and that a retract
`a ∘ b = id` of divided power `A`-algebras with `D` as source of `a` carries the retract data
`Crystalline.CoordinateDualRetractData`.

* `Ω̂¹_D` is the completion of the module `Ω_{E/A,δ}`, which is free on the `d x_i`
  (`Crystalline.envelopeDifferentialsBasis`); the completed coordinates of that basis are
  coordinate functionals on `Ω̂¹_D` dual to the `d x_i`
  (`Crystalline.envelopeCompletionCoordFun`), and every one-form is, modulo `p^n`, a finite
  combination of the `d x_i` (`Crystalline.envelopeCompletionForms_approx`).  With infinitely many
  variables `Ω̂¹_D` is not free on the `d x_i`; this topological freeness is what replaces the
  basis.
* The coordinate derivations `∂_i a = c_i(d a)` extend the first-order Taylor operators `δ_i` of
  `E` (`Crystalline.envelopeCompletionCoordDelta_inclusion`), by the derivation formula
  `Crystalline.envelopeTaylor_derivation_finset`, and so commute.
* **Taylor's formula at the levels** for a divided power endomorphism `ρ` of `D` over `A`
  compatible with the augmentation (`Crystalline.envelopeCompletion_coordDual_taylor_levels`), as
  in `Crystalline.envelopeCompletion_taylor_levels`.

## References

* [Stacks Project, Tag 07J9](https://stacks.math.columbia.edu/tag/07J9)
* [Stacks Project, Tag 07HW](https://stacks.math.columbia.edu/tag/07HW)
* [Stacks Project, Lemma 60.17.5, Tag 07L5](https://stacks.math.columbia.edu/tag/07L5)
* [Stacks Project, Remark 60.17.6, Tag 07L6](https://stacks.math.columbia.edu/tag/07L6)
-/

@[expose] public noncomputable section

open DividedPowers
open scoped TensorProduct

universe u

namespace Crystalline

attribute [local instance] dpMorphismRingHomClass

/-! ### Topological freeness from density -/

section Approx

variable (p : ℕ) {D : Type u} [CommRing D] {Omega : Type u} [AddCommGroup Omega]
  [Module D Omega] {ι : Type u} {dx : ι → Omega} {cf : ι → (Omega →ₗ[D] D)}

/-- A `D`-linear functional carries `pⁿ Ω` into `pⁿ D`. -/
theorem functional_mem_pAdicIdeal_pow (c : Omega →ₗ[D] D) {n : ℕ} {ω : Omega}
    (hω : ω ∈ pPowSmul p D Omega n) : c ω ∈ pAdicIdeal (A := D) p ^ n := by
  obtain ⟨y, hy⟩ := (mem_pPowSmul_iff p D Omega).mp hω
  rw [← hy, map_smul, smul_eq_mul]
  exact Ideal.mul_mem_right _ _ (CompletedDeRham.pow_mem_pAdicIdeal_pow p D n)

/-- **Topological freeness from density**: if every one-form is, modulo `pⁿ`, some finite
combination of the `d x_i`, then it is, modulo `pⁿ`, the finite combination of the `d x_i` with
its own coordinates as coefficients, and its other coordinates lie in `pⁿ D`. -/
theorem approx_of_dense (hc : IsCoordinateDual dx cf)
    (hdense : ∀ (ω : Omega) (n : ℕ), ∃ (T : Finset ι) (c : ι → D),
      ω - ∑ i ∈ T, c i • dx i ∈ pPowSmul p D Omega n) (ω : Omega) (n : ℕ) :
    ∃ T : Finset ι, (∀ i ∉ T, cf i ω ∈ pAdicIdeal (A := D) p ^ n) ∧
      ω - ∑ i ∈ T, cf i ω • dx i ∈ pPowSmul p D Omega n := by
  classical
  obtain ⟨T, c, hr⟩ := hdense ω n
  set r := ω - ∑ i ∈ T, c i • dx i with hr'
  have hcf : ∀ k, cf k ω = (if k ∈ T then c k else 0) + cf k r := by
    intro k
    have hω : ω = ∑ i ∈ T, c i • dx i + r := by rw [hr']; abel
    conv_lhs => rw [hω]
    rw [map_add, map_sum]
    congr 1
    have hterm : ∀ i ∈ T, cf k (c i • dx i) = if i = k then c k else 0 := by
      intro i _
      rw [map_smul, smul_eq_mul]
      split_ifs with hik
      · subst hik; rw [hc.self, mul_one]
      · rw [hc.of_ne hik, mul_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  have hcfr : ∀ k, cf k r ∈ pAdicIdeal (A := D) p ^ n :=
    fun k ↦ functional_mem_pAdicIdeal_pow p (cf k) hr
  refine ⟨T, fun i hi ↦ ?_, ?_⟩
  · rw [hcf]
    simp only [hi, ↓reduceIte, zero_add]
    exact hcfr i
  · have heq : ω - ∑ i ∈ T, cf i ω • dx i = r + ∑ i ∈ T, (-cf i r) • dx i := by
      have hsum : ∑ i ∈ T, cf i ω • dx i = ∑ i ∈ T, (c i + cf i r) • dx i :=
        Finset.sum_congr rfl fun i hi ↦ by rw [hcf]; simp only [hi, ↓reduceIte]
      rw [hsum, hr']
      simp only [add_smul, neg_smul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
      abel
    rw [heq]
    refine Submodule.add_mem _ hr (Submodule.sum_mem _ fun i _ ↦ ?_)
    exact smul_mem_pPowSmul_of_mem p (Submodule.neg_mem _ (hcfr i)) _

end Approx

/-! ### The completed one-forms of a completion and the completed differentials -/

section Generic

variable {A : Type u} {B : Type u} [CommRing A] [CommRing B] [Algebra A B] (J : Ideal B)
  (delta : _root_.DividedPowers J) (p : ℕ) [Fact p.Prime]
  (hp : IsNilpotent (Ideal.Quotient.mk J (p : B)))

/-- **The completed one-forms `Ω̂¹_{B̂/A,γ̂}` of the completion are the completion of
`Ω_{B/A,δ}`**, `B̂`-linearly, by the comparison of [Stacks, Lemma 60.20.1, Tag 07KK]. -/
def completedFormsCompletionEquiv :
    completedDividedPowerForms p A (completedDividedPowers J delta p hp).1 1 ≃ₗ[
        AdicCompletion (pAdicIdeal (A := B) p) B]
      AdicCompletion (pAdicIdeal (A := B) p) (dividedPowerDifferentials (A := A) delta) :=
  letI : IsAdicComplete (pAdicIdeal (A := AdicCompletion (pAdicIdeal (A := B) p) B) p)
      (AdicCompletion (pAdicIdeal (A := B) p) (dividedPowerDifferentials (A := A) delta)) :=
    isAdicComplete_adicCompletion_completion p _
  (adicCompletionCongrBase _ (exteriorPower.oneEquiv _ _)).trans
    ((completedDifferentialsCompletionEquiv J delta p hp).trans
      (AdicCompletion.ofLinearEquiv _ _).symm)

/-- The comparison carries the universal differential of the completion at the image of `x` to
the completion of `d x`. -/
theorem completedFormsCompletionEquiv_differential (x : B) :
    completedFormsCompletionEquiv J delta p hp
        (AdicCompletion.of (pAdicIdeal (A := AdicCompletion (pAdicIdeal (A := B) p) B) p) _
          (dividedPowerOneForm A (completedDividedPowers J delta p hp).1
            (AdicCompletion.of (pAdicIdeal (A := B) p) B x))) =
      AdicCompletion.of (pAdicIdeal (A := B) p) _ (dividedPowerDifferential (A := A) delta x) := by
  rw [dividedPowerOneForm_apply, completedFormsCompletionEquiv, LinearEquiv.trans_apply,
    LinearEquiv.trans_apply, adicCompletionCongrBase_of, LinearEquiv.apply_symm_apply,
    completedDifferentialsCompletionEquiv_of, AdicCompletion.ofLinearEquiv_symm_of]

/-- The comparison carries the universal differential of the completion at the image of `x` to
the completion of `d x`, stated with the differential of the completed ring. -/
theorem completedFormsCompletionEquiv_differentialOnRing (x : B) :
    completedFormsCompletionEquiv J delta p hp
        (completedDividedPowerDifferentialOnRing p A (completedDividedPowers J delta p hp).1
          (AdicCompletion.of (pAdicIdeal (A := B) p) B x)) =
      AdicCompletion.of (pAdicIdeal (A := B) p) _ (dividedPowerDifferential (A := A) delta x) :=
  (congrArg (completedFormsCompletionEquiv J delta p hp)
    (completedDividedPowerDifferentialOnRing_eq p A _ _)).trans
    (completedFormsCompletionEquiv_differential J delta p hp x)

end Generic

/-! ### The completed one-forms of the completed envelope -/

section Envelope

variable {A : DividedPowerRing.{u}} {ι : Type u}
  {J : Ideal (MvPolynomial ι A)} {hJ : A.ideal.map (algebraMap A (MvPolynomial ι A)) ≤ J}
  (E : DividedPowerEnvelope A (algebraMap A (MvPolynomial ι A)) J hJ) (p : ℕ) [Fact p.Prime]
  (hp : IsNilpotent (Ideal.Quotient.mk E.object.ideal (p : E.object)))

/-- The completion of an `E`-module is a module over the completed envelope `D`, `D` being the
completion of `E`. -/
@[instance_reducible]
def moduleEnvelopeCompletionAdicCompletion (M : Type u) [AddCommGroup M] [Module E.object M] :
    Module (envelopeCompletion E p hp : Type u)
      (AdicCompletion (pAdicIdeal (A := (E.object : Type u)) p) M) :=
  inferInstanceAs (Module (AdicCompletion (pAdicIdeal (A := (E.object : Type u)) p) E.object)
    (AdicCompletion (pAdicIdeal (A := (E.object : Type u)) p) M))

attribute [local instance] moduleEnvelopeCompletionAdicCompletion

/-- **`Ω̂¹_D` is the completion of `Ω_{E/A,δ}`**, linearly over `D`: the comparison of
[Stacks, Lemma 60.20.1, Tag 07KK] of the completed one-forms of the completion with the completion
of the divided power differentials. -/
def envelopeCompletionFormsEquivCompletion :
    letI : Algebra (A : Type u) E.object := E.structureMap.toRingHom.toAlgebra
    envelopeCompletionForms E p hp 1 ≃ₗ[envelopeCompletion E p hp]
      AdicCompletion (pAdicIdeal (A := (E.object : Type u)) p)
        (dividedPowerDifferentials (A := (A : Type u)) E.object.dividedPowers) :=
  letI : Algebra (A : Type u) E.object := E.structureMap.toRingHom.toAlgebra
  ((completedDividedPowerFormsAlgebraCongr p (A : Type u)
      (B := AdicCompletion (pAdicIdeal (A := (E.object : Type u)) p) E.object)
      (completedDividedPowers E.object.ideal E.object.dividedPowers p hp).1 1 inferInstance
      (algebraBaseEnvelopeCompletion E p hp) (Algebra.algebra_ext _ _ fun _ ↦ rfl)).symm.trans
    (completedFormsCompletionEquiv E.object.ideal E.object.dividedPowers p hp) :
    _ ≃ₗ[AdicCompletion (pAdicIdeal (A := (E.object : Type u)) p) E.object] _)

/-- The comparison `Ω̂¹_D → Ω̂_{E/A,δ}`. -/
def envelopeCompletionFormsToCompletion :
    letI : Algebra (A : Type u) E.object := E.structureMap.toRingHom.toAlgebra
    envelopeCompletionForms E p hp 1 →ₗ[envelopeCompletion E p hp]
      AdicCompletion (pAdicIdeal (A := (E.object : Type u)) p)
        (dividedPowerDifferentials (A := (A : Type u)) E.object.dividedPowers) :=
  (envelopeCompletionFormsEquivCompletion E p hp).toLinearMap

/-- The comparison `Ω̂_{E/A,δ} → Ω̂¹_D`, inverse to
`Crystalline.envelopeCompletionFormsToCompletion`. -/
def envelopeCompletionFormsFromCompletion :
    letI : Algebra (A : Type u) E.object := E.structureMap.toRingHom.toAlgebra
    AdicCompletion (pAdicIdeal (A := (E.object : Type u)) p)
        (dividedPowerDifferentials (A := (A : Type u)) E.object.dividedPowers)
            →ₗ[envelopeCompletion E p hp]
      envelopeCompletionForms E p hp 1 :=
  (envelopeCompletionFormsEquivCompletion E p hp).symm.toLinearMap

/-- The two comparisons are inverse. -/
theorem envelopeCompletionFormsFromCompletion_toCompletion (ω : envelopeCompletionForms E p hp 1) :
    envelopeCompletionFormsFromCompletion E p hp (envelopeCompletionFormsToCompletion E p hp ω) =
      ω :=
  (envelopeCompletionFormsEquivCompletion E p hp).symm_apply_apply ω

/-- **The comparison carries `d x_i` to the completion of the basis vector `d y_i`.** -/
theorem envelopeCompletionFormsToCompletion_differential (i : ι) :
    letI : Algebra (A : Type u) E.object := E.structureMap.toRingHom.toAlgebra
    envelopeCompletionFormsToCompletion E p hp
        (envelopeCompletionFormsDifferential E p hp (envelopeCompletionCoord E p hp i)) =
      AdicCompletion.of (pAdicIdeal (A := (E.object : Type u)) p)
        (dividedPowerDifferentials (A := (A : Type u)) E.object.dividedPowers)
        (envelopeDifferentialsBasis E i) := by
  let : Algebra (A : Type u) E.object := E.structureMap.toRingHom.toAlgebra
  have h1 := completedDividedPowerFormsAlgebraCongr_differentialOnRing p (A : Type u)
    (B := AdicCompletion (pAdicIdeal (A := (E.object : Type u)) p) E.object)
    (completedDividedPowers E.object.ideal E.object.dividedPowers p hp).1 inferInstance
    (algebraBaseEnvelopeCompletion E p hp) (Algebra.algebra_ext _ _ fun _ ↦ rfl)
    (AdicCompletion.of (pAdicIdeal (A := (E.object : Type u)) p) _
      (E.algebraMap.toRingHom (MvPolynomial.X i)))
  have ha := (LinearEquiv.symm_apply_eq _).mpr h1.symm
  exact (congrArg (completedFormsCompletionEquiv E.object.ideal E.object.dividedPowers p hp)
      ha).trans
    ((completedFormsCompletionEquiv_differentialOnRing E.object.ideal E.object.dividedPowers p hp
        _).trans
      (congrArg _ (envelopeDifferentialsBasis_apply E i).symm))

/-- **The coordinate functionals `c_j : Ω̂¹_D → D`**: the completed coordinates of the basis
`d y_i` of `Ω_{E/A,δ}`, read on `Ω̂¹_D` through the comparison with the completion. -/
def envelopeCompletionCoordFun (j : ι) :
    envelopeCompletionForms E p hp 1 →ₗ[envelopeCompletion E p hp] envelopeCompletion E p hp :=
  letI : Algebra (A : Type u) E.object := E.structureMap.toRingHom.toAlgebra
  { toFun := fun ω ↦ adicDualFamily (pAdicIdeal (A := (E.object : Type u)) p)
      (envelopeDifferentialsBasis E) j (envelopeCompletionFormsToCompletion E p hp ω)
    map_add' := fun ω η ↦ by simp only [map_add]; rfl
    map_smul' := fun r ω ↦ by
      rw [map_smul]
      exact (adicDualFamily (pAdicIdeal (A := (E.object : Type u)) p)
        (envelopeDifferentialsBasis E) j).map_smul r _ }

/-- **The coordinate functionals are dual to the `d x_i`.** -/
theorem isCoordinateDual_envelopeCompletionCoordFun :
    IsCoordinateDual (fun i ↦ envelopeCompletionFormsDifferential E p hp
      (envelopeCompletionCoord E p hp i)) (envelopeCompletionCoordFun E p hp) := by
  let : Algebra (A : Type u) E.object := E.structureMap.toRingHom.toAlgebra
  have hdual := isCoordinateDual_adicDualFamily (pAdicIdeal (A := (E.object : Type u)) p)
    (envelopeDifferentialsBasis E) (dx := fun i ↦ AdicCompletion.of _ _
        (envelopeDifferentialsBasis E i))
    fun _ ↦ rfl
  refine ⟨fun i ↦ ?_, fun {i j} hij ↦ ?_⟩
  · change adicDualFamily _ _ i (envelopeCompletionFormsToCompletion E p hp _) = 1
    rw [envelopeCompletionFormsToCompletion_differential]
    exact hdual.self i
  · change adicDualFamily _ _ j (envelopeCompletionFormsToCompletion E p hp _) = 0
    rw [envelopeCompletionFormsToCompletion_differential]
    exact hdual.of_ne hij

/-- **The one-forms are dense in the combinations of the `d x_i`**: modulo `pⁿ`, every element
of `Ω̂¹_D` is a finite `D`-combination of the `d x_i`. -/
theorem envelopeCompletionForms_dense (ω : envelopeCompletionForms E p hp 1) (n : ℕ) :
    ∃ (T : Finset ι) (c : ι → envelopeCompletion E p hp),
      ω - ∑ i ∈ T, c i • envelopeCompletionFormsDifferential E p hp
          (envelopeCompletionCoord E p hp i) ∈
        pPowSmul p (envelopeCompletion E p hp : Type u) (envelopeCompletionForms E p hp 1) n := by
  classical
  let : Algebra (A : Type u) E.object := E.structureMap.toRingHom.toAlgebra
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ ((envelopeCompletionFormsToCompletion E p
      hp ω).val n)
  have hz := sub_of_mem_pow_smul_top p (envelopeCompletionFormsToCompletion E p hp ω) n x hx.symm
  refine ⟨((envelopeDifferentialsBasis E).repr x).support, fun i ↦ AdicCompletion.of _ _
      ((envelopeDifferentialsBasis E).repr x i), ?_⟩
  have hΨ : ∀ i, envelopeCompletionFormsFromCompletion E p hp (AdicCompletion.of (pAdicIdeal (A :=
      (E.object : Type u)) p) _ (envelopeDifferentialsBasis E i)) =
      envelopeCompletionFormsDifferential E p hp (envelopeCompletionCoord E p hp i) := by
    intro i
    rw [← envelopeCompletionFormsToCompletion_differential]
    exact envelopeCompletionFormsFromCompletion_toCompletion E p hp _
  have hx' : x = ∑ i ∈ ((envelopeDifferentialsBasis E).repr x).support,
      (envelopeDifferentialsBasis E).repr x i • envelopeDifferentialsBasis E i := by
    conv_lhs => rw [← (envelopeDifferentialsBasis E).linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
  have hofx : AdicCompletion.of (pAdicIdeal (A := (E.object : Type u)) p) _ x =
      ∑ i ∈ ((envelopeDifferentialsBasis E).repr x).support,
        (show envelopeCompletion E p hp from AdicCompletion.of (pAdicIdeal (A := (E.object : Type
            u)) p) _
          ((envelopeDifferentialsBasis E).repr x i)) •
          AdicCompletion.of (pAdicIdeal (A := (E.object : Type u)) p) _
            (envelopeDifferentialsBasis E i) := by
    conv_lhs => rw [hx']
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, ← algebraMap_smul (AdicCompletion (pAdicIdeal (A := (E.object : Type u)) p)
      E.object) ((envelopeDifferentialsBasis E).repr x i), AdicCompletion.algebraMap_apply]
    rfl
  have hsum : ∑ i ∈ ((envelopeDifferentialsBasis E).repr x).support,
      (show envelopeCompletion E p hp from AdicCompletion.of (pAdicIdeal (A := (E.object : Type
          u)) p) _
        ((envelopeDifferentialsBasis E).repr x i)) •
        envelopeCompletionFormsDifferential E p hp (envelopeCompletionCoord E p hp i) =
      envelopeCompletionFormsFromCompletion E p hp (AdicCompletion.of (pAdicIdeal (A := (E.object
          : Type u)) p) _ x) := by
    rw [hofx, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, hΨ]
  rw [hsum, show ω - envelopeCompletionFormsFromCompletion E p hp (AdicCompletion.of (pAdicIdeal
      (A := (E.object : Type u)) p) _ x) =
      envelopeCompletionFormsFromCompletion E p hp (envelopeCompletionFormsToCompletion E p hp ω -
          AdicCompletion.of (pAdicIdeal (A := (E.object : Type u)) p) _ x) by
    rw [map_sub, envelopeCompletionFormsFromCompletion_toCompletion]]
  exact PAdicCompletion.map_mem_pow_smul_top p (E.object : Type u) (envelopeCompletion E p hp :
      Type u)
    (Y := envelopeCompletionForms E p hp 1)
    ((envelopeCompletionFormsFromCompletion E p hp).toAddMonoidHom : _ →+ envelopeCompletionForms
        E p hp 1) n hz

/-- **Topological freeness of `Ω̂¹_D`**: modulo `pⁿ`, every one-form is the finite combination of
the `d x_i` with its own coordinates as coefficients, its other coordinates lying in `pⁿ D`. -/
theorem envelopeCompletionForms_approx (ω : envelopeCompletionForms E p hp 1) (n : ℕ) :
    ∃ T : Finset ι, (∀ i ∉ T, envelopeCompletionCoordFun E p hp i ω ∈
        pAdicIdeal (A := (envelopeCompletion E p hp : Type u)) p ^ n) ∧
      ω - ∑ i ∈ T, envelopeCompletionCoordFun E p hp i ω •
          envelopeCompletionFormsDifferential E p hp (envelopeCompletionCoord E p hp i) ∈
        pPowSmul p (envelopeCompletion E p hp : Type u) (envelopeCompletionForms E p hp 1) n :=
  approx_of_dense p (isCoordinateDual_envelopeCompletionCoordFun E p hp)
    (envelopeCompletionForms_dense E p hp) ω n

/-! ### The two-form functionals -/

/-- **The `a`-th coordinate of a divided power one-form of `D`**: its image in `Ω̂¹_D` read by
the coordinate functional `c_a`. -/
def envelopeCompletionOneFormFun (a : ι) :
    Module.Dual (envelopeCompletion E p hp : Type u)
      (dividedPowerDifferentials (A := (A : Type u)) (envelopeCompletion E p hp).dividedPowers) :=
  envelopeCompletionCoordFun E p hp a ∘ₗ
    AdicCompletion.of (pAdicIdeal (A := (envelopeCompletion E p hp : Type u)) p) _ ∘ₗ
      (exteriorPower.oneEquiv _ _).symm.toLinearMap

/-- The `a`-th coordinate of `d x_k` is `δ_{ka}`. -/
theorem envelopeCompletionOneFormFun_differential [DecidableEq ι] (a k : ι) :
    envelopeCompletionOneFormFun E p hp a
      (dividedPowerDifferential (A := (A : Type u)) (envelopeCompletion E p hp).dividedPowers
        (envelopeCompletionCoord E p hp k)) = if k = a then 1 else 0 := by
  have hd : AdicCompletion.of (pAdicIdeal (A := (envelopeCompletion E p hp : Type u)) p) _
      ((exteriorPower.oneEquiv _ _).symm (dividedPowerDifferential (A := (A : Type u))
        (envelopeCompletion E p hp).dividedPowers (envelopeCompletionCoord E p hp k))) =
      envelopeCompletionFormsDifferential E p hp (envelopeCompletionCoord E p hp k) := by
    simp only [envelopeCompletionFormsDifferential, completedDividedPowerDifferentialOnRing_eq,
      dividedPowerOneForm_apply]
  simp only [envelopeCompletionOneFormFun, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, hd]
  split_ifs with hka
  · subst hka; exact (isCoordinateDual_envelopeCompletionCoordFun E p hp).self k
  · exact (isCoordinateDual_envelopeCompletionCoordFun E p hp).of_ne hka

/-- **The functional `φ_{ac} : Ω̂²_D → D`** dual to `d x_a ∧ d x_c`: the pairing of `⋀² Ω` with
the wedge of the coordinates `a` and `c`, extended to the `p`-adic completion. -/
def envelopeCompletionTwoFormFun (a c : ι) :
    envelopeCompletionForms E p hp (1 + 1) →ₗ[(envelopeCompletion E p hp : Type u)]
      (envelopeCompletion E p hp : Type u) :=
  (AdicCompletion.ofLinearEquiv (pAdicIdeal (A := (envelopeCompletion E p hp : Type u)) p)
      (envelopeCompletion E p hp : Type u)).symm.toLinearMap ∘ₗ
    (AdicCompletion.map (pAdicIdeal (A := (envelopeCompletion E p hp : Type u)) p)
      (exteriorPower.pairingDual (envelopeCompletion E p hp : Type u) _ 2
        (exteriorPower.ιMulti _ 2 ![envelopeCompletionOneFormFun E p hp a,
          envelopeCompletionOneFormFun E p hp c]))).restrictScalars _

/-- **The functional `φ_{ac}` on `d x_j ∧ d x_k`** is `δ_{ka} δ_{jc} - δ_{kc} δ_{ja}`. -/
theorem envelopeCompletionTwoFormFun_wedge [DecidableEq ι] (a c j k : ι) :
    envelopeCompletionTwoFormFun E p hp a c
      (envelopeCompletionFormsWedge E p hp 1
        (envelopeCompletionFormsDifferential E p hp (envelopeCompletionCoord E p hp j))
        (envelopeCompletionFormsDifferential E p hp (envelopeCompletionCoord E p hp k))) =
      (if k = a then 1 else 0) * (if j = c then 1 else 0) -
        (if k = c then 1 else 0) * (if j = a then 1 else 0) := by
  simp only [envelopeCompletionFormsDifferential,
    completedDividedPowerDifferentialOnRing_eq, envelopeCompletionFormsWedge,
    completedDividedPowerWedgeOnRing_apply, completedDividedPowerWedge_of_of,
    dividedPowerWedge_apply, dividedPowerOneForm_apply, exteriorPower.oneEquiv_symm_apply,
    exteriorPower.oneEquiv_ιMulti, leftWedge_ιMulti]
  simp only [envelopeCompletionTwoFormFun, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.coe_restrictScalars, AdicCompletion.map_of, LinearEquiv.coe_coe,
    AdicCompletion.ofLinearEquiv_symm_of, exteriorPower.pairingDual_ιMulti_ιMulti,
    Matrix.det_fin_two, Matrix.of_apply, Fin.cons_zero, Fin.cons_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, envelopeCompletionOneFormFun_differential]

/-! ### The coordinate derivations and Taylor's formula -/

/-- **The coordinate derivation `∂_i : D → D`**, `∂_i(x) = c_i(d x)`. -/
def envelopeCompletionCoordDelta (i : ι) :
    envelopeCompletion E p hp →+ envelopeCompletion E p hp :=
  (envelopeCompletionCoordFun E p hp i).toAddMonoidHom.comp
    (AddMonoidHom.mk' (envelopeCompletionFormsDifferential E p hp)
      (envelopeCompletionFormsDifferential_add E p hp))

/-- `∂_i(x)` is the `i`-th coordinate of `d x`. -/
theorem envelopeCompletionCoordDelta_apply (i : ι) (x : envelopeCompletion E p hp) :
    envelopeCompletionCoordDelta E p hp i x =
      envelopeCompletionCoordFun E p hp i (envelopeCompletionFormsDifferential E p hp x) :=
  rfl

/-- **`∂_i` extends the first-order Taylor operator `δ_i` of `E`**: by the derivation formula
`Crystalline.envelopeTaylor_derivation_finset`, `d a = ∑_k δ_k(a) d x_k` over a finite set
outside which `δ_k(a) = 0`, and the `c_i` are dual to the `d x_k`. -/
theorem envelopeCompletionCoordDelta_inclusion (i : ι) (a : E.object) :
    envelopeCompletionCoordDelta E p hp i (envelopeCompletionInclusion E p hp a) =
      envelopeCompletionInclusion E p hp (envelopeDelta E i a) := by
  classical
  obtain ⟨T, hT, hd⟩ := envelopeTaylor_derivation_finset E (envelopeCompletion E p hp)
    (envelopeCompletionInclusion E p hp) (envelopeCompletionForms E p hp 1)
    (envelopeCompletionFormsDerivation E p hp) a
  have hc := isCoordinateDual_envelopeCompletionCoordFun E p hp
  rw [envelopeCompletionCoordDelta_apply]
  change envelopeCompletionCoordFun E p hp i
    ((envelopeCompletionFormsDerivation E p hp) (envelopeCompletionInclusion E p hp a)) = _
  rw [hd, map_sum]
  have hterm : ∀ k ∈ T, envelopeCompletionCoordFun E p hp i
      (envelopeCompletionInclusion E p hp (envelopeDelta E k a) •
        (envelopeCompletionFormsDerivation E p hp)
          (envelopeCompletionInclusion E p hp (envelopeCoord E k))) =
      if k = i then envelopeCompletionInclusion E p hp (envelopeDelta E i a) else 0 := by
    intro k _
    rw [map_smul, smul_eq_mul]
    change _ * envelopeCompletionCoordFun E p hp i
      (envelopeCompletionFormsDifferential E p hp (envelopeCompletionCoord E p hp k)) = _
    split_ifs with hki
    · subst hki; rw [hc.self, mul_one]
    · rw [hc.of_ne hki, mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  split_ifs with hiT
  · rfl
  · rw [hT i hiT, map_zero]

/-- **The `∂_i` commute**: they extend the commuting `δ_i` of the dense subring `E`. -/
theorem envelopeCompletionCoordDelta_comm (i j : ι) :
    ⇑(envelopeCompletionCoordDelta E p hp i) ∘ ⇑(envelopeCompletionCoordDelta E p hp j) =
      ⇑(envelopeCompletionCoordDelta E p hp j) ∘ ⇑(envelopeCompletionCoordDelta E p hp i) := by
  have h := envelopeCompletion_addMonoidHom_ext E p hp
    ((envelopeCompletionCoordDelta E p hp i).comp (envelopeCompletionCoordDelta E p hp j))
    ((envelopeCompletionCoordDelta E p hp j).comp (envelopeCompletionCoordDelta E p hp i))
    fun a => by
      simp only [AddMonoidHom.comp_apply, envelopeCompletionCoordDelta_inclusion]
      exact congrArg (envelopeCompletionInclusion E p hp)
        (congrFun (envelopeDelta_comm E i j) a)
  exact congrArg DFunLike.coe h

/-- **The composite coordinate derivations `∂_K = ∏_i ∂_i^{k_i}`** of `D`. -/
def envelopeCompletionCoordDeltaPow :
    (ι →₀ ℕ) → envelopeCompletion E p hp → envelopeCompletion E p hp :=
  (exists_isThetaMonomialFamily (fun i => ⇑(envelopeCompletionCoordDelta E p hp i))
    (envelopeCompletionCoordDelta_comm E p hp)).choose

/-- The `∂_K` are the composites of the `∂_i`. -/
theorem isThetaMonomialFamily_envelopeCompletionCoordDeltaPow :
    IsThetaMonomialFamily (envelopeCompletion E p hp : Type u)
      (fun i => ⇑(envelopeCompletionCoordDelta E p hp i))
      (envelopeCompletionCoordDeltaPow E p hp) :=
  (exists_isThetaMonomialFamily (fun i => ⇑(envelopeCompletionCoordDelta E p hp i))
    (envelopeCompletionCoordDelta_comm E p hp)).choose_spec

/-- The `∂_K` are additive. -/
theorem envelopeCompletionCoordDeltaPow_add (K : ι →₀ ℕ) (x y : envelopeCompletion E p hp) :
    envelopeCompletionCoordDeltaPow E p hp K (x + y) =
      envelopeCompletionCoordDeltaPow E p hp K x +
        envelopeCompletionCoordDeltaPow E p hp K y := by
  classical
  have hfam := isThetaMonomialFamily_envelopeCompletionCoordDeltaPow E p hp
  induction K using finsupp_induction_single with
  | h0 => rw [hfam.1]; rfl
  | hstep K i ih =>
    rw [hfam.2 i K]
    simp only [Function.comp_apply]
    rw [ih, map_add]

/-- `∂_K` as an additive map. -/
def envelopeCompletionCoordDeltaPowHom (K : ι →₀ ℕ) :
    envelopeCompletion E p hp →+ envelopeCompletion E p hp :=
  AddMonoidHom.mk' (envelopeCompletionCoordDeltaPow E p hp K)
    (envelopeCompletionCoordDeltaPow_add E p hp K)

/-- **`∂_K` extends the Taylor coefficient `θ_K` of `E`.** -/
theorem envelopeCompletionCoordDeltaPow_inclusion (K : ι →₀ ℕ) (a : E.object) :
    envelopeCompletionCoordDeltaPow E p hp K (envelopeCompletionInclusion E p hp a) =
      envelopeCompletionInclusion E p hp (presentationTaylorCoeff E K a) := by
  classical
  have hfam := isThetaMonomialFamily_envelopeCompletionCoordDeltaPow E p hp
  have hfamE := isThetaMonomialFamily_presentationTaylorCoeff E
  induction K using finsupp_induction_single generalizing a with
  | h0 => rw [hfam.1, presentationTaylorCoeff_zero]; rfl
  | hstep K i ih =>
    rw [hfam.2 i K]
    simp only [Function.comp_apply]
    rw [ih, envelopeCompletionCoordDelta_inclusion E p hp]
    exact congrArg (envelopeCompletionInclusion E p hp) (congrFun (hfamE.2 i K) a).symm

/-- **Taylor's formula at the levels**, for the coordinate derivations `∂_K` of any family of
variables.  Let `ρ : D → D` be a divided power endomorphism over `A` compatible with the
augmentation and put `ξ_i = x_i - ρ(x_i)`.  Then for every `a ∈ D` and every `n` there is a finite
set `S` of multi-indices with `∂_K a ∈ p^n D` for `K ∉ S`,
`a ≡ ∑_{K ∈ S} ρ(∂_K a) ξ^{[K]}` and `ρ(a) ≡ ∑_{K ∈ S} ∂_K(a) (-ξ)^{[K]}` modulo `p^n D`. -/
theorem envelopeCompletion_coordDual_taylor_levels
    (ρ : DPMorphism (envelopeCompletion E p hp).dividedPowers
      (envelopeCompletion E p hp).dividedPowers)
    (hρA : ρ.comp (envelopeCompletionStructureMap E p hp) = envelopeCompletionStructureMap E p hp)
    (hρ : ∀ x, ρ x - x ∈ (envelopeCompletion E p hp).ideal) (a : envelopeCompletion E p hp)
    (n : ℕ) :
    ∃ S : Finset (ι →₀ ℕ),
      (∀ K ∉ S, envelopeCompletionCoordDeltaPow E p hp K a ∈
        pAdicIdeal (A := (envelopeCompletion E p hp : Type u)) p ^ n) ∧
      a - ∑ K ∈ S, ρ (envelopeCompletionCoordDeltaPow E p hp K a) *
          taylorMonomial (envelopeCompletion E p hp)
            (fun i => envelopeCompletionCoord E p hp i - ρ (envelopeCompletionCoord E p hp i)) K ∈
        pAdicIdeal (A := (envelopeCompletion E p hp : Type u)) p ^ n ∧
      ρ a - ∑ K ∈ S, envelopeCompletionCoordDeltaPow E p hp K a *
          taylorMonomial (envelopeCompletion E p hp)
            (-fun i => envelopeCompletionCoord E p hp i - ρ (envelopeCompletionCoord E p hp i)) K ∈
        pAdicIdeal (A := (envelopeCompletion E p hp : Type u)) p ^ n := by
  classical
  set ιD := envelopeCompletionInclusion E p hp
  set δK := envelopeCompletionCoordDeltaPow E p hp
  set 𝔭 := pAdicIdeal (A := DividedPowerRing.carrier (envelopeCompletion E p hp)) p
  obtain ⟨a₀, ha₀⟩ := exists_sub_envelopeCompletionInclusion_mem E p hp a n
  set z := a - ιD a₀ with hz
  have hδ : ∀ K, δK K a = ιD (presentationTaylorCoeff E K a₀) + δK K z := fun K => by
    rw [← envelopeCompletionCoordDeltaPow_inclusion E p hp K a₀,
      ← envelopeCompletionCoordDeltaPow_add, hz, add_sub_cancel]
  have hδz : ∀ K, δK K z ∈ 𝔭 ^ n := fun K =>
    map_mem_pAdicIdeal_pow p n (envelopeCompletionCoordDeltaPowHom E p hp K) ha₀
  have hρP : ∀ x ∈ 𝔭 ^ n, ρ x ∈ 𝔭 ^ n := fun x hx =>
    map_mem_pAdicIdeal_pow p n ρ.toRingHom.toAddMonoidHom hx
  have hFG : ιD.comp E.structureMap = (ρ.comp ιD).comp E.structureMap :=
    DFunLike.ext _ _ fun r =>
      (congrArg (fun f : DPMorphism A.dividedPowers (envelopeCompletion E p hp).dividedPowers =>
        f r) hρA).symm
  set ξ : ι → envelopeCompletion E p hp :=
    fun i => envelopeCompletionCoord E p hp i - ρ (envelopeCompletionCoord E p hp i) with hξ
  have hneg : -ξ = fun i =>
      ρ (envelopeCompletionCoord E p hp i) - envelopeCompletionCoord E p hp i :=
    funext fun i => neg_sub _ _
  set S := envelopeTaylorSupport E a₀ with hS
  have key : ∀ (ψ φ : envelopeCompletion E p hp →+ envelopeCompletion E p hp)
      (mon : (ι →₀ ℕ) → envelopeCompletion E p hp), (∀ x ∈ 𝔭 ^ n, φ x ∈ 𝔭 ^ n) → ψ z ∈ 𝔭 ^ n →
      ψ (ιD a₀) = ∑ K ∈ S, φ (ιD (presentationTaylorCoeff E K a₀)) * mon K →
      ψ a - ∑ K ∈ S, φ (δK K a) * mon K ∈ 𝔭 ^ n := fun ψ φ mon hφ hψ hT => by
    have hψa : ψ a = ψ (ιD a₀) + ψ z := by rw [← map_add, hz, add_sub_cancel]
    simp only [hδ, map_add, add_mul, Finset.sum_add_distrib, ← hT]
    rw [hψa, add_sub_add_left_eq_sub]
    exact Ideal.sub_mem _ hψ (Ideal.sum_mem _ fun K _ => Ideal.mul_mem_right _ _ (hφ _ (hδz K)))
  refine ⟨S, fun K hK => ?_, ?_, ?_⟩
  · rw [hδ, presentationTaylorCoeff_eq_zero_of_notMem E hK, map_zero, zero_add]
    exact hδz K
  · exact key (AddMonoidHom.id _) ρ.toRingHom.toAddMonoidHom _ hρP ha₀
      (envelopeTaylor_formula E (envelopeCompletion E p hp) ιD (ρ.comp ιD) hFG
        (fun i => by
          change envelopeCompletionCoord E p hp i - ρ (envelopeCompletionCoord E p hp i) ∈ _
          rw [← neg_sub]
          exact Submodule.neg_mem _ (hρ _)) a₀)
  · refine key ρ.toRingHom.toAddMonoidHom (AddMonoidHom.id _) _ (fun _ h => h) (hρP _ ha₀) ?_
    rw [hneg]
    exact envelopeTaylor_formula E (envelopeCompletion E p hp) (ρ.comp ιD) ιD hFG.symm
      (fun i => hρ _) a₀

/-! ### The data -/

/-- **The topological coordinates of the completed envelope `D`** of a polynomial presentation
with any family of variables: its completed forms `Ω̂^*_D` with the universal differential, the
coordinates `x_i`, the coordinate functionals `c_i` dual to the `d x_i` and topologically
spanning `Ω̂¹_D`, the functionals `φ_{ac}` on the two-forms, and the composite coordinate
derivations `∂_K`. -/
def envelopeCompletionCoordinateDualData [DecidableEq ι] :
    CompletedCoordinateDualData p (envelopeCompletion E p hp) where
  Om := envelopeCompletionForms E p hp
  wedge := envelopeCompletionFormsWedge E p hp
  deRham := completedDividedPowerDeRham p (A : Type u) (envelopeCompletion E p hp).dividedPowers
  diff := envelopeCompletionFormsDifferential E p hp
  diff_add := completedDividedPowerDifferentialOnRing_add p (A : Type u) _
  diff_mul := completedDividedPowerDifferentialOnRing_mul p (A : Type u) _
  diff_dpow _ hn _ hx := envelopeCompletionFormsDifferential_dpow E p hp hn hx
  isGradedLeibniz := isGradedLeibniz_envelopeCompletionForms E p hp
  wedge_anti := completedDividedPowerWedgeOnRing_one_add_swap p (A : Type u) _
  wedge_self := envelopeCompletionFormsWedge_self E p hp
  deRham_diff := completedDividedPowerDeRham_one_differentialOnRing p (A : Type u) _
  ι := ι
  coord := envelopeCompletionCoord E p hp
  coordFun := envelopeCompletionCoordFun E p hp
  isCoordinateDual := isCoordinateDual_envelopeCompletionCoordFun E p hp
  approx := envelopeCompletionForms_approx E p hp
  twoFormFun := envelopeCompletionTwoFormFun E p hp
  twoFormFun_wedge := envelopeCompletionTwoFormFun_wedge E p hp
  deltaPow := envelopeCompletionCoordDeltaPow E p hp
  isThetaMonomialFamily := isThetaMonomialFamily_envelopeCompletionCoordDeltaPow E p hp

section Retract

variable [DecidableEq ι] (D' : DividedPowerRing.{u}) [Algebra (A : Type u) (D' : Type u)]
  (a : DPMorphism (envelopeCompletion E p hp).dividedPowers D'.dividedPowers)
  (b : DPMorphism D'.dividedPowers (envelopeCompletion E p hp).dividedPowers)
  (ha : ∀ c : (A : Type u), a (algebraMap (A : Type u) (envelopeCompletion E p hp) c) =
    algebraMap (A : Type u) (D' : Type u) c)
  (hb : ∀ c : (A : Type u), b (algebraMap (A : Type u) (D' : Type u) c) =
    algebraMap (A : Type u) (envelopeCompletion E p hp) c)
  (hab : ∀ x : (D' : Type u), a (b x) = x)
  (hρ : ∀ y : envelopeCompletion E p hp, b (a y) - y ∈ (envelopeCompletion E p hp).ideal)

/-- **The retract data** of a retract `a ∘ b = id_{D'}` of divided power `A`-algebras, with the
completed envelope `D` of a polynomial presentation in any family of variables and an arbitrary
divided power ring `D'`: the comparisons of completed forms along `a` and `b`, and Taylor's
formula for `ρ = b ∘ a`. -/
def envelopeCompletionDualRetractData :
    CoordinateDualRetractData p (envelopeCompletion E p hp)
      (envelopeCompletionCoordinateDualData E p hp) :=
  let : Algebra (envelopeCompletion E p hp : Type u) (D' : Type u) := a.toRingHom.toAlgebra
  let : Algebra (D' : Type u) (envelopeCompletion E p hp : Type u) := b.toRingHom.toAlgebra
  have : IsScalarTower (D' : Type u) (envelopeCompletion E p hp : Type u) (D' : Type u) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (hab x).symm
  { ring := (D' : Type u)
    Om := completedDividedPowerForms p (A : Type u) D'.dividedPowers
    wedge := completedDividedPowerWedgeOnRing p (A : Type u) D'.dividedPowers
    deRham := completedDividedPowerDeRham p (A : Type u) D'.dividedPowers
    diff := completedDividedPowerDifferentialOnRing p (A : Type u) D'.dividedPowers
    diff_add := completedDividedPowerDifferentialOnRing_add p (A : Type u) _
    diff_mul := completedDividedPowerDifferentialOnRing_mul p (A : Type u) _
    isGradedLeibniz := isGradedLeibniz_completedDividedPowerOnRing p (A : Type u) _
    wedge_anti := completedDividedPowerWedgeOnRing_one_add_swap p (A : Type u) _
    deRham_diff := completedDividedPowerDeRham_one_differentialOnRing p (A : Type u) _
    psiA := completedMapDifferentialForms p (A : Type u) _ D'.dividedPowers
      (dpMorphismAlgHom a ha) a.isDPMorphism
    psiB := completedMapDifferentialForms p (A : Type u) D'.dividedPowers _
      (dpMorphismAlgHom b hb) b.isDPMorphism
    psiA_diff := completedMapDifferentialForms_differentialOnRing p (A : Type u) _ _ _ _
    psiB_diff := completedMapDifferentialForms_differentialOnRing p (A : Type u) _ _ _ _
    psiA_wedge := completedMapDifferentialForms_wedge p (A : Type u) _ _ _ _
    psiB_wedge := completedMapDifferentialForms_wedge p (A : Type u) _ _ _ _
    psiA_deRham := completedMapDifferentialForms_deRham p (A : Type u) _ _ _ _
    psiB_deRham := completedMapDifferentialForms_deRham p (A : Type u) _ _ _ _
    psiA_psiB := fun ω ↦ by
      have hc := completedMapDifferentialForms_comp p (A : Type u) D'.dividedPowers
        (envelopeCompletion E p hp).dividedPowers (dpMorphismAlgHom b hb) b.isDPMorphism
        D'.dividedPowers (dpMorphismAlgHom a ha) a.isDPMorphism (a.comp b).isDPMorphism 1 ω
      refine hc.symm.trans ?_
      exact (completedMapDifferentialForms_congr p (A : Type u) D'.dividedPowers D'.dividedPowers
        (g := AlgHom.id (A : Type u) (D' : Type u)) (AlgHom.ext hab) _
        (DPMorphism.id D'.dividedPowers).isDPMorphism 1 ω).trans
        (completedMapDifferentialForms_id p (A : Type u) D'.dividedPowers 1 _ ω)
    rho_sub_mem := hρ
    taylor := fun x n ↦ by
      obtain ⟨S, h1, h2, -⟩ := envelopeCompletion_coordDual_taylor_levels E p hp (b.comp a)
        (by ext c; exact (congrArg b (ha c)).trans (hb c)) hρ x n
      exact ⟨S, h1, h2⟩
    taylor' := fun x n ↦ by
      obtain ⟨S, h1, -, h3⟩ := envelopeCompletion_coordDual_taylor_levels E p hp (b.comp a)
        (by ext c; exact (congrArg b (ha c)).trans (hb c)) hρ x n
      exact ⟨S, h1, h3⟩ }

end Retract

end Envelope

end Crystalline

end
