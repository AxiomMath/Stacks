module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDeRhamDegreeZero

/-!
# The unit zero-form, and the universal differential as a de Rham differential

The completed divided power forms `Ω^*_D` of [Stacks, Tag 07HZ] carry two maps out of the ring:
the universal differential `Crystalline.completedFormsDifferential`, which
`Crystalline.CompletedConnection` takes as its `d : D → Ω¹`, and the de Rham differential
`Crystalline.completedDividedPowerDeRham` in exterior degree zero, which is the first
differential of the complex.  Nothing so far relates them, and the relation is what every
identity of the universal differential beyond additivity has to be proved through: the universal
differential is built from `Crystalline.dividedPowerOneForm` and the forms carry no product rule
of their own.

This module supplies the bridge.  The **unit zero-form** `1 ∈ Ω^0_D` — the preimage of `1 ∈ D`
under the degree-zero identification of
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedDeRhamDegreeZero.lean` — is closed and is a
unit for the wedge product, and those two facts turn the carried Leibniz rule
`Crystalline.isGradedLeibniz_completedDividedPower` into

`d (f · 1) = f · d 1 + 1 ∧ d f = d f`,

that is: **in exterior degree zero the de Rham differential, read through the unit zero-form, is
the universal differential**.  Everything else follows by instantiating the graded identities at
that form: the product rule `d (f g) = f · d g + g · d f`, `d 1 = 0`, and `d ∘ d = 0` on exact
one-forms, which is the degree-zero case of
`Crystalline.isGradedExterior_completedDividedPower`.

These are exactly the three hypotheses `hmul`, `hone`, `hclosed` of
`Crystalline.CompletedDeRham.isSquareZero_unitConnection`, so for the genuine completed divided
power forms the de Rham complex of the structure module is a complex unconditionally.

## Main definitions

* `Crystalline.unitZeroForm` and `Crystalline.completedUnitZeroForm` — **the unit zero-form**
  `1 ∈ Ω^0_{B/A,δ}` and its image in the completion.

## Main results

* `Crystalline.dividedPowerWedge_unitZeroForm` and
  `Crystalline.completedDividedPowerWedge_completedUnitZeroForm` — the unit zero-form is a left
  unit for the wedge product.
* `Crystalline.dividedPowerDeRham_unitZeroForm` and
  `Crystalline.completedDividedPowerDeRham_completedUnitZeroForm` — the unit zero-form is closed.
* `Crystalline.completedDividedPowerDeRham_smul_completedUnitZeroForm` — **in exterior degree
  zero the de Rham differential is the universal differential**.
* `Crystalline.completedFormsDifferential_mul` — **the product rule for the universal
  differential of the completion**, and `Crystalline.completedFormsDifferential_one` that it
  kills `1`.
* `Crystalline.deRham_completedFormsDifferential` — **an exact one-form of the completion is
  closed**.
* `Crystalline.mapDifferentialFormsOfDPMorphism_unitZeroForm` and
  `Crystalline.completedMapDifferentialForms_completedUnitZeroForm` — the comparison along a
  divided power morphism carries the unit zero-form to the unit zero-form, which is how the
  universal differential is seen to commute with a divided power morphism.

No `@[stacks …]` attribute is placed: these are structural identities of the forms of
[Stacks, Tag 07HZ] used inside the proof of [Stacks, Proposition 60.21.3, Tag 07LG], not the
statement of a tag.

## References

* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public noncomputable section

open DividedPowers

universe u v

namespace Crystalline

section Uncompleted

variable {A : Type u} [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
variable {J : Ideal B} (hJ : DividedPowers J)

/-! ### The unit zero-form -/

/-- **The unit zero-form `1 ∈ Ω^0_{B/A,δ}`**: the preimage of `1 ∈ B` under the identification
`Ω^0_{B/A,δ} ≅ B` of the degree-zero exterior power with the ring. -/
def unitZeroForm : dividedPowerDifferentialForms (A := A) hJ 0 :=
  (exteriorPower.zeroEquiv B (dividedPowerDifferentials (A := A) hJ)).symm 1

/-- Read inside the exterior algebra the unit zero-form is `1`. -/
theorem coe_unitZeroForm :
    ((unitZeroForm (A := A) hJ : dividedPowerDifferentialForms (A := A) hJ 0) :
      ExteriorAlgebra B (dividedPowerDifferentials (A := A) hJ)) = 1 := by
  rw [unitZeroForm]
  simp [exteriorPower.zeroEquiv_symm_apply, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.ιMulti]

/-- The degree-zero identification carries the unit zero-form to `1`. -/
@[simp] theorem zeroEquiv_unitZeroForm :
    exteriorPower.zeroEquiv B (dividedPowerDifferentials (A := A) hJ)
        (unitZeroForm (A := A) hJ) = 1 :=
  LinearEquiv.apply_symm_apply _ 1

/-- **The unit zero-form is a left unit for the wedge product**: wedging a one-form with it
returns the one-form.  Read inside the exterior algebra this is `1 · ι η = ι η`. -/
theorem dividedPowerWedge_unitZeroForm (eta : dividedPowerDifferentialForms (A := A) hJ 1) :
    dividedPowerWedge hJ 0 (unitZeroForm (A := A) hJ) eta = eta := by
  refine Subtype.ext ?_
  rw [dividedPowerWedge_apply, leftWedge_coe, coe_unitZeroForm, mul_one,
    ← coe_oneEquiv_symm hJ (exteriorPower.oneEquiv B (dividedPowerDifferentials (A := A) hJ) eta),
    LinearEquiv.symm_apply_apply]

/-- **The unit zero-form is closed.**  It is the standard generator `1` of exterior degree zero,
whose de Rham differential is the length-one wedge `d 1`, and `d 1 = 0`. -/
theorem dividedPowerDeRham_unitZeroForm :
    dividedPowerDeRham hJ 0 (unitZeroForm (A := A) hJ) = 0 := by
  have h := dividedPowerDeRham_generator (A := A) hJ 0 fun _ : Fin 1 => (1 : B)
  have hu : (1 : B) • exteriorPower.ιMulti B 0
      (fun j : Fin 0 => dividedPowerDifferential (A := A) hJ ((fun _ : Fin 1 => (1 : B)) j.succ)) =
      unitZeroForm (A := A) hJ := by
    rw [one_smul, unitZeroForm]
    exact (LinearEquiv.eq_symm_apply _).mpr (exteriorPower.zeroEquiv_ιMulti _)
  rw [hu] at h
  rw [h]
  exact (exteriorPower.ιMulti B 1).map_coord_zero (i := 0) (by simp)

/-- **The comparison of forms along a divided power morphism carries the unit zero-form to the
unit zero-form.**  In exterior degree zero the comparison is the ring map, by
`Crystalline.mapDifferentialFormsOfDPMorphism_zero`, and a ring map preserves `1`. -/
theorem mapDifferentialFormsOfDPMorphism_unitZeroForm {C : Type v} [CommRing C] [Algebra A C]
    {K : Ideal C} (epsilon : DividedPowers K) (f : B →ₐ[A] C)
    (hf : DividedPowers.IsDPMorphism hJ epsilon f.toRingHom) :
    mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := hJ) epsilon f hf 0
        (unitZeroForm (A := A) hJ) = unitZeroForm (A := A) epsilon :=
  (exteriorPower.zeroEquiv C (dividedPowerDifferentials (A := A) epsilon)).injective (by
    rw [mapDifferentialFormsOfDPMorphism_zero, zeroEquiv_unitZeroForm, zeroEquiv_unitZeroForm,
      map_one])

end Uncompleted

/-! ### The unit zero-form of the completion -/

section Completed

variable (p : ℕ) (A : Type u) [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
variable {J : Ideal B} (hJ : DividedPowers J)

/-- **The unit zero-form `1 ∈ Ω^0_D` of the completed forms**, the image of
`Crystalline.unitZeroForm`. -/
def completedUnitZeroForm : completedDividedPowerForms p A hJ 0 :=
  AdicCompletion.of (pAdicIdeal (A := B) p) _ (unitZeroForm (A := A) hJ)

/-- The level-`pⁿ` value of the unit zero-form of the completion. -/
theorem completedUnitZeroForm_val (n : ℕ) :
    (completedUnitZeroForm p A hJ).val n =
      Submodule.Quotient.mk (unitZeroForm (A := A) hJ) := rfl

/-- **The unit zero-form of the completion is a left unit for the wedge product of completed
forms.**  Both sides are computed at each level `pⁿ` from the uncompleted wedge, where the
identity is `Crystalline.dividedPowerWedge_unitZeroForm`. -/
theorem completedDividedPowerWedge_completedUnitZeroForm
    (eta : completedDividedPowerForms p A hJ 1) :
    completedDividedPowerWedge p A hJ 0 (completedUnitZeroForm p A hJ) eta = eta := by
  refine AdicCompletion.ext fun n => ?_
  obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective
    (pAdicIdeal (A := B) p ^ n • ⊤ :
      Submodule B (dividedPowerDifferentialForms (A := A) hJ 1)) (eta.val n)
  rw [completedDividedPowerWedge_val p A hJ 0 n _ eta (unitZeroForm (A := A) hJ) w
    (completedUnitZeroForm_val p A hJ n) hw.symm, dividedPowerWedge_unitZeroForm, hw]

/-- **Wedging a one-form with a multiple of the unit zero-form multiplies it by the scalar.**
This is the shape the product rule for the universal differential needs: the degree-zero factor
in the Leibniz rule `d (f · ω) = f · d ω + ω ∧ d f` is `g · 1` and not `1`. -/
theorem completedDividedPowerWedge_smul_completedUnitZeroForm
    (g : completedDividedPowerRing p (B := B)) (eta : completedDividedPowerForms p A hJ 1) :
    completedDividedPowerWedge p A hJ 0 (g • completedUnitZeroForm p A hJ) eta = g • eta := by
  have h : completedDividedPowerWedge p A hJ 0 (g • completedUnitZeroForm p A hJ) eta =
      g • completedDividedPowerWedge p A hJ 0 (completedUnitZeroForm p A hJ) eta := by
    rw [map_smul]
    rfl
  exact h.trans
    (congrArg (fun z => g • z) (completedDividedPowerWedge_completedUnitZeroForm p A hJ eta))

/-- **The unit zero-form of the completion is closed.** -/
@[simp] theorem completedDividedPowerDeRham_completedUnitZeroForm :
    completedDividedPowerDeRham p A hJ 0 (completedUnitZeroForm p A hJ) = 0 := by
  rw [completedUnitZeroForm, completedDividedPowerDeRham_of, dividedPowerDeRham_unitZeroForm,
    map_zero]

/-! ### The universal differential is the degree-zero de Rham differential -/

/-- **In exterior degree zero the de Rham differential of the completed forms is the universal
differential**, read through the unit zero-form: `d (f · 1) = d f`.

This is the carried Leibniz rule `Crystalline.isGradedLeibniz_completedDividedPower` in degree
zero at the unit zero-form, whose two correction terms are killed by
`Crystalline.completedDividedPowerDeRham_completedUnitZeroForm` and
`Crystalline.completedDividedPowerWedge_completedUnitZeroForm`.  It is what every further
identity of the universal differential is proved through: the forms carry no product rule of
their own, so the product rule of `d` is the graded Leibniz rule instantiated here. -/
theorem completedDividedPowerDeRham_smul_completedUnitZeroForm
    (f : completedDividedPowerRing p (B := B)) :
    completedDividedPowerDeRham p A hJ 0 (f • completedUnitZeroForm p A hJ) =
      completedFormsDifferential p A hJ f := by
  rw [isGradedLeibniz_completedDividedPower p A hJ 0 f (completedUnitZeroForm p A hJ),
    completedDividedPowerDeRham_completedUnitZeroForm, smul_zero]
  exact (zero_add _).trans (completedDividedPowerWedge_completedUnitZeroForm p A hJ _)

/-- The universal differential of the completion is additive. -/
theorem completedFormsDifferential_add (x y : completedDividedPowerRing p (B := B)) :
    completedFormsDifferential p A hJ (x + y) =
      completedFormsDifferential p A hJ x + completedFormsDifferential p A hJ y :=
  map_add (PAdicCompletion.mapAddHom p B B (dividedPowerOneForm A hJ)) x y

/-- **The universal differential of the completion kills `1`.** -/
@[simp] theorem completedFormsDifferential_one :
    completedFormsDifferential p A hJ (1 : completedDividedPowerRing p (B := B)) = 0 := by
  rw [← completedDividedPowerDeRham_smul_completedUnitZeroForm, one_smul,
    completedDividedPowerDeRham_completedUnitZeroForm]

/-- **The product rule for the universal differential of the completion**:
`d (f g) = f · d g + g · d f`.

The differential is `Crystalline.PAdicCompletion.mapAddHom` of
`Crystalline.dividedPowerOneForm`, which carries no product rule, so the rule is derived from the
graded Leibniz rule of the forms: `d (f g) = d (f · (g · 1))` is expanded once by
`Crystalline.isGradedLeibniz_completedDividedPower` and the two resulting terms are read back
through `Crystalline.completedDividedPowerDeRham_smul_completedUnitZeroForm`. -/
theorem completedFormsDifferential_mul (f g : completedDividedPowerRing p (B := B)) :
    completedFormsDifferential p A hJ (f * g) =
      f • completedFormsDifferential p A hJ g + g • completedFormsDifferential p A hJ f := by
  rw [← completedDividedPowerDeRham_smul_completedUnitZeroForm, mul_smul,
    isGradedLeibniz_completedDividedPower p A hJ 0 f (g • completedUnitZeroForm p A hJ),
    completedDividedPowerDeRham_smul_completedUnitZeroForm,
    completedDividedPowerWedge_smul_completedUnitZeroForm]

/-- **An exact one-form of the completion is closed**, that is `d ∘ d = 0` on the ring.  This is
the degree-zero case of `Crystalline.isGradedExterior_completedDividedPower`, reached through
`Crystalline.completedDividedPowerDeRham_smul_completedUnitZeroForm`. -/
@[simp] theorem deRham_completedFormsDifferential (x : completedDividedPowerRing p (B := B)) :
    completedDividedPowerDeRham p A hJ 1 (completedFormsDifferential p A hJ x) = 0 := by
  rw [← completedDividedPowerDeRham_smul_completedUnitZeroForm]
  exact (isGradedExterior_completedDividedPower p A hJ).deRham_deRham 0
    (x • completedUnitZeroForm p A hJ)

/-- **The comparison of completed forms carries the unit zero-form to the unit zero-form.** -/
@[simp] theorem completedMapDifferentialForms_completedUnitZeroForm {C : Type v} [CommRing C]
    [Algebra A C] {K : Ideal C} (epsilon : DividedPowers K) (f : B →ₐ[A] C)
    (hf : DividedPowers.IsDPMorphism hJ epsilon f.toRingHom) :
    completedMapDifferentialForms p A hJ epsilon f hf 0 (completedUnitZeroForm p A hJ) =
      completedUnitZeroForm p A epsilon := by
  rw [completedUnitZeroForm, completedMapDifferentialForms_of,
    mapDifferentialFormsOfDPMorphism_unitZeroForm]
  rfl

end Completed

end Crystalline

end
