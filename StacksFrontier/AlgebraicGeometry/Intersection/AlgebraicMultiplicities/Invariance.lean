module

public import StacksFrontier.AlgebraicGeometry.Intersection.AlgebraicMultiplicities.GeneralizedHilbertFunction
public import StacksFrontier.AlgebraicGeometry.Intersection.AlgebraicMultiplicities.GeneralizedMultiplicity

/-!
# Invariance of the generalized invariants under the annihilator

Adding the annihilator of a module to an ideal does not change the generalized Hilbert
function of that module, because the relevant powers act by the same submodules. Passing
further to the quotient ring by the annihilator does not change it either, and the same holds
for the generalized Hilbert–Samuel multiplicities. Together these provide the transport from
the usual ideal-of-definition results over `R / Ann(M)` to the generalized setting.

## Main results

* `Ideal.generalizedHilbertFunction_add_annihilator` identifies the generalized Hilbert
  functions for `I` and `I + Ann(M)` at every natural number.
* `Ideal.generalizedHilbertFunction_add_annihilator_eq_map_quotientAnnihilator` gives the
  equality of Hilbert functions over `R` and over `R / Ann(M)`.
* `Ideal.generalizedHilbertSamuelMultiplicity_add_annihilator_eq_map_quotientAnnihilator`
  gives the corresponding equality of generalized multiplicities.

## Implementation notes

The source situates these statements over a Noetherian local ring with finite-length
quotient, but they need none of those hypotheses. The assertion in the source that whole
sections have analogues is a description of this transport, rather than a separate
mathematical proposition.

## References

* [Stacks Project, Tag 0B00](https://stacks.math.columbia.edu/tag/0B00)
-/

@[expose] public section

open Filter Polynomial

namespace Ideal

/-- Adding the annihilator of `M` to `I` does not change the length of `M / I^n M`. -/
@[stacks 0B00 "invariance_under_adding_annihilator"]
theorem generalizedHilbertFunction_add_annihilator
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (n : ℕ) :
    Ideal.generalizedHilbertFunction (I + Module.annihilator R M) M n =
      Ideal.generalizedHilbertFunction I M n := by
  unfold Ideal.generalizedHilbertFunction
  rw [add_annihilator_pow_smul_top]

/-- The generalized Hilbert function is unchanged by passing from `I + Ann(M)` over `R` to the
image of `I` over `R / Ann(M)`. -/
@[stacks 0B00 "invariance_under_quotient_by_annihilator"]
theorem generalizedHilbertFunction_add_annihilator_eq_map_quotientAnnihilator
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (n : ℕ) :
    letI : Module (R ⧸ Module.annihilator R M) M := Module.quotientAnnihilator
    Ideal.generalizedHilbertFunction (I + Module.annihilator R M) M n =
      Ideal.generalizedHilbertFunction
        (Ideal.map (Ideal.Quotient.mk (Module.annihilator R M)) I) M n := by
  classical
  let A := Module.annihilator R M
  let S := R ⧸ A
  let : Module S M := Module.quotientAnnihilator
  change Module.length R (M ⧸ ((I + A) ^ n • (⊤ : Submodule R M))) =
    Module.length S (M ⧸ ((Ideal.map (Ideal.Quotient.mk A) I) ^ n • (⊤ : Submodule S M)))
  let q : Submodule S M := (Ideal.map (Ideal.Quotient.mk A) I) ^ n • (⊤ : Submodule S M)
  rw [add_annihilator_pow_smul_top, ← map_quotientAnnihilator_pow_smul_top I n]
  exact ((Submodule.Quotient.restrictScalarsEquiv R q).length_eq).symm.trans
    (Module.length_eq_of_surjective (S := R) (R := S) (M := M ⧸ q)
      Ideal.Quotient.mk_surjective)

/-- Generalized Hilbert–Samuel multiplicities are unchanged by passing to the quotient ring by
the annihilator of the module. -/
@[stacks 0B00 "invariance_under_quotient_by_annihilator"]
theorem generalizedHilbertSamuelMultiplicity_add_annihilator_eq_map_quotientAnnihilator
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (d : ℕ) :
    letI : Module (R ⧸ Module.annihilator R M) M := Module.quotientAnnihilator
    Ideal.generalizedHilbertSamuelMultiplicity (I + Module.annihilator R M) M d =
      Ideal.generalizedHilbertSamuelMultiplicity
        (Ideal.map (Ideal.Quotient.mk (Module.annihilator R M)) I) M d := by
  classical
  let A := Module.annihilator R M
  let S := R ⧸ A
  let : Module (R ⧸ Module.annihilator R M) M := Module.quotientAnnihilator
  let F : (ℕ → ℕ∞) → ℚ := fun L => (d.factorial : ℚ) *
    (if h : ∃ P : ℚ[X], ∀ᶠ n : ℕ in atTop, ∃ p : ℕ,
      L n = p ∧ P.eval (n : ℚ) = p then h.choose else 0).coeff d
  change F (fun n => Module.length R (M ⧸ ((I + A) ^ n • (⊤ : Submodule R M)))) =
    F (fun n => Module.length S (M ⧸ ((Ideal.map (Ideal.Quotient.mk A) I) ^ n •
      (⊤ : Submodule S M))))
  congr 1
  funext n
  exact generalizedHilbertFunction_add_annihilator_eq_map_quotientAnnihilator I n

end Ideal
