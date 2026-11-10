module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EliminateRamificationSolution
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppUniverseAssembly

/-!
# The universe layer of Epp's theorem

`Stacks.EliminateRamification.EppTheorem` has four independent universes `uA`, `uB`, `uK`, `uL`.
This file derives `EppTheorem.{uA, uB, uK, uL}` from `EppTheorem.{u, u, u, u}` at
`u = max uA uB uK uL`: the data are lifted to `Type u` along `ULift.ringEquiv`, the solution field
returned by the monomorphic theorem is descended to `Type uK`, and the weak-solution property is
transported to the canonical base-change package built downstairs.

## Main definitions

* `Stacks.EppTheorem.uliftTensorRingEquiv`: the identification of `ULift L ⊗[ULift K] K₁'` with
  `L ⊗[K] K₁` along a descent `ULift K₁ ≃ₐ[ULift K] K₁'`.
* `Stacks.EppTheorem.uliftCompositumRingEquiv`: the induced identification of the reduced
  composita.

## Main results

* `Stacks.EppTheorem.exists_field_descent_ulift`: a finite extension of `ULift K` is isomorphic to
  the lift of a finite extension of `K` in `K`'s own universe.
* `Stacks.EppTheorem.eppTheorem_of_monomorphic`: Epp's theorem at four independent universes
  follows from Epp's theorem at one.

## Implementation notes

`exists_field_descent_ulift` concludes with a bare `RingEquiv` and a compatibility condition in the
given `Algebra (ULift K) E`, never an `Algebra K E`: with `Algebra K E` in scope, `ULift.module`
and `ULift.algebra'` supply a second `Module (ULift K) E`, definitionally but not syntactically
equal to the given one, and `Module.Finite (ULift K) E` then fails to resolve.

## References

* [The Stacks Project, Tag 09EM](https://stacks.math.columbia.edu/tag/09EM)
* [The Stacks Project, Tag 09F9](https://stacks.math.columbia.edu/tag/09F9)
* [The Stacks Project, Tag 09II](https://stacks.math.columbia.edu/tag/09II)
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Stacks.EppTheorem

open IsDiscreteValuationRing

-- Not a global instance in Mathlib: it is a non-reducible diamond when `A = ULift R`.
attribute [local instance] ULift.algebra'

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe uA uB uK uL uK₁ v

/-! ### The descent, in a form that introduces no instance diamond -/

/-- **A finite extension of `ULift K` has a copy in `K`'s own universe**: for a finite extension
`E` of `ULift K` there are a finite extension `K₁` of `K` in `Type uK` and a ring isomorphism
`ULift K₁ ≃+* E` compatible with the two maps from `K`. -/
theorem exists_field_descent_ulift (K : Type uK) [Field K] (E : Type v) [Field E]
    [algUKE : Algebra (ULift.{v} K) E] [finUKE : Module.Finite (ULift.{v} K) E] :
    ∃ (K₁ : Type uK) (_ : Field K₁) (_ : Algebra K K₁) (_ : Module.Finite K K₁),
      ∃ e : ULift.{v} K₁ ≃+* E,
        ∀ x : K, e (ULift.up (algebraMap K K₁ x)) = algebraMap (ULift.{v} K) E (ULift.up x) := by
  let algKE : Algebra K E :=
    ((algebraMap (ULift.{v} K) E).comp (algebraMap K (ULift.{v} K))).toAlgebra
  have hcomp : (algebraMap K E).comp (ULift.ringEquiv : ULift.{v} K ≃+* K).toRingHom
      = (RingEquiv.refl E : E ≃+* E).toRingHom.comp (algebraMap (ULift.{v} K) E) := by
    ext x; rfl
  have finKE : Module.Finite K E :=
    @Module.Finite.of_equiv_equiv (ULift.{v} K) E K E _ _ _ _ algUKE algKE
      (ULift.ringEquiv : ULift.{v} K ≃+* K) (RingEquiv.refl E) hcomp finUKE
  obtain ⟨K₁, fK₁, aK₁, finK₁, ⟨eK⟩⟩ :=
    @Stacks.EppTheorem.exists_field_descent_of_module_finite K _ E _ algKE finKE
  refine ⟨K₁, fK₁, aK₁, finK₁, (ULift.ringEquiv : ULift.{v} K₁ ≃+* K₁).trans eK.toRingEquiv, ?_⟩
  intro x
  change eK (algebraMap K K₁ x) = _
  rw [eK.commutes]
  rfl

/-! ### The compositum, upstairs and down -/

section Compositum

variable (K : Type uK) (L : Type uL) (K₁ : Type uK₁) [Field K] [Field L] [Field K₁]
  [Algebra K L] [Algebra K K₁] {K₁' : Type v} [Field K₁'] [Algebra (ULift.{v} K) K₁']

/-- **The tensor products upstairs and downstairs are identified**: along a descent
`ULift K₁ ≃ₐ[ULift K] K₁'`, the ring isomorphism `ULift L ⊗[ULift K] K₁' ≃+* L ⊗[K] K₁`. -/
def uliftTensorRingEquiv (eUK₁ : ULift.{v} K₁ ≃ₐ[ULift.{v} K] K₁') :
    (ULift.{v} L ⊗[ULift.{v} K] K₁') ≃+* (L ⊗[K] K₁) :=
  RingEquiv.trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : ULift.{v} L ≃ₐ[ULift.{v} K] ULift.{v} L)
      eUK₁.symm).toRingEquiv
    (RingEquiv.trans
      ((Algebra.TensorProduct.uliftEquiv (R := K) (S := K) (A := L) (B := K₁) :
          ULift.{v} (L ⊗[K] K₁) ≃ₐ[K] ULift.{v} L ⊗[ULift.{v} K] ULift.{v} K₁)).symm.toRingEquiv
      ULift.ringEquiv)

variable (eUK₁ : ULift.{v} K₁ ≃ₐ[ULift.{v} K] K₁')

/-- The identification respects the left factor. -/
theorem uliftTensorRingEquiv_left (l : ULift.{v} L) :
    uliftTensorRingEquiv K L K₁ eUK₁
        (algebraMap (ULift.{v} L) (ULift.{v} L ⊗[ULift.{v} K] K₁') l)
      = algebraMap L (L ⊗[K] K₁) l.down := by
  change uliftTensorRingEquiv K L K₁ eUK₁ (l ⊗ₜ[ULift.{v} K] (1 : K₁')) = _
  simp [uliftTensorRingEquiv, Algebra.TensorProduct.algebraMap_apply]
  rfl

/-- The identification carries the solution field upstairs to the one downstairs, along the
descent. -/
theorem uliftTensorRingEquiv_right (z : K₁') :
    uliftTensorRingEquiv K L K₁ eUK₁ (algebraMap K₁' (ULift.{v} L ⊗[ULift.{v} K] K₁') z)
      = algebraMap K₁ (L ⊗[K] K₁) (eUK₁.symm z).down := by
  change uliftTensorRingEquiv K L K₁ eUK₁ ((1 : ULift.{v} L) ⊗ₜ[ULift.{v} K] z) = _
  simp [uliftTensorRingEquiv]
  rfl

/-- **The reduced composita upstairs and downstairs are identified**, by pushing
`uliftTensorRingEquiv` through the quotient by the nilradical. -/
def uliftCompositumRingEquiv (eUK₁ : ULift.{v} K₁ ≃ₐ[ULift.{v} K] K₁') :
    reducedCompositum (ULift.{v} K) (ULift.{v} L) K₁' ≃+* reducedCompositum K L K₁ :=
  Stacks.DiscreteValuationRing.EppLevelInduction.reductionRingEquiv _ _ (uliftTensorRingEquiv K L K₁
    eUK₁)

/-- The compositum identification is compatible with the maps from the tensor products. -/
private theorem uliftCompositumRingEquiv_algebraMap_tensor (z : ULift.{v} L ⊗[ULift.{v} K] K₁') :
    uliftCompositumRingEquiv K L K₁ eUK₁
        (algebraMap (ULift.{v} L ⊗[ULift.{v} K] K₁')
          (reducedCompositum (ULift.{v} K) (ULift.{v} L) K₁') z)
      = algebraMap (L ⊗[K] K₁) (reducedCompositum K L K₁) (uliftTensorRingEquiv K L K₁ eUK₁ z) :=
  rfl

/-- The compositum identification respects the left factor. -/
theorem uliftCompositumRingEquiv_left (l : ULift.{v} L) :
    uliftCompositumRingEquiv K L K₁ eUK₁
        (algebraMap (ULift.{v} L) (reducedCompositum (ULift.{v} K) (ULift.{v} L) K₁') l)
      = algebraMap L (reducedCompositum K L K₁) l.down := by
  rw [IsScalarTower.algebraMap_apply (ULift.{v} L) (ULift.{v} L ⊗[ULift.{v} K] K₁')
      (reducedCompositum (ULift.{v} K) (ULift.{v} L) K₁'),
    uliftCompositumRingEquiv_algebraMap_tensor, uliftTensorRingEquiv_left,
    IsScalarTower.algebraMap_apply L (L ⊗[K] K₁) (reducedCompositum K L K₁)]

/-- The compositum identification carries the solution field along the descent. -/
theorem uliftCompositumRingEquiv_right (z : K₁') :
    uliftCompositumRingEquiv K L K₁ eUK₁
        (algebraMap K₁' (reducedCompositum (ULift.{v} K) (ULift.{v} L) K₁') z)
      = algebraMap K₁ (reducedCompositum K L K₁) (eUK₁.symm z).down := by
  rw [IsScalarTower.algebraMap_apply K₁' (ULift.{v} L ⊗[ULift.{v} K] K₁')
      (reducedCompositum (ULift.{v} K) (ULift.{v} L) K₁'),
    uliftCompositumRingEquiv_algebraMap_tensor, uliftTensorRingEquiv_right,
    IsScalarTower.algebraMap_apply K₁ (L ⊗[K] K₁) (reducedCompositum K L K₁)]

end Compositum

/-! ### The universe layer -/

/-- **Epp's theorem at four independent universes, from Epp's theorem at one**: if
`Stacks.EliminateRamification.EppTheorem` holds with all four universes equal to
`max uA uB uK uL`, it holds at `uA`, `uB`, `uK`, `uL`. -/
theorem eppTheorem_of_monomorphic
    (h : Stacks.EliminateRamification.EppTheorem.{max uA uB uK uL, max uA uB uK uL, max uA uB uK uL,
      max uA uB uK uL}) :
    Stacks.EliminateRamification.EppTheorem.{uA, uB, uK, uL} := by
  intro A B K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hEpp
  let := isDomain_ulift.{uA, max uA uB uK uL} A
  let := isDomain_ulift.{uB, max uA uB uK uL} B
  let := isDiscreteValuationRing_ulift.{uA, max uA uB uK uL} A
  let := isDiscreteValuationRing_ulift.{uB, max uA uB uK uL} B
  let := isScalarTower_ulift.{uA, uB, uL, max uA uB uK uL} A B L
  let := isScalarTower_ulift.{uA, uK, uL, max uA uB uK uL} A K L
  let := isFractionRing_ulift.{uA, uK, max uA uB uK uL} A K
  let := isFractionRing_ulift.{uB, uL, max uA uB uK uL} B L
  let := isExtension_ulift.{uA, uB, max uA uB uK uL} A B
  have hEpp' : ∀ p : ℕ, p.Prime →
      CharP (IsLocalRing.ResidueField (ULift.{max uA uB uK uL} A)) p →
      ∀ [ExpChar (IsLocalRing.ResidueField (ULift.{max uA uB uK uL} B)) p],
        EppCondition (ULift.{max uA uB uK uL} A) (ULift.{max uA uB uK uL} B) p := by
    intro p hp hchar _
    have hcharA : CharP (IsLocalRing.ResidueField A) p :=
      charP_of_ringEquiv
        (IsLocalRing.ResidueField.mapEquiv
          (ULift.ringEquiv : ULift.{max uA uB uK uL} A ≃+* A).symm) p
    have hexpB : ExpChar (IsLocalRing.ResidueField B) p :=
      expChar_of_ringEquiv
        (IsLocalRing.ResidueField.mapEquiv
          (ULift.ringEquiv : ULift.{max uA uB uK uL} B ≃+* B).symm) p
    exact eppCondition_of_ringEquiv_square p
      (ULift.ringEquiv : ULift.{max uA uB uK uL} A ≃+* A)
      (ULift.ringEquiv : ULift.{max uA uB uK uL} B ≃+* B)
      (fun a => rfl) (hEpp p hp hcharA)
  obtain ⟨K₁', fK₁', aKK₁', aAK₁', towAKK₁', finKK₁', D, hD⟩ :=
    h (ULift.{max uA uB uK uL} A) (ULift.{max uA uB uK uL} B) (ULift.{max uA uB uK uL} K)
      (ULift.{max uA uB uK uL} L) hEpp'
  have hDcan : (canonicalBaseChange (ULift.{max uA uB uK uL} A) (ULift.{max uA uB uK uL} B)
      (ULift.{max uA uB uK uL} K) (ULift.{max uA uB uK uL} L) K₁').IsWeakSolution :=
    isWeakSolution_canonicalBaseChange_of_isWeakSolution _ _ _ _ _ D hD
  obtain ⟨K₁, fK₁, aKK₁, finKK₁, eKr, heKr⟩ :=
    exists_field_descent_ulift K K₁'
  let eUK₁ : ULift.{max uA uB uK uL} K₁ ≃ₐ[ULift.{max uA uB uK uL} K] K₁' :=
    AlgEquiv.ofRingEquiv (f := eKr) (fun x => by
      change eKr (ULift.up (algebraMap K K₁ x.down)) = _
      rw [heKr, ULift.up_down])
  let algAK₁ : Algebra A K₁ := ((algebraMap K K₁).comp (algebraMap A K)).toAlgebra
  let towAKK₁ : IsScalarTower A K K₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨K₁, fK₁, aKK₁, algAK₁, towAKK₁, finKK₁, canonicalBaseChange A B K L K₁, ?_⟩
  let : Algebra (integralClosure A K₁) (integralClosure B (reducedCompositum K L K₁)) :=
    (integralClosureCompositumMap A B K L K₁).toAlgebra
  let : Algebra (integralClosure (ULift.{max uA uB uK uL} A) K₁')
      (integralClosure (ULift.{max uA uB uK uL} B)
        (reducedCompositum (ULift.{max uA uB uK uL} K) (ULift.{max uA uB uK uL} L) K₁')) :=
    (integralClosureCompositumMap (ULift.{max uA uB uK uL} A) (ULift.{max uA uB uK uL} B)
      (ULift.{max uA uB uK uL} K) (ULift.{max uA uB uK uL} L) K₁').toAlgebra
  have hsqA : ∀ y : ULift.{max uA uB uK uL} A,
      (eUK₁.symm.toRingEquiv.trans
          (ULift.ringEquiv : ULift.{max uA uB uK uL} K₁ ≃+* K₁))
        (algebraMap (ULift.{max uA uB uK uL} A) K₁' y)
        = algebraMap A K₁ ((ULift.ringEquiv : ULift.{max uA uB uK uL} A ≃+* A) y) := by
    intro y
    change (eUK₁.symm (algebraMap (ULift.{max uA uB uK uL} A) K₁' y)).down
      = algebraMap A K₁ y.down
    rw [IsScalarTower.algebraMap_apply (ULift.{max uA uB uK uL} A)
        (ULift.{max uA uB uK uL} K) K₁' y,
      show algebraMap (ULift.{max uA uB uK uL} A) (ULift.{max uA uB uK uL} K) y
        = ULift.up (algebraMap A K y.down) from rfl,
      ← eUK₁.commutes (ULift.up (algebraMap A K y.down)), eUK₁.symm_apply_apply]
    exact (IsScalarTower.algebraMap_apply A K K₁ y.down).symm
  have hsqB : ∀ b : ULift.{max uA uB uK uL} B,
      uliftCompositumRingEquiv K L K₁ eUK₁
          (algebraMap (ULift.{max uA uB uK uL} B)
            (reducedCompositum (ULift.{max uA uB uK uL} K) (ULift.{max uA uB uK uL} L) K₁') b)
        = algebraMap B (reducedCompositum K L K₁)
            ((ULift.ringEquiv : ULift.{max uA uB uK uL} B ≃+* B) b) := by
    intro b
    rw [IsScalarTower.algebraMap_apply (ULift.{max uA uB uK uL} B) (ULift.{max uA uB uK uL} L)
        (reducedCompositum (ULift.{max uA uB uK uL} K) (ULift.{max uA uB uK uL} L) K₁'),
      uliftCompositumRingEquiv_left,
      IsScalarTower.algebraMap_apply B L (reducedCompositum K L K₁)]
    rfl
  refine Stacks.DiscreteValuationRing.EppLevelInduction.isWeakSolution_of_ringEquiv_square
    (canonicalBaseChange (ULift.{max uA uB uK uL} A) (ULift.{max uA uB uK uL} B)
      (ULift.{max uA uB uK uL} K) (ULift.{max uA uB uK uL} L) K₁')
    (canonicalBaseChange A B K L K₁)
    (integralClosureRingEquivOfSquare
      (ULift.ringEquiv : ULift.{max uA uB uK uL} A ≃+* A)
      (eUK₁.symm.toRingEquiv.trans (ULift.ringEquiv : ULift.{max uA uB uK uL} K₁ ≃+* K₁)) hsqA)
    (integralClosureRingEquivOfSquare
      (ULift.ringEquiv : ULift.{max uA uB uK uL} B ≃+* B)
      (uliftCompositumRingEquiv K L K₁ eUK₁) hsqB) ?_ hDcan
  intro x
  have hleft : ∀ y : integralClosure A K₁,
      ((algebraMap (integralClosure A K₁) (integralClosure B (reducedCompositum K L K₁)) y :
          integralClosure B (reducedCompositum K L K₁)) : reducedCompositum K L K₁)
        = algebraMap K₁ (reducedCompositum K L K₁) (y : K₁) := fun _ => rfl
  change algebraMap (integralClosure A K₁) (integralClosure B (reducedCompositum K L K₁))
      (integralClosureRingEquivOfSquare
        (ULift.ringEquiv : ULift.{max uA uB uK uL} A ≃+* A)
        (eUK₁.symm.toRingEquiv.trans
          (ULift.ringEquiv : ULift.{max uA uB uK uL} K₁ ≃+* K₁)) hsqA x)
    = integralClosureRingEquivOfSquare
        (ULift.ringEquiv : ULift.{max uA uB uK uL} B ≃+* B)
        (uliftCompositumRingEquiv K L K₁ eUK₁) hsqB
      (algebraMap (integralClosure (ULift.{max uA uB uK uL} A) K₁')
        (integralClosure (ULift.{max uA uB uK uL} B)
          (reducedCompositum (ULift.{max uA uB uK uL} K) (ULift.{max uA uB uK uL} L) K₁')) x)
  -- `let`, not `have`: the final `exact` needs the coercion of `hx` to unfold to that of `x`.
  let hx : integralClosure (ULift.{max uA uB uK uL} A) K₁' := x
  have hAcoe := integralClosureRingEquivOfSquare_coe
    (ULift.ringEquiv : ULift.{max uA uB uK uL} A ≃+* A)
    (eUK₁.symm.toRingEquiv.trans (ULift.ringEquiv : ULift.{max uA uB uK uL} K₁ ≃+* K₁)) hsqA x
  have hBcoe := integralClosureRingEquivOfSquare_coe
    (ULift.ringEquiv : ULift.{max uA uB uK uL} B ≃+* B)
    (uliftCompositumRingEquiv K L K₁ eUK₁) hsqB
    (algebraMap (integralClosure (ULift.{max uA uB uK uL} A) K₁')
      (integralClosure (ULift.{max uA uB uK uL} B)
        (reducedCompositum (ULift.{max uA uB uK uL} K) (ULift.{max uA uB uK uL} L) K₁')) x)
  apply Subtype.ext
  rw [hleft, hAcoe, hBcoe]
  exact (uliftCompositumRingEquiv_right K L K₁ eUK₁ (hx : K₁')).symm

end Stacks.EppTheorem

end
