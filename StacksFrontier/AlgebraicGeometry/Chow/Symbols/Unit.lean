module

public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.UnitScaling
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Automorphisms
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.Basic

/-!
# The symbol when one argument is a unit

For a finite module of dimension one over a Noetherian local ring, the symbol of a unit and a
nonzerodivisor is the residue of the unit raised to the length of the quotient by the
nonzerodivisor. For the ring itself, that length is its order of vanishing.

## Main results

* `AlgebraicGeometry.moduleSymbol_unit_left` computes the symbol of a unit on a module.
* `AlgebraicGeometry.moduleSymbol_unit_left_ring` gives the order-of-vanishing formula for the
  ring itself.

## Implementation notes

The quotient by `bM` is expressed as the quotient by the range of scalar multiplication by `b`.
The finite length and the order of vanishing are both converted from `ℕ∞` to `ℕ` for the
exponent.

## References

* [Stacks Project, Tag 02Q2](https://stacks.math.columbia.edu/tag/02Q2)
-/

@[expose] public section

noncomputable section

open CategoryTheory

open Module.FiniteLength

namespace AlgebraicGeometry

universe u v

/-- **Stacks Project, Tag 02Q2.** The symbol with a unit in its first argument is the
corresponding power of its residue, with exponent the length of the quotient by the second
argument. -/
@[stacks 02Q2 "module formula"]
theorem moduleSymbol_unit_left
    {A : Type u} {M : Type v} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (u : Aˣ) (b : A) (hb : IsSMulRegular M b)
    (hdim : Module.supportDim A M = 1) :
    moduleSymbol (u : A) b (Units.isSMulRegular M u) hb hdim =
      IsLocalRing.residue A u ^
        moduleLength A (M ⧸ (LinearMap.lsmul A M b).range) := by
  let φ : M →ₗ[A] M := LinearMap.lsmul A M (u : A)
  let ψ : M →ₗ[A] M := LinearMap.lsmul A M b
  have hcomm : φ ∘ₗ ψ = ψ ∘ₗ φ := LinearMap.ext fun _ => smul_comm _ _ _
  have hcommRange : LinearMap.range (φ ∘ₗ ψ) = LinearMap.range (ψ ∘ₗ φ) :=
    congrArg LinearMap.range hcomm
  have hrange : LinearMap.range (φ ∘ₗ ψ) = LinearMap.range ψ := by
    rw [hcomm, LinearMap.range_comp_of_range_eq_top]
    exact LinearMap.range_eq_top.mpr
      (fun x => ⟨((u⁻¹ : Aˣ) : A) • x, by simp [φ, smul_smul]⟩)
  let Q := M ⧸ LinearMap.range (φ ∘ₗ ψ)
  have hM : IsFiniteLength A Q :=
    isFiniteLength_quotient_mul (u : A) b (Units.isSMulRegular M u) hb hdim
  let qφ : Q →ₗ[A] Q := periodicQuotientPhi φ ψ hcommRange
  let qψ : Q →ₗ[A] Q := periodicQuotientPsi φ ψ hcommRange
  have he : (LinearEquiv.smulOfUnit (M := Q) u : Q →ₗ[A] Q) = qφ := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun m => ?_)
    change (u : A) • (Submodule.Quotient.mk m : Q) = (Submodule.Quotient.mk (φ m) : Q)
    simp [φ, LinearMap.lsmul_apply]
  have hqψ : qψ = 0 := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun m => ?_)
    change Submodule.Quotient.mk (ψ m) = 0
    rw [Submodule.Quotient.mk_eq_zero, hrange]
    exact ⟨m, rfl⟩
  have hperiodic : periodicDeterminant qφ qψ
      (exact_mul_left_right (u : A) b hb)
      (exact_mul_right_left (u : A) b (Units.isSMulRegular M u)) hM =
        determinantAutomorphism (LinearEquiv.smulOfUnit (M := Q) u) hM := by
    simpa only [hqψ, he] using
      periodicDeterminant_equiv_zero (LinearEquiv.smulOfUnit (M := Q) u) hM
  have hdet : (determinantAutomorphism (LinearEquiv.smulOfUnit (M := Q) u) hM :
      IsLocalRing.ResidueField A) = IsLocalRing.residue A u ^ moduleLength A Q := by
    let F := determinantFunctor A
    let X : FiniteLengthModuleIso A := ⟨⟨ModuleCat.of A Q, hM⟩⟩
    let f : X ⟶ X :=
      ⟨CategoryTheory.ObjectProperty.isoMk _ (LinearEquiv.smulOfUnit (M := Q) u).toModuleIso⟩
    have hdimDetX : Module.finrank (IsLocalRing.ResidueField A)
        (determinant A ↑X.of.obj) = 1 :=
      (F.objIso X).toLinearEquiv.finrank_eq.symm.trans (F.toFunctor.obj X).of.property
    change (LinearEquiv.det (F.mapLinearEquiv f) : IsLocalRing.ResidueField A) = _
    rw [LinearEquiv.coe_det, show (F.mapLinearEquiv f :
      determinant A Q →ₗ[IsLocalRing.ResidueField A] determinant A Q) =
      (IsLocalRing.residue A u ^ moduleLength A Q) • LinearMap.id from
      LinearMap.ext (determinantFunctor_map_unit_smul X u f fun _ => rfl), LinearMap.det_smul]
    simp [hdimDetX]
  change (periodicDeterminant qφ qψ (exact_mul_left_right (u : A) b hb)
    (exact_mul_right_left (u : A) b (Units.isSMulRegular M u)) hM :
      IsLocalRing.ResidueField A) = _
  rw [hperiodic, hdet]
  change IsLocalRing.residue A u ^ moduleLength A (M ⧸ LinearMap.range (φ ∘ₗ ψ)) = _
  rw [hrange]

/-- **Stacks Project, Tag 02Q2.** For a one-dimensional Noetherian local ring, the exponent in
the unit-symbol formula is the order of vanishing of the second argument. -/
@[stacks 02Q2 "ring formula"]
theorem moduleSymbol_unit_left_ring
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (u : Aˣ) (b : A) (hb : IsSMulRegular A b)
    (hdim : ringKrullDim A = 1) :
    moduleSymbol (M := A) (u : A) b (Units.isSMulRegular A u) hb
      (by simpa only [Module.supportDim_self_eq_ringKrullDim] using hdim) =
      IsLocalRing.residue A u ^ (Ring.ord A b).toNat := by
  have hrange : (LinearMap.lsmul A A b).range = Ideal.span {b} := by
    ext x
    rw [LinearMap.mem_range, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, by simp⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, by simp [LinearMap.lsmul_apply]⟩
  rw [moduleSymbol_unit_left u b hb, hrange]
  rfl

end AlgebraicGeometry
