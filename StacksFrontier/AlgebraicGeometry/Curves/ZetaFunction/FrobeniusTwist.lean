module

public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.LinearSystem
public import StacksFrontier.LinearAlgebra.SemilinearFrobeniusFixedPoints

/-!
# The Frobenius twist on Riemann–Roch spaces

Let `C` be a smooth proper curve over an algebraically closed field `Ω` of characteristic `p`, and
`Ψ` a `q`-semilinear automorphism of `C` (`q = p ^ n`), acting on the closed points by `σ` and on
rational functions by pullback `τ` (`ord_x (τ f) = ord_{σ x} f`, `τ c = c ^ q` on constants).
For a divisor `D` whose class is fixed by `Ψ^*`, `D ∘ σ = D + div u` for some `u`, and
`T f = u · τ f` is an injective `q`-semilinear endomorphism of `L(D)`.

## Main definitions

* `Stacks.Zeta.twistMap`: the `q`-semilinear endomorphism `T f = u · τ f` of `L(D)`.

## Main results

* `Stacks.Zeta.divOf_tau`: `div (τ f) = div f ∘ σ`.
* `Stacks.Zeta.exists_divisorClass_eq`: every Picard class is the class of a divisor.
* `Stacks.Zeta.twistMap_injective`: the map `T` is injective.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Order TopologicalSpace

universe u

namespace Stacks.Zeta

/-- Pullback of rational functions along an automorphism `Ψ`. -/
abbrev tau {C : Scheme.{u}} [IsIntegral C] (Ψ : C ≅ C) : C.functionField ≃+* C.functionField :=
  (Stacks.Chow.functionFieldRingEquivOfIso Ψ).symm

/-- The divisor `D ∘ σ`, written as `D.mapDomain σ⁻¹`, takes the value `D (σ x)` at `x`. -/
theorem mapDomain_closedPointPerm_symm_apply {C : Scheme.{u}} (Ψ : C ≅ C)
    (D : ClosedPoint C →₀ ℤ) (x : ClosedPoint C) :
    D.mapDomain (closedPointPerm Ψ).symm x = D (closedPointPerm Ψ x) := by
  rw [Finsupp.mapDomain_equiv_apply, Equiv.symm_symm]

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {C : Scheme.{u}} (g : C ⟶ Spec (.of Ω))
  [IsProper g] [Smooth g] [IsCurve Ω g] [IsLocallyNoetherian C]

omit [IsAlgClosed Ω] [IsProper g] in
/-- **Every Picard class is the class of a divisor**: that of a meromorphic section of its
representative. -/
theorem exists_divisorClass_eq (c : Stacks.Picard.ofScheme C) :
    ∃ D : ClosedPoint C →₀ ℤ, divisorClass g D = c := by
  set L := (Stacks.Picard.picardRepresentative C.toRingedSpace c).obj
  have hL : Stacks.SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property L :=
    (Stacks.Picard.picardRepresentative C.toRingedSpace c).property
  have : AlgebraicGeometry.SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property L :=
    hL.toAlgebraicGeometry
  obtain ⟨s, hs⟩ := exists_isRegularMeromorphicSection_of_isIntegral C L
  exact ⟨_, (divisorClass_sectionDivisor g L s hs hL).trans
    (Stacks.Picard.classOf_picardRepresentative C.toRingedSpace c)⟩

variable (p : ℕ) [hp : Fact p.Prime] [CharP Ω p] (n : ℕ) (Ψ : C ≅ C)
  (hΨ : Ψ.hom ≫ g = g ≫ Spec.map (CommRingCat.ofHom (iterateFrobenius Ω p n)))


omit [IsAlgClosed Ω] in
/-- **`div (τ f) = div f ∘ σ`.** -/
theorem divOf_tau {f : C.functionField} (hf : f ≠ 0) :
    divOf g ((map_ne_zero_iff _ (tau Ψ).injective).2 hf) =
      (divOf g hf).mapDomain (closedPointPerm Ψ).symm := by
  ext x
  rw [mapDomain_closedPointPerm_symm_apply, divOf_apply, divOf_apply,
    ord_functionFieldRingEquivOfIso_symm]
  rfl

omit [IsAlgClosed Ω] [IsProper g] [Smooth g] [IsLocallyNoetherian C] in
include hΨ in
/-- On constants, `τ` is the `q`-th power map: `τ c = c ^ q` with `q = p ^ n`. -/
theorem tau_algebraMap (c : Ω) :
    letI := ffAlg g
    tau Ψ (algebraMap Ω C.functionField c) = algebraMap Ω C.functionField c ^ p ^ n := by
  let := ffAlg g
  rw [tau, functionFieldRingEquivOfIso_symm_algebraMap g Ψ _ hΨ, iterateFrobenius_def, map_pow]

omit [IsAlgClosed Ω] [IsProper g] in
/-- `τ` carries `L(D)` into `L(D ∘ σ)`. -/
theorem tau_mem_rrSpace {D : ClosedPoint C →₀ ℤ} {a : C.functionField} :
    letI := ffAlg g
    a ∈ rrSpace g D → tau Ψ a ∈ rrSpace g (D.mapDomain (closedPointPerm Ψ).symm) := by
  let := ffAlg g
  rintro (rfl | ha)
  · rw [map_zero]; exact Or.inl rfl
  refine Or.inr fun x => ?_
  rw [mapDomain_closedPointPerm_symm_apply, ord_functionFieldRingEquivOfIso_symm]
  exact ha (closedPointPerm Ψ x)

/-- **The twisted Frobenius on `L(D)`.** If `D ∘ σ = D + div u`, then `T f = u · τ f` maps
`L(D)` to itself, `q`-semilinearly. -/
def twistMap (D : ClosedPoint C →₀ ℤ) {u : C.functionField} (hu : u ≠ 0)
    (hD : D.mapDomain (closedPointPerm Ψ).symm = D + divOf g hu) :
    letI := ffAlg g
    rrSpace g D →ₛₗ[iterateFrobenius Ω p n] rrSpace g D :=
  letI := ffAlg g
  { toFun := fun a => ⟨u * tau Ψ a, (mem_rrSpace_add_divOf_iff g hu _).1
      (hD ▸ tau_mem_rrSpace g Ψ a.2)⟩
    map_add' := fun a b => Subtype.ext (by
      change u * tau Ψ (a + b) = u * tau Ψ a + u * tau Ψ b
      rw [map_add, mul_add])
    map_smul' := fun c a => Subtype.ext (by
      change u * tau Ψ (c • (a : C.functionField)) = (iterateFrobenius Ω p n c) • (u * tau Ψ a)
      rw [Algebra.smul_def, map_mul, tau_algebraMap g p n Ψ hΨ, iterateFrobenius_def,
        Algebra.smul_def, map_pow]
      ring) }

omit [IsAlgClosed Ω] in
/-- The twisted Frobenius sends `a ∈ L(D)` to `u · τ a`. -/
theorem twistMap_apply (D : ClosedPoint C →₀ ℤ) {u : C.functionField} (hu : u ≠ 0)
    (hD : D.mapDomain (closedPointPerm Ψ).symm = D + divOf g hu) (a) :
    (twistMap g p n Ψ hΨ D hu hD a : C.functionField) = u * tau Ψ a := rfl

omit [IsAlgClosed Ω] in
/-- The twisted Frobenius on `L(D)` is injective. -/
theorem twistMap_injective (D : ClosedPoint C →₀ ℤ) {u : C.functionField} (hu : u ≠ 0)
    (hD : D.mapDomain (closedPointPerm Ψ).symm = D + divOf g hu) :
    Function.Injective (twistMap g p n Ψ hΨ D hu hD) := fun a b h => by
  have h' := congrArg Subtype.val h
  rw [twistMap_apply, twistMap_apply] at h'
  exact Subtype.ext ((tau Ψ).injective (mul_left_cancel₀ hu h'))

end Stacks.Zeta

end
