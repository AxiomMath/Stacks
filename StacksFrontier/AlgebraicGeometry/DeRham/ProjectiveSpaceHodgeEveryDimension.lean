module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DeRham.ProjectiveSpaceZeroHodge

/-!
# The Hodge cohomology of `ℙⁿ_A`, for every `n ≥ 0`

Let `A` be a commutative ring, `n ≥ 0` and `ℙⁿ_A = Proj A[T₀, …, Tₙ]` with its structure morphism
`ℙⁿ_A ⟶ Spec A`. This file states [Stacks, Tag 0FMI] for every `n ≥ 0`:

* `H^q(ℙⁿ_A, Ωᵖ) = 0` unless `0 ≤ p = q ≤ n` (`isZero_projectiveHodgeCohomology`);
* for `0 ≤ p ≤ n` the `A`-module `Hᵖ(ℙⁿ_A, Ωᵖ)` is free of rank one with basis element
  `c₁^{Hodge}(𝒪(1))ᵖ` (`exists_basis_projectiveHodgeChernPow`).

The powers `c₁^{Hodge}(𝒪(1))ᵖ` are actual cup powers, for every `n ≥ 0`: `c⁰` is the class of the
unit section of `Ω⁰ = 𝒪` and `c^{p+1} = cᵖ ∪ c₁^{Hodge}(𝒪(1))` for the cup product of
[Stacks, Section 01FP] attached to the wedge product `Ωᵖ × Ω ⟶ Ω^{p+1}`, where `c₁^{Hodge}(𝒪(1))`
is the Hodge first Chern class of [Stacks, Tag 0FLE] (`projectiveHodgeFirstChernClassModule`).

For `n = m + 1 ≥ 1` every object here is the one of
`StacksFrontier.AlgebraicGeometry.DeRham.ProjectiveSpaceHodgeCohomology` and
`StacksFrontier.AlgebraicGeometry.DeRham.ProjectiveSpaceHodgeChernPowers` by definition
(`projectiveHodgeCohomology_succ`, `projectiveHodgeChernPow_succ`), and both assertions are the
ones proved there. For `n = 0` they are proved in
`StacksFrontier.AlgebraicGeometry.DeRham.ProjectiveSpaceZeroHodge`: `Ωᵖ = 0` for `p > 0`,
`H^q(ℙ⁰_A, 𝒪) = 0` for `q > 0`, and `1` is a basis of `H⁰(ℙ⁰_A, 𝒪) = A`, which is the first line
of the source's proof.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.projectiveChernPowR2`: the powers
  `c₁^{Hodge}(𝒪(1))ᵖ`, in hypercohomology.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.projectiveHodgeChernPow`: the powers, in
  `Hᵖ(ℙⁿ_A, Ωᵖ)`.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.isZero_projectiveHodgeCohomology`:
  [Stacks, Tag 0FMI], the vanishing, for every `n ≥ 0`.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.exists_basis_projectiveHodgeChernPow`:
  [Stacks, Tag 0FMI], the basis, for every `n ≥ 0`.

## References

* [Stacks Project, Tag 0FMI](https://stacks.math.columbia.edu/tag/0FMI)
* [Stacks Project, Tag 0FUK](https://stacks.math.columbia.edu/tag/0FUK)
* [Stacks Project, Tag 0FLE](https://stacks.math.columbia.edu/tag/0FLE)
* [Stacks Project, Section 01FP](https://stacks.math.columbia.edu/tag/01FP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cech.Hypercohomology

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceHodge

open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjEulerSequence
open Stacks.ProjectiveSpace.Cohomology

variable (A : Type u) [CommRing A] (n : ℕ)

/-! ### The cup powers of the Hodge first Chern class of `𝒪(1)`, for every `n ≥ 0` -/

section Powers

/-- **The wedge product `Ωᵖ × Ω ⟶ Ω^{p+1}`** on `ℙⁿ_A`, `(x, ω) ↦ x ∧ ω`. -/
def projectiveWedgeBilinear (p : ℕ) : Stacks.BilinearMap (projectiveForms A n p).val
    (projDifferentials A n).val (projectiveForms A n (p + 1)).val :=
  ((Scheme.Modules.exteriorAlgebra (X := projectiveSpace A n) (projDifferentials A n)).mul
    (p : ℤ) 1).compRight
      (Scheme.Modules.exteriorGenerator (X := projectiveSpace A n) (projDifferentials A n)).val

/-- The wedge product `Ωᵖ × Ω ⟶ Ω^{p+1}` as a pairing of the sheaves placed in degree zero. -/
def projectiveWedgePairing (p : ℕ) : Pairing (projectiveSpace A n).sheaf
    (singlePlus (projectiveSpace A n).sheaf (projectiveForms A n p) 0)
    (singlePlus (projectiveSpace A n).sheaf (projDifferentials A n) 0)
    (singlePlus (projectiveSpace A n).sheaf (projectiveForms A n (p + 1)) 0) :=
  singlePairing (bilinearPairing (projectiveWedgeBilinear A n p))

/-- **The powers `c₁^{Hodge}(𝒪(1))ᵖ ∈ Hᵖ(ℙⁿ_A, Ωᵖ)`**, in hypercohomology: `c⁰` is the class of
the unit section `1` of `Ω⁰ = 𝒪`, and `c^{p+1} = cᵖ ∪ c₁^{Hodge}(𝒪(1))`, the cup product of
[Stacks, Section 01FP] for the wedge product `Ωᵖ × Ω ⟶ Ω^{p+1}`. -/
def projectiveChernPowR2 : (p : ℕ) → hypercohomology (projectiveSpace A n).sheaf
    (singlePlus (projectiveSpace A n).sheaf (projectiveForms A n p) 0) p
  | 0 => sectionClass (projectiveForms A n 0) (projectiveUnitForm A n)
  | p + 1 => cup (projectiveSpace A n).sheaf (cechComputesSheaf_projectiveForms A n p)
      (cechComputesSheaf_projDifferentials A n) (projectiveWedgePairing A n p) p 1
      ((p + 1 : ℕ) : ℤ) (by push_cast; ring) (projectiveChernPowR2 p)
      (projectiveHodgeFirstChernClassModule A n)

/-- **The powers `c₁^{Hodge}(𝒪(1))ᵖ ∈ Hᵖ(ℙⁿ_A, Ωᵖ)` of the Hodge first Chern class of `𝒪(1)`**,
for every `n ≥ 0`: `projectiveChernPowR2`, read in the cohomology computed by right derived
functors. -/
def projectiveHodgeChernPow (p : ℕ) : ↥(projectiveHodgeCohomology A n p p) :=
  (projectiveHodgeCohomologyIso A n p p).inv (projectiveChernPowR2 A n p)

/-- At `n = m + 1` the powers are those of
`StacksFrontier.AlgebraicGeometry.DeRham.ProjectiveSpaceHodgeChernPowers`, in hypercohomology. -/
theorem projectiveChernPowR2_succ (m : ℕ) :
    ∀ p : ℕ, projectiveChernPowR2 A (m + 1) p = chernPowR2 A m p
  | 0 => rfl
  | p + 1 => by
    rw [projectiveChernPowR2, chernPowR2, projectiveChernPowR2_succ m p]
    rfl

/-- At `n = m + 1` the powers are those of
`StacksFrontier.AlgebraicGeometry.DeRham.ProjectiveSpaceHodgeChernPowers`. -/
theorem projectiveHodgeChernPow_succ (m p : ℕ) :
    projectiveHodgeChernPow A (m + 1) p = hodgeChernPow A m p := by
  rw [projectiveHodgeChernPow, projectiveChernPowR2_succ]
  rfl

end Powers

/-! ### [Stacks, Tag 0FMI], for every `n ≥ 0` -/

section Statement

/-- **[Stacks, Tag 0FMI], the vanishing, for every `n ≥ 0`.** `H^q(ℙⁿ_A, Ωᵖ) = 0` unless
`0 ≤ p = q ≤ n`. For `n ≥ 1` it is clause (1) of [Stacks, Tag 0FUK]
(`isZero_hodgeCohomology_of_ne_or_gt`); for `n = 0` it is
`isZero_projectiveHodgeCohomology_zero`. -/
@[stacks 0FMI "H^q(ℙⁿ_A, Ω^p) = 0 unless 0 ≤ p = q ≤ n, for every n ≥ 0"]
theorem isZero_projectiveHodgeCohomology (p q : ℕ) (hpq : p ≠ q ∨ n < p) :
    IsZero (projectiveHodgeCohomology A n p q) := by
  rcases n with _ | m
  · exact isZero_projectiveHodgeCohomology_zero A p q hpq
  · exact isZero_hodgeCohomology_of_ne_or_gt p q hpq

/-- **[Stacks, Tag 0FMI], the basis, for every `n ≥ 0`.** For `0 ≤ p ≤ n` the `A`-module
`Hᵖ(ℙⁿ_A, Ωᵖ)` is free of rank one with basis element `c₁^{Hodge}(𝒪(1))ᵖ`, the `p`-th cup power
of the Hodge first Chern class of `𝒪(1)` (`projectiveHodgeChernPow`).

For `n ≥ 1` this is `exists_basis_chernPow`, through `projectiveHodgeChernPow_succ`. For `n = 0`
only `p = 0` occurs, and `c⁰ = 1` is a basis of `H⁰(ℙ⁰_A, 𝒪) = A`
(`exists_basis_projectiveHodgeCohomology_unitForm`). -/
@[stacks 0FMI "for 0 ≤ p ≤ n the A-module H^p(ℙⁿ_A, Ω^p) is free of rank one with basis element
c₁^{Hodge}(𝒪(1))^p, for every n ≥ 0"]
theorem exists_basis_projectiveHodgeChernPow (p : ℕ) (hp : p ≤ n) :
    ∃ b : Module.Basis (Fin 1) A ↥(projectiveHodgeCohomology A n p p),
      b 0 = projectiveHodgeChernPow A n p := by
  rcases n with _ | m
  · obtain rfl : p = 0 := Nat.le_zero.mp hp
    exact exists_basis_projectiveHodgeCohomology_unitForm A 0
  · rw [projectiveHodgeChernPow_succ]
    exact exists_basis_chernPow A m p hp

end Statement

end Stacks.AlgebraicGeometry.ProjectiveSpaceHodge

end
