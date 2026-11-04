module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import StacksCore.RingTheory.Ideal.Operations
public import StacksCore.RingTheory.Jacobson.Ideal
import StacksCore.Tactic.StacksAttribute

/-! # Localization and quotients of rings -/

add_to_stacks 00CT "(1)" Ideal.localized'_eq_map
add_to_stacks 02C9 IsLocalization.map_under
add_to_stacks 00E3 IsLocalization.primeSpectrumOrderIso

@[expose] public section

variable {A : Type*} [CommRing A] (S : Submonoid A) (I : Ideal A)
variable (A_S : Type*) [CommRing A_S] [Algebra A A_S] [IsLocalization S A_S]

namespace IsLocalization

variable (Q : Type*) [CommRing Q] [Algebra (A ⧸ I) Q]
variable [IsLocalization (Algebra.algebraMapSubmonoid (A ⧸ I) S) Q]

/-- Localization commutes with quotients: for any localization
`Q` of `A/I` at the image `S̄` of `S`, there is a canonical algebra (in particular ring)
isomorphism `S̄⁻¹(A/I) ≅ S⁻¹A/S⁻¹I`. -/
@[stacks 00CT "(2)"]
noncomputable def quotientEquiv : Q ≃ₐ[A ⧸ I] A_S ⧸ I.map (algebraMap A A_S) :=
  algEquiv (Algebra.algebraMapSubmonoid (A ⧸ I) S) Q (A_S ⧸ I.map (algebraMap A A_S))

end IsLocalization

/-- If a submonoid `S` absorbs an ideal `I` under addition, then `I` lands in the Jacobson
radical after localizing at `S`.

The hypothesis is exactly what makes every `1 + i/t` a unit downstairs: an element of
`I.map (algebraMap A A_S)` is `i/t` with `i ∈ I` and `t ∈ S`, so `(1 + i/t) * t = t + i`, which
`h` places back in `S` and which therefore becomes a unit. Note the proof never needs `i/t`
itself to be well-behaved — it only multiplies up by `t` and reads off
`isUnit_of_mul_isUnit_left`.

The motivating instance is `S.addIdeal I`, which absorbs `I` by construction; see
`Ideal.map_addIdeal_le_ringJacobson`. -/
theorem Ideal.map_le_ringJacobson_of_add_mem (h : ∀ s ∈ S, ∀ i ∈ I, s + i ∈ S) :
    I.map (algebraMap A A_S) ≤ Ring.jacobson A_S := by
  rw [Ideal.le_ringJacobson_iff_isUnit_one_add]
  rintro z hz
  obtain ⟨⟨i, t⟩, hit⟩ := (IsLocalization.mem_map_algebraMap_iff S A_S).1 hz
  refine isUnit_of_mul_isUnit_left (y := algebraMap A A_S t) ?_
  rw [add_mul, one_mul, hit, ← map_add]
  exact IsLocalization.map_units A_S ⟨(t : A) + (i : A), h t t.2 i i.2⟩

/-- Localizing the submodule `I • ⊤` gives the extended ideal acting on the localized module.

Three Mathlib rewrites in one place — `Submodule.localized'_smul`, `Ideal.localized'_eq_map`,
`Submodule.localized'_top` — which is the idiom Mathlib itself uses at
`RingTheory/Support.lean`'s `Module.support_quotient`. -/
theorem Submodule.localized'_smul_top {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    [Module A X] [Module A Y] [Module A_S Y] [IsScalarTower A A_S Y]
    (φ : X →ₗ[A] Y) [IsLocalizedModule S φ] :
    (I • (⊤ : Submodule A X)).localized' A_S S φ = I.map (algebraMap A A_S) • ⊤ := by
  rw [Submodule.localized'_smul, Ideal.localized'_eq_map, Submodule.localized'_top]

section AddIdeal

variable {B : Type*} [CommRing B] (T : Submonoid B) (J : Ideal B)
variable (B_T : Type*) [CommRing B_T] [Algebra B B_T] [hT : IsLocalization (T.addIdeal J) B_T]

-- `hT` is what pins down `T`; the conclusion alone does not mention it.
include hT in
/-- Localizing at `T + J` sends `J` into the Jacobson radical.

This is the reason `T + J` is the submonoid Stacks 0GLX localizes at: it is the smallest
enlargement of `T` for which Nakayama's lemma applies to `J` downstairs. -/
theorem Ideal.map_addIdeal_le_ringJacobson :
    J.map (algebraMap B B_T) ≤ Ring.jacobson B_T :=
  Ideal.map_le_ringJacobson_of_add_mem (T.addIdeal J) J B_T
    fun _ ht _ hi => Submonoid.add_mem_addIdeal ht hi

end AddIdeal
