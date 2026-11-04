module

public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Finite projective modules over a self-injective ring are injective

Let `R` be a ring which is injective as a left module over itself. Every finite projective
`R`-module is a direct summand of some `Rⁿ`, and Baer's criterion passes to finite products and
to direct summands, so every finite projective `R`-module is injective.

Over the group ring `A[G]` of a finite group with `A = ℤ/ℓⁿ` this makes the bounded complexes of
finite projective modules representing perfect complexes into bounded complexes of injective
modules. It is used in Step 7 of the proof of [Stacks, Tag 03UG].

## Main results

* `Module.Baer.pi_fin`: Baer's criterion passes to `Fin n → Q`.
* `Module.Baer.of_retract`: Baer's criterion passes to direct summands.
* `Module.Baer.of_finite_projective`: a finite projective module over a self-injective ring
  satisfies Baer's criterion.
* `ModuleCat.injective_of_finite_projective`: the same, as injectivity in `ModuleCat`.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace Module.Baer

variable {R : Type u} [Ring R]

/-- **Baer's criterion passes to finite powers.** -/
theorem pi_fin {Q : Type v} [AddCommGroup Q] [Module R Q] (hQ : Module.Baer R Q) (n : ℕ) :
    Module.Baer R (Fin n → Q) := by
  intro I g
  choose h hh using fun i : Fin n => hQ I (LinearMap.proj i ∘ₗ g)
  exact ⟨LinearMap.pi h, fun x hx => funext fun i => hh i x hx⟩

/-- **Baer's criterion passes to direct summands.** -/
theorem of_retract {Q : Type w} {P : Type v} [AddCommGroup Q] [Module R Q] [AddCommGroup P]
    [Module R P]
    (hQ : Module.Baer R Q) (s : P →ₗ[R] Q) (r : Q →ₗ[R] P) (hrs : r ∘ₗ s = LinearMap.id) :
    Module.Baer R P := by
  intro I g
  obtain ⟨h, hh⟩ := hQ I (s ∘ₗ g)
  refine ⟨r ∘ₗ h, fun x hx => ?_⟩
  rw [LinearMap.comp_apply, hh x hx]
  show (r ∘ₗ s) (g ⟨x, hx⟩) = _
  rw [hrs, LinearMap.id_apply]

/-- **A finite projective module over a self-injective ring satisfies Baer's criterion.** -/
theorem of_finite_projective (hR : Module.Baer R R) (P : Type v) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P] : Module.Baer R P := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R P
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  exact (hR.pi_fin n).of_retract s f hs

end Module.Baer

namespace ModuleCat

/-- **A finite projective module over a self-injective ring is injective.** -/
theorem injective_of_finite_projective {R : Type u} [Ring R] (hR : Module.Baer R R)
    (P : ModuleCat.{v} R) [Module.Finite R P] [Module.Projective R P] : Injective P :=
  have := (Module.Baer.of_finite_projective hR P).injective
  Module.injective_object_of_injective_module R P

end ModuleCat
