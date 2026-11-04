module

public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.RingTheory.FinitePresentation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A finite presentation whose variables include a prescribed family of elements

A finitely presented algebra `B` over `C` has a finite presentation
`B = C[x_1, …, x_n]/(f_1, …, f_m)` in which any prescribed finite family of elements of `B`
occurs among the images of the variables: adjoin the family to the variables of some presentation,
and take for relations a finite generating family of the kernel, which is finitely generated
because `B` is finitely presented.

This is what makes a *renaming of the variables* available as a morphism of presentations. A map
of two presentations defined instead by lifting the generators of the one through the other
depends on the structure map `C → B`; a renaming does not, and that is what lets one map serve two
different algebra structures at once — the situation of Stacks 0CAY, where the same polynomial
ring over `𝒪^∧_{S,s}` carries the two specialisations `σ` and `σ'` of one relation matrix.

## Main results

* `Stacks.exists_presentation_val_eq`: **the presentation with prescribed generators**.
* `Stacks.exists_presentation_val_eq_of_finiteType`: the same over a Noetherian base, where
  finite type suffices.
-/

@[expose] public section

universe u v

namespace Stacks

/-- **A finitely presented algebra has a finite presentation whose variables include any
prescribed finite family of elements.** The family is adjoined to the variables of an arbitrary
finite presentation — which keeps the generators surjective — and the relations are a finite
generating family of the kernel, finitely generated because the algebra is finitely presented. -/
theorem exists_presentation_val_eq (C : Type u) (B : Type v) [CommRing C] [CommRing B]
    [Algebra C B] [Algebra.FinitePresentation C B] {k : ℕ} (z : Fin k → B) :
    ∃ (n m : ℕ) (P : Algebra.Presentation C B (Fin n) (Fin m)) (ι : Fin k → Fin n),
      Function.Injective ι ∧ ∀ i, P.val (ι i) = z i := by
  obtain ⟨a, c, ⟨P₀⟩⟩ := Algebra.Presentation.exists_presentation_fin C B
  set val : Fin (k + a) → B := Fin.addCases z P₀.val with hvaldef
  have hleft : ∀ i : Fin k, val (Fin.castAdd a i) = z i := by
    intro i; rw [hvaldef]; exact Fin.addCases_left i
  have hright : ∀ i : Fin a, val (Fin.natAdd k i) = P₀.val i := by
    intro i; rw [hvaldef]; exact Fin.addCases_right i
  have hsurj : Function.Surjective (MvPolynomial.aeval (R := C) val) := by
    intro x
    obtain ⟨q, hq⟩ := P₀.aeval_val_surjective x
    refine ⟨MvPolynomial.rename (Fin.natAdd k) q, ?_⟩
    rw [MvPolynomial.aeval_rename]
    refine Eq.trans ?_ hq
    exact congrArg (fun w => MvPolynomial.aeval (R := C) w q) (funext hright)
  obtain ⟨m, v, hv⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Algebra.Generators.ofSurjective val hsurj).fg_ker_of_finitePresentation
  refine ⟨k + a, m,
    { __ := Algebra.Generators.ofSurjective val hsurj
      relation := v
      span_range_relation_eq_ker := hv },
    Fin.castAdd a, Fin.castAdd_injective k a, hleft⟩

/-- **Over a Noetherian base, finite type suffices**: a finite type algebra over a Noetherian ring
is finitely presented, so it has a finite presentation whose variables include any prescribed
finite family of elements. -/
@[ega "IV 1.4.1" "more general"]
theorem exists_presentation_val_eq_of_finiteType (C : Type u) (B : Type v) [CommRing C]
    [CommRing B] [Algebra C B] [IsNoetherianRing C] [Algebra.FiniteType C B] {k : ℕ}
    (z : Fin k → B) :
    ∃ (n m : ℕ) (P : Algebra.Presentation C B (Fin n) (Fin m)) (ι : Fin k → Fin n),
      Function.Injective ι ∧ ∀ i, P.val (ι i) = z i :=
  have : Algebra.FinitePresentation C B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exists_presentation_val_eq C B z

end Stacks

end
