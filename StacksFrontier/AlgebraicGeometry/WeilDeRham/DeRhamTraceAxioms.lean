module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.DeRhamKunnethAxiom
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.DeRhamGlobalSectionsAxiom
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.DeRhamFiniteProjectionInjective
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.DeRhamProjectiveBundleAxiom
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.DeRhamBlowupAxiom
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.TraceAxiomAlgClosed
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.DeRhamFieldBaseChangeData
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.FieldBaseChangeDivisorTrace
public import StacksFrontier.AlgebraicGeometry.DeRham.WeilCohomology.DeRhamWeilCoproductAxiom
public import StacksFrontier.AlgebraicGeometry.DeRham.WeilCohomology.DeRhamWeilDivisorAxiom
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Axiom (A6) for de Rham cohomology in characteristic zero

Proposition 0FWD of the Stacks project shows that de Rham cohomology over a field `k` of
characteristic zero satisfies the axioms of Section 0FID. This file proves the axiom (A6) (the
trace) for the de Rham data
`Stacks.DeRhamWeil.deRhamFirstChernClassData k`, with `γ` the cycle class map of Lemma 0FIF of any
cohomological Chern character of Tag 0FIE, following the source:

* over an algebraically closed field, (A6) is
  `Stacks.WeilDeRham.traceAxiom_cycleClass_of_isAlgClosed`, applied to the de Rham axioms
  (A1) – (A5), (A8) and to (FIN)
  (`Stacks.WeilDeRham.deRham_finiteProjectionInjective`), the finite syntomic projection to
  projective space with its de Rham trace;
* over an arbitrary field of characteristic zero, the source reduces to an algebraic closure
  `k̄` through Lemma 0FVT, whose input is the base change isomorphism
  `k̄ ⊗_k H^*_{dR}(X/k) ≅ H^*_{dR}(X_{k̄}/k̄)` (`Stacks.WeilDeRham.deRhamFieldBaseChangeData`):
  `Stacks.WeilDeRham.traceAxiom_of_fieldBaseChange`.

Axiom (A9) is not needed: Proposition 0FIU
(`Stacks.WeilCohomology.WeilChernData.exists_weilCohomologyTheory`) uses only (A1) – (A8).

## Main results

* `Stacks.WeilDeRham.deRham_traceAxiom_of_isAlgClosed`: (A6) over an algebraically closed field
  of characteristic zero.
* `Stacks.WeilDeRham.deRham_traceAxiom`: **axiom (A6) for de Rham cohomology over any field of
  characteristic zero.**

## References

* [Stacks Project, Tag 0FWD](https://stacks.math.columbia.edu/tag/0FWD)
* [Stacks Project, Section 0FWC](https://stacks.math.columbia.edu/tag/0FWC)
* [Stacks Project, Section 0FID](https://stacks.math.columbia.edu/tag/0FID)
* [Stacks Project, Tag 0FVT](https://stacks.math.columbia.edu/tag/0FVT)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme

universe u

namespace Stacks.WeilDeRham

variable {k : Type u} [Field k]

/-- **Axiom (A6) for de Rham cohomology over an algebraically closed field of characteristic
zero** (Proposition 0FWD, "Proof of Axiom (A6)"): for every cohomological Chern character of the
de Rham data and every nonempty equidimensional `X`, there is `λ` with `(1 ⊗ λ)γ([Δ]) = 1`. -/
theorem deRham_traceAxiom_of_isAlgClosed [IsAlgClosed k] [CharZero k]
    {ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
      VectorBundleKZero ((toScheme k).obj X) → ∀ n : ℕ,
        tateTwist k (DeRhamWeil.deRhamFirstChernClassData k).tate
          ((DeRhamWeil.deRhamFirstChernClassData k).H X) n}
    (h : (DeRhamWeil.deRhamFirstChernClassData k).IsCohomologicalChernCharacter ch) :
    (DeRhamWeil.deRhamFirstChernClassData k).TraceAxiomFor (deRham_kunnethAxiom k)
      h.codimensionCycleClass :=
  traceAxiom_cycleClass_of_isAlgClosed h DeRhamWeil.coproductAxiom DeRhamWeil.pullbackAxiom
    deRham_projectiveBundleAxiom (deRham_kunnethAxiom k) (deRham_globalSectionsAxiom k)
    (deRham_finiteProjectionInjective k)

/-- **The de Rham data has a cohomological Chern character** (Tag 0FIE) over any field of
characteristic zero: (A1) – (A4) hold for it. -/
theorem exists_isCohomologicalChernCharacter_deRham (K : Type u) [Field K] [CharZero K] :
    ∃ ch, (DeRhamWeil.deRhamFirstChernClassData K).IsCohomologicalChernCharacter ch :=
  ((DeRhamWeil.deRhamFirstChernClassData K).existsUnique_isCohomologicalChernCharacter
    DeRhamWeil.coproductAxiom DeRhamWeil.pullbackAxiom deRham_projectiveBundleAxiom
    DeRhamWeil.divisorAxiom).exists

/-- **Axiom (A6) for de Rham cohomology** ([Stacks, Proposition 0FWD]): over a field `k` of
characteristic zero, for every cohomological Chern character of the de Rham data (Tag 0FIE), with
`γ` its cycle class map (Lemma 0FIF), every nonempty equidimensional smooth projective `X` of
dimension `d` has `λ : H^{2d}_{dR}(X/k)(d) ⟶ k` with `(1 ⊗ λ)γ([Δ]) = 1`. The source reduces to an
algebraic closure by Lemma 0FVT. -/
theorem deRham_traceAxiom [CharZero k]
    {ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
      VectorBundleKZero ((toScheme k).obj X) → ∀ n : ℕ,
        tateTwist k (DeRhamWeil.deRhamFirstChernClassData k).tate
          ((DeRhamWeil.deRhamFirstChernClassData k).H X) n}
    (h : (DeRhamWeil.deRhamFirstChernClassData k).IsCohomologicalChernCharacter ch) :
    (DeRhamWeil.deRhamFirstChernClassData k).TraceAxiomFor (deRham_kunnethAxiom k)
      h.codimensionCycleClass := by
  obtain ⟨ch', h'⟩ := exists_isCohomologicalChernCharacter_deRham (AlgebraicClosure k)
  exact traceAxiom_of_fieldBaseChange (deRhamFieldBaseChangeData k (AlgebraicClosure k))
    DeRhamWeil.coproductAxiom deRham_projectiveBundleAxiom DeRhamWeil.coproductAxiom
    deRham_projectiveBundleAxiom h h' (deRham_kunnethAxiom k)
    (deRham_kunnethAxiom (AlgebraicClosure k)) (deRham_traceAxiom_of_isAlgClosed h')

end Stacks.WeilDeRham

end
