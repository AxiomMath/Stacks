module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.FieldBaseChangeData
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.FiniteProjectionInjective
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.HodgeTrivialProjectiveBundle
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.KunnethAxiom
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.Blowup
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.DivisorAxiom
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.TraceAxiomAlgClosed
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.FieldBaseChangeDivisorTrace

/-!
# Axiom (A6) for Hodge cohomology

Remark 0FWE of the Stacks project says that Hodge cohomology `X ↦ H^*_{Hodge}(X/k)` with
`c₁^{Hodge}` (`Stacks.HodgeWeil.hodgeFirstChernClassData`) determines a Weil cohomology theory over
a field `k` of characteristic zero, "in exactly the same manner" as de Rham cohomology
(Proposition 0FWD). This file proves the axiom (A6) of Section 0FID, the trace, for every
cohomological Chern character of the Hodge data (Tag 0FIE), with `γ` its cycle class map of
Lemma 0FIF, following the proof of Proposition 0FWD:

* over an algebraically closed field, (A6) follows from (A1) – (A5), (A8) and (FIN) by
  `Stacks.WeilDeRham.traceAxiom_cycleClass_of_isAlgClosed`; (FIN), the injectivity of
  `f^*` for a finite syntomic `f : X ⟶ ℙ^d_k`, comes from the trace on differential forms
  (`Stacks.HodgeWeil.hodge_finiteProjectionInjective`);
* over any field of characteristic zero it descends from an algebraic closure by Lemma 0FVT
  (`Stacks.WeilDeRham.traceAxiom_of_fieldBaseChange`), whose comparison data
  (`Stacks.HodgeWeil.hodgeFieldBaseChangeData`) is flat base change for `H^q(X, Ω^p)`.

## Main results

* `Stacks.HodgeWeil.hodge_traceAxiom_of_isAlgClosed`: (A6) over an algebraically closed field of
  characteristic zero.
* `Stacks.HodgeWeil.exists_isCohomologicalChernCharacter_hodge`: the Hodge data has a
  cohomological Chern character.
* `Stacks.HodgeWeil.hodge_traceAxiom`: **axiom (A6) for Hodge cohomology over any field of
  characteristic zero.**

## References

* [Stacks Project, Tag 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
* [Stacks Project, Tag 0FWD](https://stacks.math.columbia.edu/tag/0FWD)
* [Stacks Project, Section 0FID](https://stacks.math.columbia.edu/tag/0FID)
* [Stacks Project, Tag 0FVT](https://stacks.math.columbia.edu/tag/0FVT)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme Stacks.WeilDeRham

universe u

namespace Stacks.HodgeWeil

variable (k : Type u) [Field k]

/-- **Axiom (A6) for Hodge cohomology over an algebraically closed field of characteristic zero**
(Remark 0FWE, read as Proposition 0FWD, "Proof of Axiom (A6)"): for every cohomological Chern
character of the Hodge data and every nonempty equidimensional `X`, there is `λ` with
`(1 ⊗ λ)γ([Δ]) = 1`. -/
theorem hodge_traceAxiom_of_isAlgClosed [IsAlgClosed k] [CharZero k]
    {ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
      VectorBundleKZero ((toScheme k).obj X) → ∀ n : ℕ,
        tateTwist k (hodgeFirstChernClassData k).tate ((hodgeFirstChernClassData k).H X) n}
    (h : (hodgeFirstChernClassData k).IsCohomologicalChernCharacter ch) :
    (hodgeFirstChernClassData k).TraceAxiomFor (hodge_kunnethAxiom k) h.codimensionCycleClass :=
  traceAxiom_cycleClass_of_isAlgClosed h (hodge_coproductAxiom k) (hodge_pullbackAxiom k)
    (hodge_projectiveBundleAxiom k) (hodge_kunnethAxiom k) (hodge_globalSectionsAxiom k)
    (hodge_finiteProjectionInjective k)

/-- **The Hodge data has a cohomological Chern character** (Tag 0FIE): (A1) – (A4) hold for it. -/
theorem exists_isCohomologicalChernCharacter_hodge (K : Type u) [Field K] [CharZero K] :
    ∃ ch, (hodgeFirstChernClassData K).IsCohomologicalChernCharacter ch :=
  ((hodgeFirstChernClassData K).existsUnique_isCohomologicalChernCharacter
    (hodge_coproductAxiom K) (hodge_pullbackAxiom K) (hodge_projectiveBundleAxiom K)
    (hodge_divisorAxiom K)).exists

/-- **Axiom (A6) for Hodge cohomology** ([Stacks, Remark 0FWE]): over a field `k` of characteristic
zero, for every cohomological Chern character of the Hodge data (Tag 0FIE), with `γ` its cycle
class map (Lemma 0FIF), every nonempty equidimensional smooth projective `X` of dimension `d` has
`λ : H^{2d}_{Hodge}(X/k)(d) ⟶ k` with `(1 ⊗ λ)γ([Δ]) = 1`. As for de Rham cohomology
(Section 0FWC) the proof reduces to an algebraic closure by Lemma 0FVT, flat base change for
`H^q(X, Ω^p)` providing its comparison data. -/
theorem hodge_traceAxiom [CharZero k]
    {ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
      VectorBundleKZero ((toScheme k).obj X) → ∀ n : ℕ,
        tateTwist k (hodgeFirstChernClassData k).tate ((hodgeFirstChernClassData k).H X) n}
    (h : (hodgeFirstChernClassData k).IsCohomologicalChernCharacter ch) :
    (hodgeFirstChernClassData k).TraceAxiomFor (hodge_kunnethAxiom k) h.codimensionCycleClass := by
  obtain ⟨ch', h'⟩ := exists_isCohomologicalChernCharacter_hodge (AlgebraicClosure k)
  exact traceAxiom_of_fieldBaseChange (hodgeFieldBaseChangeData k (AlgebraicClosure k))
    (hodge_coproductAxiom k) (hodge_projectiveBundleAxiom k) (hodge_coproductAxiom _)
    (hodge_projectiveBundleAxiom _) h h' (hodge_kunnethAxiom k)
    (hodge_kunnethAxiom (AlgebraicClosure k)) (hodge_traceAxiom_of_isAlgClosed _ h')

end Stacks.HodgeWeil

end
