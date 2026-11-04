module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaLisseSmoothCurve
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaSmoothCurveReduction
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ProjectiveCompletion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase

/-!
# The trace formula for curves

[Stacks, Tag 03UG]: let `k` be a finite field and `X` a finite type, separated scheme of
dimension at most `1` over `k`. Let `Λ` be a finite ring whose cardinality is prime to that of
`k`, and `K ∈ D_ctf(X, Λ)`. Then

`Tr(π_X^* | RΓ_c(X_k̄, K)) = ∑_{x ∈ X(k)} Tr(π_x | K_x̄)`

in `Λ^♮`.

Here `RΓ_c(X_k̄, K)` is computed through a compactification `j : X ⟶ X̄` over `k` as
`RΓ(X̄_k̄, (j_! K)|_{X̄_k̄})`, with the canonical action of `π_X^*`; every `X` as above has a
compactification (Tag 0BXV,
`Stacks.CurveProjectiveCompletion.exists_projective_completion_of_dimension_le_one`)
and the formula holds through all of them (`Stacks.EtaleCohomology.CanonicalTraceFormula`, which
also asserts the perfectness of `RΓ_c(X_k̄, K)` and of the stalks that the traces need).

The proof follows the source. Step 2 (dimension zero) is
`Stacks.EtaleCohomology.traceFormulaUpToDim_zero`; Steps 1 and 3 (dévissage to a smooth curve
without rational points carrying a bounded complex of lisse sheaves) are
`Stacks.EtaleCohomology.traceFormulaUpToDim_one_of_smoothCurve`; Steps 3–9 on that curve (the
primary decomposition of `Λ`, Galois descent `ℱ ≅ Hom_{A[H]}(M^*, f_* A)`, the change of
coefficients of Step 7 and the vanishing of the conjugacy traces, Steps 8 and 9, through Weil's
trace formula) are `Stacks.EtaleCohomology.canonicalTraceFormula_of_lisse_smoothCurve`.

## Main results

* `Stacks.EtaleCohomology.traceFormulaUpToDim_one`: the trace formula up to dimension one.
* `Stacks.EtaleCohomology.exists_compactification_and_traceFormulaUpToDim_one`: [Stacks, Tag 03UG].

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- **The trace formula up to dimension one**: for a finite field `k`, an algebraic closure `k̄`
of `k` and a finite ring `Λ` whose cardinality is prime to that of `k`, the trace formula
`Tr(π_X^* | RΓ_c(X_k̄, K)) = ∑_{x ∈ X(k)} Tr(π_x | K_x̄)` holds for every separated scheme `X` of
finite type over `k` of dimension at most one, every compactification of `X` and every
`K ∈ D_ctf(X, Λ)`. -/
theorem traceFormulaUpToDim_one (B : BigEtaleSite.{u}) (Λ : Type) [Ring Λ] [Finite Λ]
    {k : Type u} [Field k] [Fintype k] (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
    [Algebra k kbar] [Algebra.IsAlgebraic k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
    [CharP kbar p] (hcard : Fintype.card k = p ^ q)
    (hcop : Nat.Coprime (Nat.card Λ) (Fintype.card k)) :
    TraceFormulaUpToDim B Λ kbar p q hcard 1 :=
  traceFormulaUpToDim_one_of_smoothCurve fun _U pU _ _ _ J K a b _ _ hK =>
    canonicalTraceFormula_of_lisse_smoothCurve pU kbar p q hcard hcop J K a b hK

/-- **[Stacks, Tag 03UG]: the trace formula for curves.** Let `k` be a finite field with
`#k = p ^ q`, `k̄` an algebraic closure of `k`, and `Λ` a finite ring whose cardinality is prime
to that of `k`. Every separated scheme `X` of finite type over `k` of dimension at most one has a
compactification over `k`, and for every compactification `j` of `X` and every
`K ∈ D_ctf(X, Λ)`, `RΓ_c(X_k̄, K)` (computed through `j`) and the stalks `K_x̄` at the rational
points are perfect and

`Tr(π_X^* | RΓ_c(X_k̄, K)) = ∑_{x ∈ X(k)} Tr(π_x | K_x̄)`

in `Λ^♮`. -/
@[stacks 03UG]
theorem exists_compactification_and_traceFormulaUpToDim_one (B : BigEtaleSite.{u}) (Λ : Type)
    [Ring Λ] [Finite Λ] {k : Type u} [Field k] [Fintype k] (kbar : Type u) [Field kbar]
    [IsAlgClosed kbar] [Algebra k kbar] [Algebra.IsAlgebraic k kbar] (p q : ℕ) [Fact p.Prime]
    [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q)
    (hcop : Nat.Coprime (Nat.card Λ) (Fintype.card k)) :
    (∀ (X : B.Scheme) (f : X.obj ⟶ Spec (.of k)) [QuasiCompact f] [LocallyOfFiniteType f]
      [IsSeparated f], topologicalKrullDim X.obj ≤ ((1 : ℕ) : WithBot ℕ∞) →
      Nonempty (CompactificationOf (Over.mk f))) ∧
    TraceFormulaUpToDim B Λ kbar p q hcard 1 := by
  refine ⟨fun X f _ _ _ hX => ?_, traceFormulaUpToDim_one B Λ kbar p q hcard hcop⟩
  obtain ⟨Y, q', j, hj, hjq, hproj, -, -, -, -⟩ :=
    Stacks.CurveProjectiveCompletion.exists_projective_completion_of_dimension_le_one k f
      (by exact_mod_cast hX)
  have := hj
  have : IsProper q' := isProper_of_isProjectiveMorphism q' hproj
  exact ⟨⟨StructuredArrow.mk (Y := Over.mk q') (Over.homMk (U := Over.mk f) j hjq),
    ⟨inferInstanceAs (IsOpenImmersion j), inferInstanceAs (IsProper q')⟩⟩⟩

end Stacks.EtaleCohomology

end
