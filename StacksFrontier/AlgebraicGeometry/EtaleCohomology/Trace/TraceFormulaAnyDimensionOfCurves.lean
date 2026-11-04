module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaFibration
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaCtf

/-!
# The trace formula in any dimension, from the curve case

Let `k` be a finite field with `p ^ q` elements, `X` a separated scheme of finite type over `k` of
arbitrary dimension, `Λ` a finite ring whose cardinality is prime to that of `k` and
`K ∈ D_ctf(X, Λ)`. If proper direct images of extensions by zero along curve fibrations preserve
`D_ctf` (`Stacks.EtaleCohomology.DirectImagePreservesCtf`), then for every compactification of `X`
the trace formula `Tr(π_X^* | RΓ_c(X_k̄, K)) = ∑_{x ∈ X(k)} Tr(π_x | K_x̄)` holds. The curve case
is `Stacks.EtaleCohomology.traceFormulaUpToDim_one` ([Stacks, Tag 03UG]). This is the assembly
of item (1) of [Stacks, Tag 03UI].

## Main results

* `Stacks.EtaleCohomology.canonicalTraceFormula_of_directImagePreservesCtf`.

## Implementation notes

`Λ : Type` (universe 0): the coefficient sheaves are `EtaleModules.{u, 0} Λ X`, as for the curve
case `Stacks.EtaleCohomology.traceFormulaUpToDim_one` on which the induction starts.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- **The trace formula in any dimension, given `D_ctf` of proper direct images along curve
fibrations.** For `X` separated of finite type over a finite field `k`, a finite ring `Λ` of
cardinality prime to that of `k`, `K ∈ D_ctf(X, Λ)` and any compactification `j` of `X` over `k`,
the trace formula holds. -/
theorem canonicalTraceFormula_of_directImagePreservesCtf (B : BigEtaleSite.{u}) (Λ : Type)
    [Ring Λ] [Finite Λ] {k : Type u} [Field k] [Fintype k] (kbar : Type u) [Field kbar]
    [IsAlgClosed kbar] [Algebra k kbar] [Algebra.IsAlgebraic k kbar] (p q : ℕ) [Fact p.Prime]
    [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q)
    (hcop : Nat.Coprime (Nat.card Λ) (Fintype.card k)) (hCTF : DirectImagePreservesCtf B Λ k)
    (X : B.Scheme) (f : X.obj ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X.obj))
    (hK : IsCtf B X Λ (DerivedCategory.Q.obj K.obj)) (j : CompactificationOf (Over.mk f)) :
    CanonicalTraceFormula Λ kbar p q hcard f j K :=
  canonicalTraceFormula_of_curves kbar p q hcard hCTF
    (traceFormulaUpToDim_one B Λ kbar p q hcard hcop) X f j K hK

end Stacks.EtaleCohomology

end
