module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaAnyDimensionOfCurves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaCtf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DirectImageCtf

/-!
# The trace formula in any dimension

[Stacks, Tag 03UI] (1): the trace formula of [Stacks, Tag 03UG] holds in any dimension. Let `k`
be a finite field with `p ^ q` elements, `X` a separated scheme of finite type over `k` (of
arbitrary dimension), `Λ` a finite ring whose cardinality is prime to that of `k` and
`K ∈ D_ctf(X, Λ)`. Then for every compactification `j : X ⟶ X̄` over `k`,
`RΓ_c(X_k̄, K) = RΓ(X̄_k̄, (j_! K)|)` and the stalks `K_x̄` at the rational points are perfect, and

`Tr(π_X^* | RΓ_c(X_k̄, K)) = ∑_{x ∈ X(k)} Tr(π_x | K_x̄)` in `Λ^natural`.

The proof is the source's dévissage: induction on `dim X`; a dense affine open `U` fibred in
curves over `𝔸^{d-1}_k` (Noether normalization); the open/closed dévissage; and the fibration step,
which uses proper base change, the independence of the compactification (Tag 0F7I) and the
preservation of `D_ctf` under proper direct images; the curve case is Tag 03UG.

## Implementation notes

`Λ : Type` (universe 0): the coefficient sheaves are `EtaleModules.{u, 0} Λ X`, as in item (2) of
this remark and in Tags 03VK and 03VL. The frame of Tag 03UG on which the induction starts is at
this universe; every finite ring is isomorphic to one in `Type`, so this is no loss of generality.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

-- the model in which `IsCtf` and `CanonicalTraceFormula` are defined (at default priority)
attribute [local instance] HasDerivedCategory.standard

/-- **The trace formula in any dimension ([Stacks, Tag 03UI] (1)).** Let `k` be a finite field
with `p ^ q` elements and `k̄` an algebraic closure, `X` a separated scheme of finite type over `k`
of any dimension, `Λ` a finite ring whose cardinality is prime to that of `k`, and
`K ∈ D_ctf(X, Λ)`. Then for every compactification `j : X ⟶ X̄` over `k`, the complex
`RΓ_c(X_k̄, K) = RΓ(X̄_k̄, (j_! K)|_{X̄_k̄})` and the stalks `K_x̄` at the rational points are
perfect, and `Tr(π_X^* | RΓ_c(X_k̄, K)) = ∑_{x ∈ X(k)} Tr(π_x | K_x̄)` in `Λ^natural`, for the
canonical Frobenius actions (`Stacks.EtaleCohomology.CanonicalTraceFormula`). The coefficient
ring is in `Type` (see the module docstring). -/
@[stacks 03UI "(1): the trace formula in any dimension: Tag 03UG for `X` separated of finite type
over `k` with no bound on its dimension, through every compactification. `Λ : Type` (universe 0),
see the module docstring."]
theorem canonicalTraceFormula_of_isCtf (B : BigEtaleSite.{u}) (Λ : Type) [Ring Λ] [Finite Λ]
    {k : Type u} [Field k] [Fintype k] (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
    [Algebra k kbar] [Algebra.IsAlgebraic k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
    [CharP kbar p] (hcard : Fintype.card k = p ^ q)
    (hcop : Nat.Coprime (Nat.card Λ) (Fintype.card k))
    (X : B.Scheme) (f : X.obj ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X.obj))
    (hK : IsCtf B X Λ (DerivedCategory.Q.obj K.obj)) (j : CompactificationOf (Over.mk f)) :
    CanonicalTraceFormula Λ kbar p q hcard f j K :=
  canonicalTraceFormula_of_directImagePreservesCtf B Λ kbar p q hcard hcop
    (directImagePreservesCtf B Λ k hcop) X f K hK j

end Stacks.EtaleCohomology

end
