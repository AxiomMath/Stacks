module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DirectImageCtf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaFibration
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaLisseSmoothCurve
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaSmoothCurveReduction
public import StacksFrontier.AlgebraicGeometry.NagataCompactification.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The trace formula for `D_ctf` in any dimension

Let `k` be a finite field, `X` a separated scheme of finite type over `k`, `Λ` a finite ring
(not necessarily commutative) with `#Λ` invertible in `k`, and `K ∈ D_ctf(X, Λ)`. Then
`RΓ_c(X_k̄, K)` is a perfect complex of `Λ`-modules and

`∑_{x ∈ X(k)} Tr(π_x | K_x̄) = Tr(π_X^* | RΓ_c(X_k̄, K))`

in `Λ^natural = Λ / [Λ, Λ]` ([Stacks, Tag 03V3]).

## The objects

* `RΓ_c(X_k̄, K)` is `Stacks.EtaleCohomology.compactSupportFrobeniusCohomology`, the complex
  `RΓ(X̄_k̄, (j_! K)|_{X̄_k̄})` for a compactification `j : X ⟶ X̄` of `X` over `k`; such a
  compactification exists by Nagata's theorem
  (`AlgebraicGeometry.hasCompactification_of_compactSpace_quasiSeparatedSpace`, Tag 0F41), and the
  statement holds for every one of them.
* `π_X^*` is its canonical Frobenius endomorphism
  `Stacks.EtaleCohomology.canonicalCompactSupportFrobenius`, and the right hand side is its trace
  `Stacks.EtaleCohomology.canonicalCompactSupportLefschetzNumber`.
* `K_x̄` is the stalk at the geometric point over the rational point `x`, with the geometric
  Frobenius `π_x` acting on it (`Stacks.EtaleCohomology.rationalPointStalkFrobenius`).
* `K ∈ D_ctf(X, Λ)` is `Stacks.EtaleCohomology.IsCtf` (a bounded below complex of étale sheaves of
  `Λ`-modules whose class lies in `D_ctf`; every object of `D_ctf` is bounded, so is the class of
  such a complex).

## The proof

As in the source: the case `dim X ≤ 1` (Tag 03UG), here
`Stacks.EtaleCohomology.traceFormulaUpToDim_one_of_smoothCurve` (Steps 1–3, the dévissage to a
bounded complex of lisse sheaves on a smooth curve without rational points) together with
`Stacks.EtaleCohomology.canonicalTraceFormula_of_lisse_smoothCurve` (Steps 4–9); and the
induction on `dim X` by proper base change along a curve fibration `U ⟶ 𝔸^{n}_k` of a dense
open `U` (`Stacks.EtaleCohomology.canonicalTraceFormula_of_curves`), which needs proper direct
images along curve fibrations to preserve `D_ctf`
(`Stacks.EtaleCohomology.directImagePreservesCtf`: constructibility by Tag 0GL0, boundedness, and
perfect stalks by proper base change, assembled by Tag 03TT).

## Implementation notes

`Λ : Type` (universe 0), as for the coefficient sheaves `EtaleModules.{u, 0} Λ X` of the curve
case; every finite ring is isomorphic to one in `Type`.

## References

* [Stacks Project, Tag 03V3](https://stacks.math.columbia.edu/tag/03V3)
* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.FilteredDerived

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- **The trace formula ([Stacks, Tag 03V3]).** Let `k` be a finite field with `p ^ q` elements and
`k̄` an algebraic closure of `k`, let `X` be a separated scheme of finite type over `k` (of any
dimension), let `Λ` be a finite ring whose cardinality is invertible in `k`, and let
`K ∈ D_ctf(X, Λ)`. Then `X` has a compactification over `k`, and for every compactification
`j : X ⟶ X̄` the complex `RΓ_c(X_k̄, K) = RΓ(X̄_k̄, (j_! K)|_{X̄_k̄})` lies in `D_perf(Λ)`, and

`∑_{x ∈ X(k)} Tr(π_x | K_x̄) = Tr(π_X^* | RΓ_c(X_k̄, K))`

in `Λ^natural`, where the stalks `K_x̄` at the rational points are perfect (so that their traces
are defined), `π_x` is the geometric Frobenius acting on `K_x̄` and `π_X^*` is the canonical
Frobenius action on `RΓ_c(X_k̄, K)`. -/
@[stacks 03V3 "`Λ : Type` (universe 0); X in a big étale site; K ∈ D_ctf(X, Λ) represented by a \
bounded below complex; RΓ_c(X_k̄, K) through any compactification (one exists by 0F41)",
  sga "4½ Rapport 4.10" "special case",
  sga "4½ Rapport 5.13" "more general"]
theorem isPerfect_compactSupport_and_sum_stalkTrace_eq_compactSupportLefschetzNumber
    (B : BigEtaleSite.{u}) (Λ : Type) [Ring Λ] [Finite Λ]
    {k : Type u} [Field k] [Fintype k] (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
    [Algebra k kbar] [Algebra.IsAlgebraic k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
    [CharP kbar p] (hcard : Fintype.card k = p ^ q)
    (hcop : Nat.Coprime (Nat.card Λ) (Fintype.card k))
    (X : B.Scheme) (f : X.obj ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X.obj))
    (hK : IsCtf B X Λ (DerivedCategory.Q.obj K.obj)) :
    Nonempty (CompactificationOf (Over.mk f)) ∧
      ∀ j : CompactificationOf (Over.mk f),
        StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
          (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar K)) ∧
        ∃ (hX : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
            (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar K)))
          (hs : ∀ x : rationalPoints f, StacksDraft.Perfect.IsPerfect
            (DerivedCategory.Q.obj (rationalPointStalkComplex.{u, 0} Λ kbar x.1 K))),
          ∑ᶠ x : rationalPoints f, perfectDerivedTrace Λ ⟨_, hs x⟩
              (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} Λ kbar p q hcard x.1 K)) =
            canonicalCompactSupportLefschetzNumber.{u, 0} Λ f j kbar p q hcard K hX := by
  refine ⟨?_, fun j => ?_⟩
  · obtain ⟨j, -⟩ := hasCompactification_of_compactSpace_quasiSeparatedSpace f
    exact ⟨j⟩
  obtain ⟨hX, hs, heq⟩ := canonicalTraceFormula_of_curves kbar p q hcard
    (directImagePreservesCtf B Λ k hcop)
    (traceFormulaUpToDim_one_of_smoothCurve fun U pU _ _ _ J K a b _ _ hK =>
      canonicalTraceFormula_of_lisse_smoothCurve pU kbar p q hcard hcop J K a b hK)
    X f j K hK
  exact ⟨hX, hX, hs, heq.symm⟩

end Stacks.EtaleCohomology

end
