module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaIsCtf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperDirectImageCtf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ConstructibilityUnconditional

/-!
# [Stacks, Tag 03V3]: the trace formula for `D_ctf`

Let `X` be a separated scheme of finite type over a finite field `k`, `Λ` a finite ring with
`#Λ ∈ k^*` and `K ∈ D_ctf(X, Λ)`. Then `RΓ_c(X_k̄, K) ∈ D_perf(Λ)` and
`∑_{x ∈ X(k)} Tr(π_x | K_x̄) = Tr(π_X^* | RΓ_c(X_k̄, K))`.

The proof in `Stacks.EtaleCohomology.TraceFormulaIsCtf` reduces to curves by the proper base
change theorem, using that `R π_*` preserves `D_ctf` along proper morphisms
(`Stacks.EtaleCohomology.ProperDirectImageCtfInput`). That input holds for every finite ring:
it is `Stacks.EtaleCohomology.isCtf_etaleModuleDerivedDirectImage_of_isProper` together with
the constructibility of `Rf_!` (Stacks 0GL0,
`Stacks.EtaleCohomology.lowerShriekConstructibilityInput`).

## Main results

* `properDirectImageCtfInput`: `R π_*` preserves `D_ctf` along proper morphisms with Noetherian
  target, for every finite ring `Λ`.
* `perfectDerivedTrace_canonicalCompactSupportFrobenius_eq_sum_of_isCtf_of_isSeparated`:
  [Stacks, Tag 03V3], the trace formula for `K ∈ D_ctf(X, Λ)` on a separated scheme of finite
  type over `k`.

## Implementation notes

The statements use the standard model `HasDerivedCategory.standard` of the derived category,
in which `perfectDerivedTrace` and `canonicalCompactSupportFrobenius` are defined.

## References

* [Stacks Project, Tag 03V3](https://stacks.math.columbia.edu/tag/03V3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.FilteredDerived Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

/-- **`R π_*` preserves `D_ctf` along proper morphisms**, for every finite ring `Λ`: for
`π : X ⟶ Y` proper with `Y` Noetherian, both in the big étale site `B`, and `K ∈ D⁺(X, Λ)` with
class in `D_ctf(X, Λ)`, the class of `R π_* K` lies in `D_ctf(Y, Λ)`. -/
theorem properDirectImageCtfInput (B : BigEtaleSite.{u}) (Λ : Type) [Ring Λ] [Finite Λ] :
    ProperDirectImageCtfInput B Λ :=
  fun π _ _ hX hY K hK => isCtf_etaleModuleDerivedDirectImage_of_isProper B π hX hY Λ
    (lowerShriekConstructibilityInput B) K hK

variable (Λ : Type) [Ring Λ] [Finite Λ] {k : Type u} [Field k] [Fintype k] (kbar : Type u)
  [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] [Algebra.IsAlgebraic k kbar] (p q : ℕ)
  [Fact p.Prime] [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q)
  (B : BigEtaleSite.{u})

variable {Λ kbar p q hcard B} in
/-- **[Stacks, Tag 03V3]: the trace formula for `D_ctf`.** Let `X` be a separated scheme of finite
type over the finite field `k` with `p ^ q` elements, lying in the big étale site `B`, with a
compactification `j : X ⟶ X̄` (which defines `RΓ_c`), and `k̄` an algebraic closure of `k`; let
`Λ` be a finite ring (possibly noncommutative) with `#Λ` invertible in `k`, and `K` a bounded
below complex of sheaves of `Λ`-modules on `X_étale` whose class lies in `D_ctf(X, Λ)`. Then
`RΓ_c(X_k̄, K)` is perfect, the stalks `K_x̄` at the rational points are perfect, and
`Tr(π_X^* | RΓ_c(X_k̄, K)) = ∑_{x ∈ X(k)} Tr(π_x | K_x̄)` in `Λ^♮`.

`X` is separated and of finite type over `k` as in the setting of Tag 03UG ("`X/k` as above"),
where `RΓ_c` is defined (Definition 03UT); the instance `Fintype (rationalPoints f)` always holds
(`Stacks.EtaleCohomology.finite_rationalPoints`). -/
@[stacks 03V3 "RGamma_c(X_kbar, K) is perfect and the trace formula, for K in D_ctf(X, Lambda)"]
theorem perfectDerivedTrace_canonicalCompactSupportFrobenius_eq_sum_of_isCtf_of_isSeparated
    (hΛ : (Nat.card Λ : k) ≠ 0) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f]
    [Fintype (rationalPoints f)] (J : CompactificationOf (Over.mk f))
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) (hX : B.Contains X)
    (hK : IsCtf B (B.obj X hX) Λ (DerivedCategory.Q.obj K.obj)) :
    ∃ (hKs : HasPerfectStalks Λ K) (hperf : StacksDraft.Perfect.IsPerfect
        (DerivedCategory.Plus.ι.obj (compactSupportFrobeniusCohomology.{u, 0} Λ f J kbar K))),
      perfectDerivedTrace Λ ⟨_, hperf⟩ (DerivedCategory.Plus.ι.map
          (canonicalCompactSupportFrobenius.{u, 0} Λ f J kbar p q hcard K)) =
        ∑ x : rationalPoints f, perfectDerivedTrace Λ ⟨_, hKs (rationalGeometricPoint kbar x.1)⟩
          (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} Λ kbar p q hcard x.1 K)) :=
  perfectDerivedTrace_canonicalCompactSupportFrobenius_eq_sum_of_isCtf_of_isSeparated_of_properDirectImageCtfInput
    hΛ (properDirectImageCtfInput B Λ) f J K hX hK

end Stacks.EtaleCohomology

end
