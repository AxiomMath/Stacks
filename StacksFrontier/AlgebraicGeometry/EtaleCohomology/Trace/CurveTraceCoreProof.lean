module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTraceCorePrimary
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RegularDescentHomPerfect
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveLAdicTraceFormulaInputs

/-!
# The core of the proof of Tag 03UG

For every finite ring `Λ` with `#Λ ∈ k^*`, possibly noncommutative, every smooth connected affine
curve `U` over a finite field `k` without `k`-rational points and every locally constant sheaf `F`
of `Λ`-modules on `U_étale` with finite projective values, `RΓ_c(U_k̄, F)` is perfect and
`Tr(π_U^* | RΓ_c(U_k̄, F)) = 0` in `Λ^♮` (`Stacks.EtaleCohomology.curveTraceCore`).

Consequently the trace formula of [Stacks, Tag 03V2] holds on smooth curves over the extensions
of `k` (`Stacks.EtaleCohomology.lisseCurveTraceFormulaInput`,
`Stacks.EtaleCohomology.curveTraceFormulaInput`).

## Main results

* `Stacks.EtaleCohomology.curveTraceCore`
* `Stacks.EtaleCohomology.lisseCurveTraceFormulaInput`
* `Stacks.EtaleCohomology.curveTraceFormulaInput`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius CategoryTheory.FilteredDerived
open MonoidAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.EtaleCohomology

/-- **The core of the proof of [Stacks, Tag 03UG]**: for a finite ring `Λ`, possibly
noncommutative, with `#Λ` invertible in the finite field `k`, an algebraic closure `k̄` of `k`, a
smooth connected affine curve `U` over `k` without `k`-rational points, a compactification of `U`
and a locally constant sheaf `F` of `Λ`-modules on `U_étale` with finite projective values,
`RΓ_c(U_k̄, F)` is perfect and `Tr(π_U^* | RΓ_c(U_k̄, F)) = 0`. -/
theorem curveTraceCore (Λ : Type) [Ring Λ] [Finite Λ] (k : Type u) [Field k] [Fintype k]
    (hΛ : (Nat.card Λ : k) ≠ 0) (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar]
    [Algebra.IsAlgebraic k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p]
    (hcard : Fintype.card k = p ^ q) : CurveTraceCore Λ k hΛ kbar p q hcard := by
  intro U fU _ _ _ _ _ _ _ _ J F hF
  refine compactSupportTraceVanishes_of_forall_primary fU J kbar p q hcard ?_ Λ hΛ F hF
  intro Λ' _ _ ℓ m _ hℓ hm F' hF'
  refine compactSupportTraceVanishes_of_primary fU J kbar p q hcard ℓ m hℓ Λ' hm ?_ F' hF'
  intro H _ _ G _ _ n hn _ N _ _ _ _ _ _ _ ρ
  have : ConnectedSpace ((𝟭 Scheme).obj G.cover.left) :=
    inferInstanceAs (ConnectedSpace G.cover.left)
  have : NeZero (ℓ ^ n) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  exact ⟨isPerfect_compactSupportFrobeniusCohomology_regularDescentSheaf J G kbar ℓ n hn,
    isPerfect_compactSupportFrobeniusCohomology_etaleModuleHom_regularDescentSheaf J G kbar ℓ n
      (dualRepModule (A := ZMod (ℓ ^ n)) ρ) (moduleFinite_dualRepModule (n := ℓ ^ n) ρ)
      (dualRepRightAction (A := ZMod (ℓ ^ n)) ρ) (dualRepRightAction_algebraMap ρ)
      (preservesFiniteProjective_homFunctor (n := ℓ ^ n) ρ) hn,
    perfectDerivedTrace_canonicalCompactSupportFrobenius_etaleModuleHom_regularDescentSheaf J G
      kbar ℓ n (dualRepModule (A := ZMod (ℓ ^ n)) ρ) (moduleFinite_dualRepModule (n := ℓ ^ n) ρ)
      (dualRepRightAction (A := ZMod (ℓ ^ n)) ρ) (dualRepRightAction_algebraMap ρ)
      (preservesFiniteProjective_homFunctor (n := ℓ ^ n) ρ) hn p q hcard⟩

/-- **The trace formula for a lisse sheaf on a smooth curve over the extensions of `k`**
(`Stacks.EtaleCohomology.LisseCurveTraceFormulaInput`, Tag 03V2 on curves over `k_N`). -/
theorem lisseCurveTraceFormulaInput : LisseCurveTraceFormulaInput.{u} :=
  lisseCurveTraceFormulaInput_of_curveTraceCore
    fun Λ _ _ k _ _ hΛ kbar _ _ _ _ p q _ _ _ hcard => curveTraceCore Λ k hΛ kbar p q hcard

/-- **The trace formula for the sheaf `ℱ_τ` of a representation on a smooth curve**
(`Stacks.EtaleCohomology.CurveTraceFormulaInput`, Tag 03V2 on curves over `k_N`). -/
theorem curveTraceFormulaInput : CurveTraceFormulaInput.{u} :=
  curveTraceFormulaInput_of_curveTraceCore
    fun Λ _ _ k _ _ hΛ kbar _ _ _ _ p q _ _ _ hcard => curveTraceCore Λ k hΛ kbar p q hcard

end Stacks.EtaleCohomology

end
