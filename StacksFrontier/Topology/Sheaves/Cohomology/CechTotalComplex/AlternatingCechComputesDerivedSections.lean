module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.AlternatingBoundedComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.AlternatingLimitComparison
import StacksCore.Tactic.StacksAttribute

/-!
# A basis of acyclics makes the alternating Čech complex compute derived global sections

Let `(X, O_X)` be a ringed space, let `U : I → Opens X` be a *finite* open covering of `X` and
let `F^•` be an arbitrary complex of `O_X`-modules. Let `B` be a set of open subsets of `X`
such that

1. every open of `X` is a union of members of `B`,
2. every finite intersection `U_{i_0 … i_p}` of members of the covering lies in `B`, and
3. for every `W ∈ B` and every `p > 0` the groups `H^p(W, F^q)`,
   `H^p(W, Coker(F^{q-1} → F^q))` and `H^p(W, H^q(F))` vanish.

Then the comparison map

`Tot(Č_alt^•(U, F^•)) ⟶ RΓ(X, F^•)`

of Tag 08C1 is an isomorphism in `D(Ab)`.

## Main results

* `Stacks.Cech.isIso_alternatingCechToDerivedComparison_of_acyclicBasis`:
  **[Stacks, Tag 08C2]**.

## Implementation notes

The proof assembles three steps proved in the imported modules.

The complex `F^•` is unbounded, so the resolution computing `RΓ(X, F^•)` is the functorial
K-injective resolution of Tag 079P, as in Tag 08C1. Stacks argues instead with the
candidate K-injective resolution `F^• ⟶ lim_n I_n` of Tag 071A, whose `n`-th stage resolves the
canonical truncation `τ_{≥ -n} F^•` by a bounded below complex of injectives. Such a resolution
exists for every complex (`Stacks.KInjective.nonempty_candidateKInjectiveResolution`), so one is
chosen here and the two resolutions are reconciled inside
`isIso_alternatingCechToDerivedComparison_of_stages`, both being K-injective.

Condition (3)(c) is what makes the candidate resolution an actual resolution, by Tag 071B;
conditions (3)(a) and (3)(b) are what make each stage map a quasi-isomorphism after taking
total alternating Čech complexes, by `quasiIso_alternatingCechTotalMap_candidateStage` — (3)(b)
enters because the degree `-n` term of `τ_{≥ -n} F^•` is a cokernel of a differential of `F^•`
rather than a term of `F^•`. Condition (1) is `Opens.IsBasis`, which is the hypothesis of
Tag 071B, and condition (2) is what lets (3)(a) and (3)(b) be used at the intersections the
Čech complex is built from.

The vanishing hypotheses are stated with the right derived functors of the module-valued
sections functor `SheafOfModules.evaluation`, as in Tag 01ET; this is the form the imported
results and Tag 071B use. The common universe is the one the total Čech complex API is stated
at.

## References

* [Stacks Project, Tag 08C2](https://stacks.math.columbia.edu/tag/08C2)
* [Stacks Project, Tag 08C1](https://stacks.math.columbia.edu/tag/08C1)
* [Stacks Project, Tag 071A](https://stacks.math.columbia.edu/tag/071A)
* [Stacks Project, Tag 071B](https://stacks.math.columbia.edu/tag/071B)
* [Stacks Project, Tag 01ET](https://stacks.math.columbia.edu/tag/01ET)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace

universe u

namespace Stacks.Cech

noncomputable section

variable (X : TopCat.{u})

attribute [local instance] additive_sheafOfModulesEvaluation

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat]

attribute [local instance] HasDerivedCategory.standard

variable (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- **[Stacks, Tag 08C2]** Let `(X, O_X)` be a ringed space, let `U : I → Opens X` be a finite
open covering of `X` and let `F^•` be a complex of `O_X`-modules. Let `B` be a set of open
subsets of `X` such that every open of `X` is a union of members of `B`, such that every finite
intersection of members of the covering lies in `B`, and such that for every `W ∈ B` and every
`p > 0` the cohomology groups `H^p(W, F^q)`, `H^p(W, Coker(F^{q-1} → F^q))` and
`H^p(W, H^q(F))` all vanish. Then the comparison map
`Tot(Č_alt^•(U, F^•)) ⟶ RΓ(X, F^•)` of Tag 08C1 is an isomorphism in `D(Ab)`. -/
@[stacks 08C2]
theorem isIso_alternatingCechToDerivedComparison_of_acyclicBasis
    {I : Type u} [Finite I] (U : I → Opens X) (hU : (⊤ : Opens X) = iSup U)
    (F : CochainComplex (SheafOfModules.{u} R) ℤ)
    (B : Set (Opens X)) (hB : Opens.IsBasis B)
    (h_inter : ∀ (p : ℕ) (s : Fin (p + 1) → I), (⨅ k, U (s k)) ∈ B)
    (h_terms : ∀ W ∈ B, ∀ (q : ℤ) (p : ℕ), 0 < p →
      IsZero (((SheafOfModules.evaluation R (op W)).rightDerived p).obj (F.X q)))
    (h_cokernels : ∀ W ∈ B, ∀ (q : ℤ) (p : ℕ), 0 < p →
      IsZero (((SheafOfModules.evaluation R (op W)).rightDerived p).obj
        (cokernel (F.d (q - 1) q))))
    (h_homology : ∀ W ∈ B, ∀ (q : ℤ) (p : ℕ), 0 < p →
      IsZero (((SheafOfModules.evaluation R (op W)).rightDerived p).obj (F.homology q))) :
    IsIso ((alternatingCechToDerivedComparison X R U hU).app F) := by
  obtain ⟨C⟩ := Stacks.KInjective.nonempty_candidateKInjectiveResolution R F
  exact isIso_alternatingCechToDerivedComparison_of_stages X R U hU F B hB h_homology C
    fun n ↦ quasiIso_alternatingCechTotalMap_candidateStage X R U hU F C B h_inter
      h_terms h_cokernels n

end

end Stacks.Cech

end
