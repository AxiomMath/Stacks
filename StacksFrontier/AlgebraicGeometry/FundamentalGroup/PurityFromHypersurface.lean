module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalLefschetzSituation
public import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.BelowDepth

/-!
# Lifting purity from a hypersurface section: the depth reduction

In the local Lefschetz situation of [Stacks, Tag 0BLF] — a Noetherian local ring `(A, 𝔪)`, an
element `f ∈ 𝔪`, the spectra `X = Spec A` and `X₀ = Spec (A/fA)` and their punctured spectra `U`
and `U₀` — [Stacks, Lemma 0BLM] says that a finite étale cover `V → U` extends to a finite étale
cover of `X` as soon as `depth(A) ≥ 3` and the restriction of `V` to `U₀` already extends over
`X₀`.

The source proves this by reducing it to [Stacks, Lemma 0BLS], which has the same conclusion with
the depth hypothesis replaced by: some power of `f` annihilates `H^1_𝔪(A)`, and some power of `f`
annihilates `H^2_𝔪(A)`. That reduction is what this file contains, and it is complete: by
`Stacks.LocalCohomology.subsingleton_localCohomology_closedPoint_of_lt_depth`, depth at least
three makes both of those local cohomology modules trivial, so `f ^ 0 = 1` annihilates them.

## Main results

* `Stacks.FundamentalGroup.exists_finiteEtale_extension_of_restriction_extends_of_torsionCase` —
  **[Stacks, Lemma 0BLM] from [Stacks, Lemma 0BLS]**: the depth hypothesis of 0BLM implies the
  two torsion hypotheses of 0BLS, so 0BLS's conclusion transfers verbatim.

## Implementation notes

**No Stacks attribute is placed here.** [Stacks, Lemma 0BLS] is carried in this file as an
explicit hypothesis `hTorsionCase`, transcribed against the library's own names, so the declaration
below is a theorem about a hypothesis. Both tags are formalized unconditionally elsewhere:
[Stacks, Lemma 0BLS] is
`…LocalLefschetzSituation.exists_finiteEtale_extension_of_localCohomology_annihilated` and
[Stacks, Lemma 0BLM] is
`AlgebraicGeometry.LocalLefschetzSituation.exists_finiteEtale_extension_of_three_le_depth_self`,
both in the module
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.ExtensionFromHypersurface`.
That formalization of 0BLS states its hypothesis in the coreflection model
`Stacks.LocalCohomology.localCohomologyModule` of local cohomology; the two models agree over a
Noetherian ring by `Stacks.LocalCohomology.localCohomologyWithSupportInIsoLocalCohomologyModule`.

The two local cohomology modules are
`Stacks.LocalCohomology.localCohomologyWithSupportIn A {closedPoint A} (A[0]) i` for `i = 1, 2` —
the tag-0EF4 construction, i.e. the `i`-th cohomology of total right derived sections with
support at the closed point, applied to `A` placed in degree zero. The derived category of
`ModuleCat A` is taken at `HasDerivedCategory.standard`, which is forced: the model is baked into
the type of `Stacks.LocalCohomology.derivedSectionsWithSupportIn`, whose defining file pins it at
file level, so there is no free-model version of these modules to state instead.

### The rest of the chain

The source proves [Stacks, Lemma 0BLS] from the full faithfulness of restriction of finite étale
covers from `U` to `U₀` ([Stacks, Lemma 0BM6]), after reducing to the complete case
([Stacks, Lemma 0BLL]). That proof is carried out in the module
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.ExtensionFromHypersurface`.

## References

* [Stacks Project, Tag 0BLM](https://stacks.math.columbia.edu/tag/0BLM)
* [Stacks Project, Tag 0BLS](https://stacks.math.columbia.edu/tag/0BLS)
* [Stacks Project, Tag 0BLF](https://stacks.math.columbia.edu/tag/0BLF)
* [Stacks Project, Tag 0AVZ](https://stacks.math.columbia.edu/tag/0AVZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.FundamentalGroup

/-- **[Stacks, Lemma 0BLM] reduced to [Stacks, Lemma 0BLS].**

In the local Lefschetz situation `S`, let `V` be finite étale over the punctured spectrum `U`,
suppose `depth(A) ≥ 3`, and suppose the restriction of `V` to `U₀` extends to a finite étale
`Y₀ → X₀`. Then `V` extends to a finite étale cover of `X` — provided `hTorsionCase`, which is
[Stacks, Lemma 0BLS]: the same conclusion under the hypothesis that powers of `f` annihilate
`H^1_𝔪(A)` and `H^2_𝔪(A)`.

The reduction is that `depth(A) ≥ 3` makes both of those modules subsingletons, by
`Stacks.LocalCohomology.subsingleton_localCohomology_closedPoint_of_lt_depth`, so `f ^ 0`
annihilates each. -/
theorem exists_finiteEtale_extension_of_restriction_extends_of_torsionCase
    (S : LocalLefschetzSituation.{u})
    (hTorsionCase : ∀ (V : Scheme.{u}) (pi : V ⟶ S.U) [IsFinite pi] [Etale pi],
      (∃ n : ℕ, ∀ x : Stacks.LocalCohomology.localCohomologyWithSupportIn S.A
          {IsLocalRing.closedPoint S.A}
          ((DerivedCategory.singleFunctor (ModuleCat.{u} S.A) 0).obj (ModuleCat.of S.A S.A)) 1,
        S.f ^ n • x = 0) →
      (∃ n : ℕ, ∀ x : Stacks.LocalCohomology.localCohomologyWithSupportIn S.A
          {IsLocalRing.closedPoint S.A}
          ((DerivedCategory.singleFunctor (ModuleCat.{u} S.A) 0).obj (ModuleCat.of S.A S.A)) 2,
        S.f ^ n • x = 0) →
      ∀ (Y₀ : Scheme.{u}) (f₀ : Y₀ ⟶ S.X₀) [IsFinite f₀] [Etale f₀]
        (g₀ : pullback pi S.U₀ToU ⟶ Y₀),
        IsPullback (pullback.snd pi S.U₀ToU) g₀ S.U₀Open.ι f₀ →
        ∃ (Y : Scheme.{u}) (f : Y ⟶ S.X) (g : V ⟶ Y),
          IsFinite f ∧ Etale f ∧ IsPullback pi g S.UOpen.ι f)
    (V : Scheme.{u}) (pi : V ⟶ S.U) [IsFinite pi] [Etale pi]
    (hdepth : 3 ≤ Module.depth S.A (IsLocalRing.maximalIdeal S.A) S.A)
    (Y₀ : Scheme.{u}) (f₀ : Y₀ ⟶ S.X₀) [IsFinite f₀] [Etale f₀]
    (g₀ : pullback pi S.U₀ToU ⟶ Y₀)
    (h₀ : IsPullback (pullback.snd pi S.U₀ToU) g₀ S.U₀Open.ι f₀) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ S.X) (g : V ⟶ Y),
      IsFinite f ∧ Etale f ∧ IsPullback pi g S.UOpen.ι f := by
  have hdepth' : ((3 : ℕ) : ℕ∞) ≤ Module.depth S.A (IsLocalRing.maximalIdeal S.A) S.A := by
    exact_mod_cast hdepth
  have hsub : ∀ i : ℤ, i < 3 → Subsingleton
      (Stacks.LocalCohomology.localCohomologyWithSupportIn S.A
        {IsLocalRing.closedPoint S.A}
        ((DerivedCategory.singleFunctor (ModuleCat.{u} S.A) 0).obj (ModuleCat.of S.A S.A)) i) :=
    fun i hi ↦
      Stacks.LocalCohomology.subsingleton_localCohomology_closedPoint_of_lt_depth S.A 3
        hdepth' i (by exact_mod_cast hi)
  refine hTorsionCase V pi ?_ ?_ Y₀ f₀ g₀ h₀ <;>
    exact ⟨0, fun x ↦ by simpa using (hsub _ (by norm_num)).elim x 0⟩

end Stacks.FundamentalGroup

end
