module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsThickening
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleSpacePullback.Pushforward

/-!
# The comparison along the base-change immersion is compatible with the connecting morphisms

`Deformation.Artin.SectionsSheaf.baseChangeCohomologyIso` identifies the cohomology on `W_{T'}`
of a sheaf of modules with the cohomology on `W_T` of its pushforward along the base-change
immersion `i : W_{T'} → W_T`, degreewise and naturally in the module. It says nothing about the
connecting morphisms of the two long exact sequences, and an unconstrained degreewise family
cannot be made to.

This file supplies the δ-compatible comparison at that immersion, by instantiating
`Stacks.Cohomology.ModulePushforwardDelta` — which compares cohomology along the **direct**
image and needs only that `i_*` be exact — at `f := i` and `V := ⊤`. Exactness of `i_*` is
discharged from the closed-immersion hypothesis that the section already carries, by
`Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward_of_isClosedImmersion`.

## Main definitions and results

* `Deformation.Artin.SectionsSheaf.baseChangeCohomologyComparison` — the degree-`n` comparison
  `Hⁿ(W_T, i_* G) ⟶ Hⁿ(W_{T'}, G)`, with `isIso_baseChangeCohomologyComparison`.
* `Deformation.Artin.SectionsSheaf.baseChangeCohomologyComparison_comp_δ` — **it commutes with
  the connecting morphisms.**
* `Deformation.Artin.SectionsSheaf.baseChangeCohomologyDeltaIso` — the comparison as an
  isomorphism of δ-functors, in the `Γ(i⁻¹V, −) ⋙ restrictScalars` spelling.

## Why here, and not inside `obstructionMap`

The obvious place to put a δ-compatible comparison is the second factor of
`Deformation.Artin.SectionsSheaf.obstructionMap`, in place of
`Stacks.Cohomology.moduleCohomologyPullbackMap`. **That would weaken `obstructionMap`.**
`obstructionMap` is clause (2) of Stacks 07YG for an *arbitrary* ring map
`ψ : A → A₁` over `S`, and `Spec ψ` is a closed immersion only when `ψ` is surjective; at the
morphism `obstructionMap` actually uses, instance search reports

```
failed to synthesize instance of type class
  PreservesFiniteColimits (modulePushforward (… (baseChangeMap q (quotHom ψ t))))
```

so the substitution is available only after adding `IsClosedImmersion (baseChangeMap q
(quotHom ψ t))` as a hypothesis. The thickening of this development is the *other* morphism —
the one a deformation situation `A' → A` produces, which is where
`Deformation.Artin.SectionsSheaf.baseChangeCohomologyIso` lives and where the hypothesis is
already present. So the δ-compatible comparison is proved here, at full strength, and
`obstructionMap` keeps its generality.

## What is not claimed

* This does **not** prove that `Stacks.Cohomology.moduleCohomologyPullbackMap`, or
  `baseChangeCohomologyIso`, is δ-compatible. Those are comparisons built by other routes and
  the identification of any of them with `baseChangeCohomologyComparison` is a separate
  statement, deliberately not asserted here.
* The degree-`n` component is **not** claimed to agree with any derived-category comparison for
  `n > 0`: [Stacks, Tag 010U] pins degree zero only. For a positive-degree *formula* the
  derived-category comparison is what one wants; for *δ-compatibility* it is this.
* This is **not** applicable to the sheaf-level sequence of clause (2), and so is not an input
  to `obs_naturality` of [Stacks, Tag 07YG]. `baseChangeCohomologyComparison_comp_δ` compares
  the connecting morphisms at a short exact sequence `Sq` of modules on `W_{T'}` with those at
  its direct image `i_* Sq`; the sequence of clause (2),
  `0 → 𝓕_{A'} ⊗_{A'} I → 𝓕_{A'} → 𝓕_{A'} ⊗_{A'} A → 0`, lives on `W_{A'} = W_T` and is **not**
  the direct image of any sequence on `W_A`, not even up to isomorphism: its middle term
  `𝓕_{A'}` is not a direct image along `i`, for if `𝓕_{A'} ≅ i_* G` then — `i_*` being fully
  faithful for a closed immersion — `G ≅ i^* 𝓕_{A'} = 𝓕_A` and the reduction map
  `Deformation.Artin.SectionsSheaf.reductionMap` would be an isomorphism, while its kernel is
  `𝓕_{A'} ⊗_{A'} I`, nonzero whenever `I` and `𝓕` are. So the two outer terms being direct
  images (`Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso`) is all that this
  development's use of the immersion can be, and it is an identification of single objects,
  which needs no δ-compatibility: it is what `obstructionBaseChangeIso` makes, through
  `baseChangeCohomologyObjIso`.

## Implementation notes

The short complex is stated over `SheafOfModules.{u} (structureSheafRing _)` and not over
`AlgebraicGeometry.Scheme.Modules _`. That is forced: `Scheme.Modules` is a plain `def`, so
class synthesis — which runs at `instances` transparency — does not see through it, and
`ShortComplex.ShortExact.map_of_exact` then fails to find
`(modulePushforward i).PreservesZeroMorphisms` even though `modulePushforward_additive` is a
global instance. `structureSheafRing` is `@[instance_reducible]` and is seen through.

Everything is stated in the `modulePushforward i ⋙ Γ(⊤, −)` spelling of the source rather than
the `Γ(i⁻¹⊤, −) ⋙ restrictScalars` one. Crossing the two costs a `whnf` of
`Functor.sheafPushforwardContinuous`, and a statement that crosses it twice — once in the
δ-functor and once in the comparison — exhausts the default heartbeat budget; a first draft of
`baseChangeCohomologyComparison_comp_δ` stated in the `Scheme.Modules.pushforward` /
`Stacks.Cohomology.moduleGlobalSections` spelling did exactly that and died at
`(deterministic) timeout at whnf`. `baseChangeCohomologyDeltaIso` pays the crossing exactly
once, through `Stacks.Cohomology.ModulePushforwardDelta.sectionsRestrictionDeltaIso`.

## References

* [Stacks Project, Tag 07YH](https://stacks.math.columbia.edu/tag/07YH)
* [Stacks Project, Tag 07YG](https://stacks.math.columbia.edu/tag/07YG)
* [Stacks Project, Tag 010U](https://stacks.math.columbia.edu/tag/010U)
* [Stacks Project, Tag 01EX](https://stacks.math.columbia.edu/tag/01EX)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.ModulePushforwardDelta

universe u

namespace Deformation.Artin.SectionsSheaf

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {S W : Scheme.{u}} (q : W ⟶ S) {T T' : Over S} (α : T' ⟶ T)
  [hα : IsClosedImmersion (baseChangeMap q α)]

/-- The base-change immersion `i : W_{T'} → W_T`, as a morphism of ringed spaces. This is the
spelling in which `Stacks.Cohomology.ModulePushforwardDelta` and the exactness instance for
`i_*` are stated. -/
abbrev immersionShHom : (pullback T'.hom q).toRingedSpace ⟶ (pullback T.hom q).toRingedSpace :=
  (baseChangeMap q α).toLRSHom.toShHom

/-- **The δ-compatible comparison of cohomology along the base-change immersion**,
`Hⁿ(W_T, i_* G) ⟶ Hⁿ(W_{T'}, G)` in degree `n`, naturally in `G`. It is the degree-`n`
component of an isomorphism of δ-functors, so it commutes with the connecting morphisms —
`baseChangeCohomologyComparison_comp_δ`.

Its only hypothesis is that `i` is a closed immersion, through which `i_*` is exact; the
acyclicity input behind it is [Stacks, Tag 01EX] part (2) and is unconditional. -/
def baseChangeCohomologyComparison (n : ℕ) :
    modulePushforward (immersionShHom q α) ⋙
        (sections (pullback T.hom q).toRingedSpace ⊤).rightDerived n ⟶
      (modulePushforward (immersionShHom q α) ⋙
        sections (pullback T.hom q).toRingedSpace ⊤).rightDerived n :=
  comparison (immersionShHom q α) ⊤ n

/-- The comparison along the base-change immersion is an isomorphism in every degree. -/
instance isIso_baseChangeCohomologyComparison (n : ℕ) :
    IsIso (baseChangeCohomologyComparison q α n) :=
  isIso_comparison (immersionShHom q α) ⊤ n

/-- **The comparison along the base-change immersion commutes with the connecting
morphisms.** For a short exact sequence of `𝒪_{W_{T'}}`-modules, the square whose horizontal
arrows are the connecting morphisms of the two long exact sequences — that of cohomology on
`W_T` at the pushed-forward sequence, which is short exact because `i_*` is exact, and that of
cohomology on `W_{T'}` — and whose vertical arrows are the comparison, commutes.

This is the δ-naturality that the degree induction of an obstruction theory consumes. It is a
statement about `baseChangeCohomologyComparison` and not about
`Deformation.Artin.SectionsSheaf.baseChangeCohomologyIso`, which is built by another route. -/
theorem baseChangeCohomologyComparison_comp_δ
    {Sq : ShortComplex
      (SheafOfModules.{u} (structureSheafRing (pullback T'.hom q).toRingedSpace))}
    (hSq : Sq.ShortExact) (n : ℕ) :
    (baseChangeCohomologyComparison q α n).app Sq.X₃ ≫
        (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
          (modulePushforward (immersionShHom q α) ⋙
            sections (pullback T.hom q).toRingedSpace ⊤)).δ hSq n =
      (cohomologyDeltaFunctor (pullback T.hom q).toRingedSpace ⊤).δ
          (hSq.map_of_exact (modulePushforward (immersionShHom q α))) n ≫
        (baseChangeCohomologyComparison q α (n + 1)).app Sq.X₁ :=
  comparison_comp_δ (immersionShHom q α) ⊤ hSq n

/-- **The comparison along the base-change immersion as an isomorphism of δ-functors**, in the
`Γ(i⁻¹⊤, −) ⋙ restrictScalars` spelling: the cohomology on `W_{T'}` with scalars restricted
along `i`, against the cohomology on `W_T` of the pushforward. This is the one declaration in
which the crossing between the two spellings is paid. -/
def baseChangeCohomologyDeltaIso :
    Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
        (sections (pullback T'.hom q).toRingedSpace
            ((opensMap (immersionShHom q α)).obj ⊤) ⋙
          ModuleCat.restrictScalars
            ((structureSheafHom (immersionShHom q α)).hom.app (op ⊤)).hom) ≅
      (cohomologyDeltaFunctor (pullback T.hom q).toRingedSpace ⊤).precomp
        (modulePushforward (immersionShHom q α)) :=
  sectionsRestrictionDeltaIso (immersionShHom q α) ⊤

end Deformation.Artin.SectionsSheaf

end
