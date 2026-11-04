module

public import StacksFrontier.AlgebraicGeometry.Duality.SchemeDualizingHomothety
public import StacksFrontier.AlgebraicGeometry.Duality.SheafyTraceProperIso

/-!
# `Rf_*𝒪_X ≅ R𝓗om_{𝒪_Y}(Rf_*a(K), K)` when `a(K)` is dualizing

Let `f : X ⟶ Y` be a proper morphism of Noetherian schemes and `a` the right adjoint of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` of [Stacks, Tag 0A9E]. For `K ∈ D⁺_QCoh(𝒪_Y)` put
`ω_X^• = a(K)`, the relative dualizing complex of [Stacks, Tag 0AWI]. If `ω_X^•` is a dualizing
complex on `X` ([Stacks, Tag 0A87]), then

`Rf_*𝒪_X ≅ R𝓗om_{𝒪_Y}(Rf_*ω_X^•, K)`.

This is the computation the source performs inside the proof of [Stacks, Tag 0AXD]: the sheafy
trace of [Stacks, Tag 0B6H] is an isomorphism

`Rf_*R𝓗om_{𝒪_X}(ω_X^•, a(K)) ⟶ R𝓗om_{𝒪_Y}(Rf_*ω_X^•, K)`

by [Stacks, Tag 0GEW], and since `a(K)` *is* `ω_X^•` its left-hand side is `Rf_*` of the derived
endomorphisms of `ω_X^•`, which is `Rf_*𝒪_X` because the homothety of a dualizing complex is an
isomorphism ([Stacks, Tag 08DI], `Stacks.Duality.derivedSheafHomSelfUnitIso`). So the two inputs
combine with nothing between them: the normalisation `a(K) = ω_X^•` of [Stacks, Remark 0B4R] is
here a definition rather than a hypothesis, which is what makes the left-hand side collapse.

## Main results

All in the namespace `Stacks.Duality`.

* `properRightAdjointSelfSheafHomPushforwardIso` — `Rf_*R𝓗om_{𝒪_X}(a(K), a(K)) ≅ Rf_*𝒪_X`, the
  homothety half, which needs only that `a(K)` is dualizing.
* `derivedPushforwardUnitIsoSheafHomPushforward` — the displayed isomorphism.

## What is carried, and what is not

The two boundedness and coherence hypotheses `hbm` and `hbb` are passed through to
[Stacks, Tag 0GEW] unchanged: they are the hypotheses that tag itself carries, namely
`a(K) ∈ D^-_Coh(𝒪_X)` and `K ∈ D⁺_QCoh(𝒪_Y)`. So the statement below is exactly as strong as
`Stacks.Duality.isIso_sheafyTrace_of_isProper_of_derivedCategoryBMinus`, with no further
assumption.

The hypothesis `hω` that `a(K)` is a dualizing complex is **not** discharged here, and it is the
conclusion of [Stacks, Tag 0AA3]. It is stated as the predicate
`Stacks.Duality.IsDualizingComplex` applied to the object `a(K)` — a condition on a given complex,
in the same form in which [Stacks, Tag 0GEW] and
`Stacks.Duality.isDualizingComplex_upperShriek_obj` take and state it — not as an opaque `Prop`
standing in for a tag. Discharging it from `Stacks.Duality.isDualizingComplex_upperShriek_obj`
requires moving that result from the locally small model of `D(𝒪_X)` to the standard model, at
which everything here is read; the comparison of the two readings of
`Stacks.Duality.IsDualizingComplex` is
`Stacks.Duality.isDualizingComplex_standard_iff_locallySmall` of
`Duality/DualizingComplexModelTransport.lean`, and what is still missing is the matching
comparison for the right adjoint `a` itself.

*No `@[stacks]` attribute is placed on anything in this file, and no tag's coverage changes.*
Nothing here states a tag that its inputs do not already state: it is the composite of
[Stacks, Tag 0GEW] with [Stacks, Tag 08DI] at one object, and it carries the conclusion of
[Stacks, Tag 0AA3] as a hypothesis.

## Implementation notes

Everything is at `CategoryTheory.HasDerivedCategory.standard`, which is the model both inputs are
stated at. The locally small instances of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` are *global*, so they outrank a
file-level local instance; they are erased here rather than outweighed, exactly as
`Duality/SchemeDualizingHomothety.lean` does, which keeps a single model in force for the whole
file. That the two inputs' terms compose at all is itself the check that no other model leaked in:
`Stacks.Duality.derivedSheafHomSelfUnitIso` and
`Stacks.Duality.isIso_sheafyTrace_of_isProper_of_derivedCategoryBMinus` are both fixed at the
standard model, so a leak would make the composite below fail to typecheck.

## References

* [Stacks Project, Tag 0GEW](https://stacks.math.columbia.edu/tag/0GEW)
* [Stacks Project, Tag 0B6H](https://stacks.math.columbia.edu/tag/0B6H)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0AA3](https://stacks.math.columbia.edu/tag/0AA3)
* [Stacks Project, Tag 0AWI](https://stacks.math.columbia.edu/tag/0AWI)
* [Stacks Project, Tag 0AXD](https://stacks.math.columbia.edu/tag/0AXD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite
open Stacks.SheafOfModules
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] Stacks.AssociatedSheaf.hasModuleSheafify
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective

universe u

namespace Stacks.Duality

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The right adjoint `a` of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` of [Stacks, Tag 0A9E], at the
standard model. -/
abbrev properRightAdjoint [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
    [QuasiSeparatedSpace Y] :
    quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X :=
  twistedInverseImage f (StandardModel.isQuasicoherent_homology_derivedPushforward f)

variable [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- **`Rf_*R𝓗om_{𝒪_X}(a(K), a(K)) ≅ Rf_*𝒪_X` for `a(K)` dualizing.** The derived endomorphisms of
a dualizing complex are the structure sheaf, by [Stacks, Tag 08DI] — this is
`Stacks.Duality.derivedSheafHomSelfUnitIso` — and `Rf_*` is applied to that isomorphism. -/
def properRightAdjointSelfSheafHomPushforwardIso [IsLocallyNoetherian X]
    (K : quasiCoherentDerivedCategory Y)
    (hω : IsDualizingComplex ((properRightAdjoint f).obj K).obj) :
    letI := derivedMonoidalStructure X.sheaf
    (derivedPushforward f).obj
        (((derivedSheafHom X.sheaf).obj (op ((properRightAdjoint f).obj K).obj)).obj
          ((properRightAdjoint f).obj K).obj) ≅
      (derivedPushforward f).obj (𝟙_ (DerivedCategory (StructureSheafModules X.sheaf))) :=
  letI := derivedMonoidalStructure X.sheaf
  (derivedPushforward f).mapIso
    (derivedSheafHomSelfUnitIso ((properRightAdjoint f).obj K).obj hω)

/-- **`Rf_*𝒪_X ≅ R𝓗om_{𝒪_Y}(Rf_*a(K), K)` when `a(K)` is a dualizing complex.** Let
`f : X ⟶ Y` be proper with `X` and `Y` Noetherian, let `K ∈ D⁺_QCoh(𝒪_Y)` with `a(K)` in
`D^-_Coh(𝒪_X)`, and suppose `a(K)` is a dualizing complex on `X`. Then the derived direct image of
the structure sheaf is the derived internal hom of `Rf_*a(K)` into `K`.

The sheafy trace `Rf_*R𝓗om_{𝒪_X}(a(K), a(K)) ⟶ R𝓗om_{𝒪_Y}(Rf_*a(K), K)` is an isomorphism by
[Stacks, Tag 0GEW], its source being `Rf_*R𝓗om_{𝒪_X}(L, a(K))` at `L = a(K)`; and that source is
`Rf_*𝒪_X` by `Stacks.Duality.properRightAdjointSelfSheafHomPushforwardIso`. The hypotheses `hbm`
and `hbb` are [Stacks, Tag 0GEW]'s own and are passed to it unchanged. -/
def derivedPushforwardUnitIsoSheafHomPushforward [IsProper f] [IsNoetherian X] [IsNoetherian Y]
    (K : quasiCoherentDerivedCategory Y)
    (hbm : DerivedCategoryB.derivedCategoryBMinus (fun N : X.Modules => N.IsCoherent)
      ((properRightAdjoint f).obj K).obj)
    (hbb : DerivedCategoryB.IsBoundedBelow K.obj)
    (hω : IsDualizingComplex ((properRightAdjoint f).obj K).obj) :
    letI := derivedMonoidalStructure X.sheaf
    (derivedPushforward f).obj (𝟙_ (DerivedCategory (StructureSheafModules X.sheaf))) ≅
      ((derivedSheafHom Y.sheaf).obj
        (op ((derivedPushforward f).obj ((properRightAdjoint f).obj K).obj))).obj K.obj :=
  letI := derivedMonoidalStructure X.sheaf
  haveI := isIso_sheafyTrace_of_isProper_of_derivedCategoryBMinus f
    ((properRightAdjoint f).obj K) K hbm hbb
  (properRightAdjointSelfSheafHomPushforwardIso f K hω).symm ≪≫
    asIso (sheafyTrace f
      (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite X.sheaf))
      (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite Y.sheaf))
      (StandardModel.isQuasicoherent_homology_derivedPushforward f)
      (twistedInverseImageAdjunction f
        (StandardModel.isQuasicoherent_homology_derivedPushforward f))
      ((properRightAdjoint f).obj K) K)

end Stacks.Duality

end
