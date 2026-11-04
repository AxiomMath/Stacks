module

public import StacksFrontier.AlgebraicGeometry.Duality.ModelComparisonRightAdjoint

/-!
# `Rf_*𝒪_X ≅ R𝓗om_{𝒪_Y}(Rf_*a(K), K)` for `K` a dualizing complex on `Y`

Let `f : X ⟶ Y` be a proper morphism of Noetherian schemes and `a` the right adjoint of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` of [Stacks, Tag 0A9E]. Let `K ∈ D⁺_QCoh(𝒪_Y)` be a dualizing
complex on `Y` ([Stacks, Tag 0A87]) and put `ω_X^• = a(K)`, the relative dualizing complex of
[Stacks, Tag 0AWI]. Then

`Rf_*𝒪_X ≅ R𝓗om_{𝒪_Y}(Rf_*ω_X^•, K)`.

This is `Stacks.Duality.derivedPushforwardUnitIsoSheafHomPushforward` with its hypothesis that
`a(K)` be a dualizing complex replaced by the hypothesis on `K` that implies it: `a` carries
dualizing complexes to dualizing complexes, which is
`Stacks.Duality.isDualizingComplex_properRightAdjoint_obj`. Nothing else changes; in particular
the two hypotheses of [Stacks, Tag 0GEW] that the isomorphism rests on,
`a(K) ∈ D^-_Coh(𝒪_X)` and `K ∈ D⁺_QCoh(𝒪_Y)`, are passed through unchanged.

## Main results

* `Stacks.Duality.derivedPushforwardUnitIsoSheafHomPushforwardOfIsDualizingComplex` — the
  displayed isomorphism, for `K` a dualizing complex on `Y`.

## Implementation notes

The statement is the composite of [Stacks, Tag 0GEW] with [Stacks, Tag 08DI] at one object, which
is what the input already is, with one of its hypotheses derived rather than assumed.

Everything is at `CategoryTheory.HasDerivedCategory.standard`, which is the model
`Stacks.Duality.derivedPushforwardUnitIsoSheafHomPushforward` is stated at. The locally small
instances of `StacksFrontier.Homology.DerivedCategory.LocallySmall` are *global*, so they
outrank a file-level local instance; they are erased here rather than outweighed, exactly as
`StacksFrontier.AlgebraicGeometry.Duality.ProperDualizingTraceUnit` and
`StacksFrontier.AlgebraicGeometry.Duality.SchemeDualizingHomothety` do, which keeps a single model
in force for the whole file.

## References

* [Stacks Project, Tag 0GEW](https://stacks.math.columbia.edu/tag/0GEW)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0AA3](https://stacks.math.columbia.edu/tag/0AA3)
* [Stacks Project, Tag 0AWI](https://stacks.math.columbia.edu/tag/0AWI)
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

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiSeparatedSpace X] [QuasiSeparatedSpace Y]

/-- **`Rf_*𝒪_X ≅ R𝓗om_{𝒪_Y}(Rf_*a(K), K)` for `K` a dualizing complex on `Y`.** Let
`f : X ⟶ Y` be proper with `X` and `Y` Noetherian, let `K ∈ D⁺_QCoh(𝒪_Y)` be a dualizing complex
with `a(K)` in `D^-_Coh(𝒪_X)`. Then the derived direct image of the structure sheaf is the derived
internal hom of `Rf_*a(K)` into `K`. -/
def derivedPushforwardUnitIsoSheafHomPushforwardOfIsDualizingComplex [IsProper f]
    [IsNoetherian X] [IsNoetherian Y]
    (K : quasiCoherentDerivedCategory Y)
    (hbm : DerivedCategoryB.derivedCategoryBMinus (fun N : X.Modules => N.IsCoherent)
      ((properRightAdjoint f).obj K).obj)
    (hbb : DerivedCategoryB.IsBoundedBelow K.obj)
    (hK : IsDualizingComplex K.obj) :
    letI := derivedMonoidalStructure X.sheaf
    (derivedPushforward f).obj (𝟙_ (DerivedCategory (StructureSheafModules X.sheaf))) ≅
      ((derivedSheafHom Y.sheaf).obj
        (op ((derivedPushforward f).obj ((properRightAdjoint f).obj K).obj))).obj K.obj :=
  derivedPushforwardUnitIsoSheafHomPushforward f K hbm hbb
    (isDualizingComplex_properRightAdjoint_obj f K hK)

end Stacks.Duality

end
