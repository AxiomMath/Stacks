module

public import StacksFrontier.Topology.Sheaves.Cohomology.RelativeLeray.BoundedBelowComplexes
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The relative Leray spectral sequence of a sheaf of modules

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of ringed spaces. For an `𝒪_X`-module `ℱ` there is
a spectral sequence with
```
E₂^{p, q} = R ᵖ g_*(R^q f_* ℱ)
```
converging to `R^{p+q}(g ∘ f)_* ℱ`, and it is functorial in `ℱ`: the spectral sequence is the
value at `ℱ` of a functor on `Mod(𝒪_X)` and the second-page identification is a natural
isomorphism.

It is the relative Leray spectral sequence of bounded below complexes, `spectralSequencePlus`,
evaluated on the complex concentrated in degree zero.

## Main definitions

* `Stacks.Cohomology.RelativeLeray.spectralSequence`: the relative Leray spectral sequence of a
  sheaf of modules, as a functor on `Mod(𝒪_X)`.

## Main results

* `Stacks.Cohomology.RelativeLeray.spectralSequencePageTwoIso`: the second page is
  `R ᵖ g_*(R^q f_* -)`, naturally in the module.
* `Stacks.Cohomology.RelativeLeray.abutsTo_spectralSequence`: the spectral sequence converges to
  `R ⁎(g ∘ f)_* ℱ`.

## Implementation notes

The higher direct images appear in two indexings: Mathlib's `ℕ`-indexed
`CategoryTheory.Functor.rightDerived`, in which the second page is stated, and the `ℤ`-indexed
`CategoryTheory.Functor.rightDerivedPlus` computed on the bounded below derived category, in
which the abutment is stated because the abutment of a cohomological spectral sequence is a
family indexed by `ℤ`. `Stacks.DerivedIndexing.rightDerivedIso` is the comparison, and it is
where the second page is transported from the second indexing to the first; `rightDerivedPlus n` is
`ℱ ↦ H ⁿ(R f_*(ℱ[0]))` by definition, so the abutment family needs no comparison at all.

## References

* [Stacks Project, Tag 01F6](https://stacks.math.columbia.edu/tag/01F6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.LerayTruncation

universe u

namespace Stacks.Cohomology.RelativeLeray

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] Stacks.Cohomology.PushforwardAcyclic.sheafOfModules_abelian
  DerivedPushforwardSections.modulePushforward_additive
  LerayTruncation.commShiftRightDerivedFunctorPlus
  LerayTruncation.isTriangulatedRightDerivedFunctorPlus

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **The relative Leray spectral sequence of a sheaf of modules.** For composable morphisms of
ringed spaces `f : X ⟶ Y` and `g : Y ⟶ Z`, the functor sending an `𝒪_X`-module `ℱ` to the
relative Leray spectral sequence of the complex `ℱ[0]`. -/
def spectralSequence :
    ModuleSheaves X ⥤ E₂CohomologicalSpectralSequence (ModuleSheaves Z) :=
  DerivedCategory.Plus.singleFunctor (ModuleSheaves X) 0 ⋙ spectralSequencePlus f g

/-- **The second page of the relative Leray spectral sequence of a sheaf of modules** is
`R ᵖ g_*(R^q f_* -)`, naturally in the module. -/
@[stacks 01F6 "sheaves of modules, the second page"]
def spectralSequencePageTwoIso (p q : ℕ) :
    spectralSequence f g ⋙ SpectralSequence.pageFunctor _ _ 2 2 ⋙
        HomologicalComplex.eval _ _ ((p : ℤ), (q : ℤ)) ≅
      (modulePushforward f).rightDerived q ⋙ (modulePushforward g).rightDerived p :=
  Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor (ModuleSheaves X) 0)
      (spectralSequencePlusPageTwoIso f g p q) ≪≫
    Functor.isoWhiskerRight (Stacks.DerivedIndexing.rightDerivedIso (modulePushforward f) q).symm
      ((modulePushforward g).rightDerived p)

/-- **The relative Leray spectral sequence of a sheaf of modules converges to the higher direct
images along the composite.** For every `𝒪_X`-module `ℱ`, the spectral sequence has an infinity
page at every bidegree and the terms `E_∞^{p, n-p}` are the successive quotients of a finite
decreasing filtration of `R ⁿ(g ∘ f)_* ℱ`. -/
@[stacks 01F6 "sheaves of modules, the convergence",
  ega "0 12.2.4" "abutment",
  sga "4 V 5.4" "convergence, ringed sp", sga "2 VIII 3.1" "partial"]
theorem abutsTo_spectralSequence (M : ModuleSheaves X) :
    SpectralSequence.AbutsTo ((spectralSequence f g).obj M)
      (fun n ↦ ((modulePushforward (f ≫ g)).rightDerivedPlus n).obj M) :=
  abutsTo_spectralSequencePlus f g
    ((DerivedCategory.Plus.singleFunctor (ModuleSheaves X) 0).obj M)

end Stacks.Cohomology.RelativeLeray

end
