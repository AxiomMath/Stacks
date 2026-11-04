module

public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.Assembled
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.GrothendieckSequenceAbuts
public import StacksFrontier.Topology.Sheaves.Cohomology.RecoveryA.DerivedDirectImageComposition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The relative Leray spectral sequence of a bounded below complex

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of ringed spaces and let `K` be a bounded below
complex of `𝒪_X`-modules. The relative Leray spectral sequence of `K` is the `E₂`-cohomological
spectral sequence of the canonical truncation tower of `R f_* K`, pushed forward by `R g_*` and
read through cohomology. Its second page is
```
E₂^{p, q} = R ᵖ g_*(H^q(R f_* K))
```
naturally in `K`, and it converges to `H^{p+q}(R (f ≫ g)_* K)`.

Nothing is chosen: the spectral sequence is the value at `R f_* K` of a functor on
`D⁺(Mod(𝒪_X))`, so the second-page identification is a natural isomorphism and not merely a
pointwise one.

## Main definitions

* `Stacks.Cohomology.RelativeLeray.spectralSequencePlus`: the relative Leray spectral sequence,
  as a functor on the bounded below derived category of `𝒪_X`-modules.

## Main results

* `Stacks.Cohomology.RelativeLeray.spectralSequencePlusPageTwoIso`: the second page is
  `R ᵖ g_*(H^q(R f_* -))`, naturally in the complex.
* `Stacks.Cohomology.RelativeLeray.abutsTo_spectralSequencePlus`: the spectral sequence of a
  bounded below complex `K` converges to `H ⁎(R (f ≫ g)_* K)`.

## Implementation notes

Both results are assemblies of generic statements. The second page is
`Stacks.Cohomology.LerayCard.pageTwoNatIsoDerived` for `Φ = R g_*`, whose right-hand side is
`H^q(-)` followed by `CategoryTheory.Functor.rightDerivedPlus p` by the definition of the latter;
`Stacks.DerivedIndexing.rightDerivedIso` moves that to Mathlib's `ℕ`-indexed
`CategoryTheory.Functor.rightDerived`. Convergence is
`Stacks.Cohomology.LerayTruncation.abutsTo_spectralSequence_cohomologySpectralObjectFunctor_obj`,
whose abutment family is `n ↦ H ⁿ(R g_*(R f_* K))`; the identification with
`H ⁿ(R (f ≫ g)_* K)` is [Stacks, Tag 01F5] and the transport is
`CategoryTheory.SpectralSequence.AbutsTo.of_iso`.

[Stacks, Tag 01F5] is stated for the pushforward functors `pushforward` of
`StacksFrontier.Topology.Sheaves.RingedSpace.ModuleFunctors`, while the truncation-tower material
is stated for `RingedSpaceModuleAdjunction.modulePushforward`. The two are the same functor on
the nose (`Stacks.RelativeLeray.pushforward_eq_modulePushforward`), and
`modulePushforwardDerivedCompIso` is where that identification is used.

## References

* [Stacks Project, Tag 01F5](https://stacks.math.columbia.edu/tag/01F5)
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

/-- **Composition of derived direct images**, [Stacks, Tag 01F5], in the `modulePushforward`
spelling of the pushforward of sheaves of modules.

`Stacks.Cohomology.DerivedDirectImageComposition.higherDirectImagesCompIso` is stated for the
functor `pushforward` of `StacksFrontier.Topology.Sheaves.RingedSpace.ModuleFunctors`; the two
spellings are the same functor, as `Stacks.RelativeLeray.pushforward_eq_modulePushforward`
records. -/
def modulePushforwardDerivedCompIso :
    (modulePushforward f).rightDerivedFunctorPlus ⋙
        (modulePushforward g).rightDerivedFunctorPlus ≅
      (modulePushforward (f ≫ g)).rightDerivedFunctorPlus :=
  DerivedDirectImageComposition.higherDirectImagesCompIso f g

/-- **The relative Leray spectral sequence of a bounded below complex.** For composable
morphisms of ringed spaces `f : X ⟶ Y` and `g : Y ⟶ Z`, the functor sending a bounded below
complex `K` of `𝒪_X`-modules to the `E₂`-cohomological spectral sequence of the canonical
truncation tower of `R f_* K`, pushed forward by `R g_*` and read through cohomology.

No resolution is chosen anywhere, so this is a functor on `D⁺(Mod(𝒪_X))` and not a family of
spectral sequences indexed by its objects. -/
def spectralSequencePlus :
    DerivedCategory.Plus (ModuleSheaves X) ⥤
      E₂CohomologicalSpectralSequence (ModuleSheaves Z) :=
  (modulePushforward f).rightDerivedFunctorPlus ⋙
    cohomologySpectralObjectFunctor (modulePushforward g).rightDerivedFunctorPlus ⋙
      Abelian.SpectralObject.E₂SpectralSequenceFunctor (ModuleSheaves Z)

/-- **The second page of the relative Leray spectral sequence of a bounded below complex** is
`R ᵖ g_*(H^q(R f_* -))`, naturally in the complex.

This is `Stacks.Cohomology.LerayCard.pageTwoNatIsoDerived` for `Φ = R g_*` precomposed with
`R f_*`: the right-hand side of that isomorphism is `H^q(-)` followed by the `p`-th right derived
functor of `g_*` computed on `D⁺`, and `Stacks.DerivedIndexing.rightDerivedIso` identifies the
latter with `R ᵖ g_*` in Mathlib's `ℕ`-indexed spelling. -/
@[stacks 01F6 "bounded below complexes, the second page"]
def spectralSequencePlusPageTwoIso (p : ℕ) (q : ℤ) :
    spectralSequencePlus f g ⋙ SpectralSequence.pageFunctor _ _ 2 2 ⋙
        HomologicalComplex.eval _ _ ((p : ℤ), q) ≅
      (modulePushforward f).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleSheaves Y) q ⋙
          (modulePushforward g).rightDerived p :=
  Functor.isoWhiskerLeft (modulePushforward f).rightDerivedFunctorPlus
    (LerayCard.pageTwoNatIsoDerived (modulePushforward g).rightDerivedFunctorPlus p q ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.Plus.homologyFunctor (ModuleSheaves Y) q)
        (Stacks.DerivedIndexing.rightDerivedIso (modulePushforward g) p).symm)

/-- **The relative Leray spectral sequence of a bounded below complex converges to the
cohomology of the derived direct image along the composite.** For every bounded below complex
`K` of `𝒪_X`-modules, `spectralSequencePlus f g` at `K` has an infinity page at every bidegree
and the terms `E_∞^{p, n-p}` are the successive quotients of a finite decreasing filtration of
`H ⁿ(R (f ≫ g)_* K)`.

Convergence of the truncation-tower spectral sequence of a right derived functor is
`Stacks.Cohomology.LerayTruncation.abutsTo_spectralSequence_cohomologySpectralObjectFunctor_obj`,
with abutment `H ⁿ(R g_*(R f_* K))`; the identification of that with `H ⁿ(R (f ≫ g)_* K)` is
[Stacks, Tag 01F5]. -/
@[stacks 01F6 "bounded below complexes, the convergence",
  ega "0 12.2.4" "abutment, complexes",
  sga "4 V 5.4" "convergence, ringed sp"]
theorem abutsTo_spectralSequencePlus (K : DerivedCategory.Plus (ModuleSheaves X)) :
    SpectralSequence.AbutsTo ((spectralSequencePlus f g).obj K)
      (fun n ↦ (DerivedCategory.Plus.homologyFunctor (ModuleSheaves Z) n).obj
        ((modulePushforward (f ≫ g)).rightDerivedFunctorPlus.obj K)) :=
  (abutsTo_spectralSequence_cohomologySpectralObjectFunctor_obj (modulePushforward g)
    ((modulePushforward f).rightDerivedFunctorPlus.obj K)).of_iso fun n ↦
      (DerivedCategory.Plus.homologyFunctor (ModuleSheaves Z) n).mapIso
        ((modulePushforwardDerivedCompIso f g).app K)

end Stacks.Cohomology.RelativeLeray

end
