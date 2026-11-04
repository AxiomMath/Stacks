module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingBaseChangeGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingOverIntegers
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingTensorStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingUniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.DiagonalProper
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsRightExact
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ValuativeCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionSurjectiveOnPointsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.RightExactGlobalSectionsSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GlobalFunctionsAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiMainTheoremGeneral

/-!
# The canonical morphism to the spectrum of global functions is separated

Let `X` be a quasi-compact, quasi-separated algebraic space over a scheme `S` all of whose
quasi-coherent modules have vanishing first cohomology, that is the data of Stacks 07UY, and write
`A = Γ(X, 𝒪_X)`.  **Stacks 07V5** asserts that the canonical morphism `p : X ⟶ Spec A` is
separated.

The proof here goes through the valuative criterion.  Two lifts of a valuative square for `p`
over a valuation ring `R` are two sections of the base change `X_R ⟶ Spec R`, and `X_R` is again
quasi-compact and quasi-separated with right exact global sections and global functions coming
from `R` (Stacks 07V0).  Any section `s` of such a morphism is a closed immersion: by Zariski's
main theorem `s` is an open immersion into the normalization `Y'` of `X_R` in `Spec R`, which is
integral over `X_R`; the global functions of `Y'` are detected on `Spec R`, so they come from
`R`, and `Y' ⟶ Spec R` is universally injective by the argument of Stacks 07V4.  The open
immersion `Spec R ⟶ Y'`, being a section of it, is therefore surjective, hence an isomorphism.
The equalizer of two sections is then a closed subscheme of `Spec R` containing every point,
hence everything, `R` being reduced.

## Main results

* `CohomologyVanishingSituation.isSeparated_toSpecGlobalFunctionsOverIntegers`: **Stacks 07V5**,
  over an arbitrary base scheme.
* `CohomologyVanishingSituation.isAbsolutelySeparated`: in the situation of Stacks 07UY the space
  `X` is a separated algebraic space.

The general statements of the argument — a section of a morphism `q : Y ⟶ T` to an affine object
inducing a surjection on global functions, out of a quasi-compact, quasi-separated space with
right exact global sections, is a closed immersion, two such sections agree when `T` is reduced,
and such a `q` is separated
(`AlgebraicGeometry.Space.isSeparated_of_surjective_pullbackToGlobalFunctions`) — are in
`StacksFrontier/AlgebraicGeometry/Spaces/RightExactGlobalSectionsSeparated.lean`.

## Implementation notes

*A different route from the source.*  The source chooses a scheme `Y` with a surjective integral
morphism `Y ⟶ X` (Decent Spaces, Lemma 09YB), shows `Y` affine by Serre's criterion (Stacks
01XF), and descends separatedness along the universally closed surjection.  The argument here
replaces both steps by the valuative criterion of Stacks 03KV and Zariski's main theorem for
algebraic spaces, Stacks 0ABS, applied to a single section: every input it uses is the vanishing
hypothesis in the form of right exactness of global sections on quasi-coherent modules, which
passes to spaces affine over `X` (Stacks 07V0 (1)), together with universal injectivity of
morphisms inducing a surjection on global functions, the content of Stacks 07V4.

*The view over `Spec ℤ`.*  As for Stacks 07V4, `p` is a morphism of algebraic spaces over
`Spec ℤ`, formed after regarding `X` as an algebraic space over `ℤ`
(`AlgebraicGeometry.Space.CohomologyVanishingSituation.spaceOverIntegers`), and separatedness of
`p` is separatedness over `Spec ℤ`.  The general results are stated over an arbitrary base.

## References

* [Stacks Project, Tag 07V5](https://stacks.math.columbia.edu/tag/07V5)
* [Stacks Project, Tag 07UY](https://stacks.math.columbia.edu/tag/07UY)
* [Stacks Project, Tag 07V0](https://stacks.math.columbia.edu/tag/07V0)
* [Stacks Project, Tag 07V4](https://stacks.math.columbia.edu/tag/07V4)
* [Stacks Project, Tag 03KV](https://stacks.math.columbia.edu/tag/03KV)
* [Stacks Project, Tag 0ABS](https://stacks.math.columbia.edu/tag/0ABS)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace CohomologyVanishingSituation

variable (T : CohomologyVanishingSituation.{u, u})
    (V : BigFppfOver T.site (⊤_ Scheme.{u}) T.containsTerminal)
    [IsAffine ((BigFppfOver.toScheme T.site (⊤_ Scheme.{u}) T.containsTerminal).obj V)]
    (e : Γ((BigFppfOver.toScheme T.site (⊤_ Scheme.{u}) T.containsTerminal).obj V, ⊤) ≃+*
      T.globalFunctions)

/-- **Stacks 07V5.** In the situation of Stacks 07UY, over an arbitrary base scheme `S`, the
canonical morphism `p : X ⟶ Spec A` is separated.  As in the source, `p` is the morphism of
Stacks 05Z1 formed after regarding `X` as an algebraic space over `Spec ℤ`, and `Spec A` is
presented by an affine object `V` of the site through a ring isomorphism
`Γ(V, 𝒪_V) ≅ A = Γ(X, 𝒪_X)`.

The view of `X` over `Spec ℤ` has right exact global sections on quasi-coherent modules and is
quasi-compact and quasi-separated, and every global function on it is pulled back along `p`;
the statement is then
`AlgebraicGeometry.Space.isSeparated_of_surjective_pullbackToGlobalFunctions`. -/
@[stacks 07V5]
theorem isSeparated_toSpecGlobalFunctionsOverIntegers :
    IsSeparated T.site (⊤_ Scheme.{u}) T.containsTerminal
      (toSpecGlobalFunctionsOverIntegers T V e).hom :=
  isSeparated_of_surjective_pullbackToGlobalFunctions T.containsTerminal
    T.surjective_sectionsMap_spaceOverIntegers T.isQuasiCompactSpace_spaceOverIntegers
    T.isAbsolutelyQuasiSeparated_spaceOverIntegers (toSpecGlobalFunctionsOverIntegers T V e)
    (surjective_pullbackToGlobalFunctions_toSpecGlobalFunctionsOverIntegers T V e)

/-- **In the situation of Stacks 07UY the space `X` is a separated algebraic space**, the
conclusion the proof of Stacks 07V5 reaches in the source: `X` viewed over `Spec ℤ` is separated
over the affine scheme `Spec A`, hence separated, and separatedness does not depend on the base
over which `X` is viewed.  Here `Spec A` is the chosen presentation
`AlgebraicGeometry.Space.CohomologyVanishingSituation.specA`. -/
theorem isAbsolutelySeparated :
    IsAbsolutelySeparated T.site T.base T.containsBase T.containsTerminal T.space.1 := by
  let M := T.modelOverIntegers
  let V₀ := T.specA
  have : IsAffine ((BigFppfOver.toScheme T.site (⊤_ Scheme.{u}) T.containsTerminal).obj V₀) :=
    isAffine_toScheme_obj_specGlobalFunctions _ _ _ _ _ _
  let e₀ : Γ((BigFppfOver.toScheme T.site (⊤_ Scheme.{u}) T.containsTerminal).obj V₀, ⊤) ≃+*
      T.globalFunctions :=
    ((Scheme.ΓSpecIso M.ring).commRingCatIsoToRingEquiv.trans M.equiv).trans
      T.spaceOverIntegersGlobalFunctionsEquiv
  exact (isAbsolutelySeparated_viewOverIntegers_iff T.site T.base T.containsBase
      T.containsTerminal T.space.1).1
    (isAbsolutelySeparated_of_isSeparated_to_affine T.site (⊤_ Scheme.{u}) T.containsTerminal
      T.containsTerminal V₀ inferInstance (toSpecGlobalFunctionsOverIntegers T V₀ e₀).hom
      (isSeparated_toSpecGlobalFunctionsOverIntegers T V₀ e₀))

end CohomologyVanishingSituation

end AlgebraicGeometry.Space

end
