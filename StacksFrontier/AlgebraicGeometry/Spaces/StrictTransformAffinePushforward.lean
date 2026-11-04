module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardQuasicoherentExact
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupIsomorphismOffCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleBaseChangeAffineChartBijective
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformExceptionalPreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedSectionsPushforwardIso

/-!
# Strict transforms and direct images along an affine morphism

This file holds **Stacks 0866**: for `b : A' ⟶ A` the blowup of an algebraic space `A` in a
closed subspace `Z`, an affine morphism `g : X ⟶ Y` of algebraic spaces over `A`, a
quasi-coherent `𝒪_X`-module `F` and the base change `g' : X ×_A A' ⟶ Y ×_A A'` of `g`, the
direct image `g'_*` of the strict transform of `F` is the strict transform of `g_*F`.

## Main results

* `AlgebraicGeometry.Space.exists_modulePushforward_strictTransformSheaf_iso_unconditional`
  is **Stacks 0866**.  Its hypotheses are the tag's own: a blowup of `A` along a closed
  subspace, an affine morphism of algebraic spaces over `A`, and a quasi-coherent module.

## Implementation notes

The base-change isomorphism `g'_* pr_X^*F ≅ pr_Y^* g_*F` the argument runs on — the base-change
clause of Stacks 07U8, that is Stacks 02KG for an affine morphism of algebraic spaces — is
`AlgebraicGeometry.Space.nonempty_iso_modulePushforward_modulePullback_of_isAffineHom` of
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleBaseChangeAffineChartBijective.lean`, applied to the
cartesian square `AlgebraicGeometry.Space.isPullback_strictTransformPullbackMap` of the two
ambient base changes along `b`, whose `g` is affine by hypothesis and whose base change `g'` is
affine by Stacks 03WI.

The tag lives here rather than beside Stacks 0865 and 0868 in
`StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformProperties.lean` for one reason: its proof
needs Stacks 03GA, quasi-coherence of the inverse image, which this repository has only in
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackQuasicoherentFromChartDiagrams.lean`.  That
file transitively imports
`StacksFrontier/AlgebraicGeometry/Spaces/LargestQuasicoherentSubmodule.lean`, whose
`CohomologyOfModules` dependency installs an `Abelian` instance for sheaves of modules at the
universe `max (u + 1) u m`; instance search then becomes stuck on it when the `Abelian`
instance for `AlgebraicGeometry.Space.Modules` at the universe `u` of the schemes is asked for,
and three files downstream of `StrictTransformProperties` ask for exactly that.  Keeping the
import out of that file and putting this tag here is the whole of the remedy.

## References

* [Stacks Project, Tag 0866](https://stacks.math.columbia.edu/tag/0866)
* [Stacks Project, Tag 0862](https://stacks.math.columbia.edu/tag/0862)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03WI](https://stacks.math.columbia.edu/tag/03WI)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A X Y A' : AlgebraicSpaces B S hS} (g : X ⟶ Y) (f : Y ⟶ A) (b : A' ⟶ A)

/-- **Stacks 0866.** Let `Z ⊆ A` be a closed subspace of an algebraic space over `S`, let
`b : A' ⟶ A` be the blowup of `A` in `Z`, let `g : X ⟶ Y` be an affine morphism of algebraic
spaces over `A`, let `F` be an `𝒪_X`-module and let `g' : X ×_A A' ⟶ Y ×_A A'` be the base
change of `g`.  Then `g'_*` of the strict transform of `F` relative to `b` is the strict
transform of `g_* F`, compatibly with the two quotient maps and the base-change comparison.

`F` is quasi-coherent, which is the tag's own hypothesis on it.

The hypotheses are the tag's own, and the three inputs the argument runs on are all proved.

The base-change isomorphism `α : g'_* pr_X^*F ≅ pr_Y^* g_*F` — the base-change clause of
Stacks 07U8, that is Stacks 02KG for an affine morphism of algebraic spaces — is
`AlgebraicGeometry.Space.nonempty_iso_modulePushforward_modulePullback_of_isAffineHom` at the
cartesian square of the two ambient base changes along `b`.

The identification `β` of the direct image of the sections supported on the exceptional
preimage with the sections of `pr_Y^*(g_*F)` supported there, compatibly with `α`, is
Stacks 085B transported along `α`,
`AlgebraicGeometry.Space.exists_iso_modulePushforward_supportedSectionsSubmodule_of_eq_preimage`,
together with the identification of the exceptional preimage upstairs as the inverse image of the
one downstairs, `AlgebraicGeometry.Space.exceptionalPreimageSet_comp_eq_preimage`.

Right exactness of `g'_*` on the sequence at hand — that the direct image along the affine
morphism `g'` preserves the cokernel defining the strict transform, which is the use the
Stacks Project makes of Stacks 01SB — is
`AlgebraicGeometry.Space.preservesCokernel_submoduleι_modulePushforward_of_isAffineHom`, applied
to the base change `g'` of `g`, which is affine by Stacks 03WI; its two quasi-coherence inputs
are quasi-coherence of `pr_X^*F`, which is Stacks 03GA, and quasi-coherence of the submodule of
sections supported on the exceptional preimage, which is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_supportedSections_exceptionalPreimage` above, the
exceptional divisor of a blowup being an effective Cartier divisor and hence locally principal.

What this proof does is the argument of the Stacks Project: the strict transform is a cokernel,
right exactness of the affine direct image carries it through `g'_*`, and `α` identifies the
resulting cokernel with the cokernel defining the strict transform of `g_* F`. -/
@[stacks 0866 "the hypotheses are the tag's own -- a blowup of the ambient space along a closed \
subspace, an affine morphism of algebraic spaces over it, and a quasi-coherent module -- and \
the base-change isomorphism of the base-change clause of Stacks 07U8, Stacks 02KG for an \
affine morphism of algebraic spaces, is proved on the way"]
theorem exists_modulePushforward_strictTransformSheaf_iso_unconditional
    (Z : ClosedSubspaces B S hS A.1)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (hb : IsBlowupAlong B S hS Z b) (hg : IsAffineHom B S hS g.hom) :
    ∃ (α : (modulePushforward B S hS (strictTransformPullbackMap B S hS g f b)).obj
              ((modulePullback B S hS
                (strictTransformPullbackToSource B S hS (g ≫ f) b)).obj F) ≅
            (modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj
              ((modulePushforward B S hS g).obj F))
        (e : (modulePushforward B S hS (strictTransformPullbackMap B S hS g f b)).obj
              (strictTransformSheaf B S hS (g ≫ f) b (Z.1.preimage b.hom) F) ≅
            strictTransformSheaf B S hS f b (Z.1.preimage b.hom)
              ((modulePushforward B S hS g).obj F)),
      (modulePushforward B S hS (strictTransformPullbackMap B S hS g f b)).map
            (strictTransformSheafQuotient B S hS (g ≫ f) b (Z.1.preimage b.hom) F) ≫ e.hom =
        α.hom ≫ strictTransformSheafQuotient B S hS f b (Z.1.preimage b.hom)
          ((modulePushforward B S hS g).obj F) := by
  -- the base change `g'` of the affine morphism `g` is affine, Stacks 03WI
  have hg' : IsAffineHom B S hS (strictTransformPullbackMap B S hS g f b).hom :=
    IsAffineHom.of_isPullback
      (AlgebraicSpaces.isPullback_hom B S hS
        (isPullback_strictTransformPullbackMap B S hS g f b)) hg
  -- the base-change isomorphism `g'_*(pr_X^*F) ≅ pr_Y^*(g_*F)` of the base-change clause of
  -- Stacks 07U8, which is Stacks 02KG for the affine morphism `g`
  obtain ⟨α⟩ := nonempty_iso_modulePushforward_modulePullback_of_isAffineHom B S hS
    (strictTransformPullbackToSource B S hS (g ≫ f) b)
    (strictTransformPullbackMap B S hS g f b) g
    (strictTransformPullbackToSource B S hS f b)
    (isPullback_strictTransformPullbackMap B S hS g f b) hg hg' F hF
  -- `E = b^{-1}Z` is a closed subspace of `A'`, so the exceptional preimage is a closed set
  have hE : IsClosedSubspace B S hS (Z.1.preimage b.hom) :=
    isClosedSubspace_preimage B S hS b.hom Z.1 A.2 A'.2 Z.2
  -- Stacks 085B, transported along `α`: the direct image of the sections supported on the
  -- exceptional preimage is the submodule of sections of `pr_Y^*(g_*F)` supported there
  obtain ⟨β, hβ⟩ := exists_iso_modulePushforward_supportedSectionsSubmodule_of_eq_preimage B S hS
    (strictTransformPullbackMap B S hS g f b)
    (exceptionalPreimageSet B S hS f b (Z.1.preimage b.hom))
    (isClosed_exceptionalPreimageSet B S hS f b (Z.1.preimage b.hom) hE)
    (exceptionalPreimageSet B S hS (g ≫ f) b (Z.1.preimage b.hom))
    (exceptionalPreimageSet_comp_eq_preimage B S hS g f b (Z.1.preimage b.hom)) _ _ α
  -- `pr_X^*F` is quasi-coherent, Stacks 03GA
  have hP := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    (strictTransformPullbackToSource B S hS (g ≫ f) b) F hF
  -- the exceptional divisor of the blowup is an effective Cartier divisor, hence locally
  -- principal, so the sections supported on its preimage are quasi-coherent
  have hlp := isLocallyPrincipal_definingIdealSheaf_of_isEffectiveCartierDivisor B S hS A' _
    (isEffectiveCartierDivisor_exceptionalDivisor hb)
  have hK := isQuasicoherentOnSite_supportedSections_exceptionalPreimage B S hS (g ≫ f) b
    (Z.1.preimage b.hom) _ hlp _ hP
  -- hence the affine direct image preserves the cokernel defining the strict transform
  have := preservesCokernel_submoduleι_modulePushforward_of_isAffineHom B S hS
    (strictTransformPullbackMap B S hS g f b) hg' _ hP _ hK
  refine ⟨α, PreservesCokernel.iso _ _ ≪≫ cokernel.mapIso _ _ β α hβ, ?_⟩
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun t => t ≫ (cokernel.mapIso _ _ β α hβ).hom)
    (PreservesCokernel.π_iso_hom _ _)) ?_
  exact cokernel.π_desc _ _ _

end AlgebraicGeometry.Space

end
