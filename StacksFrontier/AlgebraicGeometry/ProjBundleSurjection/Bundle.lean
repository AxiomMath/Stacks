module

public import StacksFrontier.AlgebraicGeometry.ProjBundleSurjection.Basic
public import StacksFrontier.AlgebraicGeometry.SymAlgebraQcohPieces.Basic

/-!
# Closed immersions of projective bundles

`Stacks.SymGraded.schemeProjectiveBundle` is the projective bundle `𝐏(E) = Proj_X(Sym E)` of a
module on an arbitrary scheme, and
`Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent` makes it unconditional for every
quasi-coherent `E`. This file reads the glued morphism of the sibling file at that bundle: a
homomorphism of the symmetric algebras of two quasi-coherent modules which is surjective on
homogeneous sections over the affine opens of the base induces a **closed immersion of projective
bundles over the base**.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjBundleSurjection.bundleMap`: the induced morphism
  `𝐏(E₂) ⟶ 𝐏(E₁)`.

## Main results

* `Stacks.AlgebraicGeometry.ProjBundleSurjection.bundleMap_comp_toBase`: it is a morphism over
  the base.
* `Stacks.AlgebraicGeometry.ProjBundleSurjection.isClosedImmersion_bundleMap`: **it is a closed
  immersion.**
* `Stacks.AlgebraicGeometry.ProjBundleSurjection.isPullback_chart_bundleMap`: over an affine open
  of the base it is the morphism of absolute `Proj`s of the graded rings of sections, and that
  square is cartesian.

## What this is for, and what it still needs

Tag 087S part (1) is an equivalence —
`Stacks.Tag087SBundle.isHProjective_of_isProjective_iff` — with the right-hand side
`Stacks.Tag087SBundle.BundlesAreHProjective S`, the assertion that every projective bundle of a
finite-type quasi-coherent module on the base is H-projective. The first thing that assertion
needs is a closed immersion of `𝐏(E)` into a projective space over the base, from a surjection
`𝒪_S^{⊕(n+1)} ⟶ E`. The *geometry* of that closed immersion is this file; what is missing is on
either side of it and is named here rather than assumed.

**First, the source of the hypothesis.** This is available. Functoriality of the
sheafified symmetric algebra — a
`Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom` between two
`Stacks.SymGraded.schemeSheafGradedAlgebra`s out of a morphism `E₁ ⟶ E₂` of modules — is
`Stacks.SymGraded.schemeSheafGradedAlgebraHom` of
`StacksFrontier/AlgebraicGeometry/SheafSymmetricAlgebra/Functoriality.lean`, and
`Stacks.AlgebraicGeometry.ProjBundleSurjection.symAlgebraHom` of the sibling file
`StacksFrontier/AlgebraicGeometry/ProjBundleSurjection/RationalMap.lean` is the instance this file's
`ψ` wants. What remains open about the hypothesis is only its surjectivity, below.

**Second, the surjectivity hypothesis itself**, which is not formal: a surjection of
quasi-coherent sheaves is *not* surjective on sections over an arbitrary open, and
`Sym^n` of the section map has to be surjective too. Over an affine open both hold — the first
because the kernel is quasi-coherent, the second because `Sym^n` is right exact — and the
affine-local identification of the pieces,
`Stacks.SymGraded.AffinePieces.sheafificationIsoTilde`, is the statement that would carry
it; what is missing is its naturality in `E`.

**Third, and separately: `𝐏(𝒪_S^{⊕(n+1)})` is not identified with `ℙⁿ_S`.**
`AlgebraicGeometry.projectiveSpaceOver` is the base change of `Proj ℤ[T₀, …, Tₙ]` along
`S ⟶ Spec ℤ`, and nothing in either tree relates it to a relative `Proj` over a non-affine base;
`Stacks.ProjChartBaseChange` is for an affine base and says so. This one cannot be worked
around: `Stacks.Tag087S.IsHProjective` is *defined* as the existence of a closed immersion into
`AlgebraicGeometry.projectiveSpaceOver n S` over `S`, so no amount of closed immersions between
relative `Proj`s reaches it. That comparison is a separate statement, and it is the last of the
three.

## References

* [Stacks Project, Tag 087S](https://stacks.math.columbia.edu/tag/087S)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01N1](https://stacks.math.columbia.edu/tag/01N1)

## Not done here

No project tag is attached. These are inputs, not tagged statements: 087S's labels quantify over
projectivity of a morphism, and the covering sets of 01W8 and of 07ZG are not touched.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.SymGraded

namespace Stacks.AlgebraicGeometry.ProjBundleSurjection

universe u

variable {X : Scheme.{u}}

/-- The sheaf-level graded algebra `Sym(E)` of a quasi-coherent module, with the quasi-coherence
of its pieces discharged. -/
public abbrev symAlgebra (E : X.Modules) [E.IsQuasicoherent] : SheafGradedAlgebra X :=
  schemeSheafGradedAlgebra E (isQuasicoherentPieces_of_isQuasicoherent E)

variable {E₁ E₂ : X.Modules} [E₁.IsQuasicoherent] [E₂.IsQuasicoherent]
  {ψ : SheafGradedAlgebraHom (symAlgebra E₁) (symAlgebra E₂)}

/-- **The morphism of projective bundles** induced by a surjection of their symmetric algebras:
`𝐏(E₂) ⟶ 𝐏(E₁)`. -/
public def bundleMap (hψ : SurjectiveOnAffineSections ψ) :
    (schemeProjectiveBundle E₂ (isQuasicoherentPieces_of_isQuasicoherent E₂)).scheme ⟶
      (schemeProjectiveBundle E₁ (isQuasicoherentPieces_of_isQuasicoherent E₁)).scheme :=
  map hψ

/-- **The morphism of projective bundles is over the base.** -/
public theorem bundleMap_comp_toBase (hψ : SurjectiveOnAffineSections ψ) :
    bundleMap hψ ≫ schemeProjectiveBundleToBase E₁
          (isQuasicoherentPieces_of_isQuasicoherent E₁) =
      schemeProjectiveBundleToBase E₂ (isQuasicoherentPieces_of_isQuasicoherent E₂) :=
  map_comp_toBase hψ

/-- **The morphism of projective bundles is a closed immersion.** -/
public theorem isClosedImmersion_bundleMap (hψ : SurjectiveOnAffineSections ψ) :
    IsClosedImmersion (bundleMap hψ) :=
  isClosedImmersion_map hψ

/-- Over an affine open `U` of the base, the morphism of projective bundles is the morphism of
absolute projective spectra of the graded rings of sections over `U`, and the square it forms with
the two charts is cartesian. -/
public theorem isPullback_chart_bundleMap (hψ : SurjectiveOnAffineSections ψ)
    (U : X.Opens) (hU : IsAffineOpen U) :
    IsPullback
      ((schemeProjectiveBundle E₂ (isQuasicoherentPieces_of_isQuasicoherent E₂)).chart U hU)
      (chartMap hψ U hU) (bundleMap hψ)
      ((schemeProjectiveBundle E₁ (isQuasicoherentPieces_of_isQuasicoherent E₁)).chart U hU) :=
  isPullback_chart hψ U hU

end Stacks.AlgebraicGeometry.ProjBundleSurjection

end
