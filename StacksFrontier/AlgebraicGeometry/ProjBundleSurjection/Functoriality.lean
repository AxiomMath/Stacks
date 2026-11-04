module

public import StacksFrontier.AlgebraicGeometry.ProjBundleSurjection.RationalMap
public import StacksFrontier.AlgebraicGeometry.ProjBundleSurjection.Bundle
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Functorial
public import StacksFrontier.AlgebraicGeometry.RelativeProjMapDomain.EventualBijective

/-!
# The homomorphism of symmetric algebras a morphism of modules induces

`StacksFrontier.AlgebraicGeometry.ProjBundleSurjection.Bundle` reads the morphism of projective
bundles off a `Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom` between the
symmetric algebras of two quasi-coherent modules, and records that **nothing produced one** out of
a morphism `E₁ ⟶ E₂` of the modules: the homomorphism was a variable with no source. Its first
named prerequisite is now
`Stacks.SymGraded.symSheafGradedAlgebraHom` of
`StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Functorial`.

**This file specializes it to `Stacks.AlgebraicGeometry.ProjBundleSurjection.symAlgebra`**, the
form the bundle file consumes, and discharges the eventual hypotheses of Tags 07ZI and 07ZJ for
an isomorphism of modules — so the theorems of
`StacksFrontier/AlgebraicGeometry/RelativeProjMapDomain/` now have an input that is not a variable.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjBundleSurjection.symAlgebraUnitalHom`: **the homomorphism
  `Sym(E₁) ⟶ Sym(E₂)` of relative-Proj inputs induced by `u : E₁ ⟶ E₂`**, for quasi-coherent
  modules.

## Main results

* `…ProjBundleSurjection.eventually_isIso_app_symAlgebraHom`: for an isomorphism of modules the
  induced homomorphism is an isomorphism in every degree, hence in all sufficiently large
  degrees — the hypothesis of Tags 07ZI and 07ZJ.
* `…ProjBundleSurjection.isIso_relativeMapHom_symAlgebraHom`: **Tag 07ZJ (2) for the symmetric
  algebras** — an isomorphism of quasi-coherent modules induces an isomorphism `r_ψ` of the
  relative homogeneous spectra.
* `…ProjBundleSurjection.relativeMapDomain_symAlgebraHom_eq_top`: Tag 07ZJ (1) in the same
  situation, the domain of definition is everything.

## Implementation notes

**The quasi-coherence arguments are the ones `symAlgebra` supplies.**
`Stacks.AlgebraicGeometry.ProjBundleSurjection.symAlgebra E` is
`Stacks.SymGraded.schemeSheafGradedAlgebra E` applied to
`Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E`, so `symAlgebraUnitalHom` is
`Stacks.SymGraded.symSheafGradedAlgebraHom` at exactly those two arguments and the types match
with nothing written.

**Why an isomorphism and not a surjection.** What Tag 07ZJ asks for is a degreewise isomorphism
in large degrees, and functoriality gives that from an isomorphism of modules directly. The
*surjection* hypothesis that
`Stacks.AlgebraicGeometry.ProjBundleSurjection.isClosedImmersion_bundleMap` wants is
`SurjectiveOnAffineSections`, surjectivity on homogeneous sections over the affine opens, which
does not follow from an epimorphism of modules by any formal step — `Bundle.lean` says why, and
this file does not address it.

## References

* [Stacks Project, Tag 07ZJ](https://stacks.math.columbia.edu/tag/07ZJ)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)

## Not done here

No tag is claimed. The assertions of Tag 07ZJ are proved, with their tags, in
`StacksFrontier.AlgebraicGeometry.RelativeProjMapDomain.EventualBijective`, for an arbitrary
homomorphism of graded algebras; what is below is those theorems at one particular homomorphism,
which is a consumer and not a clause.

Nothing is proved about the morphism of projective bundles a general morphism of modules induces:
that is `Bundle.lean`'s `bundleMap`, whose hypothesis is surjectivity on affine sections, and the
remaining two obstructions it names — that surjectivity, and the identification of
`𝐏(𝒪_S^{⊕(n+1)})` with `ℙⁿ_S` — are untouched.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.SymGraded

namespace Stacks.AlgebraicGeometry.ProjBundleSurjection

universe u

variable {X : Scheme.{u}} {E₁ E₂ : X.Modules} [E₁.IsQuasicoherent] [E₂.IsQuasicoherent]

/-- **The homomorphism of the symmetric algebras of two quasi-coherent modules induced by a
morphism between them**, in the form `Bundle.lean` consumes: a homomorphism of the Situation 01NN
inputs of the two projective bundles, in the sense of Tag 07ZG. -/
public def symAlgebraUnitalHom (u : E₁ ⟶ E₂) :
    SheafGradedAlgebraHom (symAlgebra E₁) (symAlgebra E₂) :=
  symSheafGradedAlgebraHom (isQuasicoherentPieces_of_isQuasicoherent E₁)
    (isQuasicoherentPieces_of_isQuasicoherent E₂) u

/-- **The hypothesis of Tags 07ZI and 07ZJ is satisfiable.** For an isomorphism of quasi-coherent
modules the induced homomorphism of symmetric algebras is an isomorphism in every degree, hence
in all sufficiently large degrees. -/
public theorem eventually_isIso_app_symAlgebraHom (e : E₁ ≅ E₂) :
    ∀ᶠ d : ℕ in atTop, IsIso ((symAlgebraUnitalHom e.hom).app (d : ℤ)) :=
  Eventually.of_forall fun d =>
    isIso_symSheafGradedAlgebraHom_app (isQuasicoherentPieces_of_isQuasicoherent E₁)
      (isQuasicoherentPieces_of_isQuasicoherent E₂) e (d : ℤ)

/-- **Tag 07ZJ (1) for the symmetric algebras.** An isomorphism of quasi-coherent modules induces
a homomorphism whose domain of definition is all of `𝐏(E₂)`. -/
public theorem relativeMapDomain_symAlgebraHom_eq_top (e : E₁ ≅ E₂) :
    (symAlgebraUnitalHom e.hom).relativeMapDomain = ⊤ :=
  relativeMapDomain_eq_top_of_eventually_isIso _ (eventually_isIso_app_symAlgebraHom e)

/-- **Tag 07ZJ (2) for the symmetric algebras.** An isomorphism of quasi-coherent modules induces
an isomorphism `r_ψ` of the relative homogeneous spectra of their symmetric algebras.

This is `Stacks.AlgebraicGeometry.RelativeProjMapDomain.isIso_relativeMapHom_of_eventually_isIso`
applied to a homomorphism that is not a variable. -/
public theorem isIso_relativeMapHom_symAlgebraHom (e : E₁ ≅ E₂) :
    IsIso (Tag07ZGMorphism.relativeMapHom (symAlgebraUnitalHom e.hom)) :=
  isIso_relativeMapHom_of_eventually_isIso _ (eventually_isIso_app_symAlgebraHom e)

end Stacks.AlgebraicGeometry.ProjBundleSurjection

end
