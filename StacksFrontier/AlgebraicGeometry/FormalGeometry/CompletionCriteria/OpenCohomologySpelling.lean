module

public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.OpenCohomologyFiniteness
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FiniteModuleModel
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.NeighbourhoodComparisonHigher
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.ComplementCohomologyDeltaNatural

/-!
# The two spellings of `H^p(U, −)` on the complement, compared as functors

Fix an algebraization situation `S`: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, the affine scheme
`X = Spec(A)` and the open complement `U = X ∖ V(𝔞)`.  The cohomology of `U` is spelled twice in
this library, and
`StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.OpenCohomologyFiniteness`
compares the two spellings *only through finiteness*, by passing through coherence of `R^p j_*`.
That
comparison forgets the maps, and so cannot transport a statement about the image of a transition
map `H^p(U, ℱₙ) ⟶ H^p(U, ℱ₁)`, which is what the Mittag-Leffler criterion [Stacks, Tag 0DXG]
consumes.

This file supplies the comparison as a **natural isomorphism of functors**, so the maps come
along:

* `Stacks.Algebraization.openCohomologyFunctor S p` derives the global sections of
  `𝒪_U`-modules on the open subscheme `U` and restricts scalars along `A ⟶ Γ(U, 𝒪_U)`.  This is
  the spelling the Mittag-Leffler criteria [Stacks, Tag 0BLC] and [Stacks, Tag 0DXG] are stated
  in.
* `Stacks.LocalCohomologySequence.complementCohomologyBaseFunctor 𝔞 p` derives the sections
  *over the open `U`* of sheaves of modules on the *ambient* `X`, read over `A` through
  `A ≅ Γ(X, 𝒪_X)`.  This is the spelling the local-cohomology development uses, and the one
  carrying the natural comparison with local cohomology.

Both are precomposed with `Stacks.Algebraization.restrictedTildeFunctor S`, the functor
`N ↦ Ñ|_U`, on which the two agree.

## Main results

* `Stacks.Algebraization.openCohomologyRestrictedTildeNatIso` —
  `(− ↦ Ñ|_U) ⋙ H^p(U, −) ≅ H^p(U, −~)`, a natural isomorphism of functors
  `ModuleCat A ⥤ ModuleCat A`.
* `Stacks.Algebraization.openCohomologyLocalCohomologyNatIso` — the composite with
  [Stacks, Tag 0BK0] (2): for `p ≥ 1`, `(− ↦ Ñ|_U) ⋙ H^p(U, −) ≅ H^{p+1}_𝔞(−)`, naturally.

## Implementation notes

Everything is one whiskering of [Stacks, Tag 01E1] (2),
`Stacks.Cohomology.SchemeOpenSections.derivedSectionsOnOpenIso`, which already states — in every
degree and naturally in the sheaf — that deriving the sections over `U` of sheaves of modules on
`X` agrees with restricting to the open subscheme `U` and deriving global sections there.  What
had to be checked is that the two outer layers match on the nose, and they do:

* `Stacks.Cohomology.AffineBase.moduleGlobalSections S.U.toScheme` is
  `SheafOfModules.evaluation S.U.toScheme.ringCatSheaf (op ⊤)`, the functor
  `openCohomologyFunctor` derives, by definitional unfolding (the structure sheaf of the open
  subscheme *is* the restricted structure sheaf);
* `ModuleCat.restrictScalars S.U.ι.appTop.hom ⋙ globalToBase (CommRingCat.of S.A)` is
  `ModuleCat.restrictScalars (scalarMap S)`, because `scalarMap S` is the composite
  `A ≅ Γ(X, 𝒪_X) ⟶ Γ(U, 𝒪_U)` and iterated restriction of scalars is restriction along the
  composite;
* `Stacks.Algebraization.AlgebraizationSituation.U` and the open complement of the zero locus
  that `complementCohomologyBaseFunctor` is built on are the same element of `X.Opens`
  (`Stacks.Algebraization.U_eq_zeroLocusCompl`), and `tilde.functor` is
  `Stacks.LocalCohomologyTilde.tildeSheafFunctor`.

So the proof is a `Functor.isoWhiskerLeft` of a `Functor.isoWhiskerRight`, with the
associativity of functor composition definitional.

## References

* [Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0DXG](https://stacks.math.columbia.edu/tag/0DXG)
* [Stacks Project, Tag 0BLC](https://stacks.math.columbia.edu/tag/0BLC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.SchemeOpenSections
open Stacks.LocalCohomologyTilde
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

/-- **[Stacks, Tag 01E1] (2) in the two spellings of the 0DXW development.**  The cohomology of
`U = X ∖ V(𝔞)` computed on the open subscheme `U`, which is
`Stacks.Algebraization.openCohomologyFunctor`, agrees on the restricted associated sheaves `Ñ|_U`
with the cohomology over `U` of sheaves of modules on the ambient `X`, which is
`Stacks.LocalCohomologySequence.complementCohomologyBaseFunctor` — as a natural isomorphism of
functors `ModuleCat A ⥤ ModuleCat A`, in every degree.

`Stacks.Algebraization.finite_openCohomology_of_finite_complementCohomologyBase` compares the
same two spellings objectwise and only through finiteness, which is enough for the 0DXW route to
condition (a) of [Stacks, Tag 0EHH] and not enough for the 0DXU route: that one asks for the
image of a transition map `H^p(U, ℱₙ) ⟶ H^p(U, ℱ₁)` to have finite length, a statement about a
map. -/
def openCohomologyRestrictedTildeNatIso (S : AlgebraizationSituation.{u}) (p : ℕ) :
    restrictedTildeFunctor S ⋙ openCohomologyFunctor S p ≅
      Stacks.LocalCohomologySequence.complementCohomologyBaseFunctor
        (A := CommRingCat.of S.A) S.a p :=
  Functor.isoWhiskerLeft (tilde.functor (CommRingCat.of S.A))
    (Functor.isoWhiskerRight
      (derivedSectionsOnOpenIso S.X S.U p).symm
      (globalToBase (CommRingCat.of S.A)))

/-- **[Stacks, Tag 0BK0] (2) in the spelling the Mittag-Leffler criteria consume.**  For `p ≥ 1`
the cohomology `H^p(U, Ñ|_U)` of the restricted associated sheaf on the open subscheme
`U = X ∖ V(𝔞)` is the local cohomology `H^{p+1}_𝔞(N)`, naturally in `N`.

This is `Stacks.Algebraization.openCohomologyRestrictedTildeNatIso` followed by
`Stacks.Algebraization.complementCohomologyBaseLocalCohomologyNatIso`.  It is the comparison the
proof of [Stacks, Tag 0DXU] uses to turn its claim about the image of
`H^1(U, ℱₙ) ⟶ H^1(U, ℱ₁)` into a claim about the image of `H^2_𝔪(Mₙ) ⟶ H^2_𝔪(M₁)`, which is
where local duality and Matlis duality apply. -/
def openCohomologyLocalCohomologyNatIso (S : AlgebraizationSituation.{u}) (p : ℕ) (hp : 0 < p) :
    restrictedTildeFunctor S ⋙ openCohomologyFunctor S p ≅
      localCohomologyDegreeFunctor S.A S.a (Ideal.fg_of_isNoetherianRing S.a) ((p : ℤ) + 1) :=
  openCohomologyRestrictedTildeNatIso S p ≪≫
    complementCohomologyBaseLocalCohomologyNatIso S.a p hp

end Stacks.Algebraization

end
