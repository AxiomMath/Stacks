module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentAlgebraCongr

/-!
# The vocabulary of a quadruple read in the restriction vocabulary of the glueing tools

The data `ψ` of a quadruple of Section 01NS is a family of morphisms
`f^*𝒜_{id} ⟶ L^{⊗ i}` written with
`Stacks.RingedSpace.pullbackFunctor` applied to the morphism of ringed spaces underlying `f`,
that being the spelling in which this repository has the monoidality of the inverse image and
the comparison `f^*(X ⊗ Y) ≅ f^*X ⊗ f^*Y` of Tag 01CD. The tools that glue sheaves of modules
and morphisms between them along a covering — `Stacks.SheafOfModules.ModulesGlueData`,
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover`,
`Stacks.Descent.hom_ext_of_restrictFunctor_map_eq` — are written with
`AlgebraicGeometry.Scheme.Modules.restrict`. This file is the dictionary between the two.

## The two functors are the same functor

The first entry is not a comparison at all:
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.modulesPullback_eq_pullbackFunctor` says that
`AlgebraicGeometry.Scheme.Modules.pullback f` and `pullbackFunctor (ringedSpaceHom f)` are
**equal by `rfl`**, both being `CategoryTheory.SheafOfModules.pullback` of the structure-sheaf
morphism of `f`, the `CategoryTheory.Functor.IsRightAdjoint` arguments through which they are
built being proofs of one `Prop`. So no transport is owed between the inverse image of a
quadruple and Mathlib's inverse image; the two differ only in which name is written, and a
statement about one is a statement about the other.

What does cost something is `AlgebraicGeometry.Scheme.Modules.restrict`, which is *not* the
inverse image but only isomorphic to it, by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`. The two entries below carry the
source and the target of `ψ` across that isomorphism.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.restrictPullbackCompIso`: **the restriction
  along an open immersion `a` of the inverse image along `f` is the inverse image along
  `a ≫ f`** — the source of `ψ` read over a member of a covering of the test scheme.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.restrictLaurentPieceIso`: **the restriction
  along `a` of the degree-`n` piece of the Laurent algebra of `L` is the degree-`n` piece of the
  Laurent algebra of any invertible module identified with `a^*L`** — the target of `ψ` read
  over a member of a covering of the test scheme.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.modulesPullback_eq_pullbackFunctor`: the two
  spellings of the inverse image of sheaves of modules on schemes are the same functor.

## Implementation notes

`restrictLaurentPieceIso` takes the invertible module over the smaller scheme and an isomorphism
of it with `a^*L` as arguments rather than using `(L.restrict a)` itself. That is not a
weakening: it is what a glueing argument supplies (the chart module of the glueing datum, with
the comparison the datum provides), and it avoids asking instance search for the invertibility of
a restriction, which it cannot find — the registered instance,
`Stacks.PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj`, is keyed on the inverse image.
For the same reason the isomorphism is stated with
`...RelativeProjQcohSheaf.LaurentPullback.pullbackModule` rather than with
`AlgebraicGeometry.Scheme.Modules.pullback`: the two are equal by `rfl`, by
`modulesPullback_eq_pullbackFunctor`, but only the former is a key instance search matches.

## No tag is claimed

Nothing here states a clause of a tag; the file translates between two spellings of one functor
and transports the source and the target of `ψ` along one isomorphism.

## References

* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory

open AlgebraicGeometry Stacks.RingedSpace

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

/-- **The inverse image of sheaves of modules along a morphism of schemes is the inverse image
along the underlying morphism of ringed spaces.** Mathlib's
`AlgebraicGeometry.Scheme.Modules.pullback` and the `Stacks.RingedSpace.pullbackFunctor` in which
the data `ψ` of a quadruple of Section 01NS is written are the *same functor*, not two functors
to be compared: both are `CategoryTheory.SheafOfModules.pullback` of the structure-sheaf morphism
of `f`, and the `CategoryTheory.Functor.IsRightAdjoint` argument each supplies is a proof of a
`Prop`, so proof irrelevance identifies them. -/
theorem modulesPullback_eq_pullbackFunctor {T S : Scheme.{u}} (f : T ⟶ S) :
    Scheme.Modules.pullback f = pullbackFunctor (ringedSpaceHom f) :=
  rfl

/-- **The restriction along an open immersion of the inverse image along `f` is the inverse image
along the composite.** This reads the source `f^*𝒜_{id}` of the data `ψ` of a quadruple over a
member of a covering of the test scheme, which is where a glueing argument compares it with the
`ψ` of the quadruple given there. -/
def restrictPullbackCompIso {V T S : Scheme.{u}} (f : T ⟶ S) (a : V ⟶ T) [IsOpenImmersion a]
    (N : S.Modules) :
    Scheme.Modules.restrict ((Scheme.Modules.pullback f).obj N) a ≅
      (Scheme.Modules.pullback (a ≫ f)).obj N :=
  (Scheme.Modules.restrictFunctorIsoPullback a).app _ ≪≫ (Scheme.Modules.pullbackComp a f).app N

/-- `...RelativeProjQcohSheaf.restrictPullbackCompIso` at the spelling of the inverse image in
which the data `ψ` of a quadruple is written. The ascription is the only content: the two
spellings are equal by `...RelativeProjQcohSheaf.modulesPullback_eq_pullbackFunctor`. -/
def restrictPullbackFunctorCompIso {V T S : Scheme.{u}} (f : T ⟶ S) (a : V ⟶ T)
    [IsOpenImmersion a] (N : SheafOfModules.{u} (structureRingSheaf S.toRingedSpace)) :
    Scheme.Modules.restrict ((pullbackFunctor (ringedSpaceHom f)).obj N) a ≅
      (pullbackFunctor (ringedSpaceHom (a ≫ f))).obj N :=
  restrictPullbackCompIso f a N

/-- **The restriction along an open immersion of a piece of the Laurent algebra of `L` is the
corresponding piece of the Laurent algebra of `a^*L`**, read through any invertible module `L'`
identified with `a^*L`. This reads the target `L^{⊗ n}` of the data `ψ` of a quadruple over a
member of a covering of the test scheme.

The comparison is `...RelativeProjQcohSheaf.LaurentPullback.pieceIso`, which compares the
inverse image of the Laurent algebra with the Laurent algebra of the inverse image, preceded by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` to pass from the restriction to the
inverse image and followed by `...RelativeProjQcohSheaf.LaurentCongr.congrIso`, the degreewise
component of the functoriality of the Laurent algebra in its invertible module. -/
def restrictLaurentPieceIso {V T : Scheme.{u}} (a : V ⟶ T) [IsOpenImmersion a]
    (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
    (L' : SheafOfModules.{u} (structureRingSheaf V.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible V.toRingedSpace.presheaf (isSheafStruct V) L']
    (e : pullbackModule a L ≅ L') (n : ℤ) :
    Scheme.Modules.restrict ((laurent L).piece n) a ≅ (laurent L').piece n :=
  (Scheme.Modules.restrictFunctorIsoPullback a).app _ ≪≫ pieceIso a L n ≪≫ congrIso e n

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
