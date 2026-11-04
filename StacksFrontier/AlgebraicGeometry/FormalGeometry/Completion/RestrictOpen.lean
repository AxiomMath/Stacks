module

public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationPullback
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Restriction along an open immersion preserves coherence

Let `f : Y ⟶ X` be an open immersion of schemes. Restriction of sheaves of modules along `f` is
isomorphic to pullback along `f`, so it inherits pullback's finiteness properties: it carries a
module of finite presentation to one of finite presentation, and — on a locally Noetherian base,
where coherence and finite presentation agree — a coherent module to a coherent module.

These are the forms the algebraization arguments of Stacks chapter 52 use. There the open
immersion is the inclusion `U ⟶ X` of the open complement of a closed subscheme, or of a smaller
neighbourhood of the closed locus inside it, and what has to be known is that the coherent module
being compared is still coherent after restriction.

## Main results

* `Stacks.Algebraization.isFinitePresentation_restrict_of_isOpenImmersion` — restriction along an
  open immersion preserves finite presentation.
* `Stacks.Algebraization.isCoherent_restrict_of_isOpenImmersion` — restriction along an open
  immersion preserves coherence.

## Implementation notes

`Stacks.AlgebraicGeometry.ReflexiveEquivalence.isCoherent_restrict` already has the special case
of the inclusion `U.ι` of an open subscheme. These are stated for an arbitrary open immersion,
which is the generality the comparison isomorphisms of the chapter are proved in: the morphism
there is `V.ι` for an open `V` of `U.toScheme`, composed into `X`, and it is not presented as the
inclusion of an open of the base.

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf`, and Stacks 01BQ
is stated over `Stacks.SheafOfModules.ringSheaf` of the underlying ringed space. Those are three
spellings of one category carrying separately declared instances, so `M.IsFinitePresentation`
cannot be left to instance search across them; it is passed positionally instead, rather than
reaching the same instance by relaxing definitional-equality transparency.

## References

* [Stacks Project, Tag 01BQ](https://stacks.math.columbia.edu/tag/01BQ)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Algebraization

/-- Restriction along an open immersion carries a module of finite presentation to a module of
finite presentation.

Restriction is isomorphic to pullback (`Scheme.Modules.restrictFunctorIsoPullback`), and pullback
preserves finite presentation by Stacks 01BQ. -/
public lemma isFinitePresentation_restrict_of_isOpenImmersion {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (M : X.Modules) [M.IsFinitePresentation] :
    ((Scheme.Modules.restrictFunctor f).obj M).IsFinitePresentation :=
  (SheafOfModules.isFinitePresentation Y.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback f).app M).symm
    (@Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _ f.toLRSHom.toShHom M
      ‹M.IsFinitePresentation›)

/-- Restriction along an open immersion carries a coherent module to a coherent module, over a
locally Noetherian base.

On a locally Noetherian scheme coherence is finite presentation (Stacks 01XZ), the source is
locally Noetherian because `f` is an open immersion, and finite presentation is preserved. -/
public lemma isCoherent_restrict_of_isOpenImmersion {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] [IsLocallyNoetherian X] (M : X.Modules) [M.IsCoherent] :
    ((Scheme.Modules.restrictFunctor f).obj M).IsCoherent :=
  have : IsLocallyNoetherian Y := isLocallyNoetherian_of_isOpenImmersion f
  have : M.IsFinitePresentation := isFinitePresentation_of_isCoherent M
  Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFinitePresentation _
    (isFinitePresentation_restrict_of_isOpenImmersion f M)

end Stacks.Algebraization

end
