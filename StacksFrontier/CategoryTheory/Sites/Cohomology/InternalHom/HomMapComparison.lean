module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexFunctoriality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietorisAndHom.HomComplexMaps

/-!
# The two spellings of the induced map of internal Hom complexes agree

A morphism `g : K' ⟶ K` and a morphism `f : L ⟶ L'` of complexes of `O`-modules on a ringed
site induce a map of internal Hom complexes
`SheafHom(K, L) ⟶ SheafHom(K', L')`, by precomposition with `g` and postcomposition with `f`.
This development constructs that map twice: as
`AlgebraicGeometry.RingedSite.homMap`, defined degreewise through the conjugation of cochains,
and as `Stacks.Cohomology.InternalHom.sheafHomComplexMap`, the `map` field of the bundled
`Stacks.Cohomology.InternalHom.sheafHomComplexConstruction`.

This file identifies them.  Both are determined by their action on local sections — pre- and
postcomposition on each slice site — and that characterisation is exactly
`Stacks.Cohomology.InternalHom.IsInducedSheafHomComplexMap`, of which
`Stacks.Cohomology.InternalHom.induced_map_ext` is the uniqueness.

## Main results

* `Stacks.Cohomology.InternalHom.homMap_eq_sheafHomComplexMap`: the two maps are equal.

## Implementation notes

The identification is what joins the two halves of Stacks 08JC.  The derived internal Hom and
all of its comparison isomorphisms are stated in the `homMap` spelling, while the two
theorems saying that internal Hom carries a termwise split short exact sequence of complexes to
a termwise split short exact sequence — `internalHomComplex_termwiseSplit_first` and
`internalHomComplex_termwiseSplit_second`, which are the content of the source's proof of
08JC — are stated in the `sheafHomComplexMap` spelling.  Without this lemma neither can be fed
to the other.

The proof is the uniqueness of an induced map applied to the two characterisations that already
exist: `AlgebraicGeometry.RingedSite.sectionsIso_homMap_v`, part (1) of Stacks 0A90, is
literally the defining property for `homMap`, and the `map_isInduced` field is it for
`sheafHomComplexMap`.

Universes: `homMap` is stated for a site `RingedSite.{u, v, w}` with an independent module
universe, while `sheafHomComplexMap` fixes the module universe to `max u v w`.  They meet on the
diagonal site `RingedSite.{u, u, u}` with module universe `u`, which is the instantiation the
derived internal Hom uses, so that is where this file states the comparison.

## References

* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 08JC](https://stacks.math.columbia.edu/tag/08JC)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace Stacks.Cohomology.InternalHom

variable (X : AlgebraicGeometry.RingedSite.{u, u, u})
    [HasWeakSheafify X.J AddCommGrpCat.{u}]
    {K K' L L' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- The map of internal Hom complexes induced by `g` and `f` is the same however it is built:
`AlgebraicGeometry.RingedSite.homMap`, defined through the conjugation of cochains, agrees with
`Stacks.Cohomology.InternalHom.sheafHomComplexMap`, the bundled bifunctorial action.  Both act on
local sections by precomposition with `g` and postcomposition with `f`, and an induced map is
determined by that action. -/
theorem homMap_eq_sheafHomComplexMap (g : K' ⟶ K) (f : L ⟶ L') :
    AlgebraicGeometry.RingedSite.homMap X g f = sheafHomComplexMap X g f :=
  induced_map_ext
    (fun U n p q hpq s =>
      AlgebraicGeometry.RingedSite.sectionsIso_homMap_v X g f U n p q hpq s)
    ((sheafHomComplexConstruction X).map_isInduced g f)

end Stacks.Cohomology.InternalHom

end
