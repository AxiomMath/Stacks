module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.StrictlyPerfectInternalHomGeneral

/-!
# The internal Hom complex of a termwise split short complex, at unequal universes

Let `(C, O)` be a ringed site whose objects, morphisms and structure rings lie in three
independent universes, and let `E₁ ⟶ E₂ ⟶ E₃` be a short complex of complexes of `O`-modules
which is split in every degree. The internal Hom complex of Stacks 0A8Z into a fixed complex `B`
turns it into a short complex

`SheafHom(E₃, B) ⟶ SheafHom(E₂, B) ⟶ SheafHom(E₁, B)`

which is again split in every degree, hence short exact. This is needed on the small étale site
of an algebraic space, a `RingedSite.{u + 1, u, u}`, where the internal Hom complex of two
complexes of modules with sections in `u` has sections in `u + 1`.

Nothing is declared here: the termwise splitting and the product description of the terms it
rests on, with the universes recorded in the statements, are in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.StrictlyPerfectInternalHomGeneral`,
which this module makes available under its own name.

## Main results

* `AlgebraicGeometry.RingedSite.Raised.homDegreeIsLimit`: the degree-`n` term of
  `SheafHom(E, F)` is the product over `q : ℤ` of the internal Hom sheaves
  `SheafHom(E^{-q}, F^{n-q})`.
* `AlgebraicGeometry.RingedSite.Raised.internalHomShortComplex_shortExact`: the internal Hom
  complex out of a termwise split short complex of sources is short exact.

## References

* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 08JC](https://stacks.math.columbia.edu/tag/08JC)
-/
