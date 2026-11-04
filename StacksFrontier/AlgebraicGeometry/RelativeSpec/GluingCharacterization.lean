module

public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.RelativeSpec
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.Construction

/-!
# The relative spectrum, characterized by its affine charts

Let `s` be a relative-spectrum situation, that is a scheme `s.base` together with a
quasi-coherent sheaf `s.algebra` of commutative algebras over its structure sheaf. For every
affine open `U` of the base there is a canonical morphism `Spec s.algebra(U) ⟶ U`, and the
relative spectrum of `s.algebra` is the scheme over `s.base` into which these affine spectra
glue: each one is the inverse image of its affine open, and the open immersions between the
inverse images are the spectra of the restriction maps of the algebra.

That description is packaged as `Stacks.RelativeSpec.RelativeSpectrum` in
`StacksFrontier.AlgebraicGeometry.RelativeSpec.Construction`, which also exhibits the glued scheme
of `Stacks.AffineAlgebraEquivalence.relativeSpecGluingData` as an instance of it
(`Stacks.RelativeSpec.relativeSpectrum`) and proves that any two such descriptions of the same
situation are uniquely isomorphic over the base
(`Stacks.RelativeSpec.existsUnique_relativeSpectrumIso`). Both are re-exported here. This file
adds the reading of the canonical morphism `Spec s.algebra(U) ⟶ U` as a component of the natural
transformation underlying the relative gluing datum, and the values of the glued scheme and its
structure morphism.

## Main definitions

* `Stacks.RelativeSpec.affineSpecToOpen` is the canonical morphism from the spectrum of the
  sections of the algebra over an affine open to that open subscheme.

## Main results

* `Stacks.RelativeSpec.affineSpecToOpen_eq` identifies it with the component at that affine open
  of the natural transformation underlying the relative gluing datum.
* `Stacks.RelativeSpec.relativeSpectrum_scheme` and
  `Stacks.RelativeSpec.relativeSpectrum_toBase` compute the glued scheme and its structure
  morphism.

## References

* [Stacks Project, Tag 01LP](https://stacks.math.columbia.edu/tag/01LP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.RelativeSpec

/-- The canonical morphism from the spectrum of the algebra's sections on an affine open to that
open subscheme: the spectrum of the structure morphism of the algebra, followed by the canonical
isomorphism of the affine open with the spectrum of its sections. -/
public noncomputable abbrev affineSpecToOpen (s : RelativeSpecSituation.{u})
    (U : s.base.affineOpens) :
    Spec (s.algebra.right.obj.obj (.op U.1)) ⟶ U.1 :=
  Spec.map (s.algebra.hom.hom.app (.op U.1)) ≫ U.2.isoSpec.inv

/-- The charts of the relative spectrum are the components of the natural transformation
underlying the relative gluing datum. -/
public theorem affineSpecToOpen_eq (s : RelativeSpecSituation.{u}) (U : s.base.affineOpens) :
    affineSpecToOpen s U = (Stacks.AffineAlgebraEquivalence.specSectionsToBase s.algebra).app U :=
  rfl

/-- The scheme underlying `relativeSpectrum s` is the glued scheme `relativeSpec s.algebra`. -/
@[simp]
public theorem relativeSpectrum_scheme (s : RelativeSpecSituation.{u}) :
    (relativeSpectrum s).scheme = Stacks.AffineAlgebraEquivalence.relativeSpec s.algebra :=
  rfl

/-- The structure morphism of `relativeSpectrum s` is the morphism `relativeSpecToBase s.algebra`
from the glued scheme to the base. -/
@[simp]
public theorem relativeSpectrum_toBase (s : RelativeSpecSituation.{u}) :
    (relativeSpectrum s).toBase =
      Stacks.AffineAlgebraEquivalence.relativeSpecToBase s.algebra :=
  rfl

end Stacks.RelativeSpec

end
