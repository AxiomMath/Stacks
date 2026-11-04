module

public import Mathlib.FieldTheory.KrullTopology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic

/-!
# Algebraic geometric points and absolute Galois groups

Let `sbar` be a geometric point of a scheme. Its morphism determines an embedding from the residue
field at its image into the algebraically closed field defining `sbar`. We call `sbar` algebraic
when this extension is an algebraic closure, and define the associated absolute Galois group using
the separable closure inside that field.

## Main definitions

* `AlgebraicGeometry.GeometricPoint.residueFieldHom` is the canonical embedding of the residue
  field at the image of a geometric point into its defining field.
* `AlgebraicGeometry.GeometricPoint.residueFieldAlgebra` is the corresponding algebra structure.
* `AlgebraicGeometry.GeometricPoint.separableClosure` is the separable closure of the residue field
  inside the field defining the geometric point.
* `AlgebraicGeometry.GeometricPoint.absoluteGaloisGroup` is its Galois group over the residue
  field.
* `AlgebraicGeometry.GeometricPoint.IsAlgebraic` says that a geometric point is algebraic.

## Implementation notes

The canonical residue-field embedding comes from `Scheme.SpecToEquivOfField`, the equivalence
between maps from the spectrum of a field and residue-field embeddings. The relative separable
closure is `separableClosure` and the predicate `GeometricPoint.IsAlgebraic` is `IsAlgClosure`,
both taken for the algebra structure given by this embedding.

## References

* [Stacks Project, Tag 03QX](https://stacks.math.columbia.edu/tag/03QX)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GeometricPoint

/-- The canonical embedding from the residue field at the image of a geometric point into the
algebraically closed field defining that geometric point. -/
@[implicit_reducible] noncomputable def residueFieldHom {S : AlgebraicGeometry.Scheme.{u}}
    (sbar : GeometricPoint S) :
    S.residueField (sbar.hom default) →+* sbar.residueField :=
  (((S.residueFieldCongr (by
    simp only [AlgebraicGeometry.Scheme.SpecToEquivOfField_apply_fst]
    exact congrArg sbar.hom (Subsingleton.elim _ _))).hom ≫
      ((S.SpecToEquivOfField sbar.residueField) sbar.hom).2).hom)

/-- The algebra structure on the field of a geometric point induced by its canonical residue-field
embedding. -/
@[instance_reducible] noncomputable def residueFieldAlgebra {S : AlgebraicGeometry.Scheme.{u}}
    (sbar : GeometricPoint S) :
    Algebra (S.residueField (sbar.hom default)) sbar.residueField :=
  (residueFieldHom sbar).toAlgebra

/-- The separable algebraic closure of the residue field at the image of a geometric point inside
its algebraically closed defining field. -/
@[stacks 03QX "the separable algebraic closure"]
noncomputable abbrev separableClosure {S : AlgebraicGeometry.Scheme.{u}}
    (sbar : GeometricPoint S) :=
  letI := residueFieldAlgebra sbar
  _root_.separableClosure (S.residueField (sbar.hom default)) sbar.residueField

/-- The absolute Galois group at a geometric point is the automorphism group of the separable
closure of the residue field at its image. -/
@[stacks 03QX "part (1): the absolute Galois group",
  sga "3 VIIB 3.3.3" "more general",
  sga "4 VIII 2.1" "more general",
  sga "4½ Arcata 2.4.2" "more general",
  sga "7 I 0.3",
  sga "7 XIII 0.2" "(0.2.5)",
  sga "7 XVI 1.6"]
noncomputable abbrev absoluteGaloisGroup {S : AlgebraicGeometry.Scheme.{u}}
    (sbar : GeometricPoint S) :=
  letI := residueFieldAlgebra sbar
  Gal(↑(separableClosure sbar) / S.residueField (sbar.hom default))

/-- A geometric point is algebraic when its algebraically closed defining field is algebraic over
the residue field at its image, and hence is an algebraic closure of that residue field. -/
@[stacks 03QX "part (2): algebraic geometric points"]
noncomputable abbrev IsAlgebraic {S : AlgebraicGeometry.Scheme.{u}}
    (sbar : GeometricPoint S) : Prop :=
  letI := residueFieldAlgebra sbar
  IsAlgClosure (S.residueField (sbar.hom default)) sbar.residueField

end AlgebraicGeometry.GeometricPoint
