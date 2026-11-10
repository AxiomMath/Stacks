module

public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Regular
public import StacksFrontier.RingTheory.GeometricallyRegular.FaithfullyFlatDescent

/-!
# Flat descent of geometric regularity

Geometric regularity at a point descends along a morphism which is flat at that point. As a
consequence, geometric regularity descends along flat surjective morphisms.

## Main results

* `AlgebraicGeometry.isGeometricallyRegularAt_of_flatAt` gives the pointwise descent result.
* `AlgebraicGeometry.isGeometricallyRegular_of_flat_surjective` gives its global consequence.

## Implementation notes

A morphism of schemes over `k` is represented by a morphism `f : X ⟶ Y` and the structure
morphism `g : Y ⟶ Spec k`; the structure morphism on `X` is then `f ≫ g`. The two declarations
separately record the pointwise assertion and the independent global consequence in the source.

## References

* [Stacks Project, Tag 05AW](https://stacks.math.columbia.edu/tag/05AW)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- **Stacks Project, Tag 05AW (pointwise statement).** Geometric regularity at a point
descends along a morphism which is flat at that point. -/
@[stacks 05AW "pointwise statement"]
public theorem isGeometricallyRegularAt_of_flatAt {k : Type u} [Field k]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Spec (.of k))
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (x : X)
    (hX : IsGeometricallyRegularAt (f ≫ g) x)
    (hf : AlgebraicGeometry.IsFlatAt f.toLRSHom.toShHom x) :
    IsGeometricallyRegularAt g (f x) := by
  let stalkAlg {Z : Scheme.{u}} (h : Z ⟶ Spec (.of k)) (z : Z) : Algebra k (Z.presheaf.stalk z) :=
    let : Algebra k ((Spec (.of k)).presheaf.stalk (h.base z)) :=
      StructureSheaf.stalkAlgebra k (h.base z)
    ((h.stalkMap z).hom.comp (algebraMap k ((Spec (.of k)).presheaf.stalk (h.base z)))).toAlgebra
  let : Algebra k (Y.presheaf.stalk (f x)) := stalkAlg g (f x)
  let : Algebra k (X.presheaf.stalk x) := stalkAlg (f ≫ g) x
  let : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  have : IsScalarTower k (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' (by
      simp only [RingHom.algebraMap_toAlgebra]
      rw [Scheme.Hom.stalkMap_comp]
      rfl)
  have : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    RingHom.flat_algebraMap_iff.mp (by
      change (f.stalkMap x).hom.Flat at hf
      simpa only [RingHom.algebraMap_toAlgebra] using hf)
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) := by
    change IsLocalHom (f.stalkMap x).hom; infer_instance
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hX' : Algebra.IsGeometricallyRegular k (X.presheaf.stalk x) :=
    ((geometricallyRegularAt_tfae k X (f ≫ g) x).out 1 3).mp hX
  exact ((geometricallyRegularAt_tfae k Y g (f x)).out 3 1).mp
    (Algebra.IsGeometricallyRegular.of_faithfullyFlat (X.presheaf.stalk x))

/-- **Stacks Project, Tag 05AW (global statement).** A flat surjective image of a
geometrically regular scheme over a field is geometrically regular. -/
@[stacks 05AW "global statement"]
public theorem isGeometricallyRegular_of_flat_surjective {k : Type u} [Field k]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Spec (.of k))
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Flat f] [Surjective f]
    (hX : IsGeometricallyRegular (f ≫ g)) :
    IsGeometricallyRegular g := by
  intro y
  obtain ⟨x, rfl⟩ := f.surjective y
  exact isGeometricallyRegularAt_of_flatAt f g x (hX x) (Flat.stalkMap f x)

end AlgebraicGeometry
