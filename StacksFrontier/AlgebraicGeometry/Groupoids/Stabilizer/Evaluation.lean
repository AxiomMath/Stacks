module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.Pullback
public import StacksFrontier.AlgebraicGeometry.Groupoids.FieldExtensionEvaluation

/-!
# Evaluation of a morphism of groupoid schemes

A morphism of groupoid schemes induces, on every test scheme over the base, a functor between
the groupoids of generalized points.

## Main definitions

* `Stacks.Groupoids.GroupoidScheme.Hom.evaluation` is the induced functor on generalized
  points.

## References

* [Stacks Project, Tag 0231](https://stacks.math.columbia.edu/tag/0231)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Groupoids.GroupoidScheme.Hom

/-- Evaluation of a morphism of groupoid schemes on a test scheme: the functor on generalized
points sending a generalized object `x` to `x` composed with the map on objects, and a
generalized arrow to its composite with the map on arrows. -/
@[implicit_reducible]
noncomputable def evaluation {S : Scheme.{u}} {G H : GroupoidScheme S} (F : Hom G H)
    (T : Over S) : Functor (G.Evaluation T) (H.Evaluation T) where
  obj x := x ≫ F.mapObjects
  map f :=
    { arrow := f.arrow ≫ F.mapArrows
      source_eq := by rw [Category.assoc, F.map_source, ← Category.assoc, f.source_eq]
      target_eq := by rw [Category.assoc, F.map_target, ← Category.assoc, f.target_eq] }
  map_id x := by
    apply EvaluationHom.ext
    change (x ≫ G.identity) ≫ F.mapArrows = (x ≫ F.mapObjects) ≫ H.identity
    simp only [Category.assoc, F.map_identity]
  map_comp f g := by
    apply EvaluationHom.ext
    change (pullback.lift g.arrow f.arrow _ ≫ G.comp) ≫ F.mapArrows =
      pullback.lift (g.arrow ≫ F.mapArrows) (f.arrow ≫ F.mapArrows) _ ≫ H.comp
    convert F.map_comp T g.arrow f.arrow (g.source_eq.trans f.target_eq.symm)
      (by
        rw [Category.assoc, F.map_source, ← Category.assoc, g.source_eq,
          Category.assoc, F.map_target, ← Category.assoc, f.target_eq]) using 1 <;>
      simp only [compose, Category.assoc]

end Stacks.Groupoids.GroupoidScheme.Hom

end
