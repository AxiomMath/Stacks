module

public import StacksFrontier.Deformation.Groupoid.BaseCategory

/-!
# Restriction of a groupoid in functors

Let `(U, R, s, t, c)` be a groupoid in functors on a category `D` and let `F : C ⥤ D` be a
functor, for instance the inclusion of a subcategory. The restriction of `(U, R, s, t, c)`
along `F` has object and arrow functors `F ⋙ U` and `F ⋙ R`, and its source, target and
composition are those of `(U, R, s, t, c)` whiskered by `F`; in particular they are given at an
object `T` of `C` by the source, target and composition of `(U, R, s, t, c)` at `F T`.

## Main results

* `Deformation.GroupoidInFunctors.restrict_source`,
  `Deformation.GroupoidInFunctors.restrict_target` and
  `Deformation.GroupoidInFunctors.restrict_comp`: the source, target and composition of a
  restriction are the whiskerings of the source, target and composition of the original
  groupoid in functors, which is what licenses denoting them by the same letters `s`, `t`, `c`.
* `Deformation.GroupoidInFunctors.restrict_compose`: composition of a composable pair of arrows
  of a restriction is their composition in the original groupoid in functors.

## References

* [Stacks Project, Tag 06KA](https://stacks.math.columbia.edu/tag/06KA)
-/

@[expose] public section

namespace Deformation

/-! ### Restriction of a groupoid in functors -/

section
open CategoryTheory
universe u v w x y

namespace GroupoidInFunctors

variable {C : Type u} {D : Type v} [Category.{w} C] [Category.{x} D]
  (G : GroupoidInFunctors.{v, x, y} D) (F : C ⥤ D)

/-- The object functor of a restriction is the object functor of the original groupoid in
functors, composed with the restricting functor. -/
@[simp]
public theorem restrict_objects : (G.restrict F).objects = F ⋙ G.objects := rfl

/-- The arrow functor of a restriction is the arrow functor of the original groupoid in
functors, composed with the restricting functor. -/
@[simp]
public theorem restrict_arrows : (G.restrict F).arrows = F ⋙ G.arrows := rfl

/-- The source of a restriction is the source of the original groupoid in functors,
whiskered by the restricting functor. -/
@[simp, stacks 06KA "source"]
public theorem restrict_source : (G.restrict F).source = F.whiskerLeft G.source := rfl

/-- The target of a restriction is the target of the original groupoid in functors,
whiskered by the restricting functor. -/
@[simp, stacks 06KA "target"]
public theorem restrict_target : (G.restrict F).target = F.whiskerLeft G.target := rfl

/-- The composition of a restriction is the composition of the original groupoid in functors,
whiskered by the restricting functor. -/
@[simp, stacks 06KA "composition"]
public theorem restrict_comp : (G.restrict F).comp = F.whiskerLeft G.comp := rfl

/-- The source of a restriction at an object `T` is the source of the original groupoid in
functors at `F T`. -/
public theorem restrict_source_app (T : C) (a : G.arrows.obj (F.obj T)) :
    (G.restrict F).source.app T a = G.source.app (F.obj T) a := rfl

/-- The target of a restriction at an object `T` is the target of the original groupoid in
functors at `F T`. -/
public theorem restrict_target_app (T : C) (a : G.arrows.obj (F.obj T)) :
    (G.restrict F).target.app T a = G.target.app (F.obj T) a := rfl

/-- Composition of a composable pair of arrows of a restriction at an object `T` is their
composition in the original groupoid in functors at `F T`. -/
public theorem restrict_compose (T : C) (a b : G.arrows.obj (F.obj T))
    (h : G.source.app (F.obj T) a = G.target.app (F.obj T) b) :
    (G.restrict F).compose T a b h = G.compose (F.obj T) a b h := rfl

end GroupoidInFunctors

end

end Deformation
