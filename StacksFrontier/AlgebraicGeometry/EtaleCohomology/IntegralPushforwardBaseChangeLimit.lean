module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardBaseChange

/-!
# Étale base change for the direct image along an integral morphism

Consider a cartesian square
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
of schemes of a big étale site with `f` integral, and a sheaf of sets `F` on the small étale site
of `X`. Stacks 0EYP asserts `f'_* (g')⁻¹ F = g⁻¹ f_* F`. Over an affine base an integral
morphism is the limit of a directed system of finite morphisms, and `F` and its direct image are
the colimits of the corresponding systems of sheaves, so the comparison for `f` is a colimit of
the comparisons for finite morphisms; those are isomorphisms by Stacks 0959, and a colimit of
isomorphisms is an isomorphism.

## Main definitions

* `AlgebraicGeometry.FiniteBaseChangeStage` — a cartesian square over `g` with finite vertical
  morphism, together with a sheaf of sets on the small étale site of its upper right corner.
* `AlgebraicGeometry.IntegralBaseChangeColimitPresentation` — data exhibiting the canonical
  comparison for `f` as a colimit of the comparisons of a system of finite stages.

## Main results

* `AlgebraicGeometry.FiniteBaseChangeStage.isIso_comparison` — the comparison at a finite stage
  is an isomorphism; this is Stacks 0959 read on the stage.
* **Stacks 0EYP** itself is
  `AlgebraicGeometry.isIso_smallEtaleBaseChangeNatTrans_of_isIntegralHom_univ`, proved in
  `StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardBaseChangeLimitUnconditional`.

## Implementation notes

The presentation of the comparison as a colimit of the comparisons for finite morphisms is
carried as an explicit datum rather than constructed: it packages the three inputs the source's
proof takes from elsewhere — that an integral morphism over an affine base is a directed limit of
finite morphisms (Stacks 09YZ), that `F` is the colimit of the inverse images of its direct
images along the projections of that limit (Stacks 0EYN), and that direct image turns that
colimit into the colimit of the direct images at the stages (Stacks 09Z1). The datum asserts a
colimit presentation only; that the comparison is an isomorphism is not among its fields.

The two diagrams and the two cocones are constrained by isomorphisms to the stagewise sheaves and
by equalities of their colimit points to the two sides of the comparison, so that the datum is a
presentation of the canonical comparison and not of an arbitrary morphism. No condition is
imposed on the index category: filteredness is what makes such a presentation exist, and is not
needed to pass isomorphy through it.

## References

* [Stacks Project, Tag 0EYP](https://stacks.math.columbia.edu/tag/0EYP)
* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)
* [Stacks Project, Tag 09YZ](https://stacks.math.columbia.edu/tag/09YZ)
* [Stacks Project, Tag 0EYN](https://stacks.math.columbia.edu/tag/0EYN)
* [Stacks Project, Tag 09Z1](https://stacks.math.columbia.edu/tag/09Z1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v w u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

section Stage

variable {Y' Y : B.Scheme}

/-- A cartesian square over `g : Y' ⟶ Y` whose right vertical morphism `f` is finite, together
with a sheaf of sets on the small étale site of the upper right corner. This is the shape of
datum Stacks 0959 applies to. -/
public structure FiniteBaseChangeStage (g : Y' ⟶ Y) where
  /-- The upper right corner `X` of the square. -/
  upper : B.Scheme
  /-- The upper left corner `X'` of the square. -/
  upperBase : B.Scheme
  /-- The right vertical morphism `f : X ⟶ Y`. -/
  down : upper ⟶ Y
  /-- The left vertical morphism `f' : X' ⟶ Y'`. -/
  downBase : upperBase ⟶ Y'
  /-- The upper horizontal morphism `g' : X' ⟶ X`. -/
  across : upperBase ⟶ upper
  /-- The right vertical morphism is finite. -/
  isFinite : IsFinite (B.inclusion.map down)
  /-- The square is cartesian. -/
  isPullback : IsPullback (B.inclusion.map across) (B.inclusion.map downBase)
    (B.inclusion.map down) (B.inclusion.map g)
  /-- The square commutes in the underlying category of the big étale site. -/
  w : across ≫ down = downBase ≫ g
  /-- The sheaf of sets on the small étale site of the upper right corner. -/
  sheaf : Sheaf (SmallEtale.topology B upper.1 upper.property) (Type (u + 1))

namespace FiniteBaseChangeStage

variable {B} {g : Y' ⟶ Y} (s : FiniteBaseChangeStage B g)

/-- The source `g⁻¹ f_* F` of the comparison at a stage. -/
public abbrev pullbackPushforward : Sheaf (SmallEtale.topology B Y'.1 Y'.property)
    (Type (u + 1)) :=
  (B.smallPushforward s.down (Type (u + 1)) ⋙
    B.smallInverseImage g (Type (u + 1))).obj s.sheaf

/-- The target `f'_* (g')⁻¹ F` of the comparison at a stage. -/
public abbrev pushforwardPullback : Sheaf (SmallEtale.topology B Y'.1 Y'.property)
    (Type (u + 1)) :=
  (B.smallInverseImage s.across (Type (u + 1)) ⋙
    B.smallPushforward s.downBase (Type (u + 1))).obj s.sheaf

/-- The canonical base-change comparison `g⁻¹ f_* F ⟶ f'_* (g')⁻¹ F` at a stage. -/
public def comparison : s.pullbackPushforward ⟶ s.pushforwardPullback :=
  (smallEtaleBaseChangeNatTrans B s.across s.downBase s.down g s.w).app s.sheaf

/-- **Stacks 0959 at a finite stage.** The comparison attached to a cartesian square with finite
right vertical morphism is an isomorphism. -/
public instance isIso_comparison : IsIso s.comparison :=
  haveI := s.isFinite
  isIso_smallEtaleBaseChangeNatTrans B s.across s.downBase s.down g s.isPullback s.w s.sheaf

end FiniteBaseChangeStage

end Stage

section Integral

variable {X' X Y' Y : B.Scheme} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- Data presenting the canonical base-change comparison `g⁻¹ f_* F ⟶ f'_* (g')⁻¹ F` as a
colimit of the comparisons attached to a system of finite stages: two diagrams of sheaves on the
small étale site of `Y'` whose values are the two sides of the stagewise comparison, the
stagewise comparisons as a morphism of diagrams, and colimit cocones on the two sides of the
comparison for `f` compatible with it. -/
public structure IntegralBaseChangeColimitPresentation {J : Type w} [Category.{v} J]
    (h : g' ≫ f = f' ≫ g)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1))) where
  /-- The finite stage at an index. -/
  stage : J → FiniteBaseChangeStage B g
  /-- The diagram of the sources of the stagewise comparisons. -/
  src : J ⥤ Sheaf (SmallEtale.topology B Y'.1 Y'.property) (Type (u + 1))
  /-- The diagram of the targets of the stagewise comparisons. -/
  tgt : J ⥤ Sheaf (SmallEtale.topology B Y'.1 Y'.property) (Type (u + 1))
  /-- At each index the first diagram is `g⁻¹ f_{j,*} F_j`. -/
  srcIso : ∀ j, src.obj j ≅ (stage j).pullbackPushforward
  /-- At each index the second diagram is `f'_{j,*} (g'_j)⁻¹ F_j`. -/
  tgtIso : ∀ j, tgt.obj j ≅ (stage j).pushforwardPullback
  /-- The morphism of diagrams. -/
  comparison : src ⟶ tgt
  /-- At each index it is the canonical comparison of the stage. -/
  comparison_app : ∀ j, comparison.app j =
    (srcIso j).hom ≫ (stage j).comparison ≫ (tgtIso j).inv
  /-- A cocone on the first diagram. -/
  srcCocone : Cocone src
  /-- Its vertex is `g⁻¹ f_* F`. -/
  srcCocone_pt : srcCocone.pt =
    (B.smallPushforward f (Type (u + 1)) ⋙ B.smallInverseImage g (Type (u + 1))).obj F
  /-- `g⁻¹ f_* F` is the colimit of the first diagram. -/
  isColimitSrc : IsColimit srcCocone
  /-- A cocone on the second diagram. -/
  tgtCocone : Cocone tgt
  /-- Its vertex is `f'_* (g')⁻¹ F`. -/
  tgtCocone_pt : tgtCocone.pt =
    (B.smallInverseImage g' (Type (u + 1)) ⋙ B.smallPushforward f' (Type (u + 1))).obj F
  /-- `f'_* (g')⁻¹ F` is the colimit of the second diagram. -/
  isColimitTgt : IsColimit tgtCocone
  /-- The canonical comparison for `f` is the morphism of colimits induced by the stagewise
  comparisons. -/
  compat : ∀ j, srcCocone.ι.app j ≫ eqToHom srcCocone_pt ≫
      (smallEtaleBaseChangeNatTrans B g' f' f g h).app F =
    comparison.app j ≫ tgtCocone.ι.app j ≫ eqToHom tgtCocone_pt

end Integral

end AlgebraicGeometry

end
