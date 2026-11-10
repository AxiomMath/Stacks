module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationsOverSpace
public import StacksFrontier.Deformation.Groupoid.Basic

/-!
# Groupoids in algebraic spaces: definitions (Stacks 043W, 043X)

The definition of a groupoid in algebraic spaces over an algebraic space `B` (**Stacks 043W**),
its morphisms with their identity and composition, the underlying groupoid in presheaves, and the
pre-relation cut out by its target and source, which is a pre-equivalence relation
(**Stacks 043X**).

## Main definitions

* `AlgebraicGeometry.composableToPullback`
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces`: **Stacks 043W**, part (1).
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom`: **Stacks 043W**, part (2).
* `AlgebraicGeometry.Space.groupoidPreRelation`

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.points_isGroupoid`
* `AlgebraicGeometry.Space.groupoidPreRelation_isPreEquivalenceRelation`: **Stacks 043X**.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- The canonical map from the presheaf of composable pairs of arrows to the presheaf pullback of
the source and target morphisms. -/
noncomputable def composableToPullback {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {U R : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (s t : R ⟶ U) :
    Deformation.composableArrows U R s t ⟶ pullback s t :=
  pullback.lift
    { app := fun _ => ↾ fun p => p.1.1
      naturality := by intros; rfl }
    { app := fun _ => ↾ fun p => p.1.2
      naturality := by intros; rfl }
    (by ext T p; exact p.2)

/-- **Stacks 043W, part (1).** A groupoid in algebraic spaces over an algebraic space `B` over
`S`: algebraic spaces of objects and of arrows, both over `B`, with source, target and
composition over `B`, whose evaluation at every test scheme is a groupoid. -/
@[stacks 043W "part (1): groupoid in algebraic spaces"]
structure GroupoidInAlgebraicSpaces
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS) where
  /-- The algebraic space of objects. -/
  objects : AlgebraicSpaces C S hS
  /-- The algebraic space of arrows. -/
  arrows : AlgebraicSpaces C S hS
  /-- The object space is over the base. -/
  objectsToBase : objects ⟶ B
  /-- The arrow space is over the base. -/
  arrowsToBase : arrows ⟶ B
  /-- The source map. -/
  source : arrows ⟶ objects
  /-- The target map. -/
  target : arrows ⟶ objects
  /-- The source map is a morphism over the base. -/
  source_over : source ≫ objectsToBase = arrowsToBase
  /-- The target map is a morphism over the base. -/
  target_over : target ≫ objectsToBase = arrowsToBase
  /-- Composition on the algebraic-space fibre product. -/
  comp : AlgebraicSpaces.fiberProduct C S hS source target ⟶ arrows
  /-- Composition is a morphism over the base, computed along the first projection. -/
  comp_over : comp ≫ arrowsToBase =
    (ObjectProperty.homMk (pullback.fst source.hom target.hom) :
      AlgebraicSpaces.fiberProduct C S hS source target ⟶ arrows) ≫ arrowsToBase
  /-- At every test scheme these maps form a groupoid. -/
  pointwiseGroupoid : ∀ T, Nonempty (Deformation.PointwiseGroupoid
    (source.hom.app T) (target.hom.app T)
    (fun p => (composableToPullback source.hom target.hom ≫ comp.hom).app T p))

namespace GroupoidInAlgebraicSpaces

/-- The underlying groupoid in presheaves of a groupoid in algebraic spaces: the same data, with
the algebraicity of the objects and the morphisms over the base forgotten. -/
noncomputable def toGroupoidInFunctors {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    Deformation.GroupoidInFunctors ((BigFppfOver C S hS)ᵒᵖ) where
  objects := G.objects.obj
  arrows := G.arrows.obj
  source := G.source.hom
  target := G.target.hom
  comp := composableToPullback G.source.hom G.target.hom ≫ G.comp.hom
  pointwiseGroupoid := G.pointwiseGroupoid

/-- **Stacks 043W, part (1), as a statement about the quintuple.** The defining property of the
quintuple `(U, R, s, t, c)` of a groupoid in algebraic spaces over `B`: the source and the target
are morphisms over `B`, and at every test scheme `T` the quintuple of `T`-points is a groupoid
category. The latter is spelled out as: the `T`-points of the object space `U` are the objects of
a groupoid, an arrow `x ⟶ y` of that groupoid is the same thing as a `T`-point `a` of the arrow
space `R` with `s(a) = x` and `t(a) = y`, and the composite of two such arrows is the `T`-point
of `R` produced by the composition morphism `c`. -/
@[stacks 043W "part (1): the T-points of the quintuple are a groupoid category"]
theorem points_isGroupoid {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B) (T : (BigFppfOver C S hS)ᵒᵖ) :
    G.source ≫ G.objectsToBase = G.arrowsToBase ∧
      G.target ≫ G.objectsToBase = G.arrowsToBase ∧
      ∀ (x y z : G.toGroupoidInFunctors.Evaluation T) (g : x ⟶ y) (f : y ⟶ z),
        (G.toGroupoidInFunctors.evaluationArrowEquiv T x z (g ≫ f)).1 =
          (composableToPullback G.source.hom G.target.hom ≫ G.comp.hom).app T
            ⟨((G.toGroupoidInFunctors.evaluationArrowEquiv T y z f).1,
                (G.toGroupoidInFunctors.evaluationArrowEquiv T x y g).1),
              (G.toGroupoidInFunctors.evaluationArrowEquiv T y z f).2.1.trans
                (G.toGroupoidInFunctors.evaluationArrowEquiv T x y g).2.2.symm⟩ :=
  ⟨G.source_over, G.target_over,
    fun _ _ _ g f => G.toGroupoidInFunctors.evaluationArrowEquiv_comp T g f⟩

/-- **Stacks 043W, part (2).** A morphism of groupoids in algebraic spaces over the same base: a
morphism of the underlying groupoids in presheaves whose maps on objects and on arrows are
morphisms over the base. -/
@[stacks 043W "part (2): morphism of groupoids in algebraic spaces"]
structure Hom {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {B : AlgebraicSpaces C S hS}
    (G H : GroupoidInAlgebraicSpaces C S hS B) where
  /-- The underlying morphism of groupoids in presheaves. -/
  toGroupoidHom : Deformation.GroupoidInFunctors.Hom
    G.toGroupoidInFunctors H.toGroupoidInFunctors
  /-- The map on objects is a morphism over the base. -/
  mapObjects_over : toGroupoidHom.mapObjects ≫ H.objectsToBase.hom = G.objectsToBase.hom
  /-- The map on arrows is a morphism over the base. -/
  mapArrows_over : toGroupoidHom.mapArrows ≫ H.arrowsToBase.hom = G.arrowsToBase.hom

/-- **The identity morphism of a groupoid in algebraic spaces over `B`.** The identity morphism of
the underlying groupoid in presheaves, which is a morphism over the base because the identity
followed by either structure morphism is that structure morphism. -/
noncomputable def Hom.id {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B) : Hom G G where
  toGroupoidHom := Deformation.GroupoidInFunctors.Hom.id G.toGroupoidInFunctors
  mapObjects_over := Category.id_comp _
  mapArrows_over := Category.id_comp _

/-- **The composition of two morphisms of groupoids in algebraic spaces over `B`.** The
composition of the underlying morphisms of groupoids in presheaves, which is a morphism over the
base by the two given compatibilities applied in turn. -/
noncomputable def Hom.comp {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {B : AlgebraicSpaces C S hS}
    {G H K : GroupoidInAlgebraicSpaces C S hS B} (φ : Hom G H) (ψ : Hom H K) : Hom G K where
  toGroupoidHom := Deformation.GroupoidInFunctors.Hom.comp φ.toGroupoidHom ψ.toGroupoidHom
  mapObjects_over :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun m => φ.toGroupoidHom.mapObjects ≫ m) ψ.mapObjects_over).trans
        φ.mapObjects_over)
  mapArrows_over :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun m => φ.toGroupoidHom.mapArrows ≫ m) ψ.mapArrows_over).trans
        φ.mapArrows_over)

end GroupoidInAlgebraicSpaces

namespace Space

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- The pre-relation on the object space of a groupoid in algebraic spaces over `B`: the
morphism `(t, s)` to the fibre product of the object space with itself over `B`, taken in the
slice of presheaves over the underlying presheaf of `B`. -/
noncomputable abbrev groupoidPreRelation (G : GroupoidInAlgebraicSpaces C S hS B) :
    PreRelation (Over.mk G.arrowsToBase.hom) (Over.mk G.objectsToBase.hom) :=
  prod.lift
    (Over.homMk G.target.hom (congrArg (fun f : G.arrows ⟶ B => f.hom) G.target_over))
    (Over.homMk G.source.hom (congrArg (fun f : G.arrows ⟶ B => f.hom) G.source_over))

/-- A point of the arrow space over a test scheme relates the two points of the object space
that are its target and its source. -/
private theorem groupoidPreRelation_rel_of_arrow
    {G : GroupoidInAlgebraicSpaces C S hS B} {T : BigFppfOver C S hS}
    {b : yoneda.obj T ⟶ B.obj}
    (x y : TestPoint T b (Over.mk G.objectsToBase.hom))
    (a : {a : G.arrows.obj.obj (Opposite.op T) //
      G.source.hom.app (Opposite.op T) a = yonedaEquiv y.1 ∧
        G.target.hom.app (Opposite.op T) a = yonedaEquiv x.1}) :
    (groupoidPreRelation G).Rel b x y := by
  obtain ⟨a, hs, ht⟩ := a
  set r := yonedaEquiv.symm a with hrdef
  have key : ∀ (m : G.arrows.obj ⟶ G.objects.obj) (z : yoneda.obj T ⟶ G.objects.obj),
      m.app (Opposite.op T) a = yonedaEquiv z → r ≫ m = z := fun m z h => by
    apply yonedaEquiv.injective
    simpa [yonedaEquiv_comp, hrdef] using h
  have hbase : r ≫ G.arrowsToBase.hom = b := by
    rw [← congrArg (fun f : G.arrows ⟶ B => f.hom) G.target_over]
    change r ≫ G.target.hom ≫ G.objectsToBase.hom = b
    rw [← Category.assoc, key _ _ ht]
    exact x.2
  exact ⟨⟨r, hbase⟩, by simpa using key _ _ ht, by simpa using key _ _ hs⟩

/-- **Stacks 043X.** The pre-relation cut out by the target and source morphisms of a groupoid
in algebraic spaces is a pre-equivalence relation: on the points of every test scheme over the
base it is reflexive, symmetric and transitive, because those points and the arrows between
them form a groupoid. -/
@[stacks 043X]
theorem groupoidPreRelation_isPreEquivalenceRelation
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    IsPreEquivalenceRelation (groupoidPreRelation G) := by
  intro T b
  let P := Classical.choice (G.pointwiseGroupoid (Opposite.op T))
  let arrowOfRel : ∀ {x y : TestPoint T b (Over.mk G.objectsToBase.hom)},
      (groupoidPreRelation G).Rel b x y →
        @Quiver.Hom _ P.groupoid.toCategory.toQuiver (yonedaEquiv y.1) (yonedaEquiv x.1) :=
    fun {x y} h => (P.arrowEquiv (yonedaEquiv y.1) (yonedaEquiv x.1)).symm
      ⟨yonedaEquiv (Classical.choose h).1,
        by simpa [yonedaEquiv_comp] using congrArg yonedaEquiv (Classical.choose_spec h).2,
        by simpa [yonedaEquiv_comp] using congrArg yonedaEquiv (Classical.choose_spec h).1⟩
  refine ⟨fun x => ?_, fun {x y} h => ?_, fun {x y z} hxy hyz => ?_⟩
  · exact groupoidPreRelation_rel_of_arrow x x (P.arrowEquiv (yonedaEquiv x.1) (yonedaEquiv x.1)
      (@CategoryStruct.id _ P.groupoid.toCategory.toCategoryStruct (yonedaEquiv x.1)))
  · exact groupoidPreRelation_rel_of_arrow y x (P.arrowEquiv (yonedaEquiv x.1) (yonedaEquiv y.1)
      (@Groupoid.inv _ P.groupoid _ _ (arrowOfRel h)))
  · exact groupoidPreRelation_rel_of_arrow x z (P.arrowEquiv (yonedaEquiv z.1) (yonedaEquiv x.1)
      (@CategoryStruct.comp _ P.groupoid.toCategory.toCategoryStruct _ _ _
        (arrowOfRel hyz) (arrowOfRel hxy)))

end Space

end AlgebraicGeometry

end
