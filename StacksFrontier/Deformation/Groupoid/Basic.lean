module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.CategoryTheory.Grothendieck
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Types.Basic
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Cofibered

/-!
# Groupoids in functors on an arbitrary category

A groupoid in functors on a category is a groupoid object in the category of
set-valued functors. This file gives the definition, the identity and inverse maps, when such a
groupoid is representable, and the quotient of a groupoid in functors.

## Main definitions

* `GroupoidInFunctors` is a groupoid in type-valued functors on a category.
* `GroupoidInFunctors.Evaluation` is its groupoid after evaluation at an object.
* `GroupoidInFunctors.Hom` is a morphism of groupoids in functors.
* `GroupoidInFunctors.Hom.evaluation` is the induced functor between evaluated
  groupoids.
* `inverseArrow` is the inverse of an arrow in an evaluated groupoid.
* `RepresentablePresentation` records a presentation by two corepresentable
  functors for which the required pushout exists.
* `IsRepresentable` says that a groupoid in functors is isomorphic to the groupoid
  associated to such a presentation.
* `evaluationFunctor` evaluates a groupoid in functors in each fiber.
* `quotientMorphism` is the canonical map from the category of elements.

## Main results

* `PointwiseGroupoid.source_comp` and `PointwiseGroupoid.target_comp` compute the source and
  the target of a composite: the composite of a composable pair has the source of the second
  arrow and the target of the first.
* `existsUnique_identity` gives the unique natural identity map.
* `existsUnique_inverse` gives the unique natural inverse map.
* `quotientProjection_cofibered` states that the projection is cofibered
  in groupoids.

## Implementation notes

### Groupoids in functors

The pointwise groupoid condition is expressed using the groupoid whose morphisms from `x`
to `y` are arrows with source `x` and target `y`.  The groupoid structure is placed under
`Nonempty`: thus identities and inverses remain properties determined by the five pieces of
data in the source, rather than additional data.  `Evaluation`, `evaluationArrowEquiv`, and
`evaluationArrowEquiv_comp` expose the evaluated groupoid and identify its arrows and
composition with the source data.

Morphisms are recorded by their maps on objects and arrows and preservation of source, target,
identity, and composition.  `Hom.evaluation` constructs the functor required in the source;
`Hom.evaluation_obj` and `Hom.evaluation_map_arrow` characterize its object and arrow maps.
The resulting type carries the category structure specified in the source.

### Identity and inverse for a groupoid in functors

The two uniqueness assertions are independent, so identity and inverse are stated
separately. The pointwise identity is `GroupoidInFunctors.identity`; `inverseArrow`
uses the equivalence between evaluated morphisms and elements of the arrow functor.

### Representable groupoids in functors

The notation \(\underline U\) in the source is implemented by the covariant representable
functor `uliftCoyoneda.obj (op U)`.  The universe lift permits the functors to take values in
a larger universe.  By the covariant Yoneda embedding, the source and target natural
transformations are induced by morphisms `U ⟶ R`; consequently the pushout in the source is
exactly `HasPushout source target`.

The pointwise groupoid law is included in a presentation, while `IsRepresentable` asks for a
categorical isomorphism rather than an equality, as in the source definition.

### Quotients of groupoids in functors

The quotient category is Mathlib's `Grothendieck (evaluationFunctor G)`;
its projection is `Grothendieck.forget (evaluationFunctor G)`. These
existing constructions are adopted directly. The quotient morphism sends
`(T, x)` to `(T, x)`, and an arrow over `f` to the arrow over `f`
whose fiber component is the identity of the transported element.
The evaluation functors have implicit reducibility so their pointwise
groupoid instances and the canonical object and arrow descriptions
remain available to clients.

## References

* [Stacks Project, Tag 06K3](https://stacks.math.columbia.edu/tag/06K3)
* [Stacks Project, Tag 06K5](https://stacks.math.columbia.edu/tag/06K5)
* [Stacks Project, Tag 06K6](https://stacks.math.columbia.edu/tag/06K6)
* [Stacks Project, Tag 06KB](https://stacks.math.columbia.edu/tag/06KB)
-/

@[expose] public section

namespace Deformation

/-! ### Groupoids in functors -/

section
open CategoryTheory
universe u v w

/-- The assertion that source, target, and composition make `U` and `R` into a groupoid.

The order in the input of `comp` is `(f, g)` when the categorical composite is `g ≫ f`.
-/
structure PointwiseGroupoid {U R : Type w} (source target : R → U)
    (comp : { p : R × R // source p.1 = target p.2 } → R) where
  /-- A groupoid structure on the set of objects. -/
  groupoid : Groupoid.{w} U
  /-- An identification of its morphisms with the arrows having the prescribed endpoints. -/
  arrowEquiv : ∀ x y,
    (@Quiver.Hom U groupoid.toCategory.toQuiver x y) ≃
      { a : R // source a = x ∧ target a = y }
  /-- Categorical composition agrees with the specified composition map. -/
  comp_eq : ∀ {x y z : U}
    (g : @Quiver.Hom U groupoid.toCategory.toQuiver x y)
    (f : @Quiver.Hom U groupoid.toCategory.toQuiver y z),
    (arrowEquiv x z (@CategoryStruct.comp U groupoid.toCategory.toCategoryStruct x y z g f)).1 =
      comp ⟨((arrowEquiv y z f).1, (arrowEquiv x y g).1),
        (arrowEquiv y z f).2.1.trans (arrowEquiv x y g).2.2.symm⟩

namespace PointwiseGroupoid

variable {U R : Type w} {source target : R → U}
  {comp : { p : R × R // source p.1 = target p.2 } → R}

/-- The given composition map computes categorical composition: for a composable pair
`(a, b)`, that is one with `source a = target b`, the categorical composite of
`b : source b ⟶ target b` with `a : target b ⟶ target a` is the arrow `comp (a, b)`. -/
theorem comp_eq_arrowEquiv_comp (H : PointwiseGroupoid source target comp)
    (a b : R) (hab : source a = target b) :
    (H.arrowEquiv (source b) (target a)
        (@CategoryStruct.comp U H.groupoid.toCategory.toCategoryStruct
          (source b) (target b) (target a)
          ((H.arrowEquiv (source b) (target b)).symm ⟨b, rfl, rfl⟩)
          ((H.arrowEquiv (target b) (target a)).symm ⟨a, hab, rfl⟩))).1 =
      comp ⟨(a, b), hab⟩ := by
  simpa using H.comp_eq ((H.arrowEquiv (source b) (target b)).symm ⟨b, rfl, rfl⟩)
    ((H.arrowEquiv (target b) (target a)).symm ⟨a, hab, rfl⟩)

/-- The composite of a composable pair has the source of its second arrow. -/
theorem source_comp (H : PointwiseGroupoid source target comp)
    (a b : R) (hab : source a = target b) :
    source (comp ⟨(a, b), hab⟩) = source b := by
  rw [← H.comp_eq_arrowEquiv_comp a b hab]
  exact (H.arrowEquiv (source b) (target a) _).2.1

/-- The composite of a composable pair has the target of its first arrow. -/
theorem target_comp (H : PointwiseGroupoid source target comp)
    (a b : R) (hab : source a = target b) :
    target (comp ⟨(a, b), hab⟩) = target a := by
  rw [← H.comp_eq_arrowEquiv_comp a b hab]
  exact (H.arrowEquiv (source b) (target a) _).2.2

end PointwiseGroupoid

/-- The functor of composable pairs of arrows.  A pair `(f, g)` is composable when the source
of `f` is the target of `g`. -/
@[implicit_reducible]
def composableArrows {C : Type u} [Category.{v} C]
    (U R : Functor.{v, w} C (Type w)) (source target : R ⟶ U) :
    Functor.{v, w} C (Type w) where
  obj T := { p : R.obj T × R.obj T // source.app T p.1 = target.app T p.2 }
  map {X Y} f := ↾ fun p => ⟨(R.map f p.1.1, R.map f p.1.2), by
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, p.2]⟩
  map_id X := by ext p <;> simp
  map_comp f g := by ext p <;> simp

/-- A groupoid in functors on `C`: functors of objects and arrows with natural source, target,
and composition maps which give a groupoid after evaluation at every object of `C`. -/
@[stacks 06K3 "objects"]
structure GroupoidInFunctors (C : Type u) [Category.{v} C] where
  /-- The functor of objects. -/
  objects : Functor.{v, w} C (Type w)
  /-- The functor of arrows. -/
  arrows : Functor.{v, w} C (Type w)
  /-- The source natural transformation. -/
  source : arrows ⟶ objects
  /-- The target natural transformation. -/
  target : arrows ⟶ objects
  /-- Composition of composable arrows. -/
  comp : composableArrows objects arrows source target ⟶ arrows
  /-- Evaluation at every object is a groupoid. -/
  pointwiseGroupoid : ∀ T, Nonempty (PointwiseGroupoid (source.app T) (target.app T)
    (fun p ↦ comp.app T p))

namespace GroupoidInFunctors

/-- A chosen witness for the groupoid obtained by evaluating `G` at `T`.  Its observable
category structure is exposed through `Evaluation` and `evaluationArrowEquiv`. -/
noncomputable def pointwiseData {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors C) (T : C) :
    PointwiseGroupoid (G.source.app T) (G.target.app T) (fun p ↦ G.comp.app T p) :=
  Classical.choice (G.pointwiseGroupoid T)

/-- The groupoid obtained by evaluating a groupoid in functors at `T`. -/
@[implicit_reducible]
def Evaluation {C : Type u} [Category.{v} C] (G : GroupoidInFunctors C) (T : C) :=
  G.objects.obj T

/-- The groupoid structure on the evaluation of a groupoid in functors at `T`. -/
noncomputable instance evaluationGroupoid {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors C) (T : C) : Groupoid.{w} (G.Evaluation T) :=
  (G.pointwiseData T).groupoid

/-- Arrows in the evaluated groupoid are precisely elements of the arrow functor with the
given source and target. -/
noncomputable def evaluationArrowEquiv {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors C) (T : C) (x y : G.Evaluation T) :
    (x ⟶ y) ≃ { a : G.arrows.obj T // G.source.app T a = x ∧ G.target.app T a = y } :=
  (G.pointwiseData T).arrowEquiv x y

/-- The composite of two composable arrows in a groupoid in functors. -/
@[implicit_reducible]
def compose {C : Type u} [Category.{v} C] (G : GroupoidInFunctors C) (T : C)
    (a b : G.arrows.obj T) (h : G.source.app T a = G.target.app T b) : G.arrows.obj T :=
  G.comp.app T (show { p : G.arrows.obj T × G.arrows.obj T //
    G.source.app T p.1 = G.target.app T p.2 } from ⟨(a, b), h⟩)

/-- The arrow representing an identity in an evaluated groupoid. -/
noncomputable def identity {C : Type u} [Category.{v} C] (G : GroupoidInFunctors C)
    (T : C) (x : G.Evaluation T) : G.arrows.obj T :=
  (G.evaluationArrowEquiv T x x (𝟙 x)).1

/-- The identity of `x` in the evaluated groupoid corresponds to the arrow
`GroupoidInFunctors.identity T x`. -/
@[simp]
theorem evaluationArrowEquiv_id {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors C) (T : C) (x : G.Evaluation T) :
    (G.evaluationArrowEquiv T x x (𝟙 x)).1 = G.identity T x := rfl

/-- The specified composition map represents categorical composition in every evaluation. -/
@[simp]
theorem evaluationArrowEquiv_comp {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors C) (T : C) {x y z : G.Evaluation T}
    (g : x ⟶ y) (f : y ⟶ z) :
    (G.evaluationArrowEquiv T x z (g ≫ f)).1 =
      G.compose T (G.evaluationArrowEquiv T y z f).1
        (G.evaluationArrowEquiv T x y g).1
        ((G.evaluationArrowEquiv T y z f).2.1.trans
          (G.evaluationArrowEquiv T x y g).2.2.symm) :=
  (G.pointwiseData T).comp_eq g f

/-- A morphism of groupoids in functors. -/
@[ext, stacks 06K3 "morphisms"]
structure Hom {C : Type u} [Category.{v} C]
    (G H : GroupoidInFunctors C) where
  /-- The natural map on objects. -/
  mapObjects : G.objects ⟶ H.objects
  /-- The natural map on arrows. -/
  mapArrows : G.arrows ⟶ H.arrows
  map_source : ∀ (T : C) (a : G.arrows.obj T),
    H.source.app T (mapArrows.app T a) = mapObjects.app T (G.source.app T a)
  map_target : ∀ (T : C) (a : G.arrows.obj T),
    H.target.app T (mapArrows.app T a) = mapObjects.app T (G.target.app T a)
  map_id : ∀ (T : C) (x : G.Evaluation T),
    mapArrows.app T (G.identity T x) = H.identity T (mapObjects.app T x)
  map_comp : ∀ (T : C) (a b : G.arrows.obj T)
      (h : G.source.app T a = G.target.app T b),
    H.compose T (mapArrows.app T a) (mapArrows.app T b)
        ((map_source T a).trans ((congrArg (mapObjects.app T) h).trans (map_target T b).symm)) =
      mapArrows.app T (G.compose T a b h)

/-- Evaluation of a morphism of groupoids in functors is the functor specified in the source
definition. -/
@[implicit_reducible]
noncomputable def Hom.evaluation {C : Type u} [Category.{v} C]
    {G H : GroupoidInFunctors C} (F : Hom G H) (T : C) : G.Evaluation T ⥤ H.Evaluation T where
  obj x := F.mapObjects.app T x
  map {x y} f := (H.evaluationArrowEquiv T _ _).symm
    ⟨F.mapArrows.app T (G.evaluationArrowEquiv T x y f).1,
      (F.map_source T _).trans (congrArg (F.mapObjects.app T) (G.evaluationArrowEquiv T x y f).2.1),
      (F.map_target T _).trans (congrArg (F.mapObjects.app T) (G.evaluationArrowEquiv T x y f).2.2)⟩
  map_id x := by
    apply (H.evaluationArrowEquiv T _ _).injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    simp only [evaluationArrowEquiv_id]
    exact F.map_id T x
  map_comp f g := by
    apply (H.evaluationArrowEquiv T _ _).injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    simp only [evaluationArrowEquiv_comp, Equiv.apply_symm_apply]
    exact (F.map_comp T _ _ _).symm

/-- On objects, the evaluation of a morphism of groupoids in functors is its map on objects. -/
@[simp]
theorem Hom.evaluation_obj {C : Type u} [Category.{v} C]
    {G H : GroupoidInFunctors C} (F : Hom G H) (T : C) (x : G.Evaluation T) :
    (F.evaluation T).obj x = F.mapObjects.app T x := rfl

/-- The arrow map of `Hom.evaluation` is the given map on the arrow functors. -/
@[simp]
theorem Hom.evaluation_map_arrow {C : Type u} [Category.{v} C]
    {G H : GroupoidInFunctors C} (F : Hom G H) (T : C)
    {x y : G.Evaluation T} (f : x ⟶ y) :
    (H.evaluationArrowEquiv T _ _ ((F.evaluation T).map f)).1 =
      F.mapArrows.app T (G.evaluationArrowEquiv T x y f).1 :=
  congrArg Subtype.val (Equiv.apply_symm_apply _ _)

/-- The identity morphism of a groupoid in functors. -/
@[simps]
def Hom.id {C : Type u} [Category.{v} C] (G : GroupoidInFunctors C) : Hom G G where
  mapObjects := 𝟙 G.objects
  mapArrows := 𝟙 G.arrows
  map_source _ _ := rfl
  map_target _ _ := rfl
  map_id _ _ := rfl
  map_comp _ _ _ _ := rfl

/-- Composition of morphisms of groupoids in functors. -/
@[simps]
def Hom.comp {C : Type u} [Category.{v} C] {G H K : GroupoidInFunctors C}
    (f : Hom G H) (g : Hom H K) : Hom G K where
  mapObjects := f.mapObjects ≫ g.mapObjects
  mapArrows := f.mapArrows ≫ g.mapArrows
  map_source T a := by simp [f.map_source, g.map_source]
  map_target T a := by simp [f.map_target, g.map_target]
  map_id T x := by simp [f.map_id, g.map_id]
  map_comp T a b h := by
    have hf : H.source.app T (f.mapArrows.app T a) =
        H.target.app T (f.mapArrows.app T b) :=
      (f.map_source T a).trans ((congrArg (f.mapObjects.app T) h).trans (f.map_target T b).symm)
    have hg : K.source.app T (g.mapArrows.app T (f.mapArrows.app T a)) =
        K.target.app T (g.mapArrows.app T (f.mapArrows.app T b)) :=
      (g.map_source T (f.mapArrows.app T a)).trans
        ((congrArg (g.mapObjects.app T) hf).trans (g.map_target T (f.mapArrows.app T b)).symm)
    change K.compose T (g.mapArrows.app T (f.mapArrows.app T a))
        (g.mapArrows.app T (f.mapArrows.app T b)) hg =
        g.mapArrows.app T (f.mapArrows.app T (G.compose T a b h))
    rw [g.map_comp T _ _ hf, f.map_comp]

/-- Groupoids in functors on `C` and their morphisms form a category. -/
instance {C : Type u} [Category.{v} C] : Category (GroupoidInFunctors C) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by ext <;> simp
  comp_id f := by ext <;> simp
  assoc f g h := by ext <;> simp

end GroupoidInFunctors

end

/-! ### Identity and inverse for a groupoid in functors -/

section
open CategoryTheory
universe u v w

private abbrev EvalHom {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors.{u, v, w} C) (T : C) (x y : G.Evaluation T) :=
  @Quiver.Hom (G.Evaluation T) (G.evaluationGroupoid T).toCategory.toQuiver x y

private noncomputable def evalMap {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors.{u, v, w} C) {T T' : C} (f : T ⟶ T')
    {x y : G.Evaluation T} (g : EvalHom G T x y) :
    EvalHom G T' (G.objects.map f x) (G.objects.map f y) := by
  let a := G.evaluationArrowEquiv T x y g
  exact (G.evaluationArrowEquiv T' (G.objects.map f x) (G.objects.map f y)).symm
    ⟨G.arrows.map f a.1,
      by simp [a.2.1],
      by simp [a.2.2]⟩

private theorem evalMap_comp {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors.{u, v, w} C) {T T' : C} (f : T ⟶ T')
    {x y z : G.Evaluation T} (g : EvalHom G T x y) (h : EvalHom G T y z) :
    evalMap G f (g ≫ h) = evalMap G f g ≫ evalMap G f h := by
  apply (G.evaluationArrowEquiv T' (G.objects.map f x) (G.objects.map f z)).injective
  apply Subtype.ext
  let a := G.evaluationArrowEquiv T x y g
  let b := G.evaluationArrowEquiv T y z h
  let D := composableArrows G.objects G.arrows G.source G.target
  let p : D.obj T := ⟨(b.1, a.1), b.2.1.trans a.2.2.symm⟩
  simp only [evalMap, Equiv.apply_symm_apply]
  rw [G.evaluationArrowEquiv_comp, G.evaluationArrowEquiv_comp]
  simp only [GroupoidInFunctors.compose]
  simp only [Equiv.apply_symm_apply]
  exact (NatTrans.naturality_apply G.comp f p).symm

private noncomputable def evalFunctor {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors.{u, v, w} C) {T T' : C} (f : T ⟶ T') :
    G.Evaluation T ⥤ G.Evaluation T' where
  obj := G.objects.map f
  map := evalMap G f
  map_id x := by
    let := G.evaluationGroupoid T'
    let b := evalMap G f (𝟙 x)
    have hb : b = b ≫ b := by
      simpa [b] using (evalMap_comp G f (𝟙 x) (𝟙 x))
    calc
      b = b ≫ 𝟙 _ := by simp
      _ = b ≫ (b ≫ Groupoid.inv b) := by rw [Groupoid.comp_inv]
      _ = (b ≫ b) ≫ Groupoid.inv b := by rw [Category.assoc]
      _ = b ≫ Groupoid.inv b := by rw [← hb]
      _ = 𝟙 _ := Groupoid.comp_inv b
  map_comp g h := evalMap_comp G f g h

/-- The map on arrows along `f` sends the identity arrow at `x` to the identity arrow at
`G.objects.map f x`. -/
public theorem evalMap_identity {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors.{u, v, w} C) {T T' : C} (f : T ⟶ T')
    (x : G.Evaluation T) :
    G.arrows.map f (G.identity T x) = G.identity T' (G.objects.map f x) := by
  let := G.evaluationGroupoid T
  let := G.evaluationGroupoid T'
  have h := (evalFunctor G f).map_id x
  have h' := congrArg
    (fun g : EvalHom G T' (G.objects.map f x) (G.objects.map f x) =>
      (G.evaluationArrowEquiv T' (G.objects.map f x) (G.objects.map f x) g).1) h
  simp only [evalFunctor] at h'
  simpa only [evalMap, Equiv.apply_symm_apply, GroupoidInFunctors.identity] using h'

/-- The inverse of an arrow in the groupoid obtained by evaluating a groupoid in functors. -/
public noncomputable def inverseArrow {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors.{u, v, w} C) (T : C) (a : G.arrows.obj T) :
    G.arrows.obj T := by
  letI := G.evaluationGroupoid T
  exact (G.evaluationArrowEquiv T (G.target.app T a) (G.source.app T a)
    (Groupoid.inv ((G.evaluationArrowEquiv T (G.source.app T a)
      (G.target.app T a)).symm ⟨a, rfl, rfl⟩))).1

/-- The inverse of an arrow has the target of the arrow as source and its source as target. -/
private theorem inverseArrow_source_target {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors.{u, v, w} C) (T : C) (a : G.arrows.obj T) :
    G.source.app T (inverseArrow G T a) = G.target.app T a ∧
      G.target.app T (inverseArrow G T a) = G.source.app T a := by
  let := G.evaluationGroupoid T
  unfold inverseArrow
  exact (G.evaluationArrowEquiv T _ _ _).2

/-- The source of the inverse of an arrow is the target of that arrow. -/
public theorem inverseArrow_source {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors.{u, v, w} C) (T : C) (a : G.arrows.obj T) :
    G.source.app T (inverseArrow G T a) = G.target.app T a :=
  (inverseArrow_source_target G T a).1

/-- The target of the inverse of an arrow is the source of that arrow. -/
public theorem inverseArrow_target {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors.{u, v, w} C) (T : C) (a : G.arrows.obj T) :
    G.target.app T (inverseArrow G T a) = G.source.app T a :=
  (inverseArrow_source_target G T a).2

/-- Composition commutes with transport along morphisms of the base. -/
public theorem compose_natural {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors.{u, v, w} C) {T T' : C} (f : T ⟶ T')
    (a b : G.arrows.obj T) (h : G.source.app T a = G.target.app T b)
    (h' : G.source.app T' (G.arrows.map f a) = G.target.app T' (G.arrows.map f b)) :
    G.arrows.map f (G.compose T a b h) =
      G.compose T' (G.arrows.map f a) (G.arrows.map f b) h' := by
  exact (NatTrans.naturality_apply G.comp f
    (⟨(a, b), h⟩ : { p : G.arrows.obj T × G.arrows.obj T //
      G.source.app T p.1 = G.target.app T p.2 })).symm

/-- Inverses commute with transport along morphisms of the base. -/
public theorem evalMap_inverse {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors.{u, v, w} C) {T T' : C} (f : T ⟶ T')
    (a : G.arrows.obj T) :
    G.arrows.map f (inverseArrow G T a) =
      inverseArrow G T' (G.arrows.map f a) := by
  let := G.evaluationGroupoid T
  let := G.evaluationGroupoid T'
  let x := G.source.app T a
  let y := G.target.app T a
  let b := inverseArrow G T a
  let a' := G.arrows.map f a
  let b' := G.arrows.map f b
  let x' := G.source.app T' a'
  let y' := G.target.app T' a'
  have hax : x' = G.objects.map f x := by
    simp [x', a', x]
  have hay : y' = G.objects.map f y := by
    simp [y', a', y]
  have hbx : G.source.app T' b' = y' := by
    calc
      G.source.app T' b' = G.objects.map f (G.source.app T b) :=
        NatTrans.naturality_apply G.source f b
      _ = G.objects.map f y := congrArg (G.objects.map f) (inverseArrow_source G T a)
      _ = y' := hay.symm
  have hby : G.target.app T' b' = x' := by
    calc
      G.target.app T' b' = G.objects.map f (G.target.app T b) :=
        NatTrans.naturality_apply G.target f b
      _ = G.objects.map f x := congrArg (G.objects.map f) (inverseArrow_target G T a)
      _ = x' := hax.symm
  let := G.evaluationGroupoid T'
  let qa := G.evaluationArrowEquiv T' x' y'
  let qi := G.evaluationArrowEquiv T' y' x'
  let fa := qa.symm ⟨a', rfl, rfl⟩
  let fb := qi.symm ⟨b', hbx, hby⟩
  have hs : G.source.app T a = G.target.app T b := by
    rw [inverseArrow_target]
  have hc : G.compose T a b hs = G.identity T y := by
    let := G.evaluationGroupoid T
    let q := G.evaluationArrowEquiv T x y
    let f₀ := q.symm ⟨a, rfl, rfl⟩
    have h := congrArg
      (fun g : EvalHom G T y y => (G.evaluationArrowEquiv T y y g).1)
      (Groupoid.inv_comp f₀)
    change G.compose T a (inverseArrow G T a) _ = G.identity T y
    simpa only [G.evaluationArrowEquiv_comp, G.evaluationArrowEquiv_id,
      GroupoidInFunctors.compose, inverseArrow, x, y, q, f₀,
      Equiv.apply_symm_apply] using h
  have hcat : @CategoryStruct.comp (G.Evaluation T')
      (G.evaluationGroupoid T').toCategory.toCategoryStruct y' x' y' fb fa =
      @CategoryStruct.id (G.Evaluation T')
        (G.evaluationGroupoid T').toCategory.toCategoryStruct y' := by
    apply (G.evaluationArrowEquiv T' y' y').injective
    apply Subtype.ext
    simp only [G.evaluationArrowEquiv_comp, G.evaluationArrowEquiv_id]
    simp only [Equiv.apply_symm_apply, qa, qi, fa, fb]
    have hcomp := compose_natural G f a b hs hby.symm
    calc
      G.compose T' a' b' hby.symm = G.arrows.map f (G.compose T a b hs) := hcomp.symm
      _ = G.arrows.map f (G.identity T y) := congrArg (G.arrows.map f) hc
      _ = G.identity T' (G.objects.map f y) := evalMap_identity G f y
      _ = G.identity T' y' := congrArg (G.identity T') hay.symm
  have hinv : fb = Groupoid.inv fa := by
    calc
      fb = fb ≫ 𝟙 _ := by simp
      _ = fb ≫ (fa ≫ Groupoid.inv fa) := by rw [Groupoid.comp_inv]
      _ = (fb ≫ fa) ≫ Groupoid.inv fa := by rw [← Category.assoc]
      _ = 𝟙 _ ≫ Groupoid.inv fa := by rw [hcat]
      _ = Groupoid.inv fa := by simp
  have h := congrArg (fun g : EvalHom G T' y' x' => (qi g).1) hinv
  simpa only [Equiv.apply_symm_apply, inverseArrow, a', b', b, fa, fb, qa, qi,
    x', y'] using h

/-- Pointwise identities uniquely assemble into a natural transformation from objects
to arrows. -/
@[stacks 06K5 "identity"]
public theorem existsUnique_identity {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors.{u, v, w} C) :
    ∃! e : G.objects ⟶ G.arrows,
      ∀ (T : C) (x : G.Evaluation T), e.app T x = G.identity T x := by
  refine ⟨{
    app T := ConcreteCategory.ofHom (TypeCat.Fun.mk fun x => G.identity T x)
    naturality := by
      intro T T' f
      ext x
      change G.identity T' (G.objects.map f x) = G.arrows.map f (G.identity T x)
      exact (evalMap_identity G f x).symm
  }, ?_, ?_⟩
  · intro T x; rfl
  · intro e' he'; ext T x; exact he' T x

/-- Pointwise inverses uniquely assemble into a natural transformation of the arrow
functor. -/
@[stacks 06K5 "inverse"]
public theorem existsUnique_inverse {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors.{u, v, w} C) :
    ∃! i : G.arrows ⟶ G.arrows,
      ∀ (T : C) (a : G.arrows.obj T), i.app T a = inverseArrow G T a := by
  refine ⟨{
    app T := ConcreteCategory.ofHom (TypeCat.Fun.mk fun a => inverseArrow G T a)
    naturality := by
      intro T T' f
      ext a
      change inverseArrow G T' (G.arrows.map f a) =
        G.arrows.map f (inverseArrow G T a)
      exact (evalMap_inverse G f a).symm
  }, ?_, ?_⟩
  · intro T a; rfl
  · intro i' hi'; ext T a; exact hi' T a

end

/-! ### Representable groupoids in functors -/

section
open CategoryTheory CategoryTheory.Limits Opposite
universe u v w


/-- Data presenting a groupoid in functors by two covariant representable functors, with the
pushout required in the definition of representability. -/
public structure RepresentablePresentation (C : Type u) [Category.{v} C] where
  /-- The object corepresenting the functor of objects. -/
  objects : C
  /-- The object corepresenting the functor of arrows. -/
  arrows : C
  /-- The morphism inducing the source natural transformation. -/
  source : objects ⟶ arrows
  /-- The morphism inducing the target natural transformation. -/
  target : objects ⟶ arrows
  /-- Composition of composable arrows. -/
  comp : composableArrows (uliftCoyoneda.{w}.obj (op objects)) (uliftCoyoneda.{w}.obj (op arrows))
    (uliftCoyoneda.{w}.map source.op) (uliftCoyoneda.{w}.map target.op) ⟶ uliftCoyoneda.{w}.obj (op
      arrows)
  /-- The specified data form a groupoid after evaluation at every object. -/
  pointwiseGroupoid : ∀ T, Nonempty (PointwiseGroupoid ((uliftCoyoneda.{w}.map source.op).app T)
    ((uliftCoyoneda.{w}.map target.op).app T) (fun p ↦ comp.app T p))
  /-- The pushout of the two maps representing source and target exists. -/
  hasPushout : HasPushout source target

namespace RepresentablePresentation

/-- The groupoid in functors associated to a representable presentation. -/
@[implicit_reducible] public def groupoidInFunctors {C : Type u} [Category.{v} C] (P :
  RepresentablePresentation.{u, v, w} C) : GroupoidInFunctors.{u, v, max w v} C where
  objects := uliftCoyoneda.{w}.obj (op P.objects)
  arrows := uliftCoyoneda.{w}.obj (op P.arrows)
  source := uliftCoyoneda.{w}.map P.source.op
  target := uliftCoyoneda.{w}.map P.target.op
  comp := P.comp
  pointwiseGroupoid := P.pointwiseGroupoid

end RepresentablePresentation

/-- A groupoid in functors is representable if it is isomorphic to one presented by
covariant representable functors of objects and arrows, and the pushout of the two morphisms
representing source and target exists. -/
@[stacks 06K6]
public def IsRepresentable {C : Type u} [Category.{v} C] (G : GroupoidInFunctors.{u,
  v, max w v} C) : Prop := ∃ P : RepresentablePresentation.{u, v, w} C, Nonempty (G ≅
    P.groupoidInFunctors)

end

/-! ### Quotients of groupoids in functors -/

section
open CategoryTheory
universe u v w

/-- Transport of the groupoid of arrows along a morphism of the base category. -/
@[implicit_reducible]
public noncomputable def evaluationMap {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors.{u, v, w} C) {T S : C} (f : T ⟶ S) :
    G.Evaluation T ⥤ G.Evaluation S where
  obj x := G.objects.map f x
  map {x y} a := (G.evaluationArrowEquiv S _ _).symm
    ⟨G.arrows.map f (G.evaluationArrowEquiv T x y a).1,
      (NatTrans.naturality_apply G.source f _).trans
        (congrArg (G.objects.map f) (G.evaluationArrowEquiv T x y a).2.1),
      (NatTrans.naturality_apply G.target f _).trans
        (congrArg (G.objects.map f) (G.evaluationArrowEquiv T x y a).2.2)⟩
  map_id x := by
    let : Groupoid.{w} (G.objects.obj S) := G.evaluationGroupoid S
    let a : (G.objects.map f x) ⟶ (G.objects.map f x) :=
      (G.evaluationArrowEquiv S _ _).symm
        ⟨G.arrows.map f (G.identity T x),
          (NatTrans.naturality_apply G.source f _).trans
            (congrArg (G.objects.map f) (G.evaluationArrowEquiv T x x (𝟙 x)).2.1),
          (NatTrans.naturality_apply G.target f _).trans
            (congrArg (G.objects.map f) (G.evaluationArrowEquiv T x x (𝟙 x)).2.2)⟩
    change a = 𝟙 _
    have h : a ≫ a = a := by
      apply (G.evaluationArrowEquiv S _ _).injective
      apply Subtype.ext
      simp only [G.evaluationArrowEquiv_comp, a, Equiv.apply_symm_apply]
      have ht : G.compose T (G.identity T x) (G.identity T x)
          ((G.evaluationArrowEquiv T x x (𝟙 x)).2.1.trans
            (G.evaluationArrowEquiv T x x (𝟙 x)).2.2.symm) = G.identity T x := by
        simpa only [Category.id_comp, G.evaluationArrowEquiv_id] using
          (G.evaluationArrowEquiv_comp T (𝟙 x) (𝟙 x)).symm
      have hn := NatTrans.naturality_apply G.comp f
        (show (composableArrows G.objects G.arrows G.source G.target).obj T from
          ⟨(G.identity T x, G.identity T x),
            (G.evaluationArrowEquiv T x x (𝟙 x)).2.1.trans
              (G.evaluationArrowEquiv T x x (𝟙 x)).2.2.symm⟩)
      exact hn.trans (congrArg (G.arrows.map f) ht)
    have h' := congrArg (fun b : (G.objects.map f x) ⟶ (G.objects.map f x) =>
      b ≫ inv a) h
    simpa [Category.assoc] using h'
  map_comp {x y z} a b := by
    apply (G.evaluationArrowEquiv S _ _).injective
    apply Subtype.ext
    simp only [G.evaluationArrowEquiv_comp, Equiv.apply_symm_apply]
    have hn := NatTrans.naturality_apply G.comp f
      (show (composableArrows G.objects G.arrows G.source G.target).obj T from
        ⟨((G.evaluationArrowEquiv T y z b).1,
          (G.evaluationArrowEquiv T x y a).1),
          (G.evaluationArrowEquiv T y z b).2.1.trans
            (G.evaluationArrowEquiv T x y a).2.2.symm⟩)
    exact hn.symm

/-- A transport of the source does not change the arrow represented by a morphism of an
evaluated groupoid. -/
public theorem evaluationArrowEquiv_eqToHom_comp {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors.{u, v, w} C) (T : C)
    {x x' y : G.Evaluation T} (hx : x' = x) (a : x ⟶ y) :
    (G.evaluationArrowEquiv T x' y (eqToHom hx ≫ a)).1 =
      (G.evaluationArrowEquiv T x y a).1 := by
  cases hx
  simp

/-- Two arrows of an evaluated groupoid with equal representing elements of the arrow functor
agree, after transport along the identifications of their sources and targets. -/
public lemma hom_eq_transport {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors.{u, v, w} C) (T : C)
    {x x' y y' : G.Evaluation T} (hx : x = x') (hy : y = y')
    (a : x ⟶ y) (b : x' ⟶ y')
    (h : (G.evaluationArrowEquiv T x y a).1 =
      (G.evaluationArrowEquiv T x' y' b).1) :
    a = eqToHom hx ≫ b ≫ eqToHom hy.symm := by
  cases hx; cases hy
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact (G.evaluationArrowEquiv T _ _).injective (Subtype.ext h)

/-- The covariant functor of groupoids obtained by evaluating a groupoid in
functors at each object of the base category. -/
@[implicit_reducible, stacks 06KB "evaluation functor"]
public noncomputable def evaluationFunctor {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors.{u, v, w} C) : C ⥤ Cat.{w, w} where
  obj T := Cat.of (G.Evaluation T)
  map f := (evaluationMap G f).toCatHom
  map_id T := by
    apply Cat.Hom.ext
    apply Functor.ext
    case h_obj =>
      intro x
      exact G.objects.map_id_apply T x
    case h_map =>
      intro x y a
      refine hom_eq_transport G T
        (G.objects.map_id_apply T x) (G.objects.map_id_apply T y) _ _ ?_
      dsimp [evaluationMap]
      simp only [Equiv.apply_symm_apply, G.arrows.map_id_apply]
  map_comp f g := by
    apply Cat.Hom.ext
    apply Functor.ext
    case h_obj =>
      intro x
      exact G.objects.map_comp_apply f g x
    case h_map =>
      intro x y a
      refine hom_eq_transport G _
        (G.objects.map_comp_apply f g x) (G.objects.map_comp_apply f g y) _ _ ?_
      dsimp [evaluationMap]
      simp only [Equiv.apply_symm_apply, G.arrows.map_comp_apply]

/-- Each fiber of the evaluation functor retains its pointwise groupoid
structure. -/
public noncomputable instance evaluationFunctor_groupoid
    {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors.{u, v, w} C) (T : C) :
    Groupoid.{w} ((evaluationFunctor G).obj T) := G.evaluationGroupoid T

/-- On objects, the transition functor `evaluationMap G f` is the map `G.objects.map f`. -/
@[simp]
public theorem evaluationMap_obj {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors.{u, v, w} C) {T S : C} (f : T ⟶ S)
    (x : G.Evaluation T) :
    (evaluationMap G f).obj x = G.objects.map f x := rfl

/-- On arrows, the transition functor `evaluationMap G f` acts as `G.arrows.map f` on the
underlying elements of the arrow functor. -/
@[simp]
public theorem evaluationMap_map_arrow {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors.{u, v, w} C) {T S : C} (f : T ⟶ S)
    {x y : G.Evaluation T} (a : x ⟶ y) :
    (G.evaluationArrowEquiv S _ _ ((evaluationMap G f).map a)).1 =
      G.arrows.map f (G.evaluationArrowEquiv T x y a).1 := by
  simp only [evaluationMap, Equiv.apply_symm_apply]

/-- The value of the evaluation functor at `T` is the evaluated groupoid at `T`. -/
@[simp]
public theorem evaluationFunctor_obj {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors.{u, v, w} C) (T : C) :
    (evaluationFunctor G).obj T = Cat.of (G.Evaluation T) := rfl

add_to_stacks 06KB "quotient category" CategoryTheory.Grothendieck
add_to_sga "7 VI 1.1(a)" CategoryTheory.Grothendieck
add_to_stacks 06KB "projection" CategoryTheory.Grothendieck.forget
add_to_sga "4 I 8.3.2" "more general" CategoryTheory.Grothendieck.forget

set_option backward.isDefEq.respectTransparency false

/-- The canonical quotient map from the category of elements of the object
functor to the Grothendieck construction of the evaluated groupoids. -/
@[implicit_reducible, stacks 06KB "quotient morphism"]
public noncomputable def quotientMorphism {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors.{u, v, w} C) :
    G.objects.Elements ⥤ Grothendieck (evaluationFunctor G) where
  obj X := ⟨X.1, X.2⟩
  map {X Y} f :=
    { base := f.1
      fiber := eqToHom f.2 }
  map_id X := by
    apply Grothendieck.ext _ _ rfl
    simp
  map_comp f g := by
    apply Grothendieck.ext _ _ (by simp)
    change _ = _ ≫ (evaluationMap G g.1).map (eqToHom f.2) ≫ _
    rw [eqToHom_map (evaluationMap G g.1) f.2]
    simp only [eqToHom_trans]

/-- The quotient morphism sends an element `(T, x)` to an object over `T`. -/
@[simp]
public theorem quotientMorphism_obj_base {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors.{u, v, w} C) (X : G.objects.Elements) :
    ((quotientMorphism G).obj X).base = X.1 := rfl

/-- The quotient morphism sends an element `(T, x)` to an object with fiber `x`. -/
@[simp]
public theorem quotientMorphism_obj_fiber {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors.{u, v, w} C) (X : G.objects.Elements) :
    ((quotientMorphism G).obj X).fiber = X.2 := rfl

/-- The quotient morphism sends a morphism of elements over `f` to a morphism over `f`. -/
@[simp]
public theorem quotientMorphism_map_base {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors.{u, v, w} C)
    {X Y : G.objects.Elements} (f : X ⟶ Y) :
    ((quotientMorphism G).map f).base = f.1 := rfl

/-- The fiber component of the image of a morphism of elements under the quotient morphism is
an identity arrow. -/
@[simp]
public theorem quotientMorphism_map_arrow {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors.{u, v, w} C)
    {X Y : G.objects.Elements} (f : X ⟶ Y) :
    (G.evaluationArrowEquiv Y.1 _ _ ((quotientMorphism G).map f).fiber).1 =
      G.identity Y.1 Y.2 := by
  have eval_eqToHom (T : C) {x y : G.Evaluation T} (h : x = y) :
      (G.evaluationArrowEquiv T x y (eqToHom h)).1 = G.identity T y := by
    cases h; rfl
  change (G.evaluationArrowEquiv Y.1 _ _ (eqToHom f.2)).1 = _
  exact eval_eqToHom Y.1 f.2

/-- The quotient morphism lies over the identity of the base category. -/
public theorem quotientMorphism_over {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors.{u, v, w} C) :
    quotientMorphism G ⋙ Grothendieck.forget (evaluationFunctor G) =
      Functor.Elements.π G.objects := rfl

open CategoryTheory.Functor

/-- A morphism of the Grothendieck construction lying over `t` has base `t`. -/
private lemma grothendieck_base_eq_of_isHomLift {C : Type u} [Category.{v} C]
    {F : C ⥤ Cat.{w, w}} {X Y : Grothendieck F} {t : X.base ⟶ Y.base} (φ : X ⟶ Y)
    [(Grothendieck.forget F).IsHomLift t φ] : φ.base = t := by
  simpa [Grothendieck.forget] using (IsHomLift.eq_of_isHomLift (Grothendieck.forget F) t φ).symm

/-- A lift of `k` along the opposite of the projection gives a lift of `k.unop`. -/
private lemma isHomLift_unop {C : Type u} [Category.{v} C] {F : C ⥤ Cat.{w, w}}
    {A B : (Grothendieck F)ᵒᵖ}
    (k : (Grothendieck.forget F).op.obj A ⟶ (Grothendieck.forget F).op.obj B) (φ : A ⟶ B)
    [(Grothendieck.forget F).op.IsHomLift k φ] :
    (Grothendieck.forget F).IsHomLift k.unop φ.unop := by
  have hu := congrArg Quiver.Hom.unop
    (IsHomLift.eq_of_isHomLift (p := (Grothendieck.forget F).op) k φ)
  exact IsHomLift.of_fac (p := Grothendieck.forget F) k.unop φ.unop rfl rfl (by simpa using hu)

private lemma grothPushMap_strong2 {C : Type u} [Category.{v} C]
    {F : C ⥤ Cat.{w, w}} {X : Grothendieck F} {S : C} (f : X.base ⟶ S) :
    (Grothendieck.forget F).IsStronglyCocartesian f (X.toTransport f) := by
  let Y : Grothendieck F := ⟨S, (F.map f).toFunctor.obj X.fiber⟩
  let φ : X ⟶ Y := ⟨f, 𝟙 _⟩
  have hφ : φ = X.toTransport f := by
    apply Grothendieck.ext φ (X.toTransport f) rfl
    simp [φ, Y, Grothendieck.toTransport]
  rw [← hφ]
  have hLift : (Grothendieck.forget F).IsHomLift f φ := Functor.IsHomLift.map (p :=
    Grothendieck.forget F) φ
  let := hLift
  apply Functor.IsStronglyCocartesian.mk
  intro Z g θ hθ
  change S ⟶ Z.base at g
  cases θ with
  | mk θbase θfiber =>
    have hθbase : θbase = f ≫ g :=
      grothendieck_base_eq_of_isHomLift ({ base := θbase, fiber := θfiber } : X ⟶ Z)
    subst θbase
    have hfg : (F.map g).toFunctor.obj ((F.map f).toFunctor.obj X.fiber) =
        (F.map (f ≫ g)).toFunctor.obj X.fiber := by
      rw [F.map_comp f g, Cat.Hom.comp_toFunctor]
      rfl
    let χ : Y ⟶ Z := ⟨g, eqToHom hfg ≫ θfiber⟩
    refine ⟨χ, ⟨Functor.IsHomLift.map χ, ?_⟩, ?_⟩
    · apply Grothendieck.ext (φ ≫ χ) ⟨f ≫ g, θfiber⟩ rfl
      rw [Grothendieck.comp_fiber]
      dsimp [φ, χ, Y]
      simp
    · intro χ' hχ'
      rcases hχ' with ⟨hχlift, hχcomp⟩
      have hχbase : χ'.base = g := grothendieck_base_eq_of_isHomLift χ'
      cases hχbase
      apply Grothendieck.ext χ' χ rfl
      dsimp only [χ]
      simp only [eqToHom_refl, Category.id_comp] at ⊢
      have hcompFiber := Grothendieck.congr hχcomp
      rw [Grothendieck.comp_fiber] at hcompFiber
      simp only [Grothendieck.comp_base, map_id, Category.id_comp, eqToHom_refl, φ, Y]
        at hcompFiber
      have hcompFiber' : eqToHom hfg.symm ≫ χ'.fiber = θfiber := by
        convert hcompFiber using 1
      calc
        χ'.fiber = eqToHom hfg ≫ (eqToHom hfg.symm ≫ χ'.fiber) := by
          simp
        _ = eqToHom hfg ≫ θfiber := by rw [hcompFiber']

private lemma grothendieck_forget_op_fibered2 {C : Type u} [Category.{v} C]
    (F : C ⥤ Cat.{w, w}) : (Grothendieck.forget F).op.IsFibered := by
  apply Functor.IsFibered.of_exists_isStronglyCartesian
  intro A R f
  let X : Grothendieck F := A.unop
  let t : X.base ⟶ R.unop := f.unop
  let Y : Grothendieck F := X.transport t
  let φ : Opposite.op Y ⟶ A := Quiver.Hom.op (X.toTransport t)
  have hLift : (Grothendieck.forget F).op.IsHomLift f φ :=
    Functor.IsHomLift.map (p := (Grothendieck.forget F).op) φ
  let := hLift
  refine ⟨Opposite.op Y, φ, ?_⟩
  let : (Grothendieck.forget F).IsStronglyCocartesian t (X.toTransport t) :=
    grothPushMap_strong2 (F := F) (X := X) (S := R.unop) t
  apply Functor.IsStronglyCartesian.mk
  intro Z g θ hθ
  let Z0 : Grothendieck F := Z.unop
  let g0 : R.unop ⟶ Z0.base := g.unop
  let θ0 : X ⟶ Z0 := Quiver.Hom.unop θ
  have hθlift : (Grothendieck.forget F).IsHomLift (t ≫ g0) θ0 := isHomLift_unop (g ≫ f) θ
  obtain ⟨χ, ⟨hχlift, hχcomp⟩, hχuniq⟩ :=
    Functor.IsStronglyCocartesian.universal_property
      (p := Grothendieck.forget F) t (X.toTransport t) g0 (t ≫ g0) rfl θ0
  refine ⟨Quiver.Hom.op χ, ⟨?_, ?_⟩, ?_⟩
  · have hχbase : g0 = (Grothendieck.forget F).map χ :=
      @IsHomLift.eq_of_isHomLift _ _ _ _ (Grothendieck.forget F) Y Z0 g0 χ hχlift
    exact IsHomLift.of_fac (p := (Grothendieck.forget F).op) g (Quiver.Hom.op χ)
      rfl rfl (by simpa [g0, Z0] using congrArg Quiver.Hom.op hχbase)
  · apply Quiver.Hom.unop_inj
    simpa [φ, Quiver.Hom.unop_op] using hχcomp
  · intro ψ hψ
    rcases hψ with ⟨hψlift, hψcomp⟩
    have hψlift0 : (Grothendieck.forget F).IsHomLift g0 (Quiver.Hom.unop ψ) := isHomLift_unop g ψ
    have hψcomp0 : X.toTransport t ≫ Quiver.Hom.unop ψ = θ0 := by
      simpa [φ, Quiver.Hom.unop_op] using congrArg Quiver.Hom.unop hψcomp
    exact Quiver.Hom.unop_inj (hχuniq (Quiver.Hom.unop ψ) ⟨hψlift0, hψcomp0⟩)

private lemma groth_hom_isIso2 {C : Type u} [Category.{v} C]
    {F : C ⥤ Cat.{w, w}} (hF : ∀ T, IsGroupoid (F.obj T))
    {X Y : Grothendieck F} (φ : X ⟶ Y) (hbase : IsIso φ.base) : IsIso φ := by
  let := hbase
  let := hF Y.base
  have he : φ = (Grothendieck.isoMk (asIso φ.base) (asIso φ.fiber)).hom := by
    apply Grothendieck.ext _ _ rfl
    simp
  rw [he]
  infer_instance

private lemma groth_op_fiber_groupoid3 {C : Type u} [Category.{v} C]
    {F : C ⥤ Cat.{w, w}} (S : Cᵒᵖ) (hF : ∀ T, IsGroupoid (F.obj T)) :
    IsGroupoid ((Grothendieck.forget F).op.Fiber S) := by
  refine ⟨?_⟩
  intro a b f
  let p := (Grothendieck.forget F).op
  let φ0 : a.1 ⟶ b.1 := Fiber.fiberInclusion.map f
  have hLift : p.IsHomLift (𝟙 S) φ0 := f.2
  have hfac := IsHomLift.fac' p (𝟙 S) φ0
  have hφmap : IsIso (p.map φ0) := by
    rw [hfac]
    infer_instance
  have hbaseop : IsIso (((Grothendieck.forget F).map φ0.unop).op) := by
    simpa [p, φ0] using hφmap
  let : IsIso (((Grothendieck.forget F).map φ0.unop).op) := hbaseop
  have hbase : IsIso ((Grothendieck.forget F).map φ0.unop) :=
    isIso_of_op _
  have hbase' : IsIso φ0.unop.base := by
    simpa [Grothendieck.forget] using hbase
  have hφ : IsIso φ0.unop := groth_hom_isIso2 hF φ0.unop hbase'
  have : IsIso φ0 := (isIso_unop_iff φ0).mp hφ
  have : IsHomLift p (𝟙 S) φ0 := hLift
  let finv : b ⟶ a := ⟨inv φ0, by
    simpa using IsHomLift.inv (p := p) (f := 𝟙 S) (φ := φ0)⟩
  refine ⟨⟨finv, ?_, ?_⟩⟩
  · apply Fiber.hom_ext
    change φ0 ≫ inv φ0 = _
    simp only [op_obj, IsIso.hom_inv_id, map_id, φ0]
    rfl
  · apply Fiber.hom_ext
    change inv φ0 ≫ φ0 = _
    simp only [op_obj, IsIso.inv_hom_id, map_id, φ0]
    rfl

/-- The projection of the Grothendieck construction of a groupoid in functors
is cofibered in groupoids. -/
@[stacks 06KB "cofibered property", sga "7 VI 1.1(a)" "groupoid in functors"]
public theorem quotientProjection_cofibered {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors.{u, v, w} C) :
    IsCofiberedInGroupoids
      (Grothendieck.forget (evaluationFunctor G)) := by
  change (Grothendieck.forget (evaluationFunctor G)).op.IsFiberedInGroupoids
  let : (Grothendieck.forget (evaluationFunctor G)).op.IsFibered :=
    grothendieck_forget_op_fibered2 (evaluationFunctor G)
  exact Functor.IsFiberedInGroupoids.mk' (fun S =>
    groth_op_fiber_groupoid3 S (fun T => by infer_instance))

end

end Deformation
