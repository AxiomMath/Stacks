module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import StacksFrontier.Deformation.Groupoid.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Groupoid objects and internal groupoid data

A groupoid in functors (Stacks 06K3) is a pair of set-valued functors with source, target and
composition whose evaluation at every object is a groupoid. That condition is *pointwise*: it
says nothing about identities and inverses as maps, and so does not transport along a functor.
This file supplies the two translations which make it transport.

* `Deformation.PointwiseGroupoid.SetData` is the data of a groupoid object in sets — source,
  target, composition, identity and inverse, with the seven laws — and
  `Deformation.PointwiseGroupoid.ofSetData` turns it into a
  `Deformation.PointwiseGroupoid`, while `Deformation.PointwiseGroupoid.toSetData` turns a
  pointwise groupoid back into such data. The two are the externalization and the
  internalization of one notion at the level of sets.
* `Deformation.GroupoidObject` is a groupoid object of an arbitrary category: the same data,
  with the composition defined on a chosen fibre product of the source and target maps, and the
  laws read on generalized elements. `Deformation.GroupoidObject.map` transports it along any
  functor preserving the two cartesian squares it carries, and
  `Deformation.GroupoidObject.pointwiseGroupoid` evaluates a groupoid object in presheaves at a
  test object to give a `Deformation.PointwiseGroupoid` on the sections there.

## Main definitions

* `Deformation.PointwiseGroupoid.SetData`: internal groupoid data on a pair of sets.
* `Deformation.PointwiseGroupoid.ofSetData`: the pointwise groupoid it determines.
* `Deformation.PointwiseGroupoid.toSetData`: the internal groupoid data a pointwise groupoid
  determines.
* `Deformation.GroupoidObject`: a groupoid object of a category.
* `Deformation.GroupoidObject.mapOfIsPullback` and `Deformation.GroupoidObject.map`: the
  transport of a groupoid object along a functor.
* `Deformation.GroupoidObject.setData` and `Deformation.GroupoidObject.pointwiseGroupoid`: the
  sections of a groupoid object in presheaves at a test object, as internal groupoid data and
  as a groupoid, for any composition law agreeing with the one of the groupoid object.
* `Deformation.GroupoidObject.sectionPairHom_eq_of_comparison`: the generalized element a
  composable pair of sections determines, read through a comparison morphism into the object of
  composable pairs.

## Implementation notes

The laws of `Deformation.GroupoidObject` which involve the composition are stated on
generalized elements — quantified over an arbitrary object `X` of the category, an arrow
`a : X ⟶ arrows` and a composable pair `k : X ⟶ pairs` presented by its two projections —
rather than as equations between morphisms out of the object of pairs. The two are equivalent,
since taking `X` to be the object of arrows and `a` the identity recovers the equation; the
quantified form is what both consumers want. `Deformation.GroupoidObject.setData` reads it at
`X = yoneda.obj T`, where `CategoryTheory.yonedaEquiv` identifies generalized elements with
sections, and `Deformation.GroupoidObject.map` proves it for the image of a functor by
factoring an arbitrary `k` through the image of the universal one.

Associativity is the one law which is not a consequence of the others, so the object `triples`
of composable triples is carried as data together with the cartesian square presenting it. It
appears in no law: it is there so that `Deformation.GroupoidObject.map` has a universal
composable triple to factor through, exactly as the object of pairs serves the other four laws.

The arrows of the groupoid `Deformation.PointwiseGroupoid.ofSetData` produces from `x` to `y`
are the elements of the arrow set with source `x` and target `y`, so that its
`Deformation.PointwiseGroupoid.arrowEquiv` is the identity and its
`Deformation.PointwiseGroupoid.comp_eq` holds by reflexivity. Nothing is chosen beyond the
given data.

## References

* [Stacks Project, Tag 06K3](https://stacks.math.columbia.edu/tag/06K3)
* [Stacks Project, Tag 06K5](https://stacks.math.columbia.edu/tag/06K5)
-/

@[expose] public section

open CategoryTheory

namespace Deformation.PointwiseGroupoid

universe w

variable {U R : Type w}

/-- Internal groupoid data on a pair of sets, read as the data of a groupoid object in sets:
source, target and composition together with an identity map, an inverse map and the seven
laws relating them. -/
@[sga "3 V 1.2" "special case"]
structure SetData (U R : Type w) where
  /-- The source map. -/
  source : R → U
  /-- The target map. -/
  target : R → U
  /-- Composition of composable pairs, in the order `(f, g)` for the composite `g ≫ f`. -/
  comp : { p : R × R // source p.1 = target p.2 } → R
  /-- The identity arrow of an object. -/
  identity : U → R
  /-- The inverse of an arrow. -/
  inverse : R → R
  /-- The identity arrow has the given object as its source. -/
  source_identity : ∀ x, source (identity x) = x
  /-- The identity arrow has the given object as its target. -/
  target_identity : ∀ x, target (identity x) = x
  /-- Inversion exchanges source and target. -/
  source_inverse : ∀ a, source (inverse a) = target a
  /-- Inversion exchanges target and source. -/
  target_inverse : ∀ a, target (inverse a) = source a
  /-- A composite has the source of its second argument. -/
  source_comp : ∀ p, source (comp p) = source p.1.2
  /-- A composite has the target of its first argument. -/
  target_comp : ∀ p, target (comp p) = target p.1.1
  /-- Composing with the identity on the target is the identity. -/
  comp_identity_left : ∀ a, comp ⟨(identity (target a), a), source_identity (target a)⟩ = a
  /-- Composing with the identity on the source is the identity. -/
  comp_identity_right :
    ∀ a, comp ⟨(a, identity (source a)), (target_identity (source a)).symm⟩ = a
  /-- Composition is associative. -/
  comp_assoc : ∀ (a b d : R) (hab : source a = target b) (hbd : source b = target d),
    comp ⟨(comp ⟨(a, b), hab⟩, d), (source_comp ⟨(a, b), hab⟩).trans hbd⟩ =
      comp ⟨(a, comp ⟨(b, d), hbd⟩), hab.trans (target_comp ⟨(b, d), hbd⟩).symm⟩
  /-- An arrow precomposed with its inverse is an identity. -/
  comp_inverse_left : ∀ a, comp ⟨(inverse a, a), source_inverse a⟩ = identity (source a)
  /-- An arrow postcomposed with its inverse is an identity. -/
  comp_inverse_right : ∀ a, comp ⟨(a, inverse a), (target_inverse a).symm⟩ = identity (target a)

/-- The groupoid in sets determined by internal groupoid data: its objects are `U`, its arrows
from `x` to `y` are the elements of `R` with source `x` and target `y`, and its composition is
the given one. -/
@[instance_reducible, sga "3 V 1.2"]
def SetData.groupoidStruct (D : SetData U R) : Groupoid.{w} U where
  toCategory :=
    { Hom x y := { a : R // D.source a = x ∧ D.target a = y }
      id x := ⟨D.identity x, D.source_identity x, D.target_identity x⟩
      comp {x y z} g f :=
        ⟨D.comp ⟨(f.1, g.1), f.2.1.trans g.2.2.symm⟩,
          (D.source_comp _).trans g.2.1, (D.target_comp _).trans f.2.2⟩
      id_comp := by
        rintro x y ⟨a, rfl, rfl⟩
        exact Subtype.ext (D.comp_identity_right a)
      comp_id := by
        rintro x y ⟨a, rfl, rfl⟩
        exact Subtype.ext (D.comp_identity_left a)
      assoc := by
        rintro w x y z ⟨a, rfl, rfl⟩ ⟨b, hb, rfl⟩ ⟨d, hd, rfl⟩
        exact Subtype.ext (D.comp_assoc d b a hd hb).symm }
  inv {x y} f := ⟨D.inverse f.1, (D.source_inverse f.1).trans f.2.2,
    (D.target_inverse f.1).trans f.2.1⟩
  inv_comp := by
    rintro x y ⟨a, rfl, rfl⟩
    exact Subtype.ext (D.comp_inverse_right a)
  comp_inv := by
    rintro x y ⟨a, rfl, rfl⟩
    exact Subtype.ext (D.comp_inverse_left a)

/-- **The constructor of a pointwise groupoid from internal groupoid data.** Source, target and
composition on a pair of sets which carry an identity map, an inverse map and the seven laws of
a groupoid object form a groupoid in the sense of `Deformation.PointwiseGroupoid`, with the
arrows from `x` to `y` being the elements of the arrow set with source `x` and target `y`. -/
@[sga "3 V 1.2"]
def ofSetData (D : SetData U R) : PointwiseGroupoid D.source D.target D.comp where
  groupoid := D.groupoidStruct
  arrowEquiv _ _ := Equiv.refl _
  comp_eq _ _ := rfl

/-! #### From a pointwise groupoid back to internal groupoid data -/

section OfPointwise

variable {s t : R → U} {c : { p : R × R // s p.1 = t p.2 } → R}

/-- The arrow of the groupoid represented by an element of the arrow set. -/
noncomputable def arrowOf (H : PointwiseGroupoid s t c) (a : R) :
    @Quiver.Hom U H.groupoid.toCategory.toQuiver (s a) (t a) :=
  (H.arrowEquiv (s a) (t a)).symm ⟨a, rfl, rfl⟩

/-- The element of the arrow set representing the identity of an object. -/
noncomputable def identityOf (H : PointwiseGroupoid s t c) (x : U) : R :=
  (H.arrowEquiv x x (@CategoryStruct.id U H.groupoid.toCategory.toCategoryStruct x)).1

/-- The element of the arrow set representing the inverse of an arrow. -/
@[sga "3 V 1.2" "inverse map σ on arrows"]
noncomputable def inverseOf (H : PointwiseGroupoid s t c) (a : R) : R :=
  (H.arrowEquiv (t a) (s a) (@Groupoid.inv U H.groupoid _ _ (H.arrowOf a))).1

/-- **A pointwise groupoid is internal groupoid data.** The identity and the inverse that the
groupoid structure determines, together with source, target and the given composition, satisfy
the seven laws of a groupoid object in sets. -/
@[sga "3 V 1.2"]
noncomputable def toSetData (H : PointwiseGroupoid s t c) : SetData U R := by
  classical
  letI := H.groupoid
  have harrow : ∀ a : R, (H.arrowEquiv (s a) (t a) (H.arrowOf a)).1 = a := by
    intro a
    simp [arrowOf]
  have hcomp : ∀ {x y z : U} (g : x ⟶ y) (f : y ⟶ z) (a b : R),
      (H.arrowEquiv y z f).1 = a → (H.arrowEquiv x y g).1 = b → ∀ hab : s a = t b,
      c ⟨(a, b), hab⟩ = (H.arrowEquiv x z (g ≫ f)).1 := by
    intro x y z g f a b ha hb hab
    subst ha
    subst hb
    exact (H.comp_eq g f).symm
  have hsi : ∀ x, s (H.identityOf x) = x := fun x => (H.arrowEquiv x x (𝟙 x)).2.1
  have hti : ∀ x, t (H.identityOf x) = x := fun x => (H.arrowEquiv x x (𝟙 x)).2.2
  have hsv : ∀ a, s (H.inverseOf a) = t a :=
    fun a => (H.arrowEquiv (t a) (s a) (Groupoid.inv (H.arrowOf a))).2.1
  have htv : ∀ a, t (H.inverseOf a) = s a :=
    fun a => (H.arrowEquiv (t a) (s a) (Groupoid.inv (H.arrowOf a))).2.2
  exact
    { source := s
      target := t
      comp := c
      identity := H.identityOf
      inverse := H.inverseOf
      source_identity := hsi
      target_identity := hti
      source_inverse := hsv
      target_inverse := htv
      source_comp := fun p => H.source_comp p.1.1 p.1.2 p.2
      target_comp := fun p => H.target_comp p.1.1 p.1.2 p.2
      comp_identity_left := fun a => by
        rw [hcomp (H.arrowOf a) (𝟙 (t a)) (H.identityOf (t a)) a rfl (harrow a),
          Category.comp_id, harrow a]
      comp_identity_right := fun a => by
        rw [hcomp (𝟙 (s a)) (H.arrowOf a) a (H.identityOf (s a)) (harrow a) rfl,
          Category.id_comp, harrow a]
      comp_inverse_left := fun a => by
        rw [hcomp (H.arrowOf a) (Groupoid.inv (H.arrowOf a)) (H.inverseOf a) a rfl (harrow a),
          Groupoid.comp_inv]
        rfl
      comp_inverse_right := fun a => by
        rw [hcomp (Groupoid.inv (H.arrowOf a)) (H.arrowOf a) a (H.inverseOf a) (harrow a) rfl,
          Groupoid.inv_comp]
        rfl
      comp_assoc := fun a b d hab hbd => by
        set A : t b ⟶ t a := (H.arrowEquiv (t b) (t a)).symm ⟨a, hab, rfl⟩ with hA
        set Bb : t d ⟶ t b := (H.arrowEquiv (t d) (t b)).symm ⟨b, hbd, rfl⟩ with hB
        have hA' : (H.arrowEquiv (t b) (t a) A).1 = a := by simp [hA]
        have hB' : (H.arrowEquiv (t d) (t b) Bb).1 = b := by simp [hB]
        rw [hcomp (H.arrowOf d) (Bb ≫ A) (c ⟨(a, b), hab⟩) d
            (hcomp Bb A a b hA' hB' hab).symm (harrow d),
          hcomp (H.arrowOf d ≫ Bb) A a (c ⟨(b, d), hbd⟩) hA'
            (hcomp (H.arrowOf d) Bb b d hB' (harrow d) hbd).symm,
          Category.assoc] }

end OfPointwise

end Deformation.PointwiseGroupoid

/-! ### Groupoid objects -/

namespace Deformation

universe v₁ v₂ u₁ u₂ w

open CategoryTheory CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- A groupoid object of a category: objects and arrows with source, target, identity, inverse
and composition, the composition being defined on a chosen fibre product `pairs` of the source
and target maps, subject to the laws of a groupoid read on generalized elements.

The object `triples` of composable triples, with its two projections to `pairs`, is carried as
data so that the structure transports along a functor preserving the two cartesian squares. -/
@[sga "3 V 1.2"]
structure GroupoidObject (C : Type u₁) [Category.{v₁} C] where
  /-- The object of objects. -/
  objects : C
  /-- The object of arrows. -/
  arrows : C
  /-- The object of composable pairs of arrows. -/
  pairs : C
  /-- The object of composable triples of arrows. -/
  triples : C
  /-- The source map. -/
  source : arrows ⟶ objects
  /-- The target map. -/
  target : arrows ⟶ objects
  /-- The identity arrow of an object. -/
  identity : objects ⟶ arrows
  /-- The inverse of an arrow. -/
  inverse : arrows ⟶ arrows
  /-- The first arrow of a composable pair. -/
  fst : pairs ⟶ arrows
  /-- The second arrow of a composable pair. -/
  snd : pairs ⟶ arrows
  /-- A composable pair is a pair of arrows whose first source is the second target. -/
  isPullback_pairs : IsPullback fst snd source target
  /-- Composition of a composable pair, in the order `(f, g)` for the composite `g ≫ f`. -/
  comp : pairs ⟶ arrows
  /-- The first pair of a composable triple. -/
  fst₃ : triples ⟶ pairs
  /-- The second pair of a composable triple. -/
  snd₃ : triples ⟶ pairs
  /-- A composable triple is a pair of composable pairs overlapping in one arrow. -/
  isPullback_triples : IsPullback fst₃ snd₃ snd fst
  /-- An identity arrow has its object as source. -/
  identity_source : identity ≫ source = 𝟙 objects
  /-- An identity arrow has its object as target. -/
  identity_target : identity ≫ target = 𝟙 objects
  /-- Inversion exchanges source and target. -/
  inverse_source : inverse ≫ source = target
  /-- Inversion exchanges target and source. -/
  inverse_target : inverse ≫ target = source
  /-- A composite has the source of the second arrow of its pair. -/
  comp_source : comp ≫ source = snd ≫ source
  /-- A composite has the target of the first arrow of its pair. -/
  comp_target : comp ≫ target = fst ≫ target
  /-- The identity on the target is a left unit for composition. -/
  comp_identity_left : ∀ {X : C} (a : X ⟶ arrows) (k : X ⟶ pairs),
    k ≫ fst = a ≫ target ≫ identity → k ≫ snd = a → k ≫ comp = a
  /-- The identity on the source is a right unit for composition. -/
  comp_identity_right : ∀ {X : C} (a : X ⟶ arrows) (k : X ⟶ pairs),
    k ≫ fst = a → k ≫ snd = a ≫ source ≫ identity → k ≫ comp = a
  /-- An arrow composed after its inverse is the identity on its source. -/
  comp_inverse_left : ∀ {X : C} (a : X ⟶ arrows) (k : X ⟶ pairs),
    k ≫ fst = a ≫ inverse → k ≫ snd = a → k ≫ comp = a ≫ source ≫ identity
  /-- An arrow composed before its inverse is the identity on its target. -/
  comp_inverse_right : ∀ {X : C} (a : X ⟶ arrows) (k : X ⟶ pairs),
    k ≫ fst = a → k ≫ snd = a ≫ inverse → k ≫ comp = a ≫ target ≫ identity
  /-- Composition is associative. -/
  comp_assoc : ∀ {X : C} (k l m n : X ⟶ pairs), k ≫ snd = l ≫ fst →
    m ≫ fst = k ≫ comp → m ≫ snd = l ≫ snd →
    n ≫ fst = k ≫ fst → n ≫ snd = l ≫ comp → m ≫ comp = n ≫ comp

namespace GroupoidObject

variable (G : GroupoidObject C)

/-- The composable pair with prescribed first and second arrow. -/
noncomputable def liftPair {X : C} (a b : X ⟶ G.arrows)
    (w : a ≫ G.source = b ≫ G.target) : X ⟶ G.pairs :=
  G.isPullback_pairs.lift a b w

/-- The first arrow of the composable pair with prescribed arrows is the first one given. -/
@[simp]
theorem liftPair_fst {X : C} (a b : X ⟶ G.arrows) (w : a ≫ G.source = b ≫ G.target) :
    G.liftPair a b w ≫ G.fst = a :=
  G.isPullback_pairs.lift_fst a b w

/-- The second arrow of the composable pair with prescribed arrows is the second one given. -/
@[simp]
theorem liftPair_snd {X : C} (a b : X ⟶ G.arrows) (w : a ≫ G.source = b ≫ G.target) :
    G.liftPair a b w ≫ G.snd = b :=
  G.isPullback_pairs.lift_snd a b w

/-- The composability of the target identity with an arrow. -/
theorem identity_target_comp_source :
    (G.target ≫ G.identity) ≫ G.source = 𝟙 G.arrows ≫ G.target := by
  rw [Category.assoc, G.identity_source, Category.comp_id, Category.id_comp]

/-- The composability of an arrow with the identity on its source. -/
theorem identity_source_comp_target :
    (𝟙 G.arrows) ≫ G.source = (G.source ≫ G.identity) ≫ G.target := by
  rw [Category.assoc, G.identity_target, Category.comp_id, Category.id_comp]

/-- The composability of the inverse of an arrow with the arrow. -/
theorem inverse_comp_source : G.inverse ≫ G.source = 𝟙 G.arrows ≫ G.target := by
  rw [G.inverse_source, Category.id_comp]

/-- The composability of an arrow with its inverse. -/
theorem inverse_comp_target : (𝟙 G.arrows) ≫ G.source = G.inverse ≫ G.target := by
  rw [G.inverse_target, Category.id_comp]

/-- The unit law for the identity on the target, read on the universal composable pair. -/
theorem compUnitLeft_comp :
    G.liftPair (G.target ≫ G.identity) (𝟙 G.arrows) G.identity_target_comp_source ≫ G.comp =
      𝟙 G.arrows :=
  G.comp_identity_left (𝟙 G.arrows) _ (by simp) (by simp)

/-- The unit law for the identity on the source, read on the universal composable pair. -/
theorem compUnitRight_comp :
    G.liftPair (𝟙 G.arrows) (G.source ≫ G.identity) G.identity_source_comp_target ≫ G.comp =
      𝟙 G.arrows :=
  G.comp_identity_right (𝟙 G.arrows) _ (by simp) (by simp)

/-- The left inverse law, read on the universal composable pair. -/
theorem compInverseLeft_comp :
    G.liftPair G.inverse (𝟙 G.arrows) G.inverse_comp_source ≫ G.comp =
      G.source ≫ G.identity := by
  simpa using G.comp_inverse_left (𝟙 G.arrows)
    (G.liftPair G.inverse (𝟙 G.arrows) G.inverse_comp_source) (by simp) (by simp)

/-- The right inverse law, read on the universal composable pair. -/
theorem compInverseRight_comp :
    G.liftPair (𝟙 G.arrows) G.inverse G.inverse_comp_target ≫ G.comp =
      G.target ≫ G.identity := by
  simpa using G.comp_inverse_right (𝟙 G.arrows)
    (G.liftPair (𝟙 G.arrows) G.inverse G.inverse_comp_target) (by simp) (by simp)

/-- The first bracketing of a composable triple: the pair of the composite of the first two
arrows with the third. -/
noncomputable def assocLeft : G.triples ⟶ G.pairs :=
  G.liftPair (G.fst₃ ≫ G.comp) (G.snd₃ ≫ G.snd) (by
    rw [Category.assoc, Category.assoc, G.comp_source, ← Category.assoc, ← Category.assoc,
      G.isPullback_triples.w, Category.assoc, Category.assoc, G.isPullback_pairs.w])

/-- The second bracketing of a composable triple: the pair of the first arrow with the
composite of the last two. -/
noncomputable def assocRight : G.triples ⟶ G.pairs :=
  G.liftPair (G.fst₃ ≫ G.fst) (G.snd₃ ≫ G.comp) (by
    rw [Category.assoc, Category.assoc, G.comp_target, ← Category.assoc, ← Category.assoc,
      ← G.isPullback_triples.w, Category.assoc, Category.assoc, G.isPullback_pairs.w])

/-- The first arrow of the first bracketing of a composable triple is the composite of the
first two arrows. -/
@[simp]
theorem assocLeft_fst : G.assocLeft ≫ G.fst = G.fst₃ ≫ G.comp := by simp [assocLeft]

/-- The second arrow of the first bracketing of a composable triple is the third arrow. -/
@[simp]
theorem assocLeft_snd : G.assocLeft ≫ G.snd = G.snd₃ ≫ G.snd := by simp [assocLeft]

/-- The first arrow of the second bracketing of a composable triple is the first arrow. -/
@[simp]
theorem assocRight_fst : G.assocRight ≫ G.fst = G.fst₃ ≫ G.fst := by simp [assocRight]

/-- The second arrow of the second bracketing of a composable triple is the composite of the
last two arrows. -/
@[simp]
theorem assocRight_snd : G.assocRight ≫ G.snd = G.snd₃ ≫ G.comp := by simp [assocRight]

/-- Associativity, read on the universal composable triple. -/
@[sga "3 V 1.2" "(4)"]
theorem assocLeft_comp : G.assocLeft ≫ G.comp = G.assocRight ≫ G.comp :=
  G.comp_assoc G.fst₃ G.snd₃ _ _ G.isPullback_triples.w (by simp) (by simp) (by simp) (by simp)

/-- **A groupoid object transports along a functor carrying its two cartesian squares to
cartesian squares.** The two squares are taken as hypotheses rather than deduced from a
preservation instance, so that the transport applies to a functor whose left exactness is
known only for the squares at hand. -/
noncomputable def mapOfIsPullback (F : C ⥤ D)
    (hp : IsPullback (F.map G.fst) (F.map G.snd) (F.map G.source) (F.map G.target))
    (ht : IsPullback (F.map G.fst₃) (F.map G.snd₃) (F.map G.snd) (F.map G.fst)) :
    GroupoidObject D where
  objects := F.obj G.objects
  arrows := F.obj G.arrows
  pairs := F.obj G.pairs
  triples := F.obj G.triples
  source := F.map G.source
  target := F.map G.target
  identity := F.map G.identity
  inverse := F.map G.inverse
  fst := F.map G.fst
  snd := F.map G.snd
  isPullback_pairs := hp
  comp := F.map G.comp
  fst₃ := F.map G.fst₃
  snd₃ := F.map G.snd₃
  isPullback_triples := ht
  identity_source := by rw [← F.map_comp, G.identity_source, F.map_id]
  identity_target := by rw [← F.map_comp, G.identity_target, F.map_id]
  inverse_source := by rw [← F.map_comp, G.inverse_source]
  inverse_target := by rw [← F.map_comp, G.inverse_target]
  comp_source := by rw [← F.map_comp, ← F.map_comp, G.comp_source]
  comp_target := by rw [← F.map_comp, ← F.map_comp, G.comp_target]
  comp_identity_left := by
    intro Y a k h₁ h₂
    have hk : k = a ≫ F.map (G.liftPair (G.target ≫ G.identity) (𝟙 G.arrows)
        G.identity_target_comp_source) := by
      refine hp.hom_ext ?_ ?_
      · simp only [h₁, Category.assoc, ← F.map_comp, liftPair_fst]
      · simp only [h₂, Category.assoc, ← F.map_comp, liftPair_snd, F.map_id, Category.comp_id]
    rw [hk, Category.assoc, ← F.map_comp, G.compUnitLeft_comp, F.map_id, Category.comp_id]
  comp_identity_right := by
    intro Y a k h₁ h₂
    have hk : k = a ≫ F.map (G.liftPair (𝟙 G.arrows) (G.source ≫ G.identity)
        G.identity_source_comp_target) := by
      refine hp.hom_ext ?_ ?_
      · simp only [h₁, Category.assoc, ← F.map_comp, liftPair_fst, F.map_id, Category.comp_id]
      · simp only [h₂, Category.assoc, ← F.map_comp, liftPair_snd]
    rw [hk, Category.assoc, ← F.map_comp, G.compUnitRight_comp, F.map_id, Category.comp_id]
  comp_inverse_left := by
    intro Y a k h₁ h₂
    have hk : k = a ≫ F.map (G.liftPair G.inverse (𝟙 G.arrows) G.inverse_comp_source) := by
      refine hp.hom_ext ?_ ?_
      · simp only [h₁, Category.assoc, ← F.map_comp, liftPair_fst]
      · simp only [h₂, Category.assoc, ← F.map_comp, liftPair_snd, F.map_id, Category.comp_id]
    rw [hk, Category.assoc, ← F.map_comp, G.compInverseLeft_comp, F.map_comp]
  comp_inverse_right := by
    intro Y a k h₁ h₂
    have hk : k = a ≫ F.map (G.liftPair (𝟙 G.arrows) G.inverse G.inverse_comp_target) := by
      refine hp.hom_ext ?_ ?_
      · simp only [h₁, Category.assoc, ← F.map_comp, liftPair_fst, F.map_id, Category.comp_id]
      · simp only [h₂, Category.assoc, ← F.map_comp, liftPair_snd]
    rw [hk, Category.assoc, ← F.map_comp, G.compInverseRight_comp, F.map_comp]
  comp_assoc := by
    intro Y k l m n hkl hm₁ hm₂ hn₁ hn₂
    have hjf := ht.lift_fst k l hkl
    have hjs := ht.lift_snd k l hkl
    set j := ht.lift k l hkl with hj
    have hmj : m = j ≫ F.map G.assocLeft := by
      refine hp.hom_ext ?_ ?_
      · rw [Category.assoc, ← F.map_comp, G.assocLeft_fst, F.map_comp, ← Category.assoc,
          hjf, hm₁]
      · rw [Category.assoc, ← F.map_comp, G.assocLeft_snd, F.map_comp, ← Category.assoc,
          hjs, hm₂]
    have hnj : n = j ≫ F.map G.assocRight := by
      refine hp.hom_ext ?_ ?_
      · rw [Category.assoc, ← F.map_comp, G.assocRight_fst, F.map_comp, ← Category.assoc,
          hjf, hn₁]
      · rw [Category.assoc, ← F.map_comp, G.assocRight_snd, F.map_comp, ← Category.assoc,
          hjs, hn₂]
    rw [hmj, hnj, Category.assoc, Category.assoc, ← F.map_comp, ← F.map_comp, G.assocLeft_comp]

/-- **A groupoid object transports along a functor preserving its two cartesian squares.** -/
noncomputable def map (F : C ⥤ D) [PreservesLimit (cospan G.source G.target) F]
    [PreservesLimit (cospan G.snd G.fst) F] : GroupoidObject D :=
  G.mapOfIsPullback F (G.isPullback_pairs.map F) (G.isPullback_triples.map F)

/-! #### Sections of a groupoid object in presheaves -/

section Presheaf

open Opposite

variable {E : Type u₂} [Category.{w} E]

/-- Two equal morphisms of set-valued presheaves agree at every section. -/
theorem app_apply_congr {F H : Eᵒᵖ ⥤ Type w} {a b : F ⟶ H} (h : a = b) (T : Eᵒᵖ)
    (x : F.obj T) : a.app T x = b.app T x := by rw [h]

/-- Composable pairs of sections of a groupoid object in presheaves at a test object. -/
@[sga "3 V 1.2" "partial"]
abbrev SectionPairs (G : GroupoidObject (Eᵒᵖ ⥤ Type w)) (T : E) :=
  { q : G.arrows.obj (op T) × G.arrows.obj (op T) //
      G.source.app (op T) q.1 = G.target.app (op T) q.2 }

/-- A composable pair of sections, read as a generalized element of the object of composable
pairs. -/
noncomputable def sectionPairHom (G : GroupoidObject (Eᵒᵖ ⥤ Type w)) (T : E)
    (p : G.SectionPairs T) : yoneda.obj T ⟶ G.pairs :=
  G.liftPair (yonedaEquiv.symm p.1.1) (yonedaEquiv.symm p.1.2)
    (by rw [yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_naturality_right, p.2])

/-- The first projection of the generalized element determined by a composable pair of
sections is the first section. -/
@[simp]
theorem sectionPairHom_fst (G : GroupoidObject (Eᵒᵖ ⥤ Type w)) (T : E) (p : G.SectionPairs T) :
    G.sectionPairHom T p ≫ G.fst = yonedaEquiv.symm p.1.1 :=
  G.liftPair_fst _ _ _

/-- The second projection of the generalized element determined by a composable pair of
sections is the second section. -/
@[simp]
theorem sectionPairHom_snd (G : GroupoidObject (Eᵒᵖ ⥤ Type w)) (T : E) (p : G.SectionPairs T) :
    G.sectionPairHom T p ≫ G.snd = yonedaEquiv.symm p.1.2 :=
  G.liftPair_snd _ _ _

/-- A composable pair of sections presented through a morphism into the object of composable
pairs: if `φ` has composites `f₁` and `f₂` with the two projections, then the generalized
element determined by a pair of sections read off from `f₁` and `f₂` is the image under `φ`. -/
theorem sectionPairHom_eq_of_comparison (G : GroupoidObject (Eᵒᵖ ⥤ Type w))
    {P : Eᵒᵖ ⥤ Type w} (φ : P ⟶ G.pairs) (f₁ f₂ : P ⟶ G.arrows)
    (h₁ : φ ≫ G.fst = f₁) (h₂ : φ ≫ G.snd = f₂)
    (T : E) (p : P.obj (op T)) (q : G.SectionPairs T)
    (hq₁ : q.1.1 = f₁.app (op T) p) (hq₂ : q.1.2 = f₂.app (op T) p) :
    G.sectionPairHom T q = yonedaEquiv.symm (φ.app (op T) p) := by
  refine G.isPullback_pairs.hom_ext ?_ ?_
  · rw [sectionPairHom_fst, yonedaEquiv_symm_naturality_right, hq₁, ← h₁]
    rfl
  · rw [sectionPairHom_snd, yonedaEquiv_symm_naturality_right, hq₂, ← h₂]
    rfl

/-- **The sections of a groupoid object in presheaves at a test object are internal groupoid
data in sets.** Source, target, identity and inverse are read off at the test object, and the
composite of a composable pair of sections is the composition of the groupoid object evaluated
on the generalized element the pair determines.

The composition law is taken as an argument, together with the identification `hc` of it with
that evaluation, so that the data comes out with the composition a client already has rather
than with one that has to be adjusted later. -/
@[sga "3 V 1.2"]
noncomputable def setData (G : GroupoidObject (Eᵒᵖ ⥤ Type w)) (T : E)
    (c : G.SectionPairs T → G.arrows.obj (op T))
    (hc : ∀ p, c p = yonedaEquiv (G.sectionPairHom T p ≫ G.comp)) :
    PointwiseGroupoid.SetData (G.objects.obj (op T)) (G.arrows.obj (op T)) where
  source := G.source.app (op T)
  target := G.target.app (op T)
  comp := c
  identity := G.identity.app (op T)
  inverse := G.inverse.app (op T)
  source_identity x := by simpa using app_apply_congr G.identity_source (op T) x
  target_identity x := by simpa using app_apply_congr G.identity_target (op T) x
  source_inverse a := by simpa using app_apply_congr G.inverse_source (op T) a
  target_inverse a := by simpa using app_apply_congr G.inverse_target (op T) a
  source_comp p := by
    have hcf : c = fun p => yonedaEquiv (G.sectionPairHom T p ≫ G.comp) := funext hc
    subst hcf
    have h : (G.sectionPairHom T p ≫ G.comp) ≫ G.source =
        yonedaEquiv.symm p.1.2 ≫ G.source := by
      rw [Category.assoc, G.comp_source, ← Category.assoc, sectionPairHom_snd]
    simpa [yonedaEquiv_comp] using congrArg (fun k => yonedaEquiv k) h
  target_comp p := by
    have hcf : c = fun p => yonedaEquiv (G.sectionPairHom T p ≫ G.comp) := funext hc
    subst hcf
    have h : (G.sectionPairHom T p ≫ G.comp) ≫ G.target =
        yonedaEquiv.symm p.1.1 ≫ G.target := by
      rw [Category.assoc, G.comp_target, ← Category.assoc, sectionPairHom_fst]
    simpa [yonedaEquiv_comp] using congrArg (fun k => yonedaEquiv k) h
  comp_identity_left a := by
    have hcf : c = fun p => yonedaEquiv (G.sectionPairHom T p ≫ G.comp) := funext hc
    subst hcf
    refine Eq.trans (congrArg (fun k => yonedaEquiv k)
      (G.comp_identity_left (yonedaEquiv.symm a) _ ?_ ?_)) (Equiv.apply_symm_apply _ a)
    · rw [sectionPairHom_fst, ← Category.assoc, yonedaEquiv_symm_naturality_right,
        yonedaEquiv_symm_naturality_right]
    · rw [sectionPairHom_snd]
  comp_identity_right a := by
    have hcf : c = fun p => yonedaEquiv (G.sectionPairHom T p ≫ G.comp) := funext hc
    subst hcf
    refine Eq.trans (congrArg (fun k => yonedaEquiv k)
      (G.comp_identity_right (yonedaEquiv.symm a) _ ?_ ?_)) (Equiv.apply_symm_apply _ a)
    · rw [sectionPairHom_fst]
    · rw [sectionPairHom_snd, ← Category.assoc, yonedaEquiv_symm_naturality_right,
        yonedaEquiv_symm_naturality_right]
  comp_inverse_left a := by
    have hcf : c = fun p => yonedaEquiv (G.sectionPairHom T p ≫ G.comp) := funext hc
    subst hcf
    refine Eq.trans (congrArg (fun k => yonedaEquiv k)
      (G.comp_inverse_left (yonedaEquiv.symm a) _ ?_ ?_)) ?_
    · rw [sectionPairHom_fst, yonedaEquiv_symm_naturality_right]
    · rw [sectionPairHom_snd]
    · rw [← Category.assoc, yonedaEquiv_symm_naturality_right,
        yonedaEquiv_symm_naturality_right, Equiv.apply_symm_apply]
  comp_inverse_right a := by
    have hcf : c = fun p => yonedaEquiv (G.sectionPairHom T p ≫ G.comp) := funext hc
    subst hcf
    refine Eq.trans (congrArg (fun k => yonedaEquiv k)
      (G.comp_inverse_right (yonedaEquiv.symm a) _ ?_ ?_)) ?_
    · rw [sectionPairHom_fst]
    · rw [sectionPairHom_snd, yonedaEquiv_symm_naturality_right]
    · rw [← Category.assoc, yonedaEquiv_symm_naturality_right,
        yonedaEquiv_symm_naturality_right, Equiv.apply_symm_apply]
  comp_assoc a b d hab hbd := by
    have hcf : c = fun p => yonedaEquiv (G.sectionPairHom T p ≫ G.comp) := funext hc
    subst hcf
    refine congrArg (fun k => yonedaEquiv k)
      (G.comp_assoc (G.sectionPairHom T ⟨(a, b), hab⟩) (G.sectionPairHom T ⟨(b, d), hbd⟩)
        _ _ ?_ ?_ ?_ ?_ ?_)
    · rw [sectionPairHom_snd, sectionPairHom_fst]
    · rw [sectionPairHom_fst, Equiv.symm_apply_apply]
    · rw [sectionPairHom_snd, sectionPairHom_snd]
    · rw [sectionPairHom_fst, sectionPairHom_fst]
    · rw [sectionPairHom_snd, Equiv.symm_apply_apply]

/-- **The sections of a groupoid object in presheaves at a test object form a groupoid**, for
any composition law on composable pairs of sections which agrees with the composition of the
groupoid object. -/
noncomputable def pointwiseGroupoid (G : GroupoidObject (Eᵒᵖ ⥤ Type w)) (T : E)
    (c : G.SectionPairs T → G.arrows.obj (op T))
    (hc : ∀ p, c p = yonedaEquiv (G.sectionPairHom T p ≫ G.comp)) :
    PointwiseGroupoid (G.source.app (op T)) (G.target.app (op T)) c :=
  PointwiseGroupoid.ofSetData (G.setData T c hc)

end Presheaf

end GroupoidObject

end Deformation

end
