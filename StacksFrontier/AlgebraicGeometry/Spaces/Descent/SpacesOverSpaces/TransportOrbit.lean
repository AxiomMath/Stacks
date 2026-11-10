module

public import Mathlib.CategoryTheory.Comma.Presheaf.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.ShrinkYoneda
public import Mathlib.CategoryTheory.Sites.Sheafification
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.Transport

/-!
# The orbit object of a move operation

A `CategoryTheory.FamilyTransport` on a family of objects `A i` over a family of bases `B i`
identifies a point of `A i` with a point of `A j` whenever the move operation carries the one
to the other. The *orbit* of the family is the quotient of the disjoint union of the points of
the `A i` by that identification. Over each point of a base `B i` the orbit has exactly one
representative in `A i`, so the orbit is a product of that base with `A i`; this is the
construction that glues a family of objects along a family of gluing isomorphisms.

When the ambient category is `CategoryTheory.Over T` for a presheaf `T` on a category with
small homs, the orbit is again a presheaf over `T`: the points of the orbit over a
representable slice object form a small type, so the orbit presheaf of the restricted Yoneda
presheaves can be shrunk to the universe of the sections of `T` and transported back along
`CategoryTheory.overEquivPresheafCostructuredArrow`.

## Main definitions

* `CategoryTheory.FamilyTransport.orbitSetoid` is the identification of local points of the
  family made by the move operation, and `CategoryTheory.FamilyTransport.orbitFunctor` is the
  resulting presheaf of orbits.
* `CategoryTheory.FamilyTransport.orbitProjection` reads an orbit as a point of a prescribed
  member of the family, and `CategoryTheory.FamilyTransport.orbitEquivFiber` is the resulting
  bijection with the points of that member lying over a prescribed point of its base.
* `CategoryTheory.FamilyTransport.restrictedOrbit` is the orbit presheaf on the slice category
  of representables over `T`, shrunk to the universe of the sections of `T`, and
  `CategoryTheory.FamilyTransport.orbitOver` is the object of `CategoryTheory.Over T` it
  corresponds to.
* `CategoryTheory.FamilyTransport.toOrbitOver` is the canonical map from a member of the
  family to the orbit.

## Main results

* `CategoryTheory.FamilyTransport.orbitOverProductIsLimit`: the member `A i` is the product of
  the orbit with the base `B i`, which is the statement that the orbit pulls back along each
  base to the given family.
* `CategoryTheory.FamilyTransport.toOrbitOver_move`: the canonical maps to the orbit identify
  a point with every point it moves to, which is the compatibility of the gluing isomorphisms
  with the glued object.
* `CategoryTheory.isPullback_sheafify`: a cartesian square of presheaves three of whose
  corners are sheaves stays cartesian after sheafifying the fourth, so a product
  decomposition of a presheaf over a sheaf survives sheafification.

## Implementation notes

The relation of `CategoryTheory.FamilyTransport.orbitSetoid` is `t.move x y = y`, read as "`y`
is a move of `x`"; reflexivity, symmetry and transitivity are exactly the axioms `move_self`,
`move_comp` and `move_base` of the move operation, so no cocycle condition is reproved here.

Smallness of the orbit comes from
`CategoryTheory.FamilyTransport.orbitProjection_injective`: as soon as the family has one
point at all, every orbit is pinned down by its representative in a single member, so the
index type of the family may be large.

`CategoryTheory.FamilyTransport.orbitOver` is built from a presheaf on the slice category of
representables rather than on the site itself, because
`CategoryTheory.overEquivPresheafCostructuredArrow` is the equivalence that turns such a
presheaf into an object of `CategoryTheory.Over T`, and the smallness of the orbit is only
available over representable slice objects.

The codomain universe of `CategoryTheory.FamilyTransport.orbitFunctor` is written out rather
than inferred: left to elaboration it becomes a universe metavariable that
`CategoryTheory.FamilyTransport.restrictedOrbit` cannot resolve.

## References

* [Stacks Project, Tag 0ADT](https://stacks.math.columbia.edu/tag/0ADT)
* [Stacks Project, Tag 0ADI](https://stacks.math.columbia.edu/tag/0ADI)
-/

@[expose] public section

noncomputable section

open CategoryTheory.Limits Opposite

universe w₁ w₂ v₁ u₁ u₂ u

namespace CategoryTheory

/-! ### Orbits of a move operation -/

namespace FamilyTransport

section Abstract

variable {C : Type u₁} [Category.{v₁} C] {I : Type w₁} {A B : I → C} {p : ∀ i, A i ⟶ B i}

/-- Two local points of a family carrying a move operation determine the same orbit when the
move operation carries the one to the other. -/
public def orbitSetoid (t : FamilyTransport A B p) (Z : C) : Setoid (Σ i, Z ⟶ A i) where
  r x y := t.move x.2 (y.2 ≫ p y.1) = y.2
  iseqv := by
    refine ⟨fun x ↦ t.move_self x.2, ?_, ?_⟩
    · intro x y h
      rw [← h, t.move_comp, t.move_self]
    · intro x y z hxy hyz
      rwa [← hxy, t.move_comp] at hyz

/-- Reading an orbit as a point of the member of the family singled out by a point of its
base. -/
public def orbitProjection (t : FamilyTransport A B p) {Z : C} {i : I} (y : Z ⟶ B i) :
    _root_.Quotient (t.orbitSetoid Z) → (Z ⟶ A i) :=
  _root_.Quotient.lift (fun x ↦ t.move x.2 y) (by
    intro x x' h
    change t.move x.2 (x'.2 ≫ p x'.1) = x'.2 at h
    rw [← h, t.move_comp])

/-- An orbit is determined by the way it reads in a single member of the family. -/
public theorem orbitProjection_injective (t : FamilyTransport A B p) {Z : C} {i : I}
    (y : Z ⟶ B i) : Function.Injective (t.orbitProjection y) := by
  intro a b
  refine _root_.Quotient.inductionOn₂ a b ?_
  intro x x' h
  apply _root_.Quotient.sound
  change t.move x.2 (x'.2 ≫ p x'.1) = x'.2
  have hh := congrArg (fun v ↦ t.move v (x'.2 ≫ p x'.1)) h
  change t.move (t.move x.2 y) (x'.2 ≫ p x'.1) =
    t.move (t.move x'.2 y) (x'.2 ≫ p x'.1) at hh
  simpa only [t.move_comp, t.move_self] using hh

/-- The orbits of a move operation form a small type as soon as the points of each member of
the family do, however large the index type of the family. -/
public theorem small_orbit (t : FamilyTransport A B p) (Z : C) [∀ i, Small.{u} (Z ⟶ A i)] :
    Small.{u} (_root_.Quotient (t.orbitSetoid Z)) := by
  classical
  by_cases h : Nonempty (Σ i, Z ⟶ A i)
  · obtain ⟨i, x⟩ := h
    exact small_of_injective (t.orbitProjection_injective (x ≫ p i))
  · have : IsEmpty (_root_.Quotient (t.orbitSetoid Z)) :=
      ⟨fun q ↦ _root_.Quotient.inductionOn q fun x ↦ h ⟨x⟩⟩
    infer_instance

/-- An orbit read in a member of the family lies over the prescribed point of its base. -/
public lemma orbitProjection_comp (t : FamilyTransport A B p) {Z : C} {i : I} (y : Z ⟶ B i)
    (q : _root_.Quotient (t.orbitSetoid Z)) : t.orbitProjection y q ≫ p i = y := by
  induction q using _root_.Quotient.inductionOn with
  | h x => exact t.move_base x.2 y

/-- An orbit is recovered from the way it reads in a single member of the family. -/
public lemma mk_orbitProjection (t : FamilyTransport A B p) {Z : C} {i : I} (y : Z ⟶ B i)
    (q : _root_.Quotient (t.orbitSetoid Z)) :
    _root_.Quotient.mk (t.orbitSetoid Z) ⟨i, t.orbitProjection y q⟩ = q := by
  apply t.orbitProjection_injective y
  induction q using _root_.Quotient.inductionOn with
  | h x => exact t.move_comp x.2 y y

/-- Over a prescribed point of the base `B i`, the orbits of a move operation are exactly the
points of `A i` lying over it. -/
public def orbitEquivFiber (t : FamilyTransport A B p) {Z : C} {i : I} (y : Z ⟶ B i) :
    _root_.Quotient (t.orbitSetoid Z) ≃ {x : Z ⟶ A i // x ≫ p i = y} where
  toFun q := ⟨t.orbitProjection y q, t.orbitProjection_comp y q⟩
  invFun x := _root_.Quotient.mk _ ⟨i, x.1⟩
  left_inv q := t.mk_orbitProjection y q
  right_inv x := by
    obtain ⟨x, hx⟩ := x
    apply Subtype.ext
    change t.move x y = x
    rw [← hx, t.move_self]

/-- The presheaf of orbits of a move operation. -/
public def orbitFunctor (t : FamilyTransport A B p) : Cᵒᵖ ⥤ Type (max w₁ v₁) where
  obj Z := _root_.Quotient (t.orbitSetoid Z.unop)
  map a := ↾(_root_.Quotient.map (fun x ↦ ⟨x.1, a.unop ≫ x.2⟩) (by
    intro x y h
    change t.move (a.unop ≫ x.2) ((a.unop ≫ y.2) ≫ p y.1) = a.unop ≫ y.2
    rw [Category.assoc, ← t.comp_move, h]))
  map_id Z := by
    ext q
    induction q using _root_.Quotient.inductionOn with
    | h x =>
      change _root_.Quotient.mk _ ⟨x.1, (𝟙 Z.unop) ≫ x.2⟩ = _root_.Quotient.mk _ x
      simp
  map_comp a b := by
    ext q
    induction q using _root_.Quotient.inductionOn with
    | h x =>
      change _root_.Quotient.mk (t.orbitSetoid _) ⟨x.1, (b.unop ≫ a.unop) ≫ x.2⟩ =
        _root_.Quotient.mk (t.orbitSetoid _) ⟨x.1, b.unop ≫ a.unop ≫ x.2⟩
      rw [Category.assoc]

end Abstract

end FamilyTransport

/-! ### Points of an object over a presheaf -/

section Over

variable {C : Type u₂} [Category.{u} C] {T : Cᵒᵖ ⥤ Type u}

/-- The points of an object over a presheaf, on a representable slice object, form a small
type. -/
public theorem small_overYoneda_hom (U : C) (t : yoneda.obj U ⟶ T) (A : Over T) :
    Small.{u} (Over.mk t ⟶ A) :=
  small_of_injective (f := fun k : Over.mk t ⟶ A ↦ yonedaEquiv k.left)
    fun _ _ h ↦ Over.OverMorphism.ext (yonedaEquiv.injective h)

/-- The sections of the restricted Yoneda presheaf of an object over `T` are the maps from the
slice object into that object. -/
public def overArrowsEquiv (A : Over T) (Z : CostructuredArrow yoneda T) :
    OverPresheafAux.OverArrows A.hom Z.hom ≃ (Over.mk Z.hom ⟶ A) where
  toFun x := Over.homMk (yonedaEquiv.symm x.val) (by
    apply yonedaEquiv.injective
    simpa [yonedaEquiv_comp, OverPresheafAux.OverArrows.val] using x.prop.app)
  invFun x := ⟨yonedaEquiv x.left, OverPresheafAux.MakesOverArrow.of_arrow (Over.w x)⟩
  left_inv x := Subtype.ext (yonedaEquiv.apply_symm_apply _)
  right_inv x := Over.OverMorphism.ext (yonedaEquiv.symm_apply_apply _)

/-- Restricting a point of an object over `T` along a map of slice objects is precomposing the
corresponding map. -/
public lemma overArrowsEquiv_map (A : Over T) {Z W : CostructuredArrow yoneda T} (k : Z ⟶ W)
    (x : OverPresheafAux.OverArrows A.hom W.hom) :
    overArrowsEquiv A Z ((OverPresheafAux.restrictedYonedaObj A.hom).map k.op x) =
      (CostructuredArrow.toOver yoneda T).map k ≫ overArrowsEquiv A W x := by
  apply Over.OverMorphism.ext
  apply yonedaEquiv.injective
  change yonedaEquiv (yonedaEquiv.symm (A.left.map k.left.op x.val)) =
    yonedaEquiv (yoneda.map k.left ≫ yonedaEquiv.symm x.val)
  simpa only [Equiv.apply_symm_apply] using
    yonedaEquiv_naturality (yonedaEquiv.symm x.val) k.left

/-- Pushing a point of an object over `T` forward along a map of objects over `T` is
postcomposing the corresponding map. -/
public lemma overArrowsEquiv_postcomp {A A' : Over T} (q : A ⟶ A')
    (Z : CostructuredArrow yoneda T) (x : OverPresheafAux.OverArrows A.hom Z.hom) :
    overArrowsEquiv A' Z (((OverPresheafAux.restrictedYoneda T).map q).app (op Z) x) =
      overArrowsEquiv A Z x ≫ q := by
  apply Over.OverMorphism.ext
  apply yonedaEquiv.injective
  change yonedaEquiv (yonedaEquiv.symm (q.left.app _ x.val)) =
    yonedaEquiv (yonedaEquiv.symm x.val ≫ q.left)
  simp [yonedaEquiv_comp]

namespace FamilyTransport

variable {I : Type w₂} {A B : I → Over T} {p : ∀ i, A i ⟶ B i}

/-- The orbits of a move operation in `Over T` over a representable slice object form a small
type. -/
public theorem small_restrictedOrbit_obj (t : FamilyTransport A B p)
    (Z : CostructuredArrow yoneda T) :
    Small.{u} (_root_.Quotient (t.orbitSetoid (Over.mk Z.hom))) := by
  have : ∀ i, Small.{u} (Over.mk Z.hom ⟶ A i) :=
    fun i ↦ small_overYoneda_hom Z.left Z.hom (A i)
  exact t.small_orbit (Over.mk Z.hom)

attribute [local instance] small_restrictedOrbit_obj

/-- The presheaf of orbits of a move operation in `Over T`, restricted to the representable
slice objects, has small sections. -/
public theorem small_restrictedOrbit (t : FamilyTransport A B p) :
    FunctorToTypes.Small.{u} ((CostructuredArrow.toOver yoneda T).op ⋙ t.orbitFunctor) :=
  fun Z ↦ t.small_restrictedOrbit_obj Z.unop

attribute [local instance] small_restrictedOrbit

/-- The presheaf of orbits of a move operation in `Over T`, on the slice category of
representables and with its sections shrunk to the universe of the sections of `T`. -/
public def restrictedOrbit (t : FamilyTransport A B p) :
    (CostructuredArrow yoneda T)ᵒᵖ ⥤ Type u :=
  FunctorToTypes.shrink.{u} ((CostructuredArrow.toOver yoneda T).op ⋙ t.orbitFunctor)

/-- The sections of the shrunk orbit presheaf over a representable slice object are the orbits
over that slice object. -/
public def restrictedOrbitEquiv (t : FamilyTransport A B p) (Z : CostructuredArrow yoneda T) :
    t.restrictedOrbit.obj (op Z) ≃ _root_.Quotient (t.orbitSetoid (Over.mk Z.hom)) :=
  (equivShrink.{u} (((CostructuredArrow.toOver yoneda T).op ⋙ t.orbitFunctor).obj (op Z))).symm

/-- Restriction in the shrunk orbit presheaf is restriction of orbits. -/
public lemma restrictedOrbitEquiv_map (t : FamilyTransport A B p)
    {Z W : (CostructuredArrow yoneda T)ᵒᵖ} (k : Z ⟶ W) (x : t.restrictedOrbit.obj Z) :
    t.restrictedOrbitEquiv W.unop (t.restrictedOrbit.map k x) =
      t.orbitFunctor.map ((CostructuredArrow.toOver yoneda T).op.map k)
        (t.restrictedOrbitEquiv Z.unop x) := by
  change (equivShrink.{u} _).symm ((equivShrink.{u} _)
      (((CostructuredArrow.toOver yoneda T).op ⋙ t.orbitFunctor).map k
        ((equivShrink.{u} _).symm x))) = _
  exact Equiv.symm_apply_apply _ _

/-- The canonical map from the restricted Yoneda presheaf of a member of the family to the
shrunk orbit presheaf. -/
public def toRestrictedOrbit (t : FamilyTransport A B p) (i : I) :
    (overEquivPresheafCostructuredArrow T).functor.obj (A i) ⟶ t.restrictedOrbit where
  app Z := ↾fun x ↦ (t.restrictedOrbitEquiv Z.unop).symm
    (_root_.Quotient.mk (t.orbitSetoid (Over.mk Z.unop.hom))
      ⟨i, overArrowsEquiv (A i) Z.unop x⟩)
  naturality := by
    intro Z W k
    ext x
    change (t.restrictedOrbitEquiv W.unop).symm
        (_root_.Quotient.mk (t.orbitSetoid (Over.mk W.unop.hom))
          ⟨i, overArrowsEquiv (A i) W.unop
            (((overEquivPresheafCostructuredArrow T).functor.obj (A i)).map k x)⟩) =
      t.restrictedOrbit.map k ((t.restrictedOrbitEquiv Z.unop).symm
        (_root_.Quotient.mk (t.orbitSetoid (Over.mk Z.unop.hom))
          ⟨i, overArrowsEquiv (A i) Z.unop x⟩))
    apply (t.restrictedOrbitEquiv W.unop).injective
    rw [Equiv.apply_symm_apply, restrictedOrbitEquiv_map, Equiv.apply_symm_apply]
    exact congrArg (fun z : Over.mk W.unop.hom ⟶ A i ↦
        _root_.Quotient.mk (t.orbitSetoid (Over.mk W.unop.hom)) ⟨i, z⟩)
      (overArrowsEquiv_map (A i) k.unop x)

/-- The shrunk orbit of the canonical map to the orbit presheaf is the class of the point. -/
private lemma restrictedOrbitEquiv_toRestrictedOrbit (t : FamilyTransport A B p) (i : I)
    (Z : CostructuredArrow yoneda T) (x : OverPresheafAux.OverArrows (A i).hom Z.hom) :
    t.restrictedOrbitEquiv Z ((t.toRestrictedOrbit i).app (op Z) x) =
      _root_.Quotient.mk (t.orbitSetoid (Over.mk Z.hom)) ⟨i, overArrowsEquiv (A i) Z x⟩ :=
  Equiv.apply_symm_apply _ _

/-- Over a representable slice object, a point of the member `A i` is the same thing as an
orbit together with a point of the base `B i`. -/
public def restrictedOrbitProductEquiv (t : FamilyTransport A B p) (i : I)
    (Z : CostructuredArrow yoneda T) :
    OverPresheafAux.OverArrows (A i).hom Z.hom ≃
      (t.restrictedOrbit.obj (op Z) × OverPresheafAux.OverArrows (B i).hom Z.hom) where
  toFun x := ⟨(t.toRestrictedOrbit i).app (op Z) x,
    ((OverPresheafAux.restrictedYoneda T).map (p i)).app (op Z) x⟩
  invFun x := (overArrowsEquiv (A i) Z).symm
    (t.orbitProjection (overArrowsEquiv (B i) Z x.2) (t.restrictedOrbitEquiv Z x.1))
  left_inv x := by
    apply (overArrowsEquiv (A i) Z).injective
    rw [Equiv.apply_symm_apply]
    change t.orbitProjection (overArrowsEquiv (B i) Z
        (((OverPresheafAux.restrictedYoneda T).map (p i)).app (op Z) x))
        (t.restrictedOrbitEquiv Z ((t.restrictedOrbitEquiv Z).symm
          (_root_.Quotient.mk (t.orbitSetoid (Over.mk Z.hom))
            ⟨i, overArrowsEquiv (A i) Z x⟩))) = overArrowsEquiv (A i) Z x
    rw [Equiv.apply_symm_apply, overArrowsEquiv_postcomp]
    exact t.move_self _
  right_inv x := by
    apply _root_.Prod.ext
    · change (t.restrictedOrbitEquiv Z).symm
          (_root_.Quotient.mk (t.orbitSetoid (Over.mk Z.hom))
            ⟨i, overArrowsEquiv (A i) Z ((overArrowsEquiv (A i) Z).symm
              (t.orbitProjection (overArrowsEquiv (B i) Z x.2)
                (t.restrictedOrbitEquiv Z x.1)))⟩) = x.1
      rw [Equiv.apply_symm_apply, t.mk_orbitProjection, Equiv.symm_apply_apply]
    · apply (overArrowsEquiv (B i) Z).injective
      rw [overArrowsEquiv_postcomp, Equiv.apply_symm_apply]
      exact t.orbitProjection_comp _ _

/-- The restricted Yoneda presheaf of the member `A i` is the product of the shrunk orbit
presheaf with the restricted Yoneda presheaf of the base `B i`. -/
public def restrictedOrbitProductIsLimit (t : FamilyTransport A B p) (i : I) :
    IsLimit (BinaryFan.mk (t.toRestrictedOrbit i)
      ((overEquivPresheafCostructuredArrow T).functor.map (p i))) := by
  apply evaluationJointlyReflectsLimits
  intro Z
  refine (isLimitMapConeBinaryFanEquiv _ _ _).symm ?_
  let e := t.restrictedOrbitProductEquiv i Z.unop
  refine BinaryFan.isLimitMk (fun s ↦ ↾fun x ↦ e.symm (s.fst x, s.snd x)) ?_ ?_ ?_
  · intro s
    ext x
    exact congrArg _root_.Prod.fst (e.apply_symm_apply (s.fst x, s.snd x))
  · intro s
    ext x
    exact congrArg _root_.Prod.snd (e.apply_symm_apply (s.fst x, s.snd x))
  · intro s m h₁ h₂
    ext x
    apply e.injective
    change e (m x) = e (e.symm (s.fst x, s.snd x))
    rw [e.apply_symm_apply]
    exact _root_.Prod.ext (congrArg (fun k : s.pt ⟶ _ ↦ k x) h₁)
      (congrArg (fun k : s.pt ⟶ _ ↦ k x) h₂)

/-- The orbit of a move operation in `Over T`, as an object over `T`. This is the object the
family glues to. -/
public def orbitOver (t : FamilyTransport A B p) : Over T :=
  (overEquivPresheafCostructuredArrow T).inverse.obj t.restrictedOrbit

/-- The canonical map from a member of the family to the orbit. -/
public def toOrbitOver (t : FamilyTransport A B p) (i : I) : A i ⟶ t.orbitOver :=
  (overEquivPresheafCostructuredArrow T).functor.preimage
    (t.toRestrictedOrbit i ≫
      ((overEquivPresheafCostructuredArrow T).counitIso.app t.restrictedOrbit).inv)

/-- The canonical map to the orbit corresponds to the canonical map to the shrunk orbit
presheaf. -/
public lemma map_toOrbitOver (t : FamilyTransport A B p) (i : I) :
    (overEquivPresheafCostructuredArrow T).functor.map (t.toOrbitOver i) =
      t.toRestrictedOrbit i ≫
        ((overEquivPresheafCostructuredArrow T).counitIso.app t.restrictedOrbit).inv :=
  Functor.map_preimage _ _

/-- **The orbit pulls back to the given family.** The member `A i` is the product of the orbit
with the base `B i`, through the canonical map to the orbit and the structure map of the
family. -/
public def orbitOverProductIsLimit (t : FamilyTransport A B p) (i : I) :
    IsLimit (BinaryFan.mk (t.toOrbitOver i) (p i)) := by
  apply isLimitOfReflectsOfMapIsLimit (overEquivPresheafCostructuredArrow T).functor
  rw [t.map_toOrbitOver]
  exact BinaryFan.isLimitCompLeftIso
    (BinaryFan.mk (t.toRestrictedOrbit i)
      ((overEquivPresheafCostructuredArrow T).functor.map (p i)))
    ((overEquivPresheafCostructuredArrow T).counitIso.app t.restrictedOrbit).inv
    (t.restrictedOrbitProductIsLimit i)

/-- The canonical maps to the shrunk orbit presheaf identify a point with every point it moves
to. -/
public lemma toRestrictedOrbit_move (t : FamilyTransport A B p) {i j : I} {Z : Over T}
    (v : Z ⟶ A i) (y : Z ⟶ B j) :
    (overEquivPresheafCostructuredArrow T).functor.map v ≫ t.toRestrictedOrbit i =
      (overEquivPresheafCostructuredArrow T).functor.map (t.move v y) ≫
        t.toRestrictedOrbit j := by
  ext ⟨W⟩ x
  apply (t.restrictedOrbitEquiv W).injective
  refine (restrictedOrbitEquiv_toRestrictedOrbit t i W _).trans
    (Eq.trans ?_ (restrictedOrbitEquiv_toRestrictedOrbit t j W _).symm)
  have h₁ := overArrowsEquiv_postcomp v W x
  have h₂ := overArrowsEquiv_postcomp (t.move v y) W x
  erw [h₁, h₂]
  refine _root_.Quotient.sound ?_
  change t.move (overArrowsEquiv Z W x ≫ v)
      ((overArrowsEquiv Z W x ≫ t.move v y) ≫ p j) = overArrowsEquiv Z W x ≫ t.move v y
  rw [Category.assoc, t.move_base, t.comp_move]

/-- **The canonical maps to the orbit identify a point with every point it moves to.** -/
public lemma toOrbitOver_move (t : FamilyTransport A B p) {i j : I} {Z : Over T}
    (v : Z ⟶ A i) (y : Z ⟶ B j) :
    v ≫ t.toOrbitOver i = t.move v y ≫ t.toOrbitOver j := by
  apply (overEquivPresheafCostructuredArrow T).functor.map_injective
  simp only [Functor.map_comp, t.map_toOrbitOver]
  exact congrArg (fun k ↦ k ≫
    ((overEquivPresheafCostructuredArrow T).counitIso.app t.restrictedOrbit).inv)
    (t.toRestrictedOrbit_move v y)

end FamilyTransport

end Over

/-! ### Cartesian squares and sheafification -/

/-- **A cartesian square of presheaves survives sheafification of one corner.** If the fibre
product of a presheaf `U` with a sheaf `X` over a sheaf `T` is a sheaf, then the same square
with `U` replaced by its sheafification is cartesian. -/
public theorem isPullback_sheafify {C : Type u₁} [Category.{v₁} C]
    (J : GrothendieckTopology C) [HasSheafify J (Type u)] {A U X T : Cᵒᵖ ⥤ Type u} {q : A ⟶ U}
    {p : A ⟶ X} {g : U ⟶ T} {f : X ⟶ T} (h : IsPullback q p g f)
    (hA : Presheaf.IsSheaf J A) (hX : Presheaf.IsSheaf J X) (hT : Presheaf.IsSheaf J T) :
    IsPullback (q ≫ toSheafify J U) p (sheafifyLift J g hT) f := by
  apply (h.map (sheafification J (Type u))).of_iso'
    (isoSheafify J hA) (Iso.refl _) (isoSheafify J hX) (isoSheafify J hT)
  · simpa only [isoSheafify_hom, Iso.refl_hom, Category.comp_id, sheafification_map] using
      (toSheafify_naturality J q).symm
  · exact (toSheafify_naturality J p).symm
  · simp only [Iso.refl_hom, Category.id_comp, sheafification_map, isoSheafify_hom]
    apply sheafify_hom_ext J _ _ ((presheafToSheaf J (Type u)).obj T).property
    rw [← toSheafify_naturality, ← Category.assoc, toSheafify_sheafifyLift]
  · exact (toSheafify_naturality J f).symm

end CategoryTheory

end
