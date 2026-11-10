module

public import Mathlib.CategoryTheory.Comma.Presheaf.Basic
public import Mathlib.CategoryTheory.ShrinkYoneda
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.DescentDataSheavesEquivalence
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfOverTypeSheafification

/-!
# Descent data and sheaves: the quotient sheaf of a descent datum, and the equivalence

Let `{X i ⟶ T}` be a family of morphisms of algebraic spaces.
`StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.DescentDataSheavesEquivalence`
proves that the functor `AlgebraicGeometry.Space.Descent.fibreDescentFunctor` from sheaves over
`T` whose fibre products with the family are algebraic spaces to descent data relative to the
family is fully faithful when the family is an fppf covering, and that such a sheaf is an
algebraic space exactly when its descent datum is effective.  This file constructs the functor
in the other direction and so proves the **equivalence of categories** asserted by Tag 0ADT.

A descent datum `{V i}` with its gluing isomorphisms has a *quotient*: a local lift over a test
object is a point of one of the `V i`, two local lifts are identified when the move operation of
the gluing isomorphisms carries one to the other, and the presheaf of equivalence classes is the
coequalizer of the two maps `∐_{i,j} V i ×_T X j ⇉ ∐_i V i`.  Each `V i` is the fibre product of
that presheaf with `X i`, because the lifts of a point of `X i` to the quotient are exactly the
points of `V i` over it.  The three other corners of that square are sheaves, so fppf
sheafification leaves it cartesian, and the sheafification is therefore a sheaf over `T` whose
fibre products with the family are the `V i`.  This makes the functor to descent data
**essentially surjective**, and with full faithfulness it is an equivalence.

## Main definitions

* `AlgebraicGeometry.Space.Descent.Orbit.orbitOver` is the quotient of a move operation — the
  presheaf of equivalence classes of local lifts — with
  `AlgebraicGeometry.Space.Descent.Orbit.toOrbitOver` the canonical maps to it from the members
  of the family. This is generic category theory, for an arbitrary
  `CategoryTheory.FamilyTransport`.
* `AlgebraicGeometry.Space.Descent.descentOrbit` is that quotient for the move operation of a
  descent datum, `AlgebraicGeometry.Space.Descent.descentQuotient` is its fppf sheafification
  as a sheaf over `T` with algebraic-space fibres, and
  `AlgebraicGeometry.Space.Descent.toDescentQuotient` are the canonical maps from the
  components.
* `AlgebraicGeometry.Space.Descent.fibreDescentFunctorEquivalence` is the equivalence of
  categories asserted by Tag 0ADT.

## Main results

* `AlgebraicGeometry.Space.Descent.Orbit.orbitOverProductIsLimit`: each member of a family
  carrying a move operation is the fibre product of the quotient with its own base, and
  `AlgebraicGeometry.Space.Descent.Orbit.isPullback_sheafify`: sheafifying a cartesian square
  whose three other corners are sheaves leaves it cartesian.
* `AlgebraicGeometry.Space.Descent.isPullback_toDescentQuotient`: the `i`-th component of a
  descent datum is the fibre product of its quotient sheaf with `X i`, and
  `AlgebraicGeometry.Space.Descent.descentQuotientIso`: the descent datum of the quotient sheaf
  is the given datum.
* `AlgebraicGeometry.Space.Descent.essSurj_fibreDescentFunctor`: the functor to descent data is
  essentially surjective, and
  `AlgebraicGeometry.Space.Descent.isEquivalence_fibreDescentFunctor`: for an fppf covering it
  is an equivalence.
* `AlgebraicGeometry.Space.Descent.isAlgebraicSpace_descentQuotient`: the quotient sheaf of an
  effective descent datum is an algebraic space.

## Implementation notes

The functor in the other direction, which the source constructs as the coequalizer of
`∐_{i,j} V i ×_T X j ⇉ ∐_i V i`, is realized here as the quotient of the move operation of the
datum rather than as a colimit of a diagram of sheaves: the sections of the coequalizer presheaf
over a test object are the orbits of local lifts, which is what that colimit computes, and
taking them directly avoids needing the coproducts to exist as algebraic spaces — the
restriction `B.AdmitsCoproductIndex` of
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/SpacesOverSpaces/CoproductAlgebraicity.lean`,
which fails for index types cofinal in the site's cutoff. The index type is accordingly
arbitrary, and the equivalence of Tag 0ADK between descent data for a family and for its sheaf
coproduct is not used on this route. The orbits over a representable test object are small
because they inject into the maps to a single member
(`AlgebraicGeometry.Space.Descent.Orbit.small_orbit`), which is what lets the quotient be
shrunk back to the universe of the sections.

Essential surjectivity needs only that `T` and the `X i` are algebraic spaces: no fppf
covering hypothesis, which enters solely through full faithfulness. So the equivalence of
categories is available exactly where the covering hypothesis is, and the identification of
the components, `AlgebraicGeometry.Space.Descent.isPullback_toDescentQuotient`, holds without
it.

Tag 0ADV, which the source's footnote invokes for the unconditional statement that the
coequalizer sheaf is an algebraic space when the index type is not too large, is **not** used
and **not** available in this library. It is not needed for essential surjectivity, nor for the
equivalence of categories: the quotient sheaf is produced as a *sheaf* with algebraic-space
fibre products, which is all the equivalence asks of it, and part (2) of Tag 0ADT then says that
it is an algebraic space exactly when the datum is effective
(`AlgebraicGeometry.Space.Descent.isAlgebraicSpace_descentQuotient`). Effectivity is available
when one member of the covering is surjective and étale, by
`AlgebraicGeometry.Space.Descent.isEffective_of_isEtale` in the module
`StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.EffectiveEtaleMemberCovering`.

## References

* [Stacks Project, Tag 0ADT](https://stacks.math.columbia.edu/tag/0ADT)
* [Stacks Project, Tag 0ADK](https://stacks.math.columbia.edu/tag/0ADK)
* [Stacks Project, Tag 0ADV](https://stacks.math.columbia.edu/tag/0ADV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space.Descent

/-! ### The quotient of a move operation

Generic category theory, for an arbitrary move operation on a family of objects over a family
of bases. A *local lift* over a test object `Z` is a point of one of the members; two local
lifts are *equivalent* when the move operation carries one to the other. The presheaf of
equivalence classes is the coequalizer of the two maps from the pairwise overlaps to the
disjoint union of the members, and each member is the fibre product of that presheaf with its
own base. -/

namespace Orbit

variable {C : Type*} [Category C] {I : Type*} {A Bb : I → C} {p : ∀ i, A i ⟶ Bb i}

/-- Two local lifts determine the same orbit when the move operation carries one to the
other. -/
public def orbitSetoid (t : FamilyTransport A Bb p) (Z : C) : Setoid (Σ i, Z ⟶ A i) where
  r x y := t.move x.2 (y.2 ≫ p y.1) = y.2
  iseqv := by
    refine ⟨fun x ↦ t.move_self x.2, ?_, ?_⟩
    · intro x y h
      rw [← h, t.move_comp, t.move_self]
    · intro x y z hxy hyz
      rw [← hxy, t.move_comp] at hyz
      exact hyz

/-- An orbit of local lifts, read in the member singled out by a point of the base. -/
public def orbitProjection (t : FamilyTransport A Bb p) {Z : C} {i : I} (y : Z ⟶ Bb i) :
    Quotient (orbitSetoid t Z) → (Z ⟶ A i) :=
  Quotient.lift (fun x ↦ t.move x.2 y) (by
    intro x x' h
    change t.move x.2 (x'.2 ≫ p x'.1) = x'.2 at h
    rw [← h, t.move_comp])

/-- Reading an orbit in a member of the family loses nothing. -/
public theorem orbitProjection_injective (t : FamilyTransport A Bb p) {Z : C} {i : I}
    (y : Z ⟶ Bb i) : Function.Injective (orbitProjection t y) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro x x' h
  apply Quotient.sound
  change t.move x.2 (x'.2 ≫ p x'.1) = x'.2
  have hh := congrArg (fun v ↦ t.move v (x'.2 ≫ p x'.1)) h
  change t.move (t.move x.2 y) (x'.2 ≫ p x'.1) =
    t.move (t.move x'.2 y) (x'.2 ≫ p x'.1) at hh
  simpa only [t.move_comp, t.move_self] using hh

/-- The orbits over a test object form a small type even for a large index type, since they
inject into the maps to a single member. -/
public theorem small_orbit (t : FamilyTransport A Bb p) (Z : C) [∀ i, Small.{u} (Z ⟶ A i)] :
    Small.{u} (Quotient (orbitSetoid t Z)) := by
  classical
  by_cases h : Nonempty (Σ i, Z ⟶ A i)
  · obtain ⟨i, x⟩ := h
    exact small_of_injective (orbitProjection_injective t (x ≫ p i))
  · let : IsEmpty (Quotient (orbitSetoid t Z)) :=
      ⟨fun q ↦ Quotient.inductionOn q fun x ↦ h ⟨x⟩⟩
    infer_instance

/-- The orbits over a test object are the lifts to one member of a prescribed point of its
base: the member is the fibre product of the orbits with the base. -/
public def orbitEquivFiber (t : FamilyTransport A Bb p) {Z : C} {i : I} (y : Z ⟶ Bb i) :
    Quotient (orbitSetoid t Z) ≃ {x : Z ⟶ A i // x ≫ p i = y} where
  toFun q := ⟨orbitProjection t y q, by
    induction q using Quotient.inductionOn with
    | h x => exact t.move_base x.2 y⟩
  invFun x := Quotient.mk _ ⟨i, x.1⟩
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h x => exact orbitProjection_injective t y (t.move_comp x.2 y y)
  right_inv x := by
    rcases x with ⟨x, hx⟩
    apply Subtype.ext
    change t.move x y = x
    rw [← hx, t.move_self]

/-- The presheaf of orbits of local lifts of a move operation. -/
public def orbitPresheaf (t : FamilyTransport A Bb p) : Cᵒᵖ ⥤ Type _ where
  obj Z := Quotient (orbitSetoid t Z.unop)
  map a := ↾(Quotient.map (fun x ↦ ⟨x.1, a.unop ≫ x.2⟩) (by
    intro x y h
    change t.move (a.unop ≫ x.2) ((a.unop ≫ y.2) ≫ p y.1) = a.unop ≫ y.2
    rw [Category.assoc, ← t.comp_move, h]))
  map_id Z := by
    ext q
    induction q using Quotient.inductionOn with
    | h x =>
      change Quotient.mk _ ⟨x.1, (𝟙 Z.unop) ≫ x.2⟩ = Quotient.mk _ x
      simp
  map_comp a b := by
    ext q
    induction q using Quotient.inductionOn with
    | h x =>
      change Quotient.mk (orbitSetoid t _) ⟨x.1, (b.unop ≫ a.unop) ≫ x.2⟩ =
        Quotient.mk (orbitSetoid t _) ⟨x.1, b.unop ≫ a.unop ≫ x.2⟩
      rw [Category.assoc]

/-! #### Shrinking the orbit presheaf to a space over the base -/

section Over

variable {Site : Type*} [Category.{u} Site] {Tg : Siteᵒᵖ ⥤ Type u}

/-- The shrunk presheaf acts on a shrunk section by the action of the original presheaf. -/
public lemma shrink_map_equivShrink {E : Type*} [Category E] (G : E ⥤ Type v)
    [FunctorToTypes.Small.{u} G] {Z W : E} (k : Z ⟶ W) (z : G.obj Z) :
    ConcreteCategory.hom ((FunctorToTypes.shrink.{u} G).map k) (equivShrink (G.obj Z) z) =
      equivShrink (G.obj W) (ConcreteCategory.hom (G.map k) z) := by
  simp [FunctorToTypes.shrink]

/-- Maps over a presheaf out of a representable are a small type: such a map is pinned down by
a single section. -/
public theorem small_overYoneda_hom (U : Site) (s : yoneda.obj U ⟶ Tg) (Z : Over Tg) :
    Small.{u} (Over.mk s ⟶ Z) :=
  small_of_injective (f := fun k : Over.mk s ⟶ Z ↦ yonedaEquiv k.left)
    fun _ _ h ↦ Over.OverMorphism.ext (yonedaEquiv.injective h)

/-- Arrows over a presheaf out of a representable are the sections of the restricted Yoneda
presheaf. -/
public def overArrowsEquiv (Z : Over Tg) (W : CostructuredArrow yoneda Tg) :
    OverPresheafAux.OverArrows Z.hom W.hom ≃ (Over.mk W.hom ⟶ Z) where
  toFun x := Over.homMk (yonedaEquiv.symm x.val) (by
    apply yonedaEquiv.injective
    simpa [yonedaEquiv_comp, OverPresheafAux.OverArrows.val] using x.prop.app)
  invFun x := ⟨yonedaEquiv x.left, OverPresheafAux.MakesOverArrow.of_arrow (Over.w x)⟩
  left_inv x := by apply Subtype.ext; exact yonedaEquiv.apply_symm_apply _
  right_inv x := by apply Over.OverMorphism.ext; exact yonedaEquiv.symm_apply_apply _

/-- The identification of arrows with sections is natural in the representable. -/
public lemma overArrowsEquiv_map (Z : Over Tg) {W W' : CostructuredArrow yoneda Tg}
    (k : W ⟶ W') (x : OverPresheafAux.OverArrows Z.hom W'.hom) :
    overArrowsEquiv Z W ((OverPresheafAux.restrictedYonedaObj Z.hom).map k.op x) =
      (CostructuredArrow.toOver yoneda Tg).map k ≫ overArrowsEquiv Z W' x := by
  apply Over.OverMorphism.ext
  apply yonedaEquiv.injective
  change yonedaEquiv (yonedaEquiv.symm (Z.left.map k.left.op x.val)) =
    yonedaEquiv (yoneda.map k.left ≫ yonedaEquiv.symm x.val)
  simpa only [Equiv.apply_symm_apply] using
    yonedaEquiv_naturality (yonedaEquiv.symm x.val) k.left

/-- The identification of arrows with sections is natural in the target. -/
public lemma overArrowsEquiv_postcomp {Z Z' : Over Tg} (m : Z ⟶ Z')
    (W : CostructuredArrow yoneda Tg) (x : OverPresheafAux.OverArrows Z.hom W.hom) :
    overArrowsEquiv Z' W ((OverPresheafAux.restrictedYoneda Tg).map m |>.app (op W) <| x) =
      overArrowsEquiv Z W x ≫ m := by
  apply Over.OverMorphism.ext
  apply yonedaEquiv.injective
  change yonedaEquiv (yonedaEquiv.symm (m.left.app _ x.val)) =
    yonedaEquiv (yonedaEquiv.symm x.val ≫ m.left)
  simp [yonedaEquiv_comp]

variable {A Bb : I → Over Tg} {p : ∀ i, A i ⟶ Bb i}

/-- Over a representable the orbits of a move operation on spaces over a presheaf are a small
type, however large the index type. -/
public theorem small_restrictedOrbit_obj (t : FamilyTransport A Bb p)
    (W : CostructuredArrow yoneda Tg) :
    Small.{u} (Quotient (orbitSetoid t (Over.mk W.hom))) := by
  let : ∀ i, Small.{u} (Over.mk W.hom ⟶ A i) :=
    fun i ↦ small_overYoneda_hom W.left W.hom (A i)
  exact small_orbit t (Over.mk W.hom)

attribute [local instance] small_restrictedOrbit_obj

/-- The orbit presheaf restricted to the representables over the base takes small values. -/
public theorem small_restrictedOrbit (t : FamilyTransport A Bb p) :
    FunctorToTypes.Small.{u} ((CostructuredArrow.toOver yoneda Tg).op ⋙ orbitPresheaf t) :=
  fun W ↦ small_restrictedOrbit_obj t W.unop

attribute [local instance] small_restrictedOrbit

/-- The orbit presheaf, restricted to the representables over the base and shrunk to the
universe of the sections. -/
public def restrictedOrbit (t : FamilyTransport A Bb p) :
    (CostructuredArrow yoneda Tg)ᵒᵖ ⥤ Type u :=
  FunctorToTypes.shrink ((CostructuredArrow.toOver yoneda Tg).op ⋙ orbitPresheaf t)

/-- The map from the `i`-th member of the family to the restricted orbit presheaf, sending a
point to its orbit. -/
public def toRestrictedOrbit (t : FamilyTransport A Bb p) (i : I) :
    (overEquivPresheafCostructuredArrow Tg).functor.obj (A i) ⟶ restrictedOrbit t where
  app W := ↾fun x ↦ equivShrink.{u} _ (Quotient.mk _ ⟨i, overArrowsEquiv (A i) W.unop x⟩)
  naturality := by
    intro W W' k
    ext x
    change equivShrink (((CostructuredArrow.toOver yoneda Tg).op ⋙ orbitPresheaf t).obj W')
        (Quotient.mk (orbitSetoid t (Over.mk W'.unop.hom))
          ⟨i, overArrowsEquiv (A i) W'.unop
            ((OverPresheafAux.restrictedYonedaObj (A i).hom).map k x)⟩) =
      ConcreteCategory.hom
        ((FunctorToTypes.shrink.{u}
          ((CostructuredArrow.toOver yoneda Tg).op ⋙ orbitPresheaf t)).map k)
        (equivShrink (((CostructuredArrow.toOver yoneda Tg).op ⋙ orbitPresheaf t).obj W)
          (Quotient.mk (orbitSetoid t (Over.mk W.unop.hom))
            ⟨i, overArrowsEquiv (A i) W.unop x⟩))
    exact (congrArg
        (equivShrink (((CostructuredArrow.toOver yoneda Tg).op ⋙ orbitPresheaf t).obj W'))
        (congrArg (fun z : Over.mk W'.unop.hom ⟶ A i ↦
          Quotient.mk (orbitSetoid t (Over.mk W'.unop.hom))
            (⟨i, z⟩ : Σ j, Over.mk W'.unop.hom ⟶ A j))
          (overArrowsEquiv_map (A i) k.unop x))).trans
      (shrink_map_equivShrink ((CostructuredArrow.toOver yoneda Tg).op ⋙ orbitPresheaf t) k
        (Quotient.mk (orbitSetoid t (Over.mk W.unop.hom))
          ⟨i, overArrowsEquiv (A i) W.unop x⟩)).symm

/-- A section of the `i`-th member goes to the orbit of the corresponding local lift. -/
private lemma toRestrictedOrbit_app (t : FamilyTransport A Bb p) (i : I)
    (W : (CostructuredArrow yoneda Tg)ᵒᵖ) (x : OverPresheafAux.OverArrows (A i).hom W.unop.hom) :
    ConcreteCategory.hom ((toRestrictedOrbit t i).app W) x =
      equivShrink.{u} _ (Quotient.mk (orbitSetoid t (Over.mk W.unop.hom))
        ⟨i, overArrowsEquiv (A i) W.unop x⟩) :=
  rfl

/-- Sections of the `i`-th member over a representable are an orbit together with a section of
its base. -/
public def restrictedOrbitProductEquiv (t : FamilyTransport A Bb p) (i : I)
    (W : CostructuredArrow yoneda Tg) :
    OverPresheafAux.OverArrows (A i).hom W.hom ≃
      ((restrictedOrbit t).obj (op W) × OverPresheafAux.OverArrows (Bb i).hom W.hom) where
  toFun x := ⟨(toRestrictedOrbit t i).app (op W) x,
    ((OverPresheafAux.restrictedYoneda Tg).map (p i)).app (op W) x⟩
  invFun x := (overArrowsEquiv (A i) W).symm
    (orbitProjection t (overArrowsEquiv (Bb i) W x.2)
      ((equivShrink.{u} (Quotient (orbitSetoid t (Over.mk W.hom)))).symm x.1))
  left_inv x := by
    apply (overArrowsEquiv (A i) W).injective
    simp only [Equiv.apply_symm_apply]
    change orbitProjection t (overArrowsEquiv (Bb i) W
      (((OverPresheafAux.restrictedYoneda Tg).map (p i)).app (op W) x))
        ((equivShrink.{u} (Quotient (orbitSetoid t (Over.mk W.hom)))).symm
          (equivShrink.{u} (Quotient (orbitSetoid t (Over.mk W.hom)))
            (Quotient.mk (orbitSetoid t (Over.mk W.hom)) ⟨i, _⟩))) = _
    rw [Equiv.symm_apply_apply, overArrowsEquiv_postcomp]
    exact t.move_self _
  right_inv x := by
    apply Prod.ext
    · change equivShrink.{u} (Quotient (orbitSetoid t (Over.mk W.hom)))
        (Quotient.mk (orbitSetoid t (Over.mk W.hom))
          ⟨i, overArrowsEquiv (A i) W ((overArrowsEquiv (A i) W).symm _)⟩) = x.1
      rw [Equiv.apply_symm_apply]
      have h := (orbitEquivFiber t (overArrowsEquiv (Bb i) W x.2)).left_inv
        ((equivShrink.{u} (Quotient (orbitSetoid t (Over.mk W.hom)))).symm x.1)
      change Quotient.mk (orbitSetoid t (Over.mk W.hom)) ⟨i, orbitProjection t _ _⟩ = _ at h
      rw [h]
      exact (equivShrink.{u} (Quotient (orbitSetoid t (Over.mk W.hom)))).apply_symm_apply x.1
    · apply (overArrowsEquiv (Bb i) W).injective
      rw [overArrowsEquiv_postcomp, Equiv.apply_symm_apply]
      exact (orbitEquivFiber t (overArrowsEquiv (Bb i) W x.2)
        ((equivShrink.{u} (Quotient (orbitSetoid t (Over.mk W.hom)))).symm x.1)).property

/-- The `i`-th member of the family is the product of the restricted orbit presheaf with its
base. -/
public def restrictedOrbitProductIsLimit (t : FamilyTransport A Bb p) (i : I) :
    IsLimit (BinaryFan.mk (toRestrictedOrbit t i)
      ((overEquivPresheafCostructuredArrow Tg).functor.map (p i))) := by
  apply evaluationJointlyReflectsLimits
  intro W
  refine (isLimitMapConeBinaryFanEquiv _ _ _).symm ?_
  let e := restrictedOrbitProductEquiv t i W.unop
  refine BinaryFan.isLimitMk (fun s ↦ ↾fun x ↦ e.symm (s.fst x, s.snd x))
    (fun s ↦ ?_) (fun s ↦ ?_) (fun s m h₁ h₂ ↦ ?_) <;> ext x
  · exact congrArg Prod.fst (e.apply_symm_apply (s.fst x, s.snd x))
  · exact congrArg Prod.snd (e.apply_symm_apply (s.fst x, s.snd x))
  · exact e.eq_symm_apply.2 <| Prod.ext (congrArg (fun k : s.pt ⟶ _ ↦ k x) h₁)
      (congrArg (fun k : s.pt ⟶ _ ↦ k x) h₂)

/-- **The quotient of a move operation**, as a space over the base: the presheaf of orbits of
local lifts. This is the coequalizer of the two maps from the pairwise overlaps to the
disjoint union of the members of the family. -/
public def orbitOver (t : FamilyTransport A Bb p) : Over Tg :=
  (overEquivPresheafCostructuredArrow Tg).inverse.obj (restrictedOrbit t)

/-- The canonical map from the `i`-th member of the family to the quotient. -/
public def toOrbitOver (t : FamilyTransport A Bb p) (i : I) : A i ⟶ orbitOver t :=
  (overEquivPresheafCostructuredArrow Tg).functor.preimage
    (toRestrictedOrbit t i ≫
      ((overEquivPresheafCostructuredArrow Tg).counitIso.app (restrictedOrbit t)).inv)

/-- The canonical map to the quotient is the map to the restricted orbit presheaf. -/
public lemma map_toOrbitOver (t : FamilyTransport A Bb p) (i : I) :
    (overEquivPresheafCostructuredArrow Tg).functor.map (toOrbitOver t i) =
      toRestrictedOrbit t i ≫
        ((overEquivPresheafCostructuredArrow Tg).counitIso.app (restrictedOrbit t)).inv :=
  Functor.map_preimage _ _

/-- **Each member of the family is the fibre product of the quotient with its own base.** -/
public def orbitOverProductIsLimit (t : FamilyTransport A Bb p) (i : I) :
    IsLimit (BinaryFan.mk (toOrbitOver t i) (p i)) := by
  apply isLimitOfReflectsOfMapIsLimit (overEquivPresheafCostructuredArrow Tg).functor
  rw [map_toOrbitOver]
  exact BinaryFan.isLimitCompLeftIso _
    ((overEquivPresheafCostructuredArrow Tg).counitIso.app (restrictedOrbit t)).inv
    (restrictedOrbitProductIsLimit t i)

/-- The maps to the restricted orbit presheaf identify a point with every point it moves
to. -/
public lemma toRestrictedOrbit_move (t : FamilyTransport A Bb p) {i j : I} {Z : Over Tg}
    (v : Z ⟶ A i) (y : Z ⟶ Bb j) :
    (overEquivPresheafCostructuredArrow Tg).functor.map v ≫ toRestrictedOrbit t i =
      (overEquivPresheafCostructuredArrow Tg).functor.map (t.move v y) ≫
        toRestrictedOrbit t j := by
  ext W x
  unfold overEquivPresheafCostructuredArrow at x
  refine (toRestrictedOrbit_app t i W _).trans
    ((?_ : _ = _).trans (toRestrictedOrbit_app t j W _).symm)
  have h₁ := overArrowsEquiv_postcomp v W.unop x
  have h₂ := overArrowsEquiv_postcomp (t.move v y) W.unop x
  simp only [Opposite.op_unop] at h₁ h₂
  erw [h₁, h₂]
  congr 1
  apply Quotient.sound
  change t.move (overArrowsEquiv Z W.unop x ≫ v)
    ((overArrowsEquiv Z W.unop x ≫ t.move v y) ≫ p j) =
      overArrowsEquiv Z W.unop x ≫ t.move v y
  rw [Category.assoc, t.move_base, t.comp_move]

/-- **The canonical maps to the quotient identify a point with every point it moves to.** This
is the relation the quotient divides by. -/
public lemma toOrbitOver_move (t : FamilyTransport A Bb p) {i j : I} {Z : Over Tg}
    (v : Z ⟶ A i) (y : Z ⟶ Bb j) :
    v ≫ toOrbitOver t i = t.move v y ≫ toOrbitOver t j := by
  apply (overEquivPresheafCostructuredArrow Tg).functor.map_injective
  simp only [Functor.map_comp, map_toOrbitOver]
  exact congrArg (fun k ↦ k ≫
    ((overEquivPresheafCostructuredArrow Tg).counitIso.app (restrictedOrbit t)).inv)
    (toRestrictedOrbit_move t v y)

end Over

/-! #### Sheafification preserves a pullback square with three sheaf corners -/

section Sheafify

universe w'

/-- Sheafifying a pullback square whose three other corners are already sheaves leaves it a
pullback square: sheafification is a left exact localization. -/
public theorem isPullback_sheafify {E : Type v} [Category.{w'} E] (J : GrothendieckTopology E)
    [HasSheafify J (Type u)] {Z U Y Tg : Eᵒᵖ ⥤ Type u} {q : Z ⟶ U} {m : Z ⟶ Y}
    {g : U ⟶ Tg} {h : Y ⟶ Tg} (sq : IsPullback q m g h)
    (hZ : Presheaf.IsSheaf J Z) (hY : Presheaf.IsSheaf J Y) (hT : Presheaf.IsSheaf J Tg) :
    IsPullback (q ≫ toSheafify J U) m (sheafifyLift J g hT) h := by
  apply (sq.map (sheafification J (Type u))).of_iso'
    (isoSheafify J hZ) (Iso.refl _) (isoSheafify J hY) (isoSheafify J hT)
  · simpa only [isoSheafify_hom, Iso.refl_hom, Category.comp_id, sheafification_map] using
      (toSheafify_naturality J q).symm
  · exact (toSheafify_naturality J m).symm
  · simp only [Iso.refl_hom, Category.id_comp, sheafification_map, isoSheafify_hom]
    apply sheafify_hom_ext J _ _ ((presheafToSheaf J (Type u)).obj Tg).property
    rw [← toSheafify_naturality, ← Category.assoc, toSheafify_sheafifyLift]
  · exact (toSheafify_naturality J h).symm

end Sheafify

end Orbit

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {ι : Type v} {X : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
variable (f : ∀ i, X i ⟶ T)

variable (hT : IsAlgebraicSpace B S hS T) (hX : ∀ i, IsAlgebraicSpace B S hS (X i))

/-! ### Essential surjectivity: the quotient sheaf of a descent datum -/

section EssSurj

attribute [local instance] AlgebraicGeometry.BigFppfOver.hasSheafify_type

variable (D : DescentData f hT hX)

/-- The orbit presheaf of the move operation of a descent datum, as a space over `T`: the
coequalizer of the two maps from the pairwise overlaps `V i ×_T X j` to the disjoint union of
the components `V i`. -/
public abbrev descentOrbit : Over T := Orbit.orbitOver D.transport

/-- **The quotient sheaf of a descent datum**, as a space over `T`: the fppf sheafification of
the coequalizer `descentOrbit` of the two maps from the pairwise overlaps to the disjoint
union of the components. -/
public def descentQuotientObj : Over T :=
  Over.mk (sheafifyLift (BigFppfOver.topology B S hS) (descentOrbit f hT hX D).hom hT.isSheaf)

/-- The quotient sheaf of a descent datum is a sheaf. -/
public lemma isSheaf_descentQuotientObj :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (descentQuotientObj f hT hX D).left :=
  ((presheafToSheaf (BigFppfOver.topology B S hS) (Type u)).obj
    (descentOrbit f hT hX D).left).property

/-- The canonical map from the `i`-th component of a descent datum to its quotient sheaf. -/
public def toDescentQuotient (i : ι) :
    (D.obj i).left ⟶ (descentQuotientObj f hT hX D).left :=
  (Orbit.toOrbitOver D.transport i).left ≫
    toSheafify (BigFppfOver.topology B S hS) (descentOrbit f hT hX D).left

/-- **The `i`-th component of a descent datum is the fibre product `X i ×_T F` of its quotient
sheaf `F` with the `i`-th member of the family.** The three other corners of the square are
already sheaves, so sheafifying the corresponding square for the coequalizer leaves it
cartesian. -/
public theorem isPullback_toDescentQuotient (i : ι) :
    IsPullback (toDescentQuotient f hT hX D i) (D.obj i).hom
      (descentQuotientObj f hT hX D).hom (f i) :=
  Orbit.isPullback_sheafify _
    (Over.isPullback_of_binaryFan_isLimit _ (Orbit.orbitOverProductIsLimit D.transport i))
    (D.obj_isAlgebraicSpace i).isSheaf (hX i).isSheaf hT.isSheaf

/-- **The quotient sheaf of a descent datum**, as an object of the source category of
`AlgebraicGeometry.Space.Descent.fibreDescentFunctor`: a sheaf over `T` whose fibre products
with the members of the family are the components of the datum, hence algebraic spaces. -/
public def descentQuotient : SheavesWithSpaceFibres f :=
  ⟨descentQuotientObj f hT hX D, isSheaf_descentQuotientObj f hT hX D,
    fun i ↦ (D.obj_isAlgebraicSpace i).of_iso
      (isPullback_toDescentQuotient f hT hX D i).isoPullback⟩

/-- The identification of the `i`-th component of a descent datum with the `i`-th fibre
product of its quotient sheaf, as spaces over `X i`. -/
public def descentQuotientComponentIso (i : ι) :
    D.obj i ≅ fibreComponent f (descentQuotient f hT hX D).obj i :=
  Over.isoMk (isPullback_toDescentQuotient f hT hX D i).isoPullback
    (isPullback_toDescentQuotient f hT hX D i).isoPullback_hom_snd

/-- The identification of components carries the projection to the quotient sheaf to the
canonical map. -/
private lemma descentQuotientComponentIso_hom_left_fst (i : ι) :
    (descentQuotientComponentIso f hT hX D i).hom.left ≫
        pullback.fst (descentQuotient f hT hX D).obj.hom (f i) =
      toDescentQuotient f hT hX D i :=
  (isPullback_toDescentQuotient f hT hX D i).isoPullback_hom_fst

/-- **The canonical maps to the quotient sheaf identify a point of one component with every
point it moves to.** This is the relation the quotient divides by, after sheafification. -/
public lemma toDescentQuotient_move {i j : ι} {Z : Over T}
    (v : Z ⟶ (Over.map (f i)).obj (D.obj i)) (y : Z ⟶ Over.mk (f j)) :
    (D.transport.move v y).left ≫ toDescentQuotient f hT hX D j =
      Over.Hom.left v ≫ toDescentQuotient f hT hX D i := by
  have key : Over.Hom.left v ≫ (Orbit.toOrbitOver D.transport i).left =
      (D.transport.move v y).left ≫ (Orbit.toOrbitOver D.transport j).left :=
    congrArg Over.Hom.left (Orbit.toOrbitOver_move D.transport v y)
  change (D.transport.move v y).left ≫ (Orbit.toOrbitOver D.transport j).left ≫
      toSheafify (BigFppfOver.topology B S hS) (descentOrbit f hT hX D).left =
    Over.Hom.left v ≫ (Orbit.toOrbitOver D.transport i).left ≫
      toSheafify (BigFppfOver.topology B S hS) (descentOrbit f hT hX D).left
  rw [← Category.assoc, ← Category.assoc, key]

/-- The identifications of components carry the move operation of the datum to the move
operation of the fibre products of the quotient sheaf. -/
private lemma descentQuotient_fibreMove_eq {i j : ι} {Z : Over T}
    (v : Z ⟶ (Over.map (f i)).obj (D.obj i)) (y : Z ⟶ Over.mk (f j)) :
    D.transport.move v y ≫
        (Over.map (f j)).map (descentQuotientComponentIso f hT hX D j).hom =
      fibreMove f (descentQuotient f hT hX D).obj
        (v ≫ (Over.map (f i)).map (descentQuotientComponentIso f hT hX D i).hom) y := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [fibreMove_left_fst]
    simp only [Over.comp_left, Over.map_map_left, Category.assoc,
      descentQuotientComponentIso_hom_left_fst]
    exact toDescentQuotient_move f hT hX D v y
  · rw [fibreMove_left_snd]
    have hw : (descentQuotientComponentIso f hT hX D j).hom.left ≫
        pullback.snd (descentQuotient f hT hX D).obj.hom (f j) = (D.obj j).hom :=
      Over.w (descentQuotientComponentIso f hT hX D j).hom
    simp only [Over.comp_left, Over.map_map_left, Category.assoc, hw]
    exact congrArg Over.Hom.left (D.transport.move_base v y)

/-- The identifications of components commute with the two move operations: the quotient
sheaf's move operation is the datum's, read through the fibre products. -/
public lemma descentQuotientComponentIso_move {i j : ι} {Z : Over T}
    (v : Z ⟶ (Over.map (f i)).obj (D.obj i)) (y : Z ⟶ Over.mk (f j)) :
    D.transport.move v y ≫
        (Over.map (f j)).map (descentQuotientComponentIso f hT hX D j).hom =
      (fibreDescentData f hT hX (descentQuotient f hT hX D)).transport.move
        (v ≫ (Over.map (f i)).map (descentQuotientComponentIso f hT hX D i).hom) y :=
  (descentQuotient_fibreMove_eq f hT hX D v y).trans <| Eq.symm <|
    (DescentData.transport_move _ _ y).trans <| by
      change prod.lift _ y ≫
          ((fibreTransport f (descentQuotient f hT hX D).obj).gluing i j).hom.left ≫ prod.snd =
        (fibreTransport f (descentQuotient f hT hX D).obj).move _ y
      rw [FamilyTransport.gluing_hom, prod.lift_snd, FamilyTransport.comp_move]
      exact congrArg₂ (fun a b => (fibreTransport f (descentQuotient f hT hX D).obj).move a b)
        (prod.lift_fst _ _) (prod.lift_snd _ _)

/-- **The descent datum of the quotient sheaf of a descent datum is that datum.** This is the
identification exhibiting the quotient sheaf as a preimage of the datum under
`AlgebraicGeometry.Space.Descent.fibreDescentFunctor`. -/
public def descentQuotientIso :
    D ≅ fibreDescentData f hT hX (descentQuotient f hT hX D) :=
  DescentData.isoMk (descentQuotientComponentIso f hT hX D) fun i j ↦
    (DescentData.transport_gluing D i j).symm ▸
      (DescentData.transport_gluing (fibreDescentData f hT hX
        (descentQuotient f hT hX D)) i j).symm ▸
      FamilyTransport.gluing_comm D.transport
        (fibreDescentData f hT hX (descentQuotient f hT hX D)).transport
        (fun k ↦ (Over.map (f k)).map (descentQuotientComponentIso f hT hX D k).hom)
        (fun k ↦ structureMap_naturality (f k)
          (descentQuotientComponentIso f hT hX D k).hom)
        (fun v y ↦ descentQuotientComponentIso_move f hT hX D v y) i j

/-- **Stacks 0ADT, essential surjectivity.** Every descent datum relative to a family of
morphisms of algebraic spaces is the descent datum of a sheaf over the target whose fibre
products with the members of the family are algebraic spaces, namely of the quotient sheaf
`AlgebraicGeometry.Space.Descent.descentQuotient` of the datum. -/
@[stacks 0ADT "ESSENTIAL SURJECTIVITY of fibreDescentFunctor, i.e. the LEFT-TO-RIGHT FUNCTOR \
of the asserted equivalence on objects: every descent datum is the descent datum of a sheaf \
over T whose fibre products with the family are the components of the datum, namely of \
descentQuotient, the fppf sheafification of the presheaf of orbits of local lifts of the \
datum. That presheaf is the object the source builds as the coequalizer of the two maps from \
the pairwise overlaps V i x_T X j to the disjoint union of the components V i; the two maps \
are equalized by toDescentQuotient_move and the components are recovered by \
isPullback_toDescentQuotient. The coequalizer UNIVERSAL PROPERTY is not stated here. Proved \
WITHOUT Stacks 0ADV and without the fppf covering hypothesis -- only that the target and the \
members of the family are algebraic spaces. The equivalence of categories, which needs full \
faithfulness as well, is fibreDescentFunctorEquivalence"]
public instance essSurj_fibreDescentFunctor : (fibreDescentFunctor f hT hX).EssSurj where
  mem_essImage D := ⟨descentQuotient f hT hX D, ⟨(descentQuotientIso f hT hX D).symm⟩⟩

end EssSurj

/-! ### The equivalence of categories -/

section Equivalence

/-- **Stacks 0ADT, the equivalence of categories.** For an fppf covering of algebraic spaces,
the functor from sheaves over the target whose fibre products with the covering are algebraic
spaces to descent data relative to the covering is an equivalence. -/
public lemma isEquivalence_fibreDescentFunctor (hcov : Space.IsFppfCovering B S hS X f) :
    (fibreDescentFunctor f hT hX).IsEquivalence :=
  have := (fibreDescentFunctorFullyFaithful f hT hX hcov).full
  have := (fibreDescentFunctorFullyFaithful f hT hX hcov).faithful
  { }

/-- **Stacks 0ADT, the equivalence of categories.** For an fppf covering `{X i ⟶ T}` of
algebraic spaces, sheaves over `T` whose fibre products with the covering are algebraic spaces
are equivalent to descent data relative to the covering, by
`AlgebraicGeometry.Space.Descent.fibreDescentFunctor`. -/
@[stacks 0ADT "THE EQUIVALENCE OF CATEGORIES ASSERTED BY THE TAG, in full, for an fppf \
covering of algebraic spaces: sheaves over the target whose fibre products with the covering \
are algebraic spaces are equivalent to descent data relative to the covering. The functor is \
fibreDescentFunctor; full faithfulness is fibreDescentFunctorFullyFaithful and essential \
surjectivity is essSurj_fibreDescentFunctor, which sends a datum to descentQuotient. Stacks \
0ADV is neither used nor needed"]
public def fibreDescentFunctorEquivalence (hcov : Space.IsFppfCovering B S hS X f) :
    SheavesWithSpaceFibres f ≌ DescentData f hT hX :=
  haveI := isEquivalence_fibreDescentFunctor f hT hX hcov
  (fibreDescentFunctor f hT hX).asEquivalence

/-- The equivalence of categories is given by
`AlgebraicGeometry.Space.Descent.fibreDescentFunctor`. -/
public lemma fibreDescentFunctorEquivalence_functor
    (hcov : Space.IsFppfCovering B S hS X f) :
    (fibreDescentFunctorEquivalence f hT hX hcov).functor = fibreDescentFunctor f hT hX := rfl

end Equivalence

/-! ### An algebraic space from a descent datum -/

section Construct

attribute [local instance] AlgebraicGeometry.BigFppfOver.hasSheafify_type

/-- The descent datum of the quotient sheaf of an effective descent datum is effective. -/
public lemma isEffective_fibreDescentData_descentQuotient (D : DescentData f hT hX)
    (hD : DescentData.IsEffective D) :
    DescentData.IsEffective (fibreDescentData f hT hX (descentQuotient f hT hX D)) :=
  Functor.essImage.ofIso (descentQuotientIso f hT hX D) hD

/-- **An algebraic space from a descent datum.** For an fppf covering of algebraic spaces, the
quotient sheaf of an effective descent datum is an algebraic space, and the `i`-th component
of the datum is its fibre product with the `i`-th member of the covering, by
`AlgebraicGeometry.Space.Descent.isPullback_toDescentQuotient`.

The hypotheses are exactly: the family is an fppf covering of algebraic spaces, and the datum
is effective. Effectivity is what Stacks 0ADV would supply unconditionally; this library does
not have 0ADV, but it does prove effectivity outright when one member of the covering is
surjective and étale, in
`AlgebraicGeometry.Space.Descent.isEffective_fibreDescentData_of_isEtale`. -/
public theorem isAlgebraicSpace_descentQuotient (hcov : Space.IsFppfCovering B S hS X f)
    (D : DescentData f hT hX) (hD : DescentData.IsEffective D) :
    IsAlgebraicSpace B S hS (descentQuotient f hT hX D).obj.left :=
  (isAlgebraicSpace_iff_isEffective_fibreDescentData f hT hX hcov
    (descentQuotient f hT hX D)).2
    (isEffective_fibreDescentData_descentQuotient f hT hX D hD)

end Construct

end AlgebraicGeometry.Space.Descent

end
