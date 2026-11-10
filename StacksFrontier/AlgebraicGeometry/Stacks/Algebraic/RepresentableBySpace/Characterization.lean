module

public import Mathlib.CategoryTheory.Groupoid.Discrete
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableBySpace.Basic
public import StacksFrontier.CategoryTheory.FiberedCategory.FiberedInSetoids
public import StacksFrontier.CategoryTheory.FiberedCategory.Strictification
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.DiscretePresheaf
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.OfPresheaf
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.Criterion
public import StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductMorPresheafMap
import StacksCore.Tactic.StacksAttribute

/-!
# Characterizing the categories fibred in groupoids representable by an algebraic space

A category fibred in groupoids over the big fppf site of a scheme is representable by an
algebraic space exactly when its fibres are setoids and its presheaf of isomorphism classes
is an algebraic space.

The proof is the one in the source. In one direction, an equivalence over the site with the
category of elements of an algebraic-space presheaf makes the fibres setoids and identifies
the presheaf of isomorphism classes with that presheaf. In the other, if the fibres are
setoids then choosing a representative in each isomorphism class produces a functor to the
category of elements of the presheaf, which is fully faithful because the fibres are thin and
essentially surjective over the site because every point of the presheaf is hit; so it is an
equivalence over the site.

## Main definitions

* `AlgebraicGeometry.IsAlgebraicSpaceIsoClassPresheaf`: the presheaf of isomorphism classes
  of a category fibred in groupoids is an algebraic space.
* `AlgebraicGeometry.elementsForwardFunctor` and
  `AlgebraicGeometry.equivalenceOver_elements_of_setoids`: the comparison of a category fibred in
  setoids with the category of elements of its presheaf of isomorphism classes, and that
  comparison as an equivalence over the base.

## Main results

* `AlgebraicGeometry.isRepresentableByAlgebraicSpace_iff`: representability by an algebraic
  space is equivalent to the conjunction of the two conditions above.
* `AlgebraicGeometry.exists_equivalenceOver_elements_of_setoids`: the comparison exists, which
  is the form of the previous definition a proof-irrelevant consumer needs.

## Implementation notes

The fibred category may have objects in a universe different from that of the site, so its
presheaf of isomorphism classes is compared with a small algebraic-space presheaf pointwise
and naturally — a family of bijections on the values compatible with restriction along every
morphism of the site — rather than by an equality of presheaves, which would force the two
universes to agree.

## References

* [Stacks Project, Tag 02ZX](https://stacks.math.columbia.edu/tag/02ZX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry

universe u v w z a b

/-- The projection from the category of elements of a set-valued presheaf is fibred in setoids:
it is fibred in groupoids with discrete fibres, so its fibres are thin groupoids. -/
theorem elementsProjection_isFiberedInSetoids
    {C : Type u} [Category.{v} C] (F : Cᵒᵖ ⥤ Type v) :
    (presheafOfCategories (F ⋙ typeToCat)).p.IsFiberedInSetoids := by
  let p := (presheafOfCategories (F ⋙ typeToCat)).p
  let : p.IsFibered := by
    dsimp [p]
    infer_instance
  have hgrp : ∀ U, IsGroupoid (p.Fiber U) := by
    intro U
    change IsGroupoid ((presheafOfGroupoids (F ⋙ typeToGrpd)).p.Fiber U)
    exact isGroupoid_fiber_presheafOfGroupoids (F ⋙ typeToGrpd) U
  have hthin : ∀ U, Quiver.IsThin (p.Fiber U) := by
    intro U
    let PF := (F ⋙ typeToCat).toPseudofunctor'
    let j := Functor.Fiber.inducedFunctor
      (Pseudofunctor.CoGrothendieck.comp_const PF U)
    let e := j.asEquivalence
    intro x y
    refine ⟨fun a b => ?_⟩
    have hdis : Subsingleton (e.symm.functor.obj x ⟶ e.symm.functor.obj y) := by
      change Subsingleton (Discrete.mk _ ⟶ Discrete.mk _)
      infer_instance
    exact (Functor.map_injective e.symm.functor) (hdis.allEq _ _)
  exact ⟨(Functor.IsFiberedInGroupoids.iff_isFibered_and_fiber_isGroupoid).2
      ⟨inferInstance, hgrp⟩, hthin⟩

/-- The class of the source of a strongly cartesian morphism over `f` is the restriction along `f`
of the class of its target. -/
private theorem isoClassMk_eq_map_of_isStronglyCartesian
    {C : Type (u + 1)} [Category.{u} C] {D : Type w} [Category.{v} D]
    {p : D ⥤ C} [p.IsFibered] {V U : C} (f : V ⟶ U) (a : p.Fiber U) (y : p.Fiber V)
    (φ : y.1 ⟶ a.1) (hφ : p.IsStronglyCartesian f φ) :
    Functor.isoClassMk p y = p.isoClassPresheaf.map f.op (Functor.isoClassMk p a) := by
  have : p.IsCartesian f φ := inferInstance
  exact (Functor.isoClassMk_eq_pullbackFiber_of_isCartesian f a y φ hφ.toIsHomLift this).trans
    (Functor.isoClassPresheaf_map_isoClassMk f a).symm

/-- **A morphism of the base is realized by a morphism of a category fibred in setoids as soon as
it is realized on isomorphism classes.** Let `p` be fibred in setoids and let its presheaf of
isomorphism classes be compared pointwise and naturally with a presheaf `F`. If `b` lies over `V`,
`a` lies over `U` and the class of `b` restricts, under the comparison, to the class of `a` along
`f : V ⟶ U`, then `b` admits a morphism to `a` lying over `f`. -/
theorem exists_hom_of_isoClass_compatibility
    {C : Type (u + 1)} [Category.{u} C] {D : Type w} [Category.{v} D]
    (p : D ⥤ C) [hp : p.IsFiberedInSetoids]
    (F : Cᵒᵖ ⥤ Type u)
    (e : ∀ U, p.isoClassPresheaf.obj U ≃ F.obj U)
    (hnat : ∀ ⦃U V⦄ (f : U ⟶ V) (x : p.isoClassPresheaf.obj U),
      e V (p.isoClassPresheaf.map f x) = F.map f (e U x))
    {V U : C} (f : V ⟶ U) (a : p.Fiber U) (b : p.Fiber V)
    (h : e (Opposite.op V) (Functor.isoClassMk p b) =
      F.map f.op (e (Opposite.op U) (Functor.isoClassMk p a))) :
    ∃ g : b.1 ⟶ a.1, p.IsHomLift f g := by
  obtain ⟨y, φ, hφ⟩ := hp.isFiberedInGroupoids.exists_lift f a.1 a.2
  have hy : p.obj y = V := IsHomLift.domain_eq p f φ
  let y' : p.Fiber V := ⟨y, hy⟩
  have hpb := isoClassMk_eq_map_of_isStronglyCartesian f a y' φ
    (hp.isFiberedInGroupoids.isStronglyCartesian_homLift f φ)
  have hclass : Functor.isoClassMk p b = Functor.isoClassMk p y' :=
    (e (Opposite.op V)).injective (by rw [h, hpb, hnat])
  obtain ⟨i⟩ := Functor.exists_iso_of_isoClassMk_eq hclass
  let ψ : b.1 ⟶ y'.1 := Functor.Fiber.fiberInclusion.map i.hom
  have hψ : p.IsHomLift (𝟙 V) ψ := by
    change p.IsHomLift (𝟙 V) i.hom.1
    exact i.hom.2
  refine ⟨ψ ≫ φ, ?_⟩
  simpa using IsHomLift.comp (p := p) (f := 𝟙 V) (g := f) ψ φ

/-- **A morphism of the total category exhibits its source as a pullback on isomorphism classes.**
For `g : x ⟶ y` in a category fibred in groupoids, the class of `x` in the fibre over `p x` is the
restriction along `p g` of the class of `y` in the fibre over `p y`. -/
theorem isoClassMk_eq_map_of_hom
    {C : Type (u + 1)} [Category.{u} C] {D : Type w} [Category.{v} D]
    (p : D ⥤ C) [p.IsFibered] (hp : p.IsFiberedInGroupoids)
    {x y : D} (g : x ⟶ y) :
    Functor.isoClassMk p (⟨x, rfl⟩ : p.Fiber (p.obj x)) =
      p.isoClassPresheaf.map (p.map g).op
        (Functor.isoClassMk p (⟨y, rfl⟩ : p.Fiber (p.obj y))) := by
  exact isoClassMk_eq_map_of_isStronglyCartesian (p.map g) ⟨y, rfl⟩ ⟨x, rfl⟩ g
    (hp.isStronglyCartesian g)

/-- **The comparison functor to a category of elements.** For `p` fibred in groupoids whose
presheaf of isomorphism classes is compared with `F`, this sends an object `x` to the pair
consisting of `p x` and the element of `F(p x)` corresponding to the isomorphism class of `x`, and
a morphism to its image in the base together with the unique morphism of the discrete fibre. -/
def elementsForwardFunctor
    {C : Type (u + 1)} [Category.{u} C] {D : Type w} [Category.{v} D]
    (p : D ⥤ C) [p.IsFibered] (hp : p.IsFiberedInGroupoids)
    (F : Cᵒᵖ ⥤ Type u)
    (e : ∀ U, p.isoClassPresheaf.obj U ≃ F.obj U)
    (hnat : ∀ ⦃U V⦄ (f : U ⟶ V) (x : p.isoClassPresheaf.obj U),
      e V (p.isoClassPresheaf.map f x) = F.map f (e U x)) :
    D ⥤ (presheafOfCategories (F ⋙ typeToCat)).obj := by
  letI : p.IsFibered := hp.isFibered
  let objF : D → (presheafOfCategories (F ⋙ typeToCat)).obj := fun x =>
    ⟨p.obj x, Discrete.mk (e (Opposite.op (p.obj x))
      (Functor.isoClassMk p ⟨x, rfl⟩))⟩
  let mapF : ∀ {x y : D}, (x ⟶ y) → ((objF x) ⟶ (objF y)) := fun {x y} g => by
      have hclass : Functor.isoClassMk p (⟨x, rfl⟩ : p.Fiber (p.obj x)) =
          p.isoClassPresheaf.map (p.map g).op
            (Functor.isoClassMk p (⟨y, rfl⟩ : p.Fiber (p.obj y))) :=
        isoClassMk_eq_map_of_hom p hp g
      have hval : e (Opposite.op (p.obj x))
          (Functor.isoClassMk p (⟨x, rfl⟩ : p.Fiber (p.obj x))) =
          F.map (p.map g).op (e (Opposite.op (p.obj y))
            (Functor.isoClassMk p (⟨y, rfl⟩ : p.Fiber (p.obj y)))) := by
        calc
          _ = e (Opposite.op (p.obj x))
              (p.isoClassPresheaf.map (p.map g).op
                (Functor.isoClassMk p (⟨y, rfl⟩ : p.Fiber (p.obj y)))) :=
                congrArg _ hclass
          _ = _ := hnat (p.map g).op _
      exact (PresheafOfCategories.homEquiv (F ⋙ typeToCat)
        (objF x) (objF y)).symm
        ⟨p.map g, eqToHom (congrArg Discrete.mk hval)⟩
  let L : D ⥤ (presheafOfCategories (F ⋙ typeToCat)).obj := {
    obj := objF
    map := mapF
    map_id := by
      intro x
      change mapF (𝟙 x) = 𝟙 (objF x)
      refine CategoryTheory.Pseudofunctor.CoGrothendieck.Hom.ext _ _ ?_ ?_
      · change p.map (𝟙 x) = 𝟙 (p.obj x)
        simp
      · dsimp [mapF, objF, PresheafOfCategories.homEquiv, typeToCat]
        apply CategoryTheory.Discrete.hom_eq
    map_comp := by
      intro x y z f g
      change mapF (f ≫ g) = mapF f ≫ mapF g
      refine CategoryTheory.Pseudofunctor.CoGrothendieck.Hom.ext _ _ ?_ ?_
      · change p.map (f ≫ g) = p.map f ≫ p.map g
        simp
      · dsimp [mapF, objF, PresheafOfCategories.homEquiv, typeToCat]
        apply CategoryTheory.Discrete.hom_eq
  }
  exact L

/-- `AlgebraicGeometry.elementsForwardFunctor` is a 1-morphism over the base. -/
theorem elementsForwardFunctor_comp
    {C : Type (u + 1)} [Category.{u} C] {D : Type w} [Category.{v} D]
    (p : D ⥤ C) [p.IsFibered] (hp : p.IsFiberedInGroupoids)
    (F : Cᵒᵖ ⥤ Type u)
    (e : ∀ U, p.isoClassPresheaf.obj U ≃ F.obj U)
    (hnat : ∀ ⦃U V⦄ (f : U ⟶ V) (x : p.isoClassPresheaf.obj U),
      e V (p.isoClassPresheaf.map f x) = F.map f (e U x)) :
    elementsForwardFunctor p hp F e hnat ⋙
      (presheafOfCategories (F ⋙ typeToCat)).p = p := by
  apply CategoryTheory.Functor.hext
  · intro x
    rfl
  · intro x y f
    rfl

/-- `AlgebraicGeometry.elementsForwardFunctor` is fully faithful when `p` is fibred in setoids:
faithfulness and fullness both reduce to thinness of the fibres, fullness through
`AlgebraicGeometry.exists_hom_of_isoClass_compatibility`. -/
theorem elementsForwardFunctor_fullyFaithful
    {C : Type (u + 1)} [Category.{u} C] {D : Type w} [Category.{v} D]
    (p : D ⥤ C) [hp : p.IsFiberedInSetoids]
    (F : Cᵒᵖ ⥤ Type u)
    (e : ∀ U, p.isoClassPresheaf.obj U ≃ F.obj U)
    (hnat : ∀ ⦃U V⦄ (f : U ⟶ V) (x : p.isoClassPresheaf.obj U),
      e V (p.isoClassPresheaf.map f x) = F.map f (e U x)) :
    (elementsForwardFunctor p hp.isFiberedInGroupoids F e hnat).Full ∧
      (elementsForwardFunctor p hp.isFiberedInGroupoids F e hnat).Faithful := by
  let L := elementsForwardFunctor p hp.isFiberedInGroupoids F e hnat
  let q := (presheafOfCategories (F ⋙ typeToCat)).p
  let hq : q.IsFiberedInSetoids := elementsProjection_isFiberedInSetoids F
  let := hq
  have hL : L ⋙ q = p := elementsForwardFunctor_comp p hp.isFiberedInGroupoids F e hnat
  have hfull : L.Full := by
    refine ⟨fun {x y} φ => ?_⟩
    let H := PresheafOfCategories.homEquiv (F ⋙ typeToCat) (L.obj x) (L.obj y) φ
    have hval : e (Opposite.op (p.obj x))
        (Functor.isoClassMk p ⟨x, rfl⟩) = F.map H.1.op
          (e (Opposite.op (p.obj y)) (Functor.isoClassMk p ⟨y, rfl⟩)) := H.2.eq
    obtain ⟨g, hg⟩ := exists_hom_of_isoClass_compatibility p F e hnat
      H.1 ⟨y, rfl⟩ ⟨x, rfl⟩ hval
    refine ⟨g, ?_⟩
    have h1 : q.IsHomLift H.1 (L.map g) := Functor.isHomLift_map_of_comp_eq hL H.1 g
    have h2 : q.IsHomLift H.1 φ := by
      have hbase : H.1 = q.map φ := by
        change (PresheafOfCategories.homEquiv (F ⋙ typeToCat) (L.obj x) (L.obj y) φ).1 = _
        rfl
      rw [hbase]
      exact IsHomLift.map (p := q) φ
    exact CategoryTheory.Functor.hom_unique_of_fiber_isThin q H.1
      (hq.fiber_isThin (p.obj x)) (L.map g) φ h1 h2
  have hfaithful : L.Faithful := by
    refine ⟨fun {x y} f g hfg => ?_⟩
    have hpfg : p.map f = p.map g := congrArg q.map hfg
    exact CategoryTheory.Functor.hom_unique_of_fiber_isThin p (p.map f)
      (hp.fiber_isThin (p.obj x)) f g
      (IsHomLift.map (p := p) f) (by rw [hpfg]; exact IsHomLift.map (p := p) g)
  exact ⟨hfull, hfaithful⟩

/-- `AlgebraicGeometry.elementsForwardFunctor` is essentially surjective over the base: every
object of the category of elements is isomorphic, by an isomorphism lying over an identity, to the
image of an object of `D`. -/
theorem elementsForwardFunctor_existsVerticalIso
    {C : Type (u + 1)} [Category.{u} C] {D : Type w} [Category.{v} D]
    (p : D ⥤ C) [hp : p.IsFiberedInSetoids]
    (F : Cᵒᵖ ⥤ Type u)
    (e : ∀ U, p.isoClassPresheaf.obj U ≃ F.obj U)
    (hnat : ∀ ⦃U V⦄ (f : U ⟶ V) (x : p.isoClassPresheaf.obj U),
      e V (p.isoClassPresheaf.map f x) = F.map f (e U x))
    (Y : (presheafOfCategories (F ⋙ typeToCat)).obj) :
    ∃ (x : D) (α : (elementsForwardFunctor p hp.isFiberedInGroupoids F e hnat).obj x ≅ Y),
      (presheafOfCategories (F ⋙ typeToCat)).p.IsHomLift
        (𝟙 ((presheafOfCategories (F ⋙ typeToCat)).p.obj Y)) α.hom := by
  let c : p.isoClassPresheaf.obj (Opposite.op Y.base) := (e (Opposite.op Y.base)).symm Y.fiber.as
  let r : p.Fiber Y.base := Quotient.out c
  let x : D := r.1
  let f : p.obj x ⟶ Y.base := eqToHom r.2
  let y : p.Fiber (p.obj x) := ⟨x, rfl⟩
  have hlift : p.IsHomLift f (𝟙 r.1) := by
    apply IsHomLift.of_fac' p f (𝟙 r.1) rfl r.2
    simp [f]
  have hclass : p.isoClassPresheaf.map f.op c = Functor.isoClassMk p y := by
    rw [show c = Functor.isoClassMk p r from (Quotient.out_eq c).symm]
    exact (isoClassMk_eq_map_of_isStronglyCartesian f r y (𝟙 r.1)
      (hp.isFiberedInGroupoids.isStronglyCartesian_homLift f (𝟙 r.1))).symm
  have hval : e (Opposite.op (p.obj x)) (Functor.isoClassMk p y) =
      F.map f.op Y.fiber.as := by
    calc
      _ = e (Opposite.op (p.obj x)) (p.isoClassPresheaf.map f.op c) := congrArg _ hclass.symm
      _ = F.map f.op (e (Opposite.op Y.base) c) := hnat f.op c
      _ = F.map f.op Y.fiber.as := by simp [c]
  let L := elementsForwardFunctor p hp.isFiberedInGroupoids F e hnat
  let α : L.obj x ⟶ Y := (PresheafOfCategories.homEquiv (F ⋙ typeToCat)
    (L.obj x) Y).symm ⟨f, eqToHom (congrArg Discrete.mk hval)⟩
  let q := (presheafOfCategories (F ⋙ typeToCat)).p
  have hbase : q.map α = f := rfl
  have hα : (presheafOfCategories (F ⋙ typeToCat)).p.IsHomLift (𝟙 Y.base) α := by
    apply IsHomLift.of_fac' q (𝟙 Y.base) α r.2 rfl
    change q.map α = eqToHom r.2 ≫ 𝟙 Y.base ≫ eqToHom (rfl : Y.base = Y.base)
    simpa [f] using hbase
  let hq : q.IsFiberedInSetoids := elementsProjection_isFiberedInSetoids F
  let := hq
  have hqg : q.IsFiberedInGroupoids := hq.isFiberedInGroupoids
  have : q.IsHomLift (𝟙 (q.obj Y)) α := hα
  have hsc := hqg.isStronglyCartesian_homLift (𝟙 (q.obj Y)) α
  have : IsIso α := Functor.IsStronglyCartesian.isIso_of_base_isIso q (𝟙 (q.obj Y)) α
  exact ⟨x, asIso α, hα⟩

/-- An equivalence of fibred categories over the base, unbundled as in
`CategoryTheory.Functor.IsFibredEquivalenceOver`, packaged as a
`StacksRepresentableCFG.EquivalenceOver`. -/
noncomputable def equivalenceOver_of_isFibredEquivalenceOver
    {C : Type (u + 1)} [Category.{u} C] {D : Type v} [Category.{w} D]
    {E : Type z} [Category.{a} E]
    {p : D ⥤ C} {q : E ⥤ C} {G : D ⥤ E}
    (h : Functor.IsFibredEquivalenceOver p q G) : StacksRepresentableCFG.EquivalenceOver p q := by
  classical
  let H := Classical.choose h.exists_inverse
  have hpack₁ := Classical.choose_spec h.exists_inverse
  let hH : Functor.IsFibredOneMorphism q p H := Classical.choose hpack₁
  have hpack₂ := Classical.choose_spec hpack₁
  let η := Classical.choose hpack₂
  have hpack₃ := Classical.choose_spec hpack₂
  let hη : ∀ x : D, p.IsHomLift (𝟙 (p.obj x)) (η.hom.app x) := Classical.choose hpack₃
  have hpack₄ := Classical.choose_spec hpack₃
  let ε := Classical.choose hpack₄
  have hε : ∀ y : E, q.IsHomLift (𝟙 (q.obj y)) (ε.hom.app y) := Classical.choose_spec hpack₄
  refine ⟨⟨G, h.isFibredOneMorphism.comp_eq⟩, ⟨H, hH.comp_eq⟩, η, ε, ?_, ?_⟩
  · ext x
    simp only [Functor.whiskerRight_app, eqToHom_app]
    have : p.IsHomLift (𝟙 (p.obj x)) (η.hom.app x) := hη x
    rw [IsHomLift.fac' p (𝟙 (p.obj x)) (η.hom.app x)]
    simp
  · ext y
    simp only [Functor.whiskerRight_app, eqToHom_app]
    have : q.IsHomLift (𝟙 (q.obj y)) (ε.hom.app y) := hε y
    rw [IsHomLift.fac' q (𝟙 (q.obj y)) (ε.hom.app y)]
    simp

/-- **A category fibred in setoids is the category of elements of its presheaf of isomorphism
classes.** Given a pointwise and natural comparison `e` of the presheaf of isomorphism classes of
`p` with a presheaf `F` of sets, this is the equivalence over the base between `p` and the category
of elements of `F`, with `AlgebraicGeometry.elementsForwardFunctor` as its forward 1-morphism.

A consumer that has to compute with the forward 1-morphism — to say which element of `F` an
object is sent to — needs the equivalence as data, which is why this is a `def` and
`AlgebraicGeometry.exists_equivalenceOver_elements_of_setoids` is derived from it rather than
the other way round; `AlgebraicGeometry.equivalenceOverElementsOfSetoids_hom_obj` is that
computation.

The total category of `p` may live in any universe; only `F` is constrained to take values in the
morphism universe of the base. -/
noncomputable def equivalenceOver_elements_of_setoids
    {C : Type (u + 1)} [Category.{u} C] {D : Type v} [Category.{w} D]
    (p : D ⥤ C) [hp : p.IsFiberedInSetoids]
    (F : Cᵒᵖ ⥤ Type u)
    (e : ∀ U, p.isoClassPresheaf.obj U ≃ F.obj U)
    (hnat : ∀ ⦃U V⦄ (f : U ⟶ V) (x : p.isoClassPresheaf.obj U),
      e V (p.isoClassPresheaf.map f x) = F.map f (e U x)) :
    StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p :=
  letI q := (presheafOfCategories (F ⋙ typeToCat)).p
  letI G := elementsForwardFunctor p hp.isFiberedInGroupoids F e hnat
  letI hcomp : G ⋙ q = p := elementsForwardFunctor_comp p hp.isFiberedInGroupoids F e hnat
  letI : G.Full := (elementsForwardFunctor_fullyFaithful p F e hnat).1
  letI : G.Faithful := (elementsForwardFunctor_fullyFaithful p F e hnat).2
  equivalenceOver_of_isFibredEquivalenceOver
    (hcomp ▸ Functor.isFibredEquivalenceOver_of_fullyFaithful G
      (elementsForwardFunctor_existsVerticalIso p F e hnat) :
      Functor.IsFibredEquivalenceOver p q G)

/-- `AlgebraicGeometry.equivalenceOver_elements_of_setoids` under the spelling the naming
convention for a definition asks for. -/
noncomputable def equivalenceOverElementsOfSetoids
    {C : Type (u + 1)} [Category.{u} C] {D : Type v} [Category.{w} D]
    (p : D ⥤ C) [p.IsFiberedInSetoids]
    (F : Cᵒᵖ ⥤ Type u)
    (e : ∀ U, p.isoClassPresheaf.obj U ≃ F.obj U)
    (hnat : ∀ ⦃U V⦄ (f : U ⟶ V) (x : p.isoClassPresheaf.obj U),
      e V (p.isoClassPresheaf.map f x) = F.map f (e U x)) :
    StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p :=
  equivalenceOver_elements_of_setoids p F e hnat

/-- The forward 1-morphism of `AlgebraicGeometry.equivalenceOverElementsOfSetoids` sends an object
`x` to the pair consisting of `p x` and the element of `F(p x)` named by the isomorphism class
of `x`. -/
theorem equivalenceOverElementsOfSetoids_hom_obj
    {C : Type (u + 1)} [Category.{u} C] {D : Type v} [Category.{w} D]
    (p : D ⥤ C) [hp : p.IsFiberedInSetoids]
    (F : Cᵒᵖ ⥤ Type u)
    (e : ∀ U, p.isoClassPresheaf.obj U ≃ F.obj U)
    (hnat : ∀ ⦃U V⦄ (f : U ⟶ V) (x : p.isoClassPresheaf.obj U),
      e V (p.isoClassPresheaf.map f x) = F.map f (e U x))
    (x : D) :
    letI : p.IsFibered := hp.isFiberedInGroupoids.isFibered
    (equivalenceOverElementsOfSetoids p F e hnat).hom.functor.obj x =
      ⟨p.obj x, Discrete.mk (e (Opposite.op (p.obj x))
        (Functor.isoClassMk p ⟨x, rfl⟩))⟩ :=
  rfl

/-- A category fibred in setoids whose presheaf of isomorphism classes is identified with a
small presheaf `F` is equivalent over the base to the category of elements of `F`. -/
theorem exists_equivalenceOver_elements_of_setoids
    {C : Type (u + 1)} [Category.{u} C] {D : Type v} [Category.{w} D]
    (p : D ⥤ C) [hp : p.IsFiberedInSetoids]
    (F : Cᵒᵖ ⥤ Type u)
    (e : ∀ U, p.isoClassPresheaf.obj U ≃ F.obj U)
    (hnat : ∀ ⦃U V⦄ (f : U ⟶ V) (x : p.isoClassPresheaf.obj U),
      e V (p.isoClassPresheaf.map f x) = F.map f (e U x)) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) :=
  ⟨equivalenceOver_elements_of_setoids p F e hnat⟩

private noncomputable def elementsProjection_fiberEquivalence
    {C : Type (u + 1)} [Category.{u} C] (F : Cᵒᵖ ⥤ Type u) (U : C) :
    ((presheafOfCategories (F ⋙ typeToCat)).p.Fiber U) ≌ Discrete (F.obj (Opposite.op U)) := by
  let PF := (F ⋙ typeToCat).toPseudofunctor'
  let j := Functor.Fiber.inducedFunctor (Pseudofunctor.CoGrothendieck.comp_const PF U)
  letI : j.IsEquivalence := inferInstance
  exact j.asEquivalence.symm

private noncomputable def elementsIsoClassEquiv
    {C : Type (u + 1)} [Category.{u} C] (F : Cᵒᵖ ⥤ Type u) (U : C) :
    ((presheafOfCategories (F ⋙ typeToCat)).p.isoClassPresheaf.obj (Opposite.op U)) ≃
      F.obj (Opposite.op U) := by
  let e := elementsProjection_fiberEquivalence F U
  let j := e.functor
  refine
    { toFun := Quotient.lift (fun x => (j.obj x).as) (fun a b hab => ?_)
      invFun := fun y => Quotient.mk _ (e.symm.functor.obj (Discrete.mk y))
      left_inv := ?_
      right_inv := ?_ }
  · obtain ⟨i⟩ := (Functor.isIsomorphicSetoid_r_iff a b).1 hab
    exact congrArg Discrete.as (obj_ext_of_isDiscrete (j.map i.hom))
  · intro c
    induction c using Quotient.ind with
    | _ a =>
      apply Quotient.sound
      change Nonempty (e.symm.functor.obj (j.obj a) ≅ a)
      exact ⟨by simpa [e, j, Functor.comp_obj] using (e.unitIso.app a).symm⟩
  · intro y
    exact congrArg Discrete.as (obj_ext_of_isDiscrete (e.counitIso.hom.app (Discrete.mk y)))

private theorem elementsIsoClassEquiv_naturality
    {C : Type (u + 1)} [Category.{u} C] (F : Cᵒᵖ ⥤ Type u)
    {U V : C} (f : V ⟶ U)
    (c : (presheafOfCategories (F ⋙ typeToCat)).p.isoClassPresheaf.obj (Opposite.op U)) :
    elementsIsoClassEquiv F V
        ((presheafOfCategories (F ⋙ typeToCat)).p.isoClassPresheaf.map f.op c) =
      F.map f.op (elementsIsoClassEquiv F U c) := by
  let q := (presheafOfCategories (F ⋙ typeToCat)).p
  let eU := elementsProjection_fiberEquivalence F U
  let eV := elementsProjection_fiberEquivalence F V
  induction c using Quotient.ind with
  | _ x =>
    let z := eU.symm.functor.obj (Discrete.mk (elementsIsoClassEquiv F U (Functor.isoClassMk q x)))
    have hxz : Functor.isoClassMk q x = Functor.isoClassMk q z :=
      Functor.isoClassMk_eq_of_iso (eU.unitIso.app x)
    have hrestr := congrArg (q.isoClassPresheaf.map f.op) hxz.symm
    let v := F.map f.op (elementsIsoClassEquiv F U (Functor.isoClassMk q x))
    let z' := eV.symm.functor.obj (Discrete.mk v)
    let P := (F ⋙ typeToCat).toPseudofunctor'
    let lift := Pseudofunctor.CoGrothendieck.cartesianLift (F := P)
      (Discrete.mk (elementsIsoClassEquiv F U (Functor.isoClassMk q x))) f
    have hcart : q.IsStronglyCartesian f lift :=
      Pseudofunctor.CoGrothendieck.isStronglyCartesian_homCartesianLift (F := P)
        (Discrete.mk (elementsIsoClassEquiv F U (Functor.isoClassMk q x))) f
    have hclass : Functor.isoClassMk q z' = q.isoClassPresheaf.map f.op (Functor.isoClassMk q x) :=
      (isoClassMk_eq_map_of_isStronglyCartesian f z z' lift hcart).trans hrestr
    exact (congrArg (elementsIsoClassEquiv F V) hclass.symm).trans
      ((elementsIsoClassEquiv F V).right_inv v)

private def fiberFunctorOfCompEq
    {C : Type (u + 1)} [Category.{u} C] {D : Type v} [Category.{w} D]
    {E : Type z} [Category.{a} E] {p : D ⥤ C} {q : E ⥤ C}
    (G : D ⥤ E) (hG : G ⋙ q = p) (U : C) : p.Fiber U ⥤ q.Fiber U where
  obj x := ⟨G.obj x.1, by
    have h := congrArg (fun H : D ⥤ C => H.obj x.1) hG
    simpa [Functor.comp_obj] using h.trans x.2⟩
  map {x y} f := ⟨G.map f.1, by
    have : p.IsHomLift (𝟙 U) f.1 := f.2
    exact Functor.isHomLift_map_of_comp_eq hG (𝟙 U) f.1⟩
  map_id x := by
    apply Functor.Fiber.hom_ext
    change G.map (𝟙 x.1) = 𝟙 (G.obj x.1)
    simp
  map_comp f g := by
    apply Functor.Fiber.hom_ext
    change G.map (f.1 ≫ g.1) = G.map f.1 ≫ G.map g.1
    simp

private noncomputable def isoClassMapOnFibers
    {C : Type (u + 1)} [Category.{u} C] {D : Type v} [Category.{w} D]
    {E : Type z} [Category.{a} E] {p : D ⥤ C} {q : E ⥤ C}
    [_hp : p.IsFiberedInSetoids] [hq : q.IsFiberedInSetoids]
    (G : D ⥤ E) (hG : G ⋙ q = p) (U : C) :
    p.isoClassPresheaf.obj (Opposite.op U) → q.isoClassPresheaf.obj (Opposite.op U) :=
  Quotient.lift (fun x => Functor.isoClassMk q ((fiberFunctorOfCompEq G hG U).obj x))
    (by
      intro x y h
      obtain ⟨i⟩ := (Functor.isIsomorphicSetoid_r_iff x y).1 h
      exact Quotient.sound ((Functor.isIsomorphicSetoid_r_iff _ _).2
        ⟨(fiberFunctorOfCompEq G hG U).mapIso i⟩))

private theorem isoClassMapOnFibers_naturality
    {C : Type (u + 1)} [Category.{u} C] {D : Type v} [Category.{w} D]
    {E : Type z} [Category.{a} E] {p : D ⥤ C} {q : E ⥤ C}
    [hp : p.IsFiberedInSetoids] [hq : q.IsFiberedInSetoids]
    (G : D ⥤ E) (hG : G ⋙ q = p) {U V : C} (f : V ⟶ U)
    (x : p.Fiber U) :
    isoClassMapOnFibers G hG V (p.isoClassPresheaf.map f.op
        (Functor.isoClassMk p x)) =
      q.isoClassPresheaf.map f.op
        (isoClassMapOnFibers G hG U (Functor.isoClassMk p x)) := by
  let a := Functor.pullbackFiber p x f
  let φ := Functor.IsPreFibered.pullbackMap x.2 f
  have : p.IsHomLift f φ := by infer_instance
  have hGφ : q.IsHomLift f (G.map φ) := Functor.isHomLift_map_of_comp_eq hG f φ
  exact isoClassMk_eq_map_of_isStronglyCartesian f ((fiberFunctorOfCompEq G hG U).obj x)
    ((fiberFunctorOfCompEq G hG V).obj a) (G.map φ)
    (hq.isFiberedInGroupoids.isStronglyCartesian_homLift f (G.map φ))

private theorem homLift_id_reindex
    {C : Type (u + 1)} [Category.{u} C] {D : Type v} [Category.{w} D]
    {p : D ⥤ C} {R U : C} (hRU : R = U) {x y : D}
    (φ : x ⟶ y) (hφ : p.IsHomLift (𝟙 R) φ) : p.IsHomLift (𝟙 U) φ := by
  subst R
  exact hφ

private noncomputable def isoClassEquivOfEquivalenceOver
    {C : Type (u + 1)} [Category.{u} C] {D : Type v} [Category.{w} D]
    {E : Type z} [Category.{a} E] {p : D ⥤ C} {q : E ⥤ C}
    [hp : p.IsFiberedInSetoids] [hq : q.IsFiberedInSetoids]
    (e : StacksRepresentableCFG.EquivalenceOver p q) (U : C) :
    p.isoClassPresheaf.obj (Opposite.op U) ≃ q.isoClassPresheaf.obj (Opposite.op U) where
  toFun := isoClassMapOnFibers e.hom.functor e.hom.w U
  invFun := isoClassMapOnFibers e.inv.functor e.inv.w U
  left_inv := by
    intro c
    induction c using Quotient.ind with
    | _ x =>
      change Functor.isoClassMk p
          ((fiberFunctorOfCompEq e.inv.functor e.inv.w U).obj
            ((fiberFunctorOfCompEq e.hom.functor e.hom.w U).obj x)) =
        Functor.isoClassMk p x
      have hvert := homLift_id_reindex x.2 (e.unitIso.hom.app x.1)
        (e.isHomLift_unitIso_hom_app x.1)
      exact (Functor.isoClassMk_eq_of_iso
        (Functor.Fiber.isoMk (e.unitIso.app x.1) hvert)).symm
  right_inv := by
    intro c
    induction c using Quotient.ind with
    | _ y =>
      change Functor.isoClassMk q
          ((fiberFunctorOfCompEq e.hom.functor e.hom.w U).obj
            ((fiberFunctorOfCompEq e.inv.functor e.inv.w U).obj y)) =
        Functor.isoClassMk q y
      have hvert := homLift_id_reindex y.2 (e.counitIso.hom.app y.1)
        (e.isHomLift_counitIso_hom_app y.1)
      exact Functor.isoClassMk_eq_of_iso
        (Functor.Fiber.isoMk (e.counitIso.app y.1) hvert)

private theorem isoClassEquivOfEquivalenceOver_naturality
    {C : Type (u + 1)} [Category.{u} C] {D : Type v} [Category.{w} D]
    {E : Type z} [Category.{a} E] {p : D ⥤ C} {q : E ⥤ C}
    [hp : p.IsFiberedInSetoids] [hq : q.IsFiberedInSetoids]
    (e : StacksRepresentableCFG.EquivalenceOver p q) {U V : C} (f : V ⟶ U)
    (c : p.isoClassPresheaf.obj (Opposite.op U)) :
    isoClassEquivOfEquivalenceOver e V (p.isoClassPresheaf.map f.op c) =
      q.isoClassPresheaf.map f.op (isoClassEquivOfEquivalenceOver e U c) := by
  induction c using Quotient.ind with
  | _ x =>
    change isoClassMapOnFibers e.hom.functor e.hom.w V
        (p.isoClassPresheaf.map f.op (Functor.isoClassMk p x)) =
      q.isoClassPresheaf.map f.op
        (isoClassMapOnFibers e.hom.functor e.hom.w U (Functor.isoClassMk p x))
    exact isoClassMapOnFibers_naturality e.hom.functor e.hom.w f x

/-- The presheaf of isomorphism classes of a category fibred in groupoids is
an algebraic space when it is naturally equivalent to an algebraic-space
presheaf of sets on the same site. -/
public def IsAlgebraicSpaceIsoClassPresheaf
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (AlgebraicGeometry.BigFppfOver B S hS)) : Prop :=
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  ∃ F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u,
    AlgebraicGeometry.IsAlgebraicSpace B S hS F ∧
      ∃ e : ∀ U, (𝒳.val.p.isoClassPresheaf.obj U) ≃ F.obj U,
        ∀ ⦃U V⦄ (f : U ⟶ V) (x : 𝒳.val.p.isoClassPresheaf.obj U),
          e V (𝒳.val.p.isoClassPresheaf.map f x) = F.map f (e U x)

/-- **Stacks 02ZX.** A category fibred in groupoids over the big fppf site
is represented by an algebraic space precisely when its fibres are setoids
and its presheaf of isomorphism classes is an algebraic space. -/
@[stacks 02ZX]
public theorem isRepresentableByAlgebraicSpace_iff
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (AlgebraicGeometry.BigFppfOver B S hS)) :
    AlgebraicGeometry.IsRepresentableByAlgebraicSpace B S hS 𝒳 ↔
      (𝒳.val.p.IsFiberedInSetoids ∧ IsAlgebraicSpaceIsoClassPresheaf B S hS 𝒳) := by
  constructor
  · rintro ⟨F, hF, ⟨e⟩⟩
    let q := (presheafOfCategories (F ⋙ typeToCat)).p
    let hq : q.IsFiberedInSetoids := elementsProjection_isFiberedInSetoids F
    have hp : 𝒳.val.p.IsFiberedInSetoids :=
      StacksRepresentableCFG.isFiberedInSetoids_of_equivalenceOver e hq
    let eclass : ∀ U : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ,
        (𝒳.val.p.isoClassPresheaf.obj U) ≃ F.obj U := fun U =>
      (isoClassEquivOfEquivalenceOver e U.unop).trans (elementsIsoClassEquiv F U.unop)
    refine ⟨hp, F, hF, eclass, ?_⟩
    intro U V f c
    change elementsIsoClassEquiv F V.unop
        (isoClassEquivOfEquivalenceOver e V.unop
          (𝒳.val.p.isoClassPresheaf.map f c)) =
      F.map f (elementsIsoClassEquiv F U.unop
        (isoClassEquivOfEquivalenceOver e U.unop c))
    calc
      _ = elementsIsoClassEquiv F V.unop
          (q.isoClassPresheaf.map f (isoClassEquivOfEquivalenceOver e U.unop c)) :=
        congrArg (elementsIsoClassEquiv F V.unop)
          (isoClassEquivOfEquivalenceOver_naturality e f.unop c)
      _ = _ := elementsIsoClassEquiv_naturality F f.unop
        (isoClassEquivOfEquivalenceOver e U.unop c)
  · rintro ⟨hset, F, hF, e, hnat⟩
    exact ⟨F, hF, exists_equivalenceOver_elements_of_setoids 𝒳.val.p F e hnat⟩

end AlgebraicGeometry

end
