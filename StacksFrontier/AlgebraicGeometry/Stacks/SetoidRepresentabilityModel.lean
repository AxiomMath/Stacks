module

public import StacksFrontier.AlgebraicGeometry.Stacks.IsoClassPresheafUniverseModel
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafRelativeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyEquivalenceIff
public import StacksFrontier.AlgebraicGeometry.Stacks.SetoidRepresentability
import all StacksFrontier.AlgebraicGeometry.Stacks.SetoidRepresentability

/-!
# Representability through presheaves of isomorphism classes, at any universe of total objects

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in setoids over the big fppf site of `S`,
and let `a : F ⟶ G` be a map of `Type u`-valued presheaves, naturally identified with the
presheaves of isomorphism classes of `𝒳` and `𝒴`, that is compatible with `f`. Then `a` is
representable by algebraic spaces if and only if `f` is, and then `a` has a property `P` exactly
when `f` has `P` in the relative sense. The universe of the total objects of `𝒳` and `𝒴` is
arbitrary.

## Main definitions

* `AlgebraicGeometry.Stack.isoClassBasedFunctorOfEquiv`: the comparison of a category fibred in
  setoids with the category of elements of a `Type u`-valued presheaf identified with its
  presheaf of isomorphism classes, as a based functor;
* `AlgebraicGeometry.Stack.isoClassComparisonIsoOfEquiv`: the 2-isomorphism comparing `f` with
  the 1-morphism attached to `a`, at an arbitrary universe of total objects;
* `AlgebraicGeometry.Stack.emptyCatFiberedInSetoids`: the empty category fibred in setoids, with
  total objects in `Type u`.

## Main results

* `AlgebraicGeometry.Stack.isoClassMap_isRepresentableByAlgebraicSpaces_iff_of_equiv`: `a` is
  representable by algebraic spaces if and only if `f` is;
* `AlgebraicGeometry.Stack.isoClassMap_isRepresentableByAlgebraicSpaces_iff_model`: the same,
  phrased on the `Type u` model of the presheaf of isomorphism classes;
* `AlgebraicGeometry.Stack.isoClassMap_holdsOnEverySchemePoint_iff_of_equiv` and
  `AlgebraicGeometry.Stack.isoClassMap_holdsOnEverySchemePoint_iff_model`: `a` has a property
  `P` exactly when `f` has `P` in the relative sense, in the same two forms;
* `AlgebraicGeometry.Stack.small_sieve_of_isFiberedInGroupoids`: for an object `x` of a category
  fibred in groupoids `p`, the base objects admitting a morphism to `p x` form a type small in
  the universe of the total objects.

## References

* [Stacks Project, Tag 04SY](https://stacks.math.columbia.edu/tag/04SY)
* [Stacks Project, Tag 02ZX](https://stacks.math.columbia.edu/tag/02ZX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w

/-- Transport of a `Discrete` of a value of a family of types along an equality of base
objects, for an arbitrary assignment `k` of such a value to an object of a fibre. -/
private theorem cast_discreteMk_fiberValue
    {C : Type (u + 1)} [Category.{u} C] {D : Type v} [Category.{w} D]
    (p : D ⥤ C) {H : C → Type u} (k : ∀ U, p.Fiber U → H U)
    {x : D} {U V : C} (h : U = V) (hu : p.obj x = U) (hv : p.obj x = V) :
    cast (congrArg (fun Z => Discrete (H Z)) h) (Discrete.mk (k U ⟨x, hu⟩)) =
      Discrete.mk (k V ⟨x, hv⟩) := by
  cases h
  rfl

section Comparison

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section OneCategory

variable (𝒳 : CatFiberedInSetoids.{u, v, u + 1, w} (BigFppfOver B S hS))
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eX : ∀ U, 𝒳.val.p.isoClassPresheaf.obj U ≃ F.obj U)
  (hnatX : ∀ ⦃U V⦄ (g : U ⟶ V) (z : 𝒳.val.p.isoClassPresheaf.obj U),
    eX V (𝒳.val.p.isoClassPresheaf.map g z) = F.map g (eX U z))

/-- A category fibred in setoids is equivalent over the site to the category of elements of any
`Type u`-valued presheaf identified with its presheaf of isomorphism classes. -/
noncomputable def isoClassEquivalenceOverOfEquiv :
    StacksRepresentableCFG.EquivalenceOver 𝒳.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p :=
  equivalenceOver_elements_of_setoids 𝒳.val.p F eX hnatX

/-- `AlgebraicGeometry.Stack.isoClassEquivalenceOverOfEquiv` read as a based functor into the
category fibred in groupoids attached to the presheaf. -/
noncomputable def isoClassBasedFunctorOfEquiv :
    𝒳.val ⥤ᵇ (fibredCategory B S hS F).val :=
  ⟨(isoClassEquivalenceOverOfEquiv B S hS 𝒳 F eX hnatX).hom.functor,
    (isoClassEquivalenceOverOfEquiv B S hS 𝒳 F eX hnatX).hom.w⟩

/-- `AlgebraicGeometry.Stack.isoClassBasedFunctorOfEquiv` is an equivalence of categories. -/
theorem isEquivalence_isoClassBasedFunctorOfEquiv :
    Functor.IsEquivalence (isoClassBasedFunctorOfEquiv B S hS 𝒳 F eX hnatX).toFunctor :=
  (isoClassEquivalenceOverOfEquiv B S hS 𝒳 F eX hnatX).toEquivalence.isEquivalence_functor

end OneCategory

variable {𝒳 𝒴 : CatFiberedInSetoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
  (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eX : ∀ U, 𝒳.val.p.isoClassPresheaf.obj U ≃ F.obj U)
  (hnatX : ∀ ⦃U V⦄ (g : U ⟶ V) (z : 𝒳.val.p.isoClassPresheaf.obj U),
    eX V (𝒳.val.p.isoClassPresheaf.map g z) = F.map g (eX U z))
  (eY : ∀ U, 𝒴.val.p.isoClassPresheaf.obj U ≃ G.obj U)
  (hnatY : ∀ ⦃U V⦄ (g : U ⟶ V) (z : 𝒴.val.p.isoClassPresheaf.obj U),
    eY V (𝒴.val.p.isoClassPresheaf.map g z) = G.map g (eY U z))
  (a : F ⟶ G)

/-- The compatibility of a map `a : F ⟶ G` of `Type u`-valued presheaves with a 1-morphism `f`
of categories fibred in setoids, across identifications of `F` and `G` with the presheaves of
isomorphism classes: `a` sends the class of `x` to the class of `f x`. -/
abbrev IsoClassCompatible : Prop :=
  ∀ (U : BigFppfOver B S hS) (x : 𝒳.val.p.Fiber U),
    a.app (Opposite.op U) (eX (Opposite.op U) (Functor.isoClassMk 𝒳.val.p x)) =
      eY (Opposite.op U) (Functor.isoClassMk 𝒴.val.p
        ((Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p
          (CatFiberedInGroupoids.homFunctor f)
          (CatFiberedInGroupoids.homFunctor_comp_p f) U).obj x))

/-- The two composites of the square comparing `f` with the 1-morphism attached to `a` agree on
objects. -/
theorem isoClassComparisonOfEquiv_obj_eq
    (ha : IsoClassCompatible B S hS f F G eX eY a) (x : 𝒳.val.obj) :
    (BasedFunctor.comp (isoClassBasedFunctorOfEquiv B S hS 𝒳 F eX hnatX)
        (associatedMap B S hS a).1.hom).obj x =
      (BasedFunctor.comp (CatFiberedInSetoids.inclusion.map f).hom
        (isoClassBasedFunctorOfEquiv B S hS 𝒴 G eY hnatY)).obj x := by
  let pX := 𝒳.val.p
  let pY := 𝒴.val.p
  let eqX := equivalenceOver_elements_of_setoids pX F eX hnatX
  let eqY := equivalenceOver_elements_of_setoids pY G eY hnatY
  let f' := CatFiberedInSetoids.inclusion.map f
  let f'' := (AlgebraicGeometry.Stack.associatedMap B S hS a).1
  let XF := fibredCategory B S hS F
  let YG := fibredCategory B S hS G
  let ax : 𝒳.val ⥤ᵇ XF.val := ⟨eqX.hom.functor, eqX.hom.w⟩
  let bY : 𝒴.val ⥤ᵇ YG.val := ⟨eqY.hom.functor, eqY.hom.w⟩
  let lhs := BasedFunctor.comp ax f''.hom
  let rhs := BasedFunctor.comp f'.hom bY
  have hlbase : (lhs.obj x).base = pX.obj x := BasedFunctor.w_obj lhs x
  have hrbase : (rhs.obj x).base = pX.obj x := BasedFunctor.w_obj rhs x
  apply (PresheafOfCategories.objEquiv (G ⋙ typeToCat)).injective
  apply Sigma.ext
  · exact hlbase.trans hrbase.symm
  · let z := eqX.hom.functor.obj x
    have hzbase : z.base = pX.obj x := by
      show (presheafOfCategories (F ⋙ typeToCat)).p.obj
          (eqX.hom.functor.obj x) = pX.obj x
      exact BasedFunctor.w_obj ax x
    have hzclass : Discrete.as
        (show Discrete (F.obj (Opposite.op z.base)) from z.fiber) =
        eX (Opposite.op z.base) (Functor.isoClassMk pX ⟨x, hzbase.symm⟩) := by
      simp only [z, eqX, equivalenceOver_elements_of_setoids,
        equivalenceOver_of_isFibredEquivalenceOver, elementsForwardFunctor]
      rfl
    let xF : pX.Fiber z.base := ⟨x, hzbase.symm⟩
    let yF := (Functor.Fiber.mapOfComp pX pY
      (CatFiberedInGroupoids.homFunctor f)
      (CatFiberedInGroupoids.homFunctor_comp_p f) z.base).obj xF
    have hassoc : HEq (lhs.obj x).fiber
        (Discrete.mk (a.app (Opposite.op z.base)
          (Discrete.as (show Discrete (F.obj (Opposite.op z.base)) from z.fiber)))) :=
      (AlgebraicGeometry.Stack.associatedMap B S hS a).property z
    have hvalue := ha z.base xF
    have hmid : HEq
        (Discrete.mk (a.app (Opposite.op z.base)
          (Discrete.as (show Discrete (F.obj (Opposite.op z.base)) from z.fiber))))
        (Discrete.mk (eY (Opposite.op z.base) (Functor.isoClassMk pY yF))) := by
      rw [hzclass]
      exact heq_of_eq (congrArg Discrete.mk hvalue)
    let yF' : pY.Fiber z.base :=
      ⟨f'.hom.toFunctor.obj x, (BasedFunctor.w_obj f'.hom x).trans hzbase.symm⟩
    have hyF : yF = yF' := Subtype.ext rfl
    have hrbase' : (rhs.obj x).base = z.base := hrbase.trans hzbase.symm
    have htype : Discrete (G.obj (Opposite.op (rhs.obj x).base)) =
        Discrete (G.obj (Opposite.op z.base)) :=
      congrArg (fun U => Discrete (G.obj (Opposite.op U))) hrbase'
    have hxU : pY.obj (f'.hom.obj x) = (rhs.obj x).base := rfl
    have hxV : pY.obj (f'.hom.obj x) = z.base := yF'.property
    have hrhsfiber : (rhs.obj x).fiber =
        Discrete.mk (eY (Opposite.op (rhs.obj x).base) (Functor.isoClassMk pY
          (⟨f'.hom.obj x, hxU⟩ : pY.Fiber ((rhs.obj x).base)))) := rfl
    have hlast : HEq (Discrete.mk (eY (Opposite.op z.base) (Functor.isoClassMk pY yF)))
        (rhs.obj x).fiber := by
      rw [hyF]
      have hcast : Eq.rec (rhs.obj x).fiber htype =
          Discrete.mk (eY (Opposite.op z.base) (Functor.isoClassMk pY yF')) := by
        have htype' := congrArg
          (fun U => Discrete (G.obj (Opposite.op U))) (hxU.symm.trans hxV)
        rw [hrhsfiber]
        show cast htype (Discrete.mk (eY (Opposite.op (rhs.obj x).base)
            (Functor.isoClassMk pY
              (⟨f'.hom.obj x, hxU⟩ : pY.Fiber ((rhs.obj x).base))))) = _
        calc
          _ = cast htype' (Discrete.mk (eY (Opposite.op (rhs.obj x).base)
              (Functor.isoClassMk pY
                (⟨f'.hom.obj x, hxU⟩ : pY.Fiber ((rhs.obj x).base))))) :=
            cast_type_eq_of_proof_irrel htype htype' _
          _ = Discrete.mk (eY (Opposite.op z.base) (Functor.isoClassMk pY yF')) :=
            cast_discreteMk_fiberValue pY
              (fun U y => eY (Opposite.op U) (Functor.isoClassMk pY y))
              (hxU.symm.trans hxV) hxU hxV
      exact (heq_of_eqRec_eq htype hcast).symm
    exact hassoc.trans (hmid.trans hlast)

/-- The based functors of `AlgebraicGeometry.Stack.isoClassBasedFunctorOfEquiv` carry the
1-morphism `f` of categories fibred in setoids to the 1-morphism attached to the compatible map
`a` of `Type u`-valued presheaves, up to a canonical 2-isomorphism. -/
noncomputable def isoClassComparisonIsoOfEquiv
    (ha : IsoClassCompatible B S hS f F G eX eY a) :
    BasedFunctor.comp (isoClassBasedFunctorOfEquiv B S hS 𝒳 F eX hnatX)
        (associatedMap B S hS a).1.hom ≅
      BasedFunctor.comp (CatFiberedInSetoids.inclusion.map f).hom
        (isoClassBasedFunctorOfEquiv B S hS 𝒴 G eY hnatY) := by
  let lhs := BasedFunctor.comp (isoClassBasedFunctorOfEquiv B S hS 𝒳 F eX hnatX)
    (associatedMap B S hS a).1.hom
  let rhs := BasedFunctor.comp (CatFiberedInSetoids.inclusion.map f).hom
    (isoClassBasedFunctorOfEquiv B S hS 𝒴 G eY hnatY)
  let q := (fibredCategory B S hS G).val.p
  letI : q.IsFiberedInSetoids := elementsProjection_isFiberedInSetoids G
  have hvertical : ∀ x : 𝒳.val.obj,
      q.IsHomLift (𝟙 (𝒳.val.p.obj x))
        (eqToHom (isoClassComparisonOfEquiv_obj_eq B S hS f F G eX hnatX eY hnatY a ha x)) :=
    fun x => based_eqToHom_isHomLift (𝒜 := 𝒳.val)
      (ℬ := (fibredCategory B S hS G).val) lhs rhs x
      (isoClassComparisonOfEquiv_obj_eq B S hS f F G eX hnatX eY hnatY a ha x)
  have niResult :=
    existsUnique_verticalIso_of_forall_exists_verticalHom
      (p := 𝒳.val.p) (q := q) (G := lhs.toFunctor) (H := rhs.toFunctor)
    lhs.w rhs.w
      (fun x => ⟨eqToHom (isoClassComparisonOfEquiv_obj_eq B S hS f F G eX hnatX eY hnatY a ha x),
        hvertical x⟩)
  exact BasedNatIso.mkNatIso niResult.choose niResult.choose_spec.1

include hnatX hnatY in
/-- For a 1-morphism `f` of categories fibred in setoids over the big fppf site of `S`, and a map
`a` of `Type u`-valued presheaves identified with their presheaves of isomorphism classes and
compatible with `f`, representability of `a` by algebraic spaces is equivalent to
representability of `f`. -/
public theorem isoClassMap_isRepresentableByAlgebraicSpaces_iff_of_equiv
    (ha : IsoClassCompatible B S hS f F G eX eY a) :
    AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces B S hS a ↔
      AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpaces B S hS
        (CatFiberedInSetoids.inclusion.map f).hom := by
  have hbridge := @AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_iff_of_equivalences
    B S hS (CatFiberedInSetoids.inclusion.obj 𝒳)
    (fibredCategory B S hS F)
    (CatFiberedInSetoids.inclusion.obj 𝒴)
    (fibredCategory B S hS G)
    (CatFiberedInSetoids.inclusion.map f).hom (associatedMap B S hS a).1.hom
    (isoClassBasedFunctorOfEquiv B S hS 𝒳 F eX hnatX)
    (isoClassBasedFunctorOfEquiv B S hS 𝒴 G eY hnatY)
    (isoClassComparisonIsoOfEquiv B S hS f F G eX hnatX eY hnatY a ha)
    (isEquivalence_isoClassBasedFunctorOfEquiv B S hS 𝒳 F eX hnatX)
    (isEquivalence_isoClassBasedFunctorOfEquiv B S hS 𝒴 G eY hnatY)
  exact (AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_iff_associatedMap
    B S hS a).trans hbridge

include hnatX hnatY in
/-- For a 1-morphism `f` of categories fibred in setoids whose compatible map `a` of
`Type u`-valued presheaves is representable by algebraic spaces, `a` has a property `P`
(`AlgebraicGeometry.Space.HasProperty`) exactly when `f` has `P` in the relative sense
(`AlgebraicGeometry.Stack.HasRelativeProperty`). -/
public theorem isoClassMap_holdsOnEverySchemePoint_iff_of_equiv
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    (ha : IsoClassCompatible B S hS f F G eX eY a)
    (hf : IsRepresentableByAlgebraicSpaces B S hS
      (CatFiberedInSetoids.inclusion.map f).hom) :
    Space.HasProperty B S hS P a
        ((isoClassMap_isRepresentableByAlgebraicSpaces_iff_of_equiv
          B S hS f F G eX hnatX eY hnatY a ha).mpr hf) ↔
      HasRelativeProperty B S hS P (CatFiberedInSetoids.inclusion.map f) hf := by
  have harep := (isoClassMap_isRepresentableByAlgebraicSpaces_iff_of_equiv
    B S hS f F G eX hnatX eY hnatY a ha).mpr hf
  have hassoc := (isRepresentableByAlgebraicSpaces_iff_associatedMap B S hS a).mp harep
  exact (holdsOnEverySchemePoint_iff_hasRelativeProperty B S hS P a harep).trans
    (@hasRelativeProperty_iff_of_equivalences' B S hS
      (CatFiberedInSetoids.inclusion.obj 𝒳) (CatFiberedInSetoids.inclusion.obj 𝒴)
      (fibredCategory B S hS F) (fibredCategory B S hS G) P _ _
      (CatFiberedInSetoids.inclusion.map f) (associatedMap B S hS a).1
      (isoClassBasedFunctorOfEquiv B S hS 𝒳 F eX hnatX)
      (isoClassBasedFunctorOfEquiv B S hS 𝒴 G eY hnatY)
      (isoClassComparisonIsoOfEquiv B S hS f F G eX hnatX eY hnatY a ha)
      (isEquivalence_isoClassBasedFunctorOfEquiv B S hS 𝒳 F eX hnatX)
      (isEquivalence_isoClassBasedFunctorOfEquiv B S hS 𝒴 G eY hnatY)
      hassoc hf)

end Comparison

section Model

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : CatFiberedInSetoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
  [CategoryTheory.FunctorToTypes.Small.{u} 𝒳.val.p.isoClassPresheaf]
  [CategoryTheory.FunctorToTypes.Small.{u} 𝒴.val.p.isoClassPresheaf]

/-- For a 1-morphism `f` of categories fibred in setoids with `u`-small presheaves of isomorphism
classes, a compatible map `a` of the `Type u` models of those presheaves is representable by
algebraic spaces if and only if `f` is. -/
public theorem isoClassMap_isRepresentableByAlgebraicSpaces_iff_model
    (a : CategoryTheory.Functor.isoClassPresheafModel.{u} 𝒳.val.p ⟶
      CategoryTheory.Functor.isoClassPresheafModel.{u} 𝒴.val.p)
    (ha : IsoClassCompatible B S hS f
      (CategoryTheory.Functor.isoClassPresheafModel.{u} 𝒳.val.p)
      (CategoryTheory.Functor.isoClassPresheafModel.{u} 𝒴.val.p)
      (CategoryTheory.Functor.isoClassPresheafModelEquiv.{u} 𝒳.val.p)
      (CategoryTheory.Functor.isoClassPresheafModelEquiv.{u} 𝒴.val.p) a) :
    AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces B S hS a ↔
      AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpaces B S hS
        (CatFiberedInSetoids.inclusion.map f).hom :=
  isoClassMap_isRepresentableByAlgebraicSpaces_iff_of_equiv B S hS f
    (CategoryTheory.Functor.isoClassPresheafModel.{u} 𝒳.val.p)
    (CategoryTheory.Functor.isoClassPresheafModel.{u} 𝒴.val.p)
    (CategoryTheory.Functor.isoClassPresheafModelEquiv.{u} 𝒳.val.p)
    (fun _ _ =>
      CategoryTheory.Functor.isoClassPresheafModelEquiv_naturality.{u} 𝒳.val.p)
    (CategoryTheory.Functor.isoClassPresheafModelEquiv.{u} 𝒴.val.p)
    (fun _ _ =>
      CategoryTheory.Functor.isoClassPresheafModelEquiv_naturality.{u} 𝒴.val.p)
    a ha

/-- For a 1-morphism `f` of categories fibred in setoids with `u`-small presheaves of isomorphism
classes, and a compatible map `a` of their `Type u` models that is representable by algebraic
spaces, `a` has a property `P` exactly when `f` has `P` in the relative sense. -/
public theorem isoClassMap_holdsOnEverySchemePoint_iff_model
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    (a : CategoryTheory.Functor.isoClassPresheafModel.{u} 𝒳.val.p ⟶
      CategoryTheory.Functor.isoClassPresheafModel.{u} 𝒴.val.p)
    (ha : IsoClassCompatible B S hS f
      (CategoryTheory.Functor.isoClassPresheafModel.{u} 𝒳.val.p)
      (CategoryTheory.Functor.isoClassPresheafModel.{u} 𝒴.val.p)
      (CategoryTheory.Functor.isoClassPresheafModelEquiv.{u} 𝒳.val.p)
      (CategoryTheory.Functor.isoClassPresheafModelEquiv.{u} 𝒴.val.p) a)
    (hf : IsRepresentableByAlgebraicSpaces B S hS
      (CatFiberedInSetoids.inclusion.map f).hom) :
    Space.HasProperty B S hS P a
        ((isoClassMap_isRepresentableByAlgebraicSpaces_iff_model B S hS f a ha).mpr hf) ↔
      HasRelativeProperty B S hS P (CatFiberedInSetoids.inclusion.map f) hf :=
  isoClassMap_holdsOnEverySchemePoint_iff_of_equiv B S hS f
    (CategoryTheory.Functor.isoClassPresheafModel.{u} 𝒳.val.p)
    (CategoryTheory.Functor.isoClassPresheafModel.{u} 𝒴.val.p)
    (CategoryTheory.Functor.isoClassPresheafModelEquiv.{u} 𝒳.val.p)
    (fun _ _ =>
      CategoryTheory.Functor.isoClassPresheafModelEquiv_naturality.{u} 𝒳.val.p)
    (CategoryTheory.Functor.isoClassPresheafModelEquiv.{u} 𝒴.val.p)
    (fun _ _ =>
      CategoryTheory.Functor.isoClassPresheafModelEquiv_naturality.{u} 𝒴.val.p)
    a P ha hf

end Model

section Inhabitation

/-! ### Categories fibred in setoids with total objects in `Type u`

The empty category is fibred in setoids with total objects in `Type u`. If a category fibred in
groupoids has an object `x`, the base objects admitting a morphism to `p x` form a type small in
the universe of its total objects. -/

/-- The category structure on an empty type, at an arbitrary universe of morphisms. -/
@[instance_reducible]
def emptyCategory : Category.{w} PEmpty.{u + 1} where
  Hom x _ := PEmpty.elim x
  id x := PEmpty.elim x
  comp {x} := PEmpty.elim x
  id_comp {x} := PEmpty.elim x
  comp_id {x} := PEmpty.elim x
  assoc {x} := PEmpty.elim x

/-- The empty category over a base, as a based category whose total objects lie in `Type u`
whatever the universe of the base. -/
def emptyBasedCategory (𝒞 : Type (u + 1)) [Category.{u} 𝒞] :
    BasedCategory.{w, u} 𝒞 :=
  letI : Category.{w} PEmpty.{u + 1} := emptyCategory.{u, w}
  { obj := PEmpty.{u + 1}
    category := emptyCategory.{u, w}
    p :=
      { obj x := PEmpty.elim x
        map {x} := PEmpty.elim x
        map_id x := PEmpty.elim x
        map_comp {x} := PEmpty.elim x } }

/-- The empty category over a base is fibred in setoids. -/
theorem isFiberedInSetoids_emptyBasedCategory (𝒞 : Type (u + 1)) [Category.{u} 𝒞] :
    (emptyBasedCategory.{u, w} 𝒞).p.IsFiberedInSetoids where
  isFiberedInGroupoids :=
    { exists_lift := fun _ x _ => PEmpty.elim x
      unique_lift := fun {x} => PEmpty.elim x }
  fiber_isThin _ z _ := PEmpty.elim z.1

/-- The empty category fibred in setoids over the big fppf site of `S`, with total objects in
`Type u`. -/
def emptyCatFiberedInSetoids (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    CatFiberedInSetoids.{u, w, u + 1, u} (BigFppfOver B S hS) :=
  CatFiberedInSetoids.mk (emptyBasedCategory.{u, w} _)
    (isFiberedInSetoids_emptyBasedCategory.{u, w} _)

/-- If a category fibred in groupoids `p : D ⥤ C` has an object `x`, then the objects of `C`
admitting a morphism to `p x` form a type small in the universe of the total objects. -/
theorem small_sieve_of_isFiberedInGroupoids {C : Type u} [Category.{v} C] {D : Type w}
    [Category.{v} D] (p : D ⥤ C) (hp : p.IsFiberedInGroupoids) (x : D) :
    Small.{w} {V : C // Nonempty (V ⟶ p.obj x)} := by
  classical
  have key : ∀ V : {V : C // Nonempty (V ⟶ p.obj x)}, ∃ z : D, p.obj z = V.1 := by
    intro V
    obtain ⟨g⟩ := V.2
    obtain ⟨z, φ, hlift⟩ := hp.exists_lift g x rfl
    have := hlift
    exact ⟨z, CategoryTheory.IsHomLift.domain_eq p g φ⟩
  exact small_of_injective (f := fun V => (key V).choose) fun V W h =>
    Subtype.ext ((key V).choose_spec.symm.trans ((congrArg p.obj h).trans (key W).choose_spec))

end Inhabitation

end AlgebraicGeometry.Stack

end
