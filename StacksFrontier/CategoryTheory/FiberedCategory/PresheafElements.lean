module

public import Mathlib.CategoryTheory.Groupoid.Discrete
public import StacksFrontier.CategoryTheory.FiberedCategory.FiberedInSetoids
public import StacksFrontier.CategoryTheory.FiberedCategory.OfPresheaf
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.Criterion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The category of elements of a set-valued presheaf

A presheaf of sets `P` on `C` becomes a presheaf of categories by taking discrete categories
(`CategoryTheory.typeToCat`), and the associated fibred category of Stacks 02XV
(`CategoryTheory.presheafOfCategories`) is its *category of elements*: an object over `U` is an
element of `P(U)`, and there is exactly one morphism over `f : V ⟶ U` from `b ∈ P(V)` to
`a ∈ P(U)` when `b = P(f)(a)` and none otherwise.

Everything here records the two consequences of that description. Each fibre is a discrete
category, so the projection is fibred in setoids; and the fibre over `U` *is* `P(U)`, so for any
category over `C` equivalent to the category of elements, the presheaf of isomorphism classes of
its fibres is `P` — pointwise, and compatibly with restriction.

## Main definitions

* `CategoryTheory.PresheafOfCategories.discreteProjection`: the projection from the category of
  elements of `P` to `C`.
* `CategoryTheory.PresheafOfCategories.discreteFiberEquiv`: its fibre over `U` is `P(U)`.
* `CategoryTheory.PresheafOfCategories.isoClassEquiv`: for `p` equivalent over `C` to the
  projection, the isomorphism classes of the fibre of `p` over `U` are `P(U)`.
* `CategoryTheory.natTransEquivOfPointwiseEquiv`: two presheaves of types identified pointwise
  and compatibly with restriction with two others have the same morphisms, even when the two
  pairs land in different universes.

## Main results

* `CategoryTheory.PresheafOfCategories.isDiscrete_fiber_discreteProjection`: the fibres are
  discrete.
* `CategoryTheory.PresheafOfCategories.isFiberedInSetoids_discreteProjection`: the projection is
  fibred in setoids.
* `CategoryTheory.PresheafOfCategories.isoClassEquiv_naturality`: `isoClassEquiv` is compatible
  with restriction.

## Implementation notes

Discreteness of a fibre is proved by transporting a morphism of the fibre through
`CategoryTheory.PresheafOfCategories.homEquiv`: its first component is the base morphism, forced
to be an identity by `CategoryTheory.IsHomLift.fac'`, and its second lives in a discrete
category, so `CategoryTheory.Discrete.eq_of_hom` both identifies the two endpoints and makes any
two such morphisms equal.

`CategoryTheory.natTransEquivOfPointwiseEquiv` is stated with four presheaves and two families of
bijections rather than with two isomorphisms of presheaves because the presheaf of isomorphism
classes of a fibred category does not land in the universe of the presheaf it is compared with;
the two pairs are therefore not isomorphic as objects of one presheaf category.

## References

* [Stacks Project, Tag 02XV](https://stacks.math.columbia.edu/tag/02XV)
* [Stacks Project, Tag 04SD](https://stacks.math.columbia.edu/tag/04SD)
-/

@[expose] public section

open Opposite

namespace CategoryTheory

universe vC uC uS

/-- Two presheaves of types identified pointwise with two others, compatibly with restriction,
have the same morphisms. The two pairs may land in different universes, which is why the data is
two families of bijections rather than two isomorphisms of presheaves. -/
noncomputable def natTransEquivOfPointwiseEquiv {D : Type uC} [Category.{vC} D]
    (A B : Dᵒᵖ ⥤ Type uS) (X Y : Dᵒᵖ ⥤ Type vC)
    (eA : ∀ U, A.obj U ≃ X.obj U) (eB : ∀ U, B.obj U ≃ Y.obj U)
    (hA : ∀ {U V} (f : U ⟶ V) (a : A.obj U), eA V (A.map f a) = X.map f (eA U a))
    (hB : ∀ {U V} (f : U ⟶ V) (b : B.obj U), eB V (B.map f b) = Y.map f (eB U b)) :
    (A ⟶ B) ≃ (X ⟶ Y) where
  toFun α :=
    { app := fun U => ↾fun a => eB U (α.app U ((eA U).symm a))
      naturality := by
        intro U V f
        ext a
        dsimp
        have harg : (eA V).symm (X.map f a) = A.map f ((eA U).symm a) := by
          apply (eA V).injective
          rw [Equiv.apply_symm_apply]
          simpa using (hA f ((eA U).symm a)).symm
        rw [harg, NatTrans.naturality_apply α f]
        exact hB f (α.app U ((eA U).symm a)) }
  invFun β :=
    { app := fun U => ↾fun a => (eB U).symm (β.app U (eA U a))
      naturality := by
        intro U V f
        ext a
        dsimp
        apply (eB V).injective
        rw [Equiv.apply_symm_apply, hB f, Equiv.apply_symm_apply, hA f a]
        exact NatTrans.naturality_apply β f (eA U a) }
  left_inv α := by ext U a; simp
  right_inv β := by ext U a; simp

namespace PresheafOfCategories

variable {C : Type uC} [Category.{vC} C]

/-- The projection to `C` from the category of elements of a presheaf of sets `P`, i.e. the
structure functor of the fibred category of Stacks 02XV attached to the presheaf of discrete
categories `P ⋙ typeToCat`. -/
@[sga "4 I 8.3.2", sga "6 I 6.6", sga "7 VI 1.1(d)" "partial"]
abbrev discreteProjection (P : Cᵒᵖ ⥤ Type vC) := (presheafOfCategories (P ⋙ typeToCat)).p

/-- A morphism of a fibre of the category of elements has the identity as base component. -/
private theorem base_homEquiv_fiber (P : Cᵒᵖ ⥤ Type vC) {U : C} (a b : Discrete (P.obj (op U)))
    (α : Functor.Fiber.mk (a := ⟨U, a⟩) (p := discreteProjection P) rfl ⟶
      Functor.Fiber.mk (a := ⟨U, b⟩) (p := discreteProjection P) rfl) :
    (homEquiv (P ⋙ typeToCat) ⟨U, a⟩ ⟨U, b⟩ α.1).1 = 𝟙 U :=
  (@IsHomLift.eq_of_isHomLift _ _ _ _ (discreteProjection P) _ _ _ α.1 α.2).symm

/-- Every fibre of the category of elements of a presheaf of sets is a discrete category: a
morphism of the fibre over `U` lies over `𝟙 U`, so its component in the discrete category
`P(U)` identifies its two endpoints and is the only such morphism. -/
@[sga "6 I 6.6" "partial", sga "6 I 8.5" "partial"]
theorem isDiscrete_fiber_discreteProjection (P : Cᵒᵖ ⥤ Type vC) (U : C) :
    IsDiscrete ((discreteProjection P).Fiber U) := by
  constructor
  · intro x y
    refine ⟨fun α β => ?_⟩
    rcases x with ⟨⟨V, a⟩, hx⟩
    rcases y with ⟨⟨W, b⟩, hy⟩
    change V = U at hx
    change W = U at hy
    subst V W
    apply Functor.Fiber.hom_ext
    apply (homEquiv (P ⋙ typeToCat) ⟨U, a⟩ ⟨U, b⟩).injective
    let eα := homEquiv (P ⋙ typeToCat) ⟨U, a⟩ ⟨U, b⟩ α.1
    let eβ := homEquiv (P ⋙ typeToCat) ⟨U, a⟩ ⟨U, b⟩ β.1
    have hαbase : eα.1 = 𝟙 U := base_homEquiv_fiber P a b α
    have hβbase : eβ.1 = 𝟙 U := base_homEquiv_fiber P a b β
    show eα = eβ
    rcases eα with ⟨f, m⟩
    rcases eβ with ⟨g, n⟩
    obtain rfl : f = g := hαbase.trans hβbase.symm
    obtain rfl : m = n := Discrete.hom_eq
    rfl
  · intro x y α
    rcases x with ⟨⟨V, a⟩, hx⟩
    rcases y with ⟨⟨W, b⟩, hy⟩
    change V = U at hx
    change W = U at hy
    subst V W
    have hbase := base_homEquiv_fiber P a b α
    have h := (homEquiv (P ⋙ typeToCat) ⟨U, a⟩ ⟨U, b⟩ α.1).2
    have hab : a = b := by
      rw [hbase] at h
      simp only [op_id, Functor.map_id] at h
      exact congrArg Discrete.mk (Discrete.eq_of_hom h)
    subst b
    rfl

/-- The category of elements of a presheaf of sets is fibred in setoids: it is fibred in
groupoids with discrete, hence thin, fibres. -/
theorem isFiberedInSetoids_discreteProjection (P : Cᵒᵖ ⥤ Type vC) :
    (discreteProjection P).IsFiberedInSetoids := by
  refine ⟨Functor.IsFiberedInGroupoids.mk' fun U => ?_,
    fun U x y => (isDiscrete_fiber_discreteProjection P U).subsingleton x y⟩
  have : IsDiscrete ((discreteProjection P).Fiber U) := isDiscrete_fiber_discreteProjection P U
  infer_instance

/-- The fibre of the category of elements of `P` over `U` is `P(U)`. -/
@[sga "6 I 6.6" "partial", sga "6 I 8.5"]
def discreteFiberEquiv (P : Cᵒᵖ ⥤ Type vC) (U : C) :
    (discreteProjection P).Fiber U ≃ P.obj (op U) where
  toFun x := cast (congrArg (fun V : C => P.obj (op V)) x.2) x.1.fiber.as
  invFun a := ⟨⟨U, Discrete.mk a⟩, rfl⟩
  left_inv x := by
    rcases x with ⟨⟨V, a⟩, hV⟩
    change V = U at hV
    subst V
    cases a
    rfl
  right_inv _ := rfl

/-- A morphism of the category of elements of `P` lying over `f : V ⟶ U` identifies the element
named by its source with the restriction along `f` of the element named by its target. -/
@[sga "6 I 6.6" "partial"]
theorem discreteFiberEquiv_eq_map_of_isHomLift (P : Cᵒᵖ ⥤ Type vC)
    {V U : C} (f : V ⟶ U) (x : (discreteProjection P).Fiber U)
    (y : (discreteProjection P).Fiber V) (φ : y.1 ⟶ x.1)
    (hφ : (discreteProjection P).IsHomLift f φ) :
    discreteFiberEquiv P V y = P.map f.op (discreteFiberEquiv P U x) := by
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  cases hx
  cases hy
  have hbase : φ.base = f := (IsHomLift.eq_of_isHomLift (discreteProjection P) f φ).symm
  have hval : y.fiber.as = P.map φ.base.op x.fiber.as :=
    Discrete.eq_of_hom (homEquiv (P ⋙ typeToCat) y x φ).2
  rwa [hbase] at hval

/-- The class of a chosen pullback of `x` along `f` names the restriction along `f` of the element
named by `x`. -/
private theorem discreteFiberEquiv_pullbackFiber {C : Type uC} [Category.{vC} C] {𝒮 : Type*}
    [Category 𝒮] {p : 𝒮 ⥤ C} [p.IsPreFibered] (P : Cᵒᵖ ⥤ Type vC)
    (e : StacksRepresentableCFG.EquivalenceOver p (discreteProjection P))
    {U V : C} (f : V ⟶ U) (x : p.Fiber U) :
    discreteFiberEquiv P V ((Functor.fiberFunctorOfCompEq e.hom.w V).obj (p.pullbackFiber x f)) =
      P.map f.op (discreteFiberEquiv P U ((Functor.fiberFunctorOfCompEq e.hom.w U).obj x)) :=
  discreteFiberEquiv_eq_map_of_isHomLift P f
    ((Functor.fiberFunctorOfCompEq e.hom.w U).obj x)
    ((Functor.fiberFunctorOfCompEq e.hom.w V).obj (p.pullbackFiber x f))
    (e.hom.functor.map (Functor.IsPreFibered.pullbackMap x.2 f))
    (Functor.isHomLift_map_of_comp_eq e.hom.w f (Functor.IsPreFibered.pullbackMap x.2 f))

variable {𝒮 : Type uS} [Category.{vC} 𝒮]

/-- For a fibred category `p` equivalent over `C` to the category of elements of `P`, the
isomorphism classes of the fibre of `p` over `U` are the elements of `P(U)`: carry a fibre object
through the equivalence and read off the element it names. -/
noncomputable def isoClassEquiv {p : 𝒮 ⥤ C} [p.IsFibered] (P : Cᵒᵖ ⥤ Type vC)
    (e : StacksRepresentableCFG.EquivalenceOver p (discreteProjection P)) (U : C) :
    p.isoClassPresheaf.obj (op U) ≃ P.obj (op U) where
  toFun c := Quotient.liftOn c
    (fun x => discreteFiberEquiv P U ((Functor.fiberFunctorOfCompEq e.hom.w U).obj x))
    (by
      intro x y h
      obtain ⟨i⟩ := (Functor.isIsomorphicSetoid_r_iff _ _).1 h
      let j := (Functor.fiberFunctorOfCompEq e.hom.w U).mapIso i
      exact congrArg (discreteFiberEquiv P U)
        ((isDiscrete_fiber_discreteProjection P U).eq_of_hom j.hom))
  invFun a := Functor.isoClassMk p
    ((Functor.fiberFunctorOfCompEq e.inv.w U).obj ((discreteFiberEquiv P U).symm a))
  left_inv c := by
    induction c using Quotient.ind with
    | _ x =>
      change Functor.isoClassMk p
        ((Functor.fiberFunctorOfCompEq e.inv.w U).obj
          ((discreteFiberEquiv P U).symm
            (discreteFiberEquiv P U ((Functor.fiberFunctorOfCompEq e.hom.w U).obj x)))) = _
      rw [Equiv.symm_apply_apply]
      apply Functor.isoClassMk_eq_of_iso
      exact Functor.Fiber.isoMk (asIso (e.unitIso.hom.app x.1)).symm (by
        have hl := e.isHomLift_unitIso_inv_app x.1
        have hlU : p.IsHomLift (𝟙 U) (e.unitIso.inv.app x.1) := by
          rwa [x.2] at hl
        simpa using hlU)
  right_inv a := by
    let z := (discreteFiberEquiv P U).symm a
    have hIso :
        (Functor.fiberFunctorOfCompEq e.hom.w U).obj
            ((Functor.fiberFunctorOfCompEq e.inv.w U).obj z) ≅ z :=
      Functor.Fiber.isoMk (asIso (e.counitIso.hom.app z.1)) (by
        have hl := e.isHomLift_counitIso_hom_app z.1
        rwa [z.2] at hl)
    have hEq :
        (Functor.fiberFunctorOfCompEq e.hom.w U).obj
            ((Functor.fiberFunctorOfCompEq e.inv.w U).obj z) = z :=
      (isDiscrete_fiber_discreteProjection P U).eq_of_hom hIso.hom
    have hval := congrArg (discreteFiberEquiv P U) hEq
    change discreteFiberEquiv P U
        ((Functor.fiberFunctorOfCompEq e.hom.w U).obj
          ((Functor.fiberFunctorOfCompEq e.inv.w U).obj
            ((discreteFiberEquiv P U).symm a))) = a
    simpa [z] using hval.trans (Equiv.apply_symm_apply (discreteFiberEquiv P U) a)

/-- `CategoryTheory.PresheafOfCategories.isoClassEquiv` is compatible with restriction: the class
of a chosen pullback of `x` along `f` names the restriction along `f` of the element named by the
class of `x`. -/
theorem isoClassEquiv_naturality {p : 𝒮 ⥤ C} [p.IsFibered]
    (hp : p.IsFiberedInGroupoids) (P : Cᵒᵖ ⥤ Type vC)
    (e : StacksRepresentableCFG.EquivalenceOver p (discreteProjection P))
    {U V : C} (f : V ⟶ U) (c : p.isoClassPresheaf.obj (op U)) :
    isoClassEquiv P e V (p.isoClassPresheaf.map f.op c) =
      P.map f.op (isoClassEquiv P e U c) := by
  let _ : p.IsPreFibered := hp.isFibered.toIsPreFibered
  induction c using Quotient.ind with
  | _ x =>
    show isoClassEquiv P e V
      (p.isoClassPresheaf.map f.op (Functor.isoClassMk p x)) = _
    rw [Functor.isoClassPresheaf_map_isoClassMk]
    exact discreteFiberEquiv_pullbackFiber P e f x

end PresheafOfCategories

end CategoryTheory

end

/-! ### The generalizations made by this development

The declarations below restate, under weaker hypotheses or at more general universes, declarations
of this file whose statements are kept as they are above. Each carries the name of the declaration
it generalizes with the suffix `_univ` (or `Univ` for a definition). -/

universe vC uC uS vS

@[expose] public section

open Opposite

namespace CategoryTheory


namespace PresheafOfCategories

variable {C : Type uC} [Category.{vC} C]

variable {𝒮 : Type uS} [Category.{vS} 𝒮]

/-- For a fibred category `p` equivalent over `C` to the category of elements of `P`, the
isomorphism classes of the fibre of `p` over `U` are the elements of `P(U)`: carry a fibre object
through the equivalence and read off the element it names. -/
noncomputable def isoClassEquivUniv {p : 𝒮 ⥤ C} [p.IsFibered] (P : Cᵒᵖ ⥤ Type vC)
    (e : StacksRepresentableCFG.EquivalenceOver p (discreteProjection P)) (U : C) :
    p.isoClassPresheaf.obj (op U) ≃ P.obj (op U) where
  toFun c := Quotient.liftOn c
    (fun x => discreteFiberEquiv P U ((Functor.fiberFunctorOfCompEq e.hom.w U).obj x))
    (by
      intro x y h
      obtain ⟨i⟩ := (Functor.isIsomorphicSetoid_r_iff _ _).1 h
      let j := (Functor.fiberFunctorOfCompEq e.hom.w U).mapIso i
      exact congrArg (discreteFiberEquiv P U)
        ((isDiscrete_fiber_discreteProjection P U).eq_of_hom j.hom))
  invFun a := Functor.isoClassMk p
    ((Functor.fiberFunctorOfCompEq e.inv.w U).obj ((discreteFiberEquiv P U).symm a))
  left_inv c := by
    induction c using Quotient.ind with
    | _ x =>
      change Functor.isoClassMk p
        ((Functor.fiberFunctorOfCompEq e.inv.w U).obj
          ((discreteFiberEquiv P U).symm
            (discreteFiberEquiv P U ((Functor.fiberFunctorOfCompEq e.hom.w U).obj x)))) = _
      rw [Equiv.symm_apply_apply]
      apply Functor.isoClassMk_eq_of_iso
      exact Functor.Fiber.isoMk (asIso (e.unitIso.hom.app x.1)).symm (by
        have hl := e.isHomLift_unitIso_inv_app x.1
        have hlU : p.IsHomLift (𝟙 U) (e.unitIso.inv.app x.1) := by
          rwa [x.2] at hl
        simpa using hlU)
  right_inv a := by
    let z := (discreteFiberEquiv P U).symm a
    have hIso :
        (Functor.fiberFunctorOfCompEq e.hom.w U).obj
            ((Functor.fiberFunctorOfCompEq e.inv.w U).obj z) ≅ z :=
      Functor.Fiber.isoMk (asIso (e.counitIso.hom.app z.1)) (by
        have hl := e.isHomLift_counitIso_hom_app z.1
        rwa [z.2] at hl)
    have hEq :
        (Functor.fiberFunctorOfCompEq e.hom.w U).obj
            ((Functor.fiberFunctorOfCompEq e.inv.w U).obj z) = z :=
      (isDiscrete_fiber_discreteProjection P U).eq_of_hom hIso.hom
    have hval := congrArg (discreteFiberEquiv P U) hEq
    change discreteFiberEquiv P U
        ((Functor.fiberFunctorOfCompEq e.hom.w U).obj
          ((Functor.fiberFunctorOfCompEq e.inv.w U).obj
            ((discreteFiberEquiv P U).symm a))) = a
    simpa [z] using hval.trans (Equiv.apply_symm_apply (discreteFiberEquiv P U) a)

/-- `CategoryTheory.PresheafOfCategories.isoClassEquivUniv` is compatible with restriction: the
class of a chosen pullback of `x` along `f` names the restriction along `f` of the element named by
the class of `x`. -/
theorem isoClassEquiv_naturality_univ {p : 𝒮 ⥤ C} [p.IsFibered]
    (hp : p.IsFiberedInGroupoids) (P : Cᵒᵖ ⥤ Type vC)
    (e : StacksRepresentableCFG.EquivalenceOver p (discreteProjection P))
    {U V : C} (f : V ⟶ U) (c : p.isoClassPresheaf.obj (op U)) :
    isoClassEquivUniv P e V (p.isoClassPresheaf.map f.op c) =
      P.map f.op (isoClassEquivUniv P e U c) := by
  let _ : p.IsPreFibered := hp.isFibered.toIsPreFibered
  induction c using Quotient.ind with
  | _ x =>
    show isoClassEquivUniv P e V
      (p.isoClassPresheaf.map f.op (Functor.isoClassMk p x)) = _
    rw [Functor.isoClassPresheaf_map_isoClassMk]
    exact discreteFiberEquiv_pullbackFiber P e f x

end PresheafOfCategories

end CategoryTheory

end
