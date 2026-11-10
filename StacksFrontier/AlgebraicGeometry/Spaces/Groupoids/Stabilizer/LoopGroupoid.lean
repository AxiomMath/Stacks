module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Groupoid.Loops
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.Basic
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks

/-!
# The stabilizer as the space of loops, and the pointwise inertia groupoid

Let `G` be a groupoid in algebraic spaces over `B`, with object space `U` and arrow space `R`,
and let `G/U` be its stabilizer (Stacks 0447, 0448). By construction the stabilizer is the fibre
product of `(t, s) : R ⟶ U ×_B U` with the diagonal of `U`, so a generalized point of it over a
test object `T` is a point `x` of `U` together with an arrow of `G` whose source and target are
both `x` — that is, a *loop* at `x` in the sense of
`Deformation.GroupoidInFunctors.pointwiseLoops`.

This file makes that identification explicit as an equivalence
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizerElementsEquiv` between the generalized
points of the stabilizer at `T` and the category of elements of the loop functor of the
evaluation of `G` at `T`. Transporting the groupoid structure of that category of elements along
the equivalence gives the *pointwise inertia groupoid*
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.pointwiseInertiaGroupoid`: its objects are the
generalized points of the stabilizer, and an arrow from `x` to `y` is an arrow of `G` from the
base point of `x` to the base point of `y` conjugating the loop of `x` into the loop of `y`.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizerFromLoop`: the generalized point of the
  stabilizer determined by an arrow whose source and target agree.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizerExplicitPullbackIso`: the generalized
  points of the stabilizer as an explicit fibre product of types.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizerElementsEquiv`: the generalized points
  of the stabilizer as the elements of the loop functor.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.pointwiseInertiaGroupoid`: the groupoid of loops
  and conjugating arrows at a fixed test object.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.sourceTarget_eq_diagonal_of_loop`: an arrow whose
  source and target agree lands in the diagonal, read on generalized points.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizerArrow_source_app` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizerArrow_target_app`: the endpoints of the
  arrow underlying a generalized point of the stabilizer.

## Implementation notes

`AlgebraicGeometry.GroupoidInAlgebraicSpaces.toGroupoidInFunctors` is given the attribute
`implicit_reducible` locally in this file. It is a structure literal whose `source` and `target`
fields are `G.source.hom` and `G.target.hom`, and the statements below mix the two spellings —
the endpoint maps of the evaluated groupoid on one side, the morphisms of algebraic spaces they
come from on the other. Without the attribute, unification is not permitted to unfold the
semireducible definition that separates them, and each such statement would need its own
transparency override.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

attribute [local implicit_reducible] toGroupoidInFunctors

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-! ### The arrow underlying a generalized point of the stabilizer -/

/-- The source of the arrow underlying a generalized point of the stabilizer is the point of the
object space that point lies over. -/
theorem stabilizerArrow_source_app (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ) (x : (stabilizerOverBase G).obj.obj T) :
    G.toGroupoidInFunctors.source.app T ((stabilizerArrow G).app T x) =
      (stabilizer G).hom.app T x := by
  exact congr_fun (congrArg (·.app T) (stabilizerArrow_source G)) x

/-- The target of the arrow underlying a generalized point of the stabilizer is the point of the
object space that point lies over. -/
theorem stabilizerArrow_target_app (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ) (x : (stabilizerOverBase G).obj.obj T) :
    G.toGroupoidInFunctors.target.app T ((stabilizerArrow G).app T x) =
      (stabilizer G).hom.app T x := by
  exact congr_fun (congrArg (·.app T) (stabilizerArrow_target G)) x

/-- The generalized point of the stabilizer determined by an arrow of the groupoid whose source
and target are both the structure morphism of the test object. -/
noncomputable def stabilizerFromLoop (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : Over G.objects.obj} (a : T.left ⟶ G.arrows.obj)
    (hs : a ≫ G.source.hom = T.hom) (ht : a ≫ G.target.hom = T.hom) :
    T ⟶ stabilizer G :=
  Over.homMk (pullback.lift a T.hom (stabilizerArrow_condition G a T.hom hs ht))
    (pullback.lift_snd a T.hom (stabilizerArrow_condition G a T.hom hs ht))

/-- The arrow underlying `AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizerFromLoop` is the
arrow it was built from. -/
theorem stabilizerFromLoop_arrow (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : Over G.objects.obj} (a : T.left ⟶ G.arrows.obj)
    (hs : a ≫ G.source.hom = T.hom) (ht : a ≫ G.target.hom = T.hom) :
    (stabilizerFromLoop G a hs ht).left ≫ stabilizerArrow G = a :=
  pullback.lift_fst a T.hom (stabilizerArrow_condition G a T.hom hs ht)

/-! ### The generalized points of the stabilizer as an explicit fibre product -/

/-- The generalized points of the stabilizer over a test object, as the explicit fibre product
of types of the source-target map with the diagonal. -/
noncomputable def stabilizerExplicitPullbackIso (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ) :
    (stabilizerOverBase G).obj.obj T ≅
      Types.PullbackObj ((sourceTarget G).hom.app T) ((diagonal G).hom.app T) :=
  pullbackObjIso (sourceTarget G).hom (diagonal G).hom T ≪≫
    Types.pullbackIsoPullback ((sourceTarget G).hom.app T) ((diagonal G).hom.app T)

/-- The first projection of the explicit fibre product of types, read through
`pullbackObjIso`. -/
private theorem pullback_fst_pullbackObjIso_hom_apply {F₁ F₂ F₃ : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (f : F₁ ⟶ F₃) (g : F₂ ⟶ F₃) (T : (BigFppfOver C S hS)ᵒᵖ) (z : (pullback f g).obj T) :
    pullback.fst (f.app T) (g.app T) ((pullbackObjIso f g T).hom z) =
      (pullback.fst f g).app T z :=
  congrArg (fun h => h z) (pullbackObjIso_hom_comp_fst f g T)

/-- The second projection of the explicit fibre product of types, read through
`pullbackObjIso`. -/
private theorem pullback_snd_pullbackObjIso_hom_apply {F₁ F₂ F₃ : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (f : F₁ ⟶ F₃) (g : F₂ ⟶ F₃) (T : (BigFppfOver C S hS)ᵒᵖ) (z : (pullback f g).obj T) :
    pullback.snd (f.app T) (g.app T) ((pullbackObjIso f g T).hom z) =
      (pullback.snd f g).app T z :=
  congrArg (fun h => h z) (pullbackObjIso_hom_comp_snd f g T)

/-- The arrow coordinate of the explicit fibre product description. -/
theorem stabilizerExplicitPullbackIso_hom_fst (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ) (q : (stabilizerOverBase G).obj.obj T) :
    ((stabilizerExplicitPullbackIso G T).hom q).1.1 = (stabilizerArrow G).app T q := by
  exact pullback_fst_pullbackObjIso_hom_apply (sourceTarget G).hom (diagonal G).hom T q

/-- The base-point coordinate of the explicit fibre product description. -/
theorem stabilizerExplicitPullbackIso_hom_snd (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ) (q : (stabilizerOverBase G).obj.obj T) :
    ((stabilizerExplicitPullbackIso G T).hom q).1.2 = (stabilizer G).hom.app T q := by
  exact pullback_snd_pullbackObjIso_hom_apply (sourceTarget G).hom (diagonal G).hom T q

/-- A generalized point of the stabilizer is determined by the arrow underlying it together with
the point of the object space it lies over. -/
theorem stabilizerOverBase_app_ext (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ) {p q : (stabilizerOverBase G).obj.obj T}
    (ha : (stabilizerArrow G).app T p = (stabilizerArrow G).app T q)
    (hb : (stabilizer G).hom.app T p = (stabilizer G).hom.app T q) : p = q := by
  refine (show Function.Injective (stabilizerExplicitPullbackIso G T).hom from
    fun u v h => by simpa using congrArg (stabilizerExplicitPullbackIso G T).inv h) ?_
  refine Subtype.ext (Prod.ext ?_ ?_)
  · rwa [stabilizerExplicitPullbackIso_hom_fst, stabilizerExplicitPullbackIso_hom_fst]
  · rwa [stabilizerExplicitPullbackIso_hom_snd, stabilizerExplicitPullbackIso_hom_snd]

/-- An arrow of the groupoid whose source and target are both `x` lands in the diagonal, read on
generalized points. -/
theorem sourceTarget_eq_diagonal_of_loop (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ) (a : G.toGroupoidInFunctors.arrows.obj T)
    (x : G.toGroupoidInFunctors.objects.obj T)
    (hs : G.toGroupoidInFunctors.source.app T a = x)
    (ht : G.toGroupoidInFunctors.target.app T a = x) :
    (sourceTarget G).hom.app T a = (diagonal G).hom.app T x := by
  let e := pullbackObjIso G.objectsToBase.hom G.objectsToBase.hom T
  have he : e.hom ((sourceTarget G).hom.app T a) = e.hom ((diagonal G).hom.app T x) := by
    refine Types.ext_of_isPullback (IsPullback.of_hasPullback _ _) ?_ ?_
    · rw [pullback_fst_pullbackObjIso_hom_apply _ _ T ((sourceTarget G).hom.app T a),
        pullback_fst_pullbackObjIso_hom_apply _ _ T ((diagonal G).hom.app T x)]
      change ((sourceTarget G).hom ≫ (objectPairsTarget G).hom).app T a =
        ((diagonal G).hom ≫ (objectPairsTarget G).hom).app T x
      rwa [sourceTarget_target_projection, diagonal_target_projection]
    · rw [pullback_snd_pullbackObjIso_hom_apply _ _ T ((sourceTarget G).hom.app T a),
        pullback_snd_pullbackObjIso_hom_apply _ _ T ((diagonal G).hom.app T x)]
      change ((sourceTarget G).hom ≫ (objectPairsSource G).hom).app T a =
        ((diagonal G).hom ≫ (objectPairsSource G).hom).app T x
      rwa [sourceTarget_source_projection, diagonal_source_projection]
  exact e.toEquiv.injective he

/-- The arrow underlying the generalized point built from an explicit fibre product element. -/
theorem stabilizerExplicitPullbackIso_inv_fst (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (q : Types.PullbackObj ((sourceTarget G).hom.app T) ((diagonal G).hom.app T)) :
    (stabilizerArrow G).app T ((stabilizerExplicitPullbackIso G T).inv q) = q.1.1 := by
  have h := congrArg (fun z : Types.PullbackObj ((sourceTarget G).hom.app T)
      ((diagonal G).hom.app T) => z.1.1)
    (Iso.inv_hom_id_apply (stabilizerExplicitPullbackIso G T) q)
  rwa [stabilizerExplicitPullbackIso_hom_fst] at h

/-- The base point of the generalized point built from an explicit fibre product element. -/
theorem stabilizerExplicitPullbackIso_inv_snd (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (q : Types.PullbackObj ((sourceTarget G).hom.app T) ((diagonal G).hom.app T)) :
    (stabilizer G).hom.app T ((stabilizerExplicitPullbackIso G T).inv q) = q.1.2 := by
  have h := congrArg (fun z : Types.PullbackObj ((sourceTarget G).hom.app T)
      ((diagonal G).hom.app T) => z.1.2)
    (Iso.inv_hom_id_apply (stabilizerExplicitPullbackIso G T) q)
  rwa [stabilizerExplicitPullbackIso_hom_snd] at h

/-! ### The stabilizer as the elements of the loop functor -/

/-- A generalized point of the stabilizer, read as an element of the loop functor: its base
point, together with the arrow underlying it as a loop there. -/
noncomputable def stabilizerToElements (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ) :
    (stabilizerOverBase G).obj.obj T →
      (G.toGroupoidInFunctors.loopConjugationFunctor T).Elements := fun q =>
  Functor.elementsMk _ ((stabilizer G).hom.app T q)
    ⟨(stabilizerArrow G).app T q, stabilizerArrow_source_app G T q,
      stabilizerArrow_target_app G T q⟩

/-- An element of the loop functor, read as a generalized point of the stabilizer. -/
noncomputable def elementsToStabilizer (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ) :
    (G.toGroupoidInFunctors.loopConjugationFunctor T).Elements →
      (stabilizerOverBase G).obj.obj T := fun e =>
  (stabilizerExplicitPullbackIso G T).inv
    ⟨(e.val.1, e.obj), sourceTarget_eq_diagonal_of_loop G T e.val.1 e.obj e.val.2.1 e.val.2.2⟩

/-- The generalized points of the stabilizer over a test object are exactly the pairs consisting
of a point of the object space and a loop at it. -/
noncomputable def stabilizerElementsEquiv (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ) :
    (stabilizerOverBase G).obj.obj T ≃
      (G.toGroupoidInFunctors.loopConjugationFunctor T).Elements where
  toFun := stabilizerToElements G T
  invFun := elementsToStabilizer G T
  left_inv q :=
    stabilizerOverBase_app_ext G T
      (stabilizerExplicitPullbackIso_inv_fst G T _)
      (stabilizerExplicitPullbackIso_inv_snd G T _)
  right_inv e := by
    obtain @⟨x, a⟩ := e
    let q : Types.PullbackObj ((sourceTarget G).hom.app T) ((diagonal G).hom.app T) :=
      ⟨(a.1, x), sourceTarget_eq_diagonal_of_loop G T a.1 x a.2.1 a.2.2⟩
    have hx : (stabilizer G).hom.app T ((stabilizerExplicitPullbackIso G T).inv q) = x :=
      stabilizerExplicitPullbackIso_inv_snd G T q
    have key : ∀ {y z : (G.toGroupoidInFunctors.loopConjugationFunctor T).Elements},
        y.obj = z.obj → y.val ≍ z.val → y = z := by
      rintro ⟨y⟩ ⟨z⟩ (rfl : _ = _) h
      cases eq_of_heq h
      rfl
    refine key hx ?_
    let b : G.toGroupoidInFunctors.pointwiseLoops T
        ((stabilizer G).hom.app T ((stabilizerExplicitPullbackIso G T).inv q)) :=
      (stabilizerToElements G T (elementsToStabilizer G T ⟨a⟩)).val
    change b ≍ a
    have hcast : b = cast (congrArg (G.toGroupoidInFunctors.pointwiseLoops T) hx.symm) a :=
      Subtype.ext ((stabilizerExplicitPullbackIso_inv_fst G T q).trans
        (G.toGroupoidInFunctors.pointwiseLoops_val_cast T hx.symm a).symm)
    exact (heq_of_eq hcast).trans (cast_heq _ a)

/-- The pointwise inertia groupoid of a groupoid in algebraic spaces at a test object: its
objects are the generalized points of the stabilizer there, and an arrow from `x` to `y` is an
arrow of the groupoid from the base point of `x` to the base point of `y` which conjugates the
loop of `x` into the loop of `y`. -/
@[instance_reducible]
noncomputable def pointwiseInertiaGroupoid (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ) : Groupoid ((stabilizerOverBase G).obj.obj T) :=
  InducedCategory.groupoid
    (Functor.Elements (G.toGroupoidInFunctors.loopConjugationFunctor T))
    (stabilizerElementsEquiv G T)

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
