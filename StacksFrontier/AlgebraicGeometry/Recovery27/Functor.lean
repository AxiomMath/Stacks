module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Recovery27.Small

/-!
# The Grassmannian functor

For natural numbers `k` and `n`, the Grassmannian functor sends a scheme `S` to the
isomorphism classes of finite locally free quotients of rank `n - k` of the free module of
rank `n`. A morphism of schemes acts by pullback.

## Main definitions

* `AlgebraicGeometry.Grassmannian.FunctorData`: the data specifying the Grassmannian
  functor, its moduli interpretation and its action by pullback.
* `AlgebraicGeometry.Grassmannian.functor`: the Grassmannian functor `G(k, n)`.

## References

* [Stacks Project, Tag 089S](https://stacks.math.columbia.edu/tag/089S)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Grassmannian

open Limits TopologicalSpace

/-- Data specifying the Grassmannian functor together with its moduli interpretation
and its action by pullback. -/
public structure FunctorData (k n : ℕ) where
  /-- The underlying contravariant functor on schemes. -/
  toFunctor : Scheme.{u}ᵒᵖ ⥤ Type u
  /-- Its value on a scheme is the set of quotient presentations up to isomorphism. -/
  objEquiv : ∀ X : Scheme.{u},
    toFunctor.obj (op X) ≃ Points X k n
  /-- Under this identification, the map associated to a scheme morphism is pullback. -/
  map_isPullback : ∀ {S T : Scheme.{u}} (f : T ⟶ S)
      (q : QuotientPresentation S k n),
    ∃ q' : QuotientPresentation T k n,
      objEquiv T (toFunctor.map f.op ((objEquiv S).symm ⟦q⟧)) = ⟦q'⟧ ∧
        q.IsPullback f q'

/-- A shrunken copy of the isomorphism classes of quotient presentations, contravariantly
functorial in the scheme by pullback. -/
public noncomputable def pointsFunctor (k n : ℕ) : Scheme.{u}ᵒᵖ ⥤ Type u where
  obj X := by
    letI : Small.{u} (Points X.unop k n) := small_points X.unop k n
    exact Shrink.{u} (Points X.unop k n)
  map {X Y} f := by
    letI : Small.{u} (Points X.unop k n) :=
      small_points X.unop k n
    letI : Small.{u} (Points Y.unop k n) :=
      small_points Y.unop k n
    exact ↾(fun x : Shrink (Points X.unop k n) ↦
      equivShrink _ (pullbackPointsMap f.unop k n ((equivShrink _).symm x)))
  map_id := by
    intro X
    let : Small.{u} (Points X.unop k n) := small_points X.unop k n
    apply TypeCat.homEquiv.injective
    funext x
    have hid : pullbackPointsMap (𝟙 X).unop k n = id := by
      simpa using (pullbackPointsMap_id (S := X.unop) k n)
    have h := congrArg (equivShrink (Points X.unop k n))
      (congrFun hid ((equivShrink (Points X.unop k n)).symm x))
    simpa only [TypeCat.homEquiv_apply, TypeCat.ofHom_apply,
      types_id_apply, Function.id_def, Equiv.apply_symm_apply] using h
  map_comp := by
    intro X Y Z f g
    let : Small.{u} (Points X.unop k n) :=
      small_points X.unop k n
    let : Small.{u} (Points Y.unop k n) :=
      small_points Y.unop k n
    let : Small.{u} (Points Z.unop k n) :=
      small_points Z.unop k n
    apply TypeCat.homEquiv.injective
    funext x
    have hcomp : pullbackPointsMap (f ≫ g).unop k n =
        pullbackPointsMap g.unop k n ∘ pullbackPointsMap f.unop k n := by
      simpa using (pullbackPointsMap_comp f.unop g.unop k n)
    have h := congrArg (equivShrink (Points Z.unop k n))
      (congrFun hcomp
        ((equivShrink (Points X.unop k n)).symm x))
    simpa only [TypeCat.homEquiv_apply, TypeCat.ofHom_apply, types_comp_apply,
      Function.comp_apply, Equiv.symm_apply_apply] using h

/-- The data of the Grassmannian functor `G(k, n)`, classifying rank-`n - k` finite locally free
quotients of the free module of rank `n`: the functor `pointsFunctor`, its moduli interpretation
and its action by pullback. -/
public noncomputable def functorData (k n : ℕ) :
    FunctorData.{u} k n := by
  have small (X : Scheme.{u}) : Small.{u} (Points X k n) :=
    small_points X k n
  exact
    { toFunctor := pointsFunctor k n
      objEquiv := fun X ↦ by
        letI : Small.{u} (Points X k n) := small X
        change Shrink.{u} (Points X k n) ≃ Points X k n
        exact (equivShrink (Points X k n)).symm
      map_isPullback := by
        intro S T f q
        refine ⟨pullbackPresentation f q, ?_, pullbackPresentation_isPullback f q⟩
        let := small S
        let := small T
        change (equivShrink (Points T k n)).symm
            (equivShrink (Points T k n) (pullbackPointsMap f k n
              ((equivShrink (Points S k n)).symm
                (equivShrink (Points S k n) ⟦q⟧)))) =
          ⟦pullbackPresentation f q⟧
        rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
        rfl }

/-- The Grassmannian functor `G(k, n)` from schemes to sets, contravariant on morphisms by
pullback. -/
@[stacks 089S]
public noncomputable def functor (k n : ℕ) :
    Scheme.{u}ᵒᵖ ⥤ Type u :=
  (functorData k n).toFunctor

end AlgebraicGeometry.Grassmannian

end
