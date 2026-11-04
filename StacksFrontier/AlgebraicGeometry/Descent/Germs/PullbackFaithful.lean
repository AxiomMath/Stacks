module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.PullbackSquare

/-!
# Faithfulness of pullback for descent data

Pullback of descent data along a surjective flat morphism of schemes is faithful.

## Main results

* `AlgebraicGeometry.pullbackFunctor_faithful` states that a pullback functor for descent data
  is faithful when the morphism along which it pulls back is surjective and flat.

## Implementation notes

The pullback functor is specified by `AlgebraicGeometry.DescentData.PullbackFunctor`, whose
fields record its canonical action on objects and morphisms. The result is stated for any
functor equipped with that structure, and hence applies in particular to
`AlgebraicGeometry.DescentData.pullbackFunctor`. A surjective flat morphism is an epimorphism
and stays one after base change, which is what makes the single component of a morphism of
descent data recoverable from its pullback.

## References

* [Stacks Project, Tag 0240](https://stacks.math.columbia.edu/tag/0240)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

open CategoryTheory

/-- **Stacks Project, Tag 0240.** Pullback of descent data along a surjective flat morphism
is faithful. -/
@[stacks 0240]
theorem pullbackFunctor_faithful
    {S S' X X' : Scheme.{u}} {a : X ⟶ S} {a' : X' ⟶ S'} {h : S' ⟶ S}
    {f : X' ⟶ X} {comm : f ≫ a = a' ≫ h}
    (P : DescentData.PullbackFunctor a a' h f comm) [Surjective f] [Flat f] :
    P.functor.Faithful := by
  have : ∀ Z (g : Z ⟶ X), Epi (Limits.pullback.fst g f) :=
    fun _ _ => Flat.epi_of_flat_of_surjective _
  constructor
  intro D E φ ψ h
  apply DescentData.hom_ext
  intro i
  cases i
  apply (Over.pullback f).map_injective
  rw [← cancel_epi (P.objIso D).hom, P.map φ, P.map ψ, congrArg (fun g => g.hom ()) h]

end AlgebraicGeometry
