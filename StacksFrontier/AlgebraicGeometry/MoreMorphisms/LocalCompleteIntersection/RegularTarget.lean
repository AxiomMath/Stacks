module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteTypeLocalAtSource
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Perfect
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.PerfectOverBase
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.RegularTarget
public import StacksCore.Tactic.StacksAttribute

/-!
# A local complete intersection over a Noetherian base factors through a regular scheme

Let `X ⟶ Y ⟶ S` be a commutative triangle of morphisms of schemes with `S` locally Noetherian,
`Y ⟶ S` locally of finite type and `Y` regular. If `X ⟶ S` is a local complete intersection
morphism, then so is `X ⟶ Y`, and `Y ⟶ S` is Koszul at the image of every point of `X`.

## Main results

* `AlgebraicGeometry.isLocalCompleteIntersectionMorphism_of_isRegular_target`: `X ⟶ Y` is a
  local complete intersection morphism.
* `AlgebraicGeometry.koszulAt_of_isRegular_target`: `Y ⟶ S` is Koszul at the image of every
  point of `X`.

## References

* [Stacks Project, Lemma 37.62.13 (0FJ2)](https://stacks.math.columbia.edu/tag/0FJ2)
* [Stacks Project, Lemma 37.62.12 (09RL)](https://stacks.math.columbia.edu/tag/09RL)
* [Stacks Project, Lemma 37.61.6 (068B)](https://stacks.math.columbia.edu/tag/068B)
* [Stacks Project, Lemma 29.15.8 (01T8)](https://stacks.math.columbia.edu/tag/01T8)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- In a commutative triangle `X ⟶ Y ⟶ S` with `Y` regular and `X ⟶ S` a local complete
intersection morphism, the morphism `f : X ⟶ Y` is perfect. -/
private theorem perfect_of_isRegular_of_isLocalCompleteIntersectionMorphism {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) {h : X ⟶ S} (hcomm : f ≫ g = h) (hY : IsRegular Y)
    (hh : IsLocalCompleteIntersectionMorphism h) : AlgebraicGeometry.Perfect f := by
  have hcomp : LocallyOfFiniteType (f ≫ g) := by
    rw [hcomm]
    exact LocallyOfFiniteType.of_forall_finiteTypeAt h fun x => (hh x).finiteTypeAt
  have : LocallyOfFiniteType f := LocallyOfFiniteType.of_comp hcomp
  exact perfect_of_isRegular f hY

/-- Let `X ⟶ Y ⟶ S` be a commutative triangle of morphisms of schemes with `S` locally
Noetherian, `Y ⟶ S` locally of finite type and `Y` regular. If `X ⟶ S` is a local complete
intersection morphism, then so is `f : X ⟶ Y`. -/
@[stacks 0FJ2 "f is a local complete intersection morphism"]
theorem isLocalCompleteIntersectionMorphism_of_isRegular_target {X Y S : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ S) {h : X ⟶ S} (hcomm : f ≫ g = h) [IsLocallyNoetherian S] [LocallyOfFiniteType g]
    (hY : IsRegular Y) (hh : IsLocalCompleteIntersectionMorphism h) :
    IsLocalCompleteIntersectionMorphism f :=
  have : AlgebraicGeometry.Perfect f :=
    perfect_of_isRegular_of_isLocalCompleteIntersectionMorphism f g hcomm hY hh
  isLocalCompleteIntersectionMorphism_of_perfect f g hcomm hh

/-- Let `X ⟶ Y ⟶ S` be a commutative triangle of morphisms of schemes with `S` locally
Noetherian, `Y ⟶ S` locally of finite type and `Y` regular. If `X ⟶ S` is a local complete
intersection morphism, then `g : Y ⟶ S` is Koszul at the image of every point of `X`. -/
@[stacks 0FJ2 "Y ⟶ S is Koszul at the image of every point of X"]
theorem koszulAt_of_isRegular_target {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) {h : X ⟶ S}
    (hcomm : f ≫ g = h) [IsLocallyNoetherian S] [LocallyOfFiniteType g] (hY : IsRegular Y)
    (hh : IsLocalCompleteIntersectionMorphism h) (x : X) : KoszulAt g (f.base x) :=
  have : AlgebraicGeometry.Perfect f :=
    perfect_of_isRegular_of_isLocalCompleteIntersectionMorphism f g hcomm hY hh
  koszulAt_of_perfect f g hcomm hh x

end AlgebraicGeometry

end
