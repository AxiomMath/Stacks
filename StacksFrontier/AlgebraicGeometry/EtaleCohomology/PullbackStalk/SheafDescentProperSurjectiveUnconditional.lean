module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperPushforwardBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentProperBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentProperSurjective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Effective descent for small étale sheaves along a proper surjection

Let `f : X ⟶ Y` be a surjective proper morphism of schemes. [Stacks, Tag 0GF0] says that the
functor sending a sheaf on the small étale site of `Y` to its canonical descent datum for
`{X ⟶ Y}` is an equivalence of categories. This file proves it for the library's descent functor
`AlgebraicGeometry.smallEtaleSheafDescentFunctor`, with no hypothesis beyond those of the source.

## Main results

* `CategoryTheory.Pseudofunctor.ext_of_locallyDiscrete`: a pseudofunctor from a locally discrete
  bicategory to `Cat` is determined by its values on objects and morphisms and by its composition
  comparisons; its identity comparisons are then forced.
* `AlgebraicGeometry.smallEtaleSheafPullbackSystem_pseudofunctor_eq`: the pseudofunctor of the
  library's `AlgebraicGeometry.smallEtaleSheafPullbackSystem` is the explicit pseudofunctor
  `AlgebraicGeometry.smallEtaleSheafInverseImagePseudofunctor`.
* `AlgebraicGeometry.smallEtaleSheafDescentFunctor_isEquivalence_of_isProper_of_surjective`:
  [Stacks, Tag 0GF0].

## Implementation notes

The source reruns the proof of [Stacks, Tag 0GEZ] with the proper base change theorem
[Stacks, Tag 0A3U] in place of [Stacks, Tag 0EYP]. The descent argument is
`smallEtaleSheafInverseImageDescentFunctor_isEquivalence_of_surjective_proper_of_properBaseChange`
in `AlgebraicGeometry`, which needs 0A3U only for two cartesian squares, and 0A3U is
`Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isProper`. That argument is stated for
the explicit pseudofunctor of small étale sheaves, while the library's descent functor is built
on a pseudofunctor chosen by `Classical.choice` that is only known to have the same fibres,
transition functors and composition comparisons. These data determine a pseudofunctor from a
locally discrete bicategory to `Cat` (the identity comparisons are forced by the left unitor
law), so the two pseudofunctors are equal.

## References

* [Stacks Project, Tag 0GF0](https://stacks.math.columbia.edu/tag/0GF0)
* [Stacks Project, Tag 0A3U](https://stacks.math.columbia.edu/tag/0A3U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w w' v u

namespace CategoryTheory.Pseudofunctor

/-- A pseudofunctor from a locally discrete bicategory to `Cat` is determined by its values on
objects and on morphisms and by its composition comparisons: its action on 2-morphisms is forced
because these are identities, and its identity comparisons are forced by the left unitor law. -/
public theorem ext_of_locallyDiscrete {C : Type w} [Category.{w'} C]
    (F G : Pseudofunctor (LocallyDiscrete C) Cat.{v, u})
    (hobj : ∀ X, F.obj X = G.obj X)
    (hmap : ∀ {X Y : LocallyDiscrete C} (f : X ⟶ Y),
      eqToHom (hobj X).symm ≫ F.map f ≫ eqToHom (hobj Y) = G.map f)
    (hcomp : ∀ {X Y Z : LocallyDiscrete C} (f : X ⟶ Y) (g : Y ⟶ Z),
      HEq (F.mapComp f g) (G.mapComp f g)) :
    F = G := by
  rcases F with ⟨⟨⟨⟨objF, mapF⟩, map₂F⟩, map₂_idF, map₂_compF⟩, idF, compF, _, _, _, luF, _⟩
  rcases G with ⟨⟨⟨⟨objG, mapG⟩, map₂G⟩, map₂_idG, map₂_compG⟩, idG, compG, _, _, _, luG, _⟩
  obtain rfl : objF = objG := funext hobj
  obtain rfl : @mapF = @mapG := by
    funext X Y f
    simpa using hmap f
  obtain rfl : @map₂F = @map₂G := by
    funext X Y f g η
    obtain rfl : f = g := LocallyDiscrete.eq_of_hom η
    obtain rfl : η = 𝟙 f := Subsingleton.elim _ _
    exact (map₂_idF f).trans (map₂_idG f).symm
  obtain rfl : @compF = @compG := by
    funext X Y Z f g
    exact eq_of_heq (hcomp f g)
  obtain rfl : idF = idG := by
    funext X
    have hF := luF (𝟙 X)
    have hG := luG (𝟙 X)
    rw [hG, cancel_epi, cancel_mono] at hF
    let e : 𝟭 (objF X) ≅ (mapF (𝟙 X)).toFunctor := (Cat.Hom.toNatIso (idF X)).symm
    have : (mapF (𝟙 X)).toFunctor.Faithful := Functor.Faithful.of_iso e
    ext x
    apply (mapF (𝟙 X)).toFunctor.map_injective
    simpa only [Cat.whiskerRight_app] using (congrArg (fun α ↦ α.toNatTrans.app x) hF).symm
  rfl

end CategoryTheory.Pseudofunctor

namespace AlgebraicGeometry

/-- The pseudofunctor of the library's small étale sheaf pullback system is the explicit
pseudofunctor of small étale sheaves and their inverse images. -/
public theorem smallEtaleSheafPullbackSystem_pseudofunctor_eq (B : BigEtaleSite.{u}) :
    (smallEtaleSheafPullbackSystem B).pseudofunctor =
      smallEtaleSheafInverseImagePseudofunctor B := by
  refine Pseudofunctor.ext_of_locallyDiscrete (F := (smallEtaleSheafPullbackSystem B).pseudofunctor)
    (G := smallEtaleSheafInverseImagePseudofunctor B)
    (hobj := fun X ↦ (smallEtaleSheafPullbackSystem B).fiber X.as.unop) ?_ ?_
  · intro X Y f
    exact (smallEtaleSheafPullbackSystem B).pullback f.as.unop
  · intro X Y Z f g
    exact ((smallEtaleSheafPullbackSystem B).mapComp_canonical g.as.unop f.as.unop).trans HEq.rfl

/-- **Effective descent of small étale sheaves along a proper surjection.** For a surjective
proper morphism `f : X ⟶ Y` of a big étale site, the functor sending a sheaf of sets on the small
étale site of `Y` to its canonical descent datum for `{X ⟶ Y}` is an equivalence of
categories. -/
@[stacks 0GF0, sga "4 VIII 9.4"]
public theorem smallEtaleSheafDescentFunctor_isEquivalence_of_isProper_of_surjective
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [Surjective (B.inclusion.map f)] [IsProper (B.inclusion.map f)] :
    (smallEtaleSheafDescentFunctor B f).IsEquivalence := by
  have h₀ :=
    smallEtaleSheafInverseImageDescentFunctor_isEquivalence_of_surjective_proper_of_properBaseChange
      B f (fun f g g' f' sq _ ↦
        Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isProper f g g' f' sq)
  have key : ∀ P, P = smallEtaleSheafInverseImagePseudofunctor B →
      (P.toDescentData (fun _ : Unit ↦ f)).IsEquivalence := by
    rintro _ rfl
    exact h₀
  have := key _ (smallEtaleSheafPullbackSystem_pseudofunctor_eq B)
  have : (eqToHom ((smallEtaleSheafPullbackSystem B).fiber Y).symm).toFunctor.IsEquivalence := by
    have gen : ∀ {A A' : Cat.{u + 1, u + 2}} (h : A = A'), (eqToHom h).toFunctor.IsEquivalence := by
      rintro A _ rfl
      exact (inferInstance : (𝟭 A).IsEquivalence)
    exact gen _
  unfold smallEtaleSheafDescentFunctor
  infer_instance

end AlgebraicGeometry

end
