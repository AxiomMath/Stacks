module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentProperBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentSectionsInverseImage
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.SmallEtalePullbackSheafDescent

/-!
# The ph sheaf condition for `π_S⁻¹F`, from proper base change in degree zero

`AlgebraicGeometry.smallEtaleInverseImage_isSheaf_ph_of_descent` deduces Stacks 0DDW from
effective descent along proper surjections for the base's pullback system. Effective descent
along proper surjections (Stacks 0GF0) is proved, from the proper base change theorem in degree
zero (Stacks 0A3U), for the explicit pseudofunctor
`AlgebraicGeometry.smallEtaleSheafInverseImagePseudofunctor`; here Stacks 0DDW is deduced from
that.

## Main results

* `AlgebraicGeometry.smallEtaleInverseImage_isProperSurjectiveSheaf_of_inverseImageDescent` — the
  proper-surjective half of the ph sheaf condition, from effective descent for the explicit
  pseudofunctor.
* `AlgebraicGeometry.smallEtaleInverseImage_isSheaf_ph_of_properBaseChange` — Stacks 0DDW, with the
  statement of Stacks 0A3U for sheaves of sets as the single hypothesis.

## References

* [Stacks Project, Tag 0A3U](https://stacks.math.columbia.edu/tag/0A3U)
* [Stacks Project, Tag 0DDW](https://stacks.math.columbia.edu/tag/0DDW)
* [Stacks Project, Tag 0GF0](https://stacks.math.columbia.edu/tag/0GF0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigPHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : Sheaf (SmallEtale.topology (phAssociatedBigEtaleSite B) S hS) (Type (u + 1)))

/-- **Descent for the explicit pseudofunctor gives the proper-surjective half of the ph sheaf
condition.** If the descent functor of `AlgebraicGeometry.smallEtaleSheafInverseImagePseudofunctor`
along every proper surjective morphism of the underlying category is an equivalence (Stacks 0GF0),
then `π_S⁻¹F` satisfies descent along every proper surjective morphism of the big ph category
over `S`. -/
public theorem smallEtaleInverseImage_isProperSurjectiveSheaf_of_inverseImageDescent
    (h0GF0 : ∀ {X Y : (phAssociatedBigEtaleSite B).Scheme} (f : X ⟶ Y)
      [Surjective ((phAssociatedBigEtaleSite B).inclusion.map f)]
      [IsProper ((phAssociatedBigEtaleSite B).inclusion.map f)],
      (smallEtaleSheafInverseImageDescentFunctor (phAssociatedBigEtaleSite B) f).IsEquivalence) :
    IsProperSurjectiveSheaf B S hS
      ((bigEtaleToSmallEtaleMorphism (phAssociatedBigEtaleSite B) S hS).inverseImage.obj
        F).obj := by
  intro X Y f hp hs
  have : IsProper ((phAssociatedBigEtaleSite B).inclusion.map f.left) := hp
  have : Surjective ((phAssociatedBigEtaleSite B).inclusion.map f.left) := hs
  rw [Presieve.ofArrows_pUnit]
  exact isSheafFor_smallEtaleInverseImage_singleton_of_inverseImageDescent
    (phAssociatedBigEtaleSite B) ((phAssociatedBigEtaleSite B).obj S hS) F f (h0GF0 f.left)

/-- **Stacks 0DDW, granted the proper base change theorem in degree zero (Stacks 0A3U).** For a
sheaf of sets `F` on the small étale site of `S`, `π_S⁻¹F` is a sheaf for the ph topology of the
big ph category over `S`, and the unit of `ε_S⁻¹ ⊣ ε_{S,*}` at `π_S⁻¹F` is an isomorphism. The
hypothesis `h0A3U` is the statement of Stacks 0A3U for sheaves of sets;
`AlgebraicGeometry.isIso_smallEtaleSetBaseChange_of_isProper_forall` proves it. -/
public theorem smallEtaleInverseImage_isSheaf_ph_of_properBaseChange
    (h0A3U : ∀ {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g), IsProper f →
        IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w)) :
    Presieve.IsSheaf (BigPHOver.topology B S hS)
        ((bigEtaleToSmallEtaleMorphism (phAssociatedBigEtaleSite B) S hS).inverseImage.obj
          F).obj ∧
      IsIso ((phToBigEtaleMorphism B (B.obj S hS)).adj.unit.app
        ((bigEtaleToSmallEtaleMorphism (phAssociatedBigEtaleSite B) S hS).inverseImage.obj F)) :=
  have hps := smallEtaleInverseImage_isProperSurjectiveSheaf_of_inverseImageDescent B S hS F
    fun f _ _ ↦
    smallEtaleSheafInverseImageDescentFunctor_isEquivalence_of_surjective_proper_of_properBaseChange
        _ f h0A3U
  ⟨smallEtaleInverseImage_isSheaf_ph_of_isProperSurjectiveSheaf B S hS F hps,
    smallEtaleInverseImage_isIso_phToBigEtale_unit_app_of_properSurjective B S hS F hps⟩

end AlgebraicGeometry

end
