module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusDescentFiniteType
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusDescentNoetherianApproximation

/-!
# Descent of vector bundles along proper morphisms in positive characteristic

This file states and proves Stacks Tag 0EXH. Let `p` be a prime, `Y` a quasi-compact and
quasi-separated scheme over `𝐅_p`, and `f : X ⟶ Y` a proper surjective morphism of finite
presentation with geometrically connected fibres. Then

1. pullback `colim_F Vect(Y) ⥤ colim_F Vect(X)` is fully faithful;
2. a finite locally free `𝒪_X`-module `ℰ` such that for every `y ∈ Y` some Frobenius power
   pullback `F^{n_y,*}ℰ` is free on the reduced fibre `X_{y,red}` has a Frobenius power pullback
   `F^{n,*}ℰ` isomorphic to the pullback of a finite locally free `𝒪_Y`-module.

Part (1) is `AlgebraicGeometry.frobeniusColimitVectModelPullback_full_faithful`. Part (2) is
reduced to the case of `Y` of finite type over a field by absolute Noetherian approximation
(`AlgebraicGeometry.descendsAfterFrobenius_of_forall_finiteType`), and that case is
`AlgebraicGeometry.descendsAfterFrobenius_of_finiteType`.

## Main results

* `AlgebraicGeometry.frobeniusColimitVectModelPullback_full_faithful_and_descends`.

## References

* [Stacks Project, Tag 0EXH](https://stacks.math.columbia.edu/tag/0EXH)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-- **Descent of vector bundles in positive characteristic** (Stacks Tag 0EXH). Let `p` be a
prime, `Y` a quasi-compact quasi-separated scheme over `𝐅_p` and `f : X ⟶ Y` a proper surjective
morphism of finite presentation with geometrically connected fibres. Then the pullback functor
`colim_F Vect(Y) ⥤ colim_F Vect(X)` is fully faithful, and if `ℰ` is a finite locally free
`𝒪_X`-module such that for all `y ∈ Y` there are `n_y, r_y ≥ 0` with
`F^{n_y,*}ℰ|_{X_{y,red}} ≅ 𝒪_{X_{y,red}}^{⊕ r_y}`, then for some `n ≥ 0` the Frobenius power
pullback `F^{n,*}ℰ` is the pullback of a finite locally free `𝒪_Y`-module. -/
@[stacks 0EXH]
theorem frobeniusColimitVectModelPullback_full_faithful_and_descends (p : ℕ) [Fact p.Prime]
    {X Y : Scheme.{u}} (hY : IsInCharacteristic Y p) (f : X ⟶ Y) [CompactSpace Y]
    [QuasiSeparatedSpace Y] [IsProper f] [Surjective f] [LocallyOfFinitePresentation f]
    [GeometricallyConnected f] :
    ((frobeniusColimitVectModelPullback f p (isInCharacteristic_of_hom f p hY) hY).Full ∧
      (frobeniusColimitVectModelPullback f p (isInCharacteristic_of_hom f p hY) hY).Faithful) ∧
    ∀ E : X.Vect,
      (∀ y : Y, ∃ n r : ℕ, Nonempty
        ((Scheme.Modules.pullback ((f.fiber y).reductionι ≫ f.fiberι y)).obj
            ((frobeniusPullbackIter X p (isInCharacteristic_of_hom f p hY) n).obj E).obj ≅
          SheafOfModules.free (ULift.{u} (Fin r)))) →
      ∃ (n : ℕ) (G : Y.Vect), Nonempty
        ((frobeniusPullbackIter X p (isInCharacteristic_of_hom f p hY) n).obj E ≅
          (Scheme.Vect.pullback f).obj G) :=
  ⟨frobeniusColimitVectModelPullback_full_faithful f p _ hY, fun E hE ↦
    descendsAfterFrobenius_of_forall_finiteType p
      (fun k _ _ _ s _ _ f₀ _ _ _ hX₀ hY₀ E₀ hE₀ ↦
        descendsAfterFrobenius_of_finiteType k s f₀ hX₀ hY₀ E₀ hE₀)
      f _ hY E hE⟩

end AlgebraicGeometry

end
