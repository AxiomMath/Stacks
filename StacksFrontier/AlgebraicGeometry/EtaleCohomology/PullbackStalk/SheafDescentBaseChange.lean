module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescent

/-!
# Descent of small étale sheaves after a base change

Effectivity of descent for sheaves on the small étale sites depends on the covering morphism
only through the sieve it generates. Consequently descent along a morphism `f : X ⟶ Y` may be
tested along the structure morphism to `Y` of the base change of `f` along any `g : Z ⟶ Y`
through which `f` factors, in particular along any `g` admitting a section.

## Main results

* `AlgebraicGeometry.smallEtaleSheafDescentFunctor_isEquivalence_iff_of_sieve_eq`: two morphisms
  with the same target generating the same sieve have the same descent behaviour.
* `AlgebraicGeometry.smallEtaleSheafDescentFunctor_isEquivalence_of_baseChange`: the base-change
  criterion for a morphism admitting a section.

## Implementation notes

The descent functor of `SheafDescent` is the canonical descent functor of the small étale sheaf
pseudofunctor precomposed with a transport along the equality identifying its fibre with the
category of sheaves on the small étale site. That transport is an equivalence, so effectivity of
descent is exactly effectivity for the underlying pseudofunctor, which is where Mathlib's
sieve-invariance of descent data applies.

## References

* [Stacks Project, Tag 0GF1](https://stacks.math.columbia.edu/tag/0GF1)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u v' u'

namespace AlgebraicGeometry

/-- Transport along an equality of categories is an equivalence. -/
private theorem isEquivalence_toFunctor_eqToHom {A C : Cat.{v', u'}} (h : A = C) :
    (eqToHom h).toFunctor.IsEquivalence := by
  cases h
  exact CategoryTheory.Equivalence.refl.isEquivalence_functor

/-- The small étale sheaf descent functor is an equivalence exactly when the canonical descent
functor of the small étale sheaf pseudofunctor is. -/
private theorem isEquivalence_smallEtaleSheafDescentFunctor_iff
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) :
    (smallEtaleSheafDescentFunctor B f).IsEquivalence ↔
      ((smallEtaleSheafPullbackSystem B).pseudofunctor.toDescentData
        (fun _ : Unit ↦ f)).IsEquivalence := by
  have he : ((eqToHom ((smallEtaleSheafPullbackSystem B).fiber Y).symm).toFunctor).IsEquivalence :=
    isEquivalence_toFunctor_eqToHom _
  constructor
  · intro hyp
    dsimp [smallEtaleSheafDescentFunctor] at hyp
    exact Functor.isEquivalence_of_comp_left
      (eqToHom ((smallEtaleSheafPullbackSystem B).fiber Y).symm).toFunctor _
  · intro hyp
    dsimp [smallEtaleSheafDescentFunctor]
    infer_instance

/-- Effectivity of descent for small étale sheaves depends on the covering morphism only through
the sieve it generates. -/
public theorem smallEtaleSheafDescentFunctor_isEquivalence_iff_of_sieve_eq
    (B : BigEtaleSite.{u}) {X X' Y : B.Scheme} (f : X ⟶ Y) (f' : X' ⟶ Y)
    (h : Sieve.ofArrows (fun _ : Unit ↦ X) (fun _ ↦ f) =
      Sieve.ofArrows (fun _ : Unit ↦ X') (fun _ ↦ f')) :
    (smallEtaleSheafDescentFunctor B f).IsEquivalence ↔
      (smallEtaleSheafDescentFunctor B f').IsEquivalence := by
  rw [isEquivalence_smallEtaleSheafDescentFunctor_iff,
    isEquivalence_smallEtaleSheafDescentFunctor_iff]
  exact Pseudofunctor.DescentData.isEquivalence_toDescentData_iff_of_sieve_eq _ _ _ h

/-- If `f : X ⟶ Y` factors through `g : Z ⟶ Y`, then `f` and the structure morphism to `Y` of
the base change `X ×_Y Z` of `f` along `g` generate the same sieve. -/
public theorem sieve_ofArrows_pullbackFst_comp
    (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Z ⟶ Y)
    (t : X ⟶ Z) (ht : t ≫ g = f) :
    Sieve.ofArrows (fun _ : Unit ↦ X) (fun _ ↦ f) =
      Sieve.ofArrows (fun _ : Unit ↦ pullback f g) (fun _ ↦ pullback.fst f g ≫ f) := by
  apply le_antisymm <;> intro T a ha <;> rw [Sieve.mem_ofArrows_iff] at ha ⊢ <;>
    obtain ⟨_, b, rfl⟩ := ha
  · exact ⟨(), b ≫ pullback.lift (𝟙 X) t (by rw [Category.id_comp, ht]),
      by rw [Category.assoc, pullback.lift_fst_assoc, Category.id_comp]⟩
  · exact ⟨(), b ≫ pullback.fst f g, by simp⟩

/-- Descent for small étale sheaves along `f : X ⟶ Y` may be tested along the structure morphism
`X ×_Y Z ⟶ Y` of the base change of `f` along any `g : Z ⟶ Y` through which `f` factors. -/
public theorem smallEtaleSheafDescentFunctor_isEquivalence_iff_baseChange
    (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Z ⟶ Y)
    (t : X ⟶ Z) (ht : t ≫ g = f) :
    (smallEtaleSheafDescentFunctor B f).IsEquivalence ↔
      (smallEtaleSheafDescentFunctor B (pullback.fst f g ≫ f)).IsEquivalence :=
  smallEtaleSheafDescentFunctor_isEquivalence_iff_of_sieve_eq B f _
    (sieve_ofArrows_pullbackFst_comp B f g t ht)

/-- Descent of small étale sheaves along `f : X ⟶ Y` is effective as soon as it is effective
along the structure morphism `X ×_Y Z ⟶ Y` of the base change of `f` along a morphism
`g : Z ⟶ Y` admitting a section. -/
@[stacks 0GF1 "only the case of a `g` admitting a section, and with the two hypotheses of the
source -- effectivity over `Z` and over `Z ×_Y Z` -- replaced by effectivity of descent along
the base change `X ×_Y Z` read along its structure morphism to `Y` rather than along its
projection to `Z`. The surjective integral and the surjective proper cases, where the content of
the source lemma lies (these are the cases in which 0GEZ resp. 0GF0 supplies effective descent
along `g`), are NOT proved here; neither is the passage from effectivity over `Z` and over
`Z ×_Y Z` to effectivity over `Y` of the base change."]
public theorem smallEtaleSheafDescentFunctor_isEquivalence_of_baseChange
    (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Z ⟶ Y) (s : Y ⟶ Z)
    (hs : s ≫ g = 𝟙 Y)
    (hXZ : (smallEtaleSheafDescentFunctor B (pullback.fst f g ≫ f)).IsEquivalence) :
    (smallEtaleSheafDescentFunctor B f).IsEquivalence :=
  (smallEtaleSheafDescentFunctor_isEquivalence_iff_baseChange B f g (f ≫ s)
    (by rw [Category.assoc, hs, Category.comp_id])).2 hXZ

/-- Descent of small étale sheaves along `f : X ⟶ Y` is effective as soon as it is effective
along the projection `X ×_Y Y ⟶ Y`. -/
@[stacks 0GF1 "the case `Z = Y`, `g = 𝟙 Y` of the source statement, with the hypothesis in the
shape the source gives it, namely effectivity along the projection `X ×_Y Z ⟶ Z`.  The hypothesis
over `Z ×_Y Z` is not needed in this case.  No other case of the source statement is proved."]
public theorem smallEtaleSheafDescentFunctor_isEquivalence_of_baseChange_id
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    (hZ : (smallEtaleSheafDescentFunctor B (pullback.snd f (𝟙 Y))).IsEquivalence) :
    (smallEtaleSheafDescentFunctor B f).IsEquivalence := by
  refine smallEtaleSheafDescentFunctor_isEquivalence_of_baseChange B f (𝟙 Y) (𝟙 Y) (by simp) ?_
  rwa [pullback.condition, Category.comp_id]

end AlgebraicGeometry

end
