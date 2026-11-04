module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.PullbackFaithful
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackFullyFaithful.Equivalence

/-!
# Faithfulness of descent-data pullback from a surjective flat source

Let `f : X ⟶ X'` be a morphism of schemes over `S`. If `X ⟶ S` is surjective and flat, then
pullback from descent data relative to `X' / S` to descent data relative to `X / S` is
faithful.

## Main results

* `AlgebraicGeometry.pullbackFunctor_faithful_of_source_surjective_flat` states faithfulness
  of the pullback functor when the source is surjective and flat over the base.

## Implementation notes

The hypotheses concern the structure morphism `X ⟶ S`, not the morphism `X ⟶ X'` used to pull
back descent data. Factoring `f` through the fibre product `X ×_S X'` replaces it by a
morphism whose second component is surjective and flat, for which
`AlgebraicGeometry.pullbackFunctor_faithful` applies, and a morphism admitting a reverse
morphism over `S`, for which `AlgebraicGeometry.pullbackFunctor_isEquivalence_of_exists_reverse`
applies. Faithfulness is transported along the resulting isomorphism after composing with
evaluation, which is itself faithful because the index type is a singleton.

## References

* [Stacks Project, Tag 040J](https://stacks.math.columbia.edu/tag/040J)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Limits

namespace DescentData

/-- Evaluation at the unique member of a singleton family is faithful. -/
lemma evaluation_unit_faithful {S X : Scheme.{u}} (a : X ⟶ S) :
    (DescentData.evaluation () :
      DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ a) ⥤ Over X).Faithful := by
  constructor
  intro D E φ ψ h
  apply DescentData.hom_ext
  rintro ⟨⟩
  simpa using h

/-- A pullback functor commutes with evaluation, up to base change of the underlying
objects. -/
def PullbackFunctor.evaluationIso {S S' X X' : Scheme.{u}} {a : X ⟶ S} {a' : X' ⟶ S'}
    {h : S' ⟶ S} {f : X' ⟶ X} {comm : f ≫ a = a' ≫ h}
    (P : PullbackFunctor a a' h f comm) :
    P.functor ⋙ DescentData.evaluation () ≅
      DescentData.evaluation () ⋙ Over.pullback f :=
  NatIso.ofComponents P.objIso fun g ↦ (P.map g).symm

end DescentData

/-- **Stacks Project, Tag 040J.** Pullback of descent data along a morphism whose source is
surjective and flat over the base is faithful. -/
@[stacks 040J]
theorem pullbackFunctor_faithful_of_source_surjective_flat
    {S X X' : Scheme.{u}} (a : X ⟶ S) (a' : X' ⟶ S) (f : X ⟶ X') (comm : f ≫ a' = a)
    [Surjective a] [Flat a] :
    (DescentData.pullbackFunctor a' a (𝟙 S) f (by simpa using comm)).functor.Faithful := by
  let Y := pullback a a'
  let p₁ : Y ⟶ X := pullback.fst a a'
  let p₂ : Y ⟶ X' := pullback.snd a a'
  let b : Y ⟶ S := p₁ ≫ a
  let j : X ⟶ Y := pullback.lift (𝟙 X) f (by simpa using comm.symm)
  have hj₁ : j ≫ p₁ = 𝟙 X := pullback.lift_fst _ _ _
  have hj₂ : j ≫ p₂ = f := pullback.lift_snd _ _ _
  have hp₂a' : p₂ ≫ a' = b := pullback.condition.symm
  have hjb : j ≫ b = a := by
    dsimp only [b]
    rw [← Category.assoc, hj₁, Category.id_comp]
  have : Surjective p₂ :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback a a') ‹Surjective a›
  have : Flat p₂ :=
    AlgebraicGeometry.Flat.isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback a a') ‹Flat a›
  let P₂ := DescentData.pullbackFunctor a' b (𝟙 S) p₂ (by simpa using hp₂a')
  let Pⱼ := DescentData.pullbackFunctor b a (𝟙 S) j (by simpa using hjb)
  let P₀ := DescentData.pullbackFunctor a' a (𝟙 S) f (by simpa using comm)
  have : P₂.functor.Faithful := pullbackFunctor_faithful P₂
  have : Pⱼ.functor.IsEquivalence :=
    pullbackFunctor_isEquivalence_of_exists_reverse b a j hjb ⟨p₁, rfl⟩
  let evX : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ a) ⥤ Over X :=
    DescentData.evaluation ()
  let evX' : DescentData (S := S) (X := fun _ : Unit ↦ X') (fun _ ↦ a') ⥤ Over X' :=
    DescentData.evaluation ()
  let evY : DescentData (S := S) (X := fun _ : Unit ↦ Y) (fun _ ↦ b) ⥤ Over Y :=
    DescentData.evaluation ()
  have e₀' : P₀.functor ⋙ evX ≅ evX' ⋙ Over.pullback (j ≫ p₂) := by
    simpa only [← hj₂] using P₀.evaluationIso
  let eIter : (P₂.functor ⋙ Pⱼ.functor) ⋙ evX ≅
      evX' ⋙ Over.pullback p₂ ⋙ Over.pullback j :=
    calc (P₂.functor ⋙ Pⱼ.functor) ⋙ evX
        ≅ P₂.functor ⋙ Pⱼ.functor ⋙ evX := Functor.associator _ _ _
      _ ≅ P₂.functor ⋙ evY ⋙ Over.pullback j :=
          Functor.isoWhiskerLeft _ Pⱼ.evaluationIso
      _ ≅ (P₂.functor ⋙ evY) ⋙ Over.pullback j := (Functor.associator _ _ _).symm
      _ ≅ (evX' ⋙ Over.pullback p₂) ⋙ Over.pullback j :=
          Functor.isoWhiskerRight P₂.evaluationIso (Over.pullback j)
      _ ≅ evX' ⋙ Over.pullback p₂ ⋙ Over.pullback j := Functor.associator _ _ _
  let ePath : P₀.functor ⋙ evX ≅ (P₂.functor ⋙ Pⱼ.functor) ⋙ evX :=
    (e₀'.trans (Functor.isoWhiskerLeft evX' (Over.pullbackComp j p₂))).trans eIter.symm
  have : evX.Faithful := DescentData.evaluation_unit_faithful a
  have : (P₀.functor ⋙ evX).Faithful := Functor.Faithful.of_iso ePath.symm
  exact Functor.Faithful.of_comp P₀.functor evX

end AlgebraicGeometry
