module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.PullbackFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackFullyFaithful.Equivalence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Fully faithful pullback of descent data from an fpqc source

Let `f : X ⟶ X'` be a morphism of schemes over `S`. If `X ⟶ S` is an fpqc covering, then
pullback from descent data relative to `X' ⟶ S` to descent data relative to `X ⟶ S` is fully
faithful.

## Main results

* `AlgebraicGeometry.pullbackFunctor_fullyFaithful_of_source_fpqc` states the full
  faithfulness of pullback when its source covers the base fpqc-locally.

## Implementation notes

An fpqc covering by the single morphism `X ⟶ S` is expressed by membership of its singleton
presieve in `AlgebraicGeometry.Scheme.fpqcPrecoverage`.

## References

* [Stacks Project, Tag 040K](https://stacks.math.columbia.edu/tag/040K)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Limits

/-- A base change of an fpqc covering by a single morphism is again one. -/
lemma singleton_pullback_snd_mem_fpqcPrecoverage {S X X' : Scheme.{u}}
    (a : X ⟶ S) (a' : X' ⟶ S)
    (hcover : Presieve.singleton a ∈ Scheme.fpqcPrecoverage S) :
    Presieve.singleton (pullback.snd a a') ∈ Scheme.fpqcPrecoverage X' := by
  have hc : Presieve.ofArrows (fun _ : PUnit.{u + 2} ↦ X) (fun _ ↦ a) ∈
      Scheme.fpqcPrecoverage S := by
    simpa only [Presieve.ofArrows_pUnit.{u + 1}] using hcover
  have hb := Precoverage.IsStableUnderBaseChange.mem_coverings_of_isPullback
    (J := Scheme.fpqcPrecoverage.{u}) (ι := PUnit.{u + 2}) (S := S)
    (X := fun _ ↦ X) (f := fun _ ↦ a) hc (Y := X') a'
    (P := fun _ ↦ pullback a a')
    (p₁ := fun _ ↦ pullback.snd a a') (p₂ := fun _ ↦ pullback.fst a a')
    (fun _ ↦ (IsPullback.of_hasPullback a a').flip)
  simpa only [Presieve.ofArrows_pUnit.{u + 1}] using hb

/-- Pullback along a morphism `X ⟶ X'` over `S` is fully
faithful on descent data if `X ⟶ S` is an fpqc covering. -/
@[stacks 040K, sga "1 VIII 5.2"]
lemma pullbackFunctor_fullyFaithful_of_source_fpqc
    {S X X' : Scheme.{u}} (a : X ⟶ S) (a' : X' ⟶ S) (f : X ⟶ X') (comm : f ≫ a' = a)
    (hcover : Presieve.singleton a ∈ Scheme.fpqcPrecoverage S) :
    Nonempty
      (DescentData.pullbackFunctor a' a (𝟙 S) f
        (by simpa using comm)).functor.FullyFaithful := by
  let Y := pullback a a'
  let p₁ : Y ⟶ X := pullback.fst a a'
  let p₂ : Y ⟶ X' := pullback.snd a a'
  let b : Y ⟶ S := p₁ ≫ a
  let j : X ⟶ Y := pullback.lift (𝟙 X) f (by simpa using comm.symm)
  have hj₁ : j ≫ p₁ = 𝟙 X := pullback.lift_fst _ _ _
  have hp₂a' : p₂ ≫ a' = b := pullback.condition.symm
  have hjb : j ≫ b = a := by rw [← Category.assoc, hj₁, Category.id_comp]
  let P₂ := DescentData.pullbackFunctor a' b (𝟙 S) p₂ (by simpa using hp₂a')
  let Pⱼ := DescentData.pullbackFunctor b a (𝟙 S) j (by simpa using hjb)
  let P₀ := DescentData.pullbackFunctor a' a (𝟙 S) (j ≫ p₂)
    (by simp [Category.assoc, hp₂a', hjb])
  let directIso := DescentData.pullbackFunctorIso a' a (𝟙 S) f (j ≫ p₂)
    (by simpa using comm) (by simp [Category.assoc, hp₂a', hjb])
  obtain ⟨h₂⟩ := pullbackFunctor_fullyFaithful_of_fpqc P₂
    (singleton_pullback_snd_mem_fpqcPrecoverage a a' hcover)
  have : Pⱼ.functor.IsEquivalence :=
    pullbackFunctor_isEquivalence_of_exists_reverse b a j hjb ⟨p₁, rfl⟩
  exact ⟨(h₂.comp (.ofFullyFaithful Pⱼ.functor)).ofIso
    (directIso.iso.trans (DescentData.pullbackFactorizationIso P₀ P₂ Pⱼ)).symm⟩

end AlgebraicGeometry
