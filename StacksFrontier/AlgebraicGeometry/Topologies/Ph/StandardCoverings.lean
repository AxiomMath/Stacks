module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksCore.Tactic.StacksAttribute

/-!
# Standard ph coverings

A standard ph covering of an affine scheme `T` is a finite family of morphisms from affine
schemes to `T` obtained by restricting a proper surjective morphism `g : U ⟶ T` to a finite
affine open cover of `U`.  Standard ph coverings are stable under base change along a
morphism of affine schemes.

## Main definitions

* `AlgebraicGeometry.StandardPHCovering`: the predicate that a family is a standard ph
  covering.

## Main results

* `AlgebraicGeometry.StandardPHCovering.pullback`: a standard ph covering stays standard
  after base change along a morphism of affine schemes.

## Implementation notes

The definition records the presentation existentially; the characterization, the constructor
`StandardPHCovering.of_presentation`, and the named projections below let one work with the
presentation without unfolding the definition.  The base change is the one of the ambient
category of schemes, so the members of the pulled-back family are the second projections of
the fibre products, and affineness of the sources is inherited from the fibre product of
affine schemes over an affine base.

## References

* [Stacks Project, Tag 0DBD](https://stacks.math.columbia.edu/tag/0DBD)
* [Stacks Project, Tag 0DBE](https://stacks.math.columbia.edu/tag/0DBE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

/-- A family `fᵢ : Xᵢ ⟶ T` is a standard ph covering if its index type is finite, every
`Xᵢ` is affine, and the family is obtained from a finite affine open cover of the source of
a proper surjective morphism to the affine scheme `T`. -/
@[stacks 0DBD]
def StandardPHCovering {ι : Type v} {T : Scheme.{u}} [IsAffine T] {X : ι → Scheme.{u}}
    (f : ∀ i, X i ⟶ T) : Prop :=
  Finite ι ∧ (∀ i, IsAffine (X i)) ∧
    ∃ (U : Scheme.{u}) (g : U ⟶ T) (j : ∀ i, X i ⟶ U),
      IsProper g ∧ Surjective g ∧ (∀ i, IsOpenImmersion (j i)) ∧
        (⋃ i, Set.range (j i)) = Set.univ ∧ (∀ i, j i ≫ g = f i)

/-- Characterization of a standard ph covering by the proper surjective morphism and affine
open cover presenting it. -/
theorem standardPHCovering_iff {ι : Type v} {T : Scheme.{u}} [IsAffine T]
    {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ T) :
    StandardPHCovering f ↔ Finite ι ∧ (∀ i, IsAffine (X i)) ∧
      ∃ (U : Scheme.{u}) (g : U ⟶ T) (j : ∀ i, X i ⟶ U),
        IsProper g ∧ Surjective g ∧ (∀ i, IsOpenImmersion (j i)) ∧
          (⋃ i, Set.range (j i)) = Set.univ ∧ (∀ i, j i ≫ g = f i) :=
  Iff.rfl

/-- The index type of a standard ph covering is finite. -/
theorem StandardPHCovering.finite {ι : Type v} {T : Scheme.{u}} [IsAffine T]
    {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ T} (hf : StandardPHCovering f) : Finite ι :=
  hf.1

/-- Every member of a standard ph covering has affine source. -/
theorem StandardPHCovering.isAffine {ι : Type v} {T : Scheme.{u}} [IsAffine T]
    {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ T} (hf : StandardPHCovering f) (i : ι) :
    IsAffine (X i) :=
  hf.2.1 i

/-- A standard ph covering admits a presentation by an affine open cover of the source of a
proper surjective morphism. -/
theorem StandardPHCovering.exists_presentation {ι : Type v} {T : Scheme.{u}} [IsAffine T]
    {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ T} (hf : StandardPHCovering f) :
    ∃ (U : Scheme.{u}) (g : U ⟶ T) (j : ∀ i, X i ⟶ U),
      IsProper g ∧ Surjective g ∧ (∀ i, IsOpenImmersion (j i)) ∧
        (⋃ i, Set.range (j i)) = Set.univ ∧ (∀ i, j i ≫ g = f i) :=
  hf.2.2

/-- A finite family of affine open restrictions of a proper surjective morphism is a
standard ph covering. -/
theorem StandardPHCovering.of_presentation {ι : Type v} {T : Scheme.{u}} [IsAffine T]
    {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ T) [Finite ι] (hX : ∀ i, IsAffine (X i))
    {U : Scheme.{u}} (g : U ⟶ T) (j : ∀ i, X i ⟶ U) (hg : IsProper g)
    (hg' : Surjective g) (hj : ∀ i, IsOpenImmersion (j i))
    (hcover : (⋃ i, Set.range (j i)) = Set.univ) (hcomp : ∀ i, j i ≫ g = f i) :
    StandardPHCovering f :=
  ⟨inferInstance, hX, U, g, j, hg, hg', hj, hcover, hcomp⟩

/-- **Stacks 0DBE.** A standard ph covering remains standard after pullback along a
morphism of affine schemes. -/
@[stacks 0DBE]
theorem StandardPHCovering.pullback {ι : Type v} {T T' : Scheme.{u}}
    [IsAffine T] [IsAffine T'] {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ T}
    (hf : StandardPHCovering f) (g : T' ⟶ T) :
    StandardPHCovering (fun i ↦ pullback.snd (f i) g) := by
  obtain ⟨U, h, j, hh, hsurj, hj, hcover, hcomp⟩ := hf.exists_presentation
  have : Finite ι := hf.finite
  let k : ∀ i, Limits.pullback (f i) g ⟶ Limits.pullback h g := fun i ↦
    pullback.map (f i) g h g (j i) (𝟙 _) (𝟙 _)
      (by simp [hcomp i]) (by simp)
  refine StandardPHCovering.of_presentation _ (fun i ↦ by
    have : IsAffine (X i) := hf.isAffine i
    infer_instance) (pullback.snd h g) k
    (IsProper.isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback h g) hh)
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective)
      (IsPullback.of_hasPullback h g) hsurj)
    (fun i ↦ by dsimp [k]; infer_instance) ?_ ?_
  · refine Set.eq_univ_iff_forall.mpr fun x ↦ ?_
    obtain ⟨i, hi⟩ :=
      Set.mem_iUnion.mp (hcover ▸ Set.mem_univ ((pullback.fst h g).base x))
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    dsimp [k]
    rw [Scheme.Pullback.range_map]
    exact ⟨hi, Set.mem_range_self _⟩
  · intro i
    dsimp [k, pullback.map]
    exact pullback.lift_snd _ _ _

end AlgebraicGeometry
