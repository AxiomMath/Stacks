module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSmoothLocalCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct

/-!
# Base change of an fpqc covering of algebraic spaces (Stacks 03MR, part (3))

Pulling an fpqc covering family of algebraic spaces over `S` back along a morphism of algebraic
spaces gives an fpqc covering of the new target, and an isomorphism is an fpqc covering.

## Main results

* `AlgebraicGeometry.Space.isFpqcCovering_pullback`: the base change of an fpqc covering of
  algebraic spaces is an fpqc covering.
* `AlgebraicGeometry.Space.isFpqcCovering_of_isIso`: an isomorphism of presheaves on the big fppf
  site of `S` is an fpqc covering.

## References

* [Stacks Project, Tag 03MR](https://stacks.math.columbia.edu/tag/03MR)
* [Stacks Project, Tag 03MO](https://stacks.math.columbia.edu/tag/03MO)
* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v

/-- Pulling an fpqc covering family of algebraic spaces over `S`
back along a morphism `f : X ⟶ Y` of algebraic spaces gives an fpqc covering of `X`: the second
projections of the fibre products of Stacks 02X2 form an fpqc covering. -/
@[stacks 03MR "part (3): base change"]
theorem isFpqcCovering_pullback
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} {Y X : AlgebraicSpaces B S hS} {Yi : I → AlgebraicSpaces B S hS}
    (g : ∀ i, Yi i ⟶ Y) (f : X ⟶ Y)
    (hg : IsFpqcCovering B S hS (fun i => (g i).hom)) :
    IsFpqcCovering B S hS (fun i => pullback.snd (g i).hom f.hom) := by
  refine ⟨fun i => (isFlat_isStableUnderBaseChange B S hS).of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct B S hS (g i) f) (hg.1 i), fun T h => ?_⟩
  obtain ⟨U, hUfinite, hUcover, hUfactor⟩ := hg.2 T (h ≫ f.hom)
  refine ⟨U, hUfinite, hUcover, fun j => ?_⟩
  obtain ⟨i, a, ha⟩ := hUfactor j
  exact ⟨i, pullback.lift a (yoneda.map ((BigAffineFppf.inclusion B S hS).map (U.f j)) ≫ h)
    (by simpa [Category.assoc] using ha), pullback.lift_snd _ _ _⟩

/-- An isomorphism of presheaves on the big fppf site of `S`, regarded as a family indexed by a
point, is an fpqc covering. -/
@[stacks 03MR "isomorphism"]
theorem isFpqcCovering_of_isIso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) [IsIso f] :
    IsFpqcCovering B S hS (fun _ : PUnit.{v + 1} => f) := by
  have hflat : IsFlat B S hS f := by
    simpa using (holdsOnEveryEtaleChart_iso_comp_iff B S hS
        (@AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u}) f (𝟙 G)).mpr
      (holdsOnEveryEtaleChart_id_presheaf B S hS
        (@AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u})
        (by intro _ _ g hg; have : AlgebraicGeometry.Etale g := hg; infer_instance) G)
  refine ⟨fun _ => hflat, fun T h => ?_⟩
  refine ⟨PreZeroHypercover.singleton (𝟙 T), inferInstance, ?_, ?_⟩
  · simp [PreZeroHypercover.presieve₀_singleton, Presieve.map_singleton]
  · rintro ⟨⟩
    refine ⟨PUnit.unit, h ≫ inv f, ?_⟩
    calc
      (h ≫ inv f) ≫ f = h := by simp [Category.assoc]
      _ = 𝟙 _ ≫ h := by simp
      _ = yoneda.map ((BigAffineFppf.inclusion B S hS).map (𝟙 T)) ≫ h := by congr 1

end AlgebraicGeometry.Space

end
