module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionGroupoid

/-!
# The composition of a restricted groupoid scheme is determined

A generalized point of the arrow scheme of a restriction `R|_{U'}` of a groupoid scheme `R`
along `g : U' ⟶ U` is a triple: an arrow of `R` together with a lift of each of its endpoints
to `U'`.  So it is determined by its source, its target and the arrow of `R` underlying it
(`AlgebraicGeometry.GroupoidScheme.restriction_hom_ext`).

This file states that uniqueness for a realization `AlgebraicGeometry.GroupoidScheme.Restriction`
of `R|_{U'}`, whose arrow scheme is identified with `restrictionArrows` only up to the transport
`arrows_eq`, and deduces that the composition morphism of such a realization is the unique
morphism whose source and target are those of the second and first factors and whose underlying
arrow of `R` is the composition in `R`.

## Main results

* `AlgebraicGeometry.GroupoidScheme.Restriction.hom_ext`: a generalized point of the arrow
  scheme of a realization of a restriction is determined by its source, its target and its
  underlying arrow.
* `AlgebraicGeometry.GroupoidScheme.Restriction.comp_unique`: the composition of a realization
  of a restriction is the unique morphism with the expected source, target and underlying arrow.

## References

* [Stacks Project, Tag 02VB](https://stacks.math.columbia.edu/tag/02VB)
* [Stacks Project, Tag 04MN](https://stacks.math.columbia.edu/tag/04MN)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme.Restriction

variable {S : Scheme.{u}} {G : GroupoidScheme S} {U' : Over S} {g : U' ⟶ G.objects}
  (R : Restriction G g)

/-- A generalized point of the arrow scheme of a realization of a restriction is determined by
its source, its target and its underlying arrow of the ambient groupoid. -/
theorem hom_ext {T : Over S} (a b : T ⟶ R.groupoid.arrows)
    (hs : a ≫ R.groupoid.source = b ≫ R.groupoid.source)
    (ht : a ≫ R.groupoid.target = b ≫ R.groupoid.target)
    (ha : a ≫ R.hom.mapArrows = b ≫ R.hom.mapArrows) :
    a = b := by
  have key : a ≫ eqToHom R.arrows_eq = b ≫ eqToHom R.arrows_eq := by
    refine AlgebraicGeometry.GroupoidScheme.restriction_hom_ext G g _ _ ?_ ?_ ?_
    · rw [R.source_eq] at hs
      simp only [← Category.assoc] at hs
      exact (cancel_mono (eqToHom R.objects_eq.symm)).1 hs
    · rw [R.target_eq] at ht
      simp only [← Category.assoc] at ht
      exact (cancel_mono (eqToHom R.objects_eq.symm)).1 ht
    · rw [R.mapArrows_eq] at ha
      simp only [← Category.assoc] at ha
      exact ha
  exact (cancel_mono (eqToHom R.arrows_eq)).1 key

/-- A morphism from the scheme of composable pairs to the arrow scheme of a realization of a
restriction, whose source is the source of the arrow applied first, whose target is the target of
the arrow applied last, and whose underlying arrow of the ambient groupoid is the ambient
composition, is the composition of the restriction. -/
theorem comp_unique (c : pullback R.groupoid.source R.groupoid.target ⟶ R.groupoid.arrows)
    (hs : c ≫ R.groupoid.source =
      pullback.snd R.groupoid.source R.groupoid.target ≫ R.groupoid.source)
    (ht : c ≫ R.groupoid.target =
      pullback.fst R.groupoid.source R.groupoid.target ≫ R.groupoid.target)
    (ha : c ≫ R.hom.mapArrows = R.hom.mapComposable ≫ G.comp) :
    c = R.groupoid.comp :=
  R.hom_ext c R.groupoid.comp (hs.trans R.groupoid.source_comp.symm)
    (ht.trans R.groupoid.target_comp.symm)
    (ha.trans (Stacks.Groupoids.GroupoidScheme.Hom.comp_mapArrows R.hom).symm)

end AlgebraicGeometry.GroupoidScheme.Restriction

end

end
