module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# A specialization created downstairs obstructs immersion

An immersion of schemes is an embedding of topological spaces, so it reflects
specializations: if `f` is an immersion and `f x ⤳ f y`, then `x ⤳ y`. This file records the
contrapositive in the form in which a relation of an algebraic space is shown not to be an
immersion.

The situation is a morphism `j : R ⟶ X`, a morphism `t : R ⟶ U` and an open immersion
`i : W ⟶ U`, with `L` the base change of `i` along `t`. Two points `x, y` of `R` are given
which `t` makes specialize and which `j` makes specialize, but which do not specialize in
`R`, and `t y` lies in the image of `i`. Then the restriction `L ⟶ X` of `j` to the open
part is not an immersion: both points lift to `L`, uniquely, and an immersion would carry the
downstairs specialization back up to `R`.

## Main results

* `AlgebraicGeometry.not_isImmersion_comp_of_specializes_of_not_specializes`: the
  obstruction.

## Implementation notes

That both points lift to `L` is where the open immersion is used twice: the range of the base
change `e : L ⟶ R` is the preimage under `t` of the range of `i`
(`AlgebraicGeometry.IsOpenImmersion.range_pullbackFst`), `t y` lies in that range by
hypothesis, and `t x` lies in it because it specializes to `t y` and the range of an open
immersion is open, hence stable under taking generalizations.

## References

* [Stacks Project, Tag 01KJ](https://stacks.math.columbia.edu/tag/01KJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry

/-- **A specialization created downstairs obstructs immersion.** Let `j : R ⟶ X` and
`t : R ⟶ U` be morphisms of schemes, let `i : W ⟶ U` be an open immersion and let
`e : L ⟶ R`, `p : L ⟶ W` be a base change of `i` along `t`. Suppose two points `x, y` of `R`
specialize under `t` and under `j` but not in `R`, and that `t y` lies in the image of `i`.

Then `e ≫ j : L ⟶ X` is not an immersion. -/
theorem not_isImmersion_comp_of_specializes_of_not_specializes
    {R X U W L : Scheme.{u}} (j : R ⟶ X) (t : R ⟶ U) (i : W ⟶ U) [IsOpenImmersion i]
    (e : L ⟶ R) (p : L ⟶ W) (hsq : IsPullback e p t i)
    (x y : R) (hspec : t x ⤳ t y) (himage : j x ⤳ j y)
    (hnot : ¬ x ⤳ y) (hy : t y ∈ Set.range i) : ¬ IsImmersion (e ≫ j) := by
  have hrange : Set.range e = t ⁻¹' Set.range i := by
    have hfac : e = hsq.isoPullback.hom ≫ pullback.fst t i := hsq.isoPullback_hom_fst.symm
    have heq : Set.range e = Set.range (pullback.fst t i) := by
      ext z
      constructor
      · rintro ⟨l, rfl⟩
        exact ⟨hsq.isoPullback.hom l, (congrArg (fun f : L ⟶ R => f l) hfac).symm⟩
      · rintro ⟨q, hq⟩
        obtain ⟨l, rfl⟩ := hsq.isoPullback.hom.homeomorph.surjective q
        exact ⟨l, by rwa [hfac]⟩
    exact heq.trans (IsOpenImmersion.range_pullbackFst i t)
  obtain ⟨y', hy'⟩ : y ∈ Set.range e := hrange ▸ hy
  obtain ⟨x', hx'⟩ : x ∈ Set.range e :=
    hrange ▸ hspec.mem_open i.isOpenEmbedding.isOpen_range hy
  intro h
  have hdown : (e ≫ j) x' ⤳ (e ≫ j) y' := by
    simpa only [Scheme.Hom.comp_apply, hx', hy'] using himage
  have hup := (e ≫ j).isEmbedding.isInducing.specializes_iff.mp hdown
  exact hnot (by simpa only [hx', hy'] using hup.map e.continuous)

end AlgebraicGeometry

end
