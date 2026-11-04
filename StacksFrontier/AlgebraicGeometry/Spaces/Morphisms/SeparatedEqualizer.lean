module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImage

/-!
# Equality of morphisms into a separated algebraic space (Stacks 084N)

Let `T` be an algebraic space over a scheme `S` contained in a big fppf site, let `X` and `Y` be
algebraic spaces over `T` with structure morphisms `p : X ⟶ T` and `q : Y ⟶ T`, and let
`f, g : X ⟶ Y` be morphisms over `T`. The locus in `X` where `f` and `g` agree is the inverse
image along `(f, g) : X ⟶ Y ×_T Y` of the relative diagonal of `q`, and it is a subfunctor of `X`
whether or not anything is separated: that is `AlgebraicGeometry.Space.eqSubfunctor`. It is
characterised by the property that a subfunctor of `X` is contained in it exactly when `f` and `g`
agree after restriction to that subfunctor, which determines it uniquely among subfunctors of `X`.

When `q` is separated its relative diagonal is a closed immersion, so the agreement locus is a
closed subspace of `X`. Hence if an open subspace `U ⊆ X` on which `f` and `g` agree has
scheme-theoretic closure all of `X` — that is, if the scheme-theoretic image of `U ⟶ X` of
Stacks 082X is `⊤` — then minimality of that scheme-theoretic image forces the agreement locus to
be all of `X`, and `f = g`. This is Stacks 084N; neither openness nor algebraicity of `U` enters
the argument.

The scheme-theoretic closure of an open subspace `U ⊆ X` is by definition the scheme-theoretic
image of its inclusion, so the hypothesis of Stacks 084N is spelled here as
`AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor B S hS U.ι = ⊤`. It is *not* the weaker
condition that `U` be topologically dense in `X`, nor the Stacks notion of `U` being
scheme-theoretically dense in `X`, which asks for full scheme-theoretic closure after every étale
pullback and is neither implied by nor implies this hypothesis in general.

## Main definitions

* `AlgebraicGeometry.Space.eqSubfunctor`: the subfunctor of the source on which two morphisms
  over a common base agree, as the inverse image of the relative diagonal of the base morphism.

## Main results

* `AlgebraicGeometry.Space.le_eqSubfunctor_iff` and
  `AlgebraicGeometry.Space.eqSubfunctor_eq_top_iff` characterise the agreement locus: a
  subfunctor is contained in it exactly when the two morphisms agree on that subfunctor, and it
  is everything exactly when the two morphisms are equal.
* `AlgebraicGeometry.Space.isClosedSubspace_eqSubfunctor`: the agreement locus of two morphisms
  into an algebraic space separated over the base is a closed subspace of the source.
* `AlgebraicGeometry.Space.eq_of_eq_on_of_schemeTheoreticImageSubfunctor_eq_top` is
  **Stacks 084N**: two morphisms over `T` into an algebraic space separated over `T` which agree
  on an open subspace whose scheme-theoretic closure is the whole source are equal.

## Implementation notes

The agreement locus is built from `CategoryTheory.Subfunctor.preimage` and the range of the
relative diagonal rather than as the subfunctor `{x | f.app i x = g.app i x}`, so that its
closedness is the already available Stacks 083Q,
`AlgebraicGeometry.Space.isClosedSubspace_preimage`, applied to the range of a closed immersion,
and no pullback square has to be exhibited by hand.

## References

* [Stacks Project, Tag 082X](https://stacks.math.columbia.edu/tag/082X)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 084N](https://stacks.math.columbia.edu/tag/084N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Equalizer

variable {T X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The relative diagonal of a morphism is a monomorphism, split by either projection of the
fibre product. -/
private theorem mono_diagonal (q : Y ⟶ T) : Mono (pullback.diagonal q) :=
  have : IsSplitMono (pullback.diagonal q) :=
    IsSplitMono.mk' ⟨pullback.fst q q, pullback.diagonal_fst q⟩
  inferInstance

/-- The subfunctor of `X` on which two morphisms `f, g : X ⟶ Y` over `q : Y ⟶ T` agree: the
inverse image of the relative diagonal of `q` along `(f, g) : X ⟶ Y ×_T Y`. -/
def eqSubfunctor (q : Y ⟶ T) (f g : X ⟶ Y) (hfg : f ≫ q = g ≫ q) : Subfunctor X :=
  (Subfunctor.range (pullback.diagonal q)).preimage (pullback.lift f g hfg)

/-- Two morphisms `a, b : Z ⟶ Y` over `q : Y ⟶ T` are equal exactly when the morphism
`(a, b) : Z ⟶ Y ×_T Y` factors through the relative diagonal of `q`, that is, exactly when its
range is contained in the range of that diagonal. -/
private theorem range_lift_le_range_diagonal_iff {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (q : Y ⟶ T) (a b : Z ⟶ Y) (hab : a ≫ q = b ≫ q) :
    Subfunctor.range (pullback.lift a b hab) ≤ Subfunctor.range (pullback.diagonal q) ↔
      a = b := by
  have := mono_diagonal B S hS q
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨r, hr⟩ : ∃ r : Z ⟶ Y, r ≫ pullback.diagonal q = pullback.lift a b hab :=
      ⟨Subfunctor.lift (pullback.lift a b hab) h ≫
        (asIso (Subfunctor.toRange (pullback.diagonal q))).inv, by
          rw [Category.assoc, inv_toRange_comp, Subfunctor.lift_ι]⟩
    have ha : r = a := by simpa using (hr =≫ pullback.fst q q).trans (pullback.lift_fst a b hab)
    have hb : r = b := by simpa using (hr =≫ pullback.snd q q).trans (pullback.lift_snd a b hab)
    exact ha.symm.trans hb
  · rintro rfl
    have hlift : pullback.lift a a hab = a ≫ pullback.diagonal q := by
      refine pullback.hom_ext ?_ ?_
      · rw [pullback.lift_fst, Category.assoc, pullback.diagonal_fst, Category.comp_id]
      · rw [pullback.lift_snd, Category.assoc, pullback.diagonal_snd, Category.comp_id]
    rw [hlift]
    exact Subfunctor.range_comp_le a (pullback.diagonal q)

/-- A subfunctor of the source is contained in the agreement locus of two morphisms exactly when
the two morphisms agree after restriction to it. Taking all subfunctors, this characterises the
agreement locus. -/
theorem le_eqSubfunctor_iff (q : Y ⟶ T) (f g : X ⟶ Y) (hfg : f ≫ q = g ≫ q)
    (U : Subfunctor X) : U ≤ eqSubfunctor B S hS q f g hfg ↔ U.ι ≫ f = U.ι ≫ g := by
  have himage : U.image (pullback.lift f g hfg) =
      Subfunctor.range (U.ι ≫ pullback.lift f g hfg) := by
    rw [Subfunctor.range_comp, Subfunctor.range_ι]
  have hcomp : U.ι ≫ pullback.lift f g hfg = pullback.lift (U.ι ≫ f) (U.ι ≫ g)
      (by rw [Category.assoc, hfg, Category.assoc]) := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
  rw [eqSubfunctor, ← Subfunctor.image_le_iff, himage, hcomp,
    range_lift_le_range_diagonal_iff]

/-- Two morphisms over a common base agree everywhere exactly when their agreement locus is the
whole source. -/
theorem eqSubfunctor_eq_top_iff (q : Y ⟶ T) (f g : X ⟶ Y) (hfg : f ≫ q = g ≫ q) :
    eqSubfunctor B S hS q f g hfg = ⊤ ↔ f = g := by
  rw [eqSubfunctor, Subfunctor.preimage_eq_top_iff, range_lift_le_range_diagonal_iff]

/-- The agreement locus of two morphisms of algebraic spaces over `S` into an algebraic space
which is separated over the base is a closed subspace of the source: the relative diagonal of a
separated morphism is a closed immersion, hence its range is a closed subspace of the fibre
product, and the agreement locus is the inverse image of that closed subspace by Stacks 083Q. -/
theorem isClosedSubspace_eqSubfunctor (hT : IsAlgebraicSpace B S hS T)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (q : Y ⟶ T) (f g : X ⟶ Y)
    (hfg : f ≫ q = g ≫ q) (hq : IsSeparated B S hS q) :
    IsClosedSubspace B S hS (eqSubfunctor B S hS q f g hfg) := by
  have := mono_diagonal B S hS q
  refine isClosedSubspace_preimage B S hS (pullback.lift f g hfg) _
    (isAlgebraicSpace_pullback B S hS q q hY hY hT) hX ⟨?_, ?_⟩
  · exact isAlgebraicSpace_of_iso B S hS
      (asIso (Subfunctor.toRange (pullback.diagonal q))) hY
  · have h := MorphismProperty.RespectsIso.precomp _
      (asIso (Subfunctor.toRange (pullback.diagonal q))).inv (pullback.diagonal q) hq
    rwa [inv_toRange_comp] at h

/-- **Stacks 084N.** Let `X` and `Y` be algebraic spaces over an algebraic space `T` with
structure morphisms `p : X ⟶ T` and `q : Y ⟶ T`, and let `f, g : X ⟶ Y` be morphisms over `T`.
Let `U ⊆ X` be an open subspace with `f` and `g` agreeing on `U`. If the scheme-theoretic closure
of `U` in `X`, that is the scheme-theoretic image of `U ⟶ X`, is all of `X` and `q` is separated,
then `f = g`.

The agreement locus of `f` and `g` is a closed subspace of `X` containing `U`, so minimality of
the scheme-theoretic image of `U ⟶ X` puts that image inside the agreement locus, which is
therefore all of `X`. Openness of `U`, and indeed algebraicity of `U`, are not used. -/
@[stacks 084N]
theorem eq_of_eq_on_of_schemeTheoreticImageSubfunctor_eq_top (hT : IsAlgebraicSpace B S hS T)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (p : X ⟶ T) (q : Y ⟶ T)
    (f g : X ⟶ Y) (hf : f ≫ q = p) (hg : g ≫ q = p) (U : Subfunctor X)
    (_hU : IsOpenSubspace B S hS U) (hfg : U.ι ≫ f = U.ι ≫ g)
    (hclosure : schemeTheoreticImageSubfunctor B S hS U.ι = ⊤) (hq : IsSeparated B S hS q) :
    f = g := by
  have hfgT : f ≫ q = g ≫ q := hf.trans hg.symm
  refine (eqSubfunctor_eq_top_iff B S hS q f g hfgT).1 (top_le_iff.1 ?_)
  calc (⊤ : Subfunctor X) = schemeTheoreticImageSubfunctor B S hS U.ι := hclosure.symm
    _ ≤ eqSubfunctor B S hS q f g hfgT :=
        schemeTheoreticImageSubfunctor_le B S hS U.ι
          (isClosedSubspace_eqSubfunctor B S hS hT hX hY q f g hfgT hq)
          (by
            rw [Subfunctor.range_ι]
            exact (le_eqSubfunctor_iff B S hS q f g hfgT U).2 hfg)

end Equalizer

end AlgebraicGeometry.Space

end
