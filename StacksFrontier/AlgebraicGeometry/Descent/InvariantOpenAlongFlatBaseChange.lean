module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.OpenSubsetFpqc

/-!
# Descending an invariant open along a flat base change

Let `q : c ⟶ a` be a surjective, quasi-compact, flat morphism of schemes and let `n : o ⟶ a` be
arbitrary, so that the base change `t : v ⟶ o` of `q` along `n` is again surjective,
quasi-compact and flat. An open subscheme of `v` whose two inverse images in `v ×_o v` agree is
the inverse image of a unique open subscheme of `o`, and the inclusion of the given open is
Cartesian over the inclusion of the descended one.

This is the one gluing step which effective descent for quasi-affine morphisms needs beyond
effective descent for affine morphisms. Over an affine base a quasi-affine morphism is a
quasi-compact open immersion into the spectrum of the global sections of its source; the descent
datum is carried by that affine hull through flat base change for global sections
(`AlgebraicGeometry.isPushout_appTop_of_flat`), so once the hull has been descended to some
`n : o ⟶ a` the morphism itself is an invariant open of `v = c ×_a o` and the theorems below cut
it out of `o`. The step is Stacks 03N0 at a one-member covering.

## Main results

* `AlgebraicGeometry.existsUnique_opens_preimage_eq`: **Stacks 03N0 for a single surjective
  quasi-compact flat morphism.** An open of the source whose two inverse images in the fibre
  square agree is the inverse image of a unique open of the target.
* `AlgebraicGeometry.existsUnique_opens_preimage_eq_of_isPullback`: the same for the base change
  of a surjective quasi-compact flat morphism along an arbitrary morphism, which is the shape a
  descent datum presents.
* `AlgebraicGeometry.exists_isPullback_of_preimage_eq_opensRange`: an open immersion whose image
  is the inverse image of an open of the target factors Cartesianly through that open.
* `AlgebraicGeometry.exists_opens_isPullback_of_preimage_eq_opensRange`: the two combined — an
  invariant open immersion into the base change descends to an open of the base, Cartesianly.
  This is the candidate for the descended object which the descent problem asks for.

## Implementation notes

The invariance hypothesis is stated as the equality of the two inverse images of the open under
the two projections of `v ×_o v`, which is the hypothesis of Stacks 03N0 at the one-member
covering `{t}` and is what a descent datum provides: the datum identifies the two base changes of
the open to `v ×_o v` as subobjects of one scheme. It is deliberately not stated through a
`AlgebraicGeometry.DescentData`, so that no realization of the canonical datum has to be fixed
and no gluing isomorphism appears in the statement.

`AlgebraicGeometry.exists_isPullback_of_preimage_eq_opensRange` returns the Cartesian leg
existentially rather than as `AlgebraicGeometry.morphismRestrict` transported along the equality
of opens: transporting it would put an `eqToHom` in the statement, and the leg is recovered from
the universal property anyway.

## References

* [Stacks Project, Tag 03N0](https://stacks.math.columbia.edu/tag/03N0)
* [Stacks Project, Tag 0247](https://stacks.math.columbia.edu/tag/0247)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- **Stacks 03N0 for a single surjective quasi-compact flat morphism.** An open subscheme `V` of
the source of a surjective, quasi-compact, flat morphism `f : X ⟶ S` whose two inverse images
under the projections of `X ×_S X` agree is the inverse image of a unique open subscheme of
`S`. -/
theorem existsUnique_opens_preimage_eq (f : X ⟶ S) [Surjective f] [QuasiCompact f] [Flat f]
    (V : X.Opens) (hV : pullback.fst f f ⁻¹ᵁ V = pullback.snd f f ⁻¹ᵁ V) :
    ∃! W : S.Opens, f ⁻¹ᵁ W = V := by
  obtain ⟨W, hW, huniq⟩ := existsUnique_isOpen_preimage_eq_of_mem_fpqcPrecoverage
    (fun _ : Unit ↦ X) (fun _ ↦ f) (ofArrows_unit_mem_fpqcPrecoverage f) (fun _ ↦ V)
    fun _ _ ↦ hV
  exact ⟨W, hW (), fun W' hW' ↦ huniq W' fun _ ↦ hW'⟩

/-- **An invariant open of a flat base change descends.** Let `q : c ⟶ a` be surjective,
quasi-compact and flat, and let `t : v ⟶ o` be its base change along a morphism `n : o ⟶ a`. An
open subscheme of `v` whose two inverse images under the projections of `v ×_o v` agree is the
inverse image of a unique open subscheme of `o`.

This is `AlgebraicGeometry.existsUnique_opens_preimage_eq` together with the base-change
stability of surjectivity, quasi-compactness and flatness; it is stated separately because a
descent datum presents its covering as a Cartesian square rather than as a morphism already known
to be faithfully flat. -/
@[sga "3 V 7.3" "more general"]
theorem existsUnique_opens_preimage_eq_of_isPullback {a c o v : Scheme.{u}} {q : c ⟶ a}
    [Surjective q] [QuasiCompact q] [Flat q] {w : v ⟶ c} {t : v ⟶ o} {n : o ⟶ a}
    (sqv : IsPullback w t q n) (V : v.Opens)
    (hV : pullback.fst t t ⁻¹ᵁ V = pullback.snd t t ⁻¹ᵁ V) :
    ∃! W : o.Opens, t ⁻¹ᵁ W = V :=
  have _hs : Surjective t := MorphismProperty.of_isPullback (P := @Surjective) sqv inferInstance
  have _hq : QuasiCompact t :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) sqv inferInstance
  have _hf : Flat t := MorphismProperty.of_isPullback (P := @Flat) sqv inferInstance
  existsUnique_opens_preimage_eq t V hV

/-- **An open immersion whose image is the inverse image of an open of the target factors
Cartesianly through that open.** Let `t : v ⟶ o` be a morphism of schemes, let `ι : z ⟶ v` be an
open immersion and let `W` be an open subscheme of `o` with `t ⁻¹ᵁ W = ι.opensRange`. Then there
is a morphism `ρ : z ⟶ W` making the square of `ρ`, `ι`, `W.ι` and `t` Cartesian.

The square is `AlgebraicGeometry.isPullback_morphismRestrict` read through the isomorphism
`AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq` between `z` and the open `t ⁻¹ᵁ W`. -/
@[ega "I 4.4.1" "open clause", sga "5 IIIB 2.1" "(1)"]
theorem exists_isPullback_of_preimage_eq_opensRange {o v z : Scheme.{u}} (t : v ⟶ o) (ι : z ⟶ v)
    [IsOpenImmersion ι] {W : o.Opens} (h : t ⁻¹ᵁ W = ι.opensRange) :
    ∃ ρ : z ⟶ W.toScheme, IsPullback ρ ι W.ι t := by
  have hrange : Set.range ι.base = Set.range (t ⁻¹ᵁ W).ι.base := by
    rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange, Scheme.Opens.opensRange_ι, h]
  let e : z ≅ (t ⁻¹ᵁ W).toScheme := IsOpenImmersion.isoOfRangeEq ι (t ⁻¹ᵁ W).ι hrange
  have hfac : e.hom ≫ (t ⁻¹ᵁ W).ι = ι := IsOpenImmersion.isoOfRangeEq_hom_fac ι _ hrange
  refine ⟨e.hom ≫ (t ∣_ W), (isPullback_morphismRestrict t W).of_iso e.symm (Iso.refl _)
    (Iso.refl _) (Iso.refl _) (by simp) ?_ (by simp) (by simp)⟩
  simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
  rw [← hfac, Iso.inv_hom_id_assoc]

/-- **An invariant open immersion into a flat base change descends, Cartesianly.** Let
`q : c ⟶ a` be surjective, quasi-compact and flat, let `t : v ⟶ o` be its base change along
`n : o ⟶ a`, and let `ι : z ⟶ v` be an open immersion whose image has the same two inverse
images under the projections of `v ×_o v`. Then there is an open subscheme `W` of `o` and a
morphism `ρ : z ⟶ W` such that the square of `ρ`, `ι`, `W.ι` and `t` is Cartesian, and `W` is
the unique open of `o` whose inverse image is the image of `ι`.

This is the candidate for the descended object of a descent problem whose datum is an open of a
descended hull: the open immersion `W.ι` is the descended morphism and the Cartesian square
identifies its base change along `t` with the given datum. -/
theorem exists_opens_isPullback_of_preimage_eq_opensRange {a c o v z : Scheme.{u}} {q : c ⟶ a}
    [Surjective q] [QuasiCompact q] [Flat q] {w : v ⟶ c} {t : v ⟶ o} {n : o ⟶ a}
    (sqv : IsPullback w t q n) (ι : z ⟶ v) [IsOpenImmersion ι]
    (hinv : pullback.fst t t ⁻¹ᵁ ι.opensRange = pullback.snd t t ⁻¹ᵁ ι.opensRange) :
    ∃ W : o.Opens, (t ⁻¹ᵁ W = ι.opensRange ∧
      ∀ W' : o.Opens, t ⁻¹ᵁ W' = ι.opensRange → W' = W) ∧
      ∃ ρ : z ⟶ W.toScheme, IsPullback ρ ι W.ι t := by
  obtain ⟨W, hW, huniq⟩ :=
    existsUnique_opens_preimage_eq_of_isPullback sqv ι.opensRange hinv
  exact ⟨W, ⟨hW, huniq⟩, exists_isPullback_of_preimage_eq_opensRange t ι hW⟩

end AlgebraicGeometry

end
