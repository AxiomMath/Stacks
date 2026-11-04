module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Depth.FlatLocalHom

/-!
# Flat base change of the depth condition on the complement of an open

Let `j : U ⟶ X` be an open immersion of schemes whose complement consists of points at which
the local ring of `X` has depth at least two, and let `g : X' ⟶ X` be flat. If `j' : U' ⟶ X'`
is the inverse image of `U`, so that the square `j' ≫ g = gU ≫ j` is Cartesian, then the local
rings of `X'` at the points outside `U'` again have depth at least two.

The reason is the additivity of depth along a flat local homomorphism (Stacks 0337): for
`x' ∉ U'` the stalk map `𝒪_{X, g(x')} ⟶ 𝒪_{X', x'}` is a flat local homomorphism, and
`depth(𝒪_{X', x'}) = depth(𝒪_{X, g(x')}) + depth(𝒪_{X', x'} / 𝔪_{g(x')} 𝒪_{X', x'})`, which is
at least `depth(𝒪_{X, g(x')})`. That the points of `X'` outside `U'` are exactly those mapping
outside `U` is the identification of the range of `j'` with the inverse image of the range
of `j`, which holds because the Cartesian square presents `U'` as `X' ×_X U` and `j` is an
open immersion.

This is the depth-transfer half of the flat base-change clause of Stacks 0EY6.

## Main results

* `Stacks.FundamentalGroup.range_eq_preimage_range_of_isPullback` — the range of the base change
  of an open immersion is the inverse image of its range.
* `Stacks.FundamentalGroup.depth_stalk_le_depth_stalk_of_flat` — along a flat morphism to a
  locally Noetherian scheme the depth of a stalk is at least the depth of the stalk below it.
* `Stacks.FundamentalGroup.extendedEtaleDepth_flatBaseChange` — depth at least two outside the
  open subscheme persists after flat base change.

## References

* [Stacks Project, Tag 0EY6](https://stacks.math.columbia.edu/tag/0EY6)
* [Stacks Project, Tag 0337](https://stacks.math.columbia.edu/tag/0337)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u

namespace Stacks.FundamentalGroup

/-- The range of the base change of an open immersion is the inverse image of its range: if
`j' ≫ g = gU ≫ j` is Cartesian and `j` is an open immersion, then a point of `X'` lies in the
image of `j'` exactly when its image under `g` lies in the image of `j`. -/
theorem range_eq_preimage_range_of_isPullback {U X U' X' : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (g : X' ⟶ X) (j' : U' ⟶ X') (gU : U' ⟶ U)
    (hj : IsPullback j' gU g j) :
    Set.range j'.base = (g ⁻¹ᵁ j.opensRange : Set X') := by
  conv_lhs => rw [← hj.isoPullback_hom_fst]
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    show Set.range (hj.isoPullback.hom.base) = Set.univ from
      Set.range_eq_univ.mpr hj.isoPullback.hom.homeomorph.surjective,
    Set.image_univ, IsOpenImmersion.range_pullbackFst j g]

/-- **Depth grows along a flat morphism.** If `g : X' ⟶ X` is flat and `X'` is locally
Noetherian, then for every `x ∈ X'` the depth of `𝒪_{X', x}` is at least the depth of
`𝒪_{X, g(x)}`. This is the inequality contained in the additivity of depth along a flat local
homomorphism (Stacks 0337), applied to the stalk map of `g` at `x`. -/
@[sga "2 III 2.11" "special case"]
theorem depth_stalk_le_depth_stalk_of_flat {X X' : Scheme.{u}} (g : X' ⟶ X) [Flat g]
    [IsLocallyNoetherian X'] (x : X') :
    Module.depth (X.presheaf.stalk (g.base x))
        (IsLocalRing.maximalIdeal (X.presheaf.stalk (g.base x)))
        (X.presheaf.stalk (g.base x)) ≤
      Module.depth (X'.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X'.presheaf.stalk x)) (X'.presheaf.stalk x) := by
  have hflat : (g.stalkMap x).hom.Flat := Flat.stalkMap g x
  have hloc : IsLocalHom (g.stalkMap x).hom := g.toLRSHom.prop x
  algebraize [(g.stalkMap x).hom]
  rw [Module.depth_self_eq_depth_self_add_depth_quotient_map_maximalIdeal
    (X.presheaf.stalk (g.base x)) (X'.presheaf.stalk x)]
  exact le_self_add

/-- **Stacks 0EY6, flat base change: the depth condition.** Depth at least two outside the open
subscheme persists after flat base change: if the local rings of `X` at the points outside the
open `U` have depth at least two and `g : X' ⟶ X` is flat with `U' = g⁻¹(U)`, then the local
rings of `X'` at the points outside `U'` have depth at least two.

This is one of the seven declarations making up tag 0EY6's `flat_base_change` clause. All
seven are now proved — the last was the Cartesian square of relative spectra, in
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.FlatBaseChangeSquare` — so each
carries `@[stacks 0EY6 "flat_base_change"]`, the clause string recording which part of the tag
is covered. -/
@[stacks 0EY6 "flat_base_change"]
theorem extendedEtaleDepth_flatBaseChange {U X U' X' : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X']
    (j : U ⟶ X) [IsOpenImmersion j]
    (g : X' ⟶ X) [Flat g]
    (j' : U' ⟶ X') [IsOpenImmersion j'] (gU : U' ⟶ U)
    (hj : IsPullback j' gU g j)
    (hdepth : ∀ x : X, x ∉ (j.opensRange : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x)) :
    ∀ x' : X', x' ∉ (j'.opensRange : Set X') →
      (2 : ℕ∞) ≤ Module.depth (X'.presheaf.stalk x')
        (IsLocalRing.maximalIdeal (X'.presheaf.stalk x'))
        (X'.presheaf.stalk x') := by
  intro x' hx'
  refine le_trans (hdepth (g.base x') ?_) (depth_stalk_le_depth_stalk_of_flat g x')
  intro hmem
  refine hx' ?_
  rw [Scheme.Hom.coe_opensRange, range_eq_preimage_range_of_isPullback j g j' gU hj]
  exact hmem

end Stacks.FundamentalGroup

end
