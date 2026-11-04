module

public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace

/-!
# The fibre of a morphism of represented algebraic spaces

Let `α : W ⟶ V` be a morphism of the big fppf site of a scheme `S` and let `p` be a
field-valued point of the algebraic space `h_V` it represents. The fibre of `h_α` over `p` is
the presheaf fibre product `h_W ×_{h_V} h_{p.siteObject}`; since Yoneda preserves fibre products
and `p` presents a morphism `p.siteObject ⟶ V` of the site, that fibre product is *represented*,
by the fibre product `W ×_V p.siteObject` formed in the site. The functor from the site to
schemes preserves fibre products too, so the representing scheme of the fibre is the fibre
product of the representing schemes; and when `p` is the canonical representative above a point
`v` of the scheme representing `V`, the morphism it presents is
`AlgebraicGeometry.Scheme.fromSpecResidueField v`, so the representing scheme of the fibre is the
scheme-theoretic fibre `AlgebraicGeometry.Scheme.Hom.fiber` at `v`.

## Main definitions

* `AlgebraicGeometry.Space.fibreRepresentedIso`: the identification of the fibre of `h_α` over a
  field-valued point `p` of `h_V` with the algebraic space of `W ×_V p.siteObject`.

## Main results

* `AlgebraicGeometry.Space.isPullback_yoneda_fibreAtFieldValuedPoint`: the square of
  representables over `h_α` and the morphism presented by `p` is a pullback square.
* `AlgebraicGeometry.Space.fibreRepresentedIso_hom_comp_projection`: the identification is
  compatible with the projection to the source.
* `AlgebraicGeometry.Space.isPullback_toScheme_fibre`: the representing scheme of the fibre is
  the fibre product of the representing schemes.
* `AlgebraicGeometry.Space.isPullback_toScheme_fibre_schemePointRepresentative`: over the residue
  field of a point `v` of the target scheme, that fibre product is the scheme-theoretic fibre
  at `v`.

## Implementation notes

No `@[stacks]` attribute is claimed here: everything in this file is the Lean-side dictionary
between the fibre of Stacks 0AC8 formed in presheaves and the fibre products of the site and of
schemes, and none of it is a numbered result of the source.

Preservation of fibre products by Yoneda is a Mathlib instance, and preservation by the functor
to schemes is `AlgebraicGeometry.Space.preservesLimitsOfShape_walkingCospan_toScheme`. That the
morphism of schemes presented by the canonical representative above `v` is
`AlgebraicGeometry.Scheme.fromSpecResidueField v` is
`AlgebraicGeometry.Space.toScheme_map_siteHom_schemePointRepresentative`.

## References

* [Stacks Project, Tag 0AC8](https://stacks.math.columbia.edu/tag/0AC8)
* [Stacks Project, Tag 021U](https://stacks.math.columbia.edu/tag/021U)
* [Stacks Project, Tag 03BV](https://stacks.math.columbia.edu/tag/03BV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {W V : BigFppfOver B S hS}

/-- The fibre of a morphism of represented algebraic spaces over a field-valued point of the
target is represented by the fibre product formed in the site. -/
theorem isPullback_yoneda_fibreAtFieldValuedPoint (α : W ⟶ V)
    (p : FieldValuedPoint B S hS (yoneda.obj V)) :
    IsPullback (yoneda.map (pullback.fst α p.siteHom))
      (yoneda.map (pullback.snd α p.siteHom))
      (yoneda.map α) (fieldMorphism B S hS (yoneda.obj V) p) := by
  rw [fieldMorphism_yoneda]
  exact (IsPullback.of_hasPullback α p.siteHom).map yoneda

/-- The identification of the fibre of `h_α` over a field-valued point `p` of `h_V` with the
algebraic space of the fibre product `W ×_V p.siteObject` formed in the site. -/
noncomputable def fibreRepresentedIso (α : W ⟶ V)
    (p : FieldValuedPoint B S hS (yoneda.obj V)) :
    schemeSpace (pullback α p.siteHom) ≅
      fibreAtFieldValuedPoint B S hS (schemeSpaceMap α) p :=
  ObjectProperty.isoMk _ (isPullback_yoneda_fibreAtFieldValuedPoint B S hS α p).isoPullback

/-- The underlying morphism of presheaves of the identification. -/
theorem fibreRepresentedIso_hom_hom (α : W ⟶ V)
    (p : FieldValuedPoint B S hS (yoneda.obj V)) :
    (fibreRepresentedIso B S hS α p).hom.hom =
      (isPullback_yoneda_fibreAtFieldValuedPoint B S hS α p).isoPullback.hom :=
  rfl

/-- The identification is compatible with the projection to the source. -/
theorem fibreRepresentedIso_hom_comp_projection (α : W ⟶ V)
    (p : FieldValuedPoint B S hS (yoneda.obj V)) :
    (fibreRepresentedIso B S hS α p).hom ≫
        fibreAtFieldValuedPointProjection B S hS (schemeSpaceMap α) p =
      schemeSpaceMap (pullback.fst α p.siteHom) :=
  ObjectProperty.hom_ext _
    (isPullback_yoneda_fibreAtFieldValuedPoint B S hS α p).isoPullback_hom_fst

/-- The underlying scheme of the fibre product formed in the site is the fibre product of the
underlying schemes. -/
theorem isPullback_toScheme_fibre (α : W ⟶ V)
    (p : FieldValuedPoint B S hS (yoneda.obj V)) :
    IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.fst α p.siteHom))
      ((BigFppfOver.toScheme B S hS).map (pullback.snd α p.siteHom))
      ((BigFppfOver.toScheme B S hS).map α)
      ((BigFppfOver.toScheme B S hS).map p.siteHom) := by
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  exact (IsPullback.of_hasPullback α p.siteHom).map _

/-- **The underlying scheme of the fibre of `h_α` over the residue field of a point `v` of the
target scheme is the scheme-theoretic fibre of the representing morphism at `v`.** -/
theorem isPullback_toScheme_fibre_schemePointRepresentative (α : W ⟶ V)
    (v : (BigFppfOver.toScheme B S hS).obj V) :
    IsPullback ((BigFppfOver.toScheme B S hS).map
        (pullback.fst α (schemePointRepresentative B S hS V v).siteHom))
      ((BigFppfOver.toScheme B S hS).map
        (pullback.snd α (schemePointRepresentative B S hS V v).siteHom))
      ((BigFppfOver.toScheme B S hS).map α)
      (((BigFppfOver.toScheme B S hS).obj V).fromSpecResidueField v) := by
  have h := isPullback_toScheme_fibre B S hS α (schemePointRepresentative B S hS V v)
  rwa [toScheme_map_siteHom_schemePointRepresentative B S hS V v] at h

end AlgebraicGeometry.Space

end
