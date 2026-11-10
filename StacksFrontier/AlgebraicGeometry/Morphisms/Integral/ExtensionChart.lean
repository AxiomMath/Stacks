module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FppfApplication.IntegralSurjectiveExtension
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasicoherentSubobjectGluing.FiniteTypeCover

/-!
# Charts for the integral extension of a morphism over an open subscheme

`AlgebraicGeometry.exists_integral_surjective_extension` — the quasi-compact case of
[Stacks, Tag 0CNX] — extends a surjective integral morphism `f : V ⟶ U` over an open
subscheme `U` of `S` to a surjective integral morphism `a : A ⟶ S`, and records the
comparison as an isomorphism `Over.mk f ≅ (Over.pullback U.ι).obj (Over.mk a)` in
`CategoryTheory.Over U.toScheme`. Its consumers need two things that the statement in that
form does not hand over directly.

The first is a supply of opens to which it applies at all: its hypothesis is
`QuasiCompact U.ι`, which is strictly stronger than `U` being a quasi-compact open — the
preimage of *every* quasi-compact open of `S` has to be quasi-compact. On a quasi-separated
scheme the two agree, so on such a scheme every point of every open has an affine
neighbourhood inside that open to which the extension applies.

The second is the comparison in geometric rather than categorical form: an open immersion
`d : V ⟶ A` over `S` whose image is exactly `a ⁻¹ᵁ U`. This is what identifies `V` as the
part of the extension lying over `U`, and it is the shape in which the proof of
[Stacks, Tag 0CNZ] consumes Tag 0CNX.

## Main results

* `AlgebraicGeometry.exists_isAffineOpen_quasiCompact_ι_mem_le`: on a quasi-separated scheme
  every point of an open has an affine neighbourhood inside it whose inclusion is
  quasi-compact.
* `AlgebraicGeometry.exists_integral_surjective_extension_isOpenImmersion`: the quasi-compact
  case of [Stacks, Tag 0CNX] with the comparison presented as an open immersion of `V` into
  the extension, with its image computed.

## Implementation notes

Nothing here is tagged. The first result is a general fact with no Stacks tag of its own, and the
second is the same statement as `AlgebraicGeometry.exists_integral_surjective_extension`, which
carries the retrocompactness hypothesis that [Stacks, Tag 0CNX] leaves implicit. The general
statement of 0CNX is false and that declaration is its corrected (retrocompact) form, so the
hypothesis cannot be removed. See the module documentation of
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.FppfApplication.IntegralSurjectiveExtension`.

The isomorphism produced by Tag 0CNX lives in `CategoryTheory.Over U.toScheme`, so its
underlying morphism of schemes is `CategoryTheory.Over.Hom.left` of its forward direction.
That morphism is an isomorphism, which is obtained from the two `Over`-level identities by
`CategoryTheory.Over.comp_left`; the image of the resulting composite with
`CategoryTheory.Limits.pullback.fst` is then computed from
`AlgebraicGeometry.IsOpenImmersion.range_pullbackFst`.

## References

* [Stacks Project, Tag 0CNX](https://stacks.math.columbia.edu/tag/0CNX)
* [Stacks Project, Tag 0CNZ](https://stacks.math.columbia.edu/tag/0CNZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- On a quasi-separated scheme every point of an open subscheme has an affine open
neighbourhood contained in it whose inclusion is a quasi-compact morphism, so that
`AlgebraicGeometry.exists_integral_surjective_extension` applies to it. -/
theorem exists_isAffineOpen_quasiCompact_ι_mem_le {S : Scheme.{u}} [QuasiSeparatedSpace S]
    (U : S.Opens) {x : S} (hx : x ∈ U) :
    ∃ W : S.Opens, IsAffineOpen W ∧ x ∈ W ∧ W ≤ U ∧ QuasiCompact W.ι := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
  exact ⟨W, hW, hxW, hWU, quasiCompact_ι_of_isCompact W hW.isCompact⟩

/-- The quasi-compact case of [Stacks, Tag 0CNX], with the comparison over `U` presented
geometrically: a surjective integral morphism `f : V ⟶ U` over an open subscheme `U` of `S`
extends to a surjective integral morphism `a : A ⟶ S` for which `V` is an open subscheme of
`A` over `S`, with image exactly the preimage of `U`.

This is the form in which the proof of [Stacks, Tag 0CNZ] uses Tag 0CNX: the extension of a
member of a Zariski covering is glued to the rest of the construction along that open
immersion, and the computation of its image is what makes the resulting family of opens cover
the total space. -/
theorem exists_integral_surjective_extension_isOpenImmersion {S : Scheme.{u}} (U : S.Opens)
    [QuasiCompact U.ι] {V : Scheme.{u}} (f : V ⟶ U.toScheme) [IsIntegralHom f] [Surjective f] :
    ∃ (A : Scheme.{u}) (a : A ⟶ S), IsIntegralHom a ∧ Surjective a ∧
      ∃ d : V ⟶ A, IsOpenImmersion d ∧ d ≫ a = f ≫ U.ι ∧
        Set.range d.base = (a ⁻¹ᵁ U : Set A) := by
  obtain ⟨A, a, ha, hasurj, ⟨e⟩⟩ := exists_integral_surjective_extension U f
  have he : IsIso e.hom.left :=
    ⟨⟨e.inv.left, by simp [← Over.comp_left, e.hom_inv_id],
      by simp [← Over.comp_left, e.inv_hom_id]⟩⟩
  have hw : e.hom.left ≫ pullback.snd a U.ι = f := Over.w e.hom
  have hsurj : Function.Surjective e.hom.left.base :=
    (TopCat.homeoOfIso (asIso e.hom.left.base)).surjective
  refine ⟨A, a, ha, hasurj, e.hom.left ≫ pullback.fst a U.ι, inferInstance, ?_, ?_⟩
  · calc (e.hom.left ≫ pullback.fst a U.ι) ≫ a
        = e.hom.left ≫ pullback.snd a U.ι ≫ U.ι := by
          rw [Category.assoc, pullback.condition]
      _ = f ≫ U.ι := by rw [← Category.assoc, hw]
  · rw [Scheme.Hom.comp_base]
    change Set.range ((pullback.fst a U.ι).base ∘ e.hom.left.base) = _
    rw [Set.range_comp, Set.range_eq_univ.mpr hsurj, Set.image_univ,
      IsOpenImmersion.range_pullbackFst, Scheme.Opens.opensRange_ι]

end AlgebraicGeometry

end
