module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented

/-!
# Density of the point set of the dense open of Stacks 089J

The refined valuative criterion of Stacks 089G, as
`AlgebraicGeometry.Space.isProper_of_refinedValuativeCriterion` takes it, asks that the
auxiliary morphism `V ⟶ X'` have *dense image on points*: dense in the topology of Stacks 03BX
on the point set of `X'`. In Stacks 089J the open `V` is dense in `X'` for a stronger and purely
scheme-theoretic reason — it is scheme-theoretically dense in the scheme-theoretic image `Z`,
by Stacks 01RG — and the two statements are about different spaces: the point set of a presheaf
on the site on one side, the underlying topological space of a scheme on the other.

This file bridges them. The point set of a represented presheaf is homeomorphic to the
underlying space of the representing scheme by Stacks 03BX, clause (1), which is
`AlgebraicGeometry.Space.schemePointsHomeomorph`, and that homeomorphism is natural; so density
of the image on points of a morphism of the site is density of the image of the morphism of
schemes. Dropping from `Z` to the open `X'` is the elementary fact that a dense subset of a
space stays dense in any open subspace containing it.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.denseRange_of_denseRange_comp_isOpenImmersion`: a morphism whose composite
  with an open immersion has dense image has dense image.
* `AlgebraicGeometry.Space.denseRange_pointsMap_yoneda_map_iff`: a morphism of the site has
  dense image on points exactly when the morphism of schemes underlying it has dense image.
* `AlgebraicGeometry.Space.denseRange_pointsMap_yoneda_map_of_comp_isOpenImmersion`: **the
  hypothesis `hdense` of `AlgebraicGeometry.Space.isProper_of_refinedValuativeCriterion`**, from
  dominance of the composite with an open immersion of the site. This is the shape Stacks 089J
  has it in: the composite `V ⟶ X' ⟶ Z` is the morphism onto the scheme-theoretic image, which
  is dominant.

## What is and is not proved

Stacks 089J is **not** proved here and no declaration in this file carries a Stacks attribute:
clause (1) of Stacks 03BX is carried by
`AlgebraicGeometry.Space.schemePointsHomeomorph`, and dominance of the morphism onto a
quasi-compact scheme-theoretic image is Stacks 01RG, carried by
`AlgebraicGeometry.isSchemeTheoreticallyDominant_toImage_of_quasiCompact`.

Dominance of the composite is taken as a hypothesis and not derived; in Stacks 089J it is
`AlgebraicGeometry.Scheme.Hom.isSchemeTheoreticallyDominant_toImage` together with
quasi-compactness of the morphism into the fibre power, which is where the quasi-compactness of
the complement of the diagonals enters. The other four hypotheses of
`AlgebraicGeometry.Space.isProper_of_refinedValuativeCriterion`, and the valuative lifting
condition itself, are not addressed here.

## References

* [Stacks Project, Tag 01RG](https://stacks.math.columbia.edu/tag/01RG)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 089G](https://stacks.math.columbia.edu/tag/089G)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A morphism whose composite with an open immersion has dense image has dense image.** A
nonempty open of the intermediate scheme has open nonempty image in the ambient one, which
therefore meets the image of the composite; the open immersion being injective, the open itself
meets the image of the first morphism.

This is how Stacks 089J passes from scheme-theoretic density of `V` in the scheme-theoretic
image `Z` to density of `V` in the open `X' ⊆ Z` out of which the cover is cut. -/
theorem denseRange_of_denseRange_comp_isOpenImmersion {A T Z : Scheme.{u}} (a : A ⟶ T)
    (b : T ⟶ Z) (hb : IsOpenImmersion b) (h : DenseRange ⇑(a ≫ b)) : DenseRange ⇑a := by
  have hb' := hb
  refine dense_iff_inter_open.2 fun O hO hOne ↦ ?_
  have hOimg : IsOpen (⇑b.base '' O) := hb'.base_open.isOpenMap O hO
  obtain ⟨z, hzO, y, hzy⟩ := dense_iff_inter_open.1 h (⇑b.base '' O) hOimg
    (hOne.image _)
  obtain ⟨x, hxO, hxz⟩ := hzO
  refine ⟨a.base y, ?_, Set.mem_range_self y⟩
  have hinj : Function.Injective ⇑b.base := hb'.base_open.injective
  have key : b.base (a.base y) = b.base x := by
    change (a ≫ b).base y = b.base x
    rw [hzy, ← hxz]
  rw [hinj key]
  exact hxO

namespace Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Density of the image is transported along a commuting square whose sides are
homeomorphisms. -/
private theorem denseRange_of_comm_homeomorph {α α' β β' : Type*} [TopologicalSpace α]
    [TopologicalSpace α'] [TopologicalSpace β]
    [TopologicalSpace β'] {g : α → β} {g' : α' → β'} (eU : α ≃ₜ α') (eV : β ≃ₜ β')
    (hnat : ∀ x, eV (g x) = g' (eU x)) (h : DenseRange g) : DenseRange g' := by
  have h' := eV.surjective.denseRange.comp h eV.continuous
  rwa [show eV ∘ g = g' ∘ eU from funext hnat, DenseRange, eU.surjective.range_comp] at h'

/-- **A morphism of the big fppf category over `S` has dense image on points exactly when the
morphism of schemes underlying it has dense image.**

Clause (1) of Stacks 03BX identifies the point set of a represented presheaf with the
underlying space of the representing scheme, homeomorphically and naturally; the two maps are
therefore conjugate, and density of the image is invariant under conjugating by
homeomorphisms. -/
theorem denseRange_pointsMap_yoneda_map_iff {U V : BigFppfOver B S hS} (f : U ⟶ V) :
    DenseRange (pointsMap B S hS (yoneda.obj U) (yoneda.map f)) ↔
      DenseRange ⇑((BigFppfOver.toScheme B S hS).map f) := by
  set eU := schemePointsHomeomorph B S hS U with heU
  set eV := schemePointsHomeomorph B S hS V with heV
  have hnat : ∀ x, eV (pointsMap B S hS (yoneda.obj U) (yoneda.map f) x) =
      ((BigFppfOver.toScheme B S hS).map f) (eU x) := fun x ↦
    pointsToScheme_pointsMap B S hS f x
  exact ⟨denseRange_of_comm_homeomorph eU eV hnat, denseRange_of_comm_homeomorph eU.symm eV.symm
    fun y ↦ by rw [Homeomorph.symm_apply_eq, hnat, Homeomorph.apply_symm_apply]⟩

/-- **A dominant morphism of the big fppf category over `S` has dense image on points.** -/
theorem denseRange_pointsMap_yoneda_map_of_isDominant {U V : BigFppfOver B S hS} (f : U ⟶ V)
    (h : _root_.AlgebraicGeometry.IsDominant ((BigFppfOver.toScheme B S hS).map f)) :
    DenseRange (pointsMap B S hS (yoneda.obj U) (yoneda.map f)) :=
  (denseRange_pointsMap_yoneda_map_iff B S hS f).2
    ((isDominant_iff ((BigFppfOver.toScheme B S hS).map f)).1 h)

/-- **The hypothesis `hdense` of
`AlgebraicGeometry.Space.isProper_of_refinedValuativeCriterion`, for the dense open of Stacks
089J.**

If the composite of a morphism `a` of the site with an open immersion `b` of the site is
dominant, then `a` has dense image on points. In Stacks 089J this is applied with `a` the
inclusion of the complement of the diagonals into the cover `X' = ⋃ᵢ gᵢ⁻¹(W)`, with `b` the
inclusion of that open into the scheme-theoretic image `Z`, and with the composite the morphism
onto `Z`, which is dominant by Stacks 01RG. -/
theorem denseRange_pointsMap_yoneda_map_of_comp_isOpenImmersion
    {A T Z : BigFppfOver B S hS} (a : A ⟶ T) (b : T ⟶ Z)
    (hb : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map b))
    (h : _root_.AlgebraicGeometry.IsDominant ((BigFppfOver.toScheme B S hS).map (a ≫ b))) :
    DenseRange (pointsMap B S hS (yoneda.obj A) (yoneda.map a)) := by
  refine (denseRange_pointsMap_yoneda_map_iff B S hS a).2 ?_
  refine denseRange_of_denseRange_comp_isOpenImmersion
    ((BigFppfOver.toScheme B S hS).map a) ((BigFppfOver.toScheme B S hS).map b) hb ?_
  rw [← Functor.map_comp]
  exact (isDominant_iff ((BigFppfOver.toScheme B S hS).map (a ≫ b))).1 h

end Space

end AlgebraicGeometry

end
