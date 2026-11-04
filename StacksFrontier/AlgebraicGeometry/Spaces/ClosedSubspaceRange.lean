module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation

/-!
# Closed subschemes of a representable algebraic space

Let `S` be a scheme contained in a big fppf site `B` and let `j : R ⟶ V` be a morphism of the
big fppf category over `S` whose underlying morphism of schemes is a closed immersion. This
file records that the range of `yoneda.map j` is then a closed subspace of `yoneda.obj V`,
which is the dictionary entry turning a closed subscheme of a scheme in the site into a closed
subspace of the algebraic space it represents.

## Main results

* `AlgebraicGeometry.Space.isClosedSubspace_range_yoneda_map`: the range of a morphism of the
  site which is a closed immersion of schemes is a closed subspace of the target.

## Implementation notes

The two clauses of `AlgebraicGeometry.Space.IsClosedSubspace` are discharged separately. Being
an algebraic space transports along the isomorphism `yoneda.obj R ≅ range (yoneda.map j)` given
by `CategoryTheory.Subfunctor.toRange`, which is an isomorphism because `yoneda.map j` is a
monomorphism — the inverse image of a property contained in the monomorphisms is contained in
the monomorphisms, and `CategoryTheory.MorphismProperty.presheaf` of such a property lands in
the monomorphisms of presheaves. The inclusion of the range is a closed immersion because
`yoneda.map j` is one, by `AlgebraicGeometry.BigFppfOver.presheaf_inverseImage_yoneda_map_iff`,
and precomposing with that isomorphism does not change the property.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The range of a morphism of the site which is a closed immersion of schemes is a closed
subspace of the target.** This is the form in which a closed subscheme `R ⊆ V` of a scheme in
the big fppf site over `S` becomes a closed subspace of the algebraic space represented by
`V`. -/
theorem isClosedSubspace_range_yoneda_map {R V : BigFppfOver B S hS} (j : R ⟶ V)
    (hj : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)) :
    IsClosedSubspace B S hS (Subfunctor.range (yoneda.map j)) := by
  classical
  have hpClosed : IsClosedImmersion B S hS (yoneda.map j) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@AlgebraicGeometry.IsClosedImmersion.{u}) j).2 hj
  have hPmono : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) ≤
      MorphismProperty.monomorphisms (BigFppfOver B S hS) := by
    intro A A' g hg
    have : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map g) := hg
    exact ⟨fun {T} g₁ g₂ hgg => Functor.map_injective (BigFppfOver.toScheme B S hS)
      ((cancel_mono ((BigFppfOver.toScheme B S hS).map g)).1
        (congrArg (fun k => (BigFppfOver.toScheme B S hS).map k) hgg))⟩
  have hpMono : Mono (yoneda.map j) :=
    MorphismProperty.presheaf_monomorphisms_le_monomorphisms _
      (MorphismProperty.relative_monotone hPmono _ hpClosed)
  refine ⟨isAlgebraicSpace_of_iso B S hS (asIso (Subfunctor.toRange (yoneda.map j))).symm
    (isAlgebraicSpace_yoneda B S hS R), ?_⟩
  have heq : (asIso (Subfunctor.toRange (yoneda.map j))).inv ≫ yoneda.map j =
      (Subfunctor.range (yoneda.map j)).ι :=
    (Iso.inv_comp_eq _).2 (Subfunctor.toRange_ι _).symm
  exact heq ▸ MorphismProperty.RespectsIso.precomp
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
    (asIso (Subfunctor.toRange (yoneda.map j))).inv (yoneda.map j) hpClosed

end AlgebraicGeometry.Space

end
