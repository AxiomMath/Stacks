module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding

/-!
# The ambient open subspace of a represented immersion is the coborder of its range

An immersion of algebraic spaces `i : Z ⟶ X` over a scheme `S` is a closed immersion into the
open subspace `X ∖ ∂Z` of Stacks 06EC, which `AlgebraicGeometry.Space.immersionAmbient`
constructs as `AlgebraicGeometry.Space.boundaryComplement` of the point set of `i`, that is as
`AlgebraicGeometry.Space.openSubspaceOfPoints` at Mathlib's `coborder` of that point set.  An
immersion of *schemes* `f` is a closed immersion into the open `AlgebraicGeometry.Scheme.Hom
.coborderRange f`, whose point set is `coborder (Set.range f.base)` on the nose.

So for a morphism `j` of the big fppf category over `S` whose underlying morphism of schemes is
an immersion, the two ambients are the same open, read through the Stacks 03BX homeomorphism
`AlgebraicGeometry.Space.schemePointsHomeomorph` between the point space of a represented
presheaf and the representing scheme.  This file proves that, which is a point-set comparison
along that homeomorphism and not a reconstruction of either ambient.

## Main results

* `Homeomorph.preimage_coborder`: a homeomorphism commutes with `coborder` on preimages.
* `AlgebraicGeometry.Space.range_pointsMap_yoneda_map_eq_schemePointsHomeomorph_preimage`: the
  point set of a represented morphism is the preimage, under the Stacks 03BX homeomorphism, of the
  range of the morphism of schemes.
* `AlgebraicGeometry.Space.range_pointsMap_ι_boundaryComplement_yoneda_map`: **the ambient
  match.**  The point set of the complement of the boundary of the point set of a represented
  morphism is the preimage of `AlgebraicGeometry.Scheme.Hom.coborderRange` of the morphism of
  schemes.
* `AlgebraicGeometry.Space.range_pointsMap_ι_immersionAmbient_yoneda_map`: the same, with the
  space side named as `AlgebraicGeometry.Space.immersionAmbient` of the represented immersion.

## Implementation notes

The point topology `AlgebraicGeometry.Space.pointTopology` is installed as a local instance, as
elsewhere in this directory.

`AlgebraicGeometry.Space.boundaryComplement` and
`AlgebraicGeometry.Space.range_pointsMap_ι_boundaryComplement` need no hypothesis on the set of
points, and `AlgebraicGeometry.Space.schemePointsHomeomorph` none on the morphism, so the only
hypothesis below is the one `AlgebraicGeometry.Scheme.Hom.coborderRange` itself requires:
that the morphism of schemes be an immersion.  The space-level immersion hypothesis that
`AlgebraicGeometry.Space.immersionAmbient` asks for is obtained from it by
`AlgebraicGeometry.BigFppfOver.presheaf_inverseImage_yoneda_map_iff`, and the two ambients then
agree definitionally, so the last statement is the second one restated.

## References

* [Stacks Project, Tag 06EC](https://stacks.math.columbia.edu/tag/06EC)
* [Stacks Project, Tag 04CE](https://stacks.math.columbia.edu/tag/04CE)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
-/

@[expose] public section

open CategoryTheory

universe u

/-- **A homeomorphism commutes with `coborder` on preimages.**  Both the closure and the
set-theoretic operations in `coborder s = (closure s \ s)ᶜ` are preserved. -/
theorem Homeomorph.preimage_coborder {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (h : α ≃ₜ β) (s : Set β) : h ⁻¹' coborder s = coborder (h ⁻¹' s) := by
  change h ⁻¹' (closure s \ s)ᶜ = (closure (h ⁻¹' s) \ h ⁻¹' s)ᶜ
  rw [Set.preimage_compl, Set.preimage_sdiff, h.preimage_closure]

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {R V : BigFppfOver B S hS}

/-- **The point set of a represented morphism, as a preimage.**  The lemma
`AlgebraicGeometry.Space.range_pointsMap_yoneda_map` presents it as the image of the range of
the morphism of schemes under the inverse comparison bijection; this is the same set read as a
preimage along the Stacks 03BX homeomorphism, which is the form `Homeomorph.preimage_coborder`
consumes. -/
theorem range_pointsMap_yoneda_map_eq_schemePointsHomeomorph_preimage (j : R ⟶ V) :
    Set.range (pointsMap B S hS (yoneda.obj R) (yoneda.map j)) =
      schemePointsHomeomorph B S hS V ⁻¹'
        Set.range ((BigFppfOver.toScheme B S hS).map j).base := by
  rw [range_pointsMap_yoneda_map, ← Homeomorph.image_symm]
  rfl

/-- **The ambient match.**  For a morphism `j` of the big fppf category over `S` whose underlying
morphism of schemes is an immersion, the point set of the open subspace `X ∖ ∂Z` of Stacks 06EC
attached to the represented morphism is the preimage, under the Stacks 03BX homeomorphism, of the
open `AlgebraicGeometry.Scheme.Hom.coborderRange` through which the morphism of schemes is a
closed immersion.

This is the comparison that reads the space-level ambient of Stacks 04CE as the scheme-level
ambient used by the conormal sheaf of Morphisms, Definition 01R2.  Both are `coborder` of the
point-set range — the space side by
`AlgebraicGeometry.Space.range_pointsMap_ι_boundaryComplement` and the scheme side by
definition — so the only content is that the two point sets correspond, which is
`AlgebraicGeometry.Space.range_pointsMap_yoneda_map`, together with
`Homeomorph.preimage_coborder`. -/
theorem range_pointsMap_ι_boundaryComplement_yoneda_map (j : R ⟶ V)
    [AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map j)] :
    Set.range (pointsMap B S hS
        (boundaryComplement B S hS (yoneda.obj V)
          (Set.range (pointsMap B S hS (yoneda.obj R) (yoneda.map j)))).toFunctor
        (boundaryComplement B S hS (yoneda.obj V)
          (Set.range (pointsMap B S hS (yoneda.obj R) (yoneda.map j)))).ι) =
      schemePointsHomeomorph B S hS V ⁻¹'
        (((BigFppfOver.toScheme B S hS).map j).coborderRange : Set _) := by
  rw [range_pointsMap_ι_boundaryComplement,
    range_pointsMap_yoneda_map_eq_schemePointsHomeomorph_preimage B S hS j,
    show (((BigFppfOver.toScheme B S hS).map j).coborderRange : Set _) =
      coborder (Set.range ((BigFppfOver.toScheme B S hS).map j).base) from rfl,
    Homeomorph.preimage_coborder]

/-- **The ambient match, with the space side named as the ambient of an immersion.**  The point
set of `AlgebraicGeometry.Space.immersionAmbient` of a represented immersion is the preimage,
under the Stacks 03BX homeomorphism, of
`AlgebraicGeometry.Scheme.Hom.coborderRange` of the morphism of schemes.

`AlgebraicGeometry.Space.immersionAmbient` is
`AlgebraicGeometry.Space.boundaryComplement` at the point set of the morphism, so this is the
previous statement; what it adds is the space-level immersion hypothesis, obtained from the
scheme-level one by `AlgebraicGeometry.BigFppfOver.presheaf_inverseImage_yoneda_map_iff`. -/
theorem range_pointsMap_ι_immersionAmbient_yoneda_map (j : R ⟶ V)
    [hj : AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map j)] :
    Set.range (pointsMap B S hS
        (immersionAmbient B S hS (isAlgebraicSpace_yoneda B S hS V)
            (isAlgebraicSpace_yoneda B S hS R) (yoneda.map j)
            ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
              (@AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u}) j).2 hj)).1
        (boundaryComplement B S hS (yoneda.obj V)
          (Set.range (pointsMap B S hS (yoneda.obj R) (yoneda.map j)))).ι) =
      schemePointsHomeomorph B S hS V ⁻¹'
        (((BigFppfOver.toScheme B S hS).map j).coborderRange : Set _) :=
  range_pointsMap_ι_boundaryComplement_yoneda_map B S hS j

end AlgebraicGeometry.Space

end
