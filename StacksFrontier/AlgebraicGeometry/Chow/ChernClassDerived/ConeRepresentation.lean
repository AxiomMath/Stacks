module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.Defined
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# The cone of a lift represents the derived pullback of the third vertex

Let `f : Y ⟶ X` be a morphism of schemes and let `E₁ ⟶ E₂ ⟶ E₃ ⟶ E₁[1]` be a distinguished
triangle of `D(𝒪_X)`. Suppose the morphism `Lf^*E₁ ⟶ Lf^*E₂` has been lifted to a morphism
`α : P₁ ⟶ P₂` of complexes of `𝒪_Y`-modules, in the sense that `P₁` and `P₂` represent `Lf^*E₁`
and `Lf^*E₂` compatibly with `α`. Then the cone `C(α)^•` represents `Lf^*E₃`.

This is the third paragraph of the proof of Stacks 0F9F, and the argument is two applications of
the triangulated machinery and nothing else: `Lf^*` is exact, so it carries the given triangle to
a distinguished triangle of `D(𝒪_Y)` whose third vertex is `Lf^*E₃`; the standard cone triangle
of `α` is distinguished in `D(𝒪_Y)`; and the two triangles agree on their first morphism under
the given isomorphisms, so they are isomorphic, so their third vertices are isomorphic.

## Main results

* `Stacks.Chow.derivedPullback_obj₃_iso_mappingCone` — for a distinguished triangle given as a
  single `Triangle` object: `Lf^*T.obj₃ ≅ C(α)^•`.
* `Stacks.Chow.derivedPullback_iso_mappingCone_of_dist` — the same for a triangle presented as
  three objects and three morphisms.

## Implementation notes

The conclusion is `Nonempty (· ≅ ·)` rather than an isomorphism because
`Stacks.Chow.EnvelopePresentation.representation`, the field this feeds, is stated that way; and
the isomorphism produced here is a choice anyway, since
`CategoryTheory.Pretriangulated.isoTriangleOfIso₁₂` rests on a choice of filler of a square.

The compatibility hypothesis is written in the `hom` direction,
`e₁.hom ≫ Q(α) = Lf^*(T.mor₁) ≫ e₂.hom`, which is literally the square that
`isoTriangleOfIso₁₂` consumes, read backwards. The `inv` direction
`e₁.inv ≫ Lf^*(T.mor₁) = Q(α) ≫ e₂.inv` says the same thing.

Both statements need the standard model of the derived category, because that is the model the
exactness of `Lf^*` and the envelope presentations of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.Defined` are stated at; the local instance
priority beats the globally available locally small model.

Two spellings are forced by instance resolution. The cone is written with its type ascribed,
`(CochainComplex.mappingCone α : CochainComplex Y.Modules ℤ)`: without it the category of the
cone is fixed by unification against the derived pullback on the left of the isomorphism, at
which spelling the binary biproducts that `HomologicalComplex.HasHomotopyCofiber` needs are not
found. And exactness is used by applying the field of
`Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_isTriangulated` to the morphism by hand
rather than through `CategoryTheory.Functor.map_distinguished`, which would have to re-synthesize
that instance together with the commutation with the shift it depends on, and does not.

## References

* [Stacks Project, Tag 0F9F](https://stacks.math.columbia.edu/tag/0F9F)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Pretriangulated

universe u

namespace Stacks.Chow

-- The standard model of the derived category is the one the exactness of `Lf^*` and the envelope
-- presentations of `Defined.lean` are stated at. The priority beats the locally small model:
-- that one is a global instance, so without it the statements here would be about an unrelated
-- model.
attribute [local instance 10000] HasDerivedCategory.standard

/-- **Stacks 0F9F, third paragraph.** Let `T` be a distinguished triangle of `D(𝒪_X)` and let
`α : P₁ ⟶ P₂` be a morphism of complexes of `𝒪_Y`-modules together with isomorphisms
`e₁ : Lf^*T.obj₁ ≅ P₁` and `e₂ : Lf^*T.obj₂ ≅ P₂` identifying `α` with `Lf^*T.mor₁`. Then the
mapping cone of `α` represents `Lf^*T.obj₃`.

Both `Lf^*T` and the cone triangle of `α` are distinguished — the first because `Lf^*` is exact,
the second because it is the standard triangle of a morphism of complexes — and `e₁`, `e₂`
identify their first morphisms, so the two triangles are isomorphic. -/
theorem derivedPullback_obj₃_iso_mappingCone {X Y : Scheme.{u}} (f : Y ⟶ X)
    (T : Triangle (DerivedCategory X.Modules))
    (hT : T ∈ distTriang (DerivedCategory X.Modules))
    {P₁ P₂ : CochainComplex Y.Modules ℤ} (α : P₁ ⟶ P₂)
    (e₁ : (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      f.toLRSHom.toShHom).obj T.obj₁ ≅ DerivedCategory.Q.obj P₁)
    (e₂ : (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      f.toLRSHom.toShHom).obj T.obj₂ ≅ DerivedCategory.Q.obj P₂)
    (hα : e₁.hom ≫ DerivedCategory.Q.map α =
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        f.toLRSHom.toShHom).map T.mor₁ ≫ e₂.hom) :
    Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      f.toLRSHom.toShHom).obj T.obj₃ ≅
      DerivedCategory.Q.obj (CochainComplex.mappingCone α :
        CochainComplex Y.Modules ℤ)) :=
  ⟨Triangle.π₃.mapIso (isoTriangleOfIso₁₂ _ _
    ((Cohomology.KFlatDerivedPullback.derivedPullback_isTriangulated
      f.toLRSHom.toShHom).map_distinguished T hT)
    (DerivedCategory.mappingCone_triangle_distinguished α) e₁ e₂ hα.symm)⟩

/-- **Stacks 0F9F, third paragraph**, for a distinguished triangle presented as three objects
`E₁`, `E₂`, `E₃` and three morphisms `u`, `v`, `w`. If `α : P₁ ⟶ P₂` lifts `Lf^*u` through
isomorphisms `Lf^*E₁ ≅ P₁` and `Lf^*E₂ ≅ P₂`, then the mapping cone of `α` represents
`Lf^*E₃`. -/
theorem derivedPullback_iso_mappingCone_of_dist {X Y : Scheme.{u}} (f : Y ⟶ X)
    {E₁ E₂ E₃ : DerivedCategory X.Modules} (u : E₁ ⟶ E₂) (v : E₂ ⟶ E₃)
    (w : E₃ ⟶ E₁⟦(1 : ℤ)⟧)
    (hT : Triangle.mk u v w ∈ distTriang (DerivedCategory X.Modules))
    {P₁ P₂ : CochainComplex Y.Modules ℤ} (α : P₁ ⟶ P₂)
    (e₁ : (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      f.toLRSHom.toShHom).obj E₁ ≅ DerivedCategory.Q.obj P₁)
    (e₂ : (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      f.toLRSHom.toShHom).obj E₂ ≅ DerivedCategory.Q.obj P₂)
    (hα : e₁.hom ≫ DerivedCategory.Q.map α =
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        f.toLRSHom.toShHom).map u ≫ e₂.hom) :
    Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      f.toLRSHom.toShHom).obj E₃ ≅
      DerivedCategory.Q.obj (CochainComplex.mappingCone α :
        CochainComplex Y.Modules ℤ)) :=
  derivedPullback_obj₃_iso_mappingCone f (Triangle.mk u v w) hT α e₁ e₂ hα

end Stacks.Chow

end
