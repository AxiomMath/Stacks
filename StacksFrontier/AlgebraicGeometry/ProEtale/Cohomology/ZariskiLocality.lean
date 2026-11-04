module

public import Mathlib.CategoryTheory.Sites.LocalProperties

/-!
# Locality of isomorphisms of sheaves along a family covering the final object

A family of objects of a site which covers the final object detects isomorphisms of sheaves of
types: a morphism of sheaves is invertible as soon as it is bijective on the sections over every
object lying over some member of the family. This file records that criterion, its extension
from a single morphism of sheaves to a natural transformation of sheaf-valued functors, and the
transport of a covering family along a cover-preserving functor.

These are the three ingredients of a descent along a covering family of the final object. They
are applied in
`StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.DirectImageDescent` to the counit of the
direct-image adjunction on small pro-étale sheaves, where the covering family is the base change
of a Zariski open cover of the target; nothing here is specific to the pro-étale situation.

## Main results

* `AlgebraicGeometry.ProEtale.coversTop_map_of_coverPreserving`: the image of a family covering
  the final object under a cover-preserving functor again covers the final object, provided the
  target site has a weakly final object in the image.
* `AlgebraicGeometry.ProEtale.isIso_of_bijective_of_coversTop`: a morphism of sheaves of types
  is an isomorphism when it is bijective on sections over every object admitting a morphism to
  some member of a family covering the final object.
* `AlgebraicGeometry.ProEtale.isIso_natTrans_of_bijective_of_coversTop`: the same criterion for
  a natural transformation of functors valued in sheaves of types, applied componentwise.

## Implementation notes

The locality of invertibility is `CategoryTheory.Sheaf.isIso_of_coversTop`, which reduces
invertibility to invertibility of the pullbacks to the localized sites `K.over (V i)`. Because
`CategoryTheory.GrothendieckTopology.overPullback` is the direct image along
`CategoryTheory.Over.forget`, the sections of such a pullback over an object `W` of `Over (V i)`
are the sections of the original sheaf over `W.left`; this is why the hypothesis above is stated
as bijectivity over the objects `Z` equipped with a morphism `Z ⟶ V i`, with no reference to a
localized site.

`coversTop_map_of_coverPreserving` is stated with an explicit weakly final object rather than
with a terminal object, since the base change of a final object of the small pro-étale site is
only canonically weakly final.

## References

* [Stacks Project, Tag 09AA](https://stacks.math.columbia.edu/tag/09AA)
* [Stacks Project, Tag 09BL](https://stacks.math.columbia.edu/tag/09BL)
* [Stacks Project, Tag 09BN](https://stacks.math.columbia.edu/tag/09BN)
* [Stacks Project, Tag 04D6](https://stacks.math.columbia.edu/tag/04D6)
-/

@[expose] public section

open CategoryTheory Opposite

universe w v₁ v₂ u₁ u₂

namespace AlgebraicGeometry.ProEtale

/-- Let `u : C ⥤ D` be cover-preserving, let `V` be a family of objects of `C` covering the final
object, and let `X` be an object of `C` such that every object of `D` admits a morphism to
`u.obj X`. Then the image family `u.obj ∘ V` covers the final object of `D`. -/
theorem coversTop_map_of_coverPreserving {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (u : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (hu : CoverPreserving J K u) {ι : Type*} {V : ι → C} (hV : J.CoversTop V)
    {X : C} (hX : ∀ Y : D, Nonempty (Y ⟶ u.obj X)) :
    K.CoversTop fun i => u.obj (V i) := by
  intro Y
  obtain ⟨g⟩ := hX Y
  have hpush : (Sieve.ofObjects V X).functorPushforward u ∈ K (u.obj X) :=
    hu.cover_preserve (hV X)
  have hle : (Sieve.ofObjects V X).functorPushforward u ≤
      Sieve.ofObjects (fun i => u.obj (V i)) (u.obj X) := by
    rintro Z a ⟨W, b, c, ⟨i, ⟨d⟩⟩, -⟩
    exact ⟨i, ⟨c ≫ u.map d⟩⟩
  have hmem : Sieve.ofObjects (fun i => u.obj (V i)) (u.obj X) ∈ K (u.obj X) :=
    K.superset_covering hle hpush
  simpa only [Sieve.pullback_ofObjects] using K.pullback_stable g hmem

/-- A morphism of sheaves of types is an isomorphism as soon as it is bijective on the sections
over every object admitting a morphism to a member of a family covering the final object. -/
theorem isIso_of_bijective_of_coversTop {C : Type u₁} [Category.{v₁} C]
    {K : GrothendieckTopology C} {ι : Type*} {V : ι → C} (hV : K.CoversTop V)
    {F G : Sheaf K (Type w)} (φ : F ⟶ G)
    (h : ∀ (i : ι) (Z : C), (Z ⟶ V i) → Function.Bijective (φ.hom.app (op Z))) :
    IsIso φ := by
  refine Sheaf.isIso_of_coversTop hV fun i => ?_
  rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
  intro W
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ?_
  exact h i W.unop.left W.unop.hom

/-- A natural transformation of functors valued in sheaves of types is an isomorphism as soon as
each of its components is bijective on the sections over every object admitting a morphism to a
member of a family covering the final object. -/
theorem isIso_natTrans_of_bijective_of_coversTop {C : Type u₁} [Category.{v₁} C]
    {K : GrothendieckTopology C} {ι : Type*} {V : ι → C} (hV : K.CoversTop V)
    {D : Type u₂} [Category.{v₂} D] {E E' : D ⥤ Sheaf K (Type w)} (α : E ⟶ E')
    (h : ∀ (X : D) (i : ι) (Z : C), (Z ⟶ V i) →
      Function.Bijective ((α.app X).hom.app (op Z))) :
    IsIso α := by
  have happ : ∀ X : D, IsIso (α.app X) := fun X =>
    isIso_of_bijective_of_coversTop hV (α.app X) (h X)
  exact NatIso.isIso_of_isIso_app α

end AlgebraicGeometry.ProEtale

end
