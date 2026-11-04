module

public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Every morphism of a full subcategory is strongly cartesian over its image

Let `C` be a category and `P : ObjectProperty C`. The inclusion `P.ι : P.FullSubcategory ⥤ C` is
fully faithful, and that alone makes *every* morphism `f` of `P.FullSubcategory` strongly cartesian
for `P.ι` over its own image `P.ι.map f`: the lift required by the universal property is produced
by fullness and is unique by faithfulness, with no condition on `P`.

This is what identifies the site that a full subcategory inherits from an ambient site. The
covering families of `CategoryTheory.Functor.inheritedPrecoverage` (Stacks 06NU) for a functor `p`
are the families of strongly `p`-cartesian morphisms whose images cover downstairs; specialised to
`p = P.ι` the cartesian clause is automatic by the instance below, so the coverings of
`P.ι.inheritedTopology J` are exactly the families of morphisms of `P.FullSubcategory` which are
coverings in the ambient site. That is the description a full subcategory of a site is normally
given by.

## Main results

* `CategoryTheory.ObjectProperty.instIsStronglyCartesianIotaMap`: every morphism of
  `P.FullSubcategory` is strongly `P.ι`-cartesian over its image.
-/

@[expose] public section

namespace CategoryTheory.ObjectProperty

universe v u

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)

/-- Every morphism `f` of a full subcategory is strongly cartesian for the inclusion
`P.ι` over its own image `P.ι.map f`.

Only full faithfulness of `P.ι` is used: given a competitor `f' : a' ⟶ y` lifting `g ≫ P.ι.map f`,
fullness turns `g` into the required morphism `a' ⟶ x`, and faithfulness gives both the
factorisation and its uniqueness. -/
public instance instIsStronglyCartesianIotaMap {x y : P.FullSubcategory} (f : x ⟶ y) :
    P.ι.IsStronglyCartesian (P.ι.map f) f where
  universal_property' {a'} g f' hf' := by
    have hg : P.ι.IsHomLift g (P.ι.preimage g) :=
      IsHomLift.of_fac' (p := P.ι) g _ rfl rfl (by simpa using P.ι.map_preimage g)
    refine ⟨P.ι.preimage g, ⟨hg, ?_⟩, ?_⟩
    · refine P.ι.map_injective ?_
      rw [P.ι.map_comp, P.ι.map_preimage]
      exact IsHomLift.eq_of_isHomLift (p := P.ι) (g ≫ P.ι.map f) f'
    · rintro χ ⟨hχ, hχ2⟩
      refine P.ι.map_injective ?_
      rw [P.ι.map_preimage]
      exact (IsHomLift.eq_of_isHomLift (p := P.ι) g χ).symm

end CategoryTheory.ObjectProperty

end
