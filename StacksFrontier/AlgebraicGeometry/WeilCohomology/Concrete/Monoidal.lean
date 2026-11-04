module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.TrivialSection
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# The symmetric monoidal category of smooth projective schemes over a field

Before Stacks 0FG7 the source equips the smooth projective schemes over a field `k` with the
tensor product `X ⊗ Y = X × Y`, the product over `k`, with unit `Spec(k)`. It takes the usual
associativity constraint of products of schemes and the factor switch `X × Y ⟶ Y × X` as the
commutativity constraint. This file constructs that symmetric monoidal structure on the category
`Stacks.WeilCohomology.(SmoothProjectiveScheme k).FullSubcategory` of smooth projective schemes
over `k`, which is the object category of the category of correspondences.

## Main definitions

* `Stacks.WeilCohomology.SmoothProjectiveScheme.isMonoidal`: smooth projective schemes form a
  monoidal property of objects of `Over (Spec k)` for the cartesian monoidal structure
  (`CategoryTheory.Over.cartesianMonoidalCategory`). The unit `Spec k ⟶ Spec k` is smooth and
  projective, and so is the fibre product of two smooth projective schemes over `k`.
* The instances `MonoidalCategory`, `BraidedCategory` and `SymmetricCategory` on
  `Stacks.WeilCohomology.(SmoothProjectiveScheme k).FullSubcategory`, inherited from
  `Over (Spec k)`.

## Main results

* `Stacks.WeilCohomology.SmoothProjectiveScheme.tensorObj_left`,
  `Stacks.WeilCohomology.SmoothProjectiveScheme.tensorObj_hom`,
  `Stacks.WeilCohomology.SmoothProjectiveScheme.tensorUnit_left` and
  `Stacks.WeilCohomology.SmoothProjectiveScheme.tensorUnit_hom` describe the tensor product: the
  fibre product `X ×_k Y` with its first projection followed by the structure morphism of `X`,
  and the unit `Spec k` with its identity.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.isProjectiveMorphism_id_spec`: the identity of
  `Spec k` is H-projective. It is a closed immersion into `ℙ⁰_k` over `k`, because a section of a
  morphism to a one-point scheme is a closed immersion.

## Implementation notes

The cartesian monoidal structure on `Over (Spec k)` is the `abbrev`
`CategoryTheory.Over.cartesianMonoidalCategory`, deliberately not a global instance in Mathlib.
It is switched on locally here and used only to produce the instances on the full subcategory
of smooth projective schemes, so no instance on `Over (Spec k)` leaks out of this file.

## References

* [Stacks Project, Tag 0FG7](https://stacks.math.columbia.edu/tag/0FG7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

universe u

namespace Stacks.WeilCohomology

namespace SmoothProjectiveScheme

variable (k : Type u) [Field k]

/-- The identity of `Spec k` is H-projective: a section `Spec k ⟶ ℙ⁰_k` of the projection is a
closed immersion, because `Spec k` has a single point. -/
theorem isProjectiveMorphism_id_spec : IsProjectiveMorphism (𝟙 (Spec (.of k))) := by
  obtain ⟨s, hs⟩ := Stacks.ProjectiveBundleSplitting.exists_section_projectiveSpaceOver 0
    (Spec (.of k))
  exact ⟨0, s, isClosedImmersion_of_comp_eq_id _ s hs, hs⟩

/-- An H-projective morphism stays H-projective after base change, read on the *first*
projection: `pullback.fst f g` is projective when `g` is. -/
theorem isProjectiveMorphism_pullback_fst {X Y S : Scheme.{u}} (f : X ⟶ S) {g : Y ⟶ S}
    (hg : IsProjectiveMorphism g) : IsProjectiveMorphism (Limits.pullback.fst f g) :=
  IsProjectiveMorphism.of_iso (pullbackSymmetry g f) (Iso.refl X)
    (by simp) (hg.baseChange f)

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

/-- Smooth projective schemes over `k` are closed under the cartesian monoidal structure of
`Over (Spec k)`: the unit `Spec k` is smooth and projective over `k`, and so is the fibre product
of two smooth projective schemes over `k`. -/
instance isMonoidal : (SmoothProjectiveScheme k).IsMonoidal where
  prop_unit := ⟨by
    rw [Over.tensorUnit_hom]
    have : IsOpenImmersion (𝟙 (Spec (.of k))) := inferInstance
    infer_instance, by
    rw [Over.tensorUnit_hom]; exact (isProjectiveMorphism_id_spec k).isProjective⟩
  prop_tensor X Y hX hY := by
    have := hX.1
    have := hY.1
    refine ⟨by rw [Over.tensorObj_hom]; infer_instance, ?_⟩
    rw [Over.tensorObj_hom]
    exact ((isProjectiveMorphism_pullback_fst X.hom
      ((AlgebraicGeometry.isProjective_iff_isProjectiveMorphism_of_isAffine _).1 hY.2)).comp
      ((AlgebraicGeometry.isProjective_iff_isProjectiveMorphism_of_isAffine _).1 hX.2)).isProjective

/-- **The monoidal category of smooth projective schemes over `k`**: `X ⊗ Y = X ×_k Y`, with
unit `Spec k` and the associativity and unit constraints of products of schemes. -/
instance monoidalCategory : MonoidalCategory ((SmoothProjectiveScheme k).FullSubcategory) :=
  ObjectProperty.fullMonoidalSubcategory _

/-- Smooth projective schemes over `k` are braided by the factor switch `X ×_k Y ≅ Y ×_k X`. -/
instance braidedCategory : BraidedCategory ((SmoothProjectiveScheme k).FullSubcategory) :=
  ObjectProperty.fullBraidedSubcategory _

/-- **The symmetric monoidal category of smooth projective schemes over `k`**, with unit
`Spec k`, tensor product the product over `k`, and the factor switch as the commutativity
constraint. -/
instance symmetricCategory : SymmetricCategory ((SmoothProjectiveScheme k).FullSubcategory) :=
  ObjectProperty.fullSymmetricSubcategory _

variable {k}

/-- The tensor product of two smooth projective schemes is their fibre product over `k`. -/
@[simp]
theorem tensorObj_left (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    (X ⊗ Y).obj.left = Limits.pullback X.obj.hom Y.obj.hom :=
  rfl

/-- The structure morphism of `X ⊗ Y` is the first projection followed by that of `X`. -/
@[simp]
theorem tensorObj_hom (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    (X ⊗ Y).obj.hom = Limits.pullback.fst X.obj.hom Y.obj.hom ≫ X.obj.hom :=
  rfl

/-- The unit of the tensor product is `Spec k`. -/
@[simp]
theorem tensorUnit_left : (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.left = Spec (.of k)
    :=
  rfl

/-- The structure morphism of the unit is the identity of `Spec k`. -/
@[simp]
theorem tensorUnit_hom : (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom = 𝟙
    (Spec (.of k)) :=
  rfl

/-- The structure morphism of the monoidal unit `Spec k` is an isomorphism. -/
instance isIso_tensorUnit_hom : IsIso (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
    := by
  rw [tensorUnit_hom]; exact IsIso.id _

/-- The underlying morphism of schemes of a tensor product of morphisms is the induced morphism
of fibre products. -/
theorem tensorHom_hom_left {X₁ Y₁ X₂ Y₂ : (SmoothProjectiveScheme k).FullSubcategory} (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) :
    (f ⊗ₘ g).hom.left =
      Limits.pullback.map X₁.obj.hom X₂.obj.hom Y₁.obj.hom Y₂.obj.hom f.hom.left g.hom.left
        (𝟙 _) (by simp) (by simp) :=
  rfl

/-- The underlying morphism of schemes of the commutativity constraint is the factor switch. -/
theorem braiding_hom_hom_left (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    (β_ X Y).hom.hom.left = (pullbackSymmetry X.obj.hom Y.obj.hom).hom :=
  rfl

end SmoothProjectiveScheme

end Stacks.WeilCohomology

end
