module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.IndQuasiAffine.Characterization
public import StacksFrontier.AlgebraicGeometry.CompactOpenSuperset

/-!
# Composites and factors of ind-quasi-affine morphisms

Ind-quasi-affine morphisms of schemes are stable under composition, and the first factor of an
ind-quasi-affine composite is ind-quasi-affine.

## Main results

* `AlgebraicGeometry.isIndQuasiAffineHom_comp` and
  `AlgebraicGeometry.isIndQuasiAffineHom_isStableUnderComposition`: a composite of
  ind-quasi-affine morphisms is ind-quasi-affine.
* `AlgebraicGeometry.isIndQuasiAffineHom_of_comp`: if `f ≫ g` is ind-quasi-affine then so
  is `f`.

## References

* [Stacks Project, Tag 0F1V](https://stacks.math.columbia.edu/tag/0F1V)
* [Stacks Project, Tag 0F1X](https://stacks.math.columbia.edu/tag/0F1X)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The composite of two ind-quasi-affine morphisms of schemes is ind-quasi-affine. -/
instance isIndQuasiAffineHom_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsIndQuasiAffineHom f] [IsIndQuasiAffineHom g] : IsIndQuasiAffineHom (f ≫ g) := by
  classical
  have hf4 := ((isIndQuasiAffineHom_tfae f).out 1 4).mp ‹IsIndQuasiAffineHom f›
  refine ⟨fun V hV => ?_⟩
  rw [Scheme.Hom.comp_preimage]
  have hV' : IsIndQuasiAffine (g ⁻¹ᵁ V).toScheme :=
    IsIndQuasiAffineHom.isIndQuasiAffine_preimage V hV
  refine ⟨fun U hU => ?_⟩
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  obtain ⟨W₀, hKW₀, hW₀c⟩ := exists_opens_superset_isCompact
    (hU.image (f ∣_ (g ⁻¹ᵁ V)).continuous)
  have hW₀qa : W₀.toScheme.IsQuasiAffine := hV'.isQuasiAffine W₀ hW₀c
  have hWqa : ((g ⁻¹ᵁ V).ι ''ᵁ W₀).toScheme.IsQuasiAffine :=
    Scheme.IsQuasiAffine.of_isAffineHom ((g ⁻¹ᵁ V).ι.isoImage W₀).inv
  have hWc : IsCompact (((g ⁻¹ᵁ V).ι ''ᵁ W₀ : Y.Opens) : Set Y) :=
    hW₀c.image (g ⁻¹ᵁ V).ι.continuous
  have hWqs : IsQuasiSeparated (((g ⁻¹ᵁ V).ι ''ᵁ W₀ : Y.Opens) : Set Y) :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ ((g ⁻¹ᵁ V).ι ''ᵁ W₀).isOpen).mpr
      (show QuasiSeparatedSpace ((g ⁻¹ᵁ V).ι ''ᵁ W₀).toScheme from inferInstance)
  have hOP : (f ⁻¹ᵁ (g ⁻¹ᵁ V)).ι ''ᵁ U ≤ f ⁻¹ᵁ ((g ⁻¹ᵁ V).ι ''ᵁ W₀) := by
    rw [← image_morphismRestrict_preimage f (g ⁻¹ᵁ V) W₀]
    exact Scheme.Hom.image_mono _ fun x hx => hKW₀ (Set.mem_image_of_mem _ hx)
  set U' : (f ⁻¹ᵁ ((g ⁻¹ᵁ V).ι ''ᵁ W₀)).toScheme.Opens :=
    (f ⁻¹ᵁ ((g ⁻¹ᵁ V).ι ''ᵁ W₀)).ι ⁻¹ᵁ ((f ⁻¹ᵁ (g ⁻¹ᵁ V)).ι ''ᵁ U)
  set eU : U.toScheme ≅ U'.toScheme :=
    (f ⁻¹ᵁ (g ⁻¹ᵁ V)).ι.isoImage U ≪≫ (Scheme.Opens.isoOfLE hOP).symm
  have hU'c : CompactSpace U'.toScheme := (TopCat.homeoOfIso (asIso eU.hom.base)).compactSpace
  have : IsQuasiAffineHom (U'.ι ≫ f ∣_ ((g ⁻¹ᵁ V).ι ''ᵁ W₀)) :=
    hf4 _ hWc hWqs U' (isCompact_iff_compactSpace.mpr hU'c)
  have : U'.toScheme.IsQuasiAffine :=
    Scheme.IsQuasiAffine.of_isQuasiAffineHom (U'.ι ≫ f ∣_ ((g ⁻¹ᵁ V).ι ''ᵁ W₀))
  exact Scheme.IsQuasiAffine.of_isAffineHom eU.hom

/-- Being an ind-quasi-affine morphism of schemes is stable under composition. -/
@[stacks 0F1V]
instance isIndQuasiAffineHom_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition
      (@IsIndQuasiAffineHom : MorphismProperty Scheme.{u}) where
  comp_mem f g hf hg := @isIndQuasiAffineHom_comp _ _ _ f g hf hg

/-- If the composite `f ≫ g` of two morphisms of schemes is ind-quasi-affine, then `f` is
ind-quasi-affine. -/
@[stacks 0F1X]
theorem isIndQuasiAffineHom_of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsIndQuasiAffineHom (f ≫ g)] : IsIndQuasiAffineHom f := by
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict fun y => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g y)) isOpen_univ
  refine ⟨g ⁻¹ᵁ U, hyU, ?_⟩
  have : IsIndQuasiAffine ((f ≫ g) ⁻¹ᵁ U).toScheme :=
    IsIndQuasiAffineHom.isIndQuasiAffine_preimage U hU
  have : IsIndQuasiAffine (f ⁻¹ᵁ (g ⁻¹ᵁ U)).toScheme := by
    rwa [← Scheme.Hom.comp_preimage]
  exact isIndQuasiAffineHom_of_isIndQuasiAffine_source (f ∣_ (g ⁻¹ᵁ U))

end AlgebraicGeometry

end
