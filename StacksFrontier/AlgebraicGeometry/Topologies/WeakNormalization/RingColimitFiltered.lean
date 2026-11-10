module

public import Mathlib.CategoryTheory.Filtered.Basic
public import StacksFrontier.AlgebraicGeometry.Seminormalization.IndexFiltered
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.FilteredColimit

/-!
# The index of the absolute weak normalization diagram is filtered

For a commutative ring `A`, `Algebra.AbsoluteWeakNormalization A` is the colimit of the
finitely presented `A`-algebras whose spectrum morphism to `Spec A` is a universal
homeomorphism. This file proves that the category of those algebras, and hence the small
category `Algebra.AbsoluteWeakNormalizationIndex A` indexing the diagram, is filtered, which
is the hypothesis under which `AlgebraicGeometry.universalHomeomorphism_specMap_of_isColimit`
applies to the colimit.

## Main results

* `AlgebraicGeometry.exists_cocone_objs_absoluteWeakNormalization`: two such algebras have a
  common upper bound, their tensor product over `A`.
* `AlgebraicGeometry.exists_cocone_maps_absoluteWeakNormalization`: two parallel maps are
  equalized by a further map, the quotient of the target by the differences of the two maps on
  a finite generating set of the source.
* `AlgebraicGeometry.absoluteWeakNormalizationIndex_isFiltered`: the index is filtered.
* `AlgebraicGeometry.absoluteWeakNormalization_universalHomeomorphism`: the canonical morphism
  `Spec (Algebra.AbsoluteWeakNormalization A) ⟶ Spec A` is a universal homeomorphism.

## Implementation notes

This is the absolute weak normalization half of the argument carried out for the
seminormalization in `StacksFrontier.AlgebraicGeometry.Seminormalization.IndexFiltered`, and it
reuses the same three geometric inputs: stability of universal homeomorphisms under base
change, in the form of `universalHomeomorphism_specMap_tensorProduct`; the nilpotency of the
difference of two algebra maps out of a universal homeomorphism,
`isNilpotent_sub_of_universalHomeomorphism`; and the fact that a quotient by an ideal of
nilpotents is a universal homeomorphism on spectra. The condition on residue fields, which the
seminormalization carries along and which forces the detour through explicit presentations,
is absent here, so the algebras themselves form the indexing category and no transport along
an algebra isomorphism is needed.

The small index of the diagram is a `CategoryTheory.SmallModel` of that category, so its
filteredness follows by transport along `CategoryTheory.equivSmallModel`.

Everything lives in a single universe `u`, as `AlgebraicGeometry.UniversalHomeomorphism` is
available only for `Scheme.{u}`.

## References

* [Stacks Project, Tag 0EUR](https://stacks.math.columbia.edu/tag/0EUR)
* [Stacks Project, Tag 0CN8](https://stacks.math.columbia.edu/tag/0CN8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

variable (A : Type u) [CommRing A]

/-- Two finitely presented `A`-algebras which are universal homeomorphisms over `A` have a
common upper bound in that category, namely their tensor product over `A`. -/
theorem exists_cocone_objs_absoluteWeakNormalization
    (X Y : (Algebra.absoluteWeakNormalizationObject A).FullSubcategory) :
    Nonempty ((Z : (Algebra.absoluteWeakNormalizationObject A).FullSubcategory) ×
      (X ⟶ Z) × (Y ⟶ Z)) := by
  have hfpX : Algebra.FinitePresentation A (X.obj : Type u) := X.property.1
  have hfpY : Algebra.FinitePresentation A (Y.obj : Type u) := Y.property.1
  have hfp : Algebra.FinitePresentation A ((X.obj : Type u) ⊗[A] (Y.obj : Type u)) :=
    Algebra.FinitePresentation.tensorProduct A _ _
  have huh : UniversalHomeomorphism (Spec.map (CommRingCat.ofHom
      (algebraMap A ((X.obj : Type u) ⊗[A] (Y.obj : Type u))))) :=
    universalHomeomorphism_specMap_tensorProduct A _ _ X.property.2 Y.property.2
  exact ⟨⟨⟨CommAlgCat.of A ((X.obj : Type u) ⊗[A] (Y.obj : Type u)), hfp, huh⟩,
    ⟨CommAlgCat.ofHom Algebra.TensorProduct.includeLeft⟩,
    ⟨CommAlgCat.ofHom Algebra.TensorProduct.includeRight⟩⟩⟩

/-- Two parallel maps of finitely presented `A`-algebras which are universal homeomorphisms
over `A` are equalized by a further map in that category: the quotient of the target by the
differences of the two maps on a finite generating set of the source. -/
theorem exists_cocone_maps_absoluteWeakNormalization
    {X Y : (Algebra.absoluteWeakNormalizationObject A).FullSubcategory} (f g : X ⟶ Y) :
    ∃ (Z : (Algebra.absoluteWeakNormalizationObject A).FullSubcategory) (h : Y ⟶ Z),
      f ≫ h = g ≫ h := by
  classical
  have hfpX : Algebra.FinitePresentation A (X.obj : Type u) := X.property.1
  have hfpY : Algebra.FinitePresentation A (Y.obj : Type u) := Y.property.1
  have hftX : Algebra.FiniteType A (X.obj : Type u) := Algebra.FiniteType.of_finitePresentation
  obtain ⟨s, hs⟩ := hftX.out
  let I : Ideal (Y.obj : Type u) := Ideal.span
    (Set.range fun b : {x : (X.obj : Type u) // x ∈ s} => f.hom.hom b.1 - g.hom.hom b.1)
  have hI_fg : I.FG := Submodule.fg_span (Set.finite_range _)
  have hIle : I ≤ nilradical (Y.obj : Type u) := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨b, rfl⟩
    exact mem_nilradical.2 (isNilpotent_sub_of_universalHomeomorphism A
      (X.obj : Type u) (Y.obj : Type u) X.property.2 f.hom.hom g.hom.hom b.1)
  have hI_nil : ∀ x ∈ I, IsNilpotent x := fun _ hx => mem_nilradical.1 (hIle hx)
  have hfpE : Algebra.FinitePresentation A ((Y.obj : Type u) ⧸ I) :=
    Algebra.FinitePresentation.quotient hI_fg
  let qalg : (Y.obj : Type u) →ₐ[A] (Y.obj : Type u) ⧸ I := Ideal.Quotient.mkₐ A I
  have hquot : UniversalHomeomorphism (Spec.map (CommRingCat.ofHom qalg.toRingHom)) :=
    universalHomeomorphism_specMap_quotient_of_nilpotent (Y.obj : Type u) I hI_nil
  have huh : UniversalHomeomorphism
      (Spec.map (CommRingCat.ofHom (algebraMap A ((Y.obj : Type u) ⧸ I)))) :=
    universalHomeomorphism_specMap_comp_algHom qalg Y.property.2 hquot
  refine ⟨⟨CommAlgCat.of A ((Y.obj : Type u) ⧸ I), hfpE, huh⟩,
    ⟨CommAlgCat.ofHom qalg⟩, ?_⟩
  apply InducedCategory.hom_ext
  apply CommAlgCat.hom_ext
  change qalg.comp f.hom.hom = qalg.comp g.hom.hom
  apply AlgHom.ext_of_adjoin_eq_top hs
  intro b hb
  have hgen : f.hom.hom b - g.hom.hom b ∈ I := Ideal.subset_span ⟨⟨b, hb⟩, rfl⟩
  have hzero : qalg (f.hom.hom b - g.hom.hom b) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hgen
  have hzero' : qalg (f.hom.hom b) - qalg (g.hom.hom b) = 0 := by
    simpa only [map_sub] using hzero
  exact sub_eq_zero.mp hzero'

/-- The base ring is itself a finitely presented `A`-algebra which is a universal
homeomorphism over `A`, so that category is nonempty. -/
theorem nonempty_absoluteWeakNormalizationObject :
    Nonempty (Algebra.absoluteWeakNormalizationObject A).FullSubcategory := by
  have hA : CommRingCat.ofHom (algebraMap A A) = 𝟙 (CommRingCat.of A) := by
    apply CommRingCat.hom_ext
    ext a
    simp
  have huh : UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A A))) := by
    rw [hA, Spec.map_id]
    exact universalHomeomorphism_of_isIso _
  exact ⟨⟨CommAlgCat.of A A, Algebra.FinitePresentation.self A, huh⟩⟩

/-- The finitely presented `A`-algebras which are universal homeomorphisms over `A` form a
filtered category. -/
instance absoluteWeakNormalizationObject_isFiltered :
    IsFiltered (Algebra.absoluteWeakNormalizationObject A).FullSubcategory where
  cocone_objs X Y := by
    obtain ⟨Z, u, v⟩ := exists_cocone_objs_absoluteWeakNormalization A X Y
    exact ⟨Z, u, v, trivial⟩
  cocone_maps _ _ f g := exists_cocone_maps_absoluteWeakNormalization A f g
  nonempty := nonempty_absoluteWeakNormalizationObject A

/-- **The index of the absolute weak normalization diagram is filtered.** -/
instance absoluteWeakNormalizationIndex_isFiltered :
    IsFiltered (Algebra.AbsoluteWeakNormalizationIndex A) :=
  IsFiltered.of_equivalence
    (equivSmallModel.{u} (Algebra.absoluteWeakNormalizationObject A).FullSubcategory)

/-- **Stacks 0EUR.** The canonical morphism from the spectrum of the absolute weak
normalization of `A` to `Spec A` is a universal homeomorphism. -/
theorem absoluteWeakNormalization_universalHomeomorphism :
    UniversalHomeomorphism (Spec.map (CommRingCat.ofHom
      (algebraMap A (Algebra.AbsoluteWeakNormalization A)))) :=
  universalHomeomorphism_specMap_of_isColimit A (Algebra.absoluteWeakNormalizationDiagram A)
    (colimit.cocone _) (colimit.isColimit _) fun _ => inferInstance

end AlgebraicGeometry

end
