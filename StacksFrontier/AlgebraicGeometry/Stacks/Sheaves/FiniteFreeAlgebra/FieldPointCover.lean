module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.FieldCover
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.UniversalBaseChange

/-!
# Every degree-`d` cover of the spectrum of a field is a base change of the universal cover

Let `K` be a field, `d` positive, and `p : Z ⟶ Spec K` finite locally free of degree `d`. Then
there is a point of the scheme of structure constants of **Stacks 05YM** along which the universal
degree-`d` cover pulls back to `p`.

This is the geometric content of the surjectivity clause of **Stacks 026O** for the category
`ℋ_d` of degree-`d` finite locally free covers, in the form **Stacks 06D4** asks for it: that
clause is equivalent, by **Stacks 06D7**, to surjectivity on objects, which tests only objects
over spectra of fields and allows passing to a field extension. No extension is needed — over a
field the cover is already the spectrum of the algebra of a structure, by
`AlgebraicGeometry.FiniteFreeAlgebra.exists_structure_overIsoSpecCover_of_field`, and the cover
of a structure is a base change of the universal cover, by
`AlgebraicGeometry.FiniteFreeAlgebra.exists_point_isPullback_universalFiniteCoverMap`.

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.exists_point_isPullback_universalFiniteCoverMap_of_field`:
  a degree-`d` finite locally free cover of the spectrum of a field is a base change of the
  universal degree-`d` cover.

## Implementation notes

The structure produced over the field `K` and the structure needed over the global sections of
`Spec K` differ by the ring isomorphism `AlgebraicGeometry.Scheme.ΓSpecIso`. Extending scalars
along it is handled by `AlgebraicGeometry.FiniteFreeAlgebra.isPullback_specCover_map`: the
comparison square it produces has an isomorphism along the bottom, so
`CategoryTheory.IsPullback.isIso_fst_of_isIso` makes its top an isomorphism, and
`AlgebraicGeometry.Scheme.isoSpec_Spec_inv` identifies that bottom isomorphism with the one the
base-change statement is phrased against. No separate transport of structures is needed.

No `@[stacks]` attribute is placed here. The surjectivity clause of Stacks 026O is a statement
about the 1-morphism `AlgebraicGeometry.Stack.finiteCoverUniversalAtlas`, as the relative
property of **Stacks 03YK** for surjectivity of morphisms of algebraic spaces; this is the
statement about schemes which that clause rests on.

## References

* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 05YM](https://stacks.math.columbia.edu/tag/05YM)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
* [Stacks Project, Tag 06D4](https://stacks.math.columbia.edu/tag/06D4)
* [Stacks Project, Tag 06D7](https://stacks.math.columbia.edu/tag/06D7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FiniteFreeAlgebra

/-- **Every degree-`d` finite locally free cover of the spectrum of a field is a base change of
the universal degree-`d` cover.** There is a point of the spectrum of the global sections of the
scheme of structure constants along which the universal cover pulls back to the given cover. -/
theorem exists_point_isPullback_universalFiniteCoverMap_of_field {K : Type u} [Field K]
    {Z : Scheme.{u}} (p : Z ⟶ Spec (.of K)) (d : ℕ) [NeZero d]
    (hp : Stacks.Morphisms.IsFiniteLocallyFreeOfRank p d) :
    ∃ (pt : Spec (.of K) ⟶ Spec (.of Γ(FiniteFreeAlgebra.scheme.{u} d, ⊤)))
      (g : Z ⟶ (specCover (universalStructure.{u} d)).left),
      IsPullback g p (specCover (universalStructure.{u} d)).hom pt := by
  obtain ⟨m, ⟨eo⟩⟩ := exists_structure_overIsoSpecCover_of_field p d hp
  obtain ⟨pt, g, hpb⟩ := exists_point_isPullback_universalFiniteCoverMap d (Spec (.of K))
    (map (Scheme.ΓSpecIso (.of K)).inv.hom m)
  have : IsIso (Spec.map (CommRingCat.ofHom (Scheme.ΓSpecIso (.of K)).inv.hom)) := by
    change IsIso (Spec.map (Scheme.ΓSpecIso (.of K)).inv)
    infer_instance
  have hsq := isPullback_specCover_map (Scheme.ΓSpecIso (.of K)).inv.hom m
  have := hsq.isIso_fst_of_isIso
  have hbot : Spec.map (CommRingCat.ofHom (Scheme.ΓSpecIso (.of K)).inv.hom) =
      (Spec (CommRingCat.of K)).isoSpec.inv :=
    (Scheme.isoSpec_Spec_inv (CommRingCat.of K)).symm
  have hwi : (Over.forget (Spec (CommRingCat.of K))).map eo.inv ≫ p = (specCover m).hom :=
    Over.w eo.inv
  obtain ⟨e₁, he₁⟩ : ∃ e₁ : (specCover (map (Scheme.ΓSpecIso (.of K)).inv.hom m)).left ≅ Z,
      e₁.hom ≫ p = (specCover (map (Scheme.ΓSpecIso (.of K)).inv.hom m)).hom ≫
        (Spec (CommRingCat.of K)).isoSpec.inv := by
    refine ⟨asIso (Spec.map (CommRingCat.ofHom
        (Carrier.mapRingHom (Scheme.ΓSpecIso (.of K)).inv.hom m))) ≪≫
      ((Over.forget (Spec (CommRingCat.of K))).mapIso eo).symm, ?_⟩
    simp only [Iso.trans_hom, asIso_hom, Iso.symm_hom, Functor.mapIso_inv, Category.assoc]
    rw [hwi, ← hbot]
    exact hsq.w
  exact ⟨pt, e₁.inv ≫ g, hpb.of_iso e₁ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simpa using he₁.symm) (by simp) (by simp)⟩

end AlgebraicGeometry.FiniteFreeAlgebra

end
