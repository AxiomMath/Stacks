module

public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexComparisonLocalization
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.YonedaKernelAcyclicCompact

/-!
# `Φ⁻¹ N = Ac` for the complexes of an abelian category

Let `A` be an abelian category, `C = Comp^dg(A)` the differential graded category of cochain
complexes of Tag 09L9, and `Ac = ` `CochainComplex.dgCategoryKAcyclic A` the acyclic objects of
`K(C)`. For a family `G : ι → C.Obj` let `Z = Φ⁻¹ N` be the subcategory
`DGCategory.RightModule.yonedaInverseImage C G` at which the chain `(*)` of [Stacks, Tag 09LK]
localizes. If every `G i` is acyclic and `G` meets every acyclic object up to isomorphism, then
`Z = Ac`. The tautological enumeration of the acyclic objects is such a family, and for it the
functor `Φ'⁻¹ ⋙ L` is a localization of `K(C)` at `Z.trW` for every localization `L` of the
ordinary homotopy category at the acyclics.

## Main definitions

* `CochainComplex.dgCategoryKAcyclicEnum`: the tautological enumeration of the acyclic objects
  of `K(Comp^dg(A))` by the subtype they form.

## Main results

* `DGCategory.RightModule.yonedaInverseImage_eq_dgCategoryKAcyclic`: `Z = Ac` for a family `G`
  of acyclics meeting every acyclic object.
* `DGCategory.RightModule.yonedaInverseImage_dgCategoryKAcyclicEnum`: `Z = Ac` for the
  tautological enumeration.
* `DGCategory.RightModule.comparisonInverse_comp_isLocalization_yonedaInverseImage`: for the
  tautological enumeration, `Φ'⁻¹ ⋙ L` is a localization of `K(Comp^dg(A))` at `Z.trW`.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK)
* [Stacks Project, Tag 09L9](https://stacks.math.columbia.edu/tag/09L9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u

namespace CochainComplex

variable (A : Type u) [Category.{u} A] [Abelian A]

attribute [local implicit_reducible] DGCategory.K

/-- **The tautological enumeration of the acyclic objects of `K(Comp^dg(A))`**: the family
`ι → (Comp^dg(A)).Obj`, with `ι` the subtype of acyclic objects, given by the first projection. -/
def dgCategoryKAcyclicEnum (X : Subtype (dgCategoryKAcyclic A)) : (dgCategory A).Obj := X.1

/-- **There is an acyclic object**: the subtype of acyclic objects of `K(Comp^dg(A))` is
nonempty. -/
instance nonempty_subtype_dgCategoryKAcyclic :
    Nonempty (Subtype (dgCategoryKAcyclic A)) :=
  ((dgCategoryKAcyclic A).exists_prop_of_nonempty).elim fun X hX ↦ ⟨⟨X, hX⟩⟩

end CochainComplex

namespace DGCategory

namespace RightModule

attribute [local implicit_reducible] DGCategory.K

variable (A : Type u) [Category.{u} A] [Abelian A]
  [((yonedaDGFunctor (CochainComplex.dgCategory A)).onK).CommShift ℤ]
  [((yonedaDGFunctor (CochainComplex.dgCategory A)).onK).IsTriangulated]

/-- **`Z = Ac` for the complexes of an abelian category.** Let `G : ι → Comp^dg(A)` be a family
of complexes, indexed by a nonempty `ι : Type u`, each of which is acyclic and which meets every
acyclic object of `K(Comp^dg(A))` up to isomorphism. Then the subcategory `Z = Φ⁻¹ N` at which
the chain `(*)` of [Stacks, Tag 09LK] localizes is exactly the acyclic objects. -/
theorem yonedaInverseImage_eq_dgCategoryKAcyclic {ι : Type u}
    (G : ι → (CochainComplex.dgCategory A).Obj) [Nonempty ι]
    (hG : ∀ X : (CochainComplex.dgCategory A).K, CochainComplex.dgCategoryKAcyclic A X →
      ∃ i, Nonempty (X ≅ (G i : (CochainComplex.dgCategory A).K)))
    (hGAc : ∀ i, CochainComplex.dgCategoryKAcyclic A
      (G i : (CochainComplex.dgCategory A).K)) :
    yonedaInverseImage (CochainComplex.dgCategory A) G =
      CochainComplex.dgCategoryKAcyclic A :=
  yonedaInverseImage_eq_of_isTriangulated (CochainComplex.dgCategory A) G
    (CochainComplex.dgCategoryKAcyclic A) hG hGAc

/-- **`Z = Ac` for the tautological enumeration** `CochainComplex.dgCategoryKAcyclicEnum` of the
acyclic objects. -/
theorem yonedaInverseImage_dgCategoryKAcyclicEnum :
    yonedaInverseImage (CochainComplex.dgCategory A)
        (CochainComplex.dgCategoryKAcyclicEnum A) =
      CochainComplex.dgCategoryKAcyclic A :=
  yonedaInverseImage_eq_dgCategoryKAcyclic A (CochainComplex.dgCategoryKAcyclicEnum A)
    (fun X hX ↦ ⟨⟨X, hX⟩, ⟨Iso.refl _⟩⟩) fun i ↦ i.2

/-- **The localization of the chain of [Stacks, Tag 09LK].** Let
`L : K(A) ⥤ D` be a localization of the ordinary homotopy category at the acyclic-cone
morphisms — for instance `CategoryTheory.DerivedCategory.Qh`. Then `Φ'⁻¹ ⋙ L`, for `Φ'` the
comparison equivalence of Tag 09L9, is a localization of `K(Comp^dg(A))` at `Z.trW` for
`Z = Φ⁻¹ N` taken at the tautological enumeration of the acyclics. -/
instance comparisonInverse_comp_isLocalization_yonedaInverseImage {D : Type*} [Category D]
    (L : HomotopyCategory A (ComplexShape.up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.subcategoryAcyclic A).trW] :
    ((CochainComplex.homotopyCategoryEquivalence A).inverse ⋙ L).IsLocalization
      (yonedaInverseImage (CochainComplex.dgCategory A)
        (CochainComplex.dgCategoryKAcyclicEnum A)).trW := by
  rw [yonedaInverseImage_dgCategoryKAcyclicEnum]
  infer_instance

end RightModule

end DGCategory

end
