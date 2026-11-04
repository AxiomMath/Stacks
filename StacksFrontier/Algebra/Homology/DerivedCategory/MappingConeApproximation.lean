module

public import StacksFrontier.Algebra.Homology.DerivedCategory.TriangleApproximation

/-!
# The mapping cone of a cohomological approximation

Let `A` be an abelian category and `α : K ⟶ L` a morphism of cochain complexes which is an
isomorphism on cohomology in every degree `> m` and a surjection on cohomology in degree `m`.
Then the mapping cone of `α` has vanishing cohomology in every degree `≥ m`.

This is the complex-level form of `DerivedCategory.triangle_obj₃_isLE_of_approximation`, which says
the same thing about the third vertex of a distinguished triangle of `D(A)`.

## Main results

* `CochainComplex.isZero_homology_mappingCone_of_approximation`: the cone of an approximation
  in degree `m` has no cohomology in the degrees `≥ m`.

## Implementation notes

The statement is about `HomologicalComplex.homology` rather than about `D(A)`. The hypothesis
`[HasDerivedCategory.{w} A]` is used only by the proof, which deduces the statement from
`DerivedCategory.triangle_obj₃_isLE_of_approximation`.

## References

* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
* [Stacks Project, Tag 05TC](https://stacks.math.columbia.edu/tag/05TC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {K L : CochainComplex A ℤ} (α : K ⟶ L)

/-- An epimorphism in the image of a functor stays one along a natural isomorphism. -/
private theorem epi_map_of_natIso {D E : Type*} [Category D] [Category E] {F₁ F₂ : D ⥤ E}
    (e : F₁ ≅ F₂) {X Y : D} (f : X ⟶ Y) (h : Epi (F₂.map f)) : Epi (F₁.map f) := by
  have hnat : F₁.map f = e.hom.app X ≫ F₂.map f ≫ e.inv.app Y := by simp
  rw [hnat]
  have := h
  infer_instance

/-- **The mapping cone of a cohomological approximation in degree `m` has no cohomology in the
degrees `≥ m`.**

If `α : K ⟶ L` is an isomorphism on cohomology in every degree `> m` and a surjection on
cohomology in degree `m`, then `H^i(mappingCone α) = 0` for every `i ≥ m`. -/
theorem isZero_homology_mappingCone_of_approximation (m : ℤ)
    (hiso : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j))
    (hepi : Epi (HomologicalComplex.homologyMap α m)) (i : ℤ) (hi : m ≤ i) :
    IsZero ((mappingCone α).homology i) := by
  have hLE : (DerivedCategory.Q.obj (mappingCone α)).IsLE (m - 1) :=
    DerivedCategory.triangle_obj₃_isLE_of_approximation _
      (DerivedCategory.mappingCone_triangle_distinguished α) m
      (fun j hj => (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors A j) α).mpr
        (hiso j hj))
      (epi_map_of_natIso (DerivedCategory.homologyFunctorFactors A m) α hepi)
  have := hLE
  exact (DerivedCategory.isZero_of_isLE _ (m - 1) i (by omega)).of_iso
    ((DerivedCategory.homologyFunctorFactors A i).app (mappingCone α)).symm

end CochainComplex

end
