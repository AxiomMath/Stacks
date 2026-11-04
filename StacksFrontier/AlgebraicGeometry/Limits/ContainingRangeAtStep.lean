module

public import StacksFrontier.AlgebraicGeometry.Limits.CommonStage

/-!
# Factoring through an open subscheme and containment of the image

A morphism of schemes factors through an open subscheme exactly when its image lies inside it.
Consequently [Stacks, Tag 0E21] holds in the form where the image of the family of points
`Spec A ⟶ W` is contained in the affine nonvanishing open `X_s`, for every scheme, granted the
single-affine step of Noetherian approximation.

## Main results

* `AlgebraicGeometry.range_subset_of_exists_factorsThrough`: a morphism that factors through an
  open subscheme has its image inside it.
* `AlgebraicGeometry.exists_factorsThrough_iff_range_subset`: factoring through an open subscheme
  and having image inside it are equivalent.
* `exists_affine_nonvanishingOpen_containing_range_of_isOneAffineOpenStep`, in the namespace
  `AlgebraicGeometry.Scheme.Modules`: for an ample invertible sheaf `L` on a scheme `X` and a
  family of points `Spec A ⟶ W` of an open `W`, some positive tensor power of `L` has a section
  whose nonvanishing open is affine, contained in `W`, and contains the image of `Spec A`,
  granted `AlgebraicGeometry.Scheme.FiniteTypeApproximation.IsOneAffineOpenStep`.

## References

* [Stacks Project, Tag 0E21](https://stacks.math.columbia.edu/tag/0E21)
* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe v u

namespace AlgebraicGeometry

/-- A morphism that factors through an open subscheme has its image inside that open. -/
theorem range_subset_of_exists_factorsThrough {X Z : Scheme.{u}} (U : X.Opens) (g : Z ⟶ X)
    (h : ∃ g' : Z ⟶ (U : Scheme.{u}), g' ≫ U.ι = g) :
    Set.range g.base ⊆ (U : Set X) := by
  obtain ⟨g', rfl⟩ := h
  rintro _ ⟨z, rfl⟩
  exact (g'.base z).property

/-- A morphism factors through an open subscheme exactly when its image lies inside it. -/
theorem exists_factorsThrough_iff_range_subset {X Z : Scheme.{u}} (U : X.Opens) (g : Z ⟶ X) :
    (∃ g' : Z ⟶ (U : Scheme.{u}), g' ≫ U.ι = g) ↔ Set.range g.base ⊆ (U : Set X) :=
  ⟨range_subset_of_exists_factorsThrough U g, exists_factorsThrough_of_range_subset U g⟩

namespace Scheme.Modules

open Stacks.SheafOfModules Stacks.SheafOfModules.Invertible

/-- Let `L` be an ample invertible sheaf on a scheme `X`, let `W ⊆ X` be open and let
`Spec A ⟶ W` be a family of points of `W` parametrised by an integral algebra over a field.
Granted the single-affine step of Noetherian approximation `hstep`, some positive tensor power of
`L` has a global section `s` whose nonvanishing open `X_s` is affine, is contained in `W`, and
contains the image of `Spec A`. -/
theorem exists_affine_nonvanishingOpen_containing_range_of_isOneAffineOpenStep
    (hstep : Scheme.FiniteTypeApproximation.IsOneAffineOpenStep.{u})
    (k : Type v) (A : Type u) [Field k] [CommRing A] [Algebra k A] [Algebra.IsIntegral k A]
    (X : Scheme.{u}) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (hL : IsAmple X L)
    (W : X.Opens) (f : Spec (CommRingCat.of A) ⟶ (W : Scheme.{u})) :
    ∃ n : ℕ, 0 < n ∧
      ∃ s : (tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L (n : ℤ)).sections,
        IsAffineOpen (nonvanishingOpen (X := X.toLocallyRingedSpace.toRingedSpace)
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s) ∧
        nonvanishingOpen (X := X.toLocallyRingedSpace.toRingedSpace)
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s ≤ W ∧
        Set.range (f ≫ W.ι) ⊆
          (nonvanishingOpen (X := X.toLocallyRingedSpace.toRingedSpace)
            (tensorPower X.toRingedSpace.presheaf
              (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s : Set X) := by
  obtain ⟨n, hn, s, U, rfl, haff, hUW, hfac⟩ :=
    exists_affine_nonvanishingOpen_factorsThrough_of_isOneAffineOpenStep hstep k A X L hL W f
  exact ⟨n, hn, s, haff, hUW, range_subset_of_exists_factorsThrough _ (f ≫ W.ι) hfac⟩

end Scheme.Modules

end AlgebraicGeometry

end
