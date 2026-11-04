module

public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.HomologyComparisonCriteria

/-!
# The counit of an adjunction on cochain complexes, in cohomology

Let `G₀ ⊣ H₀` be an adjunction between abelian categories, with `G₀ : B ⥤ A` exact and
`H₀ : A ⥤ B` left exact.  For a cochain complex `K` of `A` the counit
`G₀(H₀ K) ⟶ K` of the induced adjunction on complexes
(`CategoryTheory.Adjunction.mapHomologicalComplexAdjunction`) is, in degree-`q` cohomology, the
composite

`H^q(G₀ H₀ K) ≅ G₀(H^q(H₀ K)) ⟶ G₀ H₀ (H^q K) ⟶ H^q K`

of the homology comparison of the exact functor `G₀`, `G₀` applied to the homology comparison of
`H₀`, and the counit at `H^q K`.  So it is invertible in cohomology as soon as the comparison of
`H₀` at `K` and the counit at `H^q K` are.

## Main results

All in the namespace `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison`:

* `isIso_homologyComparison_of_exact`: the homology comparison of an exact functor is invertible.
* `homologyMap_counit_eq`: the factorisation above.
* `isIso_homologyMap_counit_of_isIso_homologyComparison`: the counit is invertible in
  degree-`q` cohomology when the comparison of `H₀` at `K` and the counit at `H^q K` are.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.HypercohomologyEdge.HomologyComparison

section Exact

variable {A B : Type*} [Category* A] [Abelian A] [Category* B] [Abelian B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- **The homology comparison of an exact functor is invertible**: an exact functor carries the
cokernel presentation `K^{q-1} ⟶ Z^q K ⟶ H^q K ⟶ 0` to a cokernel presentation. -/
theorem isIso_homologyComparison_of_exact (K : CochainComplex A ℤ) (q : ℤ) :
    IsIso (homologyComparison F K q) := by
  obtain ⟨hex, -⟩ := (ShortComplex.exact_and_epi_g_iff_g_is_cokernel
    (ShortComplex.mk (K.toCycles (q - 1) q) (K.homologyπ q)
      (K.toCycles_comp_homologyπ (q - 1) q))).2 ⟨K.homologyIsCokernel (q - 1) q (by simp)⟩
  exact isIso_homologyComparison_of_exact_of_epi F K q (hex.map F)
    (inferInstance : Epi (F.map (K.homologyπ q)))

end Exact

variable {A B : Type*} [Category* A] [Abelian A] [Category* B] [Abelian B]
  {G₀ : B ⥤ A} {H₀ : A ⥤ B} [G₀.Additive] [PreservesFiniteLimits G₀]
  [PreservesFiniteColimits G₀] [H₀.Additive] [PreservesFiniteLimits H₀] (adj : G₀ ⊣ H₀)

/-- On cycles, a morphism of complexes `G₀(H₀ K) ⟶ K` which is the counit in every degree is the
composite of the two cycles comparisons with the counit at the cycles. -/
lemma cyclesMap_eq_of_f_eq_counit (K : CochainComplex A ℤ)
    (c : (G₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((H₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ⟶ K)
    (hc : ∀ n, c.f n = adj.counit.app (K.X n)) (q : ℤ) :
    HomologicalComplex.cyclesMap c q =
      cyclesComparison G₀ ((H₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) q ≫
        G₀.map (cyclesComparison H₀ K q) ≫ adj.counit.app (K.cycles q) := by
  apply (cancel_mono (K.iCycles q)).1
  rw [HomologicalComplex.cyclesMap_i, hc, Category.assoc, Category.assoc,
    ← adj.counit_naturality, ← G₀.map_comp_assoc,
    cyclesComparison_comp_map_iCycles, cyclesComparison_comp_map_iCycles_assoc]

/-- In degree-`q` cohomology, a morphism of complexes `G₀(H₀ K) ⟶ K` which is the counit in every
degree is the composite of the homology comparison of `G₀` at `H₀ K`, `G₀` applied to the
homology comparison of `H₀` at `K`, and the counit at `H^q K`. -/
theorem homologyMap_eq_of_f_eq_counit (K : CochainComplex A ℤ)
    (c : (G₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((H₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ⟶ K)
    (hc : ∀ n, c.f n = adj.counit.app (K.X n)) (q : ℤ) :
    HomologicalComplex.homologyMap c q =
      homologyComparison G₀ ((H₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) q ≫
        G₀.map (homologyComparison H₀ K q) ≫ adj.counit.app (K.homology q) := by
  apply (cancel_epi (HomologicalComplex.homologyπ _ q)).1
  rw [HomologicalComplex.homologyπ_naturality, cyclesMap_eq_of_f_eq_counit adj K c hc,
    homologyπ_comp_homologyComparison_assoc, ← G₀.map_comp_assoc,
    homologyπ_comp_homologyComparison, G₀.map_comp, Category.assoc, Category.assoc,
    Category.assoc]
  congr 2
  exact (adj.counit.naturality (K.homologyπ q)).symm

/-- **The counit of the adjunction on complexes, in degree-`q` cohomology**, is the composite of
the homology comparison of `G₀` at `H₀ K`, `G₀` applied to the homology comparison of `H₀` at `K`,
and the counit at `H^q K`. -/
theorem homologyMap_counit_eq (K : CochainComplex A ℤ) (q : ℤ) :
    HomologicalComplex.homologyMap
        ((Adjunction.mapHomologicalComplexAdjunction adj (ComplexShape.up ℤ)).counit.app K) q =
      homologyComparison G₀ ((H₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) q ≫
        G₀.map (homologyComparison H₀ K q) ≫ adj.counit.app (K.homology q) :=
  homologyMap_eq_of_f_eq_counit adj K _ (fun _ => rfl) q

/-- **The counit of the adjunction on complexes is invertible in degree-`q` cohomology** when the
homology comparison of `H₀` at `K` and the counit at `H^q K` are invertible. -/
theorem isIso_homologyMap_counit_of_isIso_homologyComparison (K : CochainComplex A ℤ) (q : ℤ)
    (h₁ : IsIso (homologyComparison H₀ K q)) (h₂ : IsIso (adj.counit.app (K.homology q))) :
    IsIso (HomologicalComplex.homologyMap
      ((Adjunction.mapHomologicalComplexAdjunction adj (ComplexShape.up ℤ)).counit.app K) q) := by
  have := isIso_homologyComparison_of_exact G₀
    ((H₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) q
  rw [homologyMap_counit_eq]
  infer_instance

end Stacks.Cohomology.HypercohomologyEdge.HomologyComparison

end
