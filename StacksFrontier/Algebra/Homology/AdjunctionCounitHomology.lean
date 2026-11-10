module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.Adjunction
public import StacksFrontier.Algebra.Homology.RightExactHomologyComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EdgeMorphismOnARingedSite

/-!
# Cohomology of the counit of an adjunction with an exact left adjoint

Let `L ⊣ G` be an adjunction between abelian categories with `L` exact, and let `X` be a cochain
complex in the target of `L`.  The degreewise counit `L(G(X)) ⟶ X` induces on `H^n` a map which
factors as

`L(H^n(G X)) ≅ H^n(L(G X))`, then `L` of the comparison `H^n(G X) ⟶ G(H^n X)` of the left exact
functor `G`, then the counit at `H^n X`.

So the degreewise counit is a quasi-isomorphism as soon as the comparison of `G` and the counit
are isomorphisms on cohomology.

## Main results

* `CategoryTheory.Adjunction.homologyComparison_comp_homologyMap_counit_adjunctionCounitHomology`:
  the factorization.
* `CategoryTheory.Adjunction.isIso_homologyMap_counit_adjunctionCounitHomology`: the resulting
  invertibility criterion.
* `CategoryTheory.Adjunction.homologyComparison_eq_unit_comp_adjunctionCounitHomology`: the
  transposed form, describing the comparison of `G` through the unit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.HypercohomologyEdge

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  {L : D ⥤ C} {G : C ⥤ D} [L.Additive] [G.Additive] (adj : L ⊣ G)
  [PreservesFiniteColimits L] [PreservesFiniteLimits G] (X : CochainComplex C ℤ) (n : ℤ)

variable {X}
  (φ : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ⟶ X)
  (hφ : ∀ i, φ.f i = adj.counit.app (X.X i))

omit [PreservesFiniteColimits L] in
include hφ in
/-- The degreewise counit on cycles is `L` of the comparison of cycles of `G` followed by the
counit, read through the comparison of cycles of `L`. -/
theorem cyclesComparison_comp_cyclesMap_counit_adjunctionCounitHomology :
    L.cyclesComparisonRightExactHomologyComparison
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) n ≫
        HomologicalComplex.cyclesMap φ n =
      L.map (HomologyComparison.cyclesComparison G X n) ≫ adj.counit.app (X.cycles n) := by
  apply (cancel_mono (X.iCycles n)).1
  rw [Category.assoc, HomologicalComplex.cyclesMap_i, Category.assoc,
    ← adj.counit_naturality, Functor.cyclesComparisonRightExactHomologyComparison,
    HomologicalComplex.liftCycles_i_assoc, hφ]
  change _ = L.map _ ≫ L.map (G.map _) ≫ _
  rw [← L.map_comp_assoc, HomologyComparison.cyclesComparison_comp_map_iCycles]

include hφ in
/-- **The cohomology of the degreewise counit.**  On `H^n`, the degreewise counit
`L(G(X)) ⟶ X` is `L` of the comparison `H^n(G X) ⟶ G(H^n X)` of the left exact functor `G`
followed by the counit at `H^n X`, read through the comparison `L(H^n(G X)) ⟶ H^n(L(G X))`. -/
theorem homologyComparison_comp_homologyMap_counit_adjunctionCounitHomology :
    L.homologyComparisonRightExactHomologyComparison
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) n ≫
        HomologicalComplex.homologyMap φ n =
      L.map (HomologyComparison.homologyComparison G X n) ≫ adj.counit.app (X.homology n) := by
  refine L.homologyComparison_hom_ext_rightExactHomologyComparison _ n ?_
  rw [Functor.map_homologyπ_comp_homologyComparison_rightExactHomologyComparison_assoc,
    HomologicalComplex.homologyπ_naturality, ← Category.assoc,
    cyclesComparison_comp_cyclesMap_counit_adjunctionCounitHomology adj n φ hφ, ← L.map_comp_assoc,
    HomologyComparison.homologyπ_comp_homologyComparison, Category.assoc, L.map_comp,
    Category.assoc, ← adj.counit_naturality]

include hφ in
/-- If the comparison `H^n(G X) ⟶ G(H^n X)` and the counit at `H^n X` are isomorphisms, then the
degreewise counit `L(G(X)) ⟶ X` induces an isomorphism on `H^n`, `L` being exact. -/
theorem isIso_homologyMap_counit_adjunctionCounitHomology [PreservesFiniteLimits L]
    [IsIso (HomologyComparison.homologyComparison G X n)] [IsIso (adj.counit.app (X.homology n))] :
    IsIso (HomologicalComplex.homologyMap φ n) := by
  have := L.isIso_homologyComparison_of_preservesFiniteLimits_rightExactHomologyComparison
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) n
  rw [← isIso_comp_left_iff (L.homologyComparisonRightExactHomologyComparison
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) n),
    homologyComparison_comp_homologyMap_counit_adjunctionCounitHomology adj n φ hφ]
  infer_instance

include hφ in
/-- **The comparison of the right adjoint through the unit.**  The comparison
`H^n(G X) ⟶ G(H^n X)` of the left exact functor `G` is the unit at `H^n(G X)` followed by `G` of
the cohomology of the degreewise counit, read through `L(H^n(G X)) ≅ H^n(L(G X))`. -/
theorem homologyComparison_eq_unit_comp_adjunctionCounitHomology :
    HomologyComparison.homologyComparison G X n =
      adj.unit.app _ ≫ G.map (L.homologyComparisonRightExactHomologyComparison
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) n ≫
          HomologicalComplex.homologyMap φ n) := by
  rw [homologyComparison_comp_homologyMap_counit_adjunctionCounitHomology adj n φ hφ, G.map_comp]
  have h := adj.unit.naturality (HomologyComparison.homologyComparison G X n)
  dsimp only [Functor.comp_map, Functor.id_map] at h
  rw [← Category.assoc, ← h, Category.assoc, adj.right_triangle_components]
  exact (Category.comp_id _).symm

omit [PreservesFiniteColimits L] in
/-- **The degreewise counit is a quasi-isomorphism** when, in every degree, the comparison
`H^n(G X) ⟶ G(H^n X)` and the counit at `H^n X` are isomorphisms, `L` being exact. -/
theorem quasiIso_mapHomologicalComplex_counit_app_adjunctionCounitHomology [PreservesFiniteLimits L]
    [PreservesFiniteColimits L] (X : CochainComplex C ℤ)
    (h₁ : ∀ n, IsIso (HomologyComparison.homologyComparison G X n))
    (h₂ : ∀ n, IsIso (adj.counit.app (X.homology n))) :
    QuasiIso ((NatTrans.mapHomologicalComplex adj.counit (ComplexShape.up ℤ)).app X) := by
  refine ⟨fun n => (quasiIsoAt_iff_isIso_homologyMap _ n).2 ?_⟩
  have := h₁ n
  have := h₂ n
  exact adj.isIso_homologyMap_counit_adjunctionCounitHomology n
    (X := X) ((NatTrans.mapHomologicalComplex adj.counit (ComplexShape.up ℤ)).app X)
    (fun _ => rfl)

omit [PreservesFiniteColimits L] [PreservesFiniteLimits G] in
/-- The counit of the adjunction induced on homotopy categories is, at a complex `X`, inverted by
the localization to the derived category as soon as the degreewise counit at `X` is a
quasi-isomorphism. -/
theorem isIso_Qh_map_mapHomotopyCategory_counit_app_adjunctionCounitHomology [HasDerivedCategory C]
    (X : CochainComplex C ℤ)
    (h : QuasiIso ((NatTrans.mapHomologicalComplex adj.counit (ComplexShape.up ℤ)).app X)) :
    IsIso (DerivedCategory.Qh.map ((adj.mapHomotopyCategory (ComplexShape.up ℤ)).counit.app
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj X))) := by
  rw [Adjunction.mapHomotopyCategory_counit_app]
  exact Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
    _ ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 h)

end CategoryTheory.Adjunction
