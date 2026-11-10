module

public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.BoundaryChernComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.RealizationShift
public import StacksFrontier.Algebra.Homology.TriangleOfSESHomology

/-!
# The boundary map of a shifted short exact sequence on cohomology

Let `0 → P[1] → M → N → 0` be a short exact sequence of complexes and
`δ : N ⟶ P[2]` its boundary map (`Stacks.ShiftedBoundary.Sequence.boundary`). For a functor
`G` into a derived category commuting with the shift, such as derived global sections, the map
`H⁰(G N) ⟶ H⁰(G(P[2])) = H²(G P)` induced by `δ` is the connecting map
`H⁰(G N) ⟶ H¹(G(P[1]))` of the sequence followed by `H¹(G(P[1])) = H²(G P)`. This file proves
that bookkeeping identity.

## Main results

* `Stacks.ShiftedBoundary.homology_map_comp_shiftHomologyIsoU`: the identity, for a morphism
  `δ ≫ c[1]` followed by the addition of the two translations, at a functor commuting with the
  shift.
* `Stacks.ShiftedBoundary.Sequence.homology_boundary_comp_shiftHomologyIsoU`: the identity for
  the boundary map of a shifted short exact sequence.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits DerivedCategory

namespace Stacks.ShiftedBoundary

open Stacks.Cohomology.RealizationShift (shiftHomologyIsoU)

/-- Two commutative squares pasted, with every object a variable. -/
private theorem paste_sq {V : Type*} [Category* V] {p q r s t u : V} (a : p ⟶ q) (b : q ⟶ r)
    (c : r ⟶ u) (d : p ⟶ s) (e : s ⟶ t) (f : t ⟶ u) (x : s ⟶ r)
    (h₁ : a ≫ b = d ≫ x) (h₂ : x ≫ c = e ≫ f) : a ≫ (b ≫ c) = (d ≫ e) ≫ f := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

section Generic

variable {C B : Type*} [Category* C] [Category* B] [Abelian B] [HasDerivedCategory B]
  [HasShift C ℤ] (G : C ⥤ DerivedCategory B) [G.CommShift ℤ]

/-- The connecting map on cohomology of a morphism `Y ⟶ Z[1]`, at a functor commuting with the
shift, is the induced map followed by `H⁰(G(Z[1])) = H¹(G Z)`. -/
theorem shiftMap_mapδ_eq {Y Z : C} (f : Y ⟶ Z⟦(1 : ℤ)⟧) :
    (homologyFunctor B 0).shiftMap (Functor.mapδ G f) 0 1 (by omega) =
      (homologyFunctor B 0).map (G.map f) ≫ (shiftHomologyIsoU G Z 1 0 1 (by omega)).hom := by
  change (homologyFunctor B 0).map (G.map f ≫ (G.commShiftIso (1 : ℤ)).hom.app Z) ≫ _ =
    _ ≫ (homologyFunctor B 0).map ((G.commShiftIso (1 : ℤ)).hom.app Z) ≫ _
  rw [Functor.map_comp]
  exact Category.assoc _ _ _

/-- The identifications `Hᵃ(G(Y[s])) ≅ Hᵃ⁺ˢ(G Y)` are natural in `Y`. -/
theorem shiftHomologyIsoU_hom_naturality {Y Y' : C} (g : Y ⟶ Y') (s a a' : ℤ)
    (h : s + a = a') :
    (homologyFunctor B a).map (G.map (g⟦s⟧')) ≫ (shiftHomologyIsoU G Y' s a a' h).hom =
      (shiftHomologyIsoU G Y s a a' h).hom ≫ (homologyFunctor B a').map (G.map g) := by
  have e₁ := (G.commShiftIso s).hom.naturality g
  have e₂ := ((homologyFunctor B 0).shiftIso s a a' h).hom.naturality (G.map g)
  simp only [Functor.comp_map] at e₁ e₂
  have e₁' : (homologyFunctor B a).map (G.map (g⟦s⟧')) ≫
      (homologyFunctor B a).map ((G.commShiftIso s).hom.app Y') =
      (homologyFunctor B a).map ((G.commShiftIso s).hom.app Y) ≫
        (homologyFunctor B a).map ((G.map g)⟦s⟧') := by
    rw [← Functor.map_comp, ← Functor.map_comp, e₁]
  exact paste_sq _ _ _ _ _ _ _ e₁' e₂

/-- **The map induced on cohomology by `δ ≫ c[1]`**, followed by the addition of the two
translations and `H⁰(G(Z[2])) = H²(G Z)`, is the map induced by `δ` followed by
`H⁰(G(Y[1])) = H¹(G Y)`, the map induced by `c` and `H¹(G(Z[1])) = H²(G Z)`. -/
theorem homology_map_comp_shiftHomologyIsoU {N Y Z : C} (δ : N ⟶ Y⟦(1 : ℤ)⟧)
    (c : Y ⟶ Z⟦(1 : ℤ)⟧) :
    (homologyFunctor B 0).map (G.map (δ ≫ c⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd' C (1 : ℤ) 1 2 (by omega)).inv.app Z)) ≫
        (shiftHomologyIsoU G Z 2 0 2 (by omega)).hom =
      (homologyFunctor B 0).map (G.map δ) ≫ (shiftHomologyIsoU G Y 1 0 1 (by omega)).hom ≫
        (homologyFunctor B 1).map (G.map c) ≫ (shiftHomologyIsoU G Z 1 1 2 (by omega)).hom := by
  have hadd := Stacks.Cohomology.RealizationShift.shiftHomologyIsoU_add G Z 1 1 2 (by omega)
    0 1 2 (by omega) (by omega)
  have hnat := shiftHomologyIsoU_hom_naturality G c 1 0 1 (by omega)
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp, Category.assoc,
    Category.assoc, ← hadd, reassoc_of% hnat]

end Generic

namespace Sequence

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
  (G : DerivedCategory C ⥤ DerivedCategory B) [G.CommShift ℤ]
  {P N : CochainComplex C ℤ} (S : Sequence P N)

/-- **The boundary map of a shifted short exact sequence `0 → P[1] → M → N → 0` on cohomology.**
At a functor `G` commuting with the shift, the map `H⁰(G N) ⟶ H²(G P)` induced by the boundary
map `N ⟶ P[2]` is the connecting map `H⁰(G N) ⟶ H¹(G(P[1]))` of the sequence followed by
`H¹(G(P[1])) = H²(G P)`. -/
theorem homology_boundary_comp_shiftHomologyIsoU :
    (homologyFunctor B 0).map (G.map S.boundary) ≫
        (shiftHomologyIsoU G (Q.obj P) 2 0 2 (by omega)).hom =
      (homologyFunctor B 0).shiftMap (Functor.mapδ G (triangleOfSESδ S.shortExact)) 0 1
          (by omega) ≫
        (homologyFunctor B 1).map (G.map ((Q.commShiftIso (1 : ℤ)).hom.app P)) ≫
          (shiftHomologyIsoU G (Q.obj P) 1 1 2 (by omega)).hom := by
  refine (homology_map_comp_shiftHomologyIsoU G (triangleOfSESδ S.shortExact)
    ((Q.commShiftIso (1 : ℤ)).hom.app P)).trans ?_
  rw [shiftMap_mapδ_eq]
  exact (Category.assoc _ _ _).symm

end Sequence

end Stacks.ShiftedBoundary

end
