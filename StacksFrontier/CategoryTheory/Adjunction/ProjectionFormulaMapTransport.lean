module

public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMap

/-!
# Transporting the projection-formula map of an adjunction

The canonical map `CategoryTheory.adjunctionTensorMap adj A B α G H : A(R G, H) ⟶ R(B(G, L H))`
is compatible with the two operations by which one adjunction-with-comparison is compared with
another:

* replacing the bifunctors `A`, `B` by isomorphic ones, with the comparison conjugated
  accordingly (`adjunctionTensorMap_of_bifunctorIso`);
* passing along functors `iC`, `iD` from a "small" adjunction `L ⊣ R` to a "big" one
  `L' ⊣ R'`, given commutation isomorphisms `iC ⋙ L' ≅ L ⋙ iD`, `iD ⋙ R' ≅ R ⋙ iC` under which the
  counits correspond, and under which the two comparisons correspond
  (`map_adjunctionTensorMap_of_counit_comm`). This covers both the restriction of an adjunction
  to full subcategories and the comparison of two models of a derived adjunction.

In both cases the two canonical maps agree up to isomorphisms on either side, so one is
invertible exactly when the other is.
-/

@[expose] public section

namespace CategoryTheory

open scoped CategoryTheory.Prod

section Bifunctor

variable {C : Type*} {D : Type*} [Category C] [Category D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  {A A' : C × C ⥤ C} {B B' : D × D ⥤ D} (eA : A ≅ A') (eB : B ≅ B')
  (α : A ⋙ L ⟶ L.prod L ⋙ B) (α' : A' ⋙ L ⟶ L.prod L ⋙ B')

/-- **The canonical map under isomorphisms of the bifunctors.** If the comparison `α'` is `α`
conjugated by `eA : A ≅ A'` and `eB : B ≅ B'`, the canonical map of `α'` is that of `α`
conjugated by the same isomorphisms. -/
theorem adjunctionTensorMap_of_bifunctorIso
    (h : ∀ P : C × C, α'.app P = L.map (eA.inv.app P) ≫ α.app P ≫
      eB.hom.app (L.obj P.1, L.obj P.2)) (G : D) (H : C) :
    adjunctionTensorMap adj A' B' α' G H =
      eA.inv.app (R.obj G, H) ≫ adjunctionTensorMap adj A B α G H ≫
        R.map (eB.hom.app (G, L.obj H)) := by
  apply (adj.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, map_adjunctionTensorMap_comp_counit,
    L.map_comp, L.map_comp, Category.assoc, Category.assoc, adj.counit_naturality,
    map_adjunctionTensorMap_comp_counit_assoc, h]
  have n := eB.hom.naturality (adj.counit.app G ×ₘ 𝟙 (L.obj H))
  simp only [Functor.id_obj, Functor.comp_obj] at n
  simp only [Category.assoc]
  rw [n]

/-- Invertibility of the canonical map does not depend on the bifunctors up to isomorphism. -/
theorem isIso_adjunctionTensorMap_iff_of_bifunctorIso
    (h : ∀ P : C × C, α'.app P = L.map (eA.inv.app P) ≫ α.app P ≫
      eB.hom.app (L.obj P.1, L.obj P.2)) (G : D) (H : C) :
    IsIso (adjunctionTensorMap adj A' B' α' G H) ↔ IsIso (adjunctionTensorMap adj A B α G H) := by
  rw [adjunctionTensorMap_of_bifunctorIso adj eA eB α α' h, isIso_comp_left_iff,
    isIso_comp_right_iff]

end Bifunctor

section CounitComm

variable {C : Type*} {D : Type*} {C' : Type*} {D' : Type*} [Category C] [Category D]
  [Category C'] [Category D'] {iC : C ⥤ C'} {iD : D ⥤ D'}
  {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) {L' : C' ⥤ D'} {R' : D' ⥤ C'} (adj : L' ⊣ R')
  (c : iC ⋙ L' ≅ L ⋙ iD) (d : iD ⋙ R' ≅ R ⋙ iC)
  {A : C × C ⥤ C} {B : D × D ⥤ D} {A' : C' × C' ⥤ C'} {B' : D' × D' ⥤ D'}
  (eA : iC.prod iC ⋙ A' ≅ A ⋙ iC) (eB : iD.prod iD ⋙ B' ≅ B ⋙ iD)
  (α : A ⋙ L ⟶ L.prod L ⋙ B) (α' : A' ⋙ L' ⟶ L'.prod L' ⋙ B')

/-- **The canonical map along a correspondence of adjunctions.** Let `iC`, `iD` carry the
adjunction `L ⊣ R` to `L' ⊣ R'`, through commutation isomorphisms `c`, `d` under which the counits
correspond (`hc`), and the bifunctors `A`, `B` to `A'`, `B'` through `eA`, `eB`, with the
comparisons `α`, `α'` corresponding (`hα`). Then `iC` carries the canonical map of `α` at
`(G, H)` to that of `α'` at `(iD G, iC H)`, up to the evident isomorphisms on either side. -/
theorem map_adjunctionTensorMap_of_counit_comm
    (hc : ∀ Y : D, c.hom.app (R.obj Y) ≫ iD.map (a.counit.app Y) =
      L'.map (d.inv.app Y) ≫ adj.counit.app (iD.obj Y))
    (hα : ∀ P Q : C, c.hom.app (A.obj (P, Q)) ≫ iD.map (α.app (P, Q)) =
      L'.map (eA.inv.app (P, Q)) ≫ α'.app (iC.obj P, iC.obj Q) ≫
        B'.map (c.hom.app P ×ₘ c.hom.app Q) ≫ eB.hom.app (L.obj P, L.obj Q))
    (G : D) (H : C) :
    iC.map (adjunctionTensorMap a A B α G H) =
      eA.inv.app (R.obj G, H) ≫ A'.map (d.inv.app G ×ₘ 𝟙 (iC.obj H)) ≫
        adjunctionTensorMap adj A' B' α' (iD.obj G) (iC.obj H) ≫
          R'.map (B'.map (𝟙 (iD.obj G) ×ₘ c.hom.app H) ≫ eB.hom.app (G, L.obj H)) ≫
            d.hom.app (B.obj (G, L.obj H)) := by
  rw [← cancel_mono (d.inv.app (B.obj (G, L.obj H)))]
  apply (adj.homEquiv _ _).symm.injective
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id, Adjunction.homEquiv_counit,
    Functor.map_comp, Functor.comp_obj]
  -- left-hand side
  have l1 := hc (B.obj (G, L.obj H))
  have l2 := c.hom.naturality (adjunctionTensorMap a A B α G H)
  simp only [Functor.comp_obj, Functor.comp_map] at l1 l2
  rw [← l1, reassoc_of% l2, ← iD.map_comp, map_adjunctionTensorMap_comp_counit, iD.map_comp,
    reassoc_of% (hα (R.obj G) H)]
  -- right-hand side
  rw [adj.counit_naturality, adj.counit_naturality_assoc, map_adjunctionTensorMap_comp_counit_assoc]
  have r1 := α'.naturality (d.inv.app G ×ₘ 𝟙 (iC.obj H))
  simp only [Functor.comp_obj, Functor.comp_map, Functor.prod_obj, Functor.prod_map,
    CategoryTheory.Functor.map_id] at r1
  rw [reassoc_of% r1]
  refine congrArg (L'.map (eA.inv.app (R.obj G, H)) ≫ α'.app (iC.obj (R.obj G), iC.obj H) ≫ ·) ?_
  have r2 := hc G
  have r3 := eB.hom.naturality (a.counit.app G ×ₘ 𝟙 (L.obj H))
  simp only [Functor.comp_obj, Functor.comp_map, Functor.prod_obj, Functor.prod_map,
    CategoryTheory.Functor.map_id, Functor.id_obj] at r2 r3
  rw [← r3, ← B'.map_comp_assoc, ← B'.map_comp_assoc, ← B'.map_comp_assoc]
  refine congrArg (fun t => B'.map t ≫ eB.hom.app (G, L.obj H)) ?_
  apply Prod.ext
  · simp only [prod_comp, Category.assoc]
    rw [r2]
    simp
  · simp

/-- Along a correspondence of adjunctions, `iC` inverts the canonical map of `α` exactly when the
canonical map of `α'` at the images is invertible. -/
theorem isIso_map_adjunctionTensorMap_iff_of_counit_comm
    (hc : ∀ Y : D, c.hom.app (R.obj Y) ≫ iD.map (a.counit.app Y) =
      L'.map (d.inv.app Y) ≫ adj.counit.app (iD.obj Y))
    (hα : ∀ P Q : C, c.hom.app (A.obj (P, Q)) ≫ iD.map (α.app (P, Q)) =
      L'.map (eA.inv.app (P, Q)) ≫ α'.app (iC.obj P, iC.obj Q) ≫
        B'.map (c.hom.app P ×ₘ c.hom.app Q) ≫ eB.hom.app (L.obj P, L.obj Q))
    (G : D) (H : C) :
    IsIso (iC.map (adjunctionTensorMap a A B α G H)) ↔
      IsIso (adjunctionTensorMap adj A' B' α' (iD.obj G) (iC.obj H)) := by
  have : IsIso (d.inv.app G ×ₘ 𝟙 (iC.obj H)) :=
    (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  have : IsIso (𝟙 (iD.obj G) ×ₘ c.hom.app H) :=
    (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  rw [map_adjunctionTensorMap_of_counit_comm a adj c d eA eB α α' hc hα, isIso_comp_left_iff,
    isIso_comp_left_iff, ← Category.assoc, isIso_comp_right_iff, isIso_comp_right_iff]

end CounitComm

end CategoryTheory

end
