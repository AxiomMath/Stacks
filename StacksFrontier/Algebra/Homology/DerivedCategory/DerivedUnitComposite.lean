module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedUnitSquare

/-!
# The unit of a right derived functor along a composite

Let `F : 𝒜 ⥤ ℬ`, `G : ℬ ⥤ 𝒞` and `H : 𝒜 ⥤ 𝒞` be additive functors between abelian categories,
related by an isomorphism `e : F ⋙ G ≅ H`, and let `RF`, `RG`, `RH` be right derived functors
with units `u_F`, `u_G`, `u_H`. A comparison `c : RH ⟶ RF ⋙ RG` which restricts along `u_H` to
the composite unit `G(F(-)) ⟶ RG(F(-)) ⟶ RG(RF(-))` (as the comparison obtained from the universal
property of `RH` does, [Stacks, Tag 0D5T]) satisfies, on every cochain complex `K` of `𝒜`,

`u_G(F K) ≫ RG(u_F K) = e_K ≫ u_H(K) ≫ c_K : G(F(K)) ⟶ RG(RF(K))`,

that is: the composite of the two units is the unit of the composite followed by the
comparison, once `G(F(K))` and `H(K)` are identified along `e`.

## Main results

* `StacksDraft.DerivedUnitSquare.unitQ_comp_map_unitQ`: the unit along a composite.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

attribute [-instance] CategoryTheory.catToReflQuiver

namespace StacksDraft.DerivedUnitSquare

section Factors

variable {C D E : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D] [Category E]
  [Preadditive E] {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} [F.Additive] [G.Additive] [H.Additive]
  (e : F ⋙ G ≅ H)

/-- The factorisation isomorphism of `B.mapHomotopyCategory` is the identity on components. -/
lemma mapHomotopyCategoryFactors_inv_app_eq (B : C ⥤ D) [B.Additive] (K : CochainComplex C ℤ) :
    (B.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K =
      𝟙 ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj
        ((B.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
  rfl

/-- On the image of a complex, the comparison of the induced functors on homotopy categories is
the class of the comparison of complexes. -/
lemma mapHomotopyCategoryCompIso_hom_app_quotient_obj (K : CochainComplex C ℤ) :
    (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) =
      (HomotopyCategory.quotient E (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.app K) :=
  rfl

/-- The factorisation isomorphisms of `F`, `G` and `H` on homotopy categories are compatible with
the comparison induced by `e`. -/
lemma mapHomotopyCategoryFactors_inv_comp_compIso (K : CochainComplex C ℤ) :
    (G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
      (G.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K) ≫
      (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) =
    (HomotopyCategory.quotient E (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.app K) ≫
      (H.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K := by
  rw [mapHomotopyCategoryFactors_inv_app_eq, mapHomotopyCategoryFactors_inv_app_eq,
    mapHomotopyCategoryFactors_inv_app_eq, mapHomotopyCategoryCompIso_hom_app_quotient_obj]
  exact (Category.id_comp _).trans ((congrArg (· ≫ _) ((G.mapHomotopyCategory _).map_id _)).trans
    ((Category.id_comp _).trans (Category.comp_id _).symm))

end Factors

/-- A functor carries the two components of a natural isomorphism to mutually inverse maps. -/
lemma map_hom_inv_app_assoc {C D E : Type*} [Category C] [Category D] [Category E]
    {P Q : C ⥤ D} (α : P ≅ Q) (R : D ⥤ E) (X : C) {Y : E} (h : R.obj (P.obj X) ⟶ Y) :
    R.map (α.hom.app X) ≫ R.map (α.inv.app X) ≫ h = h := by
  rw [← R.map_comp_assoc, Iso.hom_inv_id_app, R.map_id, Category.id_comp]

section Comp

variable {C D E : Type*} [Category C] [Abelian C] [Category D] [Abelian D] [Category E] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H)
  {RF : DerivedCategory C ⥤ DerivedCategory D} {RG : DerivedCategory D ⥤ DerivedCategory E}
  {RH : DerivedCategory C ⥤ DerivedCategory E}
  (uF : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
  (uG : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RG)
  (uH : H.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RH)
  (c : RH ⟶ RF ⋙ RG)

include uF uG uH in
/-- **The unit along a composite.** If the comparison `c : RH ⟶ RF ⋙ RG` restricts along `u_H` to
the composite unit, then on every cochain complex `K` the composite `u_G(F K) ≫ RG(u_F K)` is
`u_H K ≫ c_K`, precomposed with the identification `G(F(K)) ≅ H(K)` given by `e`. -/
theorem unitQ_comp_map_unitQ
    (hc : ∀ K, uH.app K ≫ c.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).inv.app K) ≫
        uG.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫ RG.map (uF.app K))
    (K : CochainComplex C ℤ) :
    unitQ G uG ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫ RG.map (unitQ F uF K) =
      DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.app K) ≫
        unitQ H uH K ≫ c.app (DerivedCategory.Q.obj K) := by
  set qK := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K
  -- the factorisation, solved for the composite of the two units
  have hA : uG.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj qK) ≫ RG.map (uF.app qK) =
      DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app qK) ≫
        uH.app qK ≫ c.app (DerivedCategory.Qh.obj qK) := by
    rw [hc, map_hom_inv_app_assoc]
  have hnu := uG.naturality ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K)
  have hnc := c.naturality ((DerivedCategory.quotientCompQhIso C).hom.app K)
  have hkey := mapHomotopyCategoryFactors_inv_comp_compIso e K
  have hQ := DerivedCategory.quotientCompQhIso_inv_naturality
    ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at hnu hnc
  simp only [unitQ, Category.assoc, RG.map_comp]
  rw [map_hom_inv_app_assoc, ← reassoc_of% hnu, reassoc_of% hA, ← hnc, reassoc_of% hQ,
    ← DerivedCategory.Qh.map_comp_assoc, ← DerivedCategory.Qh.map_comp_assoc,
    ← DerivedCategory.Qh.map_comp_assoc, Category.assoc, hkey]

end Comp

end StacksDraft.DerivedUnitSquare
