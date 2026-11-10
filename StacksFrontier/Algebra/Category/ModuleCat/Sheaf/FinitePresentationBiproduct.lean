module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Basic.Finite.Sum

/-!
# Presentations of a binary biproduct of sheaves of modules

The direct sum of two sheaves of modules carries the direct sum of any two presentations of
the summands: the generators are indexed by the disjoint union of the two index types, and so
are the relations.  Consequently a biproduct of two finitely presented sheaves of modules
admits a finite presentation as soon as each summand does.

## Main definitions

* `SheafOfModules.Presentation.biprod` is the direct sum of two presentations, a presentation
  of the biproduct of the presented modules.

## Main results

* `CategoryTheory.Limits.isColimitCokernelCoforkBiprodMapOfPresentations`: a biproduct of two
  cokernel coforks is a cokernel cofork.
* `CategoryTheory.Limits.isColimitCokernelCoforkIsoComp`: precomposing the projection of a
  cokernel cofork with an isomorphism again gives a cokernel cofork.
* `SheafOfModules.Presentation.isFinite_biprod`: the direct sum of two finite presentations is
  finite.

## Implementation notes

A `SheafOfModules.Presentation` records free modules on the generators and on the relations
together with the statement that the module is their cokernel.  The construction therefore
proceeds in three steps: the biproduct of two cokernel diagrams is a cokernel diagram
(`isColimitCokernelCoforkBiprodMapOfPresentations`); the biproduct of two free modules is free
on the disjoint union of the index types (`SheafOfModules.freeSumIso`); and a cokernel diagram
may be transported along isomorphisms of its outer terms
(`isColimitCokernelCoforkIsoComp` together with
`CategoryTheory.Limits.isCokernelEpiComp`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v u₁ v₁

namespace CategoryTheory.Limits

variable {C : Type*} [Category C] [HasZeroMorphisms C]

/-- A biproduct of two cokernel coforks is a cokernel cofork: if `Z₁` is the cokernel of
`f₁ : X₁ ⟶ Y₁` and `Z₂` is the cokernel of `f₂ : X₂ ⟶ Y₂`, then `Z₁ ⊞ Z₂` is the cokernel of
`f₁ ⊞ f₂`. -/
noncomputable def isColimitCokernelCoforkBiprodMapOfPresentations
    {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}
    [HasBinaryBiproduct X₁ X₂] [HasBinaryBiproduct Y₁ Y₂] [HasBinaryBiproduct Z₁ Z₂]
    (f₁ : X₁ ⟶ Y₁) (p₁ : Y₁ ⟶ Z₁) (h₁ : f₁ ≫ p₁ = 0)
    (c₁ : IsColimit (CokernelCofork.ofπ p₁ h₁))
    (f₂ : X₂ ⟶ Y₂) (p₂ : Y₂ ⟶ Z₂) (h₂ : f₂ ≫ p₂ = 0)
    (c₂ : IsColimit (CokernelCofork.ofπ p₂ h₂))
    (hbig : biprod.map f₁ f₂ ≫ biprod.map p₁ p₂ = 0) :
    IsColimit (CokernelCofork.ofπ (biprod.map p₁ p₂) hbig) := by
  refine CokernelCofork.IsColimit.ofπ _ _
    (fun {W} g eqg =>
      biprod.desc
        (CokernelCofork.IsColimit.desc' c₁ (biprod.inl ≫ g)
          (by rw [← biprod.inl_map_assoc f₁ f₂, eqg, comp_zero])).1
        (CokernelCofork.IsColimit.desc' c₂ (biprod.inr ≫ g)
          (by rw [← biprod.inr_map_assoc f₁ f₂, eqg, comp_zero])).1)
    (fun {W} g eqg => ?_) (fun {W} g eqg m hm => ?_)
  · apply biprod.hom_ext'
    · rw [biprod.inl_map_assoc, biprod.inl_desc]
      exact (CokernelCofork.IsColimit.desc' c₁ (biprod.inl ≫ g) _).2
    · rw [biprod.inr_map_assoc, biprod.inr_desc]
      exact (CokernelCofork.IsColimit.desc' c₂ (biprod.inr ≫ g) _).2
  · apply biprod.hom_ext'
    · rw [biprod.inl_desc]
      refine Cofork.IsColimit.hom_ext c₁ ?_
      have key : p₁ ≫ biprod.inl ≫ m = biprod.inl ≫ g := by
        rw [← biprod.inl_map_assoc p₁ p₂, hm]
      exact key.trans (CokernelCofork.IsColimit.desc' c₁ (biprod.inl ≫ g) _).2.symm
    · rw [biprod.inr_desc]
      refine Cofork.IsColimit.hom_ext c₂ ?_
      have key : p₂ ≫ biprod.inr ≫ m = biprod.inr ≫ g := by
        rw [← biprod.inr_map_assoc p₁ p₂, hm]
      exact key.trans (CokernelCofork.IsColimit.desc' c₂ (biprod.inr ≫ g) _).2.symm

/-- A cokernel cofork stays one after replacing its middle term by an isomorphic object: if `Z`
is the cokernel of `f : X ⟶ Y` and `e : Yb ≅ Y`, then `Z` is the cokernel of
`f ≫ e.inv : X ⟶ Yb` with projection `e.hom ≫ p`. -/
noncomputable def isColimitCokernelCoforkIsoComp
    {X Y Yb Z : C} (e : Yb ≅ Y) (f : X ⟶ Y) (p : Y ⟶ Z) (h : f ≫ p = 0)
    (hc : IsColimit (CokernelCofork.ofπ p h)) :
    IsColimit (CokernelCofork.ofπ (e.hom ≫ p)
      (show (f ≫ e.inv) ≫ (e.hom ≫ p) = 0 by simp [Category.assoc, h])) := by
  refine CokernelCofork.IsColimit.ofπ _ _
    (fun {Z'} g' eq' => (CokernelCofork.IsColimit.desc' hc (e.inv ≫ g') (by
      rwa [← Category.assoc])).1) ?_ ?_
  · intro Z' g' eq'
    have hl := (CokernelCofork.IsColimit.desc' hc (e.inv ≫ g')
      (by rwa [← Category.assoc])).2
    simp only [CokernelCofork.π_ofπ] at hl
    rw [Category.assoc, hl, ← Category.assoc, e.hom_inv_id, Category.id_comp]
  · intro Z' g' eq' m hm
    apply Cofork.IsColimit.hom_ext hc
    simp only [CokernelCofork.π_ofπ]
    have hl := (CokernelCofork.IsColimit.desc' hc (e.inv ≫ g')
      (by rwa [← Category.assoc])).2
    simp only [CokernelCofork.π_ofπ] at hl
    rw [hl, ← hm]
    simp

end CategoryTheory.Limits

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁, u₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify J AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]

/-- The direct sum of two presentations: a presentation of `A ⊞ B` whose generators are indexed
by the disjoint union of the generators of the two given presentations, and likewise for its
relations. -/
noncomputable def Presentation.biprod
    {A B : SheafOfModules.{u} R} (P : A.Presentation) [P.IsFinite]
    (Q : B.Presentation) [Q.IsFinite]
    [HasBinaryBiproduct A B]
    [HasBinaryBiproduct (free (R := R) P.relations.I) (free (R := R) Q.relations.I)]
    [HasBinaryBiproduct (free (R := R) P.generators.I) (free (R := R) Q.generators.I)] :
    (A ⊞ B).Presentation := by
  set fP : free P.relations.I ⟶ free P.generators.I := P.relations.π ≫ kernel.ι _ with hfP
  set pP : free P.generators.I ⟶ A := P.generators.π with hpP
  set fQ : free Q.relations.I ⟶ free Q.generators.I := Q.relations.π ≫ kernel.ι _ with hfQ
  set pQ : free Q.generators.I ⟶ B := Q.generators.π with hpQ
  have hfgP : fP ≫ pP = 0 := by rw [hfP, hpP, Category.assoc, kernel.condition, comp_zero]
  have hfgQ : fQ ≫ pQ = 0 := by rw [hfQ, hpQ, Category.assoc, kernel.condition, comp_zero]
  have cP : IsColimit (CokernelCofork.ofπ pP hfgP) := P.isColimit
  have cQ : IsColimit (CokernelCofork.ofπ pQ hfgQ) := Q.isColimit
  have hbig : biprod.map fP fQ ≫ biprod.map pP pQ = 0 := by
    apply biprod.hom_ext' <;> simp [reassoc_of% hfgP, reassoc_of% hfgQ]
  have cBig : IsColimit (CokernelCofork.ofπ (biprod.map pP pQ) hbig) :=
    isColimitCokernelCoforkBiprodMapOfPresentations fP pP _ cP fQ pQ _ cQ hbig
  have eGen : ((free P.generators.I : SheafOfModules R) ⊞
      (free Q.generators.I : SheafOfModules R)) ≅
      (free (P.generators.I ⊕ Q.generators.I) : SheafOfModules R) :=
    biprod.isoCoprod _ _ ≪≫ freeSumIso _ _
  have eRel : ((free P.relations.I : SheafOfModules R) ⊞
      (free Q.relations.I : SheafOfModules R)) ≅
      (free (P.relations.I ⊕ Q.relations.I) : SheafOfModules R) :=
    biprod.isoCoprod _ _ ≪≫ freeSumIso _ _
  have cMid : IsColimit (CokernelCofork.ofπ (eGen.symm.hom ≫ biprod.map pP pQ)
      (show (biprod.map fP fQ ≫ eGen.symm.inv) ≫
        (eGen.symm.hom ≫ biprod.map pP pQ) = 0 by simp [Category.assoc, hbig])) :=
    isColimitCokernelCoforkIsoComp eGen.symm (biprod.map fP fQ) (biprod.map pP pQ) hbig cBig
  refine presentationOfIsCokernelFree
    (eRel.symm.hom ≫ (biprod.map fP fQ ≫ eGen.symm.inv))
    (eGen.symm.hom ≫ biprod.map pP pQ)
    (show (eRel.symm.hom ≫ (biprod.map fP fQ ≫ eGen.symm.inv)) ≫
      (eGen.symm.hom ≫ biprod.map pP pQ) = 0 by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [hbig, comp_zero]) ?_
  exact isCokernelEpiComp cMid eRel.symm.hom rfl

omit [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})] in
/-- The direct sum of two finite presentations is a finite presentation. -/
theorem Presentation.isFinite_biprod
    {A B : SheafOfModules.{u} R} (P : A.Presentation) [P.IsFinite]
    (Q : B.Presentation) [Q.IsFinite]
    [HasBinaryBiproduct A B]
    [HasBinaryBiproduct (free (R := R) P.relations.I) (free (R := R) Q.relations.I)]
    [HasBinaryBiproduct (free (R := R) P.generators.I) (free (R := R) Q.generators.I)] :
    (P.biprod Q).IsFinite := by
  constructor
  · constructor
    change Finite (P.generators.I ⊕ Q.generators.I)
    infer_instance
  · constructor
    change Finite (P.relations.I ⊕ Q.relations.I)
    infer_instance

end SheafOfModules

end
