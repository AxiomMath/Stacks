module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactCompositionComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactIdentityComparison

/-!
# The unit of a derived adjunction with invertible unit

For an adjunction `L ⊣ R` of additive functors with `L` preserving homology and `R` exact, the
derived adjunction `RL ⊣ RR` on bounded below derived categories
(`CategoryTheory.Adjunction.rightDerivedFunctorPlus`) has as unit the inverse of the comparison
`RL ⋙ RR ≅ R(L ⋙ R) ≅ 𝟭` induced by the inverse of the underived unit, when the underived unit is
invertible.

## Main results

* `CategoryTheory.Adjunction.rightDerivedFunctorPlus_unit_eq`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Adjunction

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A] [EnoughInjectives B]
  {L : A ⥤ B} {R : B ⥤ A} [L.Additive] [R.Additive] [L.PreservesHomology]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R] (adj : L ⊣ R) [IsIso adj.unit]

omit [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A] [EnoughInjectives B]
  [L.PreservesHomology] [PreservesFiniteLimits R] [PreservesFiniteColimits R] [IsIso adj.unit] in
/-- **The unit of the degreewise adjunction on bounded below homotopy categories** is the
degreewise image of the unit of `adj`, read through the comparison for the composite `L ⋙ R`. -/
theorem mapHomotopyCategoryPlus_unit_app_comp (K : HomotopyCategory.Plus A) :
    adj.mapHomotopyCategoryPlus.unit.app K ≫
        (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (L ⋙ R))).hom.app K =
      (Stacks.Cohomology.BaseChange.mapPlus adj.unit).app K := by
  rw [Stacks.Cohomology.BaseChange.mapHomotopyCategoryPlusCompIso_refl_comp_hom]
  ext
  change (HomotopyCategory.Plus.ι A).map (adj.mapHomotopyCategoryPlus.unit.app K) = _
  rw [Stacks.Cohomology.BaseChange.mapPlus_app_hom]
  refine (map_restrictFullyFaithful_unit_app (adj.mapHomotopyCategory (ComplexShape.up ℤ))
    (HomotopyCategory.Plus.fullyFaithfulι A) (HomotopyCategory.Plus.fullyFaithfulι B)
    (L := L.mapHomotopyCategoryPlus) (R := R.mapHomotopyCategoryPlus)
    (Iso.refl (HomotopyCategory.Plus.ι A ⋙ L.mapHomotopyCategory (ComplexShape.up ℤ)))
    (Iso.refl (HomotopyCategory.Plus.ι B ⋙ R.mapHomotopyCategory (ComplexShape.up ℤ))) K).trans ?_
  have h := congr_app (mapHomotopyCategory_unit_eq adj (ComplexShape.up ℤ)) K.obj
  obtain ⟨⟨X⟩, hX⟩ := K
  simp only [Iso.refl_hom, NatTrans.id_app]
  simp only at h
  exact ((whisker_eq _ ((Category.comp_id _).trans (CategoryTheory.Functor.map_id
    (R.mapHomotopyCategory (ComplexShape.up ℤ)) _))).trans
    (Category.comp_id _)).trans (h.trans ((Category.id_comp _).trans (Category.comp_id _)))

/-- **The unit of the derived adjunction** `RL ⊣ RR` is the inverse of the comparison
`RL ⋙ RR ≅ R(L ⋙ R) ≅ 𝟭` induced by the inverse of the (invertible) underived unit. -/
theorem rightDerivedFunctorPlus_unit_eq :
    adj.rightDerivedFunctorPlus.unit =
      (Functor.rightDerivedFunctorPlusCompIsoOfExact L R (L ⋙ R) (Iso.refl _) ≪≫
        Functor.rightDerivedFunctorPlusIdIsoOf (L ⋙ R) (asIso adj.unit).symm).inv := by
  let := L.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  have hαR : (L.rightDerivedFunctorPlus ⋙ R.rightDerivedFunctorPlus).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (asIso L.rightDerivedFunctorPlusUnith).inv R.rightDerivedFunctorPlus)
      (HomotopyCategory.Plus.quasiIso A) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (asIso L.rightDerivedFunctorPlusUnith).symm _)
  have hη : adj.rightDerivedFunctorPlus.unit =
      adj.mapHomotopyCategoryPlus.derivedη (HomotopyCategory.Plus.quasiIso A)
        (asIso L.rightDerivedFunctorPlusUnith).inv R.rightDerivedFunctorPlusUnith := rfl
  rw [hη]
  apply Localization.natTrans_ext DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A)
  intro K
  have h1 := adj.mapHomotopyCategoryPlus.derivedη_fac_app (HomotopyCategory.Plus.quasiIso A)
    (asIso L.rightDerivedFunctorPlusUnith).inv R.rightDerivedFunctorPlusUnith K
  have h2 := Functor.rightDerivedFunctorPlusCompIsoOfExact_fac L R (L ⋙ R) (Iso.refl _) K
  have h3 := mapHomotopyCategoryPlus_unit_app_comp adj K
  rw [Iso.trans_inv, NatTrans.comp_app, ← cancel_mono
    ((Functor.rightDerivedFunctorPlusCompIsoOfExact L R (L ⋙ R) (Iso.refl _)).hom.app _),
    Category.assoc, Iso.inv_hom_id_app, Category.comp_id,
    Functor.rightDerivedFunctorPlusIdIsoOf_inv_app, Functor.mapHomotopyCategoryPlusIdIsoOf_inv_app]
  have hId : R.rightDerivedFunctorPlus.map ((asIso L.rightDerivedFunctorPlusUnith).inv.app K) ≫
      R.rightDerivedFunctorPlus.map (L.rightDerivedFunctorPlusUnith.app K) = 𝟙 _ :=
    (R.rightDerivedFunctorPlus.map_comp _ _).symm.trans
      ((congrArg R.rightDerivedFunctorPlus.map
        (Iso.inv_hom_id_app (asIso L.rightDerivedFunctorPlusUnith) K)).trans
        (CategoryTheory.Functor.map_id _ _))
  rw [Iso.symm_inv, asIso_hom, ← h3, DerivedCategory.Plus.Qh.map_comp, Category.assoc, ← h2,
    ← reassoc_of% h1, reassoc_of% hId]

end CategoryTheory.Adjunction
