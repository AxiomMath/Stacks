module

public import StacksFrontier.CategoryTheory.Localization.BifunctorCommShiftTwoLiftingIso
public import StacksFrontier.CategoryTheory.Localization.BifunctorLiftNatTransCommShift
public import StacksFrontier.CategoryTheory.Shift.CommShiftTwoPostcomp
public import StacksFrontier.CategoryTheory.Shift.DetectingCommShift
public import StacksFrontier.Homology.KFlat.BifunctorCommShiftTwoInstances
public import StacksFrontier.Homology.KFlat.BifunctorModelComparison

/-!
# The comparison of the derived bifunctor at two models commutes with the shifts

For an additive bifunctor `F : A ⥤ B ⥤ D`, `CochainComplex.KFlatBifunctor.derivedBifunctorModelIso`
compares the derived bifunctors `T₁`, `T₂` of `Tot(F(-, -))` at two choices of models of `D(A)`,
`D(B)` and `D(D)`, through comparison functors `G_A`, `G_B`, `G_D` carrying the localization
functors `Qh` of the first models to those of the second: `T₂(G_A K, G_B L) ≅ G_D(T₁(K, L))`. Each
derived bifunctor commutes with the shifts in both variables
(`CochainComplex.KFlatBifunctor.derivedBifunctor_commShift₂Int`). This file shows that, when the
comparison functors and the identifications of the `Qh` commute with the shift, so does the
comparison isomorphism, in both variables.

## Main results

* `CochainComplex.KFlatBifunctor.derivedBifunctorModelIso_hom_commShift₂Int`: the comparison
  isomorphism `T₂(G_A K, G_B L) ≅ G_D(T₁(K, L))` commutes with the shifts in both variables.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.KFlatBifunctor

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
  (hA₁ hA₂ : HasDerivedCategory A) (hB₁ hB₂ : HasDerivedCategory B)
  (hD₁ hD₂ : HasDerivedCategory D)
  (resL : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
    KFlatLeft F P ∧ QuasiIso f)
  (resR : ∀ G : CochainComplex B ℤ, ∃ (P : CochainComplex B ℤ) (f : P ⟶ G),
    KFlat F P ∧ QuasiIso f)
  (GA : @DerivedCategory A _ _ hA₁ ⥤ @DerivedCategory A _ _ hA₂)
  (GB : @DerivedCategory B _ _ hB₁ ⥤ @DerivedCategory B _ _ hB₂)
  (GD : @DerivedCategory D _ _ hD₁ ⥤ @DerivedCategory D _ _ hD₂)
  (eA : @DerivedCategory.Qh A _ _ hA₁ ⋙ GA ≅ @DerivedCategory.Qh A _ _ hA₂)
  (eB : @DerivedCategory.Qh B _ _ hB₁ ⋙ GB ≅ @DerivedCategory.Qh B _ _ hB₂)
  (eD : @DerivedCategory.Qh D _ _ hD₁ ⋙ GD ≅ @DerivedCategory.Qh D _ _ hD₂)
  [GA.CommShift ℤ] [GB.CommShift ℤ] [GD.CommShift ℤ] [GD.Additive]
  [NatTrans.CommShift eA.hom ℤ] [NatTrans.CommShift eB.hom ℤ] [NatTrans.CommShift eD.hom ℤ]

/-- **The comparison of the derived bifunctor at two models commutes with the shifts in both
variables.** If the comparison functors `G_A`, `G_B`, `G_D` commute with the shift, `G_D` is
additive, and the identifications `eA`, `eB`, `eD` of the localization functors `Qh` are
compatible with the shift, then `derivedBifunctorModelIso : T₂(G_A K, G_B L) ≅ G_D(T₁(K, L))` is
compatible with the shifts of `K` and of `L`. Here each derived bifunctor carries
`CochainComplex.KFlatBifunctor.derivedBifunctor_commShift₂Int`, the source bifunctor its
precomposition with `G_A` and `G_B` (`CategoryTheory.Functor.CommShift₂.precomp₁`, `precomp₂`) and
the target its postcomposition with `G_D` (`CategoryTheory.Functor.CommShift₂.postcompInt`). -/
theorem derivedBifunctorModelIso_hom_commShift₂Int :
    letI := @kFlatQLeft_isLocalization _ _ _ _ _ _ _ _ _ F _ _ _ hA₁ resL
    letI := @kFlatQ_isLocalization _ _ _ _ _ _ _ _ _ F _ _ _ hB₁ resR
    letI := @kFlatQLeft_isLocalization _ _ _ _ _ _ _ _ _ F _ _ _ hA₂ resL
    letI := @kFlatQ_isLocalization _ _ _ _ _ _ _ _ _ F _ _ _ hB₂ resR
    letI := @derivedBifunctor_commShift₂Int _ _ _ _ _ _ _ _ _ F _ _ _ hA₁ hB₁ hD₁ _ _
    letI := @derivedBifunctor_commShift₂Int _ _ _ _ _ _ _ _ _ F _ _ _ hA₂ hB₂ hD₂ _ _
    letI : ∀ n : ℤ, (CategoryTheory.shiftFunctor (@DerivedCategory D _ _ hD₁) n).Additive :=
      fun _ => inferInstance
    letI : ∀ n : ℤ, (CategoryTheory.shiftFunctor (@DerivedCategory D _ _ hD₂) n).Additive :=
      fun _ => inferInstance
    NatTrans.CommShift₂Int
      (derivedBifunctorModelIso F hA₁ hA₂ hB₁ hB₂ hD₁ hD₂ resL resR GA GB GD eA eB eD).hom := by
  let := @kFlatQLeft_isLocalization _ _ _ _ _ _ _ _ _ F _ _ _ hA₁ resL
  let := @kFlatQ_isLocalization _ _ _ _ _ _ _ _ _ F _ _ _ hB₁ resR
  let := @kFlatQLeft_isLocalization _ _ _ _ _ _ _ _ _ F _ _ _ hA₂ resL
  let := @kFlatQ_isLocalization _ _ _ _ _ _ _ _ _ F _ _ _ hB₂ resR
  let := @derivedBifunctor_commShift₂Int _ _ _ _ _ _ _ _ _ F _ _ _ hA₁ hB₁ hD₁ _ _
  let := @derivedBifunctor_commShift₂Int _ _ _ _ _ _ _ _ _ F _ _ _ hA₂ hB₂ hD₂ _ _
  let : ∀ n : ℤ, (CategoryTheory.shiftFunctor (@DerivedCategory D _ _ hD₁) n).Additive :=
    fun _ ↦ inferInstance
  let : ∀ n : ℤ, (CategoryTheory.shiftFunctor (@DerivedCategory D _ _ hD₂) n).Additive :=
    fun _ ↦ inferInstance
  let : CategoryTheory.Localization.Lifting₂ (@kFlatQLeft _ _ _ _ _ _ _ _ _ F _ _ _ hA₁)
      (@kFlatQ _ _ _ _ _ _ _ _ _ F _ _ _ hB₁)
      (kFlatQuasiIsoLeft F) (kFlatQuasiIso F) (@kFlatToDerived _ _ _ _ _ _ _ _ _ F _ _ _ hD₂)
      (derivedBifunctorModel₂ F hA₁ hA₂ hB₁ hB₂ hD₂ resL resR GA GB) :=
    ⟨derivedBifunctorModel₂LiftingIso F hA₁ hA₂ hB₁ hB₂ hD₂ resL resR GA GB eA eB⟩
  let : CategoryTheory.Localization.Lifting₂ (@kFlatQLeft _ _ _ _ _ _ _ _ _ F _ _ _ hA₁)
      (@kFlatQ _ _ _ _ _ _ _ _ _ F _ _ _ hB₁)
      (kFlatQuasiIsoLeft F) (kFlatQuasiIso F) (@kFlatToDerived _ _ _ _ _ _ _ _ _ F _ _ _ hD₂)
      (derivedBifunctorModel₁ F hA₁ hB₁ hD₁ hD₂ resL resR GD) :=
    ⟨CategoryTheory.Localization.Lifting₂.iso (@kFlatQLeft _ _ _ _ _ _ _ _ _ F _ _ _ hA₁)
        (@kFlatQ _ _ _ _ _ _ _ _ _ F _ _ _ hB₁)
        (kFlatQuasiIsoLeft F) (kFlatQuasiIso F)
        (@kFlatToDerived _ _ _ _ _ _ _ _ _ F _ _ _ hD₁ ⋙ (Functor.whiskeringRight _ _ _).obj GD)
        (derivedBifunctorModel₁ F hA₁ hB₁ hD₁ hD₂ resL resR GD) ≪≫
      kFlatToDerivedModelIso F hD₁ hD₂ GD eD⟩
  have hid : NatTrans.CommShift₂Int
      (Iso.refl (@kFlatToDerived _ _ _ _ _ _ _ _ _ F _ _ _ hD₂)).hom :=
    inferInstanceAs (NatTrans.CommShift₂Int (𝟙 (@kFlatToDerived _ _ _ _ _ _ _ _ _ F _ _ _ hD₂)))
  let iL := Functor.associator (kFlatObjectsLeft F).ι (@DerivedCategory.Qh A _ _ hA₁) GA ≪≫
    Functor.isoWhiskerLeft (kFlatObjectsLeft F).ι eA
  let iR := Functor.associator (kFlatObjects F).ι (@DerivedCategory.Qh B _ _ hB₁) GB ≪≫
    Functor.isoWhiskerLeft (kFlatObjects F).ι eB
  let T₁ := @derivedBifunctor _ _ _ _ _ _ _ _ _ F _ _ _ hA₁ hB₁ hD₁ _ _
  let T₂ := @derivedBifunctor _ _ _ _ _ _ _ _ _ F _ _ _ hA₂ hB₂ hD₂ _ _
  let j₁ := CategoryTheory.Localization.Lifting₂.iso
    (@kFlatQLeft _ _ _ _ _ _ _ _ _ F _ _ _ hA₁) (@kFlatQ _ _ _ _ _ _ _ _ _ F _ _ _ hB₁)
    (kFlatQuasiIsoLeft F) (kFlatQuasiIso F) (@kFlatToDerived _ _ _ _ _ _ _ _ _ F _ _ _ hD₁) T₁
  let j₂ := CategoryTheory.Localization.Lifting₂.iso
    (@kFlatQLeft _ _ _ _ _ _ _ _ _ F _ _ _ hA₂) (@kFlatQ _ _ _ _ _ _ _ _ _ F _ _ _ hB₂)
    (kFlatQuasiIsoLeft F) (kFlatQuasiIso F) (@kFlatToDerived _ _ _ _ _ _ _ _ _ F _ _ _ hD₂) T₂
  have c₁ := CategoryTheory.Localization.lifting₂_iso_hom_commShift₂Int
    (@kFlatQLeft _ _ _ _ _ _ _ _ _ F _ _ _ hA₁) (@kFlatQ _ _ _ _ _ _ _ _ _ F _ _ _ hB₁)
    (kFlatQuasiIsoLeft F) (kFlatQuasiIso F) (@kFlatToDerived _ _ _ _ _ _ _ _ _ F _ _ _ hD₁) T₁
  have c₂ := CategoryTheory.Localization.lifting₂_iso_hom_commShift₂Int
    (@kFlatQLeft _ _ _ _ _ _ _ _ _ F _ _ _ hA₂) (@kFlatQ _ _ _ _ _ _ _ _ _ F _ _ _ hB₂)
    (kFlatQuasiIsoLeft F) (kFlatQuasiIso F) (@kFlatToDerived _ _ _ _ _ _ _ _ _ F _ _ _ hD₂) T₂
  have hL : NatTrans.CommShift iL.hom ℤ :=
    inferInstanceAs (NatTrans.CommShift ((Functor.associator (kFlatObjectsLeft F).ι
      (@DerivedCategory.Qh A _ _ hA₁) GA).hom ≫
        Functor.whiskerLeft (kFlatObjectsLeft F).ι eA.hom) ℤ)
  have hR : NatTrans.CommShift iR.hom ℤ :=
    inferInstanceAs (NatTrans.CommShift ((Functor.associator (kFlatObjects F).ι
      (@DerivedCategory.Qh B _ _ hB₁) GB).hom ≫
        Functor.whiskerLeft (kFlatObjects F).ι eB.hom) ℤ)
  refine CategoryTheory.Localization.lift₂NatIso_hom_commShift₂
    (@kFlatQLeft _ _ _ _ _ _ _ _ _ F _ _ _ hA₁) (@kFlatQ _ _ _ _ _ _ _ _ _ F _ _ _ hB₁)
    (kFlatQuasiIsoLeft F) (kFlatQuasiIso F) (@kFlatToDerived _ _ _ _ _ _ _ _ _ F _ _ _ hD₂)
    (@kFlatToDerived _ _ _ _ _ _ _ _ _ F _ _ _ hD₂) _ _ (Iso.refl _) ?_ ?_ ?_ ?_
  · intro X₁
    have := c₂.commShift_app X₁
    refine NatTrans.commShift_of_eq
        (θ := (Functor.associator (@kFlatQ _ _ _ _ _ _ _ _ _ F _ _ _ hB₁) GB
          (T₂.obj (GA.obj ((@kFlatQLeft _ _ _ _ _ _ _ _ _ F _ _ _ hA₁).obj X₁)))).inv ≫
      Functor.whiskerLeft (@kFlatQ _ _ _ _ _ _ _ _ _ F _ _ _ hB₁ ⋙ GB)
        (T₂.map (iL.hom.app X₁)) ≫
      Functor.whiskerRight iR.hom (T₂.obj ((@kFlatQLeft _ _ _ _ _ _ _ _ _ F _ _ _ hA₂).obj X₁)) ≫
      j₂.hom.app X₁) ?_
    ext K
    change ((derivedBifunctorModel₂LiftingIso F hA₁ hA₂ hB₁ hB₂ hD₂ resL resR GA GB eA eB).hom.app
      X₁).app K = _
    simp [derivedBifunctorModel₂LiftingIso, iL, iR, j₂, T₂]
  · intro X₁
    have := c₁.commShift_app X₁
    let : ((((Functor.whiskeringLeft₂ _).obj (@kFlatQLeft _ _ _ _ _ _ _ _ _ F _ _ _ hA₁)).obj
        (@kFlatQ _ _ _ _ _ _ _ _ _ F _ _ _ hB₁)).obj T₁).CommShift₂Int :=
      inferInstanceAs ((@kFlatQLeft _ _ _ _ _ _ _ _ _ F _ _ _ hA₁ ⋙ (T₁ ⋙
        (Functor.whiskeringLeft _ _ _).obj (@kFlatQ _ _ _ _ _ _ _ _ _ F _ _ _ hB₁))).CommShift₂Int)
    refine NatTrans.commShift_of_eq (θ := (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (j₁.hom.app X₁) GD ≫
      (Functor.associator (kFlatObjects F).ι
        ((homotopyBifunctor F).obj ((kFlatObjectsLeft F).ι.obj X₁) ⋙
          @DerivedCategory.Qh D _ _ hD₁) GD).hom ≫
      Functor.whiskerLeft (kFlatObjects F).ι (Functor.associator
        ((homotopyBifunctor F).obj ((kFlatObjectsLeft F).ι.obj X₁))
          (@DerivedCategory.Qh D _ _ hD₁) GD).hom ≫
      Functor.whiskerLeft (kFlatObjects F).ι (Functor.whiskerLeft
        ((homotopyBifunctor F).obj ((kFlatObjectsLeft F).ι.obj X₁)) eD.hom)) ?_
    ext K
    change (((Functor.isoWhiskerRight j₁ ((Functor.whiskeringRight _ _ _).obj GD) ≪≫
        kFlatToDerivedModelIso F hD₁ hD₂ GD eD).hom.app X₁).app K) = _
    simp [kFlatToDerivedModelIso, j₁, T₁]
  · intro X₂
    have := c₂.commShift_flipApp X₂
    refine NatTrans.commShift_of_eq
        (θ := (Functor.associator (@kFlatQLeft _ _ _ _ _ _ _ _ _ F _ _ _ hA₁) GA
          (T₂.flip.obj (GB.obj ((@kFlatQ _ _ _ _ _ _ _ _ _ F _ _ _ hB₁).obj X₂)))).inv ≫
      Functor.whiskerRight iL.hom
        (T₂.flip.obj (GB.obj ((@kFlatQ _ _ _ _ _ _ _ _ _ F _ _ _ hB₁).obj X₂))) ≫
      Functor.whiskerLeft (@kFlatQLeft _ _ _ _ _ _ _ _ _ F _ _ _ hA₂)
        (T₂.flip.map (iR.hom.app X₂)) ≫
      j₂.hom.flipApp X₂) ?_
    ext K
    change ((derivedBifunctorModel₂LiftingIso F hA₁ hA₂ hB₁ hB₂ hD₂ resL resR GA GB eA eB).hom.app
      K).app X₂ = _
    simp [derivedBifunctorModel₂LiftingIso, iL, iR, j₂, T₂]
  · intro X₂
    have := c₁.commShift_flipApp X₂
    let : ((((Functor.whiskeringLeft₂ _).obj (@kFlatQLeft _ _ _ _ _ _ _ _ _ F _ _ _ hA₁)).obj
        (@kFlatQ _ _ _ _ _ _ _ _ _ F _ _ _ hB₁)).obj T₁).CommShift₂Int :=
      inferInstanceAs ((@kFlatQLeft _ _ _ _ _ _ _ _ _ F _ _ _ hA₁ ⋙ (T₁ ⋙
        (Functor.whiskeringLeft _ _ _).obj (@kFlatQ _ _ _ _ _ _ _ _ _ F _ _ _ hB₁))).CommShift₂Int)
    refine NatTrans.commShift_of_eq
        (θ := (Functor.associator (@kFlatQLeft _ _ _ _ _ _ _ _ _ F _ _ _ hA₁)
        (T₁.flip.obj ((@kFlatQ _ _ _ _ _ _ _ _ _ F _ _ _ hB₁).obj X₂)) GD).inv ≫
      Functor.whiskerRight (j₁.hom.flipApp X₂) GD ≫
      (Functor.associator (kFlatObjectsLeft F).ι
        ((homotopyBifunctor F).flip.obj ((kFlatObjects F).ι.obj X₂) ⋙
          @DerivedCategory.Qh D _ _ hD₁) GD).hom ≫
      Functor.whiskerLeft (kFlatObjectsLeft F).ι (Functor.associator
        ((homotopyBifunctor F).flip.obj ((kFlatObjects F).ι.obj X₂))
          (@DerivedCategory.Qh D _ _ hD₁) GD).hom ≫
      Functor.whiskerLeft (kFlatObjectsLeft F).ι (Functor.whiskerLeft
        ((homotopyBifunctor F).flip.obj ((kFlatObjects F).ι.obj X₂)) eD.hom)) ?_
    ext K
    change (((Functor.isoWhiskerRight j₁ ((Functor.whiskeringRight _ _ _).obj GD) ≪≫
        kFlatToDerivedModelIso F hD₁ hD₂ GD eD).hom.app K).app X₂) = _
    simp [kFlatToDerivedModelIso, j₁, T₁]

end CochainComplex.KFlatBifunctor

end
