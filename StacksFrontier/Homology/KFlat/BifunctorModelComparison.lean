module

public import StacksFrontier.Homology.KFlat.BifunctorLocalization

/-!
# The derived bifunctor read at two models of the derived categories

`HasDerivedCategory` is a choice of localization, so the derived bifunctor
`CochainComplex.KFlatBifunctor.derivedBifunctor F` of `Tot(F(-, -))` is a different functor at
every choice of models of `D(A)`, `D(B)` and `D(D)`. Given comparison functors `G_A`, `G_B`,
`G_D` between two choices which carry the localization functors `Qh` of the first to those of the
second, the two derived bifunctors agree: `T₂(G_A K, G_B L) ≅ G_D(T₁(K, L))`, naturally in both
variables. Both sides are lifts, along the K-flat localizations of the first models, of
`Tot(F(-, -))` read in the second model of `D(D)`, and such a lift is unique.

## Main definitions

* `CochainComplex.KFlatBifunctor.derivedBifunctorModelIso` — the comparison isomorphism.

Its components on K-flat representatives are computed by Mathlib's
`CategoryTheory.Localization.lift₂NatTrans_app_app`, the two lifting isomorphisms being
`derivedBifunctorModel₂LiftingIso` and that of `derivedBifunctor` followed by
`kFlatToDerivedModelIso`.
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

/-- The derived bifunctor at the first models, followed by the comparison of `D(D)`. -/
abbrev derivedBifunctorModel₁ :
    @DerivedCategory A _ _ hA₁ ⥤ @DerivedCategory B _ _ hB₁ ⥤ @DerivedCategory D _ _ hD₂ :=
  haveI := @kFlatQLeft_isLocalization _ _ _ _ _ _ _ _ _ F _ _ _ hA₁ resL
  haveI := @kFlatQ_isLocalization _ _ _ _ _ _ _ _ _ F _ _ _ hB₁ resR
  @derivedBifunctor _ _ _ _ _ _ _ _ _ F _ _ _ hA₁ hB₁ hD₁ _ _ ⋙
    (Functor.whiskeringRight _ _ _).obj GD

/-- The derived bifunctor at the second models, precomposed with the comparisons of `D(A)` and
`D(B)`. -/
abbrev derivedBifunctorModel₂ :
    @DerivedCategory A _ _ hA₁ ⥤ @DerivedCategory B _ _ hB₁ ⥤ @DerivedCategory D _ _ hD₂ :=
  haveI := @kFlatQLeft_isLocalization _ _ _ _ _ _ _ _ _ F _ _ _ hA₂ resL
  haveI := @kFlatQ_isLocalization _ _ _ _ _ _ _ _ _ F _ _ _ hB₂ resR
  GA ⋙ @derivedBifunctor _ _ _ _ _ _ _ _ _ F _ _ _ hA₂ hB₂ hD₂ _ _ ⋙
    (Functor.whiskeringLeft _ _ _).obj GB

/-- `Tot(F(-, -))` on the K-flat objects, read in the first model of `D(D)` and followed by the
comparison, is `Tot(F(-, -))` read in the second model. -/
def kFlatToDerivedModelIso :
    @kFlatToDerived _ _ _ _ _ _ _ _ _ F _ _ _ hD₁ ⋙ (Functor.whiskeringRight _ _ _).obj GD ≅
      @kFlatToDerived _ _ _ _ _ _ _ _ _ F _ _ _ hD₂ :=
  (((Functor.whiskeringLeft₂ _).obj (kFlatObjectsLeft F).ι).obj (kFlatObjects F).ι).mapIso
    (Functor.isoWhiskerLeft (homotopyBifunctor F) ((Functor.whiskeringRight _ _ _).mapIso eD))

/-- The second-model derived bifunctor, precomposed with the comparisons, lifts `Tot(F(-, -))`
read in the second model of `D(D)` along the K-flat localizations of the first models. -/
def derivedBifunctorModel₂LiftingIso :
    (((Functor.whiskeringLeft₂ _).obj (@kFlatQLeft _ _ _ _ _ _ _ _ _ F _ _ _ hA₁)).obj
        (@kFlatQ _ _ _ _ _ _ _ _ _ F _ _ _ hB₁)).obj
        (derivedBifunctorModel₂ F hA₁ hA₂ hB₁ hB₂ hD₂ resL resR GA GB) ≅
      @kFlatToDerived _ _ _ _ _ _ _ _ _ F _ _ _ hD₂ :=
  letI := @kFlatQLeft_isLocalization _ _ _ _ _ _ _ _ _ F _ _ _ hA₂ resL
  letI := @kFlatQ_isLocalization _ _ _ _ _ _ _ _ _ F _ _ _ hB₂ resR
  let T₂ := @derivedBifunctor _ _ _ _ _ _ _ _ _ F _ _ _ hA₂ hB₂ hD₂ _ _
  let eL : @kFlatQLeft _ _ _ _ _ _ _ _ _ F _ _ _ hA₁ ⋙ GA ≅
      @kFlatQLeft _ _ _ _ _ _ _ _ _ F _ _ _ hA₂ :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (kFlatObjectsLeft F).ι eA
  let eR : @kFlatQ _ _ _ _ _ _ _ _ _ F _ _ _ hB₁ ⋙ GB ≅
      @kFlatQ _ _ _ _ _ _ _ _ _ F _ _ _ hB₂ :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (kFlatObjects F).ι eB
  (Iso.refl _ : _ ≅ (((Functor.whiskeringLeft₂ _).obj
      (@kFlatQLeft _ _ _ _ _ _ _ _ _ F _ _ _ hA₁ ⋙ GA)).obj
      (@kFlatQ _ _ _ _ _ _ _ _ _ F _ _ _ hB₁ ⋙ GB)).obj T₂) ≪≫
    (((Functor.whiskeringLeft₂ _).mapIso eL).app _).app T₂ ≪≫
    (((Functor.whiskeringLeft₂ _).obj (@kFlatQLeft _ _ _ _ _ _ _ _ _ F _ _ _ hA₂)).mapIso eR).app
      T₂ ≪≫
    CategoryTheory.Localization.Lifting₂.iso
      (@kFlatQLeft _ _ _ _ _ _ _ _ _ F _ _ _ hA₂) (@kFlatQ _ _ _ _ _ _ _ _ _ F _ _ _ hB₂)
      (kFlatQuasiIsoLeft F) (kFlatQuasiIso F)
      (@kFlatToDerived _ _ _ _ _ _ _ _ _ F _ _ _ hD₂) T₂

/-- **The derived bifunctor at two models.** For comparison functors `G_A`, `G_B`, `G_D` between
two choices of models of `D(A)`, `D(B)` and `D(D)`, carrying the localization functors of the
first to those of the second, `T₂(G_A K, G_B L) ≅ G_D(T₁(K, L))` naturally in `K` and `L`, where
`T₁` and `T₂` are the derived bifunctors of `F` at the two choices. -/
def derivedBifunctorModelIso :
    derivedBifunctorModel₂ F hA₁ hA₂ hB₁ hB₂ hD₂ resL resR GA GB ≅
      derivedBifunctorModel₁ F hA₁ hB₁ hD₁ hD₂ resL resR GD :=
  letI := @kFlatQLeft_isLocalization _ _ _ _ _ _ _ _ _ F _ _ _ hA₁ resL
  letI := @kFlatQ_isLocalization _ _ _ _ _ _ _ _ _ F _ _ _ hB₁ resR
  letI : CategoryTheory.Localization.Lifting₂ (@kFlatQLeft _ _ _ _ _ _ _ _ _ F _ _ _ hA₁)
      (@kFlatQ _ _ _ _ _ _ _ _ _ F _ _ _ hB₁) (kFlatQuasiIsoLeft F) (kFlatQuasiIso F)
      (@kFlatToDerived _ _ _ _ _ _ _ _ _ F _ _ _ hD₂)
      (derivedBifunctorModel₂ F hA₁ hA₂ hB₁ hB₂ hD₂ resL resR GA GB) :=
    ⟨derivedBifunctorModel₂LiftingIso F hA₁ hA₂ hB₁ hB₂ hD₂ resL resR GA GB eA eB⟩
  letI : CategoryTheory.Localization.Lifting₂ (@kFlatQLeft _ _ _ _ _ _ _ _ _ F _ _ _ hA₁)
      (@kFlatQ _ _ _ _ _ _ _ _ _ F _ _ _ hB₁) (kFlatQuasiIsoLeft F) (kFlatQuasiIso F)
      (@kFlatToDerived _ _ _ _ _ _ _ _ _ F _ _ _ hD₂)
      (derivedBifunctorModel₁ F hA₁ hB₁ hD₁ hD₂ resL resR GD) :=
    ⟨CategoryTheory.Localization.Lifting₂.iso
        (@kFlatQLeft _ _ _ _ _ _ _ _ _ F _ _ _ hA₁) (@kFlatQ _ _ _ _ _ _ _ _ _ F _ _ _ hB₁)
        (kFlatQuasiIsoLeft F) (kFlatQuasiIso F)
        (@kFlatToDerived _ _ _ _ _ _ _ _ _ F _ _ _ hD₁ ⋙ (Functor.whiskeringRight _ _ _).obj GD)
        (derivedBifunctorModel₁ F hA₁ hB₁ hD₁ hD₂ resL resR GD) ≪≫
      kFlatToDerivedModelIso F hD₁ hD₂ GD eD⟩
  CategoryTheory.Localization.lift₂NatIso (@kFlatQLeft _ _ _ _ _ _ _ _ _ F _ _ _ hA₁)
    (@kFlatQ _ _ _ _ _ _ _ _ _ F _ _ _ hB₁) (kFlatQuasiIsoLeft F) (kFlatQuasiIso F)
    (@kFlatToDerived _ _ _ _ _ _ _ _ _ F _ _ _ hD₂) (@kFlatToDerived _ _ _ _ _ _ _ _ _ F _ _ _ hD₂)
    _ _ (Iso.refl _)

end CochainComplex.KFlatBifunctor

end
