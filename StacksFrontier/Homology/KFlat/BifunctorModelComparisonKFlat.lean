module

public import StacksFrontier.Homology.KFlat.BifunctorModelComparison
public import StacksFrontier.Homology.KFlat.BifunctorOneSided

/-!
# The derived bifunctor at two models, on K-flat representatives

For an additive bifunctor `F : A ⥤ B ⥤ D`, two results on the components of the derived
bifunctor `CochainComplex.KFlatBifunctor.derivedBifunctor F` at K-flat representatives.

## Main results

* `CochainComplex.KFlatBifunctor.comparisonRight_hom_eq_of_kFlatLeft` — when the left complex is
  also left K-flat, the one-sided comparison `comparisonRight` is the `Qh ∘ quotient` versus `Q`
  bridges in both variables, then the descent isomorphism `derivedBifunctorComparisonIso` at the
  two K-flat classes, then `totalComplexQhIso`.
* `CochainComplex.KFlatBifunctor.derivedBifunctorModelIso_hom_app_app` — the component of the
  comparison `derivedBifunctorModelIso` of two models at a pair of K-flat classes: the
  comparisons of the localizations in each variable, the descent isomorphism at the second
  models, the comparison of the localizations of `D(D)` and the image of the inverse of the descent
  isomorphism at the first models; `derivedBifunctorModelIso_hom_app_app_quotient` is the same at
  the homotopy classes of two complexes.
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

/-- Generic shape of the middle factor in `comparisonRight_hom_eq_of_kFlatLeft`. -/
private lemma comparisonRightFac_hom_app_aux {C' : Type*} [Category C'] {p q s t v : C'}
    (ρp : p ⟶ s) (ρq : q ⟶ t) (m : p ⟶ q) (n : s ≅ t) (hnat : m ≫ ρq = ρp ≫ n.hom)
    (c : q ⟶ v) (hinv : v ⟶ t) (fac : s ≅ v) (hX : ρq = c ≫ hinv)
    (hq : hinv = fac.inv ≫ n.hom) : ρp ≫ fac.hom = m ≫ c := by
  have hp : ρp = m ≫ ρq ≫ n.inv := by rw [reassoc_of% hnat, Iso.hom_inv_id, Category.comp_id]
  rw [hp, hX, hq]
  simp

/-- The component at `L.obj X` of the preimage of `e` under precomposition with a localization
functor `L` is `e.app X`. -/
private lemma preimageIso_whiskeringLeft_app {C' D' E' : Type*} [Category C'] [Category D']
    [Category E'] (L : C' ⥤ D') (W : MorphismProperty C') [L.IsLocalization W] {G H : D' ⥤ E'}
    (e : L ⋙ G ≅ L ⋙ H) (X : C') :
    ((CategoryTheory.Localization.fullyFaithfulWhiskeringLeft L W E').preimageIso e).app
      (L.obj X) = e.app X :=
  Iso.ext (congrArg (fun σ => σ.app X)
    ((CategoryTheory.Localization.fullyFaithfulWhiskeringLeft L W E').map_preimage e.hom))

section OneModel

variable [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]
  [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)]

/-- The component of `derivedBifunctorRightIso` at the class of a left K-flat object. -/
theorem derivedBifunctorRightIso_hom_app_kFlatQLeft_eq_comp
    (X : (kFlatObjectsLeft F).FullSubcategory) :
    (derivedBifunctorRightIso F).hom.app ((kFlatQLeft F).obj X) =
      (derivedBifunctorComparisonIso F).hom.app X ≫
        (homotopyToDerivedRightIso F).inv.app X.obj := by
  refine (congrArg Iso.hom (preimageIso_whiskeringLeft_app _ _ _ X)).trans ?_
  simp

omit [HasDerivedCategory B] [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)] in
/-- The component of `homotopyToDerivedRightIso` at the class of a complex. -/
theorem homotopyToDerivedRightIso_inv_app_quotient (K : CochainComplex A ℤ) :
    (homotopyToDerivedRightIso F).inv.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)
        =
      (derivedToDerivedRightFac F).inv.app K ≫
        (derivedToDerivedRight F).map ((DerivedCategory.quotientCompQhIso A).inv.app K) := by
  refine (congrArg Iso.inv (preimageIso_whiskeringLeft_app _ _ _ K)).trans ?_
  simp

/-- **The one-sided comparison on a pair of K-flat complexes**: when `K` is left K-flat,
`comparisonRight F K L hL` is the `Qh ∘ quotient` versus `Q` bridges in both variables, the
descent isomorphism `derivedBifunctorComparisonIso` at the two K-flat classes, and
`totalComplexQhIso`. -/
theorem comparisonRight_hom_eq_of_kFlatLeft (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (hK : KFlatLeft F K) (hL : KFlat F L) :
    (comparisonRight F K L hL).hom =
      ((derivedBifunctor F).obj (DerivedCategory.Q.obj K)).map
          ((DerivedCategory.quotientCompQhIso B).inv.app L) ≫
        ((derivedBifunctor F).map ((DerivedCategory.quotientCompQhIso A).inv.app K)).app
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).obj L) ≫
        ((derivedBifunctorComparisonIso F).hom.app
            ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩).app
          ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩ ≫
        (totalComplexQhIso F K L).hom := by
  rw [comparisonRight_hom]
  have H : (comparisonRightFac F).hom.app K =
      (derivedBifunctorRight F).map ((DerivedCategory.quotientCompQhIso A).inv.app K) ≫
        (derivedBifunctorComparisonIso F).hom.app
          ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩ :=
    comparisonRightFac_hom_app_aux
    ((derivedBifunctorRightIso F).hom.app (DerivedCategory.Q.obj K))
    ((derivedBifunctorRightIso F).hom.app
      ((kFlatQLeft F).obj ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩))
    ((derivedBifunctorRight F).map ((DerivedCategory.quotientCompQhIso A).inv.app K))
    ((derivedToDerivedRight F).mapIso ((DerivedCategory.quotientCompQhIso A).app K).symm)
    ((derivedBifunctorRightIso F).hom.naturality
      ((DerivedCategory.quotientCompQhIso A).inv.app K))
    ((derivedBifunctorComparisonIso F).hom.app
      ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩)
    ((homotopyToDerivedRightIso F).inv.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
        K))
    ((derivedToDerivedRightFac F).app K)
    (derivedBifunctorRightIso_hom_app_kFlatQLeft_eq_comp F
      ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩)
    (homotopyToDerivedRightIso_inv_app_quotient F K)
  have H' := congrArg (fun τ => NatTrans.app τ
    (⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩ :
      (kFlatObjects F).FullSubcategory)) H
  simp only [NatTrans.comp_app] at H'
  rw [H', Category.assoc]
  rfl

end OneModel

section TwoModels

variable (hA₁ hA₂ : HasDerivedCategory A) (hB₁ hB₂ : HasDerivedCategory B)
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

/-- **The comparison of the derived bifunctor at two models, at a pair of K-flat classes**: the
comparisons `eA`, `eB` of the localizations in each variable, the descent isomorphism
`derivedBifunctorComparisonIso` at the second models, the comparison `eD` of the localizations of
`D(D)`, and the image under `GD` of the inverse of the descent isomorphism at the first models. -/
theorem derivedBifunctorModelIso_hom_app_app (X : (kFlatObjectsLeft F).FullSubcategory)
    (Y : (kFlatObjects F).FullSubcategory) :
    ((derivedBifunctorModelIso F hA₁ hA₂ hB₁ hB₂ hD₁ hD₂ resL resR GA GB GD eA eB eD).hom.app
        ((@kFlatQLeft _ _ _ _ _ _ _ _ _ F _ _ _ hA₁).obj X)).app
        ((@kFlatQ _ _ _ _ _ _ _ _ _ F _ _ _ hB₁).obj Y) =
      ((@derivedBifunctor _ _ _ _ _ _ _ _ _ F _ _ _ hA₂ hB₂ hD₂
          (@kFlatQLeft_isLocalization _ _ _ _ _ _ _ _ _ F _ _ _ hA₂ resL)
          (@kFlatQ_isLocalization _ _ _ _ _ _ _ _ _ F _ _ _ hB₂ resR)).map
          (eA.hom.app X.obj)).app (GB.obj ((@kFlatQ _ _ _ _ _ _ _ _ _ F _ _ _ hB₁).obj Y)) ≫
        ((@derivedBifunctor _ _ _ _ _ _ _ _ _ F _ _ _ hA₂ hB₂ hD₂
          (@kFlatQLeft_isLocalization _ _ _ _ _ _ _ _ _ F _ _ _ hA₂ resL)
          (@kFlatQ_isLocalization _ _ _ _ _ _ _ _ _ F _ _ _ hB₂ resR)).obj
            ((@DerivedCategory.Qh A _ _ hA₂).obj X.obj)).map (eB.hom.app Y.obj) ≫
        ((@derivedBifunctorComparisonIso _ _ _ _ _ _ _ _ _ F _ _ _ hA₂ hB₂ hD₂
          (@kFlatQLeft_isLocalization _ _ _ _ _ _ _ _ _ F _ _ _ hA₂ resL)
          (@kFlatQ_isLocalization _ _ _ _ _ _ _ _ _ F _ _ _ hB₂ resR)).hom.app X).app Y ≫
        eD.inv.app (((homotopyBifunctor F).obj X.obj).obj Y.obj) ≫
        GD.map (((@derivedBifunctorComparisonIso _ _ _ _ _ _ _ _ _ F _ _ _ hA₁ hB₁ hD₁
          (@kFlatQLeft_isLocalization _ _ _ _ _ _ _ _ _ F _ _ _ hA₁ resL)
          (@kFlatQ_isLocalization _ _ _ _ _ _ _ _ _ F _ _ _ hB₁ resR)).inv.app X).app Y) := by
  dsimp only [derivedBifunctorModelIso, CategoryTheory.Localization.lift₂NatIso]
  rw [CategoryTheory.Localization.lift₂NatTrans_app_app]
  simp [derivedBifunctorModel₂LiftingIso, kFlatToDerivedModelIso, derivedBifunctorComparisonIso]
  rfl

/-- `derivedBifunctorModelIso_hom_app_app` at the homotopy classes of a left K-flat complex `K` and
a K-flat complex `L`, in the spelling of `DerivedCategory.quotientCompQhIso`. -/
theorem derivedBifunctorModelIso_hom_app_app_quotient (K : CochainComplex A ℤ)
    (L : CochainComplex B ℤ) (hK : KFlatLeft F K) (hL : KFlat F L) :
    ((derivedBifunctorModelIso F hA₁ hA₂ hB₁ hB₂ hD₁ hD₂ resL resR GA GB GD eA eB eD).hom.app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙ @DerivedCategory.Qh A _ _ hA₁).obj
            K)).app
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ) ⋙ @DerivedCategory.Qh B _ _ hB₁).obj L) =
      ((@derivedBifunctor _ _ _ _ _ _ _ _ _ F _ _ _ hA₂ hB₂ hD₂
          (@kFlatQLeft_isLocalization _ _ _ _ _ _ _ _ _ F _ _ _ hA₂ resL)
          (@kFlatQ_isLocalization _ _ _ _ _ _ _ _ _ F _ _ _ hB₂ resR)).map
          (eA.hom.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))).app
          (GB.obj ((HomotopyCategory.quotient B (ComplexShape.up ℤ) ⋙
            @DerivedCategory.Qh B _ _ hB₁).obj L)) ≫
        ((@derivedBifunctor _ _ _ _ _ _ _ _ _ F _ _ _ hA₂ hB₂ hD₂
          (@kFlatQLeft_isLocalization _ _ _ _ _ _ _ _ _ F _ _ _ hA₂ resL)
          (@kFlatQ_isLocalization _ _ _ _ _ _ _ _ _ F _ _ _ hB₂ resR)).obj
            ((@DerivedCategory.Qh A _ _ hA₂).obj
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))).map
          (eB.hom.app ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L)) ≫
        ((@derivedBifunctorComparisonIso _ _ _ _ _ _ _ _ _ F _ _ _ hA₂ hB₂ hD₂
          (@kFlatQLeft_isLocalization _ _ _ _ _ _ _ _ _ F _ _ _ hA₂ resL)
          (@kFlatQ_isLocalization _ _ _ _ _ _ _ _ _ F _ _ _ hB₂ resR)).hom.app
            ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩).app
            ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩ ≫
        eD.inv.app (((homotopyBifunctor F).obj
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)).obj
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L)) ≫
        GD.map (((@derivedBifunctorComparisonIso _ _ _ _ _ _ _ _ _ F _ _ _ hA₁ hB₁ hD₁
          (@kFlatQLeft_isLocalization _ _ _ _ _ _ _ _ _ F _ _ _ hA₁ resL)
          (@kFlatQ_isLocalization _ _ _ _ _ _ _ _ _ F _ _ _ hB₁ resR)).inv.app
            ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩).app
            ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩) :=
  derivedBifunctorModelIso_hom_app_app F hA₁ hA₂ hB₁ hB₂ hD₁ hD₂ resL resR GA GB GD eA eB eD
    ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩
    ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩

end TwoModels

end CochainComplex.KFlatBifunctor

end
