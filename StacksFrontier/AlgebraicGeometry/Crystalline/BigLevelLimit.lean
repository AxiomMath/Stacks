module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareResolution
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigLevelInjective
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigLevelSurjective
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FrobeniusFactorization07N5
public import StacksFrontier.Algebra.Homology.Resolution.InjectiveResolution
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.EpiTowerLimitGeneral

/-!
# `RΓ(CRIS(X/S), N)` and the levels, computed on an injective resolution

Let `X/S` be a global crystalline situation with affine base, `A = Γ(S, 𝒪_S)`, and let
`e(n)` be an increasing unbounded sequence of levels (`S.LevelSequence`): the closed subschemes
`S_{e(n)} = V(p^{e(n)}) ⊂ S` carry the induced divided powers.  For a module `N` on the big site
`CRIS(X/S)` with restrictions `N_{e(n)}` to `CRIS(X/S_{e(n)})`, this file defines the objects
`RΓ(CRIS(X/S_{e(n)}), N_{e(n)})` of `D⁺(Mod_A)`, the derived comparisons of global sections along
`S_{e(n)} ⟶ S` and along `S_{e(n)} ⟶ S_{e(n+1)}`, and computes them on an injective resolution
`I` of `N`.

The restrictions of `I` to the levels are injective (`injective_levelPullback_obj`), so the
derived comparisons are the underived ones applied termwise.  The complex `Γ(CRIS(X/S), I)` is
degreewise the limit of the complexes `Γ(CRIS(X/S_{e(n)}), I_{e(n)})` (`isLimitLevelSectionsCone`),
and the transitions of this tower are surjective (`surjective_levelSectionsTransition`).

## Main definitions

* `GlobalCrystallineSituation.levelDerived`, `GlobalCrystallineSituation.levelDerivedProj` and
  `GlobalCrystallineSituation.levelDerivedTransition` — `RΓ(CRIS(X/S_{e(n)}), N_{e(n)})` in
  `D⁺(Mod_A)` and the derived comparisons.
* `GlobalCrystallineSituation.levelSectionsComplexTower` — the tower of complexes
  `n ↦ Γ(CRIS(X/S_{e(n)}), I_{e(n)})`.

## Main results

* `GlobalCrystallineSituation.levelDerivedProj_comp_levelResolutionIso`,
  `GlobalCrystallineSituation.levelDerivedTransition_comp_levelResolutionIso` — the derived
  comparisons computed on the resolution.
* `GlobalCrystallineSituation.isLimitLevelSectionsComplexCone` — the limit of complexes.
* `GlobalCrystallineSituation.levelDerivedProj_comp_levelResolutionQIso` — the comparison with a
  level is, in `D(Mod_A)`, the leg of the cone of complexes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry Opposite

universe wB wA u

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace Crystalline.GlobalCrystallineSituation

/-- The image in `D(C)` of the localization of a morphism of the bounded below homotopy
category is the localization of the underlying morphism. -/
lemma plus_ι_map_Qh_map {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    {K L : HomotopyCategory.Plus C} (f : K ⟶ L) :
    DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map f) = DerivedCategory.Qh.map f.hom :=
  rfl

/-- The quotient functor to the homotopy category on a composite of three morphisms. -/
lemma quotient_map_comp_comp_eq {V : Type*} [Category* V] [Preadditive V] {ι : Type*}
    {c : ComplexShape ι} {K₁ K₂ K₃ K₄ : HomologicalComplex V c} {f : K₁ ⟶ K₂} {g : K₂ ⟶ K₃}
    {h : K₃ ⟶ K₄} {t : K₁ ⟶ K₄} (H : f ≫ g ≫ h = t) :
    (HomotopyCategory.quotient V c).map f ≫ (HomotopyCategory.quotient V c).map g ≫
      (HomotopyCategory.quotient V c).map h = (HomotopyCategory.quotient V c).map t := by
  rw [← H, Functor.map_comp, Functor.map_comp]

/-- The localized naturality square of a transformation of additive functors on the class of a
bounded below complex. -/
lemma ι_map_Qh_map_natTrans_app {C M : Type*} [Category* C] [Category* M]
    [Preadditive C] [Abelian M] [HasDerivedCategory M] {F G : C ⥤ M} [F.Additive] [G.Additive]
    (α : F ⟶ G)
    (K : CochainComplex C ℤ) (hK : CochainComplex.plus C K) :
    DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map
        ((Functor.mapHomotopyCategoryPlusNatTrans α).app
          ((HomotopyCategory.Plus.quotient C).obj ⟨K, hK⟩))) ≫
      (DerivedCategory.quotientCompQhIso M).hom.app ((G.mapHomologicalComplex _).obj K) =
    (DerivedCategory.quotientCompQhIso M).hom.app ((F.mapHomologicalComplex _).obj K) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α _).app K) :=
  DerivedCategory.quotientCompQhIso_hom_naturality _

/-- The localized naturality square of a pasted transition `P₁ ⋙ Γ₁ ⋙ r₁ ⟶ P ⋙ Γ₂ ⋙ r` on the
class of a bounded below complex, computed piece by piece in the homotopy category. -/
lemma ι_map_Qh_map_transition_comp {C₀ C₁ C₂ M₁ M₂ A : Type*} [Category* C₀]
    [Category* C₁] [Category* C₂] [Category* M₁] [Category* M₂] [Category* A] [Preadditive C₀]
    [Preadditive C₁] [Preadditive C₂] [Preadditive M₁] [Preadditive M₂] [Abelian A]
    [HasDerivedCategory A]
    {P₁ : C₀ ⥤ C₁} {P' : C₁ ⥤ C₂} {P : C₀ ⥤ C₂} {Γ₁ : C₁ ⥤ M₁} {Γ₂ : C₂ ⥤ M₂} {r₁ : M₁ ⥤ A}
    {rt : M₂ ⥤ M₁} {r : M₂ ⥤ A} [P₁.Additive] [P'.Additive] [P.Additive] [Γ₁.Additive]
    [Γ₂.Additive] [r₁.Additive] [rt.Additive] [r.Additive]
    (α : Γ₁ ⟶ P' ⋙ Γ₂ ⋙ rt) (c : P₁ ⋙ P' ≅ P) (ρ₀ : rt ⋙ r₁ ⟶ r) (K : CochainComplex C₀ ℤ)
    (hK : CochainComplex.plus C₀ K)
    (g : P'.mapHomotopyCategoryPlus.obj (P₁.mapHomotopyCategoryPlus.obj
      ((HomotopyCategory.Plus.quotient C₀).obj ⟨K, hK⟩)) ⟶
        P.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.quotient C₀).obj ⟨K, hK⟩))
    (hg : g.hom = (HomotopyCategory.quotient C₂ _).map
      ((NatTrans.mapHomologicalComplex c.hom (ComplexShape.up ℤ)).app K)) :
    DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map
        (r₁.mapHomotopyCategoryPlus.map ((Functor.mapHomotopyCategoryPlusNatTrans α).app
            (P₁.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.quotient C₀).obj ⟨K, hK⟩))) ≫
          (Functor.mapHomotopyCategoryPlusNatTrans ρ₀).app
            (Γ₂.mapHomotopyCategoryPlus.obj (P'.mapHomotopyCategoryPlus.obj
              (P₁.mapHomotopyCategoryPlus.obj
                ((HomotopyCategory.Plus.quotient C₀).obj ⟨K, hK⟩)))) ≫
          r.mapHomotopyCategoryPlus.map (Γ₂.mapHomotopyCategoryPlus.map g))) ≫
      (DerivedCategory.quotientCompQhIso A).hom.app
        (((P ⋙ Γ₂ ⋙ r).mapHomologicalComplex _).obj K) =
    (DerivedCategory.quotientCompQhIso A).hom.app
        (((P₁ ⋙ Γ₁ ⋙ r₁).mapHomologicalComplex _).obj K) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (Functor.whiskerLeft P₁ (Functor.whiskerRight α r₁) ≫
          Functor.whiskerRight c.hom (Γ₂ ⋙ rt ⋙ r₁) ≫
            Functor.whiskerLeft (P ⋙ Γ₂) ρ₀) _).app K) := by
  have h₁ : (r₁.mapHomologicalComplex _).map ((NatTrans.mapHomologicalComplex α _).app
        ((P₁.mapHomologicalComplex _).obj K)) ≫
      (NatTrans.mapHomologicalComplex ρ₀ _).app ((Γ₂.mapHomologicalComplex _).obj
        ((P'.mapHomologicalComplex _).obj ((P₁.mapHomologicalComplex _).obj K))) ≫
      (r.mapHomologicalComplex _).map ((Γ₂.mapHomologicalComplex _).map
        ((NatTrans.mapHomologicalComplex c.hom (ComplexShape.up ℤ)).app K)) =
      (NatTrans.mapHomologicalComplex
        (Functor.whiskerLeft P₁ (Functor.whiskerRight α r₁) ≫
          Functor.whiskerRight c.hom (Γ₂ ⋙ rt ⋙ r₁) ≫ Functor.whiskerLeft (P ⋙ Γ₂) ρ₀) _).app K :=
    HomologicalComplex.hom_ext _ _ fun q =>
      congrArg (fun φ => r₁.map (α.app (P₁.obj (K.X q))) ≫ φ)
        (ρ₀.naturality (Γ₂.map (c.hom.app (K.X q)))).symm
  have h₂ := quotient_map_comp_comp_eq h₁
  obtain rfl : g = ObjectProperty.homMk ((HomotopyCategory.quotient C₂ _).map
      ((NatTrans.mapHomologicalComplex c.hom (ComplexShape.up ℤ)).app K)) :=
    ObjectProperty.hom_ext _ hg
  rw [plus_ι_map_Qh_map]
  exact (congrArg (fun φ => DerivedCategory.Qh.map φ ≫ (DerivedCategory.quotientCompQhIso A).hom.app
    (((P ⋙ Γ₂ ⋙ r).mapHomologicalComplex _).obj K)) h₂).trans
      (DerivedCategory.quotientCompQhIso_hom_naturality _)

/-- Rearranging a square through a functor and a further naturality square. -/
lemma map_comp_comp_eq_of_eq {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (F : 𝒞 ⥤ 𝒟)
    {a b c d : 𝒞} {x y : 𝒟} {u : a ⟶ b} {l : b ⟶ c} {v : a ⟶ d} {w : d ⟶ c}
    {q₁ : F.obj c ⟶ x} {q₀ : F.obj d ⟶ y} {f : y ⟶ x} (h : u ≫ l = v ≫ w)
    (h' : F.map w ≫ q₁ = q₀ ≫ f) :
    F.map u ≫ F.map l ≫ q₁ = (F.map v ≫ q₀) ≫ f := by
  rw [← Functor.map_comp_assoc, h, Functor.map_comp, Category.assoc, h', Category.assoc]

/-- `D(Mod_R)` has countable products, for any model of the derived category. -/
theorem hasProductsOfShape_nat_derivedCategory_moduleCat (R : Type u) [CommRing R]
    [HasDerivedCategory.{wA} (ModuleCat.{u + 1} R)] :
    HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u + 1} R)) :=
  have : HasLimitsOfShape (Discrete ℕ) (ModuleCat.{u + 1} R) := ModuleCat.hasLimitsOfShape
  have : HasProductsOfShape ℕ (ModuleCat.{u + 1} R) := this
  have : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{u + 1} R) :=
    moduleCat_hasExactLimitsOfShape_discrete _ ℕ
  Stacks.DerivedProducts.hasProductsOfShape_derivedCategory

variable (S : GlobalCrystallineSituation.{u}) [IsAffine S.S.scheme] (hN : S.LevelSequence)
  [HasDerivedCategory.{wB} (SmallSite.BigModuleSheaf S)]
  [∀ n, HasDerivedCategory.{wB} (SmallSite.BigModuleSheaf (S.levelSituation (hN.isLevel n)))]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
  [∀ n, HasDerivedCategory.{wA}
    (ModuleCat.{u + 1} Γ((S.levelSituation (hN.isLevel n)).S.scheme, ⊤))]

/-- The restriction of scalars along `A ⟶ A/p^eA`. -/
abbrev levelRestrictScalars {e : ℕ} (he : S.IsLevel e) :
    ModuleCat.{u + 1} Γ((S.levelSituation he).S.scheme, ⊤) ⥤ ModuleCat.{u + 1} Γ(S.S.scheme, ⊤) :=
  ModuleCat.restrictScalars.{u + 1} (SmallSite.baseChangeRingHom (S.levelProj he))

/-- **`RΓ(CRIS(X/S_{e(n)}), N_{e(n)})`, read in `D⁺(Mod_A)`.** -/
abbrev levelDerived (n : ℕ) (N : SmallSite.BigModuleSheaf S) :
    DerivedCategory.Plus (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) :=
  (S.levelRestrictScalars (hN.isLevel n)).mapDerivedCategoryPlus.obj
    ((SmallSite.derivedBigModuleGlobalSections (S.levelSituation (hN.isLevel n))).obj
      ((S.levelPullback (hN.isLevel n)).obj N))

/-- **The comparison `RΓ(CRIS(X/S), N) ⟶ RΓ(CRIS(X/S_{e(n)}), N_{e(n)})`**, the derived
comparison of global sections along `S_{e(n)} ⟶ S`. -/
abbrev levelDerivedProj (n : ℕ) (N : SmallSite.BigModuleSheaf S) :
    (SmallSite.derivedBigModuleGlobalSections S).obj N ⟶ S.levelDerived hN n N :=
  SmallSite.derivedChangeBaseBigGlobalSectionsMap (S.levelProj (hN.isLevel n)) (𝟙 S.X)
    (S.levelProj_condition (hN.isLevel n)) N

/-- **The derived restriction of scalars along `A ⟶ A/p^{e(n+1)} ⟶ A/p^{e(n)}`** is the derived
restriction of scalars along `A ⟶ A/p^{e(n)}`: the transformation of induced functors of the
composition `ModuleCat.restrictScalarsComp'`. -/
abbrev levelDerivedRestrictComp (n : ℕ) :
    (ModuleCat.restrictScalars.{u + 1} (SmallSite.baseChangeRingHom
        (S.levelTransition (hN.isLevel n) (hN.isLevel (n + 1))
          (hN.le_succ n)))).mapDerivedCategoryPlus ⋙
      (S.levelRestrictScalars (hN.isLevel (n + 1))).mapDerivedCategoryPlus ⟶
        (S.levelRestrictScalars (hN.isLevel n)).mapDerivedCategoryPlus :=
  Functor.mapDerivedCategoryPlusCompTransOfComp
    (S.levelRestrictScalarsComp (hN.isLevel n) (hN.isLevel (n + 1)) (hN.le_succ n))

/-- **The transition `RΓ(CRIS(X/S_{e(n+1)}), N_{e(n+1)}) ⟶ RΓ(CRIS(X/S_{e(n)}), N_{e(n)})`** in
`D⁺(Mod_A)`: the derived comparison of global sections along `S_{e(n)} ⟶ S_{e(n+1)}` at
`N_{e(n+1)}`, read in `D⁺(Mod_A)`, followed by the identification of the restriction of
`N_{e(n+1)}` to `CRIS(X/S_{e(n)})` with `N_{e(n)}`. -/
def levelDerivedTransition (n : ℕ) (N : SmallSite.BigModuleSheaf S) :
    S.levelDerived hN (n + 1) N ⟶ S.levelDerived hN n N :=
  (S.levelRestrictScalars (hN.isLevel (n + 1))).mapDerivedCategoryPlus.map
      (SmallSite.derivedChangeBaseBigGlobalSectionsMap
        (S.levelTransition (hN.isLevel n) (hN.isLevel (n + 1)) (hN.le_succ n)) (𝟙 S.X)
        (S.levelTransition_condition (hN.isLevel n) (hN.isLevel (n + 1)) (hN.le_succ n))
        ((S.levelPullback (hN.isLevel (n + 1))).obj N)) ≫
    (S.levelDerivedRestrictComp hN n).app _ ≫
      (S.levelRestrictScalars (hN.isLevel n)).mapDerivedCategoryPlus.map
        ((SmallSite.derivedBigModuleGlobalSections (S.levelSituation (hN.isLevel n))).map
          ((S.levelPullbackCompIso (hN.isLevel n) (hN.isLevel (n + 1)) (hN.le_succ n)).hom.app N))

/-! ### The computation on an injective resolution -/

section Resolution

variable {N : SmallSite.BigModuleSheaf S}
  (R : CochainComplex.InjectiveResolution
    ((CochainComplex.singleFunctor (SmallSite.BigModuleSheaf S) 0).obj N))

/-- The injective resolution `N[0] ⟶ I`, in the bounded below homotopy category. -/
abbrev resolutionPlus : HomotopyCategory.Plus (SmallSite.BigModuleSheaf S) :=
  (HomotopyCategory.Plus.quotient _).obj ⟨R.cocomplex, R.boundedBelow⟩

/-- The resolution map `N[0] ⟶ I`, in the bounded below homotopy category. -/
abbrev resolutionHom :
    (HomotopyCategory.Plus.singleFunctor (SmallSite.BigModuleSheaf S) 0).obj N ⟶
      resolutionPlus S R :=
  HomotopyCategory.Plus.quotientHomMk (CochainComplex.plus_singleFunctor_obj N) R.boundedBelow R.ι

/-- The resolution `N[0] ⟶ I` is inverted in the bounded below derived category. -/
instance isIso_Qh_map_resolutionHom :
    IsIso (DerivedCategory.Plus.Qh.map (resolutionHom S R)) :=
  haveI : IsIso ((DerivedCategory.Plus.singleFunctorIsoCompQh
      (SmallSite.BigModuleSheaf S) 0).hom.app
      N ≫ DerivedCategory.Plus.Qh.map (resolutionHom S R)) :=
    CochainComplex.InjectiveResolution.isIso_qhHom N R
  IsIso.of_isIso_comp_left
    ((DerivedCategory.Plus.singleFunctorIsoCompQh (SmallSite.BigModuleSheaf S) 0).hom.app N) _

/-- The resolution is by injectives, so the unit of `RΓ` is invertible on it. -/
instance isIso_unit_resolutionPlus :
    IsIso ((SmallSite.bigBaseModuleGlobalSections S).rightDerivedFunctorPlusUnit.app
      (resolutionPlus S R)) :=
  Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic _ _ fun q => by
    haveI : Injective ((resolutionPlus S R).obj.as.X q) := R.injective q
    exact Functor.rightAcyclic_of_injective _ _

/-- The restriction of the resolution to a level is by injectives, so the unit of `RΓ` is
invertible on it. -/
instance isIso_unit_levelPullback_resolutionPlus (n : ℕ) :
    IsIso ((SmallSite.bigBaseModuleGlobalSections
      (S.levelSituation (hN.isLevel n))).rightDerivedFunctorPlusUnit.app
        ((S.levelPullback (hN.isLevel n)).mapHomotopyCategoryPlus.obj (resolutionPlus S R))) :=
  Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic _ _ fun q => by
    haveI : Injective (((S.levelPullback (hN.isLevel n)).mapHomotopyCategoryPlus.obj
        (resolutionPlus S R)).obj.as.X q) :=
      S.injective_levelPullback_obj (hN.isLevel n) (R.cocomplex.X q)
    exact Functor.rightAcyclic_of_injective _ _

/-- **`RΓ(CRIS(X/S_{e(n)}), N_{e(n)})` computed on the injective resolution of `N`**: the
restriction of the resolution to the level is a resolution by injectives. -/
def levelResolutionIso (n : ℕ) :
    S.levelDerived hN n N ≅ DerivedCategory.Plus.Qh.obj
      ((S.levelRestrictScalars (hN.isLevel n)).mapHomotopyCategoryPlus.obj
        ((SmallSite.bigBaseModuleGlobalSections
          (S.levelSituation (hN.isLevel n))).mapHomotopyCategoryPlus.obj
          ((S.levelPullback (hN.isLevel n)).mapHomotopyCategoryPlus.obj (resolutionPlus S R)))) :=
  (S.levelRestrictScalars (hN.isLevel n)).mapDerivedCategoryPlus.mapIso
      ((SmallSite.bigBaseModuleGlobalSections
        (S.levelSituation (hN.isLevel n))).rightDerivedFunctorPlusResolutionIso
        (Functor.pushResolution (S.levelPullback (hN.isLevel n)) (resolutionHom S R))) ≪≫
    (S.levelRestrictScalars (hN.isLevel n)).mapDerivedCategoryPlusFactorsh.app _

/-- **`RΓ(CRIS(X/S), N)` computed on the injective resolution of `N`.** -/
abbrev baseResolutionIso :=
  (SmallSite.bigBaseModuleGlobalSections S).rightDerivedFunctorPlusResolutionIso (resolutionHom S R)

/-- **The comparison with a level, computed on the resolution**, is the restriction of global
sections applied termwise. -/
theorem levelDerivedProj_comp_levelResolutionIso (n : ℕ) :
    S.levelDerivedProj hN n N ≫ (S.levelResolutionIso hN R n).hom =
      (S.baseResolutionIso R).hom ≫ DerivedCategory.Plus.Qh.map
        ((Functor.mapHomotopyCategoryPlusNatTrans (S.levelSectionsTrans (hN.isLevel n))).app
          (resolutionPlus S R)) := by
  rw [levelDerivedProj, SmallSite.derivedChangeBaseBigGlobalSectionsMap_eq_derivedSquareMap]
  exact Functor.derivedSquareMap_comp_resolutionIso _ N _

/-- The restriction of the resolution to `CRIS(X/S_{e(n)})` through `CRIS(X/S_{e(n+1)})` is again
by injectives: it is isomorphic to the restriction to `CRIS(X/S_{e(n)})`. -/
instance isIso_unit_levelStepPullback_resolutionPlus (n : ℕ) :
    IsIso ((SmallSite.bigBaseModuleGlobalSections
      (S.levelSituation (hN.isLevel n))).rightDerivedFunctorPlusUnit.app
        ((S.levelStepPullback (hN.isLevel n) (hN.isLevel (n + 1))
          (hN.le_succ n)).mapHomotopyCategoryPlus.obj
          ((S.levelPullback (hN.isLevel (n + 1))).mapHomotopyCategoryPlus.obj
            (resolutionPlus S R)))) :=
  Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic _ _ fun q => by
    haveI : Injective ((S.levelPullback (hN.isLevel n)).obj (R.cocomplex.X q)) :=
      S.injective_levelPullback_obj (hN.isLevel n) (R.cocomplex.X q)
    haveI : Injective (((S.levelStepPullback (hN.isLevel n) (hN.isLevel (n + 1))
        (hN.le_succ n)).mapHomotopyCategoryPlus.obj
          ((S.levelPullback (hN.isLevel (n + 1))).mapHomotopyCategoryPlus.obj
            (resolutionPlus S R))).obj.as.X q) :=
      Injective.of_iso ((S.levelPullbackCompIso (hN.isLevel n) (hN.isLevel (n + 1))
        (hN.le_succ n)).app (R.cocomplex.X q)).symm inferInstance
    exact Functor.rightAcyclic_of_injective _ _

/-- The degreewise identification of the two restrictions of the resolution to
`CRIS(X/S_{e(n)})`, in the bounded below homotopy category. -/
abbrev levelStepResolutionHom (n : ℕ) :
    (S.levelStepPullback (hN.isLevel n) (hN.isLevel (n + 1))
        (hN.le_succ n)).mapHomotopyCategoryPlus.obj
        ((S.levelPullback (hN.isLevel (n + 1))).mapHomotopyCategoryPlus.obj (resolutionPlus S R)) ⟶
      (S.levelPullback (hN.isLevel n)).mapHomotopyCategoryPlus.obj (resolutionPlus S R) :=
  ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map
    ((NatTrans.mapHomologicalComplex (S.levelPullbackCompIso (hN.isLevel n) (hN.isLevel (n + 1))
      (hN.le_succ n)).hom (ComplexShape.up ℤ)).app R.cocomplex))

/-- **The transition, computed on the resolution**, is the transition of global sections applied
termwise. -/
theorem levelDerivedTransition_comp_levelResolutionIso (n : ℕ) :
    S.levelDerivedTransition hN n N ≫ (S.levelResolutionIso hN R n).hom =
      (S.levelResolutionIso hN R (n + 1)).hom ≫ DerivedCategory.Plus.Qh.map
        ((S.levelRestrictScalars (hN.isLevel (n + 1))).mapHomotopyCategoryPlus.map
            ((Functor.mapHomotopyCategoryPlusNatTrans (changeBaseBigBaseGlobalSectionsTrans
              (S.levelTransition (hN.isLevel n) (hN.isLevel (n + 1)) (hN.le_succ n)) (𝟙 S.X)
              (S.levelTransition_condition (hN.isLevel n) (hN.isLevel (n + 1))
                (hN.le_succ n)))).app
              ((S.levelPullback (hN.isLevel (n + 1))).mapHomotopyCategoryPlus.obj
                (resolutionPlus S R))) ≫
          (Functor.mapHomotopyCategoryPlusNatTrans
            (S.levelRestrictScalarsComp (hN.isLevel n) (hN.isLevel (n + 1))
              (hN.le_succ n))).app
            ((SmallSite.bigBaseModuleGlobalSections
              (S.levelSituation (hN.isLevel n))).mapHomotopyCategoryPlus.obj
              ((S.levelStepPullback (hN.isLevel n) (hN.isLevel (n + 1))
                (hN.le_succ n)).mapHomotopyCategoryPlus.obj
                ((S.levelPullback (hN.isLevel (n + 1))).mapHomotopyCategoryPlus.obj
                  (resolutionPlus S R)))) ≫
          (S.levelRestrictScalars (hN.isLevel n)).mapHomotopyCategoryPlus.map
            ((SmallSite.bigBaseModuleGlobalSections
              (S.levelSituation (hN.isLevel n))).mapHomotopyCategoryPlus.map
              (S.levelStepResolutionHom hN R n))) := by
  have hg := Functor.pushResolution_quotientHomMk_comp
    (S.levelPullbackCompIso (hN.isLevel n) (hN.isLevel (n + 1)) (hN.le_succ n))
    R.boundedBelow R.ι (S.levelStepResolutionHom hN R n) rfl
  have key := Functor.derivedSquareMap_transition_resolutionIso
    (changeBaseBigBaseGlobalSectionsTrans
      (S.levelTransition (hN.isLevel n) (hN.isLevel (n + 1)) (hN.le_succ n)) (𝟙 S.X)
      (S.levelTransition_condition (hN.isLevel n) (hN.isLevel (n + 1)) (hN.le_succ n)))
    (S.levelPullbackCompIso (hN.isLevel n) (hN.isLevel (n + 1)) (hN.le_succ n))
    (S.levelRestrictScalarsComp (hN.isLevel n) (hN.isLevel (n + 1)) (hN.le_succ n))
    (S.levelDerivedRestrictComp hN n)
    (fun L => Functor.mapDerivedCategoryPlusCompTransOfComp_compat _ L) N (resolutionHom S R)
    (S.levelStepResolutionHom hN R n) hg
  rw [levelDerivedTransition, SmallSite.derivedChangeBaseBigGlobalSectionsMap_eq_derivedSquareMap]
  simp only [levelResolutionIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  exact key

/-! ### The tower of complexes of global sections over the levels -/

/-- **The tower of complexes `n ↦ Γ(CRIS(X/S_{e(n)}), I_{e(n)})`** of global sections of the
resolution over the levels. -/
def levelSectionsComplexTower :
    ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) ℤ :=
  Functor.ofOpSequence
    (X := fun n => ((S.levelSectionsFunctor (hN.isLevel n)).mapHomologicalComplex _).obj
      R.cocomplex)
    (fun n => (NatTrans.mapHomologicalComplex (S.levelSectionsTransition (hN.isLevel n)
      (hN.isLevel (n + 1)) (hN.le_succ n)) _).app R.cocomplex)

/-- The transition of the tower of complexes from `n + 1` to `n` is the transition of global
sections applied termwise. -/
theorem levelSectionsComplexTower_map_succ (n : ℕ) :
    (S.levelSectionsComplexTower hN R).map (homOfLE (Nat.le_succ n)).op =
      (NatTrans.mapHomologicalComplex (S.levelSectionsTransition (hN.isLevel n)
        (hN.isLevel (n + 1)) (hN.le_succ n)) _).app R.cocomplex :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- **The cone over the tower of complexes** with vertex the complex `Γ(CRIS(X/S), I)`. -/
def levelSectionsComplexCone : Cone (S.levelSectionsComplexTower hN R) where
  pt := ((SmallSite.bigBaseModuleGlobalSections S).mapHomologicalComplex _).obj R.cocomplex
  π := NatTrans.ofOpSequence
    (F := (Functor.const _).obj
      (((SmallSite.bigBaseModuleGlobalSections S).mapHomologicalComplex _).obj R.cocomplex))
    (fun n => (NatTrans.mapHomologicalComplex (S.levelSectionsTrans (hN.isLevel n)) _).app
      R.cocomplex) (fun n => by
      have h : (NatTrans.mapHomologicalComplex (S.levelSectionsTrans (hN.isLevel (n + 1))) _).app
            R.cocomplex ≫ (NatTrans.mapHomologicalComplex (S.levelSectionsTransition (hN.isLevel n)
              (hN.isLevel (n + 1)) (hN.le_succ n)) _).app R.cocomplex =
          (NatTrans.mapHomologicalComplex (S.levelSectionsTrans (hN.isLevel n)) _).app
            R.cocomplex := by
        rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp,
          S.levelSectionsTrans_comp_levelSectionsTransition]
      exact (Category.id_comp _).trans (h.symm.trans (congrArg (fun φ => _ ≫ φ)
        (S.levelSectionsComplexTower_map_succ hN R n).symm)))

/-- The tower of complexes, evaluated in a degree, is the tower of global sections of the term of
the resolution in that degree, on the nose on objects. -/
def levelSectionsComplexTowerEvalHom (q : ℤ) :
    S.levelSectionsComplexTower hN R ⋙ HomologicalComplex.eval _ _ q ⟶
      S.levelSectionsTower hN (R.cocomplex.X q) :=
  NatTrans.ofOpSequence (fun n => 𝟙 ((S.levelSectionsFunctor (hN.isLevel n)).obj
    (R.cocomplex.X q))) (fun n => by
      have h : (S.levelSectionsComplexTower hN R ⋙ HomologicalComplex.eval _ _ q).map
          (homOfLE (n.le_add_right 1)).op =
          (S.levelSectionsTower hN (R.cocomplex.X q)).map (homOfLE (n.le_add_right 1)).op :=
        (congrArg (fun φ => φ.f q) (S.levelSectionsComplexTower_map_succ hN R n)).trans
          (S.levelSectionsTower_map_succ hN (R.cocomplex.X q) n).symm
      exact (Category.comp_id _).trans (h.trans (Category.id_comp _).symm))

/-- The identification of the evaluated towers is an isomorphism. -/
instance (q : ℤ) : IsIso (S.levelSectionsComplexTowerEvalHom hN R q) :=
  (NatTrans.isIso_iff_isIso_app _).2 fun _ => inferInstanceAs (IsIso (𝟙 _))

/-- **The complex `Γ(CRIS(X/S), I)` is the limit of the complexes
`Γ(CRIS(X/S_{e(n)}), I_{e(n)})`**. -/
def isLimitLevelSectionsComplexCone : IsLimit (S.levelSectionsComplexCone hN R) :=
  HomologicalComplex.isLimitOfEval _ _ fun q =>
    (IsLimit.postcomposeHomEquiv (asIso (S.levelSectionsComplexTowerEvalHom hN R q)) _)
      (IsLimit.ofIsoLimit (S.isLimitLevelSectionsCone hN (R.cocomplex.X q))
        (Cones.ext (Iso.refl _) (fun n =>
          ((Category.id_comp _).trans (Category.comp_id _)).symm)))

/-- **The transitions of the tower of complexes are epimorphisms**: degreewise they are the
transitions of global sections of an injective module, which are surjective. -/
instance epi_levelSectionsComplexTower_map (n : ℕ) :
    Epi ((S.levelSectionsComplexTower hN R).map (homOfLE (Nat.le_succ n)).op) := by
  rw [levelSectionsComplexTower_map_succ]
  refine HomologicalComplex.epi_of_epi_f _ fun q => ?_
  exact (ModuleCat.epi_iff_surjective _).2
    (S.surjective_levelSectionsTransition (hN.isLevel n) (hN.isLevel (n + 1)) (hN.le_succ n)
      (R.cocomplex.X q))

/-! ### The comparisons in `D(Mod_A)` with the tower of complexes -/

/-- `RΓ(CRIS(X/S), N) ≅ Γ(CRIS(X/S), I)` in `D(Mod_A)`. -/
def baseResolutionQIso :
    DerivedCategory.Plus.ι.obj ((SmallSite.derivedBigModuleGlobalSections S).obj N) ≅
      DerivedCategory.Q.obj (S.levelSectionsComplexCone hN R).pt :=
  DerivedCategory.Plus.ι.mapIso (S.baseResolutionIso R) ≪≫
    (DerivedCategory.quotientCompQhIso _).app (S.levelSectionsComplexCone hN R).pt

/-- `RΓ(CRIS(X/S_{e(n)}), N_{e(n)}) ≅ Γ(CRIS(X/S_{e(n)}), I_{e(n)})` in `D(Mod_A)`. -/
def levelResolutionQIso (n : ℕ) :
    DerivedCategory.Plus.ι.obj (S.levelDerived hN n N) ≅
      DerivedCategory.Q.obj ((S.levelSectionsComplexTower hN R).obj ⟨n⟩) :=
  DerivedCategory.Plus.ι.mapIso (S.levelResolutionIso hN R n) ≪≫
    (DerivedCategory.quotientCompQhIso _).app ((S.levelSectionsComplexTower hN R).obj ⟨n⟩)

/-- The comparison with a level is, in `D(Mod_A)`, the leg of the cone of complexes. -/
theorem levelDerivedProj_comp_levelResolutionQIso (n : ℕ) :
    DerivedCategory.Plus.ι.map (S.levelDerivedProj hN n N) ≫ (S.levelResolutionQIso hN R n).hom =
      (S.baseResolutionQIso hN R).hom ≫
        DerivedCategory.Q.map ((S.levelSectionsComplexCone hN R).π.app ⟨n⟩) := by
  dsimp only [levelResolutionQIso, baseResolutionQIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom]
  exact map_comp_comp_eq_of_eq DerivedCategory.Plus.ι
    (S.levelDerivedProj_comp_levelResolutionIso hN R n)
    (ι_map_Qh_map_natTrans_app (S.levelSectionsTrans (hN.isLevel n)) R.cocomplex
      R.boundedBelow)

end Resolution

end Crystalline.GlobalCrystallineSituation
