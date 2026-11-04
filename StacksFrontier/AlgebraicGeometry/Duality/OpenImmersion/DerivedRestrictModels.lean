module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.AffineConservative
public import StacksFrontier.Homology.DerivedCategory.GrothendieckModelTargetIso
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedRestrictAdjointIso
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.LocallySmall
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedRestrictComposition
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomologyCompat
public import StacksFrontier.Homology.DerivedCategory.GrothendieckModel
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonPullbackKFlat
import all StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.QuasiCoherenceOfTopCohomology

/-!
# Restriction to an open at the two models of `D(𝒪_X)`

The functor induced by an exact functor on derived categories, and its cohomology comparison,
read at the standard model and at the locally small model are identified through the comparison
of the models. For an open immersion `j`, the identification `j^* ≅ Lj^*` of the standard model
(through the exactness of restriction) and the one of the locally small model (by uniqueness of
adjoints) correspond, and so do the induced identifications `H^n(Lj^*E) ≅ j^*H^n(E)`.

## Main results

* `Stacks.Injectives.mapDerivedCategoryHomologyIso_models`: the cohomology comparison of an exact
  functor at the two models.
* `Stacks.Duality.derivedRestrictAdjointIso_inv_app_models`: `j^* ≅ Lj^*` at the two models.
* `Stacks.Duality.homology_derivedRestrictIsoDerivedPullback_models`: on cohomology.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Injectives

variable {X U : Scheme.{u}} (F : X.Modules ⥤ U.Modules) [F.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F]

/-- The functor induced by an exact functor on derived categories, at the two models. -/
def mapDerivedCategoryModelsIso :
    @Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard X.Modules) _ _ _
        (HasDerivedCategory.standard U.Modules) F _ _ _ ⋙
      (grothendieckModelEquiv.{u} U.Modules).functor ≅
    (grothendieckModelEquiv.{u} X.Modules).functor ⋙ F.mapDerivedCategory :=
  mapDerivedCategoryTargetModelIso (hd₁ := HasDerivedCategory.standard X.Modules) U.Modules F ≪≫
    mapDerivedCategoryModelIso X.Modules F

/-- `mapDerivedCategoryModelsIso` on the image of a complex. -/
theorem mapDerivedCategoryModelsIso_hom_app_Q (K : CochainComplex X.Modules ℤ) :
    (mapDerivedCategoryModelsIso F).hom.app
        ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard X.Modules)).obj K) =
      (grothendieckModelEquiv.{u} U.Modules).functor.map
          ((@Functor.mapDerivedCategoryFactors _ _ _ (HasDerivedCategory.standard X.Modules) _ _ _
            (HasDerivedCategory.standard U.Modules) F _ _ _).hom.app K) ≫
        (F.mapDerivedCategoryFactors).inv.app K := by
  simp only [Functor.comp_obj, mapDerivedCategoryModelsIso, mapDerivedCategoryTargetModelIso,
    mapDerivedCategoryModelIso, Iso.trans_hom, Localization.liftNatIso_hom, Iso.refl_hom,
    Localization.comp_liftNatTrans, Category.comp_id, Localization.liftNatTrans_app,
    Localization.Lifting.iso, Iso.symm_hom, NatTrans.comp_app, Functor.associator_inv_app,
    Category.id_comp, NatTrans.id_app]
  exact congrArg (· ≫ F.mapDerivedCategoryFactors.inv.app K) (Category.comp_id _)

/-- The cohomology comparison of the two models on the image of a complex. -/
theorem homologyFunctorModelIso_hom_app_Q (Z : Scheme.{u}) (n : ℤ)
    (L : CochainComplex Z.Modules ℤ) :
    (Stacks.Duality.homologyFunctorModelIso Z.Modules n).hom.app
        ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard Z.Modules)).obj L) =
      (DerivedCategory.homologyFunctorFactors Z.Modules n).hom.app L ≫
        (@DerivedCategory.homologyFunctorFactors _ _ _ (HasDerivedCategory.standard Z.Modules)
          n).inv.app L := by
  simp [Stacks.Duality.homologyFunctorModelIso, Localization.Lifting.iso]
  rfl

/-- The chase behind `mapDerivedCategoryHomologyIso_models`. -/
theorem mapDerivedCategoryHomologyIso_models_chase {𝒞 : Type*} [Category 𝒞]
    {A B Q' P P'' Q R S T : 𝒞} (a : A ⟶ B) (Hfs : B ⟶ Q') (Hcfs : A ⟶ P) (hl : P ⟶ Q)
    (hs : Q' ⟶ Q) (hsinv : Q ⟶ Q') (m : Q ⟶ R) (Fhsi : R ⟶ S) (Hfli : P ⟶ P'') (Hflh : P'' ⟶ P)
    (Fhli : R ⟶ T) (Fhlh : T ⟶ R) {b : B ⟶ S} {c : A ⟶ P''} {d : P'' ⟶ T} {e : T ⟶ S}
    (Ha : a ≫ Hfs = Hcfs ≫ hl ≫ hsinv) (hinv : hsinv ≫ hs = 𝟙 _) (hb : b = Hfs ≫ hs ≫ m ≫ Fhsi)
    (hc : c = Hcfs ≫ Hfli) (hd : d = Hflh ≫ hl ≫ m ≫ Fhli) (he : e = Fhlh ≫ Fhsi)
    (hfl : Hfli ≫ Hflh = 𝟙 _) (hhl : Fhli ≫ Fhlh = 𝟙 _) :
    a ≫ b = c ≫ d ≫ e := by
  subst hb hc hd he
  simp only [Category.assoc]
  rw [reassoc_of% Ha, reassoc_of% hinv, reassoc_of% hfl, reassoc_of% hhl]

/-- **The cohomology comparison of an exact functor at the two models.** -/
theorem mapDerivedCategoryHomologyIso_models (n : ℤ)
    (E : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard X.Modules)) :
    (Stacks.Duality.homologyFunctorModelIso U.Modules n).hom.app
        ((@Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard X.Modules) _ _ _
          (HasDerivedCategory.standard U.Modules) F _ _ _).obj E) ≫
      (@Functor.mapDerivedCategoryHomologyIso _ _ _ _ _ _ F _ _ _
        (HasDerivedCategory.standard X.Modules) (HasDerivedCategory.standard U.Modules)
        n).hom.app E =
    (DerivedCategory.homologyFunctor U.Modules n).map ((mapDerivedCategoryModelsIso F).hom.app E) ≫
      (F.mapDerivedCategoryHomologyIso n).hom.app
        ((grothendieckModelEquiv.{u} X.Modules).functor.obj E) ≫
      F.map ((Stacks.Duality.homologyFunctorModelIso X.Modules n).hom.app E) := by
  have key : Functor.whiskerLeft (@Functor.mapDerivedCategory _ _ _
        (HasDerivedCategory.standard X.Modules) _ _ _ (HasDerivedCategory.standard U.Modules)
        F _ _ _)
        (Stacks.Duality.homologyFunctorModelIso U.Modules n).hom ≫
      (@Functor.mapDerivedCategoryHomologyIso _ _ _ _ _ _ F _ _ _
        (HasDerivedCategory.standard X.Modules) (HasDerivedCategory.standard U.Modules) n).hom =
      Functor.whiskerRight (mapDerivedCategoryModelsIso F).hom
          (DerivedCategory.homologyFunctor U.Modules n) ≫
        Functor.whiskerLeft (grothendieckModelEquiv.{u} X.Modules).functor
          (F.mapDerivedCategoryHomologyIso n).hom ≫
        Functor.whiskerRight (Stacks.Duality.homologyFunctorModelIso X.Modules n).hom F := by
    refine Localization.natTrans_ext
      (@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard X.Modules))
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) (fun K => ?_)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    refine mapDerivedCategoryHomologyIso_models_chase _
      ((@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard U.Modules) n).map
        ((@Functor.mapDerivedCategoryFactors _ _ _ (HasDerivedCategory.standard X.Modules) _ _ _
          (HasDerivedCategory.standard U.Modules) F _ _ _).hom.app K))
      ((DerivedCategory.homologyFunctor U.Modules n).map
        ((grothendieckModelEquiv.{u} U.Modules).functor.map
          ((@Functor.mapDerivedCategoryFactors _ _ _ (HasDerivedCategory.standard X.Modules) _ _ _
            (HasDerivedCategory.standard U.Modules) F _ _ _).hom.app K)))
      ((DerivedCategory.homologyFunctorFactors U.Modules n).hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
      ((@DerivedCategory.homologyFunctorFactors _ _ _ (HasDerivedCategory.standard U.Modules)
        n).hom.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
      ((@DerivedCategory.homologyFunctorFactors _ _ _ (HasDerivedCategory.standard U.Modules)
        n).inv.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
      ((F.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).hom.app K)
      (F.map ((@DerivedCategory.homologyFunctorFactors _ _ _
        (HasDerivedCategory.standard X.Modules) n).inv.app K))
      ((DerivedCategory.homologyFunctor U.Modules n).map (F.mapDerivedCategoryFactors.inv.app K))
      ((DerivedCategory.homologyFunctor U.Modules n).map (F.mapDerivedCategoryFactors.hom.app K))
      (F.map ((DerivedCategory.homologyFunctorFactors X.Modules n).inv.app K))
      (F.map ((DerivedCategory.homologyFunctorFactors X.Modules n).hom.app K))
      ?_ (Iso.inv_hom_id_app _ _) ?_ ?_ ?_ ?_ ?_ ?_
    · exact ((Stacks.Duality.homologyFunctorModelIso U.Modules n).hom.naturality _).symm.trans
        (congrArg _ (homologyFunctorModelIso_hom_app_Q U n _))
    · exact @Stacks.ModulesOnACategory.TopCohomology.mapDerivedCategoryHomologyIso_hom_app_Q
        _ _ _ _ _ _ (HasDerivedCategory.standard X.Modules) (HasDerivedCategory.standard U.Modules)
        F _ _ _ n K
    · exact (congrArg _ (mapDerivedCategoryModelsIso_hom_app_Q F K)).trans (Functor.map_comp _ _ _)
    · exact Stacks.ModulesOnACategory.TopCohomology.mapDerivedCategoryHomologyIso_hom_app_Q F n K
    · exact (congrArg F.map (homologyFunctorModelIso_hom_app_Q X n K)).trans (F.map_comp _ _)
    · exact (Functor.map_comp _ _ _).symm.trans ((congrArg _ (Iso.inv_hom_id_app _ _)).trans
        (CategoryTheory.Functor.map_id _ _))
    · exact (F.map_comp _ _).symm.trans ((congrArg _ (Iso.inv_hom_id_app _ _)).trans
        (CategoryTheory.Functor.map_id _ _))
  exact NatTrans.congr_app key E

/-- Reading a characterization on the homotopy category on the image of a complex. -/
theorem app_Q_comp_of_app_Qh {𝒟 : Type*} [Category 𝒟] {Pq PQ Rq RQ A B C D : 𝒟}
    (x : Pq ⟶ Rq) (y : PQ ⟶ RQ) (Pqh : Pq ≅ PQ) (Rqh : Rq ⟶ RQ) (nat : Pqh.hom ≫ y = x ≫ Rqh)
    (fh : Rq ⟶ C) (fac : RQ ⟶ D) (a : D ≅ B) (b : B ≅ C) (hfh : fh = Rqh ≫ fac ≫ a.hom ≫ b.hom)
    (α : Pq ⟶ A) (mm : A ⟶ C) (hx : x ≫ fh = α ≫ mm) :
    y ≫ fac = Pqh.inv ≫ α ≫ mm ≫ b.inv ≫ a.inv := by
  rw [← cancel_epi Pqh.hom, Iso.hom_inv_id_assoc, reassoc_of% nat, ← reassoc_of% hx, hfh]
  simp

/-- A functor applied to three composable morphisms. -/
theorem map_comp₃_assoc {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (G : 𝒞 ⥤ 𝒟) {a b c d : 𝒞}
    {t : 𝒟} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (k : G.obj d ⟶ t) {φ : a ⟶ d}
    (hφ : f ≫ g ≫ h = φ) : G.map f ≫ G.map g ≫ G.map h ≫ k = G.map φ ≫ k := by
  rw [← hφ]; simp

/-- The homotopy-category comparison of an isomorphism of additive functors, on the image of a
complex. -/
theorem Qh_map_mapHomotopyCategoryIso_hom_app {𝒜 ℬ : Type*} [Category 𝒜] [Abelian 𝒜]
    [Category ℬ] [Abelian ℬ] [HasDerivedCategory ℬ] {F G : 𝒜 ⥤ ℬ} [F.Additive] [G.Additive]
    (e : F ≅ G) (K : CochainComplex 𝒜 ℤ) :
    DerivedCategory.Qh.map ((Stacks.Homology.mapHomotopyCategoryIso e (ComplexShape.up ℤ)).hom.app
        ((HomotopyCategory.quotient _ _).obj K)) ≫
      DerivedCategory.Qh.map ((G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K) ≫
      (DerivedCategory.quotientCompQhIso ℬ).hom.app ((G.mapHomologicalComplex _).obj K) =
    DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K) ≫
      (DerivedCategory.quotientCompQhIso ℬ).hom.app ((F.mapHomologicalComplex _).obj K) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app K) := by
  have h : (Stacks.Homology.mapHomotopyCategoryIso e (ComplexShape.up ℤ)).hom.app
        ((HomotopyCategory.quotient _ _).obj K) ≫
      (G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K =
      (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K ≫
      (HomotopyCategory.quotient _ _).map ((NatTrans.mapHomologicalComplex e.hom _).app K) := by
    simp only [Functor.mapHomotopyCategoryFactors, Stacks.Homology.mapHomotopyCategoryIso,
      Quotient.lift.isLift_hom, NatTrans.mapHomotopyCategory_app]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  rw [← Functor.map_comp_assoc, h, Functor.map_comp_assoc]
  exact congrArg (_ ≫ ·) ((DerivedCategory.quotientCompQhIso ℬ).hom.naturality _)

end Stacks.Injectives

namespace Stacks.Duality

open Stacks.Injectives

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- A comparison `ψ⁻¹` between derived functors, known on the homotopy category, read on the
image of a complex. -/
private theorem inv_app_Q_of_inv_app_Qh [HasDerivedCategory X.Modules]
    [HasDerivedCategory U.Modules] {Φ R : X.Modules ⥤ U.Modules} [Φ.Additive] [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (e : Φ ≅ R)
    {G : DerivedCategory X.Modules ⥤ DerivedCategory U.Modules} (ψ : R.mapDerivedCategory ≅ G)
    (c : ∀ K : HomotopyCategory X.Modules (ComplexShape.up ℤ), G.obj (DerivedCategory.Qh.obj K) ⟶
      DerivedCategory.Qh.obj ((Φ.mapHomotopyCategory (ComplexShape.up ℤ)).obj K))
    (H : ∀ K, ψ.inv.app (DerivedCategory.Qh.obj K) ≫ R.mapDerivedCategoryFactorsh.hom.app K =
      c K ≫ DerivedCategory.Qh.map
        ((Stacks.Homology.mapHomotopyCategoryIso e (ComplexShape.up ℤ)).hom.app K))
    (K : CochainComplex X.Modules ℤ) :
    ψ.inv.app (DerivedCategory.Q.obj K) ≫ R.mapDerivedCategoryFactors.hom.app K =
    G.map ((DerivedCategory.quotientCompQhIso X.Modules).inv.app K) ≫
      c ((HomotopyCategory.quotient _ _).obj K) ≫
      DerivedCategory.Qh.map ((Φ.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K) ≫
      (DerivedCategory.quotientCompQhIso U.Modules).hom.app
        ((Φ.mapHomologicalComplex _).obj K) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app K) :=
  (app_Q_comp_of_app_Qh _ _ (G.mapIso ((DerivedCategory.quotientCompQhIso X.Modules).app K))
    (R.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso X.Modules).hom.app K))
    (ψ.inv.naturality _)
    (R.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj K))
    (R.mapDerivedCategoryFactors.hom.app K)
    ((DerivedCategory.quotientCompQhIso U.Modules).app _).symm
    (DerivedCategory.Qh.mapIso ((R.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app K).symm)
    (Functor.mapDerivedCategoryFactorsh_hom_app _ K) _ _ (H _)).trans
    (congrArg (fun t => _ ≫ _ ≫ t) (Qh_map_mapHomotopyCategoryIso_hom_app e K))

/-- `derivedRestrictAdjointIso_inv_app_Qh` on the image of a complex. -/
theorem derivedRestrictAdjointIso_inv_app_Q (K : CochainComplex X.Modules ℤ) :
    (derivedRestrictAdjointIso j).inv.app (DerivedCategory.Q.obj K) ≫
      (Scheme.Modules.restrictFunctor j).mapDerivedCategoryFactors.hom.app K =
    (derivedPullback j).map ((DerivedCategory.quotientCompQhIso X.Modules).inv.app K) ≫
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
        j.toLRSHom.toShHom).app ((HomotopyCategory.quotient _ _).obj K) ≫
      DerivedCategory.Qh.map (((RingedSpaceModuleAdjunction.modulePullback
        j.toLRSHom.toShHom).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K) ≫
      (DerivedCategory.quotientCompQhIso U.Modules).hom.app
        (((Scheme.Modules.pullback j).mapHomologicalComplex _).obj K) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (Scheme.Modules.restrictFunctorIsoPullback j).symm.hom (ComplexShape.up ℤ)).app K) := by
  exact inv_app_Q_of_inv_app_Qh (Scheme.Modules.restrictFunctorIsoPullback j).symm
    (derivedRestrictAdjointIso j)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
      j.toLRSHom.toShHom).app (derivedRestrictAdjointIso_inv_app_Qh j) K

section Standard

attribute [local instance 10000] HasDerivedCategory.standard

/-- `Scheme.Modules.derivedRestrictIsoDerivedPullback_inv_app_Qh` on the image of a complex. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.derivedRestrictIsoDerivedPullback_inv_app_Q
    (K : CochainComplex X.Modules ℤ) :
    (Scheme.Modules.derivedRestrictIsoDerivedPullback j).inv.app (DerivedCategory.Q.obj K) ≫
      (Scheme.Modules.restrictFunctor j).mapDerivedCategoryFactors.hom.app K =
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback j.toLRSHom.toShHom).map
        ((DerivedCategory.quotientCompQhIso X.Modules).inv.app K) ≫
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
        j.toLRSHom.toShHom).app ((HomotopyCategory.quotient _ _).obj K) ≫
      DerivedCategory.Qh.map (((RingedSpaceModuleAdjunction.modulePullback
        j.toLRSHom.toShHom).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K) ≫
      (DerivedCategory.quotientCompQhIso U.Modules).hom.app
        (((Scheme.Modules.pullback j).mapHomologicalComplex _).obj K) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (Scheme.Modules.restrictFunctorIsoPullback j).symm.hom (ComplexShape.up ℤ)).app K) := by
  exact inv_app_Q_of_inv_app_Qh (Scheme.Modules.restrictFunctorIsoPullback j).symm
    (Scheme.Modules.derivedRestrictIsoDerivedPullback j)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
      j.toLRSHom.toShHom).app (Scheme.Modules.derivedRestrictIsoDerivedPullback_inv_app_Qh j) K

end Standard

/-- Reassociating a composite of five morphisms. -/
theorem comp₅_eq_assoc {𝒞 : Type*} [Category 𝒞] {a b c d e f : 𝒞} (x₁ : a ⟶ b) (x₂ : b ⟶ c)
    (x₃ : c ⟶ d) (x₄ : d ⟶ e) (x₅ : e ⟶ f) :
    x₁ ≫ x₂ ≫ x₃ ≫ x₄ ≫ x₅ = (x₁ ≫ x₂ ≫ x₃ ≫ x₄) ≫ x₅ := by
  simp

/-- The chase behind `derivedRestrictAdjointIso_inv_app_models`. -/
theorem derivedRestrictAdjointIso_models_chase {𝒞 : Type*} [Category 𝒞]
    {P A B R T Q P₁ P₂ P₃ : 𝒞} (y : P ⟶ R) (pmi : A ≅ P) (cd : A ⟶ B) (cf : B ⟶ T) (fac : R ≅ T)
    (b₁ : P ⟶ P₁) (b₂ : P₁ ⟶ P₂) (b₃ : P₂ ⟶ P₃) (b₄ : P₃ ⟶ Q) (cbs : A ⟶ Q) (q : Q ⟶ T)
    {z : P ⟶ R} (hz : z = pmi.inv ≫ cd ≫ cf ≫ fac.inv)
    (h1 : y ≫ fac.hom = b₁ ≫ b₂ ≫ b₃ ≫ b₄ ≫ q) (h2 : pmi.hom ≫ b₁ ≫ b₂ ≫ b₃ ≫ b₄ = cbs)
    (hD : cd ≫ cf = cbs ≫ q) : y = z := by
  rw [← cancel_mono fac.hom, h1, hz]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hD, ← h2]
  simp

/-- **Restriction ≅ derived pullback at the two models**: the isomorphism given by uniqueness of
adjoints at the locally small model is the one of the standard model, read through the
comparisons of the models. -/
theorem derivedRestrictAdjointIso_inv_app_models
    (E : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard X.Modules)) :
    (derivedRestrictAdjointIso j).inv.app ((grothendieckModelEquiv.{u} X.Modules).functor.obj E) =
      (StacksDraft.DerivedModel.derivedPullbackModelIso j.toLRSHom.toShHom).inv.app E ≫
        (grothendieckModelEquiv.{u} U.Modules).functor.map
          ((Scheme.Modules.derivedRestrictIsoDerivedPullback j).inv.app E) ≫
        (mapDerivedCategoryModelsIso (Scheme.Modules.restrictFunctor j)).hom.app E := by
  have key : Functor.whiskerLeft (grothendieckModelEquiv.{u} X.Modules).functor
      (derivedRestrictAdjointIso j).inv =
      (StacksDraft.DerivedModel.derivedPullbackModelIso j.toLRSHom.toShHom).inv ≫
        Functor.whiskerRight (Scheme.Modules.derivedRestrictIsoDerivedPullback j).inv
          (grothendieckModelEquiv.{u} U.Modules).functor ≫
        (mapDerivedCategoryModelsIso (Scheme.Modules.restrictFunctor j)).hom := by
    refine Localization.natTrans_ext
      (@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard X.Modules))
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) (fun K => ?_)
    simp only [Functor.whiskerLeft_app]
    refine derivedRestrictAdjointIso_models_chase _
      ((StacksDraft.DerivedModel.derivedPullbackModelIso j.toLRSHom.toShHom).app
        ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard X.Modules)).obj K))
      ((grothendieckModelEquiv.{u} U.Modules).functor.map
          ((Scheme.Modules.derivedRestrictIsoDerivedPullback j).inv.app
            ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard X.Modules)).obj K)))
      ((grothendieckModelEquiv.{u} U.Modules).functor.map
          ((@Functor.mapDerivedCategoryFactors _ _ _ (HasDerivedCategory.standard X.Modules) _ _ _
            (HasDerivedCategory.standard U.Modules)
            (Scheme.Modules.restrictFunctor j) _ _ _).hom.app K))
      ((Scheme.Modules.restrictFunctor j).mapDerivedCategoryFactors.app K)
      _ _ _ _ _ _ ?_ (derivedRestrictAdjointIso_inv_app_Q j K)
      (StacksDraft.DerivedModel.derivedPullbackModelIso_hom_app_Q_comp j.toLRSHom.toShHom K) ?_
    · exact congrArg (fun t => _ ≫ _ ≫ t)
        (mapDerivedCategoryModelsIso_hom_app_Q (Scheme.Modules.restrictFunctor j) K)
    · exact ((grothendieckModelEquiv.{u} U.Modules).functor.map_comp _ _).symm.trans
        ((congrArg (grothendieckModelEquiv.{u} U.Modules).functor.map
          ((Scheme.Modules.derivedRestrictIsoDerivedPullback_inv_app_Q j K).trans
            (comp₅_eq_assoc _ _ _ _ _))).trans
          ((grothendieckModelEquiv.{u} U.Modules).functor.map_comp _ _))
  exact NatTrans.congr_app key E

/-- `G.map e.hom ≫ G.map (e.inv ≫ f ≫ g) = G.map f ≫ G.map g`. -/
theorem map_hom_comp_map_inv_comp {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (G : 𝒞 ⥤ 𝒟)
    {a b c d : 𝒞} (e : a ≅ b) (f : a ⟶ c) (g : c ⟶ d) :
    G.map e.hom ≫ G.map (e.inv ≫ f ≫ g) = G.map f ≫ G.map g := by
  rw [← G.map_comp, ← G.map_comp, Iso.hom_inv_id_assoc]

/-- The chase behind `homology_derivedRestrictIsoDerivedPullback_models`. -/
theorem homology_models_chase {𝒞 : Type*} [Category 𝒞] {A B C D G H I J : 𝒞}
    (hs : A ⟶ B) (hd : B ⟶ C) (mh : C ⟶ D) (cd : A ⟶ G) (hs' : G ⟶ C) (th : G ⟶ H)
    (ml : H ⟶ I) (rh : I ⟶ D) (pm : A ⟶ J) (am : J ⟶ H) (hnat : hs ≫ hd = cd ≫ hs')
    (hM : hs' ≫ mh = th ≫ ml ≫ rh) (hS : pm ≫ am = cd ≫ th) :
    hs ≫ hd ≫ mh = pm ≫ am ≫ ml ≫ rh := by
  rw [reassoc_of% hnat, hM, reassoc_of% hS]

/-- **Cohomology commutes with restriction to an open, at the two models.** The identification
`H^n(Lj^*E) ≅ j^*H^n(E)` of the standard model, read through the comparison of cohomology at
the two models, is the one of the locally small model given by uniqueness of adjoints. -/
theorem homology_derivedRestrictIsoDerivedPullback_models (n : ℤ)
    (E : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard X.Modules)) :
    (AlgebraicGeometry.PerfectApproximation.homologyStandardIso
        ((@Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback _ _ j.toLRSHom.toShHom
          (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) inferInstance).obj E)
        n).hom ≫
      (@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard U.Modules) n).map
        ((Scheme.Modules.derivedRestrictIsoDerivedPullback j).inv.app E) ≫
      (@Functor.mapDerivedCategoryHomologyIso _ _ _ _ _ _ (Scheme.Modules.restrictFunctor j) _ _ _
        (HasDerivedCategory.standard X.Modules) (HasDerivedCategory.standard U.Modules)
        n).hom.app E =
    (DerivedCategory.homologyFunctor U.Modules n).map
        ((StacksDraft.DerivedModel.derivedPullbackModelIso j.toLRSHom.toShHom).hom.app E) ≫
      (DerivedCategory.homologyFunctor U.Modules n).map
        ((derivedRestrictAdjointIso j).inv.app
          ((grothendieckModelEquiv.{u} X.Modules).functor.obj E)) ≫
      ((Scheme.Modules.restrictFunctor j).mapDerivedCategoryHomologyIso n).hom.app
        ((grothendieckModelEquiv.{u} X.Modules).functor.obj E) ≫
      (Scheme.Modules.restrictFunctor j).map
        (AlgebraicGeometry.PerfectApproximation.homologyStandardIso E n).hom := by
  refine homology_models_chase _ _ _
    ((DerivedCategory.homologyFunctor U.Modules n).map
      ((grothendieckModelEquiv.{u} U.Modules).functor.map
        ((Scheme.Modules.derivedRestrictIsoDerivedPullback j).inv.app E)))
    (AlgebraicGeometry.PerfectApproximation.homologyStandardIso
      ((@Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard X.Modules) _ _ _
        (HasDerivedCategory.standard U.Modules) (Scheme.Modules.restrictFunctor j) _ _ _).obj E)
        n).hom
    ((DerivedCategory.homologyFunctor U.Modules n).map
      ((mapDerivedCategoryModelsIso (Scheme.Modules.restrictFunctor j)).hom.app E))
    _ _ _ _ ?_ (mapDerivedCategoryHomologyIso_models (Scheme.Modules.restrictFunctor j) n E) ?_
  · exact (AlgebraicGeometry.PerfectApproximation.homologyStandardIso_naturality _ n).symm
  · rw [derivedRestrictAdjointIso_inv_app_models]
    exact map_hom_comp_map_inv_comp (DerivedCategory.homologyFunctor U.Modules n)
      ((StacksDraft.DerivedModel.derivedPullbackModelIso j.toLRSHom.toShHom).app E) _ _

end Stacks.Duality
