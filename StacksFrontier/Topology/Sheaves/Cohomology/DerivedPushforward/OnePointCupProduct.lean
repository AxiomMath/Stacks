module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.OnePointDerivedTensorComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CupProductAndDerivedPushforward
public import StacksFrontier.Homology.Tor.DerivedTensorToTotalComplex

/-!
# The global cup product on the one-point ringed space

Let `R` be a commutative ring, `({*}, R)` the one-point ringed space, `A = Γ({*}, 𝒪)` and
`E : D(A) ⥤ D(𝒪_{({*}, R)})` the one-point identification, left adjoint to `RΓ({*}, -)`.

## Main definitions

* `Stacks.Cohomology.DerivedSectionsLeray.sectionsUnitQ`: the unit `Γ(U, N) ⟶ RΓ(U, N)` of a
  complex of modules, in the derived category.
* `Stacks.Cohomology.DerivedSectionsOnAPoint.onePointCupProduct`: the global cup product on the
  one-point ringed space.

## Main results

* `Stacks.Cohomology.DerivedSectionsOnAPoint.onePointDerived_toTensor`: the comparison
  `E(x ⊗^𝐋_A y) ≅ E x ⊗^𝐋_𝒪 E y` is compatible with the canonical maps of both derived tensor
  products to the ordinary total tensor complexes.
* `Stacks.Cohomology.DerivedSectionsOnAPoint.onePointCupProduct_naive`: [Stacks, Tag 0FP3] on the
  one-point ringed space: the global cup product, precomposed with the units in both factors, is
  the canonical map to the total tensor complex followed by the unit.
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TopologicalSpace
open Stacks.Cohomology.DerivedPullbackTensor
open Stacks.Cohomology.GlobalKunneth
open Stacks.DerivedTensor.RingedSite
open CochainComplex.KFlatBifunctor
open CochainComplex.DerivedTensor.ToTotal (canonicalDerivedToTensorNatTrans
  canonicalDerivedToTensorNatTrans_app_eq_comparison totalTensorPair)
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedSectionsOnAPoint

attribute [local instance 10000] HasDerivedCategory.standard

variable (R : Type u) [CommRing R]

/-- The left-hand side of `toTensorLeft_eq`. -/
abbrev toTensorLeft (X Y : CochainComplex (onePointModuleCat R) ℤ) :
    (sectionsOfDerivedTensor R).obj (DerivedCategory.Q.obj X, DerivedCategory.Q.obj Y) ⟶
      (modelTarget R).obj (X, Y) :=
  (onePointDerivedTensorIso R).hom.app (DerivedCategory.Q.obj X, DerivedCategory.Q.obj Y) ≫
    (rightComparison R).app (X, Y)

/-- The right-hand side of `toTensorLeft_eq`. -/
abbrev toTensorRight (X Y : CochainComplex (onePointModuleCat R) ℤ) :
    (sectionsOfDerivedTensor R).obj (DerivedCategory.Q.obj X, DerivedCategory.Q.obj Y) ⟶
      (modelTarget R).obj (X, Y) :=
  (onePointDerived R).map
      ((canonicalDerivedToTensorNatTrans ↥(baseRing (onePointRingedSpace R))).app (X, Y)) ≫
    (onePointSheafFunctor R).mapDerivedCategoryFactors.hom.app
      ((totalTensorPair ↥(baseRing (onePointRingedSpace R))).obj (X, Y))

/-- On a pair of K-flat complexes, the comparison `onePointDerivedTensorIso` is
`modelComparison`. -/
theorem onePointDerivedTensorIso_hom_app_kFlat (X Y : CochainComplex (onePointModuleCat R) ℤ)
    (hX : CochainComplex.KFlat.{u, u} X) (hY : CochainComplex.KFlat.{u, u} Y) :
    (onePointDerivedTensorIso R).hom.app (DerivedCategory.Q.obj X, DerivedCategory.Q.obj Y) =
      (modelComparison R X Y hX hY).hom := by
  let M : (kFlatObjects (MonoidalCategory.curriedTensor (onePointModuleCat R))).FullSubcategory ×
      (kFlatObjects (MonoidalCategory.curriedTensor (onePointModuleCat R))).FullSubcategory :=
    (⟨(HomotopyCategory.quotient _ _).obj X, hX⟩, ⟨(HomotopyCategory.quotient _ _).obj Y, hY⟩)
  have hL : (onePointDerivedTensorIso R).hom.app ((kFlatQModulesPair R).obj M) =
      (modelsComparison R).hom.app M := by
    dsimp only [onePointDerivedTensorIso, Localization.liftNatIso]
    rw [Localization.liftNatTrans_app]
    simp
  have hn := (onePointDerivedTensorIso R).hom.naturality (kFlatQModulesPairIso R M).hom
  rw [hL] at hn
  have hc : (onePointDerivedTensorIso R).hom.app
      (DerivedCategory.Q.obj X, DerivedCategory.Q.obj Y) =
      (sectionsOfDerivedTensor R).map (kFlatQModulesPairIso R M).inv ≫
        (modelsComparison R).hom.app M ≫
          (derivedTensorOfSections R).map (kFlatQModulesPairIso R M).hom := by
    rw [← hn, ← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
    rfl
  rw [hc]
  dsimp only [modelsComparison, NatIso.ofComponents_hom_app, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.mapIso_inv]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.comp_id]
  rw [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rfl

/-- The comparison is compatible with the canonical maps to the total tensor complexes, on a pair
of K-flat complexes. -/
theorem toTensorLeft_eq_kFlat (X Y : CochainComplex (onePointModuleCat R) ℤ)
    (hX : CochainComplex.KFlat.{u, u} X) (hY : CochainComplex.KFlat.{u, u} Y) :
    toTensorLeft R X Y = toTensorRight R X Y := by
  have := isIso_rightComparison_app R X Y hX hY
  dsimp only [toTensorLeft, toTensorRight]
  rw [onePointDerivedTensorIso_hom_app_kFlat R X Y hX hY]
  dsimp only [modelComparison, Iso.trans_hom, Iso.symm_hom, asIso_inv]
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, leftComparisonIso_hom,
    canonicalDerivedToTensorNatTrans_app_eq_comparison _ X Y hX hY]
  rfl

end Stacks.Cohomology.DerivedSectionsOnAPoint

namespace Stacks.Cohomology.DerivedSectionsOnAPoint

attribute [local instance 10000] HasDerivedCategory.standard

variable (R : Type u) [CommRing R]

/-- Two natural transformations agree at an object as soon as they agree at an object mapping to
it by a morphism the source functor inverts. -/
private theorem natTrans_app_eq_of_isIso {C : Type*} {D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D}
    (φ ψ : F ⟶ G) {X X' : C} (f : X' ⟶ X) (hf : IsIso (F.map f)) (h : φ.app X' = ψ.app X') :
    φ.app X = ψ.app X := by
  rw [← cancel_epi (F.map f), φ.naturality, ψ.naturality, h]

/-- The source of the two sides of `toTensorLeft_eq`, as a functor on pairs of complexes. -/
abbrev sectionsOfDerivedTensorQ :
    CochainComplex (onePointModuleCat R) ℤ × CochainComplex (onePointModuleCat R) ℤ ⥤
      DerivedCategory (onePointSheafCat R) :=
  DerivedCategory.Q.prod DerivedCategory.Q ⋙ sectionsOfDerivedTensor R

/-- The morphism of bifunctors whose components are `toTensorLeft`. -/
abbrev toTensorLeftNatTrans : sectionsOfDerivedTensorQ R ⟶ modelTarget R :=
  Functor.whiskerLeft _ (onePointDerivedTensorIso R).hom ≫ rightComparison R

/-- The morphism of bifunctors whose components are `toTensorRight`. -/
abbrev toTensorRightNatTrans : sectionsOfDerivedTensorQ R ⟶ modelTarget R :=
  Functor.whiskerRight (canonicalDerivedToTensorNatTrans ↥(baseRing (onePointRingedSpace R)))
      (onePointDerived R) ≫
    Functor.whiskerLeft (totalTensorPair ↥(baseRing (onePointRingedSpace R)))
      (onePointSheafFunctor R).mapDerivedCategoryFactors.hom

/-- **The comparison `E(x ⊗^𝐋_A y) ≅ E x ⊗^𝐋_𝒪 E y` is compatible with the canonical maps to the
total tensor complexes**: for complexes `X`, `Y` of `A`-modules,
`E(QX ⊗^𝐋 QY) ⟶ E(Q Tot(X ⊗ Y)) ⟶ Q(E Tot(X ⊗ Y))` is the comparison followed by
`E QX ⊗^𝐋 E QY ⟶ Q E X ⊗^𝐋 Q E Y ⟶ Q Tot(E X ⊗ E Y) ≅ Q E Tot(X ⊗ Y)`. -/
theorem toTensorLeft_eq (X Y : CochainComplex (onePointModuleCat R) ℤ) :
    toTensorLeft R X Y = toTensorRight R X Y := by
  obtain ⟨X', p, hX', hp⟩ :=
    CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso
      ↥(baseRing (onePointRingedSpace R)) X
  obtain ⟨Y', q, hY', hq⟩ :=
    CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso
      ↥(baseRing (onePointRingedSpace R)) Y
  let pq : ((X', Y') : CochainComplex (onePointModuleCat R) ℤ ×
      CochainComplex (onePointModuleCat R) ℤ) ⟶ (X, Y) := (p, q)
  have : IsIso (DerivedCategory.Q.map p ×ₘ DerivedCategory.Q.map q) :=
    (isIso_prod_iff (f := DerivedCategory.Q.map p ×ₘ DerivedCategory.Q.map q)).mpr
      ⟨inferInstance, inferInstance⟩
  exact natTrans_app_eq_of_isIso (toTensorLeftNatTrans R) (toTensorRightNatTrans R) pq
    ((sectionsOfDerivedTensor R).map_isIso (DerivedCategory.Q.map p ×ₘ DerivedCategory.Q.map q))
    (toTensorLeft_eq_kFlat R X' Y' hX' hY')

end Stacks.Cohomology.DerivedSectionsOnAPoint

namespace Stacks.Cohomology.DerivedSectionsLeray

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u}) (U : Opens X.carrier)

/-- **The unit `Γ(U, N) ⟶ RΓ(U, N)` of a complex of `𝒪_X`-modules**, read between the images of
the localization functor `Q`: the canonical comparison from termwise sections to their right
derived functor, with the identifications of `Q` with `Qh ∘ quotient` inserted at either end. -/
def sectionsUnitQ (N : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    DerivedCategory.Q.obj
        (((sectionsOverOpen X U).mapHomologicalComplex (ComplexShape.up ℤ)).obj N) ⟶
      (derivedSectionsOverOpen X U).obj (DerivedCategory.Q.obj N) :=
  (DerivedCategory.quotientCompQhIso _).inv.app _ ≫
    (derivedSectionsOverOpenUnit X U).app ((HomotopyCategory.quotient _ _).obj N) ≫
      (derivedSectionsOverOpen X U).map ((DerivedCategory.quotientCompQhIso _).hom.app N)

/-- The unit `Γ(U, -) ⟶ RΓ(U, -)` is natural in cochain maps. -/
theorem sectionsUnitQ_naturality
    {N N' : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ} (f : N ⟶ N') :
    DerivedCategory.Q.map
          (((sectionsOverOpen X U).mapHomologicalComplex (ComplexShape.up ℤ)).map f) ≫
        sectionsUnitQ X U N' =
      sectionsUnitQ X U N ≫ (derivedSectionsOverOpen X U).map (DerivedCategory.Q.map f) := by
  have h₁ := DerivedCategory.quotientCompQhIso_inv_naturality
    (C := ModuleCat.{u} ((structureSheafRing X).obj.obj (op U)))
    (((sectionsOverOpen X U).mapHomologicalComplex (ComplexShape.up ℤ)).map f)
  have h₂ := (derivedSectionsOverOpenUnit X U).naturality
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map f)
  have h₃ := congrArg ((derivedSectionsOverOpen X U).map ·)
    (DerivedCategory.quotientCompQhIso_hom_naturality
      (C := SheafOfModules.{u} (structureSheafRing X)) f)
  simp only [Functor.map_comp] at h₃
  exact Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.comp_naturality h₁
    (Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.comp_naturality h₂ h₃)

end Stacks.Cohomology.DerivedSectionsLeray

namespace Stacks.Cohomology.DerivedSectionsOnAPoint

open Stacks.Cohomology.DerivedSectionsLeray

attribute [local instance] HasDerivedCategory.standard

variable (R : Type u) [CommRing R]

/-- The counit of an adjunction transported along an isomorphism of right adjoints. -/
private theorem ofNatIsoRight_counit_app {C : Type*} {D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {G H : D ⥤ C} (adj : F ⊣ G) (e : G ≅ H) (Y : D) :
    (adj.ofNatIsoRight e).counit.app Y = F.map (e.inv.app Y) ≫ adj.counit.app Y := by
  rw [← Adjunction.homEquiv_symm_id, Adjunction.homEquiv_ofNatIsoRight_symm_apply,
    Category.id_comp, Adjunction.homEquiv_counit]

private theorem comp_cancel {C : Type*} [Category* C] {a b c d e f : C}
    (q : a ⟶ b) (un : b ⟶ c) (rm : c ⟶ d) (cmp : d ⟶ e) (cmp' : c ⟶ f) (gm : f ⟶ e)
    (fh : b ⟶ f) (fi : a ⟶ e) (hnat : rm ≫ cmp = cmp' ≫ gm) (hfac : un ≫ cmp' = fh)
    (hh : q ≫ fh ≫ gm = fi) : (q ≫ un ≫ rm) ≫ cmp = fi := by
  rw [Category.assoc, Category.assoc, hnat, ← Category.assoc un, hfac, hh]

private theorem inv_comp_of_hom_eq {C : Type*} [Category* C] {Y Z W V : C} (e : Y ≅ V)
    (g : Y ⟶ Z) (f : Z ⟶ W) (qi : W ⟶ V) (q : V ⟶ W) (hq : qi ≫ q = 𝟙 W)
    (hh : e.hom = g ≫ f ≫ qi ≫ 𝟙 V) : (e.inv ≫ g) ≫ f = q ≫ 𝟙 W := by
  rw [Category.comp_id] at hh
  rw [Category.comp_id, Category.assoc, Iso.inv_comp_eq, hh, Category.assoc, Category.assoc, hq,
    Category.comp_id]

/-- `Γ` on the homotopy category, at the class of a complex, against `Γ` on complexes. -/
private theorem factorsh_inv_app
    (N : CochainComplex (SheafOfModules.{u} (structureSheafRing (onePointRingedSpace R))) ℤ) :
    (DerivedCategory.quotientCompQhIso _).inv.app
          (((sectionsOverOpen (onePointRingedSpace R) ⊤).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj N) ≫
        (sectionsOverOpen (onePointRingedSpace R) ⊤).mapDerivedCategoryFactorsh.inv.app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N) ≫
        (sectionsOverOpen (onePointRingedSpace R) ⊤).mapDerivedCategory.map
          ((DerivedCategory.quotientCompQhIso _).hom.app N) =
      (sectionsOverOpen (onePointRingedSpace R) ⊤).mapDerivedCategoryFactors.inv.app N := by
  have hh := (sectionsOverOpen (onePointRingedSpace R) ⊤).mapDerivedCategoryFactorsh_hom_app N
  rw [← cancel_mono
    ((sectionsOverOpen (onePointRingedSpace R) ⊤).mapDerivedCategoryFactors.hom.app N)]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [← cancel_epi ((DerivedCategory.quotientCompQhIso _).hom.app _), Iso.hom_inv_id_app_assoc]
  have hid : DerivedCategory.Qh.map
      (((sectionsOverOpen (onePointRingedSpace R) ⊤).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).inv.app N) = 𝟙 _ := DerivedCategory.Qh.map_id _
  rw [hid] at hh
  simpa only [Iso.app_inv, Category.assoc, Functor.comp_obj] using inv_comp_of_hom_eq
    ((sectionsOverOpen (onePointRingedSpace R) ⊤).mapDerivedCategoryFactorsh.app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N)) _ _ _ _
    (Iso.inv_hom_id_app (DerivedCategory.quotientCompQhIso _)
      (((sectionsOverOpen (onePointRingedSpace R) ⊤).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N)) hh

/-- **On the one-point ringed space the unit `Γ ⟶ RΓ` is the factorization isomorphism of the
exact functor `Γ`**, read through the comparison `RΓ({*}, -) ≅ Γ({*}, -)`. -/
theorem sectionsUnitQ_comp_onePointDerivedSectionsComparison
    (N : CochainComplex (SheafOfModules.{u} (structureSheafRing (onePointRingedSpace R))) ℤ) :
    sectionsUnitQ (onePointRingedSpace R) ⊤ N ≫
        (onePointDerivedSectionsComparison R).app (DerivedCategory.Q.obj N) =
      (sectionsOverOpen (onePointRingedSpace R) ⊤).mapDerivedCategoryFactors.inv.app N :=
  comp_cancel _ _ _ _ _ _ _ _
    ((onePointDerivedSectionsComparison R).naturality
      ((DerivedCategory.quotientCompQhIso _).hom.app N))
    ((derivedSectionsOverOpen (onePointRingedSpace R) ⊤).rightDerived_fac_app
      (derivedSectionsOverOpenUnit (onePointRingedSpace R) ⊤)
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (structureSheafRing (onePointRingedSpace R))) (ComplexShape.up ℤ)) _
      (Stacks.DerivedFunctor.HigherDerivedOfExact.canonical
        (sectionsOverOpen (onePointRingedSpace R) ⊤))
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N))
    (factorsh_inv_app R N)

private theorem map_inv_hom_comp {C : Type*} {D : Type*} [Category* C] [Category* D]
    (E : C ⥤ D) {a b : C} {x y : D} (fi : a ⟶ b) (fh fh' : b ⟶ a) (h : fi ≫ fh' = 𝟙 a)
    (c c' : E.obj a ⟶ x) (k : x ⟶ y) (hfh : fh = fh') (hc : c = c') :
    E.map fi ≫ E.map fh ≫ c ≫ k = c' ≫ k := by
  rw [hfh, hc, ← Functor.map_comp_assoc, h, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The commutation of sections with the localizations, as the factorization isomorphism. -/
theorem catCommSq_inverse_iso_inv_app
    (N : CochainComplex (SheafOfModules.{u} (structureSheafRing (onePointRingedSpace R))) ℤ) :
    (CatCommSq.iso
        ((onePointSectionsEquivalence R).mapHomologicalComplex (ComplexShape.up ℤ)).inverse
        DerivedCategory.Q DerivedCategory.Q
        (sectionsOverOpen (onePointRingedSpace R) ⊤).mapDerivedCategory).inv.app N =
      (sectionsOverOpen (onePointRingedSpace R) ⊤).mapDerivedCategoryFactors.hom.app N :=
  rfl

/-- The commutation of the one-point identification with the localizations, as the
factorization isomorphism. -/
theorem catCommSq_functor_iso_inv_app (X : CochainComplex (onePointModuleCat R) ℤ) :
    (CatCommSq.iso
        ((onePointSectionsEquivalence R).mapHomologicalComplex (ComplexShape.up ℤ)).functor
        DerivedCategory.Q DerivedCategory.Q
        (onePointSectionsEquivalence R).functor.mapDerivedCategory).inv.app X =
      (onePointSectionsEquivalence R).functor.mapDerivedCategoryFactors.hom.app X :=
  rfl

/-- **The unit `Γ ⟶ RΓ` on the one-point ringed space, transposed along `E ⊣ RΓ({*}, -)`**:
`E` of the unit followed by the counit is the factorization isomorphism of `E` followed by the
counit of the one-point identification on complexes.  This is Stacks 0FP1 for the one-point
identification. -/
theorem onePointDerived_map_sectionsUnitQ_comp_counit
    (N : CochainComplex (SheafOfModules.{u} (structureSheafRing (onePointRingedSpace R))) ℤ) :
    (onePointDerived R).map (sectionsUnitQ (onePointRingedSpace R) ⊤ N) ≫
        (onePointDerivedAdjunction R).counit.app (DerivedCategory.Q.obj N) =
      (onePointSheafFunctor R).mapDerivedCategoryFactors.hom.app
          (((sectionsOverOpen (onePointRingedSpace R) ⊤).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj N) ≫
        DerivedCategory.Q.map ((onePointComplexEquivalence R).counit.app N) := by
  dsimp only [onePointDerivedAdjunction]
  rw [ofNatIsoRight_counit_app]
  show (onePointDerived R).map (sectionsUnitQ (onePointRingedSpace R) ⊤ N) ≫
      (onePointDerived R).map ((onePointDerivedSectionsComparison R).app
        (DerivedCategory.Q.obj N)) ≫
      (onePointDerivedSectionsAdjunction R).counit.app (DerivedCategory.Q.obj N) = _
  refine Eq.trans ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ (onePointDerivedSectionsAdjunction R).counit.app (DerivedCategory.Q.obj N))
      (((onePointDerived R).map_comp _ _).symm.trans
        (congrArg (onePointDerived R).map
          (sectionsUnitQ_comp_onePointDerivedSectionsComparison R N))))) ?_
  dsimp only [onePointDerivedSectionsAdjunction]
  rw [Adjunction.localization_counit_app]
  exact map_inv_hom_comp _ _ _ _ (Iso.inv_hom_id_app _ _) _ _ _ (catCommSq_inverse_iso_inv_app R N)
    (catCommSq_functor_iso_inv_app R _)

/-! ### Two identities for an equivalence carrying one bifunctor to another -/

section Abstract

variable {C D : Type*} [Category* C] [Category* D] (e : C ≌ D) (G : C ⥤ C ⥤ C) (F : D ⥤ D ⥤ D)
  (tsec : e.inverse.prod e.inverse ⋙ Functor.uncurry.obj G ≅ Functor.uncurry.obj F ⋙ e.inverse)

/-- The comparison `e(x ⊗ y) ≅ e x ⊗ e y` induced by an isomorphism
`e⁻¹ a ⊗ e⁻¹ b ≅ e⁻¹(a ⊗ b)`, in the shape of `onePointTensorComparisonIso`. -/
abbrev tensorComparisonOfEquivalence :
    Functor.uncurry.obj G ⋙ e.functor ≅ e.functor.prod e.functor ⋙ Functor.uncurry.obj F :=
  Functor.isoWhiskerRight (Functor.isoWhiskerRight (e.prod e).unitIso (Functor.uncurry.obj G))
      e.functor ≪≫
    Functor.isoWhiskerLeft (e.functor.prod e.functor)
        (Functor.isoWhiskerRight tsec e.functor) ≪≫
      Functor.isoWhiskerLeft (e.functor.prod e.functor ⋙ Functor.uncurry.obj F) e.counitIso

private theorem triangle_paste {C D : Type*} [Category* C] [Category* D] (E : C ⥤ D)
    {P P' Q Q' : C} {X' Z : D} (g₁ : P ⟶ P') (u : P' ⟶ P) (t : P ⟶ Q) (t' : P' ⟶ Q')
    (Γk : Q' ⟶ Q) (εX' : E.obj Q' ⟶ X') (εZ : E.obj Q ⟶ Z) (k : X' ⟶ Z)
    (hn₁ : E.map Γk ≫ εZ = εX' ≫ k) (hn₂ : u ≫ t = t' ≫ Γk) (htri : g₁ ≫ u = 𝟙 P) :
    E.map g₁ ≫ E.map t' ≫ εX' ≫ k = E.map t ≫ εZ := by
  simp only [← hn₁, ← Functor.map_comp_assoc, ← hn₂, reassoc_of% htri]

/-- **The comparison against the counit**: at `(e⁻¹ a, e⁻¹ b)` the comparison followed by the
counit in each factor is `e` of the given isomorphism followed by the counit. -/
theorem tensorComparisonOfEquivalence_hom_comp_counit (a b : D) :
    (tensorComparisonOfEquivalence e G F tsec).hom.app (e.inverse.obj a, e.inverse.obj b) ≫
        (Functor.uncurry.obj F).map (e.counit.app a ×ₘ e.counit.app b) =
      e.functor.map (tsec.hom.app (a, b)) ≫ e.counit.app ((Functor.uncurry.obj F).obj (a, b)) := by
  have hτ : (tensorComparisonOfEquivalence e G F tsec).hom.app (e.inverse.obj a, e.inverse.obj b) =
      e.functor.map ((Functor.uncurry.obj G).map
          (e.unit.app (e.inverse.obj a) ×ₘ e.unit.app (e.inverse.obj b))) ≫
        e.functor.map (tsec.hom.app (e.functor.obj (e.inverse.obj a),
          e.functor.obj (e.inverse.obj b))) ≫
        e.counit.app ((Functor.uncurry.obj F).obj (e.functor.obj (e.inverse.obj a),
          e.functor.obj (e.inverse.obj b))) := rfl
  have hn₁ := e.counit.naturality ((Functor.uncurry.obj F).map (e.counit.app a ×ₘ e.counit.app b))
  have hn₂ := tsec.hom.naturality (e.counit.app a ×ₘ e.counit.app b)
  have htri : (Functor.uncurry.obj G).map
        (e.unit.app (e.inverse.obj a) ×ₘ e.unit.app (e.inverse.obj b)) ≫
      (e.inverse.prod e.inverse ⋙ Functor.uncurry.obj G).map (e.counit.app a ×ₘ e.counit.app b) =
        𝟙 _ := by
    show (Functor.uncurry.obj G).map _ ≫ (Functor.uncurry.obj G).map
      (e.inverse.map (e.counit.app a) ×ₘ e.inverse.map (e.counit.app b)) = _
    rw [← Functor.map_comp, prod_comp, Equivalence.unit_inverse_comp,
      Equivalence.unit_inverse_comp]
    exact (Functor.uncurry.obj G).map_id _
  rw [hτ, Category.assoc, Category.assoc]
  exact triangle_paste e.functor _ _ _ _ _ _ _ _ hn₁ hn₂ htri

end Abstract

section AbstractTotal

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  (E : C ⥤ D) (Γ : D ⥤ C) [E.Additive] [Γ.Additive]
  (G : C ⥤ C ⥤ C) (F : D ⥤ D ⥤ D) [G.PreservesZeroMorphisms]
  [∀ X, (G.obj X).PreservesZeroMorphisms] [F.PreservesZeroMorphisms]
  [∀ X, (F.obj X).PreservesZeroMorphisms]
  (ε : Γ ⋙ E ⟶ 𝟭 D)
  (τ : ∀ a b : C, E.obj ((G.obj a).obj b) ≅ (F.obj (E.obj a)).obj (E.obj b))
  (σinv : ∀ a b : D, (G.obj (Γ.obj a)).obj (Γ.obj b) ⟶ Γ.obj ((F.obj a).obj b))
  (N N' : CochainComplex D ℤ)
  [HomologicalComplex.HasMapBifunctor N N' F (ComplexShape.up ℤ)]
  [HomologicalComplex.HasMapBifunctor ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
    ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj N') G (ComplexShape.up ℤ)]
  [HomologicalComplex.HasMapBifunctor
    ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj N))
    ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj N')) F (ComplexShape.up ℤ)]

/-- **The comparison of total complexes along an equivalence, against the counit.**  For an
additive functor `E` with a "counit" `ε : Γ ⋙ E ⟶ 𝟭`, comparisons `τ : E(a ⊗ b) ≅ E a ⊗ E b`
and `σinv : Γ a ⊗ Γ b ⟶ Γ(a ⊗ b)` satisfying the triangle `hτσ`, a comparison of total complexes
`T` built from `τ` and a map `t` of total complexes built from `σinv`, the map
`E(t) ≫ ε` is `T` followed by `ε` in both tensor factors. -/
theorem map_total_comp_counit
    (hτσ : ∀ a b : D, (τ (Γ.obj a) (Γ.obj b)).hom ≫ (F.map (ε.app a)).app (E.obj (Γ.obj b)) ≫
      (F.obj a).map (ε.app b) = E.map (σinv a b) ≫ ε.app ((F.obj a).obj b))
    (εc : ∀ X : CochainComplex D ℤ,
      (E.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ⟶ X)
    (hεc : ∀ (X : CochainComplex D ℤ) (n : ℤ), (εc X).f n = ε.app (X.X n))
    (T : (E.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (HomologicalComplex.mapBifunctor ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
          ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj N') G (ComplexShape.up ℤ)) ≅
      HomologicalComplex.mapBifunctor
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj N))
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj N')) F (ComplexShape.up ℤ))
    (hT : ∀ (p q n : ℤ) (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (p, q) = n),
      HomologicalComplex.ιMapBifunctor
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj N))
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj N')) F (ComplexShape.up ℤ) p q n h ≫
        T.inv.f n =
        (τ (Γ.obj (N.X p)) (Γ.obj (N'.X q))).inv ≫
          E.map (HomologicalComplex.ιMapBifunctor
            ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
            ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj N') G (ComplexShape.up ℤ) p q n h))
    (t : HomologicalComplex.mapBifunctor ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
        ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj N') G (ComplexShape.up ℤ) ⟶
      (Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (HomologicalComplex.mapBifunctor N N' F (ComplexShape.up ℤ)))
    (ht : ∀ (p q n : ℤ) (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (p, q) = n),
      HomologicalComplex.ιMapBifunctor ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
          ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj N') G (ComplexShape.up ℤ) p q n h ≫
        t.f n =
        σinv (N.X p) (N'.X q) ≫
          Γ.map (HomologicalComplex.ιMapBifunctor N N' F (ComplexShape.up ℤ) p q n h)) :
    (E.mapHomologicalComplex (ComplexShape.up ℤ)).map t ≫
        εc (HomologicalComplex.mapBifunctor N N' F (ComplexShape.up ℤ)) =
      T.hom ≫ HomologicalComplex.mapBifunctorMap (εc N) (εc N') F (ComplexShape.up ℤ) := by
  rw [← cancel_epi T.inv, Iso.inv_hom_id_assoc]
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine HomologicalComplex.mapBifunctor.hom_ext fun p q h => ?_
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  rw [reassoc_of% (hT p q n h), HomologicalComplex.ι_mapBifunctorMap, hεc, hεc, hεc,
    ← E.map_comp_assoc, ht, E.map_comp_assoc]
  have hnat := ε.naturality (HomologicalComplex.ιMapBifunctor N N' F (ComplexShape.up ℤ) p q n h)
  dsimp only [Functor.comp_map, Functor.id_map] at hnat
  rw [hnat, ← Category.assoc (E.map _), ← hτσ, Category.assoc, Iso.inv_hom_id_assoc,
    Category.assoc]
  rfl

end AbstractTotal


/-! ### The naive cup product on sections over the one point -/

/-- `Γ({*}, -)` on sheaves of modules on the one-point ringed space. -/
abbrev onePointSections : onePointSheafCat R ⥤ onePointModuleCat R :=
  (onePointSectionsEquivalence R).inverse

/-- `Γ({*}, -)` is additive. -/
instance onePointSections_additive : (onePointSections R).Additive :=
  inferInstanceAs (sectionsOverOpen (onePointRingedSpace R) ⊤).Additive

/-- `Γ({*}, -)` is an equivalence. -/
instance onePointSections_isEquivalence : (onePointSections R).IsEquivalence :=
  (onePointSectionsEquivalence R).isEquivalence_inverse

/-- `Γ({*}, F ⊗_𝒪 G) ≅ Γ({*}, F) ⊗_A Γ({*}, G)`, the inverse of the canonical map. -/
abbrev onePointSectionsTensorIso (a b : onePointSheafCat R) :
    (onePointSections R).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (onePointRingedSpace R).sheaf).obj a).obj b) ≅
      ((MonoidalCategory.curriedTensor (ModuleCat.{u} (baseRing (onePointRingedSpace R)))).obj
        ((onePointSections R).obj a)).obj ((onePointSections R).obj b) :=
  ((onePointTensorSectionsIso R).app (a, b)).symm

/-- `onePointSectionsTensorIso` is natural in pairs of morphisms. -/
private theorem onePointSectionsTensorIso_naturality {a b a' b' : onePointSheafCat R}
    (f : ((a, b) : onePointSheafCat R × onePointSheafCat R) ⟶ (a', b')) :
    (onePointSections R).map
          ((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor (onePointRingedSpace R).sheaf)).map f) ≫
        (onePointSectionsTensorIso R a' b').hom =
      (onePointSectionsTensorIso R a b).hom ≫
        ((onePointSections R).prod (onePointSections R) ⋙ Functor.uncurry.obj
          (MonoidalCategory.curriedTensor (ModuleCat.{u} (baseRing (onePointRingedSpace R))))).map
            f :=
  (onePointTensorSectionsIso R).inv.naturality f

/-- `onePointSectionsTensorIso` is natural in the first factor. -/
theorem onePointSectionsTensorIso_naturality_left
    {a a' : onePointSheafCat R} (f : a ⟶ a')
    (b : onePointSheafCat R) :
    (onePointSections R).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor (onePointRingedSpace R).sheaf).map f).app b) ≫
        (onePointSectionsTensorIso R a' b).hom =
      (onePointSectionsTensorIso R a b).hom ≫
        ((MonoidalCategory.curriedTensor (ModuleCat.{u} (baseRing (onePointRingedSpace R)))).map
          ((onePointSections R).map f)).app ((onePointSections R).obj b) := by
  simpa only [Functor.comp_map, Functor.prod_map, Functor.uncurry_obj_map, Functor.prod_obj,
    CategoryTheory.Functor.map_id, Category.comp_id] using
    onePointSectionsTensorIso_naturality R ((f : a ⟶ a') ×ₘ 𝟙 b)

/-- `onePointSectionsTensorIso` is natural in the second factor. -/
theorem onePointSectionsTensorIso_naturality_right
    (a : onePointSheafCat R)
    {b b' : onePointSheafCat R} (g : b ⟶ b') :
    (onePointSections R).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor (onePointRingedSpace R).sheaf).obj a).map g) ≫
        (onePointSectionsTensorIso R a b').hom =
      (onePointSectionsTensorIso R a b).hom ≫
        ((MonoidalCategory.curriedTensor (ModuleCat.{u} (baseRing (onePointRingedSpace R)))).obj
          ((onePointSections R).obj a)).map ((onePointSections R).map g) := by
  simpa only [Functor.comp_map, Functor.prod_map, Functor.uncurry_obj_map, Functor.prod_obj,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] using
    onePointSectionsTensorIso_naturality R (𝟙 a ×ₘ (g : b ⟶ b'))

variable (N N' : CochainComplex (onePointSheafCat R) ℤ)

/-- **Sections of a total tensor complex on the one point**:
`Γ({*}, Tot(N ⊗_𝒪 N')) ≅ Tot(Γ({*}, N) ⊗_A Γ({*}, N'))`. -/
def onePointSectionsTotalIso :
    ((onePointSections R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (HomologicalComplex.mapBifunctor N N'
          (Stacks.SheafOfModules.Tensor.sheafTensor (onePointRingedSpace R).sheaf)
          (ComplexShape.up ℤ)) ≅
      HomologicalComplex.mapBifunctor
        (((onePointSections R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
        (((onePointSections R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N')
        (MonoidalCategory.curriedTensor (ModuleCat.{u} (baseRing (onePointRingedSpace R))))
        (ComplexShape.up ℤ) :=
  CategoryTheory.Functor.mapBifunctorTotalIso
    (Stacks.SheafOfModules.Tensor.sheafTensor (onePointRingedSpace R).sheaf)
    (MonoidalCategory.curriedTensor (ModuleCat.{u} (baseRing (onePointRingedSpace R))))
    (onePointSections R) (onePointSections R) (onePointSections R) (onePointSectionsTensorIso R)
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (fun f b => onePointSectionsTensorIso_naturality_left R f b)
    (fun a _ _ g => onePointSectionsTensorIso_naturality_right R a g) N N'

end Stacks.Cohomology.DerivedSectionsOnAPoint

namespace Stacks.Cohomology.DerivedSectionsOnAPoint

open Stacks.Cohomology.DerivedSectionsLeray Stacks.Cohomology.DerivedRelativeCupProduct

attribute [local instance] HasDerivedCategory.standard

variable (R : Type u) [CommRing R]

/-- **The global cup product on the one-point ringed space**, the doubled-counit adjunction
morphism of Stacks 0B68 for the adjunction `E ⊣ RΓ({*}, -)` and the comparison
`E(x ⊗^𝐋_A y) ≅ E x ⊗^𝐋 E y`. -/
abbrev onePointCupProduct (G G' : DerivedCategory (SheafOfModules.{u}
    (structureSheafRing (onePointRingedSpace R)))) :=
  adjunctionBitensorMap (onePointDerivedAdjunction R)
    (Functor.uncurry.obj (tensorBase (onePointRingedSpace R)))
    (Functor.uncurry.obj (derivedTensorProductFunctor (onePointRingedSpace R).sheaf))
    (onePointDerivedTensorIso R).hom G G'

variable (N N' : CochainComplex (onePointSheafCat R) ℤ)

/-- The counit of the one-point identification on complexes, at the tensor product's
spelling. -/
def onePointComplexCounit (X : CochainComplex (onePointSheafCat R) ℤ) :
    ((onePointSheafFunctor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((onePointSections R).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ⟶ X :=
  (onePointComplexEquivalence R).counit.app X

/-- The degree-`n` component of `onePointComplexCounit` is the counit of the one-point
identification at `X.X n`. -/
theorem onePointComplexCounit_f (X : CochainComplex (onePointSheafCat R) ℤ) (n : ℤ) :
    (onePointComplexCounit R X).f n = (onePointSectionsEquivalence R).counit.app (X.X n) := rfl

/-- The comparison `E Tot(X ⊗ Y) ≅ Tot(E X ⊗ E Y)` on a summand of its target. -/
theorem onePointTensorComplexIso_inv_ι (X Y : CochainComplex (onePointModuleCat R) ℤ)
    (p q n : ℤ) (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (p, q) = n) :
    HomologicalComplex.ιMapBifunctor
        (((onePointSheafFunctor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj X)
        (((onePointSheafFunctor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj Y)
        (Stacks.SheafOfModules.Tensor.sheafTensor (onePointRingedSpace R).sheaf)
        (ComplexShape.up ℤ) p q n h ≫ ((onePointTensorComplexIso R).inv.app (X, Y)).f n =
      (onePointTensorIso R (X.X p) (Y.X q)).inv ≫
        (onePointSheafFunctor R).map (HomologicalComplex.ιMapBifunctor X Y
          (MonoidalCategory.curriedTensor (onePointModuleCat R)) (ComplexShape.up ℤ) p q n h) :=
  CategoryTheory.Functor.ι_mapBifunctorTotalIso_inv
    (MonoidalCategory.curriedTensor (onePointModuleCat R))
    (Stacks.SheafOfModules.Tensor.sheafTensor (onePointRingedSpace R).sheaf)
    (onePointSheafFunctor R) (onePointSheafFunctor R) (onePointSheafFunctor R)
    (onePointTensorIso R) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (fun {_ _} u N => onePointTensorIso_naturality_left R u N)
    (fun M {_ _} v => onePointTensorIso_naturality_right R M v) X Y p q n h

/-- The naive cup product `Tot(Γ N ⊗ Γ N') ⟶ Γ Tot(N ⊗ N')` on a summand of its source. -/
theorem onePointSectionsTotalIso_inv_ι (p q n : ℤ) (h : ComplexShape.π (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    HomologicalComplex.ιMapBifunctor
        (((onePointSections R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
        (((onePointSections R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N')
        (MonoidalCategory.curriedTensor (onePointModuleCat R)) (ComplexShape.up ℤ) p q n h ≫
        (onePointSectionsTotalIso R N N').inv.f n =
      (onePointTensorSectionsMap R).app (N.X p, N'.X q) ≫
        (onePointSections R).map (HomologicalComplex.ιMapBifunctor N N'
          (Stacks.SheafOfModules.Tensor.sheafTensor (onePointRingedSpace R).sheaf)
          (ComplexShape.up ℤ) p q n h) :=
  CategoryTheory.Functor.ι_mapBifunctorTotalIso_inv
    (Stacks.SheafOfModules.Tensor.sheafTensor (onePointRingedSpace R).sheaf)
    (MonoidalCategory.curriedTensor (onePointModuleCat R))
    (onePointSections R) (onePointSections R) (onePointSections R) (onePointSectionsTensorIso R)
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (fun f b => onePointSectionsTensorIso_naturality_left R f b)
    (fun a _ _ g => onePointSectionsTensorIso_naturality_right R a g) N N' p q n h

/-- The counit of the one-point identification, at the tensor product's spelling. -/
def onePointCounit : onePointSections R ⋙ onePointSheafFunctor R ⟶ 𝟭 (onePointSheafCat R) :=
  (onePointSectionsEquivalence R).counit

/-- The comparison `E(Γ a ⊗ Γ b) ≅ E Γ a ⊗ E Γ b` against the counit. -/
theorem onePointTensorIso_hom_comp_counit (a b : onePointSheafCat R) :
    (onePointTensorIso R ((onePointSections R).obj a) ((onePointSections R).obj b)).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor (onePointRingedSpace R).sheaf).map
          ((onePointCounit R).app a)).app
          ((onePointSheafFunctor R).obj ((onePointSections R).obj b)) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor (onePointRingedSpace R).sheaf).obj a).map
          ((onePointCounit R).app b) =
      (onePointSheafFunctor R).map ((onePointTensorSectionsMap R).app (a, b)) ≫
        (onePointCounit R).app
          (((Stacks.SheafOfModules.Tensor.sheafTensor (onePointRingedSpace R).sheaf).obj a).obj
            b) :=
  tensorComparisonOfEquivalence_hom_comp_counit (onePointSectionsEquivalence R)
    (MonoidalCategory.curriedTensor (onePointModuleCat R))
    (Stacks.SheafOfModules.Tensor.sheafTensor (onePointRingedSpace R).sheaf)
    (onePointTensorSectionsIso R) a b

/-- **The naive cup product of the one point against the counit**: `E` of the naive cup
product `Tot(Γ N ⊗ Γ N') ⟶ Γ Tot(N ⊗ N')` followed by the counit is the comparison
`E Tot(Γ N ⊗ Γ N') ≅ Tot(E Γ N ⊗ E Γ N')` followed by the counit in each factor. -/
theorem onePointSectionsTotalIso_inv_counit :
    ((onePointSheafFunctor R).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (onePointSectionsTotalIso R N N').inv ≫
      onePointComplexCounit R
        (HomologicalComplex.mapBifunctor N N'
          (Stacks.SheafOfModules.Tensor.sheafTensor (onePointRingedSpace R).sheaf)
          (ComplexShape.up ℤ)) =
    ((onePointTensorComplexIso R).app
        (((onePointSections R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N,
          ((onePointSections R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N')).hom ≫
      HomologicalComplex.mapBifunctorMap (onePointComplexCounit R N)
        (onePointComplexCounit R N')
        (Stacks.SheafOfModules.Tensor.sheafTensor (onePointRingedSpace R).sheaf)
        (ComplexShape.up ℤ) :=
  map_total_comp_counit (onePointSheafFunctor R) (onePointSections R)
    (MonoidalCategory.curriedTensor (onePointModuleCat R))
    (Stacks.SheafOfModules.Tensor.sheafTensor (onePointRingedSpace R).sheaf)
    (onePointCounit R) (onePointTensorIso R)
    (fun a b => (onePointTensorSectionsMap R).app (a, b)) N N'
    (onePointTensorIso_hom_comp_counit R)
    (onePointComplexCounit R) (onePointComplexCounit_f R)
    ((onePointTensorComplexIso R).app
        (((onePointSections R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N,
          ((onePointSections R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N'))
    (onePointTensorComplexIso_inv_ι R _ _)
    (onePointSectionsTotalIso R N N').inv
    (onePointSectionsTotalIso_inv_ι R N N')

/-- The component of `rightComparison` at a pair of complexes: the factorization isomorphisms of
`E` in both factors, followed by the canonical map to the total tensor complex and the inverse of
`onePointTensorComplexIso`. -/
theorem rightComparison_app (X Y : CochainComplex (onePointModuleCat R) ℤ) :
    (rightComparison R).app (X, Y) =
      (Functor.uncurry.obj (derivedTensorProductFunctor (onePointRingedSpace R).sheaf)).map
          ((onePointSheafFunctor R).mapDerivedCategoryFactors.hom.app X ×ₘ
            (onePointSheafFunctor R).mapDerivedCategoryFactors.hom.app Y) ≫
        (derivedToTensorNatTrans (onePointRingedSpace R)).app
          (((onePointSheafFunctor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj X,
            ((onePointSheafFunctor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj Y) ≫
        (DerivedCategory.Q.mapIso ((onePointTensorComplexIso R).app (X, Y))).inv :=
  rfl

private theorem comp_comp_inv_eq {C : Type*} [Category* C] {a b c d e f : C} (al : a ⟶ b)
    (p : b ⟶ c) (cn : c ⟶ d) (ec : a ⟶ e) (fa : e ⟶ f) (i : f ≅ d)
    (h : al ≫ p ≫ cn ≫ i.inv = ec ≫ fa) : ec ≫ fa ≫ i.hom = al ≫ p ≫ cn := by
  rw [← Category.assoc, ← h]
  simp

/-- `onePointSectionsTotalIso_inv_counit`, read in the derived category. -/
theorem onePointSectionsTotalIso_inv_counit_Q :
    DerivedCategory.Q.map (((onePointSheafFunctor R).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (onePointSectionsTotalIso R N N').inv) ≫
      DerivedCategory.Q.map (onePointComplexCounit R
        (HomologicalComplex.mapBifunctor N N'
          (Stacks.SheafOfModules.Tensor.sheafTensor (onePointRingedSpace R).sheaf)
          (ComplexShape.up ℤ))) =
    DerivedCategory.Q.map ((onePointTensorComplexIso R).hom.app
        (((onePointSections R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N,
          ((onePointSections R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N')) ≫
      DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (onePointComplexCounit R N)
        (onePointComplexCounit R N')
        (Stacks.SheafOfModules.Tensor.sheafTensor (onePointRingedSpace R).sheaf)
        (ComplexShape.up ℤ)) :=
  (DerivedCategory.Q.map_comp _ _).symm.trans
    ((congrArg DerivedCategory.Q.map (onePointSectionsTotalIso_inv_counit R N N')).trans
      (DerivedCategory.Q.map_comp _ _))

/-- The canonical map to the total tensor complex is natural along the counit. -/
theorem derivedToTensor_counit :
    (derivedToTensorNatTrans (onePointRingedSpace R)).app
          (((onePointSheafFunctor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (((onePointSections R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N),
            ((onePointSheafFunctor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (((onePointSections R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N')) ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (onePointComplexCounit R N)
          (onePointComplexCounit R N')
          (Stacks.SheafOfModules.Tensor.sheafTensor (onePointRingedSpace R).sheaf)
          (ComplexShape.up ℤ)) =
      (Functor.uncurry.obj (derivedTensorProductFunctor (onePointRingedSpace R).sheaf)).map
          (DerivedCategory.Q.map (onePointComplexCounit R N) ×ₘ
            DerivedCategory.Q.map (onePointComplexCounit R N')) ≫
        (derivedToTensorNatTrans (onePointRingedSpace R)).app (N, N') := by
  have h := (derivedToTensorNatTrans (onePointRingedSpace R)).naturality
    (onePointComplexCounit R N ×ₘ onePointComplexCounit R N')
  exact (h.trans (congrArg (fun z => (derivedToTensorNatTrans (onePointRingedSpace R)).app
    (((onePointSheafFunctor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((onePointSections R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N),
      ((onePointSheafFunctor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((onePointSections R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N')) ≫
      DerivedCategory.Q.map z)
    (totalComplexPair_map _ (onePointComplexCounit R N) (onePointComplexCounit R N')))).symm

/-- `E` of the canonical map to the total tensor complex, followed by the factorization isomorphism
of `E` and `onePointTensorComplexIso`, is the comparison `onePointDerivedTensorIso` followed by the
factorization isomorphisms in both factors and the canonical map to the total tensor complex. -/
theorem onePointDerived_toTensor (X Y : CochainComplex (onePointModuleCat R) ℤ) :
    (onePointDerived R).map
          ((canonicalDerivedToTensorNatTrans ↥(baseRing (onePointRingedSpace R))).app (X, Y)) ≫
        (onePointSheafFunctor R).mapDerivedCategoryFactors.hom.app
          ((totalTensorPair ↥(baseRing (onePointRingedSpace R))).obj (X, Y)) ≫
        DerivedCategory.Q.map ((onePointTensorComplexIso R).hom.app (X, Y)) =
      (onePointDerivedTensorIso R).hom.app (DerivedCategory.Q.obj X, DerivedCategory.Q.obj Y) ≫
        (Functor.uncurry.obj (derivedTensorProductFunctor (onePointRingedSpace R).sheaf)).map
          ((onePointSheafFunctor R).mapDerivedCategoryFactors.hom.app X ×ₘ
            (onePointSheafFunctor R).mapDerivedCategoryFactors.hom.app Y) ≫
        (derivedToTensorNatTrans (onePointRingedSpace R)).app
          (((onePointSheafFunctor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj X,
            ((onePointSheafFunctor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj Y) := by
  have h := toTensorLeft_eq R X Y
  rw [toTensorLeft, toTensorRight, rightComparison_app] at h
  exact comp_comp_inv_eq _ _ _ _ _
    (DerivedCategory.Q.mapIso ((onePointTensorComplexIso R).app (X, Y))) h

/-- **Stacks 0FP3 for the one-point identification**: on the one-point ringed space the
canonical map to the total tensor complex of the sections, followed by the naive cup product
`Tot(Γ N ⊗_A Γ N') ⟶ Γ Tot(N ⊗ N')` and the unit `Γ ⟶ RΓ`, is the unit in each factor followed
by the global cup product and `RΓ` of the canonical map to the total tensor complex. -/
theorem onePointCupProduct_naive :
    (canonicalDerivedToTensorNatTrans ↥(baseRing (onePointRingedSpace R))).app
          (((onePointSections R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N,
            ((onePointSections R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N') ≫
        DerivedCategory.Q.map (onePointSectionsTotalIso R N N').inv ≫
        sectionsUnitQ (onePointRingedSpace R) ⊤
          (HomologicalComplex.mapBifunctor N N'
            (Stacks.SheafOfModules.Tensor.sheafTensor (onePointRingedSpace R).sheaf)
            (ComplexShape.up ℤ)) =
      (Functor.uncurry.obj (tensorBase (onePointRingedSpace R))).map
          (sectionsUnitQ (onePointRingedSpace R) ⊤ N ×ₘ
            sectionsUnitQ (onePointRingedSpace R) ⊤ N') ≫
        onePointCupProduct R (DerivedCategory.Q.obj N) (DerivedCategory.Q.obj N') ≫
        (baseSections (onePointRingedSpace R)).map
          ((derivedToTensorNatTrans (onePointRingedSpace R)).app (N, N')) :=
  CupProductAndDerivedPushforwardOnRingedSpaces.adjunctionBitensorMap_hexagon
    (onePointDerivedAdjunction R) (Functor.uncurry.obj (tensorBase (onePointRingedSpace R)))
    (Functor.uncurry.obj (derivedTensorProductFunctor (onePointRingedSpace R).sheaf))
    (onePointDerivedTensorIso R).hom
    (sectionsUnitQ (onePointRingedSpace R) ⊤ N) (sectionsUnitQ (onePointRingedSpace R) ⊤ N')
    ((canonicalDerivedToTensorNatTrans ↥(baseRing (onePointRingedSpace R))).app
      (((onePointSections R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N,
        ((onePointSections R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N'))
    (DerivedCategory.Q.map (onePointSectionsTotalIso R N N').inv)
    (sectionsUnitQ (onePointRingedSpace R) ⊤
      (HomologicalComplex.mapBifunctor N N'
        (Stacks.SheafOfModules.Tensor.sheafTensor (onePointRingedSpace R).sheaf)
        (ComplexShape.up ℤ)))
    ((derivedToTensorNatTrans (onePointRingedSpace R)).app (N, N'))
    _ _ _ _ _ _ _ _ _ _ _
    (onePointDerived_map_sectionsUnitQ_comp_counit R N)
    (onePointDerived_map_sectionsUnitQ_comp_counit R N')
    (onePointDerived_map_sectionsUnitQ_comp_counit R _)
    ((onePointSheafFunctor R).mapDerivedCategoryFactors_hom_naturality _)
    (onePointSectionsTotalIso_inv_counit_Q R N N')
    (onePointDerived_toTensor R _ _)
    (derivedToTensor_counit R N N')

end Stacks.Cohomology.DerivedSectionsOnAPoint
