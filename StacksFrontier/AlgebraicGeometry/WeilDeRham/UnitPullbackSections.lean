module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.DerivedSectionsBridge
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.DiagonalCupStatements
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.KunnethSpaceFunctoriality
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalKunnethCupWithClassCanonical
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayCompositeSections
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ExactPushforwardSingleUnit
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.PullbackHgroupComposition
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomologyCompIso
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisonsOnHomotopyCategory
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.OrdinaryTopDegreeMate

/-!
# The pullback map on cohomology through derived sections over a base

Let `c : V ⟶ S`, `c' : V' ⟶ S` and `g : V' ⟶ V` be morphisms of schemes with `g ≫ c = c'`, and
let `F` be an `𝒪_V`-module. The pullback `g^* : Hᵠ(V, F) ⟶ Hᵠ(V', g^*F)` of [Stacks, Tag 01F9]
along the unit `F ⟶ g_*g^*F` is built in `D(Ab)`: derived global sections of the comparison
`F[-k] ⟶ (g_*g^*F)[-k] ⟶ Rg_*((g^*F)[-k])` of [Stacks, Tag 01F8], followed by the Leray
identification `RΓ(V, Rg_* -) ≅ RΓ(V', -)` of [Stacks, Tag 01EZ]. Read through the identification
`Hᵠ(V, F) ≅ H^m(RΓ_S(V, F[-k]))`, `q + k = m`, with the cohomology of the derived sections over
the base `RΓ_S(V, -)`, it is the map induced on `H^m` by the pullback
`RΓ_S(V, F[-k]) ⟶ RΓ_S(V', Lg^*(F[-k]))` on derived sections over the base followed by the
comparison `Lg^*(F[-k]) ⟶ (g^*F)[-k]` of the derived with the ordinary pullback; the latter is an
isomorphism when `F` is flat.

Both sides are the unit `K ⟶ Rg_*Lg^*K` followed by a Leray identification:

* the comparison of [Stacks, Tag 01F8] at the unit is the unit of `Lg^* ⊣ Rg_*` at `F[-k]`
  followed by `Rg_*` of the comparison `Lg^*(F[-k]) ⟶ (g^*F)[-k]`;
* the pullback on derived sections over the base is `RΓ_S(V, -)` of the unit followed by the
  relative Leray identification `RΓ_S(V, Rg_* -) ≅ RΓ_S(V', -)`;
* the Leray identification in abelian groups is the relative one with the scalars forgotten: both
  are induced, by the universal property of the right derived functor `RΓ(V', -)`, by units that
  agree once the scalars are forgotten.

## Main definitions

* `Stacks.WeilDeRham.derivedGlobalSectionsOverBaseIso`: `RΓ(V, -) ≅ RΓ_S(V, -)` in `D(Ab)`.
* `Stacks.WeilDeRham.singleDegreePullbackComparison`: the comparison `Lf^*(F[-k]) ⟶ (f^*F)[-k]`.
* `Stacks.WeilDeRham.singlePullbackComparison`: the same comparison in degree zero, for schemes.

## Main results

* `Stacks.WeilDeRham.derivedGlobalSectionsOverBaseIso_comp_lerayCompositeComparison`: the Leray
  comparison in abelian groups is the relative Leray comparison over the base.
* `Stacks.WeilDeRham.pullbackSections_comp_eq`: the pullback on derived sections over the base is
  the unit followed by the relative Leray identification.
* `Stacks.WeilDeRham.singleFunctor_map_unit_comp_singleToDerivedPushforward`: the comparison of
  [Stacks, Tag 01F8] at the unit is the derived unit followed by the derived-to-ordinary
  comparison.
* `Stacks.WeilDeRham.isIso_singleDegreePullbackComparison`: the comparison is an isomorphism for
  a flat module.
* `Stacks.WeilDeRham.pullbackHgroup_comp_hgroupSectionsOverBaseIso_hom`,
  `Stacks.WeilDeRham.unitPullbackCompat_single`, `Stacks.WeilDeRham.unitPullbackCompat`: the
  pullback map on cohomology through derived sections over the base.

## References

* [Stacks Project, Tag 01F9](https://stacks.math.columbia.edu/tag/01F9)
* [Stacks Project, Tag 01F8](https://stacks.math.columbia.edu/tag/01F8)
* [Stacks Project, Tag 01EZ](https://stacks.math.columbia.edu/tag/01EZ)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.GlobalKunneth (baseRing baseSections sectionsOverBase
  pullbackSingleComparison)
open Stacks.Cohomology.KunnethCupWithClass (pullbackSections)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward
  derivedAdjunction derivedPushforwardUnit derivedPullbackComparison derivedPushforwardCompIso
  homotopyPullbackPushforwardAdjunction)
open Stacks.Cohomology.DerivedSectionsLeray (lerayCompositeComparison derivedPreimageSectionsCompIso
  preimageSections derivedPreimageSectionsUnit sectionsOverOpen derivedSectionsOverOpenUnit)
open Stacks.DeRham.GysinCohomologyBaseChange (CohomologyPullbackComparison pullbackHgroup
  derivedPushforwardMap singleToDerivedPushforward lerayComparisonAb)
open Stacks.DerivedCategoryComparisons (mapDerivedCategoryCompIso)
open Stacks.AlgebraicGeometry.TopDegreeBaseChange
  (mapHomotopyCategoryAdjunction_unit_app_singleFunctor mapHomotopyCategorySingleFunctor_hom_app_eq)
open Stacks.Cohomology.LerayCupPairing (restrictGlobal preimageSectionsIso)
open Stacks.DeRham.CohomologicalGysin Stacks.DeRham.GysinCupHodge
open scoped Stacks.StandardDerivedModel

universe u

namespace Stacks.WeilDeRham

/-! ### Derived global sections in abelian groups over the base -/

section Sections

variable {S V : RingedSpace.{u, u}} (c : V ⟶ S)

/-- Derived global sections in abelian groups are derived sections over the base, read in
abelian groups. -/
def derivedGlobalSectionsOverBaseIso :
    derivedGlobalSections V ≅
      sectionsOverBase c ⋙
        (forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u}).mapDerivedCategory :=
  derivedGlobalSectionsForgetIso V ≪≫
    Functor.isoWhiskerLeft (baseSections V)
      (mapDerivedCategoryCompIso (restrictGlobal c)
        (forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u})) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (preimageSectionsIso c) _

/-- The components of `derivedGlobalSectionsOverBaseIso`. -/
theorem derivedGlobalSectionsOverBaseIso_hom_app
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing V))) :
    (derivedGlobalSectionsOverBaseIso c).hom.app K =
      (derivedGlobalSectionsForgetIso V).hom.app K ≫
        (mapDerivedCategoryCompIso (restrictGlobal c)
          (forget₂ (ModuleCat.{u} (baseRing S))
            AddCommGrpCat.{u})).hom.app ((baseSections V).obj K) ≫
        (forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u}).mapDerivedCategory.map
          ((preimageSectionsIso c).hom.app K) := by
  dsimp only [derivedGlobalSectionsOverBaseIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Iso.symm_hom, Functor.associator_inv_app]
  exact congrArg (fun t => _ ≫ _ ≫ t) (Category.id_comp _)

/-- Moving two isomorphisms across a commuting square, at variables. -/
private lemma iso_square_swap {C : Type*} [Category* C] {P P' Q Q' : C} (p : P ≅ P') (q : Q ≅ Q')
    (x : P ⟶ Q') (y : P' ⟶ Q) (h : p.inv ≫ x = y ≫ q.hom) : p.hom ≫ y = x ≫ q.inv := by
  rw [Iso.eq_comp_inv, Category.assoc, ← h, Iso.hom_inv_id_assoc]

/-- The algebra of `homologyForgetIso_hom_comp_sectionsOverBaseHomologyIso_inv`, at
variables. -/
private lemma forget_sections_chase {C : Type*} [Category* C] {P₀ P₁ P₂ P₂' R P₃ Q Q' : C}
    (a : P₀ ⟶ P₁) (b : P₁ ⟶ P₂) (i : P₂ ⟶ P₂') (b' : P₁ ⟶ P₂') (k : P₂' ⟶ P₃)
    (k₁ : P₂' ⟶ R) (k₂ : R ⟶ P₃) (m : P₁ ⟶ Q) (n : Q ⟶ Q') (e₂ : Q' ⟶ P₃)
    (e₁' : Q ⟶ R) (t : P₀ ⟶ Q') (ht : t = a ≫ m ≫ n) (hk : k = k₁ ≫ k₂) (hbi : b ≫ i = b')
    (hc : m ≫ e₁' = b' ≫ k₁) (hn : n ≫ e₂ = e₁' ≫ k₂) :
    a ≫ b ≫ i ≫ k = t ≫ e₂ := by
  subst hk hbi ht
  simp only [Category.assoc]
  rw [hn, reassoc_of% hc]

/-- **The identification of the cohomology groups with the cohomology of derived sections over
the base is `H^m` of `derivedGlobalSectionsOverBaseIso`**, followed by the commutation of
forgetting the scalars with cohomology. -/
theorem homologyForgetIso_hom_comp_sectionsOverBaseHomologyIso_inv
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing V))) (m : ℤ) :
    (homologyForgetIso V m K).hom ≫ (forgetRestrictGlobalIso c _).hom ≫
        (forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u}).map
          (sectionsOverBaseHomologyIso c K m).inv =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).map
          ((derivedGlobalSectionsOverBaseIso c).hom.app K) ≫
        ((forget₂ (ModuleCat.{u} (baseRing S))
          AddCommGrpCat.{u}).mapDerivedCategoryHomologyFunctorIso
          m).hom.app ((sectionsOverBase c).obj K) := by
  have hc := Functor.mapDerivedCategoryHomologyFunctorIso_comp_app (restrictGlobal c)
    (forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u}) m ((baseSections V).obj K)
  have hn := ((forget₂ (ModuleCat.{u} (baseRing S))
    AddCommGrpCat.{u}).mapDerivedCategoryHomologyFunctorIso
    m).hom.naturality ((preimageSectionsIso c).hom.app K)
  simp only [Functor.comp_map] at hn
  have hc' : (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).map
        ((mapDerivedCategoryCompIso (restrictGlobal c)
          (forget₂ (ModuleCat.{u} (baseRing S))
            AddCommGrpCat.{u})).hom.app ((baseSections V).obj K)) ≫
        ((forget₂ (ModuleCat.{u} (baseRing S))
          AddCommGrpCat.{u}).mapDerivedCategoryHomologyFunctorIso
          m).hom.app ((restrictGlobal c).mapDerivedCategory.obj ((baseSections V).obj K)) =
      ((restrictGlobal c ⋙ forget₂ (ModuleCat.{u} (baseRing S))
        AddCommGrpCat.{u}).mapDerivedCategoryHomologyFunctorIso
          m).hom.app ((baseSections V).obj K) ≫
        (forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u}).map
          (((restrictGlobal c).mapDerivedCategoryHomologyFunctorIso m).inv.app
            ((baseSections V).obj K)) :=
    iso_square_swap ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).mapIso
        ((mapDerivedCategoryCompIso (restrictGlobal c)
          (forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u})).app ((baseSections V).obj K)))
      ((forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u}).mapIso
        (((restrictGlobal c).mapDerivedCategoryHomologyFunctorIso m).app ((baseSections V).obj K)))
      _ _ hc
  have hk : (forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u}).map
        (sectionsOverBaseHomologyIso c K m).inv =
      (forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u}).map
          (((restrictGlobal c).mapDerivedCategoryHomologyFunctorIso m).inv.app
            ((baseSections V).obj K)) ≫
        (forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u}).map
          ((DerivedCategory.homologyFunctor _ m).map ((preimageSectionsIso c).hom.app K)) := by
    simp only [sectionsOverBaseHomologyIso, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv,
      Iso.symm_inv, Functor.map_comp]
  have hbi : ((forget₂ (ModuleCat.{u} (baseRing V)) AddCommGrpCat.{u}).mapDerivedCategoryHomologyIso
        m).hom.app ((baseSections V).obj K) ≫ (forgetRestrictGlobalIso c _).hom =
      ((restrictGlobal c ⋙ forget₂ (ModuleCat.{u} (baseRing S))
        AddCommGrpCat.{u}).mapDerivedCategoryHomologyFunctorIso
          m).hom.app ((baseSections V).obj K) := by
    rw [Functor.mapDerivedCategoryHomologyIso_eq_mapDerivedCategoryHomologyFunctorIso]
    exact Category.comp_id _
  have ht : (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).map
        ((derivedGlobalSectionsOverBaseIso c).hom.app K) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).map
          ((derivedGlobalSectionsForgetIso V).hom.app K) ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).map
          ((mapDerivedCategoryCompIso (restrictGlobal c)
            (forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u})).hom.app
              ((baseSections V).obj K)) ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).map
          ((forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u}).mapDerivedCategory.map
            ((preimageSectionsIso c).hom.app K)) :=
    (congrArg (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).map
      (derivedGlobalSectionsOverBaseIso_hom_app c K)).trans
      (((DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).map_comp _ _).trans
        (congrArg (_ ≫ ·) ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).map_comp _ _)))
  exact forget_sections_chase _ _ _ _ _ _ _ _ _ _ _ _ ht hk hbi hc' hn

/-- The identification `hgroupSectionsOverBaseIso`, written through
`derivedGlobalSectionsOverBaseIso`. -/
theorem hgroupSectionsOverBaseIso_hom_eq (A : SheafOfModules.{u} (structureSheafRing V))
    (k q : ℕ) (m : ℤ) (h : (q : ℤ) + (k : ℤ) = m) :
    (hgroupSectionsOverBaseIso c A k q m h).hom =
      (cohomologyDerivedSingleIso V A (k : ℤ) m q (by omega)).inv ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).map
          ((derivedGlobalSectionsOverBaseIso c).hom.app
            ((DerivedCategory.singleFunctor _ (k : ℤ)).obj A)) ≫
        ((forget₂ (ModuleCat.{u} (baseRing S))
          AddCommGrpCat.{u}).mapDerivedCategoryHomologyFunctorIso
          m).hom.app
            ((sectionsOverBase c).obj ((DerivedCategory.singleFunctor _ (k : ℤ)).obj A)) := by
  simp only [hgroupSectionsOverBaseIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  exact congrArg (_ ≫ ·) (homologyForgetIso_hom_comp_sectionsOverBaseHomologyIso_inv c _ m)

/-- The algebra of `derivedGlobalSectionsUnit_comp_derivedGlobalSectionsOverBaseIso_hom`, at
variables. -/
private lemma unit_forget_chase {C : Type*} [Category* C] {A₀ A₁ A₂ A₃ A₄ B₁ B₂ B₃ : C}
    (x : A₀ ⟶ A₁) (d : A₁ ⟶ A₂) (cm : A₂ ⟶ A₃) (s : A₃ ⟶ A₄) (t : A₁ ⟶ A₄)
    (fu : A₀ ⟶ A₂) (fi : A₀ ⟶ B₁) (fv : B₁ ⟶ A₂) (cm' : B₁ ⟶ B₂) (ru : B₂ ⟶ A₃)
    (g₁ : A₀ ⟶ B₃) (g₂ : B₃ ⟶ B₂) (w : B₃ ⟶ A₄) (ht : t = d ≫ cm ≫ s) (h₁ : x ≫ d = fu)
    (h₂ : fu = fi ≫ fv) (h₃ : fv ≫ cm = cm' ≫ ru) (h₄ : fi ≫ cm' = g₁ ≫ g₂)
    (h₅ : g₂ ≫ ru ≫ s = w) :
    x ≫ t = g₁ ≫ w := by
  subst ht h₂ h₅
  rw [reassoc_of% h₁, reassoc_of% h₃, reassoc_of% h₄]

/-- Inverting the factorization of an isomorphism, at variables. -/
private lemma inv_comp_hom_eq_of_inv_eq {C : Type*} [Category* C] {P Q R T : C} (e : P ≅ T)
    (a : T ≅ Q) (b : Q ≅ R) (i : P ≅ R)
    (h : e.inv = a.hom ≫ b.hom ≫ i.inv) : i.inv ≫ e.hom = b.inv ≫ a.inv := by
  rw [← cancel_mono e.inv, Category.assoc, Iso.hom_inv_id, Category.comp_id, h]
  simp

/-- Cancelling the factorization of an exact functor against the unit comparison, inside a
functor, at variables. -/
private lemma map_unit_chase {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {X Y Z W : C} (a : X ≅ Y) (q : Y ⟶ Y) (ru : X ⟶ Z) (ps : Z ⟶ W) (du : Y ⟶ W) (m : X ⟶ Y)
    (hu : ru ≫ ps = m ≫ du) (hm : m = a.hom ≫ q) (hq : q = 𝟙 Y) :
    F.map a.inv ≫ F.map ru ≫ F.map ps = F.map du := by
  subst hm hq
  rw [← F.map_comp, ← F.map_comp, hu, Category.comp_id, Iso.inv_hom_id_assoc]

/-- **The unit of derived global sections in abelian groups, through
`derivedGlobalSectionsOverBaseIso`, is the unit of derived sections over the base**, read in
abelian groups. -/
theorem derivedGlobalSectionsUnit_comp_derivedGlobalSectionsOverBaseIso_hom
    (Kh : HomotopyCategory (SheafOfModules.{u} (structureSheafRing V)) (ComplexShape.up ℤ)) :
    (derivedGlobalSectionsUnit V).app Kh ≫
        (derivedGlobalSectionsOverBaseIso c).hom.app (DerivedCategory.Qh.obj Kh) =
      (forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u}).mapDerivedCategoryFactorsh.inv.app
          (((preimageSections c ⊤).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj Kh) ≫
        (forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u}).mapDerivedCategory.map
          ((derivedPreimageSectionsUnit c ⊤).app Kh) := by
  have h₁ := derivedGlobalSectionsForget_fac_app V Kh
  have hid : DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso (sectionsForgetIso V)
      (ComplexShape.up ℤ)).inv.app Kh) = 𝟙 _ := DerivedCategory.Qh.map_id _
  have h₂ : (forgetUnit V).app Kh =
      (forget₂ (ModuleCat.{u} (baseRing V)) AddCommGrpCat.{u}).mapDerivedCategoryFactorsh.inv.app
          (((sectionsOverOpen V ⊤).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj Kh) ≫
        (forget₂ (ModuleCat.{u} (baseRing V)) AddCommGrpCat.{u}).mapDerivedCategory.map
          ((derivedSectionsOverOpenUnit V ⊤).app Kh) := by
    simp only [forgetUnit, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id,
      hid]
    exact Category.id_comp _
  have h₃ := (mapDerivedCategoryCompIso (restrictGlobal c)
    (forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u})).hom.naturality
      ((derivedSectionsOverOpenUnit V ⊤).app Kh)
  simp only [Functor.comp_map] at h₃
  have h₄ := inv_comp_hom_eq_of_inv_eq
    ((mapDerivedCategoryCompIso (restrictGlobal c)
      (forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u})).app
        (DerivedCategory.Qh.obj
          (((sectionsOverOpen V ⊤).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj Kh)))
    ((forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u}).mapDerivedCategory.mapIso
      ((restrictGlobal c).mapDerivedCategoryFactorsh.app
        (((sectionsOverOpen V ⊤).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj Kh)))
    ((forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u}).mapDerivedCategoryFactorsh.app
      (((restrictGlobal c).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        (((sectionsOverOpen V ⊤).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj Kh)))
    ((restrictGlobal c ⋙ forget₂ (ModuleCat.{u} (baseRing S))
      AddCommGrpCat.{u}).mapDerivedCategoryFactorsh.app
      (((sectionsOverOpen V ⊤).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj Kh))
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_app_Qh _ _ _)
  have hid' : DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
      (Iso.refl (sectionsOverOpen V ⊤ ⋙ restrictGlobal c))
      (ComplexShape.up ℤ)).hom.app Kh) = 𝟙 _ := DerivedCategory.Qh.map_id _
  have hu := Stacks.Cohomology.LerayCupPairing.preimageSectionsIso_unit c Kh
  have h₅ := map_unit_chase (forget₂ (ModuleCat.{u} (baseRing S))
    AddCommGrpCat.{u}).mapDerivedCategory
    ((restrictGlobal c).mapDerivedCategoryFactorsh.app
      (((sectionsOverOpen V ⊤).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj Kh)) _ _ _ _ _ hu rfl hid'
  exact unit_forget_chase _ _ _ _ _ _ _ _ _ _ _ _ _
    (derivedGlobalSectionsOverBaseIso_hom_app c _) h₁ h₂ h₃ h₄ h₅

end Sections

/-! ### The Leray comparisons -/

section Leray

variable {S V V' : RingedSpace.{u, u}} (c : V ⟶ S) (g : V' ⟶ V)

/-- The algebra of `derivedGlobalSectionsOverBaseIso_comp_lerayCompositeComparison`, at
variables. -/
private lemma leray_forget_chase {C : Type*} [Category* C] {A₀ A₁ A₂ A₃ A₄ B₀ B₁ B₂ : C}
    (x : A₀ ⟶ A₁) (θ₁ : A₁ ⟶ A₂) (fl : A₂ ⟶ A₃) (la : A₁ ⟶ A₄) (θc : A₄ ⟶ A₃) (i : A₀ ⟶ B₀)
    (fd₁ : B₀ ⟶ A₂) (fd₂ : B₀ ⟶ B₁) (fs : B₁ ⟶ A₃) (lua : A₀ ⟶ A₄) (q : A₀ ⟶ A₀)
    (y : A₀ ⟶ B₂) (ds : B₂ ⟶ A₄) (θc' : B₂ ⟶ B₁)
    (h₁ : x ≫ θ₁ = i ≫ fd₁) (h₂ : fd₁ ≫ fl = fd₂ ≫ fs) (h₃ : x ≫ la = lua)
    (h₄ : lua = q ≫ y ≫ ds) (hq : q = 𝟙 A₀) (h₅ : ds ≫ θc = θc' ≫ fs)
    (h₆ : y ≫ θc' = i ≫ fd₂) :
    x ≫ θ₁ ≫ fl = x ≫ la ≫ θc := by
  subst hq
  rw [reassoc_of% h₁, h₂, reassoc_of% h₃, h₄, Category.id_comp, Category.assoc, h₅,
    reassoc_of% h₆]

/-- Reading a factorization through an identity inside a functor, at variables. -/
private lemma map_fac_chase {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {X₀ X₁ X₂ X₃ : C} (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₃) (l : X₀ ⟶ X₃) (q : X₀ ⟶ X₀) (d : X₀ ⟶ X₂)
    (e : X₂ ⟶ X₃) (hab : a ≫ b = l) (hl : l = q ≫ d ≫ e) (hq : q = 𝟙 X₀) :
    F.map a ≫ F.map b = F.map d ≫ F.map e := by
  subst hl hq
  rw [← F.map_comp, hab, Category.id_comp, F.map_comp]

/-- **The Leray comparison in abelian groups is the relative Leray comparison over the base**:
through `derivedGlobalSectionsOverBaseIso`, the Leray comparison `RΓ(V', -) ⟶ RΓ(V, Rg_* -)` in
`D(Ab)` is the relative Leray comparison `RΓ_S(V', -) ⟶ RΓ_S(V, Rg_* -)` for `g` over `c`, read in
abelian groups. -/
theorem derivedGlobalSectionsOverBaseIso_comp_lerayCompositeComparison :
    (derivedGlobalSectionsOverBaseIso (g ≫ c)).hom ≫
        Functor.whiskerRight (lerayCompositeComparison g c ⊤)
          (forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u}).mapDerivedCategory =
      lerayComparisonAb g ≫
        Functor.whiskerLeft (derivedPushforward g)
          (derivedGlobalSectionsOverBaseIso c).hom := by
  apply (derivedGlobalSections V').rightDerived_ext (derivedGlobalSectionsUnit V')
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing V')) (ComplexShape.up ℤ))
  ext Kh
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  have h₂ := map_fac_chase (forget₂ (ModuleCat.{u} (baseRing S))
    AddCommGrpCat.{u}).mapDerivedCategory
    _ _ _ _ _ _ (Stacks.Cohomology.DerivedSectionsLeray.lerayCompositeComparison_fac_app g c ⊤ Kh)
    rfl (DerivedCategory.Qh.map_id _)
  have h₄ := Stacks.DeRham.GysinCohomologyBaseChange.lerayUnitAb_app g Kh
  have h₅ := (derivedGlobalSectionsOverBaseIso c).hom.naturality
    ((derivedPushforwardUnit g).app Kh)
  simp only [Functor.comp_map] at h₅
  exact leray_forget_chase _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (derivedGlobalSectionsUnit_comp_derivedGlobalSectionsOverBaseIso_hom (g ≫ c) Kh) h₂
    (Stacks.DeRham.GysinCohomologyBaseChange.lerayComparisonAb_fac_app g Kh) h₄
    (DerivedCategory.Qh.map_id _) h₅
    (derivedGlobalSectionsUnit_comp_derivedGlobalSectionsOverBaseIso_hom c _)

/-- The algebra of `pullbackSections_comp_eq`, at variables. -/
private lemma pullback_leray_chase {C D : Type*} [Category* C] [Category* D] (B : C ⥤ D)
    {X₀ X₁ X₂ : C} {Y₀ Y₁ Y₂ : D} (ιK : Y₀ ≅ B.obj X₀) (u : X₀ ⟶ X₁) (e : X₁ ≅ X₂)
    (ιL : Y₁ ≅ B.obj X₂) (ιR : Y₂ ≅ B.obj X₁) (lc : Y₁ ⟶ Y₂) (su : Y₀ ⟶ Y₂)
    (hc : ιL.hom ≫ B.map e.inv = lc ≫ ιR.hom) (hs : su ≫ ιR.hom = ιK.hom ≫ B.map u) :
    (ιK.hom ≫ B.map (u ≫ e.hom) ≫ ιL.inv) ≫ lc = su := by
  have hlc : ιL.inv ≫ lc = B.map e.inv ≫ ιR.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, hc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [Category.assoc, B.map_comp, hlc, ← B.map_comp_assoc e.hom, Iso.hom_inv_id,
    B.map_id, Category.id_comp]
  rw [← Category.assoc, ← hs, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **The pullback map on derived sections over the base factors through the base**: for
`g ≫ c`, the pullback `RΓ_S(V, K) ⟶ RΓ_S(V', Lg^*K)` is `RΓ_S(V, -)` of the unit
`K ⟶ Rg_*Lg^*K` followed by the identification `RΓ_S(V, Rg_* -) ≅ RΓ_S(V', -)` of the relative
Leray comparison. -/
theorem pullbackSections_comp_eq
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing V))) :
    @Eq ((sectionsOverBase c).obj K ⟶ (sectionsOverBase (g ≫ c)).obj ((derivedPullback g).obj K))
      (pullbackSections c g (g ≫ c) rfl K)
      ((sectionsOverBase c).map
          ((derivedAdjunction g).unit.app K) ≫
        (derivedPreimageSectionsCompIso g c ⊤).hom.app
          ((derivedPullback g).obj K)) := by
  rw [← cancel_mono ((derivedPreimageSectionsCompIso g c
    ⊤).inv.app ((derivedPullback g).obj K)), Category.assoc, Iso.hom_inv_id_app]
  refine Eq.trans ?_ (Category.comp_id _).symm
  have hc := NatTrans.congr_app (Stacks.Cohomology.DerivedSectionsLeray.lerayComparison_comp g c ⊤)
    ((derivedPullback g).obj K)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hc
  have hs := (Stacks.Cohomology.GlobalKunneth.lerayIso c).inv.naturality
    ((derivedAdjunction g).unit.app K)
  simp only [Functor.comp_map] at hs
  unfold pullbackSections
  rw [pullbackLeg_comp_eq]
  exact pullback_leray_chase (baseSections S)
    ((Stacks.Cohomology.GlobalKunneth.lerayIso c).app K).symm
    _ ((derivedPushforwardCompIso g c).app _)
    ((Stacks.Cohomology.GlobalKunneth.lerayIso (g ≫ c)).app _).symm
    ((Stacks.Cohomology.GlobalKunneth.lerayIso c).app _).symm _ _ hc hs

end Leray

/-! ### The derived-to-ordinary pullback comparison in degree `k` -/

section Single

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The derived-to-ordinary pullback comparison `Lf^*(F[-k]) ⟶ (f^*F)[-k]`** of a module placed
in degree `k`: the counit of the left derived functor `Lf^*` at the complex `F[-k]`, read through
the identifications of the single functors with the localization of single complexes and the
commutation of the degreewise pullback with `(-)[-k]`. -/
def singleDegreePullbackComparison (F : SheafOfModules.{u} (structureSheafRing Y)) (k : ℤ) :
    (derivedPullback f).obj ((DerivedCategory.singleFunctor _ k).obj F) ⟶
      (DerivedCategory.singleFunctor _ k).obj ((modulePullback f).obj F) :=
  (derivedPullback f).map ((DerivedCategory.singleFunctorIsoCompQ _ k).hom.app F) ≫
    (derivedPullback f).map
      ((DerivedCategory.quotientCompQhIso _).inv.app ((CochainComplex.singleFunctor _ k).obj F)) ≫
    (derivedPullbackComparison f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor _ k).obj F)) ≫
    (DerivedCategory.quotientCompQhIso _).hom.app
      (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor _ k).obj F)) ≫
    DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex (modulePullback f)
      (ComplexShape.up ℤ) k).hom.app F) ≫
    (DerivedCategory.singleFunctorIsoCompQ _ k).inv.app ((modulePullback f).obj F)

/-- Dropping identities around a morphism, at variables. -/
private lemma id_id_comp_id_eq {C : Type*} [Category* C] {P Q : C} (a b : P ⟶ P) (x : P ⟶ Q)
    (d : Q ⟶ Q) (ha : a = 𝟙 P) (hb : b = 𝟙 P) (hd : d = 𝟙 Q) : a ≫ b ≫ x ≫ d = x := by
  subst ha hb hd
  simp

/-- Inserting an identity, at variables. -/
private lemma eq_id_comp_of {C : Type*} [Category* C] {B D : C} (q : B ⟶ B) (y : B ⟶ D)
    (hq : q = 𝟙 B) : y = q ≫ y := by
  subst hq
  simp

/-- **The comparison `Lf(F[-k]) ⟶ (PF)[-k]` read on homotopy categories, in bare categories.**
The comparison built on complexes, from `τ : S ≅ single ⋙ Q`, the comparison
`c : Qh ⋙ Lf ⟶ MP ⋙ Qh` at the class of `F[-k]` and the commutation `smP` of `P` with `single`,
is the comparison built on homotopy categories, from `σ : S ≅ Hs ⋙ Qh` and the commutation `hsP`
of `P` with `Hs`, as soon as the pieces are related through `q : quot ⋙ Qh ≅ Q` and
`e : single ⋙ quot ≅ Hs`. -/
private lemma single_comparison_chase {AY AX HY HX DY DX CY CX : Type*} [Category* AY]
    [Category* AX] [Category* HY] [Category* HX] [Category* DY] [Category* DX] [Category* CY]
    [Category* CX] {P : AY ⥤ AX} {HsY : AY ⥤ HY} {HsX : AX ⥤ HX} {QhY : HY ⥤ DY}
    {QhX : HX ⥤ DX} {SY : AY ⥤ DY} {SX : AX ⥤ DX} {MP : HY ⥤ HX} {Lf : DY ⥤ DX}
    {singY : AY ⥤ CY} {singX : AX ⥤ CX} {quotY : CY ⥤ HY} {quotX : CX ⥤ HX}
    {QY : CY ⥤ DY} {QX : CX ⥤ DX} {CP : CY ⥤ CX}
    (τY : SY ≅ singY ⋙ QY) (τX : SX ≅ singX ⋙ QX) (qY : quotY ⋙ QhY ≅ QY)
    (qX : quotX ⋙ QhX ≅ QX) (σY : SY ≅ HsY ⋙ QhY) (σX : SX ≅ HsX ⋙ QhX)
    (eY : singY ⋙ quotY ≅ HsY) (eX : singX ⋙ quotX ≅ HsX) (c : QhY ⋙ Lf ⟶ MP ⋙ QhX)
    (fac : quotY ⋙ MP ≅ CP ⋙ quotX) (smP : singY ⋙ CP ≅ P ⋙ singX) (hsP : HsY ⋙ MP ≅ P ⋙ HsX)
    (F : AY) (ι : QhX.obj (MP.obj (quotY.obj (singY.obj F))) ⟶ QX.obj (CP.obj (singY.obj F)))
    (hι : ι = QhX.map (fac.hom.app (singY.obj F)) ≫ qX.hom.app (CP.obj (singY.obj F)))
    (hσY : σY.hom.app F ≫ QhY.map (eY.inv.app F) = τY.hom.app F ≫ qY.inv.app (singY.obj F))
    (hσX : QhX.map (eX.hom.app (P.obj F)) ≫ σX.inv.app (P.obj F) =
      qX.hom.app (singX.obj (P.obj F)) ≫ τX.inv.app (P.obj F))
    (hhs : MP.map (eY.inv.app F) ≫ fac.hom.app (singY.obj F) ≫ quotX.map (smP.hom.app F) ≫
      eX.hom.app (P.obj F) = hsP.hom.app F) :
    Lf.map (τY.hom.app F) ≫ Lf.map (qY.inv.app (singY.obj F)) ≫
        c.app (quotY.obj (singY.obj F)) ≫ ι ≫ QX.map (smP.hom.app F) ≫ τX.inv.app (P.obj F) =
      Lf.map (σY.hom.app F) ≫ c.app (HsY.obj F) ≫ QhX.map (hsP.hom.app F) ≫
        σX.inv.app (P.obj F) := by
  subst hι
  have nc := c.naturality (eY.inv.app F)
  have nq := qX.hom.naturality (smP.hom.app F)
  simp only [Functor.comp_map, Functor.comp_obj] at nc nq
  have hL : Lf.map (τY.hom.app F) ≫ Lf.map (qY.inv.app (singY.obj F)) =
      Lf.map (σY.hom.app F) ≫ Lf.map (QhY.map (eY.inv.app F)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hσY]
  simp only [Category.assoc]
  rw [reassoc_of% hL, reassoc_of% nc, ← reassoc_of% nq, ← hσX, ← hhs]
  simp only [Functor.map_comp, Category.assoc]

/-- `singleDegreePullbackComparison` read on the homotopy category: the comparison
`derivedPullbackComparison` at `F[-k]`, between the commutation of `f^*` with `(-)[-k]` on
homotopy categories and the two identifications `DerivedCategory.singleFunctorIsoCompQh`. -/
theorem singleDegreePullbackComparison_eq (F : SheafOfModules.{u} (structureSheafRing Y))
    (k : ℤ) :
    singleDegreePullbackComparison f F k =
      (derivedPullback f).map ((DerivedCategory.singleFunctorIsoCompQh _ k).hom.app F) ≫
        (derivedPullbackComparison f).app
          ((HomotopyCategory.singleFunctor _ k).obj F) ≫
        DerivedCategory.Qh.map (((modulePullback f).mapHomotopyCategorySingleFunctor k).hom.app F) ≫
        (DerivedCategory.singleFunctorIsoCompQh _ k).inv.app ((modulePullback f).obj F) := by
  have hσY : (DerivedCategory.singleFunctorIsoCompQh
        (SheafOfModules.{u} (structureSheafRing Y)) k).hom.app F ≫
      DerivedCategory.Qh.map ((HomotopyCategory.singleFunctorPostcompQuotientIso
        (SheafOfModules.{u} (structureSheafRing Y)) k).hom.app F) =
      (DerivedCategory.singleFunctorIsoCompQ (SheafOfModules.{u} (structureSheafRing Y))
        k).hom.app F ≫
        (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing Y))).inv.app
          ((CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) k).obj F) :=
    ((congrArg (_ ≫ ·) (CategoryTheory.Functor.map_id DerivedCategory.Qh _)).trans
      (Category.comp_id _)).trans ((Stacks.DerivedIndexing.singleFunctorIsoCompQh_hom_app k F).trans
        (Category.id_comp _).symm)
  have hσX : DerivedCategory.Qh.map ((HomotopyCategory.singleFunctorPostcompQuotientIso
        (SheafOfModules.{u} (structureSheafRing X)) k).inv.app ((modulePullback f).obj F)) ≫
      (DerivedCategory.singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing X)) k).inv.app
        ((modulePullback f).obj F) =
      (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X))).hom.app
          ((CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) k).obj
            ((modulePullback f).obj F)) ≫
        (DerivedCategory.singleFunctorIsoCompQ (SheafOfModules.{u} (structureSheafRing X))
          k).inv.app
          ((modulePullback f).obj F) := by
    have hσ := (Iso.inv_eq_inv ((DerivedCategory.singleFunctorIsoCompQh
        (SheafOfModules.{u} (structureSheafRing X)) k).app ((modulePullback f).obj F))
      ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X))).app
        ((CochainComplex.singleFunctor _ k).obj ((modulePullback f).obj F))).symm).2
      (Stacks.DerivedIndexing.singleFunctorIsoCompQh_hom_app k _)
    exact ((congrArg (· ≫ _) (CategoryTheory.Functor.map_id DerivedCategory.Qh _)).trans
      (Category.id_comp _)).trans (hσ.trans (Category.comp_id _).symm)
  have hhs : ((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((HomotopyCategory.singleFunctorPostcompQuotientIso
          (SheafOfModules.{u} (structureSheafRing Y)) k).hom.app F) ≫
      ((modulePullback f).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app
        ((CochainComplex.singleFunctor _ k).obj F) ≫
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex (modulePullback f)
          (ComplexShape.up ℤ) k).hom.app F) ≫
      (HomotopyCategory.singleFunctorPostcompQuotientIso
          (SheafOfModules.{u} (structureSheafRing X)) k).inv.app ((modulePullback f).obj F) =
      ((modulePullback f).mapHomotopyCategorySingleFunctor k).hom.app F :=
    (id_id_comp_id_eq _ _ _ _ (CategoryTheory.Functor.map_id _ _) rfl rfl).trans
      (mapHomotopyCategorySingleFunctor_hom_app_eq
        (modulePullback f) k F).symm
  exact single_comparison_chase
    (DerivedCategory.singleFunctorIsoCompQ (SheafOfModules.{u} (structureSheafRing Y)) k)
    (DerivedCategory.singleFunctorIsoCompQ (SheafOfModules.{u} (structureSheafRing X)) k)
    (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing Y)))
    (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X)))
    (DerivedCategory.singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing Y)) k)
    (DerivedCategory.singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing X)) k)
    (HomotopyCategory.singleFunctorPostcompQuotientIso
      (SheafOfModules.{u} (structureSheafRing Y)) k).symm
    (HomotopyCategory.singleFunctorPostcompQuotientIso
      (SheafOfModules.{u} (structureSheafRing X)) k).symm
    (derivedPullbackComparison f)
    ((modulePullback f).mapHomotopyCategoryFactors (ComplexShape.up ℤ))
    (HomologicalComplex.singleMapHomologicalComplex (modulePullback f) (ComplexShape.up ℤ) k)
    ((modulePullback f).mapHomotopyCategorySingleFunctor k) F _
    (eq_id_comp_of _ _ (CategoryTheory.Functor.map_id DerivedCategory.Qh _)) hσY hσX hhs

/-- **The comparison of [Stacks, Tag 01F8] at the unit is the derived unit followed by the
derived-to-ordinary pullback comparison.** For a module `F` placed in degree `k`, `(-)[-k]` of the
unit `F ⟶ f_*f^*F` followed by the comparison `(f_*f^*F)[-k] ⟶ Rf_*((f^*F)[-k])` is the unit of
`Lf^* ⊣ Rf_*` at `F[-k]` followed by `Rf_*` of `Lf^*(F[-k]) ⟶ (f^*F)[-k]`. -/
theorem singleFunctor_map_unit_comp_singleToDerivedPushforward
    (F : SheafOfModules.{u} (structureSheafRing Y)) (k : ℤ) :
    (DerivedCategory.singleFunctor _ k).map ((modulePullbackPushforwardAdjunction f).unit.app F) ≫
        (singleToDerivedPushforward f k).app
          ((modulePullback f).obj F) =
      (derivedAdjunction f).unit.app
          ((DerivedCategory.singleFunctor _ k).obj F) ≫
        (derivedPushforward f).map
          (singleDegreePullbackComparison f F k) := by
  rw [singleDegreePullbackComparison_eq,
    Stacks.DeRham.GysinCohomologyBaseChange.singleToDerivedPushforward_app]
  exact (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.unit_comp_singleComparison_of_fac
    (derivedAdjunction f)
    (modulePullbackPushforwardAdjunction f)
    (homotopyPullbackPushforwardAdjunction f)
    (derivedPullbackComparison f)
    (derivedPushforwardUnit f)
    (DerivedCategory.singleFunctorIsoCompQh _ k) (DerivedCategory.singleFunctorIsoCompQh _ k)
    ((modulePullback f).mapHomotopyCategorySingleFunctor k)
    ((modulePushforward f).mapHomotopyCategorySingleFunctor k) F
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_unit_fac f _)
    ((Iso.comp_inv_eq (((modulePushforward f).mapHomotopyCategorySingleFunctor k).app
      ((modulePullback f).obj F))).2
        ((mapHomotopyCategoryAdjunction_unit_app_singleFunctor
          (modulePullbackPushforwardAdjunction f) k F).symm.trans
            (Category.assoc _ _ _).symm))).symm

/-- **The derived-to-ordinary pullback comparison of a flat module is an isomorphism**: a flat
module placed in a single degree is K-flat, and on K-flat complexes the derived pullback is
computed degreewise ([Stacks, Tag 06YJ]). -/
theorem isIso_singleDegreePullbackComparison (F : SheafOfModules.{u} (structureSheafRing Y))
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) F) (k : ℤ) :
    IsIso (singleDegreePullbackComparison f F k) := by
  have h : IsIso ((derivedPullbackComparison
      f).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor _ k).obj F))) :=
    Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat f _
      (Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat Y.sheaf F hF k)
  unfold singleDegreePullbackComparison
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' inferInstance
    (IsIso.comp_isIso' h (IsIso.comp_isIso'
      (Iso.isIso_hom ((DerivedCategory.quotientCompQhIso _).app _))
      (IsIso.comp_isIso' inferInstance inferInstance))))

end Single

/-! ### The pullback map on cohomology and the pullback on derived sections over the base -/

section Pullback

variable {S V V' : RingedSpace.{u, u}} (c : V ⟶ S) (g : V' ⟶ V)

/-- **The Leray identification in abelian groups is the relative Leray identification over the
base**, at an object: `RΓ(V, Rg_*L) ≅ RΓ(V', L)` in `D(Ab)`, read through
`derivedGlobalSectionsOverBaseIso`, is `RΓ_S(V, Rg_*L) ≅ RΓ_S(V', L)` read in abelian groups. -/
theorem leray_hom_app_comp_derivedGlobalSectionsOverBaseIso_hom
    (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing V'))) :
    @Eq ((derivedGlobalSections V).obj
          ((derivedPushforward g).obj L) ⟶
        (forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u}).mapDerivedCategory.obj
          ((sectionsOverBase (g ≫ c)).obj L))
      ((CohomologyPullbackComparison.canonical
          g).leray.hom.app L ≫ (derivedGlobalSectionsOverBaseIso (g ≫ c)).hom.app L)
      ((derivedGlobalSectionsOverBaseIso c).hom.app
          ((derivedPushforward g).obj L) ≫
        (forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u}).mapDerivedCategory.map
          ((derivedPreimageSectionsCompIso g c ⊤).hom.app L)) :=
  iso_square_swap ((CohomologyPullbackComparison.canonical
      g).leray.app L)
    ((forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u}).mapDerivedCategory.mapIso
      ((derivedPreimageSectionsCompIso g c ⊤).app L)).symm _ _
    (NatTrans.congr_app (derivedGlobalSectionsOverBaseIso_comp_lerayCompositeComparison c g)
      L).symm

/-- The algebra of `derivedGlobalSections_map_derivedPushforwardMap_comp`, at variables. -/
private lemma pullback_sections_chase {C : Type*} [Category* C]
    {A₀ A₁ A₂ B₁ B₂ C₁ C₂ D₀ D₁ : C} (φ : A₀ ⟶ A₂) (u : A₀ ⟶ A₁) (rs : A₁ ⟶ A₂) (li₀ : A₂ ⟶ B₂)
    (th₀ : B₂ ⟶ C₂) (li : A₁ ⟶ B₁) (ds : B₁ ⟶ B₂) (th : B₁ ⟶ C₁) (fs : C₁ ⟶ C₂)
    (thc : A₁ ⟶ D₁) (fd : D₁ ⟶ C₁) (thK : A₀ ⟶ D₀) (fu : D₀ ⟶ D₁) (fp : D₀ ⟶ C₂)
    (hφ : φ = u ≫ rs) (n₁ : rs ≫ li₀ = li ≫ ds) (n₂ : ds ≫ th₀ = th ≫ fs)
    (h₃ : li ≫ th = thc ≫ fd) (n₄ : u ≫ thc = thK ≫ fu) (h₅ : fp = fu ≫ fd ≫ fs) :
    (φ ≫ li₀) ≫ th₀ = thK ≫ fp := by
  subst hφ h₅
  rw [Category.assoc, Category.assoc, reassoc_of% n₁, n₂, reassoc_of% h₃, reassoc_of% n₄]

/-- **The pullback map on cohomology, in `D(Ab)`, is the pullback on derived sections over the
base.** For a module `F` on `V` placed in degree `k`, derived global sections of the morphism
`F[-k] ⟶ Rg_*((g^*F)[-k])` of [Stacks, Tag 01F8] attached to the unit, followed by the Leray
identification, is — through `derivedGlobalSectionsOverBaseIso` — the pullback
`RΓ_S(V, F[-k]) ⟶ RΓ_S(V', Lg^*(F[-k]))` followed by the comparison
`Lg^*(F[-k]) ⟶ (g^*F)[-k]`. -/
theorem derivedGlobalSections_map_derivedPushforwardMap_comp
    (F : SheafOfModules.{u} (structureSheafRing V)) (k : ℤ) :
    ((derivedGlobalSections V).map
        (derivedPushforwardMap
          (CohomologyPullbackComparison.canonical g) k
          ((modulePullbackPushforwardAdjunction g).unit.app F)) ≫
      (CohomologyPullbackComparison.canonical g).leray.hom.app
        ((DerivedCategory.singleFunctor _ k).obj ((modulePullback g).obj F))) ≫
      (derivedGlobalSectionsOverBaseIso (g ≫ c)).hom.app
        ((DerivedCategory.singleFunctor _ k).obj ((modulePullback g).obj F)) =
    (derivedGlobalSectionsOverBaseIso c).hom.app ((DerivedCategory.singleFunctor _ k).obj F) ≫
      (forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u}).mapDerivedCategory.map
        (pullbackSections c g (g ≫ c) rfl ((DerivedCategory.singleFunctor _ k).obj F) ≫
          (sectionsOverBase (g ≫ c)).map (singleDegreePullbackComparison g F k)) := by
  have hφ := (congrArg (derivedGlobalSections V).map
    (singleFunctor_map_unit_comp_singleToDerivedPushforward g F k)).trans
      ((derivedGlobalSections V).map_comp _ _)
  have n₁ := (CohomologyPullbackComparison.canonical
    g).leray.hom.naturality (singleDegreePullbackComparison g F k)
  simp only [Functor.comp_map] at n₁
  have n₂ := (derivedGlobalSectionsOverBaseIso (g ≫ c)).hom.naturality
    (singleDegreePullbackComparison g F k)
  simp only [Functor.comp_map] at n₂
  have n₄ := (derivedGlobalSectionsOverBaseIso c).hom.naturality
    ((derivedAdjunction g).unit.app ((DerivedCategory.singleFunctor _ k).obj F))
  simp only [Functor.comp_map] at n₄
  have h₅ : (forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u}).mapDerivedCategory.map
        (pullbackSections c g (g ≫ c) rfl ((DerivedCategory.singleFunctor _ k).obj F) ≫
          (sectionsOverBase (g ≫ c)).map (singleDegreePullbackComparison g F k)) =
      (forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u}).mapDerivedCategory.map
          ((sectionsOverBase c).map
            ((derivedAdjunction g).unit.app
              ((DerivedCategory.singleFunctor _ k).obj F))) ≫
        (forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u}).mapDerivedCategory.map
          ((derivedPreimageSectionsCompIso g c ⊤).hom.app
            ((derivedPullback g).obj ((DerivedCategory.singleFunctor _ k).obj F))) ≫
        (forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u}).mapDerivedCategory.map
          ((sectionsOverBase (g ≫ c)).map (singleDegreePullbackComparison g F k)) := by
    rw [pullbackSections_comp_eq, Functor.map_comp, Functor.map_comp, Category.assoc]
  exact pullback_sections_chase _ _ _ _ _ _ _ _ _ _ _ _ _ _ hφ n₁ n₂
    (leray_hom_app_comp_derivedGlobalSectionsOverBaseIso_hom c g _) n₄ h₅

/-- **The pullback map on cohomology is the pullback on derived sections over the base**, as
morphisms: through `hgroupSectionsOverBaseIso`, the pullback map
`Hᵠ(V, F) ⟶ Hᵠ(V', g^*F)` of [Stacks, Tag 01F9] along the unit of `g^* ⊣ g_*`, the module placed
in degree `k`, is the map induced on `H^m` by the pullback
`RΓ_S(V, F[-k]) ⟶ RΓ_S(V', Lg^*(F[-k]))` followed by the comparison
`Lg^*(F[-k]) ⟶ (g^*F)[-k]`. -/
theorem pullbackHgroup_comp_hgroupSectionsOverBaseIso_hom
    (F : SheafOfModules.{u} (structureSheafRing V)) (k q : ℕ) (m : ℤ)
    (h : (q : ℤ) + (k : ℤ) = m) :
    pullbackHgroup (CohomologyPullbackComparison.canonical g) (k : ℤ) m q (by omega)
        ((modulePullbackPushforwardAdjunction g).unit.app F) ≫
      (hgroupSectionsOverBaseIso (g ≫ c) ((modulePullback g).obj F) k q m h).hom =
    (hgroupSectionsOverBaseIso c F k q m h).hom ≫
      (forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u}).map
        ((DerivedCategory.homologyFunctor _ m).map
          (pullbackSections c g (g ≫ c) rfl ((DerivedCategory.singleFunctor _ (k : ℤ)).obj F))) ≫
      (forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u}).map
        ((DerivedCategory.homologyFunctor _ m).map
          ((sectionsOverBase (g ≫ c)).map (singleDegreePullbackComparison g F k))) := by
  have hD := derivedGlobalSections_map_derivedPushforwardMap_comp c g F (k : ℤ)
  have hε := ((forget₂ (ModuleCat.{u} (baseRing S))
    AddCommGrpCat.{u}).mapDerivedCategoryHomologyFunctorIso
    m).hom.naturality
      (pullbackSections c g (g ≫ c) rfl ((DerivedCategory.singleFunctor _ (k : ℤ)).obj F) ≫
          (sectionsOverBase (g ≫ c)).map (singleDegreePullbackComparison g F k))
  simp only [Functor.comp_map] at hε
  rw [hgroupSectionsOverBaseIso_hom_eq, hgroupSectionsOverBaseIso_hom_eq]
  simp only [pullbackHgroup, Category.assoc, Iso.hom_inv_id_assoc]
  refine congrArg (_ ≫ ·) ?_
  rw [← Functor.map_comp_assoc, hD, Functor.map_comp_assoc, hε, Functor.map_comp,
    Functor.map_comp]

end Pullback

/-! ### Schemes -/

section Schemes

variable {S V V' : Scheme.{u}} (c : V ⟶ S) (c' : V' ⟶ S) (g : V' ⟶ V) (hg : g ≫ c = c')

/-- The derived-to-ordinary pullback comparison on a module placed in degree zero, at the
spelling of `DerivedCategory.singleFunctor`. -/
def singlePullbackComparison (F : V.Modules) :
    (derivedPullback g.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing V.toRingedSpace))
          ((0 : ℕ) : ℤ)).obj F) ⟶
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing V'.toRingedSpace))
          ((0 : ℕ) : ℤ)).obj ((Scheme.Modules.pullback g).obj F) :=
  (derivedPullback g.toLRSHom.toShHom).map
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).hom.app F) ≫
    pullbackSingleComparison g.toLRSHom.toShHom F ≫
    (DerivedCategory.singleFunctorIsoCompQ _ 0).inv.app ((Scheme.Modules.pullback g).obj F)

/-- Reassociating a composite with four middle factors, at variables. -/
private lemma comp_comp_assoc_eq {C : Type*} [Category* C] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : C}
    (a : X₀ ⟶ X₁) (b₁ : X₁ ⟶ X₂) (b₂ : X₂ ⟶ X₃) (b₃ : X₃ ⟶ X₄) (b₄ : X₄ ⟶ X₅) (d : X₅ ⟶ X₆) :
    a ≫ (b₁ ≫ b₂ ≫ b₃ ≫ b₄) ≫ d = a ≫ b₁ ≫ b₂ ≫ b₃ ≫ b₄ ≫ d := by
  simp only [Category.assoc]

/-- The comparison in degree zero is `singleDegreePullbackComparison` at `k = 0`. -/
theorem singlePullbackComparison_eq (F : V.Modules) :
    singlePullbackComparison g F =
      singleDegreePullbackComparison g.toLRSHom.toShHom F ((0 : ℕ) : ℤ) :=
  comp_comp_assoc_eq _ _ _ _ _ _

/-- The pullback map on cohomology does not depend on the spelling of the degree in which the
modules are placed. -/
private lemma pullbackHgroup_congr_degree {X X' : RingedSpace.{u, u}} {G : X' ⟶ X}
    (P : CohomologyPullbackComparison G) {a a' : ℤ}
    (ha : a = a') (m : ℤ) (n : ℕ) (hn : m - a = n) (hn' : m - a' = n)
    {M : SheafOfModules.{u} (structureSheafRing X)}
      {M' : SheafOfModules.{u} (structureSheafRing X')}
    (φ : M ⟶ (modulePushforward G).obj M') :
    pullbackHgroup P a m n hn φ =
      pullbackHgroup P a' m n hn' φ := by
  subst ha
  rfl

/-- **The pullback map on cohomology through the derived sections over the base, the module in
degree `k`.** For `g ≫ c = c'` and `x ∈ Hᵠ(V, F)`, the pullback `g^*x ∈ Hᵠ(V', g^*F)` of
[Stacks, Tag 01F9] along the unit of `g^* ⊣ g_*`, read in `H^m(RΓ_S(V', (g^*F)[-k]))` for
`q + k = m`, is the image of `x`, read in `H^m(RΓ_S(V, F[-k]))`, under the pullback
`RΓ_S(V, F[-k]) ⟶ RΓ_S(V', Lg^*(F[-k]))` followed by the comparison
`Lg^*(F[-k]) ⟶ (g^*F)[-k]`. -/
theorem unitPullbackCompat_single (F : V.Modules) (k q : ℕ) (m : ℤ) (h : (q : ℤ) + (k : ℤ) = m)
    (x : Hgroup (structureSheafRing V.toRingedSpace) ⊤ q F) :
    (hgroupSectionsOverBaseIso c'.toLRSHom.toShHom ((Scheme.Modules.pullback g).obj F) k q m
        h).hom
      ((pullbackHgroup (CohomologyPullbackComparison.canonical g.toLRSHom.toShHom) (k : ℤ) m q
        (by omega) ((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app F)).hom x) =
      ((forget₂ (ModuleCat.{u} (baseRing S.toRingedSpace)) AddCommGrpCat.{u}).map
        ((DerivedCategory.homologyFunctor _ m).map
          ((sectionsOverBase c'.toLRSHom.toShHom).map
            (singleDegreePullbackComparison g.toLRSHom.toShHom F k)))).hom
        (((forget₂ (ModuleCat.{u} (baseRing S.toRingedSpace)) AddCommGrpCat.{u}).map
          ((DerivedCategory.homologyFunctor _ m).map
            (pullbackSections c.toLRSHom.toShHom g.toLRSHom.toShHom c'.toLRSHom.toShHom
              (by rw [← hg]; rfl) ((DerivedCategory.singleFunctor _ (k : ℤ)).obj F)))).hom
          ((hgroupSectionsOverBaseIso c.toLRSHom.toShHom F k q m h).hom x)) := by
  subst hg
  exact ConcreteCategory.congr_hom
    (pullbackHgroup_comp_hgroupSectionsOverBaseIso_hom c.toLRSHom.toShHom g.toLRSHom.toShHom F k
      q m h) x

/-- **The pullback map on cohomology through the derived sections over the base.** For
`g ≫ c = c'` and `x ∈ Hᵐ(V, F)`, the pullback `g^*x ∈ Hᵐ(V', g^*F)` of [Stacks, Tag 01F9] along
the unit of `g^* ⊣ g_*` (`Stacks.WeilDeRham.unitPullback`), read in `H^m(RΓ_S(V', g^*F))`, is the
image of `x`, read in `H^m(RΓ_S(V, F))`, under the pullback `RΓ_S(V, F) ⟶ RΓ_S(V', Lg^*F)` on
derived sections over the base followed by the comparison `Lg^*F ⟶ g^*F`. -/
theorem unitPullbackCompat (F : V.Modules) (m : ℕ)
    (x : Hgroup (structureSheafRing V.toRingedSpace) ⊤ m F) :
    (hgroupSectionsOverBaseIso c'.toLRSHom.toShHom ((Scheme.Modules.pullback g).obj F) 0 m m
        (by simp)).hom ((unitPullback g F m).hom x) =
      ((forget₂ (ModuleCat.{u} (baseRing S.toRingedSpace)) AddCommGrpCat.{u}).map
        ((DerivedCategory.homologyFunctor _ (m : ℤ)).map
          ((sectionsOverBase c'.toLRSHom.toShHom).map (singlePullbackComparison g F)))).hom
        (((forget₂ (ModuleCat.{u} (baseRing S.toRingedSpace)) AddCommGrpCat.{u}).map
          ((DerivedCategory.homologyFunctor _ (m : ℤ)).map
            (pullbackSections c.toLRSHom.toShHom g.toLRSHom.toShHom c'.toLRSHom.toShHom
              (by rw [← hg]; rfl) _))).hom
          ((hgroupSectionsOverBaseIso c.toLRSHom.toShHom F 0 m m (by simp)).hom x)) := by
  refine (congrArg (fun t : Hgroup (structureSheafRing V.toRingedSpace) ⊤ m F ⟶
        Hgroup (structureSheafRing V'.toRingedSpace) ⊤ m ((Scheme.Modules.pullback g).obj F) =>
      (hgroupSectionsOverBaseIso c'.toLRSHom.toShHom
        ((Scheme.Modules.pullback g).obj F) 0 m m (by simp)).hom (t.hom x))
    (pullbackHgroup_congr_degree
      (CohomologyPullbackComparison.canonical
        g.toLRSHom.toShHom) (Nat.cast_zero (R := ℤ)).symm (m : ℤ) m (by simp) (by simp)
      ((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app F))).trans ?_
  refine (unitPullbackCompat_single c c' g hg F 0 m m (by simp) x).trans ?_
  exact congrArg (fun t => ((forget₂ (ModuleCat.{u} (baseRing S.toRingedSpace))
    AddCommGrpCat.{u}).map
    ((DerivedCategory.homologyFunctor _ (m : ℤ)).map
      ((sectionsOverBase c'.toLRSHom.toShHom).map t))).hom _)
    (singlePullbackComparison_eq g F).symm

end Schemes

end Stacks.WeilDeRham

end
