module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.HodgeCohomologyModuleBridge
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayCupPairing
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped

/-!
# Cohomology groups as the cohomology of derived sections over a base

For a morphism of ringed spaces `c : V ⟶ S`, the cohomology group `H^q(V, A)` of a sheaf of
modules is the degree `q + k` cohomology of `RΓ(V, A[-k])` computed by the derived sections over
the base `RΓ_S(V, -) = sectionsOverBase c : D(𝒪_V) ⥤ D(Γ(S, 𝒪_S))`, the realization in which the
Künneth maps of [Stacks, Tag 0G7V] are stated. This file builds that identification and records
that it carries the map on cohomology of a morphism of the derived category to the map induced on
derived sections over the base.

## Main definitions

* `Stacks.WeilDeRham.sectionsOverBaseHomologyIso`: `H^m(RΓ_S(V, K)) ≅ H^m(RΓ(V, K))` with scalars
  restricted along `c^♯`.
* `Stacks.WeilDeRham.hgroupSectionsOverBaseIso`: `H^q(V, A) ≅ H^m(RΓ_S(V, A[-k]))`, `q + k = m`.

## Main results

* `Stacks.WeilDeRham.sectionsOverBaseHomologyIso_hom_naturality`.
* `Stacks.WeilDeRham.hgroupSectionsOverBaseIso_cohomologyMapOfSingleHom`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.GlobalKunneth (baseRing baseSections sectionsOverBase)
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule)
open Stacks.Cohomology.LerayCupPairing (restrictGlobal preimageSectionsIso)
open Stacks.DeRham.CohomologicalGysin Stacks.DeRham.GysinCupHodge
open scoped Stacks.StandardDerivedModel

universe u

namespace Stacks.WeilDeRham

variable {S V : RingedSpace.{u, u}} (c : V ⟶ S)

/-- **`H^m(RΓ_S(V, K)) ≅ H^m(RΓ(V, K))`**, the right-hand side with scalars restricted along
`c^♯ : Γ(S, 𝒪_S) ⟶ Γ(V, 𝒪_V)`. -/
def sectionsOverBaseHomologyIso (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing V)))
    (m : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) m).obj
        ((sectionsOverBase c).obj K) ≅
      (restrictGlobal c).obj (cohomologyModule K m) :=
  (DerivedCategory.homologyFunctor _ m).mapIso ((preimageSectionsIso c).symm.app K) ≪≫
    ((restrictGlobal c).mapDerivedCategoryHomologyFunctorIso m).app ((baseSections V).obj K)

/-- The identification `sectionsOverBaseHomologyIso` is natural in the complex. -/
theorem sectionsOverBaseHomologyIso_hom_naturality
    {K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing V))} (φ : K ⟶ L) (m : ℤ) :
    (DerivedCategory.homologyFunctor _ m).map ((sectionsOverBase c).map φ) ≫
        (sectionsOverBaseHomologyIso c L m).hom =
      (sectionsOverBaseHomologyIso c K m).hom ≫
        (restrictGlobal c).map
          ((DerivedCategory.homologyFunctor _ m).map ((baseSections V).map φ)) := by
  have h₁ := (preimageSectionsIso c).inv.naturality φ
  have h₂ := ((restrictGlobal c).mapDerivedCategoryHomologyFunctorIso m).hom.naturality
    ((baseSections V).map φ)
  dsimp only [Functor.comp_map, Functor.comp_obj] at h₁ h₂
  simp only [sectionsOverBaseHomologyIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.symm_hom]
  rw [← Category.assoc, ← Functor.map_comp]
  rw [h₁]
  rw [Functor.map_comp, Category.assoc, h₂, Category.assoc]

/-- Restriction of scalars does not change the underlying abelian group. -/
def forgetRestrictGlobalIso (M : ModuleCat.{u} (baseRing V)) :
    (forget₂ (ModuleCat.{u} (baseRing V)) AddCommGrpCat.{u}).obj M ≅
      (forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u}).obj ((restrictGlobal c).obj M) :=
  Iso.refl _

/-- The identification `forgetRestrictGlobalIso` is natural. -/
theorem forgetRestrictGlobalIso_hom_naturality {M N : ModuleCat.{u} (baseRing V)} (g : M ⟶ N) :
    (forget₂ (ModuleCat.{u} (baseRing V)) AddCommGrpCat.{u}).map g ≫
        (forgetRestrictGlobalIso c N).hom =
      (forgetRestrictGlobalIso c M).hom ≫
        (forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u}).map ((restrictGlobal c).map g) :=
  rfl

/-- **`H^q(V, A) ≅ H^m(RΓ_S(V, A[-k]))`** for `q + k = m`, as abelian groups: the identification
`cohomologyDerivedSingleIso` with the cohomology of derived global sections in abelian groups,
the comparison `homologyForgetIso` with derived global sections over `Γ(V, 𝒪_V)`, and
`sectionsOverBaseHomologyIso`. -/
def hgroupSectionsOverBaseIso (A : SheafOfModules.{u} (structureSheafRing V)) (k q : ℕ) (m : ℤ)
    (h : (q : ℤ) + (k : ℤ) = m) :
    Hgroup (structureSheafRing V) ⊤ q A ≅
      (forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u}).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) m).obj
          ((sectionsOverBase c).obj
            ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing V))
              (k : ℤ)).obj A))) :=
  (cohomologyDerivedSingleIso V A (k : ℤ) m q (by omega)).symm ≪≫
    homologyForgetIso V m _ ≪≫ forgetRestrictGlobalIso c _ ≪≫
    (forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u}).mapIso
      (sectionsOverBaseHomologyIso c _ m).symm

/-- **The identification carries the map on cohomology of a morphism `A[-k] ⟶ F[0]` of the
derived category to the map it induces on derived sections over the base**, as morphisms. -/
theorem cohomologyMapOfSingleHom_comp_hgroupSectionsOverBaseIso
    (A F : SheafOfModules.{u} (structureSheafRing V)) (k q : ℕ) (m : ℤ)
    (h : (q : ℤ) + (k : ℤ) = m) (h₀ : ((q + k : ℕ) : ℤ) + ((0 : ℕ) : ℤ) = m)
    (φ : (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing V)) (k : ℤ)).obj A ⟶
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing V))
        ((0 : ℕ) : ℤ)).obj F) :
    cohomologyMapOfSingleHom V A F k q φ ≫ (hgroupSectionsOverBaseIso c F 0 (q + k) m h₀).hom =
      (hgroupSectionsOverBaseIso c A k q m h).hom ≫
        (forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u}).map
          ((DerivedCategory.homologyFunctor _ m).map ((sectionsOverBase c).map φ)) := by
  subst h
  have hN := homologyForgetIso_hom_naturality V ((q : ℤ) + (k : ℤ)) φ
  have hS := sectionsOverBaseHomologyIso_hom_naturality c φ ((q : ℤ) + (k : ℤ))
  have hS' : (restrictGlobal c).map
          ((DerivedCategory.homologyFunctor _ ((q : ℤ) + (k : ℤ))).map ((baseSections V).map φ)) ≫
        (sectionsOverBaseHomologyIso c _ ((q : ℤ) + (k : ℤ))).inv =
      (sectionsOverBaseHomologyIso c _ ((q : ℤ) + (k : ℤ))).inv ≫
        (DerivedCategory.homologyFunctor _ ((q : ℤ) + (k : ℤ))).map
          ((sectionsOverBase c).map φ) := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hS, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hS'' := congrArg (forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u}).map hS'
  rw [Functor.map_comp, Functor.map_comp] at hS''
  have hc : (cohomologyDerivedSingleIso V F (0 : ℤ) ((q : ℤ) + (k : ℤ)) (q + k) (by omega)).hom ≫
      (cohomologyDerivedSingleIso V F ((0 : ℕ) : ℤ) ((q : ℤ) + (k : ℤ)) (q + k) (by omega)).inv =
        𝟙 _ := Iso.hom_inv_id _
  simp only [hgroupSectionsOverBaseIso, cohomologyMapOfSingleHom, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc, reassoc_of% hc]
  rw [reassoc_of% hN, reassoc_of% (forgetRestrictGlobalIso_hom_naturality c
    ((DerivedCategory.homologyFunctor _ ((q : ℤ) + (k : ℤ))).map ((baseSections V).map φ))), hS'']

/-- **The identification carries the map on cohomology of a morphism `A[-k] ⟶ F[0]` of the
derived category to the map it induces on derived sections over the base**, on classes. -/
theorem hgroupSectionsOverBaseIso_cohomologyMapOfSingleHom
    (A F : SheafOfModules.{u} (structureSheafRing V)) (k q : ℕ) (m : ℤ)
    (h : (q : ℤ) + (k : ℤ) = m) (h₀ : ((q + k : ℕ) : ℤ) + ((0 : ℕ) : ℤ) = m)
    (φ : (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing V)) (k : ℤ)).obj A ⟶
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing V))
        ((0 : ℕ) : ℤ)).obj F)
    (x : Hgroup (structureSheafRing V) ⊤ q A) :
    (hgroupSectionsOverBaseIso c F 0 (q + k) m h₀).hom (cohomologyMapOfSingleHom V A F k q φ x) =
      ((forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u}).map
        ((DerivedCategory.homologyFunctor _ m).map ((sectionsOverBase c).map φ))).hom
        ((hgroupSectionsOverBaseIso c A k q m h).hom x) :=
  ConcreteCategory.congr_hom (cohomologyMapOfSingleHom_comp_hgroupSectionsOverBaseIso c A F k q m h
    h₀ φ) x

end Stacks.WeilDeRham

end
