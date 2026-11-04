module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsAcyclic
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareTransComposition
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusComparisons
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageComposition
public import StacksFrontier.Algebra.Homology.DerivedCategory.CochainComplexPlusDerivedUnit
public import StacksFrontier.AlgebraicGeometry.DerivedIso.Leray
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusNatIsoGlue
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derived direct images and derived global sections commute with restriction of scalars

Let `ρ : Λ →+* Λ'` be a morphism of commutative rings.  Restriction of scalars `res_ρ` of
sheaves of modules on small étale sites is exact and carries injective sheaves to sheaves which
are acyclic for every direct image and for global sections
(`Stacks.EtaleCohomology.isAcyclicEverywhere_restrictScalars'`).  Hence the derived direct
image and the derived global sections commute with it:

`Rf_*(res_ρ K) ≅ res_ρ (Rf_* K)`,   `RΓ(X, res_ρ K) ≅ res_ρ RΓ(X, K)`

in the bounded below derived categories.  This is the comparison of the cohomology of a sheaf of
`ℤ/ℓⁿ⁺¹ℤ`-modules with the cohomology of the same sheaf viewed as a sheaf of `ℤ_ℓ`-modules used
in [Tag 03V2].

## Main definitions

* `CategoryTheory.Functor.rightDerivedRestrictionIso`: the general comparison
  `RG' ⋙ r_M ≅ r_A ⋙ RG` for exact `r_A`, `r_M` with `G' ⋙ r_M ≅ r_A ⋙ G` and `r_A` carrying
  injectives to `G`-acyclic objects.
* `Stacks.EtaleCohomology.etaleModuleDerivedDirectImageRestrictScalars`.
* `Stacks.EtaleCohomology.etaleModuleDerivedGlobalSectionsRestrictScalars`.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace CategoryTheory.Functor

variable {A' A M' M : Type*} [Category* A'] [Category* A] [Category* M'] [Category* M]
  [Abelian A'] [Abelian A] [Abelian M'] [Abelian M]
  [HasDerivedCategory A'] [HasDerivedCategory A] [HasDerivedCategory M'] [HasDerivedCategory M]
  [EnoughInjectives A'] [EnoughInjectives A] [EnoughInjectives M']
  (G' : A' ⥤ M') (G : A ⥤ M) (rA : A' ⥤ A) (rM : M' ⥤ M)
  [G'.Additive] [G.Additive] [rA.Additive] [rM.Additive]
  [PreservesFiniteLimits rA] [PreservesFiniteColimits rA]
  [PreservesFiniteLimits rM] [PreservesFiniteColimits rM]

/-- **Right derived functors commute with exact functors carrying injectives to acyclics.**
For exact `r_A : A' ⥤ A`, `r_M : M' ⥤ M` and an identification `G' ⋙ r_M ≅ r_A ⋙ G`, if `r_A`
carries injectives to objects right acyclic for `G`, then `RG' ⋙ r_M ≅ r_A ⋙ RG`: both are the
right derived functor of `G' ⋙ r_M ≅ r_A ⋙ G`. -/
def rightDerivedRestrictionIso (e : G' ⋙ rM ≅ rA ⋙ G)
    (hac : ∀ I : A', Injective I → G.rightAcyclic (rA.obj I)) :
    G'.rightDerivedFunctorPlus ⋙ rM.mapDerivedCategoryPlus ≅
      rA.mapDerivedCategoryPlus ⋙ G.rightDerivedFunctorPlus :=
  (Functor.isoWhiskerLeft G'.rightDerivedFunctorPlus
      (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus rM)).symm ≪≫
    (Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic G' rM
      (fun _ _ => Functor.rightAcyclic_of_exact _ _)).symm ≪≫
    Functor.rightDerivedFunctorPlusNatIso e ≪≫
    Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic rA G hac ≪≫
    Functor.isoWhiskerRight (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus rA)
      G.rightDerivedFunctorPlus

/-- **The comparison `RG' ⋙ r_M ≅ r_A ⋙ RG` after the unit of `RG'`**: at a bounded below
complex `K`, applying `r_M` to the unit of `RG'` and then the comparison is the identification
`r_M(G'(K)) ≅ G(r_A(K))` followed by the unit of `RG` at `r_A(K)`. -/
theorem map_unit_comp_rightDerivedRestrictionIso_hom_app (e : G' ⋙ rM ≅ rA ⋙ G)
    (hac : ∀ I : A', Injective I → G.rightAcyclic (rA.obj I)) (K : HomotopyCategory.Plus A') :
    rM.mapDerivedCategoryPlus.map (G'.rightDerivedFunctorPlusUnit.app K) ≫
        (rightDerivedRestrictionIso G' G rA rM e hac).hom.app (DerivedCategory.Plus.Qh.obj K) =
      rM.mapDerivedCategoryPlusFactorsh.hom.app (G'.mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map
          ((mapHomotopyCategoryPlusCompIso (Iso.refl (G' ⋙ rM))).hom.app K ≫
            (mapHomotopyCategoryPlusNatIso e).hom.app K ≫
            (mapHomotopyCategoryPlusCompIso (Iso.refl (rA ⋙ G))).inv.app K) ≫
        G.rightDerivedFunctorPlusUnit.app (rA.mapHomotopyCategoryPlus.obj K) ≫
        G.rightDerivedFunctorPlus.map (rA.mapDerivedCategoryPlusFactorsh.inv.app K) := by
  have hN : (G' ⋙ rM).rightDerivedFunctorPlusUnit.app K ≫
      (rightDerivedFunctorPlusNatIso e).hom.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusNatIso e).hom.app K) ≫
        (rA ⋙ G).rightDerivedFunctorPlusUnit.app K :=
    rightDerivedNatTrans_app _ _ _ _ (HomotopyCategory.Plus.quasiIso A') _ K
  have hMn : rM.rightDerivedFunctorPlus.map (G'.rightDerivedFunctorPlusUnit.app K) ≫
      (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus rM).hom.app
        (G'.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj K)) =
      (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus rM).hom.app
        (DerivedCategory.Plus.Qh.obj (G'.mapHomotopyCategoryPlus.obj K)) ≫
      rM.mapDerivedCategoryPlus.map (G'.rightDerivedFunctorPlusUnit.app K) :=
    (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus rM).hom.naturality _
  have key : rM.mapDerivedCategoryPlus.map (G'.rightDerivedFunctorPlusUnit.app K) =
      rM.mapDerivedCategoryPlusFactorsh.hom.app (G'.mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map
          ((mapHomotopyCategoryPlusCompIso (Iso.refl (G' ⋙ rM))).hom.app K) ≫
        (G' ⋙ rM).rightDerivedFunctorPlusUnit.app K ≫
        (rightDerivedFunctorPlusComp G' rM).app (DerivedCategory.Plus.Qh.obj K) ≫
        (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus rM).hom.app
          (G'.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj K)) := by
    rw [reassoc_of% (rightDerivedFunctorPlusComp_fac_app G' rM K), hMn,
      reassoc_of% (unit_comp_rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom_app rM
        (G'.mapHomotopyCategoryPlus.obj K))]
    have hc : DerivedCategory.Plus.Qh.map
        ((mapHomotopyCategoryPlusCompIso (Iso.refl (G' ⋙ rM))).hom.app K) ≫
        DerivedCategory.Plus.Qh.map
          ((mapHomotopyCategoryPlusCompIso (Iso.refl (G' ⋙ rM))).inv.app K) = 𝟙 _ := by
      rw [← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
    rw [reassoc_of% hc, Iso.hom_inv_id_app_assoc]
  rw [key]
  simp only [rightDerivedRestrictionIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc]
  rw [Iso.hom_inv_id_app_assoc,
    show (rightDerivedFunctorPlusComp G' rM).app (DerivedCategory.Plus.Qh.obj K) =
      (Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic G' rM
        (fun _ _ => Functor.rightAcyclic_of_exact _ _)).hom.app _ from rfl,
    Iso.hom_inv_id_app_assoc,
    reassoc_of% hN,
    show (Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic rA G hac).hom.app
      (DerivedCategory.Plus.Qh.obj K) = (rightDerivedFunctorPlusComp rA G).app _ from rfl,
    reassoc_of% (rightDerivedFunctorPlusComp_fac_app rA G K), ← Functor.map_comp,
    unit_comp_rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom_app rA K]
  simp only [Functor.map_comp, Category.assoc]

section CompIso

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [EnoughInjectives C] [EnoughInjectives D]
  (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) [F.Additive] [G.Additive] [H.Additive]
  [F.PreservesInjectiveObjects]

/-- **The composition comparison `RH ≅ RF ⋙ RG` attached to `F ⋙ G ≅ H`, after the unit of
`RH`**: it is the identification `H(K) ≅ G(F(K))` followed by the units of `RG` and `RF`. -/
theorem unit_comp_rightDerivedFunctorPlusCompIsoOfIso_hom_app (e : F ⋙ G ≅ H)
    (K : HomotopyCategory.Plus C) :
    H.rightDerivedFunctorPlusUnit.app K ≫
        (Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso F G H e).hom.app
          (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusCompIso e).inv.app K) ≫
        G.rightDerivedFunctorPlusUnit.app (F.mapHomotopyCategoryPlus.obj K) ≫
        G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K) := by
  have h1 : H.rightDerivedFunctorPlusUnit.app K ≫
      (Stacks.EtaleCohomology.rightDerivedFunctorPlusIsoOfCompIso F G H e).inv.app
        (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map
        ((Stacks.EtaleCohomology.mapHomotopyCategoryPlusIsoOfCompIso F G H e).inv.app K) ≫
        (F ⋙ G).rightDerivedFunctorPlusUnit.app K :=
    rightDerivedNatTrans_app _ _ _ _ (HomotopyCategory.Plus.quasiIso C) _ K
  simp only [Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app]
  rw [reassoc_of% h1]
  show _ ≫ _ ≫ (rightDerivedFunctorPlusComp F G).app _ = _
  rw [rightDerivedFunctorPlusComp_fac_app F G K, ← Functor.map_comp_assoc]
  congr 2
  simp [Stacks.EtaleCohomology.mapHomotopyCategoryPlusIsoOfCompIso]

end CompIso

section QIso

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- **The localization `Q` commutes with an exact functor**: `Q ⋙ F⁺ ≅ F ⋙ Q` on bounded below
cochain complexes. -/
def mapDerivedCategoryPlusQIso :
    DerivedCategory.Plus.Q ⋙ F.mapDerivedCategoryPlus ≅
      F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q :=
  Functor.isoWhiskerRight (DerivedCategory.Plus.quotientCompQhIso A).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ F.mapDerivedCategoryPlusFactorsh ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Stacks.AlgebraicGeometry.Tag01XLDerivedIso.mapHomotopyCategoryPlusFactors F) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.Plus.quotientCompQhIso B)

end QIso

section Identities

variable {A B E : Type*} [Category* A] [Category* B] [Category* E] [Preadditive A] [Preadditive B]
  [Preadditive E] (F : A ⥤ B) (G : B ⥤ E) [F.Additive] [G.Additive]

/-- The coherence isomorphism for the identity comparison of a composite is the identity. -/
theorem mapHomotopyCategoryPlusCompIso_refl_hom_app (K : HomotopyCategory.Plus A) :
    (mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).hom.app K = 𝟙 _ :=
  rfl

/-- The bounded below form of `mapHomotopyCategoryFactors` is the identity. -/
theorem mapHomotopyCategoryPlusFactors_inv_app (K : CochainComplex.Plus A) :
    (Stacks.AlgebraicGeometry.Tag01XLDerivedIso.mapHomotopyCategoryPlusFactors F).inv.app K =
      𝟙 _ := by
  apply (HomotopyCategory.Plus.ι _).map_injective
  exact ((HomotopyCategory.Plus.ι _).map_preimage _).trans rfl

end Identities

end CategoryTheory.Functor

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable {Λ Λ' : Type} [Ring Λ] [Ring Λ'] (ρ : Λ →+* Λ')

/-- Restriction of scalars of modules is exact. -/
@[sga "4 IV 11.1.6" "special case"]
instance moduleCat_restrictScalars_preservesFiniteLimits :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{u + 1} ρ) :=
  have := (Stacks.NoncommChangeOfRings.extendRestrictScalarsAdj.{u + 1} ρ).isRightAdjoint
  inferInstance

/-- Restriction of scalars of modules preserves finite colimits. -/
@[sga "4 IV 11.1.6" "special case"]
instance moduleCat_restrictScalars_preservesFiniteColimits :
    PreservesFiniteColimits (ModuleCat.restrictScalars.{u + 1} ρ) :=
  have := (ModuleCat.restrictCoextendScalarsAdj.{u + 1} ρ).isLeftAdjoint
  inferInstance

/-- **`Rf_* ∘ res_ρ ≅ res_ρ ∘ Rf_*`** for sheaves of modules on small étale sites. -/
def etaleModuleDerivedDirectImageRestrictScalars {X Y : Scheme.{u}} (f : X ⟶ Y) :
    etaleModuleDerivedDirectImage.{u, 0} Λ' f ⋙
        (etaleModuleRestrictScalars ρ Y).mapDerivedCategoryPlus ≅
      (etaleModuleRestrictScalars ρ X).mapDerivedCategoryPlus ⋙
        etaleModuleDerivedDirectImage.{u, 0} Λ f :=
  Functor.rightDerivedRestrictionIso _ _ _ _ (etaleModuleDirectImageRestrictScalars ρ f)
    (fun I _ => rightAcyclic_directImage_of_isAcyclicEverywhere f _
      (isAcyclicEverywhere_restrictScalars' ρ I))

/-- A sheaf acyclic everywhere is acyclic for global sections. -/
theorem rightAcyclic_globalSections_of_isAcyclicEverywhere {X : Scheme.{u}}
    (B : EtaleModules.{u, 0} Λ X) (hB : IsAcyclicEverywhere B) :
    (etaleModuleGlobalSections.{u, 0} Λ X).rightAcyclic B := by
  have := hB (⊤_ X.Etale)
  rw [Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived] at this ⊢
  intro p hp
  exact (this p hp).of_iso ((ModuleSheafCohomology.rightDerivedIso
    (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
      terminalIsTerminal) p).app B)

/-- **`RΓ(X, -) ∘ res_ρ ≅ res_ρ ∘ RΓ(X, -)`** for sheaves of modules on the small étale site. -/
def etaleModuleDerivedGlobalSectionsRestrictScalars (X : Scheme.{u}) :
    etaleModuleDerivedGlobalSections.{u, 0} Λ' X ⋙
        (ModuleCat.restrictScalars.{u + 1} ρ).mapDerivedCategoryPlus ≅
      (etaleModuleRestrictScalars ρ X).mapDerivedCategoryPlus ⋙
        etaleModuleDerivedGlobalSections.{u, 0} Λ X :=
  Functor.rightDerivedRestrictionIso _ _ _ _ (etaleModuleGlobalSectionsRestrictScalars ρ X)
    (fun I _ => rightAcyclic_globalSections_of_isAcyclicEverywhere _
      (isAcyclicEverywhere_restrictScalars' ρ I))

end Stacks.EtaleCohomology

end
