module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RestrictionSectionsCorepresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition

/-!
# Restriction of étale cohomology on injective resolutions

Let `h : Y ⟶ X` be a morphism of schemes, `T` and `T'` terminal objects of `X.Etale` and
`Y.Etale`, and `k : T' ⟶ T ×_X Y`. For abelian sheaves `P` on `X` and `Q` on `Y` and a map
`g : h⁻¹P ⟶ Q`, the map `e ↦ g ∘ b ∘ h⁻¹(e)` on `Ext`-groups out of `ℤ` — restriction on étale
cohomology (`Stacks.EtaleCohomology.etaleCohomologyRestrictionMap`) followed by `g` — is computed,
after the identifications of `Ext` out of `ℤ` with the right derived functors of sections over
`T` and `T'`, by restriction of sections on injective resolutions: the unit
`I ⟶ h_*h⁻¹I` read over `T`, restriction along `k`, then any comparison of `h⁻¹I` with a
resolution of `Q` over `g`.

## Main results

* `Stacks.EtaleCohomology.extRestrictionMap_conj`: that identification, in every degree.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open ModuleSheafCohomology Stacks.Cohomology.ModuleComparison Stacks.Cohomology.ExtComparison

universe u

namespace Stacks.EtaleCohomology

variable {X Y : Scheme.{u}} (h : Y ⟶ X) {T : X.Etale} (hT : IsTerminal T) {T' : Y.Etale}
  (hT' : IsTerminal T') (k : T' ⟶ (smallEtaleBaseChange h).obj T)
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
  {P : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
  {Q : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
  (g : (etaleAbelianInverseImage.{u, 0} h).obj P ⟶ Q)

/-- Restriction on `Ext` out of `ℤ` followed by a map `g : h⁻¹P ⟶ Q`. -/
def extRestrictionMap (n : ℕ) :
    (extFunctorObj (zSheaf X) n).obj P ⟶ (extFunctorObj (zSheaf Y) n).obj Q :=
  (extMapComp (etaleAbelianInverseImage.{u, 0} h) (zComparison h) n).app P ≫
    (extFunctorObj (zSheaf Y) n).map g

include hT hT' in
/-- **Restriction followed by `g`, on injective resolutions, in positive degree.** -/
theorem extRestrictionMap_succ_conj (n : ℕ)
    (χ₀ : ((etaleAbelianInverseImage.{u, 0} h).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution P).cocomplex ⟶
      (injectiveResolution ((etaleAbelianInverseImage.{u, 0} h).obj P)).cocomplex)
    (hχ₀ : (etaleAbelianInverseImage.{u, 0} h).map ((injectiveResolution P).ι.f 0) ≫ χ₀.f 0 =
      (injectiveResolution ((etaleAbelianInverseImage.{u, 0} h).obj P)).ι.f 0)
    (g' : (injectiveResolution ((etaleAbelianInverseImage.{u, 0} h).obj P)).cocomplex ⟶
      (injectiveResolution Q).cocomplex)
    (hg' : (injectiveResolution ((etaleAbelianInverseImage.{u, 0} h).obj P)).ι ≫ g' =
      (CochainComplex.single₀ _).map g ≫ (injectiveResolution Q).ι) :
    (extFunctorObjIsoRightDerived (sectionsOver T) (zSheaf X) (sectionsCorepresentation hT)
        (n + 1)).inv.app P ≫ extRestrictionMap h g (n + 1) ≫
      (extFunctorObjIsoRightDerived (sectionsOver T') (zSheaf Y) (sectionsCorepresentation hT')
        (n + 1)).hom.app Q =
      ((injectiveResolution P).isoRightDerivedObj (sectionsOver T) (n + 1)).hom ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex (sectionsRestriction h k) (ComplexShape.up ℕ)).app
              (injectiveResolution P).cocomplex ≫
            ((sectionsOver T').mapHomologicalComplex (ComplexShape.up ℕ)).map (χ₀ ≫ g')) (n + 1) ≫
        ((injectiveResolution Q).isoRightDerivedObj (sectionsOver T') (n + 1)).inv := by
  have hnat := (extFunctorObjIsoRightDerived (sectionsOver T') (zSheaf Y)
    (sectionsCorepresentation hT') (n + 1)).hom.naturality g
  have hrd := Functor.rightDerived_map_eq (sectionsOver T') (n + 1) g g' hg'
  rw [hrd] at hnat
  have key := extMapComp_conj_succ (etaleAbelianInverseImage.{u, 0} h) (sectionsOver T')
    (zSheaf Y) (sectionsCorepresentation hT') (sectionsOver T) (zSheaf X)
    (sectionsCorepresentation hT) (zComparison h) P n χ₀ hχ₀
  rw [derivedSectionsMap_eq_sectionsRestriction h hT hT' k] at key
  have huz : HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex (sectionsRestriction h k) (ComplexShape.up ℕ)).app
            (injectiveResolution P).cocomplex ≫
          ((sectionsOver T').mapHomologicalComplex (ComplexShape.up ℕ)).map χ₀) (n + 1) ≫
        ((sectionsOver T').mapHomologicalComplex _ ⋙
          HomologicalComplex.homologyFunctor _ _ (n + 1)).map g' =
      HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex (sectionsRestriction h k) (ComplexShape.up ℕ)).app
            (injectiveResolution P).cocomplex ≫
          ((sectionsOver T').mapHomologicalComplex (ComplexShape.up ℕ)).map (χ₀ ≫ g')) (n + 1) := by
    rw [Functor.map_comp, ← Category.assoc]
    exact (HomologicalComplex.homologyMap_comp _ _ _).symm
  exact conj_succ_rearrange key hnat (Iso.inv_hom_id _) huz

end Stacks.EtaleCohomology
