module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseSheafPullback

/-!
# The inverse image of a lisse sheaf, naturally in the module

For a morphism `f : Y ⟶ X` of connected schemes and a geometric point `ȳ` of `Y`, the isomorphism
`f⁻¹ ℱ_P ≅ ℱ_{P|_{π₁(Y, ȳ)}}` of
`Stacks.EtaleCohomology.nonempty_etaleModuleInverseImage_lisseEtaleSheaf_iso` is built from one
natural isomorphism of functors (Tag 0DV6,
`AlgebraicGeometry.nonempty_finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite_pullbackIso`)
and the unit and counit of the equivalences of Tag 0DV5 (3). This file writes it down for a given
such natural isomorphism and shows that it is natural in `P`.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleInverseImageLisseEtaleSheafIso`.

## Main results

* `Stacks.EtaleCohomology.etaleModuleInverseImageLisseEtaleSheafIso_hom_naturality`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.ConstantSheaf
  Stacks.GroupCohomology

universe u

attribute [local instance] discreteForget₂AddCommGrpCat
  Stacks.EtaleCohomology.moduleCat_hasLimitsOfSize

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} [ConnectedSpace X.1] [ConnectedSpace Y.1]
  (f : Y ⟶ X) (y : GeometricPoint Y.1) (Λ : Type) [CommRing Λ] [Finite Λ]
  (α : (finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X (y.map f.hom) Λ).functor ⋙
      finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap f.hom y) ≅
    etaleSiteFiniteTypeLocallyConstantModuleSheafPullback B f Λ ⋙
      (finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B Y y Λ).functor)

/-- Pasting a commutative square in `𝒞` with the image under `ι : 𝒟 ⥤ 𝒞` of a commutative square
in `𝒟`: from `a ≫ e' = e ≫ ι.map p` and `p ≫ x' = x ≫ r`,
`a ≫ e' ≫ ι.map x' = (e ≫ ι.map x) ≫ ι.map r`. -/
theorem iso_comp_map_chase {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (ι : 𝒟 ⥤ 𝒞) {A A' : 𝒞}
    {E E' F F' : 𝒟} (a : A ⟶ A') (e : A ⟶ ι.obj E) (e' : A' ⟶ ι.obj E') (p : E ⟶ E')
    (x : E ⟶ F) (x' : E' ⟶ F') (r : F ⟶ F') (h₁ : a ≫ e' = e ≫ ι.map p)
    (h₂ : p ≫ x' = x ≫ r) : a ≫ e' ≫ ι.map x' = (e ≫ ι.map x) ≫ ι.map r := by
  rw [← Category.assoc, h₁, Category.assoc, ← ι.map_comp, h₂, ι.map_comp, Category.assoc]

/-- **`f⁻¹ ℱ_P ≅ ℱ_{P|_{π₁(Y, ȳ)}}`** (Tag 0DV6 for lisse sheaves), for a given natural
isomorphism `α` of Tag 0DV6 on the finite type locally constant sheaves of `Λ`-modules. -/
def etaleModuleInverseImageLisseEtaleSheafIso
    (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map f.hom))) :
    (etaleModuleInverseImage.{u, 0} Λ f.hom).obj ((lisseEtaleSheaf B X (y.map f.hom) Λ).obj P) ≅
      (lisseEtaleSheaf B Y y Λ).obj
        ((finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap f.hom y)).obj P) :=
  (etaleSiteSheafPullbackModuleIso B f Λ).symm.app _ ≪≫ (ObjectProperty.ι _).mapIso
    ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B Y y Λ).unitIso.app
        ((etaleSiteFiniteTypeLocallyConstantModuleSheafPullback B f Λ).obj
          ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X (y.map f.hom)
            Λ).inverse.obj P)) ≪≫
      (finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B Y y Λ).inverse.mapIso
        ((α.app ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X (y.map f.hom)
            Λ).inverse.obj P)).symm ≪≫
          (finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap f.hom y)).mapIso
            ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X (y.map f.hom)
              Λ).counitIso.app P)))

variable {Λ} in
/-- The first square of the naturality of
`Stacks.EtaleCohomology.etaleModuleInverseImageLisseEtaleSheafIso`: `f⁻¹` and the inverse image of
Mathlib's small étale site agree naturally. -/
theorem etaleModuleInverseImageLisseEtaleSheafIso_naturality_aux₁
    {P P' : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map f.hom))}
    (s : P ⟶ P') :
    (etaleModuleInverseImage.{u, 0} Λ f.hom).map ((lisseEtaleSheaf B X (y.map f.hom) Λ).map s) ≫
        (etaleSiteSheafPullbackModuleIso B f Λ).inv.app
          ((lisseEtaleSheaf B X (y.map f.hom) Λ).obj P') =
      (etaleSiteSheafPullbackModuleIso B f Λ).inv.app
          ((lisseEtaleSheaf B X (y.map f.hom) Λ).obj P) ≫
        (ObjectProperty.ι (fun F : Sheaf Y.1.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦
          IsFiniteTypeLocallyConstant Λ Y.1.smallEtaleTopology F)).map
          ((etaleSiteFiniteTypeLocallyConstantModuleSheafPullback B f Λ).map
            ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X (y.map f.hom)
              Λ).inverse.map s)) :=
  (etaleSiteSheafPullbackModuleIso B f Λ).inv.naturality _

variable {Λ} in
/-- The second square of the naturality of
`Stacks.EtaleCohomology.etaleModuleInverseImageLisseEtaleSheafIso`, on the locally constant
sheaves of `Y`. -/
theorem etaleModuleInverseImageLisseEtaleSheafIso_naturality_aux₂
    {P P' : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map f.hom))}
    (s : P ⟶ P') :
    (etaleSiteFiniteTypeLocallyConstantModuleSheafPullback B f Λ).map
        ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X (y.map f.hom)
          Λ).inverse.map s) ≫
      ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B Y y Λ).unitIso.hom.app
          ((etaleSiteFiniteTypeLocallyConstantModuleSheafPullback B f Λ).obj
            ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X (y.map f.hom)
              Λ).inverse.obj P')) ≫
        (finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B Y y Λ).inverse.map
          (α.inv.app ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X
              (y.map f.hom) Λ).inverse.obj P') ≫
            (finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap f.hom y)).map
              ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X (y.map f.hom)
                Λ).counitIso.hom.app P'))) =
      ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B Y y Λ).unitIso.hom.app
          ((etaleSiteFiniteTypeLocallyConstantModuleSheafPullback B f Λ).obj
            ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X (y.map f.hom)
              Λ).inverse.obj P)) ≫
        (finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B Y y Λ).inverse.map
          (α.inv.app ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X
              (y.map f.hom) Λ).inverse.obj P) ≫
            (finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap f.hom y)).map
              ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X (y.map f.hom)
                Λ).counitIso.hom.app P))) ≫
        (finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B Y y Λ).inverse.map
          ((finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap f.hom y)).map s) := by
  have F4 :=
    (finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B Y y Λ).unitIso.hom.naturality
      ((etaleSiteFiniteTypeLocallyConstantModuleSheafPullback B f Λ).map
        ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X (y.map f.hom)
          Λ).inverse.map s))
  have F5 := α.inv.naturality
    ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X (y.map f.hom) Λ).inverse.map s)
  have F6 := (finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X (y.map f.hom)
    Λ).counitIso.hom.naturality s
  simp only [Functor.id_map, Functor.comp_map] at F4 F5 F6
  rw [reassoc_of% F4, Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
    reassoc_of% F5, ← Functor.map_comp, F6]
  simp only [Functor.map_comp, Category.assoc]

variable {Λ} in
/-- The naturality of `Stacks.EtaleCohomology.etaleModuleInverseImageLisseEtaleSheafIso` in `P`,
with the isomorphism unfolded. -/
theorem etaleModuleInverseImageLisseEtaleSheafIso_naturality_aux
    {P P' : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map f.hom))}
    (s : P ⟶ P') :
    (etaleModuleInverseImage.{u, 0} Λ f.hom).map ((lisseEtaleSheaf B X (y.map f.hom) Λ).map s) ≫
        (etaleSiteSheafPullbackModuleIso B f Λ).inv.app
          ((lisseEtaleSheaf B X (y.map f.hom) Λ).obj P') ≫
        (ObjectProperty.ι (fun F : Sheaf Y.1.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦
          IsFiniteTypeLocallyConstant Λ Y.1.smallEtaleTopology F)).map
          ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B Y y Λ).unitIso.hom.app
              ((etaleSiteFiniteTypeLocallyConstantModuleSheafPullback B f Λ).obj
                ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X (y.map f.hom)
                  Λ).inverse.obj P')) ≫
            (finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B Y y Λ).inverse.map
              (α.inv.app ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X
                  (y.map f.hom) Λ).inverse.obj P') ≫
                (finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap f.hom y)).map
                  ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X (y.map f.hom)
                    Λ).counitIso.hom.app P'))) =
      ((etaleSiteSheafPullbackModuleIso B f Λ).inv.app
          ((lisseEtaleSheaf B X (y.map f.hom) Λ).obj P) ≫
        (ObjectProperty.ι (fun F : Sheaf Y.1.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦
          IsFiniteTypeLocallyConstant Λ Y.1.smallEtaleTopology F)).map
          ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B Y y Λ).unitIso.hom.app
              ((etaleSiteFiniteTypeLocallyConstantModuleSheafPullback B f Λ).obj
                ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X (y.map f.hom)
                  Λ).inverse.obj P)) ≫
            (finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B Y y Λ).inverse.map
              (α.inv.app ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X
                  (y.map f.hom) Λ).inverse.obj P) ≫
                (finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap f.hom y)).map
                  ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X (y.map f.hom)
                    Λ).counitIso.hom.app P)))) ≫
        (ObjectProperty.ι (fun F : Sheaf Y.1.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦
          IsFiniteTypeLocallyConstant Λ Y.1.smallEtaleTopology F)).map
          ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B Y y Λ).inverse.map
            ((finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap f.hom y)).map s)) :=
  iso_comp_map_chase
    (ObjectProperty.ι (fun F : Sheaf Y.1.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦
      IsFiniteTypeLocallyConstant Λ Y.1.smallEtaleTopology F)) _ _ _ _ _ _ _
    (etaleModuleInverseImageLisseEtaleSheafIso_naturality_aux₁ B f y s)
    (etaleModuleInverseImageLisseEtaleSheafIso_naturality_aux₂ B f y α s)

/-- **`f⁻¹ ℱ_P ≅ ℱ_{P|_{π₁(Y, ȳ)}}` is natural in `P`.** -/
theorem etaleModuleInverseImageLisseEtaleSheafIso_hom_naturality
    {P P' : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map f.hom))}
    (s : P ⟶ P') :
    (etaleModuleInverseImage.{u, 0} Λ f.hom).map ((lisseEtaleSheaf B X (y.map f.hom) Λ).map s) ≫
        (etaleModuleInverseImageLisseEtaleSheafIso B f y Λ α P').hom =
      (etaleModuleInverseImageLisseEtaleSheafIso B f y Λ α P).hom ≫
        (lisseEtaleSheaf B Y y Λ).map
          ((finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap f.hom y)).map s) :=
  etaleModuleInverseImageLisseEtaleSheafIso_naturality_aux B f y α s

end Stacks.EtaleCohomology

end
