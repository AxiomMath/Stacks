module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.RefinementKillsClosure
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.ProperModelLerayTermComp
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMate
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryCompIsoOnHomotopyCategory
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.DegreewiseForgetExcisionSquare
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMate

/-!
# Killing by a refinement of proper models is stable under further refinement

For a refinement `π : Y' ⟶ Y` of proper models of `η = Spec (Frac B)` and `G = R^q j_* F` on `Y`,
`AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.Kills` says that `π⁻¹ ι` followed
by the degree `q` base change map `π⁻¹ R^q j_* F ⟶ R^q j'_* F` of the square `𝟙 ≫ j = j' ≫ π`
vanishes. This file proves that if `π` kills `ι`, so does every composite `Y'' ⟶ Y' ⟶ Y`.

## Main results

* `comp_etaleAbelianInverseImageRightDerivedDirectImageBaseChange_eq_zero_iff` (in
  `Stacks.EtaleCohomology`): a morphism is killed by the degree `q` base change map iff it is
  killed by its derived part.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.killsStableUnderRefinement`: killing is stable under
  further refinement.

## References

* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
* [Stacks Project, Tag 0EZS](https://stacks.math.columbia.edu/tag/0EZS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section BaseChange

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (h : g' ≫ f = f' ≫ g)

/-- **A morphism is killed by the degree `q` base change map iff it is killed by its derived
part.** The base change map `g⁻¹ R^q f_* F ⟶ R^q f'_* g'⁻¹ F` ends in isomorphisms; dropping
them, a morphism `c` into `g⁻¹ R^q f_* F` composes to zero with it exactly when it composes to
zero with `g⁻¹` of `R^q f_* F ≅ H^q(Rf_* F)`, the comparison `g⁻¹ H^q ≅ H^q g⁻¹` and `H^q` of the
derived base change map. -/
theorem comp_etaleAbelianInverseImageRightDerivedDirectImageBaseChange_eq_zero_iff
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    {W : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (c : W ⟶ (etaleAbelianInverseImage.{u, 0} g).obj
      (((etaleAbelianDirectImage.{u, 0} f).rightDerived q).obj F)) :
    c ≫ etaleAbelianInverseImageRightDerivedDirectImageBaseChange f g g' f' h F q = 0 ↔
      c ≫ (etaleAbelianInverseImage.{u, 0} g).map
          (etaleAbelianRightDerivedDirectImageIsoHomology.{0, u} f q F).hom ≫
        ((etaleAbelianInverseImage.{u, 0} g).mapDerivedCategoryHomologyIso q).inv.app
          ((etaleAbelianDerivedDirectImage.{u, 0} f).obj
            ((DerivedCategory.singleFunctor
              (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)) ≫
        (DerivedCategory.homologyFunctor
            (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) q).map
          ((etaleAbelianDerivedBaseChange.{u, 0} f g g' f' h).app
            ((DerivedCategory.singleFunctor
              (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)) = 0 := by
  have e : c ≫ etaleAbelianInverseImageRightDerivedDirectImageBaseChange f g g' f' h F q =
      (c ≫ (etaleAbelianInverseImage.{u, 0} g).map
          (etaleAbelianRightDerivedDirectImageIsoHomology.{0, u} f q F).hom ≫
        ((etaleAbelianInverseImage.{u, 0} g).mapDerivedCategoryHomologyIso q).inv.app
          ((etaleAbelianDerivedDirectImage.{u, 0} f).obj
            ((DerivedCategory.singleFunctor
              (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)) ≫
        (DerivedCategory.homologyFunctor
            (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) q).map
          ((etaleAbelianDerivedBaseChange.{u, 0} f g g' f' h).app
            ((DerivedCategory.singleFunctor
              (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F))) ≫
        ((DerivedCategory.homologyFunctor
            (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) q).map
          ((etaleAbelianDerivedDirectImage.{u, 0} f').map
            (((etaleAbelianInverseImage.{u, 0} g').mapDerivedCategorySingleFunctor 0).app F).hom) ≫
          (etaleAbelianRightDerivedDirectImageIsoHomology.{0, u} f' q _).inv) := by
    simp only [etaleAbelianInverseImageRightDerivedDirectImageBaseChange,
      etaleAbelianSheafDerivedBaseChange, Functor.mapIso_hom, Iso.app_inv, Category.assoc]
  rw [e, Preadditive.IsIso.comp_right_eq_zero]

end BaseChange

end Stacks.EtaleCohomology

namespace AlgebraicGeometry.Scheme.ZariskiRiemann

open Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable {B : Type u} [CommRing B] [IsDomain B]

/-- In preadditive categories, with `G` preserving zero morphisms: if
`Φ.map ι ≫ Φ.map ρ ≫ y ≫ z = 0`, `hinv ≫ c = ε.app x₂ ≫ G.map y ≫ uinv` and
`uinv ≫ w = G.map z ≫ vinv` for a natural transformation `ε : A ⟶ Φ ⋙ G`, then
`A.map ι ≫ A.map ρ ≫ hinv ≫ c ≫ w ≫ r₁ ≫ r₂ = 0`. -/
private theorem kills_chase {C C' C'' : Type*} [Category* C] [Category* C'] [Preadditive C']
    [Category* C''] [Preadditive C''] (A : C ⥤ C'') (Φ : C ⥤ C') (G : C' ⥤ C'')
    [G.PreservesZeroMorphisms] (ε : A ⟶ Φ ⋙ G)
    {x₀ x₁ x₂ : C} (ι : x₀ ⟶ x₁) (ρ : x₁ ⟶ x₂)
    {p₂ p₃ : C'} (y : Φ.obj x₂ ⟶ p₂) (z : p₂ ⟶ p₃) (hk : Φ.map ι ≫ Φ.map ρ ≫ y ≫ z = 0)
    {o₂ o₃ o₄ o₅ o₆ : C''} (hinv : A.obj x₂ ⟶ o₂) (c : o₂ ⟶ o₃) (uinv : G.obj p₂ ⟶ o₃)
    (hcoh : hinv ≫ c = ε.app x₂ ≫ G.map y ≫ uinv)
    (w : o₃ ⟶ o₄) (vinv : G.obj p₃ ⟶ o₄) (hw : uinv ≫ w = G.map z ≫ vinv)
    (r₁ : o₄ ⟶ o₅) (r₂ : o₅ ⟶ o₆) :
    A.map ι ≫ A.map ρ ≫ hinv ≫ c ≫ w ≫ r₁ ≫ r₂ = 0 := by
  calc A.map ι ≫ A.map ρ ≫ hinv ≫ c ≫ w ≫ r₁ ≫ r₂
      = (A.map (ι ≫ ρ) ≫ ε.app x₂) ≫ G.map y ≫ G.map z ≫ vinv ≫ r₁ ≫ r₂ := by
        simp only [Functor.map_comp, Category.assoc]
        rw [reassoc_of% hcoh, reassoc_of% hw]
    _ = ε.app x₀ ≫ G.map (Φ.map ι ≫ Φ.map ρ ≫ y ≫ z) ≫ vinv ≫ r₁ ≫ r₂ := by
        rw [ε.naturality]
        simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
    _ = 0 := by rw [hk, Functor.map_zero, zero_comp, comp_zero]

/-- **Killing is stable under further refinement.** If a refinement `π : Y' ⟶ Y` of proper models
kills `ι : K ⟶ R^q j_* F`, so does every composite `Y'' ⟶ Y' ⟶ Y`. -/
theorem killsStableUnderRefinement : KillsStableUnderRefinement B := by
  intro M'' M' M ψ φ F q K ι hφ
  have sq₁ : 𝟙 _ ≫ M.j = M'.j ≫ φ.π := by rw [Category.id_comp, φ.fac]
  have sq₂ : 𝟙 _ ≫ M'.j = M''.j ≫ ψ.π := by rw [Category.id_comp, ψ.fac]
  have hyp : 𝟙 _ ≫ M.j = M''.j ≫ (ψ.comp φ).π := by rw [Category.id_comp, (ψ.comp φ).fac]
  rw [ProperModel.Refinement.Kills,
    comp_etaleAbelianInverseImageRightDerivedDirectImageBaseChange_eq_zero_iff] at hφ ⊢
  rw [etaleAbelianDerivedBaseChange_comp_app.{u, 0} φ.π M.j M'.j (𝟙 _) ψ.π M''.j (𝟙 _) sq₁ sq₂
    (ψ.comp φ).π rfl (𝟙 _) (Category.comp_id _).symm hyp,
    Functor.map_comp, Functor.map_comp, Functor.map_comp]
  have hcoh := etaleAbelianDerivedInverseImageCompIso'_homology.{u, 0}
    ψ.π φ.π (ψ.comp φ).π rfl q
    ((etaleAbelianDerivedDirectImage.{u, 0} M.j).obj
      ((DerivedCategory.singleFunctor
        (Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F))
  have hw := (((etaleAbelianInverseImage.{u, 0} ψ.π).mapDerivedCategoryHomologyIso q).inv.naturality
    ((etaleAbelianDerivedBaseChange.{u, 0} M.j φ.π (𝟙 _) M'.j sq₁).app
      ((DerivedCategory.singleFunctor
        (Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
          F))).symm
  exact kills_chase (etaleAbelianInverseImage.{u, 0} (ψ.comp φ).π)
    (etaleAbelianInverseImage.{u, 0} φ.π) (etaleAbelianInverseImage.{u, 0} ψ.π)
    (etaleAbelianInverseImageCompIso'.{u, 0} ψ.π φ.π (ψ.comp φ).π rfl).hom ι
    (etaleAbelianRightDerivedDirectImageIsoHomology.{0, u} M.j q F).hom _ _ hφ _ _ _ hcoh _ _ hw
    _ _

end AlgebraicGeometry.Scheme.ZariskiRiemann

end
