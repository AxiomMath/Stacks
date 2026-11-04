module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.DirectImageAcyclic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# The higher direct images of `𝐆_a` along an affine morphism vanish

Let `g : Y ⟶ X` be an affine morphism of schemes. Then `R^q g_* 𝐆_{a,Y} = 0` for every `q > 0`, the
higher direct images being those of abelian sheaves on the small étale sites.

## Main results

* `Stacks.ArtinSchreier.isZero_rightDerived_etaleAbelianDirectImage_of_isDirectImageAcyclic`:
  `R^q g_* M = 0` for `q > 0` and `M` acyclic in the sense of
  `Stacks.ArtinSchreier.IsDirectImageAcyclic`.
* `Stacks.ArtinSchreier.isZero_rightDerived_etaleAbelianDirectImage_additiveSheaf`:
  `R^q g_* 𝐆_a = 0` for `q > 0` and `g` affine.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry
open Stacks.EtaleCohomology

universe w u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.ArtinSchreier

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- The direct image `g_*` of abelian sheaves preserves finite limits. -/
instance preservesFiniteLimits_etaleAbelianDirectImage :
    PreservesFiniteLimits (etaleAbelianDirectImage.{u, 0} g) :=
  have := (etaleAbelianInverseImageDirectImageAdj.{u, 0} g).rightAdjoint_preservesLimits.{0, 0}
  inferInstance

variable [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **The higher direct images of an acyclic sheaf vanish.** If the cohomology of `M` over the
base change of every affine étale `X`-scheme vanishes in positive degree, then so does every
`R^q g_* M`, `q > 0`. -/
theorem isZero_rightDerived_etaleAbelianDirectImage_of_isDirectImageAcyclic (n : ℕ) :
    ∀ (M : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}),
      IsDirectImageAcyclic.{w} g M →
        IsZero (((etaleAbelianDirectImage.{u, 0} g).rightDerived (n + 1)).obj M) := by
  let D := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (etaleAbelianDirectImage.{u, 0} g)
  have presentation : ∀ M : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1},
      ∃ (S : ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (_ : S.ShortExact) (_ : Injective S.X₂), S.X₁ = M := by
    intro M
    refine ⟨ShortComplex.mk (Injective.ι M) (cokernel.π (Injective.ι M)) (cokernel.condition _),
      ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
        inferInstance inferInstance, inferInstanceAs (Injective (Injective.under M)), rfl⟩
  have hinj : ∀ (S : ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
      [Injective S.X₂] (k : ℕ), (D.functor (k + 1)).map S.f = 0 := fun S _ k =>
    IsZero.eq_of_tgt
      ((etaleAbelianDirectImage.{u, 0} g).isZero_rightDerived_obj_injective_succ k S.X₂)
      ((D.functor (k + 1)).map S.f) 0
  induction n with
  | zero =>
    intro M hM
    obtain ⟨S, hS, hI, rfl⟩ := presentation M
    have hδ : Epi (D.δ hS 0) := D.epi_δ_of_map_f_eq_zero hS 0 (hinj S 0)
    have hg : Epi ((D.functor 0).map S.g) := by
      have : Epi ((etaleAbelianDirectImage.{u, 0} g).map S.g) :=
        (shortExact_map_directImage.{w} g hS hM).epi_g
      have e := (etaleAbelianDirectImage.{u, 0} g).rightDerivedZeroIsoSelf
      have hfac : (D.functor 0).map S.g =
          e.hom.app S.X₂ ≫ (etaleAbelianDirectImage.{u, 0} g).map S.g ≫ e.inv.app S.X₃ := by
        rw [← e.hom.naturality_assoc, Iso.hom_inv_id_app, Category.comp_id]
        rfl
      rw [hfac]
      exact epi_comp' (inferInstanceAs (Epi (e.app S.X₂).hom))
        (epi_comp' this (inferInstanceAs (Epi (e.app S.X₃).inv)))
    have hzero : D.δ hS 0 = 0 := (D.exact_δ₁ hS 0).epi_f_iff.1 hg
    rw [hzero] at hδ
    exact @IsZero.of_epi_zero _ _ _ ((D.functor 0).obj S.X₃) ((D.functor (0 + 1)).obj S.X₁) hδ
  | succ n ih =>
    intro M hM
    obtain ⟨S, hS, hI, rfl⟩ := presentation M
    exact @IsZero.of_epi _ _ _ _ _ (D.δ hS (n + 1))
      (D.epi_δ_of_map_f_eq_zero hS (n + 1) (hinj S (n + 1)))
      (ih S.X₃ (isDirectImageAcyclic_X₃.{w} g hS hM))

/-- **`R^q g_* 𝐆_a = 0` for `q > 0` and `g` affine**, on the small étale sites. -/
theorem isZero_rightDerived_etaleAbelianDirectImage_additiveSheaf [IsAffineHom g] (n : ℕ) :
    IsZero (((etaleAbelianDirectImage.{u, 0} g).rightDerived (n + 1)).obj
      (additiveSheaf.{u, u + 1} Y)) :=
  isZero_rightDerived_etaleAbelianDirectImage_of_isDirectImageAcyclic.{w} g n _
    (isDirectImageAcyclic_additiveSheaf.{w} g)

end Stacks.ArtinSchreier

end
