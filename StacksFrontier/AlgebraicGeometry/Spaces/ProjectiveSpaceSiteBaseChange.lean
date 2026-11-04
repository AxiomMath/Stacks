module

public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsMorphismToProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairOpenExtensionQuotient

/-!
# Base change of projective space, in the big fppf site

For a morphism `κ : K ⟶ Y` of the site, the morphism `ℙʳ_K ⟶ ℙʳ_Y` of the site
(`AlgebraicGeometry.Space.projectiveSpaceOverSiteBaseChange`) fits into a cartesian square over
`κ` (`AlgebraicGeometry.Space.isPullback_projectiveSpaceOverSiteBaseChange`): projective space
is stable under base change, Stacks 01NF.  The morphisms of the site into `ℙʳ_Y` attached to a
morphism into `Y` and a morphism into `ℙʳ_ℤ`
(`AlgebraicGeometry.Space.projectiveSpaceOverSiteHom`) lie over `Y` and are compatible with this
base change.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The morphism `φ` attached to `a` and `g` lies over `Y`.** -/
theorem projectiveSpaceOverSiteHom_comp_proj {Y T : BigFppfOver B S hS} (r : ℕ) (a : T ⟶ Y)
    (g : (BigFppfOver.toScheme B S hS).obj T ⟶ projectiveSpaceAtUniverse.{u} r) :
    projectiveSpaceOverSiteHom B S hS r a g ≫ projectiveSpaceOverSiteObjectProj B S hS Y r = a :=
  Over.OverMorphism.ext <| ObjectProperty.hom_ext _ <|
    Stacks.AmpleProjectiveImmersion.liftOver_fst ((BigFppfOver.toScheme B S hS).map a) g

/-- **The morphism `ℙʳ_K ⟶ ℙʳ_Y` of the site induced by `κ : K ⟶ Y`.** -/
def projectiveSpaceOverSiteBaseChange {K Y : BigFppfOver B S hS} (κ : K ⟶ Y) (r : ℕ) :
    projectiveSpaceOverSiteObject B S hS K r ⟶ projectiveSpaceOverSiteObject B S hS Y r :=
  projectiveSpaceOverSiteHom B S hS r (projectiveSpaceOverSiteObjectProj B S hS K r ≫ κ)
    (projectiveSpaceOver.toIntegralAtUniverse r K.left.1)

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.projectiveSpaceOverSiteBaseChange`
is `AlgebraicGeometry.projectiveSpaceOverMap`. -/
theorem toScheme_map_projectiveSpaceOverSiteBaseChange {K Y : BigFppfOver B S hS} (κ : K ⟶ Y)
    (r : ℕ) :
    (BigFppfOver.toScheme B S hS).map (projectiveSpaceOverSiteBaseChange B S hS κ r) =
      projectiveSpaceOverMap r ((BigFppfOver.toScheme B S hS).map κ) := by
  refine pullback.hom_ext ?_ ?_
  · exact ((Stacks.AmpleProjectiveImmersion.liftOver_fst _ _).trans (Functor.map_comp _ _ _)).trans
      (projectiveSpaceOverMap_fst r _).symm
  · exact (Stacks.AmpleProjectiveImmersion.liftOver_snd _ _).trans
      (projectiveSpaceOverMap_snd r _).symm

/-- **Projective space is stable under base change in the site**: `ℙʳ_K = ℙʳ_Y ×_Y K`. -/
theorem isPullback_projectiveSpaceOverSiteBaseChange {K Y : BigFppfOver B S hS} (κ : K ⟶ Y)
    (r : ℕ) :
    IsPullback (projectiveSpaceOverSiteBaseChange B S hS κ r)
      (projectiveSpaceOverSiteObjectProj B S hS K r) (projectiveSpaceOverSiteObjectProj B S hS Y r)
      κ := by
  refine isPullback_of_isPullback_map (projectiveSpaceOverSiteHom_comp_proj B S hS r _ _) ?_
  rw [toScheme_map_projectiveSpaceOverSiteBaseChange]
  exact isPullback_projectiveSpaceOverMap r ((BigFppfOver.toScheme B S hS).map κ)

/-- **`AlgebraicGeometry.Space.projectiveSpaceOverSiteHom` is compatible with base change.** -/
theorem projectiveSpaceOverSiteHom_comp_baseChange {K Y T : BigFppfOver B S hS} (κ : K ⟶ Y)
    (r : ℕ) (a : T ⟶ K)
    (g : (BigFppfOver.toScheme B S hS).obj T ⟶ projectiveSpaceAtUniverse.{u} r) :
    projectiveSpaceOverSiteHom B S hS r a g ≫ projectiveSpaceOverSiteBaseChange B S hS κ r =
      projectiveSpaceOverSiteHom B S hS r (a ≫ κ) g := by
  refine (comp_projectiveSpaceOverSiteHom B S hS r (projectiveSpaceOverSiteHom B S hS r a g)
    (projectiveSpaceOverSiteObjectProj B S hS K r ≫ κ)
    (projectiveSpaceOver.toIntegralAtUniverse r K.left.1)).trans ?_
  rw [← Category.assoc, projectiveSpaceOverSiteHom_comp_proj]
  congr 1
  exact Stacks.AmpleProjectiveImmersion.liftOver_snd _ _

end AlgebraicGeometry.Space

end
