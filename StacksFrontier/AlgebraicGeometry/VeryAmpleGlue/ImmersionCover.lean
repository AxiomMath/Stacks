module

public import StacksFrontier.AlgebraicGeometry.VeryAmpleGlue.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceModuli.Basic

/-!
# Gluing relative very ampleness from immersions into projective space over an affine covering

Let `f : X ⟶ S` be quasi-compact, `L` an invertible `𝒪_X`-module and `S = ⋃ V_j` a covering by
affine opens such that over each `V_j` there are an integer `n_j` and an immersion
`i_j : f⁻¹(V_j) ⟶ ℙ^{n_j}_{V_j}` over `V_j` with `L|_{f⁻¹(V_j)} ≅ i_j^* 𝒪(1)`. Then `L` is very
ample relative to `f` in the sense of [Stacks, Tag 01VM]. This is [Stacks, Tag 01VR], (2) ⟹ (1),
with the members given by immersions into projective space.

## Main results

* `Stacks.VeryAmpleGlue.eq_of_pin_pullbackCoordSection`: a morphism to `ℙⁿ_S` over `S` pinned by
  the homogeneous coordinates pulled back along a morphism `i` over `S` is `i`.
* `Stacks.VeryAmpleGlue.isRelativelyVeryAmple_of_affine_cover_hasImmersionTwistOver`: `L` is
  very ample relative to `f` when over each member of an affine covering of `S` it is the pullback
  of `𝒪(1)` along an immersion into projective space.

## References

* [Stacks Project, Tag 01VR](https://stacks.math.columbia.edu/tag/01VR)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 02NQ](https://stacks.math.columbia.edu/tag/02NQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Ample Stacks.ProjectiveFromSections Stacks.AmpleProjectiveImmersion

universe u

namespace Stacks.VeryAmpleGlue

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {X S : Scheme.{u}}

/-- Let `i, p : X ⟶ ℙⁿ_S` both lie over `g : X ⟶ S`. If `p` is pinned by the homogeneous
coordinates of `𝒪(1)` pulled back along the projection of `i` to `ℙⁿ_ℤ`, then `p = i`. -/
theorem eq_of_pin_pullbackCoordSection (g : X ⟶ S) {n : ℕ} (i p : X ⟶ projectiveSpaceOver n S)
    (hi : i ≫ pullback.fst (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} n)) =
      g)
    (hp : p ≫ pullback.fst (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} n)) =
      g)
    (hpin : ∀ k, (nvCover (Stacks.TwistPullbackPinned.pullbackCoordSection
        (i ≫ projectiveSpaceOver.toIntegralAtUniverse n S)) k).ι ≫ p ≫
          projectiveSpaceOver.toIntegralAtUniverse n S =
        Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse
          (chartRatio (Stacks.TwistPullbackPinned.pullbackCoordSection
            (i ≫ projectiveSpaceOver.toIntegralAtUniverse n S)) k)
          (span_range_chartRatio (Stacks.TwistPullbackPinned.pullbackCoordSection
            (i ≫ projectiveSpaceOver.toIntegralAtUniverse n S)) k)) :
    p = i :=
  pullback.hom_ext (hp.trans hi.symm)
    (Stacks.ProjectiveSpaceModuli.eq_of_pin _ (Stacks.ProjectiveSpaceModuli.taut_generates _) _ _
      hpin (Stacks.ProjectiveSpaceModuli.taut_pin _))

/-- Let `f : X ⟶ S` be quasi-compact, `L` an invertible `𝒪_X`-module and `V_j` affine opens
covering `S`. If for every `j` there are an integer `n_j` and an immersion
`f⁻¹(V_j) ⟶ ℙ^{n_j}_{V_j}` over `V_j` pulling the hyperplane sheaf back to `L|_{f⁻¹(V_j)}`, then
`L` is very ample relative to `f`. -/
theorem isRelativelyVeryAmple_of_affine_cover_hasImmersionTwistOver (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] [QuasiCompact f] {ι : Type*} (V : ι → S.Opens)
    (hV : ∀ j, IsAffineOpen (V j)) (hcov : (⨆ j, V j) = ⊤)
    (h : ∀ j, HasImmersionTwistOver (f ∣_ V j)
      ((modulePullback (f ⁻¹ᵁ V j).ι.toLRSHom.toShHom).obj L)) :
    Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f L := by
  choose n i him hover e using h
  exact isRelativelyVeryAmple_of_cover f L V hV hcov n
    (fun j => (Scheme.Modules.pullback
      (i j ≫ projectiveSpaceOver.toIntegralAtUniverse (n j) (V j).toScheme)).obj
        (twistingSheafAtUniverse.{u} (n j)))
    (fun j => Stacks.TwistPullbackPinned.pullbackCoordSection
      (i j ≫ projectiveSpaceOver.toIntegralAtUniverse (n j) (V j).toScheme))
    (fun j => Stacks.ProjectiveSpaceModuli.taut_generates _)
    (fun j p hp hpin => eq_of_pin_pullbackCoordSection (f ∣_ V j) (i j) p (hover j) hp hpin ▸ him j)
    (fun j => λ_ _ ≪≫ (e j).some ≪≫ (Scheme.Modules.pullbackComp (i j) _).app _)

end Stacks.VeryAmpleGlue

end
