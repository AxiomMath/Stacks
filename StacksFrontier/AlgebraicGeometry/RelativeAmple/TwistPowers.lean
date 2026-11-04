module

public import StacksFrontier.AlgebraicGeometry.RelativeAmple.TwistIdentification
public import StacksFrontier.AlgebraicGeometry.PullbackSections.UnitChase
public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.TwistSections
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaUniqueSections

/-!
# The map `θ` of Tag 01O9 for a relatively ample sheaf, in every degree, on sections

For `ℒ` ample relative to a quasi-compact quasi-separated `f : X ⟶ S` and the canonical morphism
`r : X ⟶ Proj_S(⨁_{d ≥ 0} f_* ℒ^{⊗ d})` of [Stacks, Tag 01VJ], the map `θ` of [Stacks, Tag 01O9]
for `r` gives in every degree `n` a map `r^* 𝒪(n) ⟶ ℒ^{⊗ n}` on all of `X`
(`relativeAmpleTwistPow`); in degree one, followed by `ℒ^{⊗ 1} ≅ ℒ`, it is
`relativeAmpleTwistIso`. On the inverse image of a section `w` of `𝒪(n)` it is the pushforward
form `thetaPush` of `θ` applied to `w`.

## Main definitions

* `Stacks.RelativeAmple.TwistIdentification.relativeAmpleTwistPow`.

## Main results

* `…relativeAmpleTwistIso_hom_eq`, `…relativeAmpleTwistPow_app_unitApp`.

## References

* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 01VJ](https://stacks.math.columbia.edu/tag/01VJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MonoidalCategory
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.AlgebraicGeometry.SectionRingBaseChange (unitApp unitApp_naturality unitApp_map
  hom_app_map map_map_homOfLE)

universe u

namespace Stacks.RelativeAmple.TwistIdentification

-- `CategoryTheory.catToReflQuiver` offers a second route from `Category` to `Quiver`; see
-- `Stacks.AlgebraicGeometry.ProjectiveDeformation.TwistSections`.
attribute [-instance] CategoryTheory.catToReflQuiver

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

section Chase

variable {X C Pr : Scheme.{u}}

/-- The identification of the restriction along an open immersion with the inverse image, on
sections: the section `z` of `K|_C` over `W` is the restriction of the inverse image of `z`, read
over `ι(W)`. -/
theorem restrictFunctorIsoPullback_hom_app (ι : C ⟶ X) [IsOpenImmersion ι] (K : X.Modules)
    (W : C.Opens) (z : Γ(K, ι ''ᵁ W)) :
    ((Scheme.Modules.restrictFunctorIsoPullback ι).hom.app K).app W z =
      ((Scheme.Modules.pullback ι).obj K).presheaf.map (homOfLE (ι.preimage_image_eq W).ge).op
        (unitApp ι K (ι ''ᵁ W) z) := by
  have hu : unitApp ι K (ι ''ᵁ W) z =
      ((Scheme.Modules.restrictFunctorIsoPullback ι).hom.app K).app (ι ⁻¹ᵁ (ι ''ᵁ W))
        (K.presheaf.map (homOfLE (ι.image_preimage_le (ι ''ᵁ W))).op z) :=
    (congrArg (fun φ => Scheme.Modules.Hom.app φ (ι ''ᵁ W) z)
      (Stacks.AlgebraicGeometry.ProjTwistTheta.restrictUnit_comp_map_restrictFunctorIsoPullback ι
        K)).symm
  have hz : (K.restrict ι).presheaf.map (homOfLE (ι.preimage_image_eq W).ge).op
      (K.presheaf.map (homOfLE (ι.image_preimage_le (ι ''ᵁ W))).op z) = z := by
    show K.presheaf.map _ (K.presheaf.map _ z) = z
    rw [← CategoryTheory.comp_apply, ← CategoryTheory.Functor.map_comp]
    have e : ∀ q : op (ι ''ᵁ W) ⟶ op (ι ''ᵁ W), K.presheaf.map q z = z := fun q => by
      rw [Subsingleton.elim q (𝟙 _), CategoryTheory.Functor.map_id]
      rfl
    exact e _
  calc ((Scheme.Modules.restrictFunctorIsoPullback ι).hom.app K).app W z
      = ((Scheme.Modules.restrictFunctorIsoPullback ι).hom.app K).app W
          ((K.restrict ι).presheaf.map (homOfLE (ι.preimage_image_eq W).ge).op
            (K.presheaf.map (homOfLE (ι.image_preimage_le (ι ''ᵁ W))).op z)) := by rw [hz]
    _ = ((Scheme.Modules.pullback ι).obj K).presheaf.map (homOfLE (ι.preimage_image_eq W).ge).op
          (((Scheme.Modules.restrictFunctorIsoPullback ι).hom.app K).app (ι ⁻¹ᵁ (ι ''ᵁ W))
            (K.presheaf.map (homOfLE (ι.image_preimage_le (ι ''ᵁ W))).op z)) :=
        hom_app_map _ (ι.preimage_image_eq W).ge _
    _ = _ := by rw [hu]

/-- **The chase through a section of an open immersion and a map out of an inverse image into a
restriction.** -/
theorem theta_chase (j : X ⟶ C) (ι : C ⟶ X) [IsOpenImmersion ι] (hj : j ≫ ι = 𝟙 X) (gm : C ⟶ Pr)
    (rr : X ⟶ Pr) (hr : rr = j ≫ gm) {M : Pr.Modules} {K : X.Modules}
    (Θ : (Scheme.Modules.pullback gm).obj M ⟶ K.restrict ι) (O : Pr.Opens) (w : Γ(M, O))
    (z : Γ(K, ι ''ᵁ (gm ⁻¹ᵁ O))) (hΘ : Θ.app (gm ⁻¹ᵁ O) (unitApp gm M O w) = z)
    (hfin : rr ⁻¹ᵁ O ≤ ι ''ᵁ (gm ⁻¹ᵁ O)) :
    Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr hr).hom.app M ≫
        (Scheme.Modules.pullbackComp j gm).inv.app M ≫ (Scheme.Modules.pullback j).map Θ ≫
        (Scheme.Modules.pullback j).map ((Scheme.Modules.restrictFunctorIsoPullback ι).hom.app K) ≫
        (Scheme.Modules.pullbackComp j ι).hom.app K ≫ (Scheme.Modules.pullbackCongr hj).hom.app K ≫
        (Scheme.Modules.pullbackId X).hom.app K) (rr ⁻¹ᵁ O) (unitApp rr M O w) =
      K.presheaf.map (homOfLE hfin).op z := by
  subst hr
  have hW := (ι.preimage_image_eq (gm ⁻¹ᵁ O)).ge
  have h1 : j ⁻¹ᵁ gm ⁻¹ᵁ O ≤ j ⁻¹ᵁ ι ⁻¹ᵁ (ι ''ᵁ (gm ⁻¹ᵁ O)) := j.preimage_mono hW
  have h1' : j ⁻¹ᵁ gm ⁻¹ᵁ O ≤ (j ≫ ι) ⁻¹ᵁ (ι ''ᵁ (gm ⁻¹ᵁ O)) := h1
  have h1'' : j ⁻¹ᵁ gm ⁻¹ᵁ O ≤ (𝟙 X) ⁻¹ᵁ (ι ''ᵁ (gm ⁻¹ᵁ O)) := by simpa using hfin
  have hcg : (j ≫ ι) ⁻¹ᵁ (ι ''ᵁ (gm ⁻¹ᵁ O)) ≤ (𝟙 X) ⁻¹ᵁ (ι ''ᵁ (gm ⁻¹ᵁ O)) := by rw [hj]
  have s1 : Scheme.Modules.Hom.app
      ((Scheme.Modules.pullbackCongr (rfl : j ≫ gm = j ≫ gm)).hom.app M)
      (j ⁻¹ᵁ gm ⁻¹ᵁ O) (unitApp (j ≫ gm) M O w) = unitApp (j ≫ gm) M O w := rfl
  have s2 : Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp j gm).inv.app M)
      (j ⁻¹ᵁ gm ⁻¹ᵁ O) (unitApp (j ≫ gm) M O w) =
      unitApp j ((Scheme.Modules.pullback gm).obj M) (gm ⁻¹ᵁ O) (unitApp gm M O w) :=
    Scheme.Modules.pullbackComp_inv_unit j gm M O w
  have s3 : Scheme.Modules.Hom.app ((Scheme.Modules.pullback j).map Θ) (j ⁻¹ᵁ gm ⁻¹ᵁ O)
      (unitApp j ((Scheme.Modules.pullback gm).obj M) (gm ⁻¹ᵁ O) (unitApp gm M O w)) =
      unitApp j (K.restrict ι) (gm ⁻¹ᵁ O) z :=
    (unitApp_naturality j Θ (gm ⁻¹ᵁ O) (unitApp gm M O w)).trans
      (congrArg (unitApp j (K.restrict ι) (gm ⁻¹ᵁ O)) hΘ)
  have s4 : Scheme.Modules.Hom.app ((Scheme.Modules.pullback j).map
      ((Scheme.Modules.restrictFunctorIsoPullback ι).hom.app K)) (j ⁻¹ᵁ gm ⁻¹ᵁ O)
      (unitApp j (K.restrict ι) (gm ⁻¹ᵁ O) z) =
      ((Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback ι).obj K)).presheaf.map
        (homOfLE h1).op (unitApp j ((Scheme.Modules.pullback ι).obj K)
          (ι ⁻¹ᵁ (ι ''ᵁ (gm ⁻¹ᵁ O))) (unitApp ι K (ι ''ᵁ (gm ⁻¹ᵁ O)) z)) :=
    (unitApp_naturality j ((Scheme.Modules.restrictFunctorIsoPullback ι).hom.app K)
      (gm ⁻¹ᵁ O) z).trans
      ((congrArg (unitApp j ((Scheme.Modules.pullback ι).obj K) (gm ⁻¹ᵁ O))
        (restrictFunctorIsoPullback_hom_app ι K (gm ⁻¹ᵁ O) z)).trans
        (unitApp_map j ((Scheme.Modules.pullback ι).obj K) hW _))
  have s5 : Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp j ι).hom.app K) (j ⁻¹ᵁ gm ⁻¹ᵁ O)
      (((Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback ι).obj K)).presheaf.map
        (homOfLE h1).op (unitApp j ((Scheme.Modules.pullback ι).obj K)
          (ι ⁻¹ᵁ (ι ''ᵁ (gm ⁻¹ᵁ O))) (unitApp ι K (ι ''ᵁ (gm ⁻¹ᵁ O)) z))) =
      ((Scheme.Modules.pullback (j ≫ ι)).obj K).presheaf.map (homOfLE h1').op
        (unitApp (j ≫ ι) K (ι ''ᵁ (gm ⁻¹ᵁ O)) z) :=
    (hom_app_map ((Scheme.Modules.pullbackComp j ι).hom.app K) h1 _).trans
      (congrArg (((Scheme.Modules.pullback (j ≫ ι)).obj K).presheaf.map (homOfLE h1').op)
        (Stacks.AlgebraicGeometry.TwistMulLeg.pullbackComp_hom_app_unitApp j ι K _ z))
  have s6 : Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr hj).hom.app K) (j ⁻¹ᵁ gm ⁻¹ᵁ O)
      (((Scheme.Modules.pullback (j ≫ ι)).obj K).presheaf.map (homOfLE h1').op
        (unitApp (j ≫ ι) K (ι ''ᵁ (gm ⁻¹ᵁ O)) z)) =
      ((Scheme.Modules.pullback (𝟙 X)).obj K).presheaf.map (homOfLE h1'').op
        (unitApp (𝟙 X) K (ι ''ᵁ (gm ⁻¹ᵁ O)) z) :=
    (hom_app_map ((Scheme.Modules.pullbackCongr hj).hom.app K) h1' _).trans
      ((congrArg (((Scheme.Modules.pullback (𝟙 X)).obj K).presheaf.map (homOfLE h1').op)
        (Stacks.AlgebraicGeometry.TwistMulLeg.pullbackCongr_hom_app_unitApp hj K _ z)).trans
        (map_map_homOfLE _ h1' hcg h1'' _))
  have s7 : Scheme.Modules.Hom.app ((Scheme.Modules.pullbackId X).hom.app K) (j ⁻¹ᵁ gm ⁻¹ᵁ O)
      (((Scheme.Modules.pullback (𝟙 X)).obj K).presheaf.map (homOfLE h1'').op
        (unitApp (𝟙 X) K (ι ''ᵁ (gm ⁻¹ᵁ O)) z)) = K.presheaf.map (homOfLE hfin).op z :=
    (hom_app_map ((Scheme.Modules.pullbackId X).hom.app K) h1'' _).trans
      (congrArg (K.presheaf.map (homOfLE h1'').op)
        (Stacks.AlgebraicGeometry.GradedAlgebraHomSections.pullbackId_hom_app_unitApp K _ z))
  refine (Stacks.AlgebraicGeometry.TwistMulLeg.app_comp_apply _ _ _ _).trans ?_
  refine (Stacks.AlgebraicGeometry.TwistMulLeg.app_comp_apply _ _ _ _).trans ?_
  refine (Stacks.AlgebraicGeometry.TwistMulLeg.app_comp_apply _ _ _ _).trans ?_
  refine (Stacks.AlgebraicGeometry.TwistMulLeg.app_comp_apply _ _ _ _).trans ?_
  refine (Stacks.AlgebraicGeometry.TwistMulLeg.app_comp_apply _ _ _ _).trans ?_
  refine (Stacks.AlgebraicGeometry.TwistMulLeg.app_comp_apply _ _ _ _).trans ?_
  exact (congrArg (fun x => Scheme.Modules.Hom.app ((Scheme.Modules.pullbackId X).hom.app K)
      (j ⁻¹ᵁ gm ⁻¹ᵁ O) (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr hj).hom.app K)
        (j ⁻¹ᵁ gm ⁻¹ᵁ O) (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp j ι).hom.app K)
          (j ⁻¹ᵁ gm ⁻¹ᵁ O) (Scheme.Modules.Hom.app ((Scheme.Modules.pullback j).map
            ((Scheme.Modules.restrictFunctorIsoPullback ι).hom.app K)) (j ⁻¹ᵁ gm ⁻¹ᵁ O)
            (Scheme.Modules.Hom.app ((Scheme.Modules.pullback j).map Θ) (j ⁻¹ᵁ gm ⁻¹ᵁ O)
              (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp j gm).inv.app M)
                (j ⁻¹ᵁ gm ⁻¹ᵁ O) x)))))) s1).trans
    ((congrArg (fun x => Scheme.Modules.Hom.app ((Scheme.Modules.pullbackId X).hom.app K)
      (j ⁻¹ᵁ gm ⁻¹ᵁ O) (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr hj).hom.app K)
        (j ⁻¹ᵁ gm ⁻¹ᵁ O) (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp j ι).hom.app K)
          (j ⁻¹ᵁ gm ⁻¹ᵁ O) (Scheme.Modules.Hom.app ((Scheme.Modules.pullback j).map
            ((Scheme.Modules.restrictFunctorIsoPullback ι).hom.app K)) (j ⁻¹ᵁ gm ⁻¹ᵁ O)
            (Scheme.Modules.Hom.app ((Scheme.Modules.pullback j).map Θ) (j ⁻¹ᵁ gm ⁻¹ᵁ O) x)))))
      s2).trans
    ((congrArg (fun x => Scheme.Modules.Hom.app ((Scheme.Modules.pullbackId X).hom.app K)
      (j ⁻¹ᵁ gm ⁻¹ᵁ O) (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr hj).hom.app K)
        (j ⁻¹ᵁ gm ⁻¹ᵁ O) (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp j ι).hom.app K)
          (j ⁻¹ᵁ gm ⁻¹ᵁ O) (Scheme.Modules.Hom.app ((Scheme.Modules.pullback j).map
            ((Scheme.Modules.restrictFunctorIsoPullback ι).hom.app K)) (j ⁻¹ᵁ gm ⁻¹ᵁ O) x))))
      s3).trans
    ((congrArg (fun x => Scheme.Modules.Hom.app ((Scheme.Modules.pullbackId X).hom.app K)
      (j ⁻¹ᵁ gm ⁻¹ᵁ O) (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr hj).hom.app K)
        (j ⁻¹ᵁ gm ⁻¹ᵁ O) (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp j ι).hom.app K)
          (j ⁻¹ᵁ gm ⁻¹ᵁ O) x))) s4).trans
    ((congrArg (fun x => Scheme.Modules.Hom.app ((Scheme.Modules.pullbackId X).hom.app K)
      (j ⁻¹ᵁ gm ⁻¹ᵁ O) (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr hj).hom.app K)
        (j ⁻¹ᵁ gm ⁻¹ᵁ O) x)) s5).trans
    ((congrArg (fun x => Scheme.Modules.Hom.app ((Scheme.Modules.pullbackId X).hom.app K)
      (j ⁻¹ᵁ gm ⁻¹ᵁ O) x) s6).trans s7)))))

end Chase

section Relative

open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

variable {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  [QuasiCompact f] [QuasiSeparated f] (hL : IsRelativelyAmple f L)

/-- The inverse of the inclusion of `U(ψ) = X`, for the datum of a relatively ample sheaf. -/
def coveringSection : X ⟶ (directImagePowerMap f L).coveringOpen.toScheme :=
  X.topIso.inv ≫ (X.isoOfEq (coveringOpen_directImagePowerMap hL).symm).hom

/-- `coveringSection` is a section of the inclusion of `U(ψ) = X`. -/
theorem coveringSection_ι :
    coveringSection f L hL ≫ (directImagePowerMap f L).coveringOpen.ι = 𝟙 X := by
  simp only [coveringSection, Category.assoc, Scheme.isoOfEq_hom_ι, Scheme.toIso_inv_ι]

/-- The morphism `r : X ⟶ Proj` factors through `coveringSection` and the morphism defined on
`U(ψ)`. -/
theorem relativeAmpleProjHom_eq_comp :
    relativeAmpleProjHom f L hL = coveringSection f L hL ≫
      (directImagePowerMap f L).globalMorphism
        (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (directImageAlgebra f L)) := by
  simp only [relativeAmpleProjHom, coveringSection, Category.assoc]

/-- **The map `θ` of [Stacks, Tag 01O9] for `r`, in degree `n`, on all of `X`**:
`r^* 𝒪(n) ⟶ ℒ^{⊗ n}`. -/
def relativeAmpleTwistPow (n : ℤ) :
    (Scheme.Modules.pullback (relativeAmpleProjHom f L hL)).obj
        (Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwist (directImageAlgebra f L) n) ⟶
      tensorPowerModule X L n :=
  (Scheme.Modules.pullbackCongr (relativeAmpleProjHom_eq_comp f L hL)).hom.app _ ≫
    (Scheme.Modules.pullbackComp (coveringSection f L hL) ((directImagePowerMap f L).globalMorphism
      (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (directImageAlgebra f L)))).inv.app _ ≫
    (Scheme.Modules.pullback (coveringSection f L hL)).map
      ((directImagePowerMap f L).theta.app n) ≫
    (Scheme.Modules.pullback (coveringSection f L hL)).map
      ((Scheme.Modules.restrictFunctorIsoPullback (directImagePowerMap f L).coveringOpen.ι).hom.app
        (tensorPowerModule X L n)) ≫
    (Scheme.Modules.pullbackComp (coveringSection f L hL)
      (directImagePowerMap f L).coveringOpen.ι).hom.app _ ≫
    (Scheme.Modules.pullbackCongr (coveringSection_ι f L hL)).hom.app _ ≫
    (Scheme.Modules.pullbackId X).hom.app _

/-- **In degree one `relativeAmpleTwistPow` is `relativeAmpleTwistIso`**, up to `ℒ^{⊗ 1} ≅ ℒ`. -/
theorem relativeAmpleTwistIso_hom_eq :
    (relativeAmpleTwistIso f L hL).hom = relativeAmpleTwistPow f L hL 1 ≫
      (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L 1).inv ≫ (λ_ L).hom := by
  unfold relativeAmpleTwistIso relativeAmpleTwistPow
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Category.assoc]
  rfl

/-- The inverse image of an open `O` under `r` lies in the image of the inverse image of `O`
under the morphism defined on `U(ψ)`. -/
theorem relativeAmpleProjHom_preimage_le (O : (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
    (directImageAlgebra f L)).scheme.Opens) :
    relativeAmpleProjHom f L hL ⁻¹ᵁ O ≤ (directImagePowerMap f L).coveringOpen.ι ''ᵁ
      ((directImagePowerMap f L).globalMorphism
        (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (directImageAlgebra f L)) ⁻¹ᵁ O) := by
  rw [relativeAmpleProjHom_eq_comp, Scheme.Hom.comp_preimage]
  intro x hx
  refine ⟨(coveringSection f L hL).base x, hx, ?_⟩
  exact congrArg (fun φ : X ⟶ X => φ.base x) (coveringSection_ι f L hL)

/-- **`relativeAmpleTwistPow` on the inverse image of a section `w` of `𝒪(n)` is the pushforward
form of `θ` applied to `w`.** -/
theorem relativeAmpleTwistPow_app_unitApp (n : ℤ)
    (O : (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (directImageAlgebra f L)).scheme.Opens)
    (w : Γ(Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwist (directImageAlgebra f L) n, O)) :
    (relativeAmpleTwistPow f L hL n).app (relativeAmpleProjHom f L hL ⁻¹ᵁ O)
        (unitApp (relativeAmpleProjHom f L hL) _ O w) =
      (tensorPowerModule X L n).presheaf.map
        (homOfLE (relativeAmpleProjHom_preimage_le f L hL O)).op
        (((directImagePowerMap f L).thetaPush n).app O w) :=
  theta_chase (coveringSection f L hL) (directImagePowerMap f L).coveringOpen.ι
    (coveringSection_ι f L hL) _ _ (relativeAmpleProjHom_eq_comp f L hL)
    ((directImagePowerMap f L).theta.app n) O w (((directImagePowerMap f L).thetaPush n).app O w)
    (Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.transposeAppHom_pullbackUnit
      ((directImagePowerMap f L).globalMorphism
        (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
          (directImageAlgebra f L))).toLRSHom.toShHom
      (directImagePowerMap f L).thetaPushHom n O w)
    (relativeAmpleProjHom_preimage_le f L hL O)

/-- The inverse image under `r` of the inverse image of an open `V` of `S` in `Proj` lies in
`f⁻¹ V`. -/
theorem relativeAmpleProjHom_preimage_toBase_le (V : S.Opens) :
    relativeAmpleProjHom f L hL ⁻¹ᵁ
        ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj (directImageAlgebra f L)).toBase ⁻¹ᵁ V)
      ≤ f ⁻¹ᵁ V := by
  rw [← Scheme.Hom.comp_preimage, relativeAmpleProjHom_toBase]

/-- **`relativeAmpleTwistPow` on the section attached to a homogeneous element** `x` of
`f_* ℒ^{⊗ d}`: it is `x`. -/
theorem relativeAmpleTwistPow_app_unitApp_psiU (d : ℕ) (V : S.Opens)
    (x : Γ((directImageAlgebra f L).piece (d : ℤ), V)) :
    (relativeAmpleTwistPow f L hL d).app (relativeAmpleProjHom f L hL ⁻¹ᵁ
        ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj
          (directImageAlgebra f L)).toBase ⁻¹ᵁ V))
        (unitApp (relativeAmpleProjHom f L hL) _
          ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj
            (directImageAlgebra f L)).toBase ⁻¹ᵁ V)
          (Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap.psiU
            (directImageAlgebra f L) d V x)) =
      (tensorPowerModule X L d).presheaf.map
        (homOfLE (relativeAmpleProjHom_preimage_toBase_le f L hL V)).op
        (x : Γ(tensorPowerModule X L d, f ⁻¹ᵁ V)) := by
  rw [relativeAmpleTwistPow_app_unitApp, (directImagePowerMap f L).thetaPush_psiU V d x,
    directImagePowerMap_value]
  refine (congrArg (fun z => (tensorPowerModule X L d).presheaf.map
    (homOfLE (relativeAmpleProjHom_preimage_le f L hL _)).op
    ((tensorPowerModule X L d).presheaf.map
      (homOfLE ((directImagePowerMap f L).image_preimage_preimage_le V)).op z))
    (Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.hom_app_inv_app
      (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L d) (f ⁻¹ᵁ V) x)).trans ?_
  exact map_map_homOfLE _ _ _ _ _

/-- **`relativeAmpleTwistPow` is multiplicative on inverse images of sections**, `θ` being a map of
graded algebras. -/
theorem relativeAmpleTwistPow_unitMul :
    Stacks.AlgebraicGeometry.ProjectiveDeformation.TwistSections.UnitMul L
      (relativeAmpleProjHom f L hL)
      (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra
        (directImageAlgebra f L)).algebra
      (relativeAmpleTwistPow f L hL) := by
  intro i j O s t
  have e1 := relativeAmpleTwistPow_app_unitApp f L hL (i + j) O
    (((Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra
      (directImageAlgebra f L)).algebra.mul i j).app (op O) s t)
  have e2 := relativeAmpleTwistPow_app_unitApp f L hL i O s
  have e3 := relativeAmpleTwistPow_app_unitApp f L hL j O t
  have e4 := (directImagePowerMap f L).thetaPush_app_mul i j O s t
  have e5 := Stacks.TensorPowerDivision.map_localMul L
    (homOfLE (relativeAmpleProjHom_preimage_le f L hL O))
    (((directImagePowerMap f L).thetaPush i).app O s)
    (((directImagePowerMap f L).thetaPush j).app O t)
  rw [e2, e3]
  exact e1.trans ((congrArg ((tensorPowerModule X L (i + j)).presheaf.map
    (homOfLE (relativeAmpleProjHom_preimage_le f L hL O)).op) e4).trans e5)

end Relative

end Stacks.RelativeAmple.TwistIdentification

end
