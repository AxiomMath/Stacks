module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.GluedChartPullback
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic

/-!
# The glueing problem for quadruples, discharged

Let `S` be a scheme, `𝒜` a graded `𝒪_S`-algebra (Situation 01NN) and `d` an integer.
`...RelativeProjQcohSheaf.QuadrupleGlues` is step (1) of the proof of Tag 01NV with the site, the
base morphism and the quotient removed
(`...RelativeProjQcohSheaf.Fd.quadrupleGlues_iff_isSheaf`): a morphism `f : T ⟶ S`, a family of
opens covering `T`, and quadruples over the restrictions of `f` which are pairwise strictly
equivalent over the overlaps, must produce a quadruple over `f` restricting to them. This file
produces it, so `F_d` is a Zariski sheaf unconditionally
(`...RelativeProjQcohSheaf.Fd.isSheaf_functor`).

## How the quadruple is assembled

Its invertible module is the one glued from the invertible modules of the family,
`...RelativeProjQcohSheaf.quadrupleGlueData` with
`...isInvertibleModule_quadrupleGlueData_glued`.

Its map `ψ` is glued degree by degree by
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover` from the local data
`...RelativeProjQcohSheaf.chartLocalApp`, each built from the given `ψ` of a member and the
identification `...ModulesGlueData.gluedPullbackIso` of the inverse image of the glued module
with that member's invertible module. The compatibility hypothesis of that tool is
`...RelativeProjQcohSheaf.localApp_chartLocalApp_eq`, whose two inputs over a common refinement
of two members are **the second vocabulary crossing**
`...RelativeProjQcohSheaf.refineChartIso_trans_chartWitness` — the two identifications differ by
`...Quadruple.chartWitness` — and the degreewise compatibility of the strict equivalence at that
refinement, which is `...Quadruple.strictlyEquivalentOver_of_common` read through
`...Quadruple.twisting_app_comp_congrIso_witnessOver`. The congruence isomorphisms along the two
spellings `V.ι ≫ f` and `k ≫ (W a).ι ≫ f` of one base morphism compose by
`...RelativeProjQcohSheaf.pullbackCongr_hom_app_trans`.

The three conditions on the glued family are `...RelativeProjQcohSheaf.mul_of_chartLocal_cover`,
`...one_of_chartLocal_cover` and `...epi_of_chartLocal_cover`, and the strict equivalence of the
restriction of the result with the given quadruple is
`...RelativeProjQcohSheaf.pullbackFamily_congrIso_of_restrictFunctor_map_eq` together with
`...LaurentAlgebraCongr.laurentCongrIso` of the identification.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.quadrupleGlues_proof`: **the glueing problem
  for quadruples.**
* `...RelativeProjQcohSheaf.Fd.isSheaf_functor`: **`F_d` is a sheaf on the big Zariski site**,
  with no hypothesis — step (1) of the proof of Tag 01NV.

## No tag is claimed

Step (1) is an ingredient of the proof of Tag 01NV, not a clause of it; the tag's carriers are in
`...RelativeProjQcohSheaf.SmallModel` and `...RelativeProjQcohSheaf.Representable`.

## References

* [Stacks Project, Tag 01NV](https://stacks.math.columbia.edu/tag/01NV)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
-/

@[expose] public noncomputable section

open CategoryTheory

open AlgebraicGeometry Stacks.RingedSpace

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

open Stacks.SheafOfModules Stacks.AlgebraicGeometry.ModuleHomGlue
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentAlgebraCongr
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

/-- The congruence isomorphisms of the inverse image along equal morphisms compose. -/
theorem pullbackCongr_hom_app_trans {X Y : Scheme.{u}} {g₁ g₂ g₃ : X ⟶ Y} (h : g₁ = g₂)
    (h' : g₂ = g₃) (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr h).hom.app M ≫
        (Scheme.Modules.pullbackCongr h').hom.app M =
      (Scheme.Modules.pullbackCongr (h.trans h')).hom.app M := by
  subst h
  subst h'
  rw [ModuleHomGlue.pullbackCongr_rfl]
  simp

variable {S : Scheme.{u}}

/-- **The glueing problem for quadruples, discharged**: step (1) of the proof of Tag 01NV with
the site, the base morphism and the quotient removed. -/
theorem quadrupleGlues_proof
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d : ℤ) :
    QuadrupleGlues A d := by
  intro T f ι W hW P hP
  have hample := isInvertibleModule_quadrupleGlueData_glued f W hW P hP
  have hmodinv : ∀ a : ι, Stacks.SheafOfModules.IsInvertible
      ((W a).toScheme).toRingedSpace.presheaf (isSheafStruct (W a).toScheme)
      ((quadrupleGlueData f W P hP).mod a) := fun a => (P a).isInvertible
  have hg : ⨆ a, ((W a).ι).opensRange = ⊤ := iSup_opensRange_ι_eq_top W hW
  have hcov : ⨆ a, ((W a).ι) ''ᵁ (⊤ : ((W a).toScheme).Opens) = ⊤ := by
    simpa only [Scheme.Hom.image_top_eq_opensRange] using hg
  -- the compatibility hypothesis of the glueing tool
  have hcompat : ∀ n : ℤ, ∀ (i j : ι) (W₁ : ((W i).toScheme).Opens)
      (W₂ : ((W j).toScheme).Opens) (V : T.Opens) (h₁ : (W i).ι ''ᵁ W₁ = V)
      (h₂ : (W j).ι ''ᵁ W₂ = V),
      ModuleHomGlue.localApp ((W i).ι) (chartLocalApp f ((W i).ι) A d
          (quadrupleGlueData f W P hP).glued
          ((quadrupleGlueData f W P hP).gluedPullbackIso i) (P i).twisting.app n) h₁ =
        ModuleHomGlue.localApp ((W j).ι) (chartLocalApp f ((W j).ι) A d
          (quadrupleGlueData f W P hP).glued
          ((quadrupleGlueData f W P hP).gluedPullbackIso j) (P j).twisting.app n) h₂ := by
    intro n i j W₁ W₂ V h₁ h₂
    have hle : ∀ (k : ι) (W' : ((W k).toScheme).Opens), (W k).ι ''ᵁ W' = V →
        V ≤ ((W k).ι).opensRange := fun k W' h => by
      rw [← h, ← Scheme.Hom.image_top_eq_opensRange]
      exact Scheme.Hom.image_mono _ le_top
    have hV : V ≤ chartOverlap (fun a => (W a).ι) i j := le_inf (hle i W₁ h₁) (hle j W₂ h₂)
    have hb : ∀ (k : ι) (hk : V ≤ ((W k).ι).opensRange),
        V.ι ≫ f = chartOpenLift ((W k).ι) hk ≫ (W k).ι ≫ f := fun k hk => by
      rw [← chartOpenLift_fac ((W k).ι) hk]
      exact Category.assoc _ _ _
    have hb₁ := hb i (hV.trans inf_le_left)
    have hb₂ := hb j (hV.trans inf_le_right)
    have hab : chartOpenLift ((W i).ι) (hV.trans inf_le_left) ≫ (W i).ι =
        chartOpenLift ((W j).ι) (hV.trans inf_le_right) ≫ (W j).ι := by
      rw [chartOpenLift_fac, chartOpenLift_fac]
    refine localApp_chartLocalApp_eq f A d (quadrupleGlueData f W P hP).glued
      ((W i).ι) ((W j).ι)
      (chartOpenLift ((W i).ι) (hV.trans inf_le_left)) (chartOpenLift_fac _ _)
      (chartOpenLift ((W j).ι) (hV.trans inf_le_right)) (chartOpenLift_fac _ _)
      hb₁ hb₂ ((quadrupleGlueData f W P hP).gluedPullbackIso i)
      ((quadrupleGlueData f W P hP).gluedPullbackIso j) (P i).twisting (P j).twisting
      (Quadruple.chartWitness f W P hP i j _ _ hab)
      (refineChartIso_trans_chartWitness f W P hP i j hV) ?_ n h₁ h₂
        ((Scheme.Hom.image_top_eq_opensRange V.ι).trans (Scheme.Opens.opensRange_ι V))
    intro m
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun z => (Scheme.Modules.pullbackCongr hb₁).hom.app (A.piece (m * d)) ≫ z)
      (Quadruple.twisting_app_comp_congrIso_witnessOver
        (Quadruple.strictlyEquivalentOver_of_common f W P hP i j _ _ hab) m)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    exact congrArg (fun z => z ≫ ((P j).pullback
        (chartOpenLift ((W j).ι) (hV.trans inf_le_right))).twisting.app m)
      (pullbackCongr_hom_app_trans hb₁ _ (A.piece (m * d)))
  -- the glued family
  have hex : ∀ n : ℤ, ∃ φ : (pullbackFunctor (ringedSpaceHom f)).obj (A.piece (n * d)) ⟶
      (laurent (quadrupleGlueData f W P hP).glued).piece n,
      ∀ a, (Scheme.Modules.restrictFunctor ((W a).ι)).map φ =
        chartLocalApp f ((W a).ι) A d (quadrupleGlueData f W P hP).glued
          ((quadrupleGlueData f W P hP).gluedPullbackIso a) (P a).twisting.app n := by
    intro n
    obtain ⟨φ, hφ, -⟩ := ModuleHomGlue.existsUnique_hom_of_restrict_cover
      (fun a => (W a).ι) hcov
      (fun a => chartLocalApp f ((W a).ι) A d (quadrupleGlueData f W P hP).glued
        ((quadrupleGlueData f W P hP).gluedPullbackIso a) (P a).twisting.app n)
      (hcompat n)
    exact ⟨φ, hφ⟩
  choose app happ using hex
  have hres := fun (a : ι) (n : ℤ) => happ n a
  refine ⟨{ L := (quadrupleGlueData f W P hP).glued
            isInvertible := inferInstance
            twisting :=
              { app := app
                app_mul := fun i j => mul_of_chartLocal_cover (fun a => (W a).ι) hg
                  (fun a => (quadrupleGlueData f W P hP).gluedPullbackIso a)
                  (fun a => (P a).twisting) app hres i j
                app_one := one_of_chartLocal_cover (fun a => (W a).ι) hg
                  (fun a => (quadrupleGlueData f W P hP).gluedPullbackIso a)
                  (fun a => (P a).twisting) app hres }
            epi_app_one := epi_of_chartLocal_cover (fun a => (W a).ι) hg
              (fun a => (quadrupleGlueData f W P hP).gluedPullbackIso a)
              (fun a => (P a).twisting) app hres 1 fun a => (P a).epi_app_one },
    fun a => ?_⟩
  refine ⟨(quadrupleGlueData f W P hP).gluedPullbackIso a,
    laurentCongrIso ((quadrupleGlueData f W P hP).gluedPullbackIso a), ?_, fun n => ?_⟩
  · exact laurentCongrIso_app_one ((quadrupleGlueData f W P hP).gluedPullbackIso a)
  · exact pullbackFamily_congrIso_of_restrictFunctor_map_eq ((W a).ι)
      ((quadrupleGlueData f W P hP).gluedPullbackIso a) app (P a).twisting.app (hres a) n

/-- **`F_d` is a sheaf on the big Zariski site**, with no hypothesis. This is step (1) of the
proof of Tag 01NV: `...RelativeProjQcohSheaf.Fd.isSheaf_functor_of_quadrupleGlues` fed with
`...RelativeProjQcohSheaf.quadrupleGlues_proof`. -/
theorem Fd.isSheaf_functor
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d : ℤ) :
    CategoryTheory.Presheaf.IsSheaf Scheme.zariskiTopology.{u} (Fd.functor A d) :=
  Fd.isSheaf_functor_of_quadrupleGlues (quadrupleGlues_proof A d)

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
