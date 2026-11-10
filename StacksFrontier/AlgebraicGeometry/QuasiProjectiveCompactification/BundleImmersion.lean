module

public import StacksFrontier.AlgebraicGeometry.QuasiProjectiveCompactification.ChartImmersion
public import StacksFrontier.AlgebraicGeometry.QuasiProjectiveCompactification.FiniteTypeLift
public import StacksFrontier.AlgebraicGeometry.QuasiProjectiveCompactification.GlobalImmersion
public import StacksFrontier.AlgebraicGeometry.QuasiProjectiveCompactification.SymLift

/-!
# An immersion into the projective bundle of a finite-type module, from local immersions

Let `f : X ⟶ S` be a morphism to a quasi-compact quasi-separated scheme, `𝒜` a quasi-coherent
graded `𝒪_S`-algebra and `P = (L, ψ)` a graded map `f^*𝒜 ⟶ ⨁_{d ≥ 0} L^{⊗ d}` ([Stacks, Tag
01O8]). Suppose `S` is covered by finitely many affine opens `V_j`, and over each `V_j` there is a
generating family of global sections of `L|_{f⁻¹(V_j)}` — read through an isomorphism of invertible
modules — whose pinned morphism `f⁻¹(V_j) ⟶ ℙⁿ_{V_j}` is an immersion, every section of the family
being the value of `ψ` on a section of `𝒜₁` over `V_j`. Then there are a quasi-coherent
`𝒪_S`-module `ℰ` of finite type and an immersion `X ⟶ 𝐏(ℰ)` over `S`.

This is half 1 of the proof of [Stacks, Tag 07RM]: the source takes `𝒜₁ = f_*L`, writes it as a
directed colimit of finite-type modules ([Stacks, Tag 01PK]), chooses a stage `ℰ` through which the
finitely many sections `s_{j,t}` factor, and maps `X` to `𝐏(ℰ)` by the surjection `f^*ℰ ⟶ L`. Here
the stage is `Stacks.QuasiProjectiveCompactification.exists_isFiniteType_hom_lift`, the map
`Sym(ℰ) ⟶ 𝒜` extending `ℰ ⟶ 𝒜₁` is `Stacks.QuasiProjectiveCompactification.symLift`, and the
morphism `X ⟶ 𝐏(ℰ)` is the morphism `r_{L, ψ'}` of [Stacks, Tag 01O9] for the composite graded map
`ψ'`, which
`Stacks.QuasiProjectiveCompactification.isImmersion_globalMorphism_of_chartsAreImmersions`
and `Stacks.QuasiProjectiveCompactification.isImmersion_toSpecAway` show to be an immersion.

## Main results

* `Stacks.QuasiProjectiveCompactification.exists_isImmersion_projectiveBundle_of_cover`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.Ample Stacks.ProjectiveFromSections
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism
open Stacks.AlgebraicGeometry.ProjChartFullGraded
open Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul (restrictPowSection)
open Stacks.TensorPowers (natTensorPow)
open Stacks.SymGraded

universe u

namespace Stacks.QuasiProjectiveCompactification

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {S X : Scheme.{u}} {B : SheafGradedAlgebra.{u} S} {f : X ⟶ S} (P : GradedPowerMap B f)

/-- **The charts of `r_{L, ψ}` at degree-one sections are immersions covering `X`** as soon as
over each member `V_j` of an affine open covering of the base the values `ψ(a_{j,k})` of
degree-one sections are carried by an isomorphism `Φ_j` of invertible modules to a generating
family `t_j` whose pinned morphism `f⁻¹(V_j) ⟶ ℙⁿ_{V_j}` is an immersion. No finiteness of the
covering and no hypothesis on the base is used. -/
theorem chartsAreImmersions_of_cover {A : SheafGradedAlgebra.{u} S} (Q : GradedPowerMap A f)
    {ι : Type*} (V : ι → S.Opens) (hV : ∀ j, IsAffineOpen (V j))
    (hcov : ⨆ j, V j = ⊤) (n : ι → ℕ) (N : ∀ j, (f ⁻¹ᵁ V j).toScheme.Modules)
    [∀ j, IsInvertibleModule (f ⁻¹ᵁ V j).toScheme (N j)]
    (t : ∀ j, Fin (n j + 1) → Γ(N j, ⊤)) (ht : ∀ j, GeneratesStalks (t j))
    (himm : ∀ j (p : (f ⁻¹ᵁ V j).toScheme ⟶ projectiveSpaceOver (n j) (V j).toScheme),
      p ≫ pullback.fst (terminal.from _) (terminal.from (projectiveSpaceAtUniverse.{u} (n j))) =
        f ∣_ V j →
      (∀ i, (nvCover (t j) i).ι ≫ p ≫ projectiveSpaceOver.toIntegralAtUniverse (n j) _ =
        Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse (chartRatio (t j) i)
          (span_range_chartRatio (t j) i)) →
      IsImmersion p)
    (Φ : ∀ j, natTensorPow ((Scheme.Modules.pullback (f ⁻¹ᵁ V j).ι).obj Q.L) 1 ≅ N j)
    (a : ∀ j, Fin (n j + 1) → A.grading (V j) 1)
    (hval : ∀ j k, (Φ j).hom.app ⊤ ((Q.affineDatum (V j)).toFun 1 (a j k)) = t j k) :
    ChartsAreImmersions Q := by
    intro x
    obtain ⟨j, hj⟩ : ∃ j, f x ∈ V j := by
      have hx : f x ∈ (⨆ j, V j) := hcov ▸ trivial
      simpa [Opens.mem_iSup] using hx
    let x' : (f ⁻¹ᵁ V j).toScheme := ⟨x, hj⟩
    obtain ⟨i, hi⟩ := exists_mem_nvCover_of_generatesStalks (t j) (ht j) x'
    obtain ⟨p, hpf, hchart⟩ :=
      Stacks.ProjGlobalSectionsAppTop.exists_hom_projectiveSpaceOver_of_generatesStalks (t j)
        (ht j) (f ∣_ V j)
    have hW := nonvanishingOpen_eq_nvCover (Q.affineDatum (V j)) (Φ j) (a j) i (t j) (hval j)
    have hi' : x' ∈ chartOpen Q (a j i).2 := by
      change x' ∈ NonvanishingOpen.nonvanishingOpen _ _ ((Q.affineDatum (V j)).toFun 1 (a j i))
      rw [hW]; exact hi
    refine ⟨V j, hV j, (a j i : A.sectionRing (V j)), (a j i).2, ⟨x', hi'⟩, rfl, ?_⟩
    refine isImmersion_toSpecAway (Q.affineDatum (V j)) (Φ j) (a j) i le_rfl (t j) (hval j)
      (f ∣_ V j) p (himm j p hpf hchart) hpf (hchart i)
      (AlgebraicGeometry.Proj.awayι (A.grading (V j)) _ (a j i).2 one_pos ≫
        projInclusionToOpen A (V j) (hV j)) ?_
    rw [← cancel_mono (V j).ι, Category.assoc, Category.assoc, Category.assoc,
      morphismRestrict_ι, ← Category.assoc]
    exact chartToProj_comp_projInclusionToOpen_ι (hV j) (Q.affineDatum (V j))
      ((f ⁻¹ᵁ V j).ι ≫ f) (preimage_ι_comp_eq_top f (V j))
      (Q.affineDatum_toFun_gradeZeroHom (V j)) (a j i).2 one_pos le_rfl

/-- **Half 1 of the proof of [Stacks, Tag 07RM], from the local data.** See the module
documentation. -/
theorem exists_isImmersion_projectiveBundle_of_cover [CompactSpace S] [QuasiSeparatedSpace S]
    {ι : Type u} [Finite ι] (V : ι → S.Opens) (hV : ∀ j, IsAffineOpen (V j))
    (hcov : ⨆ j, V j = ⊤) (n : ι → ℕ) (N : ∀ j, (f ⁻¹ᵁ V j).toScheme.Modules)
    [∀ j, IsInvertibleModule (f ⁻¹ᵁ V j).toScheme (N j)]
    (t : ∀ j, Fin (n j + 1) → Γ(N j, ⊤)) (ht : ∀ j, GeneratesStalks (t j))
    (himm : ∀ j (p : (f ⁻¹ᵁ V j).toScheme ⟶ projectiveSpaceOver (n j) (V j).toScheme),
      p ≫ pullback.fst (terminal.from _) (terminal.from (projectiveSpaceAtUniverse.{u} (n j))) =
        f ∣_ V j →
      (∀ i, (nvCover (t j) i).ι ≫ p ≫ projectiveSpaceOver.toIntegralAtUniverse (n j) _ =
        Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse (chartRatio (t j) i)
          (span_range_chartRatio (t j) i)) →
      IsImmersion p)
    (Φ : ∀ j, natTensorPow ((Scheme.Modules.pullback (f ⁻¹ᵁ V j).ι).obj P.L) 1 ≅ N j)
    (hsurj : ∀ j (y : Γ(N j, ⊤)), ∃ σ : Γ(B.piece 1, V j),
      (Φ j).hom.app ⊤ (restrictPowSection P.L (f ⁻¹ᵁ V j) 1 (P.value 1 (V j) σ)) = y) :
    ∃ (E : S.Modules) (_ : E.IsQuasicoherent) (_ : E.IsFiniteType)
      (i : X ⟶ (schemeProjectiveBundle E (isQuasicoherentPieces_of_isQuasicoherent E)).scheme),
      IsImmersion i ∧
        i ≫ (schemeProjectiveBundle E (isQuasicoherentPieces_of_isQuasicoherent E)).toBase = f := by
  classical
  choose σ hσ using fun jk : (Σ j, Fin (n j + 1)) => hsurj jk.1 (t jk.1 jk.2)
  obtain ⟨E, hEq, hEft, u, e, hue⟩ := exists_isFiniteType_hom_lift (B.piece 1)
    (fun jk : (Σ j, Fin (n j + 1)) => V jk.1) (fun jk => hV jk.1) σ
  let A := Stacks.Tag01VMRelativeVeryAmple.symAlgebra E
  let Q : GradedPowerMap A f := P.precomp (symLift E B u)
  let rp := schemeProjectiveBundle E (isQuasicoherentPieces_of_isQuasicoherent E)
  let a : ∀ j, Fin (n j + 1) → A.grading (V j) 1 := fun j k =>
    (A.componentEquiv (V j) 1).symm
      (Scheme.Modules.Hom.app (Scheme.Modules.symmetricAlgebraGen S E) (V j) (e ⟨j, k⟩))
  have hval : ∀ j k, (Φ j).hom.app ⊤ ((Q.affineDatum (V j)).toFun 1 (a j k)) = t j k := by
    intro j k
    rw [GradedPowerMap.affineDatum_toFun_apply]
    have h1 : A.componentEquiv (V j) 1 (a j k) =
        Scheme.Modules.Hom.app (Scheme.Modules.symmetricAlgebraGen S E) (V j) (e ⟨j, k⟩) :=
      AddEquiv.apply_symm_apply _ _
    rw [h1]
    change (Φ j).hom.app ⊤ (restrictPowSection P.L (f ⁻¹ᵁ V j) 1 (P.value 1 (V j)
      (((symLift E B u).app 1).app (V j)
        (Scheme.Modules.Hom.app (Scheme.Modules.symmetricAlgebraGen S E) (V j) (e ⟨j, k⟩))))) = _
    rw [symLift_app_one_symmetricAlgebraGen, hue ⟨j, k⟩]
    exact hσ ⟨j, k⟩
  have hcharts : ChartsAreImmersions Q :=
    chartsAreImmersions_of_cover Q V hV hcov n N t ht himm Φ a hval
  have hcovQ := coveringOpen_eq_top_of_chartsAreImmersions Q hcharts
  have himmQ := isImmersion_globalMorphism_of_chartsAreImmersions Q rp hcharts
  refine ⟨E, hEq, hEft, X.topIso.inv ≫ (X.isoOfEq hcovQ).inv ≫ Q.globalMorphism rp, ?_, ?_⟩
  · infer_instance
  · rw [Category.assoc, Category.assoc, Q.globalMorphism_comp_toBase rp, GradedPowerMap.toBase,
      ← Category.assoc (X.isoOfEq hcovQ).inv, Scheme.isoOfEq_inv_ι, ← Category.assoc,
      Scheme.toIso_inv_ι, Category.id_comp]

end Stacks.QuasiProjectiveCompactification

end
