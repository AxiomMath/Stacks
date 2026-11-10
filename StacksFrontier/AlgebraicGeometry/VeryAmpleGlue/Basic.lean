module

public import StacksFrontier.AlgebraicGeometry.VeryAmpleGlue.TwistPullback
public import StacksFrontier.AlgebraicGeometry.QuasiProjectiveCompactification.ChartImmersion
public import StacksFrontier.AlgebraicGeometry.QuasiProjectiveCompactification.GlobalImmersion
public import StacksFrontier.AlgebraicGeometry.QuasiProjectiveCompactification.SymLift
public import StacksFrontier.AlgebraicGeometry.HProjective.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiProjectiveCompactification.BundleImmersion
public import StacksFrontier.AlgebraicGeometry.QuasiProjectiveCompactification.SectionTransport
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.DirectImageAlgebra

/-!
# Gluing relative very ampleness over an affine covering of the base

Let `f : X ⟶ S` be quasi-compact and `M` an invertible `𝒪_X`-module. Suppose `S` is covered by
affine opens `V_j` and that over each `V_j` the restriction of `M` to `f⁻¹(V_j)` (read through an
isomorphism `Φ_j` with a module `N_j`) has a finite generating family of global sections whose
pinned morphism `f⁻¹(V_j) ⟶ ℙ^{n_j}_{V_j}` over `V_j` is an immersion. Then `M` is very ample
relative to `f` in the sense of [Stacks, Tag 01VM]. This is [Stacks, Tag 01VR], (2) ⟹ (1), for
members carrying immersions into projective space.

## Main results

* `Stacks.VeryAmpleGlue.isSeparated_of_generatesStalks`: a morphism with such a family is
  separated.
* `Stacks.VeryAmpleGlue.isRelativelyVeryAmple_of_cover`: if the restrictions of `M` over an affine
  covering of `S` have such families, then `M` is very ample relative to `f`.

## References

* [Stacks Project, Tag 01VR](https://stacks.math.columbia.edu/tag/01VR)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
* [Stacks Project, Tag 01VQ](https://stacks.math.columbia.edu/tag/01VQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.Ample Stacks.ProjectiveFromSections
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism
open Stacks.TensorPowers (natTensorPow)

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

/-- A morphism admitting an immersion into `ℙⁿ` over its target, pinned by a generating family of
sections, is separated. -/
theorem isSeparated_of_generatesStalks (g : X ⟶ S) {L : X.Modules} [IsInvertibleModule X L]
    {n : ℕ} (t : Fin (n + 1) → Γ(L, ⊤)) (ht : GeneratesStalks t)
    (himm : ∀ p : X ⟶ projectiveSpaceOver n S,
      p ≫ pullback.fst (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} n)) = g →
      (∀ i, (nvCover t i).ι ≫ p ≫ projectiveSpaceOver.toIntegralAtUniverse n S =
        Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse (chartRatio t i)
          (span_range_chartRatio t i)) →
      IsImmersion p) :
    IsSeparated g := by
  obtain ⟨p, hpf, hchart⟩ :=
    Stacks.ProjGlobalSectionsAppTop.exists_hom_projectiveSpaceOver_of_generatesStalks t ht g
  have := himm p hpf hchart
  rw [← hpf]
  infer_instance

/-- **Gluing relative very ampleness over an affine open covering of the base.** Let
`f : X ⟶ S` be quasi-compact, `M` an invertible `𝒪_X`-module and `V_j` affine opens covering `S`.
Suppose that for every `j` the module `M|_{f⁻¹(V_j)}` is identified by `Φ_j` with a module `N_j`
having a generating family `t_j` of global sections such that every morphism
`f⁻¹(V_j) ⟶ ℙ^{n_j}_{V_j}` over `V_j` pinned by `t_j` is an immersion. Then `M` is very ample
relative to `f`. -/
theorem isRelativelyVeryAmple_of_cover (f : X ⟶ S) (M : X.Modules) [IsInvertibleModule X M]
    [QuasiCompact f] {ι : Type*} (V : ι → S.Opens) (hV : ∀ j, IsAffineOpen (V j))
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
    (Φ : ∀ j, natTensorPow ((Scheme.Modules.pullback (f ⁻¹ᵁ V j).ι).obj M) 1 ≅ N j) :
    Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f M := by
  classical
  have hsep : IsSeparated f :=
    IsZariskiLocalAtTarget.of_iSup_eq_top V hcov fun j =>
      isSeparated_of_generatesStalks (f ∣_ V j) (t j) (ht j) (himm j)
  let B := Stacks.RelativeAmple.directImageAlgebra f M
  let E : S.Modules :=
    (Scheme.Modules.pushforward f).obj (Stacks.AmpleProjectiveImmersion.tensorPowerModule X M 1)
  have : E.IsQuasicoherent := Stacks.RelativeAmple.isQuasicoherent_pushforward_laurentPowers f M 1
  let A := Stacks.Tag01VMRelativeVeryAmple.symAlgebra E
  let Q : GradedPowerMap A f :=
    (Stacks.RelativeAmple.directImagePowerMap f M).precomp
      (Stacks.QuasiProjectiveCompactification.symLift E B (𝟙 E))
  have hσ : ∀ j k, ∃ σ : Γ(E, V j), (Φ j).hom.app ⊤
      (Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictPowSection M (f ⁻¹ᵁ V j) 1
        ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare M 1).inv.app (f ⁻¹ᵁ V j) σ)) =
        t j k := by
    intro j k
    obtain ⟨z, hz⟩ := Stacks.QuasiProjectiveCompactification.restrictPowSection_surjective M
      (f ⁻¹ᵁ V j) 1 ((Φ j).inv.app ⊤ (t j k))
    refine ⟨(Stacks.AlgebraicGeometry.CoherentMulSections.powCompare M 1).hom.app (f ⁻¹ᵁ V j) z,
      ?_⟩
    have h1 : (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare M 1).inv.app (f ⁻¹ᵁ V j)
        ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare M 1).hom.app (f ⁻¹ᵁ V j) z) =
          z :=
      Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.hom_app_inv_app
        (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare M 1).symm (f ⁻¹ᵁ V j) z
    rw [h1, hz, Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.hom_app_inv_app]
  choose σ hσ using hσ
  let a : ∀ j, Fin (n j + 1) → A.grading (V j) 1 := fun j k =>
    (A.componentEquiv (V j) 1).symm
      (Scheme.Modules.Hom.app (Scheme.Modules.symmetricAlgebraGen S E) (V j) (σ j k))
  have hval : ∀ j k, (Φ j).hom.app ⊤ ((Q.affineDatum (V j)).toFun 1 (a j k)) = t j k := by
    intro j k
    have h1 : A.componentEquiv (V j) 1 (a j k) =
        Scheme.Modules.Hom.app (Scheme.Modules.symmetricAlgebraGen S E) (V j) (σ j k) :=
      AddEquiv.apply_symm_apply _ _
    rw [GradedPowerMap.affineDatum_toFun_apply, h1]
    change (Φ j).hom.app ⊤
      (Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictPowSection M (f ⁻¹ᵁ V j) 1
        ((Stacks.RelativeAmple.directImagePowerMap f M).value 1 (V j)
          (((Stacks.QuasiProjectiveCompactification.symLift E B (𝟙 E)).app 1).app (V j)
            (Scheme.Modules.Hom.app (Scheme.Modules.symmetricAlgebraGen S E) (V j) (σ j k))))) = _
    rw [Stacks.QuasiProjectiveCompactification.symLift_app_one_symmetricAlgebraGen E B (𝟙 E)]
    exact hσ j k
  have hcharts := Stacks.QuasiProjectiveCompactification.chartsAreImmersions_of_cover Q V hV hcov
    n N t ht himm Φ a hval
  have hcovQ := Stacks.QuasiProjectiveCompactification.coveringOpen_eq_top_of_chartsAreImmersions Q
    hcharts
  have himmQ :=
    Stacks.QuasiProjectiveCompactification.isImmersion_globalMorphism_of_chartsAreImmersions
      Q (relativeProj A) hcharts
  have hgen : ∀ x : Q.coveringOpen.toScheme, ∃ (W : S.Opens) (b : Γ(A.piece ((1 : ℕ) : ℤ), W)),
      Q.coveringOpen.ι.base x ∈ Q.nonvanishingOpenAt 1 W b := by
    intro x
    obtain ⟨W, hW, g, hg, x', hx', -⟩ := hcharts (Q.coveringOpen.ι x)
    refine ⟨W, A.componentEquiv W 1 ⟨g, hg⟩, ?_⟩
    rw [← hx']
    exact (Q.nonvanishingOpenAt_affineDatum W 1 ⟨g, hg⟩).le x'.2
  let r := X.topIso.inv ≫ (X.isoOfEq hcovQ).inv ≫ Q.globalMorphism (relativeProj A)
  refine Stacks.Tag01VMVeryAmple.isRelativelyVeryAmple_of_immersion f M E r inferInstance ?_
    (Stacks.VeryAmpleGlue.pullbackTwistOneIso Q hcovQ hgen)
  rw [Category.assoc, Category.assoc, Q.globalMorphism_comp_toBase (relativeProj A),
    GradedPowerMap.toBase, ← Category.assoc (X.isoOfEq hcovQ).inv, Scheme.isoOfEq_inv_ι,
    ← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp]

end Stacks.VeryAmpleGlue

end
