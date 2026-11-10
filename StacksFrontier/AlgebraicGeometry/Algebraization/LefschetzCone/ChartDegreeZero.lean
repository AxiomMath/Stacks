module

public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzCone.AdicQuotientSheaves
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Transition
public import StacksFrontier.AlgebraicGeometry.QuasicoherentBasicOpen.LocalSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PowerAnnihilated

/-!
# A coherent adic system on `P` read on the degree-zero localizations of graded modules

Let `X` be a scheme with an ample invertible `𝒪_X`-module `L` for which the canonical morphism
`X ⟶ Proj A`, `A = Γ_*(X, L)`, is an isomorphism, `s` a global section of `L`, `f ∈ A₁` its image
and `𝓘` the ideal of the zero scheme of `s`. Let `(Mₙ)` be an inverse system of graded
`A`-modules whose sheaves `(M̃ₙ|_X)` form an object of `Coh(X, 𝓘)`.

On a chart `X_{cb}` of consecutive degrees the sections of `M̃ₙ|_X` are the degree-zero
localization `Mₙ₍cb₎` (`Stacks.LefschetzCone.chartSectionsOf`), compatibly with the action of the
chart ring and with maps, and `𝓘` is generated there by the chart ratio `w = f b² / (cb)`. The
three defining properties of a coherent adic system become, on the sections over the affine open
`X_{cb}`:

* `wⁿ⁺¹ Mₙ₍cb₎ = 0`;
* `Mₙ₊₁₍cb₎ → Mₙ₍cb₎` is surjective;
* its kernel is `wⁿ⁺¹ Mₙ₊₁₍cb₎`.

## Main results

* `Stacks.LefschetzCone.chartRatio_pow_smul_eq_zero`
* `Stacks.LefschetzCone.exists_map_eq_of_isCoherentAdicSystem`
* `Stacks.LefschetzCone.exists_eq_chartRatio_pow_smul_of_map_eq_zero`
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.GradedSections (powSections mul sectionRing)
open Stacks.AmpleFiniteAvoidance (nvOpen grading)
open Stacks.SectionRingProjMorphism (projHomOfIsAmple)
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality
open scoped Stacks.GradedLocalization Pointwise

universe u

namespace Stacks.LefschetzCone

section Monoidal

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  (hL : Stacks.Ample.IsAmple X L) [IsIso (projHomOfIsAmple L hL)] (s : Γ(L, ⊤))

/-- The chart ratio `w = f b² / (cb)` of a chart of consecutive degrees. -/
abbrev chartRatioOf (ch : ConsecutiveChart L) :
    HomogeneousLocalization.Away (grading L) ch.gR :=
  Stacks.DegreeOneUnitAway.chartRatio ch.cR_mem ch.bR_mem ch.cR_mul_bR (sectionElt_mem L s)

/-- On a chart, the sections of `𝓘ᵏ M̃|_X` are the multiples of `eᵏ`, `e` the image of the chart
ratio. -/
theorem idealPowerMultiple_obj_consecutiveChart (N : GradedModuleCat.{u, u, u} (grading L))
    (k : ℕ) (ch : ConsecutiveChart L) :
    (Stacks.Algebraization.idealPowerMultiple (zeroScheme X L s) k
      (restrictedTilde L hL N)).obj (op ch.nv) =
      Ideal.span {Stacks.SectionRingChartMap.chartRingMap L ch.prod le_rfl
                    (chartRatioOf L s ch ^ k)} •
        (⊤ : Submodule Γ(X, ch.nv) Γ(restrictedTilde L hL N, ch.nv)) := by
  have := isQuasicoherent_restrictedTilde L hL N
  rw [show (Stacks.Algebraization.idealPowerMultiple (zeroScheme X L s) k
      (restrictedTilde L hL N)).obj (op ch.nv) =
      (Stacks.Algebraization.idealPowerMultiple (zeroScheme X L s) k
        (restrictedTilde L hL N)).toSubmodule.obj (op (ch.affineOpen hL).1) from rfl,
    Stacks.Algebraization.idealPowerMultiple_toSubmodule_obj_affine,
    zeroScheme_ideal_consecutiveChart L hL s ch, Ideal.span_singleton_pow, map_pow]

/-- **`𝓘ᵏ M̃|_X = 0` gives `wᵏ M₍cb₎ = 0`.** -/
public theorem chartRatio_pow_smul_eq_zero (N : GradedModuleCat.{u, u, u} (grading L)) (k : ℕ)
    (hN : Stacks.Algebraization.idealPowerMultiple (zeroScheme X L s) k
      (restrictedTilde L hL N) = ⊥)
    (ch : ConsecutiveChart L) (z : GradedModuleDegreeZeroLocalization (grading L) N.grade ch.gR) :
    chartRatioOf L s ch ^ k • z = 0 := by
  obtain ⟨σ, rfl⟩ := (chartSectionsOf L hL N ch.prod ch.deg_pos).surjective z
  have hmem : Stacks.SectionRingChartMap.chartRingMap L ch.prod le_rfl (chartRatioOf L s ch ^ k) •
      σ ∈ (Stacks.Algebraization.idealPowerMultiple (zeroScheme X L s) k
        (restrictedTilde L hL N)).obj (op ch.nv) := by
    rw [idealPowerMultiple_obj_consecutiveChart L hL s N k ch]
    exact (mem_span_singleton_smul_top_iff _ _).2 ⟨σ, rfl⟩
  rw [hN] at hmem
  have h0 : Stacks.SectionRingChartMap.chartRingMap L ch.prod le_rfl (chartRatioOf L s ch ^ k) •
      σ = 0 := by
    change _ ∈ (⊥ : (restrictedTilde L hL N).Submodule).toSubmodule.obj (op ch.nv) at hmem
    rwa [Stacks.Algebraization.bot_submodule_obj_eq_bot (restrictedTilde L hL N) (op ch.nv)] at hmem
  rw [← chartSectionsOf_smul L hL N ch.prod ch.deg_pos, h0, map_zero]

variable {L hL s}

/-- **Surjectivity on degree-zero localizations**, from an epimorphism of the sheaves. -/
public theorem exists_map_eq_of_epi {N N' : GradedModuleCat.{u, u, u} (grading L)} (φ : N ⟶ N')
    [Epi ((restrictedTildeFunctor L hL).map φ)] (ch : ConsecutiveChart L)
    (z : GradedModuleDegreeZeroLocalization (grading L) N'.grade ch.gR) :
    ∃ z' : GradedModuleDegreeZeroLocalization (grading L) N.grade ch.gR,
      LocalizedModule.map (Submonoid.powers ch.gR) φ.toLinearMap
        (z' : LocalizedModule.Away ch.gR N.carrier) = z := by
  have : ((restrictedTildeFunctor L hL).obj N).IsQuasicoherent :=
    isQuasicoherent_restrictedTilde L hL N
  have : ((restrictedTildeFunctor L hL).obj N').IsQuasicoherent :=
    isQuasicoherent_restrictedTilde L hL N'
  obtain ⟨σ, rfl⟩ := (chartSectionsOf L hL N' ch.prod ch.deg_pos).surjective z
  obtain ⟨σ', hσ'⟩ := AlgebraicGeometry.surjective_app_of_epi_of_isAffineOpen
    ((restrictedTildeFunctor L hL).map φ) (ch.isAffineOpen_nv hL) σ
  refine ⟨chartSectionsOf L hL N ch.prod ch.deg_pos σ', ?_⟩
  rw [← coe_chartSectionsOf_map L hL φ ch.prod ch.deg_pos σ']
  exact congrArg (fun t => ((chartSectionsOf L hL N' ch.prod ch.deg_pos t :
    GradedModuleDegreeZeroLocalization (grading L) N'.grade ch.gR) :
      LocalizedModule.Away ch.gR N'.carrier)) hσ'

/-- **Injectivity on degree-zero localizations**, from an isomorphism of the sheaves. -/
public theorem eq_zero_of_map_eq_zero_of_isIso {N N' : GradedModuleCat.{u, u, u} (grading L)}
    (φ : N ⟶ N') [IsIso ((restrictedTildeFunctor L hL).map φ)] (ch : ConsecutiveChart L)
    (z : GradedModuleDegreeZeroLocalization (grading L) N.grade ch.gR)
    (hz : LocalizedModule.map (Submonoid.powers ch.gR) φ.toLinearMap
      (z : LocalizedModule.Away ch.gR N.carrier) = 0) : z = 0 := by
  obtain ⟨σ, rfl⟩ := (chartSectionsOf L hL N ch.prod ch.deg_pos).surjective z
  have h1 : chartSectionsOf L hL N' ch.prod ch.deg_pos
      (((restrictedTildeFunctor L hL).map φ).app _ σ) = 0 := by
    apply Subtype.ext
    rw [coe_chartSectionsOf_map L hL φ ch.prod ch.deg_pos σ, hz, Submodule.coe_zero]
  have h2 : ((restrictedTildeFunctor L hL).map φ).app _ σ = 0 :=
    (chartSectionsOf L hL N' ch.prod ch.deg_pos).injective (h1.trans (map_zero _).symm)
  have h3 : σ = 0 := by
    have := congrArg ((inv ((restrictedTildeFunctor L hL).map φ)).app (nvOpen L ch.prod)) h2
    rwa [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, IsIso.hom_inv_id,
      Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply, map_zero] at this
  rw [h3, map_zero]

variable (L hL s)

/-- **The kernel of a transition on degree-zero localizations.** For an inverse system of graded
modules whose sheaves form a coherent adic system along `𝓘`, a degree-zero fraction of `Mₙ₊₁`
killed by the transition is `wⁿ⁺¹` times a degree-zero fraction. -/
public theorem exists_eq_chartRatio_pow_smul_of_map_eq_zero
    (M : ℕᵒᵖ ⥤ GradedModuleCat.{u, u, u} (grading L))
    (hM : Stacks.Coherent.IsCoherentAdicSystem (zeroScheme X L s)
      (M ⋙ restrictedTildeFunctor L hL)) (n : ℕ) (ch : ConsecutiveChart L)
    (z : GradedModuleDegreeZeroLocalization (grading L) (M.obj (op (n + 1))).grade ch.gR)
    (hz : LocalizedModule.map (Submonoid.powers ch.gR)
      (M.map (homOfLE (Nat.le_succ n)).op).toLinearMap
        (z : LocalizedModule.Away ch.gR (M.obj (op (n + 1))).carrier) = 0) :
    ∃ z' : GradedModuleDegreeZeroLocalization (grading L) (M.obj (op (n + 1))).grade ch.gR,
      z = chartRatioOf L s ch ^ (n + 1) • z' := by
  set t := M.map (homOfLE (Nat.le_succ n)).op
  obtain ⟨σ, rfl⟩ := (chartSectionsOf L hL (M.obj (op (n + 1))) ch.prod ch.deg_pos).surjective z
  have h1 : chartSectionsOf L hL (M.obj (op n)) ch.prod ch.deg_pos
      (((restrictedTildeFunctor L hL).map t).app _ σ) = 0 := by
    apply Subtype.ext
    rw [coe_chartSectionsOf_map L hL t ch.prod ch.deg_pos σ, hz, Submodule.coe_zero]
  have h2 : ((restrictedTildeFunctor L hL).map t).app _ σ = 0 :=
    (chartSectionsOf L hL (M.obj (op n)) ch.prod ch.deg_pos).injective
      (h1.trans (map_zero _).symm)
  have h3 : (cokernel.π (C := X.Modules) (Stacks.Algebraization.idealPowerMultiple
      (zeroScheme X L s) (n + 1) (restrictedTilde L hL (M.obj (op (n + 1))))).ι).app _ σ = 0 := by
    have h5 : cokernel.π (C := X.Modules) (Stacks.Algebraization.idealPowerMultiple
        (zeroScheme X L s) (n + 1) (restrictedTilde L hL (M.obj (op (n + 1))))).ι =
        (restrictedTildeFunctor L hL).map t ≫ (hM.quotientIso n).inv :=
      (Iso.eq_comp_inv _).2 (hM.cokernel_π_comp_quotientIso n)
    exact (congrArg (fun φ => (Scheme.Modules.Hom.app φ (nvOpen L ch.prod)) σ) h5).trans
      ((congrArg ((hM.quotientIso n).inv.app (nvOpen L ch.prod)) h2).trans (map_zero _))
  have hmem' : σ ∈ (Stacks.Algebraization.idealPowerMultiple (zeroScheme X L s) (n + 1)
      (restrictedTilde L hL (M.obj (op (n + 1))))).obj (op ch.nv) :=
    (Stacks.Algebraization.cokernel_π_app_eq_zero_iff _ _ _ σ).1 h3
  rw [idealPowerMultiple_obj_consecutiveChart L hL s _ (n + 1) ch] at hmem'
  obtain ⟨σ', hσ'⟩ := (mem_span_singleton_smul_top_iff _ _).1 hmem'
  refine ⟨chartSectionsOf L hL (M.obj (op (n + 1))) ch.prod ch.deg_pos σ', ?_⟩
  rw [← hσ', chartSectionsOf_smul]

variable {L} in
include hL in
/-- **Every prime off `V(A₊)` misses the product of a chart of consecutive degrees.** Its
homogeneous core is a point of `Proj A`, which is a point of `X`, and the charts of consecutive
degrees cover `X`. -/
public theorem exists_consecutiveChart_notMem (p : Ideal (sectionRing L)) (hpp : p.IsPrime)
    (hp : ¬ (HomogeneousIdeal.irrelevant (grading L)).toIdeal ≤ p) :
    ∃ ch : ConsecutiveChart L, ch.gR ∉ p := by
  let P := p.homogeneousCore (grading L)
  have hrel : ¬ HomogeneousIdeal.irrelevant (grading L) ≤ P := fun h => hp <| by
    rw [HomogeneousIdeal.toIdeal_irrelevant_le]
    exact fun i hi x hx =>
      Ideal.toIdeal_homogeneousCore_le _ _ ((HomogeneousIdeal.irrelevant_le _).1 h i hi hx)
  let x₀ : ProjectiveSpectrum (grading L) := ⟨P, hpp.homogeneousCore, hrel⟩
  let x : X := (inv (projHomOfIsAmple L hL)).base x₀
  have hx : (projHomOfIsAmple L hL).base x = x₀ := by
    change (inv (projHomOfIsAmple L hL) ≫ projHomOfIsAmple L hL).base x₀ = x₀
    rw [IsIso.inv_hom_id]
    rfl
  obtain ⟨_, ⟨ch, rfl⟩, hxch, -⟩ := (Opens.isBasis_iff_nbhd.mp (isBasis_consecutiveChart L hL))
    (show x ∈ (⊤ : X.Opens) from trivial)
  refine ⟨ch, fun hg => ?_⟩
  have h1 : x ∈ projHomOfIsAmple L hL ⁻¹ᵁ Proj.basicOpen (grading L) ch.gR := by
    rw [Stacks.SectionRingProjMorphism.projHomOfIsAmple_preimage_projBasicOpen L hL ch.prod
      ch.deg_pos]
    exact hxch
  have h2 : (projHomOfIsAmple L hL).base x ∈ Proj.basicOpen (grading L) ch.gR := h1
  rw [hx] at h2
  exact h2 (Ideal.mem_homogeneousCore_of_homogeneous_of_mem
    ⟨_, Stacks.ExternalGrading.of_mem_summand _ ch.prod⟩ hg)

end Monoidal

end Stacks.LefschetzCone

end
