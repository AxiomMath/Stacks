module

public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzCone.ConeProIso
public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzCone.ConeDistance
public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzCone.ConeVertex
public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzCone.ConeDepthArith
public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzCone.ChartStalk
public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzZeroSchemeImprovementHypotheses
public import StacksFrontier.RingTheory.GradedAlgebra.Proj.ConeDepth
public import StacksFrontier.RingTheory.GradedAlgebra.Proj.ConeDimension
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.FinitenessDepthCriterionDualizing
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.CanonicalExtensionDepthThree
public import StacksFrontier.AlgebraicGeometry.RelativeProjFiniteType.ModuleFinite
public import StacksFrontier.AlgebraicGeometry.ProperAmpleCohomology.SerreFiniteness
public import StacksFrontier.AlgebraicGeometry.Algebraization.BoundaryFlag
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.ImprovingFormalModulesDepthThree

/-!
# Depth plus distance on the punctured cone

Let `X` be proper over a field `k` with an ample invertible `L`, `A = Γ_*(X, L)`, `f ∈ A₁` a
section, and `U` the punctured spectrum of `A` (the punctured affine cone). For a quasi-coherent
`𝒪_X`-module `G` with `Γ_*(X, L, G)` finite whose stalks at points `x` of `Z(f)` satisfy
`depth(G_x) ≥ 1` if `dim({x}‾) ≤ 1` and `depth(G_x) ≥ 2` if `dim({x}‾) = 0`, the module
`Ψ(G) = Γ_*(X, L, G)~|_U` satisfies `depth(Ψ(G)_y) + δ(y) ≥ 3` at every point `y` of `U ∩ V(f)`.

This is the depth hypothesis of Stacks 0EJI in the proof of Stacks 0EL5. At `y = 𝔭` the point
`x ∈ X` is the homogeneous core `𝔭*` of `𝔭`; on a chart `A₍g₎` of consecutive degrees around `x`
the stalk depth `depth(G_x)` is that of `Γ_*(G)₍g₎` at the prime `𝔮` of `A₍g₎` under `𝔭`, and
`depth(Ψ(G)_𝔭) ≥ depth(G_x) + [𝔭 ≠ 𝔭*]`; on the other side `δ(𝔭) ≥ dim(A/𝔭) ≥ dim({x}‾)`, with one
more when `𝔭 = 𝔭*`.

## Main results

* `Stacks.LefschetzCone.three_le_depthOfStalkOnOpen_coneFunctor_add_distanceToZ`
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace IsLocalRing
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

/-- The depth of a localization depends only on the prime, not on how it is written. -/
theorem depth_localizedModule_congr {R : Type u} [CommRing R] (N : Type u) [AddCommGroup N]
    [Module R N] {q q' : Ideal R} [q.IsPrime] [q'.IsPrime] (h : q = q') :
    Module.depth (Localization.AtPrime q) (maximalIdeal (Localization.AtPrime q))
        (LocalizedModule q.primeCompl N) =
      Module.depth (Localization.AtPrime q') (maximalIdeal (Localization.AtPrime q'))
        (LocalizedModule q'.primeCompl N) := by
  subst h
  rfl

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  (hL : Stacks.Ample.IsAmple X L) [IsIso (projHomOfIsAmple L hL)] (s : Γ(L, ⊤))
  [IsNoetherianRing (sectionRing L)] [IsLocallyNoetherian X]

include hL in
/-- **`depth(Ψ(G)_y) + δ(y) ≥ 3` on `U ∩ V(f)`**, for `G` quasi-coherent with finite twisted
sections whose stalks have depth `≥ 1` at the points of `Z(s)` with closure of dimension `≤ 1`
and depth `≥ 2` at the closed points of `Z(s)`. -/
theorem three_le_depthOfStalkOnOpen_coneFunctor_add_distanceToZ {k : Type u} [Field k]
    (fX : X ⟶ Spec (CommRingCat.of k)) [IsProper fX]
    (G : X.Modules) [G.IsQuasicoherent]
    (hfin : Module.Finite (sectionRing L) (Stacks.TwistedSections.twistModule G L))
    (hG : ∀ x : X,
      letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) G.val x
      (x ∈ Stacks.Algebraization.zeroSchemeClosureDimLE L s 1 → (1 : ℕ∞) ≤
          Module.depth (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))
            (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x)) ∧
        (x ∈ Stacks.Algebraization.zeroSchemeClosureDimLE L s 0 → (2 : ℕ∞) ≤
          Module.depth (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))
            (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x)))
    (y : (coneSituation L s).U.toScheme) (z : (coneSituation L s).Y)
    (hyz : (coneSituation L s).U.ι.base y = (coneSituation L s).Yι.base z) :
    3 ≤ Stacks.Algebraization.depthOfStalkOnOpen (coneSituation L s) ((coneFunctor L s).obj G) y +
      (coneSituation L s).distanceToZ z := by
  classical
  -- the prime `𝔭` of `A` under `y`, containing `f`
  set p : Ideal (sectionRing L) := ((coneSituation L s).U.ι.base y).asIdeal with hp_def
  have hpp : p.IsPrime := ((coneSituation L s).U.ι.base y).isPrime
  have hpirr : ¬ (HomogeneousIdeal.irrelevant (grading L)).toIdeal ≤ p :=
    not_irrelevant_le_coneSituation L s y
  have hfp : sectionElt L s ∈ p := by
    have hz : (coneSituation L s).Yι.base z ∈ Set.range (coneSituation L s).Yι.base := ⟨z, rfl⟩
    rw [Stacks.Algebraization.range_Yι_base] at hz
    show sectionElt L s ∈ ((coneSituation L s).U.ι.base y).asIdeal
    rw [show (coneSituation L s).U.ι.base y = (coneSituation L s).Yι.base z from hyz]
    exact (PrimeSpectrum.mem_zeroLocus _ _).1 hz (Ideal.mem_span_singleton_self _)
  -- its homogeneous core `𝔭*`, a point `x` of `X`
  set P := p.homogeneousCore (grading L) with hP_def
  have hPprime : P.toIdeal.IsPrime := hpp.homogeneousCore
  have hrel : ¬ HomogeneousIdeal.irrelevant (grading L) ≤ P := by
    intro h
    apply hpirr
    rw [HomogeneousIdeal.toIdeal_irrelevant_le]
    intro i hi a ha
    exact Ideal.toIdeal_homogeneousCore_le _ _ (((HomogeneousIdeal.irrelevant_le _).1 h) i hi ha)
  let x₀ : ProjectiveSpectrum (grading L) := ⟨P, hPprime, hrel⟩
  let x : X := (inv (projHomOfIsAmple L hL)).base x₀
  have hx : (projHomOfIsAmple L hL).base x = x₀ := by
    show (inv (projHomOfIsAmple L hL) ≫ projHomOfIsAmple L hL).base x₀ = x₀
    rw [IsIso.inv_hom_id]
    rfl
  -- a chart `X_g` of consecutive degrees around `x`
  obtain ⟨_, ⟨ch, rfl⟩, hxch, -⟩ := (Opens.isBasis_iff_nbhd.mp (isBasis_consecutiveChart L hL))
    (show x ∈ (⊤ : X.Opens) from trivial)
  have hgP : ch.gR ∉ P := by
    have h1 : x ∈ projHomOfIsAmple L hL ⁻¹ᵁ Proj.basicOpen (grading L) ch.gR := by
      rw [Stacks.SectionRingProjMorphism.projHomOfIsAmple_preimage_projBasicOpen L hL ch.prod
        ch.deg_pos]
      exact hxch
    have h3 : (projHomOfIsAmple L hL).base x ∈ Proj.basicOpen (grading L) ch.gR := h1
    rw [hx] at h3
    exact h3
  have hgp : ch.gR ∉ p := fun hg => hgP (Ideal.mem_homogeneousCore_of_homogeneous_of_mem
    ⟨_, Stacks.ExternalGrading.of_mem_summand _ ch.prod⟩ hg)
  have : Fact (ch.gR ∉ p) := ⟨hgp⟩
  -- `x` lies on the zero scheme: on the chart its ideal is generated by `f b² / (cb)`
  have hxZ : x ∈ (zeroScheme X L s).support := by
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ch.affineOpen hL) hxch,
      Scheme.mem_zeroLocus_iff]
    intro r hr
    rw [zeroScheme_ideal_consecutiveChart L hL s ch, SetLike.mem_coe,
      Ideal.mem_span_singleton] at hr
    obtain ⟨t, rfl⟩ := hr
    rw [mem_basicOpen_iff_notMem_primeIdealOf (ch.isAffineOpen_nv hL) _ ⟨x, hxch⟩, not_not]
    apply Ideal.mul_mem_right
    have hz : sectionElt L s * ch.bR ^ 2 ∈
        ((projHomOfIsAmple L hL).base x).asHomogeneousIdeal := by
      rw [hx]
      exact Ideal.mul_mem_right _ _
        (Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨1, sectionElt_mem L s⟩ hfp)
    have hfb : sectionElt L s * ch.bR ^ 2 ∈ grading L (1 • (ch.m + 1 + ch.m)) := by
      have h := SetLike.mul_mem_graded (sectionElt_mem L s) (SetLike.pow_mem_graded 2 ch.bR_mem)
      convert h using 2
      simp only [smul_eq_mul]
      ring
    have hcr : Stacks.DegreeOneUnitAway.chartRatio ch.cR_mem ch.bR_mem ch.cR_mul_bR
        (Stacks.ExternalGrading.of_mem_summand 1 (degreeOneSection L s)) =
        HomogeneousLocalization.Away.mk (grading L)
          (Stacks.ExternalGrading.of_mem_summand (ch.m + 1 + ch.m) ch.prod) 1
          (sectionElt L s * ch.bR ^ 2) hfb := by
      apply HomogeneousLocalization.val_injective
      rw [Stacks.DegreeOneUnitAway.val_chartRatio, HomogeneousLocalization.Away.val_mk]
      congr 1
      apply Subtype.ext
      simp [Stacks.DegreeOneUnitAway.gen]
    rw [hcr]
    exact (chartRingMap_mk_mem_primeIdealOf_iff L hL ch hxch 1 _ hfb).2 hz
  -- the chart prime of `x` is the prime `𝔮` of `A₍g₎` under `𝔭`
  have hq : chartPrime L hL ch x = Stacks.DegreeOneUnitAway.conePrime (grading L) p hgp := by
    rw [Stacks.DegreeOneUnitAway.conePrime_eq_comap (𝒜 := grading L) p ch.cR_mem ch.bR_mem
      ch.cR_mul_bR]
    unfold chartPrime
    rw [hx]
  have := chartPrime_isPrime L hL ch hxch
  have := Stacks.DegreeOneUnitAway.conePrime_isPrime (𝒜 := grading L) p hgp
  -- finiteness and noetherianity on the chart
  have hU := ch.isAffineOpen_nv hL
  have : IsNoetherianRing Γ(X, ch.nv) := IsLocallyNoetherian.component_noetherian ⟨ch.nv, hU⟩
  have : IsNoetherianRing (HomogeneousLocalization.Away (grading L) ch.gR) :=
    isNoetherianRing_of_ringEquiv Γ(X, ch.nv) (chartRingEquiv L hL ch).symm
  have : Algebra.FiniteType ((grading L) 0) (sectionRing L) :=
    Stacks.AlgebraicGeometry.Proj.finiteType_of_isNoetherianRing (grading L)
  have := hfin
  have : Module.Finite (HomogeneousLocalization.Away (grading L) ch.gR)
      (GradedModuleDegreeZeroLocalization (grading L)
        (Stacks.TwistedSections.moduleGrading G L) ch.gR) :=
    AlgebraicGeometry.ProjectiveSpectrum.Proj.finite_degreeZeroLocalization (grading L)
      (Stacks.TwistedSections.moduleGrading G L) ch.deg_pos
      (Stacks.ExternalGrading.of_mem_summand _ ch.prod)
  -- the depths
  set dq := Module.depth (Localization.AtPrime (Stacks.DegreeOneUnitAway.conePrime (grading L) p
      hgp)) (maximalIdeal _) (LocalizedModule (Stacks.DegreeOneUnitAway.conePrime (grading L) p
        hgp).primeCompl (GradedModuleDegreeZeroLocalization (grading L)
          (Stacks.TwistedSections.moduleGrading G L) ch.gR)) with hdq_def
  set dy := Module.depth (Localization.AtPrime p) (maximalIdeal (Localization.AtPrime p))
    (LocalizedModule p.primeCompl (Stacks.TwistedSections.twistModule G L)) with hdy_def
  let := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) G.val x
  have hdq : Module.depth (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) = dq :=
    (depth_stalk_eq_depth_chartPrime L hL ch hxch G).trans
      (depth_localizedModule_congr _ hq)
  have hdy : Stacks.Algebraization.depthOfStalkOnOpen (coneSituation L s)
      ((coneFunctor L s).obj G) y = dy :=
    Stacks.Algebraization.depth_stalk_eq_depth_localizedModule_of_iso_restrict
      (coneSituation L s)
      ((coneFunctor L s).obj G) _ (Iso.refl _) y ((coneSituation L s).U.ι.base y) rfl
  have hcmp := Stacks.DegreeOneUnitAway.depth_add_le_depth_localizedModule
    (𝓜 := Stacks.TwistedSections.moduleGrading G L) p ch.cR_mem ch.bR_mem ch.cR_mul_bR
  -- the dimensions
  let : Algebra k (sectionRing L) := (sectionRingStructureMap fX L).toAlgebra
  have hk : ∀ r : k, algebraMap k (sectionRing L) r ∈ grading L 0 := fun r =>
    Stacks.ExternalGrading.of_mem_summand 0 _
  have : Algebra.FiniteType k (sectionRing L) :=
    Stacks.AlgebraicGeometry.ProperAmpleCohomology.ringHomFiniteType_sectionRing fX L hL
  have hZ : ∀ q : Ideal (coneSituation L s).A, q.IsPrime → (coneSituation L s).I ≤ q →
      (coneSituation L s).a ≤ q → q.IsMaximal :=
    fun q hq _ ha => @isMaximal_of_irrelevant_le X k _ fX L _ _ q hq ha
  have hδp : ringKrullDim (sectionRing L ⧸ p) ≤
      ((coneSituation L s).distanceToZ z : WithBot ℕ∞) := by
    have h := Stacks.Algebraization.ringKrullDim_quotient_le_distanceToZ (coneSituation L s) k
      hZ z
    rw [← hyz] at h
    exact h
  have hBq : ringKrullDim (HomogeneousLocalization.Away (grading L) ch.gR ⧸
      Stacks.DegreeOneUnitAway.conePrime (grading L) p hgp) ≤ ringKrullDim (sectionRing L ⧸ p) :=
    Stacks.DegreeOneUnitAway.ringKrullDim_quotient_conePrime_le k hk ch.deg_pos
      (Stacks.ExternalGrading.of_mem_summand _ ch.prod) p hgp
  have hBq' := Stacks.DegreeOneUnitAway.ringKrullDim_quotient_conePrime_add_one_le k hk
    ch.cR_mem ch.bR_mem ch.cR_mul_bR p hgp
  obtain ⟨e, he⟩ : ∃ e : ℕ∞, ringKrullDim (HomogeneousLocalization.Away (grading L) ch.gR ⧸
      Stacks.DegreeOneUnitAway.conePrime (grading L) p hgp) = e := by
    have : Nontrivial (HomogeneousLocalization.Away (grading L) ch.gR ⧸
        Stacks.DegreeOneUnitAway.conePrime (grading L) p hgp) :=
      Ideal.Quotient.nontrivial_iff.2 (Ideal.IsPrime.ne_top inferInstance)
    exact (WithBot.ne_bot_iff_exists.1 (ne_bot_of_le_ne_bot WithBot.zero_ne_bot
      ringKrullDim_nonneg_of_nontrivial)).imp fun _ h => h.symm
  have hdimx : Stacks.Algebraization.dimClosureAt X x = e := by
    rw [dimClosureAt_eq_ringKrullDim_chartPrime L hL k fX ch hxch, ← he]
    exact congrArg (fun t => ringKrullDim (HomogeneousLocalization.Away (grading L) ch.gR ⧸ t)) hq
  rw [hdy]
  refine three_le_add_of_fibre dy dq _ e (P.toIdeal = p) ?_ ?_ ⟨fun hgen => ?_, ?_⟩
    ((coneSituation L s).one_le_distanceToZ y z hyz) (fun he1 => ?_)
    (fun he0 => ?_)
  · by_cases hgen : P.toIdeal = p
    · exact Or.inl hgen
    · rw [if_neg hgen] at hcmp
      exact Or.inr hcmp
  · exact le_self_add.trans hcmp
  · rw [hgen, he] at hBq'
    exact_mod_cast hBq'.trans hδp
  · rw [he] at hBq
    exact_mod_cast hBq.trans hδp
  · exact hdq ▸ (hG x).1 ⟨hxZ, hdimx ▸ by exact_mod_cast he1⟩
  · exact hdq ▸ (hG x).2 ⟨hxZ, hdimx ▸ by exact_mod_cast he0⟩

end Monoidal

end Stacks.LefschetzCone

end
