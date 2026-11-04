module

public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzCone.ChartDegreeZero
public import StacksFrontier.AlgebraicGeometry.SectionExtension.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersion
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapTransport
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.LowDepthLocusClosure
public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzCone.ProjSide
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsComplete
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ProjectiveCompletion
public import StacksFrontier.AlgebraicGeometry.Scheme.SpecStalkHeight
public import StacksFrontier.RingTheory.KrullDimension.FiniteTypeOverField
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.SectionRingChartBijective.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.SectionPowerAlgebraization

/-!
# Stalks of `X` on a chart of consecutive degrees

Let `X` be a scheme with an ample invertible module `L` for which the canonical morphism
`X ⟶ Proj A`, `A = Γ_*(X, L)`, is an isomorphism, and let `X_{cb}` be a chart of consecutive
degrees (`Stacks.LefschetzCone.ConsecutiveChart`), so that `X_{cb} ≅ D₊(cb) ≅ Spec A₍cb₎`. This
file describes the stalks of `X` at the points of the chart in terms of the degree-zero ring
`A₍cb₎`, as the proof of Stacks 0EL5 needs on the punctured cone.

## Main definitions

* `Stacks.LefschetzCone.chartPrime` — the prime of `A₍cb₎` at a point `x` of the chart: the
  homogeneous prime of `x`, extended to `A_{cb}` and cut back to degree zero.
* `Stacks.LefschetzCone.chartRingEquiv` — the chart ring map `A₍cb₎ ≃+* Γ(X, X_{cb})`.

## Main results

* `Stacks.LefschetzCone.chartPrime_isPrime` — the chart prime is prime.
* `Stacks.LefschetzCone.chartPrime_eq_comap` — it is the prime of the point `x` of the affine open
  `X_{cb}`, read through the chart ring map.
* `Stacks.LefschetzCone.dimClosureAt_eq_ringKrullDim_chartPrime` — `dim({x}‾)` is the dimension
  of `A₍cb₎` modulo the chart prime of `x`, for `X` locally of finite type over a field; it rests
  on `Stacks.LefschetzCone.dimClosureAt_eq_ringKrullDim_quotient_primeIdealOf`.
* `Stacks.LefschetzCone.depth_stalk_eq_depth_chartPrime` — for `G` quasi-coherent,
  `depth(G_x) = depth((Γ_*(X, L, G)₍cb₎)_{𝔭})` over `(A₍cb₎)_𝔭`, `𝔭` the chart prime of `x`.

## References

* [Stacks Project, Tag 0EL5](https://stacks.math.columbia.edu/tag/0EL5)
* [Stacks Project, Tag 01QJ](https://stacks.math.columbia.edu/tag/01QJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.GradedSections (powSections mul sectionRing)
open Stacks.AmpleFiniteAvoidance (nvOpen grading)
open Stacks.SectionRingProjMorphism (projHomOfIsAmple)
open Stacks.SectionRingProjQuasicoherent (GoodChart associatedSchemeFunctor image_nvOpen)
open scoped Stacks.GradedLocalization

universe u

namespace Stacks.LefschetzCone

/-- **The dimension of the closure of a point, read on an affine open.** On a scheme locally of
finite type over a field, `dim({x}‾) = dim(Γ(U, 𝒪)/𝔭ₓ)` for an affine open `U ∋ x` with `𝔭ₓ` the
prime of `x`: both are the transcendence degree of the residue field at `x`. -/
theorem dimClosureAt_eq_ringKrullDim_quotient_primeIdealOf (k : Type u) [Field k]
    {X : Scheme.{u}} (fX : X ⟶ Spec (.of k)) [LocallyOfFiniteType fX] {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) :
    Stacks.Algebraization.dimClosureAt X x =
      ringKrullDim (Γ(X, U) ⧸ (hU.primeIdealOf ⟨x, hx⟩).asIdeal) := by
  let : Algebra k Γ(X, U) :=
    ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp
      (Stacks.AlgebraicGeometry.GradedProperCohomology.specAlgebraRingHom k fX)).toAlgebra
  set q := hU.primeIdealOf ⟨x, hx⟩
  have hcomp : hU.fromSpec ≫ fX = Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U))) := by
    refine ext_of_isAffine ?_
    rw [← cancel_epi (Scheme.ΓSpecIso (.of k)).inv,
      ← cancel_mono (Scheme.ΓSpecIso (.of Γ(X, U))).hom]
    rw [Category.assoc, Category.assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    rw [Scheme.Hom.comp_appTop, Category.assoc]
    have happ : hU.fromSpec.appTop = X.presheaf.map (homOfLE le_top).op ≫
        (Scheme.ΓSpecIso Γ(X, U)).inv := by
      show hU.fromSpec.app ⊤ = _
      rw [IsAffineOpen.fromSpec_app_of_le hU ⊤ le_top]
      rfl
    rw [happ]
    have hid : ∀ y, (Scheme.ΓSpecIso (CommRingCat.of ↑Γ(X, U))).hom
        ((Scheme.ΓSpecIso Γ(X, U)).inv y) = y := fun y =>
      Iso.inv_hom_id_apply (Scheme.ΓSpecIso Γ(X, U)) y
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, hid]
    rfl
  have hj : hU.fromSpec q = x := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  let : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ fX.appTop ≫ X.Γevaluation x).hom.toAlgebra
  have h1 := topologicalKrullDim_closure_singleton_eq_trdeg k X fX x
  have h2 := Stacks.CurveProjectiveCompletion.trdeg_residueField_of_isOpenImmersion k hU.fromSpec
    (Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U)))) fX hcomp q
  have h3 := trdeg_spec_residueField k Γ(X, U) q
  have hft : Algebra.FiniteType k Γ(X, U) := by
    rw [← RingHom.finiteType_algebraMap]
    have h := fX.finiteType_appLE (isAffineOpen_top (Spec (.of k))) hU (le_top)
    have hiso := RingHom.FiniteType.of_surjective ((Scheme.ΓSpecIso (.of k)).inv.hom)
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2
    have heq : algebraMap k Γ(X, U) =
        (fX.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom := rfl
    rw [heq]
    exact RingHom.FiniteType.comp h hiso
  have hdom : IsDomain (Γ(X, U) ⧸ q.asIdeal) := Ideal.Quotient.isDomain _
  have h4 := (ringKrullDim_eq_trdeg_and_ringKrullDim_localization_eq_trdeg.{u, u, u, u} k
    (Γ(X, U) ⧸ q.asIdeal) q.asIdeal.ResidueField).1
  rw [h4, ← h3, h2, hj]
  exact h1

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

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  (hL : Stacks.Ample.IsAmple X L) [IsIso (projHomOfIsAmple L hL)]

/-- The prime of the chart ring `Γ_*(X, L)₍cb₎` at a point `x` of the chart: the homogeneous prime
of `x` in `Proj Γ_*(X, L)`, extended to the localization at `cb` and cut back to degree zero. -/
def chartPrime (ch : ConsecutiveChart L) (x : X) :
    Ideal (HomogeneousLocalization.Away (grading L) ch.gR) :=
  Ideal.comap (algebraMap (HomogeneousLocalization.Away (grading L) ch.gR)
      (Localization.Away ch.gR))
    (Ideal.map (algebraMap (sectionRing L) (Localization.Away ch.gR))
      ((projHomOfIsAmple L hL).base x).asHomogeneousIdeal.toIdeal)

omit [IsIso (projHomOfIsAmple L hL)] in
/-- At a point of the chart the product `cb` is outside the homogeneous prime of the point. -/
theorem gR_notMem (ch : ConsecutiveChart L) {x : X} (hx : x ∈ ch.nv) :
    ch.gR ∉ ((projHomOfIsAmple L hL).base x).asHomogeneousIdeal := by
  have h : x ∈ projHomOfIsAmple L hL ⁻¹ᵁ Proj.basicOpen (grading L) ch.gR := by
    rw [Stacks.SectionRingProjMorphism.projHomOfIsAmple_preimage_projBasicOpen L hL ch.prod
      ch.deg_pos]
    exact hx
  exact h

omit [IsIso (projHomOfIsAmple L hL)] in
/-- **The chart prime is prime.** -/
theorem chartPrime_isPrime (ch : ConsecutiveChart L) {x : X} (hx : x ∈ ch.nv) :
    (chartPrime L hL ch x).IsPrime := by
  have hP : (((projHomOfIsAmple L hL).base x).asHomogeneousIdeal.toIdeal).IsPrime :=
    ((projHomOfIsAmple L hL).base x).isPrime
  have hdisj : Disjoint ((Submonoid.powers ch.gR : Submonoid (sectionRing L)) : Set (sectionRing L))
      (((projHomOfIsAmple L hL).base x).asHomogeneousIdeal.toIdeal : Set (sectionRing L)) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr (gR_notMem L hL ch hx)
  have := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers ch.gR)
    (Localization.Away ch.gR) _ hP hdisj
  exact Ideal.comap_isPrime _ _

omit [IsIso (projHomOfIsAmple L hL)] in
/-- Membership of a fraction `z / (cb)ⁿ` in the chart prime: `z` lies in the homogeneous prime of
the point. -/
theorem mk_mem_chartPrime_iff (ch : ConsecutiveChart L) {x : X} (hx : x ∈ ch.nv) (n : ℕ)
    (z : sectionRing L) (hz : z ∈ grading L (n • (ch.m + 1 + ch.m))) :
    HomogeneousLocalization.Away.mk (grading L)
        (Stacks.ExternalGrading.of_mem_summand (ch.m + 1 + ch.m) ch.prod) n z hz ∈
          chartPrime L hL ch x ↔
      z ∈ ((projHomOfIsAmple L hL).base x).asHomogeneousIdeal := by
  have hP : (((projHomOfIsAmple L hL).base x).asHomogeneousIdeal.toIdeal).IsPrime :=
    ((projHomOfIsAmple L hL).base x).isPrime
  rw [chartPrime, Ideal.mem_comap, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk',
    IsLocalization.mk'_mem_map_algebraMap_iff]
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, hmem⟩
    exact (hP.mem_or_mem hmem).resolve_left fun h => gR_notMem L hL ch hx (hP.mem_of_pow_mem k h)
  · intro h
    exact ⟨1, Submonoid.one_mem _, by rw [one_mul]; exact h⟩

/-- Membership of the image of a fraction `z / (cb)ⁿ` under the chart ring map in the prime of a
point `x` of the affine open `X_{cb}`: `z` lies in the homogeneous prime of `x`. -/
theorem chartRingMap_mk_mem_primeIdealOf_iff (ch : ConsecutiveChart L) {x : X} (hx : x ∈ ch.nv)
    (n : ℕ) (z : sectionRing L) (hz : z ∈ grading L (n • (ch.m + 1 + ch.m))) :
    Stacks.SectionRingChartMap.chartRingMap L ch.prod le_rfl
        (HomogeneousLocalization.Away.mk (grading L)
          (Stacks.ExternalGrading.of_mem_summand (ch.m + 1 + ch.m) ch.prod) n z hz) ∈
        ((ch.isAffineOpen_nv hL).primeIdealOf ⟨x, hx⟩).asIdeal ↔
      z ∈ ((projHomOfIsAmple L hL).base x).asHomogeneousIdeal := by
  set D := ch.m + 1 + ch.m with hD
  have hP : (((projHomOfIsAmple L hL).base x).asHomogeneousIdeal.toIdeal).IsPrime :=
    ((projHomOfIsAmple L hL).base x).isPrime
  have hgz : ch.gR * z ∈ grading L (D * (n + 1)) := by
    have h := SetLike.mul_mem_graded (Stacks.ExternalGrading.of_mem_summand D ch.prod) hz
    convert h using 2
    simp only [smul_eq_mul]
    ring
  obtain ⟨t, ht⟩ := (Stacks.ExternalGrading.mem_summand_iff).mp hgz
  rw [Stacks.SectionRingChartMap.chartRingMap_mk_eq_numMap L ch.prod le_rfl n z hz t ht]
  set f := Stacks.SectionRingChartMap.numMap L ch.prod le_rfl (n + 1) (Nat.le_add_left 1 n)
    (Stacks.SectionProduct.globalSection X _ t) with hf
  have hres := Stacks.SectionRingChartMap.numMap_smul_resTop L ch.prod le_rfl (n + 1)
    (Nat.le_add_left 1 n) (Stacks.SectionProduct.globalSection X _ t)
  have hb := Stacks.SectionExtension.nonvanishingOpen_inf_eq_basicOpen
    (Stacks.SectionProduct.globalSection X _ (Stacks.SectionExtension.powSec L ch.prod (n + 1)))
    (Stacks.SectionProduct.globalSection X _ t) (U := ch.nv)
    (Stacks.SectionRingChartMap.le_nvOpen_powSec L ch.prod le_rfl (n + 1) (Nat.le_add_left 1 n))
    f hres.symm
  rw [← not_iff_not, ← mem_basicOpen_iff_notMem_primeIdealOf (ch.isAffineOpen_nv hL), ← hb]
  have hpos : 0 < D * (n + 1) := Nat.mul_pos ch.deg_pos (Nat.succ_pos n)
  have hpre := Stacks.SectionRingProjMorphism.projHomOfIsAmple_preimage_projBasicOpen L hL t hpos
  show (x ∈ nvOpen L t ∧ x ∈ ch.nv) ↔ _
  rw [← hpre, and_iff_left hx]
  show (DirectSum.of (powSections L) (D * (n + 1)) t ∉ _) ↔ _
  rw [ht]
  constructor
  · intro h hz'
    exact h (Ideal.mul_mem_left _ _ hz')
  · intro h hgz'
    exact (hP.mem_or_mem hgz').elim (gR_notMem L hL ch hx) h

/-- **The chart prime is the prime of the point**, read through the chart ring map. -/
theorem chartPrime_eq_comap (ch : ConsecutiveChart L) {x : X} (hx : x ∈ ch.nv) :
    chartPrime L hL ch x = ((ch.isAffineOpen_nv hL).primeIdealOf ⟨x, hx⟩).asIdeal.comap
      (Stacks.SectionRingChartMap.chartRingMap L ch.prod le_rfl) := by
  ext r
  obtain ⟨n, z, hz, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (grading L)
    (Stacks.ExternalGrading.of_mem_summand (ch.m + 1 + ch.m) ch.prod) r
  rw [Ideal.mem_comap, chartRingMap_mk_mem_primeIdealOf_iff, mk_mem_chartPrime_iff L hL ch hx]

/-- **The chart ring map as an isomorphism** `Γ_*(X, L)₍cb₎ ≃+* Γ(X, X_{cb})`. -/
def chartRingEquiv (ch : ConsecutiveChart L) :
    HomogeneousLocalization.Away (grading L) ch.gR ≃+* Γ(X, ch.nv) :=
  RingEquiv.ofBijective (Stacks.SectionRingChartMap.chartRingMap L ch.prod le_rfl)
    (Stacks.SectionRingChartBijective.chartRingMap_bijective L hL ch.deg_pos ch.prod)

/-- **The depth of a stalk is read on the chart.** For a quasi-coherent `G` and `x ∈ X_{cb}`, the
depth of `G_x` over `𝒪_{X,x}` is the depth of the localization at the chart prime of
`Γ_*(X, L, G)₍cb₎`. -/
theorem depth_stalk_eq_depth_chartPrime (ch : ConsecutiveChart L) {x : X} (hx : x ∈ ch.nv)
    (G : X.Modules) [G.IsQuasicoherent] :
    letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) G.val x
    haveI := chartPrime_isPrime L hL ch hx
    Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal _)
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) =
      Module.depth (Localization.AtPrime (chartPrime L hL ch x)) (IsLocalRing.maximalIdeal _)
        (LocalizedModule (chartPrime L hL ch x).primeCompl
          (GradedModuleDegreeZeroLocalization (grading L)
            (Stacks.SectionRingProjQuasicoherent.gradedTwistedSections L G).grade ch.gR)) := by
  have := chartPrime_isPrime L hL ch hx
  have hU := ch.isAffineOpen_nv hL
  have := (hU.primeIdealOf ⟨x, hx⟩).isPrime
  have h1 := Stacks.ModuleStalkSpecialization.depth_stalk_eq_depth_localizedModule G hU ⟨x, hx⟩
  refine h1.trans ?_
  set M := Stacks.SectionRingProjQuasicoherent.gradedTwistedSections L G
  let iso : restrictedTilde L hL M ≅ G :=
    (restrictedTildeTwistedSectionsIso L hL).app ⟨G, inferInstance⟩
  let φ : GradedModuleDegreeZeroLocalization (grading L) M.grade ch.gR ≃+ Γ(G, ch.nv) :=
    (chartSectionsOf L hL M ch.prod ch.deg_pos).symm.trans
      { Stacks.Algebraization.sectionsEquivOfIso iso ch.nv with
        map_add' := fun a b => map_add _ a b }
  have hφ : ∀ (r : HomogeneousLocalization.Away (grading L) ch.gR)
      (n : GradedModuleDegreeZeroLocalization (grading L) M.grade ch.gR),
      φ (r • n) = chartRingEquiv L hL ch r • φ n := by
    intro r n
    obtain ⟨σ, rfl⟩ := (chartSectionsOf L hL M ch.prod ch.deg_pos).surjective n
    rw [← chartSectionsOf_smul L hL M ch.prod ch.deg_pos r σ]
    show iso.hom.app ch.nv ((chartSectionsOf L hL M ch.prod ch.deg_pos).symm
        (chartSectionsOf L hL M ch.prod ch.deg_pos
          (Stacks.SectionRingChartMap.chartRingMap L ch.prod le_rfl r • σ))) =
      Stacks.SectionRingChartMap.chartRingMap L ch.prod le_rfl r •
        iso.hom.app ch.nv ((chartSectionsOf L hL M ch.prod ch.deg_pos).symm
          (chartSectionsOf L hL M ch.prod ch.deg_pos σ))
    simp only [AddEquiv.symm_apply_apply]
    exact map_smul (iso.hom.val.app (op ch.nv)).hom _ _
  have h2 := LocalizedModule.depth_atPrime_comap_eq_of_ringEquiv (chartRingEquiv L hL ch) φ hφ
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  have hc : (hU.primeIdealOf ⟨x, hx⟩).asIdeal.comap
      ((chartRingEquiv L hL ch : HomogeneousLocalization.Away (grading L) ch.gR ≃+* Γ(X, ch.nv)) :
        HomogeneousLocalization.Away (grading L) ch.gR →+* Γ(X, ch.nv)) = chartPrime L hL ch x :=
    (chartPrime_eq_comap L hL ch hx).symm
  have key : ∀ (I : Ideal (HomogeneousLocalization.Away (grading L) ch.gR)) [I.IsPrime],
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal.comap
        ((chartRingEquiv L hL ch : HomogeneousLocalization.Away (grading L) ch.gR ≃+*
          Γ(X, ch.nv)) : HomogeneousLocalization.Away (grading L) ch.gR →+* Γ(X, ch.nv)) = I →
      Module.depth (Localization.AtPrime I) (IsLocalRing.maximalIdeal _)
          (LocalizedModule I.primeCompl
            (GradedModuleDegreeZeroLocalization (grading L) M.grade ch.gR)) =
        Module.depth (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal)
          (IsLocalRing.maximalIdeal _)
          (LocalizedModule (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl Γ(G, ch.nv)) := by
    rintro I _ rfl
    exact h2
  exact (key _ hc).symm

/-- **The dimension of the closure of a point of the chart** is the dimension of the chart ring
modulo the chart prime, for `X` locally of finite type over a field. -/
theorem dimClosureAt_eq_ringKrullDim_chartPrime (k : Type u) [Field k] (fX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType fX] (ch : ConsecutiveChart L) {x : X} (hx : x ∈ ch.nv) :
    Stacks.Algebraization.dimClosureAt X x =
      ringKrullDim (HomogeneousLocalization.Away (grading L) ch.gR ⧸ chartPrime L hL ch x) := by
  have hU := ch.isAffineOpen_nv hL
  rw [dimClosureAt_eq_ringKrullDim_quotient_primeIdealOf k fX hU hx]
  set e := chartRingEquiv L hL ch
  have hmap : (hU.primeIdealOf ⟨x, hx⟩).asIdeal =
      (chartPrime L hL ch x).map (e : HomogeneousLocalization.Away (grading L) ch.gR →+* _) := by
    rw [chartPrime_eq_comap L hL ch hx]
    exact (Ideal.map_comap_of_surjective _ e.surjective _).symm
  exact (ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ e hmap)).symm

end Monoidal

end Stacks.LefschetzCone

end
