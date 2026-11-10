module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.SectionRingChartTower
public import StacksFrontier.AlgebraicGeometry.SectionRingChartBijective.Basic
public import StacksFrontier.AlgebraicGeometry.SectionRingProjMorphism.ToSpecZero
public import StacksFrontier.AlgebraicGeometry.SectionRingProjIso.Proper
public import StacksFrontier.AlgebraicGeometry.ProperAmpleCohomology.SectionRingZero
public import StacksFrontier.AlgebraicGeometry.ProperAmpleCohomology.SerreFiniteness
public import StacksFrontier.RingTheory.HomogeneousLocalization.AwayDegreeOneDepth
public import StacksFrontier.RingTheory.KrullDimension.FiniteTypeOverField
public import StacksFrontier.RingTheory.LocalCohomology.SectionsIso.GradedComplement
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapTransport
public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzCompletedStalkDepthCriterion
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.StalkDepthCriterion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PuncturedConeDepthDimension
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.SectionPowerAlgebraization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ProjectiveCompletion
public import StacksFrontier.AlgebraicGeometry.Scheme.SpecStalkHeight
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg

/-!
# The punctured cone of an ample invertible sheaf over a field

Let `k` be a field, `X` a scheme proper over `k`, `L` an ample invertible `𝒪_X`-module with section
ring `A = Γ_*(X, L)`, `s ∈ Γ(X, L)` with `f ∈ A₁` the element it names, and `𝓕` a coherent
`𝒪_X`-module with graded module `M = Γ_*(X, L, 𝓕)`. This file supplies the input of Faltings'
annihilator theorem in the proof of [Stacks, Tag 0EL1]:

**if `depth(𝓕_x) + dim({x}‾) > σ` at every point `x` off the zero scheme of `s`, then
`depth(M_𝔭) + dim((A/𝔭)_𝔮) > σ + 1` for every prime `𝔭 ∌ f` of `A` and every prime `𝔮 ⊇ 𝔭`
containing the irrelevant ideal.**

A prime `𝔭 ∌ f` is a point of the punctured cone over the affine open `X_s`; it lies over the point
`x` of `X_s = Spec A₍f₎` given by the prime `𝔮₀` of `A₍f₎` under `𝔭`. Then

* `depth(M_𝔭) = depth(𝓕_x) + depth(A_𝔭 / 𝔮₀ A_𝔭)`
  (`Stacks.GradedLocalization.depth_localizedModule_eq_add`, Stacks 0338), the module `M₍f₎`
  being the sections of `𝓕` over `X_s` (Stacks 01PW);
* `dim({x}‾) = trdeg_k κ(𝔮₀)` and `dim((A/𝔭)_𝔮) = trdeg_k κ(𝔭)` (Stacks 00P0), `𝔮` being maximal;
* `trdeg_k κ(𝔮₀) + 1 ≤ depth(A_𝔭 / 𝔮₀ A_𝔭) + trdeg_k κ(𝔭)`
  (`Stacks.GradedLocalization.toENat_trdeg_add_one_le`): the fibre of the cone over `x` is
  `𝔾ₘ` over `κ(x)`.

The file also provides the charts the Čech computation of [Stacks, Tag 0EL1] runs on: finitely
many homogeneous generators of the irrelevant ideal of positive degree, whose nonvanishing opens
are affine and cover `X`.

## Main results

* `Stacks.Algebraization.relativeDimAt_eq_toENat_trdeg`: `dim((A/𝔭)_𝔮) = trdeg_k κ(𝔭)` for a
  finite type algebra over a field and `𝔮` maximal.
* `Stacks.SectionPowerConeDepth.localizedDepth_eq_sheafDepthAt_add`: the depth formula.
* `Stacks.SectionPowerConeDepth.dimClosureAt_conePoint`: the dimension formula.
* `Stacks.SectionPowerConeDepth.depthAddRelativeDim_gt`: the bound above.
* `Stacks.SectionPowerConeDepth.exists_charts`, `isAffineOpen_nvOpen`: the charts.

## References

* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 0338](https://stacks.math.columbia.edu/tag/0338)
* [Stacks Project, Tag 00P0](https://stacks.math.columbia.edu/tag/00P0)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 0EKI](https://stacks.math.columbia.edu/tag/0EKI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite IsLocalRing
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections sectionRing)
open Stacks.TwistedSections (twistModule)
open Stacks.AmpleFiniteAvoidance (nvOpen grading)
open Stacks.SectionRingChartTower (sectionElt sectionElt_mem)
open Stacks.GradedLocalization (awayDegreeZeroToAtPrime baseIdeal)
open Stacks.SectionRingZero (sectionRingZeroHom)
open Stacks.AlgebraicGeometry.GradedProperCohomology (specAlgebraRingHom)
open Stacks.SectionRingProjMorphism.ToSpecZero (degZeroRingHom unitSec)
open Stacks.Algebraization (degreeOneSection)

universe u

attribute [local instance] instVAddNatIntGradedLocalizedModule

/-! ### The relative dimension over a field -/

namespace Stacks.Algebraization

/-- For a finite type algebra `A` over a field `k` and primes `𝔭 ⊆ 𝔮` of `A` with `𝔮` maximal, the
relative dimension `dim((A/𝔭)_𝔮)` is the transcendence degree of `κ(𝔭)` over `k`. -/
theorem relativeDimAt_eq_toENat_trdeg (k : Type*) [Field k] {A : Type*} [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] (p q : PrimeSpectrum A)
    (hpq : p.asIdeal ≤ q.asIdeal) (hq : q.asIdeal.IsMaximal) :
    relativeDimAt A p q = (Cardinal.toENat (Algebra.trdeg k p.asIdeal.ResidueField) :
      WithBot ℕ∞) := by
  set P := p.asIdeal
  set Qi := q.asIdeal
  set qbar : Ideal (A ⧸ P) := Qi.map (Ideal.Quotient.mk P)
  have hcomap : qbar.comap (Ideal.Quotient.mk P) = Qi := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.2 hpq]
  have hqbar : qbar.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le
      Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hsub : Algebra.algebraMapSubmonoid (A ⧸ P) Qi.primeCompl = qbar.primeCompl := by
    ext x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    constructor
    · rintro ⟨z, hz, hzy⟩
      intro hmem
      refine hz ?_
      have hzz : Ideal.Quotient.mk P z = Ideal.Quotient.mk P y := by
        simpa [Ideal.Quotient.algebraMap_eq] using hzy
      rwa [← hcomap, SetLike.mem_coe, Ideal.mem_comap, hzz]
    · exact fun hx => ⟨y, fun hy => hx (by rwa [← hcomap] at hy), rfl⟩
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid (A ⧸ P) Qi.primeCompl)
      (Localization.AtPrime Qi ⧸ P.map (algebraMap A (Localization.AtPrime Qi))) :=
    inferInstance
  rw [hsub] at hloc
  have : IsLocalization.AtPrime
      (Localization.AtPrime Qi ⧸ P.map (algebraMap A (Localization.AtPrime Qi))) qbar := hloc
  exact (ringKrullDim_eq_trdeg_and_ringKrullDim_localization_eq_trdeg k
    (A ⧸ P) P.ResidueField).2 qbar _

end Stacks.Algebraization

namespace Stacks.SectionPowerConeDepth

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

/-! ### The degree-zero part of the section ring -/

section DegreeZero

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- The image of a global function under `Γ(X, 𝒪_X) → Γ_*(X, L)` has degree zero. -/
theorem sectionRingZeroHom_mem (t : Γ(X, ⊤)) : sectionRingZeroHom X L t ∈ grading L 0 :=
  Stacks.ExternalGrading.of_mem_summand 0 _

/-- **The degree-zero comparison undoes the degree-zero inclusion.** -/
theorem degZeroRingHom_sectionRingZeroHom (t : Γ(X, ⊤)) :
    degZeroRingHom L ⟨sectionRingZeroHom X L t, sectionRingZeroHom_mem L t⟩ = t := by
  change Stacks.SectionRingChartMap.ratioR L (unitSec L) _
    (DirectSum.of (powSections L) 0 ((Stacks.SectionRingGeometric.unitScalarAddEquiv X).symm t))
      = t
  refine (Stacks.SectionRingChartMap.ratioR_of L _ _ _).trans ?_
  refine Stacks.SectionRingChartMap.ratio_unique L _ _ _ t ?_
  rw [Stacks.SectionRingProjMorphism.ToSpecZero.resTop_top,
    Stacks.SectionRingProjMorphism.ToSpecZero.resTop_top]
  have h := Stacks.SectionRingGeometric.globalSection_unitComp (X := X)
    ((Stacks.SectionRingGeometric.unitScalarAddEquiv X).symm t) (unitSec L)
  rwa [show (Stacks.SectionRingGeometric.unitScalarAddEquiv X).symm t ≫ unitSec L =
      (Stacks.SectionRingGeometric.unitScalarAddEquiv X).symm t from Category.comp_id _,
    show Stacks.SectionRingGeometric.unitScalar X
      ((Stacks.SectionRingGeometric.unitScalarAddEquiv X).symm t) = t from
      (Stacks.SectionRingGeometric.unitScalarAddEquiv X).apply_symm_apply t] at h

end DegreeZero

/-! ### The point under a point of the punctured cone -/

section Cone

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  (hL : Stacks.Ample.IsAmple X L) (s : Γ(L, ⊤))

/-- **The chart ring isomorphism `Γ_*(X, L)₍s₎ ≅ Γ(X_s, 𝒪_X)`** of Stacks Tag 01PW. -/
def chartRingEquiv :
    HomogeneousLocalization.Away (grading L) (sectionElt L s) ≃+*
      Γ(X, nvOpen L (degreeOneSection L s)) :=
  RingEquiv.ofBijective _ (Stacks.SectionRingChartBijective.chartRingMap_bijective L hL (le_refl 1)
    (degreeOneSection L s))

variable (hU : IsAffineOpen (nvOpen L (degreeOneSection L s)))
  (p : PrimeSpectrum (sectionRing L))
  (hp : sectionElt L s ∉ p.asIdeal)

/-- The prime of `Γ(X_s, 𝒪_X)` under a point `𝔭` of the punctured cone. -/
abbrev conePrime : PrimeSpectrum Γ(X, nvOpen L (degreeOneSection L s)) :=
  ⟨(baseIdeal (grading L) p.asIdeal hp).comap
    ((chartRingEquiv L hL s).symm : Γ(X, nvOpen L (degreeOneSection L s)) →+* _), inferInstance⟩

/-- **The point of `X` under a point `𝔭` of the punctured cone**, the projection of the cone. -/
def conePoint : X := hU.fromSpec (conePrime L hL s p hp)

/-- The point under a point `𝔭` of the punctured cone lies in `X_s`. -/
theorem conePoint_mem : conePoint L hL s hU p hp ∈ nvOpen L (degreeOneSection L s) := by
  change _ ∈ ((nvOpen L (degreeOneSection L s) : X.Opens) : Set X)
  rw [← IsAffineOpen.range_fromSpec hU]
  exact ⟨_, rfl⟩

/-- The prime of `Γ(X_s, 𝒪_X)` at the point under `𝔭` is `conePrime`. -/
theorem primeIdealOf_conePoint :
    hU.primeIdealOf ⟨conePoint L hL s hU p hp, conePoint_mem L hL s hU p hp⟩ =
      conePrime L hL s p hp := by
  have := hU.isOpenImmersion_fromSpec
  apply hU.fromSpec.isOpenEmbedding.injective
  rw [hU.fromSpec_primeIdealOf]
  rfl

/-- **The depth of the cone at `𝔭` is the depth of `𝓕` at the point under it, plus the depth of
the fibre.** -/
theorem localizedDepth_eq_sheafDepthAt_add (F : X.Modules) [F.IsQuasicoherent]
    [IsNoetherianRing (sectionRing L)] [Module.Finite (sectionRing L) (twistModule F L)] :
    Stacks.Algebraization.localizedDepth (sectionRing L) (twistModule F L) p =
      Stacks.Algebraization.sheafDepthAt F (conePoint L hL s hU p hp) +
        Module.depth (Localization.AtPrime p.asIdeal) (maximalIdeal _)
          (Localization.AtPrime p.asIdeal ⧸
            (baseIdeal (grading L) p.asIdeal hp).map
              (awayDegreeZeroToAtPrime (grading L) p.asIdeal hp) •
            (⊤ : Submodule (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal))) := by
  unfold Stacks.Algebraization.localizedDepth
  rw [Stacks.GradedLocalization.depth_localizedModule_eq_add (grading L)
    (Stacks.TwistedSections.moduleGrading F L) p.asIdeal hp (sectionElt_mem L s)]
  congr 1
  set Q := baseIdeal (grading L) p.asIdeal hp
  set c := chartRingEquiv L hL s
  set D := Stacks.SectionRingChartCech.divisionEquiv L hL F one_pos
    (degreeOneSection L s)
  have hD : ∀ a m, D (a • m) = c a • D m := fun a m =>
    Stacks.SectionRingProjQuasicoherent.localDivision_smul L F _ (le_refl _) a m
  have hDs : ∀ (a : Γ(X, nvOpen L (degreeOneSection L s))) m,
      D.symm (a • m) = c.symm a • D.symm m := by
    intro a m
    apply D.injective
    rw [hD, D.apply_symm_apply, D.apply_symm_apply, c.apply_symm_apply]
  rw [← LocalizedModule.depth_atPrime_comap_eq_of_ringEquiv c.symm D.symm hDs Q]
  have h2 := AlgebraicGeometry.depth_stalk_eq_depth_localizedModule F hU
    (conePoint_mem L hL s hU p hp)
  rw [primeIdealOf_conePoint] at h2
  unfold Stacks.Algebraization.sheafDepthAt
  exact h2.symm

section Field

variable (k : Type u) [Field k] (π : X ⟶ Spec (.of k))

/-- The structure map `k → Γ_*(X, L)₀` through the global functions. -/
def zeroGradeHom : k →+* grading L 0 where
  toFun a := ⟨sectionRingZeroHom X L (specAlgebraRingHom k π a), sectionRingZeroHom_mem L _⟩
  map_one' := Subtype.ext (by simp only [map_one]; rfl)
  map_mul' a b := Subtype.ext (by simp only [map_mul]; rfl)
  map_zero' := Subtype.ext (by simp only [map_zero]; rfl)
  map_add' a b := Subtype.ext (by simp only [map_add]; rfl)

/-- The `k`-algebra structure on the degree-zero localization `Γ_*(X, L)₍s₎`. -/
abbrev awayAlgebra : Algebra k (HomogeneousLocalization.Away (grading L) (sectionElt L s)) :=
  ((HomogeneousLocalization.fromZeroRingHom (grading L) _).comp (zeroGradeHom L k π)).toAlgebra

/-- The chart ring isomorphism sends the image of `a ∈ k` to the restriction to `X_s` of the global
function `a`. -/
theorem chartRingEquiv_algebraMap (a : k) :
    letI := awayAlgebra L s k π
    chartRingEquiv L hL s (algebraMap k _ a) =
      X.presheaf.map (homOfLE (le_top : nvOpen L (degreeOneSection L s) ≤ ⊤)).op
        (specAlgebraRingHom k π a) := by
  change Stacks.SectionRingChartMap.chartRingMap L _ (le_refl _)
    (HomogeneousLocalization.fromZeroRingHom (grading L) _ (zeroGradeHom L k π a)) = _
  rw [Stacks.SectionRingProjMorphism.ToSpecZero.chartRingMap_fromZero]
  exact congrArg _ (degZeroRingHom_sectionRingZeroHom L _)

/-- The open immersion `Spec Γ_*(X, L)₍s₎ ≅ X_s ⊆ X`. -/
def chartImmersion : Spec (.of (HomogeneousLocalization.Away (grading L) (sectionElt L s))) ⟶ X :=
  Spec.map (chartRingEquiv L hL s).symm.toCommRingCatIso.hom ≫ hU.fromSpec

/-- The chart `Spec Γ_*(X, L)₍s₎ → X` is an open immersion. -/
instance : IsOpenImmersion (chartImmersion L hL s hU) := by
  unfold chartImmersion
  have := hU.isOpenImmersion_fromSpec
  infer_instance

/-- The chart sends the prime of `Γ_*(X, L)₍s₎` under `𝔭` to the point under `𝔭`. -/
theorem chartImmersion_apply :
    chartImmersion L hL s hU ⟨baseIdeal (grading L) p.asIdeal hp, inferInstance⟩ =
      conePoint L hL s hU p hp := rfl

/-- The chart composed with the structure map `X → Spec k` is the structure map of
`Spec Γ_*(X, L)₍s₎` as a `k`-scheme. -/
theorem chartImmersion_comp :
    letI := awayAlgebra L s k π
    chartImmersion L hL s hU ≫ π = Spec.map (CommRingCat.ofHom (algebraMap k _)) := by
  let := awayAlgebra L s k π
  refine ext_of_isAffine ?_
  rw [← cancel_epi (Scheme.ΓSpecIso (.of k)).inv,
    ← cancel_mono (Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away (grading L)
      (sectionElt L s)))).hom, Category.assoc, Category.assoc, Scheme.ΓSpecIso_naturality,
    Iso.inv_hom_id_assoc]
  unfold chartImmersion
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Category.assoc, Category.assoc,
    Scheme.ΓSpecIso_naturality]
  have happ : hU.fromSpec.appTop = X.presheaf.map (homOfLE le_top).op ≫
      (Scheme.ΓSpecIso Γ(X, nvOpen L (degreeOneSection L s))).inv := by
    change hU.fromSpec.app ⊤ = _
    rw [IsAffineOpen.fromSpec_app_of_le hU ⊤ le_top]
    rfl
  rw [happ]
  have hid : ∀ y,
      (Scheme.ΓSpecIso (CommRingCat.of ↑Γ(X, nvOpen L (degreeOneSection L s)))).hom
      ((Scheme.ΓSpecIso Γ(X, nvOpen L (degreeOneSection L s))).inv y) = y :=
    Iso.inv_hom_id_apply (Scheme.ΓSpecIso Γ(X, nvOpen L (degreeOneSection L s)))
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, hid]
  change (chartRingEquiv L hL s).symm (X.presheaf.map (homOfLE le_top).op
    (specAlgebraRingHom k π a)) = algebraMap k _ a
  rw [RingEquiv.symm_apply_eq, chartRingEquiv_algebraMap]

/-- **The dimension of the closure of the point under `𝔭`** is the transcendence degree of the
residue field of the prime of the base under `𝔭`. -/
theorem dimClosureAt_conePoint [LocallyOfFiniteType π] :
    letI := awayAlgebra L s k π
    Stacks.Algebraization.dimClosureAt X (conePoint L hL s hU p hp) =
      (Cardinal.toENat (Algebra.trdeg k (baseIdeal (grading L) p.asIdeal hp).ResidueField) :
        WithBot ℕ∞) := by
  let := awayAlgebra L s k π
  unfold Stacks.Algebraization.dimClosureAt
  rw [topologicalKrullDim_closure_singleton_eq_trdeg k X π]
  have h1 := Stacks.CurveProjectiveCompletion.trdeg_residueField_of_isOpenImmersion k
    (chartImmersion L hL s hU)
    (Spec.map (CommRingCat.ofHom (algebraMap k _))) π (chartImmersion_comp L hL s hU k π)
    (⟨baseIdeal (grading L) p.asIdeal hp, inferInstance⟩ :
      Spec (.of (HomogeneousLocalization.Away (grading L) (sectionElt L s))))
  rw [chartImmersion_apply] at h1
  rw [← h1, trdeg_spec_residueField k
    (HomogeneousLocalization.Away (grading L) (sectionElt L s))
    (⟨baseIdeal (grading L) p.asIdeal hp, inferInstance⟩ :
      Spec (.of (HomogeneousLocalization.Away (grading L) (sectionElt L s))))]

/-- The `k`-algebra structure on the section ring through the global functions. -/
abbrev sectionRingAlgebra : Algebra k (sectionRing L) :=
  ((sectionRingZeroHom X L).comp (specAlgebraRingHom k π)).toAlgebra

/-- The map `Γ_*(X, L)₍s₎ → Γ_*(X, L)_𝔭` is compatible with the `k`-algebra structures. -/
theorem awayDegreeZeroToAtPrime_algebraMap (a : k) :
    letI := awayAlgebra L s k π
    letI := sectionRingAlgebra L k π
    awayDegreeZeroToAtPrime (grading L) p.asIdeal hp (algebraMap k _ a) =
      algebraMap k (Localization.AtPrime p.asIdeal) a := by
  let := awayAlgebra L s k π
  let := sectionRingAlgebra L k π
  rw [Stacks.GradedLocalization.awayDegreeZeroToAtPrime_apply,
    IsScalarTower.algebraMap_apply k (sectionRing L) (Localization.AtPrime p.asIdeal),
    ← Stacks.GradedLocalization.awayToAtPrime_algebraMap p.asIdeal hp]
  rfl

end Field

/-- **The point under `𝔭` is off the zero scheme of `s`**: it lies in `X_s`, over which the ideal
of `Z(s)` is the unit ideal. -/
theorem conePoint_notMem_support :
    conePoint L hL s hU p hp ∉ ((zeroScheme X L s).support : Set X) := by
  intro hmem
  have hx := conePoint_mem L hL s hU p hp
  have h := (Scheme.IdealSheafData.mem_supportSet_iff_of_mem (I := zeroScheme X L s)
    (U := ⟨nvOpen L (degreeOneSection L s), hU⟩) hx).1 hmem
  have hideal := Stacks.SectionRingChartTower.zeroScheme_pow_ideal_chart L hL s (le_refl 1)
    (degreeOneSection L s) hU 1
  have hfrac : Stacks.SectionRingChartTower.chartFraction L s
      (degreeOneSection L s) = 1 := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_one]
    exact Localization.mk_self (⟨_, 1, rfl⟩ : Submonoid.powers _) |>.trans rfl
  rw [hfrac, map_one, one_pow, Ideal.span_singleton_one, mul_one, pow_one] at hideal
  rw [hideal] at h
  simp only [Submodule.top_coe, Scheme.zeroLocus_univ, Set.mem_compl_iff] at h
  exact h hx

section Proper

variable (k : Type u) [Field k] (π : X ⟶ Spec (.of k))

/-- **A prime of the section ring containing the irrelevant ideal is maximal**, for `X` proper
over `k`: the quotient is generated by the image of `Γ(X, 𝒪_X)`, which is integral over `k`. -/
theorem isMaximal_of_irrelevant_le [UniversallyClosed π] (q : Ideal (sectionRing L)) [q.IsPrime]
    (hq : (HomogeneousIdeal.irrelevant (grading L)).toIdeal ≤ q) : q.IsMaximal := by
  let := sectionRingAlgebra L k π
  let : Algebra k Γ(X, ⊤) := (specAlgebraRingHom k π).toAlgebra
  have hint : (specAlgebraRingHom k π).IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2
      (e := (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed π
  let ψ : Γ(X, ⊤) →ₐ[k] sectionRing L ⧸ q :=
    { toRingHom := (Ideal.Quotient.mk q).comp (sectionRingZeroHom X L)
      commutes' := fun _ => rfl }
  have : Algebra.IsIntegral k (sectionRing L ⧸ q) := ⟨fun z => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hmem : a - sectionRingZeroHom X L
        (Stacks.SectionRingGeometric.unitScalarAddEquiv X (a 0)) ∈ q := by
      refine hq ?_
      rw [HomogeneousIdeal.mem_iff, Stacks.ExternalGrading.mem_irrelevant_iff_degree_zero_eq_zero,
        Stacks.SectionRingZero.sectionRingZeroHom_apply, AddEquiv.symm_apply_apply,
        DirectSum.sub_apply, DirectSum.of_eq_same, sub_self]
    have heq : Ideal.Quotient.mk q a = ψ (Stacks.SectionRingGeometric.unitScalarAddEquiv X (a 0)) :=
      Ideal.Quotient.eq.2 hmem
    rw [heq]
    exact (show IsIntegral k _ from hint _).map ψ⟩
  exact Ideal.Quotient.maximal_of_isField q
    (isField_of_isIntegral_of_isField' (R := k) (Field.toIsField k))

end Proper

/-! ### Arithmetic in the extended integers -/

/-- The embedding `ℕ∞ → EInt` is additive. -/
theorem enatToEInt_add (a b : ℕ∞) :
    Stacks.Algebraization.enatToEInt (a + b) =
      Stacks.Algebraization.enatToEInt a + Stacks.Algebraization.enatToEInt b := by
  rw [← Stacks.Algebraization.krullDimToEInt_coe, ← Stacks.Algebraization.krullDimToEInt_coe,
    ← Stacks.Algebraization.krullDimToEInt_coe, WithBot.coe_add,
    Stacks.Algebraization.krullDimToEInt_add]

/-- For `n : ℕ` and `a : ℕ∞`, `n < a` holds in `EInt` if and only if it holds in `ℕ∞`. -/
theorem natCast_lt_enatToEInt_iff (n : ℕ) (a : ℕ∞) :
    (((n : ℤ) : EInt) < Stacks.Algebraization.enatToEInt a) ↔ (n : ℕ∞) < a := by
  cases a using ENat.recTopCoe with
  | top =>
    refine iff_of_true ?_ (ENat.natCast_lt_top n)
    change ((n : ℤ) : EInt) < (⊤ : EInt)
    exact WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _)
  | coe m =>
    change (((n : ℤ) : EInt) < ((m : ℤ) : EInt)) ↔ _
    rw [WithBotTop.coe_lt_coe, Nat.cast_lt, Nat.cast_lt]

section Assembly

variable (k : Type u) [Field k] (π : X ⟶ Spec (.of k))

include hL hU hp in
/-- **The Faltings bound on the cone over `X_s`.** If `depth(𝓕_x) + dim({x}‾) > σ` at every `x`
off the zero scheme of `s`, then `depth(M_𝔭) + dim((A/𝔭)_𝔮) > σ + 1` for every prime `𝔭 ∌ f` of the
section ring and every prime `𝔮 ⊇ 𝔭` containing the irrelevant ideal. -/
theorem depthAddRelativeDim_gt [IsProper π] (F : X.Modules) [F.IsCoherent] (σ : ℕ)
    (hdepth : ∀ x : X, x ∉ ((zeroScheme X L s).support : Set X) →
      Stacks.Algebraization.enatToEInt (Stacks.Algebraization.sheafDepthAt F x) +
        Stacks.Algebraization.krullDimToEInt (Stacks.Algebraization.dimClosureAt X x) >
          ((σ : ℤ) : EInt))
    (q : PrimeSpectrum (sectionRing L))
    (hq : (HomogeneousIdeal.irrelevant (grading L)).toIdeal ≤ q.asIdeal)
    (hpq : p.asIdeal ≤ q.asIdeal) :
    Stacks.Algebraization.depthAddRelativeDim (sectionRing L) (twistModule F L) p q >
      (((σ + 1 : ℕ) : ℤ) : EInt) := by
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  let := sectionRingAlgebra L k π
  let := awayAlgebra L s k π
  have hft : Algebra.FiniteType k (sectionRing L) := RingHom.finiteType_algebraMap.mp
    (Stacks.AlgebraicGeometry.ProperAmpleCohomology.ringHomFiniteType_sectionRing π L hL)
  have : IsNoetherianRing (sectionRing L) := Algebra.FiniteType.isNoetherianRing k _
  have : Module.Finite (sectionRing L) (twistModule F L) :=
    Stacks.AlgebraicGeometry.ProperAmpleCohomology.moduleFinite_twistModule_of_isCoherent π F L hL
  have hqmax : q.asIdeal.IsMaximal := isMaximal_of_irrelevant_le L k π q.asIdeal hq
  have hx := hdepth _ (conePoint_notMem_support L hL s hU p hp)
  rw [dimClosureAt_conePoint L hL s hU p hp k π, Stacks.Algebraization.krullDimToEInt_coe] at hx
  have hkey := Stacks.GradedLocalization.toENat_trdeg_add_one_le (grading L) p.asIdeal hp
    (sectionElt_mem L s) k (awayDegreeZeroToAtPrime_algebraMap L s p hp k π)
  unfold Stacks.Algebraization.depthAddRelativeDim
  rw [localizedDepth_eq_sheafDepthAt_add L hL s hU p hp F,
    Stacks.Algebraization.relativeDimAt_eq_toENat_trdeg k p q hpq hqmax,
    Stacks.Algebraization.krullDimToEInt_coe]
  rw [← enatToEInt_add, gt_iff_lt, natCast_lt_enatToEInt_iff] at hx ⊢
  set d := Stacks.Algebraization.sheafDepthAt F (conePoint L hL s hU p hp)
  set q0 := Cardinal.toENat (Algebra.trdeg k (baseIdeal (grading L) p.asIdeal hp).ResidueField)
  set e := Module.depth (Localization.AtPrime p.asIdeal)
    (maximalIdeal (Localization.AtPrime p.asIdeal))
    (Localization.AtPrime p.asIdeal ⧸ (baseIdeal (grading L) p.asIdeal hp).map
      (awayDegreeZeroToAtPrime (grading L) p.asIdeal hp) •
        (⊤ : Submodule (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)))
  set t := Cardinal.toENat (Algebra.trdeg k p.asIdeal.ResidueField)
  have h1 : ((σ : ℕ∞) + 1) + 1 ≤ d + (q0 + 1) := by
    rw [← add_assoc]
    exact add_le_add_left (Order.add_one_le_of_lt hx) _
  have h2 : d + (q0 + 1) ≤ d + e + t := by
    rw [add_assoc]
    exact add_le_add_right hkey _
  have h3 : ((σ + 1 : ℕ) : ℕ∞) < ((σ : ℕ∞) + 1) + 1 := by
    push_cast
    exact (ENat.lt_add_one_iff (ENat.natCast_ne_top _)).2 le_rfl
  exact lt_of_lt_of_le h3 (h1.trans h2)

end Assembly

end Cone

/-! ### Charts -/

section Charts

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  (hL : Stacks.Ample.IsAmple X L)

include hL in
/-- **Charts from generators of the irrelevant ideal.** If the section ring is Noetherian, its
irrelevant ideal is spanned by finitely many homogeneous elements `αᵢ` of positive degree, and
their nonvanishing opens cover `X`. -/
theorem exists_charts [IsNoetherianRing (sectionRing L)] :
    ∃ (r : ℕ) (d : Fin r → ℕ) (α : ∀ i, powSections L (d i)), (∀ i, 0 < d i) ∧
      Ideal.span (Set.range (Stacks.SectionRingChartCech.gen L α)) =
        (HomogeneousIdeal.irrelevant (grading L)).toIdeal ∧
      ⨆ i, nvOpen L (α i) = ⊤ := by
  classical
  obtain ⟨r, g, c, hg, hspan⟩ := Stacks.GradedLocalization.exists_fin_homogeneous_span (grading L)
    (HomogeneousIdeal.isHomogeneous _) (IsNoetherian.noetherian _)
  let d : Fin r → ℕ := fun i => if c i = 0 then 1 else c i
  let α : ∀ i, powSections L (d i) := fun i => (g i : sectionRing L) (d i)
  have hgen : ∀ i, Stacks.SectionRingChartCech.gen L α i = g i := by
    intro i
    change DirectSum.of (powSections L) (d i) ((g i) (d i)) = g i
    by_cases hc : c i = 0
    · have hgi : g i ∈ (HomogeneousIdeal.irrelevant (grading L)).toIdeal := by
        rw [← hspan]
        exact Ideal.subset_span ⟨i, rfl⟩
      have h0 : g i ∈ grading L 0 := hc ▸ hg i
      obtain ⟨a, ha⟩ := (Stacks.ExternalGrading.mem_summand_iff).1 h0
      have hz : g i = 0 := by
        rw [HomogeneousIdeal.mem_iff,
          Stacks.ExternalGrading.mem_irrelevant_iff_degree_zero_eq_zero] at hgi
        rw [← ha] at hgi ⊢
        rw [DirectSum.of_eq_same] at hgi
        rw [hgi, map_zero]
      rw [hz]
      simp
    · have hd : d i = c i := ite_eq_right hc
      obtain ⟨a, ha⟩ := (Stacks.ExternalGrading.mem_summand_iff).1 (hg i)
      have key : ∀ (n m : ℕ) (a : powSections L m), n = m →
          DirectSum.of (powSections L) n ((DirectSum.of (powSections L) m a) n) =
            DirectSum.of (powSections L) m a := by
        rintro n m a rfl
        rw [DirectSum.of_eq_same]
      rw [← ha]
      exact key _ _ a hd
  have hpos : ∀ i, 0 < d i := fun i => by
    by_cases hc : c i = 0
    · simp [d, hc]
    · simp only [d, ite_eq_right hc]
      exact Nat.pos_of_ne_zero hc
  have hspan' : Ideal.span (Set.range (Stacks.SectionRingChartCech.gen L α)) =
      (HomogeneousIdeal.irrelevant (grading L)).toIdeal := by
    rw [← hspan]
    exact congrArg (fun g' => Ideal.span (Set.range g')) (funext hgen)
  refine ⟨r, d, α, hpos, hspan', top_le_iff.1 fun x _ => ?_⟩
  rw [TopologicalSpace.Opens.mem_iSup]
  obtain ⟨e, b, he, hxb, -⟩ := Stacks.SectionExtension.exists_pos_affine_nvOpen L hL x
  have hy : Stacks.SectionRingProjMorphism.projHomOfIsAmple L hL x ∈
      Proj.basicOpen (grading L) (DirectSum.of (powSections L) e b) := by
    rwa [← Stacks.SectionRingProjMorphism.projHomOfIsAmple_preimage_projBasicOpen L hL b he] at hxb
  by_contra hall
  push Not at hall
  have hmem : ∀ i, Stacks.SectionRingChartCech.gen L α i ∈
      (Stacks.SectionRingProjMorphism.projHomOfIsAmple L hL x).asHomogeneousIdeal := by
    intro i
    have hxi := hall i
    rw [← Stacks.SectionRingProjMorphism.projHomOfIsAmple_preimage_projBasicOpen L hL (α i)
      (hpos i)] at hxi
    change ¬ (_ ∈ Proj.basicOpen _ _) at hxi
    rwa [Proj.mem_basicOpen, not_not] at hxi
  have hle : (HomogeneousIdeal.irrelevant (grading L)).toIdeal ≤
      (Stacks.SectionRingProjMorphism.projHomOfIsAmple L hL x).asHomogeneousIdeal.toIdeal := by
    rw [← hspan', Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hmem i
  rw [Proj.mem_basicOpen] at hy
  exact hy (hle (Stacks.ExternalGrading.of_mem_irrelevant (by omega) b))

section Proper

variable (k : Type u) [Field k] (π : X ⟶ Spec (.of k))

include hL in
/-- **The nonvanishing opens of homogeneous elements of positive degree are affine**, for `X`
proper over `k`: `X = Proj Γ_*(X, L)` (Stacks 0EKI) and `X_β` is the standard open `D₊(β)`. -/
theorem isAffineOpen_nvOpen [IsProper π] {e : ℕ} (β : powSections L e) (he : 0 < e) :
    IsAffineOpen (nvOpen L β) := by
  have := Stacks.SectionRingProjIso.isIso_projHomOfIsAmple_of_isProper L hL π
  rw [← Stacks.SectionRingProjMorphism.projHomOfIsAmple_preimage_projBasicOpen L hL β he]
  exact (Proj.isAffineOpen_basicOpen (grading L) _ (Stacks.ExternalGrading.of_mem_summand e β)
    he).preimage _

end Proper

end Charts

end Stacks.SectionPowerConeDepth

end
