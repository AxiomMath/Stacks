module

public import StacksFrontier.AlgebraicGeometry.SectionRingProjTheta.TwistRemarkSquareInt
public import StacksFrontier.AlgebraicGeometry.SectionRingProjMorphism.Theta
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedTriple
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.RestrictCanHom

/-!
# Assertion (i) of Stacks Tag 01QK

In the situation of Stacks Tag 01QH — `X` a scheme, `𝓛` an ample invertible `𝒪_X`-module,
`S = Γ_*(X, 𝓛)`, `Y = Proj S` and `f : X ⟶ Y` the canonical morphism — the first assertion of
Stacks Tag 01QK says that the isomorphism `f^*𝒪_Y(n) ⟶ 𝓛^{⊗ n}` of Stacks Tag 01QI is
`θ_{𝓛^{⊗ n}}`, `θ` being the comparison `f^*M̃ ⟶ 𝓕` of Stacks Tag 01QJ.

Here both maps are the constructed ones:

* the map of Tag 01QI is the degree-`n` component of clause (2) of Stacks Tag 01PZ,
  `Stacks.SectionRingProjMorphism.Theta.projTheta`, a morphism
  `r_{L, ψ}^*𝒪_Y(n) ⟶ 𝓛^{⊗ n}|_{U(ψ)}` on the open `U(ψ) = ⋃ X_s` (which is all of `X` since `𝓛`
  is ample), given on the chart `X_s` by Tag 01NK's quotient `ψ(x) / ψ(s^q)`;
* `θ_{𝓛^{⊗ n}}` is `Stacks.SectionRingProjQuasicoherent.pullbackTildeComparison` for `𝓛^{⊗ n}`,
  read on `f^*𝒪_Y(n)` through the obvious identification `𝒪_Y(n) ≅ (Γ_*(X, 𝓛, 𝓛^{⊗ n}))~`
  (`Stacks.SectionRingProjTheta.twistThetaInt`); on the chart `X_s` it divides by the powers of
  `s`.

The proof compares the two chart formulas (`localDivision_eq_intChartSection`) and concludes since
the preimages of the charts form a basis of `U(ψ)` on which the sections of `r_{L, ψ}^*𝒪_Y(n)` are
pulled back from `𝒪_Y(n)`.

## Main results

* `Stacks.SectionRingProjTheta.localDivision_eq_intChartSection`: the two chart formulas agree.
* `Stacks.SectionRingProjTheta.projTheta_app_eq_twistThetaInt`: assertion (i) of Tag 01QK.

## References

* [Stacks Project, Tag 01QK](https://stacks.math.columbia.edu/tag/01QK)
* [Stacks Project, Tag 01QI](https://stacks.math.columbia.edu/tag/01QI)
* [Stacks Project, Tag 01QJ](https://stacks.math.columbia.edu/tag/01QJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace Opposite
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections sectionRing mul)
open Stacks.TwistedSections (twistPow twistSections twistModule moduleGrading)
open Stacks.AmpleFiniteAvoidance (nvOpen grading)
open Stacks.SectionRingProjMorphism (projHomOfIsAmple)
open Stacks.SectionRingProjQuasicoherent (tildeFunctor pullbackTildeFunctor
  pullbackTildeComparison gluedComparison GoodChart localDivision unitSec powMul tildeModule)
open scoped TensorProduct
open AlgebraicGeometry.ProjectiveSpectrum.Proj (degreeZeroFraction
  associatedModuleSheafStandardOpenEquiv)
open Stacks.GradedModule (shiftedGrading)
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality (associatedModuleSheafMap)

universe u

namespace Stacks.SectionRingProjTheta

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
  (hL : Stacks.Ample.IsAmple X L)

open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.SectionRingGluedComparison (canonicalSections)
open Stacks.AlgebraicGeometry.ProjChartGradedDivision (intChartSection intChartSectionOf intValue)
open Stacks.AlgebraicGeometry.ProjTwistAwayPiece (sectionsTwistEquivGradedPiece)
open Stacks.TwistedSections (twistCongr twistPowMap)

/-- Multiplication by `aᵏ`, `𝓕 ⟶ 𝓕 ⊙ (d k)`: `Stacks.SectionRingProjQuasicoherent.powMul`. -/
abbrev localPowMul (F : X.Modules) {d : ℕ} (a : powSections L d) (k : ℕ) :
    F ⟶ twistPow F L (d * k) :=
  Stacks.SectionRingProjQuasicoherent.powMul L F a k

/-! ### The powers of a homogeneous element of the section ring -/

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- **`(s₀)^q = s₀^q`**: the `q`-th power of the homogeneous element named by `s₀` is the
homogeneous element named by the `q`-th power of `s₀`. -/
theorem of_pow_eq {d : ℕ} (s₀ : powSections L d) : ∀ q : ℕ,
    DirectSum.of (powSections L) d s₀ ^ q =
      DirectSum.of (powSections L) (d * q) (Stacks.SectionExtension.powSec L s₀ q)
  | 0 => rfl
  | q + 1 => by
      rw [pow_succ, of_pow_eq s₀ q, ← Stacks.SectionRingChartMap.of_mul_eq]
      rfl

/-- The value of the canonical datum on the element named by a section, read at an equal index. -/
theorem canonicalSections_toFun_of_eq {m m' : ℕ} (h : m = m') (σ : powSections L m)
    (hσ : DirectSum.of (powSections L) m σ ∈ grading L m') :
    (canonicalSections L).toFun m' ⟨_, hσ⟩ =
      Stacks.SectionProduct.globalSection X _ (σ ≫ eqToHom (congrArg (natTensorPow L) h)) := by
  subst h
  simpa using Stacks.SectionRingGluedComparison.canonicalSections_toFun_of L m σ hσ

/-- **The value of `ψ(s^q)` in Tag 01CU's power, as a morphism out of the unit**: the comparison
of the `q`-th power of `s`. -/
theorem intSecOf_intValue_pow {d : ℕ} (s₀ : powSections L d) (q : ℕ) :
    Stacks.TensorPowerDivision.intSecOf L
        (intValue (canonicalSections L) (q * d)
          ⟨_, Stacks.MorphismToProj.HomogeneousRatios.pow_mem
            (Stacks.ExternalGrading.of_mem_summand d s₀) q⟩) =
      Stacks.SectionExtension.powSec L s₀ q ≫
        eqToHom (congrArg (natTensorPow L) (Nat.mul_comm d q)) ≫
          (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L (q * d)).hom := by
  apply (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _).injective
  change Stacks.SectionProduct.globalSection X _ (Stacks.TensorPowerDivision.intSecOf L _) =
    Stacks.SectionProduct.globalSection X _ _
  rw [Stacks.TensorPowerDivision.globalSection_intSecOf]
  change (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L (q * d)).hom.app ⊤
      ((canonicalSections L).toFun (q * d) ⟨_, _⟩) = _
  have hpow := of_pow_eq L s₀ q
  have key : ∀ (y : sectionRing L) (hy : y ∈ grading L (q * d)),
      y = DirectSum.of (powSections L) (d * q) (Stacks.SectionExtension.powSec L s₀ q) →
      (canonicalSections L).toFun (q * d) ⟨y, hy⟩ =
        Stacks.SectionProduct.globalSection X _ (Stacks.SectionExtension.powSec L s₀ q ≫
          eqToHom (congrArg (natTensorPow L) (Nat.mul_comm d q))) := by
    rintro y hy rfl
    exact canonicalSections_toFun_of_eq L (Nat.mul_comm d q) _ hy
  rw [key _ _ hpow]
  rfl

/-- **`𝓛^{⊗ n} ⊙ m ⟶ 𝓛^{⊗ (n + m)}`** at the scheme spelling: the grouped form, the comparison of
the iterated power with Tag 01CU's, and Tag 01CU's multiplication. -/
def twistPowCompareX (n : ℤ) (m : ℕ) :
    twistPow (tensorPowerModule X L n) L m ⟶ tensorPowerModule X L (n + m) :=
  letI := Stacks.PowerFamilyBridge.instIsInvertible X.presheaf
    (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X) L
  Stacks.SheafOfModules.Invertible.twistPowCompare X.presheaf
    (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X) L n m

/-- Reindexing the twist and the target of `twistPowCompareX` along an equality of exponents. -/
theorem eqToHom_twistPowCompareX (n : ℤ) {m m' : ℕ} (h : m = m') :
    eqToHom (congrArg (twistPow (tensorPowerModule X L n) L) h) ≫ twistPowCompareX L n m' =
      twistPowCompareX L n m ≫
        eqToHom (congrArg (fun i : ℕ => tensorPowerModule X L (n + i)) h) := by
  subst h
  simp

/-- **Multiplication by `ψ(s^q)` in Tag 01CU's powers is multiplication by `s^q` in the twist**,
read through `twistPowCompareX`. -/
theorem intMulMap_intSecOf_pow (n : ℤ) {d : ℕ} (s₀ : powSections L d) (q : ℕ) :
    Stacks.TensorPowerDivision.intMulMap L
        (Stacks.TensorPowerDivision.intSecOf L
          (intValue (canonicalSections L) (q * d)
            ⟨_, Stacks.MorphismToProj.HomogeneousRatios.pow_mem
              (Stacks.ExternalGrading.of_mem_summand d s₀) q⟩)) n ≫
        eqToHom (congrArg (tensorPowerModule X L) (Int.add_comm ((q * d : ℕ) : ℤ) n)) =
      localPowMul L (tensorPowerModule X L n) s₀ q ≫
        eqToHom (congrArg (twistPow (tensorPowerModule X L n) L) (Nat.mul_comm d q)) ≫
          twistPowCompareX L n (q * d) := by
  let := Stacks.PowerFamilyBridge.instIsInvertible X.presheaf
    (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X) L
  have hA := Stacks.SheafOfModules.Invertible.smulRight_twistPowCompare X.presheaf
    (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X) L n (q * d)
    (Stacks.SectionExtension.powSec L s₀ q ≫
      eqToHom (congrArg (natTensorPow L) (Nat.mul_comm d q)))
  have hS : localPowMul L (tensorPowerModule X L n) s₀ q ≫
      eqToHom (congrArg (twistPow (tensorPowerModule X L n) L) (Nat.mul_comm d q)) =
      smulRight (tensorPowerModule X L n) (Stacks.SectionExtension.powSec L s₀ q ≫
        eqToHom (congrArg (natTensorPow L) (Nat.mul_comm d q))) := by
    rw [localPowMul, powMul_eq_smulRight, smulRight_comp_eqToHom]
    exact Nat.mul_comm d q
  rw [intSecOf_intValue_pow, reassoc_of% hS]
  unfold Stacks.TensorPowerDivision.intMulMap
  simp only [Category.assoc] at hA ⊢
  exact hA.symm

/-- **The shift of `π`, compared, is the comparison of the image of `π` in `S`.** -/
theorem twistCongr_twistPowCompareX (n : ℤ) {q d j : ℕ} (hj : (-n).toNat + j = q * d)
    (π : twistSections (twistPow (tensorPowerModule X L n) L (-n).toNat) L j) :
    twistCongr hj (twistShiftSection (-n).toNat j π) ≫ twistPowCompareX L n (q * d) =
      π ≫ twistPowMap L (twistBeta L n).inv j ≫
          eqToHom (twistPow_natTensorPow L n.toNat j) ≫
        (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L (n.toNat + j)).hom ≫
          eqToHom (congrArg (tensorPowerModule X L) (by
            have := toNat_eq_add_toNat_neg n
            push_cast
            omega)) := by
  let := Stacks.PowerFamilyBridge.instIsInvertible X.presheaf
    (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X) L
  have hB := Stacks.SheafOfModules.Invertible.eqToHom_twistPowCompare X.presheaf
    (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X) L n n.toNat (-n).toNat j
    (toNat_eq_add_toNat_neg n)
  have hI := eqToHom_twistPowCompareX L n hj
  simp only [twistCongr, twistShiftSection, Category.assoc]
  rw [hI]
  change π ≫ eqToHom _ ≫ (Stacks.SheafOfModules.Invertible.twistPowCompare X.presheaf
    (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X) L n ((-n).toNat + j)) ≫ _ = _
  exact (congrArg (fun φ => π ≫ φ) ((reassoc_of% hB) _)).trans
    (congrArg (fun φ => π ≫ twistPowMap L (twistBeta L n).inv j ≫
      eqToHom (twistPow_natTensorPow L n.toNat j) ≫
        (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L (n.toNat + j)).hom ≫ φ)
      (eqToHom_trans _ _))

/-- `intPowReindex` is the `eqToHom` of the reindexing. -/
theorem intPowReindex_hom_eq {a b : ℤ} (h : a = b) :
    (Stacks.TensorPowerDivision.intPowReindex L h).hom =
      eqToHom (congrArg (tensorPowerModule X L) h) := by
  subst h
  rfl

/-- The restriction of the value of a morphism on a global section named by a morphism out of the
unit is the section named by the composite. -/
theorem resTop_app_globalSection {M N : X.Modules} (t : 𝟙_ X.Modules ⟶ M) (g : M ⟶ N)
    (V : X.Opens) :
    Stacks.TensorPowerTrivialize.resTop N (g.app ⊤ (Stacks.SectionProduct.globalSection X M t)) V =
      unitSec (t ≫ g) V :=
  (Stacks.SectionRingProjQuasicoherent.unitSec_eq_map_globalSection (t ≫ g) V).symm

/-- The value of the canonical datum on an element equal to the one named by a section. -/
theorem canonicalSections_toFun_eq_of_eq {m : ℕ} (y : sectionRing L) (hy : y ∈ grading L m)
    (σ : powSections L m) (h : y = DirectSum.of (powSections L) m σ) :
    (canonicalSections L).toFun m ⟨y, hy⟩ = Stacks.SectionProduct.globalSection X _ σ := by
  subst h
  exact Stacks.SectionRingGluedComparison.canonicalSections_toFun_of L m σ hy

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- Two reindexings after a composite are one. -/
theorem comp_comp_eqToHom_eqToHom {A B C D E F G : X.Modules} (a : A ⟶ B) (b : B ⟶ C)
    (c : C ⟶ D) (e : D ⟶ E) (h₁ : E = F) (h₂ : F = G) (h₃ : E = G) :
    (a ≫ b ≫ c ≫ e ≫ eqToHom h₁) ≫ eqToHom h₂ = (a ≫ b ≫ c) ≫ e ≫ eqToHom h₃ := by
  simp

/-! ### The two chart formulas agree -/

/-- **On a chart, Tag 01QJ's comparison for `𝓛^{⊗ n}`, read on `𝒪_Y(n)`, is the chart formula of
Tag 01NK**: a section of `𝒪_Y(n)` over `D₊(s)` goes, through the identification
`𝒪_Y(n) ≅ (Γ_*(X, 𝓛, 𝓛^{⊗ n}))~` and the division by the powers of `s`, to the quotient
`ψ(x) / ψ(s^q)` of its representative `x / s^q`. -/
theorem localDivision_eq_intChartSection (n : ℤ) {d : ℕ} (s₀ : powSections L d) (hd : 0 < d)
    {V : X.Opens} (hU : V ≤ nvOpen L s₀)
    (hV : V ≤ Stacks.NonvanishingOpen.nonvanishingOpen X (natTensorPow L d)
      ((canonicalSections L).toFun d ⟨_, Stacks.ExternalGrading.of_mem_summand d s₀⟩))
    (b : Γ(twistY L n,
      ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀))) :
    localDivision L (tensorPowerModule X L n) s₀ hU
        (associatedModuleSheafStandardOpenEquiv (grading L)
          (moduleGrading (tensorPowerModule X L n) L)
          (Stacks.ExternalGrading.of_mem_summand d s₀) hd
          ((twistPowIdent L n).hom.val.app
            (op (ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀)))
            b)) =
      intChartSection (canonicalSections L) (Stacks.ExternalGrading.of_mem_summand d s₀) hV hd n
        (sectionsTwistEquivGradedPiece (grading L) (Stacks.ExternalGrading.of_mem_summand d s₀) hd
          n b) := by
  have ec := exists_shift_fraction L (tensorPowerModule X L n) (-n).toNat s₀ hd
    ((twistPowIdent L n).hom.val.app
      (op (ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀))) b)
  obtain ⟨q, ec⟩ := ec
  obtain ⟨j, ec⟩ := ec
  obtain ⟨hj, ec⟩ := ec
  obtain ⟨π, ec⟩ := ec
  obtain ⟨hx', ec⟩ := ec
  obtain ⟨hshift, hc⟩ := ec
  have hb := eq_symm_of_unitTwistIdent_hom L (tensorPowerModule X L n) (twistBeta L n)
    (toNat_eq_add_toNat_neg n) s₀ hd q _ hx' b hc
  subst hb
  have hv : DirectSum.of (twistSections (tensorPowerModule X L n) L) (q * d)
      (twistCongr hj (twistShiftSection (-n).toNat j π)) ∈
        moduleGrading (tensorPowerModule X L n) L (q • (d : ℤ)) :=
    hshift ▸ identRight_mem (tensorPowerModule X L n) (-n).toNat _ _ hx'
  have l2 := (congrArg (associatedModuleSheafStandardOpenEquiv (grading L)
    (moduleGrading (tensorPowerModule X L n) L) (Stacks.ExternalGrading.of_mem_summand d s₀) hd)
      hc).trans (((associatedModuleSheafStandardOpenEquiv (grading L)
        (moduleGrading (tensorPowerModule X L n) L) (Stacks.ExternalGrading.of_mem_summand d s₀)
          hd).apply_symm_apply _).trans
      (Stacks.Veronese.degreeZeroFraction_congr (grading L)
        (moduleGrading (tensorPowerModule X L n) L)
        (Stacks.ExternalGrading.of_mem_summand d s₀) rfl hshift _ hv))
  have hx : unitIdent (tensorPowerModule X L n) (twistBeta L n)
      (DirectSum.of (twistSections (twistPow (tensorPowerModule X L n) L (-n).toNat) L) j π) ∈
        grading L (n.toNat + j) := by
    rw [unitIdent_of L (tensorPowerModule X L n) (twistBeta L n) j π]
    exact Stacks.ExternalGrading.of_mem_summand _ _
  have hj' := congrArg (Nat.cast : ℕ → ℤ) hj
  push_cast at hj'
  have hE : (((q * d : ℕ) : ℤ)) + n = ((n.toNat + j : ℕ) : ℤ) := by
    have := toNat_eq_add_toNat_neg n
    push_cast
    linarith
  have hrep : ((sectionsTwistEquivGradedPiece (grading L)
      (Stacks.ExternalGrading.of_mem_summand d s₀) hd n
      ((associatedModuleSheafStandardOpenEquiv (grading L)
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading (grading L) n)
        (Stacks.ExternalGrading.of_mem_summand d s₀) hd).symm
          (degreeZeroFraction (grading L)
            (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading (grading L) n)
            (Stacks.ExternalGrading.of_mem_summand d s₀) q
            (unitIdent (tensorPowerModule X L n) (twistBeta L n)
              (DirectSum.of (twistSections (twistPow (tensorPowerModule X L n) L (-n).toNat) L)
                j π))
            (unitIdent_mem (tensorPowerModule X L n) (twistBeta L n)
              (toNat_eq_add_toNat_neg n) _ _ hx')))) :
        LocalizedModule.Away (DirectSum.of (powSections L) d s₀) (sectionRing L)) =
      LocalizedModule.mk (unitIdent (tensorPowerModule X L n) (twistBeta L n)
        (DirectSum.of (twistSections (twistPow (tensorPowerModule X L n) L (-n).toNat) L) j π))
        (⟨DirectSum.of (powSections L) d s₀ ^ q, ⟨q, rfl⟩⟩ :
          Submonoid.powers (DirectSum.of (powSections L) d s₀)) := by
    rw [Stacks.AlgebraicGeometry.ProjTwistAwayPiece.coe_sectionsTwistEquivGradedPiece]
    change ((associatedModuleSheafStandardOpenEquiv (grading L)
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading (grading L) n)
        (Stacks.ExternalGrading.of_mem_summand d s₀) hd
        ((associatedModuleSheafStandardOpenEquiv (grading L)
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading (grading L) n)
          (Stacks.ExternalGrading.of_mem_summand d s₀) hd).symm _) :
        LocalizedModule.Away (DirectSum.of (powSections L) d s₀) (sectionRing L))) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hR := Stacks.AlgebraicGeometry.ProjChartGradedDivision.intChartSection_mk
    (canonicalSections L) (Stacks.ExternalGrading.of_mem_summand d s₀) hV hd n _ q
    (n.toNat + j) hE _ hx hrep
  refine (congrArg (localDivision L (tensorPowerModule X L n) s₀ hU) l2).trans (Eq.trans ?_ hR.symm)
  have hτ := Stacks.AlgebraicGeometry.ProjChartGradedDivision.le_nonvanishingOpen_intValue_pow
    (canonicalSections L) (Stacks.ExternalGrading.of_mem_summand d s₀) hV q
  have hW : V ≤ Stacks.NonvanishingOpen.nonvanishingOpen X (tensorPowerModule X L ((q * d : ℕ) : ℤ))
      (Stacks.SectionProduct.globalSection X _ (Stacks.TensorPowerDivision.intSecOf L
        (intValue (canonicalSections L) (q * d)
          ⟨_, Stacks.MorphismToProj.HomogeneousRatios.pow_mem
            (Stacks.ExternalGrading.of_mem_summand d s₀) q⟩))) := by
    rwa [Stacks.TensorPowerDivision.globalSection_intSecOf]
  apply (Stacks.TensorPowerDivision.bijective_app_intMulMap L _ hW n le_rfl).1
  refine Eq.trans ?_ (Stacks.TensorPowerDivision.mul_intDivTop L _ hτ n _).symm
  have hM := (comp_eqToHom_iff _ _ _).1 (intMulMap_intSecOf_pow L n s₀ q)
  have hP := Stacks.SectionRingProjQuasicoherent.powMul_app_localDivision L
    (tensorPowerModule X L n) s₀ hU
    (degreeZeroFraction (grading L) (moduleGrading (tensorPowerModule X L n) L)
      (Stacks.ExternalGrading.of_mem_summand d s₀) q _ hv) q
    (twistCongr hj (twistShiftSection (-n).toNat j π)) rfl
  have hC := twistCongr_twistPowCompareX L n hj π
  have e1 := (congrArg (fun φ => Scheme.Modules.Hom.app φ V
    (localDivision L (tensorPowerModule X L n) s₀ hU
      (degreeZeroFraction (grading L) (moduleGrading (tensorPowerModule X L n) L)
        (Stacks.ExternalGrading.of_mem_summand d s₀) q _ hv))) hM).trans
    (congrArg (fun y => Scheme.Modules.Hom.app ((eqToHom (congrArg
      (twistPow (tensorPowerModule X L n) L) (Nat.mul_comm d q)) ≫
        twistPowCompareX L n (q * d)) ≫ eqToHom (congrArg (tensorPowerModule X L)
          (Int.add_comm ((q * d : ℕ) : ℤ) n).symm)) V y) hP)
  refine e1.trans ?_
  have hr := unitIdent_of L (tensorPowerModule X L n) (twistBeta L n) j π
  have hval := canonicalSections_toFun_eq_of_eq L _ hx _ hr
  have hRHS : Stacks.TensorPowerTrivialize.resTop
      (tensorPowerModule X L (((q * d : ℕ) : ℤ) + n))
      ((Stacks.TensorPowerDivision.intPowReindex L hE.symm).hom.app ⊤
        (intValue (canonicalSections L) (n.toNat + j) ⟨_, hx⟩)) V =
      unitSec ((π ≫ twistPowMap L (twistBeta L n).inv j ≫
          eqToHom (twistPow_natTensorPow L n.toNat j)) ≫
        (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L (n.toNat + j)).hom ≫
          eqToHom (congrArg (tensorPowerModule X L) hE.symm)) V := by
    have hiv : intValue (canonicalSections L) (n.toNat + j) ⟨_, hx⟩ =
        (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L (n.toNat + j)).hom.app ⊤
          (Stacks.SectionProduct.globalSection X _ (π ≫ twistPowMap L (twistBeta L n).inv j ≫
            eqToHom (twistPow_natTensorPow L n.toNat j))) :=
      congrArg (fun y => (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L
        (n.toNat + j)).hom.app ⊤ y) hval
    rw [hiv, intPowReindex_hom_eq]
    exact resTop_app_globalSection (π ≫ twistPowMap L (twistBeta L n).inv j ≫
      eqToHom (twistPow_natTensorPow L n.toNat j))
      ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L (n.toNat + j)).hom ≫
        eqToHom (congrArg (tensorPowerModule X L) hE.symm)) V
  have htc : twistCongr (Nat.mul_comm q d) (twistCongr hj (twistShiftSection (-n).toNat j π)) ≫
      eqToHom (congrArg (twistPow (tensorPowerModule X L n) L) (Nat.mul_comm d q)) =
      twistCongr hj (twistShiftSection (-n).toNat j π) := by
    simp [twistCongr]
  have hmor : twistCongr (Nat.mul_comm q d) (twistCongr hj (twistShiftSection (-n).toNat j π)) ≫
      ((eqToHom (congrArg (twistPow (tensorPowerModule X L n) L) (Nat.mul_comm d q)) ≫
        twistPowCompareX L n (q * d)) ≫ eqToHom (congrArg (tensorPowerModule X L)
          (Int.add_comm ((q * d : ℕ) : ℤ) n).symm)) =
      (π ≫ twistPowMap L (twistBeta L n).inv j ≫
          eqToHom (twistPow_natTensorPow L n.toNat j)) ≫
        (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L (n.toNat + j)).hom ≫
          eqToHom (congrArg (tensorPowerModule X L) hE.symm) := by
    rw [← Category.assoc, ← Category.assoc, htc, hC]
    exact comp_comp_eqToHom_eqToHom π (twistPowMap L (twistBeta L n).inv j)
      (eqToHom (twistPow_natTensorPow L n.toNat j))
      (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L (n.toNat + j)).hom _ _ _
  exact (congrArg (fun φ => unitSec φ V) hmor).trans hRHS.symm

/-! ### Morphisms out of a pullback along an open immersion -/

section Ext

/-- **A morphism of modules is determined on the sections over the opens of a basis.** -/
theorem modules_hom_ext_of_isBasis {Y : Scheme.{u}} {A B : Y.Modules} {ι : Type*}
    (V : ι → Y.Opens) (hV : Opens.IsBasis (Set.range V)) {φ ψ : A ⟶ B}
    (h : ∀ (i : ι) (a : Γ(A, V i)), φ.app (V i) a = ψ.app (V i) a) : φ = ψ := by
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext a
  have hcover : U ≤ iSup (fun p : {i : ι // V i ≤ U} => V p.1) := by
    intro x hx
    rw [Opens.mem_iSup]
    obtain ⟨W, ⟨i, rfl⟩, hxW, hWU⟩ := Opens.isBasis_iff_nbhd.mp hV hx
    exact ⟨⟨i, hWU⟩, hxW⟩
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨_, B.isSheaf⟩
    (fun p : {i : ι // V i ≤ U} => V p.1) U (fun p => homOfLE p.2) hcover _ _ fun p => ?_
  obtain ⟨i, hle⟩ := p
  have hφ := Stacks.Tag01VSPullbackTensor.homApp_presheaf_map φ (homOfLE hle) a
  have hψ := Stacks.Tag01VSPullbackTensor.homApp_presheaf_map ψ (homOfLE hle) a
  exact hφ.symm.trans ((h i _).trans hψ)

/-- **Along an open immersion, every section of a pullback over the preimage of an open inside the
image is pulled back.** -/
theorem pullbackSection_surjective_of_image {Y Z : Scheme.{u}} (g : Y ⟶ Z) [IsOpenImmersion g]
    (A : Z.Modules) (W : Z.Opens) (hW : g ''ᵁ (g ⁻¹ᵁ W) = W) :
    Function.Surjective (Scheme.Modules.pullbackSection g A W (g ⁻¹ᵁ W) le_rfl) := by
  intro y
  refine ⟨A.val.map (homOfLE (le_of_eq hW.symm)).op
    (Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback g).inv.app A)
      (g ⁻¹ᵁ W) y), ?_⟩
  have h2 := Scheme.Modules.restrictFunctorIsoPullback_inv_pullbackSection g A W (g ⁻¹ᵁ W)
    le_rfl (le_of_eq hW)
    (A.val.map (homOfLE (le_of_eq hW.symm)).op
      (Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback g).inv.app A)
        (g ⁻¹ᵁ W) y))
  have h3 : A.val.map (homOfLE (le_of_eq hW)).op (A.val.map (homOfLE (le_of_eq hW.symm)).op
      (Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback g).inv.app A)
        (g ⁻¹ᵁ W) y)) =
      Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback g).inv.app A)
        (g ⁻¹ᵁ W) y := by
    refine (Stacks.SectionRingProjQuasicoherent.presheaf_map_map A _ _ (𝟙 _) _).trans ?_
    rw [CategoryTheory.Functor.map_id]
    rfl
  have hinj : Function.Injective (Scheme.Modules.Hom.app
      ((Scheme.Modules.restrictFunctorIsoPullback g).inv.app A) (g ⁻¹ᵁ W)) :=
    (ConcreteCategory.bijective_of_isIso _).1
  exact hinj (h2.trans h3)

/-- The inverse of `pullbackCongr` on a pulled-back section. -/
theorem pullbackCongr_inv_pullbackSection {Y Z : Scheme.{u}} {g g' : Y ⟶ Z} (h : g = g')
    (A : Z.Modules) (W : Z.Opens) (W' : Y.Opens) (hg : W' ≤ g ⁻¹ᵁ W) (hg' : W' ≤ g' ⁻¹ᵁ W)
    (a : A.val.obj (op W)) :
    ((Scheme.Modules.pullbackCongr h).inv.app A).val.app (op W')
        (Scheme.Modules.pullbackSection g' A W W' hg' a) =
      Scheme.Modules.pullbackSection g A W W' hg a := by
  subst h
  rfl

/-- A four-fold composite of morphisms of modules on a section, step by step. -/
theorem comp4_val_app_eq {Y : Scheme.{u}} {M₀ M₁ M₂ M₃ M₄ : Y.Modules} (f₁ : M₀ ⟶ M₁)
    (f₂ : M₁ ⟶ M₂) (f₃ : M₂ ⟶ M₃) (f₄ : M₃ ⟶ M₄) (V : Y.Opens) (x₀ : M₀.val.obj (op V))
    (x₁ : M₁.val.obj (op V)) (x₂ : M₂.val.obj (op V)) (x₃ : M₃.val.obj (op V))
    (x₄ : M₄.val.obj (op V)) (h₁ : f₁.val.app (op V) x₀ = x₁) (h₂ : f₂.val.app (op V) x₁ = x₂)
    (h₃ : f₃.val.app (op V) x₂ = x₃) (h₄ : f₄.val.app (op V) x₃ = x₄) :
    (f₁ ≫ f₂ ≫ f₃ ≫ f₄).val.app (op V) x₀ = x₄ := by
  subst h₁ h₂ h₃ h₄
  rfl

/-- **Pulling back along `U ⟶ X ⟶ Y` and comparing with the restriction**, on a pulled-back
section, for a morphism `g` equal to the composite. -/
theorem transport_app_pullbackSection {Y Z T : Scheme.{u}} (ι : T ⟶ Y) [IsOpenImmersion ι]
    (f : Y ⟶ Z) (g : T ⟶ Z) (h : ι ≫ f = g) (A : Z.Modules) (N : Y.Modules)
    (θ : (Scheme.Modules.pullback f).obj A ⟶ N) (D : Z.Opens) (V : T.Opens) (hV : V ≤ g ⁻¹ᵁ D)
    (hV' : ι ''ᵁ V ≤ f ⁻¹ᵁ D) (s : A.val.obj (op D)) :
    ((Scheme.Modules.pullbackCongr h).inv.app A ≫ (Scheme.Modules.pullbackComp ι f).inv.app A ≫
        (Scheme.Modules.pullback ι).map θ ≫
          (Scheme.Modules.restrictFunctorIsoPullback ι).inv.app N).val.app (op V)
        (Scheme.Modules.pullbackSection g A D V hV s) =
      θ.val.app (op (ι ''ᵁ V)) (Scheme.Modules.pullbackSection f A D (ι ''ᵁ V) hV' s) := by
  subst h
  have hle : V ≤ ι ⁻¹ᵁ (ι ''ᵁ V) := (ι.preimage_image_eq V).ge
  have e2 := Stacks.AlgebraicGeometry.ModuleLimits.pullbackComp_inv_val_app_pullbackSection
    ι f A D (ι ''ᵁ V) V hV' hle hV s
  have e3 := Scheme.Modules.pullbackSection_naturality ι θ (ι ''ᵁ V) V hle
    (Scheme.Modules.pullbackSection f A D (ι ''ᵁ V) hV' s)
  have e4 := Scheme.Modules.restrictFunctorIsoPullback_inv_pullbackSection ι N (ι ''ᵁ V) V hle
    le_rfl (θ.val.app (op (ι ''ᵁ V)) (Scheme.Modules.pullbackSection f A D (ι ''ᵁ V) hV' s))
  have e8 : ∀ z : N.val.obj (op (ι ''ᵁ V)), N.val.map (homOfLE (le_refl (ι ''ᵁ V))).op z = z := by
    intro z
    rw [show (homOfLE (le_refl (ι ''ᵁ V))).op = 𝟙 _ from Subsingleton.elim _ _]
    simp
    rfl
  exact comp4_val_app_eq _ _ _ _ V _ _ _ _ _ rfl e2 e3 (e4.trans (e8 _))

end Ext

/-! ### Assertion (i) of Stacks Tag 01QK -/

section Normalization

/-- `U(ψ) ⟶ X ⟶ Y` is `r_{L, ψ}`, at `ψ` the identity of `Γ_*(X, 𝓛)`. -/
theorem ι_comp_projHom_eq_glued :
    (canonicalSections L).coveringOpen.ι ≫ projHomOfIsAmple L hL =
      (canonicalSections L).glued :=
  Stacks.SectionRingGluedComparison.ι_comp_projHomOfIsAmple_eq_glued L hL

include hL in
/-- `r_{L, ψ} : U(ψ) ⟶ Y` is an open immersion when `𝓛` is ample. -/
theorem isOpenImmersion_glued_canonicalSections :
    IsOpenImmersion (canonicalSections L).glued := by
  have := Stacks.SectionRingProjImmersion.isOpenImmersion_projHomOfIsAmple L hL
  rw [← ι_comp_projHom_eq_glued L hL]
  infer_instance

/-- The degree-`n` component of clause (2) of Stacks Tag 01PZ, `projTheta`, typed as a morphism
`r_{L, ψ}^*𝒪_Y(n) ⟶ 𝓛^{⊗ n}|_{U(ψ)}`. -/
def projThetaApp (n : ℤ) :
    (Scheme.Modules.pullback (canonicalSections L).glued).obj (twistY L n) ⟶
      (Scheme.Modules.restrictFunctor (canonicalSections L).coveringOpen.ι).obj
        (tensorPowerModule X L n) :=
  (Stacks.SectionRingProjMorphism.Theta.projTheta L).app n

section Charts

variable [IsOpenImmersion (projHomOfIsAmple L hL)]

/-- The chart `X_s`, read in `U(ψ)`. -/
theorem image_glued_preimage_chartOpen (c : GoodChart L hL) :
    (canonicalSections L).coveringOpen.ι ''ᵁ ((canonicalSections L).glued ⁻¹ᵁ chartOpen L hL c) =
      nvOpen L c.1.val :=
  ((canonicalSections L).chartOpen_eq (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val)
    c.1.deg_pos).trans
    (Stacks.SectionRingGluedComparison.nonvanishingOpen_canonicalSections_of L _ _ _)

omit [IsOpenImmersion (projHomOfIsAmple L hL)] in
/-- `r_{L, ψ}` on points, through `X ⟶ Y`. -/
theorem glued_apply (x : (canonicalSections L).coveringOpen.toScheme) :
    (canonicalSections L).glued x =
      (projHomOfIsAmple L hL) ((canonicalSections L).coveringOpen.ι x) :=
  (congrArg (fun g : (canonicalSections L).coveringOpen.toScheme ⟶
    AlgebraicGeometry.Proj (grading L) => g x) (ι_comp_projHom_eq_glued L hL).symm).trans
    (Scheme.Hom.comp_apply _ _ x)

/-- `D₊(s)` lies in the image of `r_{L, ψ}`. -/
theorem glued_image_preimage_chartOpen (c : GoodChart L hL) :
    haveI := isOpenImmersion_glued_canonicalSections L hL
    (canonicalSections L).glued ''ᵁ ((canonicalSections L).glued ⁻¹ᵁ chartOpen L hL c) =
      chartOpen L hL c := by
  have := isOpenImmersion_glued_canonicalSections L hL
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
  refine inf_eq_right.mpr fun y hy => ?_
  have hy' : y ∈ projHomOfIsAmple L hL ''ᵁ nvOpen L c.1.val := by
    rwa [Stacks.SectionRingProjQuasicoherent.image_nvOpen L hL c]
  obtain ⟨x, hx, rfl⟩ := hy'
  have hxU : x ∈ (canonicalSections L).coveringOpen :=
    ((canonicalSections L).nonvanishingOpenAt_le_coveringOpen_of_pos
      (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val) c.1.deg_pos)
      (by rwa [Stacks.SectionRingGluedComparison.nonvanishingOpen_canonicalSections_of])
  exact ⟨⟨x, hxU⟩, (glued_apply L hL _).trans (by simp)⟩

/-- The preimages of the good charts form a basis of `U(ψ)`. -/
theorem isBasis_glued_preimage_chartOpen :
    Opens.IsBasis (Set.range (fun c : GoodChart L hL =>
      (canonicalSections L).glued ⁻¹ᵁ chartOpen L hL c)) := by
  rw [Opens.isBasis_iff_nbhd]
  intro O x hx
  obtain ⟨W, ⟨c, rfl⟩, hxW, hWO⟩ := Opens.isBasis_iff_nbhd.mp
    (Stacks.SectionRingProjQuasicoherent.isBasis_goodChart L hL)
    (show (canonicalSections L).coveringOpen.ι.base x ∈
      (canonicalSections L).coveringOpen.ι ''ᵁ O from ⟨x, hx, rfl⟩)
  have hmem : ∀ z, z ∈ (canonicalSections L).glued ⁻¹ᵁ chartOpen L hL c ↔
      (canonicalSections L).coveringOpen.ι.base z ∈ nvOpen L c.1.val := fun z => by
    rw [← image_glued_preimage_chartOpen L hL c]
    exact ((canonicalSections L).coveringOpen.ι.isOpenEmbedding.injective.mem_set_image).symm
  refine ⟨_, ⟨c, rfl⟩, (hmem x).2 hxW, fun y hy => ?_⟩
  obtain ⟨z, hz, hzy⟩ := hWO (show (canonicalSections L).coveringOpen.ι.base y ∈
    (fun c : GoodChart L hL => nvOpen L c.1.val) c from (hmem y).1 hy)
  rwa [(canonicalSections L).coveringOpen.ι.isOpenEmbedding.injective hzy] at hz

/-- **Clause (2) of Tag 01PZ on a pulled-back section over a chart**: the chart formula of
Tag 01NK. -/
theorem projThetaApp_app_pullbackSection (n : ℤ) (c : GoodChart L hL)
    (s : Γ(twistY L n, chartOpen L hL c)) :
    Scheme.Modules.Hom.app (projThetaApp L n) ((canonicalSections L).glued ⁻¹ᵁ chartOpen L hL c)
        (Scheme.Modules.pullbackSection (canonicalSections L).glued (twistY L n)
          (chartOpen L hL c) ((canonicalSections L).glued ⁻¹ᵁ chartOpen L hL c) le_rfl s) =
      intChartSection (canonicalSections L) (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val)
        ((canonicalSections L).chartOpen_eq (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val)
          c.1.deg_pos).le c.1.deg_pos n
        (sectionsTwistEquivGradedPiece (grading L)
          (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val) c.1.deg_pos n s) :=
  Stacks.AlgebraicGeometry.ProjChartGradedTriple.app_pullbackSection_eq_intChartSection
    (Stacks.AlgebraicGeometry.ProjChartGradedTriple.isClauseTwo_theta (canonicalSections L))
    (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val) c.1.deg_pos
    ((canonicalSections L).chartOpen_eq (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val)
      c.1.deg_pos).le n s

/-- **Tag 01QJ's comparison on a pulled-back fraction, over an open inside a chart.** -/
theorem pullbackTildeComparison_app_pullbackSection_le (F : X.Modules) (c : GoodChart L hL)
    {V : X.Opens} (hV : V ≤ nvOpen L c.1.val)
    (y : Γ((tildeFunctor L).obj F, chartOpen L hL c)) :
    ((pullbackTildeComparison L hL).app F).app V
        (Scheme.Modules.pullbackSection (projHomOfIsAmple L hL) ((tildeFunctor L).obj F)
          (chartOpen L hL c) V (hV.trans (nvOpen_le_preimage L hL c)) y) =
      localDivision L F c.1.val hV
        (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (grading L)
          (moduleGrading F L) (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val)
          c.1.deg_pos y) := by
  have h1 := Stacks.AlgebraicGeometry.ProjChartRatioPullback.map_pullbackSectionHom
    (projHomOfIsAmple L hL) ((tildeFunctor L).obj F) (chartOpen L hL c) (nvOpen L c.1.val) V
    (homOfLE hV) (nvOpen_le_preimage L hL c) (hV.trans (nvOpen_le_preimage L hL c)) y
  have h2 := Stacks.Tag01VSPullbackTensor.homApp_presheaf_map
    ((pullbackTildeComparison L hL).app F) (homOfLE hV)
    (Scheme.Modules.pullbackSection (projHomOfIsAmple L hL) ((tildeFunctor L).obj F)
      (chartOpen L hL c) (nvOpen L c.1.val) (nvOpen_le_preimage L hL c) y)
  have h3 := pullbackTildeComparison_app_pullbackSection L hL F c y
  have h4 := Stacks.SectionRingProjQuasicoherent.map_localDivision L F c.1.val le_rfl (homOfLE hV)
    (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (grading L)
      (moduleGrading F L) (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val)
      c.1.deg_pos y)
  refine (congrArg (fun z => ((pullbackTildeComparison L hL).app F).app V z) h1.symm).trans ?_
  refine h2.trans ?_
  exact (congrArg (fun z => F.presheaf.map (homOfLE hV).op z) h3).trans h4

/-- The preimage of a chart under `U(ψ) ⟶ X ⟶ Y` lies in the preimage under `X ⟶ Y`. -/
theorem image_le_preimage_chartOpen (c : GoodChart L hL) :
    ((canonicalSections L).coveringOpen.ι ''ᵁ
        ((canonicalSections L).glued ⁻¹ᵁ chartOpen L hL c)) ≤
      projHomOfIsAmple L hL ⁻¹ᵁ chartOpen L hL c :=
  (le_of_eq (image_glued_preimage_chartOpen L hL c)).trans (nvOpen_le_preimage L hL c)

/-- **`θ_{𝓛^{⊗ n}}` transported to `r_{L, ψ}^*𝒪_Y(n)`, on a pulled-back section**: `twistThetaInt`
on the section pulled back along `X ⟶ Y`. -/
theorem twistThetaGlued_app_pullbackSection (n : ℤ) (c : GoodChart L hL)
    (s : Γ(twistY L n, chartOpen L hL c)) :
    ((Scheme.Modules.pullbackCongr (ι_comp_projHom_eq_glued L hL)).inv.app (twistY L n) ≫
    (Scheme.Modules.pullbackComp (canonicalSections L).coveringOpen.ι
      (projHomOfIsAmple L hL)).inv.app (twistY L n) ≫
    (Scheme.Modules.pullback (canonicalSections L).coveringOpen.ι).map (twistThetaInt L hL n) ≫
    (Scheme.Modules.restrictFunctorIsoPullback (canonicalSections L).coveringOpen.ι).inv.app
      (tensorPowerModule X L n)).val.app (op ((canonicalSections L).glued ⁻¹ᵁ chartOpen L hL c))
        (Scheme.Modules.pullbackSection (canonicalSections L).glued (twistY L n)
          (chartOpen L hL c) ((canonicalSections L).glued ⁻¹ᵁ chartOpen L hL c) le_rfl s) =
      (twistThetaInt L hL n).val.app
        (op ((canonicalSections L).coveringOpen.ι ''ᵁ
          ((canonicalSections L).glued ⁻¹ᵁ chartOpen L hL c)))
        (Scheme.Modules.pullbackSection (projHomOfIsAmple L hL) (twistY L n) (chartOpen L hL c)
          ((canonicalSections L).coveringOpen.ι ''ᵁ
            ((canonicalSections L).glued ⁻¹ᵁ chartOpen L hL c))
          (image_le_preimage_chartOpen L hL c) s) :=
  transport_app_pullbackSection (canonicalSections L).coveringOpen.ι (projHomOfIsAmple L hL)
    (canonicalSections L).glued (ι_comp_projHom_eq_glued L hL) (twistY L n)
    (tensorPowerModule X L n) (twistThetaInt L hL n) (chartOpen L hL c)
    ((canonicalSections L).glued ⁻¹ᵁ chartOpen L hL c) le_rfl
    (image_le_preimage_chartOpen L hL c) s

/-- **`twistThetaInt` on a pulled-back section over a chart**: the chart formula of Tag 01NK. -/
theorem twistThetaInt_app_pullbackSection_chart (n : ℤ) (c : GoodChart L hL)
    (s : Γ(twistY L n, chartOpen L hL c)) :
    (twistThetaInt L hL n).val.app
        (op ((canonicalSections L).coveringOpen.ι ''ᵁ
          ((canonicalSections L).glued ⁻¹ᵁ chartOpen L hL c)))
        (Scheme.Modules.pullbackSection (projHomOfIsAmple L hL) (twistY L n) (chartOpen L hL c)
          ((canonicalSections L).coveringOpen.ι ''ᵁ
            ((canonicalSections L).glued ⁻¹ᵁ chartOpen L hL c))
          (image_le_preimage_chartOpen L hL c) s) =
      intChartSection (canonicalSections L) (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val)
        ((canonicalSections L).chartOpen_eq (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val)
          c.1.deg_pos).le c.1.deg_pos n
        (sectionsTwistEquivGradedPiece (grading L)
          (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val) c.1.deg_pos n s) := by
  have hV : ((canonicalSections L).coveringOpen.ι ''ᵁ
      ((canonicalSections L).glued ⁻¹ᵁ chartOpen L hL c)) ≤ nvOpen L c.1.val :=
    le_of_eq (image_glued_preimage_chartOpen L hL c)
  have e5 := Scheme.Modules.pullbackSection_naturality (projHomOfIsAmple L hL)
    (twistPowIdent L n).hom (chartOpen L hL c)
    ((canonicalSections L).coveringOpen.ι ''ᵁ ((canonicalSections L).glued ⁻¹ᵁ chartOpen L hL c))
    (image_le_preimage_chartOpen L hL c) s
  have e6 := pullbackTildeComparison_app_pullbackSection_le L hL (tensorPowerModule X L n) c hV
    ((twistPowIdent L n).hom.val.app (op (chartOpen L hL c)) s)
  have e7 := localDivision_eq_intChartSection L n c.1.val c.1.deg_pos hV
    ((canonicalSections L).chartOpen_eq (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val)
      c.1.deg_pos).le s
  exact (congrArg (fun z => ((Stacks.SectionRingProjQuasicoherent.pullbackTildeComparison L hL).app
    (tensorPowerModule X L n)).val.app (op ((canonicalSections L).coveringOpen.ι ''ᵁ
      ((canonicalSections L).glued ⁻¹ᵁ chartOpen L hL c))) z) e5).trans (e6.trans e7)


/-- **Tag 01QJ's comparison for `𝓛^{⊗ n}`, read on `r_{L, ψ}^*𝒪_Y(n)`, on a pulled-back section
over a chart**: the chart formula of Tag 01NK. -/
theorem cmp_twistThetaInt_app_pullbackSection (n : ℤ) (c : GoodChart L hL)
    (s : Γ(twistY L n, chartOpen L hL c)) :
    Scheme.Modules.Hom.app
      ((Scheme.Modules.pullbackCongr (ι_comp_projHom_eq_glued L hL)).inv.app (twistY L n) ≫
    (Scheme.Modules.pullbackComp (canonicalSections L).coveringOpen.ι
      (projHomOfIsAmple L hL)).inv.app (twistY L n) ≫
    (Scheme.Modules.pullback (canonicalSections L).coveringOpen.ι).map (twistThetaInt L hL n) ≫
    (Scheme.Modules.restrictFunctorIsoPullback (canonicalSections L).coveringOpen.ι).inv.app
      (tensorPowerModule X L n)) ((canonicalSections L).glued ⁻¹ᵁ chartOpen L hL c)
        (Scheme.Modules.pullbackSection (canonicalSections L).glued (twistY L n)
          (chartOpen L hL c) ((canonicalSections L).glued ⁻¹ᵁ chartOpen L hL c) le_rfl s) =
      intChartSection (canonicalSections L) (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val)
        ((canonicalSections L).chartOpen_eq (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val)
          c.1.deg_pos).le c.1.deg_pos n
        (sectionsTwistEquivGradedPiece (grading L)
          (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val) c.1.deg_pos n s) :=
  (twistThetaGlued_app_pullbackSection L hL n c s).trans
    (twistThetaInt_app_pullbackSection_chart L hL n c s)

/-- The two sides of assertion (i) agree on every section over the preimage of a good chart. -/
theorem projThetaApp_app_eq (n : ℤ) (c : GoodChart L hL)
    (x : Γ((Scheme.Modules.pullback (canonicalSections L).glued).obj (twistY L n),
      ((canonicalSections L).glued ⁻¹ᵁ chartOpen L hL c))) :
    Scheme.Modules.Hom.app (projThetaApp L n) ((canonicalSections L).glued ⁻¹ᵁ chartOpen L hL c) x =
      Scheme.Modules.Hom.app
        ((Scheme.Modules.pullbackCongr (ι_comp_projHom_eq_glued L hL)).inv.app (twistY L n) ≫
    (Scheme.Modules.pullbackComp (canonicalSections L).coveringOpen.ι
      (projHomOfIsAmple L hL)).inv.app (twistY L n) ≫
    (Scheme.Modules.pullback (canonicalSections L).coveringOpen.ι).map (twistThetaInt L hL n) ≫
    (Scheme.Modules.restrictFunctorIsoPullback (canonicalSections L).coveringOpen.ι).inv.app
      (tensorPowerModule X L n)) ((canonicalSections L).glued ⁻¹ᵁ chartOpen L hL c) x := by
  have := isOpenImmersion_glued_canonicalSections L hL
  obtain ⟨s, rfl⟩ := pullbackSection_surjective_of_image (canonicalSections L).glued
    (twistY L n) (chartOpen L hL c) (glued_image_preimage_chartOpen L hL c) x
  exact (projThetaApp_app_pullbackSection L hL n c s).trans
    (cmp_twistThetaInt_app_pullbackSection L hL n c s).symm


/-- Morphisms out of `r_{L, ψ}^*𝒪_Y(n)` are determined over the preimages of the good charts. -/
theorem hom_ext_glued_chart (n : ℤ)
    {φ ψ : (Scheme.Modules.pullback (canonicalSections L).glued).obj (twistY L n) ⟶
      (Scheme.Modules.restrictFunctor (canonicalSections L).coveringOpen.ι).obj
        (tensorPowerModule X L n)}
    (h : ∀ (c : GoodChart L hL)
      (a : Γ((Scheme.Modules.pullback (canonicalSections L).glued).obj (twistY L n),
        ((canonicalSections L).glued ⁻¹ᵁ chartOpen L hL c))),
      Scheme.Modules.Hom.app φ ((canonicalSections L).glued ⁻¹ᵁ chartOpen L hL c) a =
        Scheme.Modules.Hom.app ψ ((canonicalSections L).glued ⁻¹ᵁ chartOpen L hL c) a) :
    φ = ψ :=
  modules_hom_ext_of_isBasis _ (isBasis_glued_preimage_chartOpen L hL) h

/-- **Assertion (i) of Stacks Tag 01QK**, at the typing `projThetaApp`. -/
theorem projThetaApp_eq_twistThetaInt (n : ℤ) :
    projThetaApp L n =
      ((Scheme.Modules.pullbackCongr (ι_comp_projHom_eq_glued L hL)).inv.app (twistY L n) ≫
    (Scheme.Modules.pullbackComp (canonicalSections L).coveringOpen.ι
      (projHomOfIsAmple L hL)).inv.app (twistY L n) ≫
    (Scheme.Modules.pullback (canonicalSections L).coveringOpen.ι).map (twistThetaInt L hL n) ≫
    (Scheme.Modules.restrictFunctorIsoPullback (canonicalSections L).coveringOpen.ι).inv.app
      (tensorPowerModule X L n)) :=
  hom_ext_glued_chart L hL n (projThetaApp_app_eq L hL n)

end Charts

/-- In Situation Stacks Tag 01QH, the map `f^*𝒪_Y(n) ⟶ 𝓛^{⊗ n}` of Stacks Tag 01QI — the
degree-`n` component of clause (2) of Stacks Tag 01PZ, `projTheta`, which lives on
`U(ψ) = ⋃_a X_a` — is `θ_{𝓛^{⊗ n}}`: Tag 01QJ's comparison for `𝓛^{⊗ n}`, read on `f^*𝒪_Y(n)`
through the obvious identification `𝒪_Y(n) ≅ (Γ_*(X, 𝓛, 𝓛^{⊗ n}))~` (`twistThetaInt`), for every
integer `n`. Since `projTheta` lives on `U(ψ)`, the right side is `θ_{𝓛^{⊗ n}}` pulled back along
the inclusion `U(ψ) ⟶ X`, with `r_{L, ψ} : U(ψ) ⟶ Y` identified with `U(ψ) ⟶ X ⟶ Y` and the
pullback along an open immersion with the restriction. -/
@[stacks 01QK "assertion (i), with no extra hypothesis: the isomorphism f^*O_Y(n) -> L^n of
Tag 01QI (the degree-n component of clause (2) of Tag 01PZ, defined on U(psi)) equals
theta_{L^n}, theta being the constructed comparison pullbackTildeComparison of Tag 01QJ read on
f^*O_Y(n) through the obvious identification O_Y(n) = (Gamma_*(X, L, L^n))~, for every integer
n"]
theorem projTheta_app_eq_twistThetaInt (n : ℤ) :
    (Stacks.SectionRingProjMorphism.Theta.projTheta L).app n =
      ((Scheme.Modules.pullbackCongr (ι_comp_projHom_eq_glued L hL)).inv.app (twistY L n) ≫
    (Scheme.Modules.pullbackComp (canonicalSections L).coveringOpen.ι
      (projHomOfIsAmple L hL)).inv.app (twistY L n) ≫
    (Scheme.Modules.pullback (canonicalSections L).coveringOpen.ι).map (twistThetaInt L hL n) ≫
    (Scheme.Modules.restrictFunctorIsoPullback (canonicalSections L).coveringOpen.ι).inv.app
      (tensorPowerModule X L n)) :=
  have := Stacks.SectionRingProjImmersion.isOpenImmersion_projHomOfIsAmple L hL
  projThetaApp_eq_twistThetaInt L hL n

end Normalization

end Stacks.SectionRingProjTheta

end
