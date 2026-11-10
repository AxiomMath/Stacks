module

public import StacksFrontier.AlgebraicGeometry.SectionRingProjQuasicoherent.Division
public import StacksFrontier.AlgebraicGeometry.ModuleSectionExtension.Basic
public import StacksFrontier.AlgebraicGeometry.SectionRingProjOverlap.Basic

/-!
# Stacks Tag 01PW for the division by the powers of a section

Let `X` be a scheme, `L` an ample invertible `𝒪_X`-module, `ℱ` a quasi-coherent `𝒪_X`-module and
`a` a global section of `L ^⊗ d`, `d > 0`. The division
`Stacks.SectionRingProjQuasicoherent.localDivision` sends the degree-zero localization
`Γ_*(X, L, ℱ)_{(a)}` to `Γ(X_a, ℱ)`. This file proves that it is **bijective**, which is Stacks
Tag 01PW for `ℱ`: injectivity says that a twisted section vanishing on `X_a` is killed by a power
of `a`, and surjectivity that every section of `ℱ` over `X_a`, multiplied by a power of `a`,
extends to a twisted global section.

Both halves are the usual argument over a finite affine cover of `X` by nonvanishing opens `X_{c}`
of one common degree: on `X_c` the section `aᵐ` is a function `g` times `c`, so `X_a ∩ X_c` is the
basic open of `g`, where a quasi-coherent module is a localization. The multiplication by a power
of `a` is compared with the multiplication by the function `g` through
`Stacks.SectionRingProjQuasicoherent.twistMul_app_eq_smul`.

## Main results

* `Stacks.SectionRingProjQuasicoherent.twistMul_app_eq_smul`: multiplication by a section depends
  `𝒪`-linearly on its restriction.
* `Stacks.SectionRingProjQuasicoherent.exists_twistMul_powSec_eq_zero_of_cover`: a twisted section
  vanishing on `X_a` is killed by a power of `a`.
* `Stacks.SectionRingProjQuasicoherent.localDivision_injective` and
  `Stacks.SectionRingProjQuasicoherent.localDivision_surjective`: **Stacks Tag 01PW** for the
  division.

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections mul mulMap sectionRing)
open Stacks.TwistedSections (twistPow twistSections twistModule)
open Stacks.SectionProduct (globalSection monoidalUnitSection)
open Stacks.AmpleFiniteAvoidance (nvOpen grading)
open Stacks.SectionExtension (powSec)
open scoped Stacks.GradedLocalization

universe u

namespace Stacks.SectionRingProjQuasicoherent

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (F : X.Modules)

/-! ### Multiplication by a section, on sections -/

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- **Multiplication by a section on the sections over `V`** is the sectionwise tensor product with
the restriction of the section, followed by the collecting isomorphism. -/
theorem twistMul_app_eq {j : ℕ} (b : powSections L j) (m : ℕ) (V : X.Opens)
    (z : Γ(twistPow F L m, V)) :
    (twistMul (F := F) b m).app V z =
      (twistPowAddIso F L m j).inv.app V
        (Stacks.SectionTensorFormula.tensorSection (twistPow F L m) (natTensorPow L j) z
          (unitSec b V)) := by
  have h : twistMul (F := F) b m =
      Stacks.TensorSectionNonvanishing.mulRight (twistPow F L m) b ≫
        (twistPowAddIso F L m j).inv := by
    rw [twistMul, Stacks.TensorSectionNonvanishing.mulRight, Category.assoc]
  rw [h]
  exact congrArg (fun w => (twistPowAddIso F L m j).inv.app V w)
    (Stacks.SectionProduct.mulSec_eq_tensorSection (twistPow F L m) (natTensorPow L j) b z)

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- **Multiplication by a section depends `𝒪`-linearly on its restriction**: if `b|_V = g · b'|_V`
then multiplying by `b` on the sections over `V` is `g` times multiplying by `b'`. -/
theorem twistMul_app_eq_smul {j : ℕ} (b b' : powSections L j) {V : X.Opens} (g : Γ(X, V))
    (h : unitSec b V = g • unitSec b' V) (m : ℕ) (z : Γ(twistPow F L m, V)) :
    (twistMul (F := F) b m).app V z = g • (twistMul (F := F) b' m).app V z := by
  rw [twistMul_app_eq, twistMul_app_eq, h, Stacks.SectionTensorFormula.tensorSection_smul_right,
    Scheme.Modules.Hom.app_smul]

/-- A morphism out of the monoidal unit is zero once its section over `⊤` is. -/
theorem eq_zero_of_unitSec_top_eq_zero {M : X.Modules} (t : 𝟙_ X.Modules ⟶ M)
    (h : unitSec t ⊤ = 0) : t = 0 :=
  (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X M).map_eq_zero_iff.mp
    ((Stacks.SectionProduct.globalSection_eq_app_monoidalUnitSection M t).trans h)

/-! ### Injectivity -/

/-- **A twisted section vanishing on `X_a` is killed by a power of `a`**, given a finite affine
cover of `X` by nonvanishing opens of sections `c i` of the same degree as `a`, and a degree
divisible by that degree. On `X_{c i}` the twisted section is `c iᵠ` times a section `y` of `ℱ`,
and `a = g · c i` there with `X_a ∩ X_{c i} = D(g)`; quasi-coherence kills `y` by a power of `g`,
hence the twisted section by a power of `a`, and the sheaf condition glues. -/
theorem exists_twistMul_powSec_eq_zero_of_cover [F.IsQuasicoherent] {N : ℕ}
    (a : powSections L N) {ι : Type u} [Finite ι] (c : ι → powSections L N)
    (hcaff : ∀ i, IsAffineOpen (nvOpen L (c i)))
    (hcover : (⊤ : X.Opens) ≤ ⨆ i, nvOpen L (c i)) (q : ℕ)
    (w : twistSections F L (N * q)) (hw : unitSec w (nvOpen L a) = 0) :
    ∃ k : ℕ, w ≫ twistMul (powSec L a k) (N * q) = 0 := by
  classical
  choose f hf using fun i => Stacks.SectionExtension.exists_resTop_eq_smul
    (natTensorPow L N) (globalSection X _ (c i)) (globalSection X _ a)
    (le_refl (nvOpen L (c i)))
  have hD : ∀ i, nvOpen L a ⊓ nvOpen L (c i) = X.basicOpen (f i) := fun i =>
    Stacks.SectionExtension.nonvanishingOpen_inf_eq_basicOpen (globalSection X _ (c i))
      (globalSection X _ a) (le_refl (nvOpen L (c i))) (f i) (hf i)
  have hBa : ∀ i, X.basicOpen (f i) ≤ nvOpen L a := fun i => (hD i) ▸ inf_le_left
  have hBc : ∀ i, X.basicOpen (f i) ≤ nvOpen L (c i) := fun i => X.basicOpen_le (f i)
  have key : ∀ i, ∃ e : ℕ, f i ^ e •
      (divEquiv L F (c i) le_rfl q).symm (unitSec w (nvOpen L (c i))) = 0 := by
    intro i
    refine Stacks.ModuleSectionExtension.exists_pow_smul_eq_zero F (hcaff i) (f i) _ ?_
    apply (bijective_powMul_app L F (c i) (hBc i) q).1
    rw [map_zero]
    refine (PresheafOfModules.naturality_apply
      ((Stacks.SectionProduct.forgetFun X).map (powMul L F (c i) q)) (homOfLE (hBc i)).op
      ((divEquiv L F (c i) le_rfl q).symm (unitSec w (nvOpen L (c i))))).trans ?_
    change (twistPow F L (N * q)).presheaf.map (homOfLE (hBc i)).op
      ((powMul L F (c i) q).app (nvOpen L (c i))
        ((divEquiv L F (c i) le_rfl q).symm (unitSec w (nvOpen L (c i))))) = 0
    rw [← divEquiv_apply L F (c i) le_rfl q, LinearEquiv.apply_symm_apply,
      map_unitSec, ← map_unitSec w (homOfLE (hBa i)), hw, map_zero]
  choose e he using key
  obtain ⟨K, hK⟩ := Stacks.SectionExtension.exists_forall_le e
  refine ⟨K, eq_zero_of_unitSec_top_eq_zero _ ?_⟩
  refine TopCat.Presheaf.IsSheaf.section_ext (twistPow F L (N * q + N * K)).isSheaf
    (U := op ⊤) ?_
  intro x _
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcover (TopologicalSpace.Opens.mem_top x))
  refine ⟨nvOpen L (c i), le_top, hi, ?_⟩
  rw [map_zero, map_unitSec, unitSec_comp]
  have hpow : unitSec (powSec L a K) (nvOpen L (c i)) =
      f i ^ K • unitSec (powSec L (c i) K) (nvOpen L (c i)) := by
    rw [unitSec_eq_map_globalSection, unitSec_eq_map_globalSection]
    exact Stacks.SectionExtension.resTop_globalSection_powSec L (c i) a (f i) (hf i) K
  rw [twistMul_app_eq_smul L F _ _ (f i ^ K) hpow,
    ← LinearEquiv.apply_symm_apply (divEquiv L F (c i) le_rfl q)
      (unitSec w (nvOpen L (c i))), divEquiv_apply]
  change f i ^ K • (powMul L F (c i) q ≫ twistMul (powSec L (c i) K) (N * q)).app _ _ = 0
  rw [← Scheme.Modules.Hom.app_smul,
    show f i ^ K = f i ^ (K - e i) * f i ^ e i by rw [← pow_add, Nat.sub_add_cancel (hK i)],
    mul_smul, he i, smul_zero, map_zero]

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- Multiplying by `aˢ` and then by `(aʳ)ᵏ` is multiplying by `a^{s + r k}`. -/
theorem twistMul_powSec_comp_twistMul_powSec {d : ℕ} (a : powSections L d) (r s k m : ℕ) :
    twistMul (F := F) (powSec L a s) m ≫ twistMul (powSec L (powSec L a r) k) (m + d * s) =
      twistMul (powSec L a (s + r * k)) m ≫
        eqToHom (congrArg (twistPow F L)
          (by ring : m + d * (s + r * k) = m + d * s + d * r * k)) := by
  have hof : DirectSum.of (powSections L) (d * s + d * r * k)
      (mul (powSec L a s) (powSec L (powSec L a r) k)) =
      DirectSum.of (powSections L) (d * (s + r * k)) (powSec L a (s + r * k)) := by
    rw [Stacks.SectionRingChartMap.of_mul_eq, Stacks.SectionRingChartMap.of_powSec_eq_pow,
      Stacks.SectionRingChartMap.of_powSec_eq_pow, Stacks.SectionRingChartMap.of_powSec_eq_pow,
      Stacks.SectionRingChartMap.of_powSec_eq_pow, ← pow_mul, ← pow_add]
  rw [twistMul_comp_twistMul, ← twistMul_congr_of (F := F)
    (by ring : d * s + d * r * k = d * (s + r * k))
    (mul (powSec L a s) (powSec L (powSec L a r) k)) (powSec L a (s + r * k)) hof m,
    Category.assoc, eqToHom_trans]

/-- A finite affine cover of `X` by nonvanishing opens of sections of degree `d * r`, `1 ≤ r`. -/
private theorem exists_pow_degree_affine_cover (hL : Stacks.Ample.IsAmple X L) {d : ℕ}
    (hd : 0 < d) (a : powSections L d) :
    ∃ (r : ℕ) (ι : Type u) (_ : Finite ι) (c : ι → powSections L (d * r)), 1 ≤ r ∧
      (∀ i, IsAffineOpen (nvOpen L (c i))) ∧ (⊤ : X.Opens) ≤ ⨆ i, nvOpen L (c i) := by
  obtain ⟨N, -, F0, c, hN1, ⟨r, rfl⟩, -, hcaff, hcover⟩ :=
    Stacks.SectionExtension.exists_common_degree_affine_cover L hL hd a
  exact ⟨r, _, inferInstance, c, Nat.one_le_iff_ne_zero.mpr fun h => by simp [h] at hN1,
    hcaff, hcover⟩

/-- **Stacks Tag 01PW, injectivity**: the division `Γ_*(X, L, ℱ)_{(a)} ⟶ Γ(X_a, ℱ)` is injective,
for `L` ample and `ℱ` quasi-coherent. -/
theorem localDivision_injective (hL : Stacks.Ample.IsAmple X L) [F.IsQuasicoherent] {d : ℕ}
    (hd : 0 < d) (a : powSections L d) :
    Function.Injective (localDivision L F a (le_refl (nvOpen L a))) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨n, x, hx, hzrep⟩ :=
    Stacks.SheafOfModules.degreeZeroLocalization_exists_fraction_of_degree (grading L)
      (Stacks.TwistedSections.moduleGrading F L) (Stacks.ExternalGrading.of_mem_summand d a) z
  obtain ⟨t, rfl⟩ := Stacks.TwistedSections.mem_moduleGrading_natCast_iff.mp hx
  have h0 : unitSec (Stacks.TwistedSections.twistCongr (Nat.mul_comm n d) t) (nvOpen L a) = 0 := by
    rw [← powMul_app_localDivision L F a le_rfl z n t hzrep, hz, map_zero]
  obtain ⟨r, ι, _, c, hr, hcaff, hcover⟩ := exists_pow_degree_affine_cover L hL hd a
  have hdeg : d * n + d * ((r - 1) * n) = d * r * n := by
    conv_rhs => rw [← Nat.sub_add_cancel hr]
    ring
  set s := (r - 1) * n
  set w1 : twistSections F L (d * r * n) :=
    Stacks.TwistedSections.twistCongr (Nat.mul_comm n d) t ≫ twistMul (powSec L a s) (d * n) ≫
      eqToHom (congrArg (twistPow F L) hdeg) with hw1def
  have hw1 : unitSec w1 (nvOpen L (powSec L a r)) = 0 := by
    rw [Stacks.SectionRingProjOverlap.nvOpen_powSec_of_one_le L a r hr]
    change (eqToHom (congrArg (twistPow F L) hdeg)).app (nvOpen L a)
      ((twistMul (powSec L a s) (d * n)).app (nvOpen L a)
        (unitSec (Stacks.TwistedSections.twistCongr (Nat.mul_comm n d) t) (nvOpen L a))) = 0
    rw [h0, map_zero, map_zero]
  obtain ⟨k, hk⟩ := exists_twistMul_powSec_eq_zero_of_cover L F (powSec L a r) c hcaff hcover n
    w1 hw1
  refine (Stacks.SheafOfModules.eq_zero_iff_exists_pow_smul_eq_zero (grading L)
    (Stacks.TwistedSections.moduleGrading F L) z n _ hzrep).mpr ⟨s + r * k, ?_⟩
  rw [← Stacks.SectionRingChartMap.of_powSec_eq_pow, of_smul_of_eq_twistMul]
  have hmor : t ≫ twistMul (powSec L a (s + r * k)) (n * d) = 0 := by
    rw [hw1def] at hk
    simp only [Stacks.TwistedSections.twistCongr, Category.assoc] at hk
    rw [eqToHom_comp_twistMul (powSec L (powSec L a r) k) hdeg,
      ← Category.assoc (twistMul (powSec L a s) (d * n)), twistMul_powSec_comp_twistMul_powSec,
      Category.assoc, eqToHom_comp_twistMul_assoc (powSec L a (s + r * k)) (Nat.mul_comm n d)]
      at hk
    simp only [eqToHom_trans] at hk
    rw [← Category.assoc] at hk
    exact (cancel_mono _).mp (hk.trans Limits.zero_comp.symm)
  rw [hmor, map_zero]

/-! ### Surjectivity -/

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- The `k`-th member of `Stacks.TensorPowerTrivialize.sectionPow` names `u ^ (k + 1)`. -/
theorem of_sectionPow_eq_pow {n : ℕ} (u : powSections L n) :
    ∀ k : ℕ, DirectSum.of (powSections L) (Stacks.TensorPowerTrivialize.powDeg n k)
      (Stacks.TensorPowerTrivialize.sectionPow L u k) = DirectSum.of (powSections L) n u ^ (k + 1)
  | 0 => (pow_one _).symm
  | k + 1 => by
      change DirectSum.of (powSections L) (Stacks.TensorPowerTrivialize.powDeg n k + n)
        (mul (Stacks.TensorPowerTrivialize.sectionPow L u k) u) = _
      rw [Stacks.SectionRingChartMap.of_mul_eq, of_sectionPow_eq_pow u k, ← pow_succ]

/-- **Stacks Tag 01PW, surjectivity**: every section of `ℱ` over `X_a` is the division of a twisted
global section by a power of `a`, for `L` ample and `ℱ` quasi-coherent. -/
theorem localDivision_surjective (hL : Stacks.Ample.IsAmple X L) [F.IsQuasicoherent] {d : ℕ}
    (hd : 0 < d) (a : powSections L d) :
    Function.Surjective (localDivision L F a (le_refl (nvOpen L a))) := by
  intro u
  obtain ⟨r, ι, _, c, hr, hcaff, hcover⟩ := exists_pow_degree_affine_cover L hL hd a
  obtain ⟨K, τ, -, hτ⟩ :=
    Stacks.ModuleSectionExtension.exists_sectionPow_tensorSection_family_of_affine_cover L F
      (powSec L a r) c (nvOpen L a) (Stacks.SectionRingProjOverlap.nvOpen_powSec_of_one_le L a r hr)
      (fun i => nvOpen L (c i)) (fun _ => rfl) hcaff hcover (κ := PUnit.{u + 1}) (fun _ => u)
  set n := r * (K + 1) with hn
  have hP : Stacks.TensorPowerTrivialize.powDeg (d * r) K = d * n := by
    rw [Stacks.TensorPowerTrivialize.powDeg_eq, hn]
    ring
  have hof : DirectSum.of (powSections L) (Stacks.TensorPowerTrivialize.powDeg (d * r) K)
      (Stacks.TensorPowerTrivialize.sectionPow L (powSec L a r) K) =
      DirectSum.of (powSections L) (d * n) (powSec L a n) := by
    rw [of_sectionPow_eq_pow, Stacks.SectionRingChartMap.of_powSec_eq_pow,
      Stacks.SectionRingChartMap.of_powSec_eq_pow, ← pow_mul]
  set σ := Stacks.TensorPowerTrivialize.sectionPow L (powSec L a r) K
  set τm := (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X
    (F ⊗ natTensorPow L (Stacks.TensorPowerTrivialize.powDeg (d * r) K))).symm
      (τ PUnit.unit)
  have hdeg : 0 + Stacks.TensorPowerTrivialize.powDeg (d * r) K = n * d := by
    rw [hP, Nat.zero_add, Nat.mul_comm]
  set T : twistSections F L (n * d) :=
    τm ≫ (twistPowAddIso F L 0 (Stacks.TensorPowerTrivialize.powDeg (d * r) K)).inv ≫
      eqToHom (congrArg (twistPow F L) hdeg) with hT
  refine ⟨⟨LocalizedModule.mk (DirectSum.of (twistSections F L) (n * d) T)
      ⟨DirectSum.of (powSections L) d a ^ n, ⟨n, rfl⟩⟩,
    Stacks.SheafOfModules.mk_mem_degreeZeroLocalization_of_degree (grading L)
      (Stacks.TwistedSections.moduleGrading F L) (Stacks.ExternalGrading.of_mem_summand d a) n
      (DirectSum.of (twistSections F L) (n * d) T) ⟨T, rfl⟩⟩, ?_⟩
  rw [localDivision_fraction L F a le_rfl _ n T rfl, LinearEquiv.symm_apply_eq, divEquiv_apply]
  have hτm' : unitSec τm (nvOpen L a) = Stacks.SectionTensorFormula.tensorSection F
      (natTensorPow L (Stacks.TensorPowerTrivialize.powDeg (d * r) K)) u
      (unitSec σ (nvOpen L a)) := by
    rw [unitSec_eq_map_globalSection, unitSec_eq_map_globalSection,
      show globalSection X _ τm = τ PUnit.unit from
        (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _).apply_symm_apply _]
    exact hτ PUnit.unit
  have E : twistPow F L (0 + Stacks.TensorPowerTrivialize.powDeg (d * r) K) =
      twistPow F L (d * n) :=
    congrArg (twistPow F L) (by rw [hP, Nat.zero_add])
  have key : powMul L F a n = twistMul σ 0 ≫ eqToHom E := by
    rw [powMul_eq_twistMul, ← twistMul_congr_of (F := F) hP σ (powSec L a n) hof 0,
      Category.assoc, eqToHom_trans]
    exact Category.id_comp _
  have keyT : Stacks.TwistedSections.twistCongr (Nat.mul_comm n d) T =
      τm ≫ (twistPowAddIso F L 0 (Stacks.TensorPowerTrivialize.powDeg (d * r) K)).inv ≫
        eqToHom E := by
    rw [Stacks.TwistedSections.twistCongr, hT]
    exact congrArg (τm ≫ ·) ((Category.assoc _ _ _).trans (congrArg _ (eqToHom_trans _ _)))
  rw [keyT, key]
  exact (congrArg (fun w => (eqToHom E).app (nvOpen L a) w)
    ((twistMul_app_eq L F σ 0 (nvOpen L a) u).trans (congrArg (fun w =>
      (twistPowAddIso F L 0 _).inv.app (nvOpen L a) w) hτm'.symm))).symm

end Stacks.SectionRingProjQuasicoherent

end
