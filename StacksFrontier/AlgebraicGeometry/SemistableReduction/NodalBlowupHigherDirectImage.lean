module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NodalResolution
public import StacksFrontier.AlgebraicGeometry.Blowup.PointBlowupHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.FlatPullbackStalk.Basic

/-!
# Higher direct images along the blowup of a singular point of a nodal family

Let `R` be a discrete valuation ring, `f : X ⟶ Spec R` at-worst-nodal of relative dimension one,
and `x ∈ X` a closed point with an étale nodal chart of exponent `n ≥ 2` ([Stacks, Tag 0CDD]):
étale-locally `X` is `Spec R'[u, v]/(uv - πⁿ)` near the origin. Let `b : X' ⟶ X` be the blowup
of `X` in `x`, as in the proof of [Stacks, Tag 0CDE]. Then `R^q b_*𝒪_{X'} = 0` for every `q > 0`.

The local computation is on the standard nodal model `A = R'[u, v]/(uv - πⁿ)`: its maximal ideal
`𝔪 = (π, u, v)` at the origin satisfies `𝔪² = (π, u + v) 𝔪` when `n ≥ 2`, because
`u² = u(u + v) - πⁿ` and `πⁿ = π · πⁿ⁻¹` with `πⁿ⁻¹ ∈ 𝔪`. So `(π, u + v)` is a reduction of
reduction number one, and the blowup of `Spec A` in `𝔪` has no higher cohomology
(`AlgebraicGeometry.isZero_Hgroup_blowUp_maximalIdeal_of_sq_eq`). By [Stacks, Tag 0805] the
blowup of the chart is the base change of `X'` and of the blowup of the local model, and flat base
change ([Stacks, Tag 02KH]) carries the vanishing from the local model to the chart; flat pullback
reflects the vanishing of stalks, and away from `x` the blowup is an isomorphism.

## Main results

* `Stacks.SemistableReduction.nodalCenter_sq_eq`: `𝔪² = (π, u + v) 𝔪` in `R'[u, v]/(uv - πⁿ)`.
* `Stacks.SemistableReduction.isZero_rightDerivedPlus_pushforward_blowUp_of_nodalChartAt`:
  `R^q b_*𝒪_{X'} = 0` for `q > 0`.

## Implementation notes

Higher direct images are the `ℤ`-indexed `CategoryTheory.Functor.rightDerivedPlus` in the
standard model of the derived category, in which flat base change is stated.

## References

* [Stacks Project, Tag 0CDC](https://stacks.math.columbia.edu/tag/0CDC)
* [Stacks Project, Tag 0CDE](https://stacks.math.columbia.edu/tag/0CDE)
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.Cohomology.Basis

universe u

namespace Stacks.SemistableReduction

attribute [local instance] HasDerivedCategory.standard

open Scheme.IdealSheafData

/-- **`𝔪² = (π, u + v) 𝔪` at the origin of the standard nodal model of exponent `n ≥ 2`.** -/
theorem nodalCenter_sq_eq {R : Type u} [CommRing R] (π : R) {n : ℕ} (hn : 2 ≤ n) :
    nodalCenter R π (π ^ n) ^ 2 =
      Ideal.span {algebraMap R (nodalChartRing R (π ^ n)) π,
        nodalGen R (π ^ n) 0 + nodalGen R (π ^ n) 1} * nodalCenter R π (π ^ n) := by
  set p := algebraMap R (nodalChartRing R (π ^ n)) π
  set x := nodalGen R (π ^ n) 0
  set y := nodalGen R (π ^ n) 1
  set m := nodalCenter R π (π ^ n)
  have hm : m = Ideal.span {p, x, y} := rfl
  set J := Ideal.span {p, x + y}
  have hpm : p ∈ m := algebraMap_mem_nodalCenter π (π ^ n)
  have hxm : x ∈ m := nodalGen_mem_nodalCenter π (π ^ n) 0
  have hym : y ∈ m := nodalGen_mem_nodalCenter π (π ^ n) 1
  have hJm : J ≤ m := by
    rw [Ideal.span_le]
    rintro _ (rfl | rfl)
    · exact hpm
    · exact add_mem hxm hym
  refine le_antisymm ?_ (by rw [sq]; exact Ideal.mul_mono_left hJm)
  have hpJ : p ∈ J := Ideal.subset_span (by simp)
  have hsJ : x + y ∈ J := Ideal.subset_span (by simp)
  have hxy : x * y ∈ J * m := by
    have h := nodalGen_zero_mul_nodalGen_one (R := R) (π ^ n)
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    change x * y = _ at h
    have e : algebraMap R (nodalChartRing R (π ^ (k + 2))) (π ^ (k + 2)) = p * p ^ (k + 1) := by
      simp only [p, map_pow]; ring
    rw [h, e]
    exact Ideal.mul_mem_mul hpJ (Ideal.pow_mem_of_mem _ hpm _ (by omega))
  have hxx : x * x ∈ J * m := by
    have : x * x = (x + y) * x - x * y := by ring
    rw [this]
    exact sub_mem (Ideal.mul_mem_mul hsJ hxm) hxy
  have hyy : y * y ∈ J * m := by
    have : y * y = (x + y) * y - x * y := by ring
    rw [this]
    exact sub_mem (Ideal.mul_mem_mul hsJ hym) hxy
  have hyx : y * x ∈ J * m := by rw [show y * x = x * y from mul_comm y x]; exact hxy
  have key : ∀ a ∈ ({p, x, y} : Set _), ∀ b ∈ ({p, x, y} : Set _), a * b ∈ J * m := by
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;> rw [ha, hb]
    · exact Ideal.mul_mem_mul hpJ hpm
    · exact Ideal.mul_mem_mul hpJ hxm
    · exact Ideal.mul_mem_mul hpJ hym
    · rw [show x * p = p * x from mul_comm x p]; exact Ideal.mul_mem_mul hpJ hxm
    · exact hxx
    · exact hxy
    · rw [show y * p = p * y from mul_comm y p]; exact Ideal.mul_mem_mul hpJ hym
    · exact hyx
    · exact hyy
  rw [sq, hm, Ideal.span_mul_span, Ideal.span_le]
  rintro _ ⟨a, ha, b, hb, rfl⟩
  rw [← hm]
  exact key a ha b hb

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- **`H^q` of the blowup of the standard nodal model at its origin vanishes for `q > 0`**, when
the exponent is at least two. -/
theorem isZero_Hgroup_blowUp_nodalModelOriginPoint {R' : Type u} [CommRing R'] {π : R'}
    (hπ : (Ideal.span {π}).IsMaximal) {n : ℕ} (h1 : 1 ≤ n) (hn : 2 ≤ n) (q : ℕ) (hq : 0 < q) :
    IsZero (Hgroup (blowUp (vanishingIdeal (⟨{nodalModelOriginPoint hπ h1},
        isClosed_singleton_nodalModelOriginPoint hπ h1⟩ :
          Closeds (nodalModel R' π n)))).ringCatSheaf ⊤ q
      (SheafOfModules.unit (blowUp (vanishingIdeal
        (⟨{nodalModelOriginPoint hπ h1}, isClosed_singleton_nodalModelOriginPoint hπ h1⟩ :
            Closeds (nodalModel R' π n)))).ringCatSheaf)) := by
  set I0 := (nodalModelOriginPoint hπ h1).asIdeal with hI0
  obtain ⟨κ⟩ := nonempty_over_iso_blowUpToBase_vanishingIdeal (nodalChartRing R' (π ^ n))
    (nodalModelOriginPoint hπ h1) (isClosed_singleton_nodalModelOriginPoint hπ h1)
  have hei : IsIso κ.hom.left := inferInstanceAs (IsIso ((Over.forget _).map κ.hom))
  let e' : AlgebraicGeometry.Proj (Stacks.Blowup.reesGrading I0) ≅
      blowUp (vanishingIdeal (⟨{nodalModelOriginPoint hπ h1},
        isClosed_singleton_nodalModelOriginPoint hπ h1⟩ : Closeds (nodalModel R' π n))) :=
    @asIso _ _ _ _ κ.hom.left hei
  have hI : I0 ^ 2 = Ideal.span {algebraMap R' (nodalChartRing R' (π ^ n)) π,
      nodalGen R' (π ^ n) 0 + nodalGen R' (π ^ n) 1} * I0 :=
    nodalCenter_sq_eq π hn
  have ha : algebraMap R' (nodalChartRing R' (π ^ n)) π ∈ I0 :=
    algebraMap_mem_nodalCenter π (π ^ n)
  have hb : nodalGen R' (π ^ n) 0 + nodalGen R' (π ^ n) 1 ∈ I0 :=
    add_mem (nodalGen_mem_nodalCenter π (π ^ n) 0) (nodalGen_mem_nodalCenter π (π ^ n) 1)
  have h : IsZero (Hgroup (AlgebraicGeometry.Proj (Stacks.Blowup.reesGrading I0)).ringCatSheaf ⊤ q
      (SheafOfModules.unit
        (AlgebraicGeometry.Proj (Stacks.Blowup.reesGrading I0)).ringCatSheaf)) := by
    rcases Nat.lt_or_ge q 2 with h | h
    · obtain rfl : q = 1 := by omega
      exact Stacks.Blowup.isZero_Hgroup_one_proj_reesGrading_of_sq_eq I0 ha hb hI
    · have : (SheafOfModules.unit
          (AlgebraicGeometry.Proj (Stacks.Blowup.reesGrading I0)).ringCatSheaf).IsQuasicoherent :=
        Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit _
      exact Stacks.Blowup.isZero_Hgroup_proj_reesGrading_of_sq_eq_of_two_le I0 ha hb hI _ q h
  refine (Stacks.Cohomology.SchemeIso.isZero_Hgroup_pullback_iff e' _ q).mp (h.of_iso ?_)
  exact (Hfunctor (AlgebraicGeometry.Proj (Stacks.Blowup.reesGrading I0)).ringCatSheaf ⊤ q).mapIso
    (Scheme.Modules.pullbackUnitIso e'.hom)

/-- Flat base change for the structure sheaf: `g^* R^q f_* 𝒪 ≅ R^q f'_* 𝒪` in a pullback square. -/
private theorem nonempty_iso_pullback_rightDerivedPlus_pushforward_unit {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (H : IsPullback g' f' f g) [Flat g]
    [QuasiCompact f] [QuasiSeparated f] [(SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent]
    (q : ℕ) :
    Nonempty ((Scheme.Modules.pullback g).obj
        (((Scheme.Modules.pushforward f).rightDerivedPlus q).obj
          (SheafOfModules.unit X.ringCatSheaf))
      ≅ ((Scheme.Modules.pushforward f').rightDerivedPlus q).obj
        (SheafOfModules.unit X'.ringCatSheaf)) :=
  ⟨(Stacks.AlgebraicGeometry.FlatBaseChangeDerived.higherBaseChangeIso H _ q) ≪≫
    ((Scheme.Modules.pushforward f').rightDerivedPlus q).mapIso
      (Scheme.Modules.pullbackUnitIso g')⟩

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- **`R^q b_*𝒪_{X'} = 0` for `q > 0` along the blowup `b : X' ⟶ X` of a nodal family at a closed
point with an étale nodal chart of exponent `n ≥ 2`.** -/
theorem isZero_rightDerivedPlus_pushforward_blowUp_of_nodalChartAt {X : Scheme.{u}}
    {f : X ⟶ Spec (.of R)} {x : X} (hx : IsClosed ({x} : Set X)) {n : ℕ}
    (c : NodalChartAt f x n) (hn : 2 ≤ n) [IsLocallyNoetherian X] (q : ℕ) (hq : 0 < q) :
    IsZero (((Scheme.Modules.pushforward
        (blowUpToBase (vanishingIdeal (⟨{x}, hx⟩ : Closeds X)))).rightDerivedPlus q).obj
      (SheafOfModules.unit (blowUp (vanishingIdeal (⟨{x}, hx⟩ : Closeds X))).ringCatSheaf)) := by
  set M := vanishingIdeal (⟨{x}, hx⟩ : Closeds X) with hM
  set b := blowUpToBase M with hb
  have hqc : (SheafOfModules.unit (blowUp M).ringCatSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit _
  refine AlgebraicGeometry.isZero_of_forall_isZero_stalk _ (fun y => ?_)
  by_cases hy : y = x
  · subst hy
    obtain ⟨c, hcX, hcM⟩ := c.exists_preimage_eq_singleton
    have := c.etale_toX
    have := c.etale_toModel
    have hmax : (Ideal.span {c.π}).IsMaximal :=
      isMaximal_span_singleton_of_irreducible c.irreducible
    have h1 : 1 ≤ n := by omega
    have hoC := isClosed_singleton_nodalModelOriginPoint hmax h1
    have hwo : c.toModel.base c.pt = nodalModelOriginPoint hmax h1 := PrimeSpectrum.ext c.pt_origin
    set Mo := vanishingIdeal (⟨{nodalModelOriginPoint hmax h1}, hoC⟩ :
      Closeds (nodalModel c.R' c.π n)) with hMo
    have hcomap : M.comap c.toX = Mo.comap c.toModel := by
      rw [comap_vanishingIdeal_of_smooth c.toX _
          ⟨c.toX.base ⁻¹' {y}, hx.preimage c.toX.continuous⟩ rfl,
        comap_vanishingIdeal_of_smooth c.toModel _
          ⟨c.toModel.base ⁻¹' {nodalModelOriginPoint hmax h1}, hoC.preimage c.toModel.continuous⟩
          rfl]
      congr 1
      ext1
      change c.toX.base ⁻¹' {y} = c.toModel.base ⁻¹' {nodalModelOriginPoint hmax h1}
      rw [hcX, ← hwo, hcM]
    set I := M.comap c.toX with hI
    obtain ⟨h₁, sq₁⟩ := exists_isPullback_blowUpToBase_comap c.toX M
    obtain ⟨h₂, sq₂⟩ : ∃ h₂ : blowUp I ⟶ blowUp Mo,
        IsPullback (blowUpToBase I) h₂ c.toModel (blowUpToBase Mo) := by
      rw [hcomap]
      exact exists_isPullback_blowUpToBase_comap c.toModel Mo
    have : IsAffine (nodalModel c.R' c.π n) := by
      unfold nodalModel; infer_instance
    have : IsLocallyNoetherian (nodalModel c.R' c.π n) := by
      unfold nodalModel; infer_instance
    have : IsProper (blowUpToBase Mo) :=
      AlgebraicGeometry.isProper_blowUpToBase_of_fg _ fun U =>
        have := IsLocallyNoetherian.component_noetherian U
        Ideal.fg_of_isNoetherianRing _
    have hloc := isZero_Hgroup_blowUp_nodalModelOriginPoint hmax h1 hn q hq
    have hqcMo : (SheafOfModules.unit (blowUp Mo).ringCatSheaf).IsQuasicoherent :=
      Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit _
    have hMo0 : IsZero (((Scheme.Modules.pushforward (blowUpToBase Mo)).rightDerivedPlus q).obj
        (SheafOfModules.unit (blowUp Mo).ringCatSheaf)) :=
      AlgebraicGeometry.TopDegreeBaseChange.isZero_rightDerivedPlus_pushforward_of_isZero_cohomology
        (blowUpToBase Mo) q _
        ((Cohomology.AffineBase.isZero_rightDerivedPlus_moduleGlobalSections_iff_isZero_Hgroup
          _ _ q).2 hloc)
    have hI0 : IsZero (((Scheme.Modules.pushforward (blowUpToBase I)).rightDerivedPlus q).obj
        (SheafOfModules.unit (blowUp I).ringCatSheaf)) := by
      obtain ⟨e₂⟩ := nonempty_iso_pullback_rightDerivedPlus_pushforward_unit sq₂.flip q
      exact (Functor.map_isZero _ hMo0).of_iso e₂.symm
    have hpull : IsZero ((Scheme.Modules.pullback c.toX).obj
        (((Scheme.Modules.pushforward b).rightDerivedPlus q).obj
          (SheafOfModules.unit (blowUp M).ringCatSheaf))) := by
      obtain ⟨e₁⟩ := nonempty_iso_pullback_rightDerivedPlus_pushforward_unit sq₁.flip q
      exact hI0.of_iso e₁
    have := Stacks.AlgebraicGeometry.FlatPullbackStalk.isZero_stalk_of_isZero_pullback c.toX _ c.pt
      hpull
    rw [c.pt_mem] at this
    exact this
  · let V : X.Opens := ⟨M.supportᶜ, M.support.isClosed.isOpen_compl⟩
    have hyV : y ∈ V := by
      change y ∉ (M.support : Set X)
      rw [hM, Stacks.GenericFlatness.support_vanishingIdeal]
      exact hy
    have hiso : IsIso (b ∣_ V) := isIso_blowUp_restrict_compl_support M
    have : IsAffineHom (b ∣_ V) := inferInstance
    have : ((Scheme.Modules.restrictFunctor (b ⁻¹ᵁ V).ι).obj
        (SheafOfModules.unit (blowUp M).ringCatSheaf)).IsQuasicoherent :=
      Scheme.Modules.isQuasicoherent_restrictFunctor _ _
    exact AlgebraicGeometry.SchemeHigherDirectImage.isZero_stalk_of_isZero_rightDerivedPlus_restrict
      b V y hyV _ (by positivity)
      (Stacks.Cohomology.Affine.isZero_rightDerived_pushforward_of_isAffineHom (b ∣_ V) _ q
        (by exact_mod_cast hq))

end Stacks.SemistableReduction

end
