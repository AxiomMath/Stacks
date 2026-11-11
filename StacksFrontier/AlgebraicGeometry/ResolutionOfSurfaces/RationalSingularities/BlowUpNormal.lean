module

public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalCartier
public import StacksFrontier.AlgebraicGeometry.Divisors.IntegralLocallyPrincipal
public import StacksFrontier.AlgebraicGeometry.LocallyPrincipalPullback.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalIdealPowersExtra
public import StacksFrontier.AlgebraicGeometry.Surfaces.BlowUpNormalityExtra
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalIdealPowers
import StacksCore.Tactic.StacksAttribute

/-!
# The blowup of a rational surface singularity in its maximal ideal is normal

In Situation [Stacks, Tag 0B4W] — a two-dimensional local normal Nagata domain `A` defining a
rational singularity — the blowup of `Spec(A)` in the maximal ideal `𝔪` is a normal scheme.

## Main results

* `AlgebraicGeometry.mem_idealSheafGlobalSections_of_forall_restrict_mem_ideal` and
  `AlgebraicGeometry.restrict_mem_ideal_of_mem_idealSheafGlobalSections`: a global function is a
  global section of a sheaf of ideals exactly when its restriction to each member of one affine
  open covering lies in the ideal there.
* `RationalSingularitySituation.mem_idealSheafGlobalSections_exceptionalIdealPow_of_isIntegralOver`
  (in `AlgebraicGeometry`): an element of `A` integral over `𝔪ⁿ` is a global section of `𝓘ⁿ`, as
  soon as the ideal sheaf `𝓘 = 𝔪𝒪_X` of the special fibre is locally principal.
* `AlgebraicGeometry.RationalSingularitySituation.isIntegrallyClosed_maximalIdeal_pow`: under the
  same hypothesis every power of `𝔪` is an integrally closed ideal.
* `AlgebraicGeometry.isIntegrallyClosed_maximalIdeal_pow_of_definesRationalSingularity`: every
  power of the maximal ideal of a two-dimensional local normal Nagata domain defining a rational
  singularity is an integrally closed ideal.
* `AlgebraicGeometry.isNormal_blowUp_maximalIdeal_rationalSingularitySituation`: in Situation
  [Stacks, Tag 0B4W] the blowup of `Spec(A)` in `𝔪` is normal.

## References

* [Stacks Project, Tag 0B4Z](https://stacks.math.columbia.edu/tag/0B4Z)
* [Stacks Project, Tag 0B4W](https://stacks.math.columbia.edu/tag/0B4W)
* [Stacks Project, Tag 0B4Y](https://stacks.math.columbia.edu/tag/0B4Y)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 053P](https://stacks.math.columbia.edu/tag/053P)
* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR)
* [Stacks Project, Tag 033L](https://stacks.math.columbia.edu/tag/033L)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### Membership in the global sections of a sheaf of ideals is local -/

/-- Restricting a global function to an affine open and then cutting it down to the closed
subscheme is the same as cutting it down to the closed subscheme and then restricting. -/
private theorem subschemeι_app_restrict (I : X.IdealSheafData) (U : X.affineOpens)
    (a : Γ(X, ⊤)) :
    (I.subschemeι.app (U : X.Opens)).hom
        ((X.presheaf.map (homOfLE (le_top : (U : X.Opens) ≤ ⊤)).op).hom a) =
      (I.subscheme.presheaf.map
          (homOfLE (le_top : I.subschemeι ⁻¹ᵁ (U : X.Opens) ≤ ⊤)).op).hom
        (I.subschemeι.appTop.hom a) := by
  have h : X.presheaf.map (homOfLE (le_top : (U : X.Opens) ≤ ⊤)).op ≫
        I.subschemeι.app (U : X.Opens) =
      I.subschemeι.appTop ≫ I.subscheme.presheaf.map
        (homOfLE (le_top : I.subschemeι ⁻¹ᵁ (U : X.Opens) ≤ ⊤)).op := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE]
    rfl
  exact congrArg (fun q : Γ(X, ⊤) ⟶ Γ(I.subscheme, I.subschemeι ⁻¹ᵁ (U : X.Opens)) ↦ q.hom a) h

/-- **A global section of a sheaf of ideals restricts into the ideal on every affine open.** -/
theorem restrict_mem_ideal_of_mem_idealSheafGlobalSections (I : X.IdealSheafData)
    (U : X.affineOpens) {a : Γ(X, ⊤)} (ha : a ∈ idealSheafGlobalSections I) :
    (X.presheaf.map (homOfLE (le_top : (U : X.Opens) ≤ ⊤)).op).hom a ∈ I.ideal U := by
  rw [← Scheme.IdealSheafData.ker_subschemeι_app, RingHom.mem_ker,
    subschemeι_app_restrict I U a, RingHom.mem_ker.1 ha, map_zero]

/-- **Conversely, a global function restricting into the ideal on every member of one affine open
covering is a global section of the sheaf of ideals.** -/
theorem mem_idealSheafGlobalSections_of_forall_restrict_mem_ideal (I : X.IdealSheafData)
    {ι : Type*} (U : ι → X.affineOpens) (hU : ⨆ i, (U i : X.Opens) = ⊤) {a : Γ(X, ⊤)}
    (h : ∀ i, (X.presheaf.map (homOfLE (le_top : (U i : X.Opens) ≤ ⊤)).op).hom a ∈
      I.ideal (U i)) :
    a ∈ idealSheafGlobalSections I := by
  rw [RingHom.mem_ker]
  refine I.subscheme.sheaf.eq_of_locally_eq'
    (fun i ↦ I.subschemeι ⁻¹ᵁ (U i : X.Opens)) ⊤ (fun _ ↦ homOfLE le_top)
    (le_of_eq (Scheme.Hom.iSup_preimage_eq_top I.subschemeι hU).symm) _ 0 fun i ↦ ?_
  have hzero : (I.subschemeι.app (U i : X.Opens)).hom
      ((X.presheaf.map (homOfLE (le_top : (U i : X.Opens) ≤ ⊤)).op).hom a) = 0 :=
    RingHom.mem_ker.1 ((Scheme.IdealSheafData.ker_subschemeι_app I (U i)) ▸ h i)
  rw [subschemeι_app_restrict I (U i) a] at hzero
  exact hzero.trans (map_zero _).symm

namespace RationalSingularitySituation

variable (S : RationalSingularitySituation.{u})

/-! ### The powers of `𝔪` are integrally closed ideals -/

/-- The restriction to an affine open of the image of an element of `𝔪` lies in the ideal of the
special fibre there. -/
theorem restrict_mem_ideal_exceptionalIdeal (U : S.X.affineOpens) {a : S.A}
    (ha : a ∈ S.maximalIdeal) :
    (S.X.presheaf.map (homOfLE (le_top : (U : S.X.Opens) ≤ ⊤)).op).hom
        (((Scheme.ΓSpecIso (.of S.A)).inv ≫ S.f.appTop).hom a) ∈
      S.exceptionalIdeal.ideal U :=
  restrict_mem_ideal_of_mem_idealSheafGlobalSections _ U
    ((S.mem_idealSheafGlobalSections_exceptionalIdeal_iff a).2 ha)

/-- **An element of `A` integral over `𝔪ⁿ` is a global section of `𝓘ⁿ`**, as soon as the ideal
sheaf `𝓘 = 𝔪𝒪_X` of the special fibre is locally principal. -/
theorem mem_idealSheafGlobalSections_exceptionalIdealPow_of_isIntegralOver
    (hprin : Stacks.Divisors.IsLocallyPrincipal S.exceptionalIdeal) (n : ℕ) {x : S.A}
    (hx : (RingHom.id S.A).IsIntegralElemOverIdeal (S.maximalIdeal ^ n) x) :
    ((Scheme.ΓSpecIso (.of S.A)).inv ≫ S.f.appTop).hom x ∈
      idealSheafGlobalSections (S.exceptionalIdeal ^ n) := by
  classical
  choose U hmemU hprinU using hprin
  refine mem_idealSheafGlobalSections_of_forall_restrict_mem_ideal _ U
    (top_le_iff.1 fun y _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨y, hmemU y⟩) fun y ↦ ?_
  obtain ⟨t, ht'⟩ := hprinU y
  have ht : S.exceptionalIdeal.ideal (U y) = Ideal.span {t} := ht'
  have : Nonempty ((U y : S.X.Opens) : Type u) := ⟨⟨y, hmemU y⟩⟩
  have : IsDomain Γ(S.X, (U y : S.X.Opens)) :=
    IsIntegral.component_integral (U y : S.X.Opens)
  have : IsIntegrallyClosed Γ(S.X, (U y : S.X.Opens)) :=
    (isNormal_iff_forall_affineOpen_normal S.X).1 inferInstance (U y) inferInstance
  set ψ : S.A →+* Γ(S.X, (U y : S.X.Opens)) :=
    (S.X.presheaf.map (homOfLE (le_top : (U y : S.X.Opens) ≤ ⊤)).op).hom.comp
      ((Scheme.ΓSpecIso (.of S.A)).inv ≫ S.f.appTop).hom
  have hmap : ∀ m ∈ S.maximalIdeal,
      ψ m ∈ (Ideal.span {t} : Ideal Γ(S.X, (U y : S.X.Opens))) := fun m hm ↦ by
    rw [← ht]
    exact S.restrict_mem_ideal_exceptionalIdeal (U y) hm
  have hpow : ∀ (N : ℕ) (z : S.A), z ∈ S.maximalIdeal ^ N →
      ψ z ∈ (Ideal.span {t} : Ideal Γ(S.X, (U y : S.X.Opens))) ^ N := by
    intro N z hz
    have hle : (S.maximalIdeal ^ N).map ψ ≤
        (Ideal.span {t} : Ideal Γ(S.X, (U y : S.X.Opens))) ^ N := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono
        (Ideal.map_le_iff_le_comap.2 fun m hm ↦ Ideal.mem_comap.2 (hmap m hm)) N
    exact hle (Ideal.mem_map_of_mem ψ hz)
  obtain ⟨k, c, hk, hc, hrel⟩ := hx.exists_sum_eq_zero
  have hint : (RingHom.id Γ(S.X, (U y : S.X.Opens))).IsIntegralElemOverIdeal
      ((Ideal.span {t} : Ideal Γ(S.X, (U y : S.X.Opens))) ^ n) (ψ x) := by
    refine Ideal.isIntegralElemOverIdeal_id_iff.2 ⟨k, fun j ↦ ψ (c j), hk, fun j hj ↦ ?_, ?_⟩
    · rw [← pow_mul]
      exact hpow (n * (k - j)) (c j) (by rw [pow_mul]; exact hc j hj)
    · have hz : ψ (x ^ k + ∑ j ∈ Finset.range k, c j * x ^ j) = ψ 0 := by rw [hrel]
      simpa only [map_add, map_pow, map_sum, map_mul, map_zero] using hz
  have hmem := Ideal.isIntegrallyClosed_pow_span_singleton t n (ψ x) hint
  rwa [show (S.exceptionalIdeal ^ n).ideal (U y) = S.exceptionalIdeal.ideal (U y) ^ n from rfl,
    ht]

/-! ### The situation at the normalized blowup -/

/-- The sheaf of ideals of the closed point of `Spec(A)` is the one generated over the whole space
by the image of the maximal ideal. -/
theorem ker_fromSpecResidueField_closedPoint_eq_ofIdealTop_map :
    (S.base.fromSpecResidueField S.closedPoint).ker =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (.of S.A)).inv.hom S.maximalIdeal) := by
  rw [Scheme.ker_of_isAffine]
  congr 1
  refine le_antisymm (fun y hy ↦ ?_) (Ideal.map_le_iff_le_comap.2 fun a ha ↦ ?_)
  · have hre : (Scheme.ΓSpecIso (.of S.A)).inv.hom
        ((Scheme.ΓSpecIso (.of S.A)).hom.hom y) = y := by simp
    have hy' : (Scheme.ΓSpecIso (.of S.A)).hom.hom y ∈ S.maximalIdeal :=
      (S.fromSpecResidueField_appTop_eq_zero_iff _).1 (by rw [hre]; exact RingHom.mem_ker.1 hy)
    exact hre ▸ Ideal.mem_map_of_mem _ hy'
  · exact RingHom.mem_ker.2 ((S.fromSpecResidueField_appTop_eq_zero_iff a).2 ha)

/-- **The ideal sheaf of the special fibre is locally principal whenever the modification factors
through the blowup of the closed point.** -/
theorem isLocallyPrincipal_exceptionalIdeal_of_factorsThroughBlowUp
    {I : S.base.IdealSheafData} {ν : S.X ⟶ blowUp I} (hf : S.f = ν ≫ blowUpToBase I)
    (hI : (S.base.fromSpecResidueField S.closedPoint).ker = I) :
    Stacks.Divisors.IsLocallyPrincipal S.exceptionalIdeal := by
  rw [S.exceptionalIdeal_eq_comap, hI, hf, Scheme.IdealSheafData.comap_comp]
  exact Stacks.Divisors.isLocallyPrincipal_comap ν _
    (Stacks.Divisors.isLocallyPrincipal_of_isEffectiveCartierDivisor
      (_root_.AlgebraicGeometry.exceptionalIdeal I)
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I))

/-- The map from `A` to the global functions of `X` is bijective. -/
private theorem bijective_globalFunctions :
    Function.Bijective ((Scheme.ΓSpecIso (.of S.A)).inv ≫ S.f.appTop).hom := by
  have := S.isIso_globalFunctions
  exact ConcreteCategory.bijective_of_isIso _

/-- **The ideal sheaf of the special fibre is nonzero.** -/
theorem exceptionalIdeal_ne_bot : S.exceptionalIdeal ≠ ⊥ := by
  have hmax : S.maximalIdeal ≠ ⊥ := by
    intro hm
    have hfield : IsField S.A := IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm
    exact (by norm_num : (2 : WithBot ℕ∞) ≠ 0)
      (S.dimension_two.symm.trans (ringKrullDim_eq_zero_of_isField hfield))
  obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmax
  obtain ⟨y⟩ := (inferInstance : Nonempty S.X)
  obtain ⟨U, hU⟩ := Stacks.Divisors.exists_affineOpens_mem y
  have : Nonempty ((U : S.X.Opens) : Type u) := ⟨⟨y, hU⟩⟩
  have : Nonempty ((⊤ : S.X.Opens) : Type u) := ⟨⟨y, trivial⟩⟩
  have hinjρ : Function.Injective
      ((S.X.presheaf.map (homOfLE (le_top : (U : S.X.Opens) ≤ ⊤)).op).hom) := by
    have key : ∀ b : Γ(S.X, ⊤), S.X.germToFunctionField (U : S.X.Opens)
        ((S.X.presheaf.map (homOfLE (le_top : (U : S.X.Opens) ≤ ⊤)).op).hom b) =
        S.X.germToFunctionField (⊤ : S.X.Opens) b := fun b ↦
      S.X.presheaf.germ_res_apply (homOfLE (le_top : (U : S.X.Opens) ≤ ⊤)) (genericPoint S.X) _ b
    intro b₁ b₂ hb
    exact S.X.germToFunctionField_injective (⊤ : S.X.Opens)
      (by rw [← key b₁, ← key b₂, hb])
  intro hbot
  have hmemU := S.restrict_mem_ideal_exceptionalIdeal U hm
  rw [hbot] at hmemU
  exact hm0 (S.bijective_globalFunctions.1 (hinjρ (by simpa using hmemU)))

/-- **Every power of `𝔪` is an integrally closed ideal**, as soon as the ideal sheaf of the
special fibre is locally principal. -/
theorem isIntegrallyClosed_maximalIdeal_pow
    (hprin : Stacks.Divisors.IsLocallyPrincipal S.exceptionalIdeal) (n : ℕ) :
    (S.maximalIdeal ^ n).IsIntegrallyClosed := by
  have hE : Stacks.Divisors.IsEffectiveCartierDivisor S.exceptionalIdeal :=
    Stacks.Divisors.isEffectiveCartierDivisor_of_isLocallyPrincipal _ S.exceptionalIdeal_ne_bot
      hprin
  intro x hx
  have hmem := S.mem_idealSheafGlobalSections_exceptionalIdealPow_of_isIntegralOver hprin n hx
  rw [S.idealSheafGlobalSections_exceptionalIdealPow_unconditional hE n] at hmem
  exact (Ideal.comap_map_of_bijective _ S.bijective_globalFunctions).le hmem

end RationalSingularitySituation

/-! ### Tag 0B4Z -/

/-- **Every power of the maximal ideal of a two-dimensional local normal Nagata domain defining a
rational singularity is an integrally closed ideal.** -/
theorem isIntegrallyClosed_maximalIdeal_pow_of_definesRationalSingularity (A : Type u)
    [CommRing A] [IsLocalRing A] [IsNormalDomain A] (hnag : IsNagataRing A)
    (hdim : ringKrullDim A = 2) (hrat : DefinesRationalSingularity A) (n : ℕ) :
    ((IsLocalRing.maximalIdeal A) ^ n).IsIntegrallyClosed := by
  have _ : IsNoetherianRing A := hnag.1
  exact (rationalSingularitySituationNormalizedBlowUp A hnag hdim
      hrat).isIntegrallyClosed_maximalIdeal_pow
    (RationalSingularitySituation.isLocallyPrincipal_exceptionalIdeal_of_factorsThroughBlowUp _
      (rationalSingularitySituationNormalizedBlowUp_f A hnag hdim hrat)
      (RationalSingularitySituation.ker_fromSpecResidueField_closedPoint_eq_ofIdealTop_map _)) n

/-- In Situation [Stacks, Tag 0B4W] the blowup of `Spec(A)` in the maximal ideal is a normal
scheme. -/
@[stacks 0B4Z "In Situation 0B4W the blowup of Spec(A) in the maximal ideal is normal"]
theorem isNormal_blowUp_maximalIdeal_rationalSingularitySituation
    (S : RationalSingularitySituation.{u}) :
    IsNormal (blowUp (Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (.of S.A)).inv.hom S.maximalIdeal))) :=
  isNormal_blowUp_maximalIdeal_of_forall_isIntegrallyClosed_pow S.A fun n ↦
    isIntegrallyClosed_maximalIdeal_pow_of_definesRationalSingularity S.A S.nagata
      S.dimension_two S.definesRationalSingularity n

end AlgebraicGeometry

end
