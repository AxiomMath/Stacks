module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.EssentialFiniteness.ArtinianTarget
public import StacksFrontier.RingTheory.LocalRing.ResidueSection
public import StacksFrontier.RingTheory.Smoothing.EssentiallySmooth
public import StacksFrontier.RingTheory.GeometricallyRegular.PurelyInseparableCriterion
public import StacksFrontier.RingTheory.Regular.RegularRingHom
public import StacksFrontier.RingTheory.Etale.Basic
public import StacksFrontier.RingTheory.Flat.MiracleFlatness
public import StacksFrontier.RingTheory.CohenMacaulay.Witnesses

/-!
# Inseparable residue fields: the stages `Ψ_σ(F[x₁, …, x_d])`

For a ring-theoretic section `σ : K → Λ` of the residue map of a local ring `Λ`, a subfield
`k ⊆ F ⊆ K` and elements `x₁, …, x_d` of `Λ`, the stage `Ψ_σ(F[x₁, …, x_d])` is the image of
`F[X₁, …, X_d]` under the evaluation that uses `σ` on coefficients. This file proves that `Ψ_σ`
is surjective when the `xᵢ` generate a nilpotent maximal ideal, that the coefficient field can be
enlarged to put finitely many elements into a stage, that the stages are local, and that `Λ` is
free over a suitable stage.

This is the first part of `StacksFrontier.RingTheory.Smoothing.InseparableResidueField`; the
module docstring there describes the whole development.

## Main definitions

* `Stacks.Smoothing.coefficientStage`: the stage `Ψ_σ(F[x₁, …, x_d])`.

## Main results

* `Stacks.Smoothing.eval₂Hom_surjective_of_isSection`: `Ψ_σ : K[X₁, …, X_d] → Λ` is surjective.
* `Stacks.Smoothing.exists_stage`: a stage over which `Λ` is free, Artinian local and
  essentially of finite type over `k`.
-/

@[expose] public section

namespace Stacks.Smoothing

open IsLocalRing MvPolynomial

/-! ### Freeness from a basis which works over two base fields -/

/-- Let `F ⊆ K` be fields, let `L` be a commutative `K`-algebra and let `A` be a commutative
`F`-algebra mapping to `L` over `F`. If `A` has a finite `F`-basis whose image in `L` is a
`K`-basis of `L`, then `L` is a free `A`-module: a basis is given by the image of any `F`-basis
of `K`. -/
private theorem free_of_basis_of_linearIndependent
    {F K L A ι : Type*} [Field F] [Field K] [CommRing L] [CommRing A]
    [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
    [Algebra F A] [Algebra A L] [IsScalarTower F A L]
    [Finite ι] (bA : Module.Basis ι F A)
    (hindep : LinearIndependent K fun i ↦ algebraMap A L (bA i))
    (hspan : Submodule.span K (Set.range fun i ↦ algebraMap A L (bA i)) = ⊤) :
    Module.Free A L := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨J, bK⟩ := Module.Free.exists_basis F K
  -- The two scalar towers let us move an `F`-scalar from the `K`-side to the `A`-side.
  have key : ∀ (f : F) (y : K),
      algebraMap A L (algebraMap F A f) * algebraMap K L y = algebraMap K L (f • y) := by
    intro f y
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply F K L,
      IsScalarTower.algebraMap_apply F A L]
  have hrepr : ∀ z : A, ∑ i, algebraMap F A (bA.repr z i) * bA i = z := fun z => by
    simpa [Algebra.smul_def] using bA.sum_repr z
  -- Expand an element of `K` over `bK` along any finite set containing its support.
  have hexp : ∀ (y : K) (s : Finset J), (bK.repr y).support ⊆ s →
      ∑ j ∈ s, bK.repr y j • bK j = y := by
    intro y s hs
    rw [← Finsupp.sum_of_support_subset (bK.repr y) hs (fun j (t : F) => t • bK j)
        fun _ _ => zero_smul _ _, ← Finsupp.linearCombination_apply]
    exact bK.linearCombination_repr y
  -- Regroup a sum over a `K`-combination of the `bA i` into an `A`-combination of the `bK j`.
  have hswap : ∀ (s : Finset J) (a : ι → J → F),
      ∑ i, (∑ j ∈ s, a i j • bK j : K) • algebraMap A L (bA i) =
        ∑ j ∈ s, (∑ i, algebraMap F A (a i j) * bA i) • algebraMap K L (bK j) := by
    intro s a
    calc ∑ i, (∑ j ∈ s, a i j • bK j : K) • algebraMap A L (bA i)
        = ∑ i, ∑ j ∈ s, algebraMap K L (a i j • bK j) * algebraMap A L (bA i) := by
          simp [Algebra.smul_def, map_sum, Finset.sum_mul]
      _ = ∑ j ∈ s, ∑ i, algebraMap K L (a i j • bK j) * algebraMap A L (bA i) :=
          Finset.sum_comm
      _ = ∑ j ∈ s, (∑ i, algebraMap A L (algebraMap F A (a i j) * bA i)) *
            algebraMap K L (bK j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by rw [← key, map_mul]; ring
      _ = _ := Finset.sum_congr rfl fun j _ => by rw [← map_sum, Algebra.smul_def]
  refine Module.Free.of_basis
    (Module.Basis.mk (v := fun j : J => algebraMap K L (bK j)) ?_ ?_)
  · rw [linearIndependent_iff']
    intro s g hg j hj
    have hzero : ∀ i, (∑ j ∈ s, bA.repr (g j) i • bK j : K) = 0 := by
      rw [Fintype.linearIndependent_iff] at hindep
      apply hindep
      rw [hswap s fun i j => bA.repr (g j) i]
      simp only [hrepr]
      exact hg
    have hcoef : ∀ i, bA.repr (g j) i = 0 := fun i =>
      linearIndependent_iff'.mp bK.linearIndependent s _ (hzero i) j hj
    rw [← bA.sum_repr (g j)]
    exact Finset.sum_eq_zero fun i _ => by rw [hcoef i, zero_smul]
  · intro y _
    have hy : y ∈ Submodule.span K (Set.range fun i => algebraMap A L (bA i)) := by
      rw [hspan]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hy
    obtain ⟨s, hsub⟩ : ∃ s : Finset J, ∀ i, (bK.repr (c i)).support ⊆ s :=
      ⟨Finset.univ.biUnion fun i => (bK.repr (c i)).support, fun i =>
        Finset.subset_biUnion_of_mem (fun i => (bK.repr (c i)).support) (Finset.mem_univ i)⟩
    have hy2 : y = ∑ j ∈ s,
        (∑ i, algebraMap F A (bK.repr (c i) j) * bA i) • algebraMap K L (bK j) := by
      calc y = ∑ i, c i • algebraMap A L (bA i) := hc.symm
        _ = ∑ i, (∑ j ∈ s, bK.repr (c i) j • bK j : K) • algebraMap A L (bA i) := by
            simp_rw [hexp _ s (hsub _)]
        _ = _ := hswap s fun i j => bK.repr (c i) j
    rw [hy2]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))

/-- If `v` spans an `F`-submodule of `Λ` containing `1` and closed under multiplication, if the
`xᵢ` lie in that submodule, and if every `v i` lies in the range of `MvPolynomial.aeval x`, then
that range is exactly the span of `v`. -/
private theorem aeval_range_eq_span {F Λ : Type*} [Field F] [CommRing Λ] [Algebra F Λ]
    {ι : Type*} (v : ι → Λ) {d : ℕ} (x : Fin d → Λ)
    (hone : (1 : Λ) ∈ Submodule.span F (Set.range v))
    (hx : ∀ i, x i ∈ Submodule.span F (Set.range v))
    (hmul : ∀ i j, v i * v j ∈ Submodule.span F (Set.range v))
    (hv : ∀ i, v i ∈ (MvPolynomial.aeval x : MvPolynomial (Fin d) F →ₐ[F] Λ).range) :
    ((MvPolynomial.aeval x : MvPolynomial (Fin d) F →ₐ[F] Λ).range : Set Λ)
      = (Submodule.span F (Set.range v) : Set Λ) := by
  set V : Submodule F Λ := Submodule.span F (Set.range v) with hV
  have hVV : ∀ y z : Λ, y ∈ V → z ∈ V → y * z ∈ V := by
    have h : V * V ≤ V := by
      rw [hV, Submodule.span_mul_span, Submodule.span_le]
      rintro w ⟨a, ⟨i, rfl⟩, b, ⟨j, rfl⟩, rfl⟩
      exact hmul i j
    exact fun y z hy hz => h (Submodule.mul_mem_mul hy hz)
  refine Set.Subset.antisymm ?_ ?_
  · have hle : (MvPolynomial.aeval x : MvPolynomial (Fin d) F →ₐ[F] Λ).range
        ≤ V.toSubalgebra hone hVV := by
      rw [← Algebra.adjoin_range_eq_range_aeval]
      exact Algebra.adjoin_le (Set.range_subset_iff.2 hx)
    exact hle
  · have hle : V ≤ Subalgebra.toSubmodule
        (MvPolynomial.aeval x : MvPolynomial (Fin d) F →ₐ[F] Λ).range :=
      Submodule.span_le.2 (Set.range_subset_iff.2 hv)
    exact hle

/-! ### The stages `Ψ_σ(F[x₁, …, x_d])` -/

/-- The subring `Ψ_σ(F[x₁, …, x_d])` of `Λ`: the image of the polynomial ring `F[X₁, …, X_d]`
under the evaluation which uses the ring map `σ` on coefficients and sends `Xᵢ` to `xᵢ`.

In the proof of Stacks 07FG, `σ` is a ring-theoretic section of the residue map of an Artinian
local ring `Λ` and the `xᵢ` generate its maximal ideal. The section is in general not a
`k`-algebra map, which is why this is only a subring of `Λ`; it is a `k`-subalgebra exactly when
it contains the image of `k`. -/
noncomputable def coefficientStage {k K Λ : Type*} [Field k] [Field K] [CommRing Λ]
    [Algebra k K] (σ : K →+* Λ) (F : IntermediateField k K) {d : ℕ} (x : Fin d → Λ) :
    Subring Λ :=
  (MvPolynomial.eval₂Hom (σ.comp F.val.toRingHom) x).range

section Stage

variable {k K Λ : Type*} [Field k] [Field K] [CommRing Λ] [Algebra k K] (σ : K →+* Λ)
  {d : ℕ} (x : Fin d → Λ)

/-- The image under `σ` of an element of `F` lies in the stage attached to `F`. -/
lemma mem_coefficientStage_of_mem (F : IntermediateField k K) (c : F) :
    σ (c : K) ∈ coefficientStage σ F x :=
  ⟨MvPolynomial.C c, by simp⟩

/-- The chosen elements lie in every stage. -/
lemma mem_coefficientStage_gen (F : IntermediateField k K) (i : Fin d) :
    x i ∈ coefficientStage σ F x :=
  ⟨MvPolynomial.X i, by simp⟩

/-- The stages increase with the coefficient field. -/
lemma coefficientStage_mono {F F' : IntermediateField k K} (h : F ≤ F') :
    coefficientStage σ F x ≤ coefficientStage σ F' x := by
  rintro y ⟨f, rfl⟩
  exact ⟨MvPolynomial.map (IntermediateField.inclusion h).toRingHom f, by
    simp [MvPolynomial.eval₂Hom, MvPolynomial.eval₂_map]; rfl⟩

/-- A polynomial all of whose coefficients lie in `F` evaluates into the stage of `F`. -/
lemma mem_coefficientStage_of_forall_coeff_mem (F : IntermediateField k K)
    (f : MvPolynomial (Fin d) K) (hf : ∀ e, f.coeff e ∈ F) :
    MvPolynomial.eval₂ σ x f ∈ coefficientStage σ F x := by
  classical
  refine ⟨∑ e ∈ f.support, MvPolynomial.monomial e (⟨f.coeff e, hf e⟩ : F), ?_⟩
  have h : MvPolynomial.map F.val.toRingHom
      (∑ e ∈ f.support, MvPolynomial.monomial e (⟨f.coeff e, hf e⟩ : F)) = f := by
    rw [map_sum]
    simp only [MvPolynomial.map_monomial]
    exact (MvPolynomial.as_sum f).symm
  rw [MvPolynomial.coe_eval₂Hom, ← MvPolynomial.eval₂_map, h]

end Stage

/-! ### Surjectivity of `Ψ_σ` -/

/-- Refinement step: if `𝔪` is generated by finitely many elements of a subring `R` of `Λ` and
every element of `Λ` is congruent to an element of `R` modulo `𝔪`, then an approximation modulo
`𝔪 ^ j` can be refined to one modulo `𝔪 ^ (j + 1)`. -/
private lemma exists_mem_subring_sub_mem_pow_succ {Λ : Type*} [CommRing Λ] (R : Subring Λ)
    (𝔪 : Ideal Λ) {d : ℕ} (x : Fin d → Λ) (hxR : ∀ i, x i ∈ R)
    (hx : Ideal.span (Set.range x) = 𝔪) (hA : ∀ y : Λ, ∃ r ∈ R, y - r ∈ 𝔪) :
    ∀ j : ℕ, ∀ y ∈ 𝔪 ^ j, ∃ r ∈ R, y - r ∈ 𝔪 ^ (j + 1) := by
  intro j
  induction j with
  | zero => intro y _; simpa using hA y
  | succ j ih =>
    intro y hy
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro u hu v hv
      rw [← hx, Submodule.mem_span_range_iff_exists_fun] at hv
      obtain ⟨c, hc⟩ := hv
      have key : ∀ i : Fin d, ∃ r ∈ R, u * c i - r ∈ 𝔪 ^ (j + 1) :=
        fun i => ih _ (Ideal.mul_mem_right _ _ hu)
      choose r hrR hrm using key
      refine ⟨∑ i, r i * x i, Subring.sum_mem _ fun i _ => R.mul_mem (hrR i) (hxR i), ?_⟩
      have hsum : ∑ i, (u * c i - r i) * x i = u * v - ∑ i, r i * x i := by
        rw [← hc]
        simp only [smul_eq_mul, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
      rw [← hsum, pow_succ]
      exact Ideal.sum_mem _ fun i _ =>
        Ideal.mul_mem_mul (hrm i) (hx ▸ Ideal.subset_span (Set.mem_range_self i))
    · intro a b ha hb
      obtain ⟨ra, hraR, hra⟩ := ha
      obtain ⟨rb, hrbR, hrb⟩ := hb
      refine ⟨ra + rb, R.add_mem hraR hrbR, ?_⟩
      rw [show a + b - (ra + rb) = a - ra + (b - rb) by ring]
      exact Ideal.add_mem _ hra hrb

/-- Iterating the refinement step: every element of `Λ` can be approximated by an element of the
subring `R` modulo an arbitrary power of `𝔪`. -/
private lemma exists_mem_subring_sub_mem_pow {Λ : Type*} [CommRing Λ] (R : Subring Λ)
    (𝔪 : Ideal Λ) (hB : ∀ j : ℕ, ∀ y ∈ 𝔪 ^ j, ∃ r ∈ R, y - r ∈ 𝔪 ^ (j + 1)) :
    ∀ j : ℕ, ∀ y : Λ, ∃ r ∈ R, y - r ∈ 𝔪 ^ j := by
  intro j
  induction j with
  | zero => exact fun y => ⟨0, R.zero_mem, by simp⟩
  | succ j ih =>
    intro y
    obtain ⟨r, hrR, hr⟩ := ih y
    obtain ⟨r', hr'R, hr'⟩ := hB j _ hr
    refine ⟨r + r', R.add_mem hrR hr'R, ?_⟩
    rw [show y - (r + r') = y - r - r' by ring]
    exact hr'

/-! ### Surjectivity for an arbitrary presentation of the residue field -/

/-- Let `π : Λ → K` be a surjection onto a field with nilpotent kernel, let `σ` be a
ring-theoretic section of `π` and let `x₁, …, x_d` generate `ker π`. Then
`Ψ_σ : K[X₁, …, X_d] → Λ` is surjective.

The surjection onto the residue field is a parameter rather than `IsLocalRing.residue`, because
the induction in the proof of Stacks 07FG replaces `Λ` by `Λ/𝔪^{n-1}` while keeping `K` fixed;
`eval₂Hom_surjective_of_isSection` is the special case `π = residue Λ`. -/
theorem eval₂Hom_surjective_of_section {K Λ : Type*} [Field K] [CommRing Λ] (π : Λ →+* K)
    (σ : K →+* Λ) (hσ : ∀ c, π (σ c) = c) {d : ℕ} (x : Fin d → Λ)
    (hx : Ideal.span (Set.range x) = RingHom.ker π)
    (hnil : IsNilpotent (RingHom.ker π)) :
    Function.Surjective (MvPolynomial.eval₂Hom σ x) := by
  set R := (MvPolynomial.eval₂Hom σ x).range with hR
  have hxR : ∀ i, x i ∈ R := fun i => ⟨MvPolynomial.X i, MvPolynomial.eval₂Hom_X' _ _ i⟩
  have hA : ∀ y : Λ, ∃ r ∈ R, y - r ∈ RingHom.ker π := by
    intro y
    refine ⟨σ (π y), ⟨MvPolynomial.C _, MvPolynomial.eval₂Hom_C _ _ _⟩, ?_⟩
    simp [RingHom.mem_ker, hσ]
  obtain ⟨n, hn⟩ := hnil
  intro y
  obtain ⟨r, hrR, hr⟩ := exists_mem_subring_sub_mem_pow R _
    (exists_mem_subring_sub_mem_pow_succ R _ x hxR hx hA) n y
  rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot, sub_eq_zero] at hr
  obtain ⟨q, hq⟩ := hrR
  exact ⟨q, hq.trans hr.symm⟩

/-- Let `Λ` be a local ring with nilpotent maximal ideal `𝔪`, let `σ` be a ring-theoretic section
of the residue map and let `x₁, …, x_d` generate `𝔪`. Then `Ψ_σ : K[X₁, …, X_d] → Λ` is
surjective: `Λ` is generated as a ring by the image of `σ` together with the `xᵢ`.

This is the step of the proof of Stacks 07FG at which `Ψ_σ` is introduced. -/
theorem eval₂Hom_surjective_of_isSection {Λ : Type*} [CommRing Λ] [IsLocalRing Λ]
    (σ : ResidueField Λ →+* Λ) (hσ : ∀ c, residue Λ (σ c) = c)
    {d : ℕ} (x : Fin d → Λ) (hx : Ideal.span (Set.range x) = maximalIdeal Λ)
    (hnil : IsNilpotent (maximalIdeal Λ)) :
    Function.Surjective (MvPolynomial.eval₂Hom σ x) :=
  eval₂Hom_surjective_of_section (residue Λ) σ hσ x
    (by rw [IsLocalRing.ker_residue]; exact hx) (by rw [IsLocalRing.ker_residue]; exact hnil)

/-! ### Enlarging the coefficient field -/

section EnlargeGeneral

variable {k K Λ : Type*} [Field k] [Field K] [CommRing Λ] [Algebra k K] (σ : K →+* Λ)
  {d : ℕ} (x : Fin d → Λ)

/-- Any single element of `Λ` lies in the stage of a finitely generated enlargement of a given
finitely generated coefficient field. -/
lemma exists_fg_mem_stage (hsurj : Function.Surjective (MvPolynomial.eval₂Hom σ x))
    (F₀ : IntermediateField k K) (hF₀ : F₀.FG) (y : Λ) :
    ∃ F : IntermediateField k K, F₀ ≤ F ∧ F.FG ∧ y ∈ coefficientStage σ F x := by
  classical
  obtain ⟨f, hfy⟩ := hsurj y
  refine ⟨F₀ ⊔ IntermediateField.adjoin k (f.support.image f.coeff : Finset _),
    le_sup_left, IntermediateField.fg_sup hF₀ (IntermediateField.fg_adjoin_finset _), ?_⟩
  rw [← hfy]
  refine mem_coefficientStage_of_forall_coeff_mem σ x _ f fun e => ?_
  by_cases he : e ∈ f.support
  · refine (le_sup_right : IntermediateField.adjoin k _ ≤ _)
      (IntermediateField.subset_adjoin k _ ?_)
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
    exact ⟨e, he, rfl⟩
  · simp [MvPolynomial.notMem_support_iff.mp he]

/-- Any finite set of elements of `Λ` lies in the stage of a finitely generated enlargement of a
given finitely generated coefficient field. -/
lemma exists_fg_subset_stage (hsurj : Function.Surjective (MvPolynomial.eval₂Hom σ x))
    (F₀ : IntermediateField k K) (hF₀ : F₀.FG) (s : Finset Λ) :
    ∃ F : IntermediateField k K, F₀ ≤ F ∧ F.FG ∧ ∀ y ∈ s, y ∈ coefficientStage σ F x := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨F₀, le_refl _, hF₀, by simp⟩
  | insert a s _ ih =>
    obtain ⟨F, hle, hfg, hmem⟩ := ih
    obtain ⟨F', hle', hfg', hmem'⟩ := exists_fg_mem_stage σ x hsurj F hfg a
    exact ⟨F', hle.trans hle', hfg', fun y hy => by
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hmem'
      · exact coefficientStage_mono σ x hle' (hmem y hy)⟩

end EnlargeGeneral

section Enlarge

variable {k Λ : Type*} [Field k] [CommRing Λ] [Algebra k Λ] [IsLocalRing Λ]
  (σ : ResidueField Λ →+* Λ) {d : ℕ} (x : Fin d → Λ)

/-- Any single element of `Λ` lies in the stage of a finitely generated enlargement of a given
finitely generated coefficient field. -/
lemma exists_fg_mem_coefficientStage
    (hsurj : Function.Surjective (MvPolynomial.eval₂Hom σ x))
    (F₀ : IntermediateField k (ResidueField Λ)) (hF₀ : F₀.FG) (y : Λ) :
    ∃ F : IntermediateField k (ResidueField Λ), F₀ ≤ F ∧ F.FG ∧
      y ∈ coefficientStage σ F x :=
  exists_fg_mem_stage σ x hsurj F₀ hF₀ y

/-- Any finite set of elements of `Λ` lies in the stage of a finitely generated enlargement of a
given finitely generated coefficient field. -/
lemma exists_fg_subset_coefficientStage
    (hsurj : Function.Surjective (MvPolynomial.eval₂Hom σ x))
    (F₀ : IntermediateField k (ResidueField Λ)) (hF₀ : F₀.FG) (s : Finset Λ) :
    ∃ F : IntermediateField k (ResidueField Λ), F₀ ≤ F ∧ F.FG ∧
      ∀ y ∈ s, y ∈ coefficientStage σ F x :=
  exists_fg_subset_stage σ x hsurj F₀ hF₀ s

end Enlarge

/-! ### Locality of the stages -/

/-- If the maximal ideal of a local ring `Λ` is nilpotent and a subring `A` of `Λ` carries a ring
map `τ` from a field `F` hitting every residue class, then every element of `A` outside the
maximal ideal of `Λ` is a unit of `A`. -/
private theorem isUnit_of_notMem_maximalIdeal {Λ : Type*} [CommRing Λ] [IsLocalRing Λ]
    {F : Type*} [Field F]
    (hnil : IsNilpotent (maximalIdeal Λ)) (A : Subring Λ) (τ : F →+* A)
    (hτ : ∀ a : A, ∃ c : F, (a : Λ) - (τ c : Λ) ∈ maximalIdeal Λ)
    (a : A) (ha : (a : Λ) ∉ maximalIdeal Λ) : IsUnit a := by
  obtain ⟨c, hc⟩ := hτ a
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact ha (by simpa using hc)
  have hτu : IsUnit (τ c) := (isUnit_iff_ne_zero.2 hc0).map τ
  obtain ⟨n, hn⟩ := hnil
  have hm : IsNilpotent (a - τ c) := by
    refine ⟨n, Subtype.coe_injective ?_⟩
    have h := Ideal.pow_mem_pow hc n
    rw [hn] at h
    push_cast
    simpa using h
  have hu := hm.isUnit_add_right_of_commute hτu (Commute.all _ _)
  rwa [sub_add_cancel] at hu

/-- A subring of a local ring with nilpotent maximal ideal is local as soon as it carries a ring
map from a field hitting every residue class. -/
private theorem isLocalRing_of_residueSection {Λ : Type*} [CommRing Λ] [IsLocalRing Λ]
    {F : Type*} [Field F]
    (hnil : IsNilpotent (maximalIdeal Λ)) (A : Subring Λ) (τ : F →+* A)
    (hτ : ∀ a : A, ∃ c : F, (a : Λ) - (τ c : Λ) ∈ maximalIdeal Λ) :
    IsLocalRing A := by
  have key : ∀ z : A, z ∈ nonunits A → (z : Λ) ∈ maximalIdeal Λ := fun z hz => by
    by_contra h
    exact hz (isUnit_of_notMem_maximalIdeal hnil A τ hτ z h)
  refine IsLocalRing.of_nonunits_add fun y z hy hz => mem_nonunits_iff.2 fun hu => ?_
  refine IsLocalRing.notMem_maximalIdeal.2 (hu.map A.subtype) ?_
  simpa using add_mem (key y hy) (key z hz)

/-- Under the hypotheses of `isLocalRing_of_residueSection`, the maximal ideal of the subring is
the contraction of the maximal ideal of `Λ`. -/
private theorem maximalIdeal_eq_comap_of_residueSection {Λ : Type*} [CommRing Λ] [IsLocalRing Λ]
    {F : Type*} [Field F]
    (hnil : IsNilpotent (maximalIdeal Λ)) (A : Subring Λ) (τ : F →+* A)
    (hτ : ∀ a : A, ∃ c : F, (a : Λ) - (τ c : Λ) ∈ maximalIdeal Λ) [IsLocalRing A] :
    maximalIdeal A = (maximalIdeal Λ).comap A.subtype := by
  ext y
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Ideal.mem_comap]
  refine ⟨fun h => ?_, fun h hu => IsLocalRing.notMem_maximalIdeal.2 (hu.map A.subtype) h⟩
  by_contra hm
  exact h (isUnit_of_notMem_maximalIdeal hnil A τ hτ y hm)

/-- Under the hypotheses of `isLocalRing_of_residueSection`, the field `F` surjects onto the
residue field of the subring. -/
private theorem surjective_residue_comp_of_residueSection {Λ : Type*} [CommRing Λ] [IsLocalRing Λ]
    {F : Type*} [Field F]
    (hnil : IsNilpotent (maximalIdeal Λ)) (A : Subring Λ) (τ : F →+* A)
    (hτ : ∀ a : A, ∃ c : F, (a : Λ) - (τ c : Λ) ∈ maximalIdeal Λ) [IsLocalRing A] :
    Function.Surjective ((residue A).comp τ) := by
  intro y
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨c, hc⟩ := hτ a
  have h : (residue A) (a - τ c) = 0 := by
    rw [residue_eq_zero_iff, maximalIdeal_eq_comap_of_residueSection hnil A τ hτ, Ideal.mem_comap]
    simpa using hc
  rw [map_sub, sub_eq_zero] at h
  exact ⟨c, h.symm⟩

/-! ### One stage -/

/-- Every property asserted of the approximating subalgebras in Stacks 07FG, for one stage.

`Λ` carries the `K`-algebra structure given by a ring-theoretic section of its residue map, `b`
is a finite `K`-basis of `Λ`, the `xᵢ` generate `𝔪`, and `A` is a `k`-subalgebra of `Λ` whose
underlying subring is the stage of a finitely generated coefficient field `F` large enough that
the basis vectors lie in that stage and that the `b`-coordinates of `1`, of the `xⱼ` and of the
products `bᵢbⱼ` all lie in `F`.

Flatness is delivered in the stronger form of freeness, which `free_of_basis_of_linearIndependent`
produces and which `flat_of_free_of_map_maximalIdeal_ne_top` consumes. -/
theorem exists_stage {k Λ : Type*} [Field k] [CommRing Λ] [Algebra k Λ] [IsLocalRing Λ]
    [Algebra (ResidueField Λ) Λ]
    (hsec : ∀ c, residue Λ (algebraMap (ResidueField Λ) Λ c) = c)
    (hnil : IsNilpotent (maximalIdeal Λ))
    {m : ℕ} (b : Module.Basis (Fin m) (ResidueField Λ) Λ)
    {d : ℕ} (x : Fin d → Λ) (hspanx : Ideal.span (Set.range x) = maximalIdeal Λ)
    (F : IntermediateField k (ResidueField Λ)) (hfg : F.FG)
    (hb : ∀ i, b i ∈ coefficientStage (algebraMap (ResidueField Λ) Λ) F x)
    (hr1 : ∀ i, b.repr 1 i ∈ F)
    (hrx : ∀ j i, b.repr (x j) i ∈ F)
    (hrm : ∀ i j l, b.repr (b i * b j) l ∈ F)
    (A : Subalgebra k Λ)
    (hA : A.toSubring = coefficientStage (algebraMap (ResidueField Λ) Λ) F x) :
    ∃ (_ : IsArtinianRing A) (_ : IsLocalRing A),
      Module.Free A Λ ∧ Algebra.EssFiniteType k A ∧
      Ideal.map A.val.toRingHom (maximalIdeal A) = maximalIdeal Λ := by
  classical
  set σ : ResidueField Λ →+* Λ := algebraMap (ResidueField Λ) Λ with hσdef
  have hAmem : ∀ y : Λ, y ∈ A ↔ y ∈ coefficientStage σ F x := fun y => by rw [← hA]; exact Iff.rfl
  have hxm : ∀ i, x i ∈ maximalIdeal Λ := fun i =>
    hspanx ▸ Ideal.subset_span (Set.mem_range_self i)
  -- the `F`-algebra structures
  have hτmem : ∀ c : F, algebraMap F Λ c ∈ A := fun c =>
    (hAmem _).2 (mem_coefficientStage_of_mem σ x F c)
  let : Algebra F A := (RingHom.codRestrict (algebraMap F Λ) A hτmem).toAlgebra
  have htow : IsScalarTower F A Λ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hFAcoe : ∀ c : F, ((algebraMap F A c : A) : Λ) = σ (c : ResidueField Λ) :=
    fun c => (IsScalarTower.algebraMap_apply F A Λ c).symm
  -- the stage is the `F`-span of the basis
  have hspanmem : ∀ y : Λ, (∀ i, b.repr y i ∈ F) → y ∈ Submodule.span F (Set.range b) := by
    intro y hy
    rw [← b.sum_repr y]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h : (⟨b.repr y i, hy i⟩ : F) • b i = b.repr y i • b i :=
      algebraMap_smul (ResidueField Λ) (⟨b.repr y i, hy i⟩ : F) (b i)
    rw [← h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hcarrier : ∀ y : Λ, y ∈ A ↔ y ∈ Submodule.span F (Set.range b) := by
    have h := aeval_range_eq_span (F := F) (Λ := Λ) b x (hspanmem 1 hr1)
      (fun j => hspanmem (x j) (hrx j)) (fun i j => hspanmem _ (hrm i j))
      (fun i => by obtain ⟨f, hf⟩ := hb i; exact ⟨f, hf⟩)
    intro y
    refine ⟨fun hy => ?_, fun hy => ?_⟩
    · obtain ⟨f, hf⟩ := (hAmem y).1 hy
      exact (Set.ext_iff.mp h y).1 ⟨f, hf⟩
    · obtain ⟨f, hf⟩ := (Set.ext_iff.mp h y).2 hy
      exact (hAmem y).2 ⟨f, hf⟩
  -- the basis of the stage over `F`
  have hbA : ∀ i, b i ∈ A := fun i => (hAmem _).2 (hb i)
  have hinjF : Function.Injective fun r : F => r • (1 : ResidueField Λ) := by
    intro c c' h
    simp only [Algebra.smul_def, mul_one] at h
    exact Subtype.coe_injective h
  have hval : ∀ z : A, ((Algebra.linearMap A Λ).restrictScalars F) z = (z : Λ) := fun _ => rfl
  have hindepF : LinearIndependent F (fun i => (⟨b i, hbA i⟩ : A)) :=
    LinearIndependent.of_comp ((Algebra.linearMap A Λ).restrictScalars F)
      (b.linearIndependent.restrict_scalars hinjF)
  have hcoe : ∀ c : Fin m → F, ((∑ i, c i • (⟨b i, hbA i⟩ : A) : A) : Λ) = ∑ i, c i • b i := by
    intro c
    rw [← hval, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [LinearMap.map_smul]; rfl
  have hspanA : ⊤ ≤ Submodule.span F (Set.range fun i => (⟨b i, hbA i⟩ : A)) := by
    rintro ⟨y, hy⟩ -
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp ((hcarrier y).1 hy)
    rw [Submodule.mem_span_range_iff_exists_fun]
    exact ⟨c, Subtype.ext ((hcoe c).trans hc)⟩
  let bA : Module.Basis (Fin m) F A := Module.Basis.mk hindepF hspanA
  have hbAapply : (fun i => algebraMap A Λ (bA i)) = b := by
    funext i; simp [bA]
  have hfinFA : Module.Finite F A := Module.Finite.of_basis bA
  have hart : IsArtinianRing A := IsArtinianRing.of_finite F A
  -- the stage is local, with residue field a quotient of `F`
  have hresF : ∀ y ∈ A, residue Λ y ∈ F := by
    intro y hy
    obtain ⟨f, rfl⟩ := (hAmem y).1 hy
    refine MvPolynomial.induction_on
      (motive := fun g => residue Λ (MvPolynomial.eval₂Hom (σ.comp F.val.toRingHom) x g) ∈ F)
      f ?_ ?_ ?_
    · intro a
      simp [hsec]
    · intro p q hp hq
      simp only [map_add]
      exact add_mem hp hq
    · intro p i hp
      have h0 : residue Λ (x i) = 0 := (residue_eq_zero_iff _).mpr (hxm i)
      simp [h0]
  have hτ : ∀ a : A.toSubring, ∃ c : F,
      (a : Λ) - ((algebraMap F A c : A) : Λ) ∈ maximalIdeal Λ := by
    intro a
    refine ⟨⟨residue Λ (a : Λ), hresF _ a.2⟩, ?_⟩
    rw [hFAcoe, ← residue_eq_zero_iff, map_sub, hsec, sub_self]
  have hloc : IsLocalRing A :=
    isLocalRing_of_residueSection hnil A.toSubring (algebraMap F A) hτ
  have hmax : maximalIdeal A = (maximalIdeal Λ).comap A.val.toRingHom :=
    maximalIdeal_eq_comap_of_residueSection hnil A.toSubring (algebraMap F A) hτ
  refine ⟨hart, hloc, ?_, ?_, ?_⟩
  · -- `Λ` is free over the stage
    exact free_of_basis_of_linearIndependent (K := ResidueField Λ) bA
      (by rw [hbAapply]; exact b.linearIndependent) (by rw [hbAapply]; exact b.span_eq)
  · -- the stage is essentially of finite type over `k`
    have hEFT : Algebra.EssFiniteType k F := IntermediateField.essFiniteType_iff.mpr hfg
    have hφcomm : ∀ a : k, ((residue A).comp (algebraMap F A)) (algebraMap k F a)
        = algebraMap k (ResidueField A) a := by
      intro a
      have hdiff : algebraMap F A (algebraMap k F a) - algebraMap k A a ∈ maximalIdeal A := by
        rw [hmax, Ideal.mem_comap, map_sub]
        have he1 : A.val.toRingHom (algebraMap F A (algebraMap k F a))
            = σ (algebraMap k (ResidueField Λ) a) := hFAcoe _
        have he2 : A.val.toRingHom (algebraMap k A a) = algebraMap k Λ a := rfl
        rw [he1, he2, ← residue_eq_zero_iff, map_sub, hsec]
        exact sub_eq_zero.mpr rfl
      have h2 : (residue A) (algebraMap F A (algebraMap k F a) - algebraMap k A a) = 0 :=
        (residue_eq_zero_iff _).mpr hdiff
      rw [map_sub, sub_eq_zero] at h2
      exact h2
    let φ : F →ₐ[k] ResidueField A :=
      { ((residue A).comp (algebraMap F A)) with commutes' := hφcomm }
    have hRes : Algebra.EssFiniteType k (ResidueField A) :=
      Algebra.EssFiniteType.of_surjective φ
        (surjective_residue_comp_of_residueSection hnil A.toSubring (algebraMap F A) hτ)
    rw [← RingHom.essFiniteType_algebraMap, essFiniteType_iff_residue_essFiniteType]
    have hcomp : (residue A).comp (algebraMap k A) = algebraMap k (ResidueField A) := rfl
    rw [hcomp]
    exact RingHom.essFiniteType_algebraMap.mpr hRes
  · -- the maximal ideal of the stage generates `𝔪`
    refine le_antisymm ?_ ?_
    · rw [hmax]; exact Ideal.map_comap_le
    · rw [← hspanx, Ideal.span_le]
      rintro y ⟨i, rfl⟩
      have hxA : x i ∈ A := (hAmem _).2 (mem_coefficientStage_gen σ x F i)
      have hmem : (⟨x i, hxA⟩ : A) ∈ maximalIdeal A := by
        rw [hmax, Ideal.mem_comap]; exact hxm i
      exact Ideal.mem_map_of_mem A.val.toRingHom hmem

end Stacks.Smoothing
