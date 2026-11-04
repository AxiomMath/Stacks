module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RingTheory.Nakayama
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.CharP.Lemmas
public import StacksFrontier.Deformation.Representation.FixedDeterminantFiniteness.LocalRing

/-!
# Descent of a residually absolutely irreducible representation with finite image

Let `S` be a reduced local ring of characteristic `ℓ` whose residue field is `𝐅_ℓ`, and let
`ρ₀ : N → GLₙ(𝐅_ℓ)` be a representation of a group `N` whose image spans the matrix algebra. A
representation `σ : N → GLₙ(S)` with finite image reducing to `ρ₀` is conjugate to `ρ₀` by a
matrix congruent to the identity.

The traces of `σ` are those of `ρ₀`, by the Frobenius identity `tr (X ^ ℓ) = (tr X) ^ ℓ`: an
element `b` of the maximal ideal with `b ^ ℓ ^ k₁ = b ^ ℓ ^ k₂` for some `k₁ < k₂` is nilpotent.
The trace pairing then shows that `ρ₀ h ↦ σ h` extends to an algebra map
`L : Mₙ(𝐅_ℓ) → Mₙ(S)` congruent to the inclusion, and the matrix
`P = ∑ᵢ L(E_{i i₀}) E_{i₀ i}` intertwines `L` with the inclusion.

## Main results

* `Matrix.trace_eq_algebraMap_trace_of_pow_eq_pow` — a matrix congruent to an `𝐅_ℓ`-matrix `X₀`
  with `X ^ ℓ ^ k₁ = X ^ ℓ ^ k₂` for some `k₁ < k₂` has the trace of `X₀`.
* `Matrix.mem_range_scalar_of_commute_span_eq_top` — a matrix over `S` commuting with a set of
  `𝐅_ℓ`-matrices spanning the matrix algebra is scalar.
* `Matrix.exists_conj_eq_of_finite_range` — the descent statement.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace Matrix

variable {ℓ : ℕ} [Fact ℓ.Prime] {S : Type*} [CommRing S] [IsLocalRing S] [Algebra (ZMod ℓ) S]
  {n : Type*} [Fintype n] [DecidableEq n]

/-- A matrix `X` over a reduced local ring of characteristic `ℓ`, congruent modulo the maximal
ideal to an `𝐅_ℓ`-matrix `X₀` and with `X ^ ℓ ^ k₁ = X ^ ℓ ^ k₂` for some `k₁ < k₂`, has the
trace of `X₀`. -/
theorem trace_eq_algebraMap_trace_of_pow_eq_pow [IsReduced S] (X : Matrix n n S)
    (X₀ : Matrix n n (ZMod ℓ))
    (hX : X.map (residue S) = (X₀.map (algebraMap (ZMod ℓ) S)).map (residue S))
    {k₁ k₂ : ℕ} (hk : k₁ < k₂) (hpow : X ^ ℓ ^ k₁ = X ^ ℓ ^ k₂) :
    X.trace = algebraMap (ZMod ℓ) S X₀.trace := by
  have : CharP S ℓ := charP_of_injective_algebraMap (algebraMap (ZMod ℓ) S).injective ℓ
  set b := X.trace - algebraMap (ZMod ℓ) S X₀.trace with hbdef
  have hb : b ∈ maximalIdeal S := by
    rw [← residue_eq_zero_iff, hbdef, map_sub, sub_eq_zero]
    have h1 := AddMonoidHom.map_trace (residue S).toAddMonoidHom X
    have h2 := AddMonoidHom.map_trace (residue S).toAddMonoidHom (X₀.map (algebraMap (ZMod ℓ) S))
    have h3 := AddMonoidHom.map_trace (algebraMap (ZMod ℓ) S).toAddMonoidHom X₀
    simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe] at h1 h2 h3
    rw [h1, h3, h2]
    exact congrArg trace hX
  have hfrob : ∀ k, b ^ ℓ ^ k = (X ^ ℓ ^ k).trace - algebraMap (ZMod ℓ) S X₀.trace := by
    intro k
    rw [hbdef, sub_pow_char_pow, ← map_pow, ZMod.pow_card_pow, trace_pow_char_pow]
  have hq : 2 ≤ ℓ ^ (k₂ - k₁) :=
    (Fact.out : ℓ.Prime).two_le.trans (Nat.le_self_pow (by omega) ℓ)
  have he : (b ^ ℓ ^ k₁) ^ ℓ ^ (k₂ - k₁) = b ^ ℓ ^ k₁ := by
    rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hk.le, hfrob, hfrob, hpow]
  have hem : b ^ ℓ ^ k₁ ∈ maximalIdeal S :=
    Ideal.pow_mem_of_mem _ hb _ (Nat.pow_pos (Fact.out : ℓ.Prime).pos)
  exact sub_eq_zero.1 (IsReduced.eq_zero b
    ⟨_, IsLocalRing.eq_zero_of_mem_maximalIdeal_of_pow_eq_self hem hq he⟩)

omit [IsLocalRing S] in
/-- A matrix over `S` commuting with the images of a family of `𝐅_ℓ`-matrices whose span is the
whole matrix algebra is scalar. -/
theorem mem_range_scalar_of_commute_span_eq_top {ι : Type*} (v : ι → Matrix n n (ZMod ℓ))
    (hv : Submodule.span (ZMod ℓ) (Set.range v) = ⊤) (M : Matrix n n S)
    (hM : ∀ i, Commute ((v i).map (algebraMap (ZMod ℓ) S)) M) :
    M ∈ Set.range (scalar n) := by
  let C : Submodule (ZMod ℓ) (Matrix n n (ZMod ℓ)) :=
    { carrier := {Y | Commute (Y.map (algebraMap (ZMod ℓ) S)) M}
      add_mem' := fun {Y Z} hY hZ => by
        simp only [Set.mem_ofPred_eq] at *
        rw [Matrix.map_add _ (map_add _)]
        exact hY.add_left hZ
      zero_mem' := by simp
      smul_mem' := fun c Y hY => by
        simp only [Set.mem_ofPred_eq] at *
        have : (c • Y).map (algebraMap (ZMod ℓ) S) =
            algebraMap (ZMod ℓ) S c • Y.map (algebraMap (ZMod ℓ) S) := by
          ext i j
          rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.smul_apply,
            Matrix.map_apply, smul_eq_mul]
        rw [this]
        exact hY.smul_left _ }
  have hC : C = ⊤ := by
    rw [eq_top_iff, ← hv, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hM i
  refine mem_range_scalar_of_commute_single fun i j _ => ?_
  have h : single i j (1 : ZMod ℓ) ∈ C := hC ▸ Submodule.mem_top
  have hmap : (single i j (1 : ZMod ℓ)).map (algebraMap (ZMod ℓ) S) = single i j 1 := by
    ext a b
    by_cases h1 : a = i <;> by_cases h2 : b = j <;> simp [single_apply, h1, h2]
  change Commute ((single i j (1 : ZMod ℓ)).map (algebraMap (ZMod ℓ) S)) M at h
  rwa [hmap] at h

/-- A matrix whose entries lie in an ideal `I` lies in `I • ⊤`. -/
theorem mem_smul_top_of_forall_mem {R : Type*} [CommRing R] (I : Ideal R) (X : Matrix n n R)
    (hX : ∀ i j, X i j ∈ I) : X ∈ I • (⊤ : Submodule R (Matrix n n R)) := by
  rw [matrix_eq_sum_single X]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  rw [show single i j (X i j) = X i j • single i j (1 : R) by
    rw [smul_single, smul_eq_mul, mul_one]]
  exact Submodule.smul_mem_smul (hX i j) Submodule.mem_top

variable {N : Type*} [Monoid N]

omit [Monoid N] in
/-- **Nakayama for the span of a representation.** If the residue field of `S` is `𝐅_ℓ` and a
representation `σ : N → Mₙ(S)` is congruent to an `𝐅_ℓ`-representation `ρ₀` whose image spans
`Mₙ(𝐅_ℓ)`, then the image of `σ` spans `Mₙ(S)` over `S`. -/
theorem span_range_eq_top_of_congr (σ ρ₀ : N → Matrix n n S) (ρ₀' : N → Matrix n n (ZMod ℓ))
    (hρ₀ : ∀ h, ρ₀ h = (ρ₀' h).map (algebraMap (ZMod ℓ) S))
    (hspan : Submodule.span (ZMod ℓ) (Set.range ρ₀') = ⊤)
    (hres : Function.Surjective ((residue S).comp (algebraMap (ZMod ℓ) S)))
    (hcong : ∀ h i j, σ h i j - ρ₀ h i j ∈ maximalIdeal S) :
    Submodule.span S (Set.range σ) = ⊤ := by
  classical
  refine top_le_iff.1 (Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal S)
    (Module.Finite.fg_top) ?_ ?_)
  · rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  intro X _
  choose c hc using fun x : S => hres (residue S x)
  let X₀ : Matrix n n (ZMod ℓ) := Matrix.of fun i j => c (X i j)
  have hX₀ : X₀ ∈ Submodule.span (ZMod ℓ) (Set.range ρ₀') := hspan ▸ Submodule.mem_top
  obtain ⟨a, ha⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hX₀
  let Y : Matrix n n S := a.sum fun h b => algebraMap (ZMod ℓ) S b • σ h
  have hY : Y ∈ Submodule.span S (Set.range σ) :=
    Submodule.sum_mem _ fun h _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨h, rfl⟩)
  have hdiff : ∀ i j, (X - Y) i j ∈ maximalIdeal S := by
    intro i j
    have hXij : X i j - algebraMap (ZMod ℓ) S (X₀ i j) ∈ maximalIdeal S := by
      rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
      exact (hc (X i j)).symm
    have hX₀ij : algebraMap (ZMod ℓ) S (X₀ i j) =
        a.sum fun h b => algebraMap (ZMod ℓ) S b * ρ₀ h i j := by
      rw [← ha]
      simp only [Finsupp.sum, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum,
        map_mul, hρ₀, Matrix.map_apply]
    have hYij : Y i j = a.sum fun h b => algebraMap (ZMod ℓ) S b * σ h i j := by
      simp only [Y, Finsupp.sum, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    have hsum : algebraMap (ZMod ℓ) S (X₀ i j) - Y i j ∈ maximalIdeal S := by
      rw [hX₀ij, hYij, Finsupp.sum, Finsupp.sum, ← Finset.sum_sub_distrib]
      refine Ideal.sum_mem _ fun h _ => ?_
      rw [← mul_sub]
      exact Ideal.mul_mem_left _ _ (by simpa using (maximalIdeal S).neg_mem (hcong h i j))
    rw [Matrix.sub_apply]
    simpa using (maximalIdeal S).add_mem hXij hsum
  rw [show X = Y + (X - Y) by abel]
  exact Submodule.add_mem_sup hY (mem_smul_top_of_forall_mem _ _ hdiff)

omit [IsLocalRing S] in
/-- **Nondegeneracy of the trace pairing against a spanning family.** A matrix `Z` with
`tr (Z * v i) = 0` for every member of a family spanning `Mₙ(S)` is zero. -/
theorem eq_zero_of_trace_mul_eq_zero {ι : Type*} (v : ι → Matrix n n S)
    (hv : Submodule.span S (Set.range v) = ⊤) (Z : Matrix n n S)
    (hZ : ∀ i, (Z * v i).trace = 0) : Z = 0 := by
  let f : Matrix n n S →ₗ[S] S :=
    { toFun := fun Y => (Z * Y).trace
      map_add' := fun Y W => by rw [Matrix.mul_add, trace_add]
      map_smul' := fun c Y => by
        rw [Matrix.mul_smul, trace_smul]
        rfl }
  have hf : f = 0 := LinearMap.ext_on_range hv hZ
  ext i j
  have := LinearMap.congr_fun hf (single j i 1)
  simp only [f, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply, trace_mul_single] at this
  simpa using this

/-- Right multiplication of a matrix by a matrix unit, column by column. -/
theorem mul_single_one_eq_sum {R : Type*} [CommRing R] (M : Matrix n n R) (b i₀ : n) :
    M * single b i₀ (1 : R) = ∑ k, M k b • single k i₀ (1 : R) := by
  ext a c
  simp only [mul_apply, single_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases hc : i₀ = c <;> simp [hc, eq_comm]

/-- Entrywise congruence modulo the maximal ideal is equality of residue matrices. -/
private theorem forall_sub_mem_iff_map_residue_eq {a b : Type*} (X Y : Matrix a b S) :
    (∀ i j, X i j - Y i j ∈ maximalIdeal S) ↔ X.map (residue S) = Y.map (residue S) := by
  constructor
  · intro h
    ext i j
    have := h i j
    rwa [← residue_eq_zero_iff, map_sub, sub_eq_zero] at this
  · intro h i j
    rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
    exact congrFun (congrFun h i) j

/-- A matrix is congruent to the identity modulo the maximal ideal iff its residue is `1`. -/
private theorem forall_sub_one_mem_iff_map_residue_eq_one {a : Type*} [DecidableEq a]
    (P : Matrix a a S) :
    (∀ i j, P i j - (1 : Matrix a a S) i j ∈ maximalIdeal S) ↔ P.map (residue S) = 1 := by
  rw [forall_sub_mem_iff_map_residue_eq, Matrix.map_one _ (map_zero _) (map_one _)]

/-- **Descent of a residually absolutely irreducible representation.** Let `S` be a local ring
with residue field `𝐅_ℓ`, `ρ₀ : N → Mₙ(𝐅_ℓ)` a representation whose image spans `Mₙ(𝐅_ℓ)`, and
`σ : N → Mₙ(S)` a representation congruent to `ρ₀` with the same traces. Then `σ` is conjugate to
`ρ₀` by an invertible matrix `P` congruent to the identity: `σ h * P = P * ρ₀ h` for all `h`. -/
theorem exists_conj_of_trace_eq (σ : N →* Matrix n n S) (ρ₀ : N →* Matrix n n (ZMod ℓ))
    (hspan : Submodule.span (ZMod ℓ) (Set.range ρ₀) = ⊤)
    (hres : Function.Surjective ((residue S).comp (algebraMap (ZMod ℓ) S)))
    (hcong : ∀ h i j, σ h i j - algebraMap (ZMod ℓ) S (ρ₀ h i j) ∈ maximalIdeal S)
    (htr : ∀ h, (σ h).trace = algebraMap (ZMod ℓ) S (ρ₀ h).trace) :
    ∃ P : Matrix n n S, IsUnit P ∧ (∀ i j, P i j - (1 : Matrix n n S) i j ∈ maximalIdeal S) ∧
      ∀ h, σ h * P = P * (ρ₀ h).map (algebraMap (ZMod ℓ) S) := by
  classical
  let alg := algebraMap (ZMod ℓ) S
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i₀⟩⟩
  · exact ⟨1, isUnit_one, isEmptyElim, fun h => Subsingleton.elim _ _⟩
  let L₀ := Finsupp.linearCombination (ZMod ℓ) (fun h => ρ₀ h)
  let L₁ : (N →₀ ZMod ℓ) →ₗ[ZMod ℓ] Matrix n n S :=
    Finsupp.linearCombination (ZMod ℓ) (fun h => σ h)
  have hsurj : Function.Surjective L₀ := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact hspan
  have hspanS : Submodule.span S (Set.range σ) = ⊤ :=
    span_range_eq_top_of_congr (fun h => σ h) (fun h => (ρ₀ h).map alg) (fun h => ρ₀ h)
      (fun _ => rfl) hspan hres hcong
  have hsmul : ∀ (b : ZMod ℓ) (M : Matrix n n S), b • M = alg b • M :=
    algebra_compatible_smul S
  have key : ∀ c g, (L₁ c * σ g).trace = alg (L₀ c * ρ₀ g).trace := by
    intro c g
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, Matrix.add_mul, Matrix.add_mul, trace_add,
        trace_add, hx, hy, map_add]
    | single h b =>
      simp only [L₀, L₁, Finsupp.linearCombination_single]
      rw [hsmul, Matrix.smul_mul, Matrix.smul_mul, trace_smul, trace_smul, ← map_mul, ← map_mul,
        htr, smul_eq_mul, smul_eq_mul]
      exact (map_mul alg b _).symm
  have hker : LinearMap.ker L₀ ≤ LinearMap.ker L₁ := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    refine eq_zero_of_trace_mul_eq_zero (fun h => σ h) hspanS _ fun g => ?_
    rw [key, hc, Matrix.zero_mul, trace_zero, map_zero]
  let Φ : Matrix n n (ZMod ℓ) →ₗ[ZMod ℓ] Matrix n n S :=
    (LinearMap.ker L₀).liftQ L₁ hker ∘ₗ (L₀.quotKerEquivOfSurjective hsurj).symm.toLinearMap
  have hΦ : ∀ c, Φ (L₀ c) = L₁ c := fun c => by
    simp [Φ, LinearMap.quotKerEquivOfSurjective_symm_apply]
  have hΦρ : ∀ h, Φ (ρ₀ h) = σ h := fun h => by
    simpa [L₀, L₁, Finsupp.linearCombination_single] using hΦ (Finsupp.single h 1)
  have hΦcong : ∀ Y i j, Φ Y i j - alg (Y i j) ∈ maximalIdeal S := by
    intro Y
    obtain ⟨c, rfl⟩ := hsurj Y
    rw [hΦ]
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy =>
      intro i j
      have := (maximalIdeal S).add_mem (hx i j) (hy i j)
      simp only [map_add, Matrix.add_apply] at this ⊢
      convert this using 1
      ring
    | single h b =>
      intro i j
      simp only [L₀, L₁, Finsupp.linearCombination_single]
      rw [hsmul b, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul,
        ← mul_sub]
      exact Ideal.mul_mem_left _ _ (hcong h i j)
  have hequiv : ∀ g Y, Φ (ρ₀ g * Y) = σ g * Φ Y := by
    intro g
    have : (Φ ∘ₗ LinearMap.mulLeft (ZMod ℓ) (ρ₀ g)) =
        ((LinearMap.mulLeft (ZMod ℓ) (σ g)).restrictScalars (ZMod ℓ) ∘ₗ Φ) := by
      refine LinearMap.ext_on_range hspan fun h => ?_
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
        LinearMap.coe_restrictScalars]
      rw [← map_mul, hΦρ, hΦρ, map_mul]
    exact LinearMap.congr_fun this
  let P : Matrix n n S := Matrix.of fun a b => Φ (single b i₀ 1) a i₀
  have hP1 : ∀ a b, P a b - (1 : Matrix n n S) a b ∈ maximalIdeal S := by
    intro a b
    have h2 : alg ((single b i₀ (1 : ZMod ℓ)) a i₀) = (1 : Matrix n n S) a b := by
      by_cases hab : a = b
      · simp [one_apply, hab]
      · simp [hab, Ne.symm hab]
    simpa [P, h2] using hΦcong (single b i₀ 1) a i₀
  have hPres : P.map (residue S) = 1 :=
    (forall_sub_one_mem_iff_map_residue_eq_one P).1 hP1
  have hPunit : IsUnit P := by
    rw [isUnit_iff_isUnit_det]
    have hdet : residue S P.det = 1 := by
      rw [RingHom.map_det]
      exact (congrArg det hPres).trans det_one
    by_contra hnu
    have := (residue_eq_zero_iff P.det).2 ((mem_maximalIdeal _).2 hnu)
    rw [hdet] at this
    exact one_ne_zero this
  refine ⟨P, hPunit, hP1, fun g => ?_⟩
  ext a b
  have hl : (σ g * P) a b = (σ g * Φ (single b i₀ 1)) a i₀ := by
    simp only [mul_apply, P, of_apply]
  have hr : (P * (ρ₀ g).map alg) a b = (∑ k, (ρ₀ g k b) • Φ (single k i₀ 1)) a i₀ := by
    simp only [mul_apply, P, of_apply, Matrix.sum_apply, Matrix.map_apply, hsmul,
      Matrix.smul_apply, smul_eq_mul, mul_comm]
  rw [hl, hr, ← hequiv, mul_single_one_eq_sum, map_sum]
  simp only [map_smul]

end Matrix

namespace Matrix.GeneralLinearGroup

variable {ℓ : ℕ} [Fact ℓ.Prime] {S : Type*} [CommRing S] [IsLocalRing S] [Algebra (ZMod ℓ) S]
  {n : Type*} [Fintype n] [DecidableEq n]

/-- **Rigidity on a normal subgroup.** Let `N` be a normal subgroup of a group `π`, and
`ρ₀ : π → GLₙ(𝐅_ℓ)` a representation whose restriction to `N` spans `Mₙ(𝐅_ℓ)`, with `#n`
invertible in `S`. A representation `σ : π → GLₙ(S)` congruent to `ρ₀`, with the determinant of
`ρ₀` and equal to `ρ₀` on `N`, is equal to `ρ₀`: for `g ∈ π` the matrix `ρ₀(g)⁻¹ σ(g)` commutes
with `ρ₀(N)`, hence is a scalar `u ≡ 1` with `u ^ #n = 1`, so `u = 1`. -/
theorem eq_map_of_eq_map_of_mem_normal {π : Type*} [Group π] (N : Subgroup π) [N.Normal]
    (ρ₀ : π →* GL n (ZMod ℓ))
    (hspan : Submodule.span (ZMod ℓ)
      (Set.range fun h : N => (ρ₀ h : Matrix n n (ZMod ℓ))) = ⊤)
    (hn : IsUnit (Fintype.card n : S)) (σ : π →* GL n S)
    (hcong : ∀ g i j, (σ g : Matrix n n S) i j - algebraMap (ZMod ℓ) S (ρ₀ g i j) ∈
      maximalIdeal S)
    (hdet : ∀ g, (σ g : Matrix n n S).det = algebraMap (ZMod ℓ) S (ρ₀ g : Matrix n n _).det)
    (hN : ∀ h ∈ N, σ h = map (algebraMap (ZMod ℓ) S) (ρ₀ h)) (g : π) :
    σ g = map (algebraMap (ZMod ℓ) S) (ρ₀ g) := by
  classical
  set alg := algebraMap (ZMod ℓ) S
  rcases isEmpty_or_nonempty n with hne | ⟨⟨i₀⟩⟩
  · exact ext fun i => isEmptyElim i
  set A : GL n S := map alg (ρ₀ g)
  set M : Matrix n n S := ((A⁻¹ * σ g : GL n S) : Matrix n n S)
  have hcomm : ∀ h : N, Commute ((ρ₀ h : Matrix n n (ZMod ℓ)).map alg) M := by
    intro ⟨h, hh⟩
    have hk : g * h * g⁻¹ ∈ N := Subgroup.Normal.conj_mem ‹_› h hh g
    have e1 := hN _ hk
    simp only [map_mul, map_inv, hN h hh] at e1
    have e2 : A⁻¹ * σ g * map alg (ρ₀ h) = map alg (ρ₀ h) * (A⁻¹ * σ g) := by
      calc A⁻¹ * σ g * map alg (ρ₀ h)
          = A⁻¹ * (σ g * map alg (ρ₀ h) * (σ g)⁻¹) * σ g := by group
        _ = A⁻¹ * (A * map alg (ρ₀ h) * A⁻¹) * σ g := by rw [e1]
        _ = map alg (ρ₀ h) * (A⁻¹ * σ g) := by group
    have := congrArg (fun x : GL n S => (x : Matrix n n S)) e2
    simpa [Commute, SemiconjBy, M, Matrix.mul_assoc] using this.symm
  obtain ⟨u, hu⟩ := mem_range_scalar_of_commute_span_eq_top _ hspan M hcomm
  have hMcong : ∀ i j, M i j - (1 : Matrix n n S) i j ∈ maximalIdeal S := by
    intro i j
    have hres : (σ g : Matrix n n S).map (residue S) = (A : Matrix n n S).map (residue S) :=
      (forall_sub_mem_iff_map_residue_eq _ _).1 (hcong g)
    have hM : M.map (residue S) = 1 := by
      have : M = (A⁻¹ : GL n S) * (σ g : Matrix n n S) := rfl
      rw [this, ← RingHom.mapMatrix_apply, map_mul, RingHom.mapMatrix_apply,
        RingHom.mapMatrix_apply, hres, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply,
        ← map_mul, ← coe_mul, inv_mul_cancel, coe_one, map_one]
    exact (forall_sub_one_mem_iff_map_residue_eq_one M).2 hM i j
  have hu1 : u - 1 ∈ maximalIdeal S := by
    have := hMcong i₀ i₀
    rwa [← hu, scalar_apply, diagonal_apply_eq, one_apply_eq] at this
  have hdetM : u ^ Fintype.card n = 1 := by
    have h1 : M.det = 1 := by
      have : M = (A⁻¹ : GL n S) * (σ g : Matrix n n S) := rfl
      rw [this, det_mul, hdet g]
      have hA : (A : Matrix n n S).det = alg (ρ₀ g : Matrix n n _).det := by
        simp only [A]
        rw [show ((map alg (ρ₀ g) : GL n S) : Matrix n n S) =
          (alg.mapMatrix (ρ₀ g : Matrix n n (ZMod ℓ))) from rfl, ← RingHom.map_det]
      rw [← hA, ← det_mul, ← coe_mul, inv_mul_cancel, coe_one, det_one]
    rwa [← hu, scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ] at h1
  have hu' : u = 1 :=
    sub_eq_zero.1 (IsLocalRing.eq_zero_of_one_add_pow_eq_one hu1 hn (by rwa [add_sub_cancel]))
  have hM1 : M = 1 := by rw [← hu, hu', map_one]
  have : A⁻¹ * σ g = 1 := ext fun i j => by simpa [M] using congrFun (congrFun hM1 i) j
  rw [← mul_left_cancel_iff (a := A⁻¹), this, inv_mul_cancel]

omit [Fintype n] [DecidableEq n] in
/-- Entrywise congruence modulo the maximal ideal is equality of residue matrices. -/
theorem _root_.Matrix.forall_sub_mem_maximalIdeal_iff {m : Type*} (X Y : Matrix n m S) :
    (∀ i j, X i j - Y i j ∈ maximalIdeal S) ↔ X.map (residue S) = Y.map (residue S) :=
  forall_sub_mem_iff_map_residue_eq X Y

/-- **Descent with finite geometric image.** Let `N` be a normal subgroup of a group `π`, let `S`
be a reduced local ring with residue field `𝐅_ℓ` in which `#n` is invertible, and let
`ρ₀ : π → GLₙ(𝐅_ℓ)` be a representation whose restriction to `N` spans `Mₙ(𝐅_ℓ)`. A
representation `σ : π → GLₙ(S)` congruent to `ρ₀`, with the determinant of `ρ₀` and with finite
image on `N`, is conjugate to `ρ₀` by a matrix congruent to the identity. -/
theorem exists_conj_eq_map_of_finite_image [IsReduced S] {π : Type*} [Group π]
    (N : Subgroup π) [N.Normal] (ρ₀ : π →* GL n (ZMod ℓ))
    (hspan : Submodule.span (ZMod ℓ)
      (Set.range fun h : N => (ρ₀ h : Matrix n n (ZMod ℓ))) = ⊤)
    (hres : Function.Surjective ((residue S).comp (algebraMap (ZMod ℓ) S)))
    (hn : IsUnit (Fintype.card n : S)) (σ : π →* GL n S)
    (hcong : ∀ g i j, (σ g : Matrix n n S) i j - algebraMap (ZMod ℓ) S (ρ₀ g i j) ∈
      maximalIdeal S)
    (hdet : ∀ g, (σ g : Matrix n n S).det = algebraMap (ZMod ℓ) S (ρ₀ g : Matrix n n _).det)
    (hfin : (σ '' N).Finite) :
    ∃ P : GL n S, (∀ i j, (P : Matrix n n S) i j - (1 : Matrix n n S) i j ∈ maximalIdeal S) ∧
      ∀ g, P⁻¹ * σ g * P = map (algebraMap (ZMod ℓ) S) (ρ₀ g) := by
  classical
  set alg := algebraMap (ZMod ℓ) S
  let σN : N →* Matrix n n S := (Units.coeHom _).comp (σ.comp N.subtype)
  let ρN : N →* Matrix n n (ZMod ℓ) := (Units.coeHom _).comp (ρ₀.comp N.subtype)
  have htr : ∀ h, (σN h).trace = alg (ρN h).trace := by
    intro ⟨h, hh⟩
    obtain ⟨k₁, k₂, hk, heq⟩ := hfin.exists_lt_map_eq_of_forall_mem
      (f := fun k : ℕ => σ (h ^ ℓ ^ k)) fun k => Set.mem_image_of_mem σ (N.pow_mem hh _)
    refine Matrix.trace_eq_algebraMap_trace_of_pow_eq_pow _ _ ?_ hk ?_
    · exact (Matrix.forall_sub_mem_maximalIdeal_iff _ _).1 (hcong h)
    · simp only [σN, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        Units.coeHom_apply]
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← map_pow, ← map_pow]
      exact congrArg Units.val heq
  obtain ⟨P, hPu, hP1, hPconj⟩ := Matrix.exists_conj_of_trace_eq σN ρN hspan hres
    (fun h i j => hcong h i j) htr
  let Pu : GL n S := hPu.unit
  have hPu_coe : (Pu : Matrix n n S) = P := hPu.unit_spec
  let τ : π →* GL n S := (MulAut.conj Pu⁻¹).toMonoidHom.comp σ
  have hτ : ∀ g, τ g = Pu⁻¹ * σ g * Pu := fun g => by simp [τ]
  have hPres : (Pu : Matrix n n S).map (residue S) = 1 := by
    rw [hPu_coe]
    exact (forall_sub_one_mem_iff_map_residue_eq_one P).1 hP1
  have hPinvres : ((Pu⁻¹ : GL n S) : Matrix n n S).map (residue S) = 1 := by
    have h := congrArg (fun x : GL n S => (residue S).mapMatrix (x : Matrix n n S))
      (inv_mul_cancel Pu)
    simp only [coe_mul, map_mul, coe_one, map_one] at h
    rwa [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hPres, Matrix.mul_one] at h
  refine ⟨Pu, by rwa [hPu_coe], fun g => ?_⟩
  rw [← hτ]
  refine eq_map_of_eq_map_of_mem_normal N ρ₀ hspan hn τ (fun g' => ?_) (fun g' => ?_)
    (fun h hh => ?_) g
  · refine (Matrix.forall_sub_mem_maximalIdeal_iff _
      ((ρ₀ g' : Matrix n n (ZMod ℓ)).map alg)).2 ?_
    rw [hτ, coe_mul, coe_mul,
      ← RingHom.mapMatrix_apply, map_mul, map_mul, RingHom.mapMatrix_apply,
      RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hPres, hPinvres, Matrix.one_mul,
      Matrix.mul_one]
    exact (Matrix.forall_sub_mem_maximalIdeal_iff _ _).1 (hcong g')
  · rw [hτ, coe_mul, coe_mul, det_mul, det_mul, mul_comm, ← mul_assoc, ← det_mul, ← coe_mul,
      mul_inv_cancel, coe_one, det_one, one_mul]
    exact hdet g'
  · rw [hτ]
    have h1 := hPconj ⟨h, hh⟩
    simp only [σN, ρN, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      Units.coeHom_apply] at h1
    rw [← hPu_coe] at h1
    refine Units.ext ?_
    rw [coe_mul, coe_mul, Matrix.mul_assoc, h1, ← Matrix.mul_assoc, ← coe_mul,
      inv_mul_cancel, coe_one, Matrix.one_mul]
    rfl

end Matrix.GeneralLinearGroup
