module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DimensionZeroSplitting
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ClosedImmersionClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DisjointUnionCohomology
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DisjointUnionIso
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.FurtherProperties.DimensionZero
import StacksCore.Tactic.StacksAttribute

/-!
# Weil cohomology of a smooth projective scheme of dimension zero

Let `W` be data (D0)–(D3) of Section 45.9 (Tag 0FHA) over the actual category of smooth
projective schemes over a field `k`, satisfying (A), (B) and (C), and let `X` be a smooth
projective scheme of dimension zero over `k`. This file carries out the proof of Stacks 0FHQ.

`X = Spec(A)` for the finite étale `k`-algebra `A = Γ(X, 𝒪_X)`. Choose a finite Galois `L/k` in
which every minimal polynomial of an element of `A` splits, set `Y = Spec(L)` and
`Σ = Hom_k(A, L)`. Then `X × Y = ∐_{σ ∈ Σ} Y` with coprojections `(Spec(σ), id)`
(`Stacks.WeilCohomology.SmoothProjectiveScheme.isColimitSplitCofan`), so axiom (B)(a) and Stacks
0FHJ for this finite disjoint union give the bijection

`H^*(X) ⊗_F H^*(Y) → ∏_{σ ∈ Σ} H^*(Y)`, `a ⊗ b ↦ (Spec(σ)^*a ∪ b)_σ`

(`Stacks.WeilCohomology.WeilData.splitMap_bijective`). From it, as in the source:

* `H^*(X)` is finite dimensional: the inverse images of the coordinate units are finite sums of
  pure tensors whose first factors span `H^*(X)`
  (`Stacks.WeilCohomology.DimensionZero.finiteDimensional_of_bijective`); the same argument for
  `X = Y` shows that `H^*(Y)` is finite dimensional;
* `H^*(X)` sits in degree `0`, comparing the greatest and least nonzero degrees of `H^*(Y)`
  (`Stacks.WeilCohomology.DimensionZero.grade_eq_bot_of_injective`);
* `dim_F H^0(X) = |Σ| = [A : k] = deg(X → Spec k)`;
* `H^0(X)` is separable and `∫_X` is its trace map, by the base lemmas
  `Stacks.WeilCohomology.isSeparable_cohomology_zero` and
  `Stacks.WeilCohomology.integration_eq_trace` applied to the degree-zero part of the bijection,
  together with `(∫_X a) · 1 = ∑_σ Spec(σ)^* a` in `H^0(Y)`
  (`Stacks.WeilCohomology.WeilData.sum_splitPull_eq_algebraMap_traceZero`), which is axiom (B)(b)
  combined with Stacks 0FHP for `X × Y = ∐_σ Y` (`Stacks.WeilCohomology.WeilData.trace_cofan`)
  and read off by Poincaré duality on `Y`;
* `γ([X]) = 1` by Stacks 0FHF, and `∫_X γ([X]) = Tr(1) = deg(X → Spec k)`.

The finite-index forms of Stacks 0FHJ and 0FHP are derived here by induction from the binary
ones (`Stacks.WeilCohomology.WeilData.restrictCofan_bijective`,
`Stacks.WeilCohomology.WeilData.trace_cofan`).

## Main results

Stacks 0FHQ, for `W` satisfying (A), (B), (C), `[CharZero F]`, and `X` with
`topologicalKrullDim X = 0`:

* (1) `Stacks.WeilCohomology.WeilData.grade_eq_bot_of_dimension_zero`: `H^i(X) = 0`, `i ≠ 0`;
* (2) `Stacks.WeilCohomology.WeilData.finiteDimensional_H0_of_dimension_zero` and
  `Stacks.WeilCohomology.WeilData.isSeparable_H0_of_dimension_zero`: `H^0(X)` is a finite
  separable `F`-algebra;
* (3) `Stacks.WeilCohomology.WeilData.finrank_grade_zero_eq_degree`:
  `dim_F H^0(X) = deg(X → Spec k)`;
* (4) `Stacks.WeilCohomology.WeilData.traceZero_eq_trace`: `∫_X` is the trace map;
* (5) `γ([X]) = 1` is `Stacks.WeilCohomology.WeilData.cycleClass_fundamentalClass` (Stacks
  0FHF), registered for 0FHQ by `add_to_stacks`;
* (6) `Stacks.WeilCohomology.WeilData.trace_cycleClass_fundamentalClass_of_dimension_zero`:
  `∫_X γ([X]) = deg(X → Spec k)`.

## References

* [Stacks Project, Tag 0FHQ](https://stacks.math.columbia.edu/tag/0FHQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w

namespace Stacks.WeilCohomology

namespace DimensionZero

/-! ### Linear algebra of the splitting `H^*(X) ⊗ H^*(Y) = ∏_σ H^*(Y)` -/

section Algebra

variable {F : Type u} [Field F] {M : Type v} [Ring M] [Algebra F M]
  {R : Type w} [Ring R] [Algebra F R] {ι : Type*} [Fintype ι]

/-- The tensor product of two nonzero vectors over a field is nonzero. -/
theorem tmul_ne_zero {V : Type v} [AddCommGroup V] [Module F V] {U : Type w} [AddCommGroup U]
    [Module F U] {a : V} {b : U} (ha : a ≠ 0) (hb : b ≠ 0) : a ⊗ₜ[F] b ≠ 0 := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one F ha
  obtain ⟨g, hg⟩ := Module.Projective.exists_dual_eq_one F hb
  intro h
  have := congrArg (TensorProduct.lift ((LinearMap.mul F F).compl₁₂ f g)) h
  simp [hf, hg] at this

/-- For `x ∈ V ⊗ U` there is a finitely generated `W ≤ V` containing the contractions
`(id ⊗ g)(x)` of `x` against every linear form `g` on `U`. -/
theorem exists_fg_contract {V : Type v} [AddCommGroup V] [Module F V] {U : Type w}
    [AddCommGroup U] [Module F U] (x : V ⊗[F] U) :
    ∃ P : Submodule F V, P.FG ∧ ∀ g : U →ₗ[F] F,
      TensorProduct.rid F V (LinearMap.lTensor V g x) ∈ P := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    refine ⟨Submodule.span F {a}, Submodule.fg_span_singleton a, fun g ↦ ?_⟩
    simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  | add x y hx hy =>
    obtain ⟨P, hP, hPx⟩ := hx
    obtain ⟨Q, hQ, hQy⟩ := hy
    exact ⟨P ⊔ Q, hP.sup hQ, fun g ↦ by
      rw [map_add, map_add]
      exact Submodule.add_mem_sup (hPx g) (hQy g)⟩

variable (ψ : ι → M →ₐ[F] R) (Φ : M ⊗[F] R →ₗ[F] (ι → R))
  (hΦ : ∀ a b, Φ (a ⊗ₜ b) = fun i ↦ ψ i a * b)

omit [Fintype ι] in
include hΦ in
/-- `Φ` is right `R`-linear: `Φ(x · (1 ⊗ r)) = Φ(x) · r`. -/
theorem apply_lTensor_mulRight (r : R) (x : M ⊗[F] R) :
    Φ (LinearMap.lTensor M (LinearMap.mulRight F r) x) = fun i ↦ Φ x i * r := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => ext i; simp [hΦ, mul_assoc]
  | add x y hx hy => ext i; simp [map_add, hx, hy, add_mul]

omit [Fintype ι] in
include hΦ in
/-- **Finiteness from a splitting.** If `M ⊗_F R → ∏_{i ∈ ι} R`, `a ⊗ b ↦ (ψ_i(a) b)_i`, is
bijective for algebra maps `ψ_i : M → R`, `ι` finite and `R ≠ 0`, then `M` is finite dimensional:
the inverse images of the coordinate units are finite sums of pure tensors whose first factors
span `M`. -/
theorem finiteDimensional_of_bijective [Finite ι] [Nontrivial R] (hbij : Function.Bijective Φ) :
    FiniteDimensional F M := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨l₀, hl₀⟩ := Module.Projective.exists_dual_eq_one F (one_ne_zero : (1 : R) ≠ 0)
  let e := LinearEquiv.ofBijective Φ hbij
  let t : ι → M ⊗[F] R := fun i ↦ e.symm (Pi.single i 1)
  choose P hP hPt using fun i ↦ exists_fg_contract (t i)
  have hdecomp (a : M) : a ⊗ₜ[F] (1 : R) =
      ∑ i, LinearMap.lTensor M (LinearMap.mulRight F (ψ i a)) (t i) := by
    apply hbij.1
    rw [map_sum, hΦ]
    ext j
    simp only [Finset.sum_apply, apply_lTensor_mulRight ψ Φ hΦ, t]
    change ψ j a * 1 = ∑ i, (e (e.symm (Pi.single i 1))) j * ψ i a
    simp only [LinearEquiv.apply_symm_apply, Pi.single_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, mul_one]
  have htop : (⨆ i, P i) = ⊤ := by
    refine eq_top_iff.mpr fun a _ ↦ ?_
    have h := congrArg (fun x ↦ TensorProduct.rid F M (LinearMap.lTensor M l₀ x)) (hdecomp a)
    simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, hl₀, one_smul, map_sum] at h
    rw [h]
    refine Submodule.sum_mem _ fun i _ ↦ Submodule.mem_iSup_of_mem i ?_
    rw [← LinearMap.comp_apply (LinearMap.lTensor M l₀), ← LinearMap.lTensor_comp]
    exact hPt i _
  have : Module.Finite F (⨆ i, P i : Submodule F M) :=
    Module.Finite.iff_fg.mpr (Submodule.fg_iSup _ hP)
  rw [htop] at this
  exact Module.Finite.of_surjective (⊤ : Submodule F M).subtype (fun a ↦ ⟨⟨a, trivial⟩, rfl⟩)

include hΦ in
/-- **Dimension from a splitting**: `dim_F M = |ι|` when `R` is finite dimensional and nonzero. -/
theorem finrank_eq_card_of_bijective [Nontrivial R] [FiniteDimensional F R]
    (hbij : Function.Bijective Φ) : Module.finrank F M = Fintype.card ι := by
  have := finiteDimensional_of_bijective ψ Φ hΦ hbij
  have h := (LinearEquiv.ofBijective Φ hbij).finrank_eq
  rw [Module.finrank_tensorProduct, Module.finrank_pi_fintype, Finset.sum_const,
    Finset.card_univ, smul_eq_mul] at h
  exact Nat.eq_of_mul_eq_mul_right Module.finrank_pos h

end Algebra

/-! ### Graded algebras -/

section Graded

variable {F : Type u} [Field F] {A : Type v} [Ring A] [Algebra F A] (𝒜 : ℤ → Submodule F A)
  [_root_.GradedAlgebra 𝒜]

/-- In a finite dimensional graded algebra only finitely many graded pieces are nonzero. -/
theorem finite_ne_bot [FiniteDimensional F A] : {i | 𝒜 i ≠ ⊥}.Finite :=
  Submodule.finite_ne_bot_of_iSupIndep (DirectSum.Decomposition.isInternal 𝒜).submodule_iSupIndep

/-- In a nonzero graded algebra the degree zero piece is nonzero, as it contains `1`. -/
theorem grade_zero_ne_bot [Nontrivial A] : 𝒜 0 ≠ ⊥ := fun h ↦ by
  have h1 : (1 : A) ∈ 𝒜 0 := SetLike.GradedOne.one_mem
  rw [h] at h1
  exact one_ne_zero ((Submodule.mem_bot F).mp h1)

/-- A nonzero finite dimensional graded algebra has a greatest nonzero degree. -/
theorem exists_top_degree [FiniteDimensional F A] [Nontrivial A] :
    ∃ t : ℤ, 𝒜 t ≠ ⊥ ∧ ∀ i, t < i → 𝒜 i = ⊥ := by
  obtain ⟨t, ht, hmax⟩ := (finite_ne_bot 𝒜).exists_maximal ⟨0, grade_zero_ne_bot 𝒜⟩
  exact ⟨t, ht, fun i hi ↦ not_not.mp fun h ↦ not_le.mpr hi (hmax h hi.le)⟩

/-- A nonzero finite dimensional graded algebra has a least nonzero degree. -/
theorem exists_bot_degree [FiniteDimensional F A] [Nontrivial A] :
    ∃ s : ℤ, 𝒜 s ≠ ⊥ ∧ ∀ i, i < s → 𝒜 i = ⊥ := by
  obtain ⟨s, hs, hmin⟩ := (finite_ne_bot 𝒜).exists_minimal ⟨0, grade_zero_ne_bot 𝒜⟩
  exact ⟨s, hs, fun i hi ↦ not_not.mp fun h ↦ not_le.mpr hi (hmin h hi.le)⟩

variable {B : Type w} [Ring B] [Algebra F B] (ℬ : ℤ → Submodule F B) [_root_.GradedAlgebra ℬ]
  {ι : Type*} [Fintype ι] (ψ : ι → A →ₐ[F] B) (hψ : ∀ i n (a : A), a ∈ 𝒜 n → ψ i a ∈ ℬ n)
  (Φ : A ⊗[F] B →ₗ[F] (ι → B)) (hΦ : ∀ a b, Φ (a ⊗ₜ b) = fun i ↦ ψ i a * b)

omit [_root_.GradedAlgebra 𝒜] [Fintype ι] in
include hψ hΦ in
/-- **Concentration in degree zero.** If `A ⊗_F B → ∏_{i ∈ ι} B`, `a ⊗ b ↦ (ψ_i(a) b)_i`, is
injective for graded algebra maps `ψ_i` and `B` is nonzero and finite dimensional, then `A`
vanishes outside degree `0`: comparing the greatest and the least nonzero degrees of `B`. -/
theorem grade_eq_bot_of_injective [FiniteDimensional F B] [Nontrivial B]
    (hinj : Function.Injective Φ) {n : ℤ} (hn : n ≠ 0) : 𝒜 n = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun a ha ↦ ?_
  by_contra ha0
  have key : ∀ m b, b ∈ ℬ m → ℬ (n + m) = ⊥ → b = 0 := by
    intro m b hb hbot
    by_contra hb0
    apply tmul_ne_zero (F := F) ha0 hb0
    apply hinj
    rw [hΦ, map_zero]
    ext i
    exact (Submodule.mem_bot F).mp (hbot ▸ SetLike.GradedMul.mul_mem (hψ i n a ha) hb)
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · obtain ⟨s, hs, hbelow⟩ := exists_bot_degree ℬ
    obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hs
    exact hb0 (key s b hb (hbelow _ (by omega)))
  · obtain ⟨t, ht, habove⟩ := exists_top_degree ℬ
    obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ht
    exact hb0 (key t b hb (habove _ (by omega)))

end Graded

end DimensionZero

/-! ### Finite coproducts -/

namespace WeilData

section FiniteCoproduct

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] (W : WeilData k F)

/-- The one-element cofan `Y ⟶ Y` of the constant family on `Fin 1`. -/
def cofanFinOne (Y : (SmoothProjectiveScheme k).FullSubcategory) : Cofan fun _ : Fin 1 ↦ Y :=
  Cofan.mk Y fun _ ↦ 𝟙 Y

/-- The one-element cofan is a colimit. -/
def isColimitCofanFinOne (Y : (SmoothProjectiveScheme k).FullSubcategory) : IsColimit
    (cofanFinOne Y) :=
  Cofan.IsColimit.mk _ (fun t ↦ t.inj 0)
    (fun t i ↦ by
      obtain rfl : i = 0 := Subsingleton.elim i 0
      exact Category.id_comp (t.inj 0))
    (fun t m hm ↦ (Category.id_comp m).symm.trans (hm 0))

/-- A colimit cofan of the constant family on `Fin (n + 1)`, built from binary coproducts. -/
def finCofan (Y : (SmoothProjectiveScheme k).FullSubcategory) : ∀ n : ℕ, ColimitCocone
    (Discrete.functor
    fun _ : Fin (n + 1) ↦ Y)
  | 0 => ⟨cofanFinOne Y, isColimitCofanFinOne Y⟩
  | n + 1 =>
    ⟨extendCofan (finCofan Y n).cocone (colimit.cocone (pair Y (finCofan Y n).cocone.pt)),
      extendCofanIsColimit (fun _ : Fin (n + 2) ↦ Y) (finCofan Y n).isColimit
        (colimit.isColimit _)⟩

/-- The restriction map `H^*(∐_i Y) → ∏_i H^*(Y)`, `a ↦ (ι_i^* a)_i`, of a cofan. -/
def restrictCofan {ι : Type*} {Y : (SmoothProjectiveScheme k).FullSubcategory}
    (c : Cofan fun _ : ι ↦ Y) :
    W.H c.pt → (ι → W.H Y) :=
  fun a i ↦ W.pull (c.inj i) a

/-- Pullback along an isomorphism is bijective. -/
theorem pull_bijective_of_iso {X Y : (SmoothProjectiveScheme k).FullSubcategory} (φ : X ≅ Y) :
    Function.Bijective (W.pull φ.hom) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨W.pull φ.inv, fun a ↦ ?_, fun a ↦ ?_⟩
  · rw [← AlgHom.comp_apply, ← W.pull_comp, φ.inv_hom_id, W.pull_id, AlgHom.id_apply]
  · rw [← AlgHom.comp_apply, ← W.pull_comp, φ.hom_inv_id, W.pull_id, AlgHom.id_apply]

variable {W}

/-- A colimit cofan over a nonempty finite type is identified with `finCofan Y n` along an
enumeration `Fin (n + 1) ≃ ι`. -/
private theorem exists_iso_finCofan {ι : Type*} [Finite ι] [Nonempty ι]
    {Y : (SmoothProjectiveScheme k).FullSubcategory} (c : Cofan fun _ : ι ↦ Y) (hc : IsColimit c) :
    ∃ (n : ℕ) (e : Fin (n + 1) ≃ ι) (φ : (finCofan Y n).cocone.pt ≅ c.pt),
      ∀ j, Cofan.inj (finCofan Y n).cocone j ≫ φ.hom = c.inj (e j) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card ι = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  let e : Fin (n + 1) ≃ ι := (Fintype.equivFinOfCardEq hn).symm
  let c' : Cofan fun _ : Fin (n + 1) ↦ Y := Cofan.mk c.pt fun j ↦ c.inj (e j)
  have hc' : IsColimit c' := (IsColimit.whiskerEquivalenceEquiv (Discrete.equivalence e)) hc
  exact ⟨n, e, (finCofan Y n).isColimit.coconePointUniqueUpToIso hc',
    fun j ↦ (finCofan Y n).isColimit.comp_coconePointUniqueUpToIso_hom hc' ⟨j⟩⟩

section Binary

variable [CharZero F] (hA : W.PoincareDuality) (hB : W.Kunneth)
  (hC : W.CycleClassAxiom hA.perfectPairing)

include hA hB hC in
/-- For the cofan `∐_{i : Fin (n + 1)} Y` built from binary coproducts, the restriction map
`H^*(∐_i Y) → ∏_i H^*(Y)` is bijective. -/
theorem restrictCofan_finCofan_bijective (Y : (SmoothProjectiveScheme k).FullSubcategory) :
    ∀ n : ℕ, Function.Bijective (W.restrictCofan (c := (finCofan Y n).cocone))
  | 0 => by
    have : W.restrictCofan (c := (finCofan Y 0).cocone) = fun a _ ↦ a := by
      funext a i
      exact congrFun (congrArg DFunLike.coe (W.pull_id Y)) a
    rw [this]
    exact (Equiv.funUnique (Fin 1) (W.H Y)).symm.bijective
  | n + 1 => by
    let c₁ : Cofan fun _ : Fin (n + 1) ↦ Y := (finCofan Y n).cocone
    let c₂ := colimit.cocone (pair Y c₁.pt)
    have h : W.restrictCofan (c := (finCofan Y (n + 1)).cocone) =
        (Fin.consEquiv fun _ : Fin (n + 2) ↦ W.H Y) ∘
          (Prod.map id (W.restrictCofan c₁)) ∘
            (fun a ↦ (W.pull (BinaryCofan.inl c₂) a, W.pull (BinaryCofan.inr c₂) a)) := by
      funext a i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · rfl
      · change W.pull (c₁.inj j ≫ BinaryCofan.inr c₂) a = _
        rw [W.pull_comp]
        rfl
    rw [h]
    exact (Fin.consEquiv _).bijective.comp
      ((Function.Bijective.prodMap Function.bijective_id
        (restrictCofan_finCofan_bijective Y n)).comp
          (W.pullbackPair_bijective_of_isColimit hA hB hC (colimit.isColimit _)))

include hA hB hC in
/-- **Stacks 0FHJ for a finite disjoint union of copies of one scheme**:
`H^*(∐_{i ∈ ι} Y) → ∏_{i ∈ ι} H^*(Y)` is bijective, by induction from the binary case. -/
theorem restrictCofan_bijective {ι : Type*} [Finite ι] [Nonempty ι]
    {Y : (SmoothProjectiveScheme k).FullSubcategory} (c : Cofan fun _ : ι ↦ Y) (hc : IsColimit c) :
    Function.Bijective (W.restrictCofan c) := by
  obtain ⟨n, e, φ, hφ⟩ := exists_iso_finCofan c hc
  let d : Cofan fun _ : Fin (n + 1) ↦ Y := (finCofan Y n).cocone
  have h : (fun g : ι → W.H Y ↦ g ∘ e) ∘ W.restrictCofan c =
      W.restrictCofan d ∘ W.pull φ.hom := by
    funext a j
    change W.pull (c.inj (e j)) a = W.pull (d.inj j) (W.pull φ.hom a)
    rw [← hφ, W.pull_comp]
    rfl
  have hcomp : Function.Bijective ((fun g : ι → W.H Y ↦ g ∘ e) ∘ W.restrictCofan c) := by
    rw [h]
    exact (restrictCofan_finCofan_bijective hA hB hC Y n).comp (W.pull_bijective_of_iso φ)
  exact (Function.Bijective.of_comp_iff' (Equiv.arrowCongr e (Equiv.refl (W.H Y))).symm.bijective
    _).mp hcomp

end Binary

/-- Pullback along an identity is the identity, on twisted cohomology. -/
theorem pullTw_id (X : (SmoothProjectiveScheme k).FullSubcategory) (n m : ℤ) (a : W.Tw X n m) :
    W.pullTw (𝟙 X) n m a = a := by
  apply (W.twCoord X n m).injective
  rw [twCoord_pullTw]
  apply Subtype.ext
  rw [coe_pullDeg, W.pull_id, AlgHom.id_apply]

/-- The points of the chosen cofans are nonempty and equidimensional of dimension `d`. -/
theorem isNonemptyEquidimensional_finCofan {Y : (SmoothProjectiveScheme k).FullSubcategory} {d : ℕ}
    (hY : IsNonemptyEquidimensional Y d) :
    ∀ n : ℕ, IsNonemptyEquidimensional (finCofan Y n).cocone.pt d
  | 0 => hY
  | n + 1 => isNonemptyEquidimensional_pt (colimit.isColimit _) hY
      (isNonemptyEquidimensional_finCofan hY n)

section Trace

variable (hA : W.PoincareDuality) (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)

include hA hB hC

/-- The trace on `∐_{i : Fin (n + 1)} Y` is the sum of the traces of the restrictions to the
summands: `∫_{∐_i Y} a = ∑_i ∫_Y ι_i^* a`. -/
theorem trace_finCofan {Y : (SmoothProjectiveScheme k).FullSubcategory} {d : ℕ}
    (hY : IsNonemptyEquidimensional Y d) :
    ∀ (n : ℕ) (hZ : IsNonemptyEquidimensional (finCofan Y n).cocone.pt d)
      (a : W.Tw (finCofan Y n).cocone.pt (2 * d) d),
      W.trace _ d hZ a = ∑ i : Fin (n + 1), W.trace Y d hY
        (W.pullTw (Cofan.inj (p := (finCofan Y n).cocone) i) _ _ a)
  | 0, hZ, a => by
    rw [Fin.sum_univ_one]
    exact congrArg (W.trace Y d hY) (W.pullTw_id Y _ _ a).symm
  | n + 1, hZ, a => by
    let c₁ : Cofan fun _ : Fin (n + 1) ↦ Y := (finCofan Y n).cocone
    let c₂ := colimit.cocone (pair Y c₁.pt)
    have h₁ := isNonemptyEquidimensional_finCofan hY n
    refine (W.trace_eq_add hA hB hC (isColimitMkOfIsColimit (colimit.isColimit (pair Y c₁.pt)))
      hY h₁ hZ a).trans ?_
    rw [Fin.sum_univ_succ]
    congr 1
    refine (trace_finCofan hY n h₁ _).trans (Finset.sum_congr rfl fun j _ ↦ ?_)
    exact congrArg (W.trace Y d hY) (W.pullTw_comp (c₁.inj j) (BinaryCofan.inr c₂) _ _ a).symm

/-- **Stacks 0FHP for a finite disjoint union of copies of one scheme**:
`∫_{∐_i Y} a = ∑_i ∫_Y ι_i^* a`, by induction from the binary case. -/
theorem trace_cofan {ι : Type*} [Fintype ι] [Nonempty ι]
    {Y : (SmoothProjectiveScheme k).FullSubcategory}
    (c : Cofan fun _ : ι ↦ Y) (hc : IsColimit c) {d : ℕ} (hY : IsNonemptyEquidimensional Y d)
    (hZ : IsNonemptyEquidimensional c.pt d) (a : W.Tw c.pt (2 * d) d) :
    W.trace c.pt d hZ a = ∑ i, W.trace Y d hY (W.pullTw (c.inj i) _ _ a) := by
  obtain ⟨n, e, φ, hφ⟩ := exists_iso_finCofan c hc
  let d' : Cofan fun _ : Fin (n + 1) ↦ Y := (finCofan Y n).cocone
  have : IsIso φ.hom.hom.left :=
    (inferInstance : IsIso ((ObjectProperty.ι _ ⋙ Over.forget _).map φ.hom))
  have h₁ := isNonemptyEquidimensional_finCofan hY n
  refine (W.trace_pullTw_of_isIso hA hB hC φ.hom h₁ hZ a).symm.trans ?_
  rw [trace_finCofan hA hB hC hY n h₁, ← e.sum_comp]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← W.pullTw_comp]
  change W.trace Y d hY (W.pullTw (d'.inj j ≫ φ.hom) _ _ a) = _
  rw [hφ]

end Trace

end FiniteCoproduct

end WeilData

/-! ### Zero-dimensional smooth projective schemes -/

namespace SmoothProjectiveScheme

open _root_.AlgebraicGeometry

variable {k : Type u} [Field k]

/-- A nonempty smooth projective scheme equidimensional of dimension `0` has dimension `0`: it is
homeomorphic to its fibre over the unique point of `Spec k`. -/
theorem topologicalKrullDim_eq_zero_of_isNonemptyEquidimensional
    {X : (SmoothProjectiveScheme k).FullSubcategory}
    (hX : IsNonemptyEquidimensional X 0) : topologicalKrullDim X.obj.left = 0 := by
  obtain ⟨x⟩ := hX.nonempty
  have hfib := (hX.relativeDimension (X.obj.hom x) ⟨X.obj.hom.asFiber x⟩).2
  have hpre : X.obj.hom ⁻¹' {X.obj.hom x} = Set.univ :=
    Set.eq_univ_of_forall fun y ↦ (show Subsingleton (PrimeSpectrum k) from inferInstance).elim _ _
  refine Eq.trans ?_ hfib
  exact (((X.obj.hom.fiberHomeo _).trans ((Homeomorph.setCongr hpre).trans
    (Homeomorph.Set.univ _))).isHomeomorph.topologicalKrullDim_eq).symm

/-- A smooth projective scheme has dimension zero exactly when it is nonempty and equidimensional
of dimension `0`. -/
theorem isNonemptyEquidimensional_zero_iff {X : (SmoothProjectiveScheme k).FullSubcategory} :
    IsNonemptyEquidimensional X 0 ↔ topologicalKrullDim X.obj.left = 0 :=
  ⟨topologicalKrullDim_eq_zero_of_isNonemptyEquidimensional,
    isNonemptyEquidimensional_of_dimension_zero⟩

/-- The spectrum of a nonzero finite `k`-algebra has dimension zero. -/
theorem topologicalKrullDim_spec_eq_zero (A : Type u) [CommRing A] [Algebra k A]
    [Module.Finite k A] [Nontrivial A] : topologicalKrullDim (Spec (.of A)) = 0 := by
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  have : Nonempty (PrimeSpectrum A) := PrimeSpectrum.nonempty_iff_nontrivial.mpr inferInstance
  exact topologicalKrullDim_eq_zero_of_discreteTopology_nonempty (X := PrimeSpectrum A)

section Split

variable {X : (SmoothProjectiveScheme k).FullSubcategory} (hX : topologicalKrullDim X.obj.left = 0)
  (L : Type u) [Field L] [Algebra k L] [FiniteDimensional k L] [Algebra.IsSeparable k L]

/-- `Spec(L)` is nonempty and equidimensional of dimension `0`. -/
theorem isNonemptyEquidimensional_spec_field : IsNonemptyEquidimensional (spec k L) 0 :=
  isNonemptyEquidimensional_of_dimension_zero (topologicalKrullDim_spec_eq_zero (k := k) L)

include hX

/-- `X ×_k Spec(L) ≅ Spec(Γ(X, 𝒪_X) ⊗_k L)` as schemes. -/
def prodLeftIsoSpecTensor :
    (prod X (spec k L)).obj.left ≅ Spec (.of (globalSections X ⊗[k] L)) :=
  haveI := isIso_prodMapSpec hX L
  prodLeftIso X (spec k L) ≪≫ asIso (prodMapSpec hX L) ≪≫ pullbackSpecIso k (globalSections X) L

/-- `Γ(X, 𝒪_X)` is nonzero for `X` of dimension zero. -/
theorem nontrivial_globalSections : Nontrivial (globalSections X) := by
  have := nonempty_of_dimension_zero hX
  obtain ⟨x⟩ := (inferInstance : Nonempty X.obj.left)
  exact PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨(isoSpecLeftOfDimensionZero hX).hom x⟩

/-- **`X ×_k Spec(L)` is nonempty and equidimensional of dimension `0`.** -/
theorem isNonemptyEquidimensional_prod_spec : IsNonemptyEquidimensional (prod X (spec k L)) 0 := by
  have := finite_globalSections hX
  have := nontrivial_globalSections hX
  have : Nontrivial (globalSections X ⊗[k] L) := Module.nontrivial_of_finrank_pos (R := k) (by
    rw [Module.finrank_tensorProduct]
    exact Nat.mul_pos Module.finrank_pos Module.finrank_pos)
  refine isNonemptyEquidimensional_of_dimension_zero ?_
  rw [(Scheme.homeoOfIso (prodLeftIsoSpecTensor hX L)).isHomeomorph.topologicalKrullDim_eq]
  exact topologicalKrullDim_spec_eq_zero (k := k) _

omit [FiniteDimensional k L] [Algebra.IsSeparable k L] in
/-- `Hom_k(Γ(X, 𝒪_X), L)` is nonempty when every minimal polynomial splits in `L`. -/
theorem nonempty_algHom
    (hsplit : ∀ a : globalSections X, ((minpoly k a).map (algebraMap k L)).Splits) :
    Nonempty (globalSections X →ₐ[k] L) := by
  have := finite_globalSections hX
  have := etale_globalSections hX
  have := nontrivial_globalSections hX
  refine (Nat.card_pos_iff.mp ?_).1
  rw [Stacks.FiniteEtaleSplitting.natCard_algHom k _ L hsplit]
  exact Module.finrank_pos

end Split

end SmoothProjectiveScheme

/-! ### The cohomology of a zero-dimensional scheme -/

namespace WeilData

open _root_.AlgebraicGeometry SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] {W : WeilData k F}

section Split

variable {X : (SmoothProjectiveScheme k).FullSubcategory} (hX : topologicalKrullDim X.obj.left = 0)
  (L : Type u) [Field L] [Algebra k L] [FiniteDimensional k L] [Algebra.IsSeparable k L]

variable (W) in
/-- The pullback `Spec(σ)^* : H^*(X) → H^*(Spec L)` along `Spec(σ) : Spec(L) ⟶ X`. -/
def splitPull (σ : globalSections X →ₐ[k] L) : W.H X →ₐ[F] W.H (spec k L) :=
  haveI := finite_globalSections hX
  haveI := etale_globalSections hX
  W.pull (specMap σ ≫ (isoSpecOfDimensionZero hX).inv)

variable (W) in
/-- **The splitting map** `H^*(X) ⊗_F H^*(Y) → ∏_{σ} H^*(Y)`, `Y = Spec(L)`: the Künneth map
of axiom (B)(a) followed by the restrictions to the summands of `X × Y = ∐_σ Y`. -/
def splitMap :
    W.H X ⊗[F] W.H (spec k L) →ₗ[F] ((globalSections X →ₐ[k] L) → W.H (spec k L)) :=
  (LinearMap.pi fun σ ↦ (W.pull (splitInj hX L σ)).toLinearMap) ∘ₗ W.kunnethMap X (spec k L)

/-- The splitting map sends `a ⊗ b` to `(Spec(σ)^* a ∪ b)_σ`. -/
theorem splitMap_tmul (a : W.H X) (b : W.H (spec k L)) :
    W.splitMap hX L (a ⊗ₜ b) = fun σ ↦ W.splitPull hX L σ a * b := by
  funext σ
  change W.pull (splitInj hX L σ) (W.pull (fst X _) a * W.pull (snd X _) b) = _
  rw [map_mul, ← AlgHom.comp_apply (W.pull (splitInj hX L σ)), ← W.pull_comp, splitInj_fst,
    ← AlgHom.comp_apply (W.pull (splitInj hX L σ)), ← W.pull_comp, splitInj_snd, W.pull_id]
  rfl

/-- The pullback `Spec(σ)^*` preserves the grading. -/
theorem splitPull_mem_grade (σ : globalSections X →ₐ[k] L) (n : ℤ) (a : W.H X)
    (ha : a ∈ W.grade X n) : W.splitPull hX L σ a ∈ W.grade (spec k L) n :=
  W.pull_grade _ n a ha

/-- **The splitting map is bijective**: axiom (B)(a), and Stacks 0FHJ for the finite disjoint
union `X × Y = ∐_σ Y`. -/
theorem splitMap_bijective [CharZero F] (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing)
    (hsplit : ∀ a : globalSections X, ((minpoly k a).map (algebraMap k L)).Splits) :
    Function.Bijective (W.splitMap hX L) := by
  have := nonempty_algHom hX L hsplit
  have := finite_globalSections hX
  exact (restrictCofan_bijective hA hB hC (splitCofan hX L)
    (isColimitSplitCofan hX L hsplit)).comp (hB.kunnethIsomorphism X _)

/-! ### Traces of degree-zero classes -/

section TraceZero

variable (W)

/-- `∫_Z` read on a degree-zero class `c ∈ H^0(Z)`, through `H^0(Z)(0) = H^0(Z) ⊗ F(0)`. -/
def traceZero (Z : (SmoothProjectiveScheme k).FullSubcategory) (hZ : IsNonemptyEquidimensional Z 0)
    (c : W.H Z)
    (hc : c ∈ W.grade Z 0) : F :=
  W.trace Z 0 hZ ((W.twCoord Z _ _).symm ⟨c, hc⟩)

variable {W}

/-- The degree-zero trace is additive: `∫_Z (c + c') = ∫_Z c + ∫_Z c'`. -/
theorem traceZero_add (Z : (SmoothProjectiveScheme k).FullSubcategory)
    (hZ : IsNonemptyEquidimensional Z 0)
    (c c' : W.H Z) (hc : c ∈ W.grade Z 0) (hc' : c' ∈ W.grade Z 0) :
    W.traceZero Z hZ (c + c') (Submodule.add_mem _ hc hc') =
      W.traceZero Z hZ c hc + W.traceZero Z hZ c' hc' := by
  unfold traceZero
  change W.trace Z 0 hZ ((W.twCoord Z _ _).symm (⟨c, hc⟩ + ⟨c', hc'⟩)) = _
  rw [map_add, map_add]

/-- The degree-zero trace is `F`-homogeneous. -/
theorem traceZero_smul (Z : (SmoothProjectiveScheme k).FullSubcategory)
    (hZ : IsNonemptyEquidimensional Z 0)
    (r : F) (c : W.H Z) (hc : c ∈ W.grade Z 0) :
    W.traceZero Z hZ (r • c) (Submodule.smul_mem _ r hc) = r * W.traceZero Z hZ c hc := by
  unfold traceZero
  change W.trace Z 0 hZ ((W.twCoord Z _ _).symm (r • ⟨c, hc⟩)) = _
  rw [map_smul, map_smul, smul_eq_mul]

/-- The degree-zero trace commutes with finite sums. -/
theorem traceZero_sum (Z : (SmoothProjectiveScheme k).FullSubcategory)
    (hZ : IsNonemptyEquidimensional Z 0)
    {ι : Type*} (s : Finset ι) (c : ι → W.H Z) (hc : ∀ i, c i ∈ W.grade Z 0) :
    W.traceZero Z hZ (∑ i ∈ s, c i) (Submodule.sum_mem _ fun i _ ↦ hc i) =
      ∑ i ∈ s, W.traceZero Z hZ (c i) (hc i) := by
  unfold traceZero
  rw [← map_sum, ← map_sum]
  congr 2
  exact Subtype.ext (by simp)

/-- Twisted pullback of a degree-zero class. -/
theorem pullTw_twCoord_symm {Z Z' : (SmoothProjectiveScheme k).FullSubcategory} (f : Z ⟶ Z')
    (c : W.H Z')
    (hc : c ∈ W.grade Z' (2 * ((0 : ℕ) : ℤ))) :
    W.pullTw f _ ((0 : ℕ) : ℤ) ((W.twCoord Z' _ _).symm ⟨c, hc⟩) =
      (W.twCoord Z _ _).symm ⟨W.pull f c, W.pull_grade f _ c hc⟩ := by
  apply (W.twCoord Z _ _).injective
  rw [twCoord_pullTw, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rfl

/-- Twisted cup product of degree-zero classes. -/
theorem cupTw_twCoord_symm (Z : (SmoothProjectiveScheme k).FullSubcategory) (i j n : ℤ)
    (h : i + j = n)
    (s t m : ℤ) (h' : s + t = m) (c c' : W.H Z) (hc : c ∈ W.grade Z i) (hc' : c' ∈ W.grade Z j) :
    W.cupTw Z i j n h s t m h' ((W.twCoord Z i s).symm ⟨c, hc⟩)
        ((W.twCoord Z j t).symm ⟨c', hc'⟩) =
      (W.twCoord Z n m).symm ⟨c * c', h ▸ SetLike.GradedMul.mul_mem hc hc'⟩ := by
  apply (W.twCoord Z n m).injective
  rw [twCoord_cupTw, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]
  rfl

/-- **Axiom (B)(b) on degree-zero classes**: `∫_{X×Y}(pr₁^*a ∪ pr₂^*b) = ∫_X a · ∫_Y b`. -/
theorem traceZero_kunneth (hB : W.KunnethTrace) {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (hX : IsNonemptyEquidimensional X 0) (hY : IsNonemptyEquidimensional Y 0)
    (hXY : IsNonemptyEquidimensional (prod X Y) 0) (a : W.H X) (b : W.H Y)
    (ha : a ∈ W.grade X 0) (hb : b ∈ W.grade Y 0) :
    W.traceZero (prod X Y) hXY (W.pull (fst X Y) a * W.pull (snd X Y) b)
        (SetLike.GradedMul.mul_mem (W.pull_grade _ 0 a ha) (W.pull_grade _ 0 b hb)) =
      W.traceZero X hX a ha * W.traceZero Y hY b hb := by
  have h := (hB X Y 0 0 hX hY hXY).1 ((W.twCoord X _ _).symm ⟨a, ha⟩)
    ((W.twCoord Y _ _).symm ⟨b, hb⟩)
  rw [pullTw_twCoord_symm, pullTw_twCoord_symm, cupTw_twCoord_symm] at h
  exact h

/-- The product of two degree-zero classes has degree zero. -/
theorem mul_mem_grade_zero {Z : (SmoothProjectiveScheme k).FullSubcategory} {y u : W.H Z}
    (hy : y ∈ W.grade Z 0)
    (hu : u ∈ W.grade Z 0) : y * u ∈ W.grade Z 0 := by
  simpa using SetLike.GradedMul.mul_mem hy hu

/-- The degree-zero trace of a class does not depend on the proof that it has degree zero. -/
theorem traceZero_congr (Z : (SmoothProjectiveScheme k).FullSubcategory)
    (hZ : IsNonemptyEquidimensional Z 0)
    {c c' : W.H Z} (h : c = c') (hc : c ∈ W.grade Z 0) (hc' : c' ∈ W.grade Z 0) :
    W.traceZero Z hZ c hc = W.traceZero Z hZ c' hc' := by
  subst h
  rfl

/-- **Axiom (A)(b) in degree zero**: a class `u ∈ H^0(Y)` is determined by the traces
`∫_Y y ∪ u`, `y ∈ H^0(Y)`. -/
theorem eq_of_traceZero_mul_eq (hA : W.PerfectPairing)
    {Y : (SmoothProjectiveScheme k).FullSubcategory}
    (hY : IsNonemptyEquidimensional Y 0) {u u' : W.H Y} (hu : u ∈ W.grade Y 0)
    (hu' : u' ∈ W.grade Y 0)
    (h : ∀ (y : W.H Y) (hy : y ∈ W.grade Y 0),
      W.traceZero Y hY (y * u) (mul_mem_grade_zero hy hu) =
        W.traceZero Y hY (y * u') (mul_mem_grade_zero hy hu')) :
    u = u' := by
  have key := eq_of_pairingTw_eq hA hY 0 (2 * ((0 : ℕ) : ℤ)) (by simp) 0 ((0 : ℕ) : ℤ) (by simp)
    (a := (W.twCoord Y _ _).symm ⟨u, hu⟩) (a' := (W.twCoord Y _ _).symm ⟨u', hu'⟩) (fun b ↦ by
      obtain ⟨⟨y, hy⟩, rfl⟩ := (W.twCoord Y 0 0).symm.surjective b
      rw [pairingTw_apply, pairingTw_apply, cupTw_twCoord_symm, cupTw_twCoord_symm]
      exact h y hy)
  simpa using congrArg (fun x ↦ ((W.twCoord Y _ _ x : W.grade Y _) : W.H Y)) key

end TraceZero

end Split

section Consequences

variable {L : Type u} [Field L] [Algebra k L] [FiniteDimensional k L] [Algebra.IsSeparable k L]
  [CharZero F] (hA : W.PoincareDuality) (hB : W.Kunneth)
  (hC : W.CycleClassAxiom hA.perfectPairing)

include hA hB hC

/-- `H^*(Spec L)` is nonzero (Stacks 0FHF). -/
theorem nontrivial_spec : Nontrivial (W.H (spec k L)) :=
  have : Nonempty (spec k L).obj.left :=
    nonempty_of_dimension_zero (topologicalKrullDim_spec_eq_zero (k := k) L)
  nontrivial_of_nonempty hA hB hC (spec k L)

/-- **`H^*(X)` is finite dimensional** for `X` of dimension zero split by `L`. -/
theorem finiteDimensional_of_split {X : (SmoothProjectiveScheme k).FullSubcategory}
    (hX : topologicalKrullDim X.obj.left = 0)
    (hsplit : ∀ a : globalSections X, ((minpoly k a).map (algebraMap k L)).Splits) :
    FiniteDimensional F (W.H X) := by
  classical
  have := finite_globalSections hX
  have := nontrivial_spec hA hB hC (L := L)
  exact DimensionZero.finiteDimensional_of_bijective (W.splitPull hX L) (W.splitMap hX L)
    (W.splitMap_tmul hX L) (W.splitMap_bijective hX L hA hB hC hsplit)

omit [CharZero F] hA hB hC in
/-- Every minimal polynomial over `k` of an element of `Γ(Spec L, 𝒪) = L` splits in `L`, for
`L/k` normal. -/
theorem splits_globalSections_spec [Normal k L] (a : globalSections (spec k L)) :
    ((minpoly k a).map (algebraMap k L)).Splits := by
  let e : globalSections (spec k L) ≃ₐ[k] L :=
    { (Scheme.ΓSpecIso (.of L)).commRingCatIsoToRingEquiv with
      commutes' := fun c ↦ by
        change (Scheme.ΓSpecIso (.of L)).hom.hom
          (((Scheme.ΓSpecIso (.of k)).inv ≫ (specStructure k L).appTop).hom c) = algebraMap k L c
        rw [← CommRingCat.comp_apply, Category.assoc, Scheme.ΓSpecIso_naturality,
          Iso.inv_hom_id_assoc]
        rfl }
  rw [← minpoly.algEquiv_eq e a]
  exact Normal.splits inferInstance (e a)

/-- **`H^*(Spec L)` is finite dimensional** for `L/k` finite Galois. -/
theorem finiteDimensional_spec [IsGalois k L] : FiniteDimensional F (W.H (spec k L)) :=
  finiteDimensional_of_split hA hB hC (topologicalKrullDim_spec_eq_zero (k := k) L)
    (splits_globalSections_spec)

/-- **Stacks 0FHQ (1), in the presence of a splitting field**: `H^n(X) = 0` for `n ≠ 0`. -/
theorem grade_eq_bot_of_split [IsGalois k L] {X : (SmoothProjectiveScheme k).FullSubcategory}
    (hX : topologicalKrullDim X.obj.left = 0)
    (hsplit : ∀ a : globalSections X, ((minpoly k a).map (algebraMap k L)).Splits)
    {n : ℤ} (hn : n ≠ 0) : W.grade X n = ⊥ :=
  have := finiteDimensional_spec hA hB hC (L := L)
  have := nontrivial_spec hA hB hC (L := L)
  have := finite_globalSections hX
  DimensionZero.grade_eq_bot_of_injective (W.grade X) (W.grade (spec k L)) (W.splitPull hX L)
    (W.splitPull_mem_grade hX L) (W.splitMap hX L) (W.splitMap_tmul hX L)
    (W.splitMap_bijective hX L hA hB hC hsplit).1 hn

/-- **`dim_F H^*(X) = [Γ(X, 𝒪_X) : k]`** in the presence of a splitting field. -/
theorem finrank_eq_of_split [IsGalois k L] {X : (SmoothProjectiveScheme k).FullSubcategory}
    (hX : topologicalKrullDim X.obj.left = 0)
    (hsplit : ∀ a : globalSections X, ((minpoly k a).map (algebraMap k L)).Splits) :
    Module.finrank F (W.H X) = Module.finrank k (globalSections X) := by
  classical
  have := finiteDimensional_spec hA hB hC (L := L)
  have := nontrivial_spec hA hB hC (L := L)
  have := finite_globalSections hX
  have := etale_globalSections hX
  have : Fintype (globalSections X →ₐ[k] L) := Fintype.ofFinite _
  rw [DimensionZero.finrank_eq_card_of_bijective (W.splitPull hX L) (W.splitMap hX L)
    (W.splitMap_tmul hX L) (W.splitMap_bijective hX L hA hB hC hsplit), ← Nat.card_eq_fintype_card,
    Stacks.FiniteEtaleSplitting.natCard_algHom k _ L hsplit]

end Consequences

/-! ### The degree of a zero-dimensional scheme -/

omit [Field F] in
/-- **`deg(X → Spec k) = [Γ(X, 𝒪_X) : k]`**: the degree (rank, Stacks 02KA) of the finite flat
structure morphism of a smooth projective `k`-scheme of dimension zero is the dimension over `k`
of its ring of global sections. -/
theorem finrank_hom_eq_finrank_globalSections {X : (SmoothProjectiveScheme k).FullSubcategory}
    (hX : topologicalKrullDim X.obj.left = 0) (s : Spec (.of k)) :
    X.obj.hom.finrank s = Module.finrank k (globalSections X) := by
  have := finite_globalSections hX
  have := isFinite_specStructure k (globalSections X)
  have : Flat (specStructure k (globalSections X)) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  rw [← isoSpecLeftOfDimensionZero_hom_specStructure hX, Scheme.Hom.finrank_comp_left_of_isIso]
  have := Scheme.Hom.finrank_SpecMap_algebraMap k (globalSections X) s
  rw [Module.rankAtStalk_eq_finrank_of_free] at this
  exact this

/-- If `H^*(X)` vanishes outside degree `0` then `H^0(X)` is all of `H^*(X)`. -/
theorem H0_eq_top_of_grade_eq_bot {X : (SmoothProjectiveScheme k).FullSubcategory}
    (h : ∀ n : ℤ, n ≠ 0 → W.grade X n = ⊥) : W.H0 X = ⊤ := by
  classical
  refine eq_top_iff.mpr fun a _ ↦ ?_
  change a ∈ W.grade X 0
  rw [← DirectSum.sum_support_decompose (W.grade X) a]
  refine Submodule.sum_mem _ fun n _ ↦ ?_
  by_cases hn : n = 0
  · subst hn
    exact (DirectSum.decompose (W.grade X) a 0).2
  · have hmem : ((DirectSum.decompose (W.grade X) a n : W.grade X n) : W.H X) ∈ W.grade X n :=
      (DirectSum.decompose (W.grade X) a n).2
    have h0 : ((DirectSum.decompose (W.grade X) a n : W.grade X n) : W.H X) = 0 := by
      have := h n hn
      exact (Submodule.mem_bot F).mp (this ▸ hmem)
    rw [h0]
    exact Submodule.zero_mem _

/-- A finite étale `Γ(X, 𝒪_X)` is split by a finite Galois extension `L/k`. -/
private theorem exists_isGalois_splits_globalSections
    {X : (SmoothProjectiveScheme k).FullSubcategory} (hX : topologicalKrullDim X.obj.left = 0) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : FiniteDimensional k L)
      (_ : IsGalois k L), ∀ a : globalSections X, ((minpoly k a).map (algebraMap k L)).Splits :=
  haveI := finite_globalSections hX
  haveI := etale_globalSections hX
  Stacks.FiniteEtaleSplitting.exists_isGalois_splits k (globalSections X)

section General

variable [CharZero F] (hA : W.PoincareDuality) (hB : W.Kunneth)
  (hC : W.CycleClassAxiom hA.perfectPairing)
  {X : (SmoothProjectiveScheme k).FullSubcategory} (hX : topologicalKrullDim X.obj.left = 0)

include hA hB hC hX

/-- **Stacks 0FHQ (1)**: for data (D0)–(D3) satisfying (A), (B), (C) and `X` a smooth projective
scheme of dimension zero over `k`, `H^i(X) = 0` for `i ≠ 0`. -/
@[stacks 0FHQ "part (1): H^i(X) = 0 for i ≠ 0, over the actual category of smooth projective \
  schemes and the actual Weil data (D0)-(D3) satisfying (A), (B), (C)"]
theorem grade_eq_bot_of_dimension_zero {n : ℤ} (hn : n ≠ 0) : W.grade X n = ⊥ := by
  obtain ⟨L, _, _, _, _, hL⟩ := exists_isGalois_splits_globalSections hX
  exact grade_eq_bot_of_split hA hB hC hX hL hn

/-- `H^*(X)` is finite dimensional, `X` of dimension zero. -/
theorem finiteDimensional_of_dimension_zero : FiniteDimensional F (W.H X) := by
  obtain ⟨L, _, _, _, _, hL⟩ := exists_isGalois_splits_globalSections hX
  exact finiteDimensional_of_split hA hB hC hX hL

/-- **Stacks 0FHQ (2), finiteness**: `H^0(X)` is a finite `F`-algebra, `X` of dimension zero. -/
@[stacks 0FHQ "part (2), finiteness: H^0(X) is finite dimensional over F"]
theorem finiteDimensional_H0_of_dimension_zero : FiniteDimensional F (W.H0 X) :=
  have := finiteDimensional_of_dimension_zero hA hB hC hX
  FiniteDimensional.finiteDimensional_subalgebra _

/-- `dim_F H^0(X) = [Γ(X, 𝒪_X) : k]`, `X` of dimension zero. -/
theorem finrank_H0_of_dimension_zero :
    Module.finrank F (W.H0 X) = Module.finrank k (globalSections X) := by
  obtain ⟨L, _, _, _, _, hL⟩ := exists_isGalois_splits_globalSections hX
  rw [H0_eq_top_of_grade_eq_bot fun n hn ↦ grade_eq_bot_of_dimension_zero hA hB hC hX hn,
    Subalgebra.topEquiv.toLinearEquiv.finrank_eq, finrank_eq_of_split hA hB hC hX hL]

/-- **Stacks 0FHQ (3)**: `dim_F H^0(X) = deg(X → Spec k)`, the degree being the rank of the finite
flat structure morphism at the point of `Spec k` (Stacks 02KA, `Scheme.Hom.finrank`). -/
@[stacks 0FHQ "part (3): dim_F H^0(X) = deg(X → Spec k)"]
theorem finrank_grade_zero_eq_degree (s : Spec (.of k)) :
    Module.finrank F (W.grade X 0) = X.obj.hom.finrank s := by
  rw [finrank_hom_eq_finrank_globalSections hX s,
    ← finrank_H0_of_dimension_zero hA hB hC hX]
  rfl

end General

/-! ### `(∫_X a) · 1 = ∑_σ Spec(σ)^* a` -/

section Integral

variable (hA : W.PoincareDuality) (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)
  {X : (SmoothProjectiveScheme k).FullSubcategory} (hX : topologicalKrullDim X.obj.left = 0)
  (L : Type u) [Field L] [Algebra k L] [FiniteDimensional k L] [Algebra.IsSeparable k L]
  (hsplit : ∀ a : globalSections X, ((minpoly k a).map (algebraMap k L)).Splits)

include hA hB hC hX hsplit

/-- **The trace over `X` in degree zero, through the splitting**: for `a ∈ H^0(X)`,
`(∫_X a) · 1 = ∑_σ Spec(σ)^* a` in `H^0(Spec L)`. The source obtains this from Stacks 0FHC and
Stacks 0FHP; here it is read off from axiom (B)(b) and Stacks 0FHP for `X × Spec L = ∐_σ Spec L`
by pairing against `H^0(Spec L)` (axiom (A)(b)). -/
theorem sum_splitPull_eq_algebraMap_traceZero [Fintype (globalSections X →ₐ[k] L)] (a : W.H X)
    (ha : a ∈ W.grade X 0) :
    ∑ σ, W.splitPull hX L σ a =
      algebraMap F (W.H (spec k L)) (W.traceZero X (isNonemptyEquidimensional_of_dimension_zero hX)
        a ha) := by
  classical
  have := finite_globalSections hX
  have := nonempty_algHom hX L hsplit
  have hY := isNonemptyEquidimensional_spec_field (k := k) L
  have hP := isNonemptyEquidimensional_prod_spec hX L
  have hψ (σ : globalSections X →ₐ[k] L) : W.splitPull hX L σ a ∈ W.grade (spec k L) 0 :=
    W.splitPull_mem_grade hX L σ 0 a ha
  have hsum : ∑ σ, W.splitPull hX L σ a ∈ W.grade (spec k L) 0 :=
    Submodule.sum_mem _ fun σ _ ↦ hψ σ
  have hone : algebraMap F (W.H (spec k L)) (W.traceZero X
      (isNonemptyEquidimensional_of_dimension_zero hX) a ha) ∈ W.grade (spec k L) 0 :=
    SetLike.algebraMap_mem_graded _ _
  refine eq_of_traceZero_mul_eq hA.perfectPairing hY hsum hone fun y hy ↦ ?_
  -- the right-hand side: `∫_Y y ∪ (∫_X a) · 1 = (∫_X a)(∫_Y y)`
  have hrhs : W.traceZero (spec k L) hY (y * algebraMap F _ (W.traceZero X
      (isNonemptyEquidimensional_of_dimension_zero hX) a ha)) (mul_mem_grade_zero hy hone) =
      W.traceZero X (isNonemptyEquidimensional_of_dimension_zero hX) a ha *
        W.traceZero (spec k L) hY y hy := by
    rw [← traceZero_smul]
    exact traceZero_congr _ _ (by rw [← Algebra.commutes, ← Algebra.smul_def]) _ _
  rw [hrhs]
  -- the left-hand side, through the splitting `X × Y = ∐_σ Y`
  have hc : W.pull (fst X (spec k L)) a * W.pull (snd X (spec k L)) y ∈
      W.grade (prod X (spec k L)) 0 :=
    mul_mem_grade_zero (W.pull_grade _ 0 a ha) (W.pull_grade _ 0 y hy)
  have hkun := traceZero_kunneth hB.kunnethTrace (isNonemptyEquidimensional_of_dimension_zero hX)
    hY hP a y ha hy
  have hcof := trace_cofan hA hB hC (splitCofan hX L) (isColimitSplitCofan hX L hsplit) hY hP
    ((W.twCoord _ _ _).symm ⟨_, hc⟩)
  have hcof' : W.traceZero (prod X (spec k L)) hP _ hc =
      ∑ σ, W.traceZero (spec k L) hY (W.splitPull hX L σ a * y)
        (mul_mem_grade_zero (hψ σ) hy) := by
    refine hcof.trans (Finset.sum_congr rfl fun σ _ ↦ ?_)
    have h1 := pullTw_twCoord_symm (W := W) (splitInj hX L σ) _ hc
    refine (congrArg (W.trace (spec k L) 0 hY) h1).trans ?_
    exact traceZero_congr _ _ (congrFun (W.splitMap_tmul hX L a y) σ) _ _
  rw [← hkun, hcof', ← traceZero_sum]
  refine traceZero_congr _ _ ?_ _ _
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun σ _ ↦ (W.mul_comm_of_mem_grade_zero _ (hψ σ) y).symm

end Integral

/-! ### The degree-zero splitting as an isomorphism of algebras -/

section H0Split

variable {X : (SmoothProjectiveScheme k).FullSubcategory} (hX : topologicalKrullDim X.obj.left = 0)
  (L : Type u) [Field L] [Algebra k L] [FiniteDimensional k L] [Algebra.IsSeparable k L]

variable (W) in
/-- `Spec(σ)^* : H^0(X) → H^0(Spec L)`. -/
def splitPullH0 (σ : globalSections X →ₐ[k] L) : W.H0 X →ₐ[F] W.H0 (spec k L) :=
  ((W.splitPull hX L σ).comp (W.H0 X).val).codRestrict (W.H0 (spec k L)) fun a ↦
    W.splitPull_mem_grade hX L σ 0 a a.2

/-- `Spec(σ)^* : H^0(X) → H^0(Spec L)` is the restriction of `Spec(σ)^* : H^*(X) → H^*(Spec L)`. -/
@[simp]
theorem coe_splitPullH0 (σ : globalSections X →ₐ[k] L) (a : W.H0 X) :
    (W.splitPullH0 hX L σ a : W.H (spec k L)) = W.splitPull hX L σ a := rfl

variable (W) in
/-- The `H^0(Spec L)`-algebra map `H^0(Spec L) ⊗_F H^0(X) → ∏_σ H^0(Spec L)`,
`b ⊗ a ↦ (b · Spec(σ)^* a)_σ`. -/
def splitH0 : W.H0 (spec k L) ⊗[F] W.H0 X →ₐ[W.H0 (spec k L)]
    ((globalSections X →ₐ[k] L) → W.H0 (spec k L)) :=
  AlgHom.pi fun σ ↦ Algebra.TensorProduct.lift (AlgHom.id _ _) (W.splitPullH0 hX L σ)
    fun _ _ ↦ Commute.all _ _

/-- The degree-zero splitting map sends `b ⊗ a` to `(b · Spec(σ)^* a)_σ`. -/
@[simp]
theorem splitH0_tmul (b : W.H0 (spec k L)) (a : W.H0 X) :
    W.splitH0 hX L (b ⊗ₜ a) = fun σ ↦ b * W.splitPullH0 hX L σ a := by
  ext σ
  simp [splitH0]

/-- **The degree-zero splitting is bijective** once `H^*(X)` and `H^*(Spec L)` are concentrated in
degree zero. -/
theorem splitH0_bijective [CharZero F] (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing)
    (hsplit : ∀ a : globalSections X, ((minpoly k a).map (algebraMap k L)).Splits)
    (hXtop : W.H0 X = ⊤) (hYtop : W.H0 (spec k L) = ⊤) :
    Function.Bijective (W.splitH0 hX L) := by
  have hvX : Function.Bijective (W.H0 X).val :=
    ⟨Subtype.val_injective, fun a ↦ ⟨⟨a, hXtop ▸ Algebra.mem_top⟩, rfl⟩⟩
  have hvY : Function.Bijective (W.H0 (spec k L)).val :=
    ⟨Subtype.val_injective, fun a ↦ ⟨⟨a, hYtop ▸ Algebra.mem_top⟩, rfl⟩⟩
  let T : W.H0 (spec k L) ⊗[F] W.H0 X ≃ₗ[F] W.H X ⊗[F] W.H (spec k L) :=
    TensorProduct.comm F _ _ ≪≫ₗ TensorProduct.congr
      (LinearEquiv.ofBijective (W.H0 X).val.toLinearMap hvX)
      (LinearEquiv.ofBijective (W.H0 (spec k L)).val.toLinearMap hvY)
  let post : ((globalSections X →ₐ[k] L) → W.H0 (spec k L)) →
      ((globalSections X →ₐ[k] L) → W.H (spec k L)) := fun g σ ↦ g σ
  have hpost : Function.Bijective post :=
    ⟨fun g g' h ↦ funext fun σ ↦ hvY.1 (congrFun h σ), fun g ↦
      ⟨fun σ ↦ (hvY.2 (g σ)).choose, funext fun σ ↦ (hvY.2 (g σ)).choose_spec⟩⟩
  have hcomp : post ∘ W.splitH0 hX L = W.splitMap hX L ∘ T := by
    have : ((LinearMap.pi fun σ ↦ (W.H0 (spec k L)).val.toLinearMap.comp
        (LinearMap.proj σ)) ∘ₗ ((W.splitH0 hX L).toLinearMap.restrictScalars F)) =
        W.splitMap hX L ∘ₗ T.toLinearMap := by
      refine TensorProduct.ext' fun b a ↦ ?_
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply,
        splitH0_tmul, LinearEquiv.coe_coe, T, LinearEquiv.trans_apply, TensorProduct.comm_tmul,
        TensorProduct.congr_tmul, splitMap_tmul]
      funext σ
      simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
        AlgHom.toLinearMap_apply, Subalgebra.coe_val, Subalgebra.coe_mul, coe_splitPullH0]
      exact W.mul_comm_of_mem_grade_zero _ b.2 _
    funext x
    exact congrArg (fun f ↦ f x) this
  have h2 : Function.Bijective (post ∘ W.splitH0 hX L) := by
    rw [hcomp]
    exact (W.splitMap_bijective hX L hA hB hC hsplit).comp T.bijective
  exact (Function.Bijective.of_comp_iff' hpost _).mp h2

end H0Split

/-! ### Separability and the trace -/

section H0

variable [CharZero F]

variable (hA : W.PoincareDuality) (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)
  {X : (SmoothProjectiveScheme k).FullSubcategory} (hX : topologicalKrullDim X.obj.left = 0)

include hA hB hC hX

/-- The data of the base lemmas `Stacks.WeilCohomology.isSeparable_cohomology_zero` and
`Stacks.WeilCohomology.integration_eq_trace`, produced from a Galois splitting field. -/
private theorem exists_splitting_data :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : FiniteDimensional k L)
      (_ : IsGalois k L) (_ : Nontrivial (W.H0 (spec k L))) (n : ℕ)
      (ψ : Fin n → W.H0 X →ₐ[F] W.H0 (spec k L))
      (e : W.H0 (spec k L) ⊗[F] W.H0 X ≃ₐ[W.H0 (spec k L)] (Fin n → W.H0 (spec k L))),
      (∀ a, e (1 ⊗ₜ a) = fun i ↦ ψ i a) ∧ Module.finrank F (W.H0 X) = n ∧
      ∀ a : W.H0 X, algebraMap F (W.H0 (spec k L))
        (W.traceZero X (isNonemptyEquidimensional_of_dimension_zero hX) a a.2) = ∑ i, ψ i a := by
  classical
  have := finite_globalSections hX
  have := etale_globalSections hX
  obtain ⟨L, _, _, _, _, hL⟩ := exists_isGalois_splits_globalSections hX
  have hY0 := topologicalKrullDim_spec_eq_zero (k := k) L
  have : Nonempty (spec k L).obj.left := nonempty_of_dimension_zero hY0
  have hntY := nontrivial_of_nonempty hA hB hC (spec k L)
  have : Fintype (globalSections X →ₐ[k] L) := Fintype.ofFinite _
  have hXtop := H0_eq_top_of_grade_eq_bot (W := W) fun n hn ↦
    grade_eq_bot_of_dimension_zero hA hB hC hX hn
  have hYtop := H0_eq_top_of_grade_eq_bot (W := W) fun n hn ↦
    grade_eq_bot_of_dimension_zero hA hB hC (X := spec k L) hY0 hn
  have : Nontrivial (W.H0 (spec k L)) :=
    ⟨⟨0, 1, fun h ↦ zero_ne_one (congrArg Subtype.val h)⟩⟩
  let eqv := Fintype.equivFin (globalSections X →ₐ[k] L)
  let ψ : Fin (Fintype.card (globalSections X →ₐ[k] L)) → W.H0 X →ₐ[F] W.H0 (spec k L) :=
    fun i ↦ W.splitPullH0 hX L (eqv.symm i)
  let e := (AlgEquiv.ofBijective _ (W.splitH0_bijective hX L hA hB hC hL
    hXtop hYtop)).trans (AlgEquiv.piCongrLeft' (W.H0 (spec k L))
      (fun _ ↦ W.H0 (spec k L)) eqv)
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, _, ψ, e,
    fun a ↦ ?_, ?_, fun a ↦ ?_⟩
  · funext i
    simp [e, ψ, AlgEquiv.piCongrLeft'_apply]
  · rw [finrank_H0_of_dimension_zero hA hB hC hX,
      ← Stacks.FiniteEtaleSplitting.natCard_algHom k _ L hL, Nat.card_eq_fintype_card]
  · apply Subtype.ext
    rw [Subalgebra.coe_algebraMap, ← sum_splitPull_eq_algebraMap_traceZero hA hB hC hX L hL a a.2,
      ← (W.H0 (spec k L)).val_apply, map_sum]
    exact (eqv.symm.sum_comp fun σ ↦ (W.splitPull hX L σ a)).symm

/-- **Stacks 0FHQ (2), separability**: `H^0(X)` is a separable `F`-algebra, `X` of dimension
zero. -/
@[stacks 0FHQ "part (2), separability: H^0(X) is a separable F-algebra"]
theorem isSeparable_H0_of_dimension_zero : Algebra.IsSeparable F (W.H0 X) := by
  have := finiteDimensional_H0_of_dimension_zero hA hB hC hX
  obtain ⟨L, _, _, _, _, _, n, ψ, e, he, hrank, -⟩ := exists_splitting_data hA hB hC hX
  exact isSeparable_cohomology_zero F (W.H0 X) (W.H0 (spec k L)) n ψ e he hrank

/-- **Stacks 0FHQ (4)**: `∫_X : H^0(X) → F` is the trace map of the `F`-algebra `H^0(X)`; here
`a ∈ H^0(X)` enters `∫_X` through `H^0(X)(0) = H^0(X) ⊗_F F(0)`. -/
@[stacks 0FHQ "part (4): ∫_X : H^0(X) → F is the trace map"]
theorem traceZero_eq_trace (a : W.H0 X) :
    W.trace X 0 (isNonemptyEquidimensional_of_dimension_zero hX)
        ((W.twCoord X _ _).symm ⟨a.1, a.2⟩) = Algebra.trace F (W.H0 X) a := by
  have := finiteDimensional_H0_of_dimension_zero hA hB hC hX
  obtain ⟨L, _, _, _, _, _, n, ψ, e, he, -, hint⟩ := exists_splitting_data hA hB hC hX
  let integ : W.H0 X →ₗ[F] F :=
    { toFun := fun a ↦ W.traceZero X (isNonemptyEquidimensional_of_dimension_zero hX) a a.2
      map_add' := fun a b ↦ traceZero_add _ _ _ _ a.2 b.2
      map_smul' := fun r a ↦ traceZero_smul _ _ r _ a.2 }
  exact LinearMap.congr_fun
    (integration_eq_trace F (W.H0 X) (W.H0 (spec k L)) n ψ e he integ hint) a

/-- **Stacks 0FHQ (6)**: `∫_X γ([X]) = deg(X → Spec k)`. -/
@[stacks 0FHQ "part (6): ∫_X γ([X]) = deg(X → Spec k)"]
theorem trace_cycleClass_fundamentalClass_of_dimension_zero (s : Spec (.of k)) :
    W.trace X 0 (isNonemptyEquidimensional_of_dimension_zero hX)
        (W.cycleClass X 0 (fundamentalClass X)) = (X.obj.hom.finrank s : F) := by
  have := finiteDimensional_H0_of_dimension_zero hA hB hC hX
  rw [W.cycleClass_fundamentalClass hB.kunnethIsomorphism hC.pullback hC.mul hC.point X]
  have h1 := traceZero_eq_trace hA hB hC hX 1
  have h2 : (Algebra.trace F (W.H0 X) 1 : F) = Module.finrank F (W.H0 X) := by
    rw [← map_one (algebraMap F (W.H0 X)), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one]
  rw [h2, finrank_H0_of_dimension_zero hA hB hC hX,
    ← finrank_hom_eq_finrank_globalSections hX s] at h1
  exact h1

end H0

-- Stacks 0FHQ (5), `γ([X]) = 1`: by Stacks 0FHF it holds for every smooth projective `X`.
add_to_stacks 0FHQ "part (5): γ([X]) = 1, by 0FHF, for every smooth projective X"
  Stacks.WeilCohomology.WeilData.cycleClass_fundamentalClass

end WeilData

end Stacks.WeilCohomology

end
