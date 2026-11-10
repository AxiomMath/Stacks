module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDividedPowerForms
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.PthRootFormsDecomposition

/-!
# A completed connection at the levels `pⁿ`

Let `(R, J, δ)` be a divided power ring over `A`, let `Ω^i_R` be the `p`-adic completions of its
divided power differential forms, and let `∇ : N → N ⊗̂_R Ω¹_R` be a completed connection on an
`R`-module `N`.  Modulo `pⁿ` everything is uncompleted: the level `pⁿ` of the completed tensor
product `N ⊗̂_R Ω^q_R` is `N_n ⊗_R Ω^q_{R/A,δ}` with `N_n = N / pⁿ N`
(`Crystalline.CompletedLevels.levelTensorEquiv`), the connection induces an ordinary connection
`∇_n : N_n → N_n ⊗_R Ω¹_{R/A,δ}` of [Stacks, Tag 07I0]
(`Crystalline.CompletedLevels.levelConnection`), and the
level of the completed de Rham differential of `∇` is the extension of `∇_n` to the de Rham
complex (`Crystalline.CompletedLevels.formsLevelEquiv_levelDifferential`).  If `∇` is integrable in
the sense of
[Stacks, Remark 60.6.1, Tag 07I0] — the composite `N → N ⊗̂ Ω¹ → N ⊗̂ Ω²` vanishes — then so is
every `∇_n` (`Crystalline.CompletedLevels.isIntegrable_levelConnection`).

This is how a statement about uncompleted de Rham complexes, such as
[Stacks, Lemma 60.25.2, Tag 07Q7], is carried to the completed complexes of
[Stacks, Lemma 60.25.3, Tag 07N1]: apply it at every level and assemble.

## Main definitions

* `Crystalline.CompletedLevels.levelTensorEquiv` — `(N ⊗_R X̂) / Iⁿ ≃ (N / Iⁿ N) ⊗_R X` for a
finitely generated
  ideal `I`.
* `Crystalline.CompletedLevels.levelConnection` — the connection `∇_n` on `N_n`.

## References

* [Stacks Project, Tag 07I0](https://stacks.math.columbia.edu/tag/07I0)
* [Stacks Project, Lemma 60.25.3, Tag 07N1](https://stacks.math.columbia.edu/tag/07N1)
-/

@[expose] public noncomputable section

open DividedPowers

open scoped TensorProduct

universe u w

namespace Crystalline

namespace CompletedLevels

/-! ### The levels of a completed tensor product -/

section LevelTensor

variable {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) (N X : Type*) [AddCommGroup N]
  [Module R N] [AddCommGroup X] [Module R X]

/-- An element of `Iⁿ` kills `(N / Iⁿ N) ⊗_R X`. -/
theorem smul_levelTensor_eq_zero {r : R} (hr : r ∈ I ^ n)
    (z : (N ⧸ (I ^ n • ⊤ : Submodule R N)) ⊗[R] X) : r • z = 0 := by
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    rw [TensorProduct.smul_tmul', ← Submodule.Quotient.mk_smul,
      (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.smul_mem_smul hr Submodule.mem_top),
      TensorProduct.zero_tmul]
  | add a b ha hb => rw [smul_add, ha, hb, add_zero]

/-- An element of `Iⁿ` kills a quotient by `Iⁿ`. -/
theorem smul_levelQuotient_eq_zero {Y : Type*} [AddCommGroup Y] [Module R Y] {r : R}
    (hr : r ∈ I ^ n) (z : Y ⧸ (I ^ n • ⊤ : Submodule R Y)) : r • z = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [← Submodule.Quotient.mk_smul,
    (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.smul_mem_smul hr Submodule.mem_top)]

/-- A linear map into a module killed by `Iⁿ` kills `Iⁿ` times its source. -/
theorem map_eq_zero_of_mem_pow_smul_top {Y Z : Type*} [AddCommGroup Y] [Module R Y]
    [AddCommGroup Z] [Module R Z] (f : Y →ₗ[R] Z) (hZ : ∀ r ∈ I ^ n, ∀ z : Z, r • z = 0)
    {y : Y} (hy : y ∈ (I ^ n • ⊤ : Submodule R Y)) : f y = 0 := by
  refine Submodule.smul_induction_on hy (fun r hr y _ ↦ ?_) (fun a b ha hb ↦ ?_)
  · rw [map_smul, hZ r hr]
  · rw [map_add, ha, hb, add_zero]

/-- The pairing `(N / Iⁿ N) × (X / Iⁿ X) → (N / Iⁿ N) ⊗_R X`, `(a, x mod Iⁿ) ↦ a ⊗ x`. -/
def levelTensorPairing :
    (N ⧸ (I ^ n • ⊤ : Submodule R N)) →ₗ[R] (X ⧸ (I ^ n • ⊤ : Submodule R X)) →ₗ[R]
      (N ⧸ (I ^ n • ⊤ : Submodule R N)) ⊗[R] X :=
  (Submodule.liftQ (I ^ n • ⊤ : Submodule R X)
    (TensorProduct.mk R (N ⧸ (I ^ n • ⊤ : Submodule R N)) X).flip (fun x hx ↦ by
      rw [LinearMap.mem_ker]
      exact map_eq_zero_of_mem_pow_smul_top I n _
        (fun r hr g ↦ LinearMap.ext fun a ↦ smul_levelTensor_eq_zero I n N X hr (g a)) hx)).flip

/-- The level pairing on the class of an element. -/
@[simp] theorem levelTensorPairing_mk (a : N ⧸ (I ^ n • ⊤ : Submodule R N)) (x : X) :
    levelTensorPairing I n N X a (Submodule.Quotient.mk x) = a ⊗ₜ x := rfl

/-- The forward map `(N ⊗_R X̂) → (N / Iⁿ N) ⊗_R X`, `m ⊗ x̂ ↦ m ⊗ (x̂ mod Iⁿ)`. -/
def levelTensorFwdAux :
    N ⊗[R] AdicCompletion I X →ₗ[R] (N ⧸ (I ^ n • ⊤ : Submodule R N)) ⊗[R] X :=
  TensorProduct.lift (((levelTensorPairing I n N X).compl₂ (AdicCompletion.eval I X n)).comp
    (I ^ n • ⊤ : Submodule R N).mkQ)

/-- The backward map `(N / Iⁿ N) ⊗_R X → (N ⊗_R X̂) / Iⁿ`, `(m mod Iⁿ) ⊗ x ↦ m ⊗ x`. -/
def levelTensorBwd :
    (N ⧸ (I ^ n • ⊤ : Submodule R N)) ⊗[R] X →ₗ[R]
      (N ⊗[R] AdicCompletion I X) ⧸ (I ^ n • ⊤ : Submodule R (N ⊗[R] AdicCompletion I X)) :=
  TensorProduct.lift (Submodule.liftQ (I ^ n • ⊤ : Submodule R N)
    (((TensorProduct.mk R N (AdicCompletion I X)).compl₂ (AdicCompletion.of I X)).compr₂
      (I ^ n • ⊤ : Submodule R (N ⊗[R] AdicCompletion I X)).mkQ) (fun m hm ↦ by
      rw [LinearMap.mem_ker]
      exact map_eq_zero_of_mem_pow_smul_top I n _
        (fun r hr g ↦ LinearMap.ext fun x ↦ smul_levelQuotient_eq_zero I n hr (g x)) hm))

/-- The backward level map on a pure tensor. -/
@[simp] theorem levelTensorBwd_tmul (m : N) (x : X) :
    levelTensorBwd I n N X (Submodule.Quotient.mk m ⊗ₜ x) =
      Submodule.Quotient.mk (m ⊗ₜ AdicCompletion.of I X x) := rfl

/-- **The level `Iⁿ` of `N ⊗_R X̂` is `(N / Iⁿ N) ⊗_R X`**, for a finitely generated ideal `I`:
modulo `Iⁿ` the completion of the second factor is invisible, and a tensor product modulo `Iⁿ`
only sees its first factor modulo `Iⁿ`. -/
def levelTensorEquiv (hI : I.FG) :
    ((N ⊗[R] AdicCompletion I X) ⧸ (I ^ n • ⊤ : Submodule R (N ⊗[R] AdicCompletion I X))) ≃ₗ[R]
      (N ⧸ (I ^ n • ⊤ : Submodule R N)) ⊗[R] X :=
  LinearEquiv.ofLinearMap
    (Submodule.liftQ _ (levelTensorFwdAux I n N X) (fun y hy ↦ by
      rw [LinearMap.mem_ker]
      exact map_eq_zero_of_mem_pow_smul_top I n _
        (fun r hr z ↦ smul_levelTensor_eq_zero I n N X hr z) hy))
    (levelTensorBwd I n N X)
    (by
      refine TensorProduct.ext' fun a x ↦ ?_
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ a
      simp only [LinearMap.comp_apply, levelTensorBwd_tmul, Submodule.liftQ_apply,
        levelTensorFwdAux, TensorProduct.lift.tmul,
        LinearMap.compl₂_apply, Submodule.mkQ_apply, AdicCompletion.eval_of,
        levelTensorPairing_mk, LinearMap.id_apply])
    (by
      refine Submodule.linearMap_qext _ (TensorProduct.ext' fun m xh ↦ ?_)
      obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval I X n xh)
      simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.liftQ_apply,
        levelTensorFwdAux, TensorProduct.lift.tmul, LinearMap.compl₂_apply, ← hx,
        levelTensorPairing_mk, levelTensorBwd_tmul, LinearMap.id_apply]
      rw [Submodule.Quotient.eq, ← TensorProduct.tmul_sub]
      have hmem : AdicCompletion.of I X x - xh ∈ (I ^ n • ⊤ : Submodule R (AdicCompletion I
          X)) := by
        rw [AdicCompletion.pow_smul_top_eq_ker_eval hI, LinearMap.mem_ker, map_sub,
          AdicCompletion.eval_of, Submodule.mkQ_apply, hx, sub_self]
      refine Submodule.smul_induction_on hmem (fun r hr y _ ↦ ?_) (fun a b ha hb ↦ ?_)
      · rw [TensorProduct.tmul_smul]
        exact Submodule.smul_mem_smul hr Submodule.mem_top
      · rw [TensorProduct.tmul_add]
        exact Submodule.add_mem _ ha hb)

/-- The level identification on the class of `m ⊗ x`. -/
@[simp] theorem levelTensorEquiv_mk_tmul_of (hI : I.FG) (m : N) (x : X) :
    levelTensorEquiv I n N X hI (Submodule.Quotient.mk (m ⊗ₜ AdicCompletion.of I X x)) =
      Submodule.Quotient.mk m ⊗ₜ x := by
  change levelTensorPairing I n N X (Submodule.Quotient.mk m)
    (AdicCompletion.eval I X n (AdicCompletion.of I X x)) = _
  rw [AdicCompletion.eval_of]
  rfl

/-- The inverse of the level identification on a pure tensor. -/
@[simp] theorem levelTensorEquiv_symm_mk_tmul (hI : I.FG) (m : N) (x : X) :
    (levelTensorEquiv I n N X hI).symm (Submodule.Quotient.mk m ⊗ₜ x) =
      Submodule.Quotient.mk (m ⊗ₜ AdicCompletion.of I X x) := rfl

/-- The value of the level identification on `m ⊗ x̂`, through any representative of `x̂` modulo
`Iⁿ`. -/
theorem levelTensorEquiv_mk_tmul (hI : I.FG) (m : N) (xh : AdicCompletion I X) (x : X)
    (hx : xh.val n = Submodule.Quotient.mk x) :
    levelTensorEquiv I n N X hI (Submodule.Quotient.mk (m ⊗ₜ xh)) =
      Submodule.Quotient.mk m ⊗ₜ x := by
  change levelTensorPairing I n N X (Submodule.Quotient.mk m) (AdicCompletion.eval I X n xh) = _
  rw [AdicCompletion.eval_apply, hx]
  rfl

/-- The transition map of an adic completion fixes the class of an element. -/
theorem transitionMap_mk_eq {Y : Type*} [AddCommGroup Y] [Module R Y] {m k : ℕ} (hmk : m ≤ k)
    (y : Y) :
    AdicCompletion.transitionMap I Y hmk (Submodule.Quotient.mk y) = Submodule.Quotient.mk y := by
  simp [AdicCompletion.transitionMap]

/-- **Two additive maps out of the level `Iⁿ` of `N ⊗_R X̂` agreeing on the classes of
`m ⊗ x` with `x ∈ X` are equal.** -/
theorem levelTensor_addMonoidHom_ext (hI : I.FG) {Z : Type*} [AddCommGroup Z]
    {F G : ((N ⊗[R] AdicCompletion I X) ⧸
      (I ^ n • ⊤ : Submodule R (N ⊗[R] AdicCompletion I X))) →+ Z}
    (h : ∀ (m : N) (x : X), F (Submodule.Quotient.mk (m ⊗ₜ AdicCompletion.of I X x)) =
      G (Submodule.Quotient.mk (m ⊗ₜ AdicCompletion.of I X x))) : F = G := by
  refine AddMonoidHom.ext fun y ↦ ?_
  rw [← (levelTensorEquiv I n N X hI).symm_apply_apply y]
  generalize levelTensorEquiv I n N X hI y = z
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    rw [levelTensorEquiv_symm_mk_tmul]
    exact h m x
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

/-- **The level identification is compatible with the transition maps.** -/
theorem levelTensorEquiv_transitionMap (hI : I.FG) {m k : ℕ} (hmk : m ≤ k)
    (y : (N ⊗[R] AdicCompletion I X) ⧸ (I ^ k • ⊤ : Submodule R (N ⊗[R] AdicCompletion I X))) :
    levelTensorEquiv I m N X hI (AdicCompletion.transitionMap I _ hmk y) =
      TensorProduct.map (AdicCompletion.transitionMap I N hmk) LinearMap.id
        (levelTensorEquiv I k N X hI y) := by
  have := levelTensor_addMonoidHom_ext I k N X hI
    (F := ((levelTensorEquiv I m N X hI).toLinearMap.comp
      (AdicCompletion.transitionMap I _ hmk)).toAddMonoidHom)
    (G := ((TensorProduct.map (AdicCompletion.transitionMap I N hmk) LinearMap.id).comp
      (levelTensorEquiv I k N X hI).toLinearMap).toAddMonoidHom) (fun a x ↦ by
      simp only [LinearMap.toAddMonoidHom_coe, LinearMap.coe_comp, LinearEquiv.coe_coe,
        Function.comp_apply, transitionMap_mk_eq, levelTensorEquiv_mk_tmul_of,
        TensorProduct.map_tmul, LinearMap.id_apply])
  exact DFunLike.congr_fun this y

/-- **The level identification is natural in the completed factor**: a linear map of
completions which at the level `Iⁿ` is induced by `g₀ : X → Y` corresponds to `1 ⊗ g₀`. -/
theorem levelTensorEquiv_lTensor (hI : I.FG) {Y : Type*} [AddCommGroup Y] [Module R Y]
    (g : AdicCompletion I X →ₗ[R] AdicCompletion I Y) (g0 : X →ₗ[R] Y)
    (hg : ∀ (xh : AdicCompletion I X) (x : X), xh.val n = Submodule.Quotient.mk x →
      (g xh).val n = Submodule.Quotient.mk (g0 x))
    (z : (N ⊗[R] AdicCompletion I X) ⧸ (I ^ n • ⊤ : Submodule R (N ⊗[R] AdicCompletion I X))) :
    levelTensorEquiv I n N Y hI ((LinearMap.lTensor N g).reduceModIdeal (I ^ n) z) =
      LinearMap.lTensor _ g0 (levelTensorEquiv I n N X hI z) := by
  have := levelTensor_addMonoidHom_ext I n N X hI
    (F := (levelTensorEquiv I n N Y hI).toLinearMap.toAddMonoidHom.comp
      ((LinearMap.lTensor N g).reduceModIdeal (I ^ n)).toAddMonoidHom)
    (G := ((LinearMap.lTensor _ g0).comp (levelTensorEquiv I n N X hI).toLinearMap).toAddMonoidHom)
    (fun m x ↦ by
      change levelTensorEquiv I n N Y hI
          (Submodule.Quotient.mk (m ⊗ₜ g (AdicCompletion.of I X x))) =
        LinearMap.lTensor _ g0 (levelTensorEquiv I n N X hI
          (Submodule.Quotient.mk (m ⊗ₜ AdicCompletion.of I X x)))
      rw [levelTensorEquiv_mk_tmul_of, LinearMap.lTensor_tmul]
      exact levelTensorEquiv_mk_tmul I n N Y hI m _ (g0 x)
        (hg _ x (by rw [← AdicCompletion.eval_apply, AdicCompletion.eval_of]; rfl)))
  exact DFunLike.congr_fun this z

end LevelTensor

/-- `1 ⊗ g` and `f ⊗ 1` commute. -/
theorem lTensor_map_id_comm {R : Type*} [CommRing R] {M M' X Y : Type*} [AddCommGroup M]
    [Module R M] [AddCommGroup M'] [Module R M'] [AddCommGroup X] [Module R X] [AddCommGroup Y]
    [Module R Y] (f : M →ₗ[R] M') (g : X →ₗ[R] Y) (t : M ⊗[R] X) :
    LinearMap.lTensor M' g (TensorProduct.map f LinearMap.id t) =
      TensorProduct.map f LinearMap.id (LinearMap.lTensor M g t) := by
  exact (LinearMap.congr_fun (LinearMap.lTensor_comp_rTensor _ f g) t).trans
    (LinearMap.congr_fun (LinearMap.rTensor_comp_lTensor _ f g) t).symm

/-! ### The level connection -/

section LevelConnection

open Stacks.DeRham.DifferentialDescent PthRootExtension

variable (p : ℕ) (A : Type u) [CommRing A] (R : Type u) [CommRing R] [Algebra A R]
  {J : Ideal R} (δ : DividedPowers J) (N : Type w) [AddCommGroup N] [Module R N]

/-- The level `N / pⁿ N` of an `R`-module. -/
abbrev levelModule (n : ℕ) : Type w :=
  N ⧸ (pAdicIdeal (A := R) p ^ n • ⊤ : Submodule R N)

/-- The ideal `(p)` is finitely generated. -/
theorem pAdicIdeal_fg_ring : (pAdicIdeal (A := R) p).FG :=
  Submodule.fg_span_singleton _

/-- **The level `pⁿ` of `N ⊗̂_R Ω^q_R` is `N_n ⊗_R Ω^q_{R/A,δ}`.** -/
abbrev formsLevelEquiv (q n : ℕ) :
    ((N ⊗[R] completedDividedPowerForms p A δ q) ⧸
        (pAdicIdeal (A := R) p ^ n • ⊤ : Submodule R
          (N ⊗[R] completedDividedPowerForms p A δ q))) ≃ₗ[R]
      levelModule p R N n ⊗[R] (⋀[R]^q (dividedPowerDifferentials (A := A) δ)) :=
  levelTensorEquiv (pAdicIdeal (A := R) p) n N
    (dividedPowerDifferentialForms (A := A) δ q) (pAdicIdeal_fg_ring p R)

variable (nabla : CompletedConnection p R
  (completedDividedPowerForms p A δ 1)
  (completedDividedPowerDifferentialOnRing p A δ) N)

/-- The level `pⁿ` of the values of a completed connection, read in `N_n ⊗_R Ω¹_{R/A,δ}`. -/
def levelOneForms (n : ℕ) :
    CompletedTensor p R (completedDividedPowerForms p A δ 1) N →ₗ[R]
      levelModule p R N n ⊗[R] dividedPowerDifferentials (A := A) δ :=
  (LinearMap.lTensor (levelModule p R N n)
      (exteriorPower.oneEquiv R (dividedPowerDifferentials (A := A) δ)).toLinearMap).comp
    ((formsLevelEquiv p A R δ N 1 n).toLinearMap.comp
      (AdicCompletion.eval (pAdicIdeal (A := R) p) _ n))

/-- The level of the values of a completed connection, as a formula. -/
theorem levelOneForms_apply (n : ℕ) (z : CompletedTensor p R
    (completedDividedPowerForms p A δ 1) N) :
    levelOneForms p A R δ N n z =
      LinearMap.lTensor (levelModule p R N n)
        (exteriorPower.oneEquiv R (dividedPowerDifferentials (A := A) δ)).toLinearMap
        (formsLevelEquiv p A R δ N 1 n (z.val n)) := rfl

/-- The level of `m ⊗ d b` is `m ⊗ d b`. -/
theorem levelOneForms_differential (n : ℕ) (m : N) (b : R) :
    levelOneForms p A R δ N n (toCompletedTensor p R
        (completedDividedPowerForms p A δ 1) N
        (m ⊗ₜ[R] completedDividedPowerDifferentialOnRing p A δ b)) =
      Submodule.Quotient.mk m ⊗ₜ[R]
        (dividedPowerDifferentialRelations (A := A) δ).mkQ (KaehlerDifferential.D A R b) := by
  rw [completedDividedPowerDifferentialOnRing_eq]
  change LinearMap.lTensor (levelModule p R N n)
      (exteriorPower.oneEquiv R (dividedPowerDifferentials (A := A) δ)).toLinearMap
      (formsLevelEquiv p A R δ N 1 n (Submodule.Quotient.mk (m ⊗ₜ[R]
        AdicCompletion.of (pAdicIdeal (A := R) p) _
          (dividedPowerOneForm A δ b)))) = _
  rw [levelTensorEquiv_mk_tmul_of, LinearMap.lTensor_tmul, LinearEquiv.coe_coe,
    dividedPowerOneForm_apply, LinearEquiv.apply_symm_apply]
  rfl

/-- The level connection on a representative. -/
def levelConnectionAux (n : ℕ) : N →+ levelModule p R N n ⊗[R] dividedPowerDifferentials (A := A)
    δ :=
  (levelOneForms p A R δ N n).toAddMonoidHom.comp
    (CompletedDeRham.nablaHom p R (completedDividedPowerForms p A δ) N
      nabla)

/-- The level connection as an additive map out of `N_n`. -/
def levelConnectionHom (n : ℕ) :
    levelModule p R N n →+ levelModule p R N n ⊗[R] dividedPowerDifferentials (A := A) δ :=
  QuotientAddGroup.lift _ (levelConnectionAux p A R δ N nabla n) (fun y hy ↦ by
    rw [AddMonoidHom.mem_ker]
    change levelOneForms p A R δ N n (nabla y) = 0
    rw [levelOneForms_apply,
      show (nabla y).val n = 0 from CompletedDeRham.val_eq_zero_of_mem p R
        (CompletedDeRham.nablaHom p R (completedDividedPowerForms p A δ)
          N nabla) n hy, map_zero, map_zero])

/-- The level connection on the class of an element. -/
theorem levelConnectionHom_mk (n : ℕ) (m : N) :
    levelConnectionHom p A R δ N nabla n (Submodule.Quotient.mk m) =
      levelOneForms p A R δ N n (nabla m) := rfl

/-- The Leibniz rule for the level connection. -/
theorem levelConnectionHom_leibniz (n : ℕ) (b : R) (x : levelModule p R N n) :
    levelConnectionHom p A R δ N nabla n (b • x) =
      b • levelConnectionHom p A R δ N nabla n x +
        x ⊗ₜ[R] (dividedPowerDifferentialRelations (A := A) δ).mkQ (KaehlerDifferential.D A R
            b) := by
  induction x using Submodule.Quotient.induction_on with
  | H m =>
    rw [← Submodule.Quotient.mk_smul, levelConnectionHom_mk, levelConnectionHom_mk,
      nabla.leibniz, map_add, map_smul, levelOneForms_differential]

/-- **The connection `∇_n` on `N_n = N / pⁿ N`** induced by a completed connection: the class of
`m` goes to the class of `∇ m` modulo `pⁿ`, read in `N_n ⊗_R Ω¹_{R/A,δ}`.  It is a connection in
the sense of [Stacks, Tag 07I0]. -/
def levelConnection (n : ℕ) :
    Connection A R ((dividedPowerDifferentialRelations (A := A) δ).mkQ) (levelModule p R N n) where
  toAddMonoidHom := levelConnectionHom p A R δ N nabla n
  leibniz' := levelConnectionHom_leibniz p A R δ N nabla n

/-- The level connection on the class of an element. -/
theorem levelConnection_mk (n : ℕ) (m : N) :
    levelConnection p A R δ N nabla n (Submodule.Quotient.mk m) =
      levelOneForms p A R δ N n (nabla m) := rfl

/-! ### The level of the completed de Rham differential -/

/-- **The descended de Rham differential of an extended connection on the divided power
one-forms is the divided power de Rham differential.** -/
theorem extendedConnection_deRhamDifferential_eq {M : Type w} [AddCommGroup M]
    [Module R M] (S : SourceDeRham A R)
    (nab : Connection A R ((dividedPowerDifferentialRelations (A := A) δ).mkQ) M) (q : ℕ)
    (w : ⋀[R]^q (dividedPowerDifferentials (A := A) δ)) :
    (extendedConnection S ((dividedPowerDifferentialRelations (A := A) δ).mkQ)
        (Submodule.mkQ_surjective _)
        (generationHypothesis_of_ker_eq_relations δ S _ (Submodule.ker_mkQ _))
            nab).deRhamDifferential q w =
      dividedPowerDeRham δ q w := by
  have h := Classical.choose_spec (exists_unique_quotient_deRhamDifferential S
    ((dividedPowerDifferentialRelations (A := A) δ).mkQ) (Submodule.mkQ_surjective _)
        (generationHypothesis_of_ker_eq_relations δ S _ (Submodule.ker_mkQ _)))
  have hrule : SourceDeRham.SatisfiesRule ((dividedPowerDifferentialRelations (A := A) δ).mkQ)
      (extendedConnection S ((dividedPowerDifferentialRelations (A := A) δ).mkQ)
          (Submodule.mkQ_surjective _)
        (generationHypothesis_of_ker_eq_relations δ S _ (Submodule.ker_mkQ _))
            nab).deRhamDifferential := by
    rw [h.2.2.1 _ (extendedConnection S ((dividedPowerDifferentialRelations (A := A) δ).mkQ)
        (Submodule.mkQ_surjective _)
      (generationHypothesis_of_ker_eq_relations δ S _ (Submodule.ker_mkQ _)) nab).commutes]
    exact h.2.1
  have hext : (extendedConnection S ((dividedPowerDifferentialRelations (A := A) δ).mkQ)
      (Submodule.mkQ_surjective _)
        (generationHypothesis_of_ker_eq_relations δ S _ (Submodule.ker_mkQ _))
            nab).deRhamDifferential q =
      (dividedPowerDeRhamComplex (A := A) δ).differential q := by
    apply LinearMap.ext_on (span_range_smul_ιMulti_eq_top (R := A)
      (dividedPowerDifferential (A := A) δ)
      (dividedPowerDifferentials_span δ) q)
    rintro _ ⟨f, rfl⟩
    exact (hrule q f).trans
      (dividedPowerDeRhamComplex_differential_generator δ q f).symm
  exact LinearMap.congr_fun hext w

variable (S : SourceDeRham A R)

/-- The extension of `∇_n` to the de Rham complex of `R`. -/
abbrev levelExtended (n : ℕ) :=
  extendedConnection S ((dividedPowerDifferentialRelations (A := A) δ).mkQ)
      (Submodule.mkQ_surjective _)
    (generationHypothesis_of_ker_eq_relations δ S _ (Submodule.ker_mkQ _)) (levelConnection p A R δ
        N nabla n)

/-- The level `pⁿ` of left exterior multiplication by the class of a form. -/
theorem formsLevelEquiv_wedgeMap (q n : ℕ) (w : ⋀[R]^q (dividedPowerDifferentials (A := A) δ))
    (z : CompletedTensor p R (completedDividedPowerForms p A δ 1) N) :
    formsLevelEquiv p A R δ N (q + 1) n
        ((CompletedDeRham.wedgeMap p R (completedDividedPowerForms p A δ)
          (completedDividedPowerWedgeOnRing p A δ) N q
          (AdicCompletion.of _ _ w) z).val n) =
      TensorProduct.map LinearMap.id ((leftWedge q).flip w) (levelOneForms p A R δ N n z) := by
  have h := levelTensorEquiv_lTensor (pAdicIdeal (A := R) p) n N
    (dividedPowerDifferentialForms (A := A) δ 1) (pAdicIdeal_fg_ring p R)
    (completedDividedPowerWedgeOnRing p A δ q (AdicCompletion.of _ _ w))
    ((dividedPowerWedge δ q) w) (fun xh x hx ↦ by
      rw [completedDividedPowerWedgeOnRing_apply]
      exact completedDividedPowerWedge_val p A δ q n _ xh w x rfl hx) (z.val n)
  have hv : (CompletedDeRham.wedgeMap p R
      (completedDividedPowerForms p A δ)
      (completedDividedPowerWedgeOnRing p A δ) N q (AdicCompletion.of _ _ w) z).val n =
      (LinearMap.lTensor N (completedDividedPowerWedgeOnRing p A δ q
        (AdicCompletion.of _ _ w))).reduceModIdeal (pAdicIdeal (A := R) p ^ n)
        (z.val n) :=
    AdicCompletion.map_val_apply _ _ _
  rw [hv, h]
  refine (?_ : ∀ t : levelModule p R N n ⊗[R]
      (dividedPowerDifferentialForms (A := A) δ 1),
    LinearMap.lTensor _ ((dividedPowerWedge δ q) w) t =
      TensorProduct.map LinearMap.id ((leftWedge q).flip w)
        (LinearMap.lTensor (levelModule p R N n)
          (exteriorPower.oneEquiv R (dividedPowerDifferentials (A := A) δ)).toLinearMap t))
    (formsLevelEquiv p A R δ N 1 n (z.val n))
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul a e =>
    simp only [LinearMap.lTensor_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
      LinearEquiv.coe_coe, LinearMap.flip_apply, dividedPowerWedge_apply]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- **The level `pⁿ` of the completed de Rham differential of `∇` is the extension of `∇_n` to the
de Rham complex.** -/
theorem formsLevelEquiv_levelDifferential (q n : ℕ)
    (x : (N ⊗[R] completedDividedPowerForms p A δ q) ⧸
      (pAdicIdeal (A := R) p ^ n • ⊤ : Submodule R
        (N ⊗[R] completedDividedPowerForms p A δ q))) :
    formsLevelEquiv p A R δ N (q + 1) n
        (CompletedDeRham.levelDifferential p R
          (completedDividedPowerForms p A δ)
          (completedDividedPowerWedgeOnRing p A δ)
          (completedDividedPowerDeRham p A δ) N nabla
          (isGradedLeibniz_completedDividedPowerOnRing p A δ) q n x) =
      RestrictScalars.addEquiv A R _
        ((levelExtended p A R δ N nabla S n).toLinearMap q
          ((RestrictScalars.addEquiv A R _).symm (formsLevelEquiv p A R δ N q n x))) := by
  have := levelTensor_addMonoidHom_ext (pAdicIdeal (A := R) p) n N
    (dividedPowerDifferentialForms (A := A) δ q) (pAdicIdeal_fg_ring p R)
    (F := ((formsLevelEquiv p A R δ N (q + 1) n).toLinearMap.toAddMonoidHom.comp
      (CompletedDeRham.levelDifferential p R
          (completedDividedPowerForms p A δ)
          (completedDividedPowerWedgeOnRing p A δ)
          (completedDividedPowerDeRham p A δ) N nabla
          (isGradedLeibniz_completedDividedPowerOnRing p A δ) q n)))
    (G := (RestrictScalars.addEquiv A R _).toAddMonoidHom.comp
      (((levelExtended p A R δ N nabla S n).toLinearMap q).toAddMonoidHom.comp
        ((RestrictScalars.addEquiv A R _).symm.toAddMonoidHom.comp
          (formsLevelEquiv p A R δ N q n).toLinearMap.toAddMonoidHom))) (fun m w ↦ by
      have e1 : CompletedDeRham.levelDifferential p R
          (completedDividedPowerForms p A δ)
          (completedDividedPowerWedgeOnRing p A δ)
          (completedDividedPowerDeRham p A δ) N nabla
          (isGradedLeibniz_completedDividedPowerOnRing p A δ) q n
          (Submodule.Quotient.mk (m ⊗ₜ AdicCompletion.of _ _ w)) =
          (CompletedDeRham.wedgeMap p R
            (completedDividedPowerForms p A δ)
            (completedDividedPowerWedgeOnRing p A δ) N q
            (AdicCompletion.of _ _ w) (nabla m)).val n +
          Submodule.Quotient.mk (m ⊗ₜ completedDividedPowerDeRham p A δ q
            (AdicCompletion.of _ _ w)) := rfl
      have e2 : formsLevelEquiv p A R δ N q n
          (Submodule.Quotient.mk (m ⊗ₜ AdicCompletion.of _ _ w)) =
          Submodule.Quotient.mk m ⊗ₜ w := levelTensorEquiv_mk_tmul_of _ _ _ _ _ m w
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
        LinearEquiv.coe_coe, AddEquiv.coe_toAddMonoidHom, e1, e2, map_add,
        completedDividedPowerDeRham_of, levelTensorEquiv_mk_tmul_of, formsLevelEquiv_wedgeMap]
      refine Eq.trans ?_ ((levelExtended p A R δ N nabla S n).map_tmul q
        (Submodule.Quotient.mk m) w).symm
      exact congrArg (fun t ↦ TensorProduct.map LinearMap.id ((leftWedge q).flip w)
          (levelOneForms p A R δ N n (nabla m)) + Submodule.Quotient.mk m ⊗ₜ[R] t)
        (extendedConnection_deRhamDifferential_eq A R δ S (levelConnection p A R δ N nabla n) q
            w).symm)
  exact DFunLike.congr_fun this x

/-- **Integrability in the sense of [Stacks, Remark 60.6.1, Tag 07I0] for a completed
connection**: the composite `N → N ⊗̂_R Ω¹_R → N ⊗̂_R Ω²_R` of `∇` with its extension to one-forms
vanishes. -/
def IsCompletedIntegrable : Prop :=
  ∀ m : N, CompletedDeRham.differential p R
    (completedDividedPowerForms p A δ)
    (completedDividedPowerWedgeOnRing p A δ)
    (completedDividedPowerDeRham p A δ) N nabla
    (isGradedLeibniz_completedDividedPowerOnRing p A δ) 1 (nabla m) = 0

/-- **The level connections of an integrable completed connection are integrable.** -/
theorem isIntegrable_levelConnection (hint : IsCompletedIntegrable p A R δ N nabla) (n : ℕ) :
    Connection.IsIntegrable S ((dividedPowerDifferentialRelations (A := A) δ).mkQ)
        (Submodule.mkQ_surjective _)
      (generationHypothesis_of_ker_eq_relations δ S _ (Submodule.ker_mkQ _)) (levelConnection p A R
          δ N nabla n) := by
  refine Connection.isIntegrable_of_comp_eq_zero (fun x ↦ ?_)
  induction x using Submodule.Quotient.induction_on with
  | H m =>
    have hlev := formsLevelEquiv_levelDifferential p A R δ N nabla S 1 n ((nabla m).val n)
    have hzero : CompletedDeRham.levelDifferential p R
        (completedDividedPowerForms p A δ)
        (completedDividedPowerWedgeOnRing p A δ)
        (completedDividedPowerDeRham p A δ) N nabla
        (isGradedLeibniz_completedDividedPowerOnRing p A δ) 1 n ((nabla m).val n) =
        0 :=
      congrArg (fun z : CompletedTensor p R
        (completedDividedPowerForms p A δ 2) N ↦ z.val n) (hint m)
    have hlev' := hlev.symm.trans ((congrArg (formsLevelEquiv p A R δ N (1 + 1) n) hzero).trans
      (map_zero _))
    have hone : LinearMap.lTensor _
        (exteriorPower.oneEquiv R (dividedPowerDifferentials (A := A) δ)).symm.toLinearMap
        (LinearMap.lTensor (levelModule p R N n)
          (exteriorPower.oneEquiv R (dividedPowerDifferentials (A := A) δ)).toLinearMap
          (formsLevelEquiv p A R δ N 1 n ((nabla m).val n))) =
        formsLevelEquiv p A R δ N 1 n ((nabla m).val n) := by
      rw [← LinearMap.lTensor_comp_apply]
      simp
    refine (congrArg ((levelExtended p A R δ N nabla S n).toLinearMap 1) hone).trans ?_
    exact (RestrictScalars.addEquiv A R _).injective (hlev'.trans (map_zero _).symm)

/-- **The level connections are compatible with the transition maps.** -/
theorem levelConnection_transitionMap {m k : ℕ} (hmk : m ≤ k) (x : levelModule p R N k) :
    levelConnection p A R δ N nabla m (AdicCompletion.transitionMap _ N hmk x) =
      TensorProduct.map (AdicCompletion.transitionMap _ N hmk) LinearMap.id
        (levelConnection p A R δ N nabla k x) := by
  induction x using Submodule.Quotient.induction_on with
  | H y =>
    have e1 : AdicCompletion.transitionMap _ N hmk
        (Submodule.Quotient.mk y : levelModule p R N k) = Submodule.Quotient.mk y :=
      transitionMap_mk_eq _ hmk y
    have e2 : (nabla y).val m = AdicCompletion.transitionMap _ _ hmk ((nabla y).val k) :=
      ((nabla y).property hmk).symm
    have e3 := levelTensorEquiv_transitionMap (pAdicIdeal (A := R) p) N
      (dividedPowerDifferentialForms (A := A) δ 1) (pAdicIdeal_fg_ring p R) hmk
      ((nabla y).val k)
    refine (congrArg (levelConnection p A R δ N nabla m) e1).trans ?_
    refine (congrArg (fun t ↦ LinearMap.lTensor (levelModule p R N m)
      (exteriorPower.oneEquiv R (dividedPowerDifferentials (A := A) δ)).toLinearMap
      (formsLevelEquiv p A R δ N 1 m t)) e2).trans ?_
    refine (congrArg (LinearMap.lTensor (levelModule p R N m)
      (exteriorPower.oneEquiv R (dividedPowerDifferentials (A := A) δ)).toLinearMap) e3).trans ?_
    exact lTensor_map_id_comm _ _ _

end LevelConnection

/-! ### Extended connections along horizontal maps -/

section Horizontal

open Stacks.DeRham.DifferentialDescent

variable {A B Omega : Type u} [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup Omega]
  [Module B Omega] {M M' : Type w} [AddCommGroup M] [Module B M] [AddCommGroup M']
  [Module B M']

/-- **The extension of a connection to the de Rham complex is natural along horizontal maps**:
if `f : M → M'` is `B`-linear with `∇' ∘ f = (f ⊗ 1) ∘ ∇`, then `f ⊗ 1` commutes with the two
extended connections in every degree. -/
theorem extendedConnection_map (S : SourceDeRham A B) (pi : Ω[B⁄A] →ₗ[B] Omega)
    (hpi : Function.Surjective pi) (hgen : S.GenerationHypothesis pi)
    (nab : Connection A B pi M) (nab' : Connection A B pi M') (f : M →ₗ[B] M')
    (hf : ∀ m, nab' (f m) = TensorProduct.map f LinearMap.id (nab m)) (q : ℕ)
    (x : M ⊗[B] (⋀[B]^q Omega)) :
    RestrictScalars.addEquiv A B _ ((extendedConnection S pi hpi hgen nab').toLinearMap q
        ((RestrictScalars.addEquiv A B _).symm (TensorProduct.map f LinearMap.id x))) =
      TensorProduct.map f LinearMap.id
        (RestrictScalars.addEquiv A B _ ((extendedConnection S pi hpi hgen nab).toLinearMap q
          ((RestrictScalars.addEquiv A B _).symm x))) := by
  induction x using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul m w =>
    have h1 := (extendedConnection S pi hpi hgen nab').map_tmul q (f m) w
    have h2 := (extendedConnection S pi hpi hgen nab).map_tmul q m w
    rw [TensorProduct.map_tmul, LinearMap.id_apply]
    refine h1.trans ?_
    refine Eq.trans ?_ (congrArg (TensorProduct.map f LinearMap.id) h2).symm
    rw [hf, map_add, TensorProduct.map_tmul, LinearMap.id_apply, ← LinearMap.comp_apply,
      ← LinearMap.comp_apply, ← TensorProduct.map_comp, ← TensorProduct.map_comp,
      LinearMap.id_comp, LinearMap.comp_id]
    simp only [LinearMap.id_comp, LinearMap.comp_id]
    have h := Classical.choose_spec (exists_unique_quotient_deRhamDifferential S pi hpi hgen)
    rw [h.2.2.1 _ (extendedConnection S pi hpi hgen nab').commutes,
      h.2.2.1 _ (extendedConnection S pi hpi hgen nab).commutes]

end Horizontal

end CompletedLevels

end Crystalline
