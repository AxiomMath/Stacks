module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnectionBaseChange
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.CompletedConnectionLevels
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.PthRootIntegratingHomotopy
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.CompletionLevelFormsExt

/-!
# The completed de Rham complex of the extension `B → B'` at the levels `pⁿ`

Let `(M, ∇)` be a module with a completed connection over a divided power ring `B`, and let
`B' = B[z]⟨ξ⟩/(ξ - (z^p - λ))`. The base change `M' = (B' ⊗_B M)^∧` of `M` carries the base-changed
completed connection `∇'` (`Crystalline.CompletedConnection.baseChange`), and its completed de Rham
complex has the terms `M' ⊗̂_{B'} Ω^q_{B'}`. This module identifies the level `pⁿ` of those terms
with the terms `(B' ⊗_B N_n) ⊗_{B'} Ω^q_{B'/A,γ'}` of the uncompleted de Rham complex of the base
change of the level connection `∇_n` on `N_n = M / pⁿ M`, compatibly with the differentials and
with the canonical map of complexes `c_M^•`.

## Main definitions

* `Crystalline.CompletedLevels.quotientAdicCompletionEquiv` — the level `Iⁿ` of a completion is the
  level `Iⁿ` of the module, for a finitely generated `I`.
* `Crystalline.CompletedLevels.baseChangeLevelEquiv` — `(S ⊗_R M) / pⁿ ≃ S ⊗_R (M / pⁿ M)`.
* `Crystalline.PthRootExtension.primeLevelEquiv` — the level `pⁿ` of `M' ⊗̂_{B'} Ω^q_{B'}` is
  `(B' ⊗_B N_n) ⊗_{B'} Ω^q_{B'/A,γ'}`.

## References

* [Stacks Project, Lemma 60.25.3, Tag 07N1](https://stacks.math.columbia.edu/tag/07N1)
-/

@[expose] public noncomputable section

open DividedPowers

open scoped TensorProduct

universe u w

namespace Crystalline

namespace CompletedLevels

/-! ### The levels of a completion and of a base change -/

section Generic

variable {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) (X : Type*) [AddCommGroup X] [Module R X]

/-- **The level `Iⁿ` of a completion is the level `Iⁿ` of the module**, for a finitely generated
ideal `I`: the evaluation at level `n` is surjective with kernel `Iⁿ X̂`. -/
def quotientAdicCompletionEquiv (hI : I.FG) :
    (AdicCompletion I X ⧸ (I ^ n • ⊤ : Submodule R (AdicCompletion I X))) ≃ₗ[R]
      X ⧸ (I ^ n • ⊤ : Submodule R X) :=
  (Submodule.quotEquivOfEq _ _ (AdicCompletion.pow_smul_top_eq_ker_eval hI)).trans
    ((AdicCompletion.eval I X n).quotKerEquivOfSurjective (AdicCompletion.eval_surjective I X n))

/-- The level identification on the class of an element of the completion. -/
@[simp] theorem quotientAdicCompletionEquiv_mk (hI : I.FG) (x : AdicCompletion I X) :
    quotientAdicCompletionEquiv I n X hI (Submodule.Quotient.mk x) = x.val n := rfl

variable (p : ℕ) (S : Type*) [CommRing S] [Algebra R S] (M : Type*) [AddCommGroup M] [Module R M]

/-- `pⁿ` kills `S ⊗_R (M / pⁿ M)`. -/
theorem pow_nsmul_baseChangeLevel_eq_zero
    (z : S ⊗[R] (M ⧸ (pAdicIdeal (A := R) p ^ n • ⊤ : Submodule R M))) : (p ^ n : ℕ) • z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => rw [smul_zero]
  | tmul s x =>
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [← TensorProduct.tmul_smul, ← Submodule.Quotient.mk_smul, (Submodule.Quotient.mk_eq_zero
        _).mpr
        ((PAdicCompletion.mem_pow_smul_top_iff p R n _).mpr ⟨m, rfl⟩), TensorProduct.tmul_zero]
  | add a b ha hb => rw [smul_add, ha, hb, add_zero]

/-- The forward map of `Crystalline.CompletedLevels.baseChangeLevelEquiv`. -/
def baseChangeLevelFwd :
    ((S ⊗[R] M) ⧸ (pAdicIdeal (A := S) p ^ n • ⊤ : Submodule S (S ⊗[R] M))) →ₗ[S]
      S ⊗[R] (M ⧸ (pAdicIdeal (A := R) p ^ n • ⊤ : Submodule R M)) :=
  Submodule.liftQ _ ((pAdicIdeal (A := R) p ^ n • ⊤ : Submodule R M).mkQ.baseChange S)
    (fun y hy ↦ by
      obtain ⟨y', rfl⟩ := (PAdicCompletion.mem_pow_smul_top_iff p S n y).mp hy
      rw [LinearMap.mem_ker, map_nsmul, pow_nsmul_baseChangeLevel_eq_zero])

/-- The backward map of `Crystalline.CompletedLevels.baseChangeLevelEquiv` on the second factor. -/
def baseChangeLevelBwdAux :
    (M ⧸ (pAdicIdeal (A := R) p ^ n • ⊤ : Submodule R M)) →ₗ[R]
      ((S ⊗[R] M) ⧸ (pAdicIdeal (A := S) p ^ n • ⊤ : Submodule S (S ⊗[R] M))) :=
  Submodule.liftQ _ (((pAdicIdeal (A := S) p ^ n • ⊤ : Submodule S (S ⊗[R] M)).mkQ.restrictScalars
      R).comp (TensorProduct.mk R S M 1)) (fun m hm ↦ by
    obtain ⟨m', rfl⟩ := (PAdicCompletion.mem_pow_smul_top_iff p R n m).mp hm
    rw [LinearMap.mem_ker, map_nsmul, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact (PAdicCompletion.mem_pow_smul_top_iff p S n _).mpr ⟨_, rfl⟩)

/-- **`(S ⊗_R M) / pⁿ ≃ S ⊗_R (M / pⁿ M)`**, linear over `S`. -/
def baseChangeLevelEquiv :
    ((S ⊗[R] M) ⧸ (pAdicIdeal (A := S) p ^ n • ⊤ : Submodule S (S ⊗[R] M))) ≃ₗ[S]
      S ⊗[R] (M ⧸ (pAdicIdeal (A := R) p ^ n • ⊤ : Submodule R M)) :=
  LinearEquiv.ofLinear (baseChangeLevelFwd n p S M)
    ((baseChangeLevelBwdAux n p S M).liftBaseChange S)
    (by
      refine TensorProduct.AlgebraTensorModule.ext fun s x ↦ ?_
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      have h1 : s • Submodule.Quotient.mk ((1 : S) ⊗ₜ[R] m) =
          (Submodule.Quotient.mk (s ⊗ₜ[R] m) :
            (S ⊗[R] M) ⧸ (pAdicIdeal (A := S) p ^ n • ⊤ : Submodule S (S ⊗[R] M))) := by
        rw [← Submodule.Quotient.mk_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.liftBaseChange_tmul,
        LinearMap.id_apply]
      change baseChangeLevelFwd n p S M (s • Submodule.Quotient.mk ((1 : S) ⊗ₜ[R] m)) = _
      rw [h1]
      rfl)
    (by
      refine Submodule.linearMap_qext _ (TensorProduct.AlgebraTensorModule.ext fun s m ↦ ?_)
      change s • Submodule.Quotient.mk ((1 : S) ⊗ₜ[R] m) =
        (Submodule.Quotient.mk (s ⊗ₜ[R] m) :
          (S ⊗[R] M) ⧸ (pAdicIdeal (A := S) p ^ n • ⊤ : Submodule S (S ⊗[R] M)))
      rw [← Submodule.Quotient.mk_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one])

/-- The identification `(S ⊗_R M) / pⁿ ≃ S ⊗_R (M / pⁿ M)` on a pure tensor. -/
@[simp] theorem baseChangeLevelEquiv_mk_tmul (s : S) (m : M) :
    baseChangeLevelEquiv (R := R) n p S M (Submodule.Quotient.mk (s ⊗ₜ m)) =
      s ⊗ₜ Submodule.Quotient.mk m := rfl

/-- **Two additive maps out of the level `Iⁿ` of a completion agreeing on the classes of
uncompleted elements are equal.** -/
theorem quotientAdicCompletion_addMonoidHom_ext (hI : I.FG) {Z : Type*} [AddCommGroup Z]
    {F G : (AdicCompletion I X ⧸ (I ^ n • ⊤ : Submodule R (AdicCompletion I X))) →+ Z}
    (h : ∀ x : X, F (Submodule.Quotient.mk (AdicCompletion.of I X x)) =
      G (Submodule.Quotient.mk (AdicCompletion.of I X x))) : F = G := by
  refine AddMonoidHom.ext fun y ↦ ?_
  rw [← (quotientAdicCompletionEquiv I n X hI).symm_apply_apply y]
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (quotientAdicCompletionEquiv I n X hI y)
  rw [← hx]
  have : (quotientAdicCompletionEquiv I n X hI).symm (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (AdicCompletion.of I X x) := by
    rw [LinearEquiv.symm_apply_eq]
    exact (AdicCompletion.eval_of I X n x)
  rw [this]
  exact h x

end Generic

section GenericBaseChange

variable (p n : ℕ) {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (M X Y : Type*)
  [AddCommGroup M] [Module R M] [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module S Y]
  (g : X →ₛₗ[algebraMap R S] Y)

/-- The level `pⁿ` of the base-changed module `(S ⊗_R M)^∧` is `S ⊗_R (M / pⁿ M)`. -/
abbrev baseChangeCarrierLevelEquiv :
    (CompletedConnection.baseChangeCarrier p R S M ⧸
      (pAdicIdeal (A := S) p ^ n • ⊤ : Submodule S (CompletedConnection.baseChangeCarrier p R S M)))
      ≃ₗ[S] S ⊗[R] (M ⧸ (pAdicIdeal (A := R) p ^ n • ⊤ : Submodule R M)) :=
  (quotientAdicCompletionEquiv (pAdicIdeal (A := S) p) n (S ⊗[R] M)
    (CompletedConnection.pAdicIdeal_fg p S)).trans (baseChangeLevelEquiv n p S M)

/-- **The level `pⁿ` of `ψ_* : M ⊗̂_R X̂ → M' ⊗̂_S Ŷ` is `ψ_*` on the level modules.** -/
theorem levelTensorEquiv_adicQuotientMap_baseChangeTensor
    (y : (M ⊗[R] AdicCompletion (pAdicIdeal (A := R) p) X) ⧸
      (pAdicIdeal (A := R) p ^ n • ⊤ : Submodule R
        (M ⊗[R] AdicCompletion (pAdicIdeal (A := R) p) X))) :
    TensorProduct.map (baseChangeCarrierLevelEquiv p n M).toLinearMap LinearMap.id
        (levelTensorEquiv (pAdicIdeal (A := S) p) n (CompletedConnection.baseChangeCarrier p R S M)
            Y
          (CompletedConnection.pAdicIdeal_fg p S)
          (adicQuotientMap (CompletedConnection.baseChangeTensor p R S M
            (AdicCompletion (pAdicIdeal (A := R) p) X) (AdicCompletion (pAdicIdeal (A := S) p) Y)
            (adicCompletionMapₛₗ g (CompletedConnection.pAdicIdeal_map_le p R S)))
            (CompletedConnection.pAdicIdeal_map_le p R S) n y)) =
      Connection.baseChangeValues g
        (levelTensorEquiv (pAdicIdeal (A := R) p) n M X (CompletedConnection.pAdicIdeal_fg p R)
            y) := by
  rw [← (levelTensorEquiv (pAdicIdeal (A := R) p) n M X (CompletedConnection.pAdicIdeal_fg p
      R)).symm_apply_apply y]
  generalize levelTensorEquiv (pAdicIdeal (A := R) p) n M X (CompletedConnection.pAdicIdeal_fg p R)
      y = t
  rw [LinearEquiv.apply_symm_apply]
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a x =>
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    rw [levelTensorEquiv_symm_mk_tmul]
    show TensorProduct.map (baseChangeCarrierLevelEquiv p n M).toLinearMap LinearMap.id
      (levelTensorEquiv (pAdicIdeal (A := S) p) n (CompletedConnection.baseChangeCarrier p R S M) Y
        (CompletedConnection.pAdicIdeal_fg p S) (Submodule.Quotient.mk
          (AdicCompletion.of _ _ ((1 : S) ⊗ₜ m) ⊗ₜ
            adicCompletionMapₛₗ g (CompletedConnection.pAdicIdeal_map_le p R S)
              (AdicCompletion.of _ _ x)))) = _
    rw [adicCompletionMapₛₗ_of, levelTensorEquiv_mk_tmul_of, TensorProduct.map_tmul,
      Connection.baseChangeValues_tmul]
    rfl

end GenericBaseChange

end CompletedLevels

/-! ### The base change to `B'` at the levels -/

namespace PthRootExtension

open CompletedLevels Stacks.DeRham.DifferentialDescent

section Target

variable (A : Type u) [CommRing A] (B : DividedPowerRing.{u}) [Algebra A (B : Type u)] (p : ℕ)
  (lam : (B : Type u)) (hp : p ≠ 0)

/-- The structure map `B → B'` as a morphism of `A`-algebras. -/
abbrev primeAlgHom : (B : Type u) →ₐ[A] primeRing B p lam :=
  IsScalarTower.toAlgHom A (B : Type u) (primeRing B p lam)

/-- The structure map `B → B'` is a divided power morphism, read for `primeAlgHom`. -/
theorem isDPMorphism_primeAlgHom :
    IsDPMorphism B.dividedPowers (primeDividedPowers B p lam hp)
      (primeAlgHom A B p lam).toRingHom :=
  isDPMorphism_algebraMap_primeDividedPowers B p lam hp

/-- **The degree-one comparison of divided power differentials along `B → B'` is
`Crystalline.PthRootExtension.primeFormsComparison`.** -/
theorem mapDifferentialsOfDPMorphism_primeAlgHom (omega : baseForms A B) :
    mapDifferentialsOfDPMorphism (A := A) (J := B.ideal) (delta := B.dividedPowers)
        (primeDividedPowers B p lam hp) (primeAlgHom A B p lam)
        (isDPMorphism_primeAlgHom A B p lam hp) omega =
      primeFormsComparison A B p lam hp omega := by
  have hmem : omega ∈ Submodule.span (B : Type u)
      (Set.range (dividedPowerDifferential (A := A) B.dividedPowers)) := by
    rw [dividedPowerDifferentials_span]; exact Submodule.mem_top
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    rw [mapDifferentialsOfDPMorphism_d]
    exact (primeFormsComparison_dividedPowerDifferential A B p lam hp b).symm
  | zero => rw [map_zero, map_zero]
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul r x _ hx =>
    rw [mapDifferentialsOfDPMorphism_smul, hx, LinearMap.map_smulₛₗ]
    rfl

/-- The comparison `Ω^q_{B/A,γ} → Ω^q_{B'/A,γ'}` of divided power forms along `B → B'`,
semilinear over the structure map. -/
def primeFormsMapₛₗ (q : ℕ) :
    dividedPowerDifferentialForms (A := A) B.dividedPowers q →ₛₗ[algebraMap (B : Type u)
      (primeRing B p lam)] dividedPowerDifferentialForms (A := A) (primeDividedPowers B p lam hp) q
    where
  toFun := mapDifferentialFormsOfDPMorphism (A := A) (J := B.ideal) (delta := B.dividedPowers)
    (primeDividedPowers B p lam hp) (primeAlgHom A B p lam) (isDPMorphism_primeAlgHom A B p lam hp)
        q
  map_add' := map_add _
  map_smul' := (mapDifferentialFormsOfDPMorphism (A := A) (J := B.ideal)
    (delta := B.dividedPowers) (primeDividedPowers B p lam hp) (primeAlgHom A B p lam)
    (isDPMorphism_primeAlgHom A B p lam hp) q).map_smul'

/-- The comparison of forms carries a wedge of one-forms to the wedge of their images under
`Crystalline.PthRootExtension.primeFormsComparison`. -/
theorem primeFormsMapₛₗ_ιMulti (q : ℕ) (v : Fin q → baseForms A B) :
    primeFormsMapₛₗ A B p lam hp q (exteriorPower.ιMulti (B : Type u) q v) =
      exteriorPower.ιMulti (primeRing B p lam) q (primeFormsComparison A B p lam hp ∘ v) := by
  show mapDifferentialFormsOfDPMorphism (A := A) (J := B.ideal) (delta := B.dividedPowers)
    (primeDividedPowers B p lam hp) (primeAlgHom A B p lam)
    (isDPMorphism_primeAlgHom A B p lam hp) q (exteriorPower.ιMulti (B : Type u) q v) = _
  rw [mapDifferentialFormsOfDPMorphism_ιMulti]
  congr 1
  funext j
  exact mapDifferentialsOfDPMorphism_primeAlgHom A B p lam hp (v j)

/-- The comparison of one-forms, read through `exteriorPower.oneEquiv`, is
`Crystalline.PthRootExtension.primeFormsComparison`. -/
theorem oneEquiv_primeFormsMapₛₗ (eta : dividedPowerDifferentialForms (A := A) B.dividedPowers 1) :
    exteriorPower.oneEquiv (primeRing B p lam) (primeForms A B p lam hp)
        (primeFormsMapₛₗ A B p lam hp 1 eta) =
      primeFormsComparison A B p lam hp (exteriorPower.oneEquiv (B : Type u) (baseForms A B) eta) :=
  (mapDifferentialFormsOfDPMorphism_oneEquiv _ _ _ _ eta).trans
    (mapDifferentialsOfDPMorphism_primeAlgHom A B p lam hp _)

/-- The comparison `Ω̂^q_B → Ω̂^q_{B'}` of completed divided power forms along `B → B'`. -/
abbrev primeCompletedFormsMap (q : ℕ) :
    completedDividedPowerForms p A B.dividedPowers q →ₛₗ[algebraMap (B : Type u) (primeRing B p
        lam)]
      completedDividedPowerForms p A (primeDividedPowers B p lam hp) q :=
  adicCompletionMapₛₗ (primeFormsMapₛₗ A B p lam hp q) (CompletedConnection.pAdicIdeal_map_le p _ _)

/-- It is `Crystalline.completedMapDifferentialForms` for the structure map. -/
theorem primeCompletedFormsMap_eq (q : ℕ) (x : completedDividedPowerForms p A B.dividedPowers q) :
    primeCompletedFormsMap A B p lam hp q x =
      completedMapDifferentialForms p A B.dividedPowers (primeDividedPowers B p lam hp)
        (primeAlgHom A B p lam) (isDPMorphism_primeAlgHom A B p lam hp) q x := rfl

/-- The comparison of completed forms is compatible with the universal differentials. -/
theorem primeCompletedFormsMap_differential (b : (B : Type u)) :
    primeCompletedFormsMap A B p lam hp 1
        (completedDividedPowerDifferentialOnRing p A B.dividedPowers b) =
      completedDividedPowerDifferentialOnRing p A (primeDividedPowers B p lam hp)
        (algebraMap (B : Type u) (primeRing B p lam) b) :=
  (primeCompletedFormsMap_eq A B p lam hp 1 _).trans
    (completedMapDifferentialForms_completedFormsDifferential_of p A B.dividedPowers
      (primeDividedPowers B p lam hp) (primeAlgHom A B p lam)
      (isDPMorphism_primeAlgHom A B p lam hp) b)

variable (M : Type u) [AddCommGroup M] [Module (B : Type u) M]
  (nabla : CompletedConnection p (B : Type u) (completedDividedPowerForms p A B.dividedPowers 1)
    (completedDividedPowerDifferentialOnRing p A B.dividedPowers) M)

/-- The base-changed module `M' = (B' ⊗_B M)^∧`. -/
abbrev primeCarrier : Type u :=
  CompletedConnection.baseChangeCarrier p (B : Type u) (primeRing B p lam) M

/-- **The base-changed completed connection `∇'` on `M' = (B' ⊗_B M)^∧`.** -/
abbrev primeCompletedConnection :
    CompletedConnection p (primeRing B p lam)
      (completedDividedPowerForms p A (primeDividedPowers B p lam hp) 1)
      (completedDividedPowerDifferentialOnRing p A (primeDividedPowers B p lam hp))
      (primeCarrier B p lam M) :=
  CompletedConnection.baseChange p (B : Type u) (primeRing B p lam) M
    (completedDividedPowerForms p A B.dividedPowers 1)
    (completedDividedPowerForms p A (primeDividedPowers B p lam hp) 1)
    (completedDividedPowerDifferentialOnRing p A (primeDividedPowers B p lam hp))
    (primeCompletedFormsMap A B p lam hp 1) nabla
    (completedDividedPowerDifferentialOnRing_add p A (primeDividedPowers B p lam hp))
    (completedDividedPowerDifferentialOnRing_mul p A (primeDividedPowers B p lam hp))
    (primeCompletedFormsMap_differential A B p lam hp)

/-- **The level `pⁿ` of `M'` is `B' ⊗_B M_n`.** -/
abbrev primeLevelModuleEquiv (n : ℕ) :
    levelModule p (primeRing B p lam) (primeCarrier B p lam M) n ≃ₗ[primeRing B p lam]
      primeRing B p lam ⊗[(B : Type u)] levelModule p (B : Type u) M n :=
  baseChangeCarrierLevelEquiv p n M

/-- The identification `M'_n ≃ B' ⊗_B M_n` on the class of a pure tensor. -/
theorem primeLevelModuleEquiv_mk_of (n : ℕ) (b : primeRing B p lam) (m : M) :
    primeLevelModuleEquiv B p lam M n
        (Submodule.Quotient.mk (AdicCompletion.of _ _ (b ⊗ₜ m))) =
      b ⊗ₜ Submodule.Quotient.mk m := rfl

/-- **The level `pⁿ` of `ψ_*` on the values of a completed connection is `ψ_*` on the values of
the level connection.** -/
theorem primeLevel_baseChangeValues (n : ℕ)
    (z : CompletedTensor p (B : Type u) (completedDividedPowerForms p A B.dividedPowers 1) M) :
    TensorProduct.map (primeLevelModuleEquiv B p lam M n).toLinearMap LinearMap.id
        (levelOneForms p A (primeRing B p lam) (primeDividedPowers B p lam hp)
          (primeCarrier B p lam M) n
          (CompletedConnection.baseChangeValues p (B : Type u) (primeRing B p lam) M
            (completedDividedPowerForms p A B.dividedPowers 1)
            (completedDividedPowerForms p A (primeDividedPowers B p lam hp) 1)
            (primeCompletedFormsMap A B p lam hp 1) z)) =
      Connection.baseChangeValues (primeFormsComparison A B p lam hp)
        (levelOneForms p A (B : Type u) B.dividedPowers M n z) := by
  have hg := levelTensorEquiv_adicQuotientMap_baseChangeTensor p n M
    (dividedPowerDifferentialForms (A := A) B.dividedPowers 1)
    (dividedPowerDifferentialForms (A := A) (primeDividedPowers B p lam hp) 1)
    (primeFormsMapₛₗ A B p lam hp 1) (z.val n)
  show TensorProduct.map (baseChangeCarrierLevelEquiv p n M).toLinearMap LinearMap.id
      (LinearMap.lTensor _ (exteriorPower.oneEquiv (primeRing B p lam)
        (primeForms A B p lam hp)).toLinearMap
        (levelTensorEquiv (pAdicIdeal (A := primeRing B p lam) p) n
          (CompletedConnection.baseChangeCarrier p (B : Type u) (primeRing B p lam) M)
          (dividedPowerDifferentialForms (A := A) (primeDividedPowers B p lam hp) 1)
          (CompletedConnection.pAdicIdeal_fg p _)
          (adicQuotientMap (CompletedConnection.baseChangeTensor p (B : Type u)
            (primeRing B p lam) M (completedDividedPowerForms p A B.dividedPowers 1)
            (completedDividedPowerForms p A (primeDividedPowers B p lam hp) 1)
            (primeCompletedFormsMap A B p lam hp 1))
            (CompletedConnection.pAdicIdeal_map_le p _ _) n (z.val n)))) =
    Connection.baseChangeValues (primeFormsComparison A B p lam hp)
      (LinearMap.lTensor _ (exteriorPower.oneEquiv (B : Type u) (baseForms A B)).toLinearMap
        (levelTensorEquiv (pAdicIdeal (A := (B : Type u)) p) n M
          (dividedPowerDifferentialForms (A := A) B.dividedPowers 1)
          (CompletedConnection.pAdicIdeal_fg p _) (z.val n)))
  refine (lTensor_map_id_comm _ _ _).symm.trans ?_
  refine (congrArg (LinearMap.lTensor _ (exteriorPower.oneEquiv (primeRing B p lam)
    (primeForms A B p lam hp)).toLinearMap) hg).trans ?_
  refine (?_ : ∀ t : levelModule p (B : Type u) M n ⊗[(B : Type u)]
      dividedPowerDifferentialForms (A := A) B.dividedPowers 1,
    LinearMap.lTensor _ (exteriorPower.oneEquiv (primeRing B p lam)
      (primeForms A B p lam hp)).toLinearMap
      (Connection.baseChangeValues (primeFormsMapₛₗ A B p lam hp 1) t) =
    Connection.baseChangeValues (primeFormsComparison A B p lam hp)
      (LinearMap.lTensor _ (exteriorPower.oneEquiv (B : Type u) (baseForms A B)).toLinearMap t)) _
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a eta =>
    rw [Connection.baseChangeValues_tmul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul,
      Connection.baseChangeValues_tmul, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      oneEquiv_primeFormsMapₛₗ]

/-- The level connection of `∇'` on `M'_n`. -/
abbrev primeLevelConnection (n : ℕ) :=
  levelConnection p A (primeRing B p lam) (primeDividedPowers B p lam hp) (primeCarrier B p lam M)
    (primeCompletedConnection A B p lam hp M nabla) n

/-- The base change to `B'` of the level connection of `∇` on `M_n`. -/
abbrev baseChangedLevelConnection (n : ℕ) :=
  primeConnection A B p lam hp (levelModule p (B : Type u) M n)
    (levelConnection p A (B : Type u) B.dividedPowers M nabla n)

/-- Two additive maps out of `S ⊗_R M` agreeing on pure tensors are equal. -/
theorem tensor_addMonoidHom_ext {R S M Z : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup Z] {F G : S ⊗[R] M →+ Z}
    (h : ∀ (s : S) (m : M), F (s ⊗ₜ m) = G (s ⊗ₜ m)) : F = G :=
  AddMonoidHom.ext fun t ↦ by
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul s m => exact h s m
    | add a b ha hb => rw [map_add, map_add, ha, hb]

/-- The horizontality of `M'_n ≃ B' ⊗_B M_n` on the class of a pure tensor. -/
theorem primeLevelConnection_horizontal_tmul (n : ℕ) (b' : primeRing B p lam) (m : M) :
    TensorProduct.map (primeLevelModuleEquiv B p lam M n).toLinearMap LinearMap.id
        (primeLevelConnection A B p lam hp M nabla n
          (Submodule.Quotient.mk (AdicCompletion.of _ _ (b' ⊗ₜ m)))) =
      baseChangedLevelConnection A B p lam hp M nabla n (b' ⊗ₜ Submodule.Quotient.mk m) := by
  have e1 : primeCompletedConnection A B p lam hp M nabla (AdicCompletion.of _ _ (b' ⊗ₜ m)) =
      b' • CompletedConnection.baseChangeValues p (B : Type u) (primeRing B p lam) M
        (completedDividedPowerForms p A B.dividedPowers 1)
        (completedDividedPowerForms p A (primeDividedPowers B p lam hp) 1)
        (primeCompletedFormsMap A B p lam hp 1) (nabla m) +
      CompletedConnection.correction p (B : Type u) (primeRing B p lam) M
        (completedDividedPowerForms p A (primeDividedPowers B p lam hp) 1)
        (completedDividedPowerDifferentialOnRing p A (primeDividedPowers B p lam hp) b')
        (CompletedConnection.baseChangeInclusion p (B : Type u) (primeRing B p lam) M m) :=
    CompletedConnection.baseChange_of_tmul _ _ _ _ _ _ _ _ _ _ _ _ b' m
  have e2 := primeLevel_baseChangeValues A B p lam hp M n (nabla m)
  have e3 := levelOneForms_differential p A (primeRing B p lam) (primeDividedPowers B p lam hp)
    (primeCarrier B p lam M) n
    (CompletedConnection.baseChangeInclusion p (B : Type u) (primeRing B p lam) M m) b'
  have e4 := Connection.baseChange_tmul (primeFormsComparison A B p lam hp)
    (levelConnection p A (B : Type u) B.dividedPowers M nabla n)
    (primeFormsComparison_dividedPowerDifferential A B p lam hp) b' (Submodule.Quotient.mk m)
  have s2 : TensorProduct.map (primeLevelModuleEquiv B p lam M n).toLinearMap LinearMap.id
      (levelOneForms p A (primeRing B p lam) (primeDividedPowers B p lam hp)
        (primeCarrier B p lam M) n (toCompletedTensor p (primeRing B p lam)
          (completedDividedPowerForms p A (primeDividedPowers B p lam hp) 1)
          (primeCarrier B p lam M)
          (CompletedConnection.baseChangeInclusion p (B : Type u) (primeRing B p lam) M m ⊗ₜ
            completedDividedPowerDifferentialOnRing p A (primeDividedPowers B p lam hp) b'))) =
      ((1 : primeRing B p lam) ⊗ₜ Submodule.Quotient.mk m) ⊗ₜ
        (dividedPowerDifferentialRelations (A := A) (primeDividedPowers B p lam hp)).mkQ
          (KaehlerDifferential.D A (primeRing B p lam) b') :=
    (congrArg (TensorProduct.map (primeLevelModuleEquiv B p lam M n).toLinearMap
      LinearMap.id) e3).trans (TensorProduct.map_tmul _ _ _ _)
  have s1 : levelOneForms p A (primeRing B p lam) (primeDividedPowers B p lam hp)
      (primeCarrier B p lam M) n
      (primeCompletedConnection A B p lam hp M nabla (AdicCompletion.of _ _ (b' ⊗ₜ m))) =
      b' • levelOneForms p A (primeRing B p lam) (primeDividedPowers B p lam hp)
        (primeCarrier B p lam M) n
        (CompletedConnection.baseChangeValues p (B : Type u) (primeRing B p lam) M
          (completedDividedPowerForms p A B.dividedPowers 1)
          (completedDividedPowerForms p A (primeDividedPowers B p lam hp) 1)
          (primeCompletedFormsMap A B p lam hp 1) (nabla m)) +
      levelOneForms p A (primeRing B p lam) (primeDividedPowers B p lam hp)
        (primeCarrier B p lam M) n (toCompletedTensor p (primeRing B p lam)
          (completedDividedPowerForms p A (primeDividedPowers B p lam hp) 1)
          (primeCarrier B p lam M)
          (CompletedConnection.baseChangeInclusion p (B : Type u) (primeRing B p lam) M m ⊗ₜ
            completedDividedPowerDifferentialOnRing p A (primeDividedPowers B p lam hp) b')) :=
    (congrArg (levelOneForms p A (primeRing B p lam) (primeDividedPowers B p lam hp)
      (primeCarrier B p lam M) n) e1).trans
      (((levelOneForms p A (primeRing B p lam) (primeDividedPowers B p lam hp)
        (primeCarrier B p lam M) n).map_add _ _).trans
        (congrArg (· + _) ((levelOneForms p A (primeRing B p lam) (primeDividedPowers B p lam hp)
          (primeCarrier B p lam M) n).map_smul _ _)))
  have s3 : levelConnection p A (B : Type u) B.dividedPowers M nabla n
      (Submodule.Quotient.mk m) = levelOneForms p A (B : Type u) B.dividedPowers M n (nabla m) :=
    rfl
  show TensorProduct.map (primeLevelModuleEquiv B p lam M n).toLinearMap LinearMap.id
      (levelOneForms p A (primeRing B p lam) (primeDividedPowers B p lam hp)
        (primeCarrier B p lam M) n
        (primeCompletedConnection A B p lam hp M nabla (AdicCompletion.of _ _ (b' ⊗ₜ m)))) = _
  refine (congrArg (TensorProduct.map (primeLevelModuleEquiv B p lam M n).toLinearMap
    LinearMap.id) s1).trans ?_
  refine ((TensorProduct.map (primeLevelModuleEquiv B p lam M n).toLinearMap
    LinearMap.id).map_add _ _).trans ?_
  refine Eq.trans ?_ e4.symm
  refine congrArg₂ (· + ·) (((TensorProduct.map (primeLevelModuleEquiv B p lam M n).toLinearMap
    LinearMap.id).map_smul _ _).trans (congrArg (b' • ·) (e2.trans ?_))) s2
  rw [s3]

/-- **The identification `M'_n ≃ B' ⊗_B M_n` is horizontal**: it carries the level connection of
the base-changed completed connection to the base change of the level connection. -/
theorem primeLevelConnection_horizontal (n : ℕ)
    (x : levelModule p (primeRing B p lam) (primeCarrier B p lam M) n) :
    TensorProduct.map (primeLevelModuleEquiv B p lam M n).toLinearMap LinearMap.id
        (primeLevelConnection A B p lam hp M nabla n x) =
      baseChangedLevelConnection A B p lam hp M nabla n (primeLevelModuleEquiv B p lam M n x) := by
  have key := tensor_addMonoidHom_ext
    (F := ((TensorProduct.map (primeLevelModuleEquiv B p lam M n).toLinearMap
      LinearMap.id).toAddMonoidHom.comp (primeLevelConnection A B p lam hp M nabla
          n).toAddMonoidHom).comp
        ((Submodule.mkQ _).toAddMonoidHom.comp
          (AdicCompletion.of (pAdicIdeal (A := primeRing B p lam) p)
            (primeRing B p lam ⊗[(B : Type u)] M)).toAddMonoidHom))
    (G := ((baseChangedLevelConnection A B p lam hp M nabla n).toAddMonoidHom.comp
      (primeLevelModuleEquiv B p lam M n).toLinearMap.toAddMonoidHom).comp
        ((Submodule.mkQ _).toAddMonoidHom.comp
          (AdicCompletion.of (pAdicIdeal (A := primeRing B p lam) p)
            (primeRing B p lam ⊗[(B : Type u)] M)).toAddMonoidHom))
    (fun b' m ↦ primeLevelConnection_horizontal_tmul A B p lam hp M nabla n b' m)
  have := quotientAdicCompletion_addMonoidHom_ext (pAdicIdeal (A := primeRing B p lam) p) n
    (primeRing B p lam ⊗[(B : Type u)] M) (CompletedConnection.pAdicIdeal_fg p _)
    (F := (TensorProduct.map (primeLevelModuleEquiv B p lam M n).toLinearMap
      LinearMap.id).toAddMonoidHom.comp (primeLevelConnection A B p lam hp M nabla
          n).toAddMonoidHom)
    (G := (baseChangedLevelConnection A B p lam hp M nabla n).toAddMonoidHom.comp
      (primeLevelModuleEquiv B p lam M n).toLinearMap.toAddMonoidHom)
    (fun t ↦ DFunLike.congr_fun key t)
  exact DFunLike.congr_fun this x

/-- The degree-`q` term of the target complex `M' ⊗̂_{B'} Ω^q_{B'}`. -/
abbrev primeCompletedTerm (q : ℕ) : Type u :=
  CompletedTensor p (primeRing B p lam)
    (completedDividedPowerForms p A (primeDividedPowers B p lam hp) q) (primeCarrier B p lam M)

/-- **The level `pⁿ` of the completed canonical map `c_M^•` is the canonical map of the level
modules.**  For any family `c` with the characterising value on wedges of the canonical map of
[Stacks, Tag 07PY] for the level module `M_n`, the level `pⁿ` of
`Crystalline.CompletedDeRham.baseChangeTerm` is `c`. -/
theorem primeLevel_baseChangeTerm (n : ℕ)
    (c : ∀ q : ℕ,
      RestrictScalars A (B : Type u) (baseDeRhamTerm A B (levelModule p (B : Type u) M n) q) →ₗ[A]
        RestrictScalars A (primeRing B p lam)
          (primeDeRhamTerm A B p lam hp (levelModule p (B : Type u) M n) q))
    (hc_wedge : ∀ (q : ℕ) (m : levelModule p (B : Type u) M n) (omega : Fin q → (baseForms A B)),
      c q (m ⊗ₜ[(B : Type u)] exteriorPower.ιMulti (B : Type u) q omega) =
        (1 ⊗ₜ[(B : Type u)] m) ⊗ₜ[primeRing B p lam]
          exteriorPower.ιMulti (primeRing B p lam) q ((primeFormsComparison A B p lam hp) ∘ omega))
    (q : ℕ) (x : CompletedTensor p (B : Type u) (completedDividedPowerForms p A B.dividedPowers q)
        M) :
    TensorProduct.map (primeLevelModuleEquiv B p lam M n).toLinearMap LinearMap.id
        (formsLevelEquiv p A (primeRing B p lam) (primeDividedPowers B p lam hp)
          (primeCarrier B p lam M) q n
          ((CompletedDeRham.baseChangeTerm p (B : Type u) (primeRing B p lam) M
            (completedDividedPowerForms p A B.dividedPowers)
            (completedDividedPowerForms p A (primeDividedPowers B p lam hp))
            (primeCompletedFormsMap A B p lam hp) q x).val n)) =
      RestrictScalars.addEquiv A (primeRing B p lam) _
        (c q ((RestrictScalars.addEquiv A (B : Type u) _).symm
          (formsLevelEquiv p A (B : Type u) B.dividedPowers M q n (x.val n)))) := by
  have hg := levelTensorEquiv_adicQuotientMap_baseChangeTensor p n M
    (dividedPowerDifferentialForms (A := A) B.dividedPowers q)
    (dividedPowerDifferentialForms (A := A) (primeDividedPowers B p lam hp) q)
    (primeFormsMapₛₗ A B p lam hp q) (x.val n)
  refine hg.trans ?_
  have hext := tensorExteriorPower_addMonoidHom_ext
    (F := Connection.baseChangeValues (primeFormsMapₛₗ A B p lam hp q))
    (G := (RestrictScalars.addEquiv A (primeRing B p lam) _).toAddMonoidHom.comp
      ((c q).toAddMonoidHom.comp (RestrictScalars.addEquiv A (B : Type u) _).symm.toAddMonoidHom))
    (fun m v ↦ by
      refine (Connection.baseChangeValues_tmul _ _ _).trans ?_
      refine Eq.trans ?_ (congrArg (RestrictScalars.addEquiv A (primeRing B p lam) _)
        (hc_wedge q m v)).symm
      exact congrArg (((1 : primeRing B p lam) ⊗ₜ[(B : Type u)] m) ⊗ₜ[primeRing B p lam] ·)
        (primeFormsMapₛₗ_ιMulti A B p lam hp q v))
  exact DFunLike.congr_fun hext _

variable (S' : SourceDeRham A (primeRing B p lam))

/-- **The level `pⁿ` of the completed de Rham differential of `M' ⊗̂_{B'} Ω^•_{B'}` is the
extension to the de Rham complex of the base change of `∇_n`.** -/
theorem primeLevel_levelDifferential (q n : ℕ)
    (y : (primeCarrier B p lam M ⊗[primeRing B p lam]
        completedDividedPowerForms p A (primeDividedPowers B p lam hp) q) ⧸
      (pAdicIdeal (A := primeRing B p lam) p ^ n • ⊤ : Submodule (primeRing B p lam)
        (primeCarrier B p lam M ⊗[primeRing B p lam]
          completedDividedPowerForms p A (primeDividedPowers B p lam hp) q))) :
    TensorProduct.map (primeLevelModuleEquiv B p lam M n).toLinearMap LinearMap.id
        (formsLevelEquiv p A (primeRing B p lam) (primeDividedPowers B p lam hp)
          (primeCarrier B p lam M) (q + 1) n
          (CompletedDeRham.levelDifferential p (primeRing B p lam)
            (completedDividedPowerForms p A (primeDividedPowers B p lam hp))
            (completedDividedPowerWedgeOnRing p A (primeDividedPowers B p lam hp))
            (completedDividedPowerDeRham p A (primeDividedPowers B p lam hp))
            (primeCarrier B p lam M) (primeCompletedConnection A B p lam hp M nabla)
            (isGradedLeibniz_completedDividedPowerOnRing p A (primeDividedPowers B p lam hp))
            q n y)) =
      RestrictScalars.addEquiv A (primeRing B p lam) _
        ((primeExtended A B p lam hp (levelModule p (B : Type u) M n) S'
          (levelConnection p A (B : Type u) B.dividedPowers M nabla n)).toLinearMap q
          ((RestrictScalars.addEquiv A (primeRing B p lam) _).symm
            (TensorProduct.map (primeLevelModuleEquiv B p lam M n).toLinearMap LinearMap.id
              (formsLevelEquiv p A (primeRing B p lam) (primeDividedPowers B p lam hp)
                (primeCarrier B p lam M) q n y)))) := by
  have h1 := formsLevelEquiv_levelDifferential p A (primeRing B p lam)
    (primeDividedPowers B p lam hp) (primeCarrier B p lam M)
    (primeCompletedConnection A B p lam hp M nabla) S' q n y
  have h2 := extendedConnection_map S' (primeFormsProjection A B p lam hp)
    (Submodule.mkQ_surjective _) (primeFormsGenerationHypothesis A B p lam hp S')
    (primeLevelConnection A B p lam hp M nabla n)
    (baseChangedLevelConnection A B p lam hp M nabla n)
    (primeLevelModuleEquiv B p lam M n).toLinearMap
    (fun x ↦ (primeLevelConnection_horizontal A B p lam hp M nabla n x).symm) q
    (formsLevelEquiv p A (primeRing B p lam) (primeDividedPowers B p lam hp)
      (primeCarrier B p lam M) q n y)
  exact (congrArg (TensorProduct.map (primeLevelModuleEquiv B p lam M n).toLinearMap
    LinearMap.id) h1).trans h2.symm

end Target

end PthRootExtension

end Crystalline
