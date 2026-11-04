module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalPairFunctor07JG
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelFormsCompleted
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelRingDividedPowers

/-!
# The reduction of `Ω_D` and of `M ⊗̂_D Ω_D` to the levels, for [Stacks, Tag 07JG]

In the situation of `...SmallSite.crystalPairFunctor` (the functor of [Stacks, Tag 07JG]),
`D` is the `p`-adically completed divided power envelope of the presentation (equation (07J8)),
`Ω_D` its completed module of divided power differentials (07J9), `d : D → Ω_D` the derivation
(07JA), and `T_e` the levels of the system of [Stacks, Tag 07JN], with section rings
`D_e = Γ(T_e, 𝒪) = D/p^{N+e} D`.  This module constructs the reduction `Ω_D → Ω_{D_e}` of the
differentials to the differentials `Γ(T_e, Ω_{T_e/S,δ})` of a level, which by [Stacks, Tag 07IZ]
and [Stacks, Tag 07J0] is `Ω_{D_e,δ}`, and the induced reduction
`M ⊗̂_D Ω_D → Ω_{D_e} ⊗ Γ(T_e, ℱ)` of the target of the connection of a crystal, and computes
the connection at each level.

## Main definitions

* `...SmallSite.pairLevelForms` — the differentials `Ω_{D_e}` of the level, as a `D`-module.
* `...SmallSite.pairFormsLevel` — **the reduction `Ω_D → Ω_{D_e}`.**
* `...SmallSite.pairLevelTensor` — `Ω_{D_e} ⊗_{D_e} Γ(T_e, ℱ)`, as a `D`-module.
* `...SmallSite.pairTensorLevel` — **the reduction `M ⊗̂_D Ω_D → Ω_{D_e} ⊗ Γ(T_e, ℱ)`.**

## Main results

* `...SmallSite.pairFormsLevel_pairDerivation` — the reduction carries `d` to the universal
  derivation of the level, which characterises it.
* `...SmallSite.pairFormsLevel_pairDx` — the reduction of `d x_c`.
* `...SmallSite.pairTensorLevel_toCompletedTensor_tmul` — the reduction on pure tensors.
* `...SmallSite.pairTensorLevel_pairConnection` — **the level-`e` readout of the connection**:
  `∇ m` reduces to `-∑_c d x_c ⊗ θ_c(m_e)`.
* `Crystalline.eval_completedConnection_ofLevels` — the general form of the last statement: the
  connection assembled from coordinate data at the levels is, at the step `N + n` of the `p`-adic
  filtration, the finite sum `∑_{c ∈ s} (-θ_c m) ⊗ d x_c` for any `s` containing the support at
  the level `n`.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
* [Stacks Project, Tag 07IZ](https://stacks.math.columbia.edu/tag/07IZ)
* [Stacks Project, Tag 07J0](https://stacks.math.columbia.edu/tag/07J0)
* [Stacks Project, Proposition 60.21.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry Simplicial
open scoped TensorProduct

universe u w uI

noncomputable section

namespace Crystalline

/-- The image in the completion of an element of the divided power ideal lies in the completed
ideal. -/
theorem of_mem_completionIdeal {A : Type*} [CommRing A] (I : Ideal A)
    (p : ℕ) (hp : IsNilpotent (Ideal.Quotient.mk I (p : A))) {x : A} (hx : x ∈ I) :
    AdicCompletion.of (DividedPowers.pAdicIdeal (A := A) p) A x ∈
      DividedPowers.completionIdeal I p hp := by
  show DividedPowers.completionToQuotient I p hp _ = 0
  simpa [DividedPowers.completionToQuotient] using Ideal.Quotient.eq_zero_iff_mem.mpr hx

section LevelEval

variable {A : Type u} [CommRing A] {D : DividedPowerRing.{u}} {g : A →+* D} {Omega : Type u}
  [AddCommGroup Omega] [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
  {d : DividedPowerDerivation A D g Omega} {p : ℕ}
  (M₀ : Type w) [AddCommGroup M₀] [Module (D : Type u) M₀]
  (lev : ℕ → Type w) [∀ n, AddCommGroup (lev n)] [∀ n, Module (D : Type u) (lev n)]
  (trans : ∀ n, lev (n + 1) →ₗ[(D : Type u)] lev n) (N : ℕ)
  (r : ∀ n, M₀ →ₗ[(D : Type u)] lev n)
  (hsurj : ∀ n, Function.Surjective (r n))
  (hker : ∀ n, LinearMap.ker (r n) =
    DividedPowers.pAdicIdeal (A := (D : Type u)) p ^ (N + n) •
      (⊤ : Submodule (D : Type u) M₀))
  (hcomp : ∀ n, trans n ∘ₗ r (n + 1) = r n)

include hsurj hker in
/-- Two elements of the completed base change with the same readout at the level `n` agree at
the step `N + n` of the `p`-adic filtration. -/
theorem eval_add_eq_of_completedLevelProj_eq {z z' : CompletedFirstOrderTensor D Omega p M₀}
    (n : ℕ) (h : completedLevelProj M₀ lev N r hsurj hker n z =
      completedLevelProj M₀ lev N r hsurj hker n z') :
    AdicCompletion.eval _ _ (N + n) z = AdicCompletion.eval _ _ (N + n) z' := by
  rw [AdicCompletion.eval_apply, AdicCompletion.eval_apply]
  exact (shiftedLevelQuot_bijective (DividedPowers.pAdicIdeal (A := (D : Type u)) p)
      (firstOrderExtension D Omega ⊗[D] M₀) (fun n ↦ firstOrderExtension D Omega ⊗[D] lev n) N
      (tensorLevelProj (firstOrderExtension D Omega) M₀ lev r)
      (ker_tensorLevelProj (firstOrderExtension D Omega) M₀ lev N r hsurj hker)
      (tensorLevelProj_surjective (firstOrderExtension D Omega) M₀ lev r hsurj) n).1 h

variable {ι : Type uI} (dx : ι → Omega) (θlev : ∀ n, lev n →+ (ι →₀ lev n))
  (hleib : ∀ n (a : (D : Type u)) (x : lev n), ∃ δ : ι →₀ (D : Type u),
    (∀ c, θlev n (a • x) c = a • θlev n x c + δ c • x) ∧
    (TrivSqZeroExt.inr (d a) : firstOrderExtension D Omega) ⊗ₜ[D] x =
      -δ.sum fun c b ↦ (TrivSqZeroExt.inr (dx c) : firstOrderExtension D Omega) ⊗ₜ (b • x))
  (hnat : ∀ n (x : lev (n + 1)),
    θlev n (trans n x) = (θlev (n + 1) x).mapRange (trans n) (map_zero _))
  (θ : ι → M₀ → M₀) (hθ : ∀ n c m, r n (θ c m) = θlev n (r n m) c)

include hsurj hker hcomp hθ in
/-- **The assembled connection at the step `N + n` of the filtration** is the finite sum
`∑_{c ∈ s} (-θ_c(m)) ⊗ d x_c`, for any finite `s` containing the support of the first-order
coefficients of the reduction of `m` to the level `n`. -/
theorem eval_completedConnection_ofLevels (m : M₀) (n : ℕ) (s : Finset ι)
    (hs : (θlev n (r n m)).support ⊆ s) :
    AdicCompletion.eval _ _ (N + n)
      ((CompletedFirstOrderComparison.ofLevels M₀ lev trans N r hsurj hker hcomp
        (fun n ↦ coordinateComparison D Omega d dx (θlev n) (hleib n))
        (fun n x ↦ lTensor_coordinateComparisonFun D Omega dx (θlev (n + 1)) (θlev n) (trans n)
          (hnat n) x)).completedConnection m) =
      AdicCompletion.eval _ _ (N + n)
        (toCompletedTensor p (D : Type u) Omega M₀ (∑ c ∈ s, (-θ c m) ⊗ₜ[D] dx c)) := by
  classical
  let w : firstOrderExtension D Omega ⊗[D] M₀ := (1 : firstOrderExtension D Omega) ⊗ₜ m -
    ∑ c ∈ s, (TrivSqZeroExt.inr (dx c) : firstOrderExtension D Omega) ⊗ₜ θ c m
  have hw : toCompletedTensor p (D : Type u) Omega M₀ (∑ c ∈ s, (-θ c m) ⊗ₜ[D] dx c) =
      AdicCompletion.map (DividedPowers.pAdicIdeal (A := (D : Type u)) p)
        (firstOrderDifferentialComm D Omega M₀)
        (AdicCompletion.of (DividedPowers.pAdicIdeal (A := (D : Type u)) p) _ w) := by
    rw [AdicCompletion.map_of]
    congr 1
    simp only [w, map_sub, map_sum, firstOrderDifferentialComm_tmul, TrivSqZeroExt.snd_one,
      TrivSqZeroExt.snd_inr, TensorProduct.tmul_zero, zero_sub, TensorProduct.neg_tmul,
      Finset.sum_neg_distrib]
  rw [hw]
  have hlev : completedLevelProj M₀ lev N r hsurj hker n
      (AdicCompletion.of (DividedPowers.pAdicIdeal (A := (D : Type u)) p) _ w) =
      completedLevelProj M₀ lev N r hsurj hker n
        (completedLevelComparisonFun M₀ lev trans N r hsurj hker hcomp
          (fun n ↦ coordinateComparison D Omega d dx (θlev n) (hleib n))
          (fun n x ↦ lTensor_coordinateComparisonFun D Omega dx (θlev (n + 1)) (θlev n)
            (trans n) (hnat n) x) m) := by
    refine Eq.trans ?_ (completedLevelProj_completedLevelComparisonFun M₀ lev trans N r hsurj hker
      hcomp _ _ m n).symm
    rw [completedLevelProj_of, coordinateComparison_apply,
      coordinateComparisonFun_eq D Omega dx _ _ s hs]
    simp only [w, tensorLevelProj, map_sub, map_sum, LinearMap.lTensor_tmul, hθ]
  have he := eval_add_eq_of_completedLevelProj_eq M₀ lev N r hsurj hker n hlev
  rw [AdicCompletion.eval_apply, AdicCompletion.eval_apply] at he
  show AdicCompletion.eval _ _ (N + n)
    (AdicCompletion.map _ (firstOrderDifferentialComm D Omega M₀)
      (completedLevelComparisonFun M₀ lev trans N r hsurj hker hcomp
          (fun n ↦ coordinateComparison D Omega d dx (θlev n) (hleib n))
          (fun n x ↦ lTensor_coordinateComparisonFun D Omega dx (θlev (n + 1)) (θlev n)
            (trans n) (hnat n) x) m)) = _
  rw [AdicCompletion.eval_apply, AdicCompletion.eval_apply, AdicCompletion.map_val_apply,
    AdicCompletion.map_val_apply, he]

end LevelEval

end Crystalline

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [WholeSpacePresentation S hp]

/-- If `p ^ k` kills a module over `R`, then `(p) ^ k` annihilates it. -/
private theorem pAdicIdeal_pow_smul_top_eq_bot {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (p k : ℕ) (h : ∀ w : M, p ^ k • w = 0) :
    DividedPowers.pAdicIdeal (A := R) p ^ k • (⊤ : Submodule R M) = ⊥ := by
  refine le_antisymm (fun x hx ↦ ?_) bot_le
  refine Submodule.smul_induction_on hx (fun a ha y _ ↦ ?_) (fun y z hy hz ↦ ?_)
  · rw [DividedPowers.pAdicIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [Submodule.mem_bot, mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    exact h _
  · exact Submodule.add_mem _ hy hz

section LevelForms

variable (e : ℕ)

/-- **The differentials `Ω_{D_e} = Γ(T_e, Ω_{T_e/S,δ})` of the level `e`**, as a `D`-module through
the reduction `D → Γ(T_e, 𝒪)`. -/
def pairLevelForms : Type u := crysDiffSections (levelObj hp 0 e).obj

/-- The additive group of the differentials of the level. -/
instance : AddCommGroup (pairLevelForms hp e) :=
  inferInstanceAs (AddCommGroup (crysDiffSections (levelObj hp 0 e).obj))

/-- `D` acts on the differentials of the level through the reduction `D → Γ(T_e, 𝒪)`. -/
instance pairLevelFormsModule : Module (pairRing hp) (pairLevelForms hp e) :=
  Module.compHom (crysDiffSections (levelObj hp 0 e).obj) (pairLss hp e)

/-- The envelope `E(0)` acts on the differentials of the level through its reduction
`E(0) → Γ(T_e, 𝒪)`. -/
instance pairLevelFormsEnvModule : Module (wsEnvelope hp 0 : Type u) (pairLevelForms hp e) :=
  Module.compHom (crysDiffSections (levelObj hp 0 e).obj) (envLevelMap hp 0 e)

/-- `D` acts on the differentials of the level through the reduction `D → Γ(T_e, 𝒪)`. -/
theorem pairLevelForms_smul (a : pairRing hp) (w : pairLevelForms hp e) :
    a • w = (show pairLevelForms hp e from
      pairLss hp e a • (show crysDiffSections (levelObj hp 0 e).obj from w)) :=
  rfl

/-- `E(0)` acts on the differentials of the level through the reduction `E(0) → Γ(T_e, 𝒪)`. -/
theorem pairLevelForms_envSmul (y : wsEnvelope hp 0) (w : pairLevelForms hp e) :
    y • w = (show pairLevelForms hp e from
      envLevelMap hp 0 e y • (show crysDiffSections (levelObj hp 0 e).obj from w)) :=
  rfl

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- **The map `E(0) → D` to the completion is a divided power morphism**: the divided powers of
`D` extend those of `E(0)` ([Stacks, Tag 07KD]). -/
theorem isDPMorphism_wsCompletionMap_pairRing :
    DividedPowers.IsDPMorphism (wsEnvelope hp 0).dividedPowers (pairRing hp).dividedPowers
      (wsCompletionMap hp 0) := by
  have hmem : ∀ x ∈ (wsEnvelope hp 0).ideal, wsCompletionMap hp 0 x ∈ (pairRing hp).ideal := by
    intro x hx
    exact _root_.Crystalline.of_mem_completionIdeal _ _ _ hx
  refine ⟨Ideal.map_le_iff_le_comap.mpr hmem, fun {n} x hx ↦ ?_⟩
  exact (DividedPowers.completedDividedPowers _ _ _ _).2 n x hx ⟨_, hmem x hx⟩ rfl

/-- **The reduction `E(0) → Γ(T_e, 𝒪)` is a divided power morphism.** -/
theorem isDPMorphism_envLevelMap_zero :
    DividedPowers.IsDPMorphism (wsEnvelope hp 0).dividedPowers
      (crysDividedPowers S (levelObj hp 0 e).obj) (envLevelMap hp 0 e) := by
  have h2 : DividedPowers.IsDPMorphism (wholeSpaceEnvelopeDPRing hp 0).dividedPowers
      (DividedPowers.quotientDividedPowers (wholeSpaceEnvelopeDPRing hp 0).ideal
        (wholeSpaceEnvelopeDPRing hp 0).dividedPowers (affineSituation S hp).p
        (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)
        (isPAdicLevel_wholeSpaceEnvelopeDPRing hp 0 e).1
        (isPAdicLevel_wholeSpaceEnvelopeDPRing hp 0 e).2)
      (Ideal.Quotient.mk _) :=
    DividedPowers.Quotient.isDPMorphism _ (by
      rw [inf_eq_left.mpr (isPAdicLevel_wholeSpaceEnvelopeDPRing hp 0 e).1]
      exact (isPAdicLevel_wholeSpaceEnvelopeDPRing hp 0 e).2)
  exact (isDPMorphism_wholeSpaceEnvelopeRingLevelEquiv_symm hp 0 e).comp _
    (h2.comp _ (isDPMorphism_wsCompletionMap_pairRing hp))

/-- **The reduction `E(0) → Γ(T_e, 𝒪)` is one of `Γ(S, 𝒪_S)`-algebras**: it carries the structure
map of the envelope to the map on global sections of `T_e → S`. -/
theorem envLevelMap_algebraMap (a : ((affineSituation S hp).A : Type u)) :
    letI := wsEnvelopeAlgebra hp
    envLevelMap hp 0 e (algebraMap _ (wsEnvelope hp 0 : Type u) a) =
      crysBaseAppLE S (levelObj hp 0 e).obj a := by
  let := wsEnvelopeAlgebra hp
  refine Eq.trans ?_ ((wholeSpaceEnvelopeRingLevelEquiv hp 0 e).symm_apply_apply _)
  refine congrArg (wholeSpaceEnvelopeRingLevelEquiv hp 0 e).symm ?_
  exact (wholeSpaceEnvelopeRingLevelEquiv_crysBaseAppLE hp 0 e a).symm

/-- The derivation of the level on the envelope, `y ↦ d(y_e)`: the universal divided power
derivation of `T_e` precomposed with the reduction `E(0) → Γ(T_e, 𝒪)`. -/
def envLevelDerivationFun (y : (wsEnvelope hp 0 : Type u)) : pairLevelForms hp e :=
  crysDerivation (levelObj hp 0 e).obj (envLevelMap hp 0 e y)

/-- The derivation of the level is additive. -/
theorem envLevelDerivationFun_add (x y : (wsEnvelope hp 0 : Type u)) :
    envLevelDerivationFun hp e (x + y) =
      envLevelDerivationFun hp e x + envLevelDerivationFun hp e y := by
  show crysDerivation (levelObj hp 0 e).obj (envLevelMap hp 0 e (x + y)) = _
  rw [map_add]
  exact sheafApp_add _ _ _ ⊤ _ _

/-- The Leibniz rule for the derivation of the level, `E(0)` acting through its reduction. -/
theorem envLevelDerivationFun_mul (x y : (wsEnvelope hp 0 : Type u)) :
    envLevelDerivationFun hp e (x * y) =
      x • envLevelDerivationFun hp e y + y • envLevelDerivationFun hp e x := by
  have h : crysDerivation (levelObj hp 0 e).obj (envLevelMap hp 0 e (x * y)) =
      envLevelMap hp 0 e x • crysDerivation (levelObj hp 0 e).obj (envLevelMap hp 0 e y) +
        envLevelMap hp 0 e y • crysDerivation (levelObj hp 0 e).obj (envLevelMap hp 0 e x) := by
    rw [map_mul]
    exact sheafApp_mul _ _ _ ⊤ _ _
  exact h

/-- The divided power chain rule for the derivation of the level, transported along the
divided power morphism `E(0) → Γ(T_e, 𝒪)`. -/
theorem envLevelDerivationFun_dpow (k : ℕ) (x : (wsEnvelope hp 0 : Type u))
    (hx : x ∈ (wsEnvelope hp 0).ideal) :
    envLevelDerivationFun hp e ((wsEnvelope hp 0).dividedPowers.dpow (k + 1) x) =
      (wsEnvelope hp 0).dividedPowers.dpow k x • envLevelDerivationFun hp e x := by
  have hdp := isDPMorphism_envLevelMap_zero hp e
  have hmem : envLevelMap hp 0 e x ∈
      (levelObj hp 0 e).obj.thickening.target.ideal.obj (op ⊤) :=
    hdp.ideal_comp (Ideal.mem_map_of_mem (envLevelMap hp 0 e) hx)
  have hc1 : (crysDividedPowers S (levelObj hp 0 e).obj).dpow (k + 1) (envLevelMap hp 0 e x) =
      envLevelMap hp 0 e ((wsEnvelope hp 0).dividedPowers.dpow (k + 1) x) :=
    hdp.dpow_comp x hx
  have hc2 : (crysDividedPowers S (levelObj hp 0 e).obj).dpow k (envLevelMap hp 0 e x) =
      envLevelMap hp 0 e ((wsEnvelope hp 0).dividedPowers.dpow k x) :=
    hdp.dpow_comp x hx
  have h : crysDerivation (levelObj hp 0 e).obj
        (envLevelMap hp 0 e ((wsEnvelope hp 0).dividedPowers.dpow (k + 1) x)) =
      envLevelMap hp 0 e ((wsEnvelope hp 0).dividedPowers.dpow k x) •
        crysDerivation (levelObj hp 0 e).obj (envLevelMap hp 0 e x) := by
    rw [← hc1, ← hc2]
    exact sheafApp_dpow _ _ _ ⊤ k _ hmem
  exact h

/-- The derivation of the level kills the image of the base `A = Γ(S, 𝒪_S)`. -/
theorem envLevelDerivationFun_algebraMap (a : ((affineSituation S hp).A : Type u)) :
    letI := wsEnvelopeAlgebra hp
    envLevelDerivationFun hp e (algebraMap _ (wsEnvelope hp 0 : Type u) a) = 0 := by
  let := wsEnvelopeAlgebra hp
  show crysDerivation (levelObj hp 0 e).obj _ = 0
  rw [envLevelMap_algebraMap]
  exact sheafApp_base _ _ _ ⊤ (appLE_mem_baseSections _ _ _ ⊤ ⊤ _ a)

/-- **The divided power derivation `E(0) → Ω_{D_e}` of the level**, `y ↦ d(y_e)`. -/
def envLevelDerivation :
    letI := wsEnvelopeAlgebra hp
    DividedPowerDerivation ((affineSituation S hp).A : Type u) (wsEnvelope hp 0)
      (algebraMap _ (wsEnvelope hp 0 : Type u)) (pairLevelForms hp e) :=
  letI := wsEnvelopeAlgebra hp
  { toDerivation := Derivation.mk'
      (AddMonoidHom.toIntLinearMap
        (AddMonoidHom.mk' (envLevelDerivationFun hp e) (envLevelDerivationFun_add hp e)))
      (envLevelDerivationFun_mul hp e)
    map_ringHom' := envLevelDerivationFun_algebraMap hp e
    map_dpow' := fun n hn x hx ↦ by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      exact envLevelDerivationFun_dpow hp e k x hx }

/-- **The reduction `Ω_{E(0)} → Ω_{D_e}`** of the uncompleted divided power differentials of the
envelope: the factorisation of `...SmallSite.envLevelDerivation` through the universal divided
power derivation ([Stacks, Tag 07HZ]). -/
def envFormsLevel :
    letI := wsEnvelopeAlgebra hp
    dividedPowerDifferentials (A := ((affineSituation S hp).A : Type u))
        (wsEnvelope hp 0).dividedPowers →ₗ[(wsEnvelope hp 0 : Type u)] pairLevelForms hp e :=
  letI := wsEnvelopeAlgebra hp
  (dividedPowerDifferentials_lift (wsEnvelope hp 0) (envLevelDerivation hp e)).choose

/-- The reduction `Ω_{E(0)} → Ω_{D_e}` sends `d y` to the differential of the reduction of `y`. -/
theorem envFormsLevel_dividedPowerDifferential (y : (wsEnvelope hp 0 : Type u)) :
    letI := wsEnvelopeAlgebra hp
    envFormsLevel hp e (dividedPowerDifferential (A := ((affineSituation S hp).A : Type u))
      (wsEnvelope hp 0).dividedPowers y) =
      crysDerivation (levelObj hp 0 e).obj (envLevelMap hp 0 e y) :=
  let := wsEnvelopeAlgebra hp
  (dividedPowerDifferentials_lift (wsEnvelope hp 0) (envLevelDerivation hp e)).choose_spec.1 y

/-- `p^{N+e}` kills the differentials of the level. -/
theorem nsmul_pairLevelForms (w : pairLevelForms hp e) :
    (S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)) • w = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (wsEnvelope hp 0 : Type u), pairLevelForms_envSmul,
    envLevelMap_pow, zero_smul]
  rfl

/-- The ideal `(p)^{N+e}` of `E(0)` annihilates the differentials of the level. -/
theorem pow_smul_top_pairLevelForms_eq_bot :
    DividedPowers.pAdicIdeal (A := (wsEnvelope hp 0 : Type u)) (affineSituation S hp).p ^
        (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) •
      (⊤ : Submodule (wsEnvelope hp 0 : Type u) (pairLevelForms hp e)) = ⊥ := by
  exact pAdicIdeal_pow_smul_top_eq_bot _ _ (nsmul_pairLevelForms hp e)

/-- The reduction `Ω_D → Ω_{D_e}` as an `E(0)`-linear map: `...SmallSite.envFormsLevel` extended to
the `p`-adic completion through the cutoff `N + e`. -/
def pairFormsLevelFun : pairForms hp →ₗ[(wsEnvelope hp 0 : Type u)] pairLevelForms hp e :=
  _root_.Crystalline.completionLift _
    (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) (envFormsLevel hp e)
    (pow_smul_top_pairLevelForms_eq_bot hp e)

/-- The extension to the completion agrees with `Ω_{E(0)} → Ω_{D_e}` on the image of `Ω_{E(0)}`. -/
theorem pairFormsLevelFun_of (x : letI := wsEnvelopeAlgebra hp
    dividedPowerDifferentials (A := ((affineSituation S hp).A : Type u))
      (wsEnvelope hp 0).dividedPowers) :
    pairFormsLevelFun hp e (AdicCompletion.of _ _ x) = envFormsLevel hp e x :=
  _root_.Crystalline.completionLift_of _ _ _ _ x

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- The image of `y ∈ E(0)` in `D` acts on `Ω_D` as `y` itself. -/
theorem pairOf_smul_pairForms (y : (wsEnvelope hp 0 : Type u)) (w : pairForms hp) :
    pairOf hp y • w = y • w :=
  algebraMap_smul _ y w

/-- The reduction kills `p^{N+e} Ω_D`. -/
theorem pairFormsLevelFun_pow_smul (w : pairForms hp) :
    pairFormsLevelFun hp e
      (((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) : ℕ) :
        pairRing hp) • w) = 0 := by
  rw [Nat.cast_smul_eq_nsmul, map_nsmul]
  exact nsmul_pairLevelForms hp e _

/-- **The reduction `Ω_D → Ω_{D_e}` is `D`-linear.** -/
theorem pairFormsLevelFun_smul (a : pairRing hp) (w : pairForms hp) :
    pairFormsLevelFun hp e (a • w) = a • pairFormsLevelFun hp e w := by
  obtain ⟨y, hy⟩ := surjective_envLevelMap hp 0 e (pairLss hp e a)
  obtain ⟨t, ht⟩ :=
    exists_eq_add_of_pairLss_eq hp e (hy.symm.trans (pairLss_pairOf hp e y).symm)
  have h1 : a • w = y • w +
      ((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) : ℕ) :
        pairRing hp) • (t • w) :=
    (congrArg (· • w) ht).trans ((add_smul _ _ w).trans
      (congrArg₂ (· + ·) (pairOf_smul_pairForms hp y w) (mul_smul _ _ w)))
  have h2 : pairFormsLevelFun hp e (a • w) = y • pairFormsLevelFun hp e w :=
    (congrArg (pairFormsLevelFun hp e) h1).trans (((pairFormsLevelFun hp e).map_add _ _).trans
      ((congrArg₂ (· + ·) ((pairFormsLevelFun hp e).map_smul y w)
        (pairFormsLevelFun_pow_smul hp e (t • w))).trans (add_zero _)))
  refine h2.trans ?_
  show (show pairLevelForms hp e from envLevelMap hp 0 e y •
      (show crysDiffSections (levelObj hp 0 e).obj from pairFormsLevelFun hp e w)) =
    (show pairLevelForms hp e from pairLss hp e a •
      (show crysDiffSections (levelObj hp 0 e).obj from pairFormsLevelFun hp e w))
  rw [hy]

/-- **The reduction `Ω_D → Ω_{D_e}` of the completed differentials to the differentials of the
level `e`**, `D`-linearly.  It is characterised by `...SmallSite.pairFormsLevel_pairDerivation`. -/
def pairFormsLevel : pairForms hp →ₗ[pairRing hp] pairLevelForms hp e where
  toFun := pairFormsLevelFun hp e
  map_add' := map_add _
  map_smul' := pairFormsLevelFun_smul hp e

/-- The reduction `Ω_D → Ω_{D_e}` is its `E(0)`-linear underlying map. -/
theorem pairFormsLevel_apply (w : pairForms hp) :
    pairFormsLevel hp e w = pairFormsLevelFun hp e w := rfl

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- `d(p^{N+e} t) = p^{N+e} d t`. -/
theorem pairDerivation_pow_mul (t : pairRing hp) :
    pairDerivation hp
      (((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) : ℕ) :
        pairRing hp) * t) =
      ((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) : ℕ) :
        pairRing hp) • pairDerivation hp t := by
  have hp0 : pairDerivation hp
      ((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) : ℕ) : pairRing hp) =
      0 := by
    rw [← map_natCast (algebraMap ((affineSituation S hp).A : Type u)
      (pAdicCompletedTensorPowerEnvelope (affineSituation S hp)
        (wholeSpacePresentation S hp)
        (wholeSpacePresentation_surjective S hp) 0))]
    exact (pairDerivation hp).map_ringHom _
  have h1 := (pairDerivation hp).leibniz
    (((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) : ℕ) :
      pairRing hp)) t
  rw [hp0, smul_zero, add_zero] at h1
  exact h1

/-- **The reduction carries `d` to the universal derivation of the level**: `(d a)_e = d(a_e)`. -/
theorem pairFormsLevel_pairDerivation (a : pairRing hp) :
    pairFormsLevel hp e (pairDerivation hp a) =
      crysDerivation (levelObj hp 0 e).obj (pairLss hp e a) := by
  obtain ⟨y, hy⟩ := surjective_envLevelMap hp 0 e (pairLss hp e a)
  obtain ⟨t, ht⟩ :=
    exists_eq_add_of_pairLss_eq hp e (hy.symm.trans (pairLss_pairOf hp e y).symm)
  have h0 := tensorPowerDerivation_of (affineSituation S hp)
    (wholeSpacePresentation S hp)
    (wholeSpacePresentation_surjective S hp) 0 y
  have h1 : pairDerivation hp a = AdicCompletion.of _ _
      (let := wsEnvelopeAlgebra hp
       dividedPowerDifferential (A := ((affineSituation S hp).A : Type u))
        (wsEnvelope hp 0).dividedPowers y) +
      ((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) : ℕ) :
        pairRing hp) • pairDerivation hp t := by
    rw [ht, (pairDerivation hp).map_add, pairDerivation_pow_mul]
    exact congrArg (· + _) h0
  rw [pairFormsLevel_apply, h1, map_add, pairFormsLevelFun_pow_smul, add_zero,
    pairFormsLevelFun_of, envFormsLevel_dividedPowerDifferential, hy]

/-- **The reduction of `d x_c`** is the differential of the reduction of `x_c`. -/
theorem pairFormsLevel_pairDx (c : wholeSpaceIndex S hp) :
    pairFormsLevel hp e (pairDx hp c) =
      crysDerivation (levelObj hp 0 e).obj (envLevelMap hp 0 e
        ((tensorPowerEnvelope (affineSituation S hp)
          (wholeSpacePresentation S hp) 0).algebraMap.toRingHom
            (MvPolynomial.X ((0 : Fin 1), c)))) :=
  pairFormsLevel_pairDerivation hp e _

end LevelForms

section LevelTensor

variable (Fc : QuasiCoherentCrystal S) (e : ℕ)

/-- **The tensor product `Ω_{D_e} ⊗_{D_e} Γ(T_e, ℱ)`**, as a `D`-module through the reduction
`D → Γ(T_e, 𝒪)`. -/
def pairLevelTensor : Type u :=
  crysDiffSections (levelObj hp 0 e).obj ⊗[crysSheafRing S (levelObj hp 0 e).obj]
    Fc.obj.val.obj (op (levelObj hp 0 e))

/-- The additive group of `Ω_{D_e} ⊗ Γ(T_e, ℱ)`. -/
instance : AddCommGroup (pairLevelTensor hp Fc e) :=
  inferInstanceAs (AddCommGroup (crysDiffSections (levelObj hp 0 e).obj ⊗[crysSheafRing S
    (levelObj hp 0 e).obj] Fc.obj.val.obj (op (levelObj hp 0 e))))

/-- `D` acts on `Ω_{D_e} ⊗ Γ(T_e, ℱ)` through the reduction `D → Γ(T_e, 𝒪)`. -/
instance pairLevelTensorModule : Module (pairRing hp) (pairLevelTensor hp Fc e) :=
  Module.compHom (crysDiffSections (levelObj hp 0 e).obj ⊗[crysSheafRing S
    (levelObj hp 0 e).obj] Fc.obj.val.obj (op (levelObj hp 0 e))) (pairLss hp e)

/-- The pure tensor `ω ⊗ x`, as an element of `...SmallSite.pairLevelTensor`. -/
abbrev pairLevelTmul (ω : crysDiffSections (levelObj hp 0 e).obj)
    (x : Fc.obj.val.obj (op (levelObj hp 0 e))) : pairLevelTensor hp Fc e :=
  ω ⊗ₜ[crysSheafRing S (levelObj hp 0 e).obj] x

/-- `p^{N+e}` vanishes in `Γ(T_e, 𝒪)`. -/
theorem pairLss_natCast_pow :
    pairLss hp e
      ((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) : ℕ) :
        pairRing hp) = 0 := by
  rw [map_natCast, ← map_natCast (envLevelMap hp 0 e), envLevelMap_pow]

/-- `p^{N+e}` kills `Ω_{D_e} ⊗ Γ(T_e, ℱ)`. -/
theorem nsmul_pairLevelTensor (z : pairLevelTensor hp Fc e) :
    (S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)) • z = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (pairRing hp)]
  show pairLss hp e _ • (show crysDiffSections (levelObj hp 0 e).obj ⊗[crysSheafRing S
    (levelObj hp 0 e).obj] Fc.obj.val.obj (op (levelObj hp 0 e)) from z) = 0
  rw [pairLss_natCast_pow, zero_smul]

/-- The ideal `(p)^{N+e}` of `D` annihilates `Ω_{D_e} ⊗ Γ(T_e, ℱ)`. -/
theorem pow_smul_top_pairLevelTensor_eq_bot :
    DividedPowers.pAdicIdeal (A := (pairRing hp : Type u)) S.p ^
        (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) •
      (⊤ : Submodule (pairRing hp) (pairLevelTensor hp Fc e)) = ⊥ := by
  exact pAdicIdeal_pow_smul_top_eq_bot _ _ (nsmul_pairLevelTensor hp Fc e)

/-- Pure tensors are additive in the second factor. -/
theorem pairLevelTmul_add_right (ω : crysDiffSections (levelObj hp 0 e).obj)
    (x y : Fc.obj.val.obj (op (levelObj hp 0 e))) :
    pairLevelTmul hp Fc e ω (x + y) = pairLevelTmul hp Fc e ω x + pairLevelTmul hp Fc e ω y :=
  TensorProduct.tmul_add ω x y

/-- Pure tensors are additive in the first factor. -/
theorem pairLevelTmul_add_left (ω ω' : crysDiffSections (levelObj hp 0 e).obj)
    (x : Fc.obj.val.obj (op (levelObj hp 0 e))) :
    pairLevelTmul hp Fc e (ω + ω') x = pairLevelTmul hp Fc e ω x + pairLevelTmul hp Fc e ω' x :=
  TensorProduct.add_tmul ω ω' x

/-- Scalars of `D` move out of the second factor through their reduction. -/
theorem pairLevelTmul_smul_right (a : pairRing hp) (ω : crysDiffSections (levelObj hp 0 e).obj)
    (x : Fc.obj.val.obj (op (levelObj hp 0 e))) :
    pairLevelTmul hp Fc e ω (pairLss hp e a • x) = a • pairLevelTmul hp Fc e ω x :=
  TensorProduct.tmul_smul (pairLss hp e a) ω x

/-- Scalars of `D` move out of the first factor through their reduction. -/
theorem pairLevelTmul_smul_left (a : pairRing hp) (ω : crysDiffSections (levelObj hp 0 e).obj)
    (x : Fc.obj.val.obj (op (levelObj hp 0 e))) :
    pairLevelTmul hp Fc e (pairLss hp e a • ω) x = a • pairLevelTmul hp Fc e ω x :=
  TensorProduct.smul_tmul' (pairLss hp e a) ω x

/-- The map `(m, ω) ↦ ω_e ⊗ m_e`. -/
def pairTensorLevelBilFun (m : wholeSpaceSections hp Fc ⦋0⦌) (ω : pairForms hp) :
    pairLevelTensor hp Fc e :=
  pairLevelTmul hp Fc e (pairFormsLevel hp e ω) (pairComponent hp Fc e m)

/-- The map `(m, ω) ↦ ω_e ⊗ m_e` is additive in `m`. -/
theorem pairTensorLevelBilFun_add_left (m m' : wholeSpaceSections hp Fc ⦋0⦌)
    (ω : pairForms hp) :
    pairTensorLevelBilFun hp Fc e (m + m') ω =
      pairTensorLevelBilFun hp Fc e m ω + pairTensorLevelBilFun hp Fc e m' ω :=
  (congrArg (pairLevelTmul hp Fc e (pairFormsLevel hp e ω))
    ((pairComponent hp Fc e).map_add m m')).trans
    (pairLevelTmul_add_right hp Fc e _ (pairComponent hp Fc e m) (pairComponent hp Fc e m'))

/-- The map `(m, ω) ↦ ω_e ⊗ m_e` is `D`-linear in `m`. -/
theorem pairTensorLevelBilFun_smul_left (a : pairRing hp) (m : wholeSpaceSections hp Fc ⦋0⦌)
    (ω : pairForms hp) :
    pairTensorLevelBilFun hp Fc e (a • m) ω = a • pairTensorLevelBilFun hp Fc e m ω :=
  (congrArg (pairLevelTmul hp Fc e (pairFormsLevel hp e ω))
    ((pairComponent hp Fc e).map_smul a m)).trans
    (pairLevelTmul_smul_right hp Fc e a _ (pairComponent hp Fc e m))

/-- The map `(m, ω) ↦ ω_e ⊗ m_e` is additive in `ω`. -/
theorem pairTensorLevelBilFun_add_right (m : wholeSpaceSections hp Fc ⦋0⦌)
    (ω ω' : pairForms hp) :
    pairTensorLevelBilFun hp Fc e m (ω + ω') =
      pairTensorLevelBilFun hp Fc e m ω + pairTensorLevelBilFun hp Fc e m ω' :=
  (congrArg (fun z ↦ pairLevelTmul hp Fc e z (pairComponent hp Fc e m))
    ((pairFormsLevel hp e).map_add ω ω')).trans
    (pairLevelTmul_add_left hp Fc e (pairFormsLevel hp e ω) (pairFormsLevel hp e ω') _)

/-- The map `(m, ω) ↦ ω_e ⊗ m_e` is `D`-linear in `ω`. -/
theorem pairTensorLevelBilFun_smul_right (a : pairRing hp) (m : wholeSpaceSections hp Fc ⦋0⦌)
    (ω : pairForms hp) :
    pairTensorLevelBilFun hp Fc e m (a • ω) = a • pairTensorLevelBilFun hp Fc e m ω :=
  (congrArg (fun z ↦ pairLevelTmul hp Fc e z (pairComponent hp Fc e m))
    ((pairFormsLevel hp e).map_smul a ω)).trans
    (pairLevelTmul_smul_left hp Fc e a (pairFormsLevel hp e ω) _)

/-- The bilinear map `(m, ω) ↦ ω_e ⊗ m_e`. -/
def pairTensorLevelBil :
    wholeSpaceSections hp Fc ⦋0⦌ →ₗ[pairRing hp] pairForms hp →ₗ[pairRing hp]
      pairLevelTensor hp Fc e :=
  LinearMap.mk₂ (pairRing hp) (pairTensorLevelBilFun hp Fc e)
    (pairTensorLevelBilFun_add_left hp Fc e) (pairTensorLevelBilFun_smul_left hp Fc e)
    (pairTensorLevelBilFun_add_right hp Fc e) (pairTensorLevelBilFun_smul_right hp Fc e)

/-- The reduction `M ⊗_D Ω_D → Ω_{D_e} ⊗ Γ(T_e, ℱ)`. -/
def pairTensorLevelFun :
    wholeSpaceSections hp Fc ⦋0⦌ ⊗[pairRing hp] pairForms hp →ₗ[pairRing hp]
      pairLevelTensor hp Fc e :=
  TensorProduct.lift (pairTensorLevelBil hp Fc e)

/-- **The reduction `M ⊗̂_D Ω_D → Ω_{D_e} ⊗ Γ(T_e, ℱ)`** of the target of the connection to the
level `e`: the completion of `m ⊗ ω ↦ ω_e ⊗ m_e`, cut off at `p^{N+e}`. -/
def pairTensorLevel :
    CompletedTensor S.p (pairRing hp) (pairForms hp) (wholeSpaceSections hp Fc ⦋0⦌)
      →ₗ[pairRing hp] pairLevelTensor hp Fc e :=
  _root_.Crystalline.completionLift _
    (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) (pairTensorLevelFun hp Fc e)
    (pow_smul_top_pairLevelTensor_eq_bot hp Fc e)

/-- The reduction of `M ⊗̂_D Ω_D` agrees with the uncompleted one on the image of `M ⊗_D Ω_D`. -/
theorem pairTensorLevel_toCompletedTensor (z : wholeSpaceSections hp Fc ⦋0⦌ ⊗[pairRing hp]
    pairForms hp) :
    pairTensorLevel hp Fc e (toCompletedTensor S.p (pairRing hp) (pairForms hp) _ z) =
      pairTensorLevelFun hp Fc e z :=
  _root_.Crystalline.completionLift_of _ _ _ _ z

/-- **The reduction on a pure tensor**: `m ⊗ ω ↦ ω_e ⊗ m_e`. -/
theorem pairTensorLevel_toCompletedTensor_tmul (m : wholeSpaceSections hp Fc ⦋0⦌)
    (ω : pairForms hp) :
    pairTensorLevel hp Fc e (toCompletedTensor S.p (pairRing hp) (pairForms hp) _ (m ⊗ₜ ω)) =
      pairLevelTmul hp Fc e (pairFormsLevel hp e ω) (pairComponent hp Fc e m) :=
  (pairTensorLevel_toCompletedTensor hp Fc e _).trans
    (TensorProduct.lift.tmul (f' := pairTensorLevelBil hp Fc e) m ω)

end LevelTensor

section Connection

variable (Fc : QuasiCoherentCrystal S) (e : ℕ)

/-- **The connection at the step `N + e` of the filtration** is the finite sum
`∑_{c ∈ T} (-θ_c(m)) ⊗ d x_c`, for any finite `T` outside which the first-order Taylor
coefficients of `m_e` vanish. -/
theorem eval_pairConnection (m : wholeSpaceSections hp Fc ⦋0⦌)
    (T : Finset (wholeSpaceIndex S hp))
    (hT : ∀ c ∉ T, levelTheta hp Fc e (Finsupp.single c 1) (pairComponent hp Fc e m) = 0) :
    AdicCompletion.eval _ _ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)
        (pairConnection hp Fc m) =
      AdicCompletion.eval _ _ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)
        (toCompletedTensor S.p (pairRing hp) (pairForms hp) (wholeSpaceSections hp Fc ⦋0⦌)
          (∑ c ∈ T, (-crystalTheta hp Fc (Finsupp.single c 1) m) ⊗ₜ[pairRing hp]
            pairDx hp c)) :=
  _root_.Crystalline.eval_completedConnection_ofLevels (wholeSpaceSections hp Fc ⦋0⦌)
    (pairLevel hp Fc) (pairRestrict hp Fc)
    (_root_.Crystalline.uniformLevel (affineSituation S hp))
    (pairComponent hp Fc) (surjective_pairComponent hp Fc) (ker_pairComponent hp Fc)
    (pairRestrict_comp_pairComponent hp Fc) (pairDx hp) (pairFirstOrderHom hp Fc)
    (pairLevel_leibniz hp Fc) (pairFirstOrderHom_pairRestrict hp Fc)
    (fun c m ↦ crystalTheta hp Fc (Finsupp.single c 1) m) (fun _ _ _ ↦ rfl) m e T
    (fun c hc ↦ by_contra fun h ↦ Finsupp.mem_support_iff.mp hc (hT c h))

/-- `...SmallSite.pairTensorLevel_pairConnection`, with the pure tensors written through
`...SmallSite.pairLevelTmul`. -/
theorem pairTensorLevel_pairConnection_aux (m : wholeSpaceSections hp Fc ⦋0⦌)
    (T : Finset (wholeSpaceIndex S hp))
    (hT : ∀ c ∉ T, levelTheta hp Fc e (Finsupp.single c 1) (pairComponent hp Fc e m) = 0) :
    pairTensorLevel hp Fc e (pairConnection hp Fc m) =
      -∑ c ∈ T, pairLevelTmul hp Fc e
        (crysDerivation (levelObj hp 0 e).obj (envLevelMap hp 0 e
          ((tensorPowerEnvelope (affineSituation S hp)
            (wholeSpacePresentation S hp) 0).algebraMap.toRingHom
              (MvPolynomial.X ((0 : Fin 1), c)))))
        (levelTheta hp Fc e (Finsupp.single c 1) (pairComponent hp Fc e m)) := by
  have h1 : pairTensorLevel hp Fc e (pairConnection hp Fc m) =
      pairTensorLevel hp Fc e
        (toCompletedTensor S.p (pairRing hp) (pairForms hp) (wholeSpaceSections hp Fc ⦋0⦌)
          (∑ c ∈ T, (-crystalTheta hp Fc (Finsupp.single c 1) m) ⊗ₜ[pairRing hp]
            pairDx hp c)) :=
    congrArg (_root_.Crystalline.quotLift _ _ (pairTensorLevelFun hp Fc e)
      (pow_smul_top_pairLevelTensor_eq_bot hp Fc e)) (eval_pairConnection hp Fc e m T hT)
  refine h1.trans ((pairTensorLevel_toCompletedTensor hp Fc e _).trans ?_)
  rw [map_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  refine (TensorProduct.lift.tmul (f' := pairTensorLevelBil hp Fc e) _ _).trans ?_
  show pairLevelTmul hp Fc e (pairFormsLevel hp e (pairDx hp c))
      (pairComponent hp Fc e (-crystalTheta hp Fc (Finsupp.single c 1) m)) = _
  rw [pairFormsLevel_pairDx, map_neg]
  exact TensorProduct.tmul_neg _ _

/-- **The level-`e` readout of the connection**: the reduction of `∇ m ∈ M ⊗̂_D Ω_D` to
`Ω_{D_e} ⊗ Γ(T_e, ℱ)` is `-∑_c d x_c ⊗ θ_c(m_e)`, the sum over any finite set of coordinates
outside which the first-order Taylor coefficients of `m_e` vanish. -/
theorem pairTensorLevel_pairConnection (m : wholeSpaceSections hp Fc ⦋0⦌)
    (T : Finset (wholeSpaceIndex S hp))
    (hT : ∀ c ∉ T, levelTheta hp Fc e (Finsupp.single c 1) (pairComponent hp Fc e m) = 0) :
    pairTensorLevel hp Fc e (pairConnection hp Fc m) =
      (show pairLevelTensor hp Fc e from -∑ c ∈ T,
        crysDerivation (levelObj hp 0 e).obj (envLevelMap hp 0 e
          ((tensorPowerEnvelope (affineSituation S hp)
            (wholeSpacePresentation S hp) 0).algebraMap.toRingHom
              (MvPolynomial.X ((0 : Fin 1), c)))) ⊗ₜ[crysSheafRing S (levelObj hp 0 e).obj]
          levelTheta hp Fc e (Finsupp.single c 1) (pairComponent hp Fc e m)) :=
  pairTensorLevel_pairConnection_aux hp Fc e m T hT

end Connection

end Crystalline.GlobalCrystallineSituation.SmallSite

end
