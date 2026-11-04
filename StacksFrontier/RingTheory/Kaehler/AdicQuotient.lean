module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Kaehler.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Differentials of `S / I^(n+1)` after reduction modulo `I^n`

Fix a ring map `R → S` of commutative rings, an ideal `I ⊆ S` and an integer `n ≥ 1`, and
set `S' = S / I^(n+1)`, an `R`-algebra via `R → S → S'`. The quotient map `π : S → S'`
induces the functoriality map on differentials `dπ : Ω[S/R] → Ω[S'/R]` with
`dπ(d s) = d(π s)`. Reducing both sides modulo `I^n` gives

`Φ : Ω[S/R] ⊗[S] (S/I^n) → Ω[S'/R] ⊗[S'] (S/I^n)`, `Φ(ω ⊗ s̄) = dπ(ω) ⊗ s̄`,

where `S/I^n` is an `S'`-module through the surjection `S' = S/I^(n+1) → S/I^n`, which is
well defined because `I^(n+1) ⊆ I^n`. Then `Φ` is an isomorphism. This is Stacks tag 02HQ
(Lemma 10.131.11). Throughout, `S' := S ⧸ I^(n+1)` and `Q := S ⧸ I^n`.

## Main definitions

* `algQuotPow`, `scalarTowerQuotPow`: the `S'`-algebra structure on `Q` and its
  compatibility with the `S`-action.
* `kaehlerReductionBilin`, `kaehlerReductionMap`: the map `Φ` and the `S`-bilinear map
  underlying it.
* `fwd1` / `bwd1` / `e1` and `e2fwd` / `e2bwd`: the scalar-repackaging maps that present
  `Φ` in terms of Mathlib's base-change map `KaehlerDifferential.mapBaseChange`.

## Main results

* `kaehlerReductionMap_surjective`: `Φ` is surjective, for every `n`. This needs only
  that `dπ` is surjective, which holds because `π` is (Stacks tag 00RR).
* `leibniz_pow_mem_aux`: the Leibniz estimate `D(I^(m+1)) ⊆ I^m · Ω[S/R]`.
* `conormal_rTensor_zero`: the conormal map of Stacks tag 00RU vanishes after base change
  to `Q`, which is exactly the Leibniz estimate read modulo `I^n`.
* `kaehlerReductionMap_injective`: `Φ` is injective. The conormal exact sequence
  `(J).Cotangent → S' ⊗[S] Ω[S/R] → Ω[S'/R] → 0` with `J = ker π = I^(n+1)` stays exact
  after tensoring with `Q`, and its left map becomes zero, so the middle map becomes
  injective; `Φ` is that map up to the repackagings `e1` and `e2fwd`.
* `kaehlerReductionMap_bijective` (Stacks tag 02HQ): `Φ` is bijective.

The statement is universally quantified over all `R`, `S`, `R`-algebra structures
`R → S`, ideals `I ⊆ S`, and integers `n ≥ 1`.
-/

@[expose] public section

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (I : Ideal S) (n : ℕ)

/-- The canonical `(S ⧸ I^(n+1))`-algebra structure on `S ⧸ I^n`, coming from the
quotient surjection `S ⧸ I^(n+1) → S ⧸ I^n` (well defined because
`I^(n+1) ≤ I^n`). This realizes `S/I^n` as an `S'`-module, where `S' = S/I^{n+1}`. -/
@[ega "0 19.5.6.2" "special case"]
noncomputable instance algQuotPow : Algebra (S ⧸ I ^ (n + 1)) (S ⧸ I ^ n) :=
  Ideal.Quotient.algebraQuotientOfLEComap (P := I ^ n) (p := I ^ (n + 1)) (by
    intro x hx
    rw [Ideal.mem_comap]
    exact Ideal.pow_le_pow_right (by omega) hx)

/-- The scalar actions of `S` on `S/I^n` directly and through `S' = S/I^{n+1}`
agree. -/
instance scalarTowerQuotPow : IsScalarTower S (S ⧸ I ^ (n + 1)) (S ⧸ I ^ n) := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  rfl

/-- The `S`-bilinear map underlying `Φ`: it sends `(ω, q)` to `dπ(ω) ⊗ q`, where
`dπ = KaehlerDifferential.map R R S (S ⧸ I^(n+1))` is the functoriality map for
the quotient `π : S → S ⧸ I^(n+1)`. The two `restrictScalars` reduce the
`(S ⧸ I^(n+1))`-bilinearity of the canonical tensor inclusion down to
`S`-bilinearity, so that it can be paired with the `S`-linear map `dπ`. -/
noncomputable def kaehlerReductionBilin :
    KaehlerDifferential R S →ₗ[S]
      (S ⧸ I ^ n) →ₗ[S]
        TensorProduct (S ⧸ I ^ (n + 1)) (KaehlerDifferential R (S ⧸ I ^ (n + 1))) (S ⧸ I ^ n) :=
  (LinearMap.restrictScalarsₗ S (S ⧸ I ^ (n + 1)) (S ⧸ I ^ n)
      (TensorProduct (S ⧸ I ^ (n + 1)) (KaehlerDifferential R (S ⧸ I ^ (n + 1))) (S ⧸ I ^ n)) S ∘ₗ
    ((TensorProduct.mk (S ⧸ I ^ (n + 1)) (KaehlerDifferential R (S ⧸ I ^ (n + 1)))
        (S ⧸ I ^ n)).restrictScalars S))
  ∘ₗ (KaehlerDifferential.map R R S (S ⧸ I ^ (n + 1)))

/-- The reduction-mod-`I^n` comparison map

  Φ : Ω[S/R] ⊗[S] (S/I^n) → Ω[S'/R] ⊗[S'] (S/I^n),

induced by the functoriality map `dπ : Ω[S/R] → Ω[S'/R]` of the quotient
`π : S → S' = S/I^{n+1}`. On simple tensors `Φ(ω ⊗ q) = dπ(ω) ⊗ q`. -/
noncomputable def kaehlerReductionMap :
    TensorProduct S (KaehlerDifferential R S) (S ⧸ I ^ n) →ₗ[S]
      TensorProduct (S ⧸ I ^ (n + 1)) (KaehlerDifferential R (S ⧸ I ^ (n + 1))) (S ⧸ I ^ n) :=
  TensorProduct.lift (kaehlerReductionBilin R S I n)

/-- `Φ` acts on simple tensors by `ω ⊗ q ↦ dπ(ω) ⊗ q`. -/
theorem kaehlerReductionMap_tmul (ω : KaehlerDifferential R S) (q : S ⧸ I ^ n) :
    kaehlerReductionMap R S I n (ω ⊗ₜ q) =
      (KaehlerDifferential.map R R S (S ⧸ I ^ (n + 1)) ω) ⊗ₜ[S ⧸ I ^ (n + 1)] q :=
  rfl

/-! ### Surjectivity and injectivity of `Φ`

Surjectivity holds for every `n`, and does not need `1 ≤ n`. Injectivity is where the
conormal exact sequence and the Leibniz estimate `d(I^(n+1)) ⊆ I^n · Ω[S/R]` enter.
-/

/-- `Φ` is surjective.

The target `Ω[S'/R] ⊗[S'] Q`, with `S' = S ⧸ I^(n+1)` and `Q = S ⧸ I^n`, is spanned by
simple tensors `η ⊗ₜ q`. The quotient map `S → S'` is surjective, hence so is the
functoriality map `dπ : Ω[S/R] → Ω[S'/R]` (Stacks tag 00RR), so each `η` is `dπ(ω)` for
some `ω : Ω[S/R]` and then `Φ(ω ⊗ₜ q) = η ⊗ₜ q`. Thus the range of `Φ` contains every
simple tensor and so is everything. -/
theorem kaehlerReductionMap_surjective :
    Function.Surjective (kaehlerReductionMap R S I n) := by
  intro y
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul η q =>
    obtain ⟨ω, rfl⟩ :=
      KaehlerDifferential.map_surjective_of_surjective R R S (S ⧸ I ^ (n + 1))
        Ideal.Quotient.mk_surjective η
    exact ⟨ω ⊗ₜ q, kaehlerReductionMap_tmul R S I n ω q⟩
  | add a b ha hb =>
    obtain ⟨x, rfl⟩ := ha
    obtain ⟨z, rfl⟩ := hb
    exact ⟨x + z, map_add _ _ _⟩

/-- Leibniz estimate: `D(I^(m+1)) ⊆ I^m · Ω[S/R]`. -/
lemma leibniz_pow_mem_aux :
    ∀ (m : ℕ) (x : S), x ∈ I ^ (m + 1) →
      KaehlerDifferential.D R S x ∈ (I ^ m) • (⊤ : Submodule S (KaehlerDifferential R S)) := by
  intro m
  induction m with
  | zero =>
    intro x hx
    simp
  | succ k ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      rw [Derivation.leibniz]
      apply Submodule.add_mem
      · exact Submodule.smul_mem_smul ha Submodule.mem_top
      · have hda := ih a ha
        have hpow : (I : Ideal S) ^ (k+1) = I * I^k := by rw [pow_succ, mul_comm]
        rw [hpow, Submodule.mul_smul]
        exact Submodule.smul_mem_smul hb hda
    · intro y z hy hz
      rw [map_add]
      exact Submodule.add_mem _ hy hz

open TensorProduct in
/-- Source repackaging `ω ⊗ q ↦ (1 ⊗ ω) ⊗ q`. -/
noncomputable def fwd1 : TensorProduct S (KaehlerDifferential R S) (S⧸I^n) →ₗ[S]
    TensorProduct S (TensorProduct S (S⧸I^(n+1)) (KaehlerDifferential R S)) (S⧸I^n) :=
  LinearMap.rTensor (S⧸I^n) ((TensorProduct.mk S (S⧸I^(n+1)) (KaehlerDifferential R S)) 1)

open TensorProduct in
/-- `fwd1` sends `ω ⊗ₜ q` to `(1 ⊗ₜ ω) ⊗ₜ q`. -/
@[simp] lemma fwd1_tmul (ω : KaehlerDifferential R S) (q : S ⧸ I ^ n) :
    fwd1 R S I n (ω ⊗ₜ q) = ((1:S⧸I^(n+1)) ⊗ₜ[S] ω) ⊗ₜ[S] q := by
  simp [fwd1, LinearMap.rTensor_tmul]

open TensorProduct in
/-- Inverse repackaging `(s' ⊗ ω) ⊗ q ↦ ω ⊗ (s' • q)`. -/
noncomputable def bwd1 :
    TensorProduct S (TensorProduct S (S⧸I^(n+1)) (KaehlerDifferential R S)) (S⧸I^n)
    →ₗ[S] TensorProduct S (KaehlerDifferential R S) (S⧸I^n) :=
  TensorProduct.lift
    (TensorProduct.lift
      { toFun := fun s' =>
          { toFun := fun ω =>
              { toFun := fun q => ω ⊗ₜ[S] (s' • q)
                map_add' := by intro x y; simp [smul_add, TensorProduct.tmul_add]
                map_smul' := by
                  intro c x; simp only [RingHom.id_apply]
                  rw [smul_comm s' c, TensorProduct.tmul_smul] }
            map_add' := by intro x y; ext; simp [TensorProduct.add_tmul]
            map_smul' := by intro c x; ext; simp [TensorProduct.smul_tmul'] }
        map_add' := by intro x y; ext ω; simp [add_smul, TensorProduct.tmul_add]
        map_smul' := by intro c x; ext ω; simp [smul_assoc, TensorProduct.tmul_smul] } )

open TensorProduct in
/-- `bwd1` sends `(s' ⊗ₜ ω) ⊗ₜ q` to `ω ⊗ₜ (s' • q)`. -/
@[simp] lemma bwd1_tmul (s' : S ⧸ I ^ (n + 1)) (ω : KaehlerDifferential R S) (q : S ⧸ I ^ n) :
    bwd1 R S I n ((s' ⊗ₜ[S] ω) ⊗ₜ[S] q) = ω ⊗ₜ[S] (s' • q) := by
  simp [bwd1]

/-- The class of `a : S` in `S ⧸ I^(n+1)` acts on any `S ⧸ I^(n+1)`-module like `a`. -/
private lemma quotient_mk_smul_eq {M : Type*} [AddCommMonoid M] [Module S M]
    [Module (S ⧸ I ^ (n + 1)) M] [IsScalarTower S (S ⧸ I ^ (n + 1)) M] (a : S) (m : M) :
    Ideal.Quotient.mk (I ^ (n + 1)) a • m = a • m :=
  algebraMap_smul _ _ _

open TensorProduct in
/-- Moving a scalar `s' : S ⧸ I^(n+1)` from the right factor to the left one inside
`(S/I^(n+1) ⊗[S] Ω[S/R]) ⊗[S] (S/I^n)`. -/
lemma fwdbwd_aux (s' : S ⧸ I ^ (n + 1)) (ω : KaehlerDifferential R S) (q : S ⧸ I ^ n) :
    ((((1:S⧸I^(n+1)) ⊗ₜ[S] ω) ⊗ₜ[S] (s' • q)) :
      TensorProduct S (TensorProduct S (S⧸I^(n+1)) (KaehlerDifferential R S)) (S⧸I^n))
      = (s' ⊗ₜ[S] ω) ⊗ₜ[S] q := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective s'
  have hmk : (Ideal.Quotient.mk (I^(n+1)) a) = a • (1 : S⧸I^(n+1)) := by
    rw [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]
  rw [quotient_mk_smul_eq, TensorProduct.tmul_smul, hmk, ← TensorProduct.smul_tmul',
    ← TensorProduct.smul_tmul']

open TensorProduct in
/-- The source repackaging `Ω[S/R] ⊗[S] (S/I^n) ≃ (S/I^(n+1) ⊗[S] Ω[S/R]) ⊗[S] (S/I^n)`,
given by `fwd1` with inverse `bwd1`. -/
noncomputable def e1 : TensorProduct S (KaehlerDifferential R S) (S⧸I^n) ≃ₗ[S]
    TensorProduct S (TensorProduct S (S⧸I^(n+1)) (KaehlerDifferential R S)) (S⧸I^n) :=
  LinearEquiv.ofLinearMap (fwd1 R S I n) (bwd1 R S I n)
    (by ext s' ω; simp [fwdbwd_aux])
    (by ext ω; simp)

open TensorProduct in
/-- The balanced relation in `Ω[S'/R] ⊗[S] Q`. -/
lemma e2_balanced (η : KaehlerDifferential R (S ⧸ I ^ (n + 1))) (c : S ⧸ I ^ (n + 1))
    (x : S ⧸ I ^ n) :
    (η ⊗ₜ[S] (c • x) : TensorProduct S (KaehlerDifferential R (S⧸I^(n+1))) (S⧸I^n))
      = c • (η ⊗ₜ[S] x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [quotient_mk_smul_eq, quotient_mk_smul_eq, TensorProduct.tmul_smul]

open TensorProduct in
/-- Target repackaging `η ⊗[S] q ↦ η ⊗[S'] q`. -/
noncomputable def e2fwd :
    TensorProduct S (KaehlerDifferential R (S⧸I^(n+1))) (S⧸I^n) →ₗ[S]
    TensorProduct (S⧸I^(n+1)) (KaehlerDifferential R (S⧸I^(n+1))) (S⧸I^n) :=
  TensorProduct.lift
    { toFun := fun η =>
        (TensorProduct.mk (S⧸I^(n+1))
          (KaehlerDifferential R (S⧸I^(n+1))) (S⧸I^n) η).restrictScalars S
      map_add' := by intro x y; ext; simp []
      map_smul' := by
        intro c x; ext
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
          TensorProduct.mk_apply, RingHom.id_apply, LinearMap.smul_apply,
          TensorProduct.smul_tmul'] }

open TensorProduct in
/-- `e2fwd` sends `η ⊗ₜ[S] q` to `η ⊗ₜ[S ⧸ I^(n+1)] q`. -/
@[simp] lemma e2fwd_tmul (η : KaehlerDifferential R (S ⧸ I ^ (n + 1))) (q : S ⧸ I ^ n) :
    e2fwd R S I n (η ⊗ₜ[S] q) = η ⊗ₜ[S⧸I^(n+1)] q := by simp [e2fwd]

set_option maxHeartbeats 800000 in
-- needed: `e2bwdBil`'s `map_smul'` field times out at `whnf`/`isDefEq` below 800000 heartbeats
-- while elaborating the `S ⧸ I^(n+1)`-bilinear tensor map.
open TensorProduct in
/-- The `S'`-bilinear map `(η, q) ↦ η ⊗ₜ[S] q` underlying `e2bwd`, where
`S' = S ⧸ I^(n+1)`; it is balanced by `e2_balanced`. -/
noncomputable def e2bwdBil :
    KaehlerDifferential R (S⧸I^(n+1)) →ₗ[S⧸I^(n+1)]
      (S⧸I^n) →ₗ[S⧸I^(n+1)] TensorProduct S (KaehlerDifferential R (S⧸I^(n+1))) (S⧸I^n) :=
  { toFun := fun η =>
      { toFun := fun q => η ⊗ₜ[S] q
        map_add' := fun x y => by simp [TensorProduct.tmul_add]
        map_smul' := fun c x => by simp only [RingHom.id_apply]; rw [e2_balanced] }
    map_add' := fun x y => by ext q; simp [TensorProduct.add_tmul]
    map_smul' := fun c x => by
      ext q
      simp only [RingHom.id_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply]
      rw [TensorProduct.smul_tmul'] }

open TensorProduct in
/-- Inverse target repackaging as an `S`-linear map. -/
noncomputable def e2bwd :
    TensorProduct (S⧸I^(n+1)) (KaehlerDifferential R (S⧸I^(n+1))) (S⧸I^n) →ₗ[S]
    TensorProduct S (KaehlerDifferential R (S⧸I^(n+1))) (S⧸I^n) :=
  (TensorProduct.lift (e2bwdBil R S I n)).restrictScalars S

open TensorProduct in
/-- `e2bwd` sends `η ⊗ₜ[S ⧸ I^(n+1)] q` to `η ⊗ₜ[S] q`. -/
@[simp] lemma e2bwd_tmul (η : KaehlerDifferential R (S ⧸ I ^ (n + 1))) (q : S ⧸ I ^ n) :
    e2bwd R S I n (η ⊗ₜ[S⧸I^(n+1)] q) = η ⊗ₜ[S] q := by simp [e2bwd, e2bwdBil]

open TensorProduct in
/-- `e2fwd` is injective, `e2bwd` being a left inverse. Injectivity is all that the
factorization of `Φ` needs from the target repackaging
`e2fwd : Ω[S'/R] ⊗[S] Q → Ω[S'/R] ⊗[S'] Q`, so the full `LinearEquiv` is not built: its
round-trip proofs over the `S'`-tensor elaborate very slowly with
`backward.isDefEq.respectTransparency` disabled. -/
lemma e2fwd_injective : Function.Injective (e2fwd R S I n) := by
  apply Function.LeftInverse.injective (g := e2bwd R S I n)
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul η q => rw [e2fwd_tmul, e2bwd_tmul]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

open TensorProduct in
/-- An element of `I^n · Ω[S/R]` dies after base change: for `ω ∈ I^n · Ω[S/R]`, the
element `(1 ⊗ₜ ω) ⊗ₜ q` of `(S/I^(n+1) ⊗[S] Ω[S/R]) ⊗[S] (S/I^n)` is zero, because the
scalar from `I^n` can be moved onto `q` where it acts as zero. -/
lemma elt_zero_conormal (q : S ⧸ I ^ n) (ω : KaehlerDifferential R S)
    (hω : ω ∈ (I ^ n) • (⊤ : Submodule S (KaehlerDifferential R S))) :
    (((1 : S ⧸ I^(n+1)) ⊗ₜ[S] ω) ⊗ₜ[S] q :
      TensorProduct S (TensorProduct S (S ⧸ I^(n+1)) (KaehlerDifferential R S)) (S ⧸ I^n)) = 0 := by
  refine Submodule.smul_induction_on hω ?_ ?_
  · intro a ha m _
    have h1 : ((1 : S ⧸ I^(n+1)) ⊗ₜ[S] (a • m) :
        TensorProduct S (S ⧸ I^(n+1)) (KaehlerDifferential R S))
        = a • ((1 : S ⧸ I^(n+1)) ⊗ₜ[S] m) := by rw [TensorProduct.tmul_smul]
    rw [h1, TensorProduct.smul_tmul]
    have h2 : a • q = 0 := by
      rw [Algebra.smul_def, mul_comm, Ideal.Quotient.algebraMap_eq,
        (Ideal.Quotient.eq_zero_iff_mem).mpr ha, mul_zero]
    rw [h2, TensorProduct.tmul_zero]
  · intro y z hy hz
    rw [TensorProduct.tmul_add, TensorProduct.add_tmul, hy, hz, add_zero]

-- needed: `conormal_rTensor_zero`'s `rw [LinearMap.rTensor_tmul]` only matches once defeq
-- unfolds `Ideal.Cotangent`'s `Quotient.mk` representation.
set_option backward.isDefEq.respectTransparency false in
open TensorProduct in
/-- The conormal map is zero after base change to `Q`. -/
lemma conormal_rTensor_zero :
    LinearMap.rTensor (S ⧸ I^n)
        (KaehlerDifferential.kerCotangentToTensor R S (S ⧸ I^(n+1))) = 0 := by
  apply TensorProduct.ext'
  intro c q
  obtain ⟨x, rfl⟩ := Quotient.exists_rep c
  rw [LinearMap.rTensor_tmul]
  rw [show (Quotient.mk _ x : (RingHom.ker (algebraMap S (S ⧸ I^(n+1)))).Cotangent)
        = (RingHom.ker (algebraMap S (S ⧸ I^(n+1)))).toCotangent x from rfl]
  rw [KaehlerDifferential.kerCotangentToTensor_toCotangent]
  simp only [LinearMap.zero_apply]
  apply elt_zero_conormal R S I n
  have hx : (x : S) ∈ I^(n+1) := by
    have hk : RingHom.ker (algebraMap S (S ⧸ I^(n+1))) = I^(n+1) := by
      rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
    exact hk.le x.property
  exact leibniz_pow_mem_aux R S I n (x : S) hx

/-- `Φ` is injective.

Write `S' = S ⧸ I^(n+1)`, `Q = S ⧸ I^n`, `π : S → S'` for the quotient map and
`J = ker π = I^(n+1)`. The conormal sequence of Stacks tag 00RU says that the base-change
map `mapBaseChange R S S' : S' ⊗[S] Ω[S/R] → Ω[S'/R]` has kernel the image of the conormal
map `(J).Cotangent → S' ⊗[S] Ω[S/R]`, which sends a class `[x]` to `1 ⊗ₜ D x`.

For `x ∈ I^(n+1)` the Leibniz rule gives `D x ∈ I^n · Ω[S/R]`, and `I^n · Ω[S/R]` is the
kernel of `Ω[S/R] ↠ Ω[S/R] ⊗[S] Q`. So every conormal generator dies after base change to
`Q`. Tensoring with `Q` is right exact and preserves the exactness here, so the middle map
becomes injective; since `Φ` is that map composed with the scalar repackagings `e1` and
`e2fwd`, it is injective too. -/
theorem kaehlerReductionMap_injective :
    Function.Injective (kaehlerReductionMap R S I n) := by
  classical
  -- The S-linear base-change map and its right tensor with Q = S ⧸ I^n.
  set g : TensorProduct S (S ⧸ I^(n+1)) (KaehlerDifferential R S) →ₗ[S]
      KaehlerDifferential R (S ⧸ I^(n+1)) :=
    (KaehlerDifferential.mapBaseChange R S (S ⧸ I^(n+1))).restrictScalars S with hg
  set rTg := LinearMap.rTensor (S ⧸ I^n) g with hrTg
  -- exactness of the conormal sequence base-changed by Q
  have hsurj : Function.Surjective ⇑g := by
    intro η
    obtain ⟨ω, rfl⟩ := KaehlerDifferential.map_surjective_of_surjective R R S (S ⧸ I^(n+1))
      Ideal.Quotient.mk_surjective η
    exact ⟨(1 : S ⧸ I^(n+1)) ⊗ₜ[S] ω, by
      rw [hg, LinearMap.restrictScalars_apply, KaehlerDifferential.mapBaseChange_tmul, one_smul]⟩
  have hexact :
      Function.Exact
        ⇑(LinearMap.rTensor (S ⧸ I^n) (KaehlerDifferential.kerCotangentToTensor R S (S ⧸ I^(n+1))))
        ⇑rTg :=
    rTensor_exact (S ⧸ I^n)
      (KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R S (S ⧸ I^(n+1))
        Ideal.Quotient.mk_surjective) hsurj
  -- rTg is injective since the conormal map is zero after base change
  have hrTg_inj : Function.Injective ⇑rTg := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨m, rfl⟩ := (hexact a).mp ha
    rw [conormal_rTensor_zero R S I n, LinearMap.zero_apply]
  -- the comparison map factors as e2fwd ∘ rTg ∘ e1
  have hcomm : kaehlerReductionMap R S I n
      = (e2fwd R S I n) ∘ₗ rTg ∘ₗ (e1 R S I n).toLinearMap := by
    apply TensorProduct.ext'
    intro ω q
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    rw [kaehlerReductionMap_tmul]
    show _ = e2fwd R S I n (rTg (e1 R S I n (ω ⊗ₜ q)))
    have he1 : e1 R S I n (ω ⊗ₜ q) = ((1 : S ⧸ I^(n+1)) ⊗ₜ[S] ω) ⊗ₜ[S] q := by
      simp only [e1, LinearEquiv.coe_ofLinearMap, fwd1_tmul]
    rw [he1, hrTg, LinearMap.rTensor_tmul, hg, LinearMap.restrictScalars_apply,
      KaehlerDifferential.mapBaseChange_tmul, one_smul]
    simp only [e2fwd_tmul]
  rw [hcomm]
  exact (e2fwd_injective R S I n).comp (hrTg_inj.comp (e1 R S I n).injective)

/-- **Stacks Tag 02HQ (Lemma 10.131.11).**
For a ring map `R → S`, an ideal `I ⊆ S`, and an integer `n ≥ 1`, with
`S' = S/I^{n+1}`, the comparison map

  Φ : Ω[S/R] ⊗[S] (S/I^n) → Ω[S'/R] ⊗[S'] (S/I^n)

induced by the functoriality map `dπ : Ω[S/R] → Ω[S'/R]` is bijective (an
isomorphism). -/
@[stacks 02HQ]
theorem kaehlerReductionMap_bijective :
    Function.Bijective (kaehlerReductionMap R S I n) :=
  ⟨kaehlerReductionMap_injective R S I n, kaehlerReductionMap_surjective R S I n⟩
