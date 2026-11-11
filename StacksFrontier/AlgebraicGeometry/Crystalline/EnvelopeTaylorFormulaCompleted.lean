module

public import StacksFrontier.AlgebraicGeometry.Crystalline.EnvelopeTaylorFormula
public import StacksFrontier.AlgebraicGeometry.Crystalline.ThetaMonomialFamily

/-!
# Taylor's formula on the completed divided power envelope

Let `E = D_{P,γ}(J)` be the divided power envelope of a polynomial presentation
`P = A[x_i : i ∈ ι] ⊇ J`, with `ι` finite, and let `D` be its `p`-adic completion, the ring of
[Stacks, Lemma 60.17.5, Tag 07L5], with universal differential `d : D → Ω̂^1_D`.
`StacksFrontier/AlgebraicGeometry/Crystalline/EnvelopeTaylorFormula.lean` proves Taylor's formula
for `E` with the Taylor operators `θ_K` and `δ_i = θ_{e_i}`.  This file carries it to `D`.

## Main results

* `Crystalline.envelopeCompletionFormsDifferential_inclusion` — `d(a) = ∑_i δ_i(a) d x_i` for
  `a ∈ E`, read in `D`.
* `Crystalline.envelopeCompletionDelta` — for a basis of `Ω̂^1_D` on the `d x_i`, the
  coordinates `δ̂_i(x)` of `d x`; they extend the `δ_i` of `E`
  (`Crystalline.envelopeCompletionDelta_inclusion`), are additive divided power derivations
  killing `A` (`..._mul`, `..._algebraMap`, `..._dpow`) and commute
  (`Crystalline.envelopeCompletionDelta_comm`).
* `Crystalline.envelopeCompletionDeltaPow` — their composites `δ̂_K`, extending the `θ_K`
  (`Crystalline.envelopeCompletionDeltaPow_inclusion`).
* `Crystalline.envelopeCompletion_taylor_levels` — **Taylor's formula at the levels**: for a
  divided power endomorphism `ρ` of `D` over `A` compatible with the augmentation, with
  `ξ_i = x_i - ρ(x_i)`, every `a ∈ D` satisfies, modulo `p^n D`,
  `a ≡ ∑_K ρ(δ̂_K a) ξ^{[K]}` and `ρ(a) ≡ ∑_K δ̂_K(a) (-ξ)^{[K]}`, over a finite set outside which
  `δ̂_K a ∈ p^n D`.

## References

* [Stacks Project, Tag 07L5](https://stacks.math.columbia.edu/tag/07L5)
-/

@[expose] public noncomputable section

namespace Crystalline

open DividedPowers

universe u

attribute [local instance] dpMorphismRingHomClass

/-! ### The `p`-adic filtration -/

section PAdic

/-- **An additive map preserves the `p`-adic filtration**: `f(p^n z) = p^n f(z)`. -/
theorem map_mem_pAdicIdeal_pow {R S : Type*} [CommRing R] [CommRing S] (p n : ℕ) (f : R →+ S)
    {x : R} (hx : x ∈ pAdicIdeal (A := R) p ^ n) : f x ∈ pAdicIdeal (A := S) p ^ n := by
  rw [pAdicIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hx ⊢
  obtain ⟨a, rfl⟩ := hx
  refine ⟨f a, ?_⟩
  have h1 : a * (p : R) ^ n = (p ^ n : ℕ) • a := by rw [nsmul_eq_mul, Nat.cast_pow, mul_comm]
  rw [h1, map_nsmul, nsmul_eq_mul, Nat.cast_pow, mul_comm]

/-- **A `p`-adically separated ring has no nonzero element in every `p^n R`.** -/
theorem eq_zero_of_forall_mem_pAdicIdeal_pow {R : Type*} [CommRing R] (p : ℕ)
    [IsHausdorff (pAdicIdeal (A := R) p) R] {x : R} (h : ∀ n, x ∈ pAdicIdeal (A := R) p ^ n) :
    x = 0 :=
  IsHausdorff.haus' (I := pAdicIdeal (A := R) p) x fun n => by
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    exact h n

end PAdic

/-- An induction principle for multi-indices, adding one unit at a time. -/
theorem finsupp_induction_single {ι : Type*} [DecidableEq ι] {P : (ι →₀ ℕ) → Prop}
    (h0 : P 0) (hstep : ∀ K i, P K → P (K + Finsupp.single i 1)) (K : ι →₀ ℕ) : P K := by
  refine Finsupp.induction K h0 fun i n K _ _ ih => ?_
  have key : ∀ m : ℕ, P (Finsupp.single i m + K) := by
    intro m
    induction m with
    | zero => simpa using ih
    | succ m ihm =>
      have h := hstep _ i ihm
      rwa [add_right_comm, ← Finsupp.single_add] at h
  exact key n

section Completed

variable {A : DividedPowerRing.{u}} {ι : Type u} [Fintype ι] [DecidableEq ι]
  {J : Ideal (MvPolynomial ι A)} {hJ : A.ideal.map (algebraMap A (MvPolynomial ι A)) ≤ J}
  (E : DividedPowerEnvelope A (algebraMap A (MvPolynomial ι A)) J hJ) (p : ℕ)
  (hp : IsNilpotent (Ideal.Quotient.mk E.object.ideal (p : E.object)))

/-! ### `E` is dense in `D` -/

omit [Fintype ι] [DecidableEq ι] in
/-- **Every element of `D` agrees with an element of `E` modulo `p^n D`.** -/
theorem exists_sub_envelopeCompletionInclusion_mem (x : envelopeCompletion E p hp) (n : ℕ) :
    ∃ a₀ : E.object, x - envelopeCompletionInclusion E p hp a₀ ∈
      pAdicIdeal (A := (envelopeCompletion E p hp : Type u)) p ^ n := by
  obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective _
    (AdicCompletion.eval (pAdicIdeal (A := (E.object : Type u)) p) (E.object : Type u) n x)
  refine ⟨r, ?_⟩
  have hker : (show AdicCompletion (pAdicIdeal (A := (E.object : Type u)) p) (E.object : Type u)
      from x) - AdicCompletion.of (pAdicIdeal (A := (E.object : Type u)) p)
      (E.object : Type u) r ∈
      (AdicCompletion.eval (pAdicIdeal (A := (E.object : Type u)) p) (E.object : Type u)
        n).ker := by
    rw [LinearMap.mem_ker, map_sub, AdicCompletion.eval_of, ← hr, Submodule.mkQ_apply, sub_self]
  rw [← AdicCompletion.pow_smul_top_eq_ker_eval (pAdicIdeal_fg p), Ideal.smul_top_eq_map,
    Ideal.map_pow, pAdicIdeal_map] at hker
  exact hker

omit [Fintype ι] [DecidableEq ι] in
/-- **Two additive self-maps of `D` agreeing on `E` are equal**, since `E` is dense in the
`p`-adically separated ring `D` and additive maps preserve the `p`-adic filtration. -/
theorem envelopeCompletion_addMonoidHom_ext
    (f g : envelopeCompletion E p hp →+ envelopeCompletion E p hp)
    (h : ∀ a, f (envelopeCompletionInclusion E p hp a) = g (envelopeCompletionInclusion E p hp a)) :
    f = g := by
  refine AddMonoidHom.ext fun x => sub_eq_zero.mp ?_
  refine eq_zero_of_forall_mem_pAdicIdeal_pow p fun n => ?_
  obtain ⟨a₀, ha₀⟩ := exists_sub_envelopeCompletionInclusion_mem E p hp x n
  have hx : x = envelopeCompletionInclusion E p hp a₀ +
      (x - envelopeCompletionInclusion E p hp a₀) := (add_sub_cancel _ _).symm
  have key : f x - g x = (f - g) (x - envelopeCompletionInclusion E p hp a₀) := by
    conv_lhs => rw [hx]
    rw [map_add, map_add, h, AddMonoidHom.sub_apply]
    abel
  rw [key]
  exact map_mem_pAdicIdeal_pow p n (f - g) ha₀

/-! ### The universal differential of `D` as a divided power derivation -/

omit [Fintype ι] [DecidableEq ι] in
/-- `d` kills the image of `A`. -/
theorem envelopeCompletionFormsDifferential_algebraMap (r : A) :
    envelopeCompletionFormsDifferential E p hp
      (algebraMap (A : Type u) (envelopeCompletion E p hp) r) = 0 := by
  show completedDividedPowerDifferentialOnRing p (A : Type u) _ _ = 0
  rw [completedDividedPowerDifferentialOnRing_eq, dividedPowerOneForm_apply]
  have h : dividedPowerDifferential (A := (A : Type u)) (envelopeCompletion E p hp).dividedPowers
      (algebraMap (A : Type u) (envelopeCompletion E p hp) r) = 0 := by
    rw [dividedPowerDifferential, Derivation.map_algebraMap, map_zero]
  rw [h, map_zero, map_zero]

omit [Fintype ι] [DecidableEq ι] in
/-- **The divided power chain rule for `d`**: `d(γ_n x) = γ_{n-1}(x) d x` for `x` in the divided
power ideal of `D` and `n > 0`. -/
theorem envelopeCompletionFormsDifferential_dpow {n : ℕ} (hn : 0 < n)
    {x : envelopeCompletion E p hp} (hx : x ∈ (envelopeCompletion E p hp).ideal) :
    envelopeCompletionFormsDifferential E p hp
        ((envelopeCompletion E p hp).dividedPowers.dpow n x) =
      (envelopeCompletion E p hp).dividedPowers.dpow (n - 1) x •
        envelopeCompletionFormsDifferential E p hp x := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  show completedDividedPowerDifferentialOnRing p (A : Type u) _ _ =
    _ • completedDividedPowerDifferentialOnRing p (A : Type u) _ _
  rw [completedDividedPowerDifferentialOnRing_eq, completedDividedPowerDifferentialOnRing_eq,
    dividedPowerOneForm_apply, dividedPowerOneForm_apply, Nat.add_sub_cancel]
  have h : dividedPowerDifferential (A := (A : Type u)) (envelopeCompletion E p hp).dividedPowers
      ((envelopeCompletion E p hp).dividedPowers.dpow (k + 1) x) =
      (envelopeCompletion E p hp).dividedPowers.dpow k x •
        dividedPowerDifferential (A := (A : Type u)) (envelopeCompletion E p hp).dividedPowers x :=
    dividedPowerDifferential_dpow (A := (A : Type u)) _ ⟨x, hx⟩ k
  rw [h, map_smul, map_smul]

omit [Fintype ι] [DecidableEq ι] in
/-- **`d : D → Ω̂^1_D` as a divided power derivation over `A`.** -/
def envelopeCompletionFormsDerivation :
    DividedPowerDerivation (A : Type u) (envelopeCompletion E p hp)
      (envelopeCompletionStructureMap E p hp).toRingHom (envelopeCompletionForms E p hp 1) where
  toDerivation := Derivation.mk'
    (AddMonoidHom.mk' (envelopeCompletionFormsDifferential E p hp)
      (envelopeCompletionFormsDifferential_add E p hp)).toIntLinearMap
    (envelopeCompletionFormsDifferential_mul E p hp)
  map_ringHom' r := envelopeCompletionFormsDifferential_algebraMap E p hp r
  map_dpow' _ hn _ hx := envelopeCompletionFormsDifferential_dpow E p hp hn hx

/-- **`d a = ∑_i δ_i(a) d x_i` for `a ∈ E`**, read in `D`: the derivation
`Crystalline.envelopeTaylor_derivation` of the envelope applied to `d` composed with `E → D`. -/
theorem envelopeCompletionFormsDifferential_inclusion (a : E.object) :
    envelopeCompletionFormsDifferential E p hp (envelopeCompletionInclusion E p hp a) =
      ∑ i, envelopeCompletionInclusion E p hp (envelopeDelta E i a) •
        envelopeCompletionFormsDifferential E p hp (envelopeCompletionCoord E p hp i) :=
  envelopeTaylor_derivation E (envelopeCompletion E p hp) (envelopeCompletionInclusion E p hp)
    (envelopeCompletionForms E p hp 1) (envelopeCompletionFormsDerivation E p hp) a

/-! ### The coordinate derivations `δ̂_i` of `D` -/

variable (bas : Module.Basis ι (envelopeCompletion E p hp) (envelopeCompletionForms E p hp 1))

/-- **The coordinate derivation `δ̂_i : D → D`** of a basis of `Ω̂^1_D`: `δ̂_i(x)` is the `i`-th
coordinate of `d x`. -/
def envelopeCompletionDelta (i : ι) : envelopeCompletion E p hp →+ envelopeCompletion E p hp :=
  (Finsupp.lapply (R := (envelopeCompletion E p hp : Type u)) i).toAddMonoidHom.comp
    (bas.repr.toAddMonoidHom.comp (AddMonoidHom.mk' (envelopeCompletionFormsDifferential E p hp)
      (envelopeCompletionFormsDifferential_add E p hp)))

omit [Fintype ι] [DecidableEq ι] in
/-- `δ̂_i(x)` is the `i`-th coordinate of `d x`. -/
theorem envelopeCompletionDelta_apply (i : ι) (x : envelopeCompletion E p hp) :
    envelopeCompletionDelta E p hp bas i x =
      bas.repr (envelopeCompletionFormsDifferential E p hp x) i :=
  rfl

/-- **`δ̂_i` extends `δ_i`**, for a basis on the `d x_i`. -/
theorem envelopeCompletionDelta_inclusion
    (hbas : ∀ i, bas i =
      envelopeCompletionFormsDifferential E p hp (envelopeCompletionCoord E p hp i))
    (i : ι) (a : E.object) :
    envelopeCompletionDelta E p hp bas i (envelopeCompletionInclusion E p hp a) =
      envelopeCompletionInclusion E p hp (envelopeDelta E i a) := by
  rw [envelopeCompletionDelta_apply, envelopeCompletionFormsDifferential_inclusion]
  simp_rw [← hbas]
  simp [map_sum, Finsupp.single_apply]

omit [Fintype ι] [DecidableEq ι] in
/-- **The Leibniz rule** `δ̂_i(x y) = x δ̂_i(y) + y δ̂_i(x)`. -/
theorem envelopeCompletionDelta_mul (i : ι) (x y : envelopeCompletion E p hp) :
    envelopeCompletionDelta E p hp bas i (x * y) =
      x * envelopeCompletionDelta E p hp bas i y + y * envelopeCompletionDelta E p hp bas i x := by
  rw [envelopeCompletionDelta_apply, envelopeCompletionFormsDifferential_mul, map_add,
    LinearEquiv.map_smul, LinearEquiv.map_smul]
  rfl

/-- `δ̂_i` kills the image of `A`. -/
theorem envelopeCompletionDelta_algebraMap (i : ι) (r : A) :
    envelopeCompletionDelta E p hp bas i (algebraMap (A : Type u) (envelopeCompletion E p hp) r) =
      0 := by
  rw [envelopeCompletionDelta_apply, envelopeCompletionFormsDifferential_algebraMap, map_zero]
  rfl

/-- **The divided power chain rule** `δ̂_i(γ_n x) = γ_{n-1}(x) δ̂_i(x)`. -/
theorem envelopeCompletionDelta_dpow (i : ι) {n : ℕ} (hn : 0 < n)
    {x : envelopeCompletion E p hp} (hx : x ∈ (envelopeCompletion E p hp).ideal) :
    envelopeCompletionDelta E p hp bas i ((envelopeCompletion E p hp).dividedPowers.dpow n x) =
      (envelopeCompletion E p hp).dividedPowers.dpow (n - 1) x *
        envelopeCompletionDelta E p hp bas i x := by
  rw [envelopeCompletionDelta_apply, envelopeCompletionFormsDifferential_dpow E p hp hn hx,
    LinearEquiv.map_smul]
  rfl

variable (hbas : ∀ i, bas i =
  envelopeCompletionFormsDifferential E p hp (envelopeCompletionCoord E p hp i))

include hbas in
/-- **The `δ̂_i` commute**: they extend the commuting `δ_i` of the dense subring `E`. -/
theorem envelopeCompletionDelta_comm (i j : ι) :
    ⇑(envelopeCompletionDelta E p hp bas i) ∘ ⇑(envelopeCompletionDelta E p hp bas j) =
      ⇑(envelopeCompletionDelta E p hp bas j) ∘ ⇑(envelopeCompletionDelta E p hp bas i) := by
  have h := envelopeCompletion_addMonoidHom_ext E p hp
    ((envelopeCompletionDelta E p hp bas i).comp (envelopeCompletionDelta E p hp bas j))
    ((envelopeCompletionDelta E p hp bas j).comp (envelopeCompletionDelta E p hp bas i))
    fun a => by
      simp only [AddMonoidHom.comp_apply, envelopeCompletionDelta_inclusion E p hp bas hbas]
      exact congrArg (envelopeCompletionInclusion E p hp)
        (congrFun (envelopeDelta_comm E i j) a)
  exact congrArg DFunLike.coe h

/-- **The composite coordinate operators `δ̂_K = ∏_i δ̂_i^{k_i}`** of `D`. -/
def envelopeCompletionDeltaPow : (ι →₀ ℕ) → envelopeCompletion E p hp → envelopeCompletion E p hp :=
  (exists_isThetaMonomialFamily (fun i => ⇑(envelopeCompletionDelta E p hp bas i))
    (envelopeCompletionDelta_comm E p hp bas hbas)).choose

/-- The `δ̂_K` are the composites of the `δ̂_i`. -/
theorem isThetaMonomialFamily_envelopeCompletionDeltaPow :
    IsThetaMonomialFamily (envelopeCompletion E p hp : Type u)
      (fun i => ⇑(envelopeCompletionDelta E p hp bas i))
      (envelopeCompletionDeltaPow E p hp bas hbas) :=
  (exists_isThetaMonomialFamily (fun i => ⇑(envelopeCompletionDelta E p hp bas i))
    (envelopeCompletionDelta_comm E p hp bas hbas)).choose_spec

/-- The `δ̂_K` are additive. -/
theorem envelopeCompletionDeltaPow_add (K : ι →₀ ℕ) (x y : envelopeCompletion E p hp) :
    envelopeCompletionDeltaPow E p hp bas hbas K (x + y) =
      envelopeCompletionDeltaPow E p hp bas hbas K x +
        envelopeCompletionDeltaPow E p hp bas hbas K y := by
  have hfam := isThetaMonomialFamily_envelopeCompletionDeltaPow E p hp bas hbas
  induction K using finsupp_induction_single with
  | h0 => rw [hfam.1]; rfl
  | hstep K i ih =>
    rw [hfam.2 i K]
    simp only [Function.comp_apply]
    rw [ih, map_add]

/-- `δ̂_K` as an additive map. -/
def envelopeCompletionDeltaPowHom (K : ι →₀ ℕ) :
    envelopeCompletion E p hp →+ envelopeCompletion E p hp :=
  AddMonoidHom.mk' (envelopeCompletionDeltaPow E p hp bas hbas K)
    (envelopeCompletionDeltaPow_add E p hp bas hbas K)

/-- **`δ̂_K` extends the Taylor coefficient `θ_K` of `E`.** -/
theorem envelopeCompletionDeltaPow_inclusion (K : ι →₀ ℕ) (a : E.object) :
    envelopeCompletionDeltaPow E p hp bas hbas K (envelopeCompletionInclusion E p hp a) =
      envelopeCompletionInclusion E p hp (presentationTaylorCoeff E K a) := by
  have hfam := isThetaMonomialFamily_envelopeCompletionDeltaPow E p hp bas hbas
  have hfamE := isThetaMonomialFamily_presentationTaylorCoeff E
  induction K using finsupp_induction_single generalizing a with
  | h0 => rw [hfam.1, presentationTaylorCoeff_zero]; rfl
  | hstep K i ih =>
    rw [hfam.2 i K]
    simp only [Function.comp_apply]
    rw [ih, envelopeCompletionDelta_inclusion E p hp bas hbas]
    exact congrArg (envelopeCompletionInclusion E p hp) (congrFun (hfamE.2 i K) a).symm

/-! ### Taylor's formula at the levels -/

/-- The structure map `E → D`, in the proof below. -/
local notation "ιD" => envelopeCompletionInclusion E p hp

/-- The composite coordinate operators `δ̂_K`, in the proof below. -/
local notation "δK" => envelopeCompletionDeltaPow E p hp bas hbas

/-- The ideal `(p) ⊆ D`, in the proof below. -/
local notation "𝔭" => pAdicIdeal (A := DividedPowerRing.carrier (envelopeCompletion E p hp)) p

/-- **Taylor's formula at the levels.**  Let `ρ : D → D` be a divided power endomorphism over `A`
compatible with the augmentation, i.e. `ρ(x) - x` lies in the divided power ideal for every `x`,
and put `ξ_i = x_i - ρ(x_i)`.  Then for every `a ∈ D` and every `n` there is a finite set `S` of
multi-indices with

* `δ̂_K a ∈ p^n D` for `K ∉ S`,
* `a ≡ ∑_{K ∈ S} ρ(δ̂_K a) ξ^{[K]} mod p^n D`, and
* `ρ(a) ≡ ∑_{K ∈ S} δ̂_K(a) (-ξ)^{[K]} mod p^n D`.

The proof approximates `a` by an element `a₀ ∈ E` modulo `p^n D` and applies Taylor's formula
`Crystalline.envelopeTaylor_formula` of the envelope to `E → D` and `ρ ∘ (E → D)`, in both
orders; `S` is the support of the Taylor expansion of `a₀`. -/
theorem envelopeCompletion_taylor_levels
    (ρ : DPMorphism (envelopeCompletion E p hp).dividedPowers
      (envelopeCompletion E p hp).dividedPowers)
    (hρA : ρ.comp (envelopeCompletionStructureMap E p hp) = envelopeCompletionStructureMap E p hp)
    (hρ : ∀ x, ρ x - x ∈ (envelopeCompletion E p hp).ideal) (a : envelopeCompletion E p hp)
    (n : ℕ) :
    ∃ S : Finset (ι →₀ ℕ),
      (∀ K ∉ S, envelopeCompletionDeltaPow E p hp bas hbas K a ∈
        pAdicIdeal (A := (envelopeCompletion E p hp : Type u)) p ^ n) ∧
      a - ∑ K ∈ S, ρ (envelopeCompletionDeltaPow E p hp bas hbas K a) *
          taylorMonomial (envelopeCompletion E p hp)
            (fun i => envelopeCompletionCoord E p hp i - ρ (envelopeCompletionCoord E p hp i)) K ∈
        pAdicIdeal (A := (envelopeCompletion E p hp : Type u)) p ^ n ∧
      ρ a - ∑ K ∈ S, envelopeCompletionDeltaPow E p hp bas hbas K a *
          taylorMonomial (envelopeCompletion E p hp)
            (-fun i => envelopeCompletionCoord E p hp i - ρ (envelopeCompletionCoord E p hp i)) K ∈
        pAdicIdeal (A := (envelopeCompletion E p hp : Type u)) p ^ n := by
  obtain ⟨a₀, ha₀⟩ := exists_sub_envelopeCompletionInclusion_mem E p hp a n
  set z := a - ιD a₀ with hz
  have hδ : ∀ K, δK K a = ιD (presentationTaylorCoeff E K a₀) + δK K z := fun K => by
    rw [← envelopeCompletionDeltaPow_inclusion E p hp bas hbas K a₀,
      ← envelopeCompletionDeltaPow_add, hz, add_sub_cancel]
  have hδz : ∀ K, δK K z ∈ 𝔭 ^ n := fun K =>
    map_mem_pAdicIdeal_pow p n (envelopeCompletionDeltaPowHom E p hp bas hbas K) ha₀
  have hρP : ∀ x ∈ 𝔭 ^ n, ρ x ∈ 𝔭 ^ n := fun x hx =>
    map_mem_pAdicIdeal_pow p n ρ.toRingHom.toAddMonoidHom hx
  have hFG : (ιD).comp E.structureMap = (ρ.comp ιD).comp E.structureMap :=
    DFunLike.ext _ _ fun r =>
      (congrArg (fun f : DPMorphism A.dividedPowers (envelopeCompletion E p hp).dividedPowers =>
        f r) hρA).symm
  set ξ : ι → envelopeCompletion E p hp :=
    fun i => envelopeCompletionCoord E p hp i - ρ (envelopeCompletionCoord E p hp i) with hξ
  have hneg : -ξ = fun i =>
      ρ (envelopeCompletionCoord E p hp i) - envelopeCompletionCoord E p hp i :=
    funext fun i => neg_sub _ _
  set S := envelopeTaylorSupport E a₀ with hS
  have key : ∀ (ψ φ : envelopeCompletion E p hp →+ envelopeCompletion E p hp)
      (mon : (ι →₀ ℕ) → envelopeCompletion E p hp), (∀ x ∈ 𝔭 ^ n, φ x ∈ 𝔭 ^ n) → ψ z ∈ 𝔭 ^ n →
      ψ (ιD a₀) = ∑ K ∈ S, φ (ιD (presentationTaylorCoeff E K a₀)) * mon K →
      ψ a - ∑ K ∈ S, φ (δK K a) * mon K ∈ 𝔭 ^ n := fun ψ φ mon hφ hψ hT => by
    have hψa : ψ a = ψ (ιD a₀) + ψ z := by rw [← map_add, hz, add_sub_cancel]
    simp only [hδ, map_add, add_mul, Finset.sum_add_distrib, ← hT]
    rw [hψa, add_sub_add_left_eq_sub]
    exact Ideal.sub_mem _ hψ (Ideal.sum_mem _ fun K _ => Ideal.mul_mem_right _ _ (hφ _ (hδz K)))
  refine ⟨S, fun K hK => ?_, ?_, ?_⟩
  · rw [hδ, presentationTaylorCoeff_eq_zero_of_notMem E hK, map_zero, zero_add]
    exact hδz K
  · exact key (AddMonoidHom.id _) ρ.toRingHom.toAddMonoidHom _ hρP ha₀
      (envelopeTaylor_formula E (envelopeCompletion E p hp) ιD (ρ.comp ιD) hFG
        (fun i => by
          show envelopeCompletionCoord E p hp i - ρ (envelopeCompletionCoord E p hp i) ∈ _
          rw [← neg_sub]
          exact Submodule.neg_mem _ (hρ _)) a₀)
  · refine key ρ.toRingHom.toAddMonoidHom (AddMonoidHom.id _) _ (fun _ h => h) (hρP _ ha₀) ?_
    rw [hneg]
    exact envelopeTaylor_formula E (envelopeCompletion E p hp) (ρ.comp ιD) ιD hFG.symm
      (fun i => hρ _) a₀

end Completed

end Crystalline
