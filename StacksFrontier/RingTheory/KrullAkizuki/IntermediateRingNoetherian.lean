module

public import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Krull–Akizuki

Let $R$ be an integral domain with fraction field $K$ and let $L/K$ be a finite extension of
fields.  If $R$ is Noetherian of Krull dimension $1$, then every ring $A$ with
$R \subset A \subset L$ is Noetherian.

## Conventions

The fraction field $K = \operatorname{Frac}(R)$ is carried by `IsFractionRing R K`, and
finiteness of $L/K$ by `Module.Finite K L`.  The hypothesis $\dim(R) = 1$ is
`ringKrullDim R = 1`, which in particular rules out $R$ being a field.  "Any ring $A$ with
$R \subset A \subset L$" means a `Subring L` containing the image of $R$, expressed as
`(algebraMap R L).range ≤ A`; being a subring of a field, such an $A$ is automatically a
domain.  The setup links $R$, $K$ and $L$ via `IsScalarTower R K L`, so that the canonical
map $R \to L$ factors through $K$.
-/

@[expose] public section

/-! ## Auxiliary lemmas (Stacks 00PG decomposition)

The proof of Krull–Akizuki (Stacks 00PG) for a nonzero ideal `I ⊆ A` runs:
pick a nonzero `x ∈ I ∩ R` (AUX-3); then `xA ⊆ I ⊆ A` and the `R`-module `A/xA`
has *finite length* (AUX-4 = Stacks 00PF, the analytic core); a finite-length
`R`-module is `R`-Noetherian, hence every `A`-submodule of it is finitely
generated over `A` (AUX-1/2 = `fg_of_isFiniteLength_subring`); applying this to
the image of `I` in `A/xA` and gluing with the principal ideal `xA` shows `I` is
finitely generated. -/

section KrullAkizuki

variable (R : Type*) [CommRing R] [IsDomain R]
variable (K : Type*) [Field K] [instAlgRK : Algebra R K] [instFR : IsFractionRing R K]
variable (L : Type*) [Field L] [instAlgKL : Algebra K L] [instFin : Module.Finite K L]
variable [Algebra R L] [instTower : IsScalarTower R K L]

omit [IsDomain R] in
/-- **AUX-1/2 (FG transfer).** If an `A`-module `M` has finite length as a module
over the base ring `R` (with `R` acting through a scalar tower `R → A → M`), then
every `A`-submodule of `M` is finitely generated.

Proof: finite length over `R` ⇒ `R`-Noetherian (`isFiniteLength_iff_isNoetherian_isArtinian`);
an `R`-Noetherian module is `R`-Noetherian on the restricted-scalars module, and an
`A`-submodule that is `R`-finitely-generated is in particular `A`-finitely-generated
(`Submodule.FG.of_restrictScalars`). -/
lemma fg_of_isFiniteLength_subring
    {A : Type*} [CommRing A] [Algebra R A]
    {M : Type*} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    (hM : IsFiniteLength R M) (S : Submodule A M) : S.FG := by
  have hN : IsNoetherian R M := (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).left
  exact Submodule.FG.of_restrictScalars R (hN.noetherian _)

include K instAlgRK instFR instAlgKL instFin instTower in
/-- **AUX-3 (nonzero element of `R` inside a nonzero ideal of `A`).** A nonzero ideal
`I` of an intermediate ring `R ⊆ A ⊆ L` contains the image of a nonzero element of `R`.

Math argument (Stacks 10.30.8 specialized): pick `0 ≠ a ∈ I`. Since `L/K` is finite,
`a` is algebraic over `K`; let `p = minpoly K a`. Its constant term is nonzero
(`minpoly.coeff_zero_ne_zero`, using `a ≠ 0`). Clear denominators: apply
`IsLocalization.integerNormalization (nonZeroDivisors R) p` to obtain an `R`-polynomial
`q` with `aeval a q = 0` (`IsLocalization.integerNormalization_aeval_eq_zero`) and
`q.coeff 0 ≠ 0`. Writing `0 = aeval a q = q.coeff 0 + a * (∑ …)` via
`Polynomial.aeval_eq_sum_range`, we get `algebraMap R A (q.coeff 0) = - a * c` for some
`c ∈ A`, which lies in `I` since `a ∈ I` (`Ideal.mul_mem_left` / `Ideal.neg_mem`). Take
`x := q.coeff 0`.  This requires `IsScalarTower R K L` and `IsFractionRing R K`. -/
lemma exists_nonzero_mem_of_ne_bot
    (A : Subring L)
    [Algebra R A] [IsScalarTower R A L]
    (I : Ideal A) (hI : I ≠ ⊥) :
    ∃ x : R, x ≠ 0 ∧ (algebraMap R A x) ∈ I := by
  -- `L/K` is finite, so every element of `L` (in particular elements of `A`) is
  -- algebraic over `K = Frac R`; this is the start of the denominator-clearing
  -- argument that produces the desired `x ∈ R`.
  have : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  -- Step: pick nonzero a in I
  obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  -- view a in L
  set aL : L := algebraMap (↥A) L a with haL
  have haLne : aL ≠ 0 := by
    rw [haL]
    simpa using (FaithfulSMul.algebraMap_injective (↥A) L).ne ha0
  -- minimal polynomial of aL over K
  have hint : IsIntegral K aL := Algebra.IsIntegral.isIntegral aL
  set p : Polynomial K := minpoly K aL with hp
  have hc0 : p.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint haLne
  set q : Polynomial R := IsLocalization.integerNormalization (nonZeroDivisors R) p with hq
  -- aeval aL q = 0
  have hpaeval : (Polynomial.aeval aL) p = 0 := minpoly.aeval K aL
  have haevalL : (Polynomial.aeval aL) q = 0 :=
    IsLocalization.integerNormalization_aeval_eq_zero (nonZeroDivisors R) p hpaeval
  -- q.coeff 0 ≠ 0
  obtain ⟨b, hbM, hbspec⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) p
  have hqc0 : q.coeff 0 ≠ 0 := by
    intro hcontra
    have hmap0 : (Polynomial.map (algebraMap R K) q).coeff 0 = 0 := by
      rw [Polynomial.coeff_map, hcontra, map_zero]
    have hb0 : algebraMap R K b ≠ 0 := by
      simpa using (FaithfulSMul.algebraMap_injective R K).ne (nonZeroDivisors.ne_zero hbM)
    rw [hbspec, Polynomial.coeff_smul, Algebra.smul_def] at hmap0
    exact (mul_eq_zero.mp hmap0).elim hb0 hc0
  -- aeval a q = 0 in ↥A (pull back from L via injectivity)
  have haevalA : (Polynomial.aeval a) q = 0 := by
    apply (FaithfulSMul.algebraMap_injective (↥A) L)
    rw [map_zero, ← haevalL, haL]
    exact Eq.symm (Polynomial.aeval_algebraMap_apply L a q)
  -- Decompose q = q.divX * X + C (q.coeff 0); apply aeval a.
  refine ⟨q.coeff 0, hqc0, ?_⟩
  have hexpand : (Polynomial.aeval a) (q.divX) * a + (algebraMap R (↥A)) (q.coeff 0) = 0 := by
    have := congrArg (Polynomial.aeval a) (Polynomial.divX_mul_X_add q)
    rwa [haevalA, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at this
  rw [eq_neg_of_add_eq_zero_right hexpand]
  exact I.neg_mem (I.mul_mem_left _ haI)

/-! ### The analytic core (Stacks 00PF / 10.119.11)

The plan bounds `Module.length R (A/xA) ≤ finrank K L · length_R(R/xR)`, which is finite,
hence `IsFiniteLength`.  Finiteness of `length_R(R/xR)` for `x ≠ 0` is Mathlib's
`isFiniteLength_quotient_span_singleton` (`R/(x)` is Noetherian of Krull dimension `0`,
hence Artinian, Stacks 00KH), whose hypothesis `Ring.KrullDimLE 1 R` follows from
`ringKrullDim R = 1`; the uniform bound is `length_quotient_smul_le_finrank_mul`.
-/

/-! ### The length bound (Stacks 00PE/00PF)

The argument replaces the snake lemma and the limit `n → ∞` of the source by an *exact*
cancellation identity.  For an `R`-module `M` and `x : R` we abbreviate the "`x`-quotient"
`M ⧸ (x • ⊤ : Submodule R M)` — Mathlib's `QuotSMulTop x M` — which for `M = ↥N` with
`N` a submodule is `N/xN`.  The standalone steps are:

* `length_quot_xtop_pi`: free multiplicativity,
  `length((Fin d → R)/x•⊤) = d · length(R/(x))`, whence `length_quot_xtop_le_of_span` and
  `length_quot_xtop_span_range_le` for a module generated by `d` elements.
* `length_quot_xtop_eq_of_quot_finite`: for `N ≤ M` with `x •` injective on `M` and
  `length(M/N) ≠ ⊤`, `length(M/x•⊤) = length(↥N/x•⊤)` — the cancellation identity.
* `length_le_of_forall_fg_submodule_le` and `length_quot_xtop_le_of_forall_fg`: a bound
  valid on all finitely generated submodules is a bound.
* `exists_smul_le_of_le_span_fraction`: denominator clearing, `s • N ≤ F` for a finitely
  generated `N` inside the `K`-span of `F`.

`length_quot_xtop_fg_le` assembles these into the bound for a finitely generated submodule
of a finite-dimensional `K`-vector space and `length_quotient_smul_le_finrank_mul` lifts it
to an arbitrary submodule; `isFiniteLength_quotient_smul` specializes to `V := L` and an
intermediate ring `A`.
-/
open Pointwise in
omit [IsDomain R] in
/-- **SUB-LIFT (Obligation C).** If every finitely generated `R`-submodule `N` of
`M` satisfies `Module.length R N ≤ B`, then `Module.length R M ≤ B`.

Math: `Module.length R M = Order.krullDim (Submodule R M)` is the supremum of
lengths of chains `p₀ < p₁ < … < pₖ` of submodules; any such finite chain is
contained in the f.g. submodule `N` spanned by witnesses of each strict step
(`Order.krullDim_eq_iSup_length` on the lattice `Submodule R M`; pull the chain
back into `↥N` via `comap N.subtype`, which preserves strict inclusions). Hence
every chain has length `≤ length(↥N) ≤ B`, giving `length M ≤ B`. -/
lemma length_le_of_forall_fg_submodule_le
    {M : Type*} [AddCommGroup M] [Module R M] {B : ℕ∞}
    (h : ∀ N : Submodule R M, N.FG → Module.length R N ≤ B) :
    Module.length R M ≤ B := by
  -- per-chain bound
  have key : ∀ p : LTSeries (Submodule R M), (p.length : ℕ∞) ≤ B := by
    intro p
    have hstep : ∀ i : Fin p.length, p (i.castSucc) < p (i.succ) := fun i => p.step i
    have hw : ∀ i : Fin p.length, ∃ x ∈ p (i.succ), x ∉ p (i.castSucc) :=
      fun i => IsConcreteLE.exists_of_lt (hstep i)
    choose w hwmem hwnmem using hw
    set N : Submodule R M := Submodule.span R (Set.range w) with hN
    have hNfg : N.FG := Submodule.fg_span (Set.finite_range w)
    have hwN : ∀ i, w i ∈ N := fun i => Submodule.subset_span ⟨i, rfl⟩
    have hmono : ∀ i : Fin p.length,
        (p (i.castSucc)).comap N.subtype < (p (i.succ)).comap N.subtype := by
      intro i
      refine lt_of_le_of_ne (Submodule.comap_mono (le_of_lt (hstep i))) ?_
      intro heq
      have hin : (⟨w i, hwN i⟩ : N) ∈ (p (i.succ)).comap N.subtype := hwmem i
      rw [← heq] at hin
      exact hwnmem i hin
    let q : LTSeries (Submodule R N) :=
      RelSeries.mk p.length (fun i => (p i).comap N.subtype) hmono
    have hq : q.length = p.length := rfl
    have h1 : (q.length : WithBot ℕ∞) ≤ Order.krullDim (Submodule R N) :=
      Order.LTSeries.length_le_krullDim q
    rw [← Module.coe_length R N] at h1
    have h2 : (q.length : ℕ∞) ≤ Module.length R N := by exact_mod_cast h1
    rw [hq] at h2
    exact h2.trans (h N hNfg)
  -- assemble via krullDim
  have hcoe : (↑(Module.length R M) : WithBot ℕ∞) ≤ (↑B : WithBot ℕ∞) := by
    rw [Module.coe_length R M, Order.krullDim_eq_iSup_length, WithBot.coe_le_coe]
    exact iSup_le key
  exact_mod_cast hcoe

open Pointwise in
omit [IsDomain R] in
/-- **Chain lifting.** A bound `b` for the `x`-quotient of every finitely generated
submodule `N ≤ M` is a bound for the `x`-quotient of `M`, because a chain of submodules of
`↥M/x•⊤` involves only finitely many elements of `M`: lift the witnesses of its strict
steps to `↥M`, and `↥P` is a quotient of `↥N/x•⊤` for the submodule `N ≤ M` they span. -/
lemma length_quot_xtop_le_of_forall_fg {W : Type*} [AddCommGroup W] [Module R W] (x : R)
    (M : Submodule R W) (b : ℕ∞)
    (hb : ∀ N : Submodule R W, N.FG → N ≤ M →
      Module.length R (N ⧸ (x • ⊤ : Submodule R N)) ≤ b) :
    Module.length R (M ⧸ (x • ⊤ : Submodule R M)) ≤ b := by
  classical
  set mk : (M : Type _) →ₗ[R] QuotSMulTop x (M : Type _) :=
    (x • (⊤ : Submodule R (M : Type _))).mkQ with hmk
  refine length_le_of_forall_fg_submodule_le R fun P hP => ?_
  obtain ⟨t, ht⟩ := hP
  choose g hg using fun q : QuotSMulTop x (M : Type _) =>
    (x • (⊤ : Submodule R (M : Type _))).mkQ_surjective q
  set N₀ : Submodule R (M : Type _) :=
    Submodule.span R (g '' (↑t : Set (QuotSMulTop x (M : Type _)))) with hN₀
  have hN₀fg : N₀.FG := Submodule.fg_span (t.finite_toSet.image g)
  have hmapN₀ : Submodule.map mk N₀ = P := by
    rw [hN₀, Submodule.map_span]
    have himg : mk '' (g '' (↑t : Set (QuotSMulTop x (M : Type _))))
        = (↑t : Set (QuotSMulTop x (M : Type _))) := by
      rw [Set.image_image, Set.image_congr fun q _ => hg q, Set.image_id']
    rw [himg, ht]
  -- a surjection `↥N₀ ↠ ↥P` killing `x • ⊤`
  have hmem : ∀ n : N₀, mk (N₀.subtype n) ∈ P := by
    intro n
    rw [← hmapN₀]
    exact Submodule.mem_map_of_mem n.property
  set f : (N₀ : Type _) →ₗ[R] (P : Type _) :=
    LinearMap.codRestrict P (mk.comp N₀.subtype) hmem with hf
  have hfsurj : Function.Surjective f := by
    rintro ⟨p, hp⟩
    rw [← hmapN₀, Submodule.mem_map] at hp
    obtain ⟨a, ha, hap⟩ := hp
    exact ⟨⟨a, ha⟩, Subtype.ext hap⟩
  have hker : (x • ⊤ : Submodule R (N₀ : Type _)) ≤ LinearMap.ker f := by
    intro z hz
    rw [Submodule.mem_smul_pointwise_iff_exists] at hz
    obtain ⟨n, -, rfl⟩ := hz
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    rw [hf, ZeroMemClass.coe_zero, LinearMap.codRestrict_apply, LinearMap.comp_apply,
      map_smul, Submodule.subtype_apply, hmk, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_pointwise_smul _ _ _ trivial
  have hfq : Function.Surjective (Submodule.liftQ _ f hker) := by
    intro p
    obtain ⟨n, rfl⟩ := hfsurj p
    exact ⟨Submodule.Quotient.mk n, by rw [Submodule.liftQ_apply]⟩
  -- transport `N₀ ≤ ↥M` to a submodule of `W`
  set N : Submodule R W := Submodule.map M.subtype N₀
  calc Module.length R (P : Type _)
      ≤ Module.length R ((N₀ : Type _) ⧸ (x • ⊤ : Submodule R (N₀ : Type _))) :=
        Module.length_le_of_surjective _ hfq
    _ = Module.length R ((N : Type _) ⧸ (x • ⊤ : Submodule R (N : Type _))) :=
        (QuotSMulTop.congr x
          (Submodule.equivMapOfInjective M.subtype (Submodule.subtype_injective M) N₀)).length_eq
    _ ≤ b := hb N (hN₀fg.map M.subtype) (Submodule.map_subtype_le M N₀)

open Pointwise in
omit [IsDomain R] in
/-- **SUB-FREE (Step 2, free multiplicativity, the `n = 1` case used below).** For a
finite free module `Fin d → R`, the `x`-quotient has length `d · length(R/(x))`:
`length((Fin d → R) / x • ⊤) = d · length(R/(x))`.

Math: `(Fin d → R) / x • ⊤ ≅ (R / x • ⊤)^d = (R/(x))^d` (taking `mod x` commutes
with the finite product), so `Module.length_pi_of_fintype` (sum of `d` equal
factors) and `Submodule.quotientPi` give the result. Note `(x • ⊤ : Submodule R R)
= Ideal.span {x}` (`x • ⊤ = {x·r} = (x)`). -/
@[ega "IV 21.10.13" "special case"]
lemma length_quot_xtop_pi (d : ℕ) {x : R} :
    Module.length R ((Fin d → R) ⧸ (x • ⊤ : Submodule R (Fin d → R)))
      = (d : ℕ∞) * Module.length R (R ⧸ Ideal.span {x}) := by
  -- d=0 (0·⊤=0), x=0, x unit all consistent)
  have hpi : (x • ⊤ : Submodule R (Fin d → R))
      = Submodule.pi Set.univ (fun _ => (x • ⊤ : Submodule R R)) := by
    ext v
    simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and,
      Submodule.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · rintro ⟨w, rfl⟩ i
      exact ⟨w i, rfl⟩
    · intro h
      choose w hw using h
      exact ⟨w, funext hw⟩
  have hsm : (x • ⊤ : Submodule R R) = Ideal.span {x} := by
    ext y
    simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and,
      Ideal.mem_span_singleton]
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b, by ring⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c, by rw [smul_eq_mul, mul_comm]⟩
  rw [hpi, (Submodule.quotientPi (fun _ => (x • ⊤ : Submodule R R))).length_eq,
    Module.length_pi_of_fintype, hsm, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

open Pointwise in
omit [IsDomain R] in
/-- **SUB-GEN (generated-module bound).** If an `R`-module `M` is generated by `d`
elements (i.e. there is a surjection `(Fin d → R) →ₗ M`), then
`length(M / x • ⊤) ≤ d · length(R/(x))`.

Math: a surjection `π : (Fin d → R) ↠ M` induces a surjection on `x`-quotients
`(Fin d → R)/x•⊤ ↠ M/x•⊤` (it maps `x • ⊤` into `x • ⊤`), so
`Module.length_le_of_surjective` plus `SUB-FREE` (`length_quot_xtop_pi`) bounds
`length(M/x•⊤) ≤ length((Fin d → R)/x•⊤) = d · length(R/(x))`. -/
lemma length_quot_xtop_le_of_span
    {M : Type*} [AddCommGroup M] [Module R M] (d : ℕ)
    (π : (Fin d → R) →ₗ[R] M) (hπ : Function.Surjective π) {x : R} :
    Module.length R (M ⧸ (x • ⊤ : Submodule R M))
      ≤ (d : ℕ∞) * Module.length R (R ⧸ Ideal.span {x}) := by
  -- d=0, x=0, x unit, rank-drop all consistent with the ≤ direction)
  have hmap : Submodule.map π (x • ⊤ : Submodule R (Fin d → R))
      = (x • ⊤ : Submodule R M) := by
    rw [Submodule.map_pointwise_smul, Submodule.map_top, LinearMap.range_eq_top.mpr hπ]
  have hle : (x • ⊤ : Submodule R (Fin d → R))
      ≤ Submodule.comap π (x • ⊤ : Submodule R M) := by
    rw [← Submodule.map_le_iff_le_comap, hmap]
  set q : ((Fin d → R) ⧸ (x • ⊤ : Submodule R (Fin d → R)))
      →ₗ[R] (M ⧸ (x • ⊤ : Submodule R M)) :=
    Submodule.mapQ _ _ π hle with hq
  have hqsurj : Function.Surjective q := by
    intro y
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨v, rfl⟩ := hπ m
    exact ⟨Submodule.Quotient.mk v, by rw [hq, Submodule.mapQ_apply]⟩
  calc Module.length R (M ⧸ (x • ⊤ : Submodule R M))
      ≤ Module.length R ((Fin d → R) ⧸ (x • ⊤ : Submodule R (Fin d → R))) :=
        Module.length_le_of_surjective q hqsurj
    _ = (d : ℕ∞) * Module.length R (R ⧸ Ideal.span {x}) :=
        length_quot_xtop_pi R d (x := x)

open Pointwise in
omit [IsDomain R] in
/-- The `x`-quotient of an `R`-submodule spanned by `d` elements has length at most
`d · length(R/(x))`: the span is generated by `d` elements, so `length_quot_xtop_le_of_span`
applies to it. -/
lemma length_quot_xtop_span_range_le {W : Type*} [AddCommGroup W] [Module R W] {d : ℕ}
    (w : Fin d → W) (x : R) :
    Module.length R (Submodule.span R (Set.range w)
        ⧸ (x • ⊤ : Submodule R (Submodule.span R (Set.range w))))
      ≤ (d : ℕ∞) * Module.length R (R ⧸ Ideal.span {x}) := by
  have hmem : ∀ c : Fin d → R,
      Fintype.linearCombination R w c ∈ Submodule.span R (Set.range w) := fun c => by
    simp only [Fintype.linearCombination_apply]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine length_quot_xtop_le_of_span R d
    (LinearMap.codRestrict _ (Fintype.linearCombination R w) hmem) ?_
  rintro ⟨y, hy⟩
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hy
  obtain ⟨c, rfl⟩ := hy
  refine ⟨fun i => c i, Subtype.ext ?_⟩
  simp only [LinearMap.codRestrict_apply, Fintype.linearCombination_apply]
  rw [Finsupp.sum_fintype]
  intro i
  simp

open Pointwise in
omit [IsDomain R] in
/-- **SUB-CANCEL (replaces Sublemma C).** Let `M` be an `R`-module on which `x • ·`
is injective (e.g. `M` torsion-free, `x ≠ 0`), and let `N ≤ M` be a submodule with
`Module.length R (M ⧸ N) ≠ ⊤`. Then the `x`-quotients of `M` and `N` have equal
length: `length(M / x•⊤) = length(↥N / x•⊤)`.

Math (the exact cancellation identity): with `ℓ := length(M/N) < ∞`, the three SES
`length(M / x•N) = length(M/N) + length(N/x•N)` (via `N/x•N ↪ M/x•N ↠ M/N`),
`length(M / x•N) = length(x•M/x•N) + length(M/x•M)` (via `x•M/x•N ↪ M/x•N ↠ M/x•M`),
and the iso `x•M/x•N ≅ M/N` (multiplication-by-`x`, injective on `M`) give
`length(N/x•N) + ℓ = ℓ + length(M/x•M)`; cancel the finite `ℓ`
(`WithTop.add_right_cancel`) to get `length(N/x•N) = length(M/x•M)`, and
`length(N/x•N) = length(↥N/x•⊤)` since `x•N` corresponds to `x•⊤` in `↥N`. -/
@[ega "IV 21.10.13" "(ii), special case"]
lemma length_quot_xtop_eq_of_quot_finite
    {M : Type*} [AddCommGroup M] [Module R M] (x : R)
    (hinj : Function.Injective (fun m : M => x • m))
    (N : Submodule R M) (hfin : Module.length R (M ⧸ N) ≠ ⊤) :
    Module.length R (M ⧸ (x • ⊤ : Submodule R M))
      = Module.length R (N ⧸ (x • ⊤ : Submodule R N)) := by
  -- hypothesis length(M/N) ≠ ⊤ rules out rank-drop submodules)
  have helper_00pg : ∀ (S T : Submodule R M), S ≤ T →
      Module.length R (M ⧸ S)
        = Module.length R (M ⧸ T) + Module.length R (↥T ⧸ (Submodule.comap T.subtype S)) := by
    intro S T h
    set f : (↥T ⧸ (Submodule.comap T.subtype S)) →ₗ[R] (M ⧸ S) :=
      Submodule.mapQ (Submodule.comap T.subtype S) S T.subtype (le_refl _) with hf
    set g : (M ⧸ S) →ₗ[R] (M ⧸ T) := Submodule.mapQ S T LinearMap.id (by simpa using h) with hg
    rw [Module.length_eq_add_of_exact f g ?inj ?surj ?exact]
    · ring
    case inj =>
      rw [hf, injective_iff_map_eq_zero]
      intro a ha
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ a
      rw [Submodule.mapQ_apply] at ha
      rw [Submodule.Quotient.mk_eq_zero] at ha ⊢
      rw [Submodule.mem_comap]
      simpa using ha
    case surj =>
      rw [hg]
      intro a
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ a
      exact ⟨Submodule.Quotient.mk b, by rw [Submodule.mapQ_apply]; rfl⟩
    case exact =>
      rw [hf, hg]
      intro a
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ a
      constructor
      · intro ha
        rw [Submodule.mapQ_apply] at ha
        simp only [LinearMap.id_coe, id_eq] at ha
        rw [Submodule.Quotient.mk_eq_zero] at ha
        refine ⟨Submodule.Quotient.mk ⟨b, ha⟩, ?_⟩
        rw [Submodule.mapQ_apply]
        rfl
      · rintro ⟨c, hc⟩
        obtain ⟨d, rfl⟩ := Submodule.Quotient.mk_surjective _ c
        rw [Submodule.mapQ_apply] at hc
        rw [Submodule.mapQ_apply]
        simp only [LinearMap.id_coe, id_eq]
        rw [Submodule.Quotient.mk_eq_zero]
        rw [Submodule.Quotient.eq] at hc
        have h1 : (T.subtype d) - b ∈ T := h hc
        have hd : (T.subtype d : M) ∈ T := d.property
        have := T.sub_mem hd h1
        simpa using this
  set xT : Submodule R M := x • (⊤ : Submodule R M) with hxT
  set xN : Submodule R M := x • N with hxN
  have hxNleN : xN ≤ N := Submodule.smul_le_self_of_tower x N
  have hxNlexT : xN ≤ xT := by
    rw [hxN, hxT]; gcongr; exact le_top
  have hrange : xT = LinearMap.range (LinearMap.lsmul R M x) := by
    rw [hxT]; ext m; simp [Submodule.mem_smul_pointwise_iff_exists, LinearMap.mem_range]
  have hinj' : Function.Injective (LinearMap.lsmul R M x) := hinj
  set e : M ≃ₗ[R] ↥xT :=
    (LinearEquiv.ofInjective (LinearMap.lsmul R M x) hinj').trans
      (LinearEquiv.ofEq _ _ hrange.symm) with he
  have hcoe : ∀ m : M, (e m : M) = x • m := by
    intro m; rw [he]; simp [LinearEquiv.ofInjective_apply]
  have hmap : Submodule.map (e : M →ₗ[R] ↥xT) N
      = Submodule.comap xT.subtype xN := by
    ext y
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply,
      LinearEquiv.coe_coe]
    constructor
    · rintro ⟨n, hn, rfl⟩
      rw [hcoe, hxN]
      exact Submodule.smul_mem_pointwise_smul _ _ _ hn
    · intro hy
      rw [hxN, Submodule.mem_smul_pointwise_iff_exists] at hy
      obtain ⟨n, hn, hxn⟩ := hy
      exact ⟨n, hn, Subtype.ext (by rw [hcoe]; exact hxn)⟩
  have iso3 : Module.length R (M ⧸ N)
      = Module.length R (↥xT ⧸ (Submodule.comap xT.subtype xN)) :=
    (Submodule.Quotient.equiv N (Submodule.comap xT.subtype xN) e hmap).length_eq
  have hcomapN : Submodule.comap N.subtype xN = (x • ⊤ : Submodule R ↥N) := by
    rw [hxN]; ext n'
    simp only [Submodule.mem_comap, Submodule.subtype_apply,
      Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top]
    constructor
    · rintro ⟨m, hm, hxm⟩
      exact ⟨⟨m, hm⟩, trivial, Subtype.ext hxm⟩
    · rintro ⟨t, -, rfl⟩
      exact ⟨(t : M), t.property, rfl⟩
  have eq1 := helper_00pg xN N hxNleN
  have eq2 := helper_00pg xN xT hxNlexT
  rw [iso3] at eq1
  rw [eq1] at eq2
  rw [add_comm (Module.length R (↥xT ⧸ Submodule.comap xT.subtype xN))
        (Module.length R (↥N ⧸ Submodule.comap N.subtype xN))] at eq2
  have hfin' : Module.length R (↥xT ⧸ Submodule.comap xT.subtype xN) ≠ ⊤ := by
    rwa [← iso3]
  have key := WithTop.add_right_cancel hfin' eq2
  rw [hcomapN] at key
  rw [hxT]
  exact key.symm

variable {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

omit [IsDomain R] in
/-- An element of the `K`-span of an `R`-submodule `F` of a `K`-vector space `V` has a
nonzero `R`-multiple in `F`: denominators can be cleared. -/
lemma exists_smul_mem_of_mem_span_fraction (F : Submodule R V) {v : V}
    (hv : v ∈ Submodule.span K (F : Set V)) :
    ∃ s ∈ nonZeroDivisors R, s • v ∈ F := by
  induction hv using Submodule.span_induction with
  | mem w hw => exact ⟨1, one_mem _, by simpa using hw⟩
  | zero => exact ⟨1, one_mem _, by simp⟩
  | add w₁ w₂ _ _ h₁ h₂ =>
      obtain ⟨s₁, hs₁, h₁⟩ := h₁
      obtain ⟨s₂, hs₂, h₂⟩ := h₂
      refine ⟨s₁ * s₂, mul_mem hs₁ hs₂, ?_⟩
      have e : (s₁ * s₂) • (w₁ + w₂) = s₂ • (s₁ • w₁) + s₁ • (s₂ • w₂) := by
        rw [smul_add, mul_smul, smul_comm s₁ s₂ w₁, mul_smul]
      rw [e]
      exact F.add_mem (F.smul_mem _ h₁) (F.smul_mem _ h₂)
  | smul c w _ h =>
      obtain ⟨s, hs, hsw⟩ := h
      obtain ⟨t, a, ha⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors R) c
      refine ⟨(t : R) * s, mul_mem t.2 hs, ?_⟩
      have e1 : (t : R) • (c • w) = a • w :=
        calc (t : R) • (c • w) = (algebraMap R K (t : R)) • (c • w) :=
              (algebraMap_smul K _ _).symm
          _ = ((algebraMap R K (t : R)) * c) • w := by rw [smul_smul]
          _ = ((t : R) • c) • w := by rw [Algebra.smul_def]
          _ = (algebraMap R K a) • w := by rw [ha]
          _ = a • w := algebraMap_smul K a w
      have e2 : ((t : R) * s) • (c • w) = a • (s • w) := by
        rw [mul_comm, mul_smul, e1, smul_comm]
      rw [e2]
      exact F.smul_mem _ hsw

open Pointwise in
omit [IsDomain R] in
/-- **Denominator clearing.** A finitely generated `R`-submodule `N` of a `K`-vector space
`V` contained in the `K`-span of an `R`-submodule `F` satisfies `s • N ≤ F` for some
nonzero `s ∈ R`: one denominator per generator, multiplied together. -/
lemma exists_smul_le_of_le_span_fraction (F N : Submodule R V) (hN : N.FG)
    (hNF : N ≤ (Submodule.span K (F : Set V)).restrictScalars R) :
    ∃ s ∈ nonZeroDivisors R, (s • N : Submodule R V) ≤ F := by
  classical
  obtain ⟨t, ht⟩ := hN
  have key : ∀ u : Finset V, (∀ g ∈ u, g ∈ Submodule.span K (F : Set V)) →
      ∃ s ∈ nonZeroDivisors R, ∀ g ∈ u, s • g ∈ F := by
    intro u
    induction u using Finset.induction with
    | empty => exact fun _ => ⟨1, one_mem _, by simp⟩
    | insert a u ha ih =>
        intro hu
        obtain ⟨s, hs, hsu⟩ := ih fun g hg => hu g (Finset.mem_insert_of_mem hg)
        obtain ⟨s', hs', hsa⟩ :=
          exists_smul_mem_of_mem_span_fraction R K F (hu a (Finset.mem_insert_self a u))
        refine ⟨s * s', mul_mem hs hs', fun g hg => ?_⟩
        rcases Finset.mem_insert.mp hg with rfl | hg
        · rw [mul_smul]; exact F.smul_mem _ hsa
        · rw [mul_comm, mul_smul]; exact F.smul_mem _ (hsu g hg)
  obtain ⟨s, hs, hst⟩ := key t fun g hg => hNF (by rw [← ht]; exact Submodule.subset_span hg)
  refine ⟨s, hs, ?_⟩
  rw [← ht, Submodule.smul_span, Submodule.span_le]
  rintro y ⟨g, hg, rfl⟩
  exact hst g hg

/-- Enumerating a set `{w | p w}` by `Fin d` and forgetting the proofs recovers the set. -/
private lemma range_val_equiv {W : Type*} {p : W → Prop} {d : ℕ} (e : Fin d ≃ {w // p w}) :
    Set.range (fun j => (e j : W)) = {w | p w} := by
  rw [← Function.comp_def Subtype.val e, Set.range_comp, Equiv.range_eq_univ, Set.image_univ]
  exact Subtype.range_coe_subtype

open Pointwise in
/-- **The finite case (Step 3).** For a finitely generated `R`-submodule `N` of a
finite-dimensional `K`-vector space `V`,
`length(↥N/x•⊤) ≤ finrank K V · length(R/(x))`.

Math: `V` is torsion-free over `R` (`Module.IsTorsionFree.trans`), so `x •` is injective on
`↥N`.  A maximal `K`-independent subset `b` of a finite generating set of `N`
(`exists_linearIndependent`) has `d := |b| ≤ finrank K V`
(`LinearIndependent.fintype_card_le_finrank`) and spans an `R`-submodule `F = span_R b ≤ N`
with the same `K`-span as `N`.  Some `s ∈ nonZeroDivisors R` clears all denominators
(`exists_smul_le_of_le_span_fraction`), so `↥N/F` is a quotient of the finite-length module
`↥N/s•⊤`; the cancellation identity `length_quot_xtop_eq_of_quot_finite` then gives
`length(↥N/x•⊤) = length(↥F/x•⊤) ≤ d · length(R/(x))`
(`length_quot_xtop_span_range_le`). -/
lemma length_quot_xtop_fg_le
    [IsNoetherianRing R] [Ring.KrullDimLE 1 R] [FiniteDimensional K V]
    (N : Submodule R V) (hN : N.FG) {x : R} (hx : x ≠ 0) :
    Module.length R (N ⧸ (x • ⊤ : Submodule R N))
      ≤ (Module.finrank K V : ℕ∞) * Module.length R (R ⧸ Ideal.span {x}) := by
  classical
  -- `x • ·` is injective on `↥N`, since `V` is torsion-free over `R`.
  have htf : Module.IsTorsionFree R V := Module.IsTorsionFree.trans (S := R) (R := K) (M := V)
  have htfN : Module.IsTorsionFree R (N : Type _) := Submodule.instIsTorsionFree N
  have hinj : Function.Injective (fun n : N => x • n) := smul_right_injective _ hx
  obtain ⟨t, ht⟩ := hN
  -- A maximal `K`-independent subset `b` of the generators, reindexed by `Fin d`.
  obtain ⟨b, hbt, hbspanK, hbli⟩ := exists_linearIndependent K (↑t : Set V)
  have hbfin : Fintype ↥b := (t.finite_toSet.subset hbt).fintype
  set d : ℕ := Fintype.card ↥b with hd
  have hcard : d ≤ Module.finrank K V := hbli.fintype_card_le_finrank
  obtain ⟨e⟩ := Fintype.truncEquivFin (α := ↥b)
  set v : Fin d → V := fun j => ((e.symm j : ↥b) : V) with hv
  have hrangev : Set.range v = b := range_val_equiv e.symm
  set F : Submodule R V := Submodule.span R (Set.range v) with hF
  have hFleN : F ≤ N := by
    rw [hF, Submodule.span_le, hrangev, ← ht]
    exact fun y hy => Submodule.subset_span (hbt hy)
  -- `N` lies in the `K`-span of `F`, so denominators can be cleared.
  have hNF : N ≤ (Submodule.span K (F : Set V)).restrictScalars R := by
    rw [hF, Submodule.span_span_of_tower R K, hrangev, hbspanK, ← ht, Submodule.span_le]
    exact fun y hy => Submodule.subset_span hy
  obtain ⟨s, hs, hsNF⟩ := exists_smul_le_of_le_span_fraction R K F N ⟨t, ht⟩ hNF
  set F' : Submodule R (N : Type _) := Submodule.comap N.subtype F with hF'
  have hsT : (s • ⊤ : Submodule R (N : Type _)) ≤ F' := by
    intro z hz
    rw [Submodule.mem_smul_pointwise_iff_exists] at hz
    obtain ⟨n, -, rfl⟩ := hz
    exact hsNF (Submodule.smul_mem_pointwise_smul _ _ _ n.property)
  -- `↥N/F'` is a quotient of `↥N/s•⊤`, hence of finite length.
  have hfin : Module.length R ((N : Type _) ⧸ F') ≠ ⊤ := by
    set w : Fin t.card → V := fun j => ((t.equivFin.symm j : ↥t) : V) with hw
    have hrangew : Submodule.span R (Set.range w) = N := by
      rw [hw, range_val_equiv t.equivFin.symm, ← ht]
      rfl
    have hbound := length_quot_xtop_span_range_le R w s
    rw [hrangew] at hbound
    have hsfin : Module.length R (R ⧸ Ideal.span {s}) ≠ ⊤ :=
      Module.length_ne_top_iff.mpr (isFiniteLength_quotient_span_singleton R hs)
    have hNs : Module.length R ((N : Type _) ⧸ (s • ⊤ : Submodule R (N : Type _))) ≠ ⊤ :=
      ne_top_of_le_ne_top (WithTop.mul_ne_top (ENat.natCast_ne_top _) hsfin) hbound
    exact ne_top_of_le_ne_top hNs
      (Module.length_le_of_surjective (Submodule.factor hsT) (Submodule.factor_surjective hsT))
  calc Module.length R ((N : Type _) ⧸ (x • ⊤ : Submodule R (N : Type _)))
      = Module.length R ((F' : Type _) ⧸ (x • ⊤ : Submodule R (F' : Type _))) :=
        length_quot_xtop_eq_of_quot_finite R x hinj F' hfin
    _ = Module.length R ((F : Type _) ⧸ (x • ⊤ : Submodule R (F : Type _))) :=
        (QuotSMulTop.congr x (Submodule.comapSubtypeEquivOfLe hFleN)).length_eq
    _ ≤ (d : ℕ∞) * Module.length R (R ⧸ Ideal.span {x}) := by
        rw [hF]; exact length_quot_xtop_span_range_le R v x
    _ ≤ (Module.finrank K V : ℕ∞) * Module.length R (R ⧸ Ideal.span {x}) := by gcongr

open Pointwise in
/-- **The length bound (Stacks 00PE/00PF).** For `x ≠ 0` and an arbitrary — in particular
not necessarily finitely generated — `R`-submodule `M` of a finite-dimensional `K`-vector
space `V`, `length(↥M/x•⊤) ≤ finrank K V · length(R/(x))`.

Chain lifting (`length_quot_xtop_le_of_forall_fg`) reduces the bound to the finitely
generated submodules of `M`, where `length_quot_xtop_fg_le` applies. -/
lemma length_quotient_smul_le_finrank_mul
    [IsNoetherianRing R] [Ring.KrullDimLE 1 R] [FiniteDimensional K V]
    (M : Submodule R V) {x : R} (hx : x ≠ 0) :
    Module.length R (M ⧸ (x • ⊤ : Submodule R M))
      ≤ (Module.finrank K V : ℕ∞) * Module.length R (R ⧸ Ideal.span {x}) :=
  length_quot_xtop_le_of_forall_fg R x M _ fun N hN _ => length_quot_xtop_fg_le R K N hN hx

include K instAlgRK instFR instAlgKL instFin instTower in
open Pointwise in
/-- **Stacks 00PF / 10.119.11 (the analytic core).** For `x ≠ 0` in `R`, the quotient
`A/xA` of an intermediate ring `R ⊆ A ⊆ L` has finite length as an `R`-module.

As an `R`-module `A` is the submodule `LinearMap.range ι` of `L`, where `ι : A →ₗ[R] L` is
the inclusion, and the ideal `xA` is `x • ⊤`; so this is
`length_quotient_smul_le_finrank_mul` for `V := L`, whose right-hand side is finite because
`length_R(R/(x))` is (`isFiniteLength_quotient_span_singleton`, Stacks 00KH). -/
lemma isFiniteLength_quotient_smul
    [IsNoetherianRing R] (hdim : ringKrullDim R = 1)
    (A : Subring L)
    [Algebra R A] [IsScalarTower R A L]
    {x : R} (hx : x ≠ 0) :
    IsFiniteLength R (A ⧸ (Ideal.span {algebraMap R A x})) := by
  have : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr (by rw [hdim]; norm_num)
  rw [← Module.length_ne_top_iff]
  -- As an `R`-submodule of `A`, the ideal `span {algebraMap R A x}` equals `x • ⊤`.
  have hideal : Submodule.restrictScalars R (Ideal.span {algebraMap R A x})
      = (x • ⊤ : Submodule R (↥A)) := by
    ext a
    simp only [Submodule.restrictScalars_mem, Ideal.mem_span_singleton,
      Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c, trivial, by rw [Algebra.smul_def, mul_comm]⟩
    · rintro ⟨b, -, rfl⟩
      exact ⟨b, by rw [Algebra.smul_def]⟩
  rw [← (Submodule.Quotient.restrictScalarsEquiv R
      (Ideal.span {algebraMap R A x})).length_eq, hideal]
  -- The `R`-linear injection `ι : ↥A ↪ L` identifies `↥A` with an `R`-submodule of `L`.
  set ι : (↥A) →ₗ[R] L := (IsScalarTower.toAlgHom R (↥A) L).toLinearMap with hι
  have hιinj : Function.Injective ι := FaithfulSMul.algebraMap_injective (↥A) L
  have hlen : Module.length R (↥A ⧸ (x • ⊤ : Submodule R (↥A)))
      ≤ (Module.finrank K L : ℕ∞) * Module.length R (R ⧸ Ideal.span {x}) :=
    (QuotSMulTop.congr x (LinearEquiv.ofInjective ι hιinj)).length_eq.trans_le
      (length_quotient_smul_le_finrank_mul R K (LinearMap.range ι) hx)
  refine ne_top_of_le_ne_top ?_ hlen
  exact WithTop.mul_ne_top (ENat.natCast_ne_top _) (Module.length_ne_top_iff.mpr
    (isFiniteLength_quotient_span_singleton R (mem_nonZeroDivisors_of_ne_zero hx)))

end KrullAkizuki

/-- **Krull-Akizuki (Stacks Tag 00PG).** Let `R` be a Noetherian integral domain
of Krull dimension one, with fraction field `K`, and let `L` be a finite field
extension of `K`. Then every intermediate ring `A` with `R ⊆ A ⊆ L` is
Noetherian. -/
@[stacks 00PG, ega "IV 18.9.7.8" "more general", ega "IV 21.9.10" "Domain case"]
theorem krull_akizuki
    (R : Type*) [CommRing R] [IsDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (L : Type*) [Field L] [Algebra K L] [Module.Finite K L]
    [Algebra R L] [IsScalarTower R K L]
    [IsNoetherianRing R] (hdim : ringKrullDim R = 1)
    (A : Subring L) (hA : (algebraMap R L).range ≤ A) :
    IsNoetherianRing A := by
  -- Endow `A` with its canonical `R`-algebra structure (the map `R → L` lands in `A`).
  let : Algebra R A := ((algebraMap R L).codRestrict A (fun r => hA ⟨r, rfl⟩)).toAlgebra
  have : IsScalarTower R A L := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  -- A ring is Noetherian iff every ideal is finitely generated.
  rw [isNoetherianRing_iff_ideal_fg]
  intro I
  rcases eq_or_ne I ⊥ with rfl | hI
  · exact Submodule.fg_bot
  -- Step 3: nonzero `x ∈ R` with `(algebraMap R A x) ∈ I`.
  obtain ⟨x, hx0, hxI⟩ := exists_nonzero_mem_of_ne_bot R K L A I hI
  -- The principal ideal `J = xA ⊆ I`.
  set J : Ideal A := Ideal.span {algebraMap R A x}
  have hJI : J ≤ I := (Ideal.span_singleton_le_iff_mem _).mpr hxI
  -- Step 4: `A/J` has finite length over `R` (Stacks 00PF).
  have hlen : IsFiniteLength R (A ⧸ J) := isFiniteLength_quotient_smul R K L hdim A hx0
  -- Work with `I` and `J` as `A`-submodules of `A`.
  let I' : Submodule A A := I
  let J' : Submodule A A := J
  have hJI' : J' ≤ I' := hJI
  -- Step 1/2: the image of `I` in `A/J` is an `A`-submodule of a finite-length
  -- `R`-module, hence finitely generated over `A`.
  have hquot : (Submodule.map J'.mkQ I').FG :=
    fg_of_isFiniteLength_subring R hlen _
  -- Glue: `I ⊓ ker(mkQ) = J` is principal (FG), and the image is FG, so `I` is FG.
  have hJ'fg : J'.FG := by
    change (Ideal.span {algebraMap R A x}).FG
    exact Submodule.fg_span (Set.finite_singleton _)
  have hk : (I' ⊓ LinearMap.ker J'.mkQ).FG := by
    rw [Submodule.ker_mkQ, inf_of_le_right hJI']
    exact hJ'fg
  exact Submodule.fg_of_fg_map_of_fg_inf_ker J'.mkQ hquot hk

end
