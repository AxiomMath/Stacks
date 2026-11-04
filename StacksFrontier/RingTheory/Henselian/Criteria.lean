module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.RingTheory.Henselian
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
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Identities
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.Tactic.IntervalCases
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

/-!
# A normal local domain with separably closed fraction field is strictly henselian

Throughout, $(R, \mathfrak m, \kappa)$ is a commutative local ring with maximal ideal
$\mathfrak m$ and residue field $\kappa = R/\mathfrak m$.

Let $(R, \mathfrak m, \kappa)$ be a normal local domain: a local integral domain integrally
closed in its fraction field $K = \operatorname{Frac}(R)$. If $K$ is separably algebraically
closed then $R$ is strictly henselian, i.e. the residue field $\kappa$ is separably
algebraically closed and $R$ is a henselian local ring (Stacks tag 04GF).

## The encoding

`HenselianLocalRing R` says that for every monic $f \in R[X]$ and every $a_0 \in R$ with
$f(a_0) \in \mathfrak m$ and $f'(a_0)$ a unit there is $a \in R$ with $f(a) = 0$ and
$a - a_0 \in \mathfrak m$. `IsSepClosed k` says every separable nonconstant polynomial in
$k[X]$ has a root. A normal local domain is `IsLocalRing R`, `IsDomain R` and
`IsIntegrallyClosed R`, the last being integral closedness in the fraction field. "Strictly
henselian" is the conjunction `HenselianLocalRing R ∧ IsSepClosed (IsLocalRing.ResidueField R)`,
and $K$ is any field with `IsFractionRing R K`.

## Structure of the argument

Everything rests on one observation, `IsIntegrallyClosed.algebraMap_eq_of_integral`: because
`R` is integrally closed in `K`, any `x : K` integral over `R` is the image of an element of
`R`. Both halves are instances of the same engine — a root of a monic `R`-polynomial that is
separable over `K` actually lives in `R` — packaged as `sep_root_of_monic_mem_range` (L0) and
used to discharge `henselian_half` (L2) and `residue_sepClosed_half` (L1).
-/

@[expose] public section

open Polynomial IsLocalRing

/-- **L0 (shared engine).** Let `g : R[X]` be monic and let `Ω` be any field extension of
`K` (here we take `Ω = AlgebraicClosure K`). If `α : Ω` is a root of `g` (viewed over `R`
via `R → K → Ω`) and `α` is *separable over `K`*, then `α` lies in the image of `K`, and in
fact `α = (algebraMap K Ω) (algebraMap R K y)` for some `y : R`.

Reason: `α` is integral over `R` (root of the monic `g ∈ R[X]`), hence integral over `K`;
being separable over `K` and `K` separably closed, `α ∈ K`, say `α = algebraMap K Ω x` with
`x : K`. Then `x` is a root of `g` over `K`, so `x` is integral over `R`; by
`IsIntegrallyClosed.algebraMap_eq_of_integral` (R integrally closed in K) `x = algebraMap R K y`
for some `y : R`. -/
theorem sep_root_of_monic_mem_range
    (R : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] [IsSepClosed K]
    {g : Polynomial R} (hg : g.Monic)
    {x : K} (hx : Polynomial.aeval x (g.map (algebraMap R K)) = 0) :
    ∃ y : R, algebraMap R K y = x := by
  -- `x : K` is a root of the monic `g.map (algebraMap R K)`, hence integral over `R`;
  -- conclude by `IsIntegrallyClosed.algebraMap_eq_of_integral`.
  -- (This is the pure-`K` form of the engine; the separable-closure machinery is needed only
  --  to *produce* a root `x ∈ K`, which the callers do, not here.)
  have hxR : IsIntegral R x := by
    refine ⟨g, hg, ?_⟩
    rw [Polynomial.aeval_map_algebraMap] at hx
    exact hx
  exact IsIntegrallyClosed.algebraMap_eq_of_integral hxR

/-- If `F : K[X]` has nonzero derivative, then it has a separable irreducible factor.
(Proof by well-founded induction on factorizations: if every irreducible factor had zero
derivative then `F' = 0`.) -/
theorem exists_sep_irred_factor_of_deriv_ne {K : Type*} [Field K]
    (F : K[X]) (hF : derivative F ≠ 0) :
    ∃ q : K[X], Irreducible q ∧ q ∣ F ∧ q.Separable := by
  induction F using WfDvdMonoid.induction_on_irreducible with
  | zero => simp at hF
  | unit u hu =>
      exfalso; apply hF
      rw [Polynomial.eq_C_of_natDegree_eq_zero (Polynomial.natDegree_eq_zero_of_isUnit hu)]
      simp
  | mul b i hb_ne hi IH =>
      by_cases hider : derivative i = 0
      · have hd : derivative (i * b) = i * derivative b := by
          rw [Polynomial.derivative_mul, hider, zero_mul, zero_add]
        rw [hd] at hF
        have hdb : derivative b ≠ 0 := by
          intro h; rw [h, mul_zero] at hF; exact hF rfl
        obtain ⟨q, hq_irr, hq_dvd, hq_sep⟩ := IH hdb
        exact ⟨q, hq_irr, hq_dvd.trans (Dvd.intro_left i rfl), hq_sep⟩
      · refine ⟨i, hi, Dvd.intro b rfl, ?_⟩
        exact (Polynomial.separable_iff_derivative_ne_zero hi).mpr hider

/-- **Crux.** If the reduction `f̄ = f.map (residue R)` of a monic `f : R[X]` has nonzero
derivative, then `f` has a root in `R`.

Reason: `f̄' ≠ 0` gives `f' ≠ 0`, hence `F := f.map (algebraMap R K)` has `F' ≠ 0`, so `F`
has a separable irreducible factor `q` over `K`. As `K` is separably closed, `q` splits and
has a root `x ∈ K`, which is then a root of `F`. By the engine `sep_root_of_monic_mem_range`
`x = algebraMap R K y` for some `y : R`, and unwinding gives `f.eval y = 0`. -/
theorem root_of_residue_deriv_ne
    (R : Type*) [CommRing R] [IsLocalRing R] [IsDomain R] [IsIntegrallyClosed R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] [IsSepClosed K]
    {f : Polynomial R} (hf : f.Monic)
    (hfd : Polynomial.derivative (f.map (residue R)) ≠ 0) :
    ∃ c : R, f.IsRoot c := by
  have algInj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hf'0 : derivative f ≠ 0 := by
    intro h
    apply hfd
    rw [Polynomial.derivative_map, h, Polynomial.map_zero]
  set F : K[X] := f.map (algebraMap R K) with hFdef
  have hFd : derivative F ≠ 0 := by
    rw [hFdef, Polynomial.derivative_map]
    intro h
    apply hf'0
    apply Polynomial.map_injective _ algInj
    rw [h, Polynomial.map_zero]
  obtain ⟨q, hq_irr, hq_dvd, hq_sep⟩ := exists_sep_irred_factor_of_deriv_ne F hFd
  have hqsplit : q.Splits := IsSepClosed.splits_of_separable q hq_sep
  have hqdeg : q.degree ≠ 0 := by
    have hpos : 0 < q.natDegree := hq_irr.natDegree_pos
    intro h
    rw [Polynomial.degree_eq_natDegree (by
      intro hq0; rw [hq0] at hq_irr; exact hq_irr.ne_zero rfl)] at h
    exact (Nat.cast_ne_zero.mpr hpos.ne') h
  obtain ⟨x, hx⟩ := hqsplit.exists_eval_eq_zero hqdeg
  have hxF : Polynomial.aeval x F = 0 := by
    have hroot : F.IsRoot x := (Polynomial.IsRoot.dvd hx hq_dvd)
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    simpa [hFdef, Polynomial.map_map] using hroot
  obtain ⟨y, hy⟩ := sep_root_of_monic_mem_range R K hf hxF
  refine ⟨y, ?_⟩
  rw [← hy, hFdef] at hxF
  apply algInj
  rw [map_zero]
  rw [Polynomial.aeval_map_algebraMap] at hxF
  rw [Polynomial.aeval_algebraMap_apply] at hxF
  simpa using hxF

/-- **Separable-part factorization (the analytic heart of L2).** For a monic `f : R[X]` the
separable part of `f` over `K` splits over `K`, since `K` is separably closed, and each of its
roots lies in `R` by the engine `sep_root_of_monic_mem_range`. Collecting those roots gives a
monic `g = ∏ (X - cⱼ)` with `cⱼ : R` dividing `f`, with cofactor `Q : R[X]` whose reduction
`Q.map (residue R)` is purely inseparable, i.e. `(Q.map (residue R)).derivative = 0`, because
the inseparable irreducible factors of `f` over `K` lie in `K[Xᵖ]`.

The proof is a strong induction on `f.natDegree`: if the reduction of `f` already has zero
derivative take `cs = ∅` and `Q = f`, and otherwise peel off a root `c ∈ R` supplied by
`root_of_residue_deriv_ne` and recurse on `f /ₘ (X - C c)`. -/
theorem exists_separable_part_factor
    (R : Type*) [CommRing R] [IsLocalRing R] [IsDomain R] [IsIntegrallyClosed R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] [IsSepClosed K]
    {f : Polynomial R} (hf : f.Monic) :
    ∃ (cs : Multiset R) (Q : Polynomial R),
      f = (cs.map (fun c => X - C c)).prod * Q ∧
      Polynomial.derivative (Q.map (residue R)) = 0 := by
  -- Strong induction on `natDegree f`: if `f̄' = 0` take `cs = ∅, Q = f`; otherwise peel a
  -- root `c ∈ R` (crux) and recurse on `f /ₘ (X - C c)`.
  generalize hn : f.natDegree = n
  induction n using Nat.strong_induction_on generalizing f with
  | _ n IH =>
    by_cases hderiv : Polynomial.derivative (f.map (residue R)) = 0
    · exact ⟨0, f, by simp, hderiv⟩
    · obtain ⟨c, hc⟩ := root_of_residue_deriv_ne R K hf hderiv
      have hdvd : (X - C c) ∣ f := Polynomial.dvd_iff_isRoot.mpr hc
      obtain ⟨g, hg⟩ := hdvd
      have hgm : g.Monic := (Polynomial.monic_X_sub_C c).of_mul_monic_left (hg ▸ hf)
      have hdeg : g.natDegree < n := by
        rw [← hn, hg, Polynomial.natDegree_mul (Polynomial.monic_X_sub_C c).ne_zero hgm.ne_zero]
        simp
      obtain ⟨cs, Q, hfac, hQ⟩ := IH g.natDegree hdeg hgm rfl
      refine ⟨c ::ₘ cs, Q, ?_, hQ⟩
      rw [hg, hfac, Multiset.map_cons, Multiset.prod_cons]
      ring

/-- **L2 (henselian half).** Under the hypotheses, `R` is a henselian local ring.

Via `HenselianLocalRing.TFAE R` (clause 1, the residue-field root-lifting form) it suffices:
for every monic `f : R[X]` and `a₀ : κ` with `aeval a₀ f = 0` and `aeval a₀ f' ≠ 0`, to find
`a : R` with `f.IsRoot a` and `residue R a = a₀`.

The argument, valid in characteristic `p`: from `exists_separable_part_factor` write
`f = g * Q` with `g = ∏ (X - cⱼ)` (cⱼ : R) and `(Q.map (residue R))' = 0`. Reducing mod `m`,
`f̄ = ḡ · Q̄` and `f̄' = ḡ' · Q̄` (as `Q̄' = 0`). Since `a₀` is a *simple* root of `f̄`
(`h0 : f̄(a₀) = 0`, `h0' : f̄'(a₀) ≠ 0`), `f̄'(a₀) = ḡ'(a₀)·Q̄(a₀) ≠ 0` forces `Q̄(a₀) ≠ 0`,
so `ḡ(a₀) = 0`. As `ḡ = ∏ (X - residue cⱼ)`, some `cⱼ` has `residue cⱼ = a₀`; and `cⱼ` is a
root of `f` because `(X - cⱼ) ∣ g ∣ f`. -/
theorem henselian_half
    (R : Type*) [CommRing R] [IsLocalRing R] [IsDomain R] [IsIntegrallyClosed R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] [IsSepClosed K] :
    HenselianLocalRing R := by
  refine ((HenselianLocalRing.TFAE R).out 1 2).mpr ?_
  intro f hf a₀ h0 h0'
  obtain ⟨cs, Q, hfac, hQ⟩ := exists_separable_part_factor R K hf
  set g : Polynomial R := (cs.map (fun c => X - C c)).prod with hg_def
  have hfbar : f.map (residue R) = (g.map (residue R)) * (Q.map (residue R)) := by
    rw [hfac, Polynomial.map_mul]
  have hderiv : Polynomial.derivative (f.map (residue R))
      = Polynomial.derivative (g.map (residue R)) * (Q.map (residue R)) := by
    rw [hfbar, Polynomial.derivative_mul, hQ, mul_zero, add_zero]
  have key : ∀ p : Polynomial R,
      Polynomial.aeval a₀ p = Polynomial.eval a₀ (p.map (residue R)) := fun p => by
    rw [Polynomial.eval_map]; rfl
  have hroot : (f.map (residue R)).IsRoot a₀ := by
    rw [Polynomial.IsRoot, ← key, h0]
  have hnroot' : ¬ (Polynomial.derivative (f.map (residue R))).IsRoot a₀ := by
    intro hc
    apply h0'
    rw [key, ← Polynomial.derivative_map]
    exact hc
  have hQa : Polynomial.eval a₀ (Q.map (residue R)) ≠ 0 := by
    intro hc
    apply hnroot'
    rw [Polynomial.IsRoot, hderiv, Polynomial.eval_mul, hc, mul_zero]
  have hga : Polynomial.eval a₀ (g.map (residue R)) = 0 := by
    have hr := hroot
    rw [Polynomial.IsRoot, hfbar, Polynomial.eval_mul] at hr
    rcases mul_eq_zero.mp hr with h | h
    · exact h
    · exact absurd h hQa
  have hgbar : g.map (residue R)
      = (Multiset.map (fun a => X - C a) (cs.map (residue R))).prod := by
    rw [hg_def, Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
    apply congrArg
    apply Multiset.map_congr rfl
    intro c _
    simp [Function.comp, Polynomial.map_sub]
  have hgbar_ne : g.map (residue R) ≠ 0 := by
    rw [hgbar]; exact Polynomial.monic_multiset_prod_of_monic _ _
      (fun a _ => Polynomial.monic_X_sub_C a) |>.ne_zero
  have hmem : a₀ ∈ (g.map (residue R)).roots :=
    (Polynomial.mem_roots hgbar_ne).mpr hga
  rw [hgbar, Polynomial.roots_multiset_prod_X_sub_C] at hmem
  obtain ⟨c, hc_mem, hc_eq⟩ := Multiset.mem_map.mp hmem
  refine ⟨c, ?_, hc_eq⟩
  rw [Polynomial.IsRoot, hfac, Polynomial.eval_mul]
  have hdvd : (X - C c) ∣ g :=
    Multiset.dvd_prod (Multiset.mem_map.mpr ⟨c, hc_mem, rfl⟩)
  obtain ⟨q, hq⟩ := hdvd
  rw [hg_def] at hq ⊢
  rw [hq, Polynomial.eval_mul]; simp

/-- **L1 (residue field half).** Under the hypotheses, `κ = ResidueField R` is separably
algebraically closed.

Via `IsSepClosed.of_exists_root` it suffices: every monic irreducible separable
`ḡ : κ[X]` has a root in `κ`. Lift `ḡ` to a monic `g : R[X]` of the same degree (lift each
coefficient along the surjection `residue R`). A root `α` of `g` in `Ω = AlgebraicClosure K`
that is separable over `K` lies in `R` by **L0** (its reduction is then a root of `ḡ`); such
a separable root exists because `ḡ` is separable, so the corresponding factor of `g` over
`K` is separable. The reduction of the obtained `y : R` is the required root of `ḡ` in `κ`. -/
@[sga "7 I 0.0.3" "partial"]
theorem residue_sepClosed_half
    (R : Type*) [CommRing R] [IsLocalRing R] [IsDomain R] [IsIntegrallyClosed R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] [IsSepClosed K] :
    IsSepClosed (IsLocalRing.ResidueField R) := by
  -- Reduce via `IsSepClosed.of_exists_root` to: every monic irreducible separable
  -- `ḡ ∈ κ[X]` has a root in `κ`. Lift to monic `g ∈ R[X]`, apply `root_of_residue_deriv_ne`
  -- to get an R-root c, then reduce mod m: `residue R c` is the required root of `ḡ`.
  apply IsSepClosed.of_exists_root
  intro gbar hg_monic hg_irr hg_sep
  -- Lift `gbar` to a monic `g : R[X]` along the surjective residue map.
  have hsurj : Function.Surjective (residue R) := IsLocalRing.residue_surjective
  obtain ⟨g₀, hg₀⟩ := Polynomial.map_surjective (residue R) hsurj gbar
  have hmem : gbar ∈ Polynomial.lifts (residue R) :=
    (Polynomial.mem_lifts gbar).mpr ⟨g₀, hg₀⟩
  obtain ⟨g, hg_map, _, hg_mon⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hmem hg_monic
  -- `gbar` is separable & irreducible, so its derivative is nonzero.
  have hgder : Polynomial.derivative gbar ≠ 0 :=
    (Polynomial.separable_iff_derivative_ne_zero hg_irr).mp hg_sep
  have hfd : Polynomial.derivative (g.map (residue R)) ≠ 0 := by
    rw [hg_map]; exact hgder
  -- Apply the crux to get an `R`-root `c` of `g`.
  obtain ⟨c, hc⟩ := root_of_residue_deriv_ne R K hg_mon hfd
  -- `residue R c` is a root of `gbar`.
  refine ⟨residue R c, ?_⟩
  have heval : (g.map (residue R)).eval (residue R c) = residue R (g.eval c) := by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
  rw [← hg_map, heval, hc, map_zero]

/-- **Stacks Tag 04GF.** Let `R` be a normal local domain (a local integral domain that
is integrally closed in its fraction field `K`). If `K` is separably algebraically
closed, then `R` is strictly henselian, i.e. `R` is a henselian local ring and its
residue field is separably algebraically closed. -/
@[stacks 04GF, sga "7 I 0.0.3" "partial"]
theorem normal_local_domain_sepClosed_fractionField_isStrictlyHenselian
    (R : Type*) [CommRing R] [IsLocalRing R] [IsDomain R] [IsIntegrallyClosed R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] [IsSepClosed K] :
    HenselianLocalRing R ∧ IsSepClosed (IsLocalRing.ResidueField R) :=
  ⟨henselian_half R K, residue_sepClosed_half R K⟩

-- ===== merged from StacksDraft.Ch10.Sec153.Tag04GM =====


/-- A complete local ring is Henselian: `IsAdicComplete.henselianRing` provides
the lifting property, and we transport the simple-root hypothesis along
`Ideal.Quotient.mk`. -/
@[stacks 04GM,
  ega "IV 18.5.14" "local case",
  ega "IV 18.5.16" "special case",
  sga "3 X 4.0" "partial"]
theorem henselianLocalRing_of_isAdicComplete_maximalIdeal
    (R : Type*) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] :
    HenselianLocalRing R :=
  .mk fun f hf a₀ ha₀ ha₀' =>
    (IsAdicComplete.henselianRing R _).is_henselian f hf a₀ ha₀
      (ha₀'.map (Ideal.Quotient.mk _))

-- ===== merged from StacksDraft.Ch10.Sec153.Tag06RR =====


open Polynomial

/-- If `f.eval a = 0`, then `f = (X - C a) * h` for some `h` with `h.eval a = f'.eval a`. -/
private lemma hensel_factor {R : Type*} [CommRing R] (f : Polynomial R) (a : R)
    (hfa : f.eval a = 0) :
    ∃ h : Polynomial R, f = (X - C a) * h ∧ h.eval a = (derivative f).eval a := by
  obtain ⟨h, h_eq⟩ : (X - C a) ∣ f := dvd_iff_isRoot.mpr hfa
  refine ⟨h, h_eq, ?_⟩
  rw [h_eq, derivative_mul]
  simp

/-- Hensel uniqueness: in a local ring, two roots of a polynomial that are
congruent modulo the maximal ideal must be equal, provided the formal
derivative at one of them is not in the maximal ideal. -/
@[stacks 06RR, sga "3 VIIB 1.6" "partial"]
theorem hensel_uniqueness {R : Type*} [CommRing R] [IsLocalRing R]
    (f : Polynomial R) (a b : R)
    (hfa : f.eval a = 0) (hfb : f.eval b = 0)
    (hab : a - b ∈ IsLocalRing.maximalIdeal R)
    (hf' : (Polynomial.derivative f).eval a ∉ IsLocalRing.maximalIdeal R) :
    a = b := by
  obtain ⟨h, hfact, hha⟩ := hensel_factor f a hfa
  -- Evaluate `f = (X - C a) * h` at `b` to obtain `(b - a) * h.eval b = 0`.
  have hb_eval : (b - a) * h.eval b = 0 := by
    have hev := congrArg (Polynomial.eval b) hfact
    simp only [eval_mul, eval_sub, eval_X, eval_C] at hev
    rw [← hev, hfb]
  -- Taylor expansion: `h.eval b = f'(a) + (b - a) * c` for some `c`.
  obtain ⟨c, hc⟩ : ∃ c : R, h.eval b = h.eval a + (b - a) * c :=
    (Polynomial.sub_dvd_eval_sub b a h).imp fun _ hc ↦ by linear_combination hc
  rw [hha] at hc
  have hba : b - a ∈ IsLocalRing.maximalIdeal R := by
    rw [show b - a = -(a - b) by ring]
    exact (IsLocalRing.maximalIdeal R).neg_mem hab
  -- If `h.eval b ∈ m`, then `f'(a) = h.eval b - (b - a) * c ∈ m`, contradicting `hf'`.
  have hhb_not_mem : h.eval b ∉ IsLocalRing.maximalIdeal R := fun hmem => hf' <| by
    rw [show (Polynomial.derivative f).eval a = h.eval b - (b - a) * c by linear_combination -hc]
    exact (IsLocalRing.maximalIdeal R).sub_mem hmem
      ((IsLocalRing.maximalIdeal R).mul_mem_right c hba)
  have hunit : IsUnit (h.eval b) := by
    by_contra hu
    exact hhb_not_mem hu
  have hba_zero : b - a = 0 :=
    (IsUnit.mul_right_eq_zero hunit).mp (by rw [mul_comm]; exact hb_eval)
  linear_combination -hba_zero

-- ===== merged from StacksDraft.Ch10.Sec153.Tag06RS =====

/-!
# A local ring of Krull dimension zero is henselian

Throughout, `R` is a commutative ring; when `R` is local, `m` denotes its maximal ideal and
`k = R/m` its residue field, and for `f` in `R[T]` we write `f'` for the formal derivative
with respect to `T`.

A local ring `(R, m, k)` is *henselian* if for every monic `f` in `R[T]` and every `a₀` in
`R` with `f(a₀)` in `m` and `f'(a₀)` a unit — that is, the image of `a₀` is a simple root of
the image of `f` — there is `a` in `R` with `f(a) = 0` and `a - a₀` in `m`. This is Mathlib's
`HenselianLocalRing`, whose defining field `HenselianLocalRing.is_henselian` states exactly
that. A local ring is never the zero ring, so its maximal ideal is a genuine prime and Krull
dimension `0` coincides with Krull dimension at most `0`, spelled `Ring.KrullDimLE 0 R`:
every prime ideal is maximal.

The theorem is that a local ring of dimension `0` is henselian. Instead of the
finite-algebra characterization used in the Stacks proof, the argument here is the
self-contained Newton iteration, which is valid for an arbitrary local ring of Krull
dimension `0`: no Noetherian, Artinian or `m`-adic completeness hypothesis is needed, and
indeed `m`-adic completeness can fail for such a ring.

The pieces are:

* (A) In a local ring of Krull dimension `0`, `maximalIdeal R = nilradical R`, so every
  element of `m` is nilpotent (`KrullDimLE0.maximalIdeal_eq_nilradical`).
* (B) **One Newton step.** For `f : R[X]`, `a : R` and `u : R` with
  `f.derivative.eval a * u = 1`, put `a' = a - f.eval a * u`. Then
  `f.eval a' = (f.eval a) ^ 2 * c` for some `c : R`, and `a' - a = -(f.eval a * u)`
  (`Polynomial.newton_one_step`).
* (C) **Newton convergence at a nilpotent value.** If `f.eval a₀` is nilpotent and
  `f.derivative.eval a₀` is a unit, then `f` has a genuine root `a` with
  `a - a₀ ∈ Ideal.span {f.eval a₀}`, hence in any ideal containing `f.eval a₀`. The error
  after `n` Newton steps lies in `(f.eval a₀) ^ (2 ^ n)`, which vanishes once `2 ^ n`
  exceeds the nilpotency degree, and `f.derivative.eval aₙ` stays a unit because `aₙ ≡ a₀`
  modulo the nil ideal generated by `f.eval a₀`
  (`Polynomial.exists_isRoot_of_isNilpotent_eval`).
* (D) Assembling: under the henselian hypotheses `f.eval a₀ ∈ m = nilradical` is nilpotent
  by (A), so (C) gives a root `a` with `a - a₀ ∈ span {f.eval a₀} ⊆ m`.
-/

@[expose] public section

open Polynomial IsLocalRing

/-- **(A)** In a Krull-dimension-0 local ring, the maximal ideal equals the nilradical.

Since `nilradical R = sInf {J | J.IsPrime}` and the maximal ideal `m` is prime, one
inequality is `nilradical R ≤ m`. Conversely `Ring.KrullDimLE 0 R` makes every prime ideal
maximal, and in a local ring the unique maximal ideal is `m`, so every prime equals `m`;
thus `m` is itself the infimum defining the nilradical, giving `m = nilradical R`. -/
lemma KrullDimLE0.maximalIdeal_eq_nilradical
    (R : Type*) [CommRing R] [IsLocalRing R] [Ring.KrullDimLE 0 R] :
    maximalIdeal R = nilradical R := by
  apply le_antisymm
  · rw [nilradical_eq_sInf]
    apply le_sInf
    intro p hp
    have hpm : p.IsMaximal := Ideal.IsPrime.isMaximal' hp
    rw [IsLocalRing.eq_maximalIdeal hpm]
  · exact nilradical_le_prime _

/-- **(A')** Consequence: every element of the maximal ideal of a dim-0 local ring is
nilpotent.  Direct from `KrullDimLE0.maximalIdeal_eq_nilradical` and
`mem_nilradical : x ∈ nilradical R ↔ IsNilpotent x`. -/
lemma KrullDimLE0.isNilpotent_of_mem_maximalIdeal
    (R : Type*) [CommRing R] [IsLocalRing R] [Ring.KrullDimLE 0 R]
    {x : R} (hx : x ∈ maximalIdeal R) : IsNilpotent x := by
  rw [KrullDimLE0.maximalIdeal_eq_nilradical R] at hx
  exact (mem_nilradical).mp hx

/-- **(B)** One Newton step. Let `f : R[X]`, `a : R`, and `u : R` with
`f.derivative.eval a * u = 1` (so `f.derivative.eval a` is a unit with inverse `u`).
Put `a' = a - f.eval a * u`. Then there is `c` with `f.eval a' = (f.eval a)^2 * c`, and
`a' - a = -(f.eval a * u)`.

Write `a' = a + y` with `y = -(f.eval a * u)`. By `Polynomial.binomExpansion`,
`f.eval (a + y) = f.eval a + f.derivative.eval a * y + k * y ^ 2` for some `k`. Using
`f.derivative.eval a * u = 1` one gets
`f.derivative.eval a * y = -(f.derivative.eval a * u) * f.eval a = -(f.eval a)`, so
`f.eval a + f.derivative.eval a * y = 0` and
`f.eval a' = k * y ^ 2 = (f.eval a) ^ 2 * (k * u ^ 2)`; take `c = k * u ^ 2`. -/
@[sga "3 VIIB 1.6" "partial"]
lemma Polynomial.newton_one_step {R : Type*} [CommRing R] (f : R[X]) (a u : R)
    (hu : f.derivative.eval a * u = 1) :
    ∃ c : R, f.eval (a - f.eval a * u) = (f.eval a) ^ 2 * c := by
  obtain ⟨k, hk⟩ := f.binomExpansion a (-(f.eval a * u))
  refine ⟨k * u ^ 2, ?_⟩
  rw [show a - f.eval a * u = a + (-(f.eval a * u)) by ring, hk]
  linear_combination (-(f.eval a)) * hu

/-- **(C)** Newton convergence at a nilpotent value (the analytic kernel).

If `f.eval a₀` is nilpotent and `f.derivative.eval a₀` is a unit, then `f` has a genuine root
`a` with `a - a₀` a multiple of `f.eval a₀` (hence `a - a₀ ∈ Ideal.span {f.eval a₀}`).

The argument is a terminating Newton iteration. Let `c₀ = f.eval a₀`, nilpotent of degree
`N` (`c₀ ^ N = 0`). We build a sequence `aₙ` by Newton's step (B):
`a_{n+1} = aₙ - (f.eval aₙ) * uₙ`, where `uₙ` is an inverse of `f.derivative.eval aₙ`.
Two invariants are maintained by induction on `n`:
  (i) `aₙ - a₀ ∈ Ideal.span {c₀}` — because each increment `a_{n+1} - aₙ` is a multiple of
      `f.eval aₙ`, and `f.eval aₙ ∈ span {c₀}` (shown by (ii));
  (ii) `f.eval aₙ ∈ (Ideal.span {c₀}) ^ (2^n)` — base case `n=0` is `c₀ ∈ span{c₀}`; the
      inductive step is exactly (B): `f.eval a_{n+1} = (f.eval aₙ)^2 * c`, and squaring an
      element of `(span{c₀})^(2^n)` lands in `(span{c₀})^(2^{n+1})`.
For the step to be legal we need `f.derivative.eval aₙ` to remain a unit: since
`aₙ - a₀ ∈ span{c₀}` and `c₀` is nilpotent, `aₙ - a₀` is nilpotent, so
`f.derivative.eval aₙ - f.derivative.eval a₀ ∈ span{aₙ - a₀}` (a difference of polynomial
evaluations is divisible by the difference of points) is nilpotent; a unit plus a nilpotent
is a unit (`IsUnit.add_isNilpotent` / `IsNilpotent.isUnit_add_left` style), so
`f.derivative.eval aₙ` is a unit.
Now pick `n` with `2^n ≥ N`. Then `(span{c₀})^(2^n) ≤ (span{c₀})^N = span{c₀^N} = span{0} = 0`
(using `c₀^N = 0`), so `f.eval aₙ = 0`. Set `a = aₙ`; then `f.IsRoot a` and
`a - a₀ ∈ span{c₀}` by (i). -/
@[sga "3 VIIB 1.6" "partial"]
lemma Polynomial.exists_isRoot_of_isNilpotent_eval {R : Type*} [CommRing R] (f : R[X])
    (a₀ : R) (hnil : IsNilpotent (f.eval a₀)) (hu : IsUnit (f.derivative.eval a₀)) :
    ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ Ideal.span {f.eval a₀} := by
  obtain ⟨N, hN⟩ := hnil
  suffices Q : ∀ n : ℕ, ∀ b : R, (f.eval b) ^ n = 0 → IsUnit (f.derivative.eval b) →
      ∃ a : R, f.eval a = 0 ∧ a - b ∈ Ideal.span {f.eval b} by
    exact Q N a₀ hN hu
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro b hb hub
    by_cases hc : f.eval b = 0
    · exact ⟨b, hc, by simp⟩
    · -- f.eval b ≠ 0, so n ≥ 2
      have hn2 : 2 ≤ n := by
        by_contra h
        rw [Nat.not_le] at h
        interval_cases n
        · simp only [pow_zero] at hb
          exact hc (by rw [← one_mul (f.eval b), hb, zero_mul])
        · simp only [pow_one] at hb
          exact hc hb
      -- Newton step
      obtain ⟨u, huinv⟩ := hub.exists_right_inv
      set a₁ := b - f.eval b * u with ha₁def
      obtain ⟨c, hc2⟩ := f.newton_one_step b u huinv
      -- a₁ - b = -(f.eval b * u), a multiple of f.eval b
      have hincr : a₁ - b = -(f.eval b * u) := by rw [ha₁def]; ring
      have hincr_mem : a₁ - b ∈ Ideal.span {f.eval b} := by
        rw [hincr, Ideal.mem_span_singleton]
        exact Dvd.intro (-u) (by ring)
      -- f.eval b nilpotent
      have hbnil : IsNilpotent (f.eval b) := ⟨n, hb⟩
      -- a₁ - b nilpotent
      have hincr_nil : IsNilpotent (a₁ - b) := by
        rw [hincr]
        exact (Commute.isNilpotent_mul_right (Commute.all _ _) hbnil).neg
      -- unit persistence
      have hub1 : IsUnit (f.derivative.eval a₁) := by
        have hdvd : a₁ - b ∣ f.derivative.eval a₁ - f.derivative.eval b :=
          Polynomial.sub_dvd_eval_sub a₁ b f.derivative
        obtain ⟨d, hd⟩ := hdvd
        have hnil2 : IsNilpotent (f.derivative.eval a₁ - f.derivative.eval b) := by
          rw [hd]
          exact Commute.isNilpotent_mul_right (Commute.all _ _) hincr_nil
        have he : f.derivative.eval a₁ =
            (f.derivative.eval b) + (f.derivative.eval a₁ - f.derivative.eval b) := by ring
        rw [he]
        exact hnil2.isUnit_add_left_of_commute hub (Commute.all _ _)
      -- exponent reduction
      set m := (n + 1) / 2 with hmdef
      have hmlt : m < n := by omega
      have hm2 : n ≤ 2 * m := by omega
      have heval1_pow : (f.eval a₁) ^ m = 0 := by
        rw [hc2, mul_pow, ← pow_mul]
        have hbz : (f.eval b) ^ (2 * m) = 0 := by
          calc (f.eval b) ^ (2 * m) = (f.eval b) ^ n * (f.eval b) ^ (2 * m - n) := by
                rw [← pow_add]; congr 1; omega
            _ = 0 := by rw [hb, zero_mul]
        rw [hbz, zero_mul]
      -- apply IH
      obtain ⟨a, ha0, hamem⟩ := ih m hmlt a₁ heval1_pow hub1
      refine ⟨a, ha0, ?_⟩
      -- a - b = (a - a₁) + (a₁ - b)
      have hspan_le : Ideal.span {f.eval a₁} ≤ Ideal.span {f.eval b} := by
        rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
        rw [hc2]
        exact Dvd.intro_left ((f.eval b) * c) (by ring)
      have h1 : a - a₁ ∈ Ideal.span {f.eval b} := hspan_le hamem
      have hsum : a - b = (a - a₁) + (a₁ - b) := by ring
      rw [hsum]
      exact Ideal.add_mem _ h1 hincr_mem

/-- **Stacks Tag 06RS / Lemma 10.153.10.** A local ring of Krull dimension `0` is henselian. -/
@[stacks 06RS]
theorem henselianLocalRing_of_krullDimLE_zero (R : Type*) [CommRing R] [IsLocalRing R]
  [Ring.KrullDimLE 0 R] :
    HenselianLocalRing R := by
  -- (D) Assemble. Build the `HenselianLocalRing` structure from its `is_henselian` field.
  refine { is_henselian := ?_ }
  intro f _hmonic a₀ hfa₀ hderiv
  -- `f.eval a₀ ∈ m = nilradical` is nilpotent (fact A).
  have hnil : IsNilpotent (f.eval a₀) :=
    KrullDimLE0.isNilpotent_of_mem_maximalIdeal R hfa₀
  -- Newton convergence (fact C) yields a root with `a - a₀` a multiple of `f.eval a₀`.
  obtain ⟨a, hroot, hmem⟩ := f.exists_isRoot_of_isNilpotent_eval a₀ hnil hderiv
  refine ⟨a, hroot, ?_⟩
  -- `a - a₀ ∈ span {f.eval a₀} ⊆ m`, since `f.eval a₀ ∈ m` and `m` is an ideal.
  have hsub : Ideal.span {f.eval a₀} ≤ maximalIdeal R :=
    (Ideal.span_singleton_le_iff_mem _).mpr hfa₀
  exact hsub hmem
