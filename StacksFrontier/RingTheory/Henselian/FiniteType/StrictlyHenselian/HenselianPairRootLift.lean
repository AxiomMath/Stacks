module

import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.Localization.Away.Lemmas
import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import StacksFrontier.RingTheory.Henselian.FiniteType.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.Henselian.FiniteType.StrictlyHenselian.FiniteIdempotent

/-!
# Root lifting and the henselian pair `(A, m·A)`

Lifting approximate simple roots of monic polynomials along `m·A` for `A` module-finite over a
henselian local ring `R`, giving that `(A, m·A)` is a henselian pair.
-/

section

universe u

@[expose] public section

open IsLocalRing

/-- **Coprimality building block.** Over any commutative ring `K`, if `g₁(0)` is a unit then
`X` and `g₁` are coprime in `K[X]`, by the Bézout identity
`C(g₁(0)⁻¹)·g₁ - C(g₁(0)⁻¹)·q·X = 1` where `g₁ = C(g₁(0)) + X·q`. Used for the simple-root
split `ḡ = X·g₁` over `Ā = A/mA`. -/
theorem rootlift_isCoprime_X_g1 (K : Type) [CommRing K] (g1 : Polynomial K)
    (h : IsUnit (g1.eval 0)) : IsCoprime (Polynomial.X : Polynomial K) g1 := by
  have hdvd : (Polynomial.X : Polynomial K) ∣ (g1 - Polynomial.C (g1.eval 0)) := by
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]; simp
  obtain ⟨q, hq⟩ := hdvd
  have hg1 : g1 = Polynomial.C (g1.eval 0) + Polynomial.X * q := by linear_combination hq
  obtain ⟨u, hu⟩ := h
  set v : K := ((u⁻¹ : Kˣ) : K) with hv
  refine ⟨-Polynomial.C v * q, Polynomial.C v, ?_⟩
  have hvc : v * (g1.eval 0) = 1 := by
    rw [hv, ← hu]; simp [← Units.val_mul]
  have hkey : Polynomial.C v * g1 + (-Polynomial.C v * q) * Polynomial.X = 1 := by
    rw [hg1]; ring_nf
    rw [show
        Polynomial.C v * Polynomial.C (Polynomial.eval 0 g1) =
          Polynomial.C (v * Polynomial.eval 0 g1)
        by rw [Polynomial.C_mul],
      hvc, Polynomial.C_1]
  linear_combination hkey

/-- Extending `I` along `R → A → B` in two steps agrees with extending it directly along `R → B`. -/
private theorem map_map_algebraMap {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] (I : Ideal R) :
    (I.map (algebraMap R A)).map (algebraMap A B) = I.map (algebraMap R B) := by
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]

/-- **The approximate simple-root idempotent.**
Constructs an APPROXIMATE idempotent `b₀ ∈ B = AdjoinRoot g` cutting out the simple-root
component: `b₀² - b₀ ∈ mB`, `ξ·b₀ ∈ mB` and `b₀ ∉ mB`, together with the two residue facts
that pin `b₀` to the rank-1 factor (cyclic and faithful mod `mB`). This is a pure CRT and
base-change construction, with no Nakayama step and no henselian input; the Hensel lift to a
genuine idempotent happens in the caller.

Here `mB = mA.map (of g)`, and base change gives `B/mB ≅ Ā[X]/(ḡ)` with `ḡ = X·g₁`, where
`X ∣ ḡ` because `ḡ(0) = 0` and `g₁(0)` is a unit by `hgd`. Then
`span {ḡ} = span {X} · span {g₁}` with `IsCoprime X g₁` (`rootlift_isCoprime_X_g1`), so CRT
(`Ideal.quotientMulEquivQuotientProd`) gives `B/mB ≅ (Ā[X]/X) × (Ā[X]/g₁)`; take
`ē₀ := Φ.symm (1, 0)` and lift it to `b₀`. Then `ξ̄·ē₀ = 0` gives `ξ·b₀ ∈ mB`, and `ē₀ ≠ 0`
gives `b₀ ∉ mB`, the first factor `Ā[X]/X ≅ Ā` being nontrivial since `[Nontrivial A]` forces
`mA ≠ ⊤`. -/
theorem rootlift_approx_idempotent_exists (R : Type) [CommRing R] [HenselianLocalRing R] (A : Type)
    [CommRing A] [Algebra R A] [Module.Finite R A] [Nontrivial A] (g : Polynomial A)
    (hg0 : Polynomial.eval 0 g ∈ ((maximalIdeal R).map (algebraMap R A)))
    (hgd :
      IsUnit
        ((Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R A)))
          (Polynomial.eval 0 (Polynomial.derivative g)))) :
    ∃ b₀ : AdjoinRoot g,
      (b₀ * b₀ - b₀ ∈ ((maximalIdeal R).map (algebraMap R (AdjoinRoot g)))) ∧
        ((AdjoinRoot.root g) * b₀ ∈ ((maximalIdeal R).map (algebraMap R (AdjoinRoot g)))) ∧
        (b₀ ∉ ((maximalIdeal R).map (algebraMap R (AdjoinRoot g)))) ∧
        -- (★ CYCLIC mod mB): `Ā·b̄₀` generates `b̄₀·B̄`, the rank-1 simple-root factor.
        (∀ y : AdjoinRoot g,
          ∃ r : A,
            y * b₀ - (algebraMap A (AdjoinRoot g) r) * b₀ ∈
              ((maximalIdeal R).map (algebraMap R (AdjoinRoot g)))) ∧
        -- (★ FAITHFUL mod mB): the reduction `ψ̄ : Ā → b̄₀·B̄, r̄ ↦ r̄·b̄₀` is injective.
        (∀ r : A,
          (algebraMap A (AdjoinRoot g) r) * b₀ ∈
              ((maximalIdeal R).map (algebraMap R (AdjoinRoot g))) →
            r ∈ ((maximalIdeal R).map (algebraMap R A))) := by
  -- All five facts depend only on `b₀` mod `mB`, so they may be read off in `B̄ = Ā[X]/(ḡ)`.
  -- A non-local `A`, say `A = R × R`, is covered at every degree: the `(1,0)` X-component
  -- stays of rank 1 on every residue factor. The degenerate `g = X²` is excluded by `hgd`,
  -- since there `g'(0) = 0` is not a unit; for a genuine `ḡ = X·g₁` the constructed
  -- `(1,0)`-CRT idempotent `b₀` works.
  set mA := (maximalIdeal R).map (algebraMap R A) with hmA
  set mk := Ideal.Quotient.mk mA with hmk
  set gbar : Polynomial (A ⧸ mA) := g.map mk with hgbar
  have hmBeq : (maximalIdeal R).map (algebraMap R (AdjoinRoot g)) = mA.map (AdjoinRoot.of g) := by
    exact (map_map_algebraMap _).symm
  have hgbar0 : gbar.eval 0 = mk (g.eval 0) := by
    rw [hgbar, Polynomial.eval_map, Polynomial.eval₂_at_zero, Polynomial.coeff_zero_eq_eval_zero]
  have hXdvd : (Polynomial.X : Polynomial (A ⧸ mA)) ∣ gbar := by
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero, hgbar0]
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr hg0
  obtain ⟨g1, hg1⟩ := hXdvd
  have hg1unit : IsUnit (g1.eval 0) := by
    have hder : gbar.derivative = g1 + Polynomial.X * g1.derivative := by
      rw [hg1, Polynomial.derivative_mul, Polynomial.derivative_X]; ring
    have hgbarder0 : gbar.derivative.eval 0 = g1.eval 0 := by
      rw [hder]; simp
    have hmap : gbar.derivative.eval 0 = mk (g.derivative.eval 0) := by
      rw [hgbar, Polynomial.derivative_map, Polynomial.eval_map, Polynomial.eval₂_at_zero,
        Polynomial.coeff_zero_eq_eval_zero]
    rw [hgbarder0] at hmap
    rw [hmap]; exact hgd
  have hcop : IsCoprime (Polynomial.X : Polynomial (A ⧸ mA)) g1 :=
    rootlift_isCoprime_X_g1 (A ⧸ mA) g1 hg1unit
  -- Ā = A⧸mA is nontrivial (mA ≠ ⊤ since mA ≤ jacobson ⊥ ≠ ⊤ for nontrivial A).
  have hAbar_nt : Nontrivial (A ⧸ mA) := by
    have hle := mA_le_jacobson R A
    have hjac : Ideal.jacobson (⊥ : Ideal A) ≠ ⊤ := by
      rw [Ne, Ideal.jacobson_eq_top_iff]; exact bot_ne_top
    have hne : mA ≠ ⊤ := by
      rw [hmA]; exact fun h => hjac (top_le_iff.mp (h ▸ hle))
    exact Ideal.Quotient.nontrivial_iff.mpr hne
  set IX : Ideal (Polynomial (A ⧸ mA)) := Ideal.span {Polynomial.X} with hIX
  set Ig : Ideal (Polynomial (A ⧸ mA)) := Ideal.span {g1} with hIg
  have hspan : Ideal.span {gbar} = IX * Ig := by
    rw [hIX, hIg, Ideal.span_singleton_mul_span_singleton, hg1]
  have hcopI : IsCoprime IX Ig := by
    rw [hIX, hIg, Ideal.isCoprime_span_singleton_iff]; exact hcop
  set q := Ideal.Quotient.mk (mA.map (AdjoinRoot.of g)) with hq
  -- the composite iso Φ : B/mB ≃+* (Ā[X]/X) × (Ā[X]/g₁), kept OPAQUE (clear_value) after
  -- proving the `key` computation, so later `map_mul`/`map_sub` rewrites stay cheap.
  obtain ⟨Φ, key⟩ :
    ∃ Φ :
      (AdjoinRoot g ⧸ mA.map (AdjoinRoot.of g)) ≃+*
        ((Polynomial (A ⧸ mA) ⧸ IX) × (Polynomial (A ⧸ mA) ⧸ Ig)),
      ∀ p : Polynomial A,
        Φ (q (AdjoinRoot.mk g p)) =
          (Ideal.Quotient.mk IX (p.map mk), Ideal.Quotient.mk Ig (p.map mk)) :=
    by
    refine
      ⟨((AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot mA g).trans
              (Ideal.quotEquivOfEq hspan)).trans
          (Ideal.quotientMulEquivQuotientProd IX Ig hcopI),
        ?_⟩
    intro p
    change
      (Ideal.quotientMulEquivQuotientProd IX Ig hcopI)
          ((Ideal.quotEquivOfEq hspan)
            ((AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot mA g) (q (AdjoinRoot.mk g p)))) =
        _
    rw [AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot_mk_of]; rfl
  -- iso κ : (Ā[X]/X) ≃+* Ā, with κ (mk_IX (C c)) = c; also kept opaque.
  obtain ⟨κ, hκC⟩ :
    ∃ κ : (Polynomial (A ⧸ mA) ⧸ IX) ≃+* (A ⧸ mA),
      ∀ c : A ⧸ mA, κ (Ideal.Quotient.mk IX (Polynomial.C c)) = c :=
    by
    have hIXeq : IX = Ideal.span {Polynomial.X - Polynomial.C (0 : A ⧸ mA)} := by
      rw [hIX]; simp
    refine
      ⟨(Ideal.quotEquivOfEq hIXeq).trans
          (Polynomial.quotientSpanXSubCAlgEquiv (0 : A ⧸ mA)).toRingEquiv,
        fun c => ?_⟩
    rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
    rw [show
        ((Polynomial.quotientSpanXSubCAlgEquiv (0 : A ⧸ mA)).toRingEquiv)
            (Ideal.Quotient.mk (Ideal.span {Polynomial.X - Polynomial.C (0 : A ⧸ mA)})
              (Polynomial.C c)) =
          (Polynomial.quotientSpanXSubCAlgEquiv (0 : A ⧸ mA))
            (Ideal.Quotient.mk _ (Polynomial.C c))
        from rfl]
    rw [Polynomial.quotientSpanXSubCAlgEquiv_mk]; simp
  -- Bezout split + lift of v·g₁ to A[X] gives the witness b₀ := mk g p.
  obtain ⟨u, v, huv⟩ := hcop
  obtain ⟨p, hp⟩ : ∃ p : Polynomial A, p.map mk = v * g1 :=
    ⟨_, (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective (v * g1)).choose_spec⟩
  have hXz : Ideal.Quotient.mk IX Polynomial.X = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  -- Φ(q (mk g p)) = (1, 0).
  have hΦb₀ : Φ (q (AdjoinRoot.mk g p)) = (1, 0) := by
    have h := key p
    have h1 : Ideal.Quotient.mk IX (v * g1) = 1 := by
      have hvg : v * g1 = 1 - u * Polynomial.X := by linear_combination huv
      rw [hvg, map_sub, map_one, map_mul, hXz]; ring
    have h0 : Ideal.Quotient.mk Ig (v * g1) = 0 := by
      have hgz : Ideal.Quotient.mk Ig g1 = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
      rw [map_mul, hgz]; ring
    rw [hp, h1, h0] at h
    exact h
  have mem_iff :
    ∀ x : AdjoinRoot g, x ∈ (maximalIdeal R).map (algebraMap R (AdjoinRoot g)) ↔ q x = 0 := by
    intro x; rw [hmBeq, hq, Ideal.Quotient.eq_zero_iff_mem]
  have hΦinj : Function.Injective Φ := Φ.injective
  -- Φ(q (of g a)) = (mk_IX (C (mk a)), mk_Ig (C (mk a))).
  have hofC :
    ∀ a : A,
      Φ (q (algebraMap A (AdjoinRoot g) a)) =
        (Ideal.Quotient.mk IX (Polynomial.C (mk a)),
          Ideal.Quotient.mk Ig (Polynomial.C (mk a))) := by
    intro a
    have h := key (Polynomial.C a)
    rwa [show (Polynomial.C a).map mk = Polynomial.C (mk a) by simp] at h
  refine ⟨AdjoinRoot.mk g p, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) idempotent: b₀² - b₀ ∈ mB.
    rw [mem_iff]
    apply hΦinj
    simp only [map_zero, map_sub, map_mul, hΦb₀]
    apply Prod.ext <;> simp
  · -- (2) ξ·b₀ ∈ mB.
    rw [mem_iff]
    apply hΦinj
    have hroot : q (AdjoinRoot.root g) = q (AdjoinRoot.mk g Polynomial.X) := by
      rw [AdjoinRoot.mk_X]
    simp only [map_zero, map_mul, hroot, key Polynomial.X, hΦb₀]
    apply Prod.ext <;> simp [hXz]
  · -- (3) b₀ ∉ mB.
    rw [mem_iff]
    intro hzero
    have hcontra : Φ (q (AdjoinRoot.mk g p)) = Φ 0 := by rw [hzero]
    rw [hΦb₀, map_zero] at hcontra
    have hfst : (1 : Polynomial (A ⧸ mA) ⧸ IX) = 0 := congrArg Prod.fst hcontra
    have hone : (1 : A ⧸ mA) = 0 := by
      have := congrArg κ hfst
      rwa [map_one, map_zero] at this
    exact one_ne_zero hone
  · -- (4) cyclic mod mB.
    intro y
    obtain ⟨a, ha⟩ : ∃ a : A, mk a = κ (Φ (q y)).fst := Ideal.Quotient.mk_surjective _
    refine ⟨a, ?_⟩
    rw [mem_iff]
    apply hΦinj
    have hfst : Ideal.Quotient.mk IX (Polynomial.C (mk a)) = (Φ (q y)).fst := by
      apply κ.injective; rw [hκC, ha]
    simp only [map_zero, map_sub, map_mul, hΦb₀, hofC a]
    apply Prod.ext <;> simp [hfst]
  · -- (5) faithful mod mB.
    intro r hr
    rw [mem_iff] at hr
    have hΦ0 : Φ (q (algebraMap A (AdjoinRoot g) r * AdjoinRoot.mk g p)) = 0 := by
      rw [hr]; exact map_zero Φ
    simp only [map_mul, hΦb₀, hofC r] at hΦ0
    simp only [Prod.mk_mul_mk, Prod.mk_eq_zero] at hΦ0
    have hfst : Ideal.Quotient.mk IX (Polynomial.C (mk r)) = 0 := by
      rw [← mul_one (Ideal.Quotient.mk IX (Polynomial.C (mk r)))]; exact hΦ0.left
    have hr0 : mk r = 0 := by
      have hk := congrArg κ hfst
      rwa [hκC, map_zero] at hk
    exact (Ideal.Quotient.eq_zero_iff_mem).mp hr0

/-- **Rank-1 Nakayama upgrade.**
Given `B` free and module-finite over `A` with `mA ≤ Jac A`, an idempotent `e ∈ B`, and the two
residue facts mod `mB` that pin `e` to the rank-1 simple-root factor — namely
  • (cyclic mod mB)   `∀ y, ∃ r : A, y·e − r·e ∈ mB`, so `Ā·ē` generates `ē·B̄`, and
  • (faithful mod mB) `∀ r : A, r·e ∈ mB → r ∈ mA`, so `ψ̄ : Ā → ē·B̄, r̄ ↦ r̄·ē` is injective
— one obtains the honest rank-1 freeness of `eB = A·e`: cyclic `∀ y, ∃ r, y·e = r·e` and
faithful `∀ r, r·e = 0 → r = 0`.

This is the Nakayama content: `mA_le_jacobson` together with
`Submodule.le_of_le_smul_of_le_jacobson_bot` for the cyclic half, and projective-summand
splitting together with the bottom form of Nakayama for the faithful half. The mod-`mB`
hypotheses genuinely encode the rank-1 residue structure, and they fail for `e = 1` with
`g = X²` over `𝔽₂`, where `ē·B̄ = B̄` has rank 2 so cyclic-mod-`mB` fails. -/
theorem rootlift_rank1_cyclic_faithful (R : Type) [CommRing R] [IsLocalRing R] (A : Type)
    [CommRing A] [Algebra R A] [Module.Finite R A] (g : Polynomial A) (hgmon : g.Monic)
    (e : AdjoinRoot g) (he_idem : e * e = e)
    (hgen_mod :
      ∀ y : AdjoinRoot g,
        ∃ r : A,
          y * e - (algebraMap A (AdjoinRoot g) r) * e ∈
            ((maximalIdeal R).map (algebraMap R (AdjoinRoot g))))
    (hfaith_mod :
      ∀ r : A,
        (algebraMap A (AdjoinRoot g) r) * e ∈
            ((maximalIdeal R).map (algebraMap R (AdjoinRoot g))) →
          r ∈ ((maximalIdeal R).map (algebraMap R A))) :
    (∀ y : AdjoinRoot g, ∃ r : A, y * e = (algebraMap A (AdjoinRoot g) r) * e) ∧
      (∀ r : A, (algebraMap A (AdjoinRoot g) r) * e = 0 → r = 0) := by
  -- `eB` is an `A`-direct summand of the free module `B`, so `mB ∩ eB = mA·eB`; `hgen_mod`
  -- then gives `eB = A·e + mA·eB`, and Nakayama (`mA ⊆ Jac A`) gives `eB = A·e`, the cyclic
  -- half. For the faithful half, `ψ : A ↠ eB` splits because `eB` is a projective summand,
  -- so `A ≅ eB ⊕ ker`; `hfaith_mod` gives `ker(ψ̄) = 0`, hence `ker = mA·ker`, hence
  -- `ker = 0` by Nakayama. The degenerate `e = 1` with `g = X²` over `𝔽₂` is excluded
  -- because `hgen_mod` fails there. The delicate regime is a non-chain local ring such as
  -- `𝔽₂[ε]/(ε²)`, where `mA² = 0`.
  have : Module.Finite A (AdjoinRoot g) := hgmon.finite_adjoinRoot
  have : Module.Free A (AdjoinRoot g) := hgmon.free_adjoinRoot
  set I : Ideal A := (maximalIdeal R).map (algebraMap R A) with hI
  set mB : Ideal (AdjoinRoot g) := (maximalIdeal R).map (algebraMap R (AdjoinRoot g)) with hmB
  set p : AdjoinRoot g →ₗ[A] AdjoinRoot g :=
    { toFun := fun y => y * e
      map_add' := by
        intro x y; ring
      map_smul' := by
        intro a x; simp [Algebra.smul_def]; ring } with
    hp
  have hpe : ∀ z : AdjoinRoot g, p z = z * e := fun z => rfl
  have hpidem : IsIdempotentElem p := by
    ext y; change (y * e) * e = y * e; rw [mul_assoc, he_idem]
  set N : Submodule A (AdjoinRoot g) := LinearMap.range p with hN
  have he_in_N : e ∈ N := ⟨1, by simp [hp]⟩
  have hpfix : ∀ n ∈ N, p n = n := (LinearMap.IsIdempotentElem.isProj_range p hpidem).map_id
  have hIjac : I ≤ Ideal.jacobson (⊥ : Ideal A) := mA_le_jacobson R A
  ----------------------------------------------------------------------------
  -- CYCLIC
  ----------------------------------------------------------------------------
  have hcyc : ∀ y : AdjoinRoot g, ∃ r : A, y * e = (algebraMap A (AdjoinRoot g) r) * e := by
    set M : Submodule A (AdjoinRoot g) := Submodule.span A {e} with hM
    have hNmul : ∀ b z : AdjoinRoot g, z ∈ N → b * z ∈ N := by
      rintro b z ⟨w, rfl⟩
      exact
        ⟨b * w, by
          simp [hp]; ring⟩
    have hclosed : ∀ b z : AdjoinRoot g, z ∈ I • N → b * z ∈ I • N := by
      intro b z hz
      refine Submodule.smul_induction_on hz ?_ ?_
      · intro a ha n hn
        have : b * (a • n) = a • (b * n) := by
          rw [Algebra.smul_def, Algebra.smul_def]; ring
        rw [this]
        exact Submodule.smul_mem_smul ha (hNmul b n hn)
      · intro x y hx hy
        have : b * (x + y) = b * x + b * y := by ring
        rw [this]; exact Submodule.add_mem _ hx hy
    have hstruct : ∀ m : AdjoinRoot g, m ∈ mB → m * e ∈ I • N := by
      intro m hm
      rw [hmB, ← map_map_algebraMap (A := A), Ideal.map] at hm
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hm
      · rintro x ⟨s, hs, rfl⟩
        rw [← Algebra.smul_def]
        exact Submodule.smul_mem_smul hs he_in_N
      · simp
      · intro x y _ _ hx hy
        have : (x + y) * e = x * e + y * e := by ring
        rw [this]; exact Submodule.add_mem _ hx hy
      · intro b x _ hx
        have hbx : (b • x) * e = b * (x * e) := by
          rw [smul_eq_mul]; ring
        rw [hbx]; exact hclosed b _ hx
    have hN_e : ∀ z : AdjoinRoot g, z ∈ N → z * e = z := by
      rintro z ⟨w, rfl⟩
      show (w * e) * e = w * e
      rw [mul_assoc, he_idem]
    have hkey : N ≤ M ⊔ I • N := by
      rintro n ⟨y, rfl⟩
      show y * e ∈ M ⊔ I • N
      obtain ⟨r, hr⟩ := hgen_mod y
      set c : AdjoinRoot g := y * e - (algebraMap A (AdjoinRoot g) r) * e with hc
      have hcN : c ∈ N := by
        rw [hc]
        exact Submodule.sub_mem N ⟨y, hpe y⟩ ⟨algebraMap A (AdjoinRoot g) r, hpe _⟩
      have hce : c * e ∈ I • N := hstruct c hr
      have hcIN : c ∈ I • N := by
        rw [← hN_e c hcN]; exact hce
      have hre : (algebraMap A (AdjoinRoot g) r) * e ∈ M := by
        rw [hM, Submodule.mem_span_singleton]; exact ⟨r, by rw [Algebra.smul_def]⟩
      have hsplit : y * e = (algebraMap A (AdjoinRoot g) r) * e + c := by
        rw [hc]; ring
      rw [hsplit]
      exact Submodule.add_mem _ (Submodule.mem_sup_left hre) (Submodule.mem_sup_right hcIN)
    have hNfg : N.FG := Submodule.fg_range p
    have hNM : N ≤ M := Submodule.le_of_le_smul_of_le_jacobson_bot hNfg hIjac hkey
    intro y
    have hy : y * e ∈ M := hNM ⟨y, hpe y⟩
    rw [hM, Submodule.mem_span_singleton] at hy
    obtain ⟨a, ha⟩ := hy
    exact ⟨a, by rw [← ha, Algebra.smul_def]⟩
  ----------------------------------------------------------------------------
  -- FAITHFUL
  ----------------------------------------------------------------------------
  refine ⟨hcyc, ?_⟩
  set s : AdjoinRoot g →ₗ[A] N :=
    LinearMap.codRestrict N p (fun x => LinearMap.mem_range_self p x) with hs
  have hsi : s.comp N.subtype = LinearMap.id :=
    LinearMap.ext fun n => Subtype.ext (hpfix n n.property)
  have : Module.Projective A N := Module.Projective.of_split (N.subtype) s hsi
  set ψ : A →ₗ[A] AdjoinRoot g := LinearMap.toSpanSingleton A (AdjoinRoot g) e with hψ
  have hψa : ∀ a : A, ψ a = a • e := fun a => rfl
  have hψN : ∀ a : A, ψ a ∈ N := by
    intro a; rw [hψa, Algebra.smul_def]; exact ⟨algebraMap A (AdjoinRoot g) a, rfl⟩
  set φ : A →ₗ[A] N := LinearMap.codRestrict N ψ hψN with hφ
  have hφsurj : LinearMap.range φ = ⊤ := by
    rw [eq_top_iff]; rintro ⟨n, hn⟩ -
    obtain ⟨y, rfl⟩ := hn
    obtain ⟨r, hr⟩ := hcyc y
    refine ⟨r, ?_⟩
    apply Subtype.ext
    show ψ r = y * e
    rw [hψa, Algebra.smul_def, hr]
  obtain ⟨ginv, hginv⟩ := LinearMap.exists_rightInverse_of_surjective φ hφsurj
  set q : A →ₗ[A] A := ginv.comp φ with hq
  set K : Submodule A A := LinearMap.ker ψ with hK
  have hkerφ : LinearMap.ker φ = K := by
    ext a
    show φ a = 0 ↔ ψ a = 0
    constructor
    · intro ha; have := congrArg (Subtype.val) ha; simpa [hφ] using this
    · intro ha; apply Subtype.ext; simpa [hφ] using ha
  have hqkill : ∀ a : A, q a = 0 ↔ φ a = 0 := by
    intro a
    constructor
    · intro ha
      have h2 : φ (ginv (φ a)) = φ a := LinearMap.congr_fun hginv (φ a)
      have : φ (q a) = φ a := h2
      rw [ha] at this; simpa using this.symm
    · intro ha; change ginv (φ a) = 0; rw [ha]; simp
  have hKI : K ≤ I := by
    intro k hk
    apply hfaith_mod
    have : ψ k = 0 := hk
    rw [hψa, Algebra.smul_def] at this
    rw [this]; exact Ideal.zero_mem _
  set jp : A →ₗ[A] A := LinearMap.id - q with hjp
  have hjp_apply : ∀ a : A, jp a = a - q a := fun a => rfl
  have hjp_fix : ∀ k : A, k ∈ K → jp k = k := by
    intro k hk
    have : q k = 0 := by
      rw [hqkill]; rw [← hkerφ] at hk; exact hk
    rw [hjp_apply, this, sub_zero]
  have hrange_jp : LinearMap.range jp ≤ K := by
    rintro x ⟨a, rfl⟩
    show ψ (jp a) = 0
    rw [hjp_apply]
    have hψq : ψ (q a) = ψ a := by
      have hφq : φ (q a) = φ a := LinearMap.congr_fun hginv (φ a)
      have e1 : ψ (q a) = ((φ (q a) : N) : AdjoinRoot g) := by simp [hφ]
      have e2 : ψ a = ((φ a : N) : AdjoinRoot g) := by simp [hφ]
      rw [e1, e2, hφq]
    rw [map_sub, hψq, sub_self]
  have hKeq : K = LinearMap.range jp := le_antisymm (fun k hk => ⟨k, hjp_fix k hk⟩) hrange_jp
  have hKfg : K.FG := by
    rw [hKeq]; exact Submodule.fg_range jp
  have hKIK : K ≤ I • K := by
    intro k hk
    have hkI : k ∈ I := hKI hk
    have hkITop : k ∈ I • (⊤ : Submodule A A) := by
      have : k = k • (1 : A) := by simp
      rw [this]; exact Submodule.smul_mem_smul hkI trivial
    have hmap : jp k ∈ I • LinearMap.range jp := by
      have := Submodule.mem_map_of_mem (f := jp) hkITop
      rw [Submodule.map_smul''] at this
      have hrng : Submodule.map jp (⊤ : Submodule A A) = LinearMap.range jp := by
        ext z; simp [LinearMap.mem_range]
      rw [hrng] at this
      exact this
    rw [hjp_fix k hk] at hmap
    rw [hKeq]
    exact hmap
  have hKbot : K = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I K hKfg hKIK hIjac
  intro r hr
  have hrK : r ∈ K := by
    show ψ r = 0; rw [hψa, Algebra.smul_def]; exact hr
  rw [hKbot] at hrK
  simpa using hrK

/-- **The idempotent of `B = AdjoinRoot g` cutting out the simple root `ξ̄ = 0`.**
For monic `g ∈ A[X]` with `g(0) ∈ mA` and `g'(0)` a unit mod `mA`, the reduction `ḡ = X·g₁`
has `0` as a simple root, so `B/mB ≅ Ā[X]/(ḡ) ≅ Ā × C` by CRT and carries the idempotent
`ē₀` supported on the `Ā`-factor, where `ξ̄ = 0`. Lifting `ē₀` to `B` via
`hensel_idempotent_lift_of_finite` — the only henselian input — yields a genuine idempotent
`e ∈ B` with `(AdjoinRoot.root g) * e ∈ mB` (the root acts as `0` on the `Ā`-factor) and
`e ∉ mB` (that factor being nonzero), together with the rank-1 freeness of `eB = A·e`,
i.e. `e` generates it (cyclic) and is faithful.

The steps are the simple-root split `ḡ = X·g₁` with `(X, g₁)` coprime since `g₁(0)` is a
unit, base change along `AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot`, CRT via
`Ideal.quotientMulEquivQuotientProd`, and then the Hensel lift of the approximate idempotent
`b₀`.

The last two conclusions cannot be stated for an arbitrary idempotent `e` satisfying the
first three: over `𝔽₂` with `g = X²` and `e = 1` one has `e² = e` and the faithfulness
condition holds vacuously, yet `eB = B` has rank `deg g = 2`, so cyclicity fails. They hold
only for the constructed lift of the rank-1 CRT factor, which is why `e` stays existentially
bound here rather than being re-exposed as a universally quantified input. The hypothesis
`[Nontrivial A]` is likewise needed: for the trivial ring `B = 0` and `mB = ⊤`, so `e ∉ mB`
is false. -/
theorem rootlift_idempotent_exists (R : Type) [CommRing R] [HenselianLocalRing R] (A : Type)
    [CommRing A] [Algebra R A] [Module.Finite R A] [Nontrivial A] (g : Polynomial A)
    (hgmon : g.Monic) (hg0 : Polynomial.eval 0 g ∈ ((maximalIdeal R).map (algebraMap R A)))
    (hgd :
      IsUnit
        ((Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R A)))
          (Polynomial.eval 0 (Polynomial.derivative g)))) :
    ∃ e : AdjoinRoot g,
      e * e = e ∧
        (AdjoinRoot.root g) * e ∈ ((maximalIdeal R).map (algebraMap R (AdjoinRoot g))) ∧
        e ∉ ((maximalIdeal R).map (algebraMap R (AdjoinRoot g))) ∧
        (∀ y : AdjoinRoot g, ∃ r : A, y * e = (algebraMap A (AdjoinRoot g) r) * e) ∧
        (∀ r : A, (algebraMap A (AdjoinRoot g) r) * e = 0 → r = 0) := by
  -- `e` is constructed once, as the Hensel lift of the approximate idempotent `b₀`, and kept
  -- bound; all five conjuncts are then proved for that `e`.
  set B := AdjoinRoot g with hB
  set ξ := AdjoinRoot.root g with hξ
  have : Module.Finite A B := hgmon.finite_adjoinRoot
  have : Module.Free A B := hgmon.free_adjoinRoot
  have : Module.Finite R B := Module.Finite.trans A B
  set mB := (maximalIdeal R).map (algebraMap R B) with hmB
  -- The approximate simple-root idempotent b₀ (a pure CRT construction), which also exports
  -- the rank-1 residue facts (cyclic and faithful mod mB) pinning b₀ to the simple-root
  -- factor.
  obtain ⟨b₀, hb₀idem, hb₀ξ, hb₀ne, hb₀gen, hb₀faith⟩ :=
    rootlift_approx_idempotent_exists R A g hg0 hgd
  -- The henselian lift (the only henselian input) to a genuine idempotent e with e − b₀ ∈ mB.
  obtain ⟨e, he_idem, he_close⟩ := hensel_idempotent_lift_of_finite R B b₀ hb₀idem
  -- Transfer the rank-1 residue facts from b₀ to e (they differ by mB-corrections via he_close).
  have hgen_e : ∀ y : B, ∃ r : A, y * e - (algebraMap A B r) * e ∈ mB := by
    intro y
    obtain ⟨r, hr⟩ := hb₀gen y
    refine ⟨r, ?_⟩
    have hsplit : y * e - (algebraMap A B r) * e =
        (y * b₀ - (algebraMap A B r) * b₀) + (y - algebraMap A B r) * (e - b₀) := by ring
    rw [hsplit]
    exact Ideal.add_mem _ hr (Ideal.mul_mem_left _ _ he_close)
  have hfaith_e :
    ∀ r : A, (algebraMap A B r) * e ∈ mB → r ∈ ((maximalIdeal R).map (algebraMap R A)) := by
    intro r hr
    apply hb₀faith r
    have hbridge :
      (algebraMap A B r) * b₀ = (algebraMap A B r) * e - (algebraMap A B r) * (e - b₀) := by ring
    rw [hbridge]
    exact Ideal.sub_mem _ hr (Ideal.mul_mem_left _ _ he_close)
  -- Upgrade to honest cyclic + faithful via the rank-1 Nakayama kernel.
  obtain ⟨hcyc, hfaith⟩ := rootlift_rank1_cyclic_faithful R A g hgmon e he_idem hgen_e hfaith_e
  refine ⟨e, he_idem, ?_, ?_, ?_, ?_⟩
  · -- (2) ξ·e ∈ mB.
    have hsplit : ξ * e = ξ * (e - b₀) + ξ * b₀ := by ring
    rw [hsplit]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ he_close) hb₀ξ
  · -- (3) e ∉ mB.
    intro he_mem
    apply hb₀ne
    have hrw : b₀ = e - (e - b₀) := by ring
    rw [hrw]
    exact Ideal.sub_mem _ he_mem he_close
  · -- (4) CYCLIC.
    exact hcyc
  · -- (5) FAITHFUL.
    exact hfaith

/-- **The simple-root idempotent of `AdjoinRoot g`, with its rank-1 free structure.**
For monic `g ∈ A[X]` with `g(0) ∈ mA` and `g'(0)` a unit mod `mA`, there is an idempotent
`e ∈ AdjoinRoot g` with `ξ·e ∈ mB` and `e ∉ mB`, where `ξ := AdjoinRoot.root g`, such that
moreover `eB = A·e` is free of rank 1 over `A`: `e` generates it (cyclic) and is faithful.

The hypotheses block the apparent danger of a factor-dependent rank over a non-local base
such as `A = R × R`: `g(0) ∈ mA` makes `ḡ(0) = 0` on every residue factor, so `0` is a root
everywhere, and `g'(0)` a unit mod `mA` makes `0` a SIMPLE root everywhere, so the
`X`-component has constant rank 1. The last two conjuncts are what the scalar extraction in
`root_lift_scalar_extract` needs, and they are not consequences of the first three alone. -/
alias root_lift_adjoinRoot_idempotent := rootlift_idempotent_exists

/-- **Extracting the root scalar from the rank-1 idempotent factor.**
Given the idempotent `e ∈ B = AdjoinRoot g` produced by `root_lift_adjoinRoot_idempotent`
(so `e² = e`, `ξ·e ∈ mB`, `e ∉ mB`) together with the rank-1 free structure of `eB = A·e`
over `A` (cyclic generation `hgen` and faithfulness `hfaithful`), multiplication by
`ξ := AdjoinRoot.root g` on `eB` is a scalar `a ∈ A`, that is `ξ·e = a·e`. Then `a ∈ mA`
because `ξ·e ∈ mB`, and since `g(ξ) = 0` and `e` is a free rank-1 basis,
`g(a)·e = g(ξ)·e = 0` gives `g.eval a = 0`.

The rank-1 hypotheses are essential and are not consequences of "`e` is some idempotent with
`ξ·e ∈ mB`": for `R = ℤ/4`, `A = R × R`, `g = X + C (0,1)` and `e = (1,0)`, faithfulness
fails, since `(0,1)·(1,0) = 0` while `(0,1) ≠ 0`. -/
theorem root_lift_scalar_extract (R : Type) [CommRing R] [HenselianLocalRing R] (A : Type)
    [CommRing A] [Algebra R A] [Module.Finite R A] (g : Polynomial A) (e : AdjoinRoot g)
    (he : e * e = e)
    (hξe : (AdjoinRoot.root g) * e ∈ ((maximalIdeal R).map (algebraMap R (AdjoinRoot g))))
    -- `eB = A·e` is free of rank 1 over `A`: `e` generates (cyclic) and is faithful.
    (hgen : ∀ y : AdjoinRoot g, ∃ r : A, y * e = (algebraMap A (AdjoinRoot g) r) * e)
    (hfaithful : ∀ r : A, (algebraMap A (AdjoinRoot g) r) * e = 0 → r = 0) :
    ∃ a, g.IsRoot a ∧ a ∈ ((maximalIdeal R).map (algebraMap R A)) := by
  -- Pure ring and module algebra, with no henselian input: φ := algebraMap A B = AdjoinRoot.of g,
  -- mB := m·B, mA := m·A. (1) `hgen ξ` gives a scalar `a` with `ξ·e = φ(a)·e`. (2) By induction,
  -- `ξⁿ·e = φ(aⁿ)·e`, hence for any polynomial p, `(aeval ξ p)·e = φ(p.eval a)·e`. Since
  -- `aeval ξ g = mk g g = 0`, faithfulness gives `g.eval a = 0`. (3) `φ(a)·e ∈ mB`; using
  -- `mB = mA.map φ` and `hgen`/`hfaithful` to peel multipliers off mB-generators, `a ∈ mA`.
  set φ := algebraMap A (AdjoinRoot g) with hφ
  set mB := (maximalIdeal R).map (algebraMap R (AdjoinRoot g)) with hmB
  set mA := (maximalIdeal R).map (algebraMap R A) with hmA
  obtain ⟨a, ha⟩ := hgen (AdjoinRoot.root g)
  -- Power lemma: ξ^n * e = φ (a^n) * e
  have hpow : ∀ n : ℕ, (AdjoinRoot.root g) ^ n * e = φ (a ^ n) * e := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      calc
        (AdjoinRoot.root g) ^ (k + 1) * e = (AdjoinRoot.root g) * ((AdjoinRoot.root g) ^ k * e) :=
          by ring
        _ = φ (a ^ k) * ((AdjoinRoot.root g) * e) := by
          rw [ih]
          ring
        _ = φ (a ^ (k + 1)) * e := by
          rw [ha, pow_succ, map_mul]
          ring
  -- (aeval ξ p) * e = φ (p.eval a) * e for any polynomial p
  have hpoly :
    ∀ p : Polynomial A, (Polynomial.aeval (AdjoinRoot.root g) p) * e = φ (p.eval a) * e := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add, Polynomial.eval_add, map_add, add_mul, hp, add_mul, hq]
    | monomial n c =>
      rw [Polynomial.aeval_monomial, Polynomial.eval_monomial, map_mul]
      rw [mul_assoc, hpow]
      ring
  have haeval0 : Polynomial.aeval (AdjoinRoot.root g) g = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  refine ⟨a, ?_, ?_⟩
  · -- g.IsRoot a, i.e. g.eval a = 0
    have hkey : φ (g.eval a) * e = 0 := by rw [← hpoly g, haeval0, zero_mul]
    exact hfaithful (g.eval a) hkey
  · -- a ∈ mA
    have hae : φ a * e ∈ mB := by
      rwa [← ha]
    have hmBeq : mB = mA.map φ := (map_map_algebraMap _).symm
    -- z ∈ mB → z * e = φ c * e for some c ∈ mA (faithful-mod-mB via cyclic generation)
    have hmem : ∀ z : AdjoinRoot g, z ∈ mB → ∃ c ∈ mA, z * e = φ c * e := by
      intro z hz
      rw [hmBeq, Ideal.map] at hz
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
      · rintro _ ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
      · exact ⟨0, Ideal.zero_mem _, by simp⟩
      · rintro x y _ _ ⟨cx, hcx, hx⟩ ⟨cy, hcy, hy⟩
        exact ⟨cx + cy, Ideal.add_mem _ hcx hcy, by rw [add_mul, hx, hy, map_add, add_mul]⟩
      · rintro b x _ ⟨c, hc, hx⟩
        obtain ⟨d, hd⟩ := hgen b
        refine ⟨c * d, Ideal.mul_mem_right _ _ hc, ?_⟩
        calc
          (b • x) * e = φ c * (b * e) := by
            rw [smul_eq_mul, mul_assoc, hx]
            ring
          _ = φ (c * d) * e := by
            rw [hd, map_mul]
            ring
    obtain ⟨c, hc, hce⟩ := hmem (φ a * e) hae
    have hidem : (φ a * e) * e = φ a * e := by rw [mul_assoc, he]
    rw [hidem] at hce
    have hsub : φ (a - c) * e = 0 := by rw [map_sub, sub_mul, hce, sub_self]
    rwa [sub_eq_zero.mp (hfaithful (a - c) hsub)]

/-- Assembly of the `a₀ = 0` core from the two sub-lemmas above. -/
@[sga "3 XI 1.11" "special case", sga "7 XV 1.1.2" "special case"]
theorem root_lift_via_adjoinRoot (R : Type) [CommRing R] [HenselianLocalRing R] (A : Type)
    [CommRing A] [Algebra R A] [Module.Finite R A] (g : Polynomial A) (hgmon : g.Monic)
    (hg0 : Polynomial.eval 0 g ∈ ((maximalIdeal R).map (algebraMap R A)))
    (hgd :
      IsUnit
        ((Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R A)))
          (Polynomial.eval 0 (Polynomial.derivative g)))) :
    ∃ a, g.IsRoot a ∧ a ∈ ((maximalIdeal R).map (algebraMap R A)) := by
  -- Trivial-ring edge case: if A is the zero ring, a = 0 works (everything ∈ ⊤ = mA, and any
  -- polynomial has 0 as a root since the ring is trivial). Otherwise A is nontrivial and we run
  -- the AdjoinRoot idempotent construction.
  rcases subsingleton_or_nontrivial A with hsub | hnt
  · refine ⟨0, ?_, ?_⟩
    · simp [Polynomial.IsRoot, Subsingleton.elim (g.eval 0) 0]
    · simp [Subsingleton.elim ((maximalIdeal R).map (algebraMap R A)) (⊤ : Ideal A)]
  · obtain ⟨e, he, hξe, _, hgen, hfaithful⟩ := root_lift_adjoinRoot_idempotent R A g hgmon hg0 hgd
    exact root_lift_scalar_extract R A g e he hξe hgen hfaithful

/-- **The `a₀ = 0` core of the root lift** (Stacks 09XI/04GG). This is the substantive form
of `henselian_pair_root_lift` after the reduction to `a₀ = 0` by the translation
`f ↦ f(X + a₀)` (`Polynomial.taylor`): for monic `f ∈ A[X]` with `f(0) ∈ mA` and `f'(0)` a
unit mod `mA`, there is `a ∈ mA` with `f(a) = 0`.

The steps are:
- `f̄ = X·g₁` over `Ā := A/mA` with `g₁(0)` a unit, so `0` is a SIMPLE root of `f̄` and
  `(X, g₁)` are coprime in `Ā[X]`.
- `B := AdjoinRoot f` is free of rank `n` over `A` (as `f` is monic), finite and integral over
  `R`, with universal root `ξ` satisfying `f(ξ) = 0`. By CRT on the coprime split,
  `B̄ := B/mB ≅ Ā[X]/(f̄) ≅ Ā × C`, which supplies a nontrivial idempotent `ē₀ ∈ B̄`, the unit
  of the `Ā`-factor where `ξ̄ = 0`.
- `ē₀` lifts to a genuine idempotent `e ∈ B` by `hensel_idempotent_lift_of_finite`, applied to
  a lift `b₀` of `ē₀`, which is an approximate idempotent. This is the only henselian input.
- `eB = A·e` is free of rank 1 over `A` (Nakayama, `mA_le_jacobson`), so multiplication by
  `ξ` on it is a scalar `a ∈ A`, with `a ∈ mA` because `ξ̄·ē₀ = 0`, and
  `f(a)·e = f(ξ)·e = 0` forces `f(a) = 0`.

Beyond the henselian lift, the ingredients are standard: `AdjoinRoot.powerBasis`, base
change, `Ideal.quotientMulEquivQuotientProd` and Nakayama. -/
@[sga "7 XV 1.1.2" "special case"]
theorem henselian_pair_root_lift_core (R : Type) [CommRing R] [HenselianLocalRing R] (A : Type)
    [CommRing A] [Algebra R A] [Module.Finite R A] :
    ∀ (g : Polynomial A),
      g.Monic →
        Polynomial.eval 0 g ∈ ((maximalIdeal R).map (algebraMap R A)) →
        IsUnit
          ((Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R A)))
            (Polynomial.eval 0 (Polynomial.derivative g))) →
        ∃ a, g.IsRoot a ∧ a ∈ ((maximalIdeal R).map (algebraMap R A)) := by
  -- `B := AdjoinRoot g` is free of rank n over A (g monic) and finite/integral over R, with
  -- root ξ; `root_lift_adjoinRoot_idempotent` produces a genuine idempotent e ∈ B with
  -- ξ·e ∈ mB cutting out the rank-1 "ξ̄ = 0" component, via CRT on the simple-root split
  -- f̄ = X·g₁ together with `hensel_idempotent_lift_of_finite`; then
  -- `root_lift_scalar_extract` reads off the scalar a ∈ mA with g(a) = 0, using that
  -- eB = A·e is free of rank 1 by Nakayama and `mA_le_jacobson`.
  intro g hgmon hg0 hgd
  exact root_lift_via_adjoinRoot R A g hgmon hg0 hgd

/-- **The root-lifting (`is_henselian`) property of the henselian pair `(A, mA)`**, packaged as a
standalone lemma (it is the second field of `henselian_pair_mA`'s `HenselianRing` structure).

This is the substantive half of Stacks 09XI: for monic `f ∈ A[X]` and an approximate simple root
`a₀ ∈ A` (`f(a₀) ∈ mA`, `f'(a₀)` a unit mod mA), there is an honest root `a ∈ A` with `a-a₀ ∈ mA`.

One may assume `a₀ = 0`, by the translation `X ↦ X + a₀`; then `mA ≤ Jac A` (the `jac` field)
makes the unit derivative a genuine unit, and units lift. Form the finite `R`-algebra
`B := A[X]/(f)` — finite over `A`, free of rank `deg f`, with `A` finite over `R` — carrying
the universal root `ξ`, and let `p ∈ R[T]` be the characteristic polynomial of
multiplication by `ξ` on the finite `R`-module `B`, so that `p` is monic with `p(ξ) = 0` by
Cayley–Hamilton. The closed fibre `B/mB ≅ Ā[X]/(f̄)`, with `Ā := A/mA` finite over `κ` hence
Artinian, splits by CRT into the root component (where `ξ̄ = 0`, with characteristic
polynomial `T^N`) and a complement (where `ξ̄` acts invertibly, since `f̄'(0)` is a unit), so
`p̄ = T^N · p̄₁` with `T^N` and `p̄₁` COPRIME in `κ[T]`, as `p̄₁(0) ≠ 0`. Applying
`hensel_factorization_over_R` lifts this to `p = p₀·p₁` over `R`, and Bézout coprimality
(`p₀, p₁` are coprime over `R` since they are coprime mod `m ⊆ Jac R`) gives an idempotent
`ε₀ ∈ B` cutting out the degree-`N` root component, whence a degree-1 monic factor
`g = X - a` of `f` with `g ≡ X`, so that `a ∈ mA` and `f(a) = 0`. The idempotents live
inside the finite `R`-algebra `B` and come from the factorization via Bézout. -/
@[sga "3 XI 1.11" "(f), special case", sga "7 XV 1.1.2" "special case"]
theorem henselian_pair_root_lift (R : Type) [CommRing R] [HenselianLocalRing R] (A : Type)
    [CommRing A] [Algebra R A] [Module.Finite R A] :
    ∀ (f : Polynomial A),
      f.Monic →
        ∀ (a₀ : A),
          Polynomial.eval a₀ f ∈ ((maximalIdeal R).map (algebraMap R A)) →
            IsUnit
              ((Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R A)))
                (Polynomial.eval a₀ (Polynomial.derivative f))) →
            ∃ a, f.IsRoot a ∧ a - a₀ ∈ ((maximalIdeal R).map (algebraMap R A)) := by
  -- Reduce to a₀ = 0 via `Polynomial.taylor a₀ f = f(X + a₀)`, landing in
  -- `henselian_pair_root_lift_core`, where the substantive content lives.
  set mA := (maximalIdeal R).map (algebraMap R A) with hmA
  intro f hf a₀ hf0 hd
  set g : Polynomial A := Polynomial.taylor a₀ f with hg
  have hgmon : g.Monic := by
    rw [hg, Polynomial.taylor_apply]; exact hf.comp_X_add_C a₀
  have hg0 : g.eval 0 ∈ mA := by
    rw [hg, Polynomial.taylor_eval, zero_add]; exact hf0
  have hgd :
    (Ideal.Quotient.mk mA) (g.derivative.eval 0) =
      (Ideal.Quotient.mk mA) (f.derivative.eval a₀) := by
    congr 1
    rw [hg, Polynomial.taylor_apply, Polynomial.derivative_comp]
    simp [Polynomial.eval_comp]
  have hgd' : IsUnit ((Ideal.Quotient.mk mA) (g.derivative.eval 0)) := by
    rw [hgd]; exact hd
  obtain ⟨a', ha'root, ha'mem⟩ := henselian_pair_root_lift_core R A g hgmon hg0 hgd'
  refine ⟨a' + a₀, ?_, ?_⟩
  · have : f.eval (a' + a₀) = g.eval a' := by rw [hg, Polynomial.taylor_eval]
    rw [Polynomial.IsRoot]; rw [this]; exact ha'root
  · simpa using ha'mem

/-- **The henselian-pair property of `(A, mA)`** (Stacks 09XI/04GG). For `A` module-finite,
hence integral, over a henselian local ring `R`, the pair `(A, mA)` with `mA := m·A` is a
**henselian pair**, packaged as Mathlib's `HenselianRing A mA`: one has `mA ≤ Jac A`, and for
every monic `f ∈ A[X]` with an approximate simple root `a₀` (`f(a₀) ∈ mA` and `f'(a₀)` a unit
mod `mA`) there is an honest root `a` with `a - a₀ ∈ mA`.

This is Stacks Tag 09XI: a finite, or integral, algebra over a henselian local ring is a
henselian pair. It is used in `closedFibre_idempotent_lift` to lift a single quadratic. -/
@[ega "IV 18.5.6" "(i), special case", sga "3 XXIV 8.1.2" "partial"]
theorem henselian_pair_mA (R : Type) [CommRing R] [HenselianLocalRing R] (A : Type) [CommRing A]
    [Algebra R A] [Module.Finite R A] :
    HenselianRing A ((IsLocalRing.maximalIdeal R).map (algebraMap R A)) := by
  -- `HenselianRing.mk` of its two fields:
  --   `jac` (mA ≤ Jac A) — proved inline by integral lying-over: every maximal Q of A
  --     contracts to the maximal m of R, so mA ⊆ Q for all maximal Q, hence mA ⊆ Jac A;
  --   `is_henselian` — the standalone lemma `henselian_pair_root_lift`, derived from
  --     `hensel_factorization_over_R`.
  -- Both henselianness and locality of R are load-bearing.
  refine ⟨?_, henselian_pair_root_lift R A⟩
  have hint : Algebra.IsIntegral R A := Algebra.IsIntegral.of_finite R A
  rw [show (⊥ : Ideal A).jacobson = sInf {J : Ideal A | J.IsMaximal} from by
      rw [Ideal.jacobson]; congr 1; ext J; simp [bot_le]]
  apply le_sInf
  intro Q hQ
  simp only [Set.mem_ofPred_eq] at hQ
  rw [Ideal.map_le_iff_le_comap]
  have hmax : (Q.comap (algebraMap R A)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q
  rw [IsLocalRing.eq_maximalIdeal hmax]

/-- **The henselian-pair property in quadratic form.** Single-root Hensel lifting for
`(A, mA)` in the form needed below: for the monic quadratic `f(T) = T² + b·T + d ∈ A[T]` with
`f(0) = d ∈ mA` and `f'(0) = b` a unit in `A`, there is `c ∈ mA`, i.e. `mk c = 0`, with
`c² + b·c + d = 0`.

Proved by applying `HenselianRing.is_henselian`, from `henselian_pair_mA`, to
`f = X² + (C b)·X + C d` at the approximate simple root `a₀ = 0`, where `f(0) = d ∈ mA` and
`f'(0) = b` is a unit. -/
theorem henselianPair_mA_quadratic (R : Type) [CommRing R] [HenselianLocalRing R] (A : Type)
    [CommRing A] [Algebra R A] [Module.Finite R A] (b d : A) (hb : IsUnit b)
    (hd : (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R A))) d = 0) :
    ∃ c : A,
      (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R A))) c = 0 ∧
        c * c + b * c + d = 0 := by
  -- The henselian-pair single-simple-root Hensel lift for (A, mA), applied to
  -- f = T² + bT + d with f(0) = d ∈ mA and f'(0) = b a unit, so that c = 0 is an approximate
  -- simple root. Both hypotheses are load-bearing: dropping either d ∈ mA or b a unit makes
  -- the conclusion fail.
  have hpair := henselian_pair_mA R A
  set mA := (IsLocalRing.maximalIdeal R).map (algebraMap R A) with hmA
  set f : Polynomial A := Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C d with hf
  have hmonic : f.Monic := by
    have hfe : f = Polynomial.X ^ 2 + (Polynomial.C b * Polynomial.X + Polynomial.C d) := by
      rw [hf]; ring
    rw [hfe]
    apply Polynomial.monic_X_pow_add
    compute_degree
    norm_num
  have heval : f.eval 0 = d := by simp [hf]
  have hderiv : f.derivative.eval 0 = b := by
    rw [hf]; simp [Polynomial.derivative_add, Polynomial.derivative_mul]
  have h0mem : f.eval 0 ∈ mA := by
    rw [heval]; rwa [← Ideal.Quotient.eq_zero_iff_mem]
  have hunit : IsUnit ((Ideal.Quotient.mk mA) (f.derivative.eval 0)) := by
    rw [hderiv]; exact hb.map _
  obtain ⟨a, haroot, hamem⟩ := hpair.is_henselian f hmonic 0 h0mem hunit
  refine ⟨a, ?_, ?_⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem] at hamem; simpa using hamem
  · have hr : f.eval a = 0 := haroot
    rw [hf] at hr; simp at hr; linear_combination hr

end
end
