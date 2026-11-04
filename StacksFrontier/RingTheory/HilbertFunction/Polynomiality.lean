module

public import StacksFrontier.RingTheory.HilbertFunction.ModuleInduction
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Data.Rat.Star
import Mathlib.Order.Interval.Finset.Box
import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.RingTheory.PicardGroup
import Mathlib.Algebra.AffineMonoid.UniqueSums

/-!
# The Hilbert function is a numerical polynomial

The four-term class identity for multiplication by `xʳ`, the `x`-power induction step, and
the main theorem `hilbertFun_isNumericalPolynomial` (Stacks Proposition 10.58.7, Tag 00K1).
-/

@[expose] public section
-- needed file-wide: `FinModule.cls_eq_of_linearEquiv`, `FinModule.cls_add_of_ses`,
-- `KPrime0.hom_ext`, `xpow_four_term_class` and `hilbertFun_xpow_step_identity` all rewrite
-- through the `FinModule`/`KPrime0` quotient wrappers and the graded-piece subgroup coercions,
-- which only unfold with defeq transparency relaxed.  See also the note before
-- `section MainPieces`, which depends on this option holding for the whole file.
set_option backward.isDefEq.respectTransparency false
universe u

/-- The fibre map `ℳ i → quotGrading ℳ N i` is `𝒮 0`-linear and surjective, with kernel `N`. -/
private theorem exists_quotFiber_linearMap {S M : Type u} [CommRing S] (𝒮 : ℤ → AddSubgroup S)
    [GradedRing 𝒮] [AddCommGroup M] [Module S M] (ℳ : ℤ → AddSubgroup M)
    [SetLike.GradedSMul 𝒮 ℳ] (N : Submodule S M) (i : ℤ) :
    ∃ g : ↥(ℳ i) →ₗ[↥(𝒮 0)] ↥(quotGrading ℳ N i),
      Function.Surjective g ∧ ∀ m : ↥(ℳ i), g m = 0 ↔ (m : M) ∈ N := by
  refine ⟨{ toFun := fun m => quotFiber ℳ N i m
            map_add' := fun a b => by simp
            map_smul' := fun s m => by
              apply Subtype.ext
              rw [RingHom.id_apply, quotFiber_coe, gradePieceSMul_coe, gradePieceSMul_coe,
                quotFiber_coe, Submodule.mkQ_apply, Submodule.mkQ_apply,
                Submodule.Quotient.mk_smul] }, quotFiber_surj ℳ N i, fun m => ?_⟩
  rw [Subtype.ext_iff]
  exact Submodule.Quotient.mk_eq_zero N

/-- `a` annihilates the quotient of a module by `Ideal.span {a} • ⊤`. -/
private theorem smul_eq_zero_of_mem_quot_span_smul_top {S M : Type u} [CommRing S]
    [AddCommGroup M] [Module S M] (a : S)
    (q : M ⧸ (Ideal.span {a} • (⊤ : Submodule S M))) : a • q = 0 := by
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ q
  rw [Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

/-- The Hilbert function vanishes in degrees whose graded piece is a subsingleton. -/
private theorem hilbertFun_eq_zero_of_subsingleton {S M : Type u} [CommRing S]
    [IsNoetherianRing S] (𝒮 : ℤ → AddSubgroup S) [GradedRing 𝒮] [AddCommGroup M] [Module S M]
    [Module.Finite S M] (ℳ : ℤ → AddSubgroup M) [SetLike.GradedSMul 𝒮 ℳ]
    [DirectSum.Decomposition ℳ] (hneg : ∀ d : ℤ, d < 0 → 𝒮 d = ⊥) (n : ℤ)
    [Subsingleton ↥(ℳ n)] : hilbertFun 𝒮 ℳ hneg n = 0 := by
  have : Subsingleton (gradedFinModule 𝒮 ℳ hneg n).carrier := ‹Subsingleton ↥(ℳ n)›
  exact FinModule.cls_zero_of_subsingleton (gradedFinModule 𝒮 ℳ hneg n)

section Main

variable {S M : Type u}
variable [CommRing S] [IsNoetherianRing S]
variable (𝒮 : ℤ → AddSubgroup S) [GradedRing 𝒮]
variable [AddCommGroup M] [Module S M] [Module.Finite S M]
variable (ℳ : ℤ → AddSubgroup M)
variable [SetLike.GradedSMul 𝒮 ℳ] [DirectSum.Decomposition ℳ]

/-- **(4a) Per-degree four-term `·xʳ` additivity identity.** For `x ∈ 𝒮 1`,
`r : ℕ`, a homogeneous `N = Ideal.span {xʳ} • ⊤` with its quotient grading `𝒬 = quotGrading ℳ N`
(decomposition supplied as `dec`), and any degree `n`:
`[ker μ_{r,n}] = [ℳ n] − [ℳ (n+r)] + [(M/xʳM)_{n+r}]` in `K'_0(𝒮 0)`.

PROOF: two SES of finite `𝒮 0`-modules together with `FinModule.cls_add_of_ses`:
(i) `0 → ker μ → ℳ n → im μ → 0` ⇒ `[ℳ n] = [ker μ] + [im μ]`;
(ii) `0 → im μ → ℳ (n+r) → (M/xʳM)_{n+r} → 0` ⇒ `[ℳ (n+r)] = [im μ] + [(M/xʳM)_{n+r}]`,
using `(xʳM)_{n+r} = xʳ·M_n = im μ` (homogeneous decomposition uniqueness, `(∗)`) and the
quotient-grading identification `(M/xʳM)_{n+r} ≅ M_{n+r}/(xʳM)_{n+r}` (`(∗∗)`, the `quotGrading`
bundle). Eliminate `[im μ]`. -/
theorem xpow_four_term_class (hneg : ∀ d : ℤ, d < 0 → 𝒮 d = ⊥) (x : S) (hx : x ∈ 𝒮 1) (r : ℕ)
    (n : ℤ)
    [dec : DirectSum.Decomposition (quotGrading ℳ (Ideal.span {x ^ r} • (⊤ : Submodule S M)))] :
    (xpowDegKerFin 𝒮 ℳ hneg x hx r n).cls =
      hilbertFun 𝒮 ℳ hneg n - hilbertFun 𝒮 ℳ hneg (n + r) +
        hilbertFun 𝒮 (quotGrading ℳ (Ideal.span {x ^ r} • (⊤ : Submodule S M))) hneg (n + r) := by
  -- two SES + FinModule.cls_add_of_ses.
  classical
  have : IsNoetherianRing ↥(𝒮 0) := gradeZero_isNoetherianRing 𝒮 hneg
  set N : Submodule S M := Ideal.span {x ^ r} • (⊤ : Submodule S M) with hN
  have hNhomog : N.IsHomogeneous ℳ := idealSpanPow_smul_top_homog 𝒮 ℳ x hx r
  set μ := xpowDegMap 𝒮 ℳ x hx r n with hμ
  -- coercion fact for μ
  have hμcoe : ∀ m : ↥(ℳ n), ((μ m : ↥(ℳ (n + r))) : M) = x ^ r • (m : M) := fun m => rfl
  -- finiteness of ℳ (n+r) over 𝒮 0
  have hfinnr : Module.Finite ↥(𝒮 0) ↥(ℳ (n + r)) := gradedPiece_finite 𝒮 ℳ hneg (n + r)
  have : IsNoetherian ↥(𝒮 0) ↥(ℳ (n + r)) := isNoetherian_of_isNoetherianRing_of_finite _ _
  -- the image FinModule
  have himfin : Module.Finite ↥(𝒮 0) ↥(LinearMap.range μ) :=
    Module.Finite.of_injective (LinearMap.range μ).subtype Subtype.val_injective
  let imFin : FinModule ↥(𝒮 0) := { carrier := ↥(LinearMap.range μ), finite := himfin }
  -- SES (I): 0 → ker μ → ℳ n → im μ → 0
  have hI :
    (gradedFinModule 𝒮 ℳ hneg n).cls = (xpowDegKerFin 𝒮 ℳ hneg x hx r n).cls + imFin.cls := by
    refine
      FinModule.cls_add_of_ses (gradedFinModule 𝒮 ℳ hneg n) (xpowDegKerFin 𝒮 ℳ hneg x hx r n) imFin
        (LinearMap.ker μ).subtype μ.rangeRestrict Subtype.val_injective μ.surjective_rangeRestrict
        ?_
    rw [Submodule.range_subtype, LinearMap.ker_rangeRestrict]
  -- the surjection g : ℳ (n+r) → (quotGrading)_{n+r}, with kernel `N ∩ ℳ (n+r)`
  obtain ⟨g, hgsurj, hg0⟩ := exists_quotFiber_linearMap 𝒮 ℳ N (n + r)
  -- range μ = ker g (the (∗) identification)
  have hkerg : LinearMap.range μ = LinearMap.ker g := by
    ext w
    rw [LinearMap.mem_ker, hg0]
    constructor
    · rintro ⟨m, rfl⟩
      rw [hμcoe, hN]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
    · -- the homogeneity argument (∗)
      intro hwN
      -- (w:M) = x^r • y for some y
      have hex : ∃ y : M, (w : M) = x ^ r • y := by
        rw [hN] at hwN
        refine Submodule.smul_induction_on hwN ?_ ?_
        · intro a ha b _
          rw [Ideal.mem_span_singleton] at ha
          obtain ⟨c, rfl⟩ := ha
          exact ⟨c • b, by rw [mul_smul]⟩
        · rintro y z ⟨py, hpy⟩ ⟨pz, hpz⟩
          exact ⟨py + pz, by rw [smul_add, ← hpy, ← hpz]⟩
      obtain ⟨y, hy⟩ := hex
      -- the degree-n component of y maps onto w
      set yn : M := (DirectSum.decompose ℳ y n : M) with hyn
      have hynmem : yn ∈ ℳ n := (DirectSum.decompose ℳ y n).property
      have hxr : x ^ r ∈ 𝒮 r := by simpa using SetLike.pow_mem_graded r hx
      have hwhomog : (DirectSum.decompose ℳ (w : M) (n + r) : M) = (w : M) :=
        DirectSum.decompose_of_mem_same ℳ w.property
      have hkey : (DirectSum.decompose ℳ (x ^ r • y) (r + n) : M) = x ^ r • yn :=
        gp_decompose_smul_homog 𝒮 ℳ r (x ^ r) hxr y n
      have hwxy : (w : M) = x ^ r • yn := by
        rw [← hwhomog, hy, show n + (r : ℤ) = r + n by ring, hkey]
      exact ⟨⟨yn, hynmem⟩, Subtype.ext (by rw [hμcoe]; exact hwxy.symm)⟩
  -- SES (II): 0 → im μ → ℳ (n+r) → (quotGrading)_{n+r} → 0
  have hII :
    (gradedFinModule 𝒮 ℳ hneg (n + r)).cls =
      imFin.cls + (gradedFinModule 𝒮 (quotGrading ℳ N) hneg (n + r)).cls := by
    refine
      FinModule.cls_add_of_ses (gradedFinModule 𝒮 ℳ hneg (n + r)) imFin
        (gradedFinModule 𝒮 (quotGrading ℳ N) hneg (n + r)) (LinearMap.range μ).subtype g
        Subtype.val_injective hgsurj ?_
    rw [Submodule.range_subtype, hkerg]
  -- combine: hilbertFun unfolds to gradedFinModule.cls
  show (xpowDegKerFin 𝒮 ℳ hneg x hx r n).cls = _
  rw [hilbertFun, hilbertFun, hilbertFun]
  -- hI: [ℳ n] = ker.cls + imFin.cls ; hII: [ℳ(n+r)] = imFin.cls + [quot]
  change
    (xpowDegKerFin 𝒮 ℳ hneg x hx r n).cls =
      (gradedFinModule 𝒮 ℳ hneg n).cls - (gradedFinModule 𝒮 ℳ hneg (n + r)).cls +
        (gradedFinModule 𝒮 (quotGrading ℳ N) hneg (n + r)).cls
  rw [hI, hII]; abel
/-- **(N2c-step identity) One step of the x-power induction, as a class identity.**
For `x ∈ 𝒮 1` and a finite graded module `Q` with `x^{r+1} • Q = 0`, with the two
homogeneous submodules `xQ := Ideal.span {x} • ⊤` and `K := LinearMap.ker (·x : Q →ₗ Q)`
(both homogeneous), one has, for ALL `m : ℤ`,
  `φ_Q(m) = φ_{Q/K}(m-1) + φ_{Q/xQ}(m)`,
where `Q/K` carries the `quotGrading` `quotDecomposition` from `hK` and `Q/xQ` from `hxQ`.

PROOF: the four-term `·x` identity `xpow_four_term_class` at
exponent `1` and degree `n = m-1` gives `[ker μ_{1,n}] = φ_Q(n) - φ_Q(n+1) + φ_{Q/xQ}(n+1)`;
the SES `0 → (K)_n → Q_n → (Q/K)_n → 0` (the `quotGrading` of `K` at degree `n`)
gives `φ_{Q/K}(n) = φ_Q(n) - [ker μ_{1,n}]` (here `(K)_n = ker μ_{1,n}` since `K = ker(·x)`).
Substitute and reindex `m = n+1`. -/
theorem hilbertFun_xpow_step_identity (hneg : ∀ d : ℤ, d < 0 → 𝒮 d = ⊥) (x : S) (hx : x ∈ 𝒮 1)
    [decxQ : DirectSum.Decomposition (quotGrading ℳ (Ideal.span {x} • (⊤ : Submodule S M)))]
    [decK :
      DirectSum.Decomposition (quotGrading ℳ (LinearMap.ker (DistribSMul.toLinearMap S M x)))] :
    ∀ m : ℤ,
      hilbertFun 𝒮 ℳ hneg m =
        hilbertFun 𝒮 (quotGrading ℳ (LinearMap.ker (DistribSMul.toLinearMap S M x))) hneg (m - 1) +
          hilbertFun 𝒮 (quotGrading ℳ (Ideal.span {x} • (⊤ : Submodule S M))) hneg m := by
  classical
  have : IsNoetherianRing ↥(𝒮 0) := gradeZero_isNoetherianRing 𝒮 hneg
  intro m
  set n : ℤ := m - 1 with hndef
  have hn1 : n + (1 : ℤ) = m := by
    rw [hndef]; ring
  set N : Submodule S M := Ideal.span {x} • (⊤ : Submodule S M) with hN
  set K : Submodule S M := LinearMap.ker (DistribSMul.toLinearMap S M x) with hK
  -- Step A: the four-term identity at exponent 1.
  let decN1 :
    DirectSum.Decomposition (quotGrading ℳ (Ideal.span {x ^ 1} • (⊤ : Submodule S M))) := by
    rw [pow_one]; exact decxQ
  have hA := xpow_four_term_class 𝒮 ℳ hneg x hx 1 n (dec := decN1)
  -- Reconcile span {x^1} with span {x} = N.
  -- now hA : (xpowDegKerFin … 1 n).cls
  --        = hilbertFun 𝒮 ℳ hneg n - hilbertFun 𝒮 ℳ hneg (n + 1)
  --          + hilbertFun 𝒮 (quotGrading ℳ N) hneg (n + 1)
  -- Step B: the SES 0 → ker μ → ℳ n → (M/K)_n → 0.
  set μ := xpowDegMap 𝒮 ℳ x hx 1 n with hμ
  have hμcoe : ∀ q : ↥(ℳ n), ((μ q : ↥(ℳ (n + 1))) : M) = x ^ 1 • (q : M) := fun q => rfl
  -- the surjection g : ℳ n → (quotGrading ℳ K) n, with kernel `K ∩ ℳ n`
  obtain ⟨g, hgsurj, hg0⟩ := exists_quotFiber_linearMap 𝒮 ℳ K n
  -- ker μ = ker g
  have hkerμg : LinearMap.ker μ = LinearMap.ker g := by
    ext q
    rw [LinearMap.mem_ker, LinearMap.mem_ker, hg0, Subtype.ext_iff, hμcoe, ZeroMemClass.coe_zero,
      hK, LinearMap.mem_ker, pow_one]
    rfl
  -- SES (B): [ℳ n] = [ker μ] + [(M/K)_n]
  have hB :
    (gradedFinModule 𝒮 ℳ hneg n).cls =
      (xpowDegKerFin 𝒮 ℳ hneg x hx 1 n).cls +
        (gradedFinModule 𝒮 (quotGrading ℳ K) hneg n).cls := by
    refine
      FinModule.cls_add_of_ses (gradedFinModule 𝒮 ℳ hneg n) (xpowDegKerFin 𝒮 ℳ hneg x hx 1 n)
        (gradedFinModule 𝒮 (quotGrading ℳ K) hneg n) (LinearMap.ker μ).subtype g
        Subtype.val_injective hgsurj ?_
    rw [Submodule.range_subtype, hkerμg]
  -- Step C: assemble. First convert hA's `span {x^1}` term and index `n+1` to `N`, `m`.
  have hspan : (Ideal.span {x ^ 1} • (⊤ : Submodule S M)) = N := by rw [hN, pow_one]
  have hidx : n + ((1 : ℕ) : ℤ) = m := by
    push_cast; rw [hndef]; ring
  -- Transport the quotient-piece hilbertFun across the submodule equality `span{x^1}•⊤ = N`.
  have htrans :
    ∀ (P : Submodule S M) [instP : DirectSum.Decomposition (quotGrading ℳ P)],
      P = N → hilbertFun 𝒮 (quotGrading ℳ P) hneg m = hilbertFun 𝒮 (quotGrading ℳ N) hneg m := by
    intro P instP hPN
    subst hPN
    congr 1
  -- Build hA in the N, m form.
  have hA' :
    (xpowDegKerFin 𝒮 ℳ hneg x hx 1 n).cls =
      hilbertFun 𝒮 ℳ hneg n - hilbertFun 𝒮 ℳ hneg m + hilbertFun 𝒮 (quotGrading ℳ N) hneg m := by
    rw [hidx] at hA
    rw [hA]
    rw [htrans (Ideal.span {x ^ 1} • (⊤ : Submodule S M)) hspan]
  -- unfold hilbertFun everywhere to gradedFinModule classes
  show hilbertFun 𝒮 ℳ hneg m = _
  -- goal index m-1 = n (defeq), m
  simp only [hilbertFun] at hA' ⊢
  rw [hB] at hA'
  -- hA' : kerfin.cls = (kerfin.cls + (gp (quot K) n).cls) - (gp ℳ m).cls + (gp (quot N) m).cls
  -- goal : (gp ℳ m).cls = (gp (quot K) n).cls + (gp (quot N) m).cls
  -- AddCommGroup algebra: cancel kerfin.cls and solve for (gp ℳ m).cls.
  change
    (gradedFinModule 𝒮 ℳ hneg m).cls =
      (gradedFinModule 𝒮 (quotGrading ℳ K) hneg n).cls +
        (gradedFinModule 𝒮 (quotGrading ℳ N) hneg m).cls
  have hzero :
    (gradedFinModule 𝒮 (quotGrading ℳ K) hneg n).cls - (gradedFinModule 𝒮 ℳ hneg m).cls +
        (gradedFinModule 𝒮 (quotGrading ℳ N) hneg m).cls =
      0 := by
    have h := hA'
    -- h : kerfin = kerfin + (K - M + N), so the parenthesized part is 0
    rw [eq_comm, ← sub_eq_zero] at h
    rw [← h]; abel
  rw [← sub_eq_zero]
  have hrw :
    (gradedFinModule 𝒮 ℳ hneg m).cls -
        ((gradedFinModule 𝒮 (quotGrading ℳ K) hneg n).cls +
          (gradedFinModule 𝒮 (quotGrading ℳ N) hneg m).cls) =
      -((gradedFinModule 𝒮 (quotGrading ℳ K) hneg n).cls - (gradedFinModule 𝒮 ℳ hneg m).cls +
          (gradedFinModule 𝒮 (quotGrading ℳ N) hneg m).cls) := by
    abel
  rw [hrw, hzero, neg_zero]

/-- **(N2c-aux) Generalized x-power-annihilated quotient is numerical (induction on the
exponent `r`).** Self-quantified over fresh graded data so the recursion at exponent `r`
applies to a fresh quotient. If `x^r • Q = 0` then `φ_Q` is a numerical polynomial.

PROOF (induction on `r`):
* `r = 0`: `x^0 • q = q = 0`, so `Q` is `Subsingleton`, each `Q_n` subsingleton,
  `φ_Q ≡ 0` (`FinModule.cls_zero_of_subsingleton`), numpoly (`numpoly_of_eventually_zero`).
* `r+1`: `x^{r+1} • Q = 0`. Let `xQ = span{x}•⊤`, `K = ker(·x)`.
  - `Q/xQ` is x-annihilated (quotient ⇒ witness `t`); `hilbertFun_xann_quotient_isNumpoly`
    ⇒ `φ_{Q/xQ}` numpoly.
  - `Q/K` is a quotient (witness `t`) and `x^r`-annihilated (`x^{r+1}q=0` ⇒ `x^r q ∈ K`);
    the IH at `r` gives `φ_{Q/K}` numpoly.
  - `hilbertFun_xpow_step_identity` ⇒ `φ_Q(m) = φ_{Q/K}(m-1) + φ_{Q/xQ}(m)`, so
    `φ_Q = numpoly_shift_down φ_{Q/K} + φ_{Q/xQ}` numpoly (`eventualNumpoly_add`). -/
theorem hilbertFun_xpowann_isNumpoly_aux (k : ℕ)
    (IH :
      ∀ m : ℕ,
        m < k →
          ∀ {S M : Type u} [CommRing S] [IsNoetherianRing S] (𝒮 : ℤ → AddSubgroup S) [GradedRing 𝒮]
            [AddCommGroup M] [Module S M] [Module.Finite S M] (ℳ : ℤ → AddSubgroup M)
            [SetLike.GradedSMul 𝒮 ℳ] [DirectSum.Decomposition ℳ] (hneg : ∀ d : ℤ, d < 0 → 𝒮 d = ⊥)
            (_ : GeneratedInDegreeOne 𝒮) (t : Finset S) (_ : t.card ≤ m) (_ : ∀ x ∈ t, x ∈ 𝒮 1)
            (_ :
              irrelevantIdeal 𝒮 • (⊤ : Submodule S M) =
                Ideal.span (t : Set S) • (⊤ : Submodule S M)),
            IsEventualNumericalPolynomial
              (fun n => hilbertFun 𝒮 ℳ hneg n - hilbertFun 𝒮 ℳ hneg (n - 1))) :
    ∀ (r : ℕ) {S Q : Type u} [CommRing S] [IsNoetherianRing S] (𝒮 : ℤ → AddSubgroup S)
      [GradedRing 𝒮] [AddCommGroup Q] [Module S Q] [Module.Finite S Q] (𝒬 : ℤ → AddSubgroup Q)
      [SetLike.GradedSMul 𝒮 𝒬] [DirectSum.Decomposition 𝒬] (hneg : ∀ d : ℤ, d < 0 → 𝒮 d = ⊥)
      (_ : GeneratedInDegreeOne 𝒮) (x : S) (_ : x ∈ 𝒮 1) (t : Finset S) (_ : x ∈ t)
      (_ : t.card ≤ k) (_ : ∀ y ∈ t, y ∈ 𝒮 1) (_ : ∀ q : Q, x ^ r • q = (0 : Q))
      (_ : irrelevantIdeal 𝒮 • (⊤ : Submodule S Q) = Ideal.span (t : Set S) • (⊤ : Submodule S Q)),
      IsEventualNumericalPolynomial (hilbertFun 𝒮 𝒬 hneg) := by
  intro r
  induction r with
  | zero =>
    intro S Q _ _ 𝒮 _ _ _ _ 𝒬 _ _ hneg hgen x hx t hxt hcard ht1 hxann hinv
    have hsub0 : Subsingleton Q :=
      ⟨fun a b => by
        have ha : x ^ 0 • a = 0 := hxann a
        have hb : x ^ 0 • b = 0 := hxann b
        simp only [pow_zero, one_smul] at ha hb
        rw [ha, hb]⟩
    apply numpoly_of_eventually_zero
    apply Filter.Eventually.of_forall
    intro n
    have : Subsingleton ↥(𝒬 n) := ⟨fun a b => Subtype.ext (hsub0.elim _ _)⟩
    exact hilbertFun_eq_zero_of_subsingleton 𝒮 𝒬 hneg n
  | succ r IHr =>
    intro S Q _ _ 𝒮 _ _ _ _ 𝒬 _ _ hneg hgen x hx t hxt hcard ht1 hxann hinv
    classical
    set xQ : Submodule S Q := Ideal.span {x} • (⊤ : Submodule S Q) with hxQdef
    set K : Submodule S Q := LinearMap.ker (DistribSMul.toLinearMap S Q x) with hKdef
    -- Homogeneity of xQ
    have hxQhomog : xQ.IsHomogeneous 𝒬 := by
      simpa [hxQdef, pow_one] using idealSpanPow_smul_top_homog 𝒮 𝒬 x hx 1
    -- Homogeneity of K = ker(·x)
    have hKhomog : K.IsHomogeneous 𝒬 := by
      intro n q hq
      rw [hKdef, LinearMap.mem_ker] at hq
      have hxq : x • q = 0 := by simpa using hq
      rw [hKdef, LinearMap.mem_ker]
      show x • (DirectSum.decompose 𝒬 q n : Q) = 0
      have hkey := gp_decompose_smul_homog 𝒮 𝒬 1 x hx q n
      rw [show (1 : ℤ) + n = 1 + n by rfl] at hkey
      rw [← hkey, hxq]
      simp
    -- Decomposition instances for the two quotients
    let decxQ : DirectSum.Decomposition (quotGrading 𝒬 xQ) := quotDecomposition 𝒬 xQ hxQhomog
    let decK : DirectSum.Decomposition (quotGrading 𝒬 K) := quotDecomposition 𝒬 K hKhomog
    -- Q/xQ is x-annihilated
    have hxann_xQ : ∀ qb : Q ⧸ xQ, x • qb = 0 := smul_eq_zero_of_mem_quot_span_smul_top x
    have hinv_xQ := module_inv_quotient 𝒮 t xQ hinv
    have hQxQ :=
      hilbertFun_xann_quotient_isNumpoly k IH 𝒮 (quotGrading 𝒬 xQ) hneg hgen x hx t hxt hcard ht1
        hxann_xQ hinv_xQ
    -- Q/K is x^r-annihilated
    have hxann_K : ∀ qb : Q ⧸ K, x ^ r • qb = 0 := by
      intro qb
      obtain ⟨q, rfl⟩ := K.mkQ_surjective qb
      rw [Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hKdef,
        LinearMap.mem_ker]
      show x • (x ^ r • q) = 0
      rw [← mul_smul, ← pow_succ']
      exact hxann q
    have hinv_K := module_inv_quotient 𝒮 t K hinv
    have hQK := IHr 𝒮 (quotGrading 𝒬 K) hneg hgen x hx t hxt hcard ht1 hxann_K hinv_K
    -- Step identity
    have hstep := hilbertFun_xpow_step_identity 𝒮 𝒬 hneg x hx
    -- Assemble
    have heq :
      (hilbertFun 𝒮 𝒬 hneg) = fun m =>
        hilbertFun 𝒮 (quotGrading 𝒬 K) hneg (m - 1) + hilbertFun 𝒮 (quotGrading 𝒬 xQ) hneg m := by
      funext m; exact hstep m
    rw [heq]
    exact eventualNumpoly_add _ _ (numpoly_shift_down _ hQK) hQxQ

/-- Inductive step for a module annihilated by a power of a degree-one element: the Hilbert
function of such a quotient is eventually a numerical polynomial. -/
theorem hilbertFun_quot_xpow_isNumpoly (k : ℕ)
    (IH :
      ∀ m : ℕ,
        m < k →
          ∀ {S M : Type u} [CommRing S] [IsNoetherianRing S] (𝒮 : ℤ → AddSubgroup S) [GradedRing 𝒮]
            [AddCommGroup M] [Module S M] [Module.Finite S M] (ℳ : ℤ → AddSubgroup M)
            [SetLike.GradedSMul 𝒮 ℳ] [DirectSum.Decomposition ℳ] (hneg : ∀ d : ℤ, d < 0 → 𝒮 d = ⊥)
            (_ : GeneratedInDegreeOne 𝒮) (t : Finset S) (_ : t.card ≤ m) (_ : ∀ x ∈ t, x ∈ 𝒮 1)
            (_ :
              irrelevantIdeal 𝒮 • (⊤ : Submodule S M) =
                Ideal.span (t : Set S) • (⊤ : Submodule S M)),
            IsEventualNumericalPolynomial
              (fun n => hilbertFun 𝒮 ℳ hneg n - hilbertFun 𝒮 ℳ hneg (n - 1))) :
    ∀ {S Q : Type u} [CommRing S] [IsNoetherianRing S] (𝒮 : ℤ → AddSubgroup S) [GradedRing 𝒮]
      [AddCommGroup Q] [Module S Q] [Module.Finite S Q] (𝒬 : ℤ → AddSubgroup Q)
      [SetLike.GradedSMul 𝒮 𝒬] [DirectSum.Decomposition 𝒬] (hneg : ∀ d : ℤ, d < 0 → 𝒮 d = ⊥)
      (_ : GeneratedInDegreeOne 𝒮) (x : S) (_ : x ∈ 𝒮 1) (r : ℕ) (t : Finset S) (_ : x ∈ t)
      (_ : t.card ≤ k) (_ : ∀ y ∈ t, y ∈ 𝒮 1) (_ : ∀ q : Q, x ^ r • q = (0 : Q))
      (_ : irrelevantIdeal 𝒮 • (⊤ : Submodule S Q) = Ideal.span (t : Set S) • (⊤ : Submodule S Q)),
      IsEventualNumericalPolynomial (hilbertFun 𝒮 𝒬 hneg) := by
  intro S Q _ _ 𝒮 _ _ _ _ 𝒬 _ _ hneg hgen x hx r t hxt hcard ht1 hxann hinv
  exact hilbertFun_xpowann_isNumpoly_aux k IH r 𝒮 𝒬 hneg hgen x hx t hxt hcard ht1 hxann hinv

omit [DirectSum.Decomposition ℳ] in
/-- **(4b) Noetherian kernel stabilization.** Since `M` is a finite
module over the Noetherian ring `S`, the ascending chain `ker(xʳ : M → M)` stabilizes: there is
`r₀` with `ker(x^{r₀+1} : M → M) = ker(x^{r₀} : M → M)` (as `S`-submodules of `M`). Consequently
the per-degree kernels of `μ_{r₀+1,n}` and `μ_{r₀,n}` coincide (as `𝒮 0`-submodules of `ℳ n`).

PROOF: `IsNoetherian S M` (from `[IsNoetherianRing S]` + `[Module.Finite S M]`); apply
`LinearMap.eventually_iSup_ker_pow_eq` (or `monotone`-chain stabilization) to
`LinearMap.toSpanSingleton`/`(LinearMap.mulLeft ...)`-style `·x` map; the degreewise statement
follows since `m ∈ ℳ n` with `x^{r₀+1} • m = 0` ⇔ `x^{r₀} • m = 0` once the submodule kernels
are equal. -/
theorem xpow_ker_stabilizes (x : S) (hx : x ∈ 𝒮 1) :
    ∃ r₀ : ℕ, ∀ (n : ℤ), xpowDegKerSub 𝒮 ℳ x hx (r₀ + 1) n = xpowDegKerSub 𝒮 ℳ x hx r₀ n := by
  have : IsNoetherian S M := isNoetherian_of_isNoetherianRing_of_finite S M
  -- multiplication-by-x map and the fact that its r-th power is multiplication by x^r
  set f : M →ₗ[S] M := LinearMap.lsmul S M x with hf
  have hfpow : ∀ (r : ℕ) (y : M), (f ^ r) y = x ^ r • y := by
    intro r
    induction r with
    | zero =>
      intro y; simp
    | succ k ih =>
      intro y
      rw [pow_succ, Module.End.mul_apply, ih, hf, LinearMap.lsmul_apply, pow_succ, mul_smul]
  -- coercion fact for the degreewise map
  have hcoe :
    ∀ (r : ℕ) (n : ℤ) (m : ↥(ℳ n)),
      ((xpowDegMap 𝒮 ℳ x hx r n m : ↥(ℳ (n + r))) : M) = x ^ r • (m : M) :=
    fun r n m => rfl
  -- the global kernel chain stabilizes
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (LinearMap.eventually_iSup_ker_pow_eq f)
  refine ⟨N, ?_⟩
  intro n
  have hglob : LinearMap.ker (f ^ (N + 1)) = LinearMap.ker (f ^ N) := by
    have h1 := hN (N + 1) (Nat.le_succ N)
    have h2 := hN N (le_refl N)
    rw [← h1, ← h2]
  apply Submodule.ext
  intro m
  rw [xpowDegKerSub, xpowDegKerSub, LinearMap.mem_ker, LinearMap.mem_ker]
  rw [Subtype.ext_iff, Subtype.ext_iff, ZeroMemClass.coe_zero, ZeroMemClass.coe_zero, hcoe, hcoe]
  have e1 : x ^ (N + 1) • (m : M) = 0 ↔ (m : M) ∈ LinearMap.ker (f ^ (N + 1)) := by
    rw [LinearMap.mem_ker, hfpow]
  have e2 : x ^ N • (m : M) = 0 ↔ (m : M) ∈ LinearMap.ker (f ^ N) := by
    rw [LinearMap.mem_ker, hfpow]
  rw [e1, e2, hglob]

/-- **(N2d) The four-term `·xʳ` additivity identity + Noetherian kernel cancellation.**
Pure `K'_0` additivity + Noetherian stabilization, NO `IH`. Produces the exponent `r₀` and
two fresh finite graded `S`-modules `Q1, Q2` (intended `Q1 = M/x^{r₀}M`, `Q2 = M/x^{r₀+1}M`)
each `xʳ`-annihilated (`r = r₀`, resp. `r₀+1`) and carrying the witness `t`, such that for
all `m`:  `Δφ_M(m) = φ_{Q2}(m) − φ_{Q1}(m−1)`. Bundles the quotient construction (via
`idealSpanPow_smul_top_homog` + `quotGrading`/`quotDecomposition`/`quotGradedSMul` +
`module_inv_quotient`) with the four-term/stabilization identity, so that
`hilbertDiff_eq_xpow_quot` only combines it with `hilbertFun_quot_xpow_isNumpoly`.

PROOF (Step 2): four-term degreewise exact sequence for `·xʳ`
`0 → (ker xʳ)_n → M_n →^{·xʳ} M_{n+r} → (M/xʳM)_{n+r} → 0` ⇒ (twice `FinModule.cls_add_of_ses`)
`[ker xʳ_n] = [M_n] − [M_{n+r}] + [(M/xʳM)_{n+r}]`; `ker xʳ` stabilizes (Noetherian,
`LinearMap.eventually_iSup_ker_pow_eq`) at `r₀` ⇒ subtracting at `r₀+1`,`r₀` cancels the
kernel term ⇒ the identity (reindex `m = n+r₀+1`). The witness on each quotient is
`module_inv_quotient`; `xʳ`-annihilation is `x^r • (M/xʳM) = 0` (immediate). -/
theorem hilbertDiff_xpow_quot_identity (hneg : ∀ d : ℤ, d < 0 → 𝒮 d = ⊥) (x : S) (hx : x ∈ 𝒮 1)
    (t : Finset S)
    (hinv :
      irrelevantIdeal 𝒮 • (⊤ : Submodule S M) = Ideal.span (t : Set S) • (⊤ : Submodule S M)) :
    ∃ (r₀ : ℕ) (Q1 : Type u) (_ : AddCommGroup Q1) (_ : Module S Q1) (_ : Module.Finite S Q1) (𝒬1 :
      ℤ → AddSubgroup Q1) (_ : SetLike.GradedSMul 𝒮 𝒬1) (_ : DirectSum.Decomposition 𝒬1) (Q2 :
      Type u) (_ : AddCommGroup Q2) (_ : Module S Q2) (_ : Module.Finite S Q2) (𝒬2 :
      ℤ → AddSubgroup Q2) (_ : SetLike.GradedSMul 𝒮 𝒬2) (_ : DirectSum.Decomposition 𝒬2),
      (∀ q : Q1, x ^ r₀ • q = (0 : Q1)) ∧
        (∀ q : Q2, x ^ (r₀ + 1) • q = (0 : Q2)) ∧
        (irrelevantIdeal 𝒮 • (⊤ : Submodule S Q1) =
          Ideal.span (t : Set S) • (⊤ : Submodule S Q1)) ∧
        (irrelevantIdeal 𝒮 • (⊤ : Submodule S Q2) =
          Ideal.span (t : Set S) • (⊤ : Submodule S Q2)) ∧
        (∀ m : ℤ,
          hilbertFun 𝒮 ℳ hneg m - hilbertFun 𝒮 ℳ hneg (m - 1) =
            hilbertFun 𝒮 𝒬2 hneg m - hilbertFun 𝒮 𝒬1 hneg (m - 1)) := by
  classical
  -- Stabilization exponent for the `·xʳ` kernel chain.
  obtain ⟨r₀, hstab⟩ := xpow_ker_stabilizes 𝒮 ℳ x hx
  -- The two homogeneous submodules `N1 = x^{r₀}M`, `N2 = x^{r₀+1}M`.
  set N1 : Submodule S M := Ideal.span {x ^ r₀} • (⊤ : Submodule S M) with hN1def
  set N2 : Submodule S M := Ideal.span {x ^ (r₀ + 1)} • (⊤ : Submodule S M) with hN2def
  have hN1homog : N1.IsHomogeneous ℳ := idealSpanPow_smul_top_homog 𝒮 ℳ x hx r₀
  have hN2homog : N2.IsHomogeneous ℳ := idealSpanPow_smul_top_homog 𝒮 ℳ x hx (r₀ + 1)
  -- Graded-quotient bundles.
  let dec1 : DirectSum.Decomposition (quotGrading ℳ N1) := quotDecomposition ℳ N1 hN1homog
  let dec2 : DirectSum.Decomposition (quotGrading ℳ N2) := quotDecomposition ℳ N2 hN2homog
  refine
    ⟨r₀, (M ⧸ N1), inferInstance, inferInstance, inferInstance, quotGrading ℳ N1, inferInstance,
      dec1, (M ⧸ N2), inferInstance, inferInstance, inferInstance, quotGrading ℳ N2, inferInstance,
      dec2, ?_, ?_, ?_, ?_, ?_⟩
  · -- `x ^ r₀` annihilates `M ⧸ N1`.
    exact smul_eq_zero_of_mem_quot_span_smul_top (x ^ r₀)
  · -- `x ^ (r₀+1)` annihilates `M ⧸ N2`.
    exact smul_eq_zero_of_mem_quot_span_smul_top (x ^ (r₀ + 1))
  · -- Witness `t` descends to `M ⧸ N1`.
    exact module_inv_quotient 𝒮 t N1 hinv
  · -- Witness `t` descends to `M ⧸ N2`.
    exact module_inv_quotient 𝒮 t N2 hinv
  · -- The identity, via the four-term additivity at `r₀` and `r₀+1` + kernel cancellation.
    intro m
    -- Per-degree four-term identities at degree `n = m - (r₀+1)`.
    set n : ℤ := m - (r₀ + 1) with hn
    have hr0 : n + (r₀ : ℤ) = m - 1 := by
      rw [hn]; ring
    have hr1 : n + ((r₀ + 1 : ℕ) : ℤ) = m := by
      rw [hn]; push_cast; ring
    have h4a0 := xpow_four_term_class 𝒮 ℳ hneg x hx r₀ n (dec := dec1)
    have h4a1 := xpow_four_term_class 𝒮 ℳ hneg x hx (r₀ + 1) n (dec := dec2)
    rw [hr0] at h4a0
    rw [hr1] at h4a1
    -- Kernel classes coincide by stabilization.
    have hkereq :
      (xpowDegKerFin 𝒮 ℳ hneg x hx (r₀ + 1) n).cls = (xpowDegKerFin 𝒮 ℳ hneg x hx r₀ n).cls :=
      FinModule.cls_eq_of_linearEquiv _ _ <|
        LinearEquiv.ofEq (xpowDegKerSub 𝒮 ℳ x hx (r₀ + 1) n) (xpowDegKerSub 𝒮 ℳ x hx r₀ n)
          (hstab n)
    -- Combine.
    rw [hkereq] at h4a1
    -- h4a0 : [ker r₀ n] = φ_M n - φ_M (m-1) + φ_{Q1} (m-1)
    -- h4a1 : [ker r₀ n] = φ_M n - φ_M m   + φ_{Q2} m
    have hcombine := h4a0.symm.trans h4a1
    -- φ_M n - φ_M (m-1) + φ_{Q1}(m-1) = φ_M n - φ_M m + φ_{Q2} m
    change
      hilbertFun 𝒮 ℳ hneg m - hilbertFun 𝒮 ℳ hneg (m - 1) =
        hilbertFun 𝒮 (quotGrading ℳ N2) hneg m - hilbertFun 𝒮 (quotGrading ℳ N1) hneg (m - 1)
    have := hcombine
    abel_nf at this ⊢
    linear_combination (norm := abel) this

/-- **(N2) Four-term `·xʳ` sequence + Noetherian kernel stabilization.** For `x ∈ 𝒮 1`
and `M` with the module-generation witness `t`, there is an exponent `r₀` and, for both
`r = r₀` and `r = r₀+1`, a fresh finite graded `S`-module `Q_r = M/xʳM` (with grading `𝒬_r`)
that is x-annihilated AFTER the filtration refinement (we only need `φ_{Q_r}` numerical,
supplied separately) and carries the witness `t`, such that for ALL `m ∈ ℤ`
  `Δφ_M(m) = φ_{Q_{r₀}}(m−1) − φ_{Q_{r₀+1}}(m)`.

PROOF: build `Q_r = M ⧸ (Ideal.span {xʳ} • ⊤)` (homogeneous quotient via
`gradedQuotient_bundle`), use the four-term additivity (`gradedSES_cls_additivity`-style
for `·xʳ`) and the Noetherian stabilization of `ker xʳ` to cancel the kernel class.
This lemma carries NO `IH` — it is pure `K'_0` additivity + Noetherian stabilization.
NOTE: the conjunct that each `Q_r` carries the invariant `t` is `module_inv_quotient`. -/
theorem hilbertDiff_eq_xpow_quot (k : ℕ)
    (IH :
      ∀ m : ℕ,
        m < k →
          ∀ {S M : Type u} [CommRing S] [IsNoetherianRing S] (𝒮 : ℤ → AddSubgroup S) [GradedRing 𝒮]
            [AddCommGroup M] [Module S M] [Module.Finite S M] (ℳ : ℤ → AddSubgroup M)
            [SetLike.GradedSMul 𝒮 ℳ] [DirectSum.Decomposition ℳ] (hneg : ∀ d : ℤ, d < 0 → 𝒮 d = ⊥)
            (_ : GeneratedInDegreeOne 𝒮) (t : Finset S) (_ : t.card ≤ m) (_ : ∀ x ∈ t, x ∈ 𝒮 1)
            (_ :
              irrelevantIdeal 𝒮 • (⊤ : Submodule S M) =
                Ideal.span (t : Set S) • (⊤ : Submodule S M)),
            IsEventualNumericalPolynomial
              (fun n => hilbertFun 𝒮 ℳ hneg n - hilbertFun 𝒮 ℳ hneg (n - 1)))
    (hneg : ∀ d : ℤ, d < 0 → 𝒮 d = ⊥) (hgen : GeneratedInDegreeOne 𝒮) (x : S) (hx : x ∈ 𝒮 1)
    (t : Finset S) (hxt : x ∈ t) (hcard : t.card ≤ k) (ht1 : ∀ y ∈ t, y ∈ 𝒮 1)
    (hinv :
      irrelevantIdeal 𝒮 • (⊤ : Submodule S M) = Ideal.span (t : Set S) • (⊤ : Submodule S M)) :
    ∃ (_ : ℕ) (Q1 : Type u) (_ : AddCommGroup Q1) (_ : Module S Q1) (_ : Module.Finite S Q1) (𝒬1 :
      ℤ → AddSubgroup Q1) (_ : SetLike.GradedSMul 𝒮 𝒬1) (_ : DirectSum.Decomposition 𝒬1) (Q2 :
      Type u) (_ : AddCommGroup Q2) (_ : Module S Q2) (_ : Module.Finite S Q2) (𝒬2 :
      ℤ → AddSubgroup Q2) (_ : SetLike.GradedSMul 𝒮 𝒬2) (_ : DirectSum.Decomposition 𝒬2),
      IsEventualNumericalPolynomial (hilbertFun 𝒮 𝒬1 hneg) ∧
        IsEventualNumericalPolynomial (hilbertFun 𝒮 𝒬2 hneg) ∧
        (∀ m : ℤ,
          hilbertFun 𝒮 ℳ hneg m - hilbertFun 𝒮 ℳ hneg (m - 1) =
            hilbertFun 𝒮 𝒬2 hneg m - hilbertFun 𝒮 𝒬1 hneg (m - 1)) := by
  -- off-by-sign refutation of the previous form and the worked k[x], k[x]/(x²) checks).
  -- ASSEMBLY: `hilbertDiff_xpow_quot_identity` builds the two graded quotients
  -- Q1 = M/x^{r₀}M, Q2 = M/x^{r₀+1}M (each xʳ-annihilated, carrying the witness t) plus the
  -- four-term/stabilization identity; `hilbertFun_quot_xpow_isNumpoly` (consuming IH) shows
  -- each `φ_{Qᵢ}` is a numerical polynomial.
  obtain
    ⟨r₀, Q1, _, _, _, 𝒬1, _, _, Q2, _, _, _, 𝒬2, _, _, hxann1, hxann2, hinv1, hinv2, hidentity⟩ :=
    hilbertDiff_xpow_quot_identity 𝒮 ℳ hneg x hx t hinv
  refine ⟨r₀, Q1, _, _, _, 𝒬1, _, _, Q2, _, _, _, 𝒬2, _, _, ?_, ?_, hidentity⟩
  · exact hilbertFun_quot_xpow_isNumpoly k IH 𝒮 𝒬1 hneg hgen x hx r₀ t hxt hcard ht1 hxann1 hinv1
  · exact
      hilbertFun_quot_xpow_isNumpoly k IH 𝒮 𝒬2 hneg hgen x hx (r₀ + 1) t hxt hcard ht1 hxann2 hinv2

/- **Module-level induction engine (Stacks 00K1 heart, no base-ring change).**
Generalized over all graded data and a bound `k` on the size of a degree-one set
`t ⊆ 𝒮 1` that generates the action of `S_+` on `M`
(`irrelevantIdeal 𝒮 • ⊤ = Ideal.span ↑t • ⊤`). The first difference of the Hilbert
function is a numerical polynomial.

RIGOROUS ARGUMENT — `Nat.strong_induction` on `k`:
  • Base (`t = ∅`): `hinv` ⇒ `S_+ · M = ⊥`; `module_smul_top_eq_bot_eventually_zero`
    ⇒ `φ` eventually `0` ⇒ difference eventually `0` (`numpoly_of_eventually_zero`).
  • Step (`t ≠ ∅`): pick `x ∈ t`, `t' = t.erase x` (`|t'| < k`). Split
    `M = M'`(x-power-torsion)`⊕`-additively `M'' = M/M'` via `FinModule.cls_add_of_ses`
    (`xtorsion_isHomogeneous` gives the graded submodule, hence degreewise SES):
    `Δφ_M = Δφ_{M'} + Δφ_{M''}`.
    – `M''` (x injective): degree-shift SES `0 → M''_d →(·x) M''_{d+1} → (M''/xM'')_{d+1} → 0`
      ⇒ `Δφ_{M''}(d+1) = φ_{M''/xM''}(d+1)`. `N = M''/xM''` has `x·N = 0`, so the module
      invariant for `N` holds with the smaller witness `t'` (the `x·N=0` drop); IH at
      `|t'| < k` on `N` (plus the antidifference `numpoly_of_diff` to pass from
      `Δφ_N` to `φ_N`) ⇒ `Δφ_{M''}` numerical.
    – `M'` (x globally nilpotent, `x^r·M'=0`): secondary induction on `r` using the SES
      `0 → x·M' → M' → M'/x·M' → 0`; the `r=1` layer has `x` annihilating it ⇒ witness
      `t'`, IH at `|t'| < k`; `x·M'` is a quotient of `M'` (via `·x`) with exponent
      `r-1` ⇒ secondary IH. Sum ⇒ `Δφ_{M'}` numerical.
    Sum the two ⇒ `Δφ_M` numerical. -/
/-- **Inductive STEP of the module-level engine (Stacks 00K1, `t ≠ ∅` case) —
SOUND quotient-only route.** The strong-induction recursion is threaded through the
explicit hypothesis `IH`. Here `t` is nonempty; pick `x ∈ t`, `t' = t.erase x`
(so `|t'| < k`).

RIGOROUS ARGUMENT (replacing the false torsion-split): the four-term `·xʳ` exact
sequence together with Noetherian kernel stabilization
gives an exponent `r₀` and two x-annihilated quotients `Q1 = M/x^{r₀}M`,
`Q2 = M/x^{r₀+1}M` of `M` (each carrying the witness `t` by `module_inv_quotient`) with
  `Δφ_M(m) = φ_{Q1}(m−1) − φ_{Q2}(m)`  for all `m`  (`hilbertDiff_eq_xpow_quot`).
Each `φ_{Qᵢ}` is a numerical polynomial via `hilbertFun_xann_quotient_isNumpoly`
(consuming the strong `IH` at `|t'| < k`). Then `Δφ_M` is the difference of a
down-shifted numpoly and a numpoly, hence numpoly (`numpoly_shift_down` + `eventualNumpoly_add`
+ negation). NO torsion submodule, NO submodule witness — the false counterexample is
never invoked. -/
theorem hilbertDiff_module_step (k : ℕ)
    (IH :
      ∀ m : ℕ,
        m < k →
          ∀ {S M : Type u} [CommRing S] [IsNoetherianRing S] (𝒮 : ℤ → AddSubgroup S) [GradedRing 𝒮]
            [AddCommGroup M] [Module S M] [Module.Finite S M] (ℳ : ℤ → AddSubgroup M)
            [SetLike.GradedSMul 𝒮 ℳ] [DirectSum.Decomposition ℳ] (hneg : ∀ d : ℤ, d < 0 → 𝒮 d = ⊥)
            (_ : GeneratedInDegreeOne 𝒮) (t : Finset S) (_ : t.card ≤ m) (_ : ∀ x ∈ t, x ∈ 𝒮 1)
            (_ :
              irrelevantIdeal 𝒮 • (⊤ : Submodule S M) =
                Ideal.span (t : Set S) • (⊤ : Submodule S M)),
            IsEventualNumericalPolynomial
              (fun n => hilbertFun 𝒮 ℳ hneg n - hilbertFun 𝒮 ℳ hneg (n - 1))) :
    ∀ {S M : Type u} [CommRing S] [IsNoetherianRing S] (𝒮 : ℤ → AddSubgroup S) [GradedRing 𝒮]
      [AddCommGroup M] [Module S M] [Module.Finite S M] (ℳ : ℤ → AddSubgroup M)
      [SetLike.GradedSMul 𝒮 ℳ] [DirectSum.Decomposition ℳ] (hneg : ∀ d : ℤ, d < 0 → 𝒮 d = ⊥)
      (_ : GeneratedInDegreeOne 𝒮) (t : Finset S) (_ : t.card ≤ k) (_ : ∀ x ∈ t, x ∈ 𝒮 1)
      (_ : t.Nonempty)
      (_ : irrelevantIdeal 𝒮 • (⊤ : Submodule S M) = Ideal.span (t : Set S) • (⊤ : Submodule S M)),
      IsEventualNumericalPolynomial
        (fun n => hilbertFun 𝒮 ℳ hneg n - hilbertFun 𝒮 ℳ hneg (n - 1)) := by
  intro S M inst1 inst2 𝒮 inst3 inst4 inst5 inst6 ℳ inst7 inst8 hneg hgen t hcard ht1 hne hinv
  -- Pick a degree-one generator `x ∈ t`.
  obtain ⟨x, hxt⟩ := hne
  have hx1 : x ∈ 𝒮 1 := ht1 x hxt
  -- Four-term `·xʳ` sequence + Noetherian stabilization: produce r₀ and the two
  -- quotients Q1 = M/x^{r₀}M, Q2 = M/x^{r₀+1}M with the identity AND the numpoly-ness
  -- of `φ_{Q1}`, `φ_{Q2}` (each via the `P_j`-filtration consuming the strong `IH`).
  obtain ⟨r₀, Q1, _, _, _, 𝒬1, _, _, Q2, _, _, _, 𝒬2, _, _, hQ1, hQ2, hidentity⟩ :=
    hilbertDiff_eq_xpow_quot 𝒮 ℳ k IH hneg hgen x hx1 t hxt hcard ht1 hinv
  -- `m ↦ -φ_{Q1}(m-1)` is numpoly (down-shift + negation); `m ↦ φ_{Q2}(m)` is numpoly.
  have hQ1shiftneg : IsEventualNumericalPolynomial (fun m => -hilbertFun 𝒮 𝒬1 hneg (m - 1)) :=
    numpoly_neg _ (numpoly_shift_down _ hQ1)
  -- Δφ_M(m) = φ_{Q2}(m) - φ_{Q1}(m-1) = φ_{Q2}(m) + (-φ_{Q1}(m-1)).
  have hsum := eventualNumpoly_add _ _ hQ2 hQ1shiftneg
  have hcongr :
    (fun n => hilbertFun 𝒮 ℳ hneg n - hilbertFun 𝒮 ℳ hneg (n - 1)) =
      (fun m => hilbertFun 𝒮 𝒬2 hneg m + (-hilbertFun 𝒮 𝒬1 hneg (m - 1))) := by
    funext m
    rw [hidentity m]
    abel
  rw [hcongr]
  exact hsum

/-- The module-level induction engine: for a finite graded module whose irrelevant-ideal
action is generated by at most `k` degree-one elements, the first difference of the Hilbert
function is eventually a numerical polynomial. -/
theorem hilbertDiff_numpoly_module_aux (k : ℕ) :
    ∀ {S M : Type u} [CommRing S] [IsNoetherianRing S] (𝒮 : ℤ → AddSubgroup S) [GradedRing 𝒮]
      [AddCommGroup M] [Module S M] [Module.Finite S M] (ℳ : ℤ → AddSubgroup M)
      [SetLike.GradedSMul 𝒮 ℳ] [DirectSum.Decomposition ℳ] (hneg : ∀ d : ℤ, d < 0 → 𝒮 d = ⊥)
      (_ : GeneratedInDegreeOne 𝒮) (t : Finset S) (_ : t.card ≤ k) (_ : ∀ x ∈ t, x ∈ 𝒮 1)
      (_ : irrelevantIdeal 𝒮 • (⊤ : Submodule S M) = Ideal.span (t : Set S) • (⊤ : Submodule S M)),
      IsEventualNumericalPolynomial
        (fun n => hilbertFun 𝒮 ℳ hneg n - hilbertFun 𝒮 ℳ hneg (n - 1)) := by
  -- Strong induction on `k`. Base case `t = ∅` is discharged inline via
  -- `module_smul_top_eq_bot_eventually_zero`; the nonempty step is delegated to
  -- `hilbertDiff_module_step`, threading the strong IH as its hypothesis.
  induction k using Nat.strong_induction_on with
  | _ k
    IH =>
    intro S M inst1 inst2 𝒮 inst3 inst4 inst5 inst6 ℳ inst7 inst8 hneg hgen t hcard ht1 hinv
    rcases t.eq_empty_or_nonempty with hempty | hne
    · -- Base case: t = ∅ ⇒ S_+ · M = ⊥ ⇒ M_n eventually ⊥ ⇒ difference eventually 0.
      subst hempty
      have hann : irrelevantIdeal 𝒮 • (⊤ : Submodule S M) = ⊥ := by
        rw [hinv]; simp
      have hM := module_smul_top_eq_bot_eventually_zero 𝒮 ℳ hneg hann
      rw [Filter.eventually_atTop] at hM
      obtain ⟨N, hN⟩ := hM
      apply numpoly_of_eventually_zero
      rw [Filter.eventually_atTop]
      refine ⟨N + 1, fun n hn => ?_⟩
      have hsub : Subsingleton ↥(ℳ n) := by
        rw [hN n (by omega)]; infer_instance
      have hsub' : Subsingleton ↥(ℳ (n - 1)) := by
        rw [hN (n - 1) (by omega)]; infer_instance
      simp [hilbertFun_eq_zero_of_subsingleton 𝒮 ℳ hneg n,
        hilbertFun_eq_zero_of_subsingleton 𝒮 ℳ hneg (n - 1)]
    · -- Inductive step: delegate to `hilbertDiff_module_step`.
      exact hilbertDiff_module_step k IH 𝒮 ℳ hneg hgen t hcard ht1 hne hinv

/-- Ring-level form of the induction engine: if the irrelevant ideal is spanned by at most
`k` degree-one elements, the first difference of the Hilbert function is eventually a
numerical polynomial. -/
theorem hilbertDiff_numpoly_aux (k : ℕ) :
    ∀ {S M : Type u} [CommRing S] [IsNoetherianRing S] (𝒮 : ℤ → AddSubgroup S) [GradedRing 𝒮]
      [AddCommGroup M] [Module S M] [Module.Finite S M] (ℳ : ℤ → AddSubgroup M)
      [SetLike.GradedSMul 𝒮 ℳ] [DirectSum.Decomposition ℳ] (hneg : ∀ d : ℤ, d < 0 → 𝒮 d = ⊥)
      (_ : GeneratedInDegreeOne 𝒮)
      (_ :
        ∃ t : Finset S,
          t.card ≤ k ∧ (∀ x ∈ t, x ∈ 𝒮 1) ∧ irrelevantIdeal 𝒮 = Ideal.span (t : Set S)),
      IsEventualNumericalPolynomial
        (fun n => hilbertFun 𝒮 ℳ hneg n - hilbertFun 𝒮 ℳ hneg (n - 1)) := by
  -- REDUCTION TO THE MODULE-LEVEL ENGINE (no base-ring change). A ring-level
  -- degree-one generating set `t` of `S_+` (`irrelevantIdeal 𝒮 = Ideal.span ↑t`)
  -- automatically satisfies the module-level invariant
  -- `irrelevantIdeal 𝒮 • ⊤ = Ideal.span ↑t • ⊤` (apply `(· • ⊤)` to both sides).
  intro S M inst1 inst2 𝒮 inst3 inst4 inst5 inst6 ℳ inst7 inst8 hneg hgen hk
  obtain ⟨t, hcard, ht1, htspan⟩ := hk
  have hinv :
    irrelevantIdeal 𝒮 • (⊤ : Submodule S M) = Ideal.span (t : Set S) • (⊤ : Submodule S M) := by
    rw [htspan]
  exact hilbertDiff_numpoly_module_aux k 𝒮 ℳ hneg hgen t hcard ht1 hinv

/-- The first difference `n ↦ H(n) - H(n-1)` of the Hilbert function of a finite graded
module is eventually a numerical polynomial. -/
theorem hilbertFun_diff_isNumericalPolynomial (hneg : ∀ d : ℤ, d < 0 → 𝒮 d = ⊥)
    (hgen : GeneratedInDegreeOne 𝒮) :
    IsEventualNumericalPolynomial
      (fun n => hilbertFun 𝒮 ℳ hneg n - hilbertFun 𝒮 ℳ hneg (n - 1)) := by
  -- ASSEMBLY: choose a finite degree-one generating set of the irrelevant ideal
  -- (`irrelevant_fg_degree_one`), take `k = t.card`, and apply the generalized
  -- inductive engine `hilbertDiff_numpoly_aux` at that bound.
  obtain ⟨t, ht1, htspan⟩ := irrelevant_fg_degree_one 𝒮 hgen
  exact hilbertDiff_numpoly_aux t.card 𝒮 ℳ hneg hgen ⟨t, le_rfl, ht1, htspan⟩

/-- **Main statement (Stacks Tag 00K1, Proposition 10.58.7).**
Let `S` be a Noetherian graded ring with degree-zero ring `S_0 = ↥(𝒮 0)`, graded
nonnegatively (`𝒮 d = 0` for `d < 0`), and let `M` be a finite graded `S`-module.
Assume the irrelevant ideal `S_+` is generated by elements of degree `1`
(`GeneratedInDegreeOne 𝒮`).  Then the Hilbert function
`n ↦ [M_n] ∈ K'_0(S_0)` is a numerical polynomial. -/
@[stacks 00K1]
theorem hilbertFun_isNumericalPolynomial (hneg : ∀ d : ℤ, d < 0 → 𝒮 d = ⊥)
    (hgen : GeneratedInDegreeOne 𝒮) : IsEventualNumericalPolynomial (hilbertFun 𝒮 ℳ hneg) := by
  -- ASSEMBLY of the sketch. The first difference of `φ` is a numerical
  -- polynomial (`hilbertFun_diff_isNumericalPolynomial`); the combinatorial
  -- integration lemma `numpoly_of_diff` then upgrades this to `φ` itself being
  -- a numerical polynomial. (The base case `𝒮 1 = ⊥` is already absorbed inside
  -- `hilbertFun_diff_isNumericalPolynomial`, but `numpoly_of_diff` closes the
  -- argument uniformly.)
  exact numpoly_of_diff (hilbertFun 𝒮 ℳ hneg) (hilbertFun_diff_isNumericalPolynomial 𝒮 ℳ hneg hgen)

end Main
