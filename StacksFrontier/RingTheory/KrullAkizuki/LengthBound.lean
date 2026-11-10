module

public import StacksFrontier.RingTheory.KrullAkizuki.IntermediateRingNoetherian
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite length of `R/xR` and the bound on the length of `M/xM`

Throughout, $R$ is a commutative ring (with $1$), an integral domain that is local
Noetherian of Krull dimension $1$, with fraction field $K = \operatorname{Frac}(R)$.

Let $r \geq 0$ be an integer and let $M$ be an $R$-submodule of $K^{\oplus r}$. Then for
every nonzero element $x \in R$:

1. **Finiteness.** $\operatorname{length}_R(R/xR) < \infty$.

2. **Bound.** $\operatorname{length}_R(M/xM) \leq r \cdot \operatorname{length}_R(R/xR)$.

## Background and conventions

- **Length of a module.** For an $R$-module $N$, the length $\operatorname{length}_R(N)$
  lives in $\mathbb{Z}_{\geq 0} \cup \{\infty\}$ (here modelled by `ℕ∞ = WithTop ℕ`). It is
  the supremum of lengths of strictly increasing chains of submodules, equivalently the
  length of a composition series when one exists. In Mathlib this is `Module.length R N`.
  Finiteness is expressed as `Module.length R N < ⊤`.

- **Fraction field.** $K = \operatorname{Frac}(R)$ is modelled by `FractionRing R`, the
  field of fractions of the domain $R$, with its canonical injective ring homomorphism
  $R \hookrightarrow K$ and the resulting $R$-module structure.

- **The free module $K^{\oplus r}$.** Modelled as `Fin r → FractionRing R`, carrying the
  componentwise $R$-action.

- **The submodule $xM$.** For $x \in R$ and an $R$-submodule $M \subseteq K^{\oplus r}$,
  $xM = \{x m : m \in M\}$ is the pointwise scalar multiple `x • M`, an $R$-submodule of
  $K^{\oplus r}$ contained in $M$. The quotient $M/xM$ is modelled as the quotient of $M$
  by the corresponding submodule of $M$, namely `Submodule.comap M.subtype (x • M)`.

- **The quotient $R/xR$.** The principal ideal $xR = (x)$ is `Ideal.span {x}`, and $R/xR$
  is `R ⧸ Ideal.span {x}` viewed as an $R$-module.

- **Krull dimension.** The Krull dimension of $R$ is `ringKrullDim R : WithBot ℕ∞`; the
  hypothesis $\dim R = 1$ is `ringKrullDim R = 1`.

## Edge cases

- When $r = 0$ we have $K^{\oplus 0} = 0$, so $M = 0$ and both sides of the bound are $0$.
- When $x$ is a unit, both $R/xR$ and $M/xM$ vanish and both sides are $0$.
- $M$ is NOT assumed to be finitely generated; the bound holds for an arbitrary
  $R$-submodule of $K^{\oplus r}$.
-/

@[expose] public section

open Pointwise

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]

omit [IsLocalRing R] in
/-- **Statement 1 (Finiteness).** If `R` is a local Noetherian integral domain of Krull
dimension `1` and `x ≠ 0`, then `R / xR` has finite length as an `R`-module. -/
@[stacks 00PE "(1)"]
theorem length_quotient_span_singleton_lt_top (hdim : ringKrullDim R = 1) (x : R) (hx : x ≠ 0) :
    Module.length R (R ⧸ Ideal.span {x}) < ⊤ := by
  -- `ringKrullDim R = 1` gives `Ring.KrullDimLE 1 R`, and `x ≠ 0` in a domain makes `x` a
  -- nonzerodivisor, so `R ⧸ (x)` has finite length.
  have : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr hdim.le
  exact lt_top_iff_ne_top.mpr <| Module.length_ne_top_iff.mpr <|
    isFiniteLength_quotient_span_singleton R (mem_nonZeroDivisors_of_ne_zero hx)

/-! ### Reduction of the bound to `QuotSMulTop`

The bound is proved by reducing `M ⧸ xM` to Mathlib's `QuotSMulTop x ↥M` (the module
`↥M ⧸ x • (⊤ : Submodule R ↥M)`), and then bounding `length (QuotSMulTop x ↥M)` for an
`R`-submodule `M ⊆ Fin r → K` by induction on `r`. -/

omit [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] in
/-- Pulling `x • M` back along `M.subtype` gives `x • ⊤` in `↥M`. -/
theorem comap_subtype_smul_eq_smul_top {N : Type*} [AddCommGroup N] [Module R N]
    (M : Submodule R N) (x : R) :
    Submodule.comap M.subtype (x • M) = x • (⊤ : Submodule R M) := by
  rw [← Submodule.comap_map_eq_of_injective M.subtype_injective (x • (⊤ : Submodule R M)),
    Submodule.map_pointwise_smul, Submodule.map_subtype_top]

omit [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] in
/-- **Model identification.** The model of `M ⧸ xM` used here, namely
`↥M ⧸ Submodule.comap M.subtype (x • M)`, has the same length as Mathlib's
`QuotSMulTop x ↥M = ↥M ⧸ x • (⊤ : Submodule R ↥M)`.

Indeed the two submodules of `↥M` are literally equal, because `M.subtype` is injective
with range `M`, so
`comap M.subtype (x • M) = comap M.subtype (map M.subtype (x • ⊤)) = x • ⊤`
(using `Submodule.map_pointwise_smul`, `Submodule.map_subtype_top`, and
`Submodule.comap_map_eq_of_injective`); `Submodule.quotEquivOfEq` then gives the
length-preserving `LinearEquiv`. -/
theorem length_quot_comap_eq_quotSMulTop {N : Type*} [AddCommGroup N] [Module R N]
    (M : Submodule R N) (x : R) :
    Module.length R (M ⧸ Submodule.comap M.subtype (x • M))
      = Module.length R (QuotSMulTop x M) :=
  (Submodule.quotEquivOfEq _ _ (comap_subtype_smul_eq_smul_top M x)).length_eq

omit [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] in
/-- **Right-exactness / subadditivity of `· ⧸ x·` on a short exact sequence.**
If `0 → A → B → C → 0` is a short exact sequence of `R`-modules then
`length (QuotSMulTop x B) ≤ length (QuotSMulTop x A) + length (QuotSMulTop x C)`.

Tensoring with `R ⧸ (x)` is right exact, so the induced sequence
`QuotSMulTop x A →(map f) QuotSMulTop x B →(map g) QuotSMulTop x C → 0` is exact with
`map g` surjective (`QuotSMulTop.map_exact`, `QuotSMulTop.map_surjective`). Writing
`F = QuotSMulTop.map x f`, `G = QuotSMulTop.map x g`:
* the short exact sequence `0 → ker G → QuotSMulTop x B → QuotSMulTop x C → 0`
  (`LinearMap.exact_subtype_ker_map`, `(ker G).subtype` injective, `G` surjective) gives
  `length (QuotSMulTop x B) = length (ker G) + length (QuotSMulTop x C)`
  (`Module.length_eq_add_of_exact`);
* `ker G = range F` (from exactness, `Function.Exact.linearMap_ker_eq`), and `range F` is
  the image of the surjection `F.rangeRestrict : QuotSMulTop x A ↠ range F`, so
  `length (ker G) = length (range F) ≤ length (QuotSMulTop x A)`
  (`Module.length_le_of_surjective`).
Combining with `add_le_add_right` yields the claim. -/
@[ega "III 7.3.5.3" "special case"]
theorem length_quotSMulTop_le_of_exact {A B C : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (x : R) (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hg : Function.Surjective g) (hexact : Function.Exact f g) :
    Module.length R (QuotSMulTop x B)
      ≤ Module.length R (QuotSMulTop x A) + Module.length R (QuotSMulTop x C) := by
  -- F = QuotSMulTop.map x f, G = QuotSMulTop.map x g; ⊗ R/(x) is right exact, so F,G are
  -- exact with G surjective (QuotSMulTop.map_exact / map_surjective).
  set F := QuotSMulTop.map x f with hF
  set G := QuotSMulTop.map x g with hG
  have hGsurj : Function.Surjective G := QuotSMulTop.map_surjective x hg
  have hFGexact : Function.Exact F G := QuotSMulTop.map_exact x hexact hg
  -- SES 0 → ker G → QuotSMulTop x B → QuotSMulTop x C → 0
  have hsplit : Module.length R (QuotSMulTop x B)
      = Module.length R (LinearMap.ker G) + Module.length R (QuotSMulTop x C) :=
    Module.length_eq_add_of_exact (LinearMap.ker G).subtype G
      (Submodule.subtype_injective _) hGsurj (LinearMap.exact_subtype_ker_map G)
  rw [hsplit]
  -- ker G = range F, and range F is the image of the surjection F.rangeRestrict, so
  -- length (ker G) = length (range F) ≤ length (QuotSMulTop x A).
  have hkereq : LinearMap.ker G = LinearMap.range F := hFGexact.linearMap_ker_eq
  have hle : Module.length R (LinearMap.range F) ≤ Module.length R (QuotSMulTop x A) :=
    Module.length_le_of_surjective F.rangeRestrict (LinearMap.surjective_rangeRestrict F)
  rw [hkereq]
  gcongr

/-! #### The base case `r = 1`

The base case `length (QuotSMulTop x M) ≤ length (R ⧸ (x))` for `M ⊆ K = FractionRing R`
is the heart of the lemma. The case where `x` is a unit is peeled off first (both sides
collapse to `0`), and the remaining case is split into four steps. The non-unit hypothesis
`¬ IsUnit x` is carried through the finiteness, ideal and finitely-generated steps, and is
genuinely needed: for a unit `x`, `length (R ⧸ I)` can be infinite for nonzero ideals `I`
even though `R ⧸ (x) = 0` has finite length (e.g. `R = k⟦X,Y⟧`).

* `length_quot_ideal_lt_top_of_span_lt_top` — finiteness: if `x` is a non-unit nonzerodivisor
  with `length (R ⧸ (x)) < ⊤`, then every nonzero ideal `I` has `length (R ⧸ I) < ⊤` (the only
  place the Noetherian/dimension hypotheses are used; `¬ IsUnit x` forces `dim R = 1`).
* `length_quotSMulTop_ideal_le` — the ideal case via two short exact sequences and
  cancellation of the finite addend `length (R ⧸ I)`.
* `length_quotSMulTop_fg_le` — denominator clearing: a f.g. `N ⊆ K` is isomorphic to a
  nonzero ideal, reducing to the ideal case.
* `length_quotSMulTop_le_of_fg_bound` — the chain-lifting reduction from arbitrary `M` to its
  finitely generated submodules (generic; needs no domain/dim/unit hypothesis). -/

/-- **Finiteness of `R ⧸ I` for nonzero ideals.** If `x` is a non-unit (so `(x) ≠ ⊤`)
nonzerodivisor with `length (R ⧸ (x)) < ⊤`, then `R ⧸ (x)` is Artinian, forcing `dim R = 1`;
since `R` is a local Noetherian domain, every nonzero ideal `I` is then `𝔪`-primary, so
`length (R ⧸ I) < ⊤`.

The hypothesis `hxu : ¬ IsUnit x` is essential: without it `x` could be a unit, `(x) = ⊤`
and `R ⧸ (x) = 0` of finite length vacuously while `dim R ≥ 2`, and the conclusion fails. -/
lemma length_quot_ideal_lt_top_of_span_lt_top (x : R) (hxu : ¬ IsUnit x)
    (hfin : Module.length R (R ⧸ Ideal.span {x}) < ⊤)
    (I : Ideal R) (hI : I ≠ ⊥) :
    Module.length R (R ⧸ I) < ⊤ := by
  -- Step 1: `hfin` and `x` a non-unit nonzerodivisor give `Ring.KrullDimLE 1 R`.
  -- `length (R ⧸ (x)) < ⊤` makes `R ⧸ (x)` Artinian, so `dim (R ⧸ (x)) = 0`; since `(x)` is
  -- a proper nonzero ideal, Krull's principal ideal theorem gives `dim R ≤ 1`.
  have hkd : Ring.KrullDimLE 1 R := by
    have hfl : IsFiniteLength R (R ⧸ Ideal.span {x}) :=
      Module.length_ne_top_iff.mp (lt_top_iff_ne_top.mp hfin)
    have hart : IsArtinianRing (R ⧸ Ideal.span {x}) :=
      isArtinian_of_tower R (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).right
    have hspanle : Ideal.span {x} ≤ IsLocalRing.maximalIdeal R :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (IsLocalRing.mem_maximalIdeal _ |>.mpr hxu))
    have hmin : (Ideal.span {x}).IsMinimalPrime (IsLocalRing.maximalIdeal R) := by
      refine ⟨⟨(IsLocalRing.maximalIdeal.isMaximal R).isPrime, hspanle⟩, fun q ⟨hqp, hqsub⟩ _ => ?_⟩
      have hsurj := Ideal.Quotient.mk_surjective (I := Ideal.span {x})
      have : (Ideal.map (Ideal.Quotient.mk (Ideal.span {x})) q).IsPrime :=
        Ideal.map_isPrime_of_surjective hsurj (by rwa [Ideal.mk_ker])
      have : (Ideal.map (Ideal.Quotient.mk (Ideal.span {x})) q).IsMaximal :=
        IsArtinianRing.isMaximal_of_isPrime _
      have hqmax : (Ideal.comap (Ideal.Quotient.mk (Ideal.span {x}))
          (Ideal.map (Ideal.Quotient.mk (Ideal.span {x})) q)).IsMaximal :=
        Ideal.comap_isMaximal_of_surjective _ hsurj
      rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
        sup_eq_left.mpr hqsub] at hqmax
      rw [IsLocalRing.eq_maximalIdeal hqmax]
    have hht : (IsLocalRing.maximalIdeal R).height ≤ 1 :=
      Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes_of_isLocalRing
        (Ideal.span {x}) hmin
    rw [Ring.krullDimLE_iff, ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    exact_mod_cast hht
  -- STEP 2: nonzero ideal `I` ⇒ `length (R ⧸ I) < ⊤`.
  -- Pick `0 ≠ a ∈ I`; `(a) ≤ I` gives a surjection `R ⧸ (a) ↠ R ⧸ I`, and
  -- `length (R ⧸ (a)) < ⊤` by `isFiniteLength_quotient_span_singleton` (needs `KrullDimLE 1 R`).
  obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  -- `(a) ≤ I` (since `a ∈ I`), so `R ⧸ I` is a quotient of `R ⧸ (a)`:
  -- `Submodule.mapQ`/`Ideal.Quotient.factor` is surjective; `Module.length_le_of_surjective`.
  have hle : Module.length R (R ⧸ I) ≤ Module.length R (R ⧸ Ideal.span {a}) := by
    refine Module.length_le_of_surjective (Submodule.mapQ (Ideal.span {a}) I LinearMap.id
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr haI))) ?_
    intro y
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective I y
    exact ⟨Submodule.Quotient.mk z, by simp⟩
  exact hle.trans_lt <| lt_top_iff_ne_top.mpr <| Module.length_ne_top_iff.mpr <|
    isFiniteLength_quotient_span_singleton R (mem_nonZeroDivisors_of_ne_zero ha0)

/-- **Ideal case.** For a nonzero ideal `I ⊆ R`, `x ≠ 0` a non-unit, assuming
`length (R ⧸ (x)) < ⊤`, `length (QuotSMulTop x ↥I) ≤ length (R ⧸ (x))`.

The proof uses two short exact sequences and a cancellation. If `I = ⊥`, then
`QuotSMulTop x ↥(⊥)` is trivial, of length `0`. Otherwise:
* (A) `0 → QuotSMulTop x ↥I → R ⧸ (x • I) → R ⧸ I → 0` gives
  `length (R ⧸ x•I) = length (QuotSMulTop x ↥I) + length (R ⧸ I)`;
* (B) `0 → R ⧸ I →(Ideal.mulQuot x I) R ⧸ (x • I) →(Ideal.quotOfMul x I) R ⧸ (x) → 0`
  (`Ideal.exact_mulQuot_quotOfMul`, `Ideal.mulQuot_injective` with `x ∈ nonZeroDivisors R`,
  `Ideal.quotOfMul_surjective`) gives
  `length (R ⧸ x•I) = length (R ⧸ I) + length (R ⧸ (x))`.
Equate and cancel the finite addend `length (R ⧸ I) < ⊤`
(`length_quot_ideal_lt_top_of_span_lt_top x hxu hfin I hI`; here `hxu` is required). -/
lemma length_quotSMulTop_ideal_le (x : R) (hx : x ≠ 0) (hxu : ¬ IsUnit x)
    (hfin : Module.length R (R ⧸ Ideal.span {x}) < ⊤)
    (I : Ideal R) :
    Module.length R (QuotSMulTop x I) ≤ Module.length R (R ⧸ Ideal.span {x}) := by
  -- I = ⊥ handled separately (QuotSMulTop x ⊥ subsingleton); else use the two SES above
  -- and cancel `length (R ⧸ I) < ⊤` via `length_quot_ideal_lt_top_of_span_lt_top ... hxu ...`.
  rcases eq_or_ne I ⊥ with hI | hI
  · -- I = ⊥: QuotSMulTop x ↥⊥ is subsingleton
    subst hI
    have hsub : Subsingleton (QuotSMulTop x ↥(⊥ : Ideal R)) := by
      unfold QuotSMulTop; infer_instance
    exact (Module.length_eq_zero_iff.mpr hsub).trans_le zero_le
  · -- I ≠ ⊥: two SES + cancel length (R ⧸ I)
    have hxnz : x ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hx
    have hxI_le_I : x • I ≤ I := by
      intro y hy
      rw [Submodule.mem_smul_pointwise_iff_exists] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      exact I.smul_mem x hz
    have heq := comap_subtype_smul_eq_smul_top I x
    have hf_le : (x • (⊤ : Submodule R I)) ≤ Submodule.comap I.subtype (x • I) := heq.ge
    -- sequence (A): 0 → QuotSMulTop x ↥I → R ⧸ (x•I) → R ⧸ I → 0
    let f : (QuotSMulTop x ↥I) →ₗ[R] (R ⧸ (x • I)) :=
      Submodule.mapQ (x • (⊤ : Submodule R I)) (x • I) I.subtype hf_le
    let g : (R ⧸ (x • I)) →ₗ[R] (R ⧸ I) := Submodule.factor hxI_le_I
    have hf : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ, heq, eq_bot_iff]
      rintro y hy
      rw [Submodule.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      simp only [Submodule.mem_bot, Submodule.mkQ_apply]
      exact (Submodule.Quotient.mk_eq_zero _).mpr hz
    have hg : Function.Surjective g := by
      intro y
      obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective I y
      exact ⟨Submodule.Quotient.mk z, rfl⟩
    have hexact : Function.Exact f g := by
      intro b
      obtain ⟨r, rfl⟩ := Submodule.mkQ_surjective (x • I) b
      refine ⟨fun hgb => ⟨Submodule.Quotient.mk ⟨r, ?_⟩, rfl⟩, ?_⟩
      · simpa [g, Ideal.Quotient.eq_zero_iff_mem] using hgb
      · rintro ⟨a, ha⟩
        obtain ⟨a', rfl⟩ := Submodule.mkQ_surjective _ a
        rw [← ha]
        simp [f, g, Ideal.Quotient.eq_zero_iff_mem]
    have hA : Module.length R (R ⧸ (x • I))
        = Module.length R (QuotSMulTop x ↥I) + Module.length R (R ⧸ I) :=
      Module.length_eq_add_of_exact f g hf hg hexact
    -- sequence (B): 0 → R ⧸ I → R ⧸ (x•I) → R ⧸ (x) → 0
    have hB : Module.length R (R ⧸ (x • I))
        = Module.length R (R ⧸ I) + Module.length R (R ⧸ Ideal.span {x}) :=
      Module.length_eq_add_of_exact (Ideal.mulQuot x I) (Ideal.quotOfMul x I)
        (Ideal.mulQuot_injective I hxnz) (Ideal.quotOfMul_surjective I)
        (Ideal.exact_mulQuot_quotOfMul I)
    -- combine and cancel the finite addend length (R ⧸ I)
    have hfinI : Module.length R (R ⧸ I) ≠ ⊤ :=
      ne_top_of_lt (length_quot_ideal_lt_top_of_span_lt_top x hxu hfin I hI)
    exact (WithTop.add_left_cancel hfinI ((add_comm _ _).trans (hA.symm.trans hB))).le

/-- **Denominator clearing (f.g. case).** A finitely generated `R`-submodule `N ⊆ K` is
isomorphic as an `R`-module to a nonzero ideal `I ⊆ R`, so the bound reduces to the ideal
case (`x` non-unit threaded through to that case). -/
lemma length_quotSMulTop_fg_le (x : R) (hx : x ≠ 0) (hxu : ¬ IsUnit x)
    (hfin : Module.length R (R ⧸ Ideal.span {x}) < ⊤)
    (N : Submodule R (FractionRing R)) (hN : N.FG) :
    Module.length R (QuotSMulTop x N) ≤ Module.length R (R ⧸ Ideal.span {x}) := by
  -- Clear denominators: `d ∈ nonZeroDivisors R` with `d • N ⊆ (1 : Submodule R K)`
  -- (`IsLocalization.exist_integer_multiples`); `μ_d : K ≃ₗ[R] K` (unit `d ∈ Kˣ`) restricts to
  -- `N ≃ₗ ↥(d•N)`, and `d•N ≃ₗ ↥I` for an ideal `I ⊆ R`. `QuotSMulTop.congr` +
  -- `LinearEquiv.length_eq` reduce to `length_quotSMulTop_ideal_le x hx hxu hfin I`.
  obtain ⟨s, hs⟩ := hN
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) s
    (id : FractionRing R → FractionRing R)
  have hcunit : IsUnit (algebraMap R (FractionRing R) (d : R)) :=
    IsLocalization.map_units (FractionRing R) d
  set u : (FractionRing R)ˣ := hcunit.unit with hu
  set μ : (FractionRing R) ≃ₗ[R] (FractionRing R) :=
    DistribMulAction.toLinearEquiv R (FractionRing R) u with hμ
  have hμapp : ∀ y : FractionRing R, μ y = (d : R) • y := by
    intro y
    rw [hμ]
    change u • y = _
    rw [Units.smul_def, hu, IsUnit.unit_spec, ← algebra_compatible_smul]
  -- map μ N = d • N
  have hmapeq : Submodule.map μ.toLinearMap N = (d : R) • N := by
    ext z
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      change μ y ∈ _
      rw [hμapp]
      exact Submodule.smul_mem_pointwise_smul y (d:R) N hy
    · intro hz
      rw [Submodule.mem_smul_pointwise_iff_exists] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      exact ⟨y, hy, (hμapp y)⟩
  -- d • N ≤ 1
  have hPle : (d : R) • N ≤ (1 : Submodule R (FractionRing R)) := by
    rw [← hs, Submodule.smul_span, Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    simp only [SetLike.mem_coe]
    rw [Submodule.one_eq_range]
    obtain ⟨z, hz⟩ := hd y hy
    exact ⟨z, hz⟩
  -- iso N ≃ₗ ↥(d•N)
  have e1' : N ≃ₗ[R] ↥((d : R) • N) :=
    (Submodule.equivMapOfInjective μ.toLinearMap μ.injective N).trans (.ofEq _ _ hmapeq)
  set I : Ideal R := Submodule.comap (Algebra.linearMap R (FractionRing R)) ((d : R) • N)
  have e2 : ↥I ≃ₗ[R] ↥((d : R) • N) :=
    Submodule.comap_equiv_self_of_inj_of_le (FaithfulSMul.algebraMap_injective R (FractionRing R))
      (by rwa [← Submodule.one_eq_range])
  calc Module.length R (QuotSMulTop x N)
      = Module.length R (QuotSMulTop x ↥I) := (QuotSMulTop.congr x (e1'.trans e2.symm)).length_eq
    _ ≤ Module.length R (R ⧸ Ideal.span {x}) := length_quotSMulTop_ideal_le x hx hxu hfin I

omit [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] in
/-- **Chain-lifting reduction.** If a bound `b` holds for `QuotSMulTop x ↥N` for every
finitely generated submodule `N ≤ M`, then it holds for `QuotSMulTop x ↥M`. Generic: needs
no domain/dimension/unit hypothesis. -/
lemma length_quotSMulTop_le_of_fg_bound (x : R)
    (M : Submodule R (FractionRing R)) (b : ℕ∞)
    (hb : ∀ N : Submodule R (FractionRing R), N.FG → N ≤ M →
      Module.length R (QuotSMulTop x N) ≤ b) :
    Module.length R (QuotSMulTop x M) ≤ b :=
  length_quot_xtop_le_of_forall_fg R x M b hb

/-- **Base case `r = 1`.** For an arbitrary `R`-submodule `M ⊆ K = FractionRing R` and a
nonzero `x ∈ R`, `length (QuotSMulTop x M) ≤ length (R ⧸ (x))`.

Case-split on `IsUnit x`:
* `x` a unit: `(x) = ⊤` ⇒ `R ⧸ (x) = 0` and `x • ⊤ = ⊤` ⇒ `QuotSMulTop x M = 0`; `0 ≤ 0`.
* `x` a non-unit: case on whether `length (R ⧸ (x))` is `⊤` (`le_top`); otherwise apply the
  chain-lifting reduction `length_quotSMulTop_le_of_fg_bound` with `b = length (R ⧸ (x))`,
  discharging each f.g. piece with `length_quotSMulTop_fg_le` (passing `hxu`). -/
theorem length_quotSMulTop_le_base (M : Submodule R (FractionRing R)) (x : R) (hx : x ≠ 0) :
    Module.length R (QuotSMulTop x M) ≤ Module.length R (R ⧸ Ideal.span {x}) := by
  by_cases hxu : IsUnit x
  · -- Unit case: both sides are 0.
    have hsmul : x • (⊤ : Submodule R ↥M) = ⊤ := by
      rw [eq_top_iff]; rintro n -; obtain ⟨u, rfl⟩ := hxu
      refine ⟨(↑u⁻¹ : R) • n, trivial, ?_⟩
      change (u : R) • (↑u⁻¹ : R) • n = n
      rw [smul_smul]
      simp
    have hsub : Subsingleton (QuotSMulTop x ↥M) := by
      unfold QuotSMulTop; rw [hsmul]; infer_instance
    exact (Module.length_eq_zero_iff.mpr hsub).trans_le zero_le
  · -- Non-unit case: chain-lifting reduction + denominator clearing.
    rcases eq_top_or_lt_top (Module.length R (R ⧸ Ideal.span {x})) with htop | hfin
    · rw [htop]; exact le_top
    · exact length_quotSMulTop_le_of_fg_bound x M _
        (fun N hNfg _ => length_quotSMulTop_fg_le x hx hxu hfin N hNfg)

/-- **Inductive bound for `M ⊆ Fin r → K`.** For every `r` and every `R`-submodule
`M ⊆ Fin r → K`, `length (QuotSMulTop x M) ≤ r · length (R ⧸ (x))`.

The proof is by induction on `r`.
* `r = 0`: `Fin 0 → K` is the zero module, so `M = ⊥`, `QuotSMulTop x M` is trivial, length
  `0 = 0 · _`.
* `r+1`: split off the last coordinate. Let `g : ↥M →ₗ[R] K` be evaluation at `Fin.last r`
  (restriction of `LinearMap.proj (Fin.last r)`), with image submodule `M₁ ⊆ K`, and let
  `A := ker g`, which consists of elements of `M` vanishing in the last coordinate, hence
  embeds (via dropping the last coordinate, `LinearMap.comp (LinearMap.funLeft …)` /
  `Fin.snoc` machinery) into a submodule `M₀ ⊆ Fin r → K`. This produces a short exact
  sequence `0 → A → ↥M → M₁ → 0` (with `A ≃ₗ M₀` and `M₁ ⊆ K`). Apply
  `length_quotSMulTop_le_of_exact` to get
  `length (QuotSMulTop x ↥M) ≤ length (QuotSMulTop x A) + length (QuotSMulTop x M₁)`.
  Bound the first summand by the induction hypothesis applied to `M₀` (`≤ r · length R/xR`,
  via `A ≃ₗ M₀` and `QuotSMulTop.congr`) and the second by the base case
  `length_quotSMulTop_le_base` (`≤ length R/xR`). Summing gives `(r+1) · length R/xR`. -/
theorem length_quotSMulTop_le_pi (x : R) (hx : x ≠ 0) :
    ∀ (r : ℕ) (M : Submodule R (Fin r → FractionRing R)),
      Module.length R (QuotSMulTop x M) ≤ r * Module.length R (R ⧸ Ideal.span {x}) := by
  set L := Module.length R (R ⧸ Ideal.span {x}) with hL
  intro r
  induction r with
  | zero =>
    intro M
    -- Fin 0 → K is subsingleton, so M is subsingleton, so QuotSMulTop is subsingleton
    have hsub : Subsingleton (QuotSMulTop x ↥M) := by
      unfold QuotSMulTop; infer_instance
    rw [Module.length_eq_zero_iff.mpr hsub]
    simp
  | succ r ih =>
    intro M
    -- evaluation at last coordinate, restricted to M
    set g' : ↥M →ₗ[R] FractionRing R :=
      (LinearMap.proj (Fin.last r)) ∘ₗ M.subtype with hg'
    -- target M₁ = range g', the corestriction is surjective
    set φ : ↥M →ₗ[R] ↥(LinearMap.range g') := g'.rangeRestrict with hφ
    -- SES: 0 → ker φ → ↥M → range g' → 0
    have hexact1 :
        Module.length R (QuotSMulTop x ↥M)
          ≤ Module.length R (QuotSMulTop x ↥(LinearMap.ker φ))
            + Module.length R (QuotSMulTop x ↥(LinearMap.range g')) :=
      length_quotSMulTop_le_of_exact x
        (LinearMap.ker φ).subtype φ
        (hφ ▸ LinearMap.surjective_rangeRestrict g')
        (LinearMap.exact_subtype_ker_map φ)
    -- bound the range piece by base case
    have hbase : Module.length R (QuotSMulTop x ↥(LinearMap.range g'))
        ≤ L := length_quotSMulTop_le_base (LinearMap.range g') x hx
    -- the kernel piece: A = ker g' embeds into Fin r → K via dropping last coord
    set A := LinearMap.ker φ with hA
    have hAeq : A = LinearMap.ker g' := by rw [hA, hφ, LinearMap.ker_rangeRestrict]
    -- drop-last linear map on the ambient space
    set d : (Fin (r+1) → FractionRing R) →ₗ[R] (Fin r → FractionRing R) :=
      LinearMap.funLeft R (FractionRing R) Fin.castSucc with hd
    -- d ∘ M.subtype ∘ A.subtype, as a map A → (Fin r → K)
    set dA : ↥A →ₗ[R] (Fin r → FractionRing R) := d ∘ₗ M.subtype ∘ₗ A.subtype with hdA
    have hdAinj : Function.Injective dA := by
      intro a b hab
      -- a, b : ↥A; show a = b by showing underlying functions in Fin (r+1) → K agree
      apply Subtype.ext
      apply Subtype.ext
      -- goal: underlying functions in Fin (r+1) → K agree
      -- last coords both vanish (membership in A = ker g'); others agree by hab
      have hlast (c : ↥A) : (c.val : Fin (r+1) → FractionRing R) (Fin.last r) = 0 := by
        have hc : (c.val : ↥M) ∈ LinearMap.ker g' := hAeq ▸ c.property
        simpa [hg'] using hc
      funext j
      refine Fin.lastCases (by rw [hlast, hlast]) (fun i => ?_) j
      simpa [hdA, hd, LinearMap.funLeft_apply] using congrFun hab i
    -- M₀ := range dA ⊆ Fin r → K, and A ≃ M₀
    set M₀ : Submodule R (Fin r → FractionRing R) := LinearMap.range dA with hM₀
    have hAbound : Module.length R (QuotSMulTop x ↥A) ≤ ↑r * L :=
      (QuotSMulTop.congr x (LinearEquiv.ofInjective dA hdAinj)).length_eq ▸ ih M₀
    -- combine
    calc Module.length R (QuotSMulTop x ↥M)
        ≤ Module.length R (QuotSMulTop x ↥A)
            + Module.length R (QuotSMulTop x ↥(LinearMap.range g')) := hexact1
      _ ≤ ↑r * L + L := add_le_add hAbound hbase
      _ = ↑(r+1) * L := by
          rw [Nat.cast_succ, add_mul, one_mul]

/-- **Statement 2 (Bound).** Let `R` be a local Noetherian integral domain of Krull
dimension `1` with fraction field `K = FractionRing R`. For a non-negative integer `r`,
any `R`-submodule `M` of `K^r = (Fin r → K)`, and any nonzero `x ∈ R`, the length of
`M / xM` is bounded by `r * length (R / xR)`. Here `xM = x • M` and `M / xM` is the
quotient of `M` by the submodule `Submodule.comap M.subtype (x • M)`. -/
@[stacks 00PE "(2)"]
theorem length_quot_smul_le_mul_length_quot_span
    (r : ℕ) (M : Submodule R (Fin r → FractionRing R)) (x : R) (hx : x ≠ 0) :
    Module.length R (M ⧸ Submodule.comap M.subtype (x • M))
      ≤ r * Module.length R (R ⧸ Ideal.span {x}) := by
  -- Assemble from the helpers: rewrite the model to `QuotSMulTop x ↥M`
  -- (`length_quot_comap_eq_quotSMulTop`) then apply the inductive bound
  -- (`length_quotSMulTop_le_pi`).  Note `hdim` is not needed for the inequality itself
  -- (it holds in `ℕ∞` regardless); it is needed only via Statement 1 to know the RHS is
  -- finite.
  rw [length_quot_comap_eq_quotSMulTop M x]
  exact length_quotSMulTop_le_pi x hx r M

end
