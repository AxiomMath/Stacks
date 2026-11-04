module

public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Polynomial.GroupRingAction
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.Polynomial.Subring
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

(Stacks project, Tag 09EG / Lemma 15.112.2, "More on Algebra",
Section 15.112 "Group actions and integral closure".)

Let `R` be a commutative ring, let `G` be a finite group acting on `R` by ring
automorphisms (a `MulSemiringAction G R`), and let `I ⊆ R` be a `G`-stable ideal
(i.e. `σ(I) ⊆ I` for all `σ ∈ G`; since each `σ` is an automorphism this is the
same as `σ(I) = I`). Write `A^G` for the fixed subring of a ring `A` carrying a
`G`-action (in Mathlib: `FixedPoints.subring A G`).

The `G`-action on `R` descends to a `G`-action by ring automorphisms on `R/I`,
characterized by `σ(x̄) = (σ·x)‾`. Set `I^G = I ∩ R^G`, an ideal of `R^G`. The
composite `R^G ↪ R ↠ R/I` lands in `(R/I)^G` with kernel `I^G`, hence factors as
an injective ring homomorphism

  `φ : R^G / I^G ⟶ (R/I)^G`     (the canonical comparison map).

The lemma asserts that, via `φ`:

  1. `(R/I)^G` is an *integral* extension of `R^G / I^G`;
  2. `Spec(φ) : Spec((R/I)^G) → Spec(R^G/I^G)` is a homeomorphism;
  3. for every prime `𝔮 ⊆ (R/I)^G` with contraction `𝔭 = φ⁻¹(𝔮)`, the induced
     residue field extension `κ(𝔭) → κ(𝔮)` is purely inseparable.
-/

open Pointwise

/-!
## Main Definition(s)

### The induced action on the quotient.

For a `G`-stable ideal `I` (`hI : ∀ g : G, g • I = I` using the pointwise action
of `G` on ideals), the `G`-action on `R` descends to a `MulSemiringAction G (R ⧸ I)`,
characterized by `g • (mk x) = mk (g • x)`. We construct it explicitly; it provides
the witness that the abstract hypothesis `hcompat` used below is realizable.
-/

/-- The induced `G`-action by ring automorphisms on the quotient `R ⧸ I`, for a
`G`-stable ideal `I`. Characterized by `g • (mk x) = mk (g • x)` (see
`quotAction_smul_mk`). -/
@[reducible] noncomputable def quotAction (R : Type*) [CommRing R] (G : Type*) [Group G]
    [MulSemiringAction G R] (I : Ideal R) (hI : ∀ g : G, g • I = I) :
    MulSemiringAction G (R ⧸ I) where
  smul g := fun x => Ideal.Quotient.lift I
    ((Ideal.Quotient.mk I).comp (MulSemiringAction.toRingAut G R g : R →+* R))
    (by
      intro a ha
      simp only [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      rw [← hI g]
      exact Ideal.mem_pointwise_smul_iff_inv_smul_mem.mpr (by simpa using ha)) x
  one_smul b := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective b
    change Ideal.Quotient.mk I ((1 : G) • x) = _; rw [one_smul]
  mul_smul x y b := by
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective b
    change Ideal.Quotient.mk I ((x * y) • z) = _; rw [mul_smul]; rfl
  smul_zero g := by change Ideal.Quotient.mk I (g • (0 : R)) = 0; rw [smul_zero]; rfl
  smul_add g x y := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    change Ideal.Quotient.mk I (g • (a + b)) = _; rw [smul_add]; rfl
  smul_one g := by change Ideal.Quotient.mk I (g • (1 : R)) = 1; rw [smul_one]; rfl
  smul_mul g x y := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    change Ideal.Quotient.mk I (g • (a * b)) = _; rw [smul_mul']; rfl

/-- Correctness of `quotAction`: the induced action is characterized by
`g • (mk x) = mk (g • x)`. In particular, the abstract compatibility hypothesis
`hcompat` below is satisfiable. -/
theorem quotAction_smul_mk (R : Type*) [CommRing R] (G : Type*) [Group G]
    [MulSemiringAction G R] (I : Ideal R) (hI : ∀ g : G, g • I = I) (g : G) (x : R) :
    letI := quotAction R G I hI
    g • Ideal.Quotient.mk I x = Ideal.Quotient.mk I (g • x) := rfl

/-- Every coefficient of a `G`-fixed polynomial over `R` lies in the invariant subring `R^G`. -/
theorem coeffs_subset_fixedPoints {R : Type*} [CommRing R] {G : Type*} [Group G]
    [MulSemiringAction G R] {p : Polynomial R} (hp : ∀ g : G, g • p = p) :
    (↑p.coeffs : Set R) ⊆ ↑(FixedPoints.subring R G) := by
  refine fun x hx => ?_
  rw [Finset.mem_coe, Polynomial.mem_coeffs_iff] at hx
  obtain ⟨n, -, rfl⟩ := hx
  show p.coeff n ∈ FixedPoints.subring R G
  intro g
  rw [← Polynomial.coeff_smul, hp g]

/-- Every coefficient of the characteristic polynomial
`MulSemiringAction.charpoly G y = ∏_{σ ∈ G} (X - C (σ • y))` of `y : R` lies in the
invariant subring `R^G`. -/
@[sga "3 V 4.1" "special case"]
theorem MulSemiringAction.charpoly_coeffs_subset_fixedPoints {R : Type*} [CommRing R]
    {G : Type*} [Group G] [MulSemiringAction G R] [Fintype G] (y : R) :
    (↑(MulSemiringAction.charpoly G y).coeffs : Set R) ⊆ ↑(FixedPoints.subring R G) :=
  coeffs_subset_fixedPoints fun g => MulSemiringAction.smul_charpoly y g

/-- **(Stacks 09EF, range of the map, for an arbitrary ring map.)** If every `b : B` is
matched by a monic polynomial over `A` whose image in `B[X]` is `(X - C b) ^ n`, then `b ^ n`
lies in the range of `f`: it is `(-1) ^ n` times the image of the constant coefficient of that
witness, since the constant coefficient of `(X - C b) ^ n` is `(-b) ^ n`. -/
theorem exists_apply_eq_pow_of_sub_C_pow_witness {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (n : ℕ)
    (hwit : ∀ b : B, ∃ P : Polynomial A, P.Monic ∧
      Polynomial.map f P = (Polynomial.X - Polynomial.C b) ^ n) (b : B) :
    ∃ a, f a = b ^ n := by
  obtain ⟨P, -, hPmap⟩ := hwit b
  have hc : f (P.coeff 0) = ((Polynomial.X - Polynomial.C b) ^ n).coeff 0 := by
    rw [← hPmap, Polynomial.coeff_map]
  have hrhs : ((Polynomial.X - Polynomial.C b) ^ n).coeff 0 = (-b) ^ n := by
    rw [Polynomial.coeff_zero_eq_eval_zero]; simp
  rw [hrhs] at hc
  refine ⟨(-1) ^ n * P.coeff 0, ?_⟩
  rw [map_mul, map_pow, map_neg, map_one, hc, ← mul_pow]
  norm_num

/-- If `n ≠ 0` and every `b : B` has a monic witness mapping to `(X - C b) ^ n`, `f` is integral. -/
private theorem isIntegral_of_sub_C_pow_witness {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (n : ℕ) (hn : n ≠ 0)
    (hwit : ∀ b : B, ∃ P : Polynomial A, P.Monic ∧
      Polynomial.map f P = (Polynomial.X - Polynomial.C b) ^ n) : f.IsIntegral := by
  intro b
  obtain ⟨P, hPmonic, hPmap⟩ := hwit b
  refine ⟨P, hPmonic, ?_⟩
  rw [Polynomial.eval₂_eq_eval_map, hPmap]
  simp [hn]

/-- The characteristic polynomial of a lift `y` of a fixed `b`, reduced modulo a compatibly
`G`-acted-on ideal, is `(X - C b) ^ |G|`. -/
private theorem map_mk_charpoly_eq_pow_card {R : Type*} [CommRing R] {G : Type*} [Group G]
    [Fintype G] [MulSemiringAction G R] {I : Ideal R} [MulSemiringAction G (R ⧸ I)]
    (hcompat : ∀ (g : G) (x : R), g • Ideal.Quotient.mk I x = Ideal.Quotient.mk I (g • x))
    (b : FixedPoints.subring (R ⧸ I) G) {y : R} (hy : Ideal.Quotient.mk I y = b) :
    Polynomial.map (Ideal.Quotient.mk I) (MulSemiringAction.charpoly G y)
      = (Polynomial.X - Polynomial.C (b : R ⧸ I)) ^ (Fintype.card G) := by
  rw [MulSemiringAction.charpoly_eq_prod_smul, Polynomial.map_prod]
  rw [Finset.prod_congr rfl (g := fun _ => Polynomial.X - Polynomial.C (b : R ⧸ I))
    (fun g _ => ?_)]
  · rw [Finset.prod_const, Finset.card_univ]
  · rw [smul_sub, Polynomial.smul_C, Polynomial.smul_X, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C]
    rw [← hcompat, hy, b.property g]

/-- **(Algebraic kernel of Stacks 10.46.11, residue part.)** Let `F` be a field of
exponential characteristic `q`, `Kp ⊆ F` a subfield, `β ∈ F`, and suppose that all
coefficients of `(X - C β)^n` lie in `Kp` (with `n ≠ 0`). Writing `n = q^k·m` with
`q ∤ m` (`k = n.factorization q`), the element `β^{q^k}` lies in `Kp`.

Proof: `(X - Cβ)^n = expand_{q^k}((X - Cδ)^m)` where `δ = β^{q^k}` (by
`sub_pow_expChar_pow`); reading off the coefficient of `X^{q^k·(m-1)}` gives
`-m·δ ∈ Kp` (via `coeff_expand` and `coeff_X_add_C_pow`), and `(m : F) ≠ 0`
(char `0`: `m ≠ 0`; char `p`: `p ∤ m`), so `δ = (-m·δ)·(-(m:F)⁻¹) ∈ Kp`. -/
theorem pow_expChar_mem_of_sub_C_pow_coeffs_mem
    {F : Type*} [Field F] (p : ℕ) [hc : ExpChar F p] (Kp : Subfield F) (β : F)
    (n : ℕ) (hn : n ≠ 0)
    (h : ∀ i, ((Polynomial.X - Polynomial.C β) ^ n).coeff i ∈ Kp) :
    β ^ (p ^ (n.factorization p)) ∈ Kp := by
  set k := n.factorization p with hk
  set m := n / p ^ k with hm
  have hqk : 0 < p ^ k := pow_pos (expChar_pos F p) k
  have hnk : p ^ k * m = n := Nat.mul_div_cancel' (Nat.ordProj_dvd n p)
  have hmpos : 0 < m := Nat.div_pos (Nat.ordProj_le p hn) hqk
  set δ := β ^ (p ^ k) with hδ
  have hrw : (Polynomial.X - Polynomial.C β) ^ n
      = (Polynomial.expand F (p ^ k)) ((Polynomial.X - Polynomial.C δ) ^ m) := by
    rw [map_pow, map_sub, Polynomial.expand_X, Polynomial.expand_C,
      show Polynomial.C δ = (Polynomial.C β) ^ (p ^ k) from (map_pow _ _ _),
      ← sub_pow_expChar_pow, ← pow_mul, hnk]
  have hmem : ((Polynomial.X - Polynomial.C β) ^ n).coeff (p ^ k * (m - 1)) ∈ Kp := h _
  rw [hrw, Polynomial.coeff_expand hqk, ite_eq_left (Dvd.intro _ rfl),
    Nat.mul_div_cancel_left _ hqk] at hmem
  rw [show (Polynomial.X - Polynomial.C δ) = (Polynomial.X + Polynomial.C (-δ)) by
        rw [map_neg, sub_eq_add_neg],
    Polynomial.coeff_X_add_C_pow] at hmem
  rw [show m - (m - 1) = 1 from by omega, pow_one,
    show m.choose (m - 1) = m from by
      rw [← Nat.choose_symm (by omega), show m - (m - 1) = 1 from by omega,
        Nat.choose_one_right]] at hmem
  -- hmem : -δ * ↑m ∈ Kp
  have hmF : (m : F) ≠ 0 := by
    cases hc with
    | zero => exact_mod_cast hmpos.ne'
    | prime hp =>
      rw [Ne, CharP.cast_eq_zero_iff F p]
      exact Nat.not_dvd_ordCompl hp hn
  have hmKp : (m : F) ∈ Kp := natCast_mem Kp m
  have hneg : δ * (m : F) ∈ Kp := by
    have := Kp.neg_mem hmem; simpa using this
  have : δ * (m : F) * (m : F)⁻¹ ∈ Kp := Kp.mul_mem hneg (Kp.inv_mem hmKp)
  rwa [mul_assoc, mul_inv_cancel₀ hmF, mul_one] at this

/-- **(Stacks 09EF, residue-field conclusion, for an arbitrary ring map.)** Let
`f : A →+* B` be a ring map and `n ≠ 0` a natural number such that every `b : B` is
matched by a monic polynomial over `A` whose image in `B[X]` is `(X - C b) ^ n` — this
is hypothesis (2) of Stacks Tag 09EF, in the strengthened "all of `B`" form in which it
is available here. Then for every prime `q ⊆ B`, the induced extension of residue
fields `κ(f⁻¹ q) → κ(q)` is purely inseparable.

No hypothesis on `ker f` is needed for this half of Stacks 09EF, which is why the lemma
serves both Stacks 09EG below (where `f = quotientComparison` is injective) and Stacks 0H35 (where
the comparison map `R^G/J → (R/JR)^G` has a merely nil kernel).

Proof (Stacks 10.46.11, residue part): let `p` be the exponential characteristic of
`κ(f⁻¹ q)`, let `ψ : B → κ(q)` be the canonical map and let `Kp ⊆ κ(q)` be the image
subfield of `κ(f⁻¹ q)`. Applying `Polynomial.map ψ` to the witness equation shows that
every coefficient of `(X - C (ψ b)) ^ n` lies in `Kp`, so
`pow_expChar_mem_of_sub_C_pow_coeffs_mem` gives `(ψ b) ^ (p ^ k) ∈ Kp` with
`k = n.factorization p`, for every `b : B`. Every `z : κ(q)` is a ratio of two elements
`ψ b`, hence `z ^ (p ^ k) ∈ Kp`; this is the `pow_mem` characterization of pure
inseparability. -/
theorem isPurelyInseparable_residueField_of_sub_C_pow_witness
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (n : ℕ) (hn : n ≠ 0)
    (hwit : ∀ b : B, ∃ P : Polynomial A, P.Monic ∧
      Polynomial.map f P = (Polynomial.X - Polynomial.C b) ^ n)
    (q : Ideal B) [q.IsPrime] :
    letI := (Ideal.ResidueField.map (q.comap f) q f rfl).toAlgebra
    IsPurelyInseparable (Ideal.ResidueField (q.comap f)) (Ideal.ResidueField q) := by
  set 𝔭 := q.comap f with h𝔭
  set resmap := Ideal.ResidueField.map 𝔭 q f rfl with hresmap
  let algInst : Algebra 𝔭.ResidueField q.ResidueField := resmap.toAlgebra
  have halgmap : (algebraMap 𝔭.ResidueField q.ResidueField) = resmap := rfl
  -- `ψ : B → κ(𝔮)` the canonical algebra map.
  set ψ : B →+* q.ResidueField := algebraMap B q.ResidueField with hψ
  -- exponential characteristic of the base field, transferred to κ(𝔮).
  obtain ⟨p, hp⟩ := ExpChar.exists 𝔭.ResidueField
  have : ExpChar 𝔭.ResidueField p := hp
  have : ExpChar q.ResidueField p := expChar_of_injective_ringHom resmap.injective p
  -- The subfield Kp = range of resmap.
  set Kp := resmap.fieldRange with hKp
  -- Key: for every b, all coeffs of (X - C (ψ b))^n lie in Kp.
  have key : ∀ b : B, ∀ i,
      ((Polynomial.X - Polynomial.C (ψ b)) ^ n).coeff i ∈ Kp := by
    intro b i
    obtain ⟨P, -, hPmap⟩ := hwit b
    -- Apply `Polynomial.map ψ` to the witness equation.
    have himg : (Polynomial.X - Polynomial.C (ψ b)) ^ n
        = Polynomial.map (ψ.comp f) P := by
      rw [← Polynomial.map_map, hPmap, Polynomial.map_pow, Polynomial.map_sub,
        Polynomial.map_X, Polynomial.map_C]
    rw [himg, Polynomial.coeff_map]
    -- ψ (f (P.coeff i)) = resmap (algebraMap _ _ (P.coeff i)) ∈ range resmap
    have hbridge : (ψ.comp f) (P.coeff i)
        = resmap (algebraMap A 𝔭.ResidueField (P.coeff i)) := by
      rw [RingHom.comp_apply, hresmap, Ideal.ResidueField.map_algebraMap 𝔭 q f rfl]
    rw [hbridge]
    exact resmap.mem_fieldRange_self _
  -- Hence for every b, (ψ b)^(p^k) ∈ Kp where k = n.factorization p.
  have hbpow : ∀ b : B, (ψ b) ^ (p ^ (n.factorization p)) ∈ Kp := fun b =>
    pow_expChar_mem_of_sub_C_pow_coeffs_mem p Kp (ψ b) n hn (key b)
  -- Conclude purely inseparable via the `pow_mem` characterization (base field `κ(𝔭)`).
  rw [isPurelyInseparable_iff_pow_mem 𝔭.ResidueField p]
  intro z
  set k := n.factorization p with hkdef
  refine ⟨k, ?_⟩
  -- write z as a ratio of images of elements of B.
  obtain ⟨a, y, hy, hz⟩ := IsFractionRing.div_surjective (A := B ⧸ q) z
  -- lift a, y to B.
  obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
  -- algebraMap (B/q) κ ∘ mk = ψ.
  have hψa : algebraMap (B ⧸ q) q.ResidueField (Ideal.Quotient.mk q a') = ψ a' := rfl
  have hψy : algebraMap (B ⧸ q) q.ResidueField (Ideal.Quotient.mk q y') = ψ y' := rfl
  rw [hψa, hψy] at hz
  -- ψ y' ≠ 0.
  have hy0 : ψ y' ≠ 0 := by
    rw [← hψy]
    exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
      (nonZeroDivisors.ne_zero hy)
  -- z^(p^k) = (ψ a')^(p^k) / (ψ y')^(p^k), both numerator and denominator in Kp.
  rw [← hz, div_pow, halgmap]
  -- membership in resmap.range from membership in Kp = resmap.fieldRange.
  have hmem : (ψ a') ^ (p ^ k) / (ψ y') ^ (p ^ k) ∈ Kp :=
    Kp.div_mem (hbpow a') (hbpow y')
  obtain ⟨w, hw⟩ := hmem
  exact ⟨w, hw⟩

namespace FixedPoints

/- Throughout this section, `G` is a finite group acting by ring automorphisms on
the commutative ring `R`, `I` is an ideal of `R`, and `R ⧸ I` is equipped with a
`G`-action `[MulSemiringAction G (R ⧸ I)]` that is *compatible* with the action on
`R`, meaning `g • (mk x) = mk (g • x)` (the hypothesis `hcompat`). For a `G`-stable
ideal `I`, such an action exists by `quotAction` and is unique (`quotAction_smul_mk`),
so this abstractly-specified action is exactly the induced action on the quotient.

Several results below carry `set_option linter.unusedFintypeInType false in`: `[Fintype G]`
is used in their proofs, not in their statements, and weakening it to `Finite` would break
sibling results whose types mention `Fintype.card G`. -/
variable (R : Type*) [CommRing R] (G : Type*) [Group G] [Fintype G]
  [MulSemiringAction G R] (I : Ideal R)
  [MulSemiringAction G (R ⧸ I)]
  (hcompat : ∀ (g : G) (x : R),
    g • Ideal.Quotient.mk I x = Ideal.Quotient.mk I (g • x))

omit [Fintype G] in
/-- The invariant ideal `I^G = I ∩ R^G`, regarded as an ideal of the fixed
subring `R^G = FixedPoints.subring R G`. -/
noncomputable def invariantIdeal : Ideal (FixedPoints.subring R G) :=
  I.comap (FixedPoints.subring R G).subtype

omit [Fintype G] in
/-- `invariantIdeal`, under the name used in the Stacks 09EG statements. -/
noncomputable abbrev invIdeal : Ideal (FixedPoints.subring R G) := invariantIdeal R G I

omit [Fintype G] in
/-- The ring homomorphism `R^G → (R/I)^G` sending an invariant `a` to the class of
`a` in `R/I` (which is invariant because `g • mk a = mk (g • a) = mk a`). -/
noncomputable def toFixedQuot :
    (FixedPoints.subring R G) →+* (FixedPoints.subring (R ⧸ I) G) where
  toFun a := ⟨Ideal.Quotient.mk I (a : R), by intro g; rw [hcompat, a.property g]⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

omit [Fintype G] in
/-- The canonical comparison map `φ : R^G / I^G → (R/I)^G`, obtained by factoring
`toFixedQuot` through the quotient by `I^G` (which is contained in its kernel). -/
noncomputable def quotientComparison :
    (FixedPoints.subring R G ⧸ invariantIdeal R G I) →+*
      (FixedPoints.subring (R ⧸ I) G) :=
  Ideal.Quotient.lift (invariantIdeal R G I) (toFixedQuot R G I hcompat) (by
    intro a ha
    apply Subtype.ext
    change Ideal.Quotient.mk I (a : R) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha)

omit [Fintype G] in
/-- `quotientComparison`, under the name used in the Stacks 09EG statements. -/
noncomputable abbrev compMap :
    (FixedPoints.subring R G ⧸ invIdeal R G I) →+* (FixedPoints.subring (R ⧸ I) G) :=
  quotientComparison R G I hcompat

/-!
## Main Statement(s)

The four numbered conclusions of Tag 09EG are stated below as `quotientComparison_injective`,
`quotientComparison_isIntegral`, `quotientComparison_comap_isHomeomorph` and
`quotientComparison_residueField_isPurelyInseparable`. All four rest on the core structural lemma
`quotientComparison_polyWitness` (Stacks 0BRF specialized): every `b ∈ (R/I)^G` is matched by a
monic polynomial over `R^G/I^G` whose image under `φ` is `(X - C b)^{|G|}`. The two topological
conclusions then follow from the abstract form of Stacks 09EF (Lemma 10.46.11), namely
`PrimeSpectrum.isHomeomorph_comap` and
`isPurelyInseparable_residueField_of_sub_C_pow_witness`.
-/

omit [Fintype G] in
/-- **(Well-definedness of `R^G/I^G ⊆ (R/I)^G`.)** The canonical comparison map
`φ` is injective, so `R^G / I^G` is (isomorphic to) a subring of `(R/I)^G`.

Proof: `φ` is `Ideal.Quotient.lift` of `toFixedQuot : R^G → (R/I)^G`, so it
suffices to show `ker(toFixedQuot) = I^G = invariantIdeal`. If `a ∈ R^G` maps to `0`,
then `mk_I (a : R) = 0` in `R/I`, i.e. `a ∈ I`; and `a ∈ R^G`, so
`a ∈ invariantIdeal R G I` by definition (`I.comap (R^G).subtype`). Conversely the
quotient by `invariantIdeal` already kills these, so the lifted map is injective. -/
@[stacks 09EG]
theorem quotientComparison_injective :
    Function.Injective (compMap R G I hcompat) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [Ideal.Quotient.eq_zero_iff_mem]
  have hval : ((toFixedQuot R G I hcompat a : FixedPoints.subring (R ⧸ I) G) : R ⧸ I) = 0 := by
    have := congrArg (Subtype.val) ha
    simpa [quotientComparison, Ideal.Quotient.lift_mk] using this
  show (a : R) ∈ I
  rw [show ((toFixedQuot R G I hcompat a : FixedPoints.subring (R ⧸ I) G) : R ⧸ I)
      = Ideal.Quotient.mk I (a : R) from rfl] at hval
  rwa [Ideal.Quotient.eq_zero_iff_mem] at hval

/-- **(Core structural lemma — Stacks 0BRF specialized; the "(2)" hypothesis of
Stacks 09EF.)** For every `b ∈ (R/I)^G` there exists a *monic* polynomial `P`
over `R^G/I^G` whose image, under applying `φ = quotientComparison` to its coefficients,
equals `(X - C b)^{|G|}` in `(R/I)^G[X]`. In particular `n := |G| > 0`.

Construction (rigorous): choose `x ∈ R/I` representing `b` (here `b ∈ (R/I)^G`,
and `(R/I)^G ↪ R/I`), then lift to `y ∈ R` with `mk_I y = (b : R/I)` using
surjectivity of `mk_I`. Form `q := charpoly G y ∈ R[X]`, which is monic
(`monic_charpoly`) and whose coefficients lie in `R^G` (`charpoly_coeffs_mem_fixed`),
so it descends to a monic `q' : (R^G)[X]` with `map (R^G).subtype q' = q`
(`Polynomial.toSubring` / `Polynomial.map_toSubring`). Push `q'` along
`R^G → R^G/I^G` to get the desired monic `P`. Its image in `(R/I)^G[X]`:
mapping `q = ∏_σ (X - C (σ·y))` along the equivariant surjection `R → R/I` gives
`∏_σ (X - C (σ·mk_I y)) = ∏_σ (X - C (σ·b)) = charpoly G b`, and since `b` is
`G`-fixed every factor is `X - C b`, so this product is `(X - C b)^{|G|}`. The
coefficientwise maps `R → R/I` (on `q`) and `φ : R^G/I^G → (R/I)^G` (on `P`)
agree because both compute `mk_I` on representatives (compatibility of `φ` with
the quotient maps and with `toFixedQuot`). Hence `map φ P = (X - C b)^{|G|}`.

This is the only place the cited Mathlib lemma `MulSemiringAction.charpoly_eq_prod_smul`
(Stacks 0BRF) is used, via `monic_charpoly`, `eval_charpoly`, `smul_charpoly`. -/
theorem quotientComparison_polyWitness (b : FixedPoints.subring (R ⧸ I) G) :
    ∃ (P : Polynomial (FixedPoints.subring R G ⧸ invariantIdeal R G I)),
      P.Monic ∧
      Polynomial.map (quotientComparison R G I hcompat) P
        = (Polynomial.X - Polynomial.C b) ^ (Fintype.card G) := by
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (b : R ⧸ I)
  set q' := (MulSemiringAction.charpoly G y).toSubring (FixedPoints.subring R G)
    (MulSemiringAction.charpoly_coeffs_subset_fixedPoints y) with hq'
  have hq'map : Polynomial.map (FixedPoints.subring R G).subtype q'
      = MulSemiringAction.charpoly G y := Polynomial.map_toSubring _ _ _
  have hq'monic : q'.Monic :=
    (Polynomial.monic_toSubring _ _ _).mpr (MulSemiringAction.monic_charpoly G y)
  refine ⟨q'.map (Ideal.Quotient.mk (invariantIdeal R G I)), hq'monic.map _, ?_⟩
  rw [Polynomial.map_map,
    show (quotientComparison R G I hcompat).comp (Ideal.Quotient.mk (invariantIdeal R G I))
      = toFixedQuot R G I hcompat from Ideal.Quotient.lift_comp_mk _ _ _]
  apply Polynomial.map_injective (FixedPoints.subring (R ⧸ I) G).subtype
    (Subring.subtype_injective _)
  rw [Polynomial.map_map,
    show (FixedPoints.subring (R ⧸ I) G).subtype.comp (toFixedQuot R G I hcompat)
      = (Ideal.Quotient.mk I).comp (FixedPoints.subring R G).subtype from rfl,
    ← Polynomial.map_map, hq'map]
  rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  exact map_mk_charpoly_eq_pow_card hcompat b hy

set_option linter.unusedFintypeInType false in
/-- **(Integrality.)** Via the comparison map `φ`, the ring `(R/I)^G` is an integral
extension of `R^G / I^G`: every element of `(R/I)^G` is a root of a monic polynomial with
coefficients in the image of `R^G / I^G`.

Proof: fix `b ∈ (R/I)^G` and take the monic witness `P` over `R^G/I^G` from
`quotientComparison_polyWitness b`, with `map φ P = (X - C b)^{|G|}`. Then
`eval₂ φ b P = ((X - C b)^{|G|}).eval b = (b - b)^{|G|} = 0`. -/
theorem quotientComparison_isIntegral : (quotientComparison R G I hcompat).IsIntegral := by
  exact isIntegral_of_sub_C_pow_witness _ _ Fintype.card_pos.ne'
    (quotientComparison_polyWitness R G I hcompat)

set_option linter.unusedFintypeInType false in
/-- **(Integrality.)** Via the comparison map `φ`, the ring `(R/I)^G` is an
integral extension of `R^G / I^G`: every element of `(R/I)^G` is a root of a monic
polynomial with coefficients in the image of `R^G / I^G`.

Proof: by `Algebra.IsIntegral.mk`, fix `b ∈ (R/I)^G`. Take the monic witness `P`
over `R^G/I^G` from `compMap_polyWitness b`, with `map φ P = (X - C b)^{|G|}`.
Then under the algebra structure `φ.toAlgebra`, `aeval b P = (map φ P).eval b
= ((X - C b)^{|G|}).eval b = (b - b)^{|G|} = 0` (using
`Polynomial.aeval_def`, `Polynomial.eval_map`, `Polynomial.eval_pow`,
`Polynomial.eval_sub`, `Polynomial.eval_X`, `Polynomial.eval_C`), and `P` is
monic, so `b` is integral. -/
@[stacks 09EG]
theorem compMap_isIntegral :
    letI := (compMap R G I hcompat).toAlgebra
    Algebra.IsIntegral (FixedPoints.subring R G ⧸ invIdeal R G I)
      (FixedPoints.subring (R ⧸ I) G) := by
  let := (compMap R G I hcompat).toAlgebra
  exact Algebra.IsIntegral.mk (quotientComparison_isIntegral R G I hcompat)

set_option linter.unusedFintypeInType false in
/-- **(Homeomorphism on spectra.)** The induced map on prime spectra
`Spec(φ) : Spec((R/I)^G) → Spec(R^G/I^G)` is a homeomorphism for the Zariski topologies.
This is `PrimeSpectrum.isHomeomorph_comap` (the abstract form of Stacks 09EF) applied to the
two facts read off from `quotientComparison_polyWitness` and `quotientComparison_injective`: every
`b ∈ (R/I)^G` has `b ^ |G|` in the range of `φ`, and `ker φ = 0` is nil. -/
@[stacks 09EG]
theorem quotientComparison_comap_isHomeomorph :
    IsHomeomorph (PrimeSpectrum.comap (compMap R G I hcompat)) :=
  PrimeSpectrum.isHomeomorph_comap (quotientComparison R G I hcompat)
    (fun b => ⟨Fintype.card G, Fintype.card_pos, RingHom.mem_range.mpr
      (exists_apply_eq_pow_of_sub_C_pow_witness _ _
        (quotientComparison_polyWitness R G I hcompat) b)⟩)
    (fun a ha => by
      rw [(injective_iff_map_eq_zero _).mp (quotientComparison_injective R G I hcompat) a
        (RingHom.mem_ker.mp ha)]
      exact zero_mem _)

/- **(Stacks 09EF, residue-field conclusion — abstract input.)** Specialization
of Stacks Tag 09EF to `φ = quotientComparison`: for every prime `𝔮 ⊆ (R/I)^G` with
contraction `𝔭 = φ⁻¹(𝔮)`, the residue extension `κ(𝔭) → κ(𝔮)` is purely
inseparable.

Proof (Stacks 10.46.11): localize/quotient to reduce to the field `κ(𝔭)` and the
fibre `κ(𝔭) ⊗ (R/I)^G`. By the polynomial witness, every `b ∈ (R/I)^G` satisfies
`(X - C b)^{|G|} = image of a monic P over R^G/I^G`; writing `|G| = p^k m`
(`p = char κ(𝔭)`, `p ∤ m`; the case `char = 0` is `k = 0`), the element `b^{p^k}`
lies in the image of `κ(𝔭)`. Therefore every element of `κ(𝔮)` has a `p^k`-th
power in (the image of) `κ(𝔭)`, which is precisely purely inseparable. -/
set_option linter.unusedFintypeInType false in
/-- **(Purely inseparable residue extensions.)** For every prime `𝔮 ⊆ (R/I)^G` with
contraction `𝔭 = φ⁻¹(𝔮) ⊆ R^G/I^G`, the induced extension of residue fields
`κ(𝔭) → κ(𝔮)` is purely inseparable. This is the abstract form of Stacks 09EF,
`isPurelyInseparable_residueField_of_sub_C_pow_witness`, applied to the monic witness
`quotientComparison_polyWitness`. -/
@[stacks 09EG]
theorem quotientComparison_residueField_isPurelyInseparable
    (q : Ideal (FixedPoints.subring (R ⧸ I) G)) [q.IsPrime] :
    letI := (Ideal.ResidueField.map (q.comap (compMap R G I hcompat)) q
      (compMap R G I hcompat) rfl).toAlgebra
    IsPurelyInseparable (Ideal.ResidueField (q.comap (compMap R G I hcompat)))
      (Ideal.ResidueField q) :=
  isPurelyInseparable_residueField_of_sub_C_pow_witness (quotientComparison R G I hcompat)
    (Fintype.card G) Fintype.card_pos.ne' (quotientComparison_polyWitness R G I hcompat) q

end FixedPoints

/-
# Problem Description

Let `R` be a commutative ring and let `G` be a finite group of order `n = |G|`
acting on `R` by ring automorphisms (i.e. `R` carries a `MulSemiringAction` of
`G`).

1. **Ring of invariants.** `R^G = { r ∈ R | σ • r = r for all σ ∈ G }` is the
   subring of `G`-invariant elements of `R`.  In Mathlib this is
   `FixedPoints.subring R G`.

2. **Extended ideal.** Given an ideal `J ⊆ R^G`, let `JR` denote the ideal of
   `R` generated by the image of `J` under the inclusion `R^G ↪ R`.  This is the
   `Ideal.map` of `J` along the algebra map `R^G → R`.

3. **Induced action on the quotient.** Since `J ⊆ R^G`, the ideal `JR` is
   `G`-stable, so `G` acts on the quotient ring `R / JR` by ring automorphisms,
   and `(R / JR)^G` is its subring of invariants.

4. **The comparison ring map `Φ`.** The composite ring homomorphism
   `R^G ↪ R ↠ R / JR` lands in the invariants `(R / JR)^G` and kills `J`, so it
   descends to a well-defined ring homomorphism
   `Φ : R^G / J → (R / JR)^G`, `Φ(x̄) = x̄`.

For a ring `A` we write `A[T]` for the polynomial ring in one variable `T`, and
a polynomial is *monic* if its leading coefficient is `1`.

# Main Statement(s)

1. **(Lifting characteristic-polynomial form.)** For every `b ∈ (R / JR)^G`
   there exists a monic polynomial `P ∈ (R^G / J)[T]` whose image under the
   induced map `Φ_* : (R^G / J)[T] → ((R / JR)^G)[T]` (applying `Φ` to
   coefficients) equals `(T - b)^n`.

2. **(Kernel elements are nilpotent-like.)** For every
   `a ∈ ker(Φ : R^G / J → (R / JR)^G)` we have the identity
   `(T - a)^n = T^n` in `(R^G / J)[T]`.

3. **(The "In particular".)** `Φ` is an integral ring map which induces a
   homeomorphism on spectra and purely inseparable extensions of residue fields:
   `Φ.IsIntegral`; `IsHomeomorph (PrimeSpectrum.comap Φ)`; and for every prime
   `𝔮 ⊆ (R / JR)^G` with contraction `𝔭 = Φ⁻¹(𝔮)`, the residue field extension
   `κ(𝔭) → κ(𝔮)` is purely inseparable.

These are the two numbered conclusions and the final ("In particular") sentence of
Stacks Project Lemma 15.112.4 (tag 0H35).

# Notes and Interpretation

- The "In particular" conclusion is what Stacks obtains from parts (1) and (2)
  together with Algebra Lemma 10.46.11 (tag 09EF).  Only part (1) is needed: the
  integrality and the homeomorphism follow from the monic witness of part (1)
  (the constant coefficient of that witness puts `b ^ n` in the range of `Φ`),
  the kernel condition of 09EF follows from part (2) (evaluating
  `(T - a)^n = T^n` at `T = 0` gives `a ^ n = 0`, so `ker Φ` is nil), and the
  residue-field half is `isPurelyInseparable_residueField_of_sub_C_pow_witness`,
  the abstract form of 09EF proved alongside Stacks 09EG.
- `Φ_*` in part (1) denotes `Polynomial.map` of the ring map `Φ`.
- In part (2), `a ∈ R^G / J` and `T - a`, `T^n` are elements of the polynomial
  ring `(R^G / J)[T]`.
-/

namespace Stacks.Invariant.QuotientComparison

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [MulSemiringAction G R]

-- Main Definition(s)

/-- The extended ideal `JR ⊆ R` generated by the image of an ideal `J ⊆ R^G`
under the inclusion `R^G ↪ R`. -/
noncomputable def JRideal (J : Ideal (FixedPoints.subring R G)) : Ideal R :=
  Ideal.map (algebraMap (FixedPoints.subring R G) R) J

/-- `JR` is `G`-stable: every `g ∈ G` maps `JR` to itself. -/
theorem JRideal_invariant (J : Ideal (FixedPoints.subring R G)) (g : G) :
    g • (JRideal J) = JRideal J := by
  rw [Ideal.pointwise_smul_def, JRideal, Ideal.map_map]
  congr 1; ext x; simp only [RingHom.comp_apply]; exact x.property g

/-- The induced action of `G` on the quotient ring `R / JR` by ring automorphisms. This is the
action `quotAction` descended from `R` along `Ideal.Quotient.mk`, which applies because `JR` is
`G`-stable (`JRideal_invariant`). -/
noncomputable instance quotMulSemiringAction (J : Ideal (FixedPoints.subring R G)) :
    MulSemiringAction G (R ⧸ JRideal J) :=
  quotAction R G (JRideal J) (JRideal_invariant J)

/-- The induced action on `R / JR` is characterized by `g • x̄ = (g • x)‾`. -/
theorem quotSmul_mk (J : Ideal (FixedPoints.subring R G)) (g : G) (r : R) :
    g • (Ideal.Quotient.mk (JRideal J) r) = Ideal.Quotient.mk (JRideal J) (g • r) :=
  quotAction_smul_mk R G (JRideal J) (JRideal_invariant J) g r

/-- The composite ring homomorphism `R^G ↪ R ↠ R / JR`, corestricted to the subring of
invariants `(R / JR)^G`; this is `FixedPoints.toFixedQuot` for the `G`-stable ideal `JR`. -/
noncomputable def toFixedQuotJR (J : Ideal (FixedPoints.subring R G)) :
    (FixedPoints.subring R G) →+* (FixedPoints.subring (R ⧸ JRideal J) G) :=
  FixedPoints.toFixedQuot R G (JRideal J) (quotSmul_mk J)

/-- The map `R^G → (R / JR)^G` sends `x` to the class of `x` in `R / JR`. -/
theorem toFixedQuotJR_apply (J : Ideal (FixedPoints.subring R G))
    (x : FixedPoints.subring R G) :
    (toFixedQuotJR J x : R ⧸ JRideal J)
      = Ideal.Quotient.mk (JRideal J) (algebraMap _ R x) := rfl

/-- The comparison ring map `Φ : R^G / J → (R / JR)^G`. -/
noncomputable def invariantComparison (J : Ideal (FixedPoints.subring R G)) :
    ((FixedPoints.subring R G) ⧸ J) →+* (FixedPoints.subring (R ⧸ JRideal J) G) :=
  Ideal.Quotient.lift J (toFixedQuotJR J) (by
    intro a ha
    ext
    change (Ideal.Quotient.mk (JRideal J)) (algebraMap _ R a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ ha)

-- Shared machinery: the orbit characteristic polynomial.

/-- The characteristic polynomial `MulSemiringAction.charpoly G r = ∏_{g ∈ G} (X - C (g • r))`
of `r : R`, regarded as a polynomial over the invariant subring `R^G`. -/
noncomputable def charpolyFixed (G : Type*) [Group G] [MulSemiringAction G R] [Fintype G]
    (r : R) : Polynomial (FixedPoints.subring R G) :=
  (MulSemiringAction.charpoly G r).toSubring (FixedPoints.subring R G)
    (MulSemiringAction.charpoly_coeffs_subset_fixedPoints r)

/-- Mapping `charpolyFixed G r` along the inclusion `R^G → R` recovers the characteristic
polynomial `MulSemiringAction.charpoly G r`. -/
theorem charpolyFixed_map_subtype [Fintype G] (r : R) :
    Polynomial.map (FixedPoints.subring R G).subtype (charpolyFixed G r)
      = MulSemiringAction.charpoly G r :=
  Polynomial.map_toSubring _ _ _

/-- The characteristic polynomial over the invariant subring `R^G` is monic. -/
theorem charpolyFixed_monic [Fintype G] (r : R) : (charpolyFixed G r).Monic := by
  have h := MulSemiringAction.monic_charpoly G r
  rw [← charpolyFixed_map_subtype (G := G) r] at h
  exact Polynomial.monic_of_injective (FixedPoints.subring R G).subtype_injective h

/-- Mapping the characteristic polynomial through the quotient map `R → R / JR` gives the
characteristic polynomial of the image. -/
theorem charpoly_map_mk [Fintype G] (J : Ideal (FixedPoints.subring R G)) (r : R) :
    Polynomial.map (Ideal.Quotient.mk (JRideal J)) (MulSemiringAction.charpoly G r)
      = ∏ g : G, (Polynomial.X
          - Polynomial.C (g • Ideal.Quotient.mk (JRideal J) r)) := by
  rw [MulSemiringAction.charpoly_eq, Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro g _
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, quotSmul_mk]

/-- **Orbit collapse for invariant elements.** If `r : R` is `G`-invariant then its
characteristic polynomial is literally `(X - C r) ^ n`. -/
theorem charpoly_of_invariant [Fintype G] (r : R) (hr : ∀ g : G, g • r = r) :
    MulSemiringAction.charpoly G r
      = (Polynomial.X - Polynomial.C r) ^ (Fintype.card G) := by
  rw [MulSemiringAction.charpoly_eq]
  simp only [hr]
  rw [Finset.prod_const, Finset.card_univ]

/-- The characteristic polynomial of an invariant element `x : R^G`, over `R^G`, is
`(X - C x) ^ n`. -/
theorem charpolyFixed_of_coe [Fintype G] (x : FixedPoints.subring R G) :
    charpolyFixed G (x : R) = (Polynomial.X - Polynomial.C x) ^ (Fintype.card G) := by
  apply Polynomial.map_injective _ (FixedPoints.subring R G).subtype_injective
  rw [charpolyFixed_map_subtype, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C]
  exact charpoly_of_invariant (x : R) x.property

/-- Base case of the induction for Stacks 0H34: reducing `charpolyFixed G 0` modulo `J`
gives `X ^ n`. -/
theorem charpolyFixed_zero_map_mk [Fintype G] (J : Ideal (FixedPoints.subring R G)) :
    Polynomial.map (Ideal.Quotient.mk J) (charpolyFixed G (0 : R))
      = (Polynomial.X : Polynomial ((FixedPoints.subring R G) ⧸ J)) ^ (Fintype.card G) := by
  have h : charpolyFixed G (0 : R)
      = (Polynomial.X : Polynomial (FixedPoints.subring R G)) ^ (Fintype.card G) := by
    simpa using charpolyFixed_of_coe (0 : FixedPoints.subring R G)
  rw [h, Polynomial.map_pow, Polynomial.map_X]

open Polynomial in
/-- The cofactor `(C af)^{|u|-1} * ∏_{g∈u} (- C (g•b))` extracted from a nonempty
product of the `B` factors. -/
noncomputable def charpolyCofactorTerm (af b : R) (u : Finset G) : Polynomial R :=
  (Polynomial.C af) ^ (u.card - 1) * ∏ g ∈ u, (- Polynomial.C (g • b))

open Polynomial in
/-- The cofactor `q` such that `charpoly G (y + af * b) = charpoly G y + C af * q`. -/
noncomputable def charpolyCofactor (G : Type*) [Group G] [MulSemiringAction G R] [Fintype G]
    [DecidableEq G] (af b y : R) : Polynomial R :=
  ∑ t ∈ (Finset.univ.powerset \ {Finset.univ} : Finset (Finset G)),
    (∏ g ∈ t, (Polynomial.X - Polynomial.C (g • y)))
      * charpolyCofactorTerm af b (Finset.univ \ t)

open Polynomial in
/-- For a nonempty `u`, `∏_{g ∈ u} (-(C af * C (g • b))) = C af * charpolyCofactorTerm af b u`. -/
theorem charpolyCofactorTerm_factor (af b : R) (u : Finset G) (hu : u.Nonempty) :
    (∏ g ∈ u, (-(Polynomial.C af * Polynomial.C (g • b))))
      = Polynomial.C af * charpolyCofactorTerm af b u := by
  unfold charpolyCofactorTerm
  rw [Finset.prod_congr rfl (fun g _ => by ring :
      ∀ g ∈ u, (-(Polynomial.C af * Polynomial.C (g • b)))
        = Polynomial.C af * (- Polynomial.C (g • b)))]
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  have hpos : 1 ≤ u.card := Finset.card_pos.mpr hu
  have hpow : (Polynomial.C af) ^ u.card = Polynomial.C af * (Polynomial.C af) ^ (u.card - 1) := by
    conv_lhs => rw [show u.card = 1 + (u.card - 1) by omega, pow_add, pow_one]
  rw [hpow]; ring

open Polynomial in
/-- The `R`-level factorization `charpoly G (y + af * b) = charpoly G y + C af * q`, for
`G`-invariant `af`. -/
theorem charpoly_add_mul_eq [Fintype G] [DecidableEq G] (af b y : R)
    (haf : ∀ g : G, g • af = af) :
    MulSemiringAction.charpoly G (y + af * b)
      = MulSemiringAction.charpoly G y + Polynomial.C af * charpolyCofactor G af b y := by
  classical
  have hstep : MulSemiringAction.charpoly G (y + af * b)
      = ∏ g : G, ((Polynomial.X - Polynomial.C (g • y))
          + (-(Polynomial.C af * Polynomial.C (g • b)))) := by
    rw [MulSemiringAction.charpoly_eq]
    apply Finset.prod_congr rfl
    intro g _
    rw [smul_add, smul_mul', haf, Polynomial.C_add, Polynomial.C_mul]; ring
  rw [hstep, Finset.prod_add]
  rw [Finset.sum_eq_sum_sdiff_singleton_add (Finset.mem_powerset_self _)]
  simp only [sdiff_self, Finset.bot_eq_empty, Finset.prod_empty, mul_one]
  have hcpy : (∏ i : G, (Polynomial.X - Polynomial.C (i • y)))
      = MulSemiringAction.charpoly G y := rfl
  rw [hcpy, add_comm]
  congr 1
  unfold charpolyCofactor
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [Finset.mem_sdiff, Finset.mem_powerset, Finset.mem_singleton] at ht
  have hne : (Finset.univ \ t).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hcon
    exact ht.right (Finset.Subset.antisymm (Finset.subset_univ t) hcon)
  rw [charpolyCofactorTerm_factor af b _ hne]
  ring

open Polynomial in
/-- `qR` is `G`-fixed: the `G`-action permutes the indexing subsets and leaves the
sum invariant. -/
theorem charpolyCofactor_map_fixed [Fintype G] [DecidableEq G] (af b y : R) (h : G)
    (haf : ∀ g : G, g • af = af) :
    Polynomial.map (MulSemiringAction.toRingHom G R h) (charpolyCofactor G af b y)
      = charpolyCofactor G af b y := by
  classical
  unfold charpolyCofactor
  rw [Polynomial.map_sum]
  refine Finset.sum_equiv (Equiv.finsetCongr (Equiv.mulLeft h)) ?_ ?_
  · intro t
    simp only [Finset.mem_sdiff, Finset.mem_powerset, Finset.subset_univ, true_and,
      Finset.mem_singleton, Equiv.finsetCongr_apply]
    refine ⟨fun ht hcontra => ht (Finset.eq_univ_of_card t ?_),
      fun ht hcontra => ht (by rw [hcontra]; simp)⟩
    simpa using congrArg Finset.card hcontra
  · intro t ht
    simp only [Equiv.finsetCongr_apply]
    have hsdiff : Finset.univ \ Finset.map (Equiv.mulLeft h).toEmbedding t
          = Finset.map (Equiv.mulLeft h).toEmbedding (Finset.univ \ t) := by
        rw [Finset.map_sdiff]; congr 1; simp
    rw [Polynomial.map_mul]
    congr 1
    · rw [Polynomial.map_prod, Finset.prod_map]
      apply Finset.prod_congr rfl
      intro g _
      simp only [Equiv.coe_toEmbedding, Equiv.coe_mulLeft]
      simp [MulSemiringAction.toRingHom, mul_smul]
    · unfold charpolyCofactorTerm
      rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_prod, hsdiff]
      congr 1
      · congr 2
        · simp [MulSemiringAction.toRingHom, haf]
        · rw [Finset.card_map]
      · rw [Finset.prod_map]
        apply Finset.prod_congr rfl
        intro g _
        simp only [Equiv.coe_toEmbedding, Equiv.coe_mulLeft]
        rw [Polynomial.map_neg, Polynomial.map_C]
        simp [MulSemiringAction.toRingHom, mul_smul]

open Polynomial in
/-- The coefficients of `qR` are `G`-fixed (consequence of `charpolyCofactor_map_fixed`). -/
theorem charpolyCofactor_coeff_fixed [Fintype G] [DecidableEq G] (af b y : R)
    (haf : ∀ g : G, g • af = af) (k : ℕ) :
    (charpolyCofactor G af b y).coeff k ∈ FixedPoints.subring R G := by
  intro h
  have hc := congrArg (fun p => Polynomial.coeff p k) (charpolyCofactor_map_fixed af b y h haf)
  simp only [Polynomial.coeff_map] at hc
  exact hc

open Polynomial in
/-- If `af` is `G`-invariant, every coefficient of `charpolyCofactor G af b y` lies in the
invariant subring `R^G`. -/
theorem charpolyCofactor_coeffs_subset [Fintype G] [DecidableEq G] (af b y : R)
    (haf : ∀ g : G, g • af = af) :
    (↑(charpolyCofactor G af b y).coeffs : Set R) ⊆ (↑(FixedPoints.subring R G) : Set R) := by
  intro x hx
  rw [Finset.mem_coe, Polynomial.mem_coeffs_iff] at hx
  obtain ⟨n, _, rfl⟩ := hx
  exact charpolyCofactor_coeff_fixed af b y haf n

open Polynomial in
/-- **The single inductive step of Stacks 0H34.** For `f ∈ J ⊆ R^G` (hence `G`-invariant)
and arbitrary `b y : R`, adjusting the argument of the characteristic polynomial by the
`JR`-element `(algebraMap R^G R f) * b` does not change its reduction modulo `J`.

Implementation note: the `Finset.prod_add` expansion of
`charpoly G (y + af·b) = ∏_g ((X - C (g•y)) - C af · C (g•b))` is packaged as the single
cofactor `charpolyCofactor`, which is `G`-invariant (`charpolyCofactor_map_fixed`) and
therefore descends to a polynomial `Q` over `R^G` with
`charpolyFixed G (y + af·b) = charpolyFixed G y + C f * Q`. -/
theorem charpolyFixed_map_mk_add_mul_of_mem [Fintype G] (J : Ideal (FixedPoints.subring R G))
    (f : FixedPoints.subring R G) (hf : f ∈ J) (b : R) (y : R) :
    Polynomial.map (Ideal.Quotient.mk J) (charpolyFixed G (y + (algebraMap _ R f) * b))
      = Polynomial.map (Ideal.Quotient.mk J) (charpolyFixed G y) := by
  classical
  set af : R := algebraMap _ R f with haf_def
  have haf : ∀ g : G, g • af = af := f.property
  set Q : Polynomial (FixedPoints.subring R G) :=
    (charpolyCofactor G af b y).toSubring (FixedPoints.subring R G)
      (charpolyCofactor_coeffs_subset af b y haf) with hQ_def
  have hsubQ : Polynomial.map (FixedPoints.subring R G).subtype Q = charpolyCofactor G af b y := by
    rw [hQ_def]; exact Polynomial.map_toSubring _ _ _
  have hfactor : charpolyFixed G (y + af * b) = charpolyFixed G y + Polynomial.C f * Q := by
    apply Polynomial.map_injective _ (FixedPoints.subring R G).subtype_injective
    rw [charpolyFixed_map_subtype, Polynomial.map_add, charpolyFixed_map_subtype,
      Polynomial.map_mul, Polynomial.map_C, hsubQ]
    have hsub : (FixedPoints.subring R G).subtype f = af := rfl
    rw [hsub]
    exact charpoly_add_mul_eq af b y haf
  rw [hfactor, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
  have hf0 : Ideal.Quotient.mk J f = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hf
  rw [hf0, Polynomial.C_0, zero_mul, add_zero]

open Polynomial in
/-- **Stacks 0H34 (tag 0H34 = Lemma 15.112.3).** For `x ∈ JR`, the characteristic
polynomial `∏_{σ ∈ G} (T - σ x) = T^n + a₁T^{n-1} + … + aₙ` has all its non-leading
coefficients `aᵢ` in `J`; equivalently, reducing the coefficients of `charpolyFixed G x`
modulo `J` gives `X ^ n`.

Implementation note: the coefficients `aᵢ` lie in `R^G`, and what has to be shown is that
they lie in `J` — the ideal of `R^G` — and not merely in the a priori larger `JR ∩ R^G`.
Writing `x = Σⱼ fⱼ bⱼ` with `fⱼ ∈ J ⊆ R^G` and `bⱼ ∈ R`, invariance of `fⱼ` gives
`σ x = Σⱼ fⱼ (σ bⱼ)`, so each elementary symmetric coefficient is a sum of products each
carrying a factor `∏ fⱼ ∈ J`, and symmetrizing over the orbit keeps the remaining cofactor
in `R^G`; hence `aᵢ ∈ J · R^G = J`. -/
@[stacks 0H34]
theorem charpolyFixed_map_mk_of_mem [Fintype G] (J : Ideal (FixedPoints.subring R G))
    (x : R) (hx : x ∈ JRideal J) :
    Polynomial.map (Ideal.Quotient.mk J) (charpolyFixed G x)
      = (Polynomial.X : Polynomial ((FixedPoints.subring R G) ⧸ J)) ^ (Fintype.card G) := by
  let Φ : R → Polynomial ((FixedPoints.subring R G) ⧸ J) :=
    fun r => Polynomial.map (Ideal.Quotient.mk J) (charpolyFixed G r)
  have key : ∀ z ∈ JRideal J, ∀ (c : R) (y : R), Φ (y + c * z) = Φ y := by
    intro z hz
    rw [JRideal, Ideal.map, Ideal.span] at hz
    induction hz using Submodule.span_induction with
    | mem g hg =>
        obtain ⟨f, hfJ, rfl⟩ := hg
        intro c y
        rw [mul_comm c _]
        exact charpolyFixed_map_mk_add_mul_of_mem J f hfJ c y
    | zero => simp
    | add a b ha hb iha ihb =>
        intro c y
        calc Φ (y + c * (a + b)) = Φ ((y + c * b) + c * a) := by ring_nf
          _ = Φ (y + c * b) := iha c (y + c * b)
          _ = Φ y := ihb c y
    | smul d a ha iha =>
        intro c y
        show Φ (y + c * (d • a)) = Φ y
        rw [smul_eq_mul, show c * (d * a) = c * d * a by ring]
        exact iha (c * d) y
  have h0 := key x hx 1 0
  rw [zero_add, one_mul] at h0
  exact h0.trans (charpolyFixed_zero_map_mk J)

-- Main Statement(s)

/-- **(Lifting characteristic-polynomial form.)** For every `b ∈ (R / JR)^G`
there is a monic polynomial `P ∈ (R^G / J)[T]` whose image under
`Polynomial.map (invariantComparison J)` equals `(X - C b) ^ n`, where
`n = Fintype.card G`. -/
@[stacks 0H35 "(1)"]
theorem exists_monic_map_eq_X_sub_C_pow [Fintype G] (J : Ideal (FixedPoints.subring R G))
    (b : FixedPoints.subring (R ⧸ JRideal J) G) :
    ∃ P : Polynomial ((FixedPoints.subring R G) ⧸ J),
      P.Monic ∧
        P.map (invariantComparison J)
          = (Polynomial.X - Polynomial.C b) ^ (Fintype.card G) := by
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (b : R ⧸ JRideal J)
  refine ⟨(charpolyFixed G r).map (Ideal.Quotient.mk J), ?_, ?_⟩
  · exact (charpolyFixed_monic r).map _
  · apply Polynomial.map_injective _ (FixedPoints.subring (R ⧸ JRideal J) G).subtype_injective
    rw [Polynomial.map_map, Polynomial.map_map]
    have hcomp1 : ((FixedPoints.subring (R ⧸ JRideal J) G).subtype.comp
        (invariantComparison J)).comp (Ideal.Quotient.mk J)
        = (Ideal.Quotient.mk (JRideal J)).comp (algebraMap (FixedPoints.subring R G) R) := by
      ext y
      simp only [RingHom.coe_comp, Function.comp_apply, invariantComparison,
        Ideal.Quotient.lift_mk]
      exact toFixedQuotJR_apply J y
    rw [hcomp1]
    rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rw [← Polynomial.map_map (algebraMap (FixedPoints.subring R G) R)
        (Ideal.Quotient.mk (JRideal J))]
    rw [show Polynomial.map (algebraMap (FixedPoints.subring R G) R) (charpolyFixed G r)
        = MulSemiringAction.charpoly G r from charpolyFixed_map_subtype (G := G) r]
    exact map_mk_charpoly_eq_pow_card (quotSmul_mk J) b hr

/-- **(Kernel elements are nilpotent-like.)** For every
`a ∈ ker(invariantComparison J)` we have `(X - C a) ^ n = X ^ n` in
`(R^G / J)[T]`, where `n = Fintype.card G`. -/
@[stacks 0H35 "(2)"]
theorem X_sub_C_pow_eq_X_pow_of_mem_ker [Fintype G] (J : Ideal (FixedPoints.subring R G))
    (a : (FixedPoints.subring R G) ⧸ J) (ha : a ∈ RingHom.ker (invariantComparison J)) :
    (Polynomial.X - Polynomial.C a) ^ (Fintype.card G)
      = (Polynomial.X : Polynomial ((FixedPoints.subring R G) ⧸ J)) ^ (Fintype.card G) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hxJR : (x : R) ∈ JRideal J := by
    rw [RingHom.mem_ker, invariantComparison, Ideal.Quotient.lift_mk] at ha
    have hval : (toFixedQuotJR J x : R ⧸ JRideal J) = 0 := by rw [ha]; rfl
    rw [toFixedQuotJR_apply] at hval
    rwa [Ideal.Quotient.eq_zero_iff_mem] at hval
  have key : (Polynomial.X - Polynomial.C (Ideal.Quotient.mk J x)) ^ (Fintype.card G)
      = Polynomial.map (Ideal.Quotient.mk J) (charpolyFixed G (x : R)) := by
    rw [charpolyFixed_of_coe x, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C]
  rw [key, charpolyFixed_map_mk_of_mem J (x : R) hxJR]

/-- **(Helper for the "In particular".)** For every `b ∈ (R / JR)^G` the power `b ^ n`
(`n = |G|`) is in the range of `Φ`. -/
theorem exists_invariantComparison_eq_pow_card [Fintype G]
    (J : Ideal (FixedPoints.subring R G)) (b : FixedPoints.subring (R ⧸ JRideal J) G) :
    ∃ a, invariantComparison J a = b ^ (Fintype.card G) :=
  exists_apply_eq_pow_of_sub_C_pow_witness _ _ (exists_monic_map_eq_X_sub_C_pow J) b

/-- **(Helper for the "In particular".)** The kernel of `Φ` is nil, i.e. contained in
the nilradical of `R^G / J`: evaluating the identity `(X - C a) ^ n = X ^ n` of
`X_sub_C_pow_eq_X_pow_of_mem_ker` at `X = 0` gives `(-a) ^ n = 0`. -/
theorem ker_invariantComparison_le_nilradical [Finite G]
    (J : Ideal (FixedPoints.subring R G)) :
    RingHom.ker (invariantComparison J) ≤ nilradical ((FixedPoints.subring R G) ⧸ J) := by
  have := Fintype.ofFinite G
  intro a ha
  have h := congrArg (Polynomial.eval (0 : (FixedPoints.subring R G) ⧸ J))
    (X_sub_C_pow_eq_X_pow_of_mem_ker J a ha)
  simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, zero_sub] at h
  rw [zero_pow Fintype.card_pos.ne'] at h
  rw [mem_nilradical]
  have hnil : IsNilpotent (-a) := ⟨Fintype.card G, h⟩
  simpa using hnil.neg

set_option linter.unusedFintypeInType false in
/-- **(In particular: integrality.)** The comparison map
`Φ : R^G / J → (R / JR)^G` is an integral ring map: every `b ∈ (R / JR)^G` is a root
of the monic polynomial over `R^G / J` supplied by `exists_monic_map_eq_X_sub_C_pow`, because
that polynomial maps to `(X - C b) ^ n`, which vanishes at `b`. -/
@[stacks 0H35 "final statement, integrality"]
theorem invariantComparison_isIntegral [Fintype G] (J : Ideal (FixedPoints.subring R G)) :
    (invariantComparison J).IsIntegral := by
  exact isIntegral_of_sub_C_pow_witness _ _ Fintype.card_pos.ne'
    (exists_monic_map_eq_X_sub_C_pow J)

set_option linter.unusedFintypeInType false in
/-- **(In particular: homeomorphism on spectra.)** `Spec(Φ) : Spec((R / JR)^G) →
Spec(R^G / J)` is a homeomorphism.  This is `PrimeSpectrum.isHomeomorph_comap`
(Stacks 0BR8) applied to the two facts extracted from parts (1) and (2): every
`b ∈ (R / JR)^G` has `b ^ n` in the range of `Φ` (`exists_apply_eq_pow`), and
`ker Φ` is nil (`ker_invariantComparison_le_nilradical`). -/
@[stacks 0H35 "final statement, homeomorphism on spectra"]
theorem invariantComparison_comap_isHomeomorph [Fintype G] (J : Ideal (FixedPoints.subring R G)) :
    IsHomeomorph (PrimeSpectrum.comap (invariantComparison J)) :=
  PrimeSpectrum.isHomeomorph_comap (invariantComparison J)
    (fun b => ⟨Fintype.card G, Fintype.card_pos,
      RingHom.mem_range.mpr (exists_invariantComparison_eq_pow_card J b)⟩)
    (ker_invariantComparison_le_nilradical J)

set_option linter.unusedFintypeInType false in
/-- **(In particular: purely inseparable residue extensions.)** For every prime
`𝔮 ⊆ (R / JR)^G` with contraction `𝔭 = Φ⁻¹(𝔮) ⊆ R^G / J`, the induced extension of
residue fields `κ(𝔭) → κ(𝔮)` is purely inseparable.  This is the abstract form of
Stacks 09EF (`isPurelyInseparable_residueField_of_sub_C_pow_witness`, proved with
Stacks 09EG) applied to the monic witness of part (1). -/
@[stacks 0H35 "final statement, purely inseparable residue fields"]
theorem invariantComparison_residueField_isPurelyInseparable [Fintype G]
    (J : Ideal (FixedPoints.subring R G))
    (q : Ideal (FixedPoints.subring (R ⧸ JRideal J) G)) [q.IsPrime] :
    letI := (Ideal.ResidueField.map (q.comap (invariantComparison J)) q
      (invariantComparison J) rfl).toAlgebra
    IsPurelyInseparable (Ideal.ResidueField (q.comap (invariantComparison J)))
      (Ideal.ResidueField q) :=
  isPurelyInseparable_residueField_of_sub_C_pow_witness (invariantComparison J)
    (Fintype.card G) Fintype.card_pos.ne' (exists_monic_map_eq_X_sub_C_pow J) q

end Stacks.Invariant.QuotientComparison

/-!
## Lifting a power of a linear polynomial along an equivariant surjection

For an equivariant surjection of rings carrying an action of a finite group, a fixed element
of the target admits a monic polynomial over the fixed subring of the source whose image is
the corresponding power of its linear polynomial.  Together with the invertible-order case of
the comparison map `Φ : R^G / J → (R / JR)^G` this completes Section 15.112 of the Stacks
project.

## Main results

* `MulSemiringAction.exists_monic_map_eq_X_sub_C_pow_card` (Stacks 0BRF): a fixed element of
  the target of an equivariant surjection has a monic polynomial lift over the fixed subring
  of the source whose image is `(X - C b) ^ |G|`.
* `Stacks.Invariant.QuotientComparison.charpolyFixed_map_mk_of_mem` (Stacks 0H34): all the
  non-leading coefficients of
  the orbit polynomial of an element of `JR` lie in `J`.
* `Stacks.Invariant.QuotientComparison.invariantComparison_bijective_of_isUnit_card` (Stacks 0H36):
  if `|G|` is
  invertible in `R` then `Φ : R^G / J → (R / JR)^G` is an isomorphism.

## References

* [Stacks Project, Tag 0BRF](https://stacks.math.columbia.edu/tag/0BRF)
* [Stacks Project, Tag 0H34](https://stacks.math.columbia.edu/tag/0H34)
* [Stacks Project, Tag 0H36](https://stacks.math.columbia.edu/tag/0H36)
-/

namespace MulSemiringAction

/-- **Stacks 0BRF.** Let `φ : A → B` be a surjective `G`-equivariant ring homomorphism for a
finite group `G`.  Every `b ∈ B^G` is matched by a monic polynomial `P` over `A^G` whose image
under the restriction `A^G → B^G` of `φ` is `(X - C b) ^ |G|`.

The witness is the orbit polynomial `∏_{g ∈ G} (X - C (g • a))` of any lift `a` of `b`: its
coefficients are `G`-invariant, and each factor maps to `X - C b`, since
`φ (g • a) = g • b = b`. -/
@[stacks 0BRF]
theorem exists_monic_map_eq_X_sub_C_pow_card
    {G : Type*} [Group G] [Finite G]
    {A B : Type*} [CommRing A] [CommRing B]
    [MulSemiringAction G A] [MulSemiringAction G B]
    (φ : A →+*[G] B) (hφ : Function.Surjective φ)
    (b : FixedPoints.subring B G) :
    ∃ P : Polynomial (FixedPoints.subring A G), P.Monic ∧
      Polynomial.map
          ((φ : A →+* B).restrict (FixedPoints.subring A G) (FixedPoints.subring B G)
            (by
              intro a ha g
              change g • φ a = φ a
              rw [← map_smul φ, ha g])) P =
        (Polynomial.X - Polynomial.C b) ^ Nat.card G := by
  classical
  have := Fintype.ofFinite G
  obtain ⟨a, ha⟩ := hφ b
  let Q : Polynomial A := ∏ g : G, g • (Polynomial.X - Polynomial.C a)
  have hQ (g : G) : g • Q = Q := Finset.smul_prod_perm (Polynomial.X - Polynomial.C a) g
  have hcoeff : (↑Q.coeffs : Set A) ⊆ FixedPoints.subring A G := by
    intro c hc g
    obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hc
    rw [← Polynomial.coeff_smul, hQ]
  refine ⟨Q.toSubring (FixedPoints.subring A G) hcoeff, ?_, ?_⟩
  · rw [Polynomial.monic_toSubring]
    dsimp only [Q]
    refine Polynomial.monic_prod_of_monic _ _ fun g _ ↦ ?_
    rw [smul_sub, Polynomial.smul_X, Polynomial.smul_C]
    exact Polynomial.monic_X_sub_C (g • a)
  · apply Polynomial.map_injective _ (FixedPoints.subring B G).subtype_injective
    simp only [Polynomial.map_map]
    rw [show
      (Subring.subtype (FixedPoints.subring B G)).comp
          ((φ : A →+* B).restrict (FixedPoints.subring A G) (FixedPoints.subring B G) _) =
        (φ : A →+* B).comp (Subring.subtype (FixedPoints.subring A G)) by ext; rfl]
    rw [← Polynomial.map_map, Polynomial.map_toSubring]
    simp only [Q, smul_sub, Polynomial.smul_X, Polynomial.smul_C, Polynomial.map_prod,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.map_pow]
    have hf (g : G) : (φ : A →+* B) (g • a) = b := by
      show φ (g • a) = b
      rw [φ.map_smul, ha, b.property g]
    rw [Finset.prod_congr rfl (fun g _ ↦ by rw [hf g]), Finset.prod_const, Finset.card_univ,
      Nat.card_eq_fintype_card]
    rfl

end MulSemiringAction

namespace Stacks.Invariant.QuotientComparison

/-- **Stacks 0H36.** If the order of the finite group `G` acting on `R` is invertible in `R`,
the canonical comparison map `Φ : R^G / J → (R / JR)^G` is an isomorphism.

Injectivity: for `a ∈ ker Φ` the identity `(X - C a) ^ n = X ^ n` of
`X_sub_C_pow_eq_X_pow_of_mem_ker` has vanishing coefficient in degree `n - 1`, i.e. `n • a = 0`,
and `n` is invertible.  Surjectivity: `n⁻¹ ∑_{g ∈ G} g • r` is an invariant lift of any
invariant class `r̄`. -/
@[stacks 0H36]
theorem invariantComparison_bijective_of_isUnit_card
    {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G] [MulSemiringAction G R]
    (J : Ideal (FixedPoints.subring R G)) (hG : IsUnit (Fintype.card G : R)) :
    Function.Bijective (invariantComparison J) := by
  classical
  let c : R := ↑hG.unit⁻¹
  have hnc : (Fintype.card G : R) * c = 1 := hG.mul_val_inv
  have hcn : c * (Fintype.card G : R) = 1 := hG.val_inv_mul
  have hc : ∀ g : G, g • c = c := by
    intro g
    apply hG.mul_right_cancel
    have hg := congrArg (fun z ↦ g • z) hcn
    rw [smul_mul'] at hg
    have hnfix : g • (Fintype.card G : R) = (Fintype.card G : R) :=
      map_natCast (MulSemiringAction.toRingHom G R g) _
    rw [hnfix, smul_one] at hg
    rwa [hcn]
  let d : FixedPoints.subring R G := ⟨c, hc⟩
  have hnd : (Fintype.card G : FixedPoints.subring R G) * d = 1 := Subtype.ext hnc
  have hn_unit : IsUnit (Fintype.card G : FixedPoints.subring R G) :=
    IsUnit.of_mul_eq_one d hnd
  have hnq_unit : IsUnit (Fintype.card G : (FixedPoints.subring R G) ⧸ J) := by
    simpa using hn_unit.map (Ideal.Quotient.mk J)
  constructor
  · intro a b hab
    rw [← sub_eq_zero]
    apply hnq_unit.mul_left_cancel
    have hk : a - b ∈ RingHom.ker (invariantComparison J) := by
      rw [RingHom.mem_ker, map_sub, hab, sub_self]
    have hp := congrArg (fun p : Polynomial ((FixedPoints.subring R G) ⧸ J) ↦
        p.coeff (Fintype.card G - 1))
      (X_sub_C_pow_eq_X_pow_of_mem_ker J (a - b) hk)
    have hl : ((Polynomial.X - Polynomial.C (a - b)) ^ Fintype.card G).coeff
        (Fintype.card G - 1) = -∑ _ : G, (a - b) := by
      simpa only [Finset.prod_const, Finset.card_univ] using
        (Polynomial.prod_X_sub_C_coeff_card_pred Finset.univ (fun _ ↦ a - b)
          Fintype.card_pos)
    have hr : ((Polynomial.X : Polynomial ((FixedPoints.subring R G) ⧸ J)) ^
        Fintype.card G).coeff (Fintype.card G - 1) = 0 := by
      rw [Polynomial.coeff_X_pow]
      split
      · have := Fintype.card_pos (α := G)
        omega
      · rfl
    rw [hl, hr] at hp
    have hp' := neg_eq_zero.mp hp
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at hp'
    simpa using hp'
  · intro b
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (b : R ⧸ JRideal J)
    let x : FixedPoints.subring R G :=
      ⟨c * ∑ g : G, g • r, fun h ↦ by
        rw [smul_mul', hc]
        congr 1
        rw [Finset.smul_sum, ← (Equiv.mulLeft h).sum_comp Finset.univ (fun g : G ↦ g • r)]
        · simp only [Equiv.coe_mulLeft, mul_smul]
        · simp⟩
    refine ⟨Ideal.Quotient.mk J x, Subtype.ext ?_⟩
    rw [invariantComparison, Ideal.Quotient.lift_mk, toFixedQuotJR_apply]
    show Ideal.Quotient.mk (JRideal J) (c * ∑ g : G, g • r) = b
    rw [map_mul, map_sum]
    have hfix (g : G) : g • (b : R ⧸ JRideal J) = b := b.2 g
    simp_rw [← quotSmul_mk, hr, hfix]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul (R := R ⧸ JRideal J),
      smul_eq_mul, ← map_natCast (Ideal.Quotient.mk (JRideal J)),
      ← mul_assoc, ← map_mul (Ideal.Quotient.mk (JRideal J)), hcn, map_one, one_mul]

end Stacks.Invariant.QuotientComparison
