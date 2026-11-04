module

public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.TwistedGeneral
public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.PointComparison
public import StacksFrontier.NumberTheory.BombieriStepanov.GaloisClosure
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# The lower bound of Bombieri's proof of the Riemann hypothesis for curves

Let `K/F₀` be a finite separable extension of the rational function field `F₀ = k(x)` over a
finite field `k` with `q` elements, and let `B_K` be the integral closure of `k[x]` in `K`. Then
the number `M_m` of Frobenius-fixed points `B_K → Ω` over `k` satisfies

`q ^ m ≤ M_m + C · √q ^ m`

for `m` beyond a bound along a progression.

Let `L` be the Galois closure of `K/F₀` with group `G`, `B` the integral closure of `k[x]` in `L`,
`E` the field of constants of `L`, `G'` the elements of `G` fixing `E` and `H` the group of `L/K`.
The twisted counts `N_σ` of the points of `B` over a fixed embedding of `E` satisfy
`∑_{σ ∈ G'} N_σ = |G'| q^m` (`Stacks.BombieriStepanov.sum_twistedCount_eq`),
`∑_{σ ∈ H ∩ G'} N_σ ≤ |H ∩ G'| M_m` (`Stacks.BombieriStepanov.sum_twistedCount_le`), and
`N_σ ≤ q^m + c √q^m` (`Stacks.BombieriStepanov.exists_ncard_twisted_le_of_isIntegral`). Hence
`|H ∩ G'| (q^m - M_m) ≤ (|G'| - |H ∩ G'|) c √q^m`.

## Main results

* `Stacks.BombieriStepanov.exists_lower_bound_of_isSeparable`
-/

@[expose] public noncomputable section

open AlgebraicGeometry Polynomial

universe u

namespace Stacks.BombieriStepanov

/-- Elements of a field fixed by the `pr ^ n`-th power map form a finite set, for `n ≠ 0`. -/
private theorem finite_setOf_pow_prime_pow {Ω : Type*} [Field Ω] (pr : ℕ) [Fact pr.Prime] {n : ℕ}
    (hn : n ≠ 0) : {a : Ω | a ^ (pr ^ n) = a}.Finite :=
  (setOf_pow_eq_self_finite_ncard_le (Nat.one_lt_pow hn (Fact.out : pr.Prime).one_lt)).1

/-- Two ring homomorphisms into a field agreeing on `R`, with finite residue ring, differ by an
element of a finite group `G` acting on `B` with invariants `R`. -/
private theorem exists_smul_eq_of_comp_eq {R B Ω : Type*} [CommRing R] [CommRing B] [Field Ω]
    [Algebra R B] (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G R B]
    [Algebra.IsInvariant R B G] (φ φ' : B →+* Ω)
    (hagree : φ.comp (algebraMap R B) = φ'.comp (algebraMap R B))
    (hfin : Finite (B ⧸ RingHom.ker φ)) : ∃ g : G, ∀ b, φ' b = φ (g • b) := by
  let : Algebra R Ω := (φ.comp (algebraMap R B)).toAlgebra
  let a : B →ₐ[R] Ω := { φ with commutes' := fun _ => rfl }
  have : Finite (B ⧸ RingHom.ker a) := hfin
  exact exists_smul_eq_of_algHom G a
    { φ' with commutes' := fun r => (congrArg (fun F : R →+* Ω => F r) hagree).symm }

/-- **The first counting identity, over `k[x]`.** For a finite group `G` acting on a domain `B`
finite over `k[x]` with invariants `k[x]`, and the field `E ⊆ B` of constants, the twisted counts
of the elements of `G` fixing `E` add up to `|G'| · Q`, for `Q = p ^ n` a power of `#E`. -/
theorem sum_twistedCount_eq_card_mul {k : Type u} [Field k] [Finite k] {B : Type u} [CommRing B]
    [IsDomain B] [Algebra k[X] B] [Module.Finite k[X] B]
    (hinjB : Function.Injective (algebraMap k[X] B)) {G : Type*} [Group G] [Finite G]
    [MulSemiringAction G B] [SMulCommClass G k[X] B] [Algebra.IsInvariant k[X] B G]
    {E : Type u} [Field E] [Finite E] [Algebra k E] [Algebra.IsAlgebraic k E] [Algebra E B]
    [Algebra k B] [IsScalarTower k E B] [IsScalarTower k k[X] B]
    {Ω : Type*} [Field Ω] [IsAlgClosed Ω] (pr : ℕ) [Fact pr.Prime] [CharP Ω pr] (ι : E →+* Ω)
    {n : ℕ} (hn : n ≠ 0) (hQE : ∀ e : E, e ^ (pr ^ n) = e) [Fintype (constantFixing B E G)] :
    ∑ σ : constantFixing B E G, twistedCount B ι (pr ^ n) (σ : G) =
      Fintype.card (constantFixing B E G) * pr ^ n := by
  have := Fintype.ofFinite E
  set xB : B := algebraMap k[X] B X
  let : Algebra E[X] B := (Polynomial.aeval xB : E[X] →ₐ[E] B).toRingHom.toAlgebra
  have : IsScalarTower E E[X] B := IsScalarTower.of_algebraMap_eq fun c => by
    show algebraMap E B c = Polynomial.aeval xB (Polynomial.C c)
    rw [Polynomial.aeval_C]
  have hcompX : (algebraMap E[X] B).comp (Polynomial.mapRingHom (algebraMap k E)) =
      algebraMap k[X] B := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · rw [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C]
      show Polynomial.aeval xB (Polynomial.C (algebraMap k E c)) = _
      rw [Polynomial.aeval_C, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply k k[X] B, Polynomial.algebraMap_eq]
    · rw [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X]
      show Polynomial.aeval xB Polynomial.X = xB
      rw [Polynomial.aeval_X]
  have hcomp : ∀ r : k[X], algebraMap E[X] B (Polynomial.map (algebraMap k E) r) =
      algebraMap k[X] B r := fun r => congrArg (fun F : k[X] →+* B => F r) hcompX
  have : Algebra.IsIntegral k[X] B := Algebra.IsIntegral.of_finite k[X] B
  have : Algebra.IsIntegral E[X] B := ⟨fun b => by
    simpa using IsIntegral.map_of_comp_eq (Polynomial.mapRingHom (algebraMap k E)) (RingHom.id B)
      (hcompX.trans (RingHom.id_comp _).symm) (Algebra.IsIntegral.isIntegral (R := k[X]) b)⟩
  have hinjE : Function.Injective (algebraMap E[X] B) := by
    have htk : Transcendental k xB := by
      rw [transcendental_iff_injective]
      have : (Polynomial.aeval xB : k[X] →ₐ[k] B) = IsScalarTower.toAlgHom k k[X] B :=
        Polynomial.algHom_ext (by simp [xB])
      rw [this]
      exact hinjB
    have htE : Transcendental E xB := fun h =>
      htk (IsAlgebraic.restrictScalars (R := k) (S := E) (A := B) h)
    exact transcendental_iff_injective.1 htE
  have hRfin := finite_setOf_pow_prime_pow (Ω := Ω) pr hn
  refine sum_twistedCount_eq pr n hn hQE FiniteField.pow_card
    (fun b hb => exists_algebraMap_eq_of_pow_eq b hb) hinjE
    (fun g => by
      show g • Polynomial.aeval xB (Polynomial.X : E[X]) = Polynomial.aeval xB Polynomial.X
      rw [Polynomial.aeval_X]
      exact smul_algebraMap g (Polynomial.X : k[X])) (fun φ φ' hfix hagree => ?_)
  have hagree' : φ.comp (algebraMap k[X] B) = φ'.comp (algebraMap k[X] B) :=
    RingHom.ext fun r => by
      have := congrArg (fun F : E[X] →+* Ω => F (Polynomial.map (algebraMap k E) r)) hagree
      simpa only [RingHom.comp_apply, hcomp] using this
  exact exists_smul_eq_of_comp_eq G φ φ' hagree'
    (finite_quotient_ker (R := k[X]) φ (hRfin.subset (by
      rintro _ ⟨r, rfl⟩
      have := hfix (Polynomial.map (algebraMap k E) r)
      simp only [hcomp] at this
      exact this)))

/-- **The second counting identity, for a subgroup with invariants `B_H`.** -/
theorem sum_twistedCount_le_of_invariant {k : Type u} [Field k] {B : Type u} [CommRing B]
    [IsDomain B] [Algebra k[X] B] [Module.Finite k[X] B] {G : Type*} [Group G] [Finite G]
    [MulSemiringAction G B] {E : Type u} [Field E] [Finite E] [Algebra k E] [Algebra E B]
    [Algebra k B] [IsScalarTower k E B] {BH : Type*} [CommRing BH] [Algebra k BH] [Algebra BH B]
    [IsScalarTower k BH B] [Algebra k[X] BH] [IsScalarTower k[X] BH B] (H : Subgroup G)
    (hH : ∀ h ∈ H, ∀ c : BH, h • algebraMap BH B c = algebraMap BH B c)
    (hinv : ∀ b : B, (∀ h ∈ H, h • b = b) → ∃ c : BH, algebraMap BH B c = b)
    {Ω : Type*} [Field Ω] (pr : ℕ) [Fact pr.Prime] [CharP Ω pr] (ι : E →+* Ω) {n : ℕ}
    (hn : n ≠ 0) (hQE : ∀ e : E, e ^ (pr ^ n) = e)
    (hD : {ψ : PointsOver BH (ι.comp (algebraMap k E)) | ∀ c, ψ.1 c ^ (pr ^ n) = ψ.1 c}.Finite)
    [Fintype (H ⊓ constantFixing B E G : Subgroup G)] :
    ∑ σ : (H ⊓ constantFixing B E G : Subgroup G), twistedCount B ι (pr ^ n) (σ : G) ≤
      Fintype.card (H ⊓ constantFixing B E G : Subgroup G) *
        {ψ : PointsOver BH (ι.comp (algebraMap k E)) | ∀ c, ψ.1 c ^ (pr ^ n) = ψ.1 c}.ncard := by
  have := Fintype.ofFinite E
  have hRfin := finite_setOf_pow_prime_pow (Ω := Ω) pr hn
  have : SMulCommClass H BH B := ⟨fun h c b => by
    rw [Algebra.smul_def, Algebra.smul_def, Subgroup.smul_def, Subgroup.smul_def, smul_mul',
      hH h.1 h.2]⟩
  have : Algebra.IsInvariant BH B H := ⟨fun b hb => hinv b fun h hh => hb ⟨h, hh⟩⟩
  refine sum_twistedCount_le pr n hQE FiniteField.pow_card
    (fun b hb => exists_algebraMap_eq_of_pow_eq b hb) H hH (fun φ φ' hfix hagree => ?_) hD
  obtain ⟨g, hg⟩ := exists_smul_eq_of_comp_eq H φ φ' hagree
    (finite_quotient_ker (R := k[X]) φ (hRfin.subset (by
      rintro _ ⟨r, rfl⟩
      have := hfix (algebraMap k[X] BH r)
      rwa [← IsScalarTower.algebraMap_apply] at this)))
  exact ⟨g, g.2, hg⟩

/-- **The arithmetic of the lower bound.** If the counts `T σ` over a finite set add up to
`|G'| Q`, those over a nonempty subset `S` add up to at most `|S| M`, and each is at most
`Q + U`, then `Q ≤ M + |G'| U`. -/
theorem le_add_of_sum_eq {G' : Type*} [Fintype G'] (T : G' → ℕ) (S : Finset G') (Q M U : ℕ)
    (hsum : ∑ σ, T σ = Fintype.card G' * Q) (hS : ∑ σ ∈ S, T σ ≤ S.card * M)
    (hpos : S.Nonempty) (hU : ∀ σ, T σ ≤ Q + U) :
    (Q : ℤ) ≤ M + Fintype.card G' * U := by
  classical
  have hsplit := Finset.sum_add_sum_compl S T
  have hcompl : ∑ σ ∈ Sᶜ, T σ ≤ Sᶜ.card * (Q + U) := by
    rw [← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun σ _ => hU σ
  have hcard : S.card + Sᶜ.card = Fintype.card G' := Finset.card_add_card_compl S
  have hSc : 0 < S.card := hpos.card_pos
  have h1 : (Fintype.card G' : ℤ) * Q ≤ S.card * M + Sᶜ.card * (Q + U) := by
    have := congrArg (fun z : ℕ => (z : ℤ)) (hsplit.trans hsum)
    push_cast at this
    have h2 : ((∑ σ ∈ S, T σ : ℕ) : ℤ) ≤ S.card * M := by exact_mod_cast hS
    have h3 : ((∑ σ ∈ Sᶜ, T σ : ℕ) : ℤ) ≤ Sᶜ.card * (Q + U) := by exact_mod_cast hcompl
    push_cast at h2 h3
    linarith
  have hcardZ : (S.card : ℤ) + Sᶜ.card = Fintype.card G' := mod_cast hcard
  have h4 : (S.card : ℤ) * (Q - M) ≤ Fintype.card G' * U := by
    have hU0 : (0 : ℤ) ≤ U := by positivity
    have hSc' : (0 : ℤ) ≤ Sᶜ.card := by positivity
    nlinarith
  by_cases hQM : (Q : ℤ) ≤ M
  · have : (0 : ℤ) ≤ Fintype.card G' * U := by positivity
    linarith
  · rw [not_le] at hQM
    have hSc1 : (1 : ℤ) ≤ S.card := by exact_mod_cast hSc
    nlinarith

/-- Summing over `H ⊓ G'` is summing over the elements of `G'` lying in `H`, and the two index
sets have the same cardinality. -/
theorem sum_inf_eq_sum_filter {G : Type*} [Group G] (H G' : Subgroup G) [Fintype G']
    [Fintype (H ⊓ G' : Subgroup G)] [DecidablePred (fun σ : G' => (σ : G) ∈ H)] (T : G → ℕ) :
    ∑ σ : (H ⊓ G' : Subgroup G), T σ =
      ∑ σ ∈ (Finset.univ.filter fun σ : G' => (σ : G) ∈ H), T σ ∧
    Fintype.card (H ⊓ G' : Subgroup G) =
      (Finset.univ.filter fun σ : G' => (σ : G) ∈ H).card := by
  let e : (H ⊓ G' : Subgroup G) ≃ {σ : G' // (σ : G) ∈ H} :=
    { toFun := fun σ => ⟨⟨σ, σ.2.2⟩, σ.2.1⟩
      invFun := fun σ => ⟨σ.1, σ.2, σ.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  constructor
  · rw [Finset.sum_subtype (Finset.univ.filter fun σ : G' => (σ : G) ∈ H)
      (p := fun σ : G' => (σ : G) ∈ H) (fun x => by simp) (fun σ : G' => T σ)]
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  · rw [Fintype.card_congr e, Fintype.card_subtype]

/-- **The lower bound from the three estimates.** If the counts over `G'` add up to `|G'| Q`,
those over `H ⊓ G'` add up to at most `|H ⊓ G'| N`, and each is at most `Q + U`, then
`Q ≤ N + |G'| U`. -/
private theorem le_add_of_sum_eq_inf {G : Type*} [Group G] (H G' : Subgroup G) [Fintype G']
    [Fintype (H ⊓ G' : Subgroup G)] (T : G → ℕ) (Q N U : ℕ)
    (hsum : ∑ σ : G', T σ = Fintype.card G' * Q)
    (hle : ∑ σ : (H ⊓ G' : Subgroup G), T σ ≤ Fintype.card (H ⊓ G' : Subgroup G) * N)
    (hU : ∀ σ : G', T σ ≤ Q + U) : (Q : ℤ) ≤ N + Fintype.card G' * U := by
  classical
  obtain ⟨hsum', hcard⟩ := sum_inf_eq_sum_filter H G' T
  exact le_add_of_sum_eq (fun σ : G' => T σ)
    (Finset.univ.filter fun σ : G' => (σ : G) ∈ H) Q N U hsum
    (by rwa [← hsum', ← hcard]) ⟨1, by simp [H.one_mem]⟩ hU

/-- An element of a finite group has order dividing the group order, so iterating the ring
automorphism it induces `Nat.card G` times is the identity. -/
private theorem iterate_toRingEquiv_eq {G B : Type*} [Group G] [Finite G] [Semiring B]
    [MulSemiringAction G B] (σ : G) (b : B) :
    (⇑(MulSemiringAction.toRingEquiv G B σ))^[Nat.card G] b = b := by
  have h : (⇑(MulSemiringAction.toRingEquiv G B σ))^[Nat.card G] b = (σ ^ Nat.card G) • b := by
    show (fun b : B => σ • b)^[Nat.card G] b = _
    rw [smul_iterate]
  rw [h, pow_card_eq_one', one_smul]

/-- A field inside a finite type algebra over a finite field is finite: it embeds into the residue
field at a maximal ideal, which is a finite module over the base. -/
private theorem finite_subfield_of_finiteType {k : Type u} [Field k] [Finite k] {B : Type u}
    [CommRing B] [Nontrivial B] [Algebra k B] [Algebra.FiniteType k B] (E : Type u) [Field E]
    [Algebra E B] : Finite E := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal B
  let : Field (B ⧸ P) := Ideal.Quotient.field P
  have : Module.Finite k (B ⧸ P) := finite_of_finite_type_of_isJacobsonRing k (B ⧸ P)
  have : Finite (B ⧸ P) := Module.finite_of_finite k
  exact Finite.of_injective _ ((Ideal.Quotient.mk P).comp (algebraMap E B)).injective

/-- The map from a ring to a ring between its fraction field and a further field extension is
injective, the composite into the extension being injective. -/
private theorem injective_algebraMap_of_isScalarTower {R Kf Lf B : Type*} [CommRing R] [Field Kf]
    [Field Lf] [CommRing B] [Algebra R Kf] [IsFractionRing R Kf] [Algebra Kf Lf] [Algebra R Lf]
    [IsScalarTower R Kf Lf] [Algebra R B] [Algebra B Lf] [IsScalarTower R B Lf] :
    Function.Injective (algebraMap R B) := by
  intro a b h
  have h' : algebraMap R Lf a = algebraMap R Lf b := by
    rw [IsScalarTower.algebraMap_apply R B Lf, IsScalarTower.algebraMap_apply R B Lf, h]
  rw [IsScalarTower.algebraMap_apply R Kf Lf, IsScalarTower.algebraMap_apply R Kf Lf] at h'
  exact IsFractionRing.injective R Kf ((algebraMap Kf Lf).injective h')

/-- The progression passes the Stepanov threshold: if `2 (γ² + 3γ + 2) ≤ 2 a nE j` and `f` is
positive then `γ² + 3γ + 1 < pr ^ (f (a nE j))` for every `pr > 1`. -/
private theorem lt_pow_mul_of_le {pr γ f a nE j : ℕ} (hpr : 1 < pr) (hf : 1 ≤ f)
    (hm : 2 * (γ ^ 2 + 3 * γ + 2) ≤ 2 * a * nE * j) :
    γ ^ 2 + 3 * γ + 1 < pr ^ (f * (a * nE * j)) := by
  have h1' : γ ^ 2 + 3 * γ + 2 ≤ f * (a * nE * j) := by nlinarith
  exact lt_of_lt_of_le (by omega) (Nat.lt_pow_self hpr).le

/-- Every element of a finite field with `pr ^ nE` elements is fixed by raising to the
`pr ^ (f (2 a nE j))` power, that exponent being a power of the cardinality. -/
private theorem pow_pow_mul_card_eq_self {E : Type*} [Field E] [Fintype E] {pr nE : ℕ}
    (hqE : Fintype.card E = pr ^ nE) (f a j : ℕ) (c : E) :
    c ^ (pr ^ (f * (2 * a * nE * j))) = c := by
  have h : pr ^ (f * (2 * a * nE * j)) = Fintype.card E ^ (f * (2 * a * j)) := by
    rw [hqE, ← pow_mul]
    ring_nf
  rw [h, FiniteField.pow_card_pow]

/-- **The field of constants.** In a field `L` of transcendence degree one over a finite field `k`,
the elements algebraic over `k` form a finite field `E`: the extension `L/E` again has
transcendence degree one, every `E`-integral element of `L` already lies in `E`, and `E` is
contained in any subalgebra `B` of `L` holding the `R`-integral elements. -/
private theorem exists_constantField {k : Type u} [Field k] [Finite k] {R : Type u} [CommRing R]
    {L : Type u} [Field L] [Algebra k L] [Algebra R L] [Algebra k R] [IsScalarTower k R L]
    (B : Subalgebra R L) [IsDomain B] [Algebra k B] [IsScalarTower k B L]
    [Algebra.FiniteType k B] [IsFractionRing B L] (hB : ∀ c : L, IsIntegral R c → c ∈ B)
    (htrL : Algebra.trdeg k L = 1) :
    ∃ (E : Type u) (_ : Field E) (_ : Fintype E) (_ : Algebra k E) (_ : Algebra E L)
      (_ : Algebra E B) (_ : IsScalarTower k E L) (_ : IsScalarTower E B L)
      (_ : IsScalarTower k E B) (_ : Algebra.IsIntegral k E) (_ : Algebra.FiniteType E B)
      (_ : Algebra.EssFiniteType E L),
      (∀ c : L, IsIntegral E c → c ∈ (algebraMap E L).range) ∧ Algebra.trdeg E L = 1 := by
  obtain ⟨E, _, _, jE, hjE⟩ : ∃ (E : Type u) (_ : Field E) (_ : Algebra k E) (j : E →ₐ[k] L),
      ∀ c : L, c ∈ Set.range j ↔ IsIntegral k c :=
    ⟨algebraicClosure k L, inferInstance, inferInstance, (algebraicClosure k L).val,
      fun c => ⟨by rintro ⟨e, rfl⟩; exact e.2, fun h => ⟨⟨c, h⟩, rfl⟩⟩⟩
  let : Algebra E L := (jE : E →+* L).toAlgebra
  have : IsScalarTower k E L := IsScalarTower.of_algebraMap_eq fun c => (jE.commutes c).symm
  have hEB : ∀ e : E, algebraMap E L e ∈ B := fun e =>
    hB _ ((hjE _).1 ⟨e, rfl⟩).tower_top
  let : Algebra E B := ((algebraMap E L).codRestrict B.toSubring hEB).toAlgebra
  have : IsScalarTower E B L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower k E B := IsScalarTower.of_algebraMap_eq fun c => Subtype.ext (by
    have h1 : ((algebraMap k B c : B) : L) = algebraMap k L c :=
      (IsScalarTower.algebraMap_apply k B L c).symm
    have h2 : ((algebraMap E B (algebraMap k E c) : B) : L) =
        algebraMap E L (algebraMap k E c) := rfl
    rw [h1, h2, ← IsScalarTower.algebraMap_apply])
  have : Algebra.FiniteType E B := Algebra.FiniteType.of_restrictScalars_finiteType k E B
  have : Algebra.IsIntegral k E := ⟨fun e =>
    (isIntegral_algHom_iff (jE : E →ₐ[k] L) jE.toRingHom.injective).1 ((hjE (jE e)).1 ⟨e, rfl⟩)⟩
  have : Finite E := finite_subfield_of_finiteType (k := k) (B := B) E
  let : Fintype E := Fintype.ofFinite _
  have : Algebra.EssFiniteType B L := Algebra.EssFiniteType.of_isLocalization L (nonZeroDivisors B)
  have : Algebra.EssFiniteType E L := Algebra.EssFiniteType.comp E B L
  refine ⟨E, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ?_, ?_⟩
  · intro c hc
    exact (hjE c).2 (isIntegral_trans (R := k) c hc)
  have h := trdeg_add_eq k E (A := L)
  have : Algebra.IsAlgebraic k E := Algebra.IsIntegral.isAlgebraic
  rwa [_root_.trdeg_eq_zero (R := k) (A := E), zero_add, htrL] at h

/-- **The lower bound, for the integral closure of `k[x]` in a separable function field.** -/
theorem exists_lower_bound_of_isSeparable {k : Type u} [Field k] [Fintype k] (pr : ℕ)
    [Fact pr.Prime] [CharP k pr] {F₀ : Type u} [Field F₀] [Algebra k[X] F₀]
    [IsFractionRing k[X] F₀] [Algebra k F₀] [IsScalarTower k k[X] F₀]
    (htr₀ : Algebra.trdeg k F₀ = 1)
    {K : Type u} [Field K] [Algebra F₀ K] [FiniteDimensional F₀ K] [Algebra.IsSeparable F₀ K]
    [Algebra k K] [IsScalarTower k F₀ K] [Algebra k[X] K] [IsScalarTower k[X] F₀ K]
    [IsScalarTower k k[X] K]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (ι₀ : k →+* Ω) (M : ℕ → ℕ)
    (hM : ∀ m : ℕ, m ≠ 0 →
      {ψ : PointsOver (integralClosure k[X] K) ι₀ |
        ∀ a, ψ.1 a ^ (Fintype.card k ^ m) = ψ.1 a}.Finite ∧
      {ψ : PointsOver (integralClosure k[X] K) ι₀ |
        ∀ a, ψ.1 a ^ (Fintype.card k ^ m) = ψ.1 a}.ncard ≤ M m) :
    ∃ (C : ℕ) (m₀ d f : ℕ), d ≠ 0 ∧ 2 ∣ d ∧ Fintype.card k = pr ^ f ∧ ∀ m : ℕ, m₀ ≤ m → d ∣ m →
      (Fintype.card k ^ m : ℤ) ≤ M m + C * pr ^ (f * m / 2) := by
  classical
  -- the Galois closure `L` of `K/F₀`, as an opaque field
  obtain ⟨L, _, _, _, _, _, _⟩ := exists_galoisClosure F₀ K
  let : Algebra k[X] L := ((algebraMap F₀ L).comp (algebraMap k[X] F₀)).toAlgebra
  have : IsScalarTower k[X] F₀ L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra k L := ((algebraMap F₀ L).comp (algebraMap k F₀)).toAlgebra
  have : IsScalarTower k F₀ L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower k k[X] L := IsScalarTower.of_algebraMap_eq fun c => by
    show algebraMap F₀ L (algebraMap k F₀ c) = algebraMap F₀ L (algebraMap k[X] F₀ _)
    rw [← IsScalarTower.algebraMap_apply k k[X] F₀]
  -- the Galois group and the integral closure `B`
  set G := L ≃ₐ[F₀] L
  have : SMulCommClass G k[X] L := SMulCommClass.symm _ _ _
  set B := integralClosure k[X] L
  have : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension F₀ L
  have : IsGaloisGroup G k[X] B := IsGaloisGroup.of_isFractionRing G k[X] B F₀ L
  have : Algebra.IsInvariant k[X] B G := IsGaloisGroup.isInvariant
  have : IsDedekindDomain B := integralClosure.isDedekindDomain k[X] F₀ L
  have : Module.Finite k[X] B := IsIntegralClosure.finite k[X] F₀ L B
  let : Algebra k B := ((algebraMap k[X] B).comp (algebraMap k k[X])).toAlgebra
  have : IsScalarTower k k[X] B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType k B := Algebra.FiniteType.trans (S := k[X]) inferInstance inferInstance
  have : IsScalarTower k B L := IsScalarTower.of_algebraMap_eq fun c => by
    show algebraMap k L c = algebraMap k[X] L (algebraMap k k[X] c)
    rw [← IsScalarTower.algebraMap_apply]
  have htrL : Algebra.trdeg k L = 1 := by
    have h := trdeg_add_eq k F₀ (A := L)
    have : Algebra.IsAlgebraic F₀ L := Algebra.IsIntegral.isAlgebraic
    rwa [_root_.trdeg_eq_zero (R := F₀) (A := L), add_zero, htr₀, eq_comm] at h
  -- the field of constants `E` of `L`, as an opaque type
  obtain ⟨E, _, _, _, _, _, _, _, _, _, _, _, hEint, htrE⟩ :=
    exists_constantField (R := k[X]) B (fun _ hc => hc) htrL
  -- an embedding of the constants
  let : Algebra k Ω := ι₀.toAlgebra
  have : Algebra.IsAlgebraic k E := Algebra.IsIntegral.isAlgebraic
  let ιA : E →ₐ[k] Ω := IsAlgClosed.lift
  set ι : E →+* Ω := (ιA : E →+* Ω)
  have hι : ι.comp (algebraMap k E) = ι₀ := RingHom.ext ιA.commutes
  have : CharP E pr := charP_of_injective_algebraMap (algebraMap k E).injective pr
  -- the twisted Stepanov bound for each element fixing the constants
  set G' := constantFixing B E G
  have hpartB : ∀ σ : G', ∃ γ a : ℕ, 0 < a ∧ ∀ e : ℕ, a ∣ e → γ ^ 2 + 3 * γ + 1 < pr ^ e →
      twistedCount B ι (pr ^ e * pr ^ e) (σ : G) ≤ pr ^ e * pr ^ e + (2 * γ + 1) * pr ^ e := by
    intro σ
    exact exists_ncard_twisted_le_of_isIntegral pr htrE hEint
      (MulSemiringAction.toRingEquiv G B (σ : G)) σ.2 Nat.card_pos.ne'
      (iterate_toRingEquiv_eq (σ : G)) ι
  choose γσ aσ haσ hγσ using hpartB
  set γ := Finset.univ.sup γσ
  set a := ∏ σ, aσ σ
  have ha0 : 0 < a := Finset.prod_pos fun σ _ => haσ σ
  have hbound : ∀ σ : G', ∀ e : ℕ, a ∣ e → γ ^ 2 + 3 * γ + 1 < pr ^ e →
      twistedCount B ι (pr ^ e * pr ^ e) (σ : G) ≤ pr ^ e * pr ^ e + (2 * γ + 1) * pr ^ e := by
    intro σ e hae he
    have hle : γσ σ ≤ γ := Finset.le_sup (Finset.mem_univ σ)
    have h1 := hγσ σ e ((Finset.dvd_prod_of_mem aσ (Finset.mem_univ σ)).trans hae)
      (lt_of_le_of_lt (by nlinarith) he)
    exact h1.trans (by nlinarith)
  -- the group of `L/K` and its invariants
  have : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k F₀ L, IsScalarTower.algebraMap_apply k F₀ K,
      ← IsScalarTower.algebraMap_apply F₀ K L]
  have : IsScalarTower k[X] K L := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply k[X] F₀ L, IsScalarTower.algebraMap_apply k[X] F₀ K,
      ← IsScalarTower.algebraMap_apply F₀ K L]
  have : CharP Ω pr := charP_of_injective_algebraMap (algebraMap k Ω).injective pr
  set K' : IntermediateField F₀ L := (IsScalarTower.toAlgHom F₀ K L).fieldRange
  set H : Subgroup G := K'.fixingSubgroup
  set BH := integralClosure k[X] K
  have hBHL : ∀ c : BH, IsIntegral k[X] (algebraMap K L c) := fun c =>
    (c.2.map (IsScalarTower.toAlgHom k[X] K L) :)
  let : Algebra BH B := ((algebraMap K L).comp (algebraMap BH K)).codRestrict B.toSubring
    hBHL |>.toAlgebra
  have : IsScalarTower k[X] BH B := IsScalarTower.of_algebraMap_eq fun r => Subtype.ext (by
    show algebraMap k[X] L r = algebraMap K L (algebraMap k[X] K r)
    rw [← IsScalarTower.algebraMap_apply])
  have : IsScalarTower k BH B := IsScalarTower.of_algebraMap_eq fun c => Subtype.ext (by
    have h1 : ((algebraMap k B c : B) : L) = algebraMap k L c :=
      (IsScalarTower.algebraMap_apply k B L c).symm
    rw [h1]
    show algebraMap k L c = algebraMap K L (algebraMap BH K (algebraMap k BH c))
    rw [← IsScalarTower.algebraMap_apply k BH K, ← IsScalarTower.algebraMap_apply])
  have hH : ∀ h ∈ H, ∀ c : BH, h • algebraMap BH B c = algebraMap BH B c := by
    intro h hh c
    refine Subtype.ext ?_
    show h (algebraMap K L c) = algebraMap K L c
    exact (IntermediateField.mem_fixingSubgroup_iff K' h).1 hh _ ⟨c, rfl⟩
  have hinv : ∀ b : B, (∀ h ∈ H, h • b = b) → ∃ c : BH, algebraMap BH B c = b := by
    intro b hb
    have hfix : (b : L) ∈ IntermediateField.fixedField H := by
      rw [IntermediateField.mem_fixedField_iff]
      intro h hh
      exact congrArg Subtype.val (hb h hh)
    rw [IsGalois.fixedField_fixingSubgroup] at hfix
    obtain ⟨c, hc⟩ := hfix
    have hcint : IsIntegral k[X] c := by
      have := b.2
      rw [← hc] at this
      exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom k[X] K L)
        (algebraMap K L).injective).1 this
    exact ⟨⟨c, hcint⟩, Subtype.ext hc⟩
  have hinjB : Function.Injective (algebraMap k[X] B) :=
    injective_algebraMap_of_isScalarTower (Kf := F₀) (Lf := L)
  -- the progression and the constants
  obtain ⟨f, -, hqf⟩ := FiniteField.card k pr
  obtain ⟨nE, -, hqE⟩ := FiniteField.card E pr
  let : Fintype G' := Fintype.ofFinite _
  let : Fintype (H ⊓ G' : Subgroup G) := Fintype.ofFinite _
  refine ⟨Fintype.card G' * (2 * γ + 1), 2 * (γ ^ 2 + 3 * γ + 2), 2 * a * nE, f,
    by positivity, ⟨a * nE, by ring⟩, hqf, fun m hm hdm => ?_⟩
  obtain ⟨j, rfl⟩ := hdm
  have hj : j ≠ 0 := by
    rintro rfl
    simp at hm
  set e := (f : ℕ) * (a * nE * j) with he
  have hfm : (f : ℕ) * (2 * a * nE * j) = e + e := by rw [he]; ring
  have hfm2 : (f : ℕ) * (2 * a * nE * j) / 2 = e := by rw [hfm]; omega
  have hn : (f : ℕ) * (2 * a * nE * j) ≠ 0 := by positivity
  have hQ : Fintype.card k ^ (2 * a * nE * j) = pr ^ ((f : ℕ) * (2 * a * nE * j)) := by
    rw [hqf, ← pow_mul]
  have hQE : ∀ c : E, c ^ (pr ^ ((f : ℕ) * (2 * a * nE * j))) = c :=
    pow_pow_mul_card_eq_self hqE _ _ _
  have hQee : pr ^ e * pr ^ e = pr ^ ((f : ℕ) * (2 * a * nE * j)) := by rw [hfm, pow_add]
  -- the three estimates
  have h1 := sum_twistedCount_eq_card_mul hinjB pr ι hn hQE (G := G)
  have hMm := hM (2 * a * nE * j) (by positivity)
  rw [hQ, ← hι] at hMm
  have h2 := sum_twistedCount_le_of_invariant H hH hinv pr ι hn hQE hMm.1
  have hlarge : γ ^ 2 + 3 * γ + 1 < pr ^ e := by
    rw [he]
    exact lt_pow_mul_of_le (Fact.out : pr.Prime).one_lt f.pos hm
  have h3 : ∀ σ : G', twistedCount B ι (pr ^ ((f : ℕ) * (2 * a * nE * j))) (σ : G) ≤
      pr ^ ((f : ℕ) * (2 * a * nE * j)) + (2 * γ + 1) * pr ^ e := by
    intro σ
    rw [← hQee]
    exact hbound σ e (Dvd.intro_left ((f : ℕ) * (nE * j)) (by rw [he]; ring)) hlarge
  have key := le_add_of_sum_eq_inf H G'
    (fun σ => twistedCount B ι (pr ^ ((f : ℕ) * (2 * a * nE * j))) σ) _ _ _ h1
    (h2.trans (Nat.mul_le_mul_left _ hMm.2)) h3
  have hQZ : ((Fintype.card k : ℤ) ^ (2 * a * nE * j)) =
      ((pr ^ ((f : ℕ) * (2 * a * nE * j)) : ℕ) : ℤ) := by
    rw [← hQ]
    push_cast
    rfl
  rw [hQZ, hfm2]
  push_cast at key ⊢
  linarith

end Stacks.BombieriStepanov

end
