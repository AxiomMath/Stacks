module

public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.TwistedBound
public import StacksFrontier.NumberTheory.BombieriStepanov.PointsLift
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# The twisted Bombieri–Stepanov bound without a rational point

Let `B` be a Dedekind domain of finite type over a finite field `E` whose fraction field `L` has
transcendence degree one over `E`, with `E` algebraically closed in `L`. For a ring automorphism
`σ` of `B` of finite order fixing `E`, the `σ`-twisted points `φ : B → Ω` into an algebraically
closed field number at most `Q + (2γ + 1) √Q` for `Q` an even power of the characteristic, beyond
a bound and along a progression.

`B` need not have a maximal ideal with residue field `E`. Let `E₁ = B / P₀` for some maximal ideal
`P₀`, let `L₁ = L ⊗_E E₁` be the constant field extension
(`Stacks.BombieriStepanov.isGalois_constPoly`) and `B₁` the integral closure of `B` in `L₁`, with
`σ` extended to `σ₁`. Every `σ`-twisted point of `B` lifts to a `σ₁`-twisted point of `B₁` over a
fixed embedding of `E₁`: lift along the integral extension, correct the restriction to `E₁` by
an element of `Gal(L₁/L)` (`Stacks.BombieriStepanov.galoisOfAut`), and compare `φ₁ ∘ σ₁` with
`Frob ∘ φ₁` by uniqueness of lifts (`Stacks.BombieriStepanov.eq_of_comp_algebraMap_eq`). The same
argument applied to `B → B / P₀ = E₁` gives a maximal ideal of `B₁` with residue field `E₁`, so
`Stacks.BombieriStepanov.exists_ncard_twisted_le` applies to `B₁`.

## Main results

* `Stacks.BombieriStepanov.exists_ncard_twisted_le_of_isIntegral`
-/

@[expose] public noncomputable section

open AlgebraicGeometry Polynomial

universe u

namespace Stacks.BombieriStepanov

/-- A Dedekind domain of finite type over a finite field is not a field when its fraction field
has transcendence degree one: a field would be finite over `E`, hence so would its fraction
field, forcing transcendence degree zero. -/
private theorem not_isField_of_trdeg_eq_one {E : Type u} [Field E] [Fintype E] {L : Type u}
    [Field L] [Algebra E L] [Algebra.EssFiniteType E L] (htr : Algebra.trdeg E L = 1)
    {B : Type u} [CommRing B] [IsDedekindDomain B] [Algebra E B] [Algebra.FiniteType E B]
    [Algebra B L] [IsScalarTower E B L] [IsFractionRing B L] : ¬ IsField B := by
  intro hBf
  let : Field B := hBf.toField
  have : Module.Finite E B := finite_of_finite_type_of_isJacobsonRing E B
  have hsurj : Function.Surjective (algebraMap B L) := by
    intro l
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := B) l
    exact ⟨a / b, by rw [map_div₀]⟩
  have : Algebra.IsAlgebraic E L := by
    have : Algebra.IsAlgebraic E B := Algebra.IsIntegral.isAlgebraic
    exact ⟨fun l => by
      obtain ⟨b, rfl⟩ := hsurj l
      rw [← IsScalarTower.toAlgHom_apply E B L]
      exact (Algebra.IsAlgebraic.isAlgebraic b).algHom _⟩
  have := _root_.trdeg_eq_zero (R := E) (A := L)
  rw [htr] at this
  exact one_ne_zero this

/-- An automorphism of the fraction field extending an automorphism `σ` of the base with
`σ ^ N = 1` again satisfies `σ ^ N = 1`, since it is determined by its restriction. -/
private theorem iterate_eq_self_of_isFractionRing {B L : Type*} [CommRing B] [IsDomain B]
    [Field L] [Algebra B L] [IsFractionRing B L] (σ : B ≃+* B) {N : ℕ}
    (hN : ∀ b, (⇑σ)^[N] b = b) (σL : L ≃+* L)
    (hσLB : ∀ b, σL (algebraMap B L b) = algebraMap B L (σ b)) : ∀ l, (⇑σL)^[N] l = l := by
  have h1 : ∀ k b, (⇑σL)^[k] (algebraMap B L b) = algebraMap B L ((⇑σ)^[k] b) := fun k b =>
    (Function.Semiconj.iterate_right (f := algebraMap B L) (fun b => (hσLB b).symm) k b).symm
  have h2 : (σL : L →+* L) ^ N = RingHom.id L :=
    IsLocalization.ringHom_ext (nonZeroDivisors B) (RingHom.ext fun b => by
      simp only [RingHom.comp_apply, RingHom.coe_pow, RingHom.id_apply]
      exact (h1 N b).trans (by rw [hN]))
  intro l
  have := congrArg (fun F : L →+* L => F l) h2
  simpa using this

/-- An automorphism of `AdjoinRoot f` fixing the root and restricting on the coefficients to an
automorphism with `σ ^ N = 1` again satisfies `σ ^ N = 1`. -/
private theorem iterate_eq_self_of_adjoinRoot {L : Type*} [CommRing L] {f : L[X]} (σL : L ≃+* L)
    {N : ℕ} (hσLN : ∀ l, (⇑σL)^[N] l = l) (σ₁ : AdjoinRoot f ≃+* AdjoinRoot f)
    (hof : ∀ l, σ₁ (AdjoinRoot.of f l) = AdjoinRoot.of f (σL l))
    (hroot : σ₁ (AdjoinRoot.root f) = AdjoinRoot.root f) : ∀ x, (⇑σ₁)^[N] x = x := by
  have h1 : ∀ k l, (⇑σ₁)^[k] (AdjoinRoot.of _ l) = AdjoinRoot.of f ((⇑σL)^[k] l) := fun k l =>
    (Function.Semiconj.iterate_right (f := AdjoinRoot.of f) (fun l => (hof l).symm) k l).symm
  have h2 : ∀ k, (⇑σ₁)^[k] (AdjoinRoot.root f) = AdjoinRoot.root _ := fun k =>
    Function.iterate_fixed hroot k
  have h3 : (σ₁ : AdjoinRoot f →+* AdjoinRoot f) ^ N = RingHom.id (AdjoinRoot f) :=
    adjoinRoot_ringHom_ext (fun l => by
      rw [RingHom.coe_pow, RingHom.id_apply]
      exact (h1 N l).trans (by rw [hσLN])) (by rw [RingHom.coe_pow, RingHom.id_apply]; exact h2 N)
  intro x
  have := congrArg (fun F : AdjoinRoot f →+* AdjoinRoot f => F x) h3
  simpa using this

/-- A self-map of a subobject compatible along an injection with a self-map of the ambient object
inherits the relation `τ ^ N = 1` from it. -/
private theorem iterate_eq_self_of_injective {X Y : Type*} {c : X → Y} {τ : X → X} {τ' : Y → Y}
    (hcomm : ∀ x, c (τ x) = τ' (c x)) (hc : Function.Injective c) {N : ℕ}
    (hN : ∀ y, τ'^[N] y = y) (x : X) : τ^[N] x = x := by
  exact hc ((Function.Semiconj.iterate_right hcomm N x).trans (hN (c x)))

/-- A homomorphism whose image lies in a finite set has nonzero kernel as soon as an infinite
ring injects into its source: otherwise the source, and with it that ring, would be finite. -/
private theorem ker_ne_bot_of_range_subset_finite {B B₁ Ω : Type*} [CommRing B] [CommRing B₁]
    [Field Ω] [Algebra B B₁] [Infinite B] (hinjB : Function.Injective (algebraMap B B₁))
    (φ : B₁ →+* Ω) {R : Set Ω} (hRfin : R.Finite) (hmem : ∀ z, φ z ∈ R) :
    RingHom.ker φ ≠ ⊥ := by
  intro h
  have hinj : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot _).2 h
  have : Finite B₁ := by
    refine Finite.of_injective (β := hRfin.toFinset) (fun z => ⟨φ z, ?_⟩) fun a b h => ?_
    · rw [Set.Finite.mem_toFinset]
      exact hmem z
    · exact hinj (congrArg Subtype.val h)
  have : Finite B := Finite.of_injective _ hinjB
  exact not_finite B

/-- **Lifting a point along the constant extension.** A point of `B` over `ι` with maximal kernel
extends to a point of `B₁` over the chosen embedding `ι₁A` of the constants: lift it along the
integral extension, then correct its restriction to the constants by an element of the group
`Γ` of `B₁` over `B`. -/
private theorem exists_pointsOver_comp_eq {E E₁ Ω : Type*} [Field E] [Field E₁] [Fintype E₁]
    [Algebra E E₁] [Field Ω] [IsAlgClosed Ω] [Algebra E Ω] {B B₁ : Type*} [CommRing B]
    [CommRing B₁] [Algebra E B] [Algebra B B₁] [Algebra.IsIntegral B B₁] [Algebra E₁ B₁]
    (Γ : Type*) [Group Γ] [MulSemiringAction Γ B₁] (G : (E₁ →ₐ[E] E₁) → Γ)
    (hΓB : ∀ (g : Γ) (b : B), g • algebraMap B B₁ b = algebraMap B B₁ b)
    (hΓE : ∀ (τ : E₁ →ₐ[E] E₁) (c : E₁), G τ • algebraMap E₁ B₁ c = algebraMap E₁ B₁ (τ c))
    (hEB₁ : ∀ c : E, algebraMap E₁ B₁ (algebraMap E E₁ c) = algebraMap B B₁ (algebraMap E B c))
    (hinjB : Function.Injective (algebraMap B B₁)) (ι : E →+* Ω)
    (hι : ∀ c : E, ι c = algebraMap E Ω c) (ι₁A : E₁ →ₐ[E] Ω) :
    ∀ φ : B →+* Ω, (∀ c, φ (algebraMap E B c) = ι c) → (RingHom.ker φ).IsMaximal →
      ∃ φ₁ : PointsOver B₁ (ι₁A : E₁ →+* Ω), φ₁.1.comp (algebraMap B B₁) = φ := by
  intro φ hφE hφmax
  obtain ⟨φ', hφ'⟩ := exists_comp_algebraMap_eq hinjB φ
  let u : E₁ →ₐ[E] Ω :=
    { (φ'.comp (algebraMap E₁ B₁)) with
      commutes' := fun c => by
        rw [← hι]
        show φ' (algebraMap E₁ B₁ (algebraMap E E₁ c)) = ι c
        rw [hEB₁, ← RingHom.comp_apply, hφ', hφE] }
  obtain ⟨τ, hτ⟩ := exists_algEquiv_comp_eq u ι₁A
  refine ⟨⟨φ'.comp (MulSemiringAction.toRingHom Γ B₁ (G τ.toAlgHom)),
    RingHom.ext fun c => ?_⟩, RingHom.ext fun b => ?_⟩
  · simp only [RingHom.comp_apply, MulSemiringAction.toRingHom_apply, hΓE]
    exact (hτ c).symm
  · simp only [RingHom.comp_apply, MulSemiringAction.toRingHom_apply, hΓB]
    rw [← RingHom.comp_apply, hφ']

/-- **A lifted point takes values in the constants.** If the restriction of a point `φ₁` of `B₁`
to `B` factors through the finite field `E₁`, then `φ₁` itself has values in the image of `E₁`:
composing `φ₁` with the Frobenius of `E₁` restricts to the same point of `B`, and lifts of a
point with finite image are unique. -/
private theorem pow_eq_self_of_comp_eq {E₁ Ω : Type*} [Field E₁] [Fintype E₁] [Field Ω]
    (ι₁ : E₁ →+* Ω) {B B₁ : Type*} [CommRing B] [CommRing B₁] [Algebra B B₁] [Algebra E₁ B₁]
    {pr : ℕ} [Fact pr.Prime] [CharP Ω pr] {n : ℕ} (hq₁ : Fintype.card E₁ = pr ^ n)
    (huniq : ∀ ψ ψ' : PointsOver B₁ ι₁,
      ψ.1.comp (algebraMap B B₁) = ψ'.1.comp (algebraMap B B₁) →
      (Set.range (ψ.1.comp (algebraMap B B₁))).Finite → ψ = ψ')
    (φ₁ : PointsOver B₁ ι₁) (g : B →+* E₁) (hφ₁ : φ₁.1.comp (algebraMap B B₁) = ι₁.comp g)
    (hrangeι₁ : (Set.range ι₁).Finite) : ∀ z, φ₁.1 z ^ (pr ^ n) = φ₁.1 z := by
  have hfix : ∀ c : E₁, ι₁ c ^ (pr ^ n) = ι₁ c := by
    intro c
    rw [← map_pow, ← hq₁, FiniteField.pow_card]
  let ψ' : PointsOver B₁ ι₁ := ⟨(iterateFrobenius Ω pr n).comp φ₁.1, RingHom.ext fun c => by
    have := congrArg (fun F : E₁ →+* Ω => F c) φ₁.2
    simp only [RingHom.comp_apply] at this ⊢
    rw [this, iterateFrobenius_def, hfix]⟩
  have heq : ψ' = φ₁ := huniq ψ' φ₁ (by
      rw [RingHom.comp_assoc, hφ₁]
      ext b
      simp only [RingHom.comp_apply, iterateFrobenius_def]
      exact hfix _) (by
      refine hrangeι₁.subset ?_
      rintro _ ⟨b, rfl⟩
      refine ⟨g b, ?_⟩
      show (ι₁.comp g) b = (ψ'.1.comp (algebraMap B B₁)) b
      rw [RingHom.comp_assoc, hφ₁]
      simp only [RingHom.comp_apply, iterateFrobenius_def]
      exact (hfix _).symm)
  intro z
  have := congrArg (fun ψ : PointsOver B₁ ι₁ => ψ.1 z) heq
  simpa [ψ', iterateFrobenius_def] using this

/-- The kernel of a point of `B₁` whose values are fixed by the Frobenius of the finite field
`E₁` is a rational maximal ideal: every element of `B₁` is congruent to a constant modulo it. -/
private theorem exists_sub_algebraMap_mem_ker {E₁ Ω : Type*} [Field E₁] [Fintype E₁] [Field Ω]
    (ι₁ : E₁ →+* Ω) {B₁ : Type*} [CommRing B₁] [Algebra E₁ B₁] (φ₁ : PointsOver B₁ ι₁)
    {q : ℕ} (hq₁ : Fintype.card E₁ = q) (hφ₁frob : ∀ z, φ₁.1 z ^ q = φ₁.1 z) :
    ∀ z : B₁, ∃ c : E₁, z - algebraMap E₁ B₁ c ∈ RingHom.ker φ₁.1 := by
  intro z
  let : Algebra E₁ Ω := ι₁.toAlgebra
  obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_pow_eq (E := E₁) (φ₁.1 z)
    (by rw [hq₁]; exact hφ₁frob z)
  refine ⟨c, ?_⟩
  rw [RingHom.mem_ker, map_sub, sub_eq_zero]
  have := congrArg (fun F : E₁ →+* Ω => F c) φ₁.2
  simp only [RingHom.comp_apply] at this
  rw [this]
  exact hc.symm

/-- **Lifting a twisted point along the constant extension.** A `σ`-twisted point of `B` lifts to
a `σ₁`-twisted point of `B₁`: lift it as a point, then note that the lift precomposed with `σ₁`
and the lift followed by the `Q`-power Frobenius are two points of `B₁` with the same restriction
to `B`, hence equal. -/
private theorem exists_pointsOver_comp_eq_twisted {E E₁ Ω : Type*} [Field E] [Field E₁]
    [Fintype E₁] [Algebra E E₁] [Field Ω] {B B₁ : Type*} [CommRing B] [IsDedekindDomain B]
    [CommRing B₁] [Algebra E B] [Algebra B B₁] [Algebra E₁ B₁] {pr : ℕ} [Fact pr.Prime]
    [CharP Ω pr] (ι : E →+* Ω) (ι₁ : E₁ →+* Ω) (σ : B ≃+* B) {N : ℕ}
    (hN : ∀ b, (⇑σ)^[N] b = b) (σ₁B : B₁ ≃+* B₁)
    (hσ₁BB : ∀ b, σ₁B (algebraMap B B₁ b) = algebraMap B B₁ (σ b))
    (hσ₁BE : ∀ c : E₁, σ₁B (algebraMap E₁ B₁ c) = algebraMap E₁ B₁ c)
    {m Q : ℕ} (hQ : Q = pr ^ m * pr ^ m) (hQE₁ : ∀ c : E₁, c ^ Q = c)
    (hRQ : {z : Ω | z ^ Q ^ N = z}.Finite)
    (hlift : ∀ φ : B →+* Ω, (∀ c, φ (algebraMap E B c) = ι c) → (RingHom.ker φ).IsMaximal →
      ∃ φ₁ : PointsOver B₁ ι₁, φ₁.1.comp (algebraMap B B₁) = φ)
    (huniq : ∀ ψ ψ' : PointsOver B₁ ι₁,
      ψ.1.comp (algebraMap B B₁) = ψ'.1.comp (algebraMap B B₁) →
      (Set.range (ψ.1.comp (algebraMap B B₁))).Finite → ψ = ψ') :
    ∀ φ : PointsOver B ι, (∀ b, φ.1 (σ b) = φ.1 b ^ Q) →
      ∃ φ₁ : PointsOver B₁ ι₁, φ₁.1.comp (algebraMap B B₁) = φ.1 ∧
        ∀ z, φ₁.1 (σ₁B z) = φ₁.1 z ^ Q := by
  intro φ hφ
  have hvals : ∀ b, φ.1 b ^ (Q ^ N) = φ.1 b := pow_pow_eq_of_twisted σ hN Q φ.1 hφ
  have : (RingHom.ker φ.1).IsMaximal := isMaximal_ker_of_finite_range φ.1
    (hRQ.subset (by rintro _ ⟨b, rfl⟩; exact hvals b))
  obtain ⟨φ₁, hφ₁⟩ := hlift φ.1 (fun c => congrArg (fun F : E →+* Ω => F c) φ.2) inferInstance
  refine ⟨φ₁, hφ₁, fun z => ?_⟩
  let ψa : PointsOver B₁ ι₁ := ⟨φ₁.1.comp (σ₁B : B₁ →+* B₁), RingHom.ext fun c => by
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, hσ₁BE]
    exact congrArg (fun F : E₁ →+* Ω => F c) φ₁.2⟩
  let ψb : PointsOver B₁ ι₁ := ⟨(iterateFrobenius Ω pr (m + m)).comp φ₁.1,
    RingHom.ext fun c => by
      have h1 := congrArg (fun F : E₁ →+* Ω => F c) φ₁.2
      simp only [RingHom.comp_apply] at h1 ⊢
      rw [h1, iterateFrobenius_def, ← map_pow, pow_add, ← hQ, hQE₁]⟩
  have hab : ψa = ψb := huniq ψa ψb (by
      ext b
      simp only [ψa, ψb, RingHom.comp_apply, RingEquiv.coe_toRingHom, hσ₁BB,
        iterateFrobenius_def]
      rw [← RingHom.comp_apply, hφ₁, ← RingHom.comp_apply, hφ₁, pow_add, ← hQ]
      exact hφ b) (by
      refine hRQ.subset ?_
      rintro _ ⟨b, rfl⟩
      simp only [ψa, RingHom.comp_apply, RingEquiv.coe_toRingHom, hσ₁BB]
      rw [← RingHom.comp_apply, hφ₁]
      exact hvals _)
  have := congrArg (fun ψ : PointsOver B₁ ι₁ => ψ.1 z) hab
  simp only [ψa, ψb, RingHom.comp_apply, RingEquiv.coe_toRingHom, iterateFrobenius_def,
    pow_add, ← hQ] at this
  exact this

/-- **The twisted Bombieri–Stepanov bound without a rational point.** For a ring automorphism `σ`
of finite order of a Dedekind domain `B` of finite type over a finite field `E`, fixing `E` and
with `B` of transcendence degree one, the `σ`-twisted points `φ : B → Ω` number at most
`Q + (2γ + 1) √Q` for `Q = p ^ (2e)` beyond a bound and along a progression. No maximal ideal of
`B` with residue field `E` is assumed. -/
theorem exists_ncard_twisted_le_of_isIntegral {E : Type u} [Field E] [Fintype E] (pr : ℕ)
    [Fact pr.Prime] [CharP E pr] {L : Type u} [Field L] [Algebra E L] [Algebra.EssFiniteType E L]
    (htr : Algebra.trdeg E L = 1)
    (hEint : ∀ c : L, IsIntegral E c → c ∈ (algebraMap E L).range)
    {B : Type u} [CommRing B] [IsDedekindDomain B] [Algebra E B] [Algebra.FiniteType E B]
    [Algebra B L] [IsScalarTower E B L] [IsFractionRing B L]
    (σ : B ≃+* B) (hσE : ∀ c, σ (algebraMap E B c) = algebraMap E B c) {N : ℕ} (hN0 : N ≠ 0)
    (hN : ∀ b, (⇑σ)^[N] b = b) {Ω : Type*} [Field Ω] [IsAlgClosed Ω] (ι : E →+* Ω) :
    ∃ γ a : ℕ, 0 < a ∧ ∀ e : ℕ, a ∣ e → γ ^ 2 + 3 * γ + 1 < pr ^ e →
      {φ : PointsOver B ι | ∀ b, φ.1 (σ b) = φ.1 b ^ (pr ^ e * pr ^ e)}.ncard ≤
        pr ^ e * pr ^ e + (2 * γ + 1) * pr ^ e := by
  classical
  -- `B` is not a field
  have hBnf : ¬ IsField B := not_isField_of_trdeg_eq_one htr
  -- a maximal ideal and its residue field
  obtain ⟨P₀, hP₀⟩ := Ideal.exists_maximal B
  have hP₀ne : P₀ ≠ ⊥ := fun h => hBnf ((Ring.isField_iff_maximal_bot).2 (h ▸ hP₀))
  let : Field (B ⧸ P₀) := Ideal.Quotient.field P₀
  have : Module.Finite E (B ⧸ P₀) := finite_of_finite_type_of_isJacobsonRing E (B ⧸ P₀)
  have : Finite (B ⧸ P₀) := Module.finite_of_finite E
  let : Fintype (B ⧸ P₀) := Fintype.ofFinite _
  let pb : PowerBasis E (B ⧸ P₀) := Field.powerBasisOfFiniteOfSeparable E (B ⧸ P₀)
  have hirr : Fact (Irreducible (constPoly pb L)) :=
    ⟨irreducible_map_of_forall_isIntegral hEint (minpoly.monic (PowerBasis.isIntegral_gen pb))
      (minpoly.irreducible (PowerBasis.isIntegral_gen pb))⟩
  have : IsGalois L (AdjoinRoot (constPoly pb L)) := isGalois_constPoly pb
  -- the integral closure `B₁` of `B` in `L₁`
  set L₁ := AdjoinRoot (constPoly pb L)
  set B₁ := integralClosure B L₁
  have : IsDedekindDomain B₁ := integralClosure.isDedekindDomain B L L₁
  have : IsFractionRing B₁ L₁ := integralClosure.isFractionRing_of_finite_extension L L₁
  have : Module.Finite B B₁ := IsIntegralClosure.finite B L L₁ B₁
  -- the constants `E₁ ⊆ B₁`
  have hint : ∀ c : B ⧸ P₀, IsIntegral B (constJ (L := L) pb c) := by
    intro c
    have h1 : IsIntegral E (constJ (L := L) pb c) :=
      (Algebra.IsIntegral.isIntegral c).map (constJ (L := L) pb)
    exact h1.tower_top
  let jE₁ : (B ⧸ P₀) →+* B₁ :=
    (constJ (L := L) pb : (B ⧸ P₀) →+* L₁).codRestrict (integralClosure B L₁).toSubring hint
  let : Algebra (B ⧸ P₀) B₁ := jE₁.toAlgebra
  have hjE₁ : ∀ c, (algebraMap (B ⧸ P₀) B₁ c : L₁) = constJ pb c := fun c => rfl
  -- the extension `σ₁` of `σ`
  set σL : L ≃+* L := IsFractionRing.ringEquivOfRingEquiv (K := L) (L := L) σ
  have hσLB : ∀ b, σL (algebraMap B L b) = algebraMap B L (σ b) :=
    fun b => IsFractionRing.ringEquivOfRingEquiv_algebraMap σ b
  have hσL : ∀ c : E, σL (algebraMap E L c) = algebraMap E L c := by
    intro c
    rw [IsScalarTower.algebraMap_apply E B L, hσLB, hσE]
  set σ₁ : L₁ ≃+* L₁ := liftRingEquiv pb σL hσL
  have hσ₁B : ∀ b, σ₁ (algebraMap B L₁ b) = algebraMap B L₁ (σ b) := by
    intro b
    rw [AdjoinRoot.algebraMap_eq', RingHom.comp_apply, RingHom.comp_apply, liftRingEquiv_of, hσLB]
  have hσ₁B' : ∀ b, σ₁.symm (algebraMap B L₁ b) = algebraMap B L₁ (σ.symm b) := by
    intro b
    rw [RingEquiv.symm_apply_eq, hσ₁B, RingEquiv.apply_symm_apply]
  have hmem : ∀ x : L₁, x ∈ B₁ → σ₁ x ∈ B₁ := fun x hx =>
    IsIntegral.map_of_comp_eq (σ : B →+* B) (σ₁ : L₁ →+* L₁)
      (RingHom.ext fun b => (hσ₁B b).symm) hx
  have hmem' : ∀ x : L₁, x ∈ B₁ → σ₁.symm x ∈ B₁ := fun x hx =>
    IsIntegral.map_of_comp_eq (σ.symm : B →+* B) (σ₁.symm : L₁ →+* L₁)
      (RingHom.ext fun b => (hσ₁B' b).symm) hx
  let σ₁B : B₁ ≃+* B₁ :=
    { toFun := fun x => ⟨σ₁ x, hmem x x.2⟩
      invFun := fun x => ⟨σ₁.symm x, hmem' x x.2⟩
      left_inv := fun x => Subtype.ext (σ₁.symm_apply_apply (x : L₁))
      right_inv := fun x => Subtype.ext (σ₁.apply_symm_apply (x : L₁))
      map_mul' := fun x y => Subtype.ext (map_mul σ₁ (x : L₁) (y : L₁))
      map_add' := fun x y => Subtype.ext (map_add σ₁ (x : L₁) (y : L₁)) }
  have hσ₁Bcoe : ∀ x : B₁, (σ₁B x : L₁) = σ₁ x := fun x => rfl
  have hσ₁BB : ∀ b, σ₁B (algebraMap B B₁ b) = algebraMap B B₁ (σ b) :=
    fun b => Subtype.ext (hσ₁B b)
  have hσ₁BE : ∀ c : B ⧸ P₀, σ₁B (algebraMap (B ⧸ P₀) B₁ c) = algebraMap (B ⧸ P₀) B₁ c :=
    fun c => Subtype.ext (liftRingEquiv_constJ pb σL hσL c)
  -- `σ₁` has finite order
  have hσLN : ∀ l, (⇑σL)^[N] l = l := iterate_eq_self_of_isFractionRing σ hN σL hσLB
  have hσ₁N : ∀ x, (⇑σ₁)^[N] x = x :=
    iterate_eq_self_of_adjoinRoot σL hσLN σ₁ (liftRingEquiv_of pb σL hσL)
      (liftRingEquiv_root pb σL hσL)
  have hσ₁BN : ∀ x, (⇑σ₁B)^[N] x = x :=
    iterate_eq_self_of_injective hσ₁Bcoe (fun _ _ h => Subtype.ext h) hσ₁N
  -- the Galois group of `L₁/L` acting on `B₁`
  set Γ := L₁ ≃ₐ[L] L₁
  have : SMulCommClass Γ B L₁ := SMulCommClass.symm _ _ _
  have : IsGaloisGroup Γ B B₁ := IsGaloisGroup.of_isFractionRing Γ B B₁ L L₁
  have : Algebra.IsInvariant B B₁ Γ := IsGaloisGroup.isInvariant
  have hΓB : ∀ (g : Γ) (b : B), g • algebraMap B B₁ b = algebraMap B B₁ b := fun g b =>
    Subtype.ext (by
      show g (algebraMap B L₁ b) = algebraMap B L₁ b
      rw [IsScalarTower.algebraMap_apply B L L₁, AlgEquiv.commutes])
  have hΓE : ∀ (τ : (B ⧸ P₀) →ₐ[E] (B ⧸ P₀)) (c : B ⧸ P₀),
      galoisOfAut (L := L) pb τ • algebraMap (B ⧸ P₀) B₁ c = algebraMap (B ⧸ P₀) B₁ (τ c) :=
    fun τ c => Subtype.ext (galoisOfAut_constJ pb τ c)
  have hfaith : ∀ g : Γ, (∀ c : B ⧸ P₀, g • algebraMap (B ⧸ P₀) B₁ c =
      algebraMap (B ⧸ P₀) B₁ c) → g = 1 := fun g hg =>
    eq_one_of_forall_constJ pb g (fun c => congrArg Subtype.val (hg c))
  have hEB₁ : ∀ c : E, algebraMap (B ⧸ P₀) B₁ (algebraMap E (B ⧸ P₀) c) =
      algebraMap B B₁ (algebraMap E B c) := fun c => Subtype.ext (by
    show constJ pb (algebraMap E (B ⧸ P₀) c) = algebraMap B L₁ (algebraMap E B c)
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply B L L₁,
      ← IsScalarTower.algebraMap_apply E B L, ← IsScalarTower.algebraMap_apply E L L₁])
  have hinjB : Function.Injective (algebraMap B B₁) := by
    intro a b h
    have h' : algebraMap B L₁ a = algebraMap B L₁ b := congrArg (fun x : B₁ => (x : L₁)) h
    rw [IsScalarTower.algebraMap_apply B L L₁, IsScalarTower.algebraMap_apply B L L₁] at h'
    exact IsFractionRing.injective B L ((algebraMap L L₁).injective h')
  -- the embedding of the constants
  let : Algebra E Ω := ι.toAlgebra
  let ι₁A : (B ⧸ P₀) →ₐ[E] Ω := IsAlgClosed.lift
  set ι₁ : (B ⧸ P₀) →+* Ω := (ι₁A : (B ⧸ P₀) →+* Ω)
  -- lifting points along `B ⊆ B₁`
  have hlift : ∀ φ : B →+* Ω, (∀ c, φ (algebraMap E B c) = ι c) → (RingHom.ker φ).IsMaximal →
      ∃ φ₁ : PointsOver B₁ ι₁, φ₁.1.comp (algebraMap B B₁) = φ :=
    exists_pointsOver_comp_eq Γ (fun τ => galoisOfAut (L := L) pb τ) hΓB hΓE hEB₁ hinjB ι
      (fun _ => rfl) ι₁A
  -- uniqueness of lifts
  have huniq : ∀ ψ ψ' : PointsOver B₁ ι₁, ψ.1.comp (algebraMap B B₁) = ψ'.1.comp (algebraMap B B₁) →
      (Set.range (ψ.1.comp (algebraMap B B₁))).Finite → ψ = ψ' := by
    intro ψ ψ' h hfin
    have := finite_quotient_ker ψ.1 hfin
    exact eq_of_comp_algebraMap_eq ι₁ Γ hfaith ψ ψ' h
  -- characteristic and the size of `E₁`
  have : CharP Ω pr := charP_of_injective_algebraMap (algebraMap E Ω).injective pr
  have : CharP (B ⧸ P₀) pr :=
    charP_of_injective_algebraMap (algebraMap E (B ⧸ P₀)).injective pr
  obtain ⟨n₁, -, hq₁⟩ := FiniteField.card (B ⧸ P₀) pr
  have hι₁E : ∀ c : E, ι₁ (algebraMap E (B ⧸ P₀) c) = ι c := fun c => ι₁A.commutes c
  -- a point of `B₁` with values in `E₁`, hence a rational maximal ideal
  set φ₀ : B →+* Ω := ι₁.comp (Ideal.Quotient.mk P₀)
  have hφ₀E : ∀ c, φ₀ (algebraMap E B c) = ι c := fun c => hι₁E c
  have hφ₀max : (RingHom.ker φ₀).IsMaximal := by
    have : RingHom.ker φ₀ = P₀ := by
      ext b
      simp [φ₀, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
    rw [this]
    exact hP₀
  obtain ⟨φ₁, hφ₁⟩ := hlift φ₀ hφ₀E hφ₀max
  have hrangeι₁ : (Set.range ι₁).Finite := Set.finite_range _
  have hφ₁frob : ∀ z, φ₁.1 z ^ (pr ^ (n₁ : ℕ)) = φ₁.1 z :=
    pow_eq_self_of_comp_eq ι₁ hq₁ huniq φ₁ (Ideal.Quotient.mk P₀) hφ₁ hrangeι₁
  have hq₁pos : 1 < pr ^ (n₁ : ℕ) := Nat.one_lt_pow n₁.ne_zero (Fact.out : pr.Prime).one_lt
  obtain ⟨hRfin, -⟩ := setOf_pow_eq_self_finite_ncard_le (Ω := Ω) hq₁pos
  have hP₁max : (RingHom.ker φ₁.1).IsMaximal := isMaximal_ker_of_finite_range φ₁.1
    (hRfin.subset (by rintro _ ⟨z, rfl⟩; exact hφ₁frob z))
  have hBinf : Infinite B := by
    by_contra h
    rw [not_infinite_iff_finite] at h
    exact hBnf (Finite.isField_of_domain B)
  have hP₁ne : RingHom.ker φ₁.1 ≠ ⊥ :=
    ker_ne_bot_of_range_subset_finite hinjB φ₁.1 hRfin hφ₁frob
  have hP₁rat : ∀ z : B₁, ∃ c : B ⧸ P₀, z - algebraMap (B ⧸ P₀) B₁ c ∈ RingHom.ker φ₁.1 :=
    exists_sub_algebraMap_mem_ker ι₁ φ₁ hq₁ hφ₁frob
  -- the structures needed for the bound on `B₁` over `E₁`
  let : Algebra (B ⧸ P₀) L₁ := (constJ (L := L) pb : (B ⧸ P₀) →+* L₁).toAlgebra
  have : IsScalarTower (B ⧸ P₀) B₁ L₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra E B₁ := ((algebraMap B B₁).comp (algebraMap E B)).toAlgebra
  have : IsScalarTower E B B₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType B B₁ := inferInstance
  have : Algebra.FiniteType E B₁ := Algebra.FiniteType.trans (S := B) inferInstance inferInstance
  have : IsScalarTower E (B ⧸ P₀) B₁ := IsScalarTower.of_algebraMap_eq fun c => (hEB₁ c).symm
  have : Algebra.FiniteType (B ⧸ P₀) B₁ := Algebra.FiniteType.of_restrictScalars_finiteType E _ _
  have : Algebra.EssFiniteType B₁ L₁ :=
    Algebra.EssFiniteType.of_isLocalization L₁ (nonZeroDivisors B₁)
  have : Algebra.EssFiniteType (B ⧸ P₀) L₁ := Algebra.EssFiniteType.comp _ B₁ _
  have : IsScalarTower E (B ⧸ P₀) L₁ := IsScalarTower.of_algebraMap_eq fun c =>
    ((constJ (L := L) pb).commutes c).symm
  have htr₁ : Algebra.trdeg (B ⧸ P₀) L₁ = 1 := by
    have h1 := trdeg_add_eq E (B ⧸ P₀) (A := L₁)
    have h2 := trdeg_add_eq E L (A := L₁)
    have : Algebra.IsAlgebraic E (B ⧸ P₀) := Algebra.IsIntegral.isAlgebraic
    have : Algebra.IsAlgebraic L L₁ := Algebra.IsIntegral.isAlgebraic
    rw [_root_.trdeg_eq_zero, zero_add] at h1
    rw [_root_.trdeg_eq_zero (R := L) (A := L₁), add_zero, htr] at h2
    rw [h1, ← h2]
  obtain ⟨γ, hγ⟩ := exists_ncard_twisted_le pr htr₁ (RingHom.ker φ₁.1) hP₁ne hP₁rat σ₁B hσ₁BE
    hN0 hσ₁BN ι₁
  refine ⟨γ, n₁, n₁.pos, fun e hdvd he => ?_⟩
  set Q := pr ^ e * pr ^ e with hQ
  obtain ⟨t, rfl⟩ := hdvd
  have hQE₁ : ∀ c : B ⧸ P₀, c ^ Q = c := by
    intro c
    have : Q = Fintype.card (B ⧸ P₀) ^ (2 * t) := by
      rw [hQ, hq₁, ← pow_mul, ← pow_add]
      ring_nf
    rw [this, FiniteField.pow_card_pow]
  obtain ⟨hfin₁, hle₁⟩ := hγ (n₁ * t) he
  have hQ1 : 1 < Q ^ N := by
    have h1 : 1 < pr ^ (n₁ * t) := lt_of_le_of_lt (by omega) he
    exact Nat.one_lt_pow hN0 (by nlinarith)
  obtain ⟨hRQ, -⟩ := setOf_pow_eq_self_finite_ncard_le (Ω := Ω) hQ1
  -- every twisted point of `B` lifts to a twisted point of `B₁`
  have hlift' : ∀ φ : PointsOver B ι, (∀ b, φ.1 (σ b) = φ.1 b ^ Q) →
      ∃ φ₁ : PointsOver B₁ ι₁, φ₁.1.comp (algebraMap B B₁) = φ.1 ∧
        ∀ z, φ₁.1 (σ₁B z) = φ₁.1 z ^ Q :=
    exists_pointsOver_comp_eq_twisted ι ι₁ σ hN σ₁B hσ₁BB hσ₁BE hQ hQE₁ hRQ hlift huniq
  have : Nonempty (PointsOver B₁ ι₁) := ⟨φ₁⟩
  choose! Λ hΛ using hlift'
  refine (Set.ncard_le_ncard_of_injOn Λ
    (t := {φ : PointsOver B₁ ι₁ | ∀ b, φ.1 (σ₁B b) = φ.1 b ^ (pr ^ (n₁ * t) * pr ^ (n₁ * t))})
    (fun φ hφ => (hΛ φ hφ).2) (fun φ hφ φ' hφ' h => ?_) hfin₁).trans hle₁
  refine Subtype.ext (RingHom.ext fun b => ?_)
  rw [← (hΛ φ hφ).1, ← (hΛ φ' hφ').1, RingHom.comp_apply, RingHom.comp_apply, h]

end Stacks.BombieriStepanov

end
