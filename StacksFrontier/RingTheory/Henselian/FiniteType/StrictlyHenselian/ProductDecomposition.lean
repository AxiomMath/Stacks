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
public import StacksFrontier.RingTheory.Henselian.FiniteType.StrictlyHenselian.HenselianPairRootLift

/-!
# Decomposition into finite local factors and the main statement

Lifting complete orthogonal idempotents from the closed fibre, the local finite factors of a
module-finite algebra over a henselian local ring, the decomposition `S ≃ₐ[R] (∀ i, A i) × B`
of a finite type algebra, and Stacks Tag 06DD for strictly henselian local rings.
-/

section

universe u

@[expose] public section

open IsLocalRing

/-- **Bare idempotent lift along `mA`.** For `A` module-finite over henselian local `R`,
idempotents of the closed fibre `A ⧸ mA` lift to idempotents of `A`. The proof combines
`isUnit_of_isUnit_mk` and `henselianPair_mA_quadratic` using the Newton data: a lift `a` of
`e₁`, the unit `b := 2a - 1` (a unit since `(2a-1)² ≡ 1 mod mA`), `d := a² - a ∈ mA`,
`f(T) = T² + bT + d`, and finally `e₀ := a + c`. -/
theorem closedFibre_idempotent_lift (R : Type) [CommRing R] [HenselianLocalRing R] (A : Type)
    [CommRing A] [Algebra R A] [Module.Finite R A]
    (e₁ : A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) (he₁ : IsIdempotentElem e₁) :
    ∃ e₀ : A, IsIdempotentElem e₀ ∧ (Ideal.Quotient.mk _) e₀ = e₁ := by
  -- Lift e₁ to a ∈ A.
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective e₁
  set mk := Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R A)) with hmk
  -- d := a² - a ∈ mA, i.e. mk d = 0.
  have hd : mk (a * a - a) = 0 := by
    rw [map_sub, map_mul, ha, he₁.eq, sub_self]
  -- b := 2a - 1 is a unit: its image squares to 1 in A⧸mA.
  have hbunit : IsUnit (2 * a - 1) := by
    apply isUnit_of_isUnit_mk R A
    have hsq : mk (2 * a - 1) * mk (2 * a - 1) = 1 := by
      have : mk ((2 * a - 1) * (2 * a - 1)) = mk (4 * (a * a - a) + 1) := by
        congr 1; ring
      rw [map_mul] at this
      rw [this, map_add, map_mul, hd, mul_zero, zero_add, map_one]
    exact IsUnit.of_mul_eq_one (mk (2 * a - 1)) hsq
  -- Apply the henselian-pair quadratic lift with b = 2a-1, d = a²-a.
  obtain ⟨c, hc0, hceq⟩ := henselianPair_mA_quadratic R A (2 * a - 1) (a * a - a) hbunit hd
  refine ⟨a + c, ?_, ?_⟩
  · -- (a+c)² = a+c  ⇔  c² + (2a-1)c + (a²-a) = 0
    change (a + c) * (a + c) = a + c
    linear_combination hceq
  · rw [map_add, hc0, add_zero, ha]

/-- **Idempotent lift below a relative unit.** For `A` module-finite, hence integral, over a
henselian local ring `R`, with `mA := m·A` and `mk : A → A ⧸ mA`: given an idempotent `f ∈ A`
and an idempotent `e₁ ∈ A ⧸ mA` lying *below* `mk f`, i.e. `e₁ * mk f = e₁`, there is an
idempotent `e' ∈ A` lying below `f`, i.e. `e' * f = e'`, with `mk e' = e₁`.

This is the bare single-idempotent lift to which the orthogonality refinement of
`henselian_orthogonal_idempotent_lift` reduces by a formal corner argument. The "below `f`"
phrasing replaces the corner ring `C = f·A` without constructing it, using `f` as a relative
unit. The mathematical content is to lift a chosen preimage `a` of `e₁`, which satisfies
`a² - a ∈ mA`, to an honest idempotent: `a` is integral over `R`, so there is a monic
`p ∈ R[X]` with `p(a) = 0`; the reduction `p̄` factors coprimely, separating the idempotent;
the factorization form of henselianness (`hensel_factorization_over_R`) lifts that
factorization; Nakayama gives comaximality `(g) + (h) = R[X]`; and CRT in `R[X]/(p)` builds
the idempotent, which is transported to `A` via `X ↦ a`. Staying below `f` means applying the
lift inside the relative unit `f`, equivalently in the corner `f·A`, and `mA ⊆ Jac A` (by
integral lying-over) makes idempotents in the kernel unique. -/
theorem henselian_idempotent_lift_below (R : Type) [CommRing R] [HenselianLocalRing R] (A : Type)
    [CommRing A] [Algebra R A] [Module.Finite R A] (f : A) (hf : IsIdempotentElem f)
    (e₁ : A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) (he₁ : IsIdempotentElem e₁)
    (hbelow : e₁ * (Ideal.Quotient.mk _) f = e₁) :
    ∃ e' : A, IsIdempotentElem e' ∧ (Ideal.Quotient.mk _) e' = e₁ ∧ e' * f = e' := by
  -- The "below f" refinement is purely formal: if e₀ is ANY idempotent of A with
  -- mk e₀ = e₁, then e' := f * e₀ works. It is idempotent (f and e₀ are, and A is
  -- commutative), mk e' = mk f * e₁ = e₁ * mk f = e₁ by hbelow, and
  -- e' * f = f² e₀ = f e₀ = e'. So everything reduces to bare idempotent lifting along mA,
  -- i.e. to the henselian-pair property (Stacks 04GG/09XI).
  obtain ⟨e₀, he₀, hmk₀⟩ := closedFibre_idempotent_lift R A e₁ he₁
  refine ⟨f * e₀, ?_, ?_, ?_⟩
  · exact hf.mul he₀
  · -- mk (f * e₀) = e₁
    rw [map_mul, hmk₀, mul_comm, hbelow]
  · -- (f * e₀) * f = f * e₀
    linear_combination e₀ * hf.eq

/-- **The orthogonal single-idempotent lifting primitive along `mA`.** For `A` module-finite,
hence integral, over a henselian local `R`: given an idempotent `e₁` of the closed fibre
`Ā = A ⧸ mA` in the image of `mk`, and an idempotent `e₂ ∈ A` orthogonal to `e₁` on both
sides, there is an idempotent `e' ∈ A` lifting `e₁` and orthogonal to `e₂`.

This is the henselian analogue of Mathlib's
`exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent`, which needs a NILPOTENT kernel; here
the kernel `mA` is merely contained in `rad A`, and the HENSELIAN-PAIR property of `(A, mA)`
(Stacks 04GG/09XI) is used instead.

The argument: lift `e₁` to some `a ∈ A`; `a` is integral over `R`, satisfying a monic
`p ∈ R[X]`, and `p̄ ∈ κ[X]` factors as a product of coprime monics `p̄₀ p̄₁` according to the
idempotent, by CRT splitting of the Artinian `κ[X]/(p̄)`; the factorization form of
henselianness (`hensel_factorization_over_R`) lifts this to `p = p₀ p₁` over `R`; and
Nakayama comaximality together with CRT in `B = R[X]/(p) ↠ R[a] ⊆ A` produces the lifted
idempotent. Orthogonality to `e₂` is arranged in the corner ring `(1 - e₂)A`, where `e₂` acts
as `0`. -/
theorem henselian_orthogonal_idempotent_lift (R : Type) [CommRing R] [HenselianLocalRing R]
    (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A] :
    ∀ (e₁ : A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)),
      e₁ ∈ (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R A))).range →
        IsIdempotentElem e₁ →
        ∀ (e₂ : A),
          IsIdempotentElem e₂ →
            e₁ * (Ideal.Quotient.mk _) e₂ = 0 →
            (Ideal.Quotient.mk _) e₂ * e₁ = 0 →
            ∃ e' : A,
              IsIdempotentElem e' ∧ (Ideal.Quotient.mk _) e' = e₁ ∧ e' * e₂ = 0 ∧ e₂ * e' = 0 := by
  -- Orthogonality to e₂ is equivalent to landing below f := 1 - e₂, so the whole content is
  -- the bare lift `henselian_idempotent_lift_below`. Steps:
  --   * set f := 1 - e₂ (idempotent by IsIdempotentElem.one_sub); mk f = 1 - mk e₂.
  --   * e₁ lies below mk f: e₁ * mk f = e₁ * (1 - mk e₂) = e₁ - e₁ * mk e₂ = e₁ - 0 = e₁,
  --     using the hypothesis e₁ * mk e₂ = 0 and that mk is a ring hom.
  --   * apply henselian_idempotent_lift_below R A f hf e₁ he₁ hbelow to get e' idempotent
  --     with mk e' = e₁ and e' * f = e'.
  --   * orthogonality: e' * e₂ = e' * (1 - f) = e' - e' * f = e' - e' = 0, and
  --     e₂ * e' = e' * e₂ = 0 by commutativity.
  intro e₁ _ he₁ e₂ he₂ horth _
  have hf : IsIdempotentElem (1 - e₂) := he₂.one_sub
  -- e₁ lies below mk (1 - e₂)
  have hbelow : e₁ * (Ideal.Quotient.mk _) (1 - e₂) = e₁ := by
    rw [map_sub, map_one, mul_sub, mul_one, horth, sub_zero]
  obtain ⟨e', he'idem, he'mk, he'below⟩ :=
    henselian_idempotent_lift_below R A (1 - e₂) hf e₁ he₁ hbelow
  -- e' * e₂ = e' * (1 - (1-e₂)) = e' - e' * (1-e₂) = e' - e' = 0
  have h0 : e' * e₂ = 0 := by
    have hee : e' * e₂ = e' - e' * (1 - e₂) := by ring
    rw [hee, he'below, sub_self]
  exact
    ⟨e', he'idem, he'mk, h0, by
      rw [mul_comm]; exact h0⟩

/-- **Lifting a complete orthogonal idempotent system along a surjection.**
Generic lift of a COMPLETE ORTHOGONAL idempotent system along any surjective ring hom
`f : A →+* B` having the orthogonal single-idempotent lifting property `Hlift`.

This mirrors Mathlib's `CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker` and
`OrthogonalIdempotents.lift_of_isNilpotent_ker_aux`, with the nilpotent-kernel hypothesis
replaced by the abstract lifting hypothesis `Hlift`: the only place the Mathlib proof uses
nilpotency is to invoke `exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent`, which has
exactly the shape of `Hlift`. The proof inducts on the `Fin n` family via `Fin.cons`, lifting
one idempotent at a time orthogonally to those already lifted, using `Hlift`; surjectivity
supplies the range membership, and the lifted family sums to `1` by completeness. -/
theorem coi_lift_of_orthogonal_lift {A : Type} [CommRing A] {B : Type} [CommRing B] (f : A →+* B)
    (Hlift :
      ∀ (e₁ : B),
        e₁ ∈ f.range →
          IsIdempotentElem e₁ →
          ∀ (e₂ : A),
            IsIdempotentElem e₂ →
              e₁ * f e₂ = 0 →
              f e₂ * e₁ = 0 →
              ∃ e' : A, IsIdempotentElem e' ∧ f e' = e₁ ∧ e' * e₂ = 0 ∧ e₂ * e' = 0)
    (Hsurj : Function.Surjective f) (Hker0 : ∀ x : A, IsIdempotentElem x → f x = 0 → x = 0) {n : ℕ}
    {e : Fin n → B} (he : CompleteOrthogonalIdempotents e) :
    ∃ e' : Fin n → A, CompleteOrthogonalIdempotents e' ∧ f ∘ e' = e := by
  -- STEP 1: orthogonal aux lemma, mirroring OrthogonalIdempotents.lift_of_isNilpotent_ker_aux
  have aux :
    ∀ {m : ℕ} (e : Fin m → B),
      OrthogonalIdempotents e →
        (∀ i, e i ∈ f.range) → ∃ e' : Fin m → A, OrthogonalIdempotents e' ∧ f ∘ e' = e := by
    intro m
    induction m with
    | zero =>
      intro e he he'; exact ⟨0, ⟨finZeroElim, finZeroElim⟩, funext finZeroElim⟩
    | succ m IH =>
      intro e he he'
      obtain ⟨e', h₁, h₂⟩ := IH (e ∘ Fin.succ) (he.embedding (Fin.succEmb m)) (fun i ↦ he' _)
      have h₂' (i) : f (e' i) = e i.succ := congr_fun h₂ i
      obtain ⟨e₀, h₃, h₄, h₅, h₆⟩ :=
        Hlift _ (he' 0) (he.idem 0) _ h₁.isIdempotentElem_sum
          (by simp [Finset.mul_sum, h₂', he.mul_eq, eq_comm])
          (by simp [Finset.sum_mul, h₂', he.mul_eq])
      refine ⟨_, (h₁.option _ h₃ h₅ h₆).embedding (finSuccEquiv m).toEmbedding, funext fun i ↦ ?_⟩
      obtain ⟨_ | i, rfl⟩ := (finSuccEquiv m).symm.surjective i <;> simp [*]
  -- STEP 2: completeness
  obtain ⟨e', h₁, h₂⟩ :=
    aux e he.toOrthogonalIdempotents (fun i ↦ RingHom.mem_range.mpr (Hsurj (e i)))
  have h₂' (i) : f (e' i) = e i := congr_fun h₂ i
  have hsidem : IsIdempotentElem (∑ i, e' i) := h₁.isIdempotentElem_sum
  have hfs : f (∑ i, e' i) = 1 := by
    rw [map_sum]
    simp only [h₂']
    exact he.complete
  have h1s : IsIdempotentElem (1 - ∑ i, e' i) := hsidem.one_sub
  have hf1s : f (1 - ∑ i, e' i) = 0 := by rw [map_sub, map_one, hfs, sub_self]
  have hzero : (1 : A) - ∑ i, e' i = 0 := Hker0 _ h1s hf1s
  have hscomplete : ∑ i, e' i = 1 := by
    have := sub_eq_zero.mp hzero
    exact this.symm
  exact ⟨e', ⟨h₁, hscomplete⟩, h₂⟩

/-- **Lifting a complete orthogonal idempotent system from the closed fibre.**
For `A` module-finite, hence integral, over a henselian local ring `R`, the pair `(A, mA)` is
a HENSELIAN PAIR, so every complete orthogonal idempotent system of the closed fibre `A ⧸ mA`
lifts to a complete orthogonal idempotent system of `A` reducing to it, that is with
`Ideal.Quotient.mk _ ∘ e = eb`.

This applies the generic assembly `coi_lift_of_orthogonal_lift` to the quotient map
`mk : A → A ⧸ mA`, surjective by `Ideal.Quotient.mk_surjective`, with the orthogonal
single-idempotent lifting primitive `henselian_orthogonal_idempotent_lift` supplying the
`Hlift` hypothesis. -/
@[sga "1 I 6.2" "partial"]
theorem henselian_lift_completeOrthogonalIdempotents (R : Type) [CommRing R] [HenselianLocalRing R]
    (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A] (n : ℕ)
    (eb : Fin n → (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)))
    (heb : CompleteOrthogonalIdempotents eb) :
    ∃ e : Fin n → A, CompleteOrthogonalIdempotents e ∧ (Ideal.Quotient.mk _) ∘ e = eb := by
  -- Henselian-pair idempotent lifting (Stacks 04GG/09XI).
  exact
    coi_lift_of_orthogonal_lift
      (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R A)))
      (henselian_orthogonal_idempotent_lift R A) Ideal.Quotient.mk_surjective
      (fun x hx hx0 => by
        -- x ∈ mA ⊆ jacobson ⊥; an idempotent in the Jacobson radical is 0.
        have hmem : x ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R A) :=
          (Ideal.Quotient.eq_zero_iff_mem).mp hx0
        have hjac : x ∈ Ideal.jacobson (⊥ : Ideal A) := mA_le_jacobson R A hmem
        -- (1 - x) - 1 = -x ∈ jacobson ⊥ ⇒ 1 - x is a unit.
        have hu : IsUnit (1 - x) :=
          Ideal.isUnit_of_sub_one_mem_jacobson_bot (1 - x)
            (by
              have : (1 - x) - 1 = -x := by ring
              rw [this]; exact neg_mem hjac)
        have hzero : x * (1 - x) = 0 := by
          have : x * (1 - x) = x - x * x := by ring
          rw [this, hx.eq, sub_self]
        exact hu.mul_left_eq_zero.mp hzero)
      heb

/-- **Factor properties from a local closed fibre.**
Given a complete orthogonal idempotent system `e : Fin n → A` of a module-finite `R`-algebra
`A` over a local ring `R`, whose reduction in the closed fibre `A ⧸ mA` cuts out LOCAL factors
(`hfib`), each corner `A ⧸ span {1 - e i}` is itself LOCAL and FINITE over `R`, with LOCAL
structure map `R → A ⧸ span {1 - e i}`.

Indeed `A_i := A ⧸ span {1 - e i} ≅ eᵢ·A` is a corner of the finite `R`-module `A`, hence
finite over `R`. Since `A` is integral over the local ring `R`, every maximal ideal of `A_i`
lies over `m` and therefore contains `mA_i`, so the maximal ideals of `A_i` biject with those
of the closed fibre `A_i ⧸ mA_i ≅ Ā ⧸ span {1 - mk e i}`, which is local by `hfib`; hence
`A_i` is local. The structure map `R → A_i` is local because `R` local together with
`A_i ≠ 0` and integrality force `(algebraMap R A_i)⁻¹(maximal) = m`. The ingredients are
lying-over for integral extensions and the corner of a finite module. -/
@[ega "0 10.3.1.2" "partial", ega "0 22.5.2" "partial"]
theorem decompFactor_isLocal_finite_localHom (R : Type) [CommRing R] [IsLocalRing R] (A : Type)
    [CommRing A] [Algebra R A] [Module.Finite R A] (n : ℕ) (e : Fin n → A)
    (hfib :
      ∀ i,
        IsLocalRing
          ((A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) ⧸
            Ideal.span {1 - (Ideal.Quotient.mk _ (e i))})) :
    (∀ i, IsLocalRing (A ⧸ Ideal.span {1 - e i})) ∧
      (∀ i, IsLocalHom (algebraMap R (A ⧸ Ideal.span {1 - e i}))) ∧
      (∀ i, Module.Finite R (A ⧸ Ideal.span {1 - e i})) := by
  set mA := (IsLocalRing.maximalIdeal R).map (algebraMap R A) with hmAdef
  -- (c) finiteness
  have hfin : ∀ i, Module.Finite R (A ⧸ Ideal.span {1 - e i}) := fun i =>
    Module.Finite.quotient R (Ideal.span {1 - e i})
  -- For each i: locality of A_i AND local-hom of structure map.
  have hkey :
    ∀ i,
      IsLocalRing (A ⧸ Ideal.span {1 - e i}) ∧
        IsLocalHom (algebraMap R (A ⧸ Ideal.span {1 - e i})) := by
    intro i
    set Si := Ideal.span {1 - e i} with hSi
    set mAi := mA.map (Ideal.Quotient.mk Si) with hmAi
    -- (1) mAi ≤ jacobson ⊥ in A_i
    have hjac : mAi ≤ Ideal.jacobson (⊥ : Ideal (A ⧸ Si)) := by
      have hsurj : Function.Surjective (Ideal.Quotient.mk Si) := Ideal.Quotient.mk_surjective
      have hkerSi : RingHom.ker (Ideal.Quotient.mk Si) ≤ Si := by rw [Ideal.mk_ker]
      have hmapj :
        Ideal.map (Ideal.Quotient.mk Si) (Ideal.jacobson Si) =
          (Ideal.map (Ideal.Quotient.mk Si) Si).jacobson :=
        Ideal.map_jacobson_of_surjective hsurj hkerSi
      have hmapSi : Ideal.map (Ideal.Quotient.mk Si) Si = ⊥ := by
        rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
      rw [hmapSi] at hmapj
      calc
        mAi = mA.map (Ideal.Quotient.mk Si) := hmAi
        _ ≤ (Ideal.jacobson Si).map (Ideal.Quotient.mk Si) :=
          Ideal.map_mono ((mA_le_jacobson R A).trans (Ideal.jacobson_mono bot_le))
        _ = Ideal.jacobson (⊥ : Ideal (A ⧸ Si)) := hmapj
    -- (2) A_i / mAi is local via iso chain to hfib i
    have hlocFib : IsLocalRing ((A ⧸ Si) ⧸ mAi) := by
      let ψ :
        ((A ⧸ mA) ⧸ Ideal.span {1 - (Ideal.Quotient.mk mA (e i))}) ≃+*
          A ⧸ (mA ⊔ Ideal.span {1 - e i}) := by
        have h := DoubleQuot.quotQuotEquivQuotSup mA (Ideal.span {1 - e i})
        rwa [Ideal.map_span, Set.image_singleton, map_sub, map_one] at h
      have hfibi : IsLocalRing ((A ⧸ mA) ⧸ Ideal.span {1 - (Ideal.Quotient.mk mA (e i))}) := hfib i
      have hsup : IsLocalRing (A ⧸ (mA ⊔ Ideal.span {1 - e i})) := ψ.isLocalRing
      let φ : ((A ⧸ Si) ⧸ mAi) ≃+* A ⧸ (Si ⊔ mA) := DoubleQuot.quotQuotEquivQuotSup Si mA
      have heq : Si ⊔ mA = mA ⊔ Ideal.span {1 - e i} := by rw [hSi, sup_comm]
      exact (φ.trans (Ideal.quotEquivOfEq heq)).symm.isLocalRing
    -- (a) A_i is local
    have hlh : IsLocalHom (Ideal.Quotient.mk mAi) := isLocalHom_of_le_jacobson_bot mAi hjac
    have hAiloc : IsLocalRing (A ⧸ Si) := (Ideal.Quotient.mk mAi).domain_isLocalRing
    -- (b) structure map R → A_i is a local hom: the composite R → A_i → A_i/mAi sends
    -- maximalIdeal R to 0 (mA ⊆ mAi), hence is local; factor through isLocalHom_of_comp.
    have hslh : IsLocalHom (algebraMap R (A ⧸ Si)) := by
      have hcomp : IsLocalHom ((Ideal.Quotient.mk mAi).comp (algebraMap R (A ⧸ Si))) := by
        constructor
        intro a ha
        by_contra hna
        have hca : (Ideal.Quotient.mk mAi).comp (algebraMap R (A ⧸ Si)) a = 0 := by
          rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
          change Ideal.Quotient.mk Si (algebraMap R A a) ∈ mAi
          rw [hmAi, hmAdef]
          exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hna)
        exact not_isUnit_zero (hca ▸ ha)
      exact isLocalHom_of_comp (algebraMap R (A ⧸ Si)) (Ideal.Quotient.mk mAi)
    exact ⟨hAiloc, hslh⟩
  exact ⟨fun i => (hkey i).left, fun i => (hkey i).right, hfin⟩

/-- **Henselian decomposition of a module-finite algebra.** A module-finite algebra `A` over
a henselian local ring `R` is a finite product of local finite `R`-algebras, expressed at the
idempotent level: there is a COMPLETE orthogonal idempotent system `ε : Fin n → A`, so that
`∑ ε i = 1_A`, with each factor `A ⧸ span {1 - ε i}` a LOCAL ring, FINITE over `R`, and with
`R → A ⧸ span {1 - ε i}` a LOCAL homomorphism.

The closed fibre `Ā = A/mA = A ⊗_R κ` is a finite-dimensional `κ`-algebra, hence Artinian; its
Jacobson radical is nilpotent (`IsArtinianRing.isNilpotent_jacobson_bot`) and `Ā/rad` is a
finite product of fields, which gives a complete orthogonal idempotent system in `Ā` by lifting
along the nilpotent radical. The crux is then to lift that system from `Ā = A/mA` to `A` along
the kernel `mA`, which is NOT nilpotent: this uses the henselian-pair property of `(A, mA)`,
i.e. that idempotents lift along `mA` because `A` is integral over the henselian local `R`.
Each lifted primitive idempotent cuts out a local factor, its closed fibre being a single
local Artinian ring, finite over `R`, with local structure map, since `A` integral over the
local `R` forces maximal ideals to lie over `m`. -/
@[ega "IV 18.5.11" "partial",
  ega "IV 18.5.9" "(ii), necessity",
  sga "3 XV 1.5" "partial",
  sga "3 XV 3.9" "partial",
  sga "4 VIII 4.1" "(i)"]
theorem henselian_finite_decomp_corner (R : Type) [CommRing R] [HenselianLocalRing R] (A : Type)
    [CommRing A] [Algebra R A] [Module.Finite R A] :
    ∃ (n : ℕ) (ε : Fin n → A),
      CompleteOrthogonalIdempotents ε ∧
        (∀ i, IsLocalRing (A ⧸ Ideal.span {1 - ε i})) ∧
        (∀ i, IsLocalHom (algebraMap R (A ⧸ Ideal.span {1 - ε i}))) ∧
        (∀ i, Module.Finite R (A ⧸ Ideal.span {1 - ε i})) := by
  -- The henselian core of Stacks 04GE/04GG: finite over henselian local means a finite
  -- product of local finite factors.
  --
  -- `closedFibre_completeOrthogonalIdempotents` gives a complete orthogonal idempotent system
  -- `eb` of the closed fibre `A ⧸ mA` with local factors;
  -- `henselian_lift_completeOrthogonalIdempotents` lifts it to a system `ε` of `A` reducing to
  -- `eb`; and `decompFactor_isLocal_finite_localHom` promotes each `A ⧸ span {1-ε i}` to
  -- local, finite and local-hom, using that its closed fibre coincides with `eb i`'s factor.
  obtain ⟨n, eb, hcoi_b, hfib_b⟩ := closedFibre_completeOrthogonalIdempotents R A
  obtain ⟨ε, hcoi, hlift⟩ := henselian_lift_completeOrthogonalIdempotents R A n eb hcoi_b
  have hfib :
    ∀ i,
      IsLocalRing
        ((A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) ⧸
          Ideal.span {1 - (Ideal.Quotient.mk _ (ε i))}) := by
    intro i
    have hi :
      (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R A))) (ε i) = eb i := by
      have := congrFun hlift i
      simpa using this
    rw [hi]
    exact hfib_b i
  obtain ⟨hloc, hlh, hfin⟩ := decompFactor_isLocal_finite_localHom R A n ε hfib
  exact ⟨n, ε, hcoi, hloc, hlh, hfin⟩

/-- **Transport of a corner decomposition back below an idempotent.**
Given an idempotent `c : S` and a COMPLETE orthogonal idempotent system `ε : Fin n → A` of the
corner ring `A := S ⧸ span {1 - c} ≅ c·S`, with each factor `A ⧸ span {1 - ε i}` local, finite
over `R` and with local structure map, one obtains ORTHOGONAL idempotents `e : Fin n → S` BELOW
`c`, i.e. `e i * c = e i`, with `∑ e i = c`, such that each `S ⧸ span {1 - e i}` carries the
same local, finite and local-hom data.

Idempotents of `A = S ⧸ span {1-c} ≅ c·S` correspond bijectively to idempotents `e` of `S`
with `e ≤ c`, i.e. `e * c = e`, via `e := c * (lift of ε)`; this sends orthogonal families to
orthogonal families and the unit `1_A` to `c`, so the completeness relation `∑ ε i = 1_A`
transports to `∑ e i = c`. Moreover `S ⧸ span {1 - e i} ≅ A ⧸ span {1 - ε i}` as `R`-algebras,
both being `≅ e_i·S = ε_i·A`, so locality, finiteness and the local-hom property transport
along that `R`-algebra isomorphism. -/
theorem orthogonalIdempotents_below_of_decomp (R : Type) [CommRing R] [IsLocalRing R] (S : Type)
    [CommRing S] [Algebra R S] (c : S) (hc : IsIdempotentElem c) (n : ℕ)
    (ε : Fin n → (S ⧸ Ideal.span {1 - c})) (hε : CompleteOrthogonalIdempotents ε)
    (hloc : ∀ i, IsLocalRing ((S ⧸ Ideal.span {1 - c}) ⧸ Ideal.span {1 - ε i}))
    (hlh : ∀ i, IsLocalHom (algebraMap R ((S ⧸ Ideal.span {1 - c}) ⧸ Ideal.span {1 - ε i})))
    (hfin : ∀ i, Module.Finite R ((S ⧸ Ideal.span {1 - c}) ⧸ Ideal.span {1 - ε i})) :
    ∃ (e : Fin n → S),
      OrthogonalIdempotents e ∧
        (∑ i, e i = c) ∧
        (∀ i, IsLocalRing (S ⧸ Ideal.span {1 - e i})) ∧
        (∀ i, IsLocalHom (algebraMap R (S ⧸ Ideal.span {1 - e i}))) ∧
        (∀ i, Module.Finite R (S ⧸ Ideal.span {1 - e i})) := by
  set q : S →+* (S ⧸ Ideal.span {1 - c}) := Ideal.Quotient.mk (Ideal.span {1 - c}) with hq
  have hcc : c * c = c := hc.eq
  have hkey : ∀ x y : S, q x = q y → c * x = c * y := by
    intro x y h
    have h2 : q (x - y) = 0 := by rw [map_sub, h, sub_self]
    rw [hq, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h2
    obtain ⟨r, hr⟩ := h2
    linear_combination c * hr - r * hcc
  have hmul : ∀ x y : S, c * x * (c * y) = c * (x * y) := fun x y => by
    linear_combination (x * y) * hcc
  have hqc1 : q c = 1 := by
    rw [hq, ← map_one (Ideal.Quotient.mk (Ideal.span {1 - c})), Ideal.Quotient.eq,
      Ideal.mem_span_singleton]
    exact ⟨-1, by ring⟩
  choose s hs using fun i => Ideal.Quotient.mk_surjective (ε i)
  -- the R-algebra equivalence for each factor
  have hequiv :
    ∀ i,
      Nonempty
        ((S ⧸ Ideal.span {1 - (c * s i)}) ≃ₐ[R]
          ((S ⧸ Ideal.span {1 - c}) ⧸ Ideal.span {1 - ε i})) := by
    intro i
    set e : S := c * s i with he
    have hle : Ideal.span {1 - c} ≤ Ideal.span {1 - e} := by
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_span_singleton]
      refine ⟨1 - c, ?_⟩
      rw [he]
      linear_combination (-s i) * hcc
    have hsup : Ideal.span {1 - c} ⊔ Ideal.span {1 - e} = Ideal.span {1 - e} :=
      sup_eq_right.mpr hle
    have hmap : Ideal.span {1 - ε i} = (Ideal.span {1 - e}).map q := by
      rw [Ideal.map_span, Set.image_singleton]
      congr 2
      rw [map_sub, map_one, he, map_mul, hqc1, one_mul, hs i]
    have hmkα :
      (Ideal.span {1 - e}).map (Ideal.Quotient.mkₐ R (Ideal.span {1 - c})) =
        Ideal.span {1 - ε i} := by
      have hcoe :
        (Ideal.Quotient.mkₐ R (Ideal.span {1 - c}) : S →+* (S ⧸ Ideal.span {1 - c})) =
          Ideal.Quotient.mk (Ideal.span {1 - c}) := by
        ext x; rfl
      rw [show
          (Ideal.span {1 - e}).map (Ideal.Quotient.mkₐ R (Ideal.span {1 - c})) =
            (Ideal.span {1 - e}).map
              (Ideal.Quotient.mkₐ R (Ideal.span {1 - c}) : S →+* (S ⧸ Ideal.span {1 - c}))
          from rfl,
        hcoe, ← hq, ← hmap]
    let f1 :
      ((S ⧸ Ideal.span {1 - c}) ⧸
          (Ideal.span {1 - e}).map (Ideal.Quotient.mkₐ R (Ideal.span {1 - c}))) ≃ₐ[R]
        S ⧸ (Ideal.span {1 - c} ⊔ Ideal.span {1 - e}) :=
      DoubleQuot.quotQuotEquivQuotSupₐ R (Ideal.span {1 - c}) (Ideal.span {1 - e})
    let f2 : (S ⧸ (Ideal.span {1 - c} ⊔ Ideal.span {1 - e})) ≃ₐ[R] (S ⧸ Ideal.span {1 - e}) :=
      Ideal.quotientEquivAlgOfEq R hsup
    let f3 :
      ((S ⧸ Ideal.span {1 - c}) ⧸ Ideal.span {1 - ε i}) ≃ₐ[R]
        ((S ⧸ Ideal.span {1 - c}) ⧸
          (Ideal.span {1 - e}).map (Ideal.Quotient.mkₐ R (Ideal.span {1 - c}))) :=
      Ideal.quotientEquivAlgOfEq R hmkα.symm
    exact ⟨(f3.trans (f1.trans f2)).symm⟩
  -- now assemble
  refine ⟨fun i => c * s i, ?_, ?_, ?_, ?_, ?_⟩
  · -- OrthogonalIdempotents
    constructor
    · intro i
      change c * s i * (c * s i) = c * s i
      rw [hmul, hkey _ (s i) (by rw [map_mul, hs i, (hε.idem i).eq])]
    · intro i j hij
      rw [hmul, hkey _ 0 (by rw [map_zero, map_mul, hs i, hs j, hε.ortho hij]), mul_zero]
  · -- sum = c
    have hsumε : ∑ i, ε i = 1 := hε.complete
    have h5 : q (∑ i, s i) = q c := by
      rw [map_sum, hqc1, ← hsumε]
      exact Finset.sum_congr rfl (fun i _ => hs i)
    have hkk := hkey _ _ h5
    rw [Finset.mul_sum] at hkk
    change ∑ i, c * s i = c
    rw [hkk, hcc]
  · -- IsLocalRing
    intro i
    have := hloc i
    exact (Classical.choice (hequiv i)).symm.toRingEquiv.isLocalRing
  · -- IsLocalHom
    intro i
    have := hloc i
    have f := Classical.choice (hequiv i)
    have hcomp :
      (f.symm.toAlgHom.toRingHom).comp
          (algebraMap R ((S ⧸ Ideal.span {1 - c}) ⧸ Ideal.span {1 - ε i})) =
        algebraMap R (S ⧸ Ideal.span {1 - (c * s i)}) := by
      ext r; simp
    have : IsLocalHom (algebraMap R ((S ⧸ Ideal.span {1 - c}) ⧸ Ideal.span {1 - ε i})) := hlh i
    have hfsym : IsLocalHom (f.symm.toAlgHom.toRingHom) :=
      inferInstanceAs
        (IsLocalHom
          (f.symm.toRingEquiv :
            ((S ⧸ Ideal.span {1 - c}) ⧸ Ideal.span {1 - ε i}) →+*
              (S ⧸ Ideal.span {1 - (c * s i)})))
    change IsLocalHom (algebraMap R (S ⧸ Ideal.span {1 - (c * s i)}))
    rw [← hcomp]
    exact RingHom.isLocalHom_comp _ _
  · -- Module.Finite
    intro i
    have := hfin i
    exact Module.Finite.equiv (Classical.choice (hequiv i)).symm.toLinearEquiv

/-- **Henselian finite decomposition** (Stacks 04GE/04GG). A module-finite algebra over a
henselian local ring is a finite product of LOCAL finite `R`-algebras. Phrased at the
idempotent level: given an idempotent `c : S` whose factor `S·c = S ⧸ span {1 - c}` is FINITE
over the henselian local ring `R`, there is a finite family `e : Fin n → S` of ORTHOGONAL
idempotents with `∑ e i = c`, so the `e i` refine `c`, each factor `S·e_i = S ⧸ span {1 - e i}`
being a LOCAL ring, FINITE over `R`, with `R → S·e_i` a LOCAL homomorphism.

Here `A := S·c` is finite over `R`, hence semilocal, and `A/rad A` is a finite product of
fields, being Artinian, which gives a complete orthogonal idempotent system in `A/rad A`. That
system lifts along the nilpotent kernel `A → A/rad A`
(`CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker`,
`IsArtinianRing.isNilpotent_jacobson_bot`), and each lifted idempotent cuts out a LOCAL factor
— a single closed point — finite over `R` and with local structure map. Finally the idempotents
of `A = S·c` are transported back to orthogonal idempotents `e_i` of `S` below `c`, using that
idempotents of `S ⧸ span {1 - c}` lift to idempotents `≤ c` in `S`. -/
@[ega "IV 18.5.9" "more general", sga "1 III 1.4" "special case"]
theorem exists_orthogonalIdempotents_isLocalRing_finite (R : Type) [CommRing R]
    [HenselianLocalRing R] (S : Type)
    [CommRing S] [Algebra R S] (c : S) (hc : IsIdempotentElem c)
    (hfin : Module.Finite R (S ⧸ Ideal.span {1 - c})) :
    ∃ (n : ℕ) (e : Fin n → S),
      OrthogonalIdempotents e ∧
        (∑ i, e i = c) ∧
        (∀ i, IsLocalRing (S ⧸ Ideal.span {1 - e i})) ∧
        (∀ i, IsLocalHom (algebraMap R (S ⧸ Ideal.span {1 - e i}))) ∧
        (∀ i, Module.Finite R (S ⧸ Ideal.span {1 - e i})) := by
  -- `A := S ⧸ span{1-c}` is finite over the henselian local `R`, so
  -- `henselian_finite_decomp_corner` gives a COMPLETE orthogonal idempotent system of `A`
  -- with local, finite and local-hom factors (the henselian content), and
  -- `orthogonalIdempotents_below_of_decomp` transports it to orthogonal idempotents below
  -- `c` in `S` summing to `c`. The case `c = 0` is the empty family, `n = 0`.
  obtain ⟨n, ε, hcoi, hloc, hlh, hfinA⟩ :=
    henselian_finite_decomp_corner R (S ⧸ Ideal.span {1 - c})
  obtain ⟨e, hortho, hsum, heloc, helh, hefin⟩ :=
    orthogonalIdempotents_below_of_decomp R S c hc n ε hcoi hloc hlh hfinA
  exact ⟨n, e, hortho, hsum, heloc, helh, hefin⟩

/-- **Core henselian idempotent decomposition** (Stacks 04GE).
For `R` henselian local and `S` of finite type over `R`, there is a number `n`, a family
`e : Fin n → S` of idempotents, and a complementary idempotent `f : S`, forming a *complete
orthogonal idempotent system* `CompleteOrthogonalIdempotents (Fin.cons f e : Fin (n+1) → S)`
— equivalently: all `e i` and `f` are idempotent and pairwise orthogonal, and
`f + ∑ i, e i = 1` — such that
* each factor `S ⧸ Ideal.span {1 - e i}` is a LOCAL ring, FINITE over `R`, with
  `R → S ⧸ Ideal.span {1 - e i}` a LOCAL ring homomorphism (these are the `A i`);
* the complementary factor `B := S ⧸ Ideal.span {1 - f}` has NO quasi-finite prime over `m`.

This is the henselian content of Stacks 04GE phrased at the level of idempotents of `S`. Its
three ingredients are:
(a) the set of primes over `m` at which `R → S` is quasi-finite is finite, these being the
    isolated points of the fibre `Spec(S/mS)`, a finite-type `κ`-algebra;
(b) at each such point the henselian property (Stacks 04GG) descends the étale-local
    idempotent of `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq` (Stacks 00UK) to
    a genuine idempotent of `S`, splitting off a finite local factor, and the
    finite-over-henselian-local structure makes these idempotents orthogonal;
(c) the complement collects exactly the non-quasi-finite points over `m`.

Concretely, `exists_isIdempotentElem_finite_and_not_quasiFiniteAt` splits off the finite-over-`R`
quasi-finite locus as an idempotent `c` whose complement `B = S·(1-c)` has no quasi-finite prime
over `m`, and `exists_orthogonalIdempotents_isLocalRing_finite` decomposes the finite factor `S·c`
into orthogonal local finite factors `e i` with `∑ e i = c`. -/
theorem exists_completeOrthogonalIdempotents_of_henselianLocalRing (R : Type) [CommRing R]
  [HenselianLocalRing R] (S : Type) [CommRing S]
    [Algebra R S] [Algebra.FiniteType R S] :
    ∃ (n : ℕ) (e : Fin n → S) (f : S),
      CompleteOrthogonalIdempotents (Fin.cons f e) ∧
        (∀ i, IsLocalRing (S ⧸ Ideal.span {1 - e i})) ∧
        (∀ i, IsLocalHom (algebraMap R (S ⧸ Ideal.span {1 - e i}))) ∧
        (∀ i, Module.Finite R (S ⧸ Ideal.span {1 - e i})) ∧
        (∀ (q : Ideal (S ⧸ Ideal.span {1 - f})) (hq : q.IsPrime),
          q.LiesOver (maximalIdeal R) → ¬@Algebra.QuasiFiniteAt R _ _ _ _ q hq) := by
  -- `exists_isIdempotentElem_finite_and_not_quasiFiniteAt` splits off the finite-over-`R`
  -- quasi-finite locus as an idempotent `c`, with complement `B = S·(1-c)` having no
  -- quasi-finite prime over `m`; `exists_orthogonalIdempotents_isLocalRing_finite` decomposes
  -- the finite factor `S·c` into orthogonal local finite factors `e i` with ∑ e i = c.
  -- Set `f := 1 - c`; then `Fin.cons f e` is a complete orthogonal idempotent
  -- system (f + ∑ e i = (1-c) + c = 1; orthogonality of f with each e_i uses
  -- e_i ≤ c, i.e. e_i * c = e_i), and `B = S ⧸ span {1 - (1 - c)}` is the complement
  -- produced by `exists_isIdempotentElem_finite_and_not_quasiFiniteAt`.
  obtain ⟨c, hc, hcfin, hB⟩ := exists_isIdempotentElem_finite_and_not_quasiFiniteAt R S
  obtain ⟨n, e, hortho, hsum, hloc, hlh, hfin⟩ :=
    exists_orthogonalIdempotents_isLocalRing_finite R S c hc hcfin
  have hcoi : CompleteOrthogonalIdempotents (Fin.cons (1 - c) e) := by
    rw [CompleteOrthogonalIdempotents.iff_ortho_complete]
    constructor
    · -- pairwise orthogonal: e_i * c = e_i (since ∑ e = c, orthogonal), so
      -- (1 - c) * e_i = 0, and distinct e_i, e_j are orthogonal by `hortho`.
      have hec : ∀ k, e k * c = e k := by
        intro k
        rw [← hsum, Finset.mul_sum]
        rw [Finset.sum_eq_single k]
        · exact hortho.idem k
        · intro b _ hbk
          exact hortho.ortho (Ne.symm hbk)
        · intro h; exact absurd (Finset.mem_univ k) h
      have h0 : ∀ k, (1 - c) * e k = 0 := fun k => by linear_combination -(hec k)
      intro i j
      refine Fin.cases ?_ (fun i' => ?_) i
      · refine Fin.cases ?_ (fun j' => ?_) j
        · intro hij; exact absurd rfl hij
        · intro _
          simp only [Fin.cons_zero, Fin.cons_succ]
          exact h0 j'
      · refine Fin.cases ?_ (fun j' => ?_) j
        · intro _
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [mul_comm]
          exact h0 i'
        · intro hij
          simp only [Fin.cons_succ]
          exact hortho.ortho (fun he => hij (congrArg Fin.succ he))
    · -- sum = 1: f + ∑ e i = (1 - c) + c = 1
      rw [Fin.sum_cons, hsum]; ring
  refine ⟨n, e, 1 - c, hcoi, hloc, hlh, hfin, ?_⟩
  -- `B = S ⧸ span {1 - (1 - c)}` is definitionally the complement of
  -- `exists_isIdempotentElem_finite_and_not_quasiFiniteAt`.
  intro q hq hover
  exact hB q hq hover

-- needed: `exists_algEquiv_pi_prod_of_henselianLocalRing` leaves unsolved goals unless the
-- residue-field algebra instances are defeq at `default` transparency
set_option backward.isDefEq.respectTransparency false in
/-- **Assembly of the henselian decomposition.** Given the complete
orthogonal idempotent system of `exists_completeOrthogonalIdempotents_of_henselianLocalRing`,
regroup the resulting product
`S ≃ₐ[R] ∏_{Fin (n+1)} (S ⧸ span {1 - ·})` into `(∏_{Fin n} A i) × B`, where the
`A i` are the local finite factors and `B` is the complement. This is pure ring
theory: `CompleteOrthogonalIdempotents.bijective_pi` /
`AlgEquiv.prodQuotientOfIsIdempotentElem` give the isomorphism, and the
properties transport. -/
theorem exists_algEquiv_pi_prod_of_henselianLocalRing (R : Type) [CommRing R] [HenselianLocalRing R]
  (S : Type) [CommRing S]
    [Algebra R S] [Algebra.FiniteType R S] :
    ∃ (n : ℕ) (A : Fin n → Type) (_ : ∀ i, CommRing (A i)) (_ : ∀ i, Algebra R (A i)) (_ :
      ∀ i, IsLocalRing (A i)) (_ : ∀ i, IsLocalHom (algebraMap R (A i))) (B : Type) (_ :
      CommRing B) (_ : Algebra R B),
      Nonempty (S ≃ₐ[R] ((Π i, A i) × B)) ∧
        (∀ i, Module.Finite R (A i)) ∧
        (∀ (q : Ideal B) (hq : q.IsPrime),
          q.LiesOver (maximalIdeal R) → ¬@Algebra.QuasiFiniteAt R B _ _ _ q hq) := by
  -- Obtain the idempotent data from the core lemma.
  obtain ⟨n, e, f, hcoi, hloc, hlh, hfin, hB⟩ :=
    exists_completeOrthogonalIdempotents_of_henselianLocalRing R S
  -- Set `A i := S ⧸ span {1 - e i}` and `B := S ⧸ span {1 - f}`. The product
  -- decomposition follows from the complete orthogonal idempotent system via
  -- `CompleteOrthogonalIdempotents.bijective_pi` over `Fin (n+1)`, regrouping the
  -- `Fin (n+1) = {f} ⊕ Fin n` index. All instance data is recorded by `hloc`,
  -- `hlh`, `hfin`, `hB`.
  refine
    ⟨n, fun i => S ⧸ Ideal.span {1 - e i}, inferInstance, inferInstance, hloc, hlh,
      S ⧸ Ideal.span {1 - f}, inferInstance, inferInstance, ?_, hfin, hB⟩
  -- All that is left is the existence (`Nonempty`) of an R-algebra equiv from the complete
  -- orthogonal idempotent system, produced by
  -- `CompleteOrthogonalIdempotents.bijective_pi` together with a `Fin.cons` regrouping.
  have hbij := hcoi.bijective_pi
  let ψ : S →ₐ[R] ((Π j : Fin n, S ⧸ Ideal.span {1 - e j}) × (S ⧸ Ideal.span {1 - f})) :=
    (AlgHom.pi (fun j => Ideal.Quotient.mkₐ R (Ideal.span {1 - e j}))).prod
      (Ideal.Quotient.mkₐ R (Ideal.span {1 - f}))
  let regroup :
    (Π i : Fin (n + 1), S ⧸ Ideal.span {1 - (Fin.cons f e : Fin (n + 1) → S) i}) ≃
      ((Π j : Fin n, S ⧸ Ideal.span {1 - e j}) × (S ⧸ Ideal.span {1 - f})) :=
    { toFun := fun g => (fun j => g j.succ, g 0)
      invFun := fun p => Fin.cons p.snd p.fst
      left_inv := fun g => by
        funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
      right_inv := fun p => by simp [Fin.cons_zero, Fin.cons_succ] }
  have hψbij : Function.Bijective ψ := by
    have :
      (ψ : S → _) =
        regroup ∘
          (RingHom.pi fun i =>
            Ideal.Quotient.mk (Ideal.span {1 - (Fin.cons f e : Fin (n + 1) → S) i})) :=
      rfl
    rw [this]
    exact regroup.bijective.comp hbij
  exact ⟨AlgEquiv.ofBijective ψ hψbij⟩

/-- **Henselian decomposition** (Stacks 04GE). A finite type algebra `S` over a henselian local
ring `(R, m, κ)` splits as an `R`-algebra isomorphism `S ≃ₐ[R] (∏ i, A i) × B`, where each `A i`
is a local ring finite over `R` with `R → A i` a local homomorphism, and `R → B` is not
quasi-finite at any prime of `B` lying over `m`.

The primes of `S` lying over `m` at which `R → S` is quasi-finite are the finitely many isolated
points of the fibre `Spec(S/mS)`. Because `R` is henselian, each of them splits off a factor
`A i` that is finite and local over `R` (Stacks 04GG), and the complementary idempotent cuts out
`B`, in which no point over `m` is quasi-finite. -/
@[ega "IV 18.5.9" "more general",
  sga "3 XI 1.11" "partial",
  sga "4 VIII 4.1" "(ii)",
  sga "7 IX 2.2.3" "special case"]
alias exists_algEquiv_pi_prod_of_henselian := exists_algEquiv_pi_prod_of_henselianLocalRing

/-! ## Main statement -/

-- needed: `exists_prod_local_purelyInseparable_not_quasiFiniteAt` cannot synthesize
-- `Algebra.IsAlgebraic (ResidueField R) (ResidueField (A i))` unless the residue-field algebra
-- structure unfolds at `default` transparency
set_option backward.isDefEq.respectTransparency false in
/-- Let `(R, m, κ)` be a strictly henselian local ring (a
henselian local ring whose residue field is separably closed) and let `S` be a
finite type `R`-algebra. Then `S` decomposes as an `R`-algebra isomorphism
`S ≃ₐ[R] (∏ i, A i) × B`, where:
* each `A i` is a local ring, finite over `R`, with `R → A i` a local
  homomorphism;
* for each `i`, the induced residue field extension `κ → κ(m_{A i})` is finite
  and purely inseparable;
* `R → B` is not quasi-finite at any prime of `B` lying over `m`. -/
@[stacks 06DD]
theorem exists_prod_local_purelyInseparable_not_quasiFiniteAt (R : Type) [CommRing R]
    [HenselianLocalRing R] [IsSepClosed (ResidueField R)]
    (S : Type) [CommRing S] [Algebra R S] [Algebra.FiniteType R S] :
    ∃ (n : ℕ) (A : Fin n → Type) (_ : ∀ i, CommRing (A i)) (_ : ∀ i, Algebra R (A i)) (_ :
      ∀ i, IsLocalRing (A i)) (_ : ∀ i, IsLocalHom (algebraMap R (A i))) (B : Type) (_ :
      CommRing B) (_ : Algebra R B),
      -- the `R`-algebra decomposition `S ≅ (∏ i, A i) × B`
      Nonempty (S ≃ₐ[R] ((Π i, A i) × B)) ∧
        -- (1) each `A i` is finite over `R` (locality and local-hom are recorded
        --     by the instance binders above)
        (∀ i, Module.Finite R (A i)) ∧
          -- (2) each residue extension `κ → κ(m_{A i})` is purely inseparable and
          --     finite, where the `κ`-algebra structure on `κ(m_{A i})` comes from
          --     the residue field map of the local homomorphism `R → A i`
          (∀ i,
              letI : Algebra (ResidueField R) (ResidueField (A i)) :=
                (ResidueField.map (algebraMap R (A i))).toAlgebra
              IsPurelyInseparable (ResidueField R) (ResidueField (A i)) ∧
                Module.Finite (ResidueField R) (ResidueField (A i))) ∧
            -- (3) `R → B` is not quasi-finite at any prime of `B` lying over `m`
            (∀ (q : Ideal B) (hq : q.IsPrime),
              q.LiesOver (maximalIdeal R) → ¬@Algebra.QuasiFiniteAt R B _ _ _ q hq) := by
  -- The substantive geometric input is the henselian decomposition
  -- (Stacks 04GE): a finite type algebra over a henselian
  -- local ring splits as a finite product of finite local `R`-algebras times a
  -- "no quasi-finite point over `m`" part; this is
  -- `exists_algEquiv_pi_prod_of_henselian`.
  -- The remaining content of 06DD — that each residue extension
  -- `κ → κ(m_{A i})` is finite and purely inseparable — is then derived from
  -- finiteness and the assumption that `κ` is separably closed.
  obtain ⟨n, A, instCR, instAlg, instLoc, instLH, B, instCRB, instAlgB, hiso, hfin, hB⟩ :=
    exists_algEquiv_pi_prod_of_henselian R S
  refine ⟨n, A, instCR, instAlg, instLoc, instLH, B, instCRB, instAlgB, hiso, hfin, ?_, hB⟩
  -- Condition (2): finiteness + pure inseparability of each residue extension.
  intro i
  let : CommRing (A i) := instCR i
  let : Algebra R (A i) := instAlg i
  let : IsLocalRing (A i) := instLoc i
  let : IsLocalHom (algebraMap R (A i)) := instLH i
  have : Module.Finite R (A i) := hfin i
  let : Algebra (ResidueField R) (ResidueField (A i)) :=
    (ResidueField.map (algebraMap R (A i))).toAlgebra
  -- `ResidueField (A i)` is finite over `R`, hence over `κ = ResidueField R`.
  have hRfin : Module.Finite R (ResidueField (A i)) := IsLocalRing.instFiniteResidueField (A i)
  have hst : IsScalarTower R (ResidueField R) (ResidueField (A i)) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change
      residue (A i) (algebraMap R (A i) x) = (ResidueField.map (algebraMap R (A i))) (residue R x)
    rw [ResidueField.map_residue]
  have hfin₂ : Module.Finite (ResidueField R) (ResidueField (A i)) :=
    Module.Finite.of_restrictScalars_finite R (ResidueField R) (ResidueField (A i))
  have : Module.Finite (ResidueField R) (ResidueField (A i)) := hfin₂
  refine ⟨?_, hfin₂⟩
  -- A finite (hence algebraic) extension of a separably closed field is purely
  -- inseparable: `Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed`.
  exact Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed

end
end
