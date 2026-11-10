module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Kaehler.Polynomial
public import StacksFrontier.LinearAlgebra.ExteriorPower.WedgeBasisDuality
public import StacksFrontier.RingTheory.FormsTrace.AnyFrame
public import StacksFrontier.RingTheory.FormsTrace.Basic
public import StacksFrontier.RingTheory.FormsTrace.Relative
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Trace maps on forms along a Frobenius-type extension

Let `Λ → A → B` be ring maps, `B` framed (or zero) over `A`, with trace maps
`Θ_Λ : Ω^•_{B/Λ} → Ω^•_{A/Λ}` on relative forms (the descent `KaehlerDifferential.relativeTrace` of
`Stacks.FormsTrace.frameTrace`, Stacks, Proposition 0FLC (3)). Suppose that `Ω_{A/Λ}` is free with
basis `dy₁, …, dy_d` and that `B` contains `p`-th roots `x_i` of the `y_i`, where `p = 0` in `B`.
This is the local shape of the relative Frobenius `F : X → X^{(p)}` of a smooth `S`-scheme of
relative dimension `d` in characteristic `p` (Stacks, Lemma 0FW2), with `A`, `B` the functions on
`X^{(p)}` and on `X`.

* The pull-back `Ω_{A/Λ} → Ω_{B/Λ}` is zero, since `d(x_i^p) = p x_i^{p-1} dx_i = 0`. As `Θ_Λ` is
  linear over the forms of `A`, every value `θ = Θ_Λ(η)` of degree `k < d` satisfies `ω ∧ θ = 0`
  for all forms `ω` of degree `d - k ≥ 1`; the wedge pairing of the free module `Ω_{A/Λ}` is
  perfect, so `θ = 0`. In degrees `k > d` the target `Ω^k_{A/Λ}` is zero. So `Θ_Λ` vanishes
  outside degree `d` (`Stacks.FormsTrace.relativeTrace_eq_zero_of_ne`).
* If moreover `Θ_Λ(x^{p-1} dx₁ ∧ ⋯ ∧ dx_d) = dy₁ ∧ ⋯ ∧ dy_d`, where `x^{p-1} = ∏ x_i^{p-1}`,
  then `Θ_Λ` is surjective in degree `d`, because `Ω^d_{A/Λ} = A · dy₁ ∧ ⋯ ∧ dy_d`
  (`Stacks.FormsTrace.relativeTrace_surjective_of_eq`).
* That value is the base change of the universal one: if `(A, B)` is a pushout of a framed pair
  `(A₀, B₀)` in which `y_i = x_i^p`, `B₀` is free of rank `p^d` over `A₀` and `Ω^d_{A₀/ℤ}` has no
  `p`-torsion, then over `A₀` one has `p^d · Θ(x^{p-1} dx) = Θ(d(x₁^p) ∧ ⋯ ∧ d(x_d^p)) =
  Trace_{B₀/A₀}(1) · dy = p^d · dy`, hence `Θ(x^{p-1} dx) = dy`, and this transfers along the
  pushout (`Stacks.FormsTrace.frameTrace_prod_pow_smul_ιMulti_D`,
  `Stacks.FormsTrace.relativeTrace_prod_pow_smul_ιMulti_D_of_isPushout`). This is the
  computation of the proof of Lemma 0FW2 in the universal case, done with property (1) of
  Lemma 0FLB and torsion-freeness instead of over `ℂ`.

## Main results

* `Stacks.FormsTrace.relativeTrace_eq_zero_of_ne`: vanishing outside degree `d`.
* `Stacks.FormsTrace.relativeTrace_surjective_of_eq`: surjectivity in degree `d`.
* `Stacks.FormsTrace.frameTrace_prod_pow_smul_ιMulti_D`: the universal value.
* `Stacks.FormsTrace.relativeTrace_prod_pow_smul_ιMulti_D_of_isPushout`: its base change.
* `Stacks.FormsTrace.exists_basis_kaehler_of_etale`: the differentials of an algebra étale over a
  polynomial ring are free on the differentials of the variables.

## References

* [Stacks Project, Tag 0FW2](https://stacks.math.columbia.edu/tag/0FW2)
* [Stacks Project, Tag 0FLC](https://stacks.math.columbia.edu/tag/0FLC)
* [Stacks Project, Tag 0FLB](https://stacks.math.columbia.edu/tag/0FLB)
-/

@[expose] public noncomputable section

open KaehlerDifferential exteriorPower
open scoped TensorProduct

universe u

namespace Stacks.FormsTrace

/-! ### Linear algebra of exterior powers -/

section ExteriorPower

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **Exterior powers above the rank vanish**: if `M` is free with a basis indexed by a finite
linearly ordered type of cardinality `< k`, then `⋀ᵏ M = 0`. -/
@[sga "6 VII 4.1" "special case"]
theorem subsingleton_exteriorPower_of_card_lt {ι : Type*} [Fintype ι] [LinearOrder ι]
    (b : Module.Basis ι R M) {k : ℕ} (hk : Fintype.card ι < k) : Subsingleton (⋀[R]^k M) := by
  have : IsEmpty (Set.powersetCard ι k) := ⟨fun s => by
    have h := Set.powersetCard.card_eq s
    have := Finset.card_le_univ s.val
    omega⟩
  exact (b.exteriorPower k).repr.toEquiv.subsingleton

/-- **The wedge pairing against the complementary degree is perfect, on the left**: if `M` is free
with a basis indexed by a finite linearly ordered type of cardinality `a + b`, and `θ ∈ ⋀ᵃ M`
satisfies `ω ∧ θ = 0` for every `ω ∈ ⋀ᵇ M`, then `θ = 0`. -/
theorem eq_zero_of_forall_wedgeMul_eq_zero {ι : Type*} [Fintype ι] [LinearOrder ι]
    (v : Module.Basis ι R M) {a b : ℕ} (hab : a + b = Fintype.card ι) (θ : ⋀[R]^a M)
    (h : ∀ ω : ⋀[R]^b M, wedgeMul b a ω θ = 0) : θ = 0 := by
  refine (wedgeBasisMap_bijective v hab).1 ?_
  rw [map_zero]
  funext s
  rw [wedgeBasisMap_apply, wedgeMul_comm, h, map_zero, smul_zero]
  rfl

/-- **The top exterior power is spanned by the wedge of a basis**: if `M` has a basis `v` indexed
by `Fin d`, every element of `⋀ᵈ M` is a multiple of `v₁ ∧ ⋯ ∧ v_d`. -/
theorem exists_eq_smul_ιMulti_basis {d : ℕ} (v : Module.Basis (Fin d) R M) (ω : ⋀[R]^d M) :
    ∃ c : R, ω = c • ιMulti R d v := by
  have := subsingleton_powersetCard_card (ι := Fin d) (n := d) (Fintype.card_fin d).symm
  let s₀ : Set.powersetCard (Fin d) d :=
    ⟨Finset.univ, by rw [Set.powersetCard.mem_iff, Finset.card_univ, Fintype.card_fin]⟩
  have : Unique (Set.powersetCard (Fin d) d) :=
    { default := s₀
      uniq := fun _ => Subsingleton.elim _ _ }
  have he : v.exteriorPower d s₀ = ιMulti R d v := by
    rw [exteriorPower.basis_apply, ιMulti_family]
    have hid := (Set.powersetCard.ofFinEmbEquiv.symm s₀).strictMono.eq_id
    congr 1
    funext i
    simp only [Function.comp_apply]
    rw [show (Set.powersetCard.ofFinEmbEquiv.symm s₀) i = i from congrFun hid i]
  have hω : ω ∈ Submodule.span R (Set.range (v.exteriorPower d)) := by
    rw [(v.exteriorPower d).span_eq]
    trivial
  rw [Set.range_unique] at hω
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hω
  refine ⟨c, ?_⟩
  rw [← hc, show (default : Set.powersetCard (Fin d) d) = s₀ from Subsingleton.elim _ _, he]

/-- On a free module over a domain, the exterior powers have no torsion by an integer which is
nonzero in the ring. -/
theorem eq_zero_of_natCast_smul_exteriorPower {ι : Type*} [LinearOrder ι] [IsDomain R]
    (v : Module.Basis ι R M) {k n : ℕ} (hn : (n : R) ≠ 0) (ω : ⋀[R]^k M)
    (h : (n : R) • ω = 0) : ω = 0 := by
  have := (v.exteriorPower k).isTorsionFree
  exact (smul_eq_zero_iff_right hn).mp h

end ExteriorPower

/-! ### Differentials of an algebra étale over a polynomial ring -/

section Kaehler

/-- **The differentials of an algebra étale over a polynomial ring are free on the differentials of
the variables.** Let `φ : Λ[X_i : i ∈ ι] → A` be an étale map of `Λ`-algebras. Then `Ω_{A/Λ}` has
the basis `dφ(X_i)`. -/
@[ega "0 20.4.13" "more general"]
theorem exists_basis_kaehler_of_etale {Λ A ι : Type*} [CommRing Λ] [CommRing A]
    [Algebra Λ A] (φ : MvPolynomial ι Λ →ₐ[Λ] A) (hφ : φ.toRingHom.Etale) :
    ∃ b : Module.Basis ι A Ω[A⁄Λ], ∀ i, b i = D Λ A (φ (MvPolynomial.X i)) := by
  let := φ.toRingHom.toAlgebra
  have : IsScalarTower Λ (MvPolynomial ι Λ) A :=
    IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  have : Algebra.FormallyEtale (MvPolynomial ι Λ) A := hφ.formallyEtale
  let e := tensorKaehlerEquivOfFormallyEtale Λ (MvPolynomial ι Λ) A
  refine ⟨((mvPolynomialBasis Λ ι).baseChange A).map e, fun i => ?_⟩
  have hX : mvPolynomialBasis Λ ι i = D Λ (MvPolynomial ι Λ) (MvPolynomial.X i) := by
    refine (mvPolynomialBasis Λ ι).repr.injective ?_
    rw [Module.Basis.repr_self, mvPolynomialBasis_repr_D_X]
  rw [Module.Basis.map_apply, Module.Basis.baseChange_apply, hX,
    tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, one_smul, map_D]
  rfl

end Kaehler

/-! ### Vanishing outside the top degree, and surjectivity in the top degree -/

section Vanishing

variable {Λ A B : Type u} [CommRing Λ] [CommRing A] [CommRing B] [Algebra Λ A] [Algebra Λ B]
  [Algebra A B] [IsScalarTower Λ A B]

/-- If the pull-back `Ω_{A/Λ} → Ω_{B/Λ}` of differentials is zero, so is the pull-back of forms
in every positive degree. -/
theorem mapExteriorPower_eq_zero (h : KaehlerDifferential.map Λ Λ A B = 0) {q : ℕ} (hq : q ≠ 0) :
    mapExteriorPower Λ A B q = 0 := by
  refine LinearMap.ext_on (ιMulti_span A q (M := Ω[A⁄Λ])) ?_
  rintro _ ⟨v, rfl⟩
  rw [mapExteriorPower_ιMulti, LinearMap.zero_apply]
  exact (ιMulti B q).toMultilinearMap.map_coord_zero ⟨0, Nat.pos_of_ne_zero hq⟩ (by simp [h])

/-- If `a` becomes the `p`-th power `x ^ p`, then `d a` pulls back to `p x ^ (p - 1) dx`. -/
private theorem kaehlerMap_D_of_eq_pow {Λ A B : Type*} [CommRing Λ] [CommRing A] [CommRing B]
    [Algebra Λ A] [Algebra Λ B] [Algebra A B] [IsScalarTower Λ A B] {p : ℕ} {a : A} {x : B}
    (h : algebraMap A B a = x ^ p) :
    KaehlerDifferential.map Λ Λ A B (D Λ A a) = ((p : B) * x ^ (p - 1)) • D Λ B x := by
  rw [map_D, h, Derivation.leibniz_pow, mul_smul, Nat.cast_smul_eq_nsmul]

/-- **The pull-back of differentials along a Frobenius-type extension is zero.** If `Ω_{A/Λ}` is
spanned by (indeed has the basis) `dy_i`, and in `B` the `y_i` become `p`-th powers `x_i ^ p` with
`p = 0` in `B`, then `Ω_{A/Λ} → Ω_{B/Λ}` vanishes: `d(x_i ^ p) = p x_i ^ (p - 1) dx_i = 0`. -/
theorem kaehlerMap_eq_zero_of_eq_pow {d p : ℕ} (b : Module.Basis (Fin d) A Ω[A⁄Λ])
    (y : Fin d → A) (hb : ∀ i, b i = D Λ A (y i)) (x : Fin d → B)
    (hxy : ∀ i, algebraMap A B (y i) = x i ^ p) (hp : (p : B) = 0) :
    KaehlerDifferential.map Λ Λ A B = 0 := by
  refine b.ext fun i => ?_
  rw [hb, LinearMap.zero_apply, kaehlerMap_D_of_eq_pow (hxy i), hp, zero_mul, zero_smul]

variable (Θ : ∀ n : ℕ, ⋀[B]^n Ω[B⁄ℤ] →ₗ[A] ⋀[A]^n Ω[A⁄ℤ]) (hΘ : IsWedgeLinear A B Θ)

/-- **Below the top degree the trace on relative forms vanishes** when `Ω_{A/Λ}` is free of
rank `d` and the pull-back `Ω_{A/Λ} → Ω_{B/Λ}` is zero: a value `θ` of degree `k < d` satisfies
`ω ∧ θ = Θ_Λ(f^*ω ∧ η) = 0` for every `ω` of degree `d - k ≥ 1`, so `θ = 0` by perfectness of the
wedge pairing. -/
theorem relativeTrace_eq_zero_of_lt {d : ℕ} (v : Module.Basis (Fin d) A Ω[A⁄Λ])
    (hmap : KaehlerDifferential.map Λ Λ A B = 0) {k : ℕ} (hk : k < d) :
    relativeTrace Λ Θ hΘ k = 0 := by
  refine LinearMap.ext fun η => ?_
  refine eq_zero_of_forall_wedgeMul_eq_zero v (a := k) (b := d - k)
    (by rw [Fintype.card_fin]; omega) _ fun ω => ?_
  rw [← relativeTrace_wedgeMul Λ Θ hΘ, mapExteriorPower_eq_zero hmap (by omega)]
  simp

/-- **Above the rank the forms vanish**: if `Ω_{A/Λ}` is free of rank `d`, the trace on relative
forms is zero in every degree `k > d`, its target being zero. -/
theorem relativeTrace_eq_zero_of_gt {d : ℕ} (v : Module.Basis (Fin d) A Ω[A⁄Λ]) {k : ℕ}
    (hk : d < k) : relativeTrace Λ Θ hΘ k = 0 := by
  have := subsingleton_exteriorPower_of_card_lt v (k := k) (by rwa [Fintype.card_fin])
  exact LinearMap.ext fun _ => Subsingleton.elim _ _

/-- **The trace on relative forms vanishes outside the top degree** when `Ω_{A/Λ}` is free of
rank `d` and the pull-back `Ω_{A/Λ} → Ω_{B/Λ}` is zero. -/
theorem relativeTrace_eq_zero_of_ne {d : ℕ} (v : Module.Basis (Fin d) A Ω[A⁄Λ])
    (hmap : KaehlerDifferential.map Λ Λ A B = 0) {k : ℕ} (hk : k ≠ d) :
    relativeTrace Λ Θ hΘ k = 0 := by
  rcases Nat.lt_or_gt_of_ne hk with h | h
  · exact relativeTrace_eq_zero_of_lt Θ hΘ v hmap h
  · exact relativeTrace_eq_zero_of_gt Θ hΘ v h

/-- **In the top degree the trace on relative forms is surjective** as soon as it hits the wedge
`v₁ ∧ ⋯ ∧ v_d` of a basis of `Ω_{A/Λ}`: the top forms are the multiples of that wedge, and the
trace is `A`-linear. -/
theorem relativeTrace_surjective_of_eq {d : ℕ} (v : Module.Basis (Fin d) A Ω[A⁄Λ])
    (η₀ : ⋀[B]^d Ω[B⁄Λ]) (h : relativeTrace Λ Θ hΘ d η₀ = ιMulti A d v) :
    Function.Surjective (relativeTrace Λ Θ hΘ d) := by
  intro ω
  obtain ⟨c, rfl⟩ := exists_eq_smul_ιMulti_basis v ω
  exact ⟨c • η₀, by rw [map_smul, h]⟩

end Vanishing

/-! ### The value on `x^{p-1} dx₁ ∧ ⋯ ∧ dx_d` -/

section Universal

variable {A₀ B₀ : Type u} [CommRing A₀] [CommRing B₀] [Algebra A₀ B₀]

/-- The trace of `1` in a free algebra with a basis indexed by `ι` is `#ι`. -/
theorem trace_one_of_basis [Module.Finite A₀ B₀] [Module.Free A₀ B₀] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι A₀ B₀) : trace A₀ B₀ 1 = Fintype.card ι := by
  classical
  rw [trace, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_one,
    Stacks.Discriminant.finiteProjectiveTrace_eq_trace, Module.End.one_eq_id,
    LinearMap.trace_eq_matrix_trace A₀ b, LinearMap.toMatrix_id, Matrix.trace_one]

/-- **The universal value of the trace on `x^{p-1} dx`.** Let `B₀` be a framed (or zero) finite
free `A₀`-algebra in which `y_i = x_i ^ p` (`i = 1, …, d`), with `Trace_{B₀/A₀}(1) = p^d` and no
`p^d`-torsion in `Ω^d_{A₀/ℤ}`. Then `Θ(x₁^{p-1} ⋯ x_d^{p-1} dx₁ ∧ ⋯ ∧ dx_d) = dy₁ ∧ ⋯ ∧ dy_d`:
indeed `d(x_i ^ p) = p x_i ^ (p - 1) dx_i`, so the pull-back of `dy₁ ∧ ⋯ ∧ dy_d` is
`p^d · x^{p-1} dx`, which `Θ` sends to `Trace(1) · dy = p^d · dy` (Lemma 0FLB (1)). -/
theorem frameTrace_prod_pow_smul_ιMulti_D [Module.Finite A₀ B₀] [Module.Free A₀ B₀]
    (hB₀ : Subsingleton B₀ ∨ Nonempty (AnyFrame A₀ B₀)) {p d : ℕ} (y : Fin d → A₀)
    (x : Fin d → B₀) (hxy : ∀ i, algebraMap A₀ B₀ (y i) = x i ^ p)
    (htr : trace A₀ B₀ 1 = ((p ^ d : ℕ) : A₀))
    (htors : ∀ ω : ⋀[A₀]^d Ω[A₀⁄ℤ], ((p ^ d : ℕ) : A₀) • ω = 0 → ω = 0) :
    frameTrace A₀ B₀ d ((∏ i, x i ^ (p - 1)) • ιMulti B₀ d (fun i => D ℤ B₀ (x i))) =
      ιMulti A₀ d (fun i => D ℤ A₀ (y i)) := by
  set z := (∏ i, x i ^ (p - 1)) • ιMulti B₀ d (fun i => D ℤ B₀ (x i)) with hz
  have hpull : formsMap A₀ B₀ d (ιMulti A₀ d fun i => D ℤ A₀ (y i)) =
      algebraMap A₀ B₀ ((p ^ d : ℕ) : A₀) • z := by
    simp only [formsMap_ιMulti, fun i : Fin d => kaehlerMap_D_of_eq_pow (Λ := ℤ) (hxy i)]
    rw [AlternatingMap.map_smul_univ, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, mul_smul, hz, map_natCast, Nat.cast_pow]
  have h1 := isFormsTrace_frameTrace hB₀ d 1 (ιMulti A₀ d fun i => D ℤ A₀ (y i))
  rw [one_smul, hpull, htr, algebraMap_smul, map_smul] at h1
  refine sub_eq_zero.mp (htors _ ?_)
  rw [smul_sub, h1, sub_self]

end Universal

section Pushout

variable {Λ A B : Type u} [CommRing Λ] [CommRing A] [CommRing B] [Algebra Λ A] [Algebra Λ B]
  [Algebra A B] [IsScalarTower Λ A B]
  {A₀ B₀ : Type u} [CommRing A₀] [CommRing B₀] [Algebra A₀ B₀] [Algebra A₀ A] [Algebra B₀ B]
  [Algebra A₀ B] [IsScalarTower A₀ A B] [IsScalarTower A₀ B₀ B] [Algebra.IsPushout A₀ B₀ A B]

/-- **The value on `x^{p-1} dx` is compatible with base change**, and descends to relative
forms: if `(A, B)` is a pushout of `(A₀, B₀)`, both framed or zero, and over `A₀` the trace sends
`x^{p-1} dx₁ ∧ ⋯ ∧ dx_d` to `dy₁ ∧ ⋯ ∧ dy_d`, then over `A` the trace on forms relative to any
`Λ` sends the image `x'^{p-1} dx'₁ ∧ ⋯ ∧ dx'_d` to `dy'₁ ∧ ⋯ ∧ dy'_d`. -/
theorem relativeTrace_prod_pow_smul_ιMulti_D_of_isPushout
    (hB₀ : Subsingleton B₀ ∨ Nonempty (AnyFrame A₀ B₀))
    (hB : Subsingleton B ∨ Nonempty (AnyFrame A B)) {p d : ℕ} (y : Fin d → A₀) (x : Fin d → B₀)
    (h₀ : frameTrace A₀ B₀ d ((∏ i, x i ^ (p - 1)) • ιMulti B₀ d (fun i => D ℤ B₀ (x i))) =
      ιMulti A₀ d (fun i => D ℤ A₀ (y i))) :
    relativeTrace Λ (frameTrace A B) (isWedgeLinear_frameTrace hB) d
        ((∏ i, algebraMap B₀ B (x i) ^ (p - 1)) •
          ιMulti B d (fun i => D Λ B (algebraMap B₀ B (x i)))) =
      ιMulti A d (fun i => D Λ A (algebraMap A₀ A (y i))) := by
  have hz : formsMap B₀ B d ((∏ i, x i ^ (p - 1)) • ιMulti B₀ d (fun i => D ℤ B₀ (x i))) =
      (∏ i, algebraMap B₀ B (x i) ^ (p - 1)) •
        ιMulti B d (fun i => D ℤ B (algebraMap B₀ B (x i))) := by
    rw [map_smulₛₗ, formsMap_ιMulti, map_prod]
    simp only [map_pow, map_D]
  have h := frameTrace_formsMap_of_isPushout A B hB₀ hB d
    ((∏ i, x i ^ (p - 1)) • ιMulti B₀ d (fun i => D ℤ B₀ (x i)))
  rw [hz, h₀, formsMap_ιMulti] at h
  simp only [map_D] at h
  have hrel : (∏ i, algebraMap B₀ B (x i) ^ (p - 1)) •
        ιMulti B d (fun i => D Λ B (algebraMap B₀ B (x i))) =
      absoluteToRelative Λ B d ((∏ i, algebraMap B₀ B (x i) ^ (p - 1)) •
        ιMulti B d (fun i => D ℤ B (algebraMap B₀ B (x i)))) := by
    rw [map_smul, absoluteToRelative_ιMulti_D]
  rw [hrel, relativeTrace_absoluteToRelative, h, absoluteToRelative_ιMulti_D]

end Pushout

end Stacks.FormsTrace

end
