module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.CodimensionClasses
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.CodimensionGysinRational
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.DivisorChernClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClassCycleClassMap
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilData

/-!
# The cycle class map of a Weil III theory on the integral Chow groups

Tag 0FIF states the cycle class map of a Weil cohomology theory built from Chern classes as a
graded ring homomorphism `γ : CH^*(X) ⟶ ⨁_{i ≥ 0} H^{2i}(X)(i)` on the *integral* Chow ring
`CH^*(X) = ⨁_i CH^i(X)`, `CH^i(X) = ∏_d CH_{d-i}(X_d)` (Chow Homology, Section 0FE2), compatible
with the Gysin pullbacks, with `γ(ch(α)) = ch^H(α)` read through `CH^*(X) ⟶ CH^*(X) ⊗ 𝐐`.
`StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClassCycleClassMap` constructs `γ` on
`CH^*(X) ⊗ 𝐐`; this file restricts it to the integral classes, degree by degree.

## Main definitions

* `Stacks.WeilCohomology.FirstChernClassData.IsCohomologicalChernCharacter.codimensionCycleClass`
  — `γ : CH^i(X) ⟶ H^{2i}(X)(i)`.

## Main results

* `codimensionCycleClass_mem` — `γ` lands in `H^{2i}(X)(i)`.
* `codimensionCycleClass_codimensionIntersectionProduct` — `γ(α · β) = γ(α) ∪ γ(β)` for the
  intersection product of Chow Homology, Section 0FC0 (through Stacks 0FFF).
* `codimensionCycleClass_fundamentalClass` — `γ([X]) = 1`.
* `codimensionCycleClass_codimensionGysin` — `γ(f^! β) = f^* γ(β)`, axiom (C)(a) in this setting.
* `codimensionCycleClass_eq_nsmul` — `γ(ch(α)) = ch^H(α)`, read through `CH ⟶ CH ⊗ 𝐐`.
* `codimensionCycleClass_divisor` — `γ([D]) = c₁^H(𝒪_X(D))` for an effective Cartier divisor `D`.
* `Stacks.WeilCohomology.FirstChernClassData.existsUnique_codimensionCycleClass` — **Tag 0FIF on
  the integral Chow ring**, derived from the rational form.

## References

* [Stacks Project, Tag 0FIF](https://stacks.math.columbia.edu/tag/0FIF)
* [Stacks Project, Tag 0FFF](https://stacks.math.columbia.edu/tag/0FFF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow
open scoped TensorProduct

universe u w

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme

/-- The underlying scheme of a smooth projective scheme over `k` is quasi-compact. -/
instance compactSpace_left {k : Type u} [Field k] (X : (SmoothProjectiveScheme k).FullSubcategory) :
    CompactSpace X.obj.left :=
  SmoothProjectiveScheme.compactSpace X

namespace FirstChernClassData

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] {𝔇 : FirstChernClassData k F}
  {ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
    VectorBundleKZero ((toScheme k).obj X) → ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n}

omit [CharZero F] in
/-- `exp(x)` has degree-one part `x`. -/
theorem expTw_one (X : (SmoothProjectiveScheme k).FullSubcategory)
    (x : tateTwist F 𝔇.tate (𝔇.H X) 1) :
    𝔇.expTw X x 1 = x := by
  apply (𝔇.κ X 1).injective
  have h1 := 𝔇.κ_twistPow X x 1
  rw [pow_one] at h1
  rwa [expTw, map_smul, Nat.factorial_one, Nat.cast_one, inv_one, one_smul]

namespace IsCohomologicalChernCharacter

variable (h : 𝔇.IsCohomologicalChernCharacter ch)

/-- The cycle class map on `CH^*(X) ⊗ 𝐐` as an additive homomorphism. -/
private def cycleClassAddHom (X : (SmoothProjectiveScheme k).FullSubcategory) :
    smoothRationalChowRing (k := k) X.obj.hom →+
      ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n :=
  AddMonoidHom.mk' (h.cycleClassMap X) (h.cycleClassMap_add X)

/-- The cycle class map on `CH^*(X) ⊗ 𝐐` sends `0` to `0`. -/
private theorem cycleClassMap_zero (X : (SmoothProjectiveScheme k).FullSubcategory) :
    h.cycleClassMap X 0 = 0 :=
  map_zero (h.cycleClassAddHom X)

/-- **The cycle class map `γ : CH^i(X) ⟶ H^{2i}(X)(i)` on the integral Chow group** of
codimension `i`: the degree-`i` component of the cycle class map on `CH^*(X) ⊗ 𝐐` at the image of
a class of `CH^i(X) = ∏_d CH_{d-i}(X_d)`. -/
def codimensionCycleClass (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℕ) :
    codimensionChowGroup k X.obj.hom i →+ tateTwist F 𝔇.tate (𝔇.H X) i where
  toFun a := h.cycleClassMap X
    (smoothChowEquiv X.obj.hom (codimensionToRationalChow k X.obj.hom i a)) i
  map_zero' := by rw [map_zero, map_zero, h.cycleClassMap_zero, Pi.zero_apply]
  map_add' a b := by
    rw [map_add, map_add, h.cycleClassMap_add, Pi.add_apply]

/-- `γ(a)` is the degree-`i` component of the cycle class map on `CH^*(X) ⊗ 𝐐` at the image of
`a ∈ CH^i(X)`. -/
theorem codimensionCycleClass_apply (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℕ)
    (a : codimensionChowGroup k X.obj.hom i) :
    h.codimensionCycleClass X i a = h.cycleClassMap X
      (smoothChowEquiv X.obj.hom (codimensionToRationalChow k X.obj.hom i a)) i :=
  rfl

/-- The image of a class of `CH^i(X)` in `CH^*(X) ⊗ 𝐐` has codimension `i`. -/
theorem symm_smoothChowEquiv_mem (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℕ)
    (a : codimensionChowGroup k X.obj.hom i) :
    (smoothChowEquiv X.obj.hom).symm
        (smoothChowEquiv X.obj.hom (codimensionToRationalChow k X.obj.hom i a)) ∈
      codimensionChowSubmodule (fieldChowSituation k) X.obj.hom i := by
  rw [LinearEquiv.symm_apply_apply]
  exact codimensionToRationalChow_mem_codimensionChowSubmodule X.obj.hom i a

/-- **`γ` lands in `H^{2i}(X)(i)`.** -/
theorem codimensionCycleClass_mem (hA1 : 𝔇.CoproductAxiom) (hA3 : 𝔇.ProjectiveBundleAxiom)
    (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℕ)
        (a : codimensionChowGroup k X.obj.hom i) :
    h.codimensionCycleClass X i a ∈
      LinearMap.range (tateTwistMap (L := 𝔇.tate) (𝔇.grade X (2 * (i : ℤ))).subtype i) :=
  (h.cycleClassMap_mem hA1 hA3 X _ (symm_smoothChowEquiv_mem X i a)).1

/-- The cycle class map on `CH^*(X) ⊗ 𝐐` of the image of a class of `CH^i(X)` is concentrated in
degree `i`. -/
theorem cycleClassMap_eq_zero_of_ne (hA1 : 𝔇.CoproductAxiom) (hA3 : 𝔇.ProjectiveBundleAxiom)
    (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℕ)
        (a : codimensionChowGroup k X.obj.hom i) {n : ℕ}
    (hn : n ≠ i) :
    h.cycleClassMap X (smoothChowEquiv X.obj.hom (codimensionToRationalChow k X.obj.hom i a)) n =
      0 :=
  (h.cycleClassMap_mem hA1 hA3 X _ (symm_smoothChowEquiv_mem X i a)).2 n hn

/-- **`γ` is multiplicative**: `γ(α · β) = γ(α) ∪ γ(β)` for `α ∈ CH^i(X)`, `β ∈ CH^j(X)` and the
intersection product of Chow Homology, Section 0FC0. Through Stacks 0FFF the product is that of
Section 0FEX on `CH^*(X) ⊗ 𝐐`, where `γ` is multiplicative for the cup product of
`∏_n H^{2n}(X)(n)`; in degree `i + j` only the term `γ(α)_i ∪ γ(β)_j` survives. -/
theorem codimensionCycleClass_codimensionIntersectionProduct (hA1 : 𝔇.CoproductAxiom)
    (hA3 : 𝔇.ProjectiveBundleAxiom) (X : (SmoothProjectiveScheme k).FullSubcategory) (i j : ℕ)
    (a : codimensionChowGroup k X.obj.hom i) (b : codimensionChowGroup k X.obj.hom j) :
    h.codimensionCycleClass X (i + j) (codimensionIntersectionProduct k X.obj.hom i j a b) =
      tateCup 𝔇.finrank_tate (𝔇.cup X) i j (i + j) (by push_cast; ring)
        (h.codimensionCycleClass X i a) (h.codimensionCycleClass X j b) := by
  have hprod : codimensionToRationalChow k X.obj.hom ((i + j : ℕ) : ℤ)
      (codimensionIntersectionProduct k X.obj.hom i j a b) =
      rationalIntersectionProduct (isRegular_of_smooth_over_field X.obj.hom)
        (exists_bounds_relativeDimension_fieldChowSituation k X.obj.hom)
        (codimensionToRationalChow k X.obj.hom i a)
        (codimensionToRationalChow k X.obj.hom j b) := by
    have h1 := codimensionRationalChowEquiv_codimensionIntersectionProduct k X.obj.hom i j 1 1 a b
    rwa [codimensionRationalChowEquiv_tmul_of, codimensionRationalChowEquiv_tmul_of,
      codimensionRationalChowEquiv_tmul_of, one_mul, one_smul, one_smul, one_smul] at h1
  rw [codimensionCycleClass_apply, hprod]
  show h.cycleClassMap X (smoothChowEquiv X.obj.hom (codimensionToRationalChow k X.obj.hom i a) *
    smoothChowEquiv X.obj.hom (codimensionToRationalChow k X.obj.hom j b)) (i + j) = _
  rw [h.cycleClassMap_mul, cupConv, Finset.sum_eq_single ⟨i, by omega⟩]
  · show tateCup 𝔇.finrank_tate (𝔇.cup X) i ((i + j - i : ℕ) : ℤ) ((i + j : ℕ) : ℤ) _
      (h.codimensionCycleClass X i a) (h.cycleClassMap X (smoothChowEquiv X.obj.hom
        (codimensionToRationalChow k X.obj.hom j b)) (i + j - i)) = _
    have key : ∀ (m : ℕ) (_ : m = j) (hk : (i : ℤ) + (m : ℤ) = ((i + j : ℕ) : ℤ))
        (y : ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n),
        tateCup 𝔇.finrank_tate (𝔇.cup X) i m ((i + j : ℕ) : ℤ) hk
            (h.codimensionCycleClass X i a) (y m) =
          tateCup 𝔇.finrank_tate (𝔇.cup X) i j ((i : ℤ) + (j : ℤ)) (by ring)
            (h.codimensionCycleClass X i a) (y j) := by
      rintro m rfl hk y
      rfl
    exact key _ (by omega) _ _
  · intro p _ hp
    rw [h.cycleClassMap_eq_zero_of_ne hA1 hA3 X i a (fun hpi => hp (Fin.ext hpi)), map_zero,
      LinearMap.zero_apply]
  · exact fun hmem => absurd (Finset.mem_univ _) hmem

/-- **`γ([X]) = 1`** for the fundamental class `[X] = ∑_d [X_d]_d ∈ CH^0(X)`. -/
theorem codimensionCycleClass_fundamentalClass (X : (SmoothProjectiveScheme k).FullSubcategory) :
    h.codimensionCycleClass X 0 (fundamentalClass X) = 𝔇.unitTw X := by
  rw [codimensionCycleClass_apply]
  have h1 : smoothChowEquiv X.obj.hom (codimensionToRationalChow k X.obj.hom ((0 : ℕ) : ℤ)
      (fundamentalClass X)) = 1 := by
    rw [RationalIntersectionRing.one_eq]
    exact congrArg _ (codimensionToRationalChow_fundamentalClass X.obj.hom)
  rw [h1, h.cycleClassMap_one]
  rfl

/-- `γ` is additive on finite sums. -/
theorem cycleClassMap_sum (X : (SmoothProjectiveScheme k).FullSubcategory) {ι : Type*}
    (s : Finset ι)
    (α : ι → smoothRationalChowRing (k := k) X.obj.hom) :
    h.cycleClassMap X (∑ t ∈ s, α t) = ∑ t ∈ s, h.cycleClassMap X (α t) :=
  map_sum (h.cycleClassAddHom X) α s

/-- **The degree-`p` part of `γ(ch(α') ∩ [X])` is `γ(ch_p(α') ∩ [X])`**: the components
`ch_q(α') ∩ [X]` of `ch(α') ∩ [X]` lie in `CH^q(X) ⊗ 𝐐`, where `γ` is concentrated in degree
`q`. -/
theorem cycleClassMap_rationalChernCharacterComponentCap (hA1 : 𝔇.CoproductAxiom)
    (hA3 : 𝔇.ProjectiveBundleAxiom) (X : (SmoothProjectiveScheme k).FullSubcategory)
    (x : ℚ ⊗[ℤ] VectorBundleKZero ((toScheme k).obj X)) (p : ℕ) :
    h.cycleClassMap X (smoothChowEquiv X.obj.hom
        (rationalChernCharacterComponentCap (fieldChowSituation k) X.obj.hom p x
          (rationalFundamentalClass (fieldChowSituation k) X.obj.hom))) p =
      h.cycleClassMap X (rationalChernCharacterAlgEquiv (isRegular_of_smooth_over_field X.obj.hom)
        (exists_bounds_relativeDimension_fieldChowSituation k X.obj.hom) x) p := by
  classical
  obtain ⟨lo, hi, hb⟩ := exists_bounds_relativeDimension_fieldChowSituation k X.obj.hom
  have hsum := rationalChernCharacterCap_eq_sum (fieldChowSituation k) X.obj.hom hb
    (N := max (hi - lo).toNat p) (by omega)
  have hmem : ∀ q : ℕ, (smoothChowEquiv X.obj.hom).symm (smoothChowEquiv X.obj.hom
      (rationalChernCharacterComponentCap (fieldChowSituation k) X.obj.hom q x
        (rationalFundamentalClass (fieldChowSituation k) X.obj.hom))) ∈
      codimensionChowSubmodule (fieldChowSituation k) X.obj.hom q := fun q => by
    rw [LinearEquiv.symm_apply_apply, rationalChernCharacterComponentCap_apply]
    have H := rationalChowCap_mem_codimensionChowSubmodule_add (fieldChowSituation k)
      X.obj.hom _ (isCohenMacaulay_of_isRegular (isRegular_of_smooth_over_field X.obj.hom)) q
      (rationalChernCharacterVectorBundle (fieldChowSituation k) X.obj.hom x q)
      (directSumRight_one_tmul_totalFundamentalClass_mem_codimensionChowSubmodule_zero
        (fieldChowSituation k) X.obj.hom)
    rwa [zero_add] at H
  rw [rationalChernCharacterAlgEquiv_apply, hsum, LinearMap.sum_apply, LinearMap.sum_apply,
    map_sum, h.cycleClassMap_sum, Finset.sum_apply,
    Finset.sum_eq_single_of_mem p (by rw [Finset.mem_range]; omega)]
  intro q _ hq
  exact (h.cycleClassMap_mem hA1 hA3 X _ (hmem q)).2 p (Ne.symm hq)

/-- `γ` commutes with multiplication by natural numbers. -/
theorem cycleClassMap_nsmul (X : (SmoothProjectiveScheme k).FullSubcategory) (m : ℕ)
    (α : smoothRationalChowRing (k := k) X.obj.hom) :
    h.cycleClassMap X (m • α) = m • h.cycleClassMap X α :=
  map_nsmul (h.cycleClassAddHom X) m α

/-- **The defining equation of Tag 0FIF on integral classes**: `γ(ch(α)) = ch^H(α)` read through
`CH^*(X) ⟶ CH^*(X) ⊗ 𝐐`. If a class `a ∈ CH^n(X)` has image `m · (ch_n(α) ∩ [X])` in
`CH^*(X) ⊗ 𝐐`, then `γ(a) = m · ch^H_n(α)`. -/
theorem codimensionCycleClass_eq_nsmul (hA1 : 𝔇.CoproductAxiom) (hA3 : 𝔇.ProjectiveBundleAxiom)
    (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℕ)
        (a : codimensionChowGroup k X.obj.hom n)
    (α : VectorBundleKZero ((toScheme k).obj X)) (m : ℕ)
    (ha : codimensionToRationalChow k X.obj.hom n a =
      m • rationalChernCharacterComponentCap (fieldChowSituation k) X.obj.hom n (1 ⊗ₜ[ℤ] α)
        (rationalFundamentalClass (fieldChowSituation k) X.obj.hom)) :
    h.codimensionCycleClass X n a = m • ch X α n := by
  rw [codimensionCycleClass_apply, ha, map_nsmul, h.cycleClassMap_nsmul, Pi.smul_apply,
    h.cycleClassMap_rationalChernCharacterComponentCap hA1 hA3,
    h.cycleClassMap_rationalChernCharacterAlgEquiv]

/-- **`γ` is compatible with the Gysin pullbacks**: `γ(f^! β) = f^* γ(β)` for a morphism
`f : X ⟶ Y` of smooth projective schemes and `β ∈ CH^i(Y)`, `f^!` the Gysin map of Chow
Homology, Tag 0FF3, graded by codimension. Rationally `f^!` is the Gysin map of
`CH^*(-) ⊗ 𝐐` (`Stacks.Chow.codimensionToRationalChow_codimensionGysin`), with which `γ` is
compatible. -/
theorem codimensionCycleClass_codimensionGysin {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y)
    (i : ℕ) (b : codimensionChowGroup k Y.obj.hom i) :
    h.codimensionCycleClass X i (codimensionGysin X.obj.hom Y.obj.hom (w f) i b) =
      𝔇.pullTw f i (h.codimensionCycleClass Y i b) := by
  rw [codimensionCycleClass_apply, codimensionCycleClass_apply,
    codimensionToRationalChow_codimensionGysin, ← h.cycleClassMap_smoothGysinRingHom f,
    smoothGysinRingHom_equiv]

/-- **`γ([D]) = c₁^H(𝒪_X(D))`** for an effective Cartier divisor `D` on a smooth projective `X`,
`[D] ∈ CH^1(X)` the class of the closed subscheme `D`. Indeed `ch_1(𝒪_X(D)) ∩ [X] = [D]` in
`CH^*(X) ⊗ 𝐐` (Stacks 0FA9), so `γ([D]) = ch^H_1(𝒪_X(D))`, the degree-one part of
`exp(c₁^H(𝒪_X(D)))`. -/
theorem codimensionCycleClass_divisor (hA1 : 𝔇.CoproductAxiom) (hA3 : 𝔇.ProjectiveBundleAxiom)
    (X : (SmoothProjectiveScheme k).FullSubcategory) (D : X.obj.left.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] :
    h.codimensionCycleClass X 1 (closedSubschemeClass X.obj.hom D.subschemeι 1) =
      𝔇.c₁ X (picardClassOf _ (Stacks.Divisors.divisorSheaf D)
        (Stacks.Divisors.isInvertible_divisorSheaf D)) := by
  have hD := codimensionToRationalChow_closedSubschemeClass_eq_chernCharacterCap X.obj.hom D
  rw [h.codimensionCycleClass_eq_nsmul hA1 hA3 X 1 _ (VectorBundleKZero.classOf _
    (Stacks.Divisors.divisorSheaf D)) 1 (by rwa [one_smul]), one_smul]
  exact (congrFun (h.2.2.2.2.2 X _ (Stacks.Divisors.isInvertible_divisorSheaf D)) 1).trans
    (expTw_one X _)

end IsCohomologicalChernCharacter

/-- **Stacks Project, Tag 0FIF, on the integral Chow ring.** Assume given (D0), (D1), (D2')
satisfying axioms (A1), (A2), (A3) and (A4). There is a unique rule which assigns to every smooth
projective `X` over `k` a graded ring homomorphism

  `γ : CH^*(X) ⟶ ⨁_{i ≥ 0} H^{2i}(X)(i)`

compatible with pullbacks such that `γ(ch(α)) = ch^H(α)` for `α ∈ K₀(Vect(X))`.

`CH^*(X) = ⨁_i CH^i(X)` is the integral Chow ring, `CH^i(X) = ∏_d CH_{d-i}(X_d)` with the
intersection product of Chow Homology, Section 0FC0, and unit the fundamental class `[X]`;
pullback is the Gysin map `f^!` of Chow Homology, Tag 0FF3, graded by codimension. A graded ring
homomorphism is given by its components `γ : CH^i(X) ⟶ H^{2i}(X)(i)`: additive, multiplicative
for the cup product, and sending `[X]` to `1`. The equation `γ(ch(α)) = ch^H(α)` involves the
rational class `ch(α) ∩ [X] ∈ CH^*(X) ⊗ 𝐐` and is read through `CH^*(X) ⟶ CH^*(X) ⊗ 𝐐`: the
`𝐐`-linear extension `γ_𝐐` of `γ` to `CH^*(X) ⊗ 𝐐` (an additive map agreeing with `γ` on the
integral classes) satisfies `γ_𝐐(ch(α) ∩ [X]) = ch^H(α)`, `ch^H` being the cohomological Chern
character of Tag 0FIE. -/
@[stacks 0FIF "the integral form: existence and uniqueness, under exactly (D0), (D1), (D2') and \
(A1)-(A4), of γ on the integral Chow groups CH^i(X) = prod_d CH_{d-i}(X_d) of every smooth \
projective X over k, with values in H^{2i}(X)(i), additive, multiplicative for the intersection \
product of 0FC0 and the cup product, γ([X]) = 1, compatible with the codimension-graded Gysin \
pullbacks f^! of 0FF3, and with γ(ch(α)) = ch^H(α) read through CH -> CH ⊗ Q (the Q-linear \
extension of γ sends ch(α) ∩ [X] to ch^H(α), ch^H as in 0FIE). Derived from the rational form \
existsUnique_cycleClassMap; nothing is assumed"]
theorem existsUnique_codimensionCycleClass (hA1 : 𝔇.CoproductAxiom) (hA2 : 𝔇.PullbackAxiom)
    (hA3 : 𝔇.ProjectiveBundleAxiom) (hA4 : 𝔇.DivisorAxiom) :
    ∃! γ : ∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℕ),
        codimensionChowGroup k X.obj.hom i →+ tateTwist F 𝔇.tate (𝔇.H X) i,
      (∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℕ)
          (a : codimensionChowGroup k X.obj.hom i),
        γ X i a ∈
          LinearMap.range (tateTwistMap (L := 𝔇.tate) (𝔇.grade X (2 * (i : ℤ))).subtype i)) ∧
      (∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (i j : ℕ)
          (a : codimensionChowGroup k X.obj.hom i)
        (b : codimensionChowGroup k X.obj.hom j),
        γ X (i + j) (codimensionIntersectionProduct k X.obj.hom i j a b) =
          tateCup 𝔇.finrank_tate (𝔇.cup X) i j (i + j) (by push_cast; ring) (γ X i a)
            (γ X j b)) ∧
      (∀ X : (SmoothProjectiveScheme k).FullSubcategory, γ X 0 (fundamentalClass X) = 𝔇.unitTw X) ∧
      (∀ {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (i : ℕ)
        (b : codimensionChowGroup k Y.obj.hom i),
        γ X i (codimensionGysin X.obj.hom Y.obj.hom (w f) i b) = 𝔇.pullTw f i (γ Y i b)) ∧
      ∀ ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
          VectorBundleKZero ((toScheme k).obj X) → ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n,
        𝔇.IsCohomologicalChernCharacter ch →
        ∃ γℚ : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
            smoothRationalChowRing (k := k) X.obj.hom → ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n,
          (∀ (X : (SmoothProjectiveScheme k).FullSubcategory)
              (α β : smoothRationalChowRing (k := k) X.obj.hom),
            γℚ X (α + β) = γℚ X α + γℚ X β) ∧
          (∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℕ)
              (a : codimensionChowGroup k X.obj.hom i),
            γℚ X (smoothChowEquiv X.obj.hom (codimensionToRationalChow k X.obj.hom i a)) i =
              γ X i a ∧
            ∀ n : ℕ, n ≠ i →
              γℚ X (smoothChowEquiv X.obj.hom (codimensionToRationalChow k X.obj.hom i a)) n =
                0) ∧
          ∀ (X : (SmoothProjectiveScheme k).FullSubcategory)
              (a : VectorBundleKZero ((toScheme k).obj X)),
            γℚ X (rationalChernCharacterAlgEquiv (isRegular_of_smooth_over_field X.obj.hom)
              (exists_bounds_relativeDimension_fieldChowSituation k X.obj.hom) (1 ⊗ₜ[ℤ] a)) =
              ch X a := by
  obtain ⟨ch₀, h₀, huniq⟩ := 𝔇.existsUnique_isCohomologicalChernCharacter hA1 hA2 hA3 hA4
  refine ⟨h₀.codimensionCycleClass, ⟨fun X i a => h₀.codimensionCycleClass_mem hA1 hA3 X i a,
    fun X i j a b => h₀.codimensionCycleClass_codimensionIntersectionProduct hA1 hA3 X i j a b,
    fun X => h₀.codimensionCycleClass_fundamentalClass X,
    fun f i b => h₀.codimensionCycleClass_codimensionGysin f i b, fun ch hch => ?_⟩, ?_⟩
  · obtain rfl := huniq ch hch
    exact ⟨h₀.cycleClassMap, h₀.cycleClassMap_add, fun X i a =>
      ⟨rfl, fun n hn => h₀.cycleClassMap_eq_zero_of_ne hA1 hA3 X i a hn⟩,
      h₀.cycleClassMap_rationalChernCharacterAlgEquiv⟩
  · rintro γ ⟨-, -, -, -, hdef⟩
    obtain ⟨γℚ, hadd, hcomp, hval⟩ := hdef ch₀ h₀
    -- the rational extension is the cycle class map of Tag 0FIF
    have hγℚ : ∀ X, γℚ X = h₀.cycleClassMap X := fun X => funext fun α => by
      obtain ⟨x, rfl⟩ := (rationalChernCharacterAlgEquiv
        (isRegular_of_smooth_over_field X.obj.hom)
        (exists_bounds_relativeDimension_fieldChowSituation k X.obj.hom)).surjective α
      let e := (rationalChernCharacterAlgEquiv (isRegular_of_smooth_over_field X.obj.hom)
        (exists_bounds_relativeDimension_fieldChowSituation k X.obj.hom)).toAddEquiv.toAddMonoidHom
      exact eq_of_eq_one_tmul (fun d x hd h => nsmul_eq_zero_twist d x hd h)
        (φ := (AddMonoidHom.mk' (γℚ X) (hadd X)).comp e)
        (ψ := (h₀.cycleClassAddHom X).comp e)
        (fun a => (hval X a).trans (h₀.cycleClassMap_rationalChernCharacterAlgEquiv X a).symm) x
    funext X i
    ext a
    rw [← (hcomp X i a).1, hγℚ]
    rfl

end FirstChernClassData

end Stacks.WeilCohomology

end
