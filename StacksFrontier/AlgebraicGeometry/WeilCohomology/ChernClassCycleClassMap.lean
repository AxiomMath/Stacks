module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.SecondAdamsChernCharacter
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.SmoothGysinRing
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.CohomologicalChernCharacterAdams
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition
public import StacksCore.Tactic.StacksAttribute

/-!
# The cycle class map of a Weil cohomology theory, from Chern classes

Section 45.14 of the Stacks Project fixes data (D0), (D1), (D2') — a Tate line `F(1)`, a
contravariant functor `H^*` from smooth projective schemes over `k` to graded commutative
`F`-algebras, and a first Chern class `c₁^H : Pic(X) → H^2(X)(1)` — subject to axioms (A1)–(A4).
Tag 0FIF asserts that there is a unique rule assigning to every smooth projective `X` over `k` a
graded ring homomorphism

  `γ : CH^*(X) ⟶ ⨁_{i ≥ 0} H^{2i}(X)(i)`

compatible with pullbacks such that `ch^H(α) = γ(ch(α))` for `α ∈ K₀(Vect(X))`, `ch^H` being the
cohomological Chern character of Tag 0FIE.

## The objects

Everything is the actual object of the source.

* The data and axioms are `Stacks.WeilCohomology.FirstChernClassData` and its four axioms
  `CoproductAxiom` (A1), `PullbackAxiom` (A2), `ProjectiveBundleAxiom` (A3), `DivisorAxiom` (A4).
* `ch^H` is any rule with the properties of Tag 0FIE
  (`Stacks.WeilCohomology.FirstChernClassData.IsCohomologicalChernCharacter`); Tag 0FIE says there
  is exactly one.
* `CH^*(X) ⊗ 𝐐` is the rational Chow group `CH_*(X) ⊗ 𝐐` of `X` over the field `k` with the
  intersection product of Chow Homology, Section 0FEX (`Stacks.Chow.smoothRationalChowRing`), whose
  codimension pieces are `Stacks.Chow.codimensionChowSubmodule`; the Chern character
  `α ↦ ch(α) ∩ [X]` is the ring isomorphism `Stacks.Chow.rationalChernCharacterAlgEquiv` of
  Tags 0FEY and 0FEM; pullback along `f : X ⟶ Y` is the Gysin map `f^!` of Chow Homology,
  Tag 0FF3 (`Stacks.Chow.smoothGysinRingHom`).
* `⨁_{i ≥ 0} H^{2i}(X)(i)` is read inside the families `(a_n)_{n ≥ 0}`, `a_n ∈ H^*(X)(n)`, with
  the cup product `Stacks.WeilCohomology.FirstChernClassData.cupConv`, as in Tag 0FIE: `γ(α)` has
  only finitely many nonzero components because `γ` is graded and `CH^*(X)` is the direct sum of
  finitely many `CH^i(X)`.

## The statement as printed, and the statement proved

The source writes the defining property as `ch^H(α) = γ(ch(α))`, with `γ` on `CH^*(X)`. What its
proof substitutes into `γ` is the class `ch(α) ∩ [X]` of `CH^*(X) ⊗ 𝐐`, and it defines `γ` on
`CH^*(X) ⊗ 𝐐`, through the isomorphism `K₀(Vect(X)) ⊗ 𝐐 ≅ CH^*(X) ⊗ 𝐐`. So `γ` is a ring
homomorphism on `CH^*(X) ⊗ 𝐐` here, graded in the sense `γ(CH^i(X) ⊗ 𝐐) ⊆ H^{2i}(X)(i)`, and the
defining property is `γ(ch(α) ∩ [X]) = ch^H(α)`.

## The proof

The source's proof. `γ(α) = ch^H(α')` for the class `α' ∈ K₀(Vect(X)) ⊗ 𝐐` with
`ch(α') ∩ [X] = α` (Tags 0FEY, 0FEM): a ring homomorphism, being a composite of two. It is
compatible with pullbacks because `ch^H` is (Tag 0FIE) and Chern classes commute with Gysin maps
(Chow Homology, Tag 0FF8: `f^!(ch(α') ∩ [Y]) = ch(f^*α') ∩ [X]`). It is graded: for
`α ∈ CH^i(X) ⊗ 𝐐`, `ψ²(α') = 2^i α'` (Chow Homology, Section 0FEX, from Tag 0FEN), and
`ch^H_n(ψ²(α')) = 2^n ch^H_n(α')` (Tag 0FIA, from Tag 0FEJ), so `ch^H_n(α') = 0` for `n ≠ i`.
Uniqueness: the classes `ch(α) ∩ [X]`, `α ∈ K₀(Vect(X))`, span `CH^*(X) ⊗ 𝐐` over `𝐐`
(Tag 0FEY), and an additive map into an `F`-vector space is `𝐐`-linear.

## Main definitions

* `Stacks.WeilCohomology.FirstChernClassData.IsCohomologicalChernCharacter.rationalLift` — `ch^H`
  on `K₀(Vect(X)) ⊗ 𝐐`, in coordinates.
* `Stacks.WeilCohomology.FirstChernClassData.IsCohomologicalChernCharacter.cycleClassMap` — **the
  cycle class map `γ`**.

## Main results

* `Stacks.WeilCohomology.FirstChernClassData.existsUnique_cycleClassMap` — **Tag 0FIF.**

## References

* [Stacks Project, Tag 0FIF](https://stacks.math.columbia.edu/tag/0FIF)
* [Stacks Project, Tag 0FIE](https://stacks.math.columbia.edu/tag/0FIE)
* [Stacks Project, Tag 0FIA](https://stacks.math.columbia.edu/tag/0FIA)
* [Stacks Project, Tag 0FEY](https://stacks.math.columbia.edu/tag/0FEY)
* [Stacks Project, Tag 0FEM](https://stacks.math.columbia.edu/tag/0FEM)
* [Stacks Project, Tag 0FF8](https://stacks.math.columbia.edu/tag/0FF8)
* [Stacks Project, Section 0FEX](https://stacks.math.columbia.edu/tag/0FEX)
* [Stacks Project, Tag 0FEJ](https://stacks.math.columbia.edu/tag/0FEJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow
open scoped TensorProduct

universe u w

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme

/-! ### Smooth projective schemes as in Chow Homology, Tag 0FEY -/

section Hypotheses

variable {k : Type u} [Field k]

/-- The underlying scheme of a smooth projective scheme over a field is Noetherian. -/
instance isNoetherian_left (X : (SmoothProjectiveScheme k).FullSubcategory) :
    IsNoetherian X.obj.left :=
  haveI := (isProjective X).isProper
  isNoetherian_of_quasiCompact_fieldChowSituation k X.obj.hom

/-- The diagonal of the underlying scheme of a smooth projective scheme over a field is affine. -/
instance isAffineHom_diagonal_left (X : (SmoothProjectiveScheme k).FullSubcategory) :
    IsAffineHom (pullback.diagonal (terminal.from X.obj.left)) :=
  haveI := (isProjective X).isProper
  isAffineHom_diagonal_of_isSeparated_fieldChowSituation k X.obj.hom

/-- A morphism of smooth projective schemes over a field is locally of finite type. -/
instance locallyOfFiniteType_map {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y) : LocallyOfFiniteType ((toScheme k).map f) :=
  locallyOfFiniteType_of_comp_eq (w f)

end Hypotheses

namespace FirstChernClassData

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] {𝔇 : FirstChernClassData k F}
  {ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
    VectorBundleKZero ((toScheme k).obj X) → ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n}

namespace IsCohomologicalChernCharacter

variable (h : 𝔇.IsCohomologicalChernCharacter ch)

/-- **`ch^H` on `K₀(Vect(X)) ⊗ 𝐐`**, in the coordinates `∏_{i ≥ 0} A^i(X)`,
`A(X) = ⨁_{i ≥ 0} H^{2i}(X)`: the `𝐐`-algebra map extending
`Stacks.WeilCohomology.FirstChernClassData.IsCohomologicalChernCharacter.lift`. -/
def rationalLift (X : (SmoothProjectiveScheme k).FullSubcategory) :
    ℚ ⊗[ℤ] VectorBundleKZero ((toScheme k).obj X) →ₐ[ℚ] PowerSeries (𝔇.A X) :=
  Algebra.TensorProduct.lift (Algebra.ofId ℚ (PowerSeries (𝔇.A X)))
    { h.lift X with
      commutes' := fun n => by
        change h.lift X (algebraMap ℤ _ n) = algebraMap ℤ _ n
        rw [algebraMap_int_eq, eq_intCast, map_intCast]
        exact (eq_intCast (algebraMap ℤ (PowerSeries (𝔇.A X))) n).symm }
    fun q _ => (Algebra.commute_algebraMap_left q _ :
      Commute (Algebra.ofId ℚ (PowerSeries (𝔇.A X)) q) _)

/-- `rationalLift` sends `q ⊗ a` to `q • ch^H(a)`. -/
theorem rationalLift_tmul (X : (SmoothProjectiveScheme k).FullSubcategory) (q : ℚ)
    (a : VectorBundleKZero ((toScheme k).obj X)) :
    h.rationalLift X (q ⊗ₜ[ℤ] a) = q • h.lift X a := by
  refine (Algebra.TensorProduct.lift_tmul _ _ _ q a).trans ?_
  rw [Algebra.ofId_apply, ← Algebra.smul_def]
  rfl

/-- **The cycle class map `γ : CH^*(X) ⊗ 𝐐 ⟶ ⨁_{i ≥ 0} H^{2i}(X)(i)` of Tag 0FIF**: `ch^H(α')`
for the class `α' ∈ K₀(Vect(X)) ⊗ 𝐐` with `ch(α') ∩ [X] = α`. -/
def cycleClassMap (X : (SmoothProjectiveScheme k).FullSubcategory)
    (α : smoothRationalChowRing (k := k) X.obj.hom) : ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n :=
  𝔇.twistRule (h.rationalLift X ((rationalChernCharacterAlgEquiv
    (isRegular_of_smooth_over_field X.obj.hom)
    (exists_bounds_relativeDimension_fieldChowSituation k X.obj.hom)).symm α))

/-- `ch^H` on `K₀(Vect(X)) ⊗ 𝐐` has its `n`-th coefficient in `A^n(X) = H^{2n}(X)`. -/
theorem coeff_rationalLift_mem (hA1 : 𝔇.CoproductAxiom) (hA3 : 𝔇.ProjectiveBundleAxiom)
    (X : (SmoothProjectiveScheme k).FullSubcategory)
    (x : ℚ ⊗[ℤ] VectorBundleKZero ((toScheme k).obj X)) (n : ℕ) :
    PowerSeries.coeff n (h.rationalLift X x) ∈ evenGrade (𝔇.grade X) n := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy
  | tmul q a =>
    rw [rationalLift_tmul, PowerSeries.coeff_smul]
    exact 𝔇.isRationallyGraded hA1 hA3 X n q (h.coeff_lift_mem X a n)

/-- **Tag 0FIA on `K₀(Vect(X)) ⊗ 𝐐`**: `ch^H_n(ψ²(α')) = 2^n ch^H_n(α')`. -/
theorem coeff_rationalLift_rationalSecondAdams (hA1 : 𝔇.CoproductAxiom)
    (hA3 : 𝔇.ProjectiveBundleAxiom) (X : (SmoothProjectiveScheme k).FullSubcategory)
    (x : ℚ ⊗[ℤ] VectorBundleKZero ((toScheme k).obj X))
    (n : ℕ) :
    PowerSeries.coeff n (h.rationalLift X (rationalSecondAdams ((toScheme k).obj X) x)) =
      (2 ^ n : ℕ) • PowerSeries.coeff n (h.rationalLift X x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, smul_zero]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add, map_add, smul_add]
  | tmul q a =>
    rw [rationalSecondAdams_tmul, rationalLift_tmul, rationalLift_tmul, PowerSeries.coeff_smul,
      PowerSeries.coeff_smul, h.coeff_lift_secondAdams hA1 hA3, smul_comm]

/-- `ch^H` on `K₀(Vect(X)) ⊗ 𝐐` is compatible with pullbacks. -/
theorem map_rationalLift {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y)
    (x : ℚ ⊗[ℤ] VectorBundleKZero ((toScheme k).obj Y)) :
    PowerSeries.map (𝔇.pullA f).toRingHom (h.rationalLift Y x) =
      h.rationalLift X ((VectorBundleKZero.pullback ((toScheme k).map f)).toIntLinearMap.baseChange
        ℚ x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul q a =>
    rw [LinearMap.baseChange_tmul, AddMonoidHom.coe_toIntLinearMap, rationalLift_tmul,
      rationalLift_tmul, VectorBundleKZero.pullback_eq_pullbackRingHom, ← h.map_lift f a]
    ext n
    simp only [PowerSeries.coeff_map, PowerSeries.coeff_smul, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe]
    rw [rat_smul_A, rat_smul_A, AlgHom.map_smul_of_tower]

/-- **The defining equation of Tag 0FIF**: `γ(ch(α) ∩ [X]) = ch^H(α)` for `α ∈ K₀(Vect(X))`. -/
theorem cycleClassMap_rationalChernCharacterAlgEquiv
    (X : (SmoothProjectiveScheme k).FullSubcategory)
    (a : VectorBundleKZero ((toScheme k).obj X)) :
    h.cycleClassMap X (rationalChernCharacterAlgEquiv (isRegular_of_smooth_over_field X.obj.hom)
      (exists_bounds_relativeDimension_fieldChowSituation k X.obj.hom) (1 ⊗ₜ[ℤ] a)) = ch X a := by
  rw [cycleClassMap, AlgEquiv.symm_apply_apply, rationalLift_tmul, one_smul, h.twistRule_lift]

/-- **`γ` is additive.** -/
theorem cycleClassMap_add (X : (SmoothProjectiveScheme k).FullSubcategory)
    (α β : smoothRationalChowRing (k := k) X.obj.hom) :
    h.cycleClassMap X (α + β) = h.cycleClassMap X α + h.cycleClassMap X β := by
  rw [cycleClassMap, map_add, map_add, twistRule_add]; rfl

/-- **`γ` is multiplicative** for the intersection product of Section 0FEX and the cup product
of `∏_{i ≥ 0} H^{2i}(X)(i)`. -/
theorem cycleClassMap_mul (X : (SmoothProjectiveScheme k).FullSubcategory)
    (α β : smoothRationalChowRing (k := k) X.obj.hom) :
    h.cycleClassMap X (α * β) = 𝔇.cupConv X (h.cycleClassMap X α) (h.cycleClassMap X β) := by
  rw [cycleClassMap, map_mul, map_mul, twistRule_mul]; rfl

/-- **`γ` is unital.** -/
theorem cycleClassMap_one (X : (SmoothProjectiveScheme k).FullSubcategory) :
    h.cycleClassMap X 1 = 𝔇.oneConv X := by
  rw [cycleClassMap, map_one, map_one, twistRule_one]

/-- **`γ` is compatible with pullbacks**: `f^* γ(α) = γ(f^! α)`, `f^!` the Gysin map. -/
theorem cycleClassMap_smoothGysinRingHom {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y) (α : smoothRationalChowRing (k := k) Y.obj.hom) (n : ℕ) :
    h.cycleClassMap X (smoothGysinRingHom X.obj.hom Y.obj.hom (w f) α) n =
      𝔇.pullTw f n (h.cycleClassMap Y α n) := by
  obtain ⟨x, rfl⟩ := (rationalChernCharacterAlgEquiv (isRegular_of_smooth_over_field Y.obj.hom)
    (exists_bounds_relativeDimension_fieldChowSituation k Y.obj.hom)).surjective α
  rw [smoothGysinRingHom_rationalChernCharacterAlgEquiv, cycleClassMap, cycleClassMap,
    AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply, ← h.map_rationalLift f, twistRule_map]

/-- **`γ` is graded**: a class of codimension `i` goes to `H^{2i}(X)(i)`. For
`α ∈ CH^i(X) ⊗ 𝐐` with `α = ch(α') ∩ [X]`, `ψ²(α') = 2^i α'` (Section 0FEX) and
`ch^H_n(ψ²(α')) = 2^n ch^H_n(α')` (Tag 0FIA), so `ch^H_n(α') = 0` for `n ≠ i`. -/
theorem cycleClassMap_mem (hA1 : 𝔇.CoproductAxiom) (hA3 : 𝔇.ProjectiveBundleAxiom)
    (X : (SmoothProjectiveScheme k).FullSubcategory)
    {i : ℕ} (α : smoothRationalChowRing (k := k) X.obj.hom)
    (hα : (smoothChowEquiv X.obj.hom).symm α ∈
      codimensionChowSubmodule (fieldChowSituation k) X.obj.hom i) :
    h.cycleClassMap X α i ∈
        LinearMap.range (tateTwistMap (L := 𝔇.tate) (𝔇.grade X (2 * (i : ℤ))).subtype i) ∧
      ∀ n : ℕ, n ≠ i → h.cycleClassMap X α n = 0 := by
  set x := (rationalChernCharacterAlgEquiv (isRegular_of_smooth_over_field X.obj.hom)
    (exists_bounds_relativeDimension_fieldChowSituation k X.obj.hom)).symm α with hx
  have hcap : rationalChernCharacterCap (fieldChowSituation k) X.obj.hom x
      (rationalFundamentalClass (fieldChowSituation k) X.obj.hom) ∈
        codimensionChowSubmodule (fieldChowSituation k) X.obj.hom i := by
    have := (rationalChernCharacterAlgEquiv_apply (isRegular_of_smooth_over_field X.obj.hom)
      (exists_bounds_relativeDimension_fieldChowSituation k X.obj.hom) x).symm
    rw [hx, AlgEquiv.apply_symm_apply] at this
    rw [← (smoothChowEquiv X.obj.hom).symm_apply_apply
      (rationalChernCharacterCap _ _ x _)]
    convert hα using 2
  have hψ := rationalSecondAdams_eq_smul_of_rationalChernCharacterCap_mem
    (isRegular_of_smooth_over_field X.obj.hom)
    (exists_bounds_relativeDimension_fieldChowSituation k X.obj.hom) hcap
  refine ⟨?_, fun n hn => ?_⟩
  · rw [cycleClassMap, mem_range_tateTwistMap_iff, κ_twistRule, ← hx]
    have hmem := h.coeff_rationalLift_mem hA1 hA3 X x i
    rw [mem_evenGrade] at hmem
    exact hmem
  · rw [cycleClassMap, ← hx]
    have key := h.coeff_rationalLift_rationalSecondAdams hA1 hA3 X x n
    have hψ' : rationalSecondAdams ((toScheme k).obj X) x = (2 ^ i : ℚ) • x := hψ
    rw [hψ', map_smul, PowerSeries.coeff_smul, ← Nat.cast_smul_eq_nsmul ℚ] at key
    have h0 : PowerSeries.coeff n (h.rationalLift X x) = 0 := by
      have h2 : ((2 : ℚ) ^ i - 2 ^ n) • PowerSeries.coeff n (h.rationalLift X x) = 0 := by
        rw [sub_smul, key]; push_cast; exact sub_self _
      have hne : ((2 : ℚ) ^ i - 2 ^ n) ≠ 0 := by
        intro h'
        rw [sub_eq_zero] at h'
        exact hn (Nat.pow_right_injective (le_refl 2) (by exact_mod_cast h'.symm))
      rw [← one_smul ℚ (PowerSeries.coeff n _), ← inv_mul_cancel₀ hne, mul_smul, h2, smul_zero]
    apply (𝔇.κ X n).injective
    rw [κ_twistRule, h0, ZeroMemClass.coe_zero, map_zero]

end IsCohomologicalChernCharacter

/-- Two additive maps out of `K₀(Vect(X)) ⊗ 𝐐` into a torsion-free group agreeing on the classes
`1 ⊗ α` are equal. -/
theorem eq_of_eq_one_tmul {K M : Type*} [AddCommGroup K] [AddCommGroup M]
    (hM : ∀ (d : ℕ) (x : M), d ≠ 0 → d • x = 0 → x = 0) {φ ψ : ℚ ⊗[ℤ] K →+ M}
    (h : ∀ a : K, φ (1 ⊗ₜ a) = ψ (1 ⊗ₜ a)) (x : ℚ ⊗[ℤ] K) : φ x = ψ x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul q a =>
    have hq : ((q.den : ℤ) • q : ℚ) = (q.num : ℤ) • (1 : ℚ) := by
      rw [zsmul_eq_mul, zsmul_eq_mul, mul_one, Int.cast_natCast]
      exact Rat.den_mul_eq_num q
    have key : q.den • (q ⊗ₜ[ℤ] a) = 1 ⊗ₜ[ℤ] ((q.num : ℤ) • a) := by
      rw [← Nat.cast_smul_eq_nsmul ℤ, TensorProduct.smul_tmul', hq, TensorProduct.smul_tmul]
    have hsub : q.den • (φ (q ⊗ₜ[ℤ] a) - ψ (q ⊗ₜ[ℤ] a)) = 0 := by
      rw [smul_sub, ← map_nsmul, ← map_nsmul, key, h, sub_self]
    exact sub_eq_zero.mp (hM _ _ q.den_nz hsub)

/-- The families `(a_n)_{n ≥ 0}`, `a_n ∈ H^*(X)(n)`, form a torsion-free group, `F` having
characteristic zero. -/
theorem nsmul_eq_zero_twist {X : (SmoothProjectiveScheme k).FullSubcategory} (d : ℕ)
    (x : ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n) (hd : d ≠ 0) (h : d • x = 0) : x = 0 := by
  funext n
  have hn := congrFun h n
  rw [Pi.smul_apply, Pi.zero_apply, ← Nat.cast_smul_eq_nsmul F] at hn
  exact (smul_eq_zero.mp hn).resolve_left (Nat.cast_ne_zero.mpr hd)

/-- **Stacks Project, Tag 0FIF.** Assume given (D0), (D1), (D2') satisfying axioms (A1), (A2),
(A3) and (A4). There is a unique rule which assigns to every smooth projective `X` over `k` a
graded ring homomorphism

  `γ : CH^*(X) ⊗ 𝐐 ⟶ ⨁_{i ≥ 0} H^{2i}(X)(i)`

compatible with pullbacks such that `γ(ch(α) ∩ [X]) = ch^H(α)` for `α ∈ K₀(Vect(X))`, `ch^H` being
the cohomological Chern character of Tag 0FIE.

`CH^*(X) ⊗ 𝐐` is `CH_*(X) ⊗ 𝐐` with the intersection product of Chow Homology, Section 0FEX, and
its codimension grading; pullback is the Gysin map `f^!` of Chow Homology, Tag 0FF3; `ch(α) ∩ [X]`
is the isomorphism of Chow Homology, Tags 0FEY and 0FEM. A value of `γ` is a family
`(γ(α)_n)_{n ≥ 0}`, `γ(α)_n ∈ H^*(X)(n)`; graded means that a class of codimension `i` has
`γ(α)_i ∈ H^{2i}(X)(i)` and all other components zero (so `γ(α) ∈ ⨁_{i ≥ 0} H^{2i}(X)(i)`), and
the ring structure of the target is the cup product `cupConv` with unit `oneConv`, as in Tag 0FIE.
The rule `ch^H` is quantified over: Tag 0FIE says exactly one rule has its properties. -/
@[stacks 0FIF "existence and uniqueness, under exactly (D0), (D1), (D2') and (A1)-(A4) \
(FirstChernClassData with its four axioms), for all smooth projective X over k: γ on \
CH^*(X) ⊗ Q (the actual rational Chow group of X with the intersection product of Chow \
Homology, Section 0FEX, and its codimension grading) is graded, additive, multiplicative and \
unital for the cup product of prod_i H^{2i}(X)(i), compatible with the actual Gysin pullbacks f^!, \
and γ(ch(α) ∩ [X]) = ch^H(α) for every α in K_0(Vect(X)) and the ch^H of Tag 0FIE. The source \
prints the last equation as ch^H(α) = γ(ch(α)), which typechecks only after capping with [X], and \
takes γ on CH^*(X); its proof defines γ on CH^*(X) ⊗ Q, where the equation lives, and so does \
this statement. 0FEY, 0FEM, 0FF8, 0FEN, 0FEX and 0FIA are proved, not assumed"]
theorem existsUnique_cycleClassMap (hA1 : 𝔇.CoproductAxiom) (hA2 : 𝔇.PullbackAxiom)
    (hA3 : 𝔇.ProjectiveBundleAxiom) (hA4 : 𝔇.DivisorAxiom) :
    ∃! γ : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
        smoothRationalChowRing (k := k) X.obj.hom → ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n,
      (∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℕ)
          (α : smoothRationalChowRing (k := k) X.obj.hom),
        (smoothChowEquiv X.obj.hom).symm α ∈
            codimensionChowSubmodule (fieldChowSituation k) X.obj.hom i →
          γ X α i ∈
              LinearMap.range (tateTwistMap (L := 𝔇.tate) (𝔇.grade X (2 * (i : ℤ))).subtype i) ∧
            ∀ n : ℕ, n ≠ i → γ X α n = 0) ∧
      (∀ (X : (SmoothProjectiveScheme k).FullSubcategory)
          (α β : smoothRationalChowRing (k := k) X.obj.hom),
        γ X (α + β) = γ X α + γ X β) ∧
      (∀ (X : (SmoothProjectiveScheme k).FullSubcategory)
          (α β : smoothRationalChowRing (k := k) X.obj.hom),
        γ X (α * β) = 𝔇.cupConv X (γ X α) (γ X β)) ∧
      (∀ (X : (SmoothProjectiveScheme k).FullSubcategory), γ X 1 = 𝔇.oneConv X) ∧
      (∀ {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y)
          (α : smoothRationalChowRing (k := k) Y.obj.hom) (n : ℕ),
        γ X (smoothGysinRingHom X.obj.hom Y.obj.hom (w f) α) n = 𝔇.pullTw f n (γ Y α n)) ∧
      ∀ ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
          VectorBundleKZero ((toScheme k).obj X) → ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n,
        𝔇.IsCohomologicalChernCharacter ch → ∀ (X : (SmoothProjectiveScheme k).FullSubcategory)
          (a : VectorBundleKZero ((toScheme k).obj X)),
          γ X (rationalChernCharacterAlgEquiv (isRegular_of_smooth_over_field X.obj.hom)
            (exists_bounds_relativeDimension_fieldChowSituation k X.obj.hom) (1 ⊗ₜ[ℤ] a)) =
            ch X a := by
  obtain ⟨ch₀, h₀, huniq⟩ := 𝔇.existsUnique_isCohomologicalChernCharacter hA1 hA2 hA3 hA4
  refine ⟨h₀.cycleClassMap, ⟨fun X i α hα => h₀.cycleClassMap_mem hA1 hA3 X α hα,
    h₀.cycleClassMap_add, h₀.cycleClassMap_mul, h₀.cycleClassMap_one,
    fun f α n => h₀.cycleClassMap_smoothGysinRingHom f α n, fun ch hch X a => ?_⟩, ?_⟩
  · rw [huniq ch hch]
    exact h₀.cycleClassMap_rationalChernCharacterAlgEquiv X a
  · rintro γ ⟨-, hadd, -, -, -, hdef⟩
    funext X α
    obtain ⟨x, rfl⟩ := (rationalChernCharacterAlgEquiv (isRegular_of_smooth_over_field X.obj.hom)
      (exists_bounds_relativeDimension_fieldChowSituation k X.obj.hom)).surjective α
    let φ : ℚ ⊗[ℤ] VectorBundleKZero ((toScheme k).obj X) →+
        ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n :=
      .mk' (fun x => γ X (rationalChernCharacterAlgEquiv _ _ x)) fun x y => by rw [map_add, hadd]
    let ψ : ℚ ⊗[ℤ] VectorBundleKZero ((toScheme k).obj X) →+
        ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n :=
      .mk' (fun x => h₀.cycleClassMap X (rationalChernCharacterAlgEquiv _ _ x)) fun x y => by
        rw [map_add, h₀.cycleClassMap_add]
    exact eq_of_eq_one_tmul (fun d x hd h => nsmul_eq_zero_twist d x hd h) (φ := φ) (ψ := ψ)
      (fun a => (hdef ch₀ h₀ X a).trans
      (h₀.cycleClassMap_rationalChernCharacterAlgEquiv X a).symm) x

end FirstChernClassData

end Stacks.WeilCohomology

end
