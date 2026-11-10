module

public import StacksFrontier.AlgebraicGeometry.Crystalline.EnvelopeCompletionFormsBasis
public import StacksFrontier.AlgebraicGeometry.Crystalline.EnvelopeTaylorFormula
public import StacksFrontier.AlgebraicGeometry.Crystalline.Examples.TorsionDegreeZero
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.Universal

/-!
# The element `τ` of [Stacks, Tag 07LJ] does not depend on the choice of coordinates

Keep the situation of `StacksFrontier.AlgebraicGeometry.Crystalline.Examples.TorsionDegreeZero`: the
base `(A, I, γ) = (ℤ_[p], (p), γ)`, the presentation `C = P/J = ℤ_[p][x, y]/(p, x², xy, y²)` of
`C = 𝐅_p[x, y]/(x², xy, y²)` and the divided power envelope `E = D_{P, γ}(J)`, whose `p`-adic
completion is the ring `D` of the example.  The element

`τ = γ_p(x²) γ_p(y²) − γ_p(xy)²`

already lives in `E` (`Crystalline.TorsionExample.envelopeTau`).  This module proves the
algebraic facts about it that the example's two conclusions on `H⁰(Cris(X/S), 𝒪_{X/S})` rest on.

* **`τ` is independent of the coordinates**
  (`Crystalline.TorsionExample.envelopeTau_eq_of_sub_mem`): two divided power morphisms
  `F, G : E → B` over `A` whose values on `x` and on `y` differ by elements of the divided power
  ideal of `B` agree on `τ`.  This is what makes `τ` a section of `𝒪_{X/S}` over every object of
  `Cris(X/S)`, and it is the content of "`dτ = 0`" that the source uses through
  [Stacks, Proposition 60.21.3, Tag 07LG]: by Taylor's formula
  (`Crystalline.envelopeTaylor_formula`) `F(τ) = ∑_K G(θ_K τ) (F(y) − G(y))^{[K]}`, the operators
  `θ_K` are composites of the first order operators `δ_i`, and `δ_i(τ)` is the coefficient of
  `d y_i` in `dτ`, which vanishes by the example's displayed computation.
* **`p τ = 0` in `E`** (`Crystalline.TorsionExample.prime_mul_envelopeTau`).
* **The Frobenius lift `x ↦ x^p`, `y ↦ y^p` kills `τ`**
  (`Crystalline.TorsionExample.envelopeFrobenius_envelopeTau`), for the divided power
  endomorphism `envelopeFrobenius` of `E` over `A` that the universal property of the envelope
  attaches to it.

The computations are done once for an arbitrary divided power ideal, for the element
`Crystalline.dpowTau γ p X Y = γ_p(X²) γ_p(Y²) − γ_p(XY)²` with `X², XY, Y²` in the ideal.

## References

* [Stacks Project, Tag 07LJ](https://stacks.math.columbia.edu/tag/07LJ)
* [Stacks Project, Tag 07HW](https://stacks.math.columbia.edu/tag/07HW)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public noncomputable section

open DividedPowers

namespace Crystalline

/-! ### The element `γ_p(X²) γ_p(Y²) − γ_p(XY)²` of a divided power ring -/

section Generic

variable {B : Type*} [CommRing B] {I : Ideal B} (γ : DividedPowers I) (p : ℕ) [Fact p.Prime]

/-- The element `γ_p(X²) γ_p(Y²) − γ_p(XY)²` of a ring with divided powers `γ`. -/
def dpowTau (X Y : B) : B :=
  γ.dpow p (X ^ 2) * γ.dpow p (Y ^ 2) - γ.dpow p (X * Y) ^ 2

variable {γ p}

omit [Fact p.Prime] in
/-- `p! (γ_p(X²) γ_p(Y²) − γ_p(XY)²) = 0`, as
`p! γ_p(X²) γ_p(Y²) = X^{2p} γ_p(Y²) = γ_p(X²Y²) = (XY)^p γ_p(XY) = p! γ_p(XY)²`. -/
theorem factorial_mul_dpowTau {X Y : B} (hx : X ^ 2 ∈ I) (hy : Y ^ 2 ∈ I) (hz : X * Y ∈ I) :
    (p.factorial : B) * dpowTau γ p X Y = 0 := by
  calc (p.factorial : B) * dpowTau γ p X Y
      = ((p.factorial : B) * γ.dpow p (X ^ 2)) * γ.dpow p (Y ^ 2) -
          ((p.factorial : B) * γ.dpow p (X * Y)) * γ.dpow p (X * Y) := by
        rw [dpowTau]
        ring
    _ = (X ^ 2) ^ p * γ.dpow p (Y ^ 2) - (X * Y) ^ p * γ.dpow p (X * Y) := by
        rw [γ.factorial_mul_dpow_eq_pow (n := p) hx, γ.factorial_mul_dpow_eq_pow (n := p) hz]
    _ = γ.dpow p (X ^ 2 * Y ^ 2) - γ.dpow p ((X * Y) * (X * Y)) := by
        rw [← γ.dpow_mul (n := p) (a := X ^ 2) hy, ← γ.dpow_mul (n := p) (a := X * Y) hz]
    _ = 0 := by rw [show X ^ 2 * Y ^ 2 = (X * Y) * (X * Y) by ring, sub_self]

/-- `p! = p · (p − 1)!` in a commutative ring. -/
theorem natCast_factorial_eq_prime_mul_factorial_pred :
    (p.factorial : B) = (p : B) * ((p - 1).factorial : B) := by
  have hp : p.Prime := Fact.out
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hp.ne_zero
  rw [Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  ring

/-- `p (γ_p(X²) γ_p(Y²) − γ_p(XY)²) = 0` when `(p − 1)!` is invertible. -/
theorem prime_mul_dpowTau {X Y : B} (hx : X ^ 2 ∈ I) (hy : Y ^ 2 ∈ I) (hz : X * Y ∈ I)
    (hunit : IsUnit (((p - 1).factorial : ℕ) : B)) :
    (p : B) * dpowTau γ p X Y = 0 := by
  have h := factorial_mul_dpowTau (γ := γ) (p := p) hx hy hz
  rw [natCast_factorial_eq_prime_mul_factorial_pred, mul_comm (p : B), mul_assoc] at h
  exact hunit.mul_right_eq_zero.mp h

omit [Fact p.Prime] in
/-- `X^p γ_p(Y²) = Y^p γ_p(XY)`, both sides being `γ_p(XY²)`. -/
theorem pow_mul_dpow_sq_eq {X Y : B} (hy : Y ^ 2 ∈ I) (hz : X * Y ∈ I) :
    X ^ p * γ.dpow p (Y ^ 2) = Y ^ p * γ.dpow p (X * Y) := by
  rw [← γ.dpow_mul hy, ← γ.dpow_mul hz]
  ring_nf

/-- **The Frobenius twist of `γ_p(X²) γ_p(Y²) − γ_p(XY)²` vanishes**:
`γ_p(X^{2p}) γ_p(Y^{2p}) − γ_p(X^p Y^p)² = (XY)^{2p(p − 1)} (γ_p(X²) γ_p(Y²) − γ_p(XY)²)`, and
since `2p(p − 1) ≥ p` the factor `(XY)^p = p! γ_p(XY)` splits off, which kills the second
factor by `Crystalline.factorial_mul_dpowTau`. -/
theorem dpowTau_pow_eq_zero {X Y : B} (hx : X ^ 2 ∈ I) (hy : Y ^ 2 ∈ I) (hz : X * Y ∈ I) :
    dpowTau γ p (X ^ p) (Y ^ p) = 0 := by
  have hp : p.Prime := Fact.out
  obtain ⟨q, hq⟩ := Nat.exists_eq_add_one_of_ne_zero hp.ne_zero
  have hsq : ∀ Z : B, (Z ^ p) ^ 2 = Z ^ (2 * q) * Z ^ 2 := fun Z => by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have hZ : X ^ p * Y ^ p = X ^ q * Y ^ q * (X * Y) := by
    rw [hq, pow_succ, pow_succ]
    ring
  have htwist : dpowTau γ p (X ^ p) (Y ^ p) =
      (X * Y) ^ (2 * q * p) * dpowTau γ p X Y := by
    rw [dpowTau, hsq, hsq, hZ, γ.dpow_mul hx, γ.dpow_mul hy, γ.dpow_mul hz, dpowTau]
    simp only [mul_pow, ← pow_mul]
    ring
  have hle : p ≤ 2 * q * p := Nat.le_mul_of_pos_left p (by have := hp.two_le; omega)
  obtain ⟨m, hm⟩ : ∃ m, 2 * q * p = m + p := ⟨_, (Nat.sub_add_cancel hle).symm⟩
  rw [htwist, hm, pow_add, ← γ.factorial_mul_dpow_eq_pow (n := p) hz]
  calc (X * Y) ^ m * ((p.factorial : B) * γ.dpow p (X * Y)) * dpowTau γ p X Y
      = (X * Y) ^ m * γ.dpow p (X * Y) * ((p.factorial : B) * dpowTau γ p X Y) := by ring
    _ = 0 := by rw [factorial_mul_dpowTau hx hy hz, mul_zero]

omit [Fact p.Prime] in
/-- A divided power morphism carries `γ_p(X²) γ_p(Y²) − γ_p(XY)²` to the same expression in the
images of `X` and `Y`. -/
theorem map_dpowTau {C : Type*} [CommRing C] {K : Ideal C} {δ : DividedPowers K}
    (f : DPMorphism γ δ) {X Y : B} (hx : X ^ 2 ∈ I) (hy : Y ^ 2 ∈ I) (hz : X * Y ∈ I) :
    f (dpowTau γ p X Y) = dpowTau δ p (f X) (f Y) := by
  change f.toRingHom (dpowTau γ p X Y) = dpowTau δ p (f.toRingHom X) (f.toRingHom Y)
  rw [dpowTau, dpowTau, map_sub, map_mul, map_pow, ← f.dpow_comp (n := p) _ hx,
    ← f.dpow_comp (n := p) _ hy, ← f.dpow_comp (n := p) _ hz, map_pow, map_pow, map_mul]

end Generic

namespace TorsionExample

variable (p : ℕ) [Fact p.Prime]

/-! ### `τ` in the envelope -/

/-- `τ` is `Crystalline.dpowTau` of the coordinates of the envelope. -/
theorem envelopeTau_eq_dpowTau :
    envelopeTau p = dpowTau (envelope p).object.dividedPowers p (envelopeX p) (envelopeY p) :=
  rfl

/-- The coordinate `y_0` of the envelope is `x`. -/
theorem envelopeCoord_zero : envelopeCoord (envelope p) 0 = envelopeX p := rfl

/-- The coordinate `y_1` of the envelope is `y`. -/
theorem envelopeCoord_one : envelopeCoord (envelope p) 1 = envelopeY p := rfl

/-- `(p − 1)!` is invertible in the envelope, being the image of a unit of `ℤ_[p]`. -/
theorem isUnit_factorial_pred_envelope :
    IsUnit ((((p - 1).factorial : ℕ) : (envelope p).object)) := by
  have hp : p.Prime := Fact.out
  have hu : IsUnit ((((p - 1).factorial : ℕ) : ℤ_[p])) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact Nat.Prime.coprime_factorial_of_lt hp (by have := hp.pos; omega)
  simpa only [map_natCast] using hu.map (envelope p).structureMap.toRingHom

/-- **`p τ = 0` in the envelope `E`**, before any completion. -/
theorem prime_mul_envelopeTau : (p : (envelope p).object) * envelopeTau p = 0 :=
  prime_mul_dpowTau (envelopeX_sq_mem p) (envelopeY_sq_mem p) (envelopeX_mul_envelopeY_mem p)
    (isUnit_factorial_pred_envelope p)

/-! ### `dτ = 0` in `Ω_{E/A, γ}`, and `δ_i(τ) = 0` -/

/-- The `A`-algebra structure of the envelope through its structure map, the one for which
`Crystalline.envelopeDifferentialsBasis` is stated. -/
@[instance_reducible]
def envelopeBaseAlgebra : Algebra ℤ_[p] (envelope p).object :=
  (envelope p).structureMap.toRingHom.toAlgebra

attribute [local instance] envelopeBaseAlgebra

/-- **`dτ = 0` in `Ω_{E/A, γ}`**, the example's displayed computation, read in the envelope. -/
theorem dividedPowerDifferential_envelopeTau :
    dividedPowerDifferential (A := ℤ_[p]) (envelope p).object.dividedPowers (envelopeTau p) =
      0 := by
  have hp : p.Prime := Fact.out
  exact dividedPowerDifferential_dpow_mul_sub_sq_eq_zero (A := ℤ_[p])
    (envelope p).object.dividedPowers hp.ne_zero (envelopeX_sq_mem p) (envelopeY_sq_mem p)
    (envelopeX_mul_envelopeY_mem p)
    (pow_mul_dpow_sq_eq (envelopeY_sq_mem p) (envelopeX_mul_envelopeY_mem p))
    (by
      rw [pow_mul_dpow_sq_eq (envelopeX_sq_mem p) (by
        rw [mul_comm]
        exact envelopeX_mul_envelopeY_mem p), mul_comm (envelopeY p)])
    (isUnit_factorial_pred_envelope p)

/-- **`δ_i(τ) = 0`**: the first order Taylor operator `δ_i` of the envelope reads off the
coefficient of `d y_i`, `d a = ∑_i δ_i(a) d y_i` (`Crystalline.envelopeTaylor_derivation`), the
`d y_i` being a basis of `Ω_{E/A, γ}` (`Crystalline.envelopeDifferentialsBasis`, which is
[Stacks, Tag 07HW]); and `dτ = 0`. -/
theorem envelopeDelta_envelopeTau (i : Fin 2) :
    envelopeDelta (envelope p) i (envelopeTau p) = 0 := by
  classical
  set b := envelopeDifferentialsBasis (envelope p)
  have hd := envelopeTaylor_derivation (envelope p) (envelope p).object
    (DPMorphism.id (envelope p).object.dividedPowers)
    (dividedPowerDifferentials (A := ℤ_[p]) (envelope p).object.dividedPowers)
    universalDividedPowerDerivation (envelopeTau p)
  have hcoord := congrArg (fun ω => b.repr ω i) hd
  simp only at hcoord
  change b.repr (dividedPowerDifferential (A := ℤ_[p]) (envelope p).object.dividedPowers
      (envelopeTau p)) i = _ at hcoord
  rw [dividedPowerDifferential_envelopeTau, map_zero, Finsupp.zero_apply, map_sum,
    Finsupp.finsetSum_apply] at hcoord
  have key : ∀ x : Fin 2, b.repr ((DPMorphism.id (envelope p).object.dividedPowers)
        ((envelopeDelta (envelope p) x) (envelopeTau p)) •
      universalDividedPowerDerivation.toDerivation
        ((DPMorphism.id (envelope p).object.dividedPowers) (envelopeCoord (envelope p) x))) i =
      if x = i then envelopeDelta (envelope p) x (envelopeTau p) else 0 := by
    intro x
    have hbx : universalDividedPowerDerivation.toDerivation
        ((DPMorphism.id (envelope p).object.dividedPowers) (envelopeCoord (envelope p) x)) =
        b x := (envelopeDifferentialsBasis_apply (envelope p) x).symm
    rw [hbx, LinearEquiv.map_smul, b.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
    split_ifs <;> simp [smul_eq_mul]
    rfl
  simp_rw [key, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hcoord
  exact hcoord.symm

/-- **The Taylor coefficients `θ_K(τ)` vanish for `K ≠ 0`**: `θ_K` is `θ_{K − e_i} ∘ δ_i` for any
`i` with `K_i ≠ 0`, by the cocycle identity `Crystalline.presentationTaylorCoeff_add`, and
`δ_i(τ) = 0`. -/
theorem presentationTaylorCoeff_envelopeTau {K : Fin 2 →₀ ℕ} (hK : K ≠ 0) :
    presentationTaylorCoeff (envelope p) K (envelopeTau p) = 0 := by
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hK
  have hle : Finsupp.single i 1 ≤ K := by
    rw [Finsupp.single_le_iff]
    exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  have hsplit : K = (K - Finsupp.single i 1) + Finsupp.single i 1 :=
    (tsub_add_cancel_of_le hle).symm
  rw [hsplit, presentationTaylorCoeff_add, Function.comp_apply]
  change presentationTaylorCoeff (envelope p) _ (envelopeDelta (envelope p) i (envelopeTau p)) = 0
  rw [envelopeDelta_envelopeTau, map_zero]

/-- **`τ` does not depend on the coordinates.**  Two divided power morphisms `F, G` from the
envelope to a divided power ring `B`, agreeing on the base and with `F(x) − G(x)` and
`F(y) − G(y)` in the divided power ideal of `B`, agree on `τ`: in Taylor's formula
`F(τ) = ∑_K G(θ_K τ) (F(y) − G(y))^{[K]}` only `K = 0` survives. -/
theorem envelopeTau_eq_of_sub_mem (B : DividedPowerRing.{0})
    (F G : DPMorphism (envelope p).object.dividedPowers B.dividedPowers)
    (hFG : F.comp (envelope p).structureMap = G.comp (envelope p).structureMap)
    (hxi : ∀ i, F (envelopeCoord (envelope p) i) - G (envelopeCoord (envelope p) i) ∈ B.ideal) :
    F (envelopeTau p) = G (envelopeTau p) := by
  have hG : ∀ b, G.toRingHom 0 * b = 0 := fun b => by rw [map_zero, zero_mul]
  rw [envelopeTaylor_formula (envelope p) B F G hFG hxi (envelopeTau p)]
  rw [Finset.sum_eq_single (0 : Fin 2 →₀ ℕ)]
  · rw [taylorMonomial_zero, mul_one, presentationTaylorCoeff_zero]
    rfl
  · intro K _ hK
    rw [presentationTaylorCoeff_envelopeTau p hK]
    exact hG _
  · intro h0
    rw [presentationTaylorCoeff_eq_zero_of_notMem (envelope p) h0]
    exact hG _

/-! ### The Frobenius lift of the envelope -/

/-- The polynomial map `x ↦ x^p`, `y ↦ y^p` of `P` into the envelope carries `J = (p, x², xy, y²)`
into the divided power ideal. -/
theorem frobeniusCoords_map_relations_le :
    (relations p).map (MvPolynomial.eval₂Hom (envelope p).structureMap.toRingHom
        (fun i => envelopeCoord (envelope p) i ^ p)) ≤ (envelope p).object.ideal := by
  have hppos : 0 < p := (Fact.out : p.Prime).pos
  have hpmem : (p : (envelope p).object) ∈ (envelope p).object.ideal := by
    have hpbase : (p : base p) ∈ (base p).ideal := Ideal.subset_span (by simp)
    simpa using (envelope p).structureMap.ideal_comp
      (Ideal.mem_map_of_mem (envelope p).structureMap.toRingHom hpbase)
  refine Ideal.map_le_iff_le_comap.mpr ?_
  change Ideal.span ({(p : polynomial p), polynomialX p ^ 2,
    polynomialX p * polynomialY p, polynomialY p ^ 2} : Set (polynomial p)) ≤ _
  rw [Ideal.span_le]
  rintro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rw [SetLike.mem_coe, Ideal.mem_comap]
  rcases hz with rfl | rfl | rfl | rfl
  · rw [map_natCast]
    exact hpmem
  · rw [map_pow, MvPolynomial.eval₂Hom_X', ← pow_mul, mul_comm, pow_mul]
    exact Ideal.pow_mem_of_mem _ (envelopeX_sq_mem p) p hppos
  · rw [map_mul, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X', ← mul_pow]
    exact Ideal.pow_mem_of_mem _ (envelopeX_mul_envelopeY_mem p) p hppos
  · rw [map_pow, MvPolynomial.eval₂Hom_X', ← pow_mul, mul_comm, pow_mul]
    exact Ideal.pow_mem_of_mem _ (envelopeY_sq_mem p) p hppos

/-- The existence of the Frobenius lift of the envelope. -/
theorem exists_envelopeFrobenius :
    ∃ q : DPMorphism (envelope p).object.dividedPowers (envelope p).object.dividedPowers,
      q.comp (envelope p).structureMap = (envelope p).structureMap ∧
        ∀ i, q (envelopeCoord (envelope p) i) = envelopeCoord (envelope p) i ^ p :=
  exists_envelope_dpMorphism (envelope p) (envelope p).object (envelope p).structureMap _
    (frobeniusCoords_map_relations_le p)

/-- **The Frobenius lift `σ` of the envelope**: the divided power endomorphism of `E` over `A`
with `σ(x) = x^p` and `σ(y) = y^p`, given by the universal property of the envelope. -/
def envelopeFrobenius :
    DPMorphism (envelope p).object.dividedPowers (envelope p).object.dividedPowers :=
  (exists_envelopeFrobenius p).choose

/-- `σ` is a morphism over the base `A`. -/
theorem envelopeFrobenius_comp_structureMap :
    (envelopeFrobenius p).comp (envelope p).structureMap = (envelope p).structureMap :=
  (exists_envelopeFrobenius p).choose_spec.1

/-- `σ(y_i) = y_i^p`. -/
theorem envelopeFrobenius_coord (i : Fin 2) :
    envelopeFrobenius p (envelopeCoord (envelope p) i) = envelopeCoord (envelope p) i ^ p :=
  (exists_envelopeFrobenius p).choose_spec.2 i

/-- **The Frobenius lift `x ↦ x^p`, `y ↦ y^p` kills `τ`**, already in the envelope. -/
theorem envelopeFrobenius_envelopeTau : envelopeFrobenius p (envelopeTau p) = 0 := by
  rw [envelopeTau_eq_dpowTau, map_dpowTau _ (envelopeX_sq_mem p) (envelopeY_sq_mem p)
    (envelopeX_mul_envelopeY_mem p), ← envelopeCoord_zero, ← envelopeCoord_one,
    envelopeFrobenius_coord, envelopeFrobenius_coord, envelopeCoord_zero, envelopeCoord_one]
  exact dpowTau_pow_eq_zero (envelopeX_sq_mem p) (envelopeY_sq_mem p)
    (envelopeX_mul_envelopeY_mem p)

end TorsionExample

end Crystalline

end
