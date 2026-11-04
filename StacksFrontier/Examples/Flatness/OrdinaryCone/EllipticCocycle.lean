module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.FractionRing
public import StacksFrontier.Examples.Flatness.OrdinaryCone.Cone
public import StacksFrontier.RingTheory.WittVector.FrobeniusCocycle

/-!
# An Artin–Schreier–Witt cocycle on an ordinary elliptic curve

Let `k` be a field and `G = k[x, y, z]/(z³ + (y² + xy) z + x³)` the cone
`Stacks.Examples.OrdinaryCone.Cone k`, graded with `x`, `y` and `z` of degree one. Over a field of
characteristic two this is the homogeneous coordinate ring of the ordinary elliptic curve
`E : y²z + xyz = x³ + z³`, and the affine opens `D₊(x)` and `D₊(y)` cover `E`. Inside the fraction
field `Ω` of `G` we consider the rings of functions on `D₊(x)`, `D₊(y)` and `D₊(x) ∩ D₊(y)`: the
degree-zero fractions `g / xⁿ`, `g / yⁿ` and `g / (xⁱ yʲ)` with `g` homogeneous of degree `n`,
respectively `i + j`.

## Main definitions

* `Stacks.Examples.OrdinaryCone.Cone.lift`: the algebra map out of the cone determined by a
  solution of the cubic.
* `Stacks.Examples.OrdinaryCone.Cone.awayX`, `Cone.awayY`, `Cone.awayXY`: the degree-zero parts of
  `G[1/x]`, `G[1/y]` and `G[1/(xy)]`, as subalgebras of `Ω`.
* `Stacks.Examples.OrdinaryCone.Cone.e`: the function `z² / (xy)` on `D₊(x) ∩ D₊(y)`.

## Main results

* `Cone.exists_eq_add_add_smul_e`: every function on `D₊(x) ∩ D₊(y)` is the sum of a function on
  `D₊(x)`, a function on `D₊(y)` and a constant multiple of `e`.
* `Cone.e_ne_add`: `e` is not the sum of a function on `D₊(x)` and a function on `D₊(y)`; thus
  `e` spans `H¹(E, 𝒪_E)`.
* `Cone.e_sq`: in characteristic two, `e² = e + z² / x² + x z / y²`; the Frobenius acts on
  `H¹(E, 𝒪_E)` as the identity, so `E` is ordinary.
* `Cone.exists_wittVector_cocycle`: when every element of `k` has the form `μ² + μ`, there are
  Witt vectors `a_x`, `a_y` and `c` over `Ω` with coefficients in the functions on `D₊(x)`,
  `D₊(y)` and `D₊(x) ∩ D₊(y)` respectively, with `a_y - a_x = F c - c` and with zeroth coefficient
  of `a_x` equal to `(z / x)²`.

## Implementation notes

That `e` is not a sum of functions on `D₊(x)` and `D₊(y)` is read off the coordinate of `z²` in the
basis `1, z, z²` of `k[x, y][z]/(z³ + (y² + xy) z + x³)` over `k[x, y]`, into which the cone maps.
-/

@[expose] public section

namespace Stacks.Examples.OrdinaryCone

open MvPolynomial

namespace Cone

section Nonvanishing

variable (k : Type*) [CommRing k] [Nontrivial k]

/-- The generator `x` of the cone is nonzero. -/
theorem x_ne_zero : x k ≠ 0 := fun h => by
  have := congrArg (lift k (1 : k) 0 (-1) (by ring)) h
  rw [lift_x, map_zero] at this
  exact one_ne_zero this

/-- The generator `y` of the cone is nonzero. -/
theorem y_ne_zero : y k ≠ 0 := fun h => by
  have := congrArg (lift k (-1 : k) 1 1 (by ring)) h
  rw [lift_y, map_zero] at this
  exact one_ne_zero this

/-- The generator `z` of the cone is nonzero. -/
theorem z_ne_zero : z k ≠ 0 := fun h => by
  have := congrArg (lift k (-1 : k) 0 1 (by ring)) h
  rw [lift_z, map_zero] at this
  exact one_ne_zero this

end Nonvanishing

section Component

variable {k : Type*} [CommRing k]

/-- An element of the cone has degree `d` if and only if it is the image of a homogeneous
polynomial of degree `d`. -/
theorem mem_component {d : ℕ} {g : Cone k} :
    g ∈ component k d ↔ ∃ p : MvPolynomial (Fin 3) k, p.IsHomogeneous d ∧
      Ideal.Quotient.mk _ p = g := by
  simp [component]

/-- The product of elements of degrees `m` and `n` has degree `m + n`. -/
theorem mul_mem_component {m n : ℕ} {g h : Cone k} (hg : g ∈ component k m)
    (hh : h ∈ component k n) : g * h ∈ component k (m + n) := by
  obtain ⟨p, hp, rfl⟩ := mem_component.1 hg
  obtain ⟨q, hq, rfl⟩ := mem_component.1 hh
  exact mem_component.2 ⟨p * q, hp.mul hq, map_mul _ _ _⟩

/-- The constants of the cone have degree zero. -/
theorem algebraMap_mem_component_zero (c : k) : algebraMap k (Cone k) c ∈ component k 0 :=
  mem_component.2 ⟨(C c : MvPolynomial (Fin 3) k), isHomogeneous_C (Fin 3) c, rfl⟩

/-- The unit `1` of the cone has degree zero. -/
theorem one_mem_component_zero : (1 : Cone k) ∈ component k 0 := by
  simpa using algebraMap_mem_component_zero (k := k) 1

/-- The generator `x` has degree one. -/
theorem x_mem_component_one : x k ∈ component k 1 :=
  mem_component.2 ⟨X 0, isHomogeneous_X _ _, rfl⟩

/-- The generator `y` has degree one. -/
theorem y_mem_component_one : y k ∈ component k 1 :=
  mem_component.2 ⟨X 1, isHomogeneous_X _ _, rfl⟩

/-- The generator `z` has degree one. -/
theorem z_mem_component_one : z k ∈ component k 1 :=
  mem_component.2 ⟨X 2, isHomogeneous_X _ _, rfl⟩

/-- The `n`-th power of an element of degree `m` has degree `m n`. -/
theorem pow_mem_component {g : Cone k} {m : ℕ} (hg : g ∈ component k m) (n : ℕ) :
    g ^ n ∈ component k (m * n) := by
  induction n with
  | zero => simpa using one_mem_component_zero
  | succ n ih => simpa [pow_succ, Nat.mul_succ] using mul_mem_component ih hg

/-- The monomial `xᵃ yᵇ zᶜ` has degree `a + b + c`. -/
theorem monomial_mem_component (a b c : ℕ) :
    x k ^ a * y k ^ b * z k ^ c ∈ component k (a + b + c) := by
  simpa using mul_mem_component (mul_mem_component
    (pow_mem_component (x_mem_component_one (k := k)) a)
    (pow_mem_component (y_mem_component_one (k := k)) b))
    (pow_mem_component (z_mem_component_one (k := k)) c)

/-- An induction principle for the degree `d` part of the cone: it is spanned over `k` by the
monomials `xᵃ yᵇ zᶜ` with `a + b + c = d`. -/
theorem component_induction {d : ℕ} {P : Cone k → Prop} (zero : P 0)
    (add : ∀ g h, P g → P h → P (g + h)) (smul : ∀ (r : k) g, P g → P (r • g))
    (monomial : ∀ a b c, a + b + c = d → P (x k ^ a * y k ^ b * z k ^ c)) {g : Cone k}
    (hg : g ∈ component k d) : P g := by
  obtain ⟨p, hp, rfl⟩ := mem_component.1 hg
  rw [p.as_sum, map_sum]
  refine Finset.sum_induction _ P add zero fun s hs => ?_
  have hdeg : s 0 + s 1 + s 2 = d := by
    have : (Finsupp.weight 1) s = d := hp (mem_support_iff.1 hs)
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_three] at this
    simpa using this
  have hmon : Ideal.Quotient.mk (Ideal.span {equation k}) (MvPolynomial.monomial s (coeff s p)) =
      coeff s p • (x k ^ s 0 * y k ^ s 1 * z k ^ s 2) := by
    rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three,
      Algebra.smul_def]
    simp only [map_mul, map_pow, x, y, z, mul_assoc]
    rfl
  rw [hmon]
  exact smul _ _ (monomial _ _ _ hdeg)

end Component

section Coordinate

variable (k : Type*) [CommRing k]

/-- The cubic `z³ + (y² + xy) z + x³` as a polynomial in `z` over `k[x, y]`. -/
noncomputable def cubicInZ : Polynomial (MvPolynomial (Fin 2) k) :=
  Polynomial.X ^ 3 + Polynomial.C (X 1 ^ 2 + X 0 * X 1) * Polynomial.X + Polynomial.C (X 0 ^ 3)

/-- The cubic `z³ + (y² + xy) z + x³` is monic in `z`. -/
theorem monic_cubicInZ : (cubicInZ k).Monic := by
  unfold cubicInZ
  monicity!

/-- The cubic `z³ + (y² + xy) z + x³` has degree three in `z`. -/
theorem natDegree_cubicInZ [Nontrivial k] : (cubicInZ k).natDegree = 3 := by
  unfold cubicInZ
  compute_degree!

/-- The cone maps to `k[x, y][z]/(z³ + (y² + xy) z + x³)`, which is free over `k[x, y]` with basis
`1, z, z²`. -/
noncomputable def toAdjoinRoot : Cone k →ₐ[k] AdjoinRoot (cubicInZ k) :=
  lift k (AdjoinRoot.of _ (X 0)) (AdjoinRoot.of _ (X 1)) (AdjoinRoot.root _) <| by
    have h : AdjoinRoot.mk (cubicInZ k) (cubicInZ k) = 0 := AdjoinRoot.mk_self
    calc _ = AdjoinRoot.mk (cubicInZ k) (Polynomial.X ^ 3 +
          Polynomial.C (X 1 ^ 2 + X 0 * X 1) * Polynomial.X + Polynomial.C (X 0 ^ 3)) := by
          simp [AdjoinRoot.mk_X, AdjoinRoot.mk_C]
      _ = 0 := h

/-- The coordinate of `z²` in the basis `1, z, z²` of `k[x, y][z]/(z³ + (y² + xy) z + x³)` over
`k[x, y]`. -/
noncomputable def coordZSq [Nontrivial k] :
    AdjoinRoot (cubicInZ k) →ₗ[MvPolynomial (Fin 2) k] MvPolynomial (Fin 2) k :=
  (AdjoinRoot.powerBasis' (monic_cubicInZ k)).basis.coord
    ⟨2, by rw [AdjoinRoot.powerBasis'_dim, natDegree_cubicInZ]; norm_num⟩

/-- The coordinate of `z²` in `m z²` is `m`, for `m ∈ k[x, y]`. -/
theorem coordZSq_smul_root_sq [Nontrivial k] (m : MvPolynomial (Fin 2) k) :
    coordZSq k (AdjoinRoot.of _ m * AdjoinRoot.root _ ^ 2) = m := by
  have hb := (AdjoinRoot.powerBasis' (monic_cubicInZ k)).basis_eq_pow
    ⟨2, by rw [AdjoinRoot.powerBasis'_dim, natDegree_cubicInZ]; norm_num⟩
  rw [AdjoinRoot.powerBasis'_gen] at hb
  rw [← AdjoinRoot.algebraMap_eq, ← Algebra.smul_def, coordZSq, map_smul]
  simp only at hb
  rw [← hb, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul,
    mul_one]

end Coordinate

section Away

variable (k : Type*) [Field k]

local notation "Ω" => FractionRing (Cone k)

local notation "⟪" g "⟫" => algebraMap (Cone k) (FractionRing (Cone k)) g

/-- The degree-zero part of the localization of the cone at the powers of an element `s` of
degree `m`: the fractions `g / sⁿ` in the fraction field, with `g` of degree `m n`. -/
noncomputable def away (s : Cone k) (m : ℕ) (hs : s ∈ component k m) : Subalgebra k Ω where
  carrier := {t | ∃ n, ∃ g ∈ component k (m * n), ⟪s⟫ ^ n * t = ⟪g⟫}
  mul_mem' := by
    rintro t t' ⟨n, g, hg, hgt⟩ ⟨n', g', hg', hgt'⟩
    refine ⟨n + n', g * g', by simpa [Nat.mul_add] using mul_mem_component hg hg', ?_⟩
    rw [map_mul, ← hgt, ← hgt', pow_add]
    ring
  add_mem' := by
    rintro t t' ⟨n, g, hg, hgt⟩ ⟨n', g', hg', hgt'⟩
    refine ⟨n + n', g * s ^ n' + s ^ n * g', ?_, ?_⟩
    · rw [Nat.mul_add]
      exact add_mem (mul_mem_component hg (pow_mem_component hs n'))
        (by simpa [add_comm] using mul_mem_component (pow_mem_component hs n) hg')
    · rw [map_add, map_mul, map_mul, map_pow, map_pow, ← hgt, ← hgt', pow_add]
      ring
  algebraMap_mem' c := ⟨0, algebraMap k (Cone k) c, by
    simpa using algebraMap_mem_component_zero c, by
      simp [IsScalarTower.algebraMap_apply k (Cone k) Ω]⟩

/-- An element `t` of the fraction field lies in `away k s m hs` if and only if `sⁿ t = g` for
some `n` and some `g` of degree `m n`. -/
theorem mem_away {s : Cone k} {m : ℕ} {hs : s ∈ component k m} {t : Ω} :
    t ∈ away k s m hs ↔ ∃ n, ∃ g ∈ component k (m * n), ⟪s⟫ ^ n * t = ⟪g⟫ :=
  Iff.rfl

/-- The functions on the affine open `D₊(x)` of the elliptic curve: the degree-zero part of the
localization `G[1/x]` of the cone. -/
noncomputable def awayX : Subalgebra k Ω :=
  away k (x k) 1 x_mem_component_one

/-- The functions on the affine open `D₊(y)` of the elliptic curve: the degree-zero part of the
localization `G[1/y]` of the cone. -/
noncomputable def awayY : Subalgebra k Ω :=
  away k (y k) 1 y_mem_component_one

/-- The functions on the intersection `D₊(x) ∩ D₊(y)` of the two affine opens of the elliptic
curve: the degree-zero part of the localization `G[1/(xy)]` of the cone. -/
noncomputable def awayXY : Subalgebra k Ω :=
  away k (x k * y k) 2 (mul_mem_component x_mem_component_one y_mem_component_one)

/-- A nonzero element of the cone has nonzero image in the fraction field. -/
private theorem algebraMap_ne_zero {g : Cone k} (hg : g ≠ 0) : ⟪g⟫ ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective (Cone k) Ω)).2 hg

/-- The image of `x` in the fraction field is nonzero. -/
theorem algebraMap_x_ne_zero : ⟪x k⟫ ≠ 0 :=
  algebraMap_ne_zero k (x_ne_zero k)

/-- The image of `y` in the fraction field is nonzero. -/
theorem algebraMap_y_ne_zero : ⟪y k⟫ ≠ 0 :=
  algebraMap_ne_zero k (y_ne_zero k)

/-- The image of `z` in the fraction field is nonzero. -/
theorem algebraMap_z_ne_zero : ⟪z k⟫ ≠ 0 :=
  algebraMap_ne_zero k (z_ne_zero k)

/-- The degree-zero part of the localization at a nonzero element `s` of degree one consists of the
fractions `g / sⁿ` with `g` homogeneous of degree `n`. -/
private theorem mem_away_one_iff {s : Cone k} (hs : ⟪s⟫ ≠ 0) (h : s ∈ component k 1) {t : Ω} :
    t ∈ away k s 1 h ↔ ∃ n, ∃ g ∈ component k n, t = ⟪g⟫ / ⟪s⟫ ^ n := by
  simp only [mem_away, one_mul]
  refine exists_congr fun n => exists_congr fun g => and_congr_right fun _ => ?_
  rw [eq_div_iff (pow_ne_zero _ hs), mul_comm]

/-- The functions on `D₊(x)` are the fractions `g / xⁿ` with `g` homogeneous of degree `n`. -/
theorem mem_awayX_iff {t : Ω} :
    t ∈ awayX k ↔ ∃ n, ∃ g ∈ component k n, t = ⟪g⟫ / ⟪x k⟫ ^ n :=
  mem_away_one_iff k (algebraMap_x_ne_zero k) _

/-- The functions on `D₊(y)` are the fractions `g / yⁿ` with `g` homogeneous of degree `n`. -/
theorem mem_awayY_iff {t : Ω} :
    t ∈ awayY k ↔ ∃ n, ∃ g ∈ component k n, t = ⟪g⟫ / ⟪y k⟫ ^ n :=
  mem_away_one_iff k (algebraMap_y_ne_zero k) _

/-- The functions on `D₊(x) ∩ D₊(y)` are the fractions `g / (xⁱ yʲ)` with `g` homogeneous of
degree `i + j`. -/
theorem mem_awayXY_iff {t : Ω} :
    t ∈ awayXY k ↔ ∃ i j, ∃ g ∈ component k (i + j), t = ⟪g⟫ / (⟪x k⟫ ^ i * ⟪y k⟫ ^ j) := by
  have hx := algebraMap_x_ne_zero k
  have hy := algebraMap_y_ne_zero k
  simp only [awayXY, mem_away]
  constructor
  · rintro ⟨n, g, hg, hgt⟩
    refine ⟨n, n, g, by simpa [two_mul] using hg, ?_⟩
    rw [eq_div_iff (by positivity), ← mul_pow, mul_comm, ← map_mul, hgt]
  · rintro ⟨i, j, g, hg, rfl⟩
    refine ⟨i + j, g * x k ^ j * y k ^ i, ?_, ?_⟩
    · convert mul_mem_component (mul_mem_component hg
        (pow_mem_component (x_mem_component_one (k := k)) j))
        (pow_mem_component (y_mem_component_one (k := k)) i) using 2
      ring
    · simp only [map_mul, map_pow]
      field_simp
      ring

/-- The function `e = z² / (xy)` on `D₊(x) ∩ D₊(y)`, whose class spans `H¹(E, 𝒪_E)`. -/
noncomputable def e : Ω :=
  ⟪z k⟫ ^ 2 / (⟪x k⟫ * ⟪y k⟫)

/-- Every function on `D₊(x)` restricts to a function on `D₊(x) ∩ D₊(y)`. -/
theorem awayX_le_awayXY : awayX k ≤ awayXY k := by
  intro t ht
  obtain ⟨n, g, hg, rfl⟩ := (mem_awayX_iff k).1 ht
  exact (mem_awayXY_iff k).2 ⟨n, 0, g, by simpa using hg, by simp⟩

/-- Every function on `D₊(y)` restricts to a function on `D₊(x) ∩ D₊(y)`. -/
theorem awayY_le_awayXY : awayY k ≤ awayXY k := by
  intro t ht
  obtain ⟨n, g, hg, rfl⟩ := (mem_awayY_iff k).1 ht
  exact (mem_awayXY_iff k).2 ⟨0, n, g, by simpa using hg, by simp⟩

/-- The function `e = z² / (xy)` is a function on `D₊(x) ∩ D₊(y)`. -/
theorem e_mem_awayXY : e k ∈ awayXY k :=
  (mem_awayXY_iff k).2 ⟨1, 1, z k ^ 2, by
    simpa using pow_mem_component (z_mem_component_one (k := k)) 2, by simp [e]⟩

end Away

section Decomposition

variable (k : Type*) [Field k]

local notation "Ω" => FractionRing (Cone k)

local notation "⟪" g "⟫" => algebraMap (Cone k) (FractionRing (Cone k)) g

/-- The `k`-subspace `O_x + O_y + k e` of the fraction field. -/
private noncomputable def decompositionSpace : Submodule k Ω :=
  Subalgebra.toSubmodule (awayX k) ⊔ Subalgebra.toSubmodule (awayY k) ⊔ k ∙ e k

/-- Every monomial fraction `xᵃ yᵇ zᶜ / (xy)ⁿ` of degree zero lies in `O_x + O_y + k e`. -/
private theorem monomial_div_mem_decompositionSpace (c : ℕ) :
    ∀ a b n, a + b + c = 2 * n →
      ⟪x k ^ a * y k ^ b * z k ^ c⟫ / (⟪x k⟫ * ⟪y k⟫) ^ n ∈ decompositionSpace k := by
  have hx := algebraMap_x_ne_zero k
  have hy := algebraMap_y_ne_zero k
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro a b n habc
  by_cases hc : 3 ≤ c
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le' hc
    have hrel : x k ^ a * y k ^ b * z k ^ (c + 3) = -(x k ^ a * y k ^ (b + 2) * z k ^ (c + 1)) -
        x k ^ (a + 1) * y k ^ (b + 1) * z k ^ (c + 1) - x k ^ (a + 3) * y k ^ b * z k ^ c := by
      linear_combination (x k ^ a * y k ^ b * z k ^ c) * equation_eq_zero k
    rw [hrel, map_sub, map_sub, map_neg, sub_div, sub_div, neg_div]
    refine sub_mem (sub_mem (neg_mem (ih _ (by omega) _ _ _ (by omega)))
      (ih _ (by omega) _ _ _ (by omega))) (ih _ (by omega) _ _ _ (by omega))
  by_cases ha : n ≤ a
  · obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le ha
    refine Submodule.mem_sup_left (Submodule.mem_sup_right ?_)
    refine (mem_awayY_iff k).2 ⟨n, x k ^ a * y k ^ b * z k ^ c, ?_, ?_⟩
    · convert monomial_mem_component (k := k) a b c using 2
      omega
    · simp only [map_mul, map_pow]
      field_simp
      ring
  by_cases hb : n ≤ b
  · obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hb
    refine Submodule.mem_sup_left (Submodule.mem_sup_left ?_)
    refine (mem_awayX_iff k).2 ⟨n, x k ^ a * y k ^ b * z k ^ c, ?_, ?_⟩
    · convert monomial_mem_component (k := k) a b c using 2
      omega
    · simp only [map_mul, map_pow]
      field_simp
      ring
  obtain ⟨rfl, rfl, rfl⟩ : c = 2 ∧ n = a + 1 ∧ b = a := by omega
  refine Submodule.mem_sup_right (Submodule.mem_span_singleton.2 ⟨1, ?_⟩)
  simp only [one_smul, e, map_mul, map_pow]
  field_simp
  ring

/-- **Functions on `D₊(x) ∩ D₊(y)`.** Every function on `D₊(x) ∩ D₊(y)` is the sum of a function
on `D₊(x)`, a function on `D₊(y)` and a constant multiple of `e = z² / (xy)`. -/
theorem exists_eq_add_add_smul_e {t : Ω} (ht : t ∈ awayXY k) :
    ∃ a ∈ awayX k, ∃ b ∈ awayY k, ∃ l : k, t = a + b + l • e k := by
  have hmem : t ∈ decompositionSpace k := by
    obtain ⟨n, g, hg, hgt⟩ := (mem_away k).1 ht
    have ht' : t = ⟪g⟫ / (⟪x k⟫ * ⟪y k⟫) ^ n := by
      rw [eq_div_iff (pow_ne_zero _ (mul_ne_zero (algebraMap_x_ne_zero k)
        (algebraMap_y_ne_zero k))), mul_comm, ← hgt, map_mul]
    rw [ht']
    refine component_induction (P := fun g => ⟪g⟫ / (⟪x k⟫ * ⟪y k⟫) ^ n ∈ decompositionSpace k)
      (by simp) (fun g h hg hh => by simpa [add_div] using add_mem hg hh) (fun r g hg => ?_)
      (fun a b c habc => monomial_div_mem_decompositionSpace k c a b n (by omega)) hg
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, mul_div_assoc,
      ← Algebra.smul_def]
    exact Submodule.smul_mem _ r hg
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hu
  obtain ⟨l, rfl⟩ := Submodule.mem_span_singleton.1 hw
  exact ⟨a, ha, b, hb, l, rfl⟩

/-- **`e` is not a coboundary.** The function `e = z² / (xy)` on `D₊(x) ∩ D₊(y)` is not the sum of
a function on `D₊(x)` and a function on `D₊(y)`. -/
theorem e_ne_add {a b : Ω} (ha : a ∈ awayX k) (hb : b ∈ awayY k) : e k ≠ a + b := by
  intro he
  obtain ⟨i, g, -, hg⟩ := (mem_away k).1 ha
  obtain ⟨j, h, -, hh⟩ := (mem_away k).1 hb
  have hx := algebraMap_x_ne_zero k
  have hy := algebraMap_y_ne_zero k
  have he' : ⟪z k⟫ ^ 2 = (a + b) * (⟪x k⟫ * ⟪y k⟫) := by
    rw [← he, e, div_mul_cancel₀ _ (mul_ne_zero hx hy)]
  have hrel : x k ^ i * y k ^ j * z k ^ 2 =
      g * (x k * y k ^ (j + 1)) + h * (x k ^ (i + 1) * y k) := by
    apply IsFractionRing.injective (Cone k) Ω
    simp only [map_mul, map_pow, map_add, ← hg, ← hh]
    linear_combination (⟪x k⟫ ^ i * ⟪y k⟫ ^ j) * he'
  have key : ∀ u m, coordZSq k (u * AdjoinRoot.of _ m) = m * coordZSq k u := fun u m => by
    rw [mul_comm, ← AdjoinRoot.algebraMap_eq, ← Algebra.smul_def, map_smul, smul_eq_mul]
  have := congrArg (fun u => coordZSq k (toAdjoinRoot k u)) hrel
  simp only [map_mul, map_pow, map_add, toAdjoinRoot, lift_x, lift_y, lift_z] at this
  rw [← map_pow, ← map_pow, ← map_mul, coordZSq_smul_root_sq, ← map_pow, ← map_pow, ← map_mul,
    ← map_mul (AdjoinRoot.of _) (X 0 ^ (i + 1)), key, key] at this
  -- Compare the coefficients of `x^i y^j` in `k[x, y]`.
  set s : Fin 2 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 j
  have hmon : ∀ a b : ℕ, (X 0 ^ a * X 1 ^ b : MvPolynomial (Fin 2) k) =
      monomial (Finsupp.single 0 a + Finsupp.single 1 b) 1 := fun a b => by
    rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul]
  have h1 : coeff s (X 0 ^ i * X 1 ^ j : MvPolynomial (Fin 2) k) = 1 := by
    rw [hmon, coeff_monomial, if_pos rfl]
  have h2 : ∀ P : MvPolynomial (Fin 2) k, coeff s (X 0 * X 1 ^ (j + 1) * P) = 0 := fun P => by
    rw [← pow_one (X 0 : MvPolynomial (Fin 2) k), hmon, coeff_monomial_mul', if_neg]
    intro hle
    have := hle 1
    simp [s] at this
  have h3 : ∀ P : MvPolynomial (Fin 2) k, coeff s (X 0 ^ (i + 1) * X 1 * P) = 0 := fun P => by
    rw [← pow_one (X 1 : MvPolynomial (Fin 2) k), hmon, coeff_monomial_mul', if_neg]
    intro hle
    have := hle 0
    simp [s] at this
  have := congrArg (coeff s) this
  rw [h1, coeff_add, h2, h3, add_zero] at this
  exact one_ne_zero this

end Decomposition

section Cocycle

variable (k : Type*) [Field k] [CharP k 2]

local notation "Ω" => FractionRing (Cone k)

local notation "⟪" g "⟫" => algebraMap (Cone k) (FractionRing (Cone k)) g

/-- Over a field of characteristic two, the fraction field of the cone has characteristic two. -/
instance charP_fractionRing : CharP Ω 2 :=
  charP_of_injective_algebraMap (algebraMap k Ω).injective 2

/-- **The Hasse invariant of `E` is one.** In characteristic two,
`e² = e + z² / x² + x z / y²`, with `z² / x²` a function on `D₊(x)` and `x z / y²` a function on
`D₊(y)`: the Frobenius acts as the identity on `H¹(E, 𝒪_E)`. -/
theorem e_sq : e k ^ 2 = e k + ⟪z k⟫ ^ 2 / ⟪x k⟫ ^ 2 + ⟪x k⟫ * ⟪z k⟫ / ⟪y k⟫ ^ 2 := by
  have hx := algebraMap_x_ne_zero k
  have hy := algebraMap_y_ne_zero k
  have h := congrArg (algebraMap (Cone k) Ω) (equation_eq_zero k)
  simp only [map_add, map_mul, map_pow, map_zero] at h
  have h2 : (2 : Ω) = 0 := CharTwo.two_eq_zero
  rw [e, div_pow, mul_pow, div_add_div _ _ (mul_ne_zero hx hy) (pow_ne_zero 2 hx),
    div_add_div _ _ (mul_ne_zero (mul_ne_zero hx hy) (pow_ne_zero 2 hx)) (pow_ne_zero 2 hy),
    div_eq_div_iff (mul_ne_zero (pow_ne_zero 2 hx) (pow_ne_zero 2 hy))
      (mul_ne_zero (mul_ne_zero (mul_ne_zero hx hy) (pow_ne_zero 2 hx)) (pow_ne_zero 2 hy))]
  linear_combination (⟪x k⟫ ^ 3 * ⟪y k⟫ ^ 3 * ⟪z k⟫) * h -
    (⟪x k⟫ ^ 3 * ⟪y k⟫ ^ 3 * (⟪y k⟫ ^ 2 * ⟪z k⟫ ^ 2 + ⟪x k⟫ * ⟪y k⟫ * ⟪z k⟫ ^ 2 +
      ⟪x k⟫ ^ 3 * ⟪z k⟫)) * h2

omit [CharP k 2] in
/-- The function `(z / x)²` is a function on `D₊(x)`. -/
theorem sq_z_div_x_mem_awayX : (⟪z k⟫ / ⟪x k⟫) ^ 2 ∈ awayX k :=
  (mem_awayX_iff k).2 ⟨2, z k ^ 2, by
    simpa using pow_mem_component (z_mem_component_one (k := k)) 2, by simp [div_pow]⟩

omit [CharP k 2] in
/-- The function `x z / y²` is a function on `D₊(y)`. -/
theorem x_mul_z_div_sq_y_mem_awayY : ⟪x k⟫ * ⟪z k⟫ / ⟪y k⟫ ^ 2 ∈ awayY k :=
  (mem_awayY_iff k).2 ⟨2, x k * z k, by
    simpa using mul_mem_component (x_mem_component_one (k := k)) z_mem_component_one, by simp⟩

/-- **An Artin–Schreier–Witt cocycle on the ordinary elliptic curve.** Let `k` be a field of
characteristic two in which every element has the form `μ² + μ`. There are Witt vectors `a_x`,
`a_y` and `c` over the fraction field of the cone, with coefficients in the functions on `D₊(x)`,
on `D₊(y)` and on `D₊(x) ∩ D₊(y)` respectively, such that `a_y - a_x = F c - c`, with zeroth
coefficients `(z / x)²`, `x z / y²` and `e = z² / (xy)`. -/
theorem exists_wittVector_cocycle (hk : ∀ l : k, ∃ μ : k, μ ^ 2 + μ = l) :
    ∃ aX ∈ WittVector.coeffSubring 2 (awayX k).toSubring,
      ∃ aY ∈ WittVector.coeffSubring 2 (awayY k).toSubring,
        ∃ c ∈ WittVector.coeffSubring 2 (awayXY k).toSubring,
          aX.coeff 0 = (⟪z k⟫ / ⟪x k⟫) ^ 2 ∧ aY.coeff 0 = ⟪x k⟫ * ⟪z k⟫ / ⟪y k⟫ ^ 2 ∧
            c.coeff 0 = e k ∧ aY - aX = WittVector.frobenius c - c := by
  have hH := WittVector.exists_sub_eq_add_pow_sub_self_of_eq_add_smul (p := 2) (O₁ := awayX k)
    (O₂ := awayY k) (e_mem_awayXY k)
    (fun l => by
      obtain ⟨μ, hμ⟩ := hk l
      exact ⟨μ, by rw [CharTwo.sub_eq_add, hμ]⟩)
    (fun ε hε => by
      obtain ⟨a, ha, b, hb, l, rfl⟩ := exists_eq_add_add_smul_e k hε
      exact ⟨-a, neg_mem ha, b, hb, l, by ring⟩)
    ⟨-(⟪z k⟫ / ⟪x k⟫) ^ 2, neg_mem (sq_z_div_x_mem_awayX k), ⟪x k⟫ * ⟪z k⟫ / ⟪y k⟫ ^ 2,
      x_mul_z_div_sq_y_mem_awayY k, by rw [e_sq, div_pow]; ring⟩
  obtain ⟨aX, haX, aY, haY, c, hc, h0X, h0Y, h0c, hsol⟩ :=
    WittVector.exists_sub_eq_frobenius_sub_self (p := 2) (O₁ := (awayX k).toSubring)
      (O₂ := (awayY k).toSubring) (O₁₂ := (awayXY k).toSubring) (awayX_le_awayXY k)
      (awayY_le_awayXY k) hH (α₀ := (⟪z k⟫ / ⟪x k⟫) ^ 2) (sq_z_div_x_mem_awayX k)
      (x_mul_z_div_sq_y_mem_awayY k) (e_mem_awayXY k) (by
        have h2 : (2 : Ω) = 0 := CharTwo.two_eq_zero
        rw [e_sq]
        linear_combination (-(⟪z k⟫ / ⟪x k⟫) ^ 2) * h2)
  exact ⟨aX, haX, aY, haY, c, hc, h0X, h0Y, h0c, hsol⟩

end Cocycle

end Cone

end Stacks.Examples.OrdinaryCone
