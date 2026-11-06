module

public import StacksFrontier.NumberTheory.Drinfeld.AutomorphismCuspForm
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.Algebra.Polynomial.SpecificDegree

/-!
# The function field of `y² + y = x³ + x + 1` over `𝔽₂`

We study the function field `K = 𝔽₂(x)[y] / (y² + y + x³ + x + 1)` of the supersingular elliptic
curve `E : y² + y = x³ + x + 1` over `𝔽₂`, and the automorphism `α : x ↦ x + 1, y ↦ y + x` of
`K` (an automorphism of `E` of order `4` fixing the origin).

## Main definitions

* `Stacks.Drinfeld.SupersingularCurve.K` — the function field.
* `Stacks.Drinfeld.SupersingularCurve.x`, `Stacks.Drinfeld.SupersingularCurve.y` — the
  coordinates, with `y² + y = x³ + x + 1`.
* `Stacks.Drinfeld.SupersingularCurve.alpha` — the automorphism `x ↦ x + 1, y ↦ y + x`.
* `Stacks.Drinfeld.SupersingularCurve.iota` — the hyperelliptic involution `y ↦ y + 1`.
-/

@[expose] public noncomputable section

open Polynomial Stacks.Adeles Stacks.Adeles.GlobalFunctionField IntermediateField

namespace Stacks.Drinfeld.SupersingularCurve

/-- `x³ + x + 1 ∈ 𝔽₂[x]`. -/
public def cub : (ZMod 2)[X] := X ^ 3 + X + 1

/-- The polynomial `Y² + Y + (x³ + x + 1)` over `𝔽₂(x)`. -/
public def eqn : (RatFunc (ZMod 2))[X] :=
  X ^ 2 + X + C (algebraMap (ZMod 2)[X] (RatFunc (ZMod 2)) cub)

/-- The polynomial `eqn` has degree `2`. -/
public theorem natDegree_eqn : eqn.natDegree = 2 := by
  unfold eqn; compute_degree!

/-- The polynomial `eqn` is monic. -/
public theorem eqn_monic : eqn.Monic := by
  unfold eqn; monicity!

/-- The polynomial `eqn` is nonzero. -/
public theorem eqn_ne_zero : eqn ≠ 0 := eqn_monic.ne_zero

/-- The polynomial `eqn` has no root in `𝔽₂(x)`. -/
public theorem not_isRoot_eqn (r : RatFunc (ZMod 2)) : ¬ eqn.IsRoot r := by
  intro hr
  have hmon : (X ^ 2 + X + C cub : ((ZMod 2)[X])[X]).Monic := by monicity!
  have hroot : aeval r (X ^ 2 + X + C cub : ((ZMod 2)[X])[X]) = 0 := by
    simpa [eqn, IsRoot, aeval_def] using hr
  obtain ⟨a, ha⟩ := isInteger_of_is_root_of_monic hmon hroot
  rw [← ha] at hroot
  have h0 : a ^ 2 + a + cub = 0 := by
    apply IsFractionRing.injective (ZMod 2)[X] (RatFunc (ZMod 2))
    simpa [aeval_def, eval₂_add, eval₂_pow] using hroot
  have h1 := congrArg (Polynomial.eval 0) h0
  simp only [cub, eval_add, eval_pow, eval_X, eval_one, eval_zero] at h1
  have : ∀ t : ZMod 2, t ^ 2 + t + (0 ^ 3 + 0 + 1) ≠ 0 := by decide
  exact this _ h1

/-- The polynomial `eqn` is irreducible over `𝔽₂(x)`. -/
public theorem irreducible_eqn : Irreducible eqn :=
  irreducible_of_degree_le_three_of_not_isRoot (by rw [natDegree_eqn]; decide) not_isRoot_eqn

/-- The irreducibility of `eqn`, as an instance. -/
public instance : Fact (Irreducible eqn) := ⟨irreducible_eqn⟩

/-- The function field of `y² + y = x³ + x + 1` over `𝔽₂`. -/
public abbrev K : Type := AdjoinRoot eqn

/-- `K` is finite-dimensional over `𝔽₂(x)`. -/
public instance : FiniteDimensional (RatFunc (ZMod 2)) K :=
  (AdjoinRoot.powerBasis' eqn_monic).finite

/-- `K` is a function field over `𝔽₂`. -/
public instance : FunctionField (ZMod 2) K := inferInstanceAs (FiniteDimensional _ _)

/-- The coordinate `x`. -/
public def x : K := algebraMap (RatFunc (ZMod 2)) K RatFunc.X

/-- The coordinate `y`. -/
public def y : K := AdjoinRoot.root eqn

/-- `x` is the generator `gen (ZMod 2) K` of the rational function field inside `K`. -/
public theorem x_eq_gen : x = gen (ZMod 2) K := rfl

/-- `K` has characteristic `2`: `2 = 0` in `K`. -/
public theorem two_eq_zero : (2 : K) = 0 := by
  rw [← map_ofNat (algebraMap (ZMod 2) K) 2, show (OfNat.ofNat 2 : ZMod 2) = 0 from rfl, map_zero]

/-- The image of `x³ + x + 1 ∈ 𝔽₂[x]` in `K` is `x ^ 3 + x + 1`. -/
public theorem algebraMap_cub : algebraMap (RatFunc (ZMod 2)) K
    (algebraMap (ZMod 2)[X] (RatFunc (ZMod 2)) cub) = x ^ 3 + x + 1 := by
  simp [cub, x]

/-- `y² + y = x³ + x + 1`. -/
public theorem y_sq_add_y : y ^ 2 + y = x ^ 3 + x + 1 := by
  have h : aeval y eqn = 0 := AdjoinRoot.eval₂_root eqn
  simp only [eqn, map_add, map_pow, aeval_X, aeval_C] at h
  rw [algebraMap_cub] at h
  rw [← sub_eq_zero, ← h]
  linear_combination (-(x ^ 3 + x + 1)) * two_eq_zero

/-- The embedding `𝔽₂(x) → K`. -/
public abbrev ofR : RatFunc (ZMod 2) →+* K := algebraMap (RatFunc (ZMod 2)) K

/-- The image in `K` of a polynomial `f ∈ 𝔽₂[x]` is `f(x)`. -/
public theorem ofR_algebraMap (f : (ZMod 2)[X]) :
    ofR (algebraMap (ZMod 2)[X] (RatFunc (ZMod 2)) f) = aeval x f := by
  have h := Polynomial.ringHom_ext (f := ofR.comp (algebraMap (ZMod 2)[X] (RatFunc (ZMod 2))))
    (g := (aeval x).toRingHom) (fun a => by
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
      rw [show C a = algebraMap (ZMod 2) (ZMod 2)[X] a from rfl,
        ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply])
    (by simp [x, RatFunc.algebraMap_X])
  exact congrArg (fun φ : (ZMod 2)[X] →+* K => φ f) h

/-- `z + z = 0` for every `z ∈ K`. -/
public theorem char_two (z : K) : z + z = 0 := by
  rw [← two_mul, two_eq_zero, zero_mul]

/-- `-z = z` for every `z ∈ K`. -/
public theorem neg_eq_self (z : K) : -z = z := by
  rw [neg_eq_iff_add_eq_zero, char_two]

/-- Every element of `K` is `a + b y` with `a, b ∈ 𝔽₂(x)`. -/
public theorem exists_eq_add_mul_y (z : K) : ∃ a b : RatFunc (ZMod 2), z = ofR a + ofR b * y := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  have hmod : AdjoinRoot.mk eqn p = AdjoinRoot.mk eqn (p %ₘ eqn) := by
    rw [AdjoinRoot.mk_eq_mk]
    refine ⟨p /ₘ eqn, ?_⟩
    have := modByMonic_add_div p eqn
    linear_combination this.symm
  have hdeg : (p %ₘ eqn).degree ≤ 1 := by
    have := degree_modByMonic_lt p eqn_monic
    rw [degree_eq_natDegree eqn_ne_zero, natDegree_eqn] at this
    exact Order.le_of_lt_succ this
  rw [hmod, eq_X_add_C_of_degree_le_one hdeg]
  refine ⟨(p %ₘ eqn).coeff 0, (p %ₘ eqn).coeff 1, ?_⟩
  simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
  rw [add_comm]
  rfl

/-- `y` does not lie in `𝔽₂(x)`. -/
public theorem y_notMem_range (a : RatFunc (ZMod 2)) : ofR a ≠ y := by
  intro h
  apply not_isRoot_eqn a
  apply (algebraMap (RatFunc (ZMod 2)) K).injective
  have h0 : aeval y eqn = 0 := AdjoinRoot.eval₂_root eqn
  rw [← h, aeval_algebraMap_apply] at h0
  have := (map_eq_zero_iff _ (algebraMap (RatFunc (ZMod 2)) K).injective).1 h0
  rw [coe_aeval_eq_eval] at this
  exact congrArg _ this

/-- `1` and `y` are linearly independent over `𝔽₂(x)`: `a + b y = 0` forces `a = b = 0`. -/
public theorem add_mul_y_eq_zero {a b : RatFunc (ZMod 2)} (h : ofR a + ofR b * y = 0) :
    a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · subst hb
    simpa using h
  · exfalso
    apply y_notMem_range (-a / b)
    rw [map_div₀, map_neg, div_eq_iff ((_root_.map_ne_zero _).2 hb)]
    linear_combination -h

/-- Evaluating `eqn` along `f : 𝔽₂(x) → K` at `t` gives `t² + t + f(x³ + x + 1)`. -/
public theorem eval₂_eqn (f : RatFunc (ZMod 2) →+* K) (t : K) :
    eqn.eval₂ f t = t ^ 2 + t + f (algebraMap (ZMod 2)[X] (RatFunc (ZMod 2)) cub) := by
  simp [eqn, eval₂_add, eval₂_pow, eval₂_X, eval₂_C]

/-- `σ₀ : 𝔽₂(x) ≃ 𝔽₂(x)`, `x ↦ x + 1`. -/
public def sigma0 : RatFunc (ZMod 2) ≃+* RatFunc (ZMod 2) :=
  IsFractionRing.ringEquivOfRingEquiv (algEquivAevalXAddC (1 : ZMod 2)).toRingEquiv

/-- `σ₀` sends a polynomial `f(x)` to `f(x + 1)`. -/
public theorem sigma0_algebraMap (f : (ZMod 2)[X]) :
    sigma0 (algebraMap (ZMod 2)[X] (RatFunc (ZMod 2)) f) =
      algebraMap (ZMod 2)[X] (RatFunc (ZMod 2)) (f.comp (X + C 1)) := by
  rw [sigma0, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  rfl

/-- The image in `K` of `σ₀ f` is `f(x + 1)`, for a polynomial `f`. -/
public theorem ofR_sigma0_algebraMap (f : (ZMod 2)[X]) :
    ofR (sigma0 (algebraMap (ZMod 2)[X] (RatFunc (ZMod 2)) f)) = aeval (x + 1) f := by
  rw [sigma0_algebraMap, ofR_algebraMap, aeval_comp]
  simp

/-- The ring endomorphism `x ↦ x + 1`, `y ↦ y + x` of `K`. -/
public def alphaHom : K →+* K :=
  AdjoinRoot.lift (ofR.comp sigma0.toRingHom) (y + x) (by
    rw [eval₂_eqn, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      ofR_sigma0_algebraMap]
    simp only [cub, map_add, map_pow, aeval_X, map_one]
    have h := y_sq_add_y
    linear_combination h + (x ^ 3 + 2 * x ^ 2 + 3 * x + 2 + x * y) * two_eq_zero)

/-- `alphaHom` restricts to `σ₀` on `𝔽₂(x)`. -/
public theorem alphaHom_ofR (a : RatFunc (ZMod 2)) : alphaHom (ofR a) = ofR (sigma0 a) :=
  AdjoinRoot.lift_of _

/-- `alphaHom y = y + x`. -/
public theorem alphaHom_y : alphaHom y = y + x := AdjoinRoot.lift_root _

/-- `alphaHom x = x + 1`. -/
public theorem alphaHom_x : alphaHom x = x + 1 := by
  change alphaHom (ofR RatFunc.X) = x + 1
  rw [alphaHom_ofR, ← RatFunc.algebraMap_X, ofR_sigma0_algebraMap, aeval_X]

/-- `alphaHom` is bijective. -/
public theorem alphaHom_bijective : Function.Bijective alphaHom := by
  refine ⟨alphaHom.injective, fun z => ?_⟩
  obtain ⟨a, b, rfl⟩ := exists_eq_add_mul_y z
  refine ⟨ofR (sigma0.symm a) + ofR (sigma0.symm b) * (y + x + 1), ?_⟩
  rw [map_add, map_mul, alphaHom_ofR, alphaHom_ofR, RingEquiv.apply_symm_apply,
    RingEquiv.apply_symm_apply, map_add, map_add, alphaHom_y, alphaHom_x, map_one]
  linear_combination (ofR b) * (x + 1) * two_eq_zero

/-- The automorphism `α : x ↦ x + 1, y ↦ y + x` of `K`. -/
public def alpha : K ≃+* K := RingEquiv.ofBijective alphaHom alphaHom_bijective

/-- The automorphism `α` acts as `alphaHom`. -/
public theorem alpha_apply (z : K) : alpha z = alphaHom z := rfl

/-- The ring endomorphism `y ↦ y + 1` of `K` over `𝔽₂(x)`. -/
public def iotaHom : K →+* K :=
  AdjoinRoot.lift ofR (y + 1) (by
    rw [eval₂_eqn, show ofR (algebraMap (ZMod 2)[X] (RatFunc (ZMod 2)) cub) = x ^ 3 + x + 1 from
      algebraMap_cub]
    have h := y_sq_add_y
    linear_combination h + (x ^ 3 + x + 2 + y) * two_eq_zero)

/-- `iotaHom` is the identity on `𝔽₂(x)`. -/
public theorem iotaHom_ofR (a : RatFunc (ZMod 2)) : iotaHom (ofR a) = ofR a :=
  AdjoinRoot.lift_of _

/-- `iotaHom y = y + 1`. -/
public theorem iotaHom_y : iotaHom y = y + 1 := AdjoinRoot.lift_root _

/-- `iotaHom` is an involution. -/
public theorem iotaHom_iotaHom (z : K) : iotaHom (iotaHom z) = z := by
  obtain ⟨a, b, rfl⟩ := exists_eq_add_mul_y z
  simp only [map_add, map_mul, iotaHom_ofR, iotaHom_y, map_one]
  linear_combination (ofR b) * two_eq_zero

/-- The hyperelliptic involution `y ↦ y + 1` of `K`. -/
public def iota : K ≃+* K where
  toFun := iotaHom
  invFun := iotaHom
  left_inv := iotaHom_iotaHom
  right_inv := iotaHom_iotaHom
  map_mul' := map_mul _
  map_add' := map_add _

/-- The involution `ι` acts as `iotaHom`. -/
public theorem iota_apply (z : K) : iota z = iotaHom z := rfl

/-- `ι` is the identity on `𝔽₂(x)`. -/
public theorem iota_ofR (a : RatFunc (ZMod 2)) : iota (ofR a) = ofR a := iotaHom_ofR a

/-- `ι x = x`. -/
public theorem iota_x : iota x = x := iotaHom_ofR _

/-- The trace of `a + b y` to `𝔽₂(x)`: `(a + b y) + ι(a + b y) = b`. -/
public theorem add_iota (a b : RatFunc (ZMod 2)) :
    (ofR a + ofR b * y) + iota (ofR a + ofR b * y) = ofR b := by
  rw [iota_apply]
  simp only [map_add, map_mul, iotaHom_ofR, iotaHom_y]
  linear_combination (ofR a + ofR b * y) * two_eq_zero

/-- The norm of `a + b y` to `𝔽₂(x)`: `(a + b y) ι(a + b y) = a² + a b + b² (x³ + x + 1)`. -/
public theorem mul_iota (a b : RatFunc (ZMod 2)) :
    (ofR a + ofR b * y) * iota (ofR a + ofR b * y) =
      ofR (a ^ 2 + a * b + b ^ 2 * algebraMap (ZMod 2)[X] (RatFunc (ZMod 2)) cub) := by
  rw [iota_apply]
  simp only [map_add, map_mul, iotaHom_ofR, iotaHom_y, map_pow, algebraMap_cub]
  have h := y_sq_add_y
  linear_combination (ofR b) ^ 2 * h + (ofR a * ofR b * y) * two_eq_zero

section Places

/-- A subring of `K` containing `𝔽₂` and `x` contains `f(x)` for every polynomial `f`. -/
private theorem aeval_x_mem_of_mem {S : Subring K} (hC : ∀ a : ZMod 2, algebraMap (ZMod 2) K a ∈ S)
    (hx : x ∈ S) (f : (ZMod 2)[X]) : aeval x f ∈ S := by
  induction f using Polynomial.induction_on with
  | C a => rw [aeval_C]; exact hC a
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n a _ =>
    rw [map_mul, map_pow, aeval_X, aeval_C]
    exact mul_mem (hC a) (pow_mem hx _)

/-- `f(x)` lies in the intermediate field `𝔽₂⟮x⟯` of `K`, for every polynomial `f`. -/
public theorem aeval_x_mem_adjoin (f : (ZMod 2)[X]) : aeval x f ∈ (ZMod 2)⟮x⟯ :=
  aeval_x_mem_of_mem (S := (ZMod 2)⟮x⟯.toSubfield.toSubring)
    (IntermediateField.algebraMap_mem _) (IntermediateField.mem_adjoin_simple_self _ x) f

/-- The image of `𝔽₂(x)` in `K` lies in the intermediate field `𝔽₂⟮x⟯`. -/
public theorem ofR_mem_adjoin (a : RatFunc (ZMod 2)) : ofR a ∈ (ZMod 2)⟮x⟯ := by
  rw [← RatFunc.num_div_denom a, map_div₀, ofR_algebraMap, ofR_algebraMap]
  exact div_mem (aeval_x_mem_adjoin _) (aeval_x_mem_adjoin _)

/-- `[K : 𝔽₂(x)] ≤ 2`. -/
public theorem finrank_adjoin_x_le : Module.finrank (ZMod 2)⟮x⟯ K ≤ 2 := by
  classical
  have hspan : Submodule.span (ZMod 2)⟮x⟯ (({1, y} : Finset K) : Set K) = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨a, b, rfl⟩ := exists_eq_add_mul_y z
    have h1 : (1 : K) ∈ Submodule.span (ZMod 2)⟮x⟯ (({1, y} : Finset K) : Set K) :=
      Submodule.subset_span (by simp)
    have h2 : y ∈ Submodule.span (ZMod 2)⟮x⟯ (({1, y} : Finset K) : Set K) :=
      Submodule.subset_span (by simp)
    have e1 : ofR a = (⟨ofR a, ofR_mem_adjoin a⟩ : (ZMod 2)⟮x⟯) • (1 : K) := by
      rw [Algebra.smul_def, mul_one]; rfl
    have e2 : ofR b * y = (⟨ofR b, ofR_mem_adjoin b⟩ : (ZMod 2)⟮x⟯) • y := by
      rw [Algebra.smul_def]; rfl
    rw [e1, e2]
    exact add_mem (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ h2)
  have := finrank_span_finset_le_card (R := (ZMod 2)⟮x⟯) ({1, y} : Finset K)
  rw [Set.finrank, hspan, finrank_top] at this
  exact this.trans (Finset.card_le_two)

/-- A place containing `x` contains `y`. -/
public theorem y_mem_of_x_mem {v : Place K} (hx : x ∈ v.1) : y ∈ v.1 := by
  by_contra hy
  have hinv : y⁻¹ ∈ v.1 := (v.1.mem_or_inv_mem y).resolve_left hy
  have hy0 : y ≠ 0 := fun h => hy (h ▸ v.1.zero_mem)
  have hc : y ^ 2 + y ∈ v.1 := by
    rw [y_sq_add_y]; exact add_mem (add_mem (pow_mem hx 3) hx) v.1.one_mem
  have e : y = (y ^ 2 + y) * y⁻¹ - 1 := by field_simp; ring
  exact hy (e ▸ sub_mem (mul_mem hc hinv) v.1.one_mem)

/-- A field with two elements has only `0` and `1`. -/
public theorem eq_zero_or_eq_one_of_card_eq_two {R : Type*} [Field R] (h : Nat.card R = 2)
    (t : R) : t = 0 ∨ t = 1 := by
  classical
  have : Finite R := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  let := Fintype.ofFinite R
  by_contra ht
  push Not at ht
  have hcard : ({0, 1, t} : Finset R).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [ht.1.symm]), Finset.card_pair ht.2.symm]
  have := Finset.card_le_univ ({0, 1, t} : Finset R)
  rw [hcard, ← Nat.card_eq_fintype_card, h] at this
  omega

/-- No place containing `x` has residue field `𝔽₂`: the curve has no affine `𝔽₂`-point. -/
public theorem resCard_ne_two_of_x_mem {v : Place K} (hx : x ∈ v.1) : v.resCard ≠ 2 := by
  intro h2
  have hy := y_mem_of_x_mem hx
  set R := IsLocalRing.ResidueField v.1
  set X' : R := IsLocalRing.residue v.1 ⟨x, hx⟩
  set Y' : R := IsLocalRing.residue v.1 ⟨y, hy⟩
  have hrel : Y' ^ 2 + Y' = X' ^ 3 + X' + 1 := by
    have e : (⟨y, hy⟩ : v.1) ^ 2 + ⟨y, hy⟩ = ⟨x, hx⟩ ^ 3 + ⟨x, hx⟩ + 1 :=
      Subtype.ext (by simpa using y_sq_add_y)
    have := congrArg (IsLocalRing.residue v.1) e
    rw [map_add, map_pow, map_add, map_add, map_pow, map_one] at this
    exact this
  have h01 := eq_zero_or_eq_one_of_card_eq_two (R := R) h2
  have hsq : ∀ t : R, t ^ 2 = t := fun t => by rcases h01 t with rfl | rfl <;> simp
  have hcube : X' ^ 3 = X' := by rcases h01 X' with h | h <;> rw [h] <;> simp
  have htwo : (2 : R) = 0 := by
    rcases h01 2 with h | h
    · exact h
    · exfalso
      have : (1 : R) = 0 := by linear_combination h
      exact one_ne_zero this
  exact one_ne_zero (by linear_combination -hrel + hsq Y' - hcube + (Y' - X') * htwo : (1 : R) = 0)

/-- `ord(a + b) = ord a` if `ord a < ord b`. -/
public theorem ord_add_eq_of_lt {v : Place K} {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : v.ord a < v.ord b) : v.ord (a + b) = v.ord a := by
  have hlt : v.normVal b < v.normVal a := by
    rw [Place.normVal_eq_exp ha, Place.normVal_eq_exp hb, WithZero.exp_lt_exp]
    omega
  rw [Place.ord, Valuation.map_add_eq_of_lt_left _ hlt, Place.ord]

/-- At a place not containing `x`, `x` has a pole. -/
public theorem ord_x_neg {v : Place K} (hx : x ∉ v.1) : v.ord x < 0 :=
  ord_gen_neg_of_notMem (ZMod 2) hx

/-- `x ≠ 0`. -/
public theorem x_ne_zero : x ≠ 0 := gen_ne_zero (ZMod 2) K

/-- `f(x) ≠ 0` for a nonzero polynomial `f`, as `x` is transcendental over `𝔽₂`. -/
private theorem aeval_x_ne_zero {f : (ZMod 2)[X]} (hf : f ≠ 0) : aeval x f ≠ 0 := fun h0 =>
  hf ((transcendental_iff_injective.1 (gen_transcendental (ZMod 2) K)) (h0.trans (map_zero _).symm))

/-- `x³ + x + 1 ≠ 0`, proved before `y_ne_zero` needs it. -/
private theorem cub_ne_zero_aux : x ^ 3 + x + 1 ≠ 0 :=
  fun h => aeval_x_ne_zero (f := X ^ 3 + X + 1)
    (by monicity! : (X ^ 3 + X + 1 : (ZMod 2)[X]).Monic).ne_zero (by simpa)

/-- `y ≠ 0`. -/
public theorem y_ne_zero : y ≠ 0 := fun h => by
  have e := y_sq_add_y
  rw [h] at e
  exact cub_ne_zero_aux (by linear_combination -e)

/-- `ord_v 1 = 0` at every place `v`. -/
public theorem ord_one (v : Place K) : v.ord 1 = 0 := by simp [Place.ord]

/-- `x + 1 ≠ 0`. -/
public theorem x_add_one_ne_zero : x + 1 ≠ 0 := fun h =>
  aeval_x_ne_zero (f := X + 1) (by monicity! : (X + 1 : (ZMod 2)[X]).Monic).ne_zero (by simpa)

/-- `x³ + x + 1 ≠ 0`. -/
public theorem cub_ne_zero : x ^ 3 + x + 1 ≠ 0 := cub_ne_zero_aux

/-- At a place not containing `x`, `ord (x + 1) = ord x`. -/
public theorem ord_x_add_one {v : Place K} (hx : x ∉ v.1) : v.ord (x + 1) = v.ord x :=
  ord_add_eq_of_lt x_ne_zero one_ne_zero (by rw [ord_one]; exact ord_x_neg hx)

/-- At a place not containing `x`, `ord (x³ + x + 1) = 3 ord x`. -/
public theorem ord_cub {v : Place K} (hx : x ∉ v.1) : v.ord (x ^ 3 + x + 1) = 3 * v.ord x := by
  rw [add_assoc, ord_add_eq_of_lt (pow_ne_zero 3 x_ne_zero) x_add_one_ne_zero, Place.ord_pow]
  · rfl
  · rw [Place.ord_pow, ord_x_add_one hx]
    have := ord_x_neg hx
    push_cast
    omega

/-- A place not containing `x` does not contain `y`. -/
public theorem y_notMem_of_x_notMem {v : Place K} (hx : x ∉ v.1) : y ∉ v.1 := by
  intro hy
  have hmem : x ^ 3 + x + 1 ∈ v.1 := by
    rw [← y_sq_add_y]; exact add_mem (pow_mem hy 2) hy
  have := (Place.ord_nonneg_iff (isDiscrete (ZMod 2) v) cub_ne_zero).2 hmem
  rw [ord_cub hx] at this
  have := ord_x_neg hx
  omega

/-- At a place not containing `x`, `2 ord y = 3 ord x`. -/
public theorem two_mul_ord_y {v : Place K} (hx : x ∉ v.1) : 2 * v.ord y = 3 * v.ord x := by
  have hy : v.ord y < 0 := by
    by_contra h
    push Not at h
    exact y_notMem_of_x_notMem hx ((Place.ord_nonneg_iff (isDiscrete (ZMod 2) v) y_ne_zero).1 h)
  have e : v.ord (y ^ 2 + y) = 2 * v.ord y := by
    rw [ord_add_eq_of_lt (pow_ne_zero 2 y_ne_zero) y_ne_zero, Place.ord_pow]
    · rfl
    · rw [Place.ord_pow]; push_cast; omega
  rw [← e, y_sq_add_y, ord_cub hx]

/-- Some place of `K` does not contain `x`. -/
public theorem x_notMem_some : ∃ v : Place K, x ∉ v.1 := by
  by_contra h
  push Not at h
  have hfin := finite_setOf_forall_mem (ZMod 2) (K := K)
  have hinj : Function.Injective fun n : ℕ => x ^ n := by
    intro n m hnm
    by_contra hne
    refine aeval_x_ne_zero (f := X ^ n - X ^ m) (fun h0 => hne ?_) (by simp [hnm])
    rw [sub_eq_zero] at h0
    simpa using congrArg natDegree h0
  exact (Set.infinite_of_injective_forall_mem (s := {z : K | ∀ v : Place K, z ∈ v.1}) hinj
    (fun n v => pow_mem (h v) n)) hfin

/-- **The place at infinity.** There is exactly one place `∞` of `K` not containing `x`; it has
residue field `𝔽₂` and `ord_∞ x = -2`. -/
public theorem exists_unique_infinitePlace :
    ∃ w : Place K, x ∉ w.1 ∧ (∀ v : Place K, x ∉ v.1 → v = w) ∧ w.resCard = 2 ∧ w.ord x = -2 := by
  classical
  set T := (finite_setOf_gen_notMem (ZMod 2) (K := K)).toFinset
  have hT : ∀ v ∈ T, (gen (ZMod 2) K)⁻¹ ∈ v.1 := fun v hv =>
    ((gen_notMem_iff (ZMod 2) v).1 (by simpa [T, x_eq_gen] using hv)).1
  have key := prod_resCard_pow_ord_le (ZMod 2) (gen (ZMod 2) K)⁻¹
    (gen_inv_transcendental (ZMod 2) K) (f := X) X_ne_zero T hT
  rw [finrank_adjoin_gen_inv, natDegree_X, mul_one, Nat.card_zmod] at key
  have hdeg : degree (ZMod 2) K ≤ 2 := finrank_adjoin_x_le
  have hRHS : 2 ^ degree (ZMod 2) K ≤ 4 :=
    (Nat.pow_le_pow_right (by norm_num) hdeg).trans (by norm_num)
  have hfac : ∀ v ∈ T,
      4 ≤ v.resCard ^ (v.ord (aeval (gen (ZMod 2) K)⁻¹ (X : (ZMod 2)[X]))).toNat := by
    intro v hv
    have hx : x ∉ v.1 := by simpa [T, x_eq_gen] using hv
    have he := two_mul_ord_y hx
    have hneg := ord_x_neg hx
    rw [aeval_X, ord_gen_inv, ← x_eq_gen]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ v.resCard ^ 2 := Nat.pow_le_pow_left (one_lt_resCard (ZMod 2) v) 2
      _ ≤ v.resCard ^ (-v.ord x).toNat :=
        Nat.pow_le_pow_right (one_pos.trans (one_lt_resCard (ZMod 2) v)) (by omega)
  obtain ⟨w, hw⟩ := x_notMem_some
  have hwT : w ∈ T := by simpa [T, x_eq_gen] using hw
  have huniq : ∀ v : Place K, x ∉ v.1 → v = w := by
    intro v hv
    by_contra hne
    have hvT : v ∈ T := by simpa [T, x_eq_gen] using hv
    have hsub : ({v, w} : Finset (Place K)) ⊆ T := by
      intro u hu; rcases Finset.mem_insert.1 hu with rfl | hu
      · exact hvT
      · rw [Finset.mem_singleton.1 hu]; exact hwT
    have h16 : 4 ^ 2 ≤ ∏ u ∈ ({v, w} : Finset (Place K)),
        u.resCard ^ (u.ord (aeval (gen (ZMod 2) K)⁻¹ (X : (ZMod 2)[X]))).toNat := by
      have := Finset.pow_card_le_prod ({v, w} : Finset (Place K)) _ 4 (fun u hu => hfac u (hsub hu))
      rwa [Finset.card_pair hne] at this
    have hle : ∏ u ∈ ({v, w} : Finset (Place K)),
        u.resCard ^ (u.ord (aeval (gen (ZMod 2) K)⁻¹ (X : (ZMod 2)[X]))).toNat ≤
        ∏ u ∈ T, u.resCard ^ (u.ord (aeval (gen (ZMod 2) K)⁻¹ (X : (ZMod 2)[X]))).toNat :=
      Finset.prod_le_prod_of_subset_of_one_le' hsub (fun u _ _ =>
        Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ (by have := one_lt_resCard (ZMod 2) u; omega)))
    omega
  have hTw : T = {w} := by
    ext u
    refine ⟨fun hu => Finset.mem_singleton.2 (huniq u (by simpa [T, x_eq_gen] using hu)),
      fun hu => ?_⟩
    rw [Finset.mem_singleton.1 hu]
    exact hwT
  rw [hTw, Finset.prod_singleton, aeval_X, ord_gen_inv, ← x_eq_gen] at key
  have he := two_mul_ord_y hw
  have hneg := ord_x_neg hw
  have hq := one_lt_resCard (ZMod 2) w
  refine ⟨w, hw, huniq, ?_, ?_⟩
  · by_contra hq2
    have h3 : 3 ≤ w.resCard := by omega
    have : 3 ^ 2 ≤ w.resCard ^ (-w.ord x).toNat :=
      (Nat.pow_le_pow_left h3 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  · by_contra h2
    have h4 : 4 ≤ (-w.ord x).toNat := by omega
    have : 2 ^ 4 ≤ w.resCard ^ (-w.ord x).toNat :=
      (Nat.pow_le_pow_left (by omega) 4).trans (Nat.pow_le_pow_right (by omega) h4)
    omega

/-- Over every prime `f ∈ 𝔽₂[x]` lies a place of `K`. -/
public theorem exists_place_of_prime {f : (ZMod 2)[X]} (hf : Prime f) :
    ∃ v : Place K, x ∈ v.1 ∧ v.1.valuation (aeval x f) < 1 := by
  set t := gen (ZMod 2) K
  have hx := gen_transcendental (ZMod 2) K
  set a : polySubalg (ZMod 2) t := polySubalgMap (k := ZMod 2) t f
  have haprime : Prime a := by
    simpa [a] using (MulEquiv.prime_iff (polySubalgEquiv hx).toMulEquiv).2 hf
  have hmax : (Ideal.span {a}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible haprime.irreducible
  have hinj : Function.Injective
      (algebraMap (polySubalg (ZMod 2) t) (intClosure (ZMod 2) t)) := fun c d h =>
    Subtype.ext (congrArg (algebraMap (intClosure (ZMod 2) t) K) h)
  have hker : RingHom.ker (algebraMap (polySubalg (ZMod 2) t) (intClosure (ZMod 2) t)) ≤
      Ideal.span {a} :=
    ((RingHom.injective_iff_ker_eq_bot _).1 hinj).le.trans bot_le
  obtain ⟨Q, hQmax, hQ⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (S := intClosure (ZMod 2) t) _ hker
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    refine haprime.ne_zero (Ideal.span_singleton_eq_bot.1 ?_)
    rw [← hQ, Ideal.under_def, ← RingHom.ker_eq_comap_bot,
      (RingHom.injective_iff_ker_eq_bot _).1 hinj]
  let P : IsDedekindDomain.HeightOneSpectrum (intClosure (ZMod 2) t) := ⟨Q, hQmax.isPrime, hQ0⟩
  refine ⟨Place.ofHeightOneSpectrum (K := K) P, ?_, ?_⟩
  · have htmem : t ∈ intClosure (ZMod 2) t :=
      (isIntegral_algebraMap (R := polySubalg (ZMod 2) t) (A := K)
        (x := ⟨t, Algebra.self_mem_adjoin_singleton (ZMod 2) t⟩))
    exact (Valuation.mem_valuationSubring_iff _ _).2 (P.valuation_le_one (K := K) ⟨t, htmem⟩)
  · have hbQ : algebraMap (polySubalg (ZMod 2) t) (intClosure (ZMod 2) t) a ∈ Q := by
      rw [← Ideal.mem_comap, ← Ideal.under_def, hQ]
      exact Ideal.subset_span rfl
    have hlt := (P.valuation_lt_one_iff_mem (K := K) _).2 hbQ
    change (P.valuation K) (aeval x f) < 1 at hlt
    exact (Valuation.isEquiv_valuation_valuationSubring (P.valuation K)).lt_one_iff_lt_one.1 hlt

/-- An element of `𝔽₂(x)` integral at every place containing `x` is a polynomial in `x`. -/
public theorem exists_poly_of_forall_mem (r : RatFunc (ZMod 2))
    (h : ∀ v : Place K, x ∈ v.1 → ofR r ∈ v.1) :
    ∃ f : (ZMod 2)[X], r = algebraMap (ZMod 2)[X] (RatFunc (ZMod 2)) f := by
  by_cases hd : IsUnit r.denom
  · refine ⟨r.num, ?_⟩
    have h1 : r.denom = 1 := (RatFunc.monic_denom r).eq_one_of_isUnit hd
    have := RatFunc.num_div_denom r
    rw [h1, map_one, div_one] at this
    exact this.symm
  obtain ⟨p, hp, hpd⟩ := WfDvdMonoid.exists_irreducible_factor hd (RatFunc.monic_denom r).ne_zero
  obtain ⟨v, hxv, hlt⟩ := exists_place_of_prime hp.prime
  exfalso
  obtain ⟨q, hq⟩ := hpd
  have hpoly := aeval_x_mem_of_mem (S := v.1.toSubring) (algebraMap_mem_place v) hxv
  have hle : ∀ g : (ZMod 2)[X], v.1.valuation (aeval x g) ≤ 1 := fun g =>
    (ValuationSubring.valuation_le_one_iff _ _).2 (hpoly g)
  have hden : v.1.valuation (aeval x r.denom) < 1 := by
    rw [hq, map_mul, map_mul]
    exact mul_lt_one_of_lt_of_le hlt (hle q)
  have hnum : v.1.valuation (aeval x r.num) = 1 := by
    refine le_antisymm (hle _) (not_lt.1 fun hlt' => ?_)
    obtain ⟨u, w, huw⟩ := (RatFunc.isCoprime_num_denom r).of_isCoprime_of_dvd_right ⟨q, hq⟩
    have e := congrArg (aeval x) huw
    rw [map_add, map_mul, map_mul, map_one] at e
    have h1 : v.1.valuation (aeval x u * aeval x r.num + aeval x w * aeval x p) < 1 :=
      lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt
        (by rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle u)) hlt')
        (by rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle w)) hlt))
    rw [e, map_one] at h1
    exact lt_irrefl _ h1
  have hr := h v hxv
  rw [← RatFunc.num_div_denom r, map_div₀, ofR_algebraMap, ofR_algebraMap] at hr
  have hval := (ValuationSubring.valuation_le_one_iff _ _).2 hr
  have hd0 := aeval_x_ne_zero (RatFunc.monic_denom r).ne_zero
  rw [map_div₀, hnum, div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hd0))] at hval
  exact absurd hden (not_lt.2 hval)

/-- If a place contains `x`, so does its pullback along `ι`. -/
public theorem placeComap_iota_mem_x {w : Place K} (hw : x ∈ w.1) : x ∈ (placeComap iota w).1 := by
  rwa [mem_placeComap, iota_x]

/-- **Elements integral at the finite places.** An element of `K` lying in every place containing
`x` is `a(x) + b(x) y` with polynomials `a, b`. -/
public theorem exists_poly_add_mul_y (z : K) (h : ∀ v : Place K, x ∈ v.1 → z ∈ v.1) :
    ∃ a b : (ZMod 2)[X], z = aeval x a + aeval x b * y := by
  obtain ⟨a, b, rfl⟩ := exists_eq_add_mul_y z
  have hι : ∀ v : Place K, x ∈ v.1 → iota (ofR a + ofR b * y) ∈ v.1 := fun v hv =>
    (mem_placeComap iota).1 (h _ (placeComap_iota_mem_x hv))
  obtain ⟨b', rfl⟩ := exists_poly_of_forall_mem b fun v hv => by
    rw [← add_iota]; exact add_mem (h v hv) (hι v hv)
  obtain ⟨n', hn'⟩ := exists_poly_of_forall_mem
    (a ^ 2 + a * algebraMap (ZMod 2)[X] (RatFunc (ZMod 2)) b' +
      (algebraMap (ZMod 2)[X] (RatFunc (ZMod 2)) b') ^ 2 *
        algebraMap (ZMod 2)[X] (RatFunc (ZMod 2)) cub) fun v hv => by
    rw [← mul_iota]; exact mul_mem (h v hv) (hι v hv)
  have hmon : (X ^ 2 + C b' * X + C (b' ^ 2 * cub - n') : ((ZMod 2)[X])[X]).Monic := by
    monicity!
  have hroot : aeval a (X ^ 2 + C b' * X + C (b' ^ 2 * cub - n') : ((ZMod 2)[X])[X]) = 0 := by
    simp only [map_add, map_mul, map_pow, aeval_X, aeval_C, map_sub]
    rw [← hn']
    ring
  obtain ⟨a', rfl⟩ := isInteger_of_is_root_of_monic hmon hroot
  exact ⟨a', b', by rw [ofR_algebraMap, ofR_algebraMap]⟩

end Places

section Infinity

/-- The place at infinity of `K`. -/
public def infPlace : Place K := exists_unique_infinitePlace.choose

/-- The place at infinity does not contain `x`. -/
public theorem x_notMem_infPlace : x ∉ infPlace.1 := exists_unique_infinitePlace.choose_spec.1

/-- The place at infinity is the only place not containing `x`. -/
public theorem eq_infPlace {v : Place K} (hv : x ∉ v.1) : v = infPlace :=
  exists_unique_infinitePlace.choose_spec.2.1 v hv

/-- The residue field at infinity has two elements. -/
public theorem resCard_infPlace : infPlace.resCard = 2 :=
  exists_unique_infinitePlace.choose_spec.2.2.1

/-- `ord_∞ x = -2`. -/
public theorem ord_infPlace_x : infPlace.ord x = -2 := exists_unique_infinitePlace.choose_spec.2.2.2

/-- `ord_∞ y = -3`. -/
public theorem ord_infPlace_y : infPlace.ord y = -3 := by
  have := two_mul_ord_y x_notMem_infPlace
  rw [ord_infPlace_x] at this
  omega

/-- `ord_∞ f(x) = -2 deg f` for a nonzero polynomial `f`. -/
public theorem ord_infPlace_aeval {f : (ZMod 2)[X]} (hf : f ≠ 0) :
    infPlace.ord (aeval x f) = -2 * f.natDegree := by
  rw [x_eq_gen, ord_aeval_gen_of_notMem (ZMod 2) (by rw [← x_eq_gen]; exact x_notMem_infPlace) hf,
    ← x_eq_gen, ord_infPlace_x]
  ring

/-- `f(x) ≠ 0` for a nonzero polynomial `f`. -/
public theorem aeval_ne_zero {f : (ZMod 2)[X]} (hf : f ≠ 0) : aeval x f ≠ 0 := aeval_x_ne_zero hf

/-- `ord_∞ (f(x) y) = -2 deg f - 3` for a nonzero polynomial `f`. -/
public theorem ord_infPlace_aeval_mul_y {f : (ZMod 2)[X]} (hf : f ≠ 0) :
    infPlace.ord (aeval x f * y) = -2 * f.natDegree - 3 := by
  rw [Place.ord_mul _ (aeval_ne_zero hf) y_ne_zero, ord_infPlace_aeval hf, ord_infPlace_y]
  ring

/-- If `b ≠ 0`, then `a(x) + b(x) y` has a pole of order `≥ 3` at infinity. -/
public theorem ord_infPlace_le {a b : (ZMod 2)[X]} (hb : b ≠ 0) :
    infPlace.ord (aeval x a + aeval x b * y) ≤ -3 := by
  have hby := ord_infPlace_aeval_mul_y hb
  rcases eq_or_ne a 0 with rfl | ha
  · rw [map_zero, zero_add, hby]; omega
  have hay := ord_infPlace_aeval ha
  have hne : infPlace.ord (aeval x a) ≠ infPlace.ord (aeval x b * y) := by
    rw [hay, hby]; omega
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · rw [ord_add_eq_of_lt (aeval_ne_zero ha) (mul_ne_zero (aeval_ne_zero hb) y_ne_zero) hlt]
    omega
  · rw [add_comm,
      ord_add_eq_of_lt (mul_ne_zero (aeval_ne_zero hb) y_ne_zero) (aeval_ne_zero ha) hlt]
    omega

/-- **`L(2∞) = 𝔽₂ + 𝔽₂ x`.** An element of `K` integral at every place containing `x` and with a
pole of order at most `2` at infinity is `c + d x` with `c, d ∈ 𝔽₂`. -/
public theorem eq_add_mul_x_of_mem (z : K) (h : ∀ v : Place K, x ∈ v.1 → z ∈ v.1)
    (hinf : z ≠ 0 → -2 ≤ infPlace.ord z) :
    ∃ c d : ZMod 2, z = algebraMap (ZMod 2) K c + algebraMap (ZMod 2) K d * x := by
  obtain ⟨a, b, rfl⟩ := exists_poly_add_mul_y z h
  rcases eq_or_ne b 0 with rfl | hb
  · rw [map_zero, zero_mul, add_zero] at hinf ⊢
    rcases eq_or_ne a 0 with rfl | ha
    · exact ⟨0, 0, by simp⟩
    have := hinf (aeval_ne_zero ha)
    rw [ord_infPlace_aeval ha] at this
    have hdeg : a.degree ≤ 1 := by
      rw [degree_eq_natDegree ha]; exact_mod_cast (by omega : a.natDegree ≤ 1)
    rw [eq_X_add_C_of_degree_le_one hdeg]
    refine ⟨a.coeff 0, a.coeff 1, ?_⟩
    simp only [map_add, map_mul, aeval_C, aeval_X]
    ring
  · exfalso
    have hz : aeval x a + aeval x b * y ≠ 0 := by
      intro h0
      have := add_mul_y_eq_zero (a := algebraMap (ZMod 2)[X] (RatFunc (ZMod 2)) a)
        (b := algebraMap (ZMod 2)[X] (RatFunc (ZMod 2)) b) (by rwa [ofR_algebraMap, ofR_algebraMap])
      exact hb (IsFractionRing.injective (ZMod 2)[X] (RatFunc (ZMod 2))
        (this.2.trans (map_zero _).symm))
    have := hinf hz
    have := ord_infPlace_le (a := a) hb
    omega

/-- The ultrametric inequality `min (ord a) (ord b) ≤ ord (a + b)`, for `a`, `b` and `a + b`
nonzero. -/
public theorem ord_add_ge {v : Place K} {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0) :
    min (v.ord a) (v.ord b) ≤ v.ord (a + b) := by
  have h := Valuation.map_add v.normVal a b
  rw [Place.normVal_eq_exp ha, Place.normVal_eq_exp hb, Place.normVal_eq_exp hab] at h
  rcases le_total (v.ord a) (v.ord b) with hle | hle
  · rw [max_eq_left (WithZero.exp_le_exp.2 (by omega)), WithZero.exp_le_exp] at h
    omega
  · rw [max_eq_right (WithZero.exp_le_exp.2 (by omega)), WithZero.exp_le_exp] at h
    omega

/-- A place containing `x` contains `a(x) + b(x) y` for all polynomials `a`, `b`. -/
public theorem mem_of_x_mem_poly {v : Place K} (hv : x ∈ v.1) (a b : (ZMod 2)[X]) :
    aeval x a + aeval x b * y ∈ v.1 := by
  have hpoly := aeval_x_mem_of_mem (S := v.1.toSubring) (algebraMap_mem_place v) hv
  exact add_mem (hpoly a) (mul_mem (hpoly b) (y_mem_of_x_mem hv))

open scoped Classical in
/-- `ℓ(2m ∞) ≥ 2^(2m)`: the functions `a(x) + b(x) y` with `deg a ≤ m`, `deg b ≤ m - 2`. -/
public theorem pow_le_ell (m : ℕ) (hm : 1 ≤ m) :
    2 ^ (2 * m) ≤ ell (ZMod 2) K (Finsupp.single infPlace (2 * m : ℤ)) := by
  set D : Place K →₀ ℤ := Finsupp.single infPlace (2 * m : ℤ)
  let φ : degreeLT (ZMod 2) (m + 1) × degreeLT (ZMod 2) (m - 1) →
      ↥(principal (ZMod 2) K ⊓ adeleLattice K D) := fun p =>
    ⟨diag (ZMod 2) K (aeval x (p.1 : (ZMod 2)[X]) + aeval x (p.2 : (ZMod 2)[X]) * y), by
      refine AddSubgroup.mem_inf.2 ⟨⟨_, rfl⟩, ?_⟩
      rw [diag_mem_adeleLattice_iff]
      by_cases hz : aeval x (p.1 : (ZMod 2)[X]) + aeval x (p.2 : (ZMod 2)[X]) * y = 0
      · exact Or.inl hz
      refine Or.inr fun v => ?_
      by_cases hv : v = infPlace
      · subst hv
        simp only [D, Finsupp.single_eq_same]
        have ha := p.1.2
        have hb := p.2.2
        rw [mem_degreeLT] at ha hb
        have hA : (aeval x (p.1 : (ZMod 2)[X])) ≠ 0 → -(2 * m : ℤ) ≤
            infPlace.ord (aeval x (p.1 : (ZMod 2)[X])) := by
          intro h0
          have hp0 : (p.1 : (ZMod 2)[X]) ≠ 0 := fun h => h0 (by rw [h, map_zero])
          rw [ord_infPlace_aeval hp0]
          have : (p.1 : (ZMod 2)[X]).natDegree ≤ m := by
            rw [degree_eq_natDegree hp0] at ha
            have : (p.1 : (ZMod 2)[X]).natDegree < m + 1 := by exact_mod_cast ha
            omega
          omega
        have hB : (aeval x (p.2 : (ZMod 2)[X]) * y) ≠ 0 → -(2 * m : ℤ) ≤
            infPlace.ord (aeval x (p.2 : (ZMod 2)[X]) * y) := by
          intro h0
          have hp0 : (p.2 : (ZMod 2)[X]) ≠ 0 := fun h => h0 (by rw [h, map_zero, zero_mul])
          rw [ord_infPlace_aeval_mul_y hp0]
          have : (p.2 : (ZMod 2)[X]).natDegree + 1 ≤ m - 1 := by
            rw [degree_eq_natDegree hp0] at hb
            have : (p.2 : (ZMod 2)[X]).natDegree < m - 1 := by exact_mod_cast hb
            omega
          omega
        by_cases h1 : aeval x (p.1 : (ZMod 2)[X]) = 0
        · rw [h1, zero_add] at hz ⊢; exact hB hz
        by_cases h2 : aeval x (p.2 : (ZMod 2)[X]) * y = 0
        · rw [h2, add_zero] at hz ⊢; exact hA hz
        exact le_trans (le_min (hA h1) (hB h2)) (ord_add_ge h1 h2 hz)
      · simp only [D, Finsupp.single_apply, Ne.symm hv, ite_false, neg_zero]
        have hx : x ∈ v.1 := by
          by_contra h; exact hv (eq_infPlace h)
        exact (Place.ord_nonneg_iff (isDiscrete (ZMod 2) v) hz).2 (mem_of_x_mem_poly hx _ _)⟩
  have hφ : Function.Injective φ := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h1 : aeval x (a : (ZMod 2)[X]) + aeval x (b : (ZMod 2)[X]) * y =
        aeval x (a' : (ZMod 2)[X]) + aeval x (b' : (ZMod 2)[X]) * y :=
      diag_injective (ZMod 2) (congrArg Subtype.val h)
    have h2 : ofR (algebraMap (ZMod 2)[X] (RatFunc (ZMod 2)) ((a : (ZMod 2)[X]) - a')) +
        ofR (algebraMap (ZMod 2)[X] (RatFunc (ZMod 2)) ((b : (ZMod 2)[X]) - b')) * y = 0 := by
      rw [ofR_algebraMap, ofR_algebraMap, map_sub, map_sub]
      linear_combination h1
    obtain ⟨ha, hb⟩ := add_mul_y_eq_zero h2
    have ha' := IsFractionRing.injective (ZMod 2)[X] (RatFunc (ZMod 2)) (ha.trans (map_zero _).symm)
    have hb' := IsFractionRing.injective (ZMod 2)[X] (RatFunc (ZMod 2)) (hb.trans (map_zero _).symm)
    rw [sub_eq_zero] at ha' hb'
    simp only [Prod.mk.injEq]
    exact ⟨Subtype.ext ha', Subtype.ext hb'⟩
  have hfin := finite_principal_inf_adeleLattice (ZMod 2) (K := K) D
  have hcard := Nat.card_le_card_of_injective φ hφ
  have hdeg : ∀ n, Nat.card (degreeLT (ZMod 2) n) = 2 ^ n := fun n => by
    rw [Nat.card_congr (degreeLTEquiv (ZMod 2) n).toEquiv, Nat.card_fun, Nat.card_zmod,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [Nat.card_prod, hdeg, hdeg, ← pow_add] at hcard
  have : m + 1 + (m - 1) = 2 * m := by omega
  rw [this] at hcard
  exact hcard

/-- `ℓ(0) ≥ h¹(0)`, from Riemann–Roch at `2m ∞` for `m` large. -/
public theorem one_le_chi : (1 : ℚ) ≤ ell (ZMod 2) K 0 / hOne (ZMod 2) K 0 := by
  obtain ⟨M₀, hM₀⟩ := exists_sup_adeleLattice_eq_top (ZMod 2) (K := K)
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (max M₀ 1) (by norm_num : (1 : ℚ) < 4)
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp at hm
    · exact h
  set D : Place K →₀ ℤ := Finsupp.single infPlace (2 * m : ℤ)
  have hN : divNorm K D = 4 ^ m := by
    rw [divNorm_single, resCard_infPlace, zpow_mul, zpow_natCast]; norm_num
  have htop := hM₀ D (by rw [hN]; exact (le_max_left _ _).trans hm.le)
  have hh : hOne (ZMod 2) K D = 1 := by rw [hOne, htop, AddSubgroup.index_top]
  have hRR := ell_div_hOne (ZMod 2) (K := K) D
  rw [hh, Nat.cast_one, div_one, hN] at hRR
  have hell := pow_le_ell m hm1
  have h4 : ((2 ^ (2 * m) : ℕ) : ℚ) = 4 ^ m := by push_cast; rw [pow_mul]; norm_num
  have : (4 : ℚ) ^ m ≤ 4 ^ m * (ell (ZMod 2) K 0 / hOne (ZMod 2) K 0) := by
    rw [← hRR, ← h4]; exact_mod_cast hell
  have hpos : (0 : ℚ) < 4 ^ m := by positivity
  nlinarith

/-- **Class number one.** Every divisor `D` of `K` with `N(D) = 1` (that is, of degree `0`) is
principal. -/
public theorem exists_principalDivisor_eq {D : Place K →₀ ℤ} (hD : divNorm K D = 1) :
    ∃ κ : K, κ ≠ 0 ∧ principalDivisor (ZMod 2) K κ = D := by
  classical
  set E := D + Finsupp.single infPlace 1
  have hNE : divNorm K E = 2 := by
    rw [divNorm_add (ZMod 2), hD, divNorm_single, resCard_infPlace]; norm_num
  have hRR := ell_div_hOne (ZMod 2) (K := K) E
  have hh1 : (1 : ℚ) ≤ hOne (ZMod 2) K E := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (hOne_ne_zero _ E)
  have hell : 1 < ell (ZMod 2) K E := by
    have hchi := one_le_chi
    have : (2 : ℚ) ≤ ell (ZMod 2) K E := by
      have e : (ell (ZMod 2) K E : ℚ) =
          hOne (ZMod 2) K E * (2 * (ell (ZMod 2) K 0 / hOne (ZMod 2) K 0)) := by
        rw [← hNE, ← hRR]; field_simp
      rw [e]; nlinarith
    exact_mod_cast (by linarith : (1 : ℚ) < ell (ZMod 2) K E)
  obtain ⟨κ, hκ, hmem⟩ := exists_ne_zero_of_one_lt_ell (ZMod 2) hell
  have hF : 0 ≤ E + principalDivisor (ZMod 2) K κ :=
    le_add_principalDivisor_of_mem (ZMod 2) hκ (by rwa [sub_zero])
  set F := E + principalDivisor (ZMod 2) K κ
  have hNF : divNorm K F = 2 := by
    rw [divNorm_add (ZMod 2), divNorm_principalDivisor (ZMod 2) hκ, hNE, mul_one]
  have hFv : ∀ v, v ≠ infPlace → F v = 0 := by
    intro v hv
    by_contra hne
    have h1 : Finsupp.single v 1 ≤ F := by
      intro u
      by_cases hu : u = v
      · subst hu; simp only [Finsupp.single_eq_same]; have := hF u; simp at this; omega
      · simp only [Finsupp.single_apply, Ne.symm hu, ite_false]; exact hF u
    have := divNorm_mono (ZMod 2) h1
    rw [divNorm_single, hNF, zpow_one] at this
    have hx : x ∈ v.1 := by by_contra h; exact hv (eq_infPlace h)
    have hq := resCard_ne_two_of_x_mem hx
    have hq1 := one_lt_resCard (ZMod 2) v
    have : v.resCard ≤ 2 := by exact_mod_cast this
    omega
  have hFeq : F = Finsupp.single infPlace (F infPlace) := by
    ext u
    by_cases hu : u = infPlace
    · subst hu; simp
    · simp [Ne.symm hu, hFv u hu]
  have hFinf : F infPlace = 1 := by
    have := hNF
    rw [hFeq, divNorm_single, resCard_infPlace] at this
    have h := zpow_right_injective₀ (by norm_num : (0 : ℚ) < 2) (by norm_num : (2 : ℚ) ≠ 1)
      (this.trans (zpow_one (2 : ℚ)).symm)
    exact h
  refine ⟨κ⁻¹, inv_ne_zero hκ, ?_⟩
  rw [principalDivisor_inv (ZMod 2) hκ]
  have : F = Finsupp.single infPlace 1 := by rw [hFeq, hFinf]
  have e2 : D = F - Finsupp.single infPlace 1 - principalDivisor (ZMod 2) K κ := by
    simp only [F, E]; abel
  rw [e2, this, sub_self, zero_sub]

end Infinity








end Stacks.Drinfeld.SupersingularCurve

end
