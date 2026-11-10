module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Finiteness of the integral closure in a purely inseparable degree-`p` extension

Let `R` be a Noetherian normal domain with fraction field `K = Frac R`, and suppose `K`
has characteristic `p > 0` for a prime `p`. Let `a : K` be an element for which there is
a derivation `D : R → R` with `D a ≠ 0`. Then the integral closure of `R` in
`L = K[x]/(xᵖ - a)` is finite over `R`, that is, finitely generated as an `R`-module.

A *normal domain* is an integral domain integrally closed in its fraction field, which
is the conjunction `[IsDomain R] [IsIntegrallyClosed R]`. A derivation is modelled by
`Derivation ℤ K K`, and `D` is phrased as a derivation `K → K` mapping `R` into `R`, the
canonical extension to `Frac R`, with `D a ≠ 0`. The integral closure of `R` in an
`R`-algebra `A` is `integralClosure R A`, and `L = K[x]/(xᵖ - a)` is
`AdjoinRoot (X ^ p - C a)`.
-/

@[expose] public section

namespace Stacks.Nagata.PurelyInseparable

variable {R K : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  (p : ℕ) [Fact (Nat.Prime p)] [CharP K p] (a : K)

/-- `L = K[x]/(x^p - a)`, viewed as an `R`-algebra via `R ⊆ K`. -/
noncomputable abbrev Lext : Type _ := AdjoinRoot (Polynomial.X ^ p - Polynomial.C a)

/-! ## Structure lemmas about `L = K[x]/(xᵖ - a)` -/

omit [CharP K p] in
/-- The defining polynomial `X^p - C a` has degree `p ≠ 0`. -/
theorem degree_poly_ne : (Polynomial.X ^ p - Polynomial.C a : Polynomial K).degree ≠ 0 := by
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  rw [Polynomial.degree_X_pow_sub_C (by omega)]; exact_mod_cast by omega

omit [CharP K p] in
/-- `K → L` is injective (since the defining polynomial is nonconstant). -/
theorem algMap_inj : Function.Injective (algebraMap K (Lext p a)) := by
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.coe_injective (degree_poly_ne p a)

omit [CharP K p] in
/-- `K` acts faithfully on `L`, which is exactly the injectivity of `K → L`.
This is the form `isIntegral_algebraMap_iff` now takes its injectivity hypothesis in. -/
instance faithfulSMul_Lext : FaithfulSMul K (Lext p a) :=
  (faithfulSMul_iff_algebraMap_injective K (Lext p a)).mpr (algMap_inj p a)

omit [Fact (Nat.Prime p)] [CharP K p] in
/-- The root `α` of `X^p - C a` satisfies `α^p = a` in `L`. -/
theorem root_pow :
    (AdjoinRoot.root (Polynomial.X ^ p - Polynomial.C a)) ^ p = algebraMap K (Lext p a) a := by
  have h : (Polynomial.aeval (AdjoinRoot.root (Polynomial.X ^ p - Polynomial.C a))
      (Polynomial.X ^ p - Polynomial.C a) : Lext p a) = 0 := by
    rw [AdjoinRoot.aeval_eq]; exact AdjoinRoot.mk_self
  simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C] at h
  rw [sub_eq_zero] at h
  exact h

/-! ## Frobenius and `p`-th power lemmas -/

/-- **Frobenius fact.** Since `char L = p` and `α^p = a ∈ K`, every element of
`L = K[α]` has its `p`-th power in (the image of) `K`. -/
theorem pow_mem_K (y : Lext p a) : ∃ k : K, y ^ p = algebraMap K (Lext p a) k := by
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective y
  refine ⟨Polynomial.aeval a (Polynomial.map (frobenius K p) g), ?_⟩
  rw [← AdjoinRoot.aeval_eq, ← map_pow]
  have hgp : g ^ p = (Polynomial.expand K p) (Polynomial.map (frobenius K p) g) := by
    rw [← Polynomial.map_expand, Polynomial.map_frobenius_expand]
  rw [hgp, Polynomial.expand_aeval, root_pow p a, Polynomial.aeval_algebraMap_apply]

/-- An element of `K` whose image in a faithful `K`-algebra `A` is integral over the normal
domain `R` comes from `R`. -/
private theorem exists_algebraMap_eq_of_isIntegral {S F A : Type*} [CommRing S]
    [IsIntegrallyClosed S] [Field F] [Algebra S F] [IsFractionRing S F] [CommRing A] [Algebra S A]
    [Algebra F A] [IsScalarTower S F A] [FaithfulSMul F A] (k : F)
    (hk : IsIntegral S (algebraMap F A k)) : ∃ r : S, algebraMap S F r = k :=
  IsIntegrallyClosed.isIntegral_iff.mp (isIntegral_algebraMap_iff.mp hk)

omit [IsDomain R] [IsNoetherianRing R] in
/-- **Key arithmetic step.** If `y ∈ L` is integral over the normal domain `R`,
then its `p`-th power lies in `R` (the image of `R → L`). -/
theorem pow_mem_R (y : Lext p a) (hy : IsIntegral R y) :
    ∃ r : R, y ^ p = algebraMap R (Lext p a) r := by
  obtain ⟨k, hk⟩ := pow_mem_K p a y
  obtain ⟨r, hr⟩ := exists_algebraMap_eq_of_isIntegral k (by rw [← hk]; exact hy.pow p)
  exact ⟨r, by rw [hk, ← hr, ← IsScalarTower.algebraMap_apply R K (Lext p a)]⟩

/-! ## The finite module spanned by `α^i` for `i < p` -/

/-- The root `α` of `X^p - C a`, living in `L`. -/
noncomputable def rootα : Lext p a := AdjoinRoot.root _

/-- The `R`-submodule of `L` spanned by `α^0, …, α^{p-1}`. -/
noncomputable abbrev spanPow :
    Submodule R (AdjoinRoot (Polynomial.X ^ p - Polynomial.C a : Polynomial K)) :=
  Submodule.span R (Set.range fun i : Fin p => rootα p a ^ (i : ℕ))

omit [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] [IsFractionRing R K] [Fact (Nat.Prime
    p)] [CharP K p] in
/-- The span of the finitely many powers `α^i`, `i < p`, is finitely generated. -/
theorem spanPow_fg : (spanPow (R := R) p a).FG :=
  Submodule.fg_span (Set.finite_range _)

/-! ## The power basis `1, α, …, α^{p-1}` of `L` over `K` -/

omit [CharP K p] in
/-- The defining polynomial `X^p - C a` is nonzero (it has degree `p`). -/
theorem poly_ne_zero : (Polynomial.X ^ p - Polynomial.C a : Polynomial K) ≠ 0 :=
  Polynomial.X_pow_sub_C_ne_zero (Fact.out (p := p.Prime)).pos a

/-- The power basis `1, α, …, α^{p-1}` of `L = K[x]/(x^p-a)` over `K`. -/
noncomputable def pb : PowerBasis K (Lext p a) := AdjoinRoot.powerBasis (poly_ne_zero p a)

omit [CharP K p] in
/-- The power basis has dimension `p`. -/
theorem pb_dim : (pb p a).dim = p := by
  unfold pb; rw [AdjoinRoot.powerBasis_dim, Polynomial.natDegree_sub_C]; simp

omit [CharP K p] in
/-- The generator of the power basis is the root `α`. -/
theorem pb_gen : (pb p a).gen = AdjoinRoot.root _ := by
  unfold pb; rw [AdjoinRoot.powerBasis_gen]

omit [CharP K p] in
omit [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] [IsFractionRing R K] in
/-- Each basis power `α^j` (for `j < p`) lies in `spanPow`. -/
theorem gen_pow_mem (j : Fin (pb p a).dim) :
    (pb p a).gen ^ (j : ℕ) ∈ spanPow (R := R) p a := by
  rw [pb_gen]; apply Submodule.subset_span
  exact ⟨⟨(j : ℕ), j.isLt.trans_eq (pb_dim p a)⟩, rfl⟩

/-- Every element of a power-basis algebra is the sum of its coordinates against the powers of
the generator. -/
private theorem eq_sum_repr_smul_gen_pow {F A : Type*} [Field F] [Ring A] [Algebra F A]
    (pb : PowerBasis F A) (y : A) :
    y = ∑ j : Fin pb.dim, pb.basis.repr y j • pb.gen ^ (j : ℕ) := by
  conv_lhs => rw [← pb.basis.sum_repr y]
  exact Finset.sum_congr rfl (fun j _ => by rw [PowerBasis.coe_basis])

/-- The coordinates of `∑ w m • α^m` in the power basis are the `w m`. -/
private theorem repr_sum_smul_gen_pow {F A : Type*} [Field F] [Ring A] [Algebra F A]
    (pb : PowerBasis F A) (w : Fin pb.dim → F) (k : Fin pb.dim) :
    pb.basis.repr (∑ m, w m • pb.gen ^ (m : ℕ)) k = w k := by
  have he : (∑ m, w m • pb.gen ^ (m : ℕ)) = ∑ m, w m • pb.basis m := by
    apply Finset.sum_congr rfl; intro m _; rw [PowerBasis.coe_basis]
  rw [he, ← pb.basis.equivFun_symm_apply, ← pb.basis.equivFun_apply,
    LinearEquiv.apply_symm_apply]

/-- A derivation kills `q`-th powers in characteristic `q`. -/
private theorem derivation_pow_char {F : Type*} [Field F] (q : ℕ) [CharP F q]
    (D : Derivation ℤ F F) (c : F) : D (c ^ q) = 0 := by
  rw [Derivation.leibniz_pow, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]

/-! ## The derivation induction -/

/-! ### The coordinate denominator bound

There is a single nonzero `d : K`, morally `(D a)^{p-1}`, such that in the power basis
`1, α, …, α^{p-1}` multiplying any integral element `y` by `d` clears the denominators
of all of its coordinates, each `d · (coordinate of y)` lying in the image of `R`.

First reduce to `a ∈ R`. Replacing the root `x` by `f x` and `a` by `fᵖ a` for a
suitable nonzero `f ∈ R` clears the denominator of `a`, so one may assume `a ∈ R`, and
then `D a ∈ R` as well; write `δ = D a ≠ 0 ∈ R`. This replacement is an isomorphism of
the `K`-algebra `K[x]/(xᵖ - a)` that only rescales the chosen power basis, so it
suffices to bound coordinates in the new basis. Take `d = δ^{p-1}`.

Now the induction. Every element is uniquely `y = a₀ + a₁ x + ⋯ + a_{p-1} x^{p-1}` with
`a_j ∈ K`. One shows by induction on `i ≤ p - 1` that if `y = a₀ + a₁ x + ⋯ + a_i xⁱ` is
integral over `R` then `δⁱ a_j ∈ R` for all `j ≤ i`.

For `i = 0`, `y = a₀` is integral over `R` if and only if `a₀ ∈ R`, since `R` is
integrally closed in `K`, so `δ⁰ a₀ = a₀ ∈ R`.

For the step from `i` to `i + 1`, let `y = a₀ + ⋯ + a_{i+1} x^{i+1}` be integral. Then
`yᵖ = a₀ᵖ + a₁ᵖ a + ⋯ + a_{i+1}ᵖ a^{i+1} ∈ K` is integral over `R`, hence lies in `R`,
using that `R` is normal and `xᵖ = a`. Applying `D`, which kills `p`-th powers and obeys
the Leibniz rule, gives
`D (yᵖ) = (a₁ᵖ + 2 a₂ᵖ a + ⋯ + (i+1) a_{i+1}ᵖ aⁱ) · D a ∈ R`. The element
`z = δ a₁ + 2 δ a₂ x + ⋯ + (i+1) δ a_{i+1} xⁱ`, of degree `i`, satisfies `zᵖ ∈ R` and so
is integral over `R`; the induction hypothesis applied to `z` gives
`δⁱ ((j+1) δ a_{j+1}) ∈ R`, that is `δ^{i+1} a_j ∈ R` for `j = 1, …, i+1`, since
`1, …, i+1` are invertible mod `p`. Finally `δ^{i+1} a₀ ∈ R` as the difference of
`δ^{i+1} y` and `∑_{j>0} δ^{i+1} a_j xʲ`, both integral, `x` being integral because
`a ∈ R`.

Taking `i = p - 1`, every integral `y` has `δ^{p-1} a_j ∈ R` for all `j`.
-/
/-- **Frobenius coordinate identity.** The `p`-th power of any `y`
collapses, in the power basis, to the diagonal sum of `p`-th powers of its
coordinates against the powers of `a` (cross terms vanish in characteristic `p`).
This is the algebraic engine that turns the integrality datum `y^p ∈ R`
(`pow_mem_R`) into a relation among the coordinates `c_j := repr y j`. -/
theorem pow_eq_sum_repr (y : Lext p a) :
    y ^ p = algebraMap K (Lext p a)
      (∑ j : Fin (pb p a).dim, ((pb p a).basis.repr y j) ^ p * a ^ (j : ℕ)) := by
  have : CharP (Lext p a) p := charP_of_injective_algebraMap (algMap_inj p a) p
  -- Write `y` as the sum of its coordinates against the powers of the generator.
  conv_lhs => rw [eq_sum_repr_smul_gen_pow (pb p a) y]
  -- Use the Frobenius endomorphism (additive over the sum).
  rw [← frobenius_def, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [frobenius_def]
  -- `(c • α^j)^p = c^p • (α^j)^p`
  rw [Algebra.smul_def, mul_pow, ← map_pow]
  -- `(α^j)^p = (α^p)^j = a^j`
  have hgen : ((pb p a).gen ^ (j : ℕ)) ^ p = algebraMap K (Lext p a) (a ^ (j : ℕ)) := by
    rw [pb_gen, ← pow_mul, mul_comm, pow_mul, root_pow, ← map_pow]
  rw [hgen, ← map_mul]

omit [IsIntegrallyClosed R] [IsNoetherianRing R] in
/-- **Reduction to `a ∈ R`.** It suffices to prove `coord_denom_bound` under the
extra hypothesis that `a` lies in the image of `R`. Indeed, choosing `f ∈ R`,
`f ≠ 0`, clearing the denominator of `a` (so `f^p · a ∈ R`), the substitution
`x ↦ f · x` gives a `K`-algebra isomorphism `Lext p a ≃ₐ[K] Lext p (f^p·a)`
that rescales the power-basis coordinates by powers of `f` (units in `K`), and
transports integral elements to integral elements. A coordinate bound in the
target `Lext p (f^p·a)` (where `f^p·a ∈ R`) therefore pulls back to one in
`Lext p a` after multiplying `d` by the appropriate power of `f`.

This statement is the *reduction*: it says proving the bound in the special case
`a ∈ R` is enough for the general case. Its proof is the AlgEquiv transport. -/
theorem coord_denom_bound_reduce
    (H : ∀ (a' : K), (∃ a₀ : R, a' = algebraMap R K a₀) →
      (∃ D : Derivation ℤ K K,
        (∀ r : R, ∃ s : R, D (algebraMap R K r) = algebraMap R K s) ∧ D a' ≠ 0) →
      ∃ d : K, d ≠ 0 ∧ ∀ y : Lext p a', IsIntegral R y → ∀ j : Fin (pb p a').dim,
        ∃ r : R, d * (pb p a').basis.repr y j = algebraMap R K r)
    (h : ∃ D : Derivation ℤ K K,
      (∀ r : R, ∃ s : R, D (algebraMap R K r) = algebraMap R K s) ∧ D a ≠ 0) :
    ∃ d : K, d ≠ 0 ∧ ∀ y : Lext p a, IsIntegral R y → ∀ j : Fin (pb p a).dim,
      ∃ r : R, d * (pb p a).basis.repr y j = algebraMap R K r := by
  classical
  -- Clear the denominator of `a`: get `f ≠ 0 ∈ R` with `(algebraMap R K f) * a ∈ image R`.
  obtain ⟨xnum, f, hf_mem, hxy⟩ := IsFractionRing.div_surjective (A := R) (K := K) a
  have hfne : f ≠ 0 := nonZeroDivisors.ne_zero hf_mem
  -- `Cf := algebraMap R K f ≠ 0`.
  set Cf : K := algebraMap R K f with hCfdef
  have hCfne : Cf ≠ 0 := (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R K)).mpr hfne
  -- `Cf * a = algebraMap R K xnum`.
  have hCfa : Cf * a = algebraMap R K xnum := by
    rw [div_eq_iff hCfne] at hxy
    rw [hxy, hCfdef]; ring
  -- The new element `a' = Cf^p * a`, which lies in the image of `R`.
  obtain ⟨D, hD, hDa⟩ := h
  have hp1 : 1 ≤ p := (Fact.out (p := p.Prime)).pos
  set a' : K := Cf ^ p * a with ha'def
  -- `a'` is in the image of `R`: `a' = algebraMap R K (f^(p-1) * xnum)`.
  have ha'img : a' = algebraMap R K (f ^ (p - 1) * xnum) := by
    rw [ha'def, map_mul, map_pow, ← hCfdef]
    calc Cf ^ p * a = Cf ^ (p - 1) * (Cf * a) := by
            rw [← mul_assoc, ← pow_succ, show p - 1 + 1 = p by omega]
      _ = Cf ^ (p - 1) * algebraMap R K xnum := by rw [hCfa]
  -- `D` kills `p`-th powers in `K`.
  have hDpow := derivation_pow_char p D
  -- `D a' = Cf^p * D a`, hence nonzero.
  have hDa' : D a' = Cf ^ p * D a := by
    rw [ha'def, Derivation.leibniz, hDpow, smul_zero, add_zero, smul_eq_mul]
  have hDa'ne : D a' ≠ 0 := by
    rw [hDa']
    exact mul_ne_zero (pow_ne_zero _ hCfne) hDa
  -- Apply `H` to `a'`.
  obtain ⟨d', hd'0, hbound'⟩ := H a' ⟨f ^ (p - 1) * xnum, ha'img⟩ ⟨D, hD, hDa'ne⟩
  -- The two power bases have the same dimension `p`.
  have hdim : (pb p a).dim = p := pb_dim p a
  have hdim' : (pb p a').dim = p := pb_dim p a'
  -- The root `β` of `X^p - C a'` and the rescaled element `t = Cf⁻¹ * β`.
  set β : Lext p a' := (pb p a').gen with hβ
  have hβp : β ^ p = algebraMap K (Lext p a') a' := by rw [hβ, pb_gen]; exact root_pow p a'
  set t : Lext p a' := algebraMap K (Lext p a') Cf⁻¹ * β with htdef
  -- `t^p = algebraMap K (Lext p a') a`.
  have htp : t ^ p = algebraMap K (Lext p a') a := by
    rw [htdef, mul_pow, ← map_pow, hβp, ha'def, ← map_mul]
    congr 1
    rw [inv_pow]
    field_simp
  -- The eval₂ hypothesis: `t` is a root of `X^p - C a`.
  have hev : Polynomial.eval₂ (algebraMap K (Lext p a')) t
      (Polynomial.X ^ p - Polynomial.C a) = 0 := by
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, htp,
      sub_self]
  -- The K-algebra hom `φ : Lext p a →ₐ[K] Lext p a'` sending the root to `t`.
  set φ : Lext p a →ₐ[K] Lext p a' :=
    AdjoinRoot.liftAlgHom _ (Algebra.ofId K (Lext p a')) t hev with hφdef
  have hφα : φ (pb p a).gen = t := by
    rw [pb_gen, hφdef]; exact AdjoinRoot.liftAlgHom_root _ _ _ _
  -- `φ` is an `R`-algebra hom too (restrict scalars), so it preserves integrality.
  have hφint : ∀ y : Lext p a, IsIntegral R y → IsIntegral R (φ y) := by
    intro y hy
    exact hy.map (φ.restrictScalars R)
  -- repr of an explicit coordinate sum in `pb p a'`.
  -- The repr of `β^m` in `pb p a'`.
  have hreprβ : ∀ (m : ℕ) (hm : m < (pb p a').dim) (k : Fin (pb p a').dim),
      (pb p a').basis.repr (β ^ m) k = if (k : ℕ) = m then 1 else 0 := by
    intro m hm k
    have hsum : β ^ m = ∑ i : Fin (pb p a').dim,
        (if (i : ℕ) = m then (1 : K) else 0) • (pb p a').gen ^ (i : ℕ) := by
      rw [Finset.sum_eq_single (⟨m, hm⟩ : Fin (pb p a').dim)]
      · rw [ite_eq_left rfl, one_smul, hβ]
      · intro b _ hb
        rw [ite_eq_right (fun hh => hb (Fin.ext hh)), zero_smul]
      · intro hcon; exact absurd (Finset.mem_univ _) hcon
    rw [hsum, repr_sum_smul_gen_pow]
  -- The key coordinate relation: `repr_{a'} (φ y) j' = Cf⁻¹^j * repr_a y j`.
  have hkey : ∀ (y : Lext p a) (j : Fin (pb p a).dim)
      (j' : Fin (pb p a').dim) (hjj' : (j' : ℕ) = (j : ℕ)),
      (pb p a').basis.repr (φ y) j' = Cf⁻¹ ^ (j : ℕ) * (pb p a).basis.repr y j := by
    intro y j j' hjj'
    -- Express `y` in the power basis and push `φ` through.
    have hφy : φ y = ∑ m : Fin (pb p a).dim,
        ((pb p a).basis.repr y m * Cf⁻¹ ^ (m : ℕ)) • β ^ (m : ℕ) := by
      conv_lhs => rw [eq_sum_repr_smul_gen_pow (pb p a) y]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro m _
      rw [map_smul, map_pow, hφα, htdef, mul_pow, ← map_pow]
      rw [Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul]
    rw [hφy, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · rw [map_smul, Finsupp.smul_apply,
        hreprβ (j : ℕ) (by rw [hdim']; exact j.isLt.trans_eq hdim) j',
        ite_eq_left hjj', smul_eq_mul, mul_one, mul_comm]
    · intro m _ hm
      rw [map_smul, Finsupp.smul_apply,
        hreprβ (m : ℕ) (by rw [hdim']; exact m.isLt.trans_eq hdim) j',
        ite_eq_right (by rw [hjj']; exact fun hh => hm (Fin.ext hh.symm)), smul_zero]
    · intro hcon; exact absurd (Finset.mem_univ j) hcon
  -- Conclude with `d := d'`.
  refine ⟨d', hd'0, ?_⟩
  intro y hy j
  -- The corresponding index in `pb p a'`.
  set j' : Fin (pb p a').dim := ⟨(j : ℕ), j.isLt.trans_eq hdim |>.trans_eq hdim'.symm⟩ with hj'def
  obtain ⟨r, hr⟩ := hbound' (φ y) (hφint y hy) j'
  rw [hkey y j j' (by rw [hj'def])] at hr
  -- `d' * (Cf⁻¹^j * c_j) = algebraMap R K r`; multiply by `Cf^j = algebraMap (f^j)`.
  refine ⟨f ^ (j : ℕ) * r, ?_⟩
  calc d' * (pb p a).basis.repr y j
      = Cf ^ (j : ℕ) * (d' * (Cf⁻¹ ^ (j : ℕ) * (pb p a).basis.repr y j)) := by
        rw [← mul_assoc, mul_comm (Cf ^ (j : ℕ)) d', mul_assoc d', ← mul_assoc (Cf ^ (j:ℕ)),
          ← mul_pow, mul_inv_cancel₀ hCfne, one_pow, one_mul]
    _ = Cf ^ (j : ℕ) * algebraMap R K r := by rw [hr]
    _ = algebraMap R K (f ^ (j : ℕ) * r) := by rw [hCfdef, map_mul, map_pow]

omit [IsDomain R] [IsNoetherianRing R] in
/-- **The coordinate denominator bound in the case `a ∈ R`** — the derivation
induction core. Assume `a = algebraMap R K a₀` for some `a₀ : R`, and a
derivation `D` mapping `R` to `R` with `δ := D a ≠ 0`. Since `a ∈ R`, also
`δ ∈ R`, the root `α` is integral over `R`, and we may take `d := δ^(p-1)`.

Proof by induction on the support degree `i`: if `y` is integral over `R` and
`repr y j = 0` for `j > i`, then `δ^i · repr y j ∈ R` for all `j`. The step uses
`pow_eq_sum_repr` + `pow_mem_R` to get `y^p ∈ R`, applies `D` (which kills the
`p`-th powers `c_j^p` and, by Leibniz, extracts `δ · Σ_{j≥1} j c_j^p a^{j-1}`),
forms the lower-degree auxiliary element `z := Σ_{j≥1} (j δ c_j) α^{j-1}` whose
`p`-th power is `δ^{p-1} · (δ Σ j c_j^p a^{j-1}) ∈ R` (here `δ^{p-1} ∈ R` uses
`a ∈ R`), so `z` is integral, and the IH on `z` peels each coordinate using that
`1, …, p-1` are units mod `p`. -/
theorem coord_denom_bound_integral
    (a₀ : R) (ha : a = algebraMap R K a₀)
    (h : ∃ D : Derivation ℤ K K,
      (∀ r : R, ∃ s : R, D (algebraMap R K r) = algebraMap R K s) ∧ D a ≠ 0) :
    ∃ d : K, d ≠ 0 ∧ ∀ y : Lext p a, IsIntegral R y → ∀ j : Fin (pb p a).dim,
      ∃ r : R, d * (pb p a).basis.repr y j = algebraMap R K r := by
  obtain ⟨D, hD, hDa⟩ := h
  -- δ = D a lies in R; pick δ₀ : R with D a = algebraMap R K δ₀, δ₀ ≠ 0.
  obtain ⟨δ₀, hδ₀⟩ := hD a₀
  rw [← ha] at hδ₀
  have hδ₀ne : δ₀ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hδ₀
    exact hDa hδ₀
  -- Abbreviations.
  set α : Lext p a := (pb p a).gen with hα
  -- `α` is integral over `R`: it is a root of the monic `X^p - C a₀ ∈ R[X]`.
  have hαint : IsIntegral R α :=
    IsIntegral.of_pow (Fact.out (p := p.Prime)).pos (by
      rw [hα, pb_gen, root_pow, ha, ← IsScalarTower.algebraMap_apply]
      exact isIntegral_algebraMap)
  -- `δ := D a` kills `p`-th powers: `D (c^p) = 0` for any `c : K`.
  have hDpow := derivation_pow_char p D
  -- The "diagonal sum" `S y := ∑ c_j^p a^j` lies in `R` when `y` integral.
  have hSmem : ∀ y : Lext p a, IsIntegral R y →
      ∃ r : R, (∑ j : Fin (pb p a).dim, ((pb p a).basis.repr y j) ^ p * a ^ (j : ℕ))
        = algebraMap R K r := by
    intro y hy
    obtain ⟨r, hr⟩ := pow_mem_R p a y hy
    refine ⟨r, ?_⟩
    apply algMap_inj p a
    rw [← pow_eq_sum_repr, hr, ← IsScalarTower.algebraMap_apply]
  -- Set `δ := D a = algebraMap R K δ₀`.
  set δ : K := algebraMap R K δ₀ with hδdef
  have hδval : D a = δ := hδ₀
  have hδne : δ ≠ 0 := (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R K)).mpr hδ₀ne
  have hdim : (pb p a).dim = p := pb_dim p a
  -- A `δ`-power lies in `R`.
  have hδpowmem : ∀ i : ℕ, ∃ r : R, δ ^ i = algebraMap R K r :=
    fun i => ⟨δ₀ ^ i, by rw [hδdef, map_pow]⟩
  -- The key inductive claim, on the support degree `i`.
  have key : ∀ i : ℕ, ∀ y : Lext p a, IsIntegral R y →
      (∀ j : Fin (pb p a).dim, i < (j : ℕ) → (pb p a).basis.repr y j = 0) →
      ∀ j : Fin (pb p a).dim, ∃ r : R, δ ^ i * (pb p a).basis.repr y j = algebraMap R K r := by
    -- `(n : K)^p = n`.
    have hnatfrob : ∀ n : ℕ, (n : K) ^ p = (n : K) := by
      intro n; rw [← frobenius_def]; exact map_natCast (frobenius K p) n
    -- `(p : R) = 0` (pulled back from `K` along the injective `R → K`).
    have hpR : (p : R) = 0 := by
      apply FaithfulSMul.algebraMap_injective R K
      rw [map_natCast, map_zero]; exact_mod_cast CharP.cast_eq_zero K p
    -- `(j : R)` is a unit in `R` for `0 < j < p`.
    have hunit : ∀ j : ℕ, 0 < j → j < p → IsUnit ((j : R)) := by
      intro j hj0 hjp
      have hcop : Nat.Coprime j p :=
        (Nat.coprime_comm.mp ((Fact.out (p := p.Prime)).coprime_iff_not_dvd.mpr
          (fun hdvd => by have := Nat.le_of_dvd hj0 hdvd; omega)))
      -- Bezout: `j * gcdA + p * gcdB = 1` over `ℤ`; reduce mod `p` (= 0 in `R`).
      have hbez : (j : ℤ) * (Int.gcdA j p) + (p : ℤ) * (Int.gcdB j p) = 1 := by
        have h := Int.gcd_eq_gcd_ab j p
        rw [Int.gcd_natCast_natCast, hcop] at h
        push_cast at h ⊢; linarith [h]
      have hR : (j : R) * (Int.cast (Int.gcdA j p) : R)
          + (p : R) * (Int.cast (Int.gcdB j p) : R) = 1 := by
        have := congrArg (Int.cast : ℤ → R) hbez
        push_cast at this; convert this using 2
      rw [hpR, zero_mul, add_zero] at hR
      exact ⟨⟨(j : R), (Int.cast (Int.gcdA j p) : R), hR, by rw [mul_comm, hR]⟩, rfl⟩
    intro i
    induction i with
    | zero =>
      intro y hy hsupp j
      rw [pow_zero, one_mul]
      by_cases hj0 : (j : ℕ) = 0
      · -- `y = algebraMap K L (repr y 0)`, so `repr y 0` integral over `R`, hence in `R`.
        have hsingle : (∑ m, (pb p a).basis.repr y m • (pb p a).gen ^ (m : ℕ))
            = (pb p a).basis.repr y j • (pb p a).gen ^ (j : ℕ) := by
          apply Finset.sum_eq_single j
          · intro k _ hk
            have hzk : (pb p a).basis.repr y k = 0 := by
              apply hsupp k
              have : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext (by rw [h, ← hj0]))
              omega
            rw [hzk, zero_smul]
          · intro hcon; exact absurd (Finset.mem_univ j) hcon
        have hy0 : y = algebraMap K (Lext p a) ((pb p a).basis.repr y j) := by
          conv_lhs => rw [eq_sum_repr_smul_gen_pow (pb p a) y, hsingle, hj0, pow_zero,
            Algebra.smul_def, mul_one]
        obtain ⟨r, hr⟩ := exists_algebraMap_eq_of_isIntegral _ (by rw [← hy0]; exact hy)
        exact ⟨r, hr.symm⟩
      · have : (pb p a).basis.repr y j = 0 := hsupp j (by omega)
        exact ⟨0, by rw [this, map_zero]⟩
    | succ i ih =>
      intro y hy hsupp
      -- Coordinates as a function on `ℕ` (0 outside range).
      set c : ℕ → K := fun m => if h : m < (pb p a).dim then (pb p a).basis.repr y ⟨m, h⟩ else 0
        with hc
      have hcj : ∀ j : Fin (pb p a).dim, c (j : ℕ) = (pb p a).basis.repr y j := by
        intro j; rw [hc]; simp only [j.isLt, dite_eq_left]
      -- The diagonal sum `S = ∑ c_j^p a^j` lies in `R`, so `D S ∈ R`.
      obtain ⟨s, hs⟩ := hSmem y hy
      obtain ⟨s', hs'⟩ := hD s
      -- `D S = δ * Σ'`, where `Σ' = ∑_j (j:K) c_j^p a^{j-1}`.
      have hDS : D (∑ j : Fin (pb p a).dim, ((pb p a).basis.repr y j) ^ p * a ^ (j : ℕ))
          = δ * ∑ j : Fin (pb p a).dim,
            ((j : ℕ) : K) * ((pb p a).basis.repr y j) ^ p * a ^ ((j : ℕ) - 1) := by
        rw [map_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [Derivation.leibniz, hDpow, smul_zero, add_zero, Derivation.leibniz_pow, hδval]
        simp only [smul_eq_mul, nsmul_eq_mul]
        ring
      -- Hence `δ * Σ' = algebraMap R K s'` (an element of `R`).
      have hSig : δ * (∑ j : Fin (pb p a).dim,
          ((j : ℕ) : K) * ((pb p a).basis.repr y j) ^ p * a ^ ((j : ℕ) - 1)) =
            algebraMap R K s' := by
        rw [← hDS, hs, hs']
      -- The auxiliary lower-degree element `z = ∑_j ((j:K) δ c_j) • α^{j-1}`.
      set w : Fin (pb p a).dim → K :=
        fun k => (((k : ℕ) + 1 : ℕ) : K) * δ * c ((k : ℕ) + 1) with hw
      set z : Lext p a := ∑ m, w m • (pb p a).gen ^ (m : ℕ) with hz
      have hzrepr : ∀ k, (pb p a).basis.repr z k = w k := repr_sum_smul_gen_pow (pb p a) w
      -- `z^p ∈ R`, hence `z` is integral over `R`.
      have hzint : IsIntegral R z := by
        have hzp : z ^ p = algebraMap K (Lext p a)
            (∑ m : Fin (pb p a).dim, (w m) ^ p * a ^ (m : ℕ)) := by
          rw [pow_eq_sum_repr p a z]; congr 1; apply Finset.sum_congr rfl
          intro m _; rw [hzrepr m]
        -- The inner sum equals `δ^(p-1) * (δ * Σ')`, which lies in `R`.
        have hinner : (∑ m : Fin (pb p a).dim, (w m) ^ p * a ^ (m : ℕ))
            = δ ^ (p - 1) * (δ * ∑ j : Fin (pb p a).dim,
              ((j : ℕ) : K) * ((pb p a).basis.repr y j) ^ p * a ^ ((j : ℕ) - 1)) := by
          -- First, simplify `(w m)^p`.
          have hp1 : 1 ≤ p := (Fact.out (p := p.Prime)).pos
          have hdpos : 1 ≤ (pb p a).dim := by rw [hdim]; exact hp1
          have hwp : ∀ m : Fin (pb p a).dim,
              (w m) ^ p * a ^ (m : ℕ)
                = δ ^ p * (((((m : ℕ) + 1 : ℕ)) : K) * (c ((m : ℕ) + 1)) ^ p * a ^ (m : ℕ)) := by
            intro m
            rw [hw]
            simp only [mul_pow]
            rw [hnatfrob]
            ring
          rw [Finset.sum_congr rfl (fun m _ => hwp m), ← Finset.mul_sum]
          -- Rewrite the RHS coordinates `repr y j` as `c j`.
          simp only [← hcj]
          rw [← mul_assoc, ← pow_succ, show p - 1 + 1 = p by omega]
          congr 1
          -- Reindexing identity `m ↦ m+1` over `Finset.range`.
          rw [Fin.sum_univ_eq_sum_range
                (fun m => (((m + 1 : ℕ)) : K) * (c (m + 1)) ^ p * a ^ m),
            Fin.sum_univ_eq_sum_range
                (fun j => ((j : ℕ) : K) * (c j) ^ p * a ^ (j - 1))]
          rw [show (pb p a).dim = ((pb p a).dim - 1) + 1 by omega]
          rw [Finset.sum_range_succ' (fun j => ((j : ℕ) : K) * (c j) ^ p * a ^ (j - 1)),
            Finset.sum_range_succ (fun m => (((m + 1 : ℕ)) : K) * (c (m + 1)) ^ p * a ^ m)]
          have hcdim : c ((pb p a).dim - 1 + 1) = 0 := by
            rw [hc]; simp only [dite_eq_right (show ¬ (pb p a).dim - 1 + 1 < (pb p a).dim by omega)]
          have hp0 : p ≠ 0 := (Fact.out (p := p.Prime)).pos.ne'
          rw [hcdim]
          simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.add_sub_cancel,
            zero_pow hp0]
        obtain ⟨r0, hr0⟩ := hδpowmem (p - 1)
        rw [hinner, hSig, hr0] at hzp
        refine IsIntegral.of_pow (Fact.out (p := p.Prime)).pos ?_
        rw [hzp, map_mul, ← IsScalarTower.algebraMap_apply,
          ← IsScalarTower.algebraMap_apply, ← map_mul]
        exact isIntegral_algebraMap
      -- Apply the IH to `z` (support degree ≤ i).
      have hzsupp : ∀ k : Fin (pb p a).dim, i < (k : ℕ) → (pb p a).basis.repr z k = 0 := by
        intro k hk
        rw [hzrepr k]
        have hck : c ((k : ℕ) + 1) = 0 := by
          rw [hc]
          by_cases hlt : (k : ℕ) + 1 < (pb p a).dim
          · simp only [dite_eq_left hlt]
            apply hsupp ⟨(k : ℕ) + 1, hlt⟩
            simp only []; omega
          · simp only [dite_eq_right hlt]
        simp only [hw, hck, mul_zero]
      have ihz := ih z hzint hzsupp
      -- Conclude for `y`: handle `j ≥ 1` (peel via the unit `(j:R)`) and `j = 0` (difference).
      have hp1 : 1 ≤ p := (Fact.out (p := p.Prime)).pos
      -- For `j ≥ 1`: `δ^(i+1) * repr y j ∈ R`.
      have hge1 : ∀ j : Fin (pb p a).dim, 0 < (j : ℕ) →
          ∃ r : R, δ ^ (i + 1) * (pb p a).basis.repr y j = algebraMap R K r := by
        intro j hjpos
        have hjp : (j : ℕ) < p := j.isLt.trans_eq hdim
        obtain ⟨r, hr⟩ := ihz ⟨(j : ℕ) - 1, by omega⟩
        rw [hzrepr] at hr
        -- `repr z ⟨j-1⟩ = (j:K) * δ * (repr y j)`.
        have hidx : (j : ℕ) - 1 + 1 = (j : ℕ) := by omega
        have hwval : w ⟨(j : ℕ) - 1, by omega⟩ = ((j : ℕ) : K) * δ * (pb p a).basis.repr y j := by
          rw [hw]
          simp only [hidx]
          rw [show c (j : ℕ) = (pb p a).basis.repr y j from hcj j]
        rw [hwval] at hr
        -- Now `δ^i * ((j:K) * δ * repr y j) = algebraMap r`, i.e. `(j:K)*(δ^(i+1)*repr y j) = r`.
        obtain ⟨v, hv⟩ := (hunit (j : ℕ) hjpos hjp).exists_right_inv
        refine ⟨v * r, ?_⟩
        have key1 : ((j : ℕ) : K) * (δ ^ (i + 1) * (pb p a).basis.repr y j) = algebraMap R K r := by
          rw [← hr]; ring
        calc δ ^ (i + 1) * (pb p a).basis.repr y j
            = algebraMap R K v * (((j : ℕ) : K) * (δ ^ (i + 1) * (pb p a).basis.repr y j)) := by
              rw [← map_natCast (algebraMap R K) (j : ℕ), ← mul_assoc, ← map_mul, mul_comm v, hv,
                map_one, one_mul]
          _ = algebraMap R K v * algebraMap R K r := by rw [key1]
          _ = algebraMap R K (v * r) := by rw [map_mul]
      -- For `j = 0`: difference argument.
      have hge0 : ∃ r : R, δ ^ (i + 1) * (pb p a).basis.repr y ⟨0, by omega⟩ =
        algebraMap R K r := by
        set j0 : Fin (pb p a).dim := ⟨0, by omega⟩ with hj0def
        -- A total choice of the `R`-witnesses for `k ≥ 1`.
        set rk : Fin (pb p a).dim → R :=
          fun k => if h : 0 < (k : ℕ) then (hge1 k h).choose else 0 with hrk
        have hrk_spec : ∀ k : Fin (pb p a).dim, 0 < (k : ℕ) →
            δ ^ (i + 1) * (pb p a).basis.repr y k = algebraMap R K (rk k) := by
          intro k hk; rw [hrk]; simp only [dite_eq_left hk]; exact (hge1 k hk).choose_spec
        set t : K := δ ^ (i + 1) * (pb p a).basis.repr y j0 with ht
        -- `δ^(i+1) • y = ∑_k (δ^(i+1) * repr y k) • α^k`.
        have hYeq : algebraMap K (Lext p a) (δ ^ (i + 1)) * y
            = algebraMap K (Lext p a) t
              + ∑ k ∈ Finset.univ.erase j0,
                  algebraMap R (Lext p a) (rk k) * (pb p a).gen ^ (k : ℕ) := by
          conv_lhs => rw [eq_sum_repr_smul_gen_pow (pb p a) y, Finset.mul_sum]
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j0)]
          congr 1
          · rw [Algebra.smul_def, ← mul_assoc, ← map_mul, ht]
            simp only [hj0def]
            rw [pow_zero, mul_one]
          · apply Finset.sum_congr rfl
            intro k hk
            have hkpos : 0 < (k : ℕ) := by
              rcases Nat.eq_zero_or_pos (k : ℕ) with h0 | h0
              · exact absurd (Fin.ext h0 : k = j0) (Finset.ne_of_mem_erase hk)
              · exact h0
            rw [Algebra.smul_def, ← mul_assoc, ← map_mul, hrk_spec k hkpos,
              ← IsScalarTower.algebraMap_apply]
        -- `algebraMap t` is integral, hence `t ∈ R`.
        have hint : IsIntegral R (algebraMap K (Lext p a) t) := by
          have heq : algebraMap K (Lext p a) t
              = algebraMap K (Lext p a) (δ ^ (i + 1)) * y
                - ∑ k ∈ Finset.univ.erase j0,
                    algebraMap R (Lext p a) (rk k) * (pb p a).gen ^ (k : ℕ) := by
            rw [hYeq]; ring
          obtain ⟨rd, hrd⟩ := hδpowmem (i + 1)
          rw [heq, hrd, ← IsScalarTower.algebraMap_apply]
          exact (isIntegral_algebraMap.mul hy).sub
            (IsIntegral.sum _ fun k _ => isIntegral_algebraMap.mul (hαint.pow _))
        obtain ⟨r, hr⟩ := exists_algebraMap_eq_of_isIntegral _ hint
        exact ⟨r, hr.symm⟩
      -- Combine.
      intro j
      rcases Nat.eq_zero_or_pos (j : ℕ) with hj0 | hjpos
      · have hje : j = ⟨0, by omega⟩ := Fin.ext hj0
        rw [hje]; exact hge0
      · exact hge1 j hjpos
  -- Apply at `i = p - 1`: the support condition is vacuous.
  refine ⟨δ ^ (p - 1), pow_ne_zero _ hδne, ?_⟩
  intro y hy j
  refine key (p - 1) y hy ?_ j
  intro j hj
  exfalso
  have : (j : ℕ) < p := j.isLt.trans_eq hdim
  omega

omit [IsNoetherianRing R] in
/-- A single nonzero `d : K` clears the denominators of all power-basis coordinates of
every integral element at once. -/
theorem coord_denom_bound
    (h : ∃ D : Derivation ℤ K K,
      (∀ r : R, ∃ s : R, D (algebraMap R K r) = algebraMap R K s) ∧ D a ≠ 0) :
    ∃ d : K, d ≠ 0 ∧ ∀ y : Lext p a, IsIntegral R y → ∀ j : Fin (pb p a).dim,
      ∃ r : R, d * (pb p a).basis.repr y j = algebraMap R K r := by
  -- Reduce to the case `a ∈ R` (`coord_denom_bound_reduce`), then apply the
  -- derivation induction in that case (`coord_denom_bound_integral`).
  refine coord_denom_bound_reduce p a (fun a' ha' h' => ?_) h
  obtain ⟨a₀, ha₀⟩ := ha'
  exact coord_denom_bound_integral p a' a₀ ha₀ h'

/-! ## The inclusion `integralClosure ⊆ d⁻¹ · spanPow` -/

omit [IsNoetherianRing R] in
/-- The integral closure of `R` in `L` is contained in the image of the finitely
generated module `spanPow` under multiplication by a single fixed element
`e = algebraMap K L d⁻¹`. Derived from the coordinate denominator bound:
writing `y = ∑_j (repr y j) • α^j`, the bound gives `r_j ∈ R` with
`d · repr y j = algebraMap R K r_j`, so `y = e · (∑_j r_j • α^j)` with the inner
sum in `spanPow`. -/
theorem integralClosure_le_smul_spanPow
    (h : ∃ D : Derivation ℤ K K,
      (∀ r : R, ∃ s : R, D (algebraMap R K r) = algebraMap R K s) ∧ D a ≠ 0) :
    ∃ e : Lext p a,
      Subalgebra.toSubmodule (integralClosure R (Lext p a)) ≤
        Submodule.map ((LinearMap.mulLeft K e).restrictScalars R) (spanPow p a) := by
  obtain ⟨d, hd0, hbound⟩ := coord_denom_bound p a h
  refine ⟨algebraMap K (Lext p a) d⁻¹, ?_⟩
  intro y hy
  simp only [Subalgebra.mem_toSubmodule, mem_integralClosure_iff] at hy
  rw [Submodule.mem_map]
  choose r hr using hbound y hy
  refine ⟨∑ j : Fin (pb p a).dim, (r j) • (pb p a).gen ^ (j : ℕ), ?_, ?_⟩
  · apply Submodule.sum_mem
    intro j _
    exact Submodule.smul_mem _ _ (gen_pow_mem p a j)
  · simp only [LinearMap.restrictScalars_apply, LinearMap.mulLeft_apply, Finset.mul_sum]
    rw [eq_sum_repr_smul_gen_pow (pb p a) y]
    apply Finset.sum_congr rfl
    intro j _
    rw [Algebra.smul_def, Algebra.smul_def]
    rw [show (algebraMap R (Lext p a)) (r j) = algebraMap K (Lext p a) (algebraMap R K (r j)) by
      rw [← IsScalarTower.algebraMap_apply]]
    have hcoeff : d⁻¹ * algebraMap R K (r j) = (pb p a).basis.repr y j := by
      rw [← hr j]; field_simp
    rw [← mul_assoc, ← map_mul, hcoeff]

/-! ## Packaging the finiteness -/

omit [IsNoetherianRing R] in
/-- **Content of Stacks 0AE0 (finiteness packaging).**
The integral closure of `R` in `L` is contained in a *finitely generated*
`R`-submodule `N` of `L`. Take `N` to be the image of `spanPow` (which is `FG`
by `spanPow_fg`) under multiplication by the fixed element `e` from
`integralClosure_le_smul_spanPow`; `N` is `FG` as the `R`-linear image of an `FG`
module, and contains the integral closure by that lemma. -/
theorem exists_fg_le
    (h : ∃ D : Derivation ℤ K K,
      (∀ r : R, ∃ s : R, D (algebraMap R K r) = algebraMap R K s) ∧ D a ≠ 0) :
    ∃ N : Submodule R (Lext p a), N.FG ∧
      Subalgebra.toSubmodule (integralClosure R (Lext p a)) ≤ N := by
  obtain ⟨e, hle⟩ := integralClosure_le_smul_spanPow p a h
  exact ⟨_, (spanPow_fg p a).map _, hle⟩

/-! ## The main statement -/

/-- **Stacks 0AE0.** The integral closure of `R` in `L = K[x]/(x^p - a)` is
finite over `R`. Given the finitely generated `R`-module `N ⊇ integral closure`
from `exists_fg_le`, the integral closure is a submodule of the f.g. module `N`
over the Noetherian ring `R`, hence itself f.g. (`Submodule.FG.of_le`), hence
finite (`Module.Finite.of_fg`). -/
@[stacks 0AE0]
theorem integralClosure_finite
    (h : ∃ D : Derivation ℤ K K,
      (∀ r : R, ∃ s : R, D (algebraMap R K r) = algebraMap R K s) ∧ D a ≠ 0) :
    Module.Finite R (integralClosure R (Lext p a)) := by
  obtain ⟨N, hNfg, hle⟩ := exists_fg_le p a h
  have hfg : (Subalgebra.toSubmodule (integralClosure R (Lext p a))).FG :=
    Submodule.FG.of_le hNfg hle
  exact Module.Finite.of_fg hfg

end Stacks.Nagata.PurelyInseparable
