module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicCompactSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationSheaf

/-!
# The weight bound of Weil II on curves

The proof of [Stacks, Tag 03VH] (Deligne, *La conjecture de Weil II*, 3.2–3.3) bounds the weights
of `Hⁱ_c` first on curves and then reduces a variety of dimension `d` to curves by fibring it.
This file states the curve case in the form the reduction consumes.

A continuous `ρ : π₁(U, x̄) → GL_r(K)` on a connected scheme `U` of finite type over a finite
field `k` with `q` elements is *pointwise `ι`-mixed of weights `≤ w`* when for every closed point
`y` of `U` every complex root of the characteristic polynomial of `ρ(F_y)`, read along
`ι : K →+* ℂ`, has absolute value `q ^ (deg y · w' / 2)` for an integer `w' ≤ w` (Weil II 1.2.2;
`F_y` is the geometric Frobenius element `Stacks.EtaleCohomology.geometricFrobeniusFamily`).
It is *`ι`-realizable* when it is a direct summand of a representation whose Frobenius
characteristic polynomials have `ι`-real coefficients (Weil II 1.5; Kedlaya, *Fourier transforms
and p-adic Weil II*, §6). The curve case asserts that for such `ρ`, pointwise mixed and
realizable, on a smooth geometrically connected curve the complex
roots of the characteristic polynomial of `π_U^*` on `Hⁱ_c(U_k̄, ℱ_ρ ⊗ ℚ_ℓ)` along `ι` have
absolute value `q ^ (w' / 2)` for an integer `w' ≤ w + i`.

Only absolute values along the single embedding `ι` appear: the argument of Weil II is carried
out one embedding at a time, and the algebraicity of the eigenvalues in Tag 03VH comes at the end
from the bound along every embedding
(`Stacks.EtaleCohomology.isCharpolyMixedOfWeightLE_of_forall_norm_eq`).

## Main definitions

* `Stacks.EtaleCohomology.IsPointwiseMixedOfWeightLE` — pointwise `ι`-mixedness of weights
  `≤ w` of a representation of `π₁`.
* `Stacks.EtaleCohomology.IsIotaRealizable` — `ι`-realizability.
* `Stacks.EtaleCohomology.WeilIICurveBound` — the statement of the curve case, for all curves
  over all finite fields.

## Main results

* `Stacks.EtaleCohomology.HasDeligneConclusions.isPointwiseMixedOfWeightLE` — a representation
  satisfying the conclusions of Deligne's conjecture is pointwise `ι`-mixed of weights `≤ 0`;
  `Stacks.EtaleCohomology.HasDeligneConclusions.isIotaRealizable` — and `ι`-realizable, with
  witness its contragredient.

## References

* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
* P. Deligne, *La conjecture de Weil II*, Publ. Math. IHÉS 52 (1980), 1.2.2, 3.2.3.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

section DualCharpoly

open Polynomial

/-- `dualCharpoly` is multiplicative. -/
public theorem dualCharpoly_mul {F : Type*} [Field F] (P Q : F[X]) :
    dualCharpoly (P * Q) = dualCharpoly P * dualCharpoly Q := by
  rw [dualCharpoly, dualCharpoly, dualCharpoly, reverse_mul_of_domain, mul_coeff_zero, mul_inv,
    C_mul]
  ring

/-- The dual of a linear factor `Polynomial.X - z` with `z ≠ 0` is `Polynomial.X - z⁻¹`. -/
public theorem dualCharpoly_X_sub_C {F : Type*} [Field F] {z : F} (hz : z ≠ 0) :
    dualCharpoly (Polynomial.X - Polynomial.C z) = Polynomial.X - Polynomial.C z⁻¹ := by
  have hrev : (Polynomial.X - Polynomial.C z).reverse = 1 - Polynomial.C z * Polynomial.X := by
    rw [sub_eq_add_neg, ← C_neg, reverse_add_C, natDegree_X]
    have : (Polynomial.X : F[X]).reverse = 1 := by
      rw [← one_mul (Polynomial.X : F[X]), reverse_mul_X, ← C_1, reverse_C]
    rw [this, pow_one, C_neg, neg_mul]
    ring
  rw [dualCharpoly, hrev, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, inv_neg, C_neg,
    neg_mul, mul_sub, mul_one, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hz, C_1]
  ring

/-- **A product with its dual is conjugation invariant when the roots are unimodular**: for a
multiset `M` of complex numbers of absolute value `1`, the polynomial `Q · Q^∨` with
`Q = ∏_{z ∈ M} (Polynomial.X - z)` has real coefficients, since `z̄ = z⁻¹`. -/
public theorem map_conj_prod_mul_dualCharpoly (M : Multiset ℂ) (hM : ∀ z ∈ M, ‖z‖ = 1) :
    ((M.map fun z => Polynomial.X - Polynomial.C z).prod *
        dualCharpoly (M.map fun z => Polynomial.X - Polynomial.C z).prod).map (starRingEnd ℂ) =
      (M.map fun z => Polynomial.X - Polynomial.C z).prod *
        dualCharpoly (M.map fun z => Polynomial.X - Polynomial.C z).prod := by
  induction M using Multiset.induction_on with
  | empty =>
    rw [Multiset.map_zero, Multiset.prod_zero, dualCharpoly, ← C_1, reverse_C]
    simp
  | cons a M ih =>
    have ha : ‖a‖ = 1 := hM a (Multiset.mem_cons_self a M)
    have ha0 : a ≠ 0 := by
      intro h
      rw [h, norm_zero] at ha
      exact zero_ne_one ha
    have hconj : (starRingEnd ℂ) a = a⁻¹ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, ha]
      simp
    have ih' := ih fun z hz => hM z (Multiset.mem_cons_of_mem hz)
    simp only [Multiset.map_cons, Multiset.prod_cons, dualCharpoly_mul,
      dualCharpoly_X_sub_C ha0] at ih' ⊢
    have key : ((Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C a⁻¹)).map
        (starRingEnd ℂ) = (Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C a⁻¹) := by
      simp only [Polynomial.map_mul, Polynomial.map_sub, map_X, map_C, hconj, map_inv₀, inv_inv]
      ring
    calc ((Polynomial.X - Polynomial.C a) * (M.map fun z => Polynomial.X - Polynomial.C z).prod *
          ((Polynomial.X - Polynomial.C a⁻¹) *
            dualCharpoly (M.map fun z => Polynomial.X - Polynomial.C z).prod)).map (starRingEnd ℂ)
        = (((Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C a⁻¹)) *
            ((M.map fun z => Polynomial.X - Polynomial.C z).prod *
              dualCharpoly (M.map fun z => Polynomial.X - Polynomial.C z).prod)).map
              (starRingEnd ℂ) := by ring_nf
      _ = ((Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C a⁻¹)) *
            ((M.map fun z => Polynomial.X - Polynomial.C z).prod *
              dualCharpoly (M.map fun z => Polynomial.X - Polynomial.C z).prod) := by
          rw [Polynomial.map_mul, key, ih']
      _ = _ := by ring

end DualCharpoly

section Pointwise

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}} [ConnectedSpace X]
  (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : GeometricPoint X)
  {K : Type*} [Field K] {r : ℕ}

/-- **Pointwise `ι`-mixedness of weights `≤ w`** (Weil II 1.2.2) of a representation
`ρ : π₁(X, x̄) → GL_r(K)` of a connected scheme `X` of finite type over a finite field with `q`
elements: at every closed point `y`, every complex root of the characteristic polynomial of the
geometric Frobenius `ρ(F_y)` read along `ι` has absolute value `q ^ (deg y · w' / 2)` for some
integer `w' ≤ w`. -/
public def IsPointwiseMixedOfWeightLE (q : ℕ) (ι : K →+* ℂ) (w : ℤ)
    (ρ : EtaleFundamentalGroup X x →* GL (Fin r) K) : Prop :=
  ∀ (y : closedPoints X) (z : ℂ),
    (((ρ (geometricFrobeniusFamily f x y) : GL (Fin r) K) :
      Matrix (Fin r) (Fin r) K).charpoly.map ι).IsRoot z →
    ∃ w' : ℤ, w' ≤ w ∧ ‖z‖ = (q : ℝ) ^ (((residueDegree f y.1 : ℤ) * w' : ℝ) / 2)

/-- **`ι`-realizability** (Weil II 1.5, Kedlaya §6) of a representation `ρ : π₁(X, x̄) → GL_r(K)`:
`ρ` is a direct summand of a representation with `ι`-real Frobenius characteristic polynomials,
i.e. there is a continuous `ρ' : π₁(X, x̄) → GL_{r'}(K)` such that at every closed point `y` the
characteristic polynomial of `(ρ ⊕ ρ')(F_y)`, the product of those of `ρ(F_y)` and `ρ'(F_y)`, has
coefficients which `ι` maps into `ℝ`. -/
public def IsIotaRealizable [TopologicalSpace K] (ι : K →+* ℂ)
    (ρ : EtaleFundamentalGroup X x →* GL (Fin r) K) : Prop :=
  ∃ (r' : ℕ) (ρ' : EtaleFundamentalGroup X x →* GL (Fin r') K), Continuous ρ' ∧
    ∀ (y : closedPoints X) (n : ℕ),
      ι (((((ρ (geometricFrobeniusFamily f x y) : GL (Fin r) K) :
          Matrix (Fin r) (Fin r) K).charpoly *
        ((ρ' (geometricFrobeniusFamily f x y) : GL (Fin r') K) :
          Matrix (Fin r') (Fin r') K).charpoly).coeff n)) ∈ Set.range ((↑) : ℝ → ℂ)

variable {f x}

/-- Pointwise mixedness is monotone in the weight. -/
public theorem IsPointwiseMixedOfWeightLE.mono {q : ℕ} {ι : K →+* ℂ} {w w₂ : ℤ}
    {ρ : EtaleFundamentalGroup X x →* GL (Fin r) K} (h : IsPointwiseMixedOfWeightLE f x q ι w ρ)
    (hw : w ≤ w₂) : IsPointwiseMixedOfWeightLE f x q ι w₂ ρ := fun y z hz =>
  let ⟨w', hw', hz'⟩ := h y z hz
  ⟨w', hw'.trans hw, hz'⟩

/-- Pointwise mixedness only sees `ι` on the coefficients of the Frobenius characteristic
polynomials: it passes to any `ι₁` agreeing with `ι` there. -/
public theorem IsPointwiseMixedOfWeightLE.of_eq_on_coeff {q : ℕ} {ι ι₁ : K →+* ℂ} {w : ℤ}
    {ρ : EtaleFundamentalGroup X x →* GL (Fin r) K} (h : IsPointwiseMixedOfWeightLE f x q ι w ρ)
    (heq : ∀ (y : closedPoints X) (n : ℕ),
      ι (((ρ (geometricFrobeniusFamily f x y) : GL (Fin r) K) :
        Matrix (Fin r) (Fin r) K).charpoly.coeff n) =
      ι₁ (((ρ (geometricFrobeniusFamily f x y) : GL (Fin r) K) :
        Matrix (Fin r) (Fin r) K).charpoly.coeff n)) :
    IsPointwiseMixedOfWeightLE f x q ι₁ w ρ := fun y z hz => by
  refine h y z ?_
  have hP : (((ρ (geometricFrobeniusFamily f x y) : GL (Fin r) K) :
      Matrix (Fin r) (Fin r) K).charpoly.map ι) =
      (((ρ (geometricFrobeniusFamily f x y) : GL (Fin r) K) :
        Matrix (Fin r) (Fin r) K).charpoly.map ι₁) :=
    Polynomial.ext fun n => by rw [Polynomial.coeff_map, Polynomial.coeff_map, heq y n]
  rwa [hP]

/-- A representation satisfying the conclusions of Deligne's conjecture at the geometric
Frobenius elements is pointwise `ι`-mixed of weights `≤ 0`: its Frobenius eigenvalues have
absolute value `1 = q ^ 0`. -/
public theorem HasDeligneConclusions.isPointwiseMixedOfWeightLE [TopologicalSpace K] [CharZero K]
    {p q : ℕ} {ι : K →+* ℂ} {ρ : EtaleFundamentalGroup X x →* GL (Fin r) K}
    (h : HasDeligneConclusions (geometricFrobeniusFamily f x) p ι ρ) :
    IsPointwiseMixedOfWeightLE f x q ι 0 ρ := fun y z hz =>
  ⟨0, le_rfl, by rw [h.norm_eq_one y z hz]; simp⟩


/-- **A representation satisfying the conclusions of Deligne's conjecture is `ι`-realizable**, with
witness its contragredient: the Frobenius eigenvalues of `ρ^∨` are the inverses of those of `ρ`,
which are their complex conjugates since they have absolute value `1`, so the characteristic
polynomial of `(ρ ⊕ ρ^∨)(F_y)` is real along `ι`. -/
public theorem HasDeligneConclusions.isIotaRealizable [TopologicalSpace K] [CharZero K]
    {p : ℕ} {ι : K →+* ℂ} {ρ : EtaleFundamentalGroup X x →* GL (Fin r) K} (hρ : Continuous ρ)
    (h : HasDeligneConclusions (geometricFrobeniusFamily f x) p ι ρ) :
    IsIotaRealizable f x ι ρ := by
  refine ⟨r, Stacks.EtaleCohomology.contragredient ρ, continuous_contragredient hρ, fun y n => ?_⟩
  set P := ((ρ (geometricFrobeniusFamily f x y) : GL (Fin r) K) :
    Matrix (Fin r) (Fin r) K).charpoly
  rw [charpoly_contragredient, ← Polynomial.coeff_map, Polynomial.map_mul, ← dualCharpoly_map]
  have hmonic : (P.map ι).Monic := (Matrix.charpoly_monic _).map ι
  have hsplit : ((P.map ι).roots.map fun a => Polynomial.X - Polynomial.C a).prod = P.map ι :=
    Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic
      IsAlgClosed.card_roots_eq_natDegree
  have hconj := map_conj_prod_mul_dualCharpoly (P.map ι).roots fun z hz =>
    h.norm_eq_one y z ((Polynomial.mem_roots hmonic.ne_zero).1 hz)
  rw [hsplit] at hconj
  have hc := congrArg (fun Q => Q.coeff n) hconj
  simp only [Polynomial.coeff_map] at hc
  obtain ⟨c, hc'⟩ := Complex.conj_eq_iff_real.1 hc
  exact ⟨c, hc'.symm⟩

end Pointwise

section Curve

/-- **The weight bound of Weil II on curves** (Deligne, Weil II 3.2.3). For every finite field `k`
with `q = p ^ n` elements, every smooth separated geometrically connected curve `U` over `k` (an
object of a bounded big étale site `B`), every prime `ℓ ≠ p`, every continuous
`ρ : π₁(U, x̄) → GL_r(ℚ_ℓ)` and every `ι : ℚ_ℓ →+* ℂ`: if `ρ` is pointwise `ι`-mixed of weights
`≤ w` and `ι`-realizable, then for every `i` every complex root of the characteristic polynomial of
`π_U^*` on `Hⁱ_c(U_k̄, ℱ_ρ ⊗ ℚ_ℓ)`, read along `ι`, has absolute value `q ^ (w' / 2)` for an
integer `w' ≤ w + i`. -/
public def WeilIICurveBound : Prop :=
  ∀ (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B U.1 U.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [IsNoetherian U.1] [Fact ℓ.Prime] [ConnectedSpace U.1]
    (k : Type u) [Field k] [Fintype k] (f : U.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar]
    [ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
    (p n : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ n) (_ : ℓ ≠ p)
    (x : GeometricPoint U.1) {r : ℕ} (ρ : EtaleFundamentalGroup U.1 x →* GL (Fin r) ℚ_[ℓ])
    (hρ : Continuous ρ) (ι : ℚ_[ℓ] →+* ℂ) (w : ℤ),
    IsPointwiseMixedOfWeightLE f x (p ^ n) ι w ρ → IsIotaRealizable f x ι ρ →
    ∀ (i : ℤ) [FiniteDimensional ℚ_[ℓ]
        (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
          (LAdicSheaf.representationSheaf B U x ρ hρ) i)] (z : ℂ),
      ((ModuleCat.Hom.hom (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B U ℓ f j kbar
        p n hcard (LAdicSheaf.representationSheaf B U x ρ hρ) i)).charpoly.map ι).IsRoot z →
      ∃ w' : ℤ, w' ≤ w + i ∧ ‖z‖ = ((p ^ n : ℕ) : ℝ) ^ ((w' : ℝ) / 2)

end Curve

end Stacks.EtaleCohomology

end
