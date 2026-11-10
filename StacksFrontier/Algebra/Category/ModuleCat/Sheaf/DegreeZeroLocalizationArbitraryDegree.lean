module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjModuleRestriction

/-!
# Degree-zero fractions whose denominator has arbitrary degree

Let `A = ⨁_{n ≥ 0} A n` be a graded ring, let `M = ⨁_{i ∈ ℤ} B i` be a graded `A`-module and let
`f ∈ A d` be a homogeneous element of degree `d`. The degree-zero part `M₍f₎` of the localization
`M_f`, that is `GradedModuleDegreeZeroLocalization A B f`, is spanned by the homogeneous fractions
whose numerator and denominator have the same degree; since the denominators are the powers of
`f`, those are the fractions `x / f ^ n` with `x` homogeneous of degree `n * d`.

This file develops the calculus of such fractions for an *arbitrary* degree `d`: every element of
`M₍f₎` is a single fraction `x / f ^ n` with `x` of degree `n * d`, each such fraction lies in
`M₍f₎`, and a family of additive maps indexed by the *exponent* `n` which is compatible with
multiplying numerator and denominator by `f` descends to an additive map out of `M₍f₎`,
characterized by its values on fractions. The same is done for the ring
`HomogeneousLocalization.Away A f` itself, whose elements are the fractions `a / f ^ n` with `a` of
degree `n * d`.

Taking `d = 1` recovers the family of results of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/NonvanishingSections.lean`
(`Stacks.SheafOfModules.degreeZeroLocalization_exists_fraction`,
`Stacks.SheafOfModules.fractionValue`, `Stacks.SheafOfModules.degreeZeroLocalizationLift`) and the
results `Stacks.SheafOfModules.degreeZeroLocalizationLift_fraction` and
`Stacks.SheafOfModules.mk_mem_degreeZeroLocalization`: the degree-`n * 1` of a numerator is its
degree `n`, so each of those is the `d = 1` instance of its namesake below, up to that
normalization of the index. Those statements are left untouched.

## Main definitions

* `Stacks.SheafOfModules.fractionValueOfDegree` evaluates a degree-zero fraction against a family
  of additive maps indexed by the exponent of the denominator, and
  `Stacks.SheafOfModules.degreeZeroLocalizationLiftOfDegree` packages it as an additive map out of
  the degree-zero localization.
* `Stacks.SheafOfModules.homogeneousLocalizationLiftOfDegree` is the ring-valued counterpart, a
  ring map out of `HomogeneousLocalization.Away A f`.

## Main results

* `Stacks.SheafOfModules.degreeZeroLocalization_exists_fraction_of_degree`: **every element of the
  degree-zero localization is a fraction** with homogeneous numerator of degree `n * d` and
  denominator `f ^ n`.
* `Stacks.SheafOfModules.mk_mem_degreeZeroLocalization_of_degree`: **every such fraction lies in
  the degree-zero localization.**
* `Stacks.SheafOfModules.degreeZeroLocalizationLiftOfDegree_fraction` and
  `Stacks.SheafOfModules.homogeneousLocalizationLiftOfDegree_fraction`: **the value of a lifted
  family on a fraction.**
* `Stacks.SheafOfModules.degreeZeroLocalizationLiftOfDegree_smul`: a lifted family is semilinear
  over a ring map out of `HomogeneousLocalization.Away A f` as soon as it is so on numerators.
* `Stacks.SheafOfModules.eq_zero_iff_exists_pow_smul_eq_zero`: **a fraction vanishes exactly when a
  power of `f` kills its numerator.**

## Implementation notes

The degree of a numerator is spelled `((n * d : ℕ) : ℤ)` throughout, with the product formed in
`ℕ` and then cast, rather than `n • (d : ℤ)` as in the defining span of
`GradedModuleDegreeZeroLocalization` or `(n : ℤ) * d`. The three spellings are crossed exactly
once, in `Stacks.SheafOfModules.natCast_mul_eq_nsmul`, and all degree bookkeeping is done by the
four private lemmas of the `Degrees` section, each of which states its conclusion at an
*arbitrary* exponent `p` together with the equation `_ + _ = p`; that is what lets the same lemma
serve the two orders in which a sum of two fractions is put over a common denominator, without a
rewrite under the binder `B _`.

Positivity of `d` is never needed: for `d = 0` the numerators are the elements of `B 0` and the
statements below remain true, so none of them assumes `0 < d`. Degree `0` is of course of no
geometric use, `D₊(f)` being empty there.

The lift is built from the value `Stacks.SheafOfModules.fractionValueOfDegree` of a chosen
representative together with a proof that the value does not depend on the representative, not by
choosing the additive map itself; `Stacks.SheafOfModules.fraction_values_eq_of_degree` is that
independence.

## References

* [Stacks Project, Tag 01M4](https://stacks.math.columbia.edu/tag/01M4)
-/

@[expose] public noncomputable section

namespace Stacks.SheafOfModules

open DirectSum

universe u v w t

/-! ### Degree bookkeeping -/

section Degrees

variable {R : Type u} {σ : Type w} [CommRing R] [SetLike σ R] [AddSubgroupClass σ R]
  (A : ℕ → σ) [GradedRing A] {f : R} {d : ℕ}

/-- The two spellings of the degree of a numerator over the denominator `f ^ n`: the product
`n * d` formed in `ℕ` and cast to `ℤ`, and the `n`-fold multiple of `(d : ℤ)` used in the span
defining `GradedModuleDegreeZeroLocalization`. -/
private theorem natCast_mul_eq_nsmul (n d : ℕ) : ((n * d : ℕ) : ℤ) = n • (d : ℤ) := by
  rw [nsmul_eq_mul, Nat.cast_mul]

/-- The unit is homogeneous of degree `0 * d`. -/
private theorem one_mem_degree : (1 : R) ∈ A (0 * d) := by
  simpa using SetLike.one_mem_graded A

/-- Homogeneous elements of degrees `m * d` and `n * d` multiply into degree `(m + n) * d`. -/
theorem _root_.SetLike.mul_mem_graded_mul {S : Type*} {τ : Type*} [Mul S] [SetLike τ S]
    {B : ℕ → τ} [SetLike.GradedMul B] {d m n p : ℕ} (hp : m + n = p) {x y : S}
    (hx : x ∈ B (m * d)) (hy : y ∈ B (n * d)) : x * y ∈ B (p * d) := by
  subst hp
  rw [add_mul]
  exact SetLike.mul_mem_graded hx hy

end Degrees

/-! ### Fractions of a graded module -/

section ModuleFractions

/-- The grading action of a naturally graded ring on an integer-graded module, the one under which
`GradedModuleDegreeZeroLocalization` is formed. -/
local instance instVAddNatIntDegreeZeroArbitraryDegree : VAdd ℕ ℤ where
  vadd n z := (n : ℤ) + z

variable {R : Type u} {M : Type v} {σ : Type w} {τ : Type t}
  [CommRing R] [AddCommGroup M] [Module R M]
  [SetLike σ R] [AddSubgroupClass σ R] (A : ℕ → σ) [GradedRing A]
  [SetLike τ M] [AddSubgroupClass τ M] (B : ℤ → τ) [Decomposition B]
  [SetLike.GradedSMul A B] {f : R} {d : ℕ}
  {N : Type*} [AddCommGroup N]

omit [AddSubgroupClass σ R] [GradedRing A] [AddSubgroupClass τ M] [Decomposition B] in
/-- Acting by a homogeneous element of degree `m * d` on a numerator of degree `n * d` gives a
numerator of degree `p * d`, for `p = m + n`. -/
private theorem smul_mem_degree {m n p : ℕ} (hp : m + n = p) {r : R} (hr : r ∈ A (m * d)) {x : M}
    (hx : x ∈ B ((n * d : ℕ) : ℤ)) : r • x ∈ B ((p * d : ℕ) : ℤ) := by
  subst hp
  rw [add_mul, Nat.cast_add]
  exact SetLike.GradedSMul.smul_mem hr hx

omit [AddSubgroupClass τ M] [Decomposition B] in
/-- Multiplying a numerator of degree `n * d` by `f ^ k` gives a numerator of degree `p * d`, for
`p = n + k`: this is what clears denominators. -/
public theorem pow_smul_mem_degree (hf : f ∈ A d) {n k p : ℕ} (hp : n + k = p) {x : M}
    (hx : x ∈ B ((n * d : ℕ) : ℤ)) : f ^ k • x ∈ B ((p * d : ℕ) : ℤ) :=
  smul_mem_degree A B (by omega) (SetLike.pow_mem_graded k hf) hx

/-- **A fraction with homogeneous numerator of degree `n * d` and denominator `f ^ n` lies in the
degree-zero part of the localization**, for `f` homogeneous of degree `d`. -/
public theorem mk_mem_degreeZeroLocalization_of_degree (hf : f ∈ A d) (n : ℕ) (x : M)
    (hx : x ∈ B ((n * d : ℕ) : ℤ)) :
    LocalizedModule.mk (S := Submonoid.powers f) x ⟨f ^ n, by exact ⟨n, rfl⟩⟩ ∈
      GradedModuleDegreeZeroLocalization A B f := by
  let := Module.compHom (R := Localization.Away f)
    (LocalizedModule.Away (R := R) f M)
    (algebraMap (HomogeneousLocalization.Away A f) (Localization.Away f))
  refine Submodule.subset_span ⟨d, n, hf, x, ?_, rfl⟩
  rwa [← natCast_mul_eq_nsmul]

/-- **Every element of the degree-zero part of the localization is a fraction** with homogeneous
numerator of degree `n * d` and denominator `f ^ n`, for `f` homogeneous of degree `d`. -/
public theorem degreeZeroLocalization_exists_fraction_of_degree (hf : f ∈ A d)
    (z : GradedModuleDegreeZeroLocalization A B f) :
    ∃ (n : ℕ) (x : M), x ∈ B ((n * d : ℕ) : ℤ) ∧
      (z : LocalizedModule.Away f M) =
        LocalizedModule.mk (S := Submonoid.powers f) x ⟨f ^ n, by exact ⟨n, rfl⟩⟩ := by
  let := Module.compHom (R := Localization.Away f)
    (LocalizedModule.Away (R := R) f M)
    (algebraMap (HomogeneousLocalization.Away A f) (Localization.Away f))
  by_cases hf0 : f = 0
  · have : Subsingleton (LocalizedModule.Away (R := R) f M) :=
      LocalizedModule.subsingleton_iff.mpr (fun m => ⟨f, ⟨1, pow_one f⟩, by simp [hf0]⟩)
    exact ⟨0, 0, zero_mem _, Subsingleton.elim _ _⟩
  rcases z with ⟨z, hz⟩
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨c, n, hfc, x, hx, rfl⟩ := hz
      have hcd : c = d := DirectSum.degree_eq_of_mem_mem A hfc hf hf0
      subst hcd
      refine ⟨n, x, ?_, rfl⟩
      rwa [natCast_mul_eq_nsmul]
  | zero => exact ⟨0, 0, zero_mem _, (LocalizedModule.zero_mk _).symm⟩
  | add z w hz hw ihz ihw =>
      obtain ⟨n, x, hx, rfl⟩ := ihz
      obtain ⟨m, y, hy, rfl⟩ := ihw
      refine ⟨n + m, f ^ m • x + f ^ n • y,
        add_mem (pow_smul_mem_degree A B hf rfl hx)
          (pow_smul_mem_degree A B hf (Nat.add_comm m n) hy), ?_⟩
      change LocalizedModule.mk (S := Submonoid.powers f) x _ +
        LocalizedModule.mk (S := Submonoid.powers f) y _ = _
      rw [LocalizedModule.mk_add_mk]
      congr 1
      exact Subtype.ext (pow_add f n m).symm
  | smul a z hz ih =>
      obtain ⟨n, x, hx, rfl⟩ := ih
      obtain ⟨m, r, hr, rfl⟩ := HomogeneousLocalization.Away.mk_surjective A hf a
      refine ⟨m + n, r • x,
        smul_mem_degree A B rfl hr hx, ?_⟩
      change HomogeneousLocalization.val (HomogeneousLocalization.Away.mk A hf m r hr) •
        LocalizedModule.mk (S := Submonoid.powers f) x _ = _
      rw [HomogeneousLocalization.Away.val_mk, LocalizedModule.mk_smul_mk]
      congr 1
      exact Subtype.ext (pow_add f m n).symm

omit [AddSubgroupClass τ M] [Decomposition B] in
/-- **Two homogeneous representatives of the same fraction have the same numerator value**, for a
family of additive maps compatible with multiplying numerator and denominator by `f`. This is the
representative-independence that makes the lift below a definition rather than a choice. -/
private theorem fraction_values_eq_of_degree (e : ℕ → M →+ N)
    (he : ∀ (n k : ℕ) (x : M), x ∈ B ((n * d : ℕ) : ℤ) → e (n + k) (f ^ k • x) = e n x)
    (n m : ℕ) (x y : M) (hx : x ∈ B ((n * d : ℕ) : ℤ)) (hy : y ∈ B ((m * d : ℕ) : ℤ))
    (h : LocalizedModule.mk (S := Submonoid.powers f) x ⟨f ^ n, by exact ⟨n, rfl⟩⟩ =
      LocalizedModule.mk (S := Submonoid.powers f) y ⟨f ^ m, by exact ⟨m, rfl⟩⟩) :
    e n x = e m y := by
  obtain ⟨⟨u, k, rfl⟩, hu⟩ := LocalizedModule.mk_eq.mp h
  change f ^ k • f ^ m • x = f ^ k • f ^ n • y at hu
  rw [smul_smul, smul_smul, ← pow_add, ← pow_add] at hu
  rw [← he n (k + m) x hx, ← he m (k + n) y hy, show n + (k + m) = m + (k + n) by omega, hu]

/-- The value of a family of additive maps on a degree-zero fraction, read off a representative
`x / f ^ n` with `x` homogeneous of degree `n * d` as the `n`-th member of the family at `x`. It
is independent of the representative as soon as the family is compatible with multiplication by
`f`, which is `Stacks.SheafOfModules.fractionValueOfDegree_eq`. -/
public noncomputable def fractionValueOfDegree (hf : f ∈ A d) (e : ℕ → M →+ N)
    (z : GradedModuleDegreeZeroLocalization A B f) : N :=
  let h := degreeZeroLocalization_exists_fraction_of_degree A B hf z
  e h.choose h.choose_spec.choose

/-- The value of a compatible family on a fraction is the value of the family on the numerator,
for any representative. -/
private theorem fractionValueOfDegree_eq (hf : f ∈ A d) (e : ℕ → M →+ N)
    (he : ∀ (n k : ℕ) (x : M), x ∈ B ((n * d : ℕ) : ℤ) → e (n + k) (f ^ k • x) = e n x)
    (z : GradedModuleDegreeZeroLocalization A B f)
    (n : ℕ) (x : M) (hx : x ∈ B ((n * d : ℕ) : ℤ))
    (hz : (z : LocalizedModule.Away f M) =
      LocalizedModule.mk (S := Submonoid.powers f) x ⟨f ^ n, by exact ⟨n, rfl⟩⟩) :
    fractionValueOfDegree A B hf e z = e n x := by
  let h := degreeZeroLocalization_exists_fraction_of_degree A B hf z
  exact fraction_values_eq_of_degree B e he _ _ _ _ h.choose_spec.choose_spec.1 hx
    (h.choose_spec.choose_spec.2.symm.trans hz)

/-- **A family of additive maps compatible with multiplying numerator and denominator by `f` lifts
to the degree-zero part of the localization**, for `f` homogeneous of degree `d`. The family is
indexed by the exponent of the denominator, so its `n`-th member is used on numerators of degree
`n * d`. -/
public noncomputable def degreeZeroLocalizationLiftOfDegree (hf : f ∈ A d) (e : ℕ → M →+ N)
    (he : ∀ (n k : ℕ) (x : M), x ∈ B ((n * d : ℕ) : ℤ) → e (n + k) (f ^ k • x) = e n x) :
    GradedModuleDegreeZeroLocalization A B f →+ N where
  toFun := fractionValueOfDegree A B hf e
  map_zero' := by
    rw [fractionValueOfDegree_eq A B hf e he 0 0 0 (zero_mem _) (by simp)]
    exact map_zero _
  map_add' z w := by
    obtain ⟨n, x, hx, hz⟩ := degreeZeroLocalization_exists_fraction_of_degree A B hf z
    obtain ⟨m, y, hy, hw⟩ := degreeZeroLocalization_exists_fraction_of_degree A B hf w
    have hmx : f ^ m • x ∈ B (((n + m) * d : ℕ) : ℤ) := pow_smul_mem_degree A B hf rfl hx
    have hny : f ^ n • y ∈ B (((n + m) * d : ℕ) : ℤ) :=
      pow_smul_mem_degree A B hf (Nat.add_comm m n) hy
    have hzw : ((z + w : GradedModuleDegreeZeroLocalization A B f) :
        LocalizedModule.Away f M) =
        LocalizedModule.mk (S := Submonoid.powers f) (f ^ m • x + f ^ n • y)
          ⟨f ^ (n + m), by exact ⟨n + m, rfl⟩⟩ := by
      change (z : LocalizedModule.Away f M) + (w : LocalizedModule.Away f M) = _
      rw [hz, hw, LocalizedModule.mk_add_mk]
      congr 1
      exact Subtype.ext (pow_add f n m).symm
    rw [fractionValueOfDegree_eq A B hf e he (z + w) (n + m) _ (add_mem hmx hny) hzw,
      fractionValueOfDegree_eq A B hf e he z n x hx hz,
      fractionValueOfDegree_eq A B hf e he w m y hy hw, map_add, he n m x hx]
    congr 1
    simpa [Nat.add_comm] using he m n y hy

/-- **The value of a lifted family on a fraction**: the lift sends a fraction with homogeneous
numerator `x` of degree `n * d` and denominator `f ^ n` to the `n`-th member of the family
evaluated at `x`. -/
public theorem degreeZeroLocalizationLiftOfDegree_fraction (hf : f ∈ A d) (e : ℕ → M →+ N)
    (he : ∀ (n k : ℕ) (x : M), x ∈ B ((n * d : ℕ) : ℤ) → e (n + k) (f ^ k • x) = e n x)
    (z : GradedModuleDegreeZeroLocalization A B f)
    (n : ℕ) (x : M) (hx : x ∈ B ((n * d : ℕ) : ℤ))
    (hz : (z : LocalizedModule.Away f M) =
      LocalizedModule.mk (S := Submonoid.powers f) x ⟨f ^ n, by exact ⟨n, rfl⟩⟩) :
    degreeZeroLocalizationLiftOfDegree A B hf e he z = e n x :=
  fractionValueOfDegree_eq A B hf e he z n x hx hz

/-- **A lifted family is semilinear** over a ring map `φ` out of the degree-zero part of the
localized ring, as soon as acting by a homogeneous numerator of degree `m * d` is multiplication
by the value of `φ` on the corresponding fraction. -/
public theorem degreeZeroLocalizationLiftOfDegree_smul (hf : f ∈ A d) (e : ℕ → M →+ N)
    (he : ∀ (n k : ℕ) (x : M), x ∈ B ((n * d : ℕ) : ℤ) → e (n + k) (f ^ k • x) = e n x)
    {K : Type*} [CommRing K] [Module K N]
    (φ : HomogeneousLocalization.Away A f →+* K)
    (hφ : ∀ (m n : ℕ) (r : R) (x : M) (hr : r ∈ A (m • d))
      (_hx : x ∈ B ((n * d : ℕ) : ℤ)), e (m + n) (r • x) =
        φ (HomogeneousLocalization.Away.mk A hf m r hr) • e n x)
    (a : HomogeneousLocalization.Away A f) (z : GradedModuleDegreeZeroLocalization A B f) :
    degreeZeroLocalizationLiftOfDegree A B hf e he (a • z) =
      φ a • degreeZeroLocalizationLiftOfDegree A B hf e he z := by
  obtain ⟨n, x, hx, hz⟩ := degreeZeroLocalization_exists_fraction_of_degree A B hf z
  obtain ⟨m, r, hr, rfl⟩ := HomogeneousLocalization.Away.mk_surjective A hf a
  have hrx : r • x ∈ B (((m + n) * d : ℕ) : ℤ) :=
    smul_mem_degree A B rfl hr hx
  have haz : ((HomogeneousLocalization.Away.mk A hf m r hr • z :
      GradedModuleDegreeZeroLocalization A B f) : LocalizedModule.Away f M) =
      LocalizedModule.mk (S := Submonoid.powers f) (r • x)
        ⟨f ^ (m + n), by exact ⟨m + n, rfl⟩⟩ := by
    change HomogeneousLocalization.val (HomogeneousLocalization.Away.mk A hf m r hr) •
      (z : LocalizedModule.Away f M) = _
    rw [hz, HomogeneousLocalization.Away.val_mk, LocalizedModule.mk_smul_mk]
    congr 1
    exact Subtype.ext (pow_add f m n).symm
  rw [degreeZeroLocalizationLiftOfDegree_fraction A B hf e he _ (m + n) (r • x) hrx haz,
    degreeZeroLocalizationLiftOfDegree_fraction A B hf e he z n x hx hz]
  exact hφ m n r x hr hx

/-- **A fraction of the degree-zero localization vanishes exactly when a power of `f` kills its
numerator.** No hypothesis on the degree of `f` is needed; what is new here, compared with the
same criterion for the ambient localized module, is that vanishing is tested in the degree-zero
part. -/
public theorem eq_zero_iff_exists_pow_smul_eq_zero
    (z : GradedModuleDegreeZeroLocalization A B f) (n : ℕ) (x : M)
    (hz : (z : LocalizedModule.Away f M) =
      LocalizedModule.mk (S := Submonoid.powers f) x ⟨f ^ n, by exact ⟨n, rfl⟩⟩) :
    z = 0 ↔ ∃ k : ℕ, f ^ k • x = 0 := by
  let := Module.compHom (R := Localization.Away f)
    (LocalizedModule.Away (R := R) f M)
    (algebraMap (HomogeneousLocalization.Away A f) (Localization.Away f))
  rw [← Submodule.coe_eq_zero, hz, ← LocalizedModule.zero_mk (1 : Submonoid.powers f),
    LocalizedModule.mk_eq]
  constructor
  · rintro ⟨⟨u, k, rfl⟩, hu⟩
    exact ⟨k, by simpa [Submonoid.smul_def] using hu⟩
  · rintro ⟨k, hk⟩
    exact ⟨⟨f ^ k, ⟨k, rfl⟩⟩, by simpa [Submonoid.smul_def] using hk⟩

end ModuleFractions

/-! ### Fractions of a graded ring -/

section RingFractions

variable {R : Type u} {σ : Type w} [CommRing R] [SetLike σ R] [AddSubgroupClass σ R]
  (A : ℕ → σ) [GradedRing A] {f : R} {d : ℕ}
  {K : Type*} [CommRing K]

omit [AddSubgroupClass σ R] [GradedRing A] in
/-- **Two homogeneous representatives of the same fraction have the same numerator value**, in the
ring-valued case. -/
private theorem ringFraction_values_eq_of_degree (e : ℕ → R →+ K)
    (he : ∀ (n k : ℕ) (x : R), x ∈ A (n * d) → e (n + k) (f ^ k * x) = e n x)
    (n m : ℕ) (x y : R) (hx : x ∈ A (n * d)) (hy : y ∈ A (m * d))
    (h : Localization.mk x (⟨f ^ n, by exact ⟨n, rfl⟩⟩ : Submonoid.powers f) =
      Localization.mk y (⟨f ^ m, by exact ⟨m, rfl⟩⟩ : Submonoid.powers f)) :
    e n x = e m y := by
  obtain ⟨⟨u, k, rfl⟩, hu⟩ := Localization.r_iff_exists.mp (Localization.mk_eq_mk_iff.mp h)
  change f ^ k * (f ^ m * x) = f ^ k * (f ^ n * y) at hu
  rw [← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add] at hu
  rw [← he n (k + m) x hx, ← he m (k + n) y hy, show n + (k + m) = m + (k + n) by omega, hu]

/-- The value of a family of additive maps on a homogeneous fraction of the degree-zero localized
ring, read off a representative `x / f ^ n` with `x` homogeneous of degree `n * d`. It is
independent of the representative as soon as the family is compatible with multiplication by `f`;
`Stacks.SheafOfModules.homogeneousLocalizationLiftOfDegree` is the packaging of that. -/
public noncomputable def ringFractionValueOfDegree (hf : f ∈ A d) (e : ℕ → R →+ K)
    (z : HomogeneousLocalization.Away A f) : K :=
  let h := HomogeneousLocalization.Away.mk_surjective A hf z
  e h.choose h.choose_spec.choose

/-- The value of a compatible family on a homogeneous fraction is the value of the family on the
numerator, for any representative. -/
private theorem ringFractionValueOfDegree_eq (hf : f ∈ A d) (e : ℕ → R →+ K)
    (he : ∀ (n k : ℕ) (x : R), x ∈ A (n * d) → e (n + k) (f ^ k * x) = e n x)
    (z : HomogeneousLocalization.Away A f)
    (n : ℕ) (x : R) (hx : x ∈ A (n * d))
    (hz : HomogeneousLocalization.val z =
      Localization.mk x (⟨f ^ n, by exact ⟨n, rfl⟩⟩ : Submonoid.powers f)) :
    ringFractionValueOfDegree A hf e z = e n x := by
  let h := HomogeneousLocalization.Away.mk_surjective A hf z
  have hh := congrArg HomogeneousLocalization.val h.choose_spec.choose_spec.choose_spec
  rw [HomogeneousLocalization.Away.val_mk] at hh
  exact ringFraction_values_eq_of_degree A e he _ _ _ _
    (by simpa [smul_eq_mul] using h.choose_spec.choose_spec.choose) hx (hh.trans hz)

/-- **A family of additive maps compatible with multiplying numerator and denominator by `f`, with
the unit and the multiplication of numerators, lifts to a ring map out of the degree-zero
localized ring** `HomogeneousLocalization.Away A f`, for `f` homogeneous of degree `d`. The family
is indexed by the exponent of the denominator, so its `n`-th member is used on numerators of
degree `n * d`. -/
public noncomputable def homogeneousLocalizationLiftOfDegree (hf : f ∈ A d) (e : ℕ → R →+ K)
    (he : ∀ (n k : ℕ) (x : R), x ∈ A (n * d) → e (n + k) (f ^ k * x) = e n x)
    (h1 : e 0 1 = 1)
    (hmul : ∀ (n m : ℕ) (x y : R), x ∈ A (n * d) → y ∈ A (m * d) →
      e (n + m) (x * y) = e n x * e m y) :
    HomogeneousLocalization.Away A f →+* K where
  toFun := ringFractionValueOfDegree A hf e
  map_zero' := by
    rw [ringFractionValueOfDegree_eq A hf e he 0 0 0 (zero_mem _) (by simp [Localization.mk_zero])]
    exact map_zero _
  map_one' := by
    rw [ringFractionValueOfDegree_eq A hf e he 1 0 1 (one_mem_degree A) (by simp)]
    exact h1
  map_add' z w := by
    obtain ⟨n, x, hx, rfl⟩ := HomogeneousLocalization.Away.mk_surjective A hf z
    obtain ⟨m, y, hy, rfl⟩ := HomogeneousLocalization.Away.mk_surjective A hf w
    have hx' : x ∈ A (n * d) := by simpa [smul_eq_mul] using hx
    have hy' : y ∈ A (m * d) := by simpa [smul_eq_mul] using hy
    have hnx : f ^ m * x ∈ A ((n + m) * d) :=
      SetLike.mul_mem_graded_mul (Nat.add_comm m n) (SetLike.pow_mem_graded m hf) hx'
    have hmy : f ^ n * y ∈ A ((n + m) * d) :=
      SetLike.mul_mem_graded_mul rfl (SetLike.pow_mem_graded n hf) hy'
    have hv : HomogeneousLocalization.val
        (HomogeneousLocalization.Away.mk A hf n x hx +
          HomogeneousLocalization.Away.mk A hf m y hy) =
        Localization.mk (f ^ m * x + f ^ n * y)
          (⟨f ^ (n + m), by exact ⟨n + m, rfl⟩⟩ : Submonoid.powers f) := by
      rw [HomogeneousLocalization.val_add, HomogeneousLocalization.Away.val_mk,
        HomogeneousLocalization.Away.val_mk, Localization.add_mk]
      congr 1
      · exact add_comm _ _
      · exact Subtype.ext (pow_add f n m).symm
    rw [ringFractionValueOfDegree_eq A hf e he _ (n + m) _ (add_mem hnx hmy) hv,
      ringFractionValueOfDegree_eq A hf e he _ n x hx' (HomogeneousLocalization.Away.val_mk ..),
      ringFractionValueOfDegree_eq A hf e he _ m y hy' (HomogeneousLocalization.Away.val_mk ..),
      map_add, he n m x hx']
    congr 1
    simpa [Nat.add_comm] using he m n y hy'
  map_mul' z w := by
    obtain ⟨n, x, hx, rfl⟩ := HomogeneousLocalization.Away.mk_surjective A hf z
    obtain ⟨m, y, hy, rfl⟩ := HomogeneousLocalization.Away.mk_surjective A hf w
    have hx' : x ∈ A (n * d) := by simpa [smul_eq_mul] using hx
    have hy' : y ∈ A (m * d) := by simpa [smul_eq_mul] using hy
    have hv : HomogeneousLocalization.val
        (HomogeneousLocalization.Away.mk A hf n x hx *
          HomogeneousLocalization.Away.mk A hf m y hy) =
        Localization.mk (x * y)
          (⟨f ^ (n + m), by exact ⟨n + m, rfl⟩⟩ : Submonoid.powers f) := by
      rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.Away.val_mk,
        HomogeneousLocalization.Away.val_mk, Localization.mk_mul]
      congr 1
      exact Subtype.ext (pow_add f n m).symm
    rw [ringFractionValueOfDegree_eq A hf e he _ (n + m) _
        (SetLike.mul_mem_graded_mul rfl hx' hy') hv,
      ringFractionValueOfDegree_eq A hf e he _ n x hx' (HomogeneousLocalization.Away.val_mk ..),
      ringFractionValueOfDegree_eq A hf e he _ m y hy' (HomogeneousLocalization.Away.val_mk ..)]
    exact hmul n m x y hx' hy'

/-- **The value of a lifted family on a homogeneous fraction**: the ring map sends a fraction with
homogeneous numerator `x` of degree `n * d` and denominator `f ^ n` to the `n`-th member of the
family evaluated at `x`. -/
public theorem homogeneousLocalizationLiftOfDegree_fraction (hf : f ∈ A d) (e : ℕ → R →+ K)
    (he : ∀ (n k : ℕ) (x : R), x ∈ A (n * d) → e (n + k) (f ^ k * x) = e n x)
    (h1 : e 0 1 = 1)
    (hmul : ∀ (n m : ℕ) (x y : R), x ∈ A (n * d) → y ∈ A (m * d) →
      e (n + m) (x * y) = e n x * e m y)
    (z : HomogeneousLocalization.Away A f)
    (n : ℕ) (x : R) (hx : x ∈ A (n * d))
    (hz : HomogeneousLocalization.val z =
      Localization.mk x (⟨f ^ n, by exact ⟨n, rfl⟩⟩ : Submonoid.powers f)) :
    homogeneousLocalizationLiftOfDegree A hf e he h1 hmul z = e n x :=
  ringFractionValueOfDegree_eq A hf e he z n x hx hz

/-- The value of a lifted family on the fraction `x / f ^ n` named by
`HomogeneousLocalization.Away.mk`. -/
public theorem homogeneousLocalizationLiftOfDegree_mk (hf : f ∈ A d) (e : ℕ → R →+ K)
    (he : ∀ (n k : ℕ) (x : R), x ∈ A (n * d) → e (n + k) (f ^ k * x) = e n x)
    (h1 : e 0 1 = 1)
    (hmul : ∀ (n m : ℕ) (x y : R), x ∈ A (n * d) → y ∈ A (m * d) →
      e (n + m) (x * y) = e n x * e m y)
    (n : ℕ) (x : R) (hx : x ∈ A (n • d)) :
    homogeneousLocalizationLiftOfDegree A hf e he h1 hmul
        (HomogeneousLocalization.Away.mk A hf n x hx) = e n x :=
  homogeneousLocalizationLiftOfDegree_fraction A hf e he h1 hmul _ n x
    hx (HomogeneousLocalization.Away.val_mk ..)

/-- **A lifted ring map is injective** as soon as a numerator annihilated by its member of the
family is annihilated by a power of `f`. Together with
`Stacks.SheafOfModules.homogeneousLocalizationLiftOfDegree_surjective` this reduces bijectivity of
a comparison map at an arbitrary degree to the two statements about numerators, which are the ones
that have geometric content. -/
public theorem homogeneousLocalizationLiftOfDegree_injective (hf : f ∈ A d) (e : ℕ → R →+ K)
    (he : ∀ (n k : ℕ) (x : R), x ∈ A (n * d) → e (n + k) (f ^ k * x) = e n x)
    (h1 : e 0 1 = 1)
    (hmul : ∀ (n m : ℕ) (x y : R), x ∈ A (n * d) → y ∈ A (m * d) →
      e (n + m) (x * y) = e n x * e m y)
    (hker : ∀ (n : ℕ) (x : R), x ∈ A (n * d) → e n x = 0 → ∃ k : ℕ, f ^ k * x = 0) :
    Function.Injective (homogeneousLocalizationLiftOfDegree A hf e he h1 hmul) := by
  intro z w hzw
  obtain ⟨n, x, hx, rfl⟩ := HomogeneousLocalization.Away.mk_surjective A hf z
  obtain ⟨m, y, hy, rfl⟩ := HomogeneousLocalization.Away.mk_surjective A hf w
  rw [homogeneousLocalizationLiftOfDegree_mk A hf e he h1 hmul n x hx,
    homogeneousLocalizationLiftOfDegree_mk A hf e he h1 hmul m y hy] at hzw
  have hfx : f ^ m * x ∈ A ((n + m) * d) :=
    SetLike.mul_mem_graded_mul (Nat.add_comm m n) (SetLike.pow_mem_graded m hf) hx
  have hfy : f ^ n * y ∈ A ((n + m) * d) :=
    SetLike.mul_mem_graded_mul rfl (SetLike.pow_mem_graded n hf) hy
  have hvy : e (n + m) (f ^ n * y) = e m y := by
    simpa [Nat.add_comm] using he m n y hy
  have hzero : e (n + m) (f ^ m * x - f ^ n * y) = 0 := by
    rw [map_sub, he n m x hx, hvy, hzw, sub_self]
  obtain ⟨k, hk⟩ := hker (n + m) _ (sub_mem hfx hfy) hzero
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨⟨f ^ k, ⟨k, rfl⟩⟩, eq_of_sub_eq_zero ?_⟩
  rwa [← mul_sub]

/-- **A lifted ring map is surjective** as soon as every element of the target is the value of the
family on some numerator. -/
public theorem homogeneousLocalizationLiftOfDegree_surjective (hf : f ∈ A d) (e : ℕ → R →+ K)
    (he : ∀ (n k : ℕ) (x : R), x ∈ A (n * d) → e (n + k) (f ^ k * x) = e n x)
    (h1 : e 0 1 = 1)
    (hmul : ∀ (n m : ℕ) (x y : R), x ∈ A (n * d) → y ∈ A (m * d) →
      e (n + m) (x * y) = e n x * e m y)
    (hsurj : ∀ y : K, ∃ (n : ℕ) (x : R), x ∈ A (n * d) ∧ e n x = y) :
    Function.Surjective (homogeneousLocalizationLiftOfDegree A hf e he h1 hmul) := fun y => by
  obtain ⟨n, x, hx, hxy⟩ := hsurj y
  exact ⟨HomogeneousLocalization.Away.mk A hf n x hx,
    (homogeneousLocalizationLiftOfDegree_mk A hf e he h1 hmul n x _).trans hxy⟩

end RingFractions

end Stacks.SheafOfModules

end
