module

public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FittingProductAll
public import StacksFrontier.AlgebraicGeometry.DivisorSum.LocallyFinite
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Difference
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierSimultaneous
public import StacksFrontier.RingTheory.Fitting.GlobalEquations

/-!
# The divisors `D_j` of a module with effective Cartier Fitting ideals

Stacks tag 0ESU blows a scheme up so that every Fitting ideal `Fit_k(ℱ)` of a module becomes an
effective Cartier divisor `E_k`, and then asserts that the `E_k` are the locally finite sums

```
E_k = D_{k+1} + 2 D_{k+2} + 3 D_{k+3} + ⋯
```

of effective Cartier divisors `D_j`. `StacksFrontier.AlgebraicGeometry.DivisorSum.LocallyFinite`
supplies the sum and its cancellation — so the `D_j` are unique once they exist — but nothing
produced them. This file produces them.

## Main results

* `AlgebraicGeometry.exists_affineOpen_forall_fittingIdeal_eq_prod`: around every point there is
  an affine open carrying local equations `e_1, …, e_N` of the divisors, with
  `Fit_k(ℱ) = ∏_{j > k} (e_j)^{j-k}`. This is the scheme-level form of
  `Stacks.FittingFiltration.exists_equations_of_forall_fittingIdeal_eq_span_singleton`.
* `AlgebraicGeometry.fittingIdeal_mul_fittingIdeal_le`: the Fitting ideal *sheaves* are
  log-concave, `Fit_k · Fit_{k+2} ≤ Fit_{k+1}^2`.
* `AlgebraicGeometry.exists_divisors_locallyFiniteSum_eq_fittingIdeal`: **the divisors `D_j`.**
  Effective Cartier divisors `D_j`, only finitely many of them meeting any affine open, with
  `Fit_k(ℱ) = ∑_{j > k} (j - k) D_j` as a locally finite sum.
* `AlgebraicGeometry.exists_isAdmissibleBlowup_divisors`: the two halves joined — for a finitely
  presented module vanishing on an open `U` there is a `U`-admissible blowup on which the
  divisors `D_j` exist.

## Implementation notes

**Where the divisors come from.** Not from a colon of ideal sheaves, but from tag 02ON,
`AlgebraicGeometry.exists_isEffectiveCartierDivisor_mul_eq_of_le`: an effective Cartier divisor
contained in another is the sum of the other and a third. Applying it twice gives the `D_j`:

* once to `Fit_k ≤ Fit_{k+1}`, which produces the *tail sums* `G_{k+1} = D_{k+1} + D_{k+2} + ⋯`
  with `Fit_k = Fit_{k+1} · G_{k+1}`;
* once to `G_{k+1} ≤ G_{k+2}`, which produces `D_{k+1}` itself with `G_{k+1} = G_{k+2} · D_{k+1}`.

The first inclusion is monotonicity of the Fitting ideals, tag 07Z7. The second is the only real
input: it is log-concavity, `Fit_k · Fit_{k+2} ≤ Fit_{k+1}^2`, which is checked on the affine
opens of the first main result, where the local equations make it an identity. Both applications
are existence statements, so the family `D` is obtained by choice; it is nonetheless canonical,
being pinned down by the cancellation
`Stacks.Divisors.eq_of_mul_eq_mul_of_isEffectiveCartierDivisor`.

**Indexing.** `D j` here is `D_{j+1}` of the source, so that the family is indexed by `ℕ` with no
unused zeroth member, and the multiplicity of `D j` in `E_k` is `(j + 1) - k` in truncated
subtraction — which is `0` exactly when `j + 1 ≤ k`, as the source's sum over `j > k` requires.

## References

* [Stacks Project, Tag 0ESU](https://stacks.math.columbia.edu/tag/0ESU)
* [Stacks Project, Tag 02ON](https://stacks.math.columbia.edu/tag/02ON)
* [Stacks Project, Tag 07Z7](https://stacks.math.columbia.edu/tag/07Z7)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Divisors Stacks.FittingFiltration

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (F : X.Modules)

/-- The sections of a product of quasi-coherent ideal sheaves on an affine open are the product
of their sections. -/
theorem ideal_mul_apply (I J : X.IdealSheafData) (W : X.affineOpens) :
    (I * J).ideal W = I.ideal W * J.ideal W := rfl

/-- The sections of a power of a quasi-coherent ideal sheaf on an affine open are the power of
its sections. -/
theorem ideal_pow_apply (I : X.IdealSheafData) (n : ℕ) (W : X.affineOpens) :
    (I ^ n).ideal W = I.ideal W ^ n := rfl

/-- If a product of ideal sheaves and one factor are the unit ideal on an affine open, so is the
other factor. -/
private theorem ideal_eq_top_of_mul_eq {I J K : X.IdealSheafData} (W : X.affineOpens)
    (h : K = I * J) (hI : I.ideal W = ⊤) (hK : K.ideal W = ⊤) : J.ideal W = ⊤ := by
  rw [← hK, h, ideal_mul_apply, hI, Ideal.top_mul]

/-! ### The local equations on an affine open -/

/-- **The local equations of the divisors `D_j`, on an affine open.** If every Fitting ideal of a
finitely presented module is an effective Cartier divisor, then around every point there is an
affine open `V` and elements `e_1, …, e_N` of `Γ(X, V)`, nonzerodivisors and units past `N`, with

```
Fit_k(ℱ)(V) = ∏_{j > k} (e_j)^{j - k}
```

for every `k`. The bound `N` is found first, on any affine open, as the index past which the
Fitting ideals are the unit ideal; the equations are then found on a smaller affine open where
every Fitting ideal of index below `N` is principal on a nonzerodivisor, by dividing. -/
theorem exists_affineOpen_forall_fittingIdeal_eq_prod [F.IsFinitePresentation]
    (hcart : ∀ k : ℕ, IsEffectiveCartierDivisor (fittingIdeal F (k : ℤ))) (x : X) :
    ∃ V : X.affineOpens, x ∈ (V.1 : Set X) ∧ ∃ (N : ℕ) (e : ℕ → Γ(X, V.1)),
      (∀ j, e j ∈ nonZeroDivisors Γ(X, V.1)) ∧
      (∀ j, N < j → IsUnit (e j)) ∧
      (∀ k : ℕ, ∃ g ∈ nonZeroDivisors Γ(X, V.1),
        (fittingIdeal F (k : ℤ)).ideal V = Ideal.span {g}) ∧
      (∀ k : ℕ, (fittingIdeal F (k : ℤ)).ideal V =
        ∏ j ∈ Finset.Icc (k + 1) N, Ideal.span {e j} ^ (j - k)) := by
  classical
  have hft : F.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F
  have hqc : F.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation F
  obtain ⟨U, hxU⟩ := exists_affineOpens_mem x
  obtain ⟨N, hN⟩ := exists_forall_fittingIdeal_ideal_eq_top F U
  obtain ⟨V, hxV, hVU, f, hf⟩ :=
    exists_affineOpen_le_forall_ideal_eq_span (Finset.range N)
      (fun k : ℕ => fittingIdeal F (k : ℤ)) (fun k _ => hcart k) U x hxU
  obtain ⟨g, hgdef⟩ : ∃ g : ℕ → Γ(X, V.1), ∀ k, g k = if k < N then f k else 1 :=
    ⟨_, fun _ => rfl⟩
  have htopV : ∀ k : ℕ, N ≤ k → (fittingIdeal F (k : ℤ)).ideal V = ⊤ := by
    intro k hk
    rw [← Scheme.IdealSheafData.map_ideal (fittingIdeal F (k : ℤ)) hVU, hN k hk, Ideal.map_top]
  have hgen : ∀ k : ℕ, (fittingIdeal F (k : ℤ)).ideal V = Ideal.span {g k} := by
    intro k
    rw [hgdef k]
    split_ifs with hk
    · exact (hf k (Finset.mem_range.mpr hk)).2
    · rw [htopV k (not_lt.mp hk), Ideal.span_singleton_one]
  have hgmem : ∀ k, g k ∈ nonZeroDivisors Γ(X, V.1) := by
    intro k
    rw [hgdef k]
    split_ifs with hk
    · exact isRegular_iff_mem_nonZeroDivisors.mp (hf k (Finset.mem_range.mpr hk)).1
    · exact one_mem _
  have hgunit : ∀ k, N ≤ k → IsUnit (g k) := by
    intro k hk
    rw [hgdef k, if_neg (not_lt.mpr hk)]
    exact isUnit_one
  have hfin : Module.Finite Γ(X, V.1) Γ(F, V.1) := moduleFinite_sections_on_affine F V.1 V.2
  have hfitM : ∀ k : ℕ, _root_.fittingIdeal (M := Γ(F, V.1)) (k : ℤ) = Ideal.span {g k} :=
    fun k => (fittingIdeal_ideal F (k : ℤ) V).symm.trans (hgen k)
  obtain ⟨e, hemem, heunit, heprod⟩ :=
    exists_equations_of_forall_fittingIdeal_eq_span_singleton
      (R := Γ(X, V.1)) (M := Γ(F, V.1)) N g hgmem hfitM hgunit
  exact ⟨V, hxV, N, e, hemem, heunit, fun k => ⟨g k, hgmem k, hgen k⟩,
    fun k => (fittingIdeal_ideal F (k : ℤ) V).trans (heprod k)⟩

/-! ### The Fitting ideal sheaves are log-concave -/

/-- **The Fitting ideal sheaves are log-concave.** If every Fitting ideal of a finitely presented
module is an effective Cartier divisor then

```
Fit_k(ℱ) · Fit_{k+2}(ℱ) ≤ Fit_{k+1}(ℱ)^2.
```

An inclusion of quasi-coherent ideal sheaves may be checked on a cover by affine opens, and the
cover of `AlgebraicGeometry.exists_affineOpen_forall_fittingIdeal_eq_prod` carries the hypothesis
of `Stacks.FittingFiltration.fittingIdeal_mul_fittingIdeal_le`. -/
theorem fittingIdeal_mul_fittingIdeal_le [F.IsFinitePresentation]
    (hcart : ∀ k : ℕ, IsEffectiveCartierDivisor (fittingIdeal F (k : ℤ))) (k : ℕ) :
    fittingIdeal F (k : ℤ) * fittingIdeal F ((k + 2 : ℕ) : ℤ) ≤
      fittingIdeal F ((k + 1 : ℕ) : ℤ) * fittingIdeal F ((k + 1 : ℕ) : ℤ) := by
  classical
  have hft : F.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F
  have hqc : F.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation F
  choose V hxV N e hemem heunit hprin heprod using
    exists_affineOpen_forall_fittingIdeal_eq_prod F hcart
  refine Scheme.IdealSheafData.le_of_iSup_eq_top V
    (eq_top_iff.mpr fun z _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hxV z⟩) fun y => ?_
  have hfin : Module.Finite Γ(X, (V y).1) Γ(F, (V y).1) :=
    moduleFinite_sections_on_affine F (V y).1 (V y).2
  have hfitM : ∀ j : ℕ, ∃ c ∈ nonZeroDivisors Γ(X, (V y).1),
      _root_.fittingIdeal (M := Γ(F, (V y).1)) (j : ℤ) = Ideal.span {c} := by
    intro j
    obtain ⟨c, hc, hcj⟩ := hprin y j
    exact ⟨c, hc, (fittingIdeal_ideal F (j : ℤ) (V y)).symm.trans hcj⟩
  simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
  rw [fittingIdeal_ideal F (k : ℤ) (V y), fittingIdeal_ideal F ((k + 2 : ℕ) : ℤ) (V y),
    fittingIdeal_ideal F ((k + 1 : ℕ) : ℤ) (V y)]
  exact Stacks.FittingFiltration.fittingIdeal_mul_fittingIdeal_le (M := Γ(F, (V y).1)) hfitM k

/-! ### The divisors -/

/-- **The divisors `D_j` of Stacks tag 0ESU.** If every Fitting ideal of a finitely presented
module `ℱ` is an effective Cartier divisor, then there are effective Cartier divisors `D_j`, only
finitely many of which meet any affine open, with

```
Fit_k(ℱ) = D_{k+1} + 2 D_{k+2} + 3 D_{k+3} + ⋯
```

a locally finite sum, for every `k ≥ 0`. In the indexing here `D j` is the source's `D_{j+1}` and
the multiplicity of `D j` in the `k`-th sum is `(j + 1) - k`, which vanishes for `j + 1 ≤ k`.

The last clause records the *local equations* of the divisors: around every point there is an
affine open on which `D_j` is cut out by a single element `e_{j+1}`, and on which every divisor
from the `N`-th on is empty. This is what identifies the filtrations of
`StacksFrontier.AlgebraicGeometry.DivisorSum.FittingFiltrations` with the local ones.

Tag 02ON turns the inclusion `Fit_k ≤ Fit_{k+1}` into a difference `G_{k+1}`, the tail sum
`D_{k+1} + D_{k+2} + ⋯`, and then the inclusion `G_{k+1} ≤ G_{k+2}` into `D_{k+1}`. The second
inclusion is log-concavity of the Fitting ideals, which the local equations supply. -/
theorem exists_divisors_locallyFiniteSum_eq_fittingIdeal [F.IsFinitePresentation]
    (hcart : ∀ k : ℕ, IsEffectiveCartierDivisor (fittingIdeal F (k : ℤ))) :
    ∃ D : ℕ → X.IdealSheafData,
      (∀ j, IsEffectiveCartierDivisor (D j)) ∧
      IsLocallyFiniteFamily D ∧
      (∀ k : ℕ, fittingIdeal F (k : ℤ) = locallyFiniteSum D fun j => (j + 1) - k) ∧
      (∀ x : X, ∃ V : X.affineOpens, x ∈ (V.1 : Set X) ∧
        ∃ (N : ℕ) (e : ℕ → Γ(X, V.1)),
          (∀ j, j + 1 ≤ N → (D j).ideal V = Ideal.span {e (j + 1)}) ∧
          (∀ j, N ≤ j → (D j).ideal V = ⊤) ∧
          (∀ j, e j ∈ nonZeroDivisors Γ(X, V.1)) ∧
          (∀ j, N < j → IsUnit (e j)) ∧
          (∀ k : ℕ, (fittingIdeal F (k : ℤ)).ideal V =
            ∏ j ∈ Finset.Icc (k + 1) N, Ideal.span {e j} ^ (j - k))) := by
  classical
  have hft : F.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F
  have hqc : F.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation F
  choose V hxV N e hemem heunit hprin heprod using
    exists_affineOpen_forall_fittingIdeal_eq_prod F hcart
  have hcover : ⨆ y : X, (V y).1 = ⊤ :=
    eq_top_iff.mpr fun z _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hxV z⟩
  -- Monotonicity of the Fitting ideals, tag 07Z7, at the level of ideal sheaves.
  have hmono : ∀ k : ℕ, fittingIdeal F (k : ℤ) ≤ fittingIdeal F ((k + 1 : ℕ) : ℤ) := by
    intro k
    refine Scheme.IdealSheafData.le_def.mpr fun U => ?_
    have hfin : Module.Finite Γ(X, U.1) Γ(F, U.1) := moduleFinite_sections_on_affine F U.1 U.2
    rw [fittingIdeal_ideal F (k : ℤ) U, fittingIdeal_ideal F ((k + 1 : ℕ) : ℤ) U]
    exact Stacks.Fitting.fittingIdeal_monotone (by exact_mod_cast Nat.le_succ k)
  -- The tail sums `G_{k+1} = D_{k+1} + D_{k+2} + ⋯`, by tag 02ON.
  choose G hGcart hGeq using fun k : ℕ =>
    exists_isEffectiveCartierDivisor_mul_eq_of_le (fittingIdeal F ((k + 1 : ℕ) : ℤ))
      (fittingIdeal F (k : ℤ)) (hcart (k + 1)) (hcart k) (hmono k)
  -- On each chart the tail sum is the tail product of the equations.
  have hGideal : ∀ (y : X) (k : ℕ),
      (G k).ideal (V y) = equationTail (e y) (N y) k := by
    intro y k
    obtain ⟨c, hc, hck⟩ := hprin y (k + 1)
    refine eq_of_span_singleton_mul_eq hc ?_
    rw [← hck, ← ideal_mul_apply, ← hGeq k, heprod y k,
      prod_pow_eq_mul_equationTail (e y) (N y) k, ← heprod y (k + 1), hck]
  -- The tail sums decrease, which is log-concavity.
  have hGmono : ∀ k : ℕ, G k ≤ G (k + 1) := by
    intro k
    refine Scheme.IdealSheafData.le_of_iSup_eq_top V hcover fun y => ?_
    rw [hGideal y k, hGideal y (k + 1)]
    rcases le_or_gt (k + 1) (N y) with hk | hk
    · rw [equationTail_succ (e y) hk]
      exact Ideal.mul_le_right
    · rw [equationTail_of_le (e y) (show N y ≤ k by omega),
        equationTail_of_le (e y) (show N y ≤ k + 1 by omega)]
  -- The divisors themselves, by tag 02ON again.
  choose D hDcart hDeq using fun k : ℕ =>
    exists_isEffectiveCartierDivisor_mul_eq_of_le (G (k + 1)) (G k) (hGcart (k + 1)) (hGcart k)
      (hGmono k)
  -- On each chart `D_{k+1}` is cut out by the equation `e_{k+1}`.
  have hDideal : ∀ (y : X) (k : ℕ), k + 1 ≤ N y →
      (D k).ideal (V y) = Ideal.span {e y (k + 1)} := by
    intro y k hk
    have hfmem : (∏ j ∈ Finset.Icc (k + 1 + 1) (N y), e y j) ∈
        nonZeroDivisors Γ(X, (V y).1) :=
      prod_mem_nonZeroDivisors_of_mem_nonZeroDivisors fun j _ => hemem y j
    have h1 : Ideal.span {∏ j ∈ Finset.Icc (k + 1 + 1) (N y), e y j}
        = (G (k + 1)).ideal (V y) := by
      rw [← equationTail_eq_span, hGideal y (k + 1)]
    refine eq_of_span_singleton_mul_eq hfmem ?_
    rw [h1, ← ideal_mul_apply, ← hDeq k, hGideal y k, equationTail_succ (e y) hk,
      hGideal y (k + 1), mul_comm]
  -- Off the chart's bound every divisor is empty.
  have hDtop : ∀ (y : X) (k : ℕ), N y ≤ k → (D k).ideal (V y) = ⊤ := by
    intro y k hk
    exact ideal_eq_top_of_mul_eq (V y) (hDeq k)
      (by rw [hGideal y (k + 1), equationTail_of_le (e y) (by omega)])
      (by rw [hGideal y k, equationTail_of_le (e y) hk])
  -- Local finiteness, on every affine open and not only on the charts.
  have hlf : IsLocallyFiniteFamily D := by
    intro U
    obtain ⟨M, hM⟩ := exists_forall_fittingIdeal_ideal_eq_top F U
    refine ⟨Finset.range M, fun i hi => ?_⟩
    have hiM : M ≤ i := by simpa using hi
    have h1 : (G i).ideal U = ⊤ :=
      ideal_eq_top_of_mul_eq U (hGeq i) (hM (i + 1) (by omega)) (hM i hiM)
    have h2 : (G (i + 1)).ideal U = ⊤ :=
      ideal_eq_top_of_mul_eq U (hGeq (i + 1)) (hM (i + 2) (by omega)) (hM (i + 1) (by omega))
    exact ideal_eq_top_of_mul_eq U (hDeq i) h2 h1
  refine ⟨D, hDcart, hlf, fun k => ?_,
    fun y => ⟨V y, hxV y, N y, e y, hDideal y, hDtop y, hemem y, heunit y, heprod y⟩⟩
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top V hcover fun y => ?_
  have htop : ∀ i ∉ Finset.range (N y), (D i).ideal (V y) = ⊤ :=
    fun i hi => hDtop y i (by simpa using hi)
  rw [locallyFiniteSum_ideal_eq_finsetProd hlf _ (V y) htop,
    Scheme.IdealSheafData.ideal_finsetProd_eq_prod, heprod y k]
  -- Reindex `i ↦ i + 1` and drop the factors of exponent zero.
  have hreindex : (∏ i ∈ Finset.range (N y), ((D i) ^ ((i + 1) - k)).ideal (V y))
      = ∏ j ∈ Finset.Icc 1 (N y), Ideal.span {e y j} ^ (j - k) := by
    rw [show Finset.Icc 1 (N y) = (Finset.range (N y)).image (· + 1) by
      ext z
      simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
      constructor
      · intro hz
        exact ⟨z - 1, by omega, by omega⟩
      · rintro ⟨w, hw, rfl⟩
        omega]
    rw [Finset.prod_image fun a _ b _ h => by simpa using h]
    refine Finset.prod_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    rw [ideal_pow_apply, hDideal y i (by omega)]
  rw [hreindex]
  refine Finset.prod_subset (fun j hj => ?_) fun j hj hj' => ?_
  · simp only [Finset.mem_Icc] at hj ⊢
    omega
  · simp only [Finset.mem_Icc] at hj hj'
    rw [show j - k = 0 by omega, pow_zero]

/-! ### The blowup and the divisors together -/

/-- **Stacks Project, Tag 0ESU, the divisors `D_j` on an admissible blowup.** For a finitely
presented `𝒪_X`-module `ℱ` with `ℱ|_U = 0` there is a `U`-admissible blowup `b : X' → X` and
effective Cartier divisors `D_j` on `X'`, only finitely many meeting any affine open, with every
Fitting ideal of `b^*ℱ` the locally finite sum `Fit_k = ∑_{j > k} (j - k) D_j`, and with local
equations for the `D_j` around every point of the blowup.

This joins
`AlgebraicGeometry.exists_isAdmissibleBlowup_isEffectiveCartierDivisor_fittingIdeal_pullback`,
which produces the blowup and the divisors `E_k`, to
`AlgebraicGeometry.exists_divisors_locallyFiniteSum_eq_fittingIdeal`, which extracts the `D_j`
from them. -/
theorem exists_isAdmissibleBlowup_divisors [F.IsFinitePresentation] (U : X.Opens)
    (hzero : CategoryTheory.Limits.IsZero ((Scheme.Modules.pullback U.ι).obj F)) :
    ∃ (X' : Scheme.{u}) (b : X' ⟶ X), Stacks.Blowup.IsAdmissibleBlowup U b ∧
      ∃ D : ℕ → X'.IdealSheafData,
        (∀ j, IsEffectiveCartierDivisor (D j)) ∧
        IsLocallyFiniteFamily D ∧
        (∀ k : ℕ, fittingIdeal ((Scheme.Modules.pullback b).obj F) (k : ℤ) =
          locallyFiniteSum D fun j => (j + 1) - k) ∧
        (∀ x : X', ∃ V : X'.affineOpens, x ∈ (V.1 : Set X') ∧
          ∃ (N : ℕ) (e : ℕ → Γ(X', V.1)),
            (∀ j, j + 1 ≤ N → (D j).ideal V = Ideal.span {e (j + 1)}) ∧
            (∀ j, N ≤ j → (D j).ideal V = ⊤) ∧
            (∀ j, e j ∈ nonZeroDivisors Γ(X', V.1)) ∧
            (∀ j, N < j → IsUnit (e j)) ∧
            (∀ k : ℕ, (fittingIdeal ((Scheme.Modules.pullback b).obj F) (k : ℤ)).ideal V =
              ∏ j ∈ Finset.Icc (k + 1) N, Ideal.span {e j} ^ (j - k))) := by
  obtain ⟨X', b, hb, hcart⟩ :=
    exists_isAdmissibleBlowup_isEffectiveCartierDivisor_fittingIdeal_pullback F U hzero
  have : ((Scheme.Modules.pullback b).obj F).IsFinitePresentation :=
    @Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _ b.toLRSHom.toShHom F ‹_›
  exact ⟨X', b, hb, exists_divisors_locallyFiniteSum_eq_fittingIdeal _ hcart⟩

end AlgebraicGeometry

end
