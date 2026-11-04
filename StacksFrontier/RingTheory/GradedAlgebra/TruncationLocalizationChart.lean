module

public import StacksFrontier.RingTheory.GradedAlgebra.TruncationLocalization
public import StacksFrontier.RingTheory.GradedAlgebra.Proj.LaurentAwayDivisor
public import StacksFrontier.RingTheory.DeRham.PolynomialLaurentPositiveForms

/-!
# The chart of the cone over a standard open, as a polynomial algebra

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded `R`-algebra, `B = ⨁_{d ≥ 0} A_{≥ d}` its truncation algebra
and `L = Proj B` the cone over `P = Proj A` ([Stacks, Tag 0EKG]). Over a standard open `D₊(g)` of
`P` the cone is the affine scheme with ring `C = B₍ψ g₎`, and the comparison map
`Stacks.Truncation.awayToLocalization : C → A[1/g]` identifies `C` with the nonnegative part of
the localization.

Suppose `g = u h` with `u` of degree one. Then `A[1/g] = A₍g₎[u, u⁻¹]`
(`Stacks.GradedLaurent.laurentDivisorEquiv`), and this file shows that `C = A₍g₎[X]` with `X`
the element `u` of `C`: the cone over `D₊(g)` is the trivial line bundle. Under these
identifications the restriction to the punctured cone `C → A[1/g]` is `A₍g₎[X] → A₍g₎[T;T⁻¹]`,
and the restriction to the zero section `C → A₍g₎` induced by `τ` is evaluation at `X = 0`.
Together with `StacksFrontier.RingTheory.DeRham.PolynomialLaurentPositiveForms` this computes the
forms on the cone vanishing on the zero section.

## Main definitions

* `Stacks.Truncation.Chart.coordinate`: the element `X = (u g)⁽ᵈ⁺¹⁾ / ψ g` of `C`.
* `Stacks.Truncation.Chart.polyAlgEquiv`: the identification `A₍g₎[X] ≃ₐ[R] C`.
* `Stacks.Truncation.Chart.laurentAlgEquiv`: the identification `A₍g₎[T;T⁻¹] ≃ₐ[R] A[1/g]`.
* `Stacks.Truncation.Chart.restrictAlg`, `Stacks.Truncation.Chart.zeroAlg`: the restrictions
  `C → A[1/g]` and `C → A₍g₎`, as maps of `R`-algebras.

## Main results

* `Stacks.Truncation.Chart.restrictAlg_comp_polyAlgEquiv` and
  `Stacks.Truncation.Chart.zeroAlg_comp_polyAlgEquiv`: the two restrictions are, through the
  identifications, `A₍g₎[X] → A₍g₎[T;T⁻¹]` and evaluation at `0`.

## References

* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
* [Stacks Project, Tag 0FUR](https://stacks.math.columbia.edu/tag/0FUR)
-/

@[expose] public noncomputable section

open HomogeneousLocalization Polynomial LaurentPolynomial
open Stacks.AlgebraicGeometry.ProjAndSpecTruncation

universe u

namespace Stacks.Truncation.Chart

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A)
  [_root_.GradedAlgebra 𝒜]

/-! ### The `R`-algebra structures -/

-- The degree-zero localization of a graded `R`-algebra is an `R`-algebra, through the
-- degree-zero constants: this is `HomogeneousLocalization.instAlgebra`, whose action is
-- Mathlib's `HomogeneousLocalization.instSMul`.

/-- The `R`-algebra map into `HomogeneousLocalization 𝒜 x` sends `r` to the degree-zero
constant `algebraMap R (𝒜 0) r`. -/
theorem algebraMap_homogeneousLocalization (x : Submonoid A) (r : R) :
    algebraMap R (HomogeneousLocalization 𝒜 x) r = fromZeroRingHom 𝒜 x (algebraMap R (𝒜 0) r) :=
  rfl

/-- The degree-zero localizations of the truncation algebra are `R`-algebras, through
`σ : A ≃ B₀`. -/
instance algebraTruncationLocalization (x : Submonoid (TruncationRing 𝒜)) :
    Algebra R (HomogeneousLocalization (grading 𝒜) x) :=
  ((fromZeroRingHom (grading 𝒜) x).comp
    (((sigma 𝒜 : A ≃+* grading 𝒜 0) : A →+* grading 𝒜 0).comp (algebraMap R A))).toAlgebra

/-- The `R`-algebra map into a degree-zero localization of the truncation algebra sends `r`
to the degree-zero constant `σ (algebraMap R A r)`. -/
theorem algebraMap_truncationLocalization (x : Submonoid (TruncationRing 𝒜)) (r : R) :
    algebraMap R (HomogeneousLocalization (grading 𝒜) x) r =
      fromZeroRingHom (grading 𝒜) x (sigma 𝒜 (algebraMap R A r)) :=
  rfl

/-! ### The coordinate of the chart -/

section Chart

variable {𝒜} {u h g : A} {d : ℕ}

/-- `u g` lies in `A_{≥ d + 1}` when `g` has degree `d + 1`. -/
theorem mul_mem_truncation (hu : u ∈ 𝒜 1) (hgd : g ∈ 𝒜 (d + 1)) :
    u * g ∈ truncation 𝒜 (1 * (d + 1)) :=
  mem_truncation_of_mem 𝒜 (by omega) (SetLike.mul_mem_graded hu hgd)

/-- **The fibre coordinate of the cone over `D₊(g)`**: the element `(u g)⁽ᵈ⁺¹⁾ / ψ g` of
`C = B₍ψ g₎`, which is `u` in `A[1/g]`. -/
def coordinate (hu : u ∈ 𝒜 1) (hgd : g ∈ 𝒜 (d + 1)) : Away (grading 𝒜) (psi 𝒜 g) :=
  awayElt 𝒜 (d + 1) hgd 1 (u * g) (mul_mem_truncation hu hgd)

/-- The comparison map `C → A[1/g]` sends the fibre coordinate to `u`. -/
theorem awayToLocalization_coordinate (hu : u ∈ 𝒜 1) (hgd : g ∈ 𝒜 (d + 1)) :
    awayToLocalization 𝒜 (coordinate hu hgd) = algebraMap A (Localization.Away g) u := by
  rw [coordinate, awayToLocalization_awayElt, awayFrac, ← Localization.mk_one_eq_algebraMap,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp only [Submonoid.coe_one, one_mul, pow_one]; ring⟩

/-- The degree-zero fraction `x / gⁿ` of `A`, carried by `ψ` into `C`, is `x⁽ⁿ⁽ᵈ⁺¹⁾⁾ / (ψ g)ⁿ`. -/
theorem awayMap_psi_mk (hgd : g ∈ 𝒜 (d + 1)) (n : ℕ) (x : A) (hx : x ∈ 𝒜 (n • (d + 1))) :
    Away.map (psi 𝒜) g (Away.mk 𝒜 hgd n x hx) =
      awayElt 𝒜 (d + 1) hgd n x (mem_truncation_of_mem 𝒜 (by simp [smul_eq_mul]) hx) := by
  rw [Away.map_mk]
  refine congrArg HomogeneousLocalization.mk
    (HomogeneousLocalization.NumDenSameDeg.ext _ (smul_eq_mul n (d + 1)) ?_ ?_)
  · change psi 𝒜 x = degElt 𝒜 (n * (d + 1)) x _
    rw [psi_eq_degElt 𝒜 x hx]
    exact degElt_congr 𝒜 (smul_eq_mul n (d + 1)) rfl _ _
  · change psi 𝒜 g ^ n = psi 𝒜 g ^ n
    rfl

/-- **On degree-zero fractions of `A` the comparison map `C → A[1/g]` is the inclusion.** -/
theorem awayToLocalization_awayMap_psi (hgd : g ∈ 𝒜 (d + 1)) (c : Away 𝒜 g) :
    awayToLocalization 𝒜 (Away.map (psi 𝒜) g c) = c.val := by
  obtain ⟨n, x, hx, rfl⟩ := Away.mk_surjective 𝒜 hgd c
  rw [awayMap_psi_mk hgd, awayToLocalization_awayElt, Away.val_mk]
  rfl

/-- The map `A₍g₎[X] → C` sending `X` to the fibre coordinate. -/
def polyHom (hu : u ∈ 𝒜 1) (hgd : g ∈ 𝒜 (d + 1)) :
    (Away 𝒜 g)[X] →+* Away (grading 𝒜) (psi 𝒜 g) :=
  eval₂RingHom (Away.map (psi 𝒜) g) (coordinate hu hgd)

/-- **Restricting to the punctured cone is `A₍g₎[X] → A₍g₎[T;T⁻¹]`.** -/
theorem awayToLocalization_comp_polyHom (hu : u ∈ 𝒜 1) (hh : h ∈ 𝒜 d) (hg : u * h = g) :
    (awayToLocalization 𝒜).comp (polyHom hu (Stacks.GradedLaurent.mem_of_mul_eq 𝒜 hu hh hg)) =
      (Stacks.GradedLaurent.laurentDivisorEquiv 𝒜 hu hh hg : _ →+* _).comp
        (toLaurent : (Away 𝒜 g)[X] →+* (Away 𝒜 g)[T;T⁻¹]) := by
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · change awayToLocalization 𝒜 (Polynomial.eval₂ (Away.map (psi 𝒜) g) _ (Polynomial.C c)) =
      Stacks.GradedLaurent.laurentDivisorHom 𝒜 hg (toLaurent (Polynomial.C c))
    rw [Polynomial.eval₂_C, toLaurent_C, Stacks.GradedLaurent.laurentDivisorHom_C]
    exact awayToLocalization_awayMap_psi (Stacks.GradedLaurent.mem_of_mul_eq 𝒜 hu hh hg) c
  · change awayToLocalization 𝒜 (Polynomial.eval₂ (Away.map (psi 𝒜) g) _ Polynomial.X) =
      Stacks.GradedLaurent.laurentDivisorHom 𝒜 hg (toLaurent Polynomial.X)
    rw [Polynomial.eval₂_X, toLaurent_X, Stacks.GradedLaurent.laurentDivisorHom_T, zpow_one,
      Stacks.GradedLaurent.coe_unitOfMul]
    exact awayToLocalization_coordinate hu _

/-- **The cone over `D₊(g)` is the trivial line bundle**: `A₍g₎[X] → C` is bijective. -/
theorem bijective_polyHom (hu : u ∈ 𝒜 1) (hh : h ∈ 𝒜 d) (hg : u * h = g) :
    Function.Bijective (polyHom hu (Stacks.GradedLaurent.mem_of_mul_eq 𝒜 hu hh hg)) := by
  classical
  have hgd := Stacks.GradedLaurent.mem_of_mul_eq 𝒜 hu hh hg
  have hcomp := awayToLocalization_comp_polyHom (𝒜 := 𝒜) hu hh hg
  have hρinj := awayToLocalization_injective 𝒜 (d + 1) hgd
  refine ⟨fun P Q hPQ => ?_, fun c => ?_⟩
  · have := congrArg (awayToLocalization 𝒜) hPQ
    rw [← RingHom.comp_apply, ← RingHom.comp_apply, hcomp, RingHom.comp_apply,
      RingHom.comp_apply] at this
    exact toLaurent_injective ((Stacks.GradedLaurent.laurentDivisorEquiv 𝒜 hu hh hg).injective
      this)
  · obtain ⟨k, a, ha, rfl⟩ := awayElt_surjective 𝒜 (d + 1) hgd c
    -- the image `a / gᵏ` is a polynomial in `u`
    have hpoly : ∀ e ∈ DFinsupp.support (DirectSum.decompose 𝒜 a),
        ∃ P : (Away 𝒜 g)[X], (Stacks.GradedLaurent.laurentDivisorEquiv 𝒜 hu hh hg)
          (toLaurent P) = Localization.mk (DirectSum.decompose 𝒜 a e : A)
            (Stacks.GradedLaurent.powSub g k) := by
      intro e he
      have hle : k * (d + 1) ≤ e := by
        by_contra hlt
        exact (DFinsupp.mem_support_iff.1 he) (Subtype.ext
          (proj_eq_zero_of_mem_truncation 𝒜 (by omega) ha))
      obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hle
      obtain ⟨c', hc'⟩ := Stacks.GradedLaurent.exists_mk_eq_val_mul_zpow 𝒜 hu hh hg
        (DirectSum.decompose 𝒜 a e).2 k
      refine ⟨Polynomial.C c' * X ^ j, ?_⟩
      have hexp : ((e : ℕ) : ℤ) - (k : ℤ) * ((d : ℤ) + 1) = (j : ℤ) := by
        rw [hj]; push_cast; ring
      rw [hc', hexp]
      simp only [Stacks.GradedLaurent.laurentDivisorEquiv_apply, map_mul, map_pow, toLaurent_C,
        toLaurent_X, Stacks.GradedLaurent.laurentDivisorHom_C,
        Stacks.GradedLaurent.laurentDivisorHom_T, zpow_one, zpow_natCast,
        Units.val_pow_eq_pow_val]
    choose P hP using hpoly
    refine ⟨∑ e ∈ (DFinsupp.support (DirectSum.decompose 𝒜 a)).attach, P e.1 e.2, hρinj ?_⟩
    rw [← RingHom.comp_apply, hcomp, RingHom.comp_apply, map_sum, map_sum,
      awayToLocalization_awayElt]
    simp only [RingEquiv.coe_toRingHom, hP]
    rw [Finset.sum_attach (DFinsupp.support (DirectSum.decompose 𝒜 a))
      (fun e => (Localization.mk (DirectSum.decompose 𝒜 a e : A)
        (Stacks.GradedLaurent.powSub g k) : Localization.Away g)),
      ← Localization.mk_sum, DirectSum.sum_support_decompose 𝒜 a]
    rfl

/-- **The restriction to the zero section** `C → A₍g₎`, induced by `τ : B → A`. -/
def zeroHom (g : A) : Away (grading 𝒜) (psi 𝒜 g) →+* Away 𝒜 g :=
  HomogeneousLocalization.map (tau 𝒜) (Submonoid.powers_le.2 (by
    change tau 𝒜 (psi 𝒜 g) ∈ Submonoid.powers g
    rw [tau_psi_apply]
    exact Submonoid.mem_powers g))

/-- The restriction to the zero section sends `a / (ψ g)ᵏ`, for `a ∈ A_{≥ k (d + 1)}`, to
`a' / gᵏ`, where `a'` is the degree-`k (d + 1)` component of `a`. -/
theorem zeroHom_awayElt (hgd : g ∈ 𝒜 (d + 1)) (k : ℕ) (a : A) (ha : a ∈ truncation 𝒜 (k * (d + 1)))
    (hproj : GradedRing.proj 𝒜 (k * (d + 1)) a ∈ 𝒜 (k • (d + 1))) :
    zeroHom (𝒜 := 𝒜) g (awayElt 𝒜 (d + 1) hgd k a ha) =
      Away.mk 𝒜 hgd k (GradedRing.proj 𝒜 (k * (d + 1)) a) hproj := by
  rw [zeroHom, awayElt, HomogeneousLocalization.map_mk]
  refine congrArg HomogeneousLocalization.mk
    (HomogeneousLocalization.NumDenSameDeg.ext _ (smul_eq_mul k (d + 1)).symm ?_ ?_)
  · exact tau_degElt 𝒜 _ a ha
  · change tau 𝒜 (psi 𝒜 g ^ k) = g ^ k
    rw [map_pow, tau_psi_apply]

/-- On degree-zero fractions of `A` the restriction to the zero section is the inverse of `ψ`. -/
private theorem zeroHom_awayMap_psi (hgd : g ∈ 𝒜 (d + 1)) (c : Away 𝒜 g) :
    zeroHom (𝒜 := 𝒜) g (Away.map (psi 𝒜) g c) = c := by
  obtain ⟨n, x, hx, rfl⟩ := Away.mk_surjective 𝒜 hgd c
  have hpx : GradedRing.proj 𝒜 (n * (d + 1)) x = x := by
    rw [GradedRing.proj_apply, ← smul_eq_mul]
    exact DirectSum.decompose_of_mem_same 𝒜 hx
  rw [awayMap_psi_mk hgd, zeroHom_awayElt hgd n x _ (by rw [hpx]; exact hx)]
  refine HomogeneousLocalization.val_injective _ ?_
  rw [Away.val_mk, Away.val_mk, hpx]

/-- **Restricting to the zero section is evaluation at `X = 0`.** -/
theorem zeroHom_comp_polyHom (hu : u ∈ 𝒜 1) (hgd : g ∈ 𝒜 (d + 1)) :
    (zeroHom (𝒜 := 𝒜) g).comp (polyHom hu hgd) = Polynomial.evalRingHom 0 := by
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · change zeroHom g (Polynomial.eval₂ (Away.map (psi 𝒜) g) _ (Polynomial.C _)) =
      Polynomial.eval 0 (Polynomial.C _)
    rw [Polynomial.eval₂_C, Polynomial.eval_C]
    exact zeroHom_awayMap_psi hgd c
  · change zeroHom g (Polynomial.eval₂ (Away.map (psi 𝒜) g) _ Polynomial.X) =
      Polynomial.eval 0 Polynomial.X
    rw [Polynomial.eval₂_X, Polynomial.eval_X, coordinate]
    have h0 : GradedRing.proj 𝒜 (1 * (d + 1)) (u * g) = 0 :=
      proj_of_mem_ne 𝒜 (SetLike.mul_mem_graded hu hgd) (by omega)
    rw [zeroHom_awayElt hgd 1 (u * g) _ (by rw [h0]; exact zero_mem _)]
    refine HomogeneousLocalization.val_injective _ ?_
    rw [Away.val_mk, HomogeneousLocalization.val_zero]
    simp only [h0, Localization.mk_zero]

end Chart

/-! ### The maps as maps of `R`-algebras -/

section AlgebraMaps

variable {𝒜} {u h g : A} {d : ℕ}

/-- The image of `r : R` in `A₍g₎`, viewed in `A[1/g]`, is the image of `r` there. -/
theorem val_algebraMap_away (r : R) :
    (algebraMap R (Away 𝒜 g) r).val = algebraMap R (Localization.Away g) r := by
  rw [algebraMap_homogeneousLocalization, HomogeneousLocalization.val_fromZeroRingHom,
    SetLike.GradeZero.coe_algebraMap, IsScalarTower.algebraMap_apply R A (Localization.Away g),
    Localization.mk_one_eq_algebraMap]

/-- The image of `r : R` in `A` has degree `0 • (d + 1)`. -/
theorem algebraMap_mem_zero_smul (r : R) : algebraMap R A r ∈ 𝒜 (0 • (d + 1)) := by
  rw [zero_smul]
  exact SetLike.algebraMap_mem_graded 𝒜 r

/-- The image of `r : R` in `A₍g₎` is the fraction `r / g⁰`. -/
theorem algebraMap_away_eq_mk (hgd : g ∈ 𝒜 (d + 1)) (r : R) :
    algebraMap R (Away 𝒜 g) r =
      Away.mk 𝒜 hgd 0 (algebraMap R A r) (algebraMap_mem_zero_smul r) := by
  refine HomogeneousLocalization.val_injective _ ?_
  rw [val_algebraMap_away, Away.val_mk, IsScalarTower.algebraMap_apply R A (Localization.Away g),
    ← Localization.mk_one_eq_algebraMap]
  congr 1
  exact Subtype.ext (pow_zero g).symm

/-- The image of `r : R` in `A` lies in `A_{≥ 0 * (d + 1)}`. -/
theorem algebraMap_mem_truncation_zero_mul (r : R) :
    algebraMap R A r ∈ truncation 𝒜 (0 * (d + 1)) := by
  rw [Nat.zero_mul]
  exact mem_truncation_zero 𝒜 _

/-- The image of `r : R` in `C = B₍ψ g₎` is the fraction `r / (ψ g)⁰`. -/
theorem algebraMap_truncation_eq_awayElt (hgd : g ∈ 𝒜 (d + 1)) (r : R) :
    algebraMap R (Away (grading 𝒜) (psi 𝒜 g)) r =
      awayElt 𝒜 (d + 1) hgd 0 (algebraMap R A r) (algebraMap_mem_truncation_zero_mul r) := by
  rw [algebraMap_truncationLocalization, awayElt]
  refine congrArg HomogeneousLocalization.mk
    (HomogeneousLocalization.NumDenSameDeg.ext _ (Nat.zero_mul (d + 1)).symm ?_ ?_)
  · change ((sigma 𝒜 (algebraMap R A r) : grading 𝒜 0) : TruncationRing 𝒜) = degElt 𝒜 _ _ _
    rw [coe_sigma_eq_degElt]
    exact degElt_congr 𝒜 (Nat.zero_mul (d + 1)).symm rfl _ _
  · change (1 : TruncationRing 𝒜) = psi 𝒜 g ^ 0
    rw [pow_zero]

/-- The image of `r : R` in `C` is the image of its image in `A₍g₎` under `ψ`. -/
private theorem algebraMap_truncation_eq_awayMap (hgd : g ∈ 𝒜 (d + 1)) (r : R) :
    algebraMap R (Away (grading 𝒜) (psi 𝒜 g)) r =
      Away.map (psi 𝒜) g (algebraMap R (Away 𝒜 g) r) := by
  rw [algebraMap_away_eq_mk hgd, awayMap_psi_mk hgd, algebraMap_truncation_eq_awayElt hgd]

/-- **The restriction `C → A[1/g]` to the punctured cone**, as a map of `R`-algebras. -/
def restrictAlg (hgd : g ∈ 𝒜 (d + 1)) :
    Away (grading 𝒜) (psi 𝒜 g) →ₐ[R] Localization.Away g where
  __ := awayToLocalization 𝒜
  commutes' r := by
    change awayToLocalization 𝒜 _ = _
    rw [algebraMap_truncation_eq_awayElt hgd, awayToLocalization_awayElt,
      awayFrac_zero_eq_algebraMap, IsScalarTower.algebraMap_apply R A (Localization.Away g)]

/-- `restrictAlg` is the comparison map `awayToLocalization`. -/
@[simp]
theorem restrictAlg_apply (hgd : g ∈ 𝒜 (d + 1)) (c : Away (grading 𝒜) (psi 𝒜 g)) :
    restrictAlg hgd c = awayToLocalization 𝒜 c := rfl

/-- **The Laurent identification `A₍g₎[T;T⁻¹] ≅ A[1/g]`**, as an isomorphism of `R`-algebras. -/
def laurentAlgEquiv (hu : u ∈ 𝒜 1) (hh : h ∈ 𝒜 d) (hg : u * h = g) :
    (Away 𝒜 g)[T;T⁻¹] ≃ₐ[R] Localization.Away g where
  __ := Stacks.GradedLaurent.laurentDivisorEquiv 𝒜 hu hh hg
  commutes' r := by
    change Stacks.GradedLaurent.laurentDivisorHom 𝒜 hg _ = _
    rw [LaurentPolynomial.algebraMap_apply, Stacks.GradedLaurent.laurentDivisorHom_C,
      val_algebraMap_away]

/-- `laurentAlgEquiv` is the map `Stacks.GradedLaurent.laurentDivisorHom`. -/
@[simp]
theorem laurentAlgEquiv_apply (hu : u ∈ 𝒜 1) (hh : h ∈ 𝒜 d) (hg : u * h = g)
    (P : (Away 𝒜 g)[T;T⁻¹]) :
    laurentAlgEquiv hu hh hg P = Stacks.GradedLaurent.laurentDivisorHom 𝒜 hg P := rfl

/-- The map `A₍g₎[X] → C` commutes with the `R`-algebra structure maps. -/
theorem polyHom_algebraMap (hu : u ∈ 𝒜 1) (hgd : g ∈ 𝒜 (d + 1)) (r : R) :
    polyHom hu hgd (algebraMap R (Away 𝒜 g)[X] r) =
      algebraMap R (Away (grading 𝒜) (psi 𝒜 g)) r := by
  rw [Polynomial.algebraMap_apply, polyHom, coe_eval₂RingHom, Polynomial.eval₂_C,
    algebraMap_truncation_eq_awayMap hgd]

/-- **The identification `A₍g₎[X] ≅ C`**, as an isomorphism of `R`-algebras. -/
def polyAlgEquiv (hu : u ∈ 𝒜 1) (hh : h ∈ 𝒜 d) (hg : u * h = g) :
    (Away 𝒜 g)[X] ≃ₐ[R] Away (grading 𝒜) (psi 𝒜 g) :=
  AlgEquiv.ofBijective
    { polyHom hu (Stacks.GradedLaurent.mem_of_mul_eq 𝒜 hu hh hg) with
      commutes' := polyHom_algebraMap hu _ }
    (bijective_polyHom hu hh hg)

/-- `polyAlgEquiv` is the map `polyHom`. -/
@[simp]
theorem polyAlgEquiv_apply (hu : u ∈ 𝒜 1) (hh : h ∈ 𝒜 d) (hg : u * h = g) (P : (Away 𝒜 g)[X]) :
    polyAlgEquiv hu hh hg P = polyHom hu (Stacks.GradedLaurent.mem_of_mul_eq 𝒜 hu hh hg) P := rfl

/-- The restriction `C → A₍g₎` to the zero section commutes with the `R`-algebra structure
maps. -/
theorem zeroHom_algebraMap (hgd : g ∈ 𝒜 (d + 1)) (r : R) :
    zeroHom (𝒜 := 𝒜) g (algebraMap R (Away (grading 𝒜) (psi 𝒜 g)) r) =
      algebraMap R (Away 𝒜 g) r := by
  rw [algebraMap_truncation_eq_awayMap hgd, zeroHom_awayMap_psi hgd]

/-- **The restriction `C → A₍g₎` to the zero section**, as a map of `R`-algebras. -/
def zeroAlg (hgd : g ∈ 𝒜 (d + 1)) : Away (grading 𝒜) (psi 𝒜 g) →ₐ[R] Away 𝒜 g where
  __ := zeroHom (𝒜 := 𝒜) g
  commutes' := zeroHom_algebraMap hgd

/-- `zeroAlg` is the ring map `zeroHom`. -/
@[simp]
theorem zeroAlg_apply (hgd : g ∈ 𝒜 (d + 1)) (c : Away (grading 𝒜) (psi 𝒜 g)) :
    zeroAlg hgd c = zeroHom (𝒜 := 𝒜) g c :=
  rfl

/-- **Restricting to the punctured cone is `A₍g₎[X] → A₍g₎[T;T⁻¹]`**, as maps of
`R`-algebras: through `polyAlgEquiv` and `laurentAlgEquiv`, `restrictAlg` is the inclusion
`PolynomialDeRham.toLaurentR` of polynomials into Laurent polynomials. -/
theorem restrictAlg_comp_polyAlgEquiv (hu : u ∈ 𝒜 1) (hh : h ∈ 𝒜 d) (hg : u * h = g) :
    (restrictAlg (Stacks.GradedLaurent.mem_of_mul_eq 𝒜 hu hh hg)).comp
        (polyAlgEquiv hu hh hg : (Away 𝒜 g)[X] →ₐ[R] Away (grading 𝒜) (psi 𝒜 g)) =
      (laurentAlgEquiv hu hh hg : (Away 𝒜 g)[T;T⁻¹] →ₐ[R] Localization.Away g).comp
        (PolynomialDeRham.toLaurentR R (Away 𝒜 g)) := by
  refine AlgHom.ext fun P => ?_
  have := RingHom.congr_fun (awayToLocalization_comp_polyHom (𝒜 := 𝒜) hu hh hg) P
  simpa [IsScalarTower.toAlgHom_apply, LaurentPolynomial.algebraMap_eq_toLaurent] using this

/-- **Restricting to the zero section is evaluation at `X = 0`**, as maps of `R`-algebras:
through `polyAlgEquiv`, `zeroAlg` is `PolynomialDeRham.evalZeroAlg`. -/
theorem zeroAlg_comp_polyAlgEquiv (hu : u ∈ 𝒜 1) (hh : h ∈ 𝒜 d) (hg : u * h = g) :
    (zeroAlg (Stacks.GradedLaurent.mem_of_mul_eq 𝒜 hu hh hg)).comp
        (polyAlgEquiv hu hh hg : (Away 𝒜 g)[X] →ₐ[R] Away (grading 𝒜) (psi 𝒜 g)) =
      PolynomialDeRham.evalZeroAlg R (Away 𝒜 g) := by
  refine AlgHom.ext fun P => ?_
  have := RingHom.congr_fun (zeroHom_comp_polyHom (𝒜 := 𝒜) hu
    (Stacks.GradedLaurent.mem_of_mul_eq 𝒜 hu hh hg)) P
  simpa [Polynomial.coe_aeval_eq_eval] using this

end AlgebraMaps

end Stacks.Truncation.Chart

end
