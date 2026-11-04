module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.TorsionVanishingBound
public import StacksFrontier.AlgebraicGeometry.SpecResidueFieldClosedPoint
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.LocallyFiniteTypeSiteGabberInputs

/-!
# Input (3) of the vanishing above `d_V` at the closed point of a local base

Let `A` be a local ring whose residue field `κ` is finite or separably closed, and let
`S ≅ Spec A`. Input (3) of Stacks 0DC6
(`AlgebraicGeometry.Scheme.ResidueFieldVanishingBound S n`) asks that `1 + 2 dim(S)` bound the
étale cohomology of `Spec κ(s)` with coefficients killed by `n` at every point `s` of `S`.

At the closed point `s₀` of `S` the residue field `κ(s₀)` is isomorphic to `κ`, so it is finite or
separably closed, and its étale cohomology with coefficients killed by `n > 0` vanishes above `1`
(`AlgebraicGeometry.Scheme.isTorsionVanishingBound_spec_of_finite`,
`AlgebraicGeometry.Scheme.isTorsionVanishingBound_spec_of_isSepClosed`). As `1 ≤ 1 + 2 dim(S)`,
input (3) reduces to the points `s ≠ s₀`, which for a base of positive dimension is Travaux de
Gabber, Exposé XVIII-A, Corollary 1.2. When `A` has dimension zero, `s₀` is the only point and
input (3) holds outright.

## Main results

* `AlgebraicGeometry.Scheme.isTorsionVanishingBound_spec_of_ringEquiv`: a field isomorphic to a
  finite or separably closed field has `n`-cohomological dimension at most one.
* `AlgebraicGeometry.Scheme.isTorsionVanishingBound_residueField_closedPoint`: the bound `1` at the
  closed point of `S`.
* `AlgebraicGeometry.Scheme.residueFieldVanishingBound_of_forall_ne`: input (3) from the points
  other than the closed point.
* `AlgebraicGeometry.Scheme.residueFieldVanishingBound_of_ringKrullDim_eq_zero`: input (3) over a
  local ring of dimension zero.

## References

* [Stacks Project, Tag 0DC6](https://stacks.math.columbia.edu/tag/0DC6)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- **A field isomorphic to a finite or separably closed field has `n`-cohomological dimension at
most one**, for every positive `n`. -/
theorem isTorsionVanishingBound_spec_of_ringEquiv {k K : Type u} [Field k] [Field K]
    (φ : k ≃+* K) (hk : Finite k ∨ IsSepClosed k) {n : ℕ} (hn : 0 < n) :
    IsTorsionVanishingBound (Spec (.of K)) n 1 := by
  rcases hk with hk | hk
  · have : Finite K := Finite.of_equiv k φ.toEquiv
    exact isTorsionVanishingBound_spec_of_finite K hn
  · let _ : Algebra k K := φ.toRingHom.toAlgebra
    have : Algebra.IsAlgebraic k K := ⟨fun x =>
      (show x = algebraMap k K (φ.symm x) by simp [RingHom.algebraMap_toAlgebra]) ▸
        isAlgebraic_algebraMap _⟩
    have : IsSepClosed K := Algebra.IsAlgebraic.isSepClosed (F := k) (E := K)
    exact (isTorsionVanishingBound_spec_of_isSepClosed K hn).mono zero_le_one

/-- **The residue field at the closed point of a local base** (Stacks 0DC6, input (3) at the
closed point). Let `A` be a local ring whose residue field is finite or separably closed and let
`e : S ≅ Spec A`. At the closed point `s₀` of `S`, `1` bounds the étale cohomology of `Spec κ(s₀)`
with coefficients killed by `n`, for every `n > 0`: `κ(s₀)` is isomorphic to the residue field
of `A`. -/
theorem isTorsionVanishingBound_residueField_closedPoint {S : Scheme.{u}} (A : Type u)
    [CommRing A] [IsLocalRing A]
    (hk : Finite (IsLocalRing.ResidueField A) ∨ IsSepClosed (IsLocalRing.ResidueField A))
    (e : S ≅ Spec (.of A)) {n : ℕ} (hn : 0 < n) :
    IsTorsionVanishingBound (Spec (.of (S.residueField (e.inv.base (IsLocalRing.closedPoint A)))))
      n 1 := by
  set s₀ : S := e.inv.base (IsLocalRing.closedPoint A)
  have hs₀ : e.hom.base s₀ = IsLocalRing.closedPoint A := Scheme.inv_hom_apply e _
  -- `κ(s₀) ≅ κ(closed point of Spec A) ≅ κ`
  let φ₁ : (Spec (.of A)).residueField (e.hom.base s₀) ≅ S.residueField s₀ :=
    asIso (e.hom.residueFieldMap s₀)
  let φ₂ : (Spec (.of A)).residueField (e.hom.base s₀) ≃+*
      (Spec (.of A)).residueField (IsLocalRing.closedPoint (CommRingCat.of A)) :=
    ((Spec (.of A)).residueFieldCongr hs₀).commRingCatIsoToRingEquiv
  let φ : IsLocalRing.ResidueField A ≃+* S.residueField s₀ :=
    (residueFieldAtClosedPointEquiv (R := .of A)).symm.trans
      (φ₂.symm.trans φ₁.commRingCatIsoToRingEquiv)
  exact isTorsionVanishingBound_spec_of_ringEquiv φ hk hn

/-- **Input (3) from the points other than the closed point** (Stacks 0DC6). Let `A` be a local
ring whose residue field is finite or separably closed, `e : S ≅ Spec A` and `n > 0`. If
`1 + 2 dim(S)` bounds the étale cohomology of `Spec κ(s)` with coefficients killed by `n` at every
point `s` other than the closed point `s₀`, then it does at every point: at `s₀` the bound is
`1 ≤ 1 + 2 dim(S)`. -/
theorem residueFieldVanishingBound_of_forall_ne {S : Scheme.{u}} (A : Type u) [CommRing A]
    [IsLocalRing A]
    (hk : Finite (IsLocalRing.ResidueField A) ∨ IsSepClosed (IsLocalRing.ResidueField A))
    (e : S ≅ Spec (.of A)) {n : ℕ} (hn : 0 < n)
    (h : ∀ s : S, s ≠ e.inv.base (IsLocalRing.closedPoint A) →
      IsTorsionVanishingBound (Spec (.of (S.residueField s))) n (1 + 2 * topologicalKrullDim S)) :
    ResidueFieldVanishingBound S n := by
  intro s
  by_cases hs : s = e.inv.base (IsLocalRing.closedPoint A)
  · subst hs
    have : Nonempty (TopologicalSpace.IrreducibleCloseds S) :=
      ⟨⟨closure {e.inv.base (IsLocalRing.closedPoint A)}, isIrreducible_singleton.closure,
        isClosed_closure⟩⟩
    have h0 : (0 : WithBot ℕ∞) ≤ topologicalKrullDim S := Order.krullDim_nonneg
    refine (isTorsionVanishingBound_residueField_closedPoint A hk e hn).mono ?_
    refine le_add_of_nonneg_right ?_
    rw [two_mul]
    exact add_nonneg h0 h0
  · exact h s hs

/-- **Input (3) over a local ring of dimension zero** (Stacks 0DC6). Let `A` be a local ring of
Krull dimension zero whose residue field is finite or separably closed, `e : S ≅ Spec A` and
`n > 0`. Then `1 + 2 dim(S)` bounds the étale cohomology of `Spec κ(s)` with coefficients killed
by `n` at every point `s` of `S`: the closed point is the only point. -/
theorem residueFieldVanishingBound_of_ringKrullDim_eq_zero {S : Scheme.{u}} (A : Type u)
    [CommRing A] [IsLocalRing A] (hdim : ringKrullDim A = 0)
    (hk : Finite (IsLocalRing.ResidueField A) ∨ IsSepClosed (IsLocalRing.ResidueField A))
    (e : S ≅ Spec (.of A)) {n : ℕ} (hn : 0 < n) :
    ResidueFieldVanishingBound S n := by
  have : Ring.KrullDimLE 0 A := ⟨hdim.le⟩
  -- every point of `S` is the closed point
  have hall : ∀ s : S, s = e.inv.base (IsLocalRing.closedPoint A) := by
    intro s
    have hx : e.hom.base s = IsLocalRing.closedPoint A :=
      PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal
        (Ideal.IsPrime.isMaximal' (e.hom.base s).2))
    rw [← hx]
    exact (Scheme.hom_inv_apply e s).symm
  exact residueFieldVanishingBound_of_forall_ne A hk e hn fun s hs => absurd (hall s) hs

end AlgebraicGeometry.Scheme
