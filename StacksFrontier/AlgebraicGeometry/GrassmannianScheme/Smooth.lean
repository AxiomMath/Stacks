module

public import StacksFrontier.AlgebraicGeometry.Recovery27.GrassmannianScheme
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineSpaceBundleSmooth

/-!
# The Grassmannian is smooth

The Grassmannian `G(k, n)` over the integers is covered by the coordinate charts of Tag 089T,
each an affine space of dimension `k(n - k)` over `Spec ℤ`. Since smoothness of a given relative
dimension is local on the source and affine space is smooth of its dimension, `G(k, n)` is smooth
of relative dimension `k(n - k)` over `Spec ℤ`, and hence so is its base change `G(k, n)_S` over
every scheme `S`.

## Main definitions

* `AlgebraicGeometry.Grassmannian.chartIndexEquiv`: the chart coordinates are `k(n - k)` in
  number.
* `AlgebraicGeometry.Grassmannian.chartCover`: the open cover of `G(k, n)` by its coordinate
  charts.

## Main results

* `AlgebraicGeometry.Grassmannian.smoothOfRelativeDimension_terminalFrom`: `G(k, n)` is smooth of
  relative dimension `k(n - k)` over `Spec ℤ`.
* `AlgebraicGeometry.Grassmannian.smoothOfRelativeDimension_schemeOver`: `G(k, n)_S` is smooth of
  relative dimension `k(n - k)` over `S`.

## References

* [Stacks Project, Tag 089T](https://stacks.math.columbia.edu/tag/089T)
* [Stacks Project, Tag 089U](https://stacks.math.columbia.edu/tag/089U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Grassmannian

variable (k n : ℕ)

/-- The basis vectors outside the range of an embedding `Fin (n - k) ↪ Fin n` are `n - (n - k)`
in number. -/
theorem card_compl_range {k n : ℕ} (ι : Fin (n - k) ↪ Fin n) :
    Fintype.card {j // j ∉ Set.range ι} = n - (n - k) := by
  classical
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Set.card_range_of_injective ι.injective,
    Fintype.card_fin]

/-- `n - (n - k)` copies of `n - k` coordinates are `k(n - k)` coordinates. -/
theorem sub_sub_mul (k n : ℕ) : (n - (n - k)) * (n - k) = k * (n - k) := by
  rcases le_total k n with h | h
  · rw [Nat.sub_sub_self h]
  · rw [Nat.sub_eq_zero_of_le h, Nat.mul_zero, Nat.mul_zero]

/-- **The chart coordinates are `k(n - k)` in number.** -/
def chartIndexEquiv {k n : ℕ} (ι : Fin (n - k) ↪ Fin n) :
    ChartIndex.{u} ι ≃ ULift.{u} (Fin (k * (n - k))) :=
  Equiv.ulift.trans
    ((Fintype.equivFinOfCardEq (by
        rw [Fintype.card_prod, card_compl_range, Fintype.card_fin, sub_sub_mul])).trans
      Equiv.ulift.symm)

/-- A coordinate chart of `G(k, n)` is smooth of relative dimension `k(n - k)` over `Spec ℤ`. -/
theorem smoothOfRelativeDimension_terminalFrom_chartDomain {k n : ℕ}
    (ι : Fin (n - k) ↪ Fin n) :
    SmoothOfRelativeDimension (k * (n - k))
      (terminal.from (Spec (.of (MvPolynomial (ChartIndex.{u} ι) (ULift.{u} ℤ))))) := by
  have hC : SmoothOfRelativeDimension (k * (n - k))
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := ChartIndex.{u} ι)
        (R := ULift.{u} ℤ)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension (k * (n - k)))]
    refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
    show (algebraMap (ULift.{u} ℤ)
      (MvPolynomial (ChartIndex.{u} ι) (ULift.{u} ℤ))).IsStandardSmoothOfRelativeDimension
        (k * (n - k))
    rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv (k * (n - k))
      (MvPolynomial.renameEquiv (ULift.{u} ℤ)
        ((chartIndexEquiv ι).trans (Equiv.ulift.{u, 0} (α := Fin (k * (n - k))))).symm)
  have _ := isIso_of_isTerminal specULiftZIsTerminal.{u} terminalIsTerminal
    (terminal.from (Spec (CommRingCat.of (ULift.{u} ℤ))))
  rw [← terminal.comp_from (Spec.map (CommRingCat.ofHom MvPolynomial.C))]
  exact SmoothOfRelativeDimension.comp_relativeDimension_zero _ _
    (terminal.from (Spec (.of (ULift.{u} ℤ))))

/-- **The open cover of `G(k, n)` by its coordinate charts.** -/
def chartCover : (scheme.{u} k n).OpenCover :=
  Scheme.Cover.mkOfCovers (Fin (n - k) ↪ Fin n)
    (fun ι => Spec (.of (MvPolynomial (ChartIndex.{u} ι) (ULift.{u} ℤ))))
    (fun ι => chart k n ι)
    (fun x => by
      obtain ⟨ι, y, hy⟩ := exists_mem_range_chart k n x
      exact ⟨ι, y, hy⟩)

/-- **`G(k, n)` is smooth of relative dimension `k(n - k)` over `Spec ℤ`.** -/
instance smoothOfRelativeDimension_terminalFrom :
    SmoothOfRelativeDimension (k * (n - k)) (terminal.from (scheme.{u} k n)) := by
  have _ : IsZariskiLocalAtSource
      (@SmoothOfRelativeDimension (k * (n - k)) : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension (k * (n - k)))
    (chartCover k n) fun ι => ?_
  rw [terminal.comp_from]
  exact smoothOfRelativeDimension_terminalFrom_chartDomain ι

/-- **`G(k, n)_S` is smooth of relative dimension `k(n - k)` over `S`**, as a base change of
`G(k, n) ⟶ Spec ℤ`. -/
instance smoothOfRelativeDimension_schemeOver (S : Scheme.{u}) :
    SmoothOfRelativeDimension (k * (n - k)) (schemeOver.over k n S).hom := by
  change SmoothOfRelativeDimension (k * (n - k))
    (pullback.fst (terminal.from S) (terminal.from (scheme.{u} k n)))
  have _ : MorphismProperty.IsStableUnderBaseChangeAlong
      (@SmoothOfRelativeDimension (k * (n - k)) : MorphismProperty Scheme.{u}) (terminal.from S) :=
    ⟨fun pb hpb ↦ (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback pb hpb⟩
  exact MorphismProperty.pullback_fst
    (P := (@SmoothOfRelativeDimension (k * (n - k)) : MorphismProperty Scheme.{u})) _ _
    (smoothOfRelativeDimension_terminalFrom k n)

/-- `G(k, n)_S` is smooth over `S`. -/
instance smooth_schemeOver (S : Scheme.{u}) : Smooth (schemeOver.over k n S).hom :=
  SmoothOfRelativeDimension.smooth (k * (n - k)) _

end AlgebraicGeometry.Grassmannian

end
