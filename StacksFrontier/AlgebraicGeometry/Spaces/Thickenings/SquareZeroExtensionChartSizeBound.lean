module

public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionChartSize
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.InductionSupplement
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.OneAffineOpenStepSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.Topology.Dimension.KrullSupplement

/-!
# A size bound for the chart thickenings of a square-zero extension

Let `E` be a square-zero extension `0 → ℐ → 𝒜 → 𝒪_X → 0` on the small étale site of an algebraic
space `X` (the data of Stacks 05ZT), and `U` an étale chart of `X`. The chart thickening `U'` has
the underlying space of `U` and structure sheaf `𝒜|_{U_Zar}`, so an affine open `V` of `U` is an
affine open of `U'` (a thickening of an affine scheme is affine, Stacks 06AD) whose ring of
sections is `𝒜(V)`. Covering `U'` by these opens (Stacks 000Q), the size of `U'` is bounded by the
size of `U` and a uniform bound on the cardinalities `#𝒜(V)`; in particular a big fppf site
containing `U` contains `U'` once these cardinalities are uniformly below its cutoff. This is the
size bound that lets the thickening of Stacks 05ZT be realized on the given site when the
extension is small, as in the proof of Stacks 0D3X.

## Main results

* `AlgebraicGeometry.Space.SquareZeroExtension.isAffineOpen_chartThickening`: an affine open of
  `U` is an affine open of `U'`.
* `AlgebraicGeometry.Space.SquareZeroExtension.contains_chartThickening_of_mk_le`: the size bound.
* `AlgebraicGeometry.Space.SquareZeroExtension.mk_A_le_mk_mul`: `#𝒜(W) ≤ #𝒪_X(W) · #ℐ(W)`.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
* [Stacks Project, Tag 000Q](https://stacks.math.columbia.edu/tag/000Q)
-/

@[expose] public section

open CategoryTheory Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space.SquareZeroExtension

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)

/-- **An affine open of an étale chart `U` is an affine open of the chart thickening `U'`**: the
restriction of the first-order thickening `U ⟶ U'` over it is a thickening of an affine scheme
(Stacks 06AD). -/
theorem isAffineOpen_chartThickening (U : SmallEtale B S hS X.1)
    (V : (chartScheme U).affineOpens) :
    @IsAffineOpen (chartThickening B S hS E U) V.1 := by
  have hι := isFirstOrderThickening_chartImmersion B S hS E U
  have : IsAffine ((chartImmersion B S hS E U ⁻¹ᵁ V.1 : (chartScheme U).Opens) :
      Scheme.{u}) := V.2
  exact Stacks.Thickenings.isAffine_of_isThickening (i := chartImmersion B S hS E U ∣_ V.1)
    ⟨IsZariskiLocalAtTarget.restrict (P := @_root_.AlgebraicGeometry.IsClosedImmersion) hι.1 V.1,
      (IsZariskiLocalAtTarget.restrict (P := @_root_.AlgebraicGeometry.Surjective)
        ⟨hι.isThickening.2⟩ V.1).surj⟩

/-- **The size bound for a chart thickening.** If the sections of `𝒜` over the affine opens of an
étale chart `U` have cardinality at most `κ`, the chart thickening `U'` has size at most
`max (size U) (max ℵ₀ κ)`; so a big fppf site whose cutoff exceeds `κ` contains `U'`. -/
theorem contains_chartThickening_of_mk_le (U : SmallEtale B S hS X.1) {κ : Cardinal.{u}}
    (hκ : κ < B.cutoff)
    (h : ∀ V : (chartScheme U).affineOpens,
      #(E.A.val.obj (op ((chartOpens B S hS U).obj V.1))) ≤ κ) :
    B.Contains (chartThickening B S hS E U) := by
  have hne : Nonempty (chartScheme U).affineOpens := ⟨⟨⊥, isAffineOpen_bot _⟩⟩
  have h' : ∀ V : (chartScheme U).affineOpens,
      #(E.A.val.obj (op ((openChartFunctor B S hS X.1 U).obj V.1))) ≤ κ := fun V =>
    chartOpens_obj_eq_openChartFunctor_obj B S hS U V.1 ▸ h V
  let O : (chartScheme U).affineOpens → (chartThickening B S hS E U).Opens := fun V => V.1
  have hle := Scheme.size_le_of_iSup_eq_top (X := chartThickening B S hS E U) O
    (iSup_affineOpens_eq_top (chartScheme U))
  have hV : ∀ V, Scheme.size (O V : Scheme.{u}) ≤ max ℵ₀ κ := fun V => by
    have : IsAffine (O V : Scheme.{u}) := isAffineOpen_chartThickening E U V
    rw [Scheme.size_of_isAffine]
    exact max_le_max le_rfl
      ((Cardinal.mk_congr (O V).topIso.commRingCatIsoToRingEquiv.toEquiv).trans_le (h' V))
  exact hle.trans_lt (max_lt ((Scheme.mk_affineOpens_le_size _).trans_lt U.obj.left.left.2)
    ((ciSup_le' hV).trans_lt (max_lt B.aleph0_lt_cutoff hκ)))

/-- **The sections of `𝒜` are bounded by those of the kernel and of `𝒪_X`**: over every chart,
`𝒜(W) ⟶ 𝒪_X(W)` is additive with kernel the image of `ℐ(W)`, so each of its fibres is in
bijection with a subset of `ℐ(W)`. -/
theorem mk_A_le_mk_mul (W : (SmallEtale B S hS X.1)ᵒᵖ) :
    #(E.A.val.obj W) ≤
      #((smallEtaleRingedTopos B S hS X).O.val.obj W) * #(E.I.val.obj W) := by
  classical
  refine Cardinal.mk_le_mk_mul_of_mk_preimage_le (E.π.hom.app W) fun o => ?_
  by_cases hne : (E.π.hom.app W ⁻¹' {o}).Nonempty
  · obtain ⟨a₀, ha₀⟩ := hne
    have hmem : ∀ a : E.π.hom.app W ⁻¹' {o}, E.π.hom.app W (a.1 - a₀) = 0 := fun a => by
      rw [map_sub, sub_eq_zero]
      exact a.2.trans ha₀.symm
    refine Cardinal.mk_le_of_injective
      (f := fun a => (E.exact_kernel W (a.1 - a₀) (hmem a)).choose) fun a b hab => ?_
    have ha := (E.exact_kernel W (a.1 - a₀) (hmem a)).choose_spec.1
    have hb := (E.exact_kernel W (b.1 - a₀) (hmem b)).choose_spec.1
    dsimp only at hab
    rw [hab, hb] at ha
    exact Subtype.ext (sub_left_injective ha.symm)
  · exact (Cardinal.mk_eq_zero_iff.2 ⟨fun x => hne ⟨x.1, x.2⟩⟩).trans_le zero_le

end AlgebraicGeometry.Space.SquareZeroExtension

end
