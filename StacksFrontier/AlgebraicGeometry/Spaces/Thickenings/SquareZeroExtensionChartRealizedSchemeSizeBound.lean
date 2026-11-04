module

public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionChartRealizedSchemeSize
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionChartSizeBound

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

* `AlgebraicGeometry.Space.SquareZeroExtension.isAffineOpen_chartRealizedScheme`: an affine open of
  `U` is an affine open of `U'`.
* `AlgebraicGeometry.Space.SquareZeroExtension.contains_chartRealizedScheme_of_mk_le`: the size
  bound.

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
theorem isAffineOpen_chartRealizedScheme (U : SmallEtale B S hS X.1)
    (V : (chartScheme U).affineOpens) :
    @IsAffineOpen (E.chartRealizedScheme U) V.1 := by
  have hι := E.isFirstOrderThickening_chartInclusion U
  have : _root_.AlgebraicGeometry.IsClosedImmersion (E.chartInclusion U) := hι.1
  have : _root_.AlgebraicGeometry.Surjective (E.chartInclusion U) := ⟨hι.isThickening.2⟩
  have : _root_.AlgebraicGeometry.IsClosedImmersion (E.chartInclusion U ∣_ V.1) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict _ _).flip inferInstance
  have : _root_.AlgebraicGeometry.Surjective (E.chartInclusion U ∣_ V.1) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict _ _).flip inferInstance
  have : IsAffine ((E.chartInclusion U ⁻¹ᵁ V.1 : (chartScheme U).Opens) : Scheme.{u}) := V.2
  exact Stacks.Thickenings.isAffine_of_isThickening (i := E.chartInclusion U ∣_ V.1)
    ⟨inferInstance, (_root_.AlgebraicGeometry.Surjective.surj (f := E.chartInclusion U ∣_ V.1))⟩

/-- **The size bound for a chart thickening.** If the sections of `𝒜` over the affine opens of an
étale chart `U` have cardinality at most `κ`, the chart thickening `U'` has size at most
`max (size U) (max ℵ₀ κ)`; so a big fppf site whose cutoff exceeds `κ` contains `U'`. -/
theorem contains_chartRealizedScheme_of_mk_le (U : SmallEtale B S hS X.1) {κ : Cardinal.{u}}
    (hκ : κ < B.cutoff)
    (h : ∀ V : (chartScheme U).affineOpens,
      #(E.A.val.obj (op ((chartOpens B S hS U).obj V.1))) ≤ κ) :
    B.Contains (E.chartRealizedScheme U) := by
  have hne : Nonempty (chartScheme U).affineOpens := ⟨⟨⊥, isAffineOpen_bot _⟩⟩
  let O : (chartScheme U).affineOpens → (E.chartRealizedScheme U).Opens := fun V => V.1
  have hcov : ⨆ V, O V = ⊤ := iSup_affineOpens_eq_top (chartScheme U)
  have hle := Scheme.size_le_of_iSup_eq_top (X := E.chartRealizedScheme U) O hcov
  have hV : ∀ V, Scheme.size (O V : Scheme.{u}) ≤ max ℵ₀ κ := fun V => by
    have : IsAffine (O V : Scheme.{u}) := E.isAffineOpen_chartRealizedScheme U V
    rw [Scheme.size_of_isAffine]
    exact max_le_max le_rfl
      ((Cardinal.mk_congr (O V).topIso.commRingCatIsoToRingEquiv.toEquiv).trans_le (h V))
  have hU : #(chartScheme U).affineOpens < B.cutoff :=
    lt_of_le_of_lt (Scheme.mk_affineOpens_le_size _) U.obj.left.left.2
  exact lt_of_le_of_lt hle (max_lt hU (lt_of_le_of_lt (ciSup_le' hV)
    (max_lt B.aleph0_lt_cutoff hκ)))

end AlgebraicGeometry.Space.SquareZeroExtension

end
