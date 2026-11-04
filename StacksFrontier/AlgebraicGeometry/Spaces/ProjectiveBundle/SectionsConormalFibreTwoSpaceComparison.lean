module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionsConormalFibreTwoSpaceComparison.FibreSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionsConormalFibreTwoSpaceComparison.FibreQuotients
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionsConormalFibreTwoSpaceComparison.FibreQuotientTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionsConormalFibreTwoSpaceComparison.BaseChange

/-!
# Comparison of the fibres of `𝐏(g^*ℰ)` and `𝐏(ℰ)` read through the fibres as projective bundles

Let `g : X' ⟶ X` be a morphism of algebraic spaces, `u : T ⟶ X` and `v : T' ⟶ X'` scheme points
and `h : T' ⟶ T` with `v ≫ g = u ∘ h`.  The fibre `𝐏(g^*ℰ)_{T'}` over `v` is identified with
`𝐏((v^*g^*ℰ)_Zar)` and the fibre `𝐏(ℰ)_T` over `u` with `𝐏((u^*ℰ)_Zar)` (Stacks 084B, 01OB).  This
file proves that, through these identifications, the comparison of fibres
`𝐏(g^*ℰ)_{T'} ⟶ 𝐏(ℰ)_T` is the base-change morphism of projective bundles of Tag 01O3 along `h`
and `(v^*g^*ℰ)_Zar ≅ h^*(u^*ℰ)_Zar`.  Both morphisms into `𝐏((u^*ℰ)_Zar)` carry the same invertible
quotient (the uniqueness half of Tag 01O4).

## Main results

* `AlgebraicGeometry.Space.pointTwoSpaceCompIso_eq_pointCompIso`: the identification
  `(u ∘ h ∘ f')^*ℰ ≅ (v ∘ f')^* g^*ℰ` is the comparison of Stacks 03LU at the point `v ∘ f'`.
* `pointFibreProjectiveBundleIso_hom_comp_projectiveBundleBaseChange_twoSpace`: the comparison
  of fibres is the base change of projective bundles.

## References

* [Stacks Project, Tag 0B4I](https://stacks.math.columbia.edu/tag/0B4I)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)

## Parts

* `FibreSections`
* `FibreQuotients`
* `FibreQuotientTransport`
* `BaseChange`
-/
