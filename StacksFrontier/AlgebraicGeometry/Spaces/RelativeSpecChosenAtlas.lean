module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeAlgebraRelativeSpecSize
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInQcqs

/-!
# The relative spectrum of a quasi-coherent algebra with bounded chart sections

Let `W` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let `A` be
a quasi-coherent sheaf of commutative `𝒪_W`-algebras on its small étale site. The relative
spectrum `π : \underline{Spec}_W(A) ⟶ W` of Stacks 081W is the algebraic space affine over `W`
with `π_* 𝒪 = A`. It is the quotient of the étale equivalence relation of the scheme-level
relative spectra of `A` over the surjective étale atlas of `W` and its kernel pair
(`AlgebraicGeometry.Space.chosenAtlasPairFst` and `AlgebraicGeometry.Space.chosenAtlasPairSnd`),
provided **the sections of `A` over the étale charts cut out by the affine opens of each chart's
scheme are bounded by one cardinal below the cutoff**, chart by chart; this condition puts every
chart object of the construction in the site.

## Main definitions

* `AlgebraicGeometry.Space.HasBoundedChartSections`: the size condition above.
* `AlgebraicGeometry.Space.relativeSpecOfBounded`: **the relative spectrum
  `\underline{Spec}_W(A)`**, as an algebraic space affine over `W`.
* `AlgebraicGeometry.Space.relativeSpecOfBoundedPushforwardIso`: **`π_* 𝒪 ≅ A`** as sheaves of
  commutative `𝒪_W`-algebras.

## Main results

* `AlgebraicGeometry.Space.contains_chartRelativeSpec_of_hasBoundedChartSections`: the size
  condition puts every chart object of the construction in the site.
* `AlgebraicGeometry.Space.isAffineHom_relativeSpecOfBounded`: the structure morphism is affine.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (W : AlgebraicSpaces B S hS) (A : AlgebraSheaf.{u, u} B S hS W.1 W.2)

/-- **The sections of an algebra sheaf are bounded chart by chart**: for every étale chart `V` of
`W` there is one cardinal below the cutoff bounding the sections of `A` over the étale charts cut
out by all the affine opens of the scheme of `V`. -/
def HasBoundedChartSections : Prop :=
  ∀ V : SmallEtale B S hS W.1, ∃ c < B.cutoff, ∀ O : (chartScheme V).affineOpens,
    #(A.right.obj.obj (op (openChart B S hS W.1 V (O : (chartScheme V).Opens)))) ≤ c

variable {B S hS W A}

/-- **Bounded chart sections put every chart object of the relative spectrum in the site.** -/
theorem contains_chartRelativeSpec_of_hasBoundedChartSections (hA : A.IsQuasicoherent)
    (hb : HasBoundedChartSections B S hS W A) (V : SmallEtale B S hS W.1) :
    B.Contains (chartRelativeSpec B S hS W A hA V) := by
  obtain ⟨c, hc, hcO⟩ := hb V
  have hV : (chartScheme V).size < B.cutoff := SmallEtale.contains_chartScheme B S hS W.1 V
  exact contains_chartRelativeSpec_of_lt_cutoff B S hS W A hA V (max_lt hV hc)
    (le_max_left _ _) fun O => (hcO O).trans (le_max_right _ _)

variable (B S hS W A)

/-- **The relative spectrum `π : \underline{Spec}_W(A) ⟶ W` of a quasi-coherent algebra with
bounded chart sections, as an algebraic space affine over `W`** (Stacks 081W): the quotient of
the étale equivalence relation of the relative spectra of `A` over the chosen atlas of `W` and its
kernel pair, with the morphism to `W` they descend to. -/
def relativeSpecOfBounded (hA : A.IsQuasicoherent) (hb : HasBoundedChartSections B S hS W A) :
    AffineOver B S hS W :=
  ⟨Over.mk (chartRelativeSpecQuotientHom B S hS W A hA (chosenAtlasPairFst B S hS W)
      (chosenAtlasPairSnd B S hS W) (isPullback_chosenAtlasPair B S hS W)
      (contains_chartRelativeSpec_of_hasBoundedChartSections hA hb _)
      (contains_chartRelativeSpec_of_hasBoundedChartSections hA hb _)
      (contains_chartRelativeSpec_of_hasBoundedChartSections hA hb _)),
    isAffineHom_chartRelativeSpecQuotientHom B S hS W A hA _ _
      (isPullback_chosenAtlasPair B S hS W) (surjective_chosenAtlasPairTarget B S hS W) _ _ _⟩

/-- **The structure morphism of the relative spectrum is affine.** -/
theorem isAffineHom_relativeSpecOfBounded (hA : A.IsQuasicoherent)
    (hb : HasBoundedChartSections B S hS W A) :
    IsAffineHom B S hS (relativeSpecOfBounded B S hS W A hA hb).obj.hom.hom :=
  (relativeSpecOfBounded B S hS W A hA hb).property

/-- **`π_* 𝒪_{\underline{Spec}_W(A)} ≅ A`** as sheaves of commutative `𝒪_W`-algebras on the small
étale site of `W`. -/
def relativeSpecOfBoundedPushforwardIso (hA : A.IsQuasicoherent)
    (hb : HasBoundedChartSections B S hS W A) :
    pushforwardAlgebra B S hS (relativeSpecOfBounded B S hS W A hA hb).obj ≅ A :=
  (chartRelativeSpecQuotientPushforwardIso B S hS W A hA _ _
    (isPullback_chosenAtlasPair B S hS W) (surjective_chosenAtlasPairTarget B S hS W) _ _ _
    (contains_chartRelativeSpec_of_hasBoundedChartSections hA hb)).symm

end AlgebraicGeometry.Space

end
