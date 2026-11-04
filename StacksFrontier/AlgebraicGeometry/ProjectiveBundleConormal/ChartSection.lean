module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartTransport
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.SectionPreimage

/-!
# A section of the projective bundle, read on a chart

`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartTransport` identifies the part of
`𝐏(ℰ)` lying over an affine open `W` of the base with the absolute `Proj(Sym_A M)`, for
`A = Γ(X, W)` and `M = Γ(ℰ, W)`, and computes the tautological map there. Everything it says is
about that chart; nothing in it mentions a section `σ` of the projection `π : 𝐏(ℰ) ⟶ X`. **This
file crosses the gap**, producing from `σ` a morphism

  `σ|_W : W ⟶ Proj(Sym_A M)`

together with its defining factorization. A section of `π` lands over `W` exactly on `W` — that
is `Stacks.ProjectiveBundleConormal.preimage_toBase_preimage` — so `σ` restricts to the part of
the bundle over `W`, and the chart identification carries that restriction to the absolute `Proj`.

This is the form in which a statement about `Proj(Sym_A M)` becomes a statement about `σ`. In
particular `Stacks.ProjectiveBundleConormal.preimage_basicOpen_eq_top` applies to it: a frame
section `s` of `ℰ` over `W` cuts out the standard open `D₊(ι s)`, and
`Stacks.ProjectiveBundleConormal.chartSection` is the morphism whose factorization through it
`Stacks.ProjectiveBundleConormal.liftSplitChart` turns into a point of the affine bundle, where
`Stacks.ProjectiveBundleConormal.eq_of_comp_splitChartMap_eq` compares it with the zero section.

## Main definitions

* `Stacks.ProjectiveBundleConormal.restrictSectionOver`: `σ` restricted to a morphism
  `W ⟶ (π⁻¹W)`, which is possible because `σ⁻¹(π⁻¹W) = W`.
* `Stacks.ProjectiveBundleConormal.chartSection`: **`σ` read on the chart**, a morphism
  `W ⟶ Proj(Sym_A M)`.

## Main results

* `Stacks.ProjectiveBundleConormal.bundleOverIso_hom_comp_ι` and
  `Stacks.ProjectiveBundleConormal.bundleOverIso_inv_comp_chartMap`: the chart identification
  `Stacks.ProjectiveBundleConormal.bundleOverIso` is the chart, i.e. it composes with the
  inclusion of `π⁻¹W` to give `Stacks.ProjectiveBundleConormal.chartMap`.
* `Stacks.ProjectiveBundleConormal.chartSection_comp_chartMap`: **the defining factorization**,
  `σ|_W ≫ chartMap = W.ι ≫ σ`. Since `chartMap` is a monomorphism this determines `σ|_W`, and it
  is how any identity proved on the chart is transported to `σ`.

## Implementation notes

The restriction is `AlgebraicGeometry.Scheme.Hom.resLE` and not a hand-built factorization through
an open immersion: `AlgebraicGeometry.Scheme.Hom.resLE_comp_ι` is already the factorization, so
`Stacks.ProjectiveBundleConormal.restrictSectionOver_comp_ι` is that lemma and nothing else.

`Stacks.ProjectiveBundleConormal.bundleOverIso` is built as
`Scheme.Hom.isoOpensRange ≪≫ Scheme.isoOfEq`, and each factor is pinned in Mathlib by
`AlgebraicGeometry.Scheme.Hom.isoOpensRange_hom_ι` and
`AlgebraicGeometry.Scheme.isoOfEq_hom_ι`; the composite is their composition, written in term mode
rather than by `rw`, which is the discipline the rest of this directory follows at a composite of
isomorphisms.

**The quasi-coherence witness is `Stacks.ProjectiveBundleConormal.symPieces E`, not a variable.**
The chart material of `ChartTransport` is stated for an arbitrary `hqc : IsQuasicoherentPieces E`,
but `Stacks.ProjectiveBundleConormal.bundle` — the bundle a section is a section *of* — is
`relativeProj (schemeSheafGradedAlgebra E (symPieces E))` by definition, so the two statements
mentioning `σ` are instantiated there and no transport between witnesses is needed.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01OA](https://stacks.math.columbia.edu/tag/01OA)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.ProjectiveBundleSplitting
open Stacks.SymGraded

universe u

namespace Stacks.ProjectiveBundleConormal

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]
  (hqc : IsQuasicoherentPieces E) {W : X.Opens} (hW : IsAffineOpen W)

/-- **The chart identification is the chart.** Composing `bundleOverIso` with the inclusion of
`π⁻¹W` gives `Stacks.ProjectiveBundleConormal.chartMap`, each of its two factors being pinned by
`AlgebraicGeometry.Scheme.Hom.isoOpensRange_hom_ι` and `AlgebraicGeometry.Scheme.isoOfEq_hom_ι`. -/
theorem bundleOverIso_hom_comp_ι :
    (bundleOverIso E hqc hW).hom ≫
        ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ W).ι =
      chartMap E hqc hW :=
  ((Category.assoc _ _ _).trans
    (congrArg (fun g => (chartMap E hqc hW).isoOpensRange.hom ≫ g)
      (Scheme.isoOfEq_hom_ι _ (opensRange_chartMap E hqc hW)))).trans
    (Scheme.Hom.isoOpensRange_hom_ι (chartMap E hqc hW))

/-- **The chart, read backwards through the chart identification, is the inclusion of `π⁻¹W`.**
This is the form `Stacks.ProjectiveBundleConormal.chartSection_comp_chartMap` consumes: it is what
lets the chart be cancelled off a morphism that was transported to the absolute `Proj`. -/
theorem bundleOverIso_inv_comp_chartMap :
    (bundleOverIso E hqc hW).inv ≫ chartMap E hqc hW =
      ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ W).ι :=
  (congrArg (fun g => (bundleOverIso E hqc hW).inv ≫ g)
      (bundleOverIso_hom_comp_ι E hqc hW).symm).trans
    ((bundleOverIso E hqc hW).inv_hom_id_assoc _)

section Section

variable {σ : X ⟶ (bundle E).scheme} (hσ : σ ≫ (bundle E).toBase = 𝟙 X)

include hσ in
/-- **A section of `π` meets the part of the bundle over `W` on all of `W`.** This is the half of
`Stacks.ProjectiveBundleConormal.preimage_toBase_preimage` that
`AlgebraicGeometry.Scheme.Hom.resLE` asks for. -/
theorem le_preimage_toBase_preimage :
    W ≤ σ ⁻¹ᵁ ((bundle E).toBase ⁻¹ᵁ W) :=
  (preimage_toBase_preimage E hσ W).ge

include hσ in
/-- **`σ` restricted to the part of the bundle over `W`**, a morphism `W ⟶ (π⁻¹W)`. It exists
because a section meets `π⁻¹W` in exactly `W`. -/
def restrictSectionOver : W.toScheme ⟶ ((bundle E).toBase ⁻¹ᵁ W).toScheme :=
  σ.resLE ((bundle E).toBase ⁻¹ᵁ W) W (le_preimage_toBase_preimage E hσ)

include hσ in
/-- **The restriction is a restriction**: composed with the inclusion of `π⁻¹W` it is `σ` on `W`.
This is `AlgebraicGeometry.Scheme.Hom.resLE_comp_ι`. -/
theorem restrictSectionOver_comp_ι :
    restrictSectionOver E hσ ≫ ((bundle E).toBase ⁻¹ᵁ W).ι = W.ι ≫ σ :=
  Scheme.Hom.resLE_comp_ι σ (le_preimage_toBase_preimage E hσ)

include hσ in
/-- **The section `σ` read on the chart**, a morphism `W ⟶ Proj(Sym_{Γ(X,W)} Γ(ℰ, W))`: the
restriction of `σ` to the part of the bundle over `W`, carried to the absolute `Proj` by the chart
identification `Stacks.ProjectiveBundleConormal.bundleOverIso`.

Every statement about `Proj(Sym_A M)` that clause 3 of [Stacks, Tag 0B3V] needs about `σ` — that
it lands in the standard open `D₊(ι s)` of a frame section, and that the resulting point of the
affine bundle is the zero section — is a statement about this morphism. -/
def chartSection : W.toScheme ⟶ AlgebraicGeometry.Proj (SymmetricAlgebra.grading Γ(X, W) Γ(E, W)) :=
  restrictSectionOver E hσ ≫ (bundleOverIso E (symPieces E) hW).inv

include hσ in
/-- **The defining factorization of the chart section**: `σ|_W ≫ chartMap = W.ι ≫ σ`. The chart
is a monomorphism, so this determines `Stacks.ProjectiveBundleConormal.chartSection`, and it is
the identity along which a computation carried out on `Proj(Sym_A M)` — for instance
`Stacks.ProjectiveBundleConormal.chartTwistIso_hom_pullbackSection` — is transported to `σ`. -/
theorem chartSection_comp_chartMap :
    chartSection E hW hσ ≫ chartMap E (symPieces E) hW = W.ι ≫ σ :=
  ((Category.assoc _ _ _).trans
    (congrArg (fun g => restrictSectionOver E hσ ≫ g)
      (bundleOverIso_inv_comp_chartMap E (symPieces E) hW))).trans
    (restrictSectionOver_comp_ι E hσ)

end Section

end Stacks.ProjectiveBundleConormal

end
