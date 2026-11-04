module

public import StacksFrontier.Cotangent.AtiyahClassSmallSiteFirstVertexDerived
import StacksCore.Tactic.StacksAttribute

/-!
# The displayed Atiyah triangle on the small model of the restricted site

[Stacks, Tag 09DD] displays its triangle with both endpoints identified:

`L_{B/A} ⊗^𝐋_B M ⟶ Lπ_!(P¹_{𝒪/A}(M)) ⟶ M ⟶ (L_{B/A} ⊗^𝐋_B M)[1]`,

and [Tag 09DE] calls the last arrow the *Atiyah class* of `M`. On the small model of the
`κ`-bounded full subcategory of `C_{B/A}` both identifications are theorems of this tree —
`CommAlgCat.nonempty_smallAtiyahFirstVertexDerivedTensorIso` for the first term and
`CommAlgCat.smallPolynomialAtiyahTriangleObj₃Iso` for the third — so the displayed triangle can
be stated with nothing assumed. That is what this file does.

The identification of the first term is available as a `Nonempty`, the choice of a K-flat
resolution inside `CommAlgCat.nonempty_cotangentComplexDerivedTensorModule_iso` being
non-canonical, so the displayed triangle is stated existentially in that identification;
membership in `CategoryTheory.Pretriangulated.distinguishedTriangles` is a `Prop`, so nothing is
lost. The identification of the third term is canonical and is named outright.

## Main results

* `CommAlgCat.exists_smallAtiyahDisplayedTriangle_distinguished`: the displayed triangle of
  [Stacks, Tag 09DD], with its first term `L_{B/A} ⊗^𝐋_B M` and its third term `M`, is
  distinguished **on the small model of the footnote-restricted site**.
* `CommAlgCat.exists_smallAtiyahDisplayedClass_mem_distinguished`: the Atiyah class of `M`,
  `M ⟶ (L_{B/A} ⊗^𝐋_B M)[1]`, is the last arrow of that triangle, again **on that model**.

## Implementation notes

**Why neither 09DD nor 09DE is registered here.** Both statements below are about the small model
`CommAlgCat.smallBoundedPolynomialSite A B κ` of the `κ`-bounded full subcategory of `C_{B/A}`,
not about `C_{B/A}` itself, and that is a special case of the tag twice over: restricting to a
full subcategory of bounded-cardinality augmentations changes both `Mod(B̲)` and `Lπ_!`, and the
module `M` here ranges over `ModuleCat.{u} B` rather than over the
`ModuleCat.{u + 1} (ULift B)` of the site's own ringed point
`CommAlgCat.polynomialRingedPoint`. Both tags are therefore registered at the site `C_{B/A}`
itself, in `StacksFrontier/Cotangent/AtiyahClassBigSiteDisplayed.lean`, where both endpoint
identifications are proved as well: 09DD on
`CommAlgCat.exists_atiyahDisplayedTriangle_distinguished`, the displayed triangle, and 09DE on
`CommAlgCat.exists_atiyahDisplayedClass_mem_distinguished`, its last arrow — the Atiyah class.

Nothing transports between the two, in either direction. The inclusion of the small model into
the unrestricted site is only fully faithful
(`CommAlgCat.fullyFaithfulSmallBoundedPolynomialSiteToPolynomialSite`,
`StacksFrontier/Cotangent/PolynomialAlgebraSiteSmall.lean:240`), not an equivalence — it is the
*restricted* site of the source's footnote that is essentially small at `u`
(`CommAlgCat.essentiallySmall_boundedPolynomialSite`, ibid.`:227`, through
`CommAlgCat.boundedPolynomialSiteEquiv`, ibid.`:215`), while the unrestricted site is not — and
`Stacks.CategoryHomology.totalDerivedColimitEquivalenceIso` would need an equivalence; and the
two universes of `M` make the statement at `C_{B/A}` strictly the wider one. So the statements
below are kept as the small-model record of the same mathematics, untagged. The declarations and
their proofs are unchanged; only the tag attributes have come off them.

## References

* [Stacks Project, Tag 09DD](https://stacks.math.columbia.edu/tag/09DD)
* [Stacks Project, Tag 09DE](https://stacks.math.columbia.edu/tag/09DE)
* [Stacks Project, Tag 08PT](https://stacks.math.columbia.edu/tag/08PT)
* [Stacks Project, Tag 08QE](https://stacks.math.columbia.edu/tag/08QE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace CommAlgCat

attribute [local instance 2000] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) (M : ModuleCat.{u} (B : Type u))

/-- **`L_{B/A} ⊗^𝐋_B M`**, the first term of the triangle as [Stacks, Tag 09DD] displays it. -/
abbrev smallAtiyahDisplayedObj₁ : DerivedCategory (ModuleCat.{u} (B : Type u)) :=
  ((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor (B : Type u)).obj
      (DerivedCategory.Q.obj (cotangentComplex.{u, u} A B))).obj
    (DerivedCategory.Q.obj (moduleSingleComplex A B M))

/-- **The displayed triangle of [Stacks, Tag 09DD] on the small model of the
footnote-restricted site.** For a `B`-module `M` there is an identification `e₁` of the first
term of the Atiyah triangle on that model with `L_{B/A} ⊗^𝐋_B M` for which

`L_{B/A} ⊗^𝐋_B M ⟶ Lπ_!(P¹_{𝒪/A}(M)) ⟶ M ⟶ (L_{B/A} ⊗^𝐋_B M)[1]`

is a distinguished triangle, the third term being identified with `M` by the canonical
`CommAlgCat.smallPolynomialAtiyahTriangleObj₃Iso`.

Nothing is assumed: the first identification is
`CommAlgCat.nonempty_smallAtiyahFirstVertexDerivedTensorIso`, the chain of [Stacks, Tag 08PT] and
[Tag 08PU] ending in `CommAlgCat.nonempty_smallAtiyahMooreDerivedTensorIso`, and the third is
[Tag 08QE] through `Stacks.ChaoticSite.derivedColimitWithCoefficientsRestrictScalarsIso`. It is
`e₁` that is existentially quantified rather than named, because the K-flat resolution computing
the derived tensor product is chosen and not canonical.

This is *not* Tag 09DD: the site is the small model of the `κ`-bounded full subcategory of
`C_{B/A}` rather than `C_{B/A}`, which changes both `Mod(B̲)` and `Lπ_!`, and the module ranges
over `ModuleCat.{u} B` rather than over the `ModuleCat.{u + 1} (ULift B)` of the site's own
ringed point. The tag is `CommAlgCat.exists_atiyahDisplayedTriangle_distinguished`
(`StacksFrontier/Cotangent/AtiyahClassBigSiteDisplayed.lean`), at the site itself; the module
documentation above records why neither statement transports to the other. -/
theorem exists_smallAtiyahDisplayedTriangle_distinguished :
    ∃ e₁ : (smallPolynomialAtiyahTriangle A B (standardResolutionVarCardinal A B) M).obj₁ ≅
        smallAtiyahDisplayedObj₁ A B M,
      Triangle.mk
          (e₁.inv ≫
            (smallPolynomialAtiyahTriangle A B (standardResolutionVarCardinal A B) M).mor₁)
          ((smallPolynomialAtiyahTriangle A B (standardResolutionVarCardinal A B) M).mor₂ ≫
            (smallPolynomialAtiyahTriangleObj₃Iso A B M).hom)
          ((smallPolynomialAtiyahTriangleObj₃Iso A B M).inv ≫
            (smallPolynomialAtiyahTriangle A B (standardResolutionVarCardinal A B) M).mor₃ ≫
              (shiftFunctor (DerivedCategory (ModuleCat.{u} (B : Type u)))
                (1 : ℤ)).map e₁.hom) ∈
        distinguishedTriangles := by
  obtain ⟨e₁⟩ := nonempty_smallAtiyahFirstVertexDerivedTensorIso A B M
  exact ⟨e₁, Stacks.Atiyah.triangle_distinguished_of_iso _ _ _ _ _ _ e₁
    (smallPolynomialAtiyahTriangleObj₃Iso A B M)⟩

/-- **The Atiyah class on the small model of the footnote-restricted site.** The arrow
`M ⟶ (L_{B/A} ⊗^𝐋_B M)[1]` obtained from the last arrow
`CommAlgCat.smallPolynomialAtiyahClass` of the Atiyah triangle by the two endpoint
identifications is the last arrow of the displayed distinguished triangle of
[Stacks, Tag 09DD].

This is `CommAlgCat.exists_smallAtiyahDisplayedTriangle_distinguished` with the third arrow
written through `CommAlgCat.smallPolynomialAtiyahClass`, which is the same arrow: the Atiyah
class is by definition `mor₃` of the triangle. Both identifications are proved, so no hypothesis
of the kind carried by `CommAlgCat.polynomialAtiyahClassOfIso` on the unrestricted site appears
here.

This is *not* Tag 09DE, for the reason the triangle above is not Tag 09DD: the site is the small
model of the `κ`-bounded full subcategory of `C_{B/A}` rather than `C_{B/A}`, which changes both
`Mod(B̲)` and `Lπ_!`, and the module ranges over `ModuleCat.{u} B` rather than over the
`ModuleCat.{u + 1} (ULift B)` of the site's own ringed point. The tag is
`CommAlgCat.exists_atiyahDisplayedClass_mem_distinguished`
(`StacksFrontier/Cotangent/AtiyahClassBigSiteDisplayed.lean`), which names the Atiyah class at the
site itself; the module documentation above records why neither statement transports to the
other. -/
theorem exists_smallAtiyahDisplayedClass_mem_distinguished :
    ∃ e₁ : (smallPolynomialAtiyahTriangle A B (standardResolutionVarCardinal A B) M).obj₁ ≅
        smallAtiyahDisplayedObj₁ A B M,
      Triangle.mk
          (e₁.inv ≫
            (smallPolynomialAtiyahTriangle A B (standardResolutionVarCardinal A B) M).mor₁)
          ((smallPolynomialAtiyahTriangle A B (standardResolutionVarCardinal A B) M).mor₂ ≫
            (smallPolynomialAtiyahTriangleObj₃Iso A B M).hom)
          ((smallPolynomialAtiyahTriangleObj₃Iso A B M).inv ≫
            smallPolynomialAtiyahClass A B (standardResolutionVarCardinal A B) M ≫
              (shiftFunctor (DerivedCategory (ModuleCat.{u} (B : Type u)))
                (1 : ℤ)).map e₁.hom) ∈
        distinguishedTriangles :=
  exists_smallAtiyahDisplayedTriangle_distinguished A B M

end CommAlgCat

end
