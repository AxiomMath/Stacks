module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionSmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationChangeOfBaseQuantifier
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningSeparationConverse

/-!
# Clauses (5) and (6) of Stacks 0BPW at the absolute separation axioms

Let `𝒳 ⊂ 𝒳'` be a thickening of algebraic stacks over a scheme `S`. Clauses (5) and (6) of
**Stacks 0BPW** say that `𝒳` is separated, respectively quasi-separated, if and only if `𝒳'` is.
"Separated" and "quasi-separated" are the absolute notions of **Stacks 050D**, parts (7) and (8):
the separation axioms over `Spec(ℤ)`, after viewing the stacks over `Spec(ℤ)` by **Stacks 04X6**.

The forms over the base scheme `S`, parts (3) and (4) of Stacks 050D, are
`AlgebraicGeometry.Stack.isSeparatedOver_iff_isThickening` and
`AlgebraicGeometry.Stack.isQuasiSeparatedOver_iff_isThickening`. This file reads them at the base
`Spec(ℤ)`, which needs the thickening itself to survive the viewing: a thickening of algebraic
stacks over `S`, viewed over a larger base `S'` by Construction A of **Stacks 04X5**, is again a
thickening.

## Main results

* `AlgebraicGeometry.Stack.isClosedImmersion_changeBaseHom_iff`: the closed-immersion condition of
  Stacks 04XB is unchanged by Construction A.
* `AlgebraicGeometry.Stack.isThickening_changeBaseHomAlgebraicStacks`: a thickening of algebraic
  stacks, viewed over a larger base by Stacks 04X6, is a thickening.
* `AlgebraicGeometry.Stack.isSeparatedAbs_iff_isThickening`: **Stacks 0BPW, clause (5)**.
* `AlgebraicGeometry.Stack.isQuasiSeparatedAbs_iff_isThickening`: **Stacks 0BPW, clause (6)**.

## Implementation notes

A thickening is a closed immersion in the sense of Stacks 04YL which is surjective on points.
Representability by algebraic spaces is unchanged by Construction A
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_changeBaseFunctor_iff`); the
closed-immersion condition of Stacks 04XB quantifies over scheme-valued points of the target and
over the algebraic spaces representing the base changes, and those match up exactly as for
quasi-compactness in `AlgebraicGeometry.Stack.isQuasiCompact_changeBaseHom_iff`, leaving
`AlgebraicGeometry.Space.isClosedImmersion_spacesOverSmallerBaseFunctor_iff`; surjectivity on
points is surjectivity on objects in the sense of Stacks 06D4
(`AlgebraicGeometry.Stack.pointsMap_surjective_of_isSurjectiveOnObjects` and its converse), which
`AlgebraicGeometry.Stack.isSurjectiveOnObjects_changeBaseHom_iff` transfers.

## References

* [Stacks Project, Tag 04X5](https://stacks.math.columbia.edu/tag/04X5)
* [Stacks Project, Tag 04X6](https://stacks.math.columbia.edu/tag/04X6)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 06D4](https://stacks.math.columbia.edu/tag/06D4)
* [Stacks Project, Tag 0BPP](https://stacks.math.columbia.edu/tag/0BPP)
* [Stacks Project, Tag 0BPW](https://stacks.math.columbia.edu/tag/0BPW)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w w'

section ChangeOfBase

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')

/-- **The closed-immersion condition of Stacks 04XB is unchanged by Construction A.** A
1-morphism of categories fibred in groupoids over the big fppf site of `S` is a closed immersion
in the relative sense of Stacks 04XB exactly when the 1-morphism over the big fppf site of `S'`
produced by Construction A is one. The argument of
`AlgebraicGeometry.Stack.isQuasiCompact_changeBaseHom_iff` with
`AlgebraicGeometry.Space.isClosedImmersion_spacesOverSmallerBaseFunctor_iff` in place of its
space-level ingredient. -/
theorem isClosedImmersion_changeBaseHom_iff
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴) :
    IsClosedImmersion B S' hS' (changeBaseHom B S S' hS hS' g f) ↔
      IsClosedImmersion B S hS f := by
  constructor
  · rintro hbig U y hy F hF ⟨E⟩
    exact (Space.isClosedImmersion_spacesOverSmallerBaseFunctor_iff B U.left.1 S U.left.2 hS
      U.hom S' hS' g (U.hom ≫ g) rfl F hF).1 (hbig ((Over.map g).obj U) y
        (comp_changeBase_p_eq_map B S S' hS hS' g 𝒴.val U y hy) F hF
        ⟨TwoFibreProductOver.unrelocalizeFstEquivalenceOver_trans g hy f.hom.w E⟩)
  · rintro hsmall U' y hy' F hF ⟨E'⟩
    obtain ⟨h₀, hy, hg⟩ := exists_comp_p_eq_map_of_changeBase B S S' hS hS' g 𝒴.val U' y hy'
    rw [← hg, Over.mapComp_eq] at E'
    exact (Space.isClosedImmersion_spacesOverSmallerBaseFunctor_iff B U'.left.1 S U'.left.2
      hS h₀ S' hS' g U'.hom hg F hF).2 (hsmall (Over.mk h₀) y hy F hF
        ⟨TwoFibreProductOver.fstEquivalenceOver_trans g hy f.hom.w E'⟩)

/-- **A thickening of algebraic stacks stays a thickening when the base is enlarged.** If
`i : 𝒳 ⟶ 𝒳'` is a thickening of algebraic stacks over `S` (**Stacks 0BPP**, part (1)), then `i`
viewed as a 1-morphism of algebraic stacks over `S'` by **Stacks 04X6** is a thickening. -/
theorem isThickening_changeBaseHomAlgebraicStacks {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS}
    (i : 𝒳 ⟶ 𝒳') (hi : IsThickening i) :
    IsThickening (changeBaseHomAlgebraicStacks.{u, w, w'} B S S' hS hS' g i) :=
  ⟨⟨(isRepresentableByAlgebraicSpaces_changeBaseFunctor_iff B S S' hS hS' g i.hom.hom).2 hi.1.1,
      (isClosedImmersion_changeBaseHom_iff B S S' hS hS' g i.hom).2 hi.1.2⟩,
    pointsMap_surjective_of_isSurjectiveOnObjects B S' hS' _
      ((isSurjectiveOnObjects_changeBaseHom_iff B S S' hS hS' g i.hom).2
        (isSurjectiveOnObjects_of_pointsMap_surjective B S hS i hi.2))⟩

end ChangeOfBase

section Absolute

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 0BPW, clause (5).** If `𝒳 ⊂ 𝒳'` is a thickening of algebraic stacks over `S` then
`𝒳` is separated if and only if `𝒳'` is — the absolute axiom, part (7) of **Stacks 050D**.

Both sides are separatedness over `Spec(ℤ)` of the stacks viewed by **Stacks 04X6**, and the
thickening viewed over `Spec(ℤ)` is a thickening
(`AlgebraicGeometry.Stack.isThickening_changeBaseHomAlgebraicStacks`), so this is
`AlgebraicGeometry.Stack.isSeparatedOver_iff_isThickening` at the base `Spec(ℤ)`. -/
@[stacks 0BPW "clause (5): separated, the absolute axiom of Stacks 050D part (7)"]
theorem isSeparatedAbs_iff_isThickening (i : 𝒳 ⟶ 𝒳') (hi : IsThickening i) :
    IsSeparatedAbs.{u, w, w'} B S hS 𝒳 ↔ IsSeparatedAbs.{u, w, w'} B S hS 𝒳' :=
  isSeparatedOver_iff_isThickening B _ (contains_specULiftZ B)
    (viewOverIntHom.{u, w, w'} B S hS i)
    (isThickening_changeBaseHomAlgebraicStacks.{u, w, w'} B S _ hS (contains_specULiftZ B)
      (toIntObject B S hS) i hi)

/-- **Stacks 0BPW, clause (6).** If `𝒳 ⊂ 𝒳'` is a thickening of algebraic stacks over `S` then
`𝒳` is quasi-separated if and only if `𝒳'` is — the absolute axiom, part (8) of
**Stacks 050D**.

The companion of `AlgebraicGeometry.Stack.isSeparatedAbs_iff_isThickening` at
`AlgebraicGeometry.Stack.isQuasiSeparatedOver_iff_isThickening`. -/
@[stacks 0BPW "clause (6): quasi-separated, the absolute axiom of Stacks 050D part (8)"]
theorem isQuasiSeparatedAbs_iff_isThickening (i : 𝒳 ⟶ 𝒳') (hi : IsThickening i) :
    IsQuasiSeparatedAbs.{u, w, w'} B S hS 𝒳 ↔ IsQuasiSeparatedAbs.{u, w, w'} B S hS 𝒳' :=
  isQuasiSeparatedOver_iff_isThickening B _ (contains_specULiftZ B)
    (viewOverIntHom.{u, w, w'} B S hS i)
    (isThickening_changeBaseHomAlgebraicStacks.{u, w, w'} B S _ hS (contains_specULiftZ B)
      (toIntObject B S hS) i hi)

end Absolute

end AlgebraicGeometry.Stack

end
