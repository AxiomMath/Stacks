module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedPieceTargetDegreewise
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedPieceConcentration
public import StacksFrontier.Algebra.Homology.IsoOfGE
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AbelianOfSmallSite

/-!
# Section 0FMK at the level of complexes, from the cut and the squares

[Stacks, Section 0FMK] identifies the `k`-th graded piece of the filtration of `Ω^•_{X/S}` by the
forms pulled back from `Y` with

`gr^kΩ^•_{X/S}  ≅  f^{-1}Ω^k_{Y/S}[-k] ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y}`

for `f` smooth. **This file assembles that isomorphism of complexes from the degreewise one**,
by `CochainComplex.isoOfGE`: both sides vanish below the cut
(`Stacks.DeRhamSmooth.isZero_gradedPiece_X` and
`Stacks.DeRhamSmooth.isZero_gradedTargetComplex_X`), and in every degree `k + 1 + m` with
`m : ℕ` the comparison is `Stacks.DeRhamSmooth.gradedPieceXIsoGradedTargetX`. The comparison `e₀`
in the degree `k` of the cut and the squares `he` against the differentials are hypotheses.

## Main definitions

* `Stacks.DeRhamSmooth.gradedPieceXIsoGradedTargetXFromCut`: the degreewise comparison in every
  degree `≥ k`, the degree `k` taken as an input and every higher degree supplied by
  `Stacks.DeRhamSmooth.gradedPieceXIsoGradedTargetX`.
* `Stacks.DeRhamSmooth.gradedPieceIsoGradedTargetComplex`: **the isomorphism of complexes**,
  granted the comparison at the cut and the squares.

## Implementation notes

The degree is matched by substituting the degree variable of
`CochainComplex.isoOfGE`'s hypothesis away, rather than by transporting a comparison along an
equality of degrees. That hypothesis is stated with a degree binder and an equation precisely so
that this is possible, and it is why no `eqToHom` appears in the comparison this file builds: at
these binders a square carrying one stops matching the generic square, since `eqToHom` reduces to
an identity but `𝟙 ≫ h = h` is not definitional.

## References

* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.DeRhamDirectImage

attribute [local instance 2000] HasDerivedCategory.standard

universe u

namespace Stacks.DeRhamSmooth

attribute [local instance] Stacks.SheafOfModules.abelianOfSmallSite

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **The degreewise comparison of Section 0FMK in every degree `≥ k`**, with the degree `k` of
the cut taken as an input `e₀`.

Above the cut every degree is `k + 1 + m` with `m : ℕ` and the comparison is
`Stacks.DeRhamSmooth.gradedPieceXIsoGradedTargetX`; at the cut it is `e₀`. -/
def gradedPieceXIsoGradedTargetXFromCut [Smooth f] (k : ℕ)
    (e₀ : (gradedPiece (inverseImageBase (f ≫ g)) (k : ℤ) (deRhamSmoothFiltration f g)).X (k : ℤ) ≅
      (gradedTargetComplex f g k).X (k : ℤ)) :
    ∀ (m : ℕ) (p : ℤ), (k : ℤ) + (m : ℤ) = p →
      ((gradedPiece (inverseImageBase (f ≫ g)) (k : ℤ) (deRhamSmoothFiltration f g)).X p ≅
        (gradedTargetComplex f g k).X p)
  | 0, p, hp => by
      obtain rfl : ((k : ℕ) : ℤ) = p := by push_cast at hp ⊢; omega
      exact e₀
  | (j + 1), p, hp => by
      obtain rfl : ((k + 1 + j : ℕ) : ℤ) = p := by push_cast at hp ⊢; omega
      exact gradedPieceXIsoGradedTargetX f g k j

/-- **Stacks Project, Section 0FMK, at the level of complexes.** For `f : X ⟶ Y` smooth over a
base `S` and a cut `k`,

`gr^kΩ^•_{X/S}  ≅  f^{-1}Ω^k_{Y/S}[-k] ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y}`,

granted the comparison `e₀` in the degree `k` of the cut and the squares `he` against the
differentials. Smoothness of `f` is the only hypothesis on `f`, and it is the hypothesis of
Section 0FMK. -/
def gradedPieceIsoGradedTargetComplex [Smooth f] (k : ℕ)
    (e₀ : (gradedPiece (inverseImageBase (f ≫ g)) (k : ℤ) (deRhamSmoothFiltration f g)).X (k : ℤ) ≅
      (gradedTargetComplex f g k).X (k : ℤ))
    (he : ∀ (m : ℕ) (p q : ℤ) (hp : (k : ℤ) + (m : ℤ) = p)
        (hq : (k : ℤ) + ((m + 1 : ℕ) : ℤ) = q),
      (gradedPieceXIsoGradedTargetXFromCut f g k e₀ m p hp).hom ≫
          (gradedTargetComplex f g k).d p q =
        (gradedPiece (inverseImageBase (f ≫ g)) (k : ℤ) (deRhamSmoothFiltration f g)).d p q ≫
          (gradedPieceXIsoGradedTargetXFromCut f g k e₀ (m + 1) q hq).hom) :
    gradedPiece (inverseImageBase (f ≫ g)) (k : ℤ) (deRhamSmoothFiltration f g) ≅
      gradedTargetComplex f g k :=
  CochainComplex.isoOfGE _ _ (k : ℤ)
    (fun p hp => isZero_gradedPiece_X f g (k : ℤ) p hp)
    (fun p hp => isZero_gradedTargetComplex_X f g k p hp)
    (gradedPieceXIsoGradedTargetXFromCut f g k e₀) he

end Stacks.DeRhamSmooth

end
