module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.PositiveRankSurjectivity
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ProjectiveLineIntegral

/-!
# The two affine lines over a scheme agree

The Chow chapter of this development carries the affine line over a scheme `S` as
`Stacks.Chow.affineLineOver S`, the base change of the coordinate chart of `ℙ¹_ℤ`, which is built
from the *univariate* polynomial ring `ℤ[T]`. Stacks 02TT is stated with Mathlib's affine space
`𝔸(ULift (Fin 1); S)`, which is built from `MvPolynomial (ULift (Fin 1)) ℤ`. The two are the same
scheme over `S`, and this file supplies the identification.

`Stacks.Chow.affineLineOverIsoAffineSpace` already identifies `affineLineOver S` with affine space
indexed by `PUnit`; what is added here is the reindexing to the index type `ULift (Fin 1)` in
which the affine-space bundle of Stacks 02TT is phrased, together with the statement that the
identification is one of schemes over `S`.

## Main definitions

* `Stacks.Chow.affineLineOverIsoAffineLine` — `affineLineOver S ≅ 𝔸(ULift (Fin 1); S)`.

## Main results

* `Stacks.Chow.affineLineOverIsoAffineLine_hom_over` — the identification is one of schemes
  over `S`.

## References

* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
* [Stacks Project, Tag 01M0](https://stacks.math.columbia.edu/tag/01M0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- `PUnit` and `ULift (Fin 1)` both index a single variable, so they index the same affine
line. -/
def punitEquivULiftFinOne : PUnit.{u + 1} ≃ ULift.{u} (Fin 1) :=
  (Equiv.equivPUnit (ULift.{u} (Fin 1))).symm

/-- `Stacks.Chow.affineLineOverIsoAffineSpace` with Mathlib's affine space as its target: the
pullback it names is by construction `𝔸(PUnit; S)`. -/
def affineLineOverIsoAffineSpacePUnit (S : Scheme.{u}) :
    affineLineOver S ≅ 𝔸(PUnit.{u + 1}; S) :=
  affineLineOverIsoAffineSpace S

/-- The `PUnit`-indexed identification is one of schemes over `S`. -/
theorem affineLineOverIsoAffineSpacePUnit_hom_over (S : Scheme.{u}) :
    (affineLineOverIsoAffineSpacePUnit S).hom ≫ (𝔸(PUnit.{u + 1}; S) ↘ S) =
      pullback.fst (terminal.from S)
        (terminal.from (Spec (CommRingCat.of (Polynomial (ULift.{u} ℤ))))) :=
  toAffineSpace_fst S

/-- **The affine line of the Chow chapter is Mathlib's affine line.** The scheme
`Stacks.Chow.affineLineOver S`, built from the univariate polynomial ring `ℤ[T]`, is affine space
over `S` on the index type `ULift (Fin 1)`, which is how the affine-space bundles of Stacks 02TT
are written. -/
def affineLineOverIsoAffineLine (S : Scheme.{u}) :
    affineLineOver S ≅ 𝔸(ULift.{u} (Fin 1); S) :=
  affineLineOverIsoAffineSpacePUnit S ≪≫ affineSpaceReindexIso punitEquivULiftFinOne.{u} S

/-- The identification of the two affine lines over `S` is one of schemes over `S`: it carries
the structure morphism of `𝔸(ULift (Fin 1); S)` back to the first pullback projection, which is
the structure morphism of `Stacks.Chow.affineLineOver S`. -/
theorem affineLineOverIsoAffineLine_hom_over (S : Scheme.{u}) :
    (affineLineOverIsoAffineLine S).hom ≫ (𝔸(ULift.{u} (Fin 1); S) ↘ S) =
      pullback.fst (terminal.from S)
        (terminal.from (Spec (CommRingCat.of (Polynomial (ULift.{u} ℤ))))) := by
  rw [affineLineOverIsoAffineLine, Iso.trans_hom, Category.assoc,
    affineSpaceReindexIso_hom_over]
  exact affineLineOverIsoAffineSpacePUnit_hom_over S

end Stacks.Chow

end
