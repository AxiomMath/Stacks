module

public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.QcohPresentation
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyAffineDiagonal

/-!
# Perfect objects are bounded complexes of finite locally free modules

Let `X` be a quasi-compact and quasi-separated scheme with the resolution property.  Every
perfect object of `D(𝒪_X)` is then isomorphic to the image of a bounded complex of finite
locally free `𝒪_X`-modules.  This is [Stacks, Tag 0F8F], and it is the converse of
`Stacks.Perfect.BoundedLocallyFreeComplexes.isPerfect_of_boundedFiniteLocallyFree`, which needs
no hypothesis on `X`.

## Main results

All in the namespace `Stacks.Perfect.BoundedLocallyFreeComplexes`:

* `exists_boundedFiniteLocallyFree_iso_of_affineDiagonal` is the statement for a scheme that is
  moreover assumed to have affine diagonal.
* `exists_boundedFiniteLocallyFree_iso_of_hasResolutionProperty` is [Stacks, Tag 0F8F];
  `exists_boundedFiniteLocallyFree_iso` is the same statement with an additional assumption
  `hstage` that it does not use.

## Implementation notes

The proof is the source's: a perfect object has quasi-coherent cohomology and is bounded below,
so on a scheme with affine diagonal it is represented by a bounded below complex of
quasi-coherent modules by [Stacks, Tag 08DB], and the finite locally free replacement of
[Stacks, Tag 0F8E] applies to that complex.

Affineness of the diagonal is supplied by [Stacks, Tag 0F8C],
`AlgebraicGeometry.HasResolutionProperty.isAffineHom_diagonal`: `X` is affine over a Noetherian
scheme with the resolution property, through the converse of [Stacks, Tag 0F8B] at Noetherian
stages (`AlgebraicGeometry.hasResolutionProperty_stage`).

## References

* [Stacks Project, Tag 0F8F](https://stacks.math.columbia.edu/tag/0F8F)
* [Stacks Project, Tag 0F8C](https://stacks.math.columbia.edu/tag/0F8C)
* [Stacks Project, Tag 0F8E](https://stacks.math.columbia.edu/tag/0F8E)
* [Stacks Project, Tag 08DB](https://stacks.math.columbia.edu/tag/08DB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.PerfectComplexes

universe u

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

attribute [local instance 10000] HasDerivedCategory.standard

/-- **[Stacks, Tag 0F8F] for a scheme with affine diagonal.**  On a quasi-compact and
quasi-separated scheme with the resolution property and affine diagonal, every perfect object of
`D(𝒪_X)` is isomorphic to the image of a bounded complex of finite locally free
`𝒪_X`-modules. -/
theorem exists_boundedFiniteLocallyFree_iso_of_affineDiagonal (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [HasResolutionProperty X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (K : DerivedCategory X.Modules) (hK : IsPerfect (X := X.toRingedSpace) K) :
    ∃ E : CochainComplex X.Modules ℤ, boundedFiniteLocallyFreeComplex X E ∧
      Nonempty (DerivedCategory.Q.obj E ≅ K) := by
  obtain ⟨G, hGplus, hGqc, ⟨eGK⟩⟩ := exists_plus_quasicoherent_representative X K hK
  obtain ⟨E, f, hE, hf⟩ := exists_boundedFiniteLocallyFree_quasiIso X G hGplus hGqc
    (isPerfect_of_iso eGK.symm hK)
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso X.Modules f).2 hf
  exact ⟨E, hE, ⟨asIso (DerivedCategory.Q.map f) ≪≫ eGK⟩⟩

/-- **[Stacks, Tag 0F8F].**  Let `X` be a quasi-compact and quasi-separated scheme with the
resolution property.  Every perfect object of `D(𝒪_X)` is isomorphic to the image of a bounded
complex of finite locally free `𝒪_X`-modules.

The three assumptions on `X` are exactly the source's.  The affine diagonal used in the proof
comes
from [Stacks, Tag 0F8C], `AlgebraicGeometry.HasResolutionProperty.isAffineHom_diagonal`. -/
@[stacks 0F8F]
theorem exists_boundedFiniteLocallyFree_iso_of_hasResolutionProperty (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [HasResolutionProperty X]
    (K : DerivedCategory X.Modules) (hK : IsPerfect (X := X.toRingedSpace) K) :
    ∃ E : CochainComplex X.Modules ℤ, boundedFiniteLocallyFreeComplex X E ∧
      Nonempty (DerivedCategory.Q.obj E ≅ K) :=
  have := HasResolutionProperty.isAffineHom_diagonal X
  exists_boundedFiniteLocallyFree_iso_of_affineDiagonal X K hK

/-- **[Stacks, Tag 0F8F], with an additional assumption `hstage`.**  Let
`X` be a quasi-compact and quasi-separated scheme with the resolution property.  Every perfect
object of `D(𝒪_X)` is isomorphic to the image of a bounded complex of finite locally free
`𝒪_X`-modules.  The assumption `hstage`, the converse of
[Stacks, Tag 0F8B], is not needed:
`exists_boundedFiniteLocallyFree_iso_of_hasResolutionProperty`
states the conclusion without it. -/
theorem exists_boundedFiniteLocallyFree_iso (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [HasResolutionProperty X]
    (hstage : ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : Iᵒᵈ ⥤ Scheme.{u}) (c : Cone D), IsLimit c →
      (∀ {i j : Iᵒᵈ} (g : i ⟶ j), IsAffineHom (D.map g)) →
      (∀ i, CompactSpace (D.obj i)) → (∀ i, QuasiSeparatedSpace (D.obj i)) →
      HasResolutionProperty c.pt → ∃ i, HasResolutionProperty (D.obj i))
    (K : DerivedCategory X.Modules) (hK : IsPerfect (X := X.toRingedSpace) K) :
    ∃ E : CochainComplex X.Modules ℤ, boundedFiniteLocallyFreeComplex X E ∧
      Nonempty (DerivedCategory.Q.obj E ≅ K) :=
  have := isAffineHom_diagonal_of_hasResolutionProperty X hstage
  exists_boundedFiniteLocallyFree_iso_of_affineDiagonal X K hK

end Stacks.Perfect.BoundedLocallyFreeComplexes

end
