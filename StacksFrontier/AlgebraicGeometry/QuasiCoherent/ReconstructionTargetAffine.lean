module

public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.AffineOfModuleCategory
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.AffineReconstruction
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ReconstructionRestrictionSquare

/-!
# The matched open in the target of a reconstruction equivalence is affine

Let `X` and `Y` be quasi-compact and quasi-separated schemes and let
`e : QCoh(𝒪_X) ≌ QCoh(𝒪_Y)` be an equivalence.  This file carries out **step 7** of
[Stacks, Tag 0GPJ]: in the situation of step 6, if the open `U ⊆ X` is affine then so is the
matched open `V ⊆ Y`.

Indeed `QCoh(𝒪_U)` is the category of `Γ(U, ⊤)`-modules
(`AlgebraicGeometry.affineQuasicoherentModulesEquiv`), so the restriction square of step 6
exhibits `QCoh(𝒪_V)` as a category of modules over a commutative ring, and `V` is quasi-compact
and quasi-separated, so [Stacks, Tag 0GPI] applies.

## Implementation notes

Quasi-separatedness of `V` is not an instance: it is deduced from quasi-separatedness of `Y`
along the open embedding `V.ι`, which is what [Stacks, Tag 0GPI] needs on top of
quasi-compactness of `V`.

## Main results

* `AlgebraicGeometry.isAffine_of_supportedCorrespondence` — **step 7**.

## References

* [Stacks Project, Proposition 56.6.6 (Tag 0GPJ)](https://stacks.math.columbia.edu/tag/0GPJ)
* [Stacks Project, Lemma 56.6.5 (Tag 0GPI)](https://stacks.math.columbia.edu/tag/0GPI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Step 7 of [Stacks, Tag 0GPJ] -/

section Reconstruction

variable {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
  [QuasiSeparatedSpace Y]
  (e : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ≌
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory)

section Matched

variable (Z : Set X) (T : Set Y)
  (hcorr : ∀ E, quasicoherentSupportedOn X Z E ↔
    quasicoherentSupportedOn Y T (e.functor.obj E))

include e hcorr

/-- **Step 7 of [Stacks, Tag 0GPJ].**  In the situation of step 6, if `U` is affine then `V` is
affine.  Indeed `QCoh(𝒪_U)` is the category of `Γ(U, ⊤)`-modules
(`AlgebraicGeometry.affineQuasicoherentModulesEquiv`), so step 6 exhibits `QCoh(𝒪_V)` as a
category of modules over a commutative ring, and `V` is quasi-compact and quasi-separated, so
[Stacks, Tag 0GPI] applies. -/
theorem isAffine_of_supportedCorrespondence (U : X.Opens) (hUZ : (U : Set X) = Zᶜ)
    (hU : IsCompact (U : Set X)) (hUaff : IsAffineOpen U) (V : Y.Opens)
    (hVT : (V : Set Y) = Tᶜ) (hV : IsCompact (V : Set Y)) : IsAffine V.toScheme := by
  have : IsAffine U.toScheme := hUaff
  have : CompactSpace V.toScheme := isCompact_iff_compactSpace.mp hV
  have : QuasiSeparatedSpace V.toScheme :=
    QuasiSeparatedSpace.of_isOpenEmbedding V.ι.isOpenEmbedding
  obtain ⟨F, hF, ⟨_⟩⟩ :=
    exists_isEquivalence_restrictionSquare e Z T hcorr U hUZ hU V hVT hV
  have := hF
  exact AffineOfModuleCategory.isAffine_of_quasicoherentModules_equivalent_moduleCat
    V.toScheme (ToType Γ(U.toScheme, ⊤))
    ((affineQuasicoherentModulesEquiv U.toScheme).trans F.asEquivalence)

end Matched

end Reconstruction

end AlgebraicGeometry

end
