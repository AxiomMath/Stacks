module

public import StacksFrontier.AlgebraicGeometry.Chow.DiagonalGysin
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonUnconditional
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.DiagonalRigidity
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.Composition
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.RegularImmersion
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.Implications
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `ω_{X/Y}^• ⊗ c(𝒪) ≅ 𝒪_X` for a smooth proper morphism

Let `Y` be a Noetherian scheme and `f : X ⟶ Y` a smooth proper morphism, with diagonal
`Δ : X ⟶ X ×_Y X`. Let `a` and `c` be the right adjoints of `Rf_*` and `RΔ_*` on `D_QCoh`
([Stacks, Tag 0A9E]) and `ω_{X/Y}^• = a(𝒪_Y)`. The first three equalities of the proof of
[Stacks, Tag 0BRT] are

`𝒪_X = c(L pr₁^* ω_{X/Y}^•) = LΔ^*(L pr₁^* ω_{X/Y}^•) ⊗ᴸ c(𝒪_{X ×_Y X})
  = ω_{X/Y}^• ⊗ᴸ c(𝒪_{X ×_Y X})`:
the first is equation (0E2Q) of [Stacks, Tag 0E2P], the second is [Stacks, Tag 0A9U] for `Δ`,
which is a Koszul-regular immersion ([Stacks, Tags 067U, 0FBR]), hence a perfect proper morphism
([Stacks, Tag 068C]), and the third is `pr₁ ∘ Δ = id`.

The fourth equality of that proof, `c(𝒪) = ⋀^d 𝒩_Δ[-d]`, is [Stacks, Tag 0BR0]
(`Stacks.Duality.KoszulRegular.nonempty_normalExteriorComplex_iso_rightAdjoint_structureSheaf`).

## Main results

* `Stacks.Duality.isKoszulRegularImmersion_diagonal_of_smooth`: the diagonal of a smooth morphism
  is a Koszul-regular immersion.
* `Stacks.Duality.nonempty_tensor_twistedInverseImage_diagonal_iso`:
  `ω_{X/Y}^• ⊗ᴸ c(𝒪_{X ×_Y X}) ≅ 𝒪_X`.

## References

* [Stacks Project, Tag 0BRT](https://stacks.math.columbia.edu/tag/0BRT)
* [Stacks Project, Tag 0E2P](https://stacks.math.columbia.edu/tag/0E2P)
* [Stacks Project, Tag 0A9U](https://stacks.math.columbia.edu/tag/0A9U)
* [Stacks Project, Tag 068C](https://stacks.math.columbia.edu/tag/068C)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The diagonal of a smooth morphism is a Koszul-regular immersion**: it is a regular
immersion ([Stacks, Tag 0FBR], a section of the smooth first projection), and a regular immersion
is Koszul-regular ([Stacks, Tag 063K]). -/
@[sga "6 VII 1.10" "special case", sga "6 VIII 1.3" "special case"]
theorem isKoszulRegularImmersion_diagonal_of_smooth [Smooth f] :
    Stacks.AlgebraicGeometry.RegularIdealSheaf.IsKoszulRegularImmersion (pullback.diagonal f) :=
  Stacks.AlgebraicGeometry.RegularIdealSheaf.isKoszulRegularImmersion_of_isRegularImmersion _
    (Stacks.Chow.isRegularImmersion_diagonal_of_smooth f)

variable [IsNoetherian Y] [IsProper f] [Smooth f]

/-- **`ω_{X/Y}^• ⊗ᴸ c(𝒪_{X ×_Y X}) ≅ 𝒪_X`** for a smooth proper morphism `f : X ⟶ Y` to a
Noetherian scheme, `c` the twisted inverse image along the diagonal: the first three equalities of
the proof of [Stacks, Tag 0BRT]. -/
theorem nonempty_tensor_twistedInverseImage_diagonal_iso :
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    haveI := QuasiCompact.compactSpace_of_compactSpace (pullback.snd f f)
    haveI := quasiSeparatedSpace_of_quasiSeparated (pullback.snd f f)
    Nonempty (((quasiCoherentDerivedTensor X).obj
        ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
          (DerivedPushforward.derivedStructureSheaf Y))).obj
        ((twistedInverseImage (pullback.diagonal f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs (pullback.diagonal f))).obj
          (DerivedPushforward.derivedStructureSheaf (pullback f f))) ≅
      DerivedPushforward.derivedStructureSheaf X) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have := QuasiCompact.compactSpace_of_compactSpace (pullback.snd f f)
  have := quasiSeparatedSpace_of_quasiSeparated (pullback.snd f f)
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian f }
  have : IsNoetherian (Limits.pullback f f : Scheme.{u}) :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f f) }
  have : AlgebraicGeometry.Perfect (pullback.diagonal f) :=
    perfect_of_isKoszulRegularImmersion _ (isKoszulRegularImmersion_diagonal_of_smooth f)
  obtain ⟨e⟩ := nonempty_twistedInverseImage_diagonal_fst_iso f
    (DerivedPushforward.derivedStructureSheaf Y)
  refine ⟨((quasiCoherentDerivedTensor X).mapIso ?_).app _ ≪≫
    compareWithPullbackIso (pullback.diagonal f) _ ≪≫ e ≪≫
    ObjectProperty.isoMk _ (derivedPullbackStructureSheafIso f)⟩
  exact ((quasiCoherentDerivedPullbackCompIso (pullback.diagonal f) (pullback.fst f f)).app _ ≪≫
    (quasiCoherentDerivedPullbackCongr (pullback.diagonal_fst f)).app _ ≪≫
    (quasiCoherentDerivedPullbackIdIso X _).app _).symm

end Stacks.Duality
