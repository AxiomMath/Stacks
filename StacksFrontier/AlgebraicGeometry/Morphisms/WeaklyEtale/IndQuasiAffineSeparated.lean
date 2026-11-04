module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.IndQuasiAffine
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A separated quasi-finite morphism of schemes is ind-quasi-affine

A separated locally quasi-finite morphism of schemes is ind-quasi-affine. Here "locally
quasi-finite" is the notion of Stacks 02NG, which includes being locally of finite type; in
Mathlib's vocabulary that is `AlgebraicGeometry.LocallyQuasiFinite` together with
`AlgebraicGeometry.LocallyOfFiniteType`. Mathlib's `AlgebraicGeometry.LocallyQuasiFinite` alone
does not imply local finite type: `Spec ℚ ⟶ Spec ℤ` satisfies it.

## Main results

* `AlgebraicGeometry.isQuasiAffine_of_isSeparated_of_locallyQuasiFinite`: a quasi-compact
  scheme which is separated and quasi-finite over an affine scheme is quasi-affine.
* `AlgebraicGeometry.isIndQuasiAffineHom_of_isSeparated_of_locallyQuasiFinite`: a separated
  quasi-finite morphism of schemes is ind-quasi-affine.

## References

* [Stacks Project, Tag 0AP9](https://stacks.math.columbia.edu/tag/0AP9)
* [Stacks Project, Tag 0AP6](https://stacks.math.columbia.edu/tag/0AP6)
* [Stacks Project, Tag 02LR](https://stacks.math.columbia.edu/tag/02LR)
* [Stacks Project, Tag 02NG](https://stacks.math.columbia.edu/tag/02NG)
* [Stacks Project, Tag 0BCK](https://stacks.math.columbia.edu/tag/0BCK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A quasi-compact scheme which is separated and quasi-finite over an affine scheme is
quasi-affine. -/
@[ega "IV 18.12.12" "Affine target",
  ega "IV 8.11.2" "special case",
  sga "1 VIII 6.2" "special case"]
theorem isQuasiAffine_of_isSeparated_of_locallyQuasiFinite {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsAffine Y] [CompactSpace X] [IsSeparated g] [LocallyQuasiFinite g]
    [LocallyOfFiniteType g] : Scheme.IsQuasiAffine X := by
  have hX : QuasiCompact (g ≫ terminal.from Y) := by
    rw [terminal.comp_from]
    exact (compactSpace_iff_quasiCompact X).mp ‹CompactSpace X›
  have : QuasiCompact g := QuasiCompact.of_comp g (terminal.from Y)
  have h : Scheme.IsQuasiAffine (⊤ : X.Opens).toScheme :=
    (isQuasiAffineHom_of_locallyQuasiFinite g).isQuasiAffine_preimage ⊤ (isAffineOpen_top Y)
  exact Scheme.IsQuasiAffine.of_isImmersion X.topIso.inv

/-- A separated morphism of schemes which is locally quasi-finite and locally of finite type is
ind-quasi-affine. -/
@[stacks 0AP9]
instance isIndQuasiAffineHom_of_isSeparated_of_locallyQuasiFinite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyQuasiFinite f] [LocallyOfFiniteType f] :
    IsIndQuasiAffineHom f := by
  refine ⟨fun U hU ↦ ⟨fun W hW ↦ ?_⟩⟩
  have : IsAffine U.toScheme := hU
  have : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp hW
  exact isQuasiAffine_of_isSeparated_of_locallyQuasiFinite (W.ι ≫ f ∣_ U)

end AlgebraicGeometry

end
