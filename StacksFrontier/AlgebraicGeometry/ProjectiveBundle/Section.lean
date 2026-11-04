module

public import StacksFrontier.AlgebraicGeometry.RelativeProjBundle.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.TerminalRelativeProj
public import StacksCore.Tactic.StacksAttribute

/-!
# A section of a projective bundle is a closed immersion

Let `X` be a scheme, `F` a quasi-coherent `𝒪_X`-module and `π : 𝐏(F) ⟶ X` the projection of
the projective bundle of `F`. A *section* of `π` is a morphism `σ : X ⟶ 𝐏(F)` with
`σ ≫ π = 𝟙 X`. Every such `σ` is a closed immersion.

## Main results

* `Stacks.RelativeProj.isSeparated_projectiveBundleToBase`: `π` is separated.
* `Stacks.RelativeProj.isClosedImmersion_of_section_projectiveBundleToBase`: a section of `π`
  is a closed immersion.

## Implementation notes

The argument is the one the Stacks project gives: `π` is separated, and a section of a
separated morphism is a closed immersion.

Separatedness is `Stacks.RelativeProj.Situation.isSeparated_relativeProjToBase`, the
Situation-level form of Tag 01O2, and `projectiveBundleToBase` is by definition the structure
morphism of the relative `Proj` of a Situation, so no transport is needed; it is registered
here as an instance so that the general lemma applies without an explicit `letI`.

The second half is general and belongs to no particular bundle: for `σ ≫ π = 𝟙 X` the
composite `σ ≫ π` is an isomorphism, hence a closed immersion, and
`AlgebraicGeometry.IsClosedImmersion.of_comp` cancels `π` off the right because `π` is
separated. That lemma is Mathlib's, and it is the content of Schemes, Tag 01KT; nothing new is
proved about it here.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01O2](https://stacks.math.columbia.edu/tag/01O2)
* [Stacks Project, Tag 01KT](https://stacks.math.columbia.edu/tag/01KT)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.RelativeProj

/-- **The projection `π : 𝐏(F) ⟶ X` of a projective bundle is separated.** This is Tag 01O2 for
the relative `Proj` of the symmetric algebra of `F`. -/
instance isSeparated_projectiveBundleToBase (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent] : IsSeparated (projectiveBundleToBase X F) :=
  Situation.isSeparated_relativeProjToBase _

/-- **A section of the projection of a projective bundle is a closed immersion.** Since
`π : 𝐏(F) ⟶ X` is separated (Tag 01O2) and `σ ≫ π = 𝟙 X` is an isomorphism, `σ` is a closed
immersion. -/
@[stacks 0B3V "closed immersion"]
theorem isClosedImmersion_of_section_projectiveBundleToBase (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent] (σ : X ⟶ projectiveBundle X F)
    (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X) : IsClosedImmersion σ :=
  have : IsClosedImmersion (σ ≫ projectiveBundleToBase X F) := hσ ▸ inferInstance
  IsClosedImmersion.of_comp σ (projectiveBundleToBase X F)

end Stacks.RelativeProj

end
