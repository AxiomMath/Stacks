module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.CompactPerfectTag
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCompactGeneration
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.RightAdjointDirectSums
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.PerfectDirectImageLocallySmall
public import StacksFrontier.CategoryTheory.Triangulated.RightAdjointCoproductsFamily
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The twisted inverse image of a perfect proper morphism commutes with direct sums

Let `f : X ⟶ Y` be a perfect proper morphism of Noetherian schemes. Then the right adjoint
`a = f^×` of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` commutes with direct sums: this is
[Stacks, Tag 0A9R], here with nothing carried.

The source's argument: `Rf_*` carries perfect objects to perfect objects ([Stacks, Tag 0B6G]),
perfect objects of `D_QCoh` are exactly the compact ones ([Stacks, Tag 09M1]), and `D_QCoh(𝒪_X)`
is compactly generated ([Stacks, Tag 09IS]); so the left adjoint `Rf_*` preserves compactness of a
generating family and its right adjoint commutes with direct sums.

## Main results

* `Stacks.Duality.isCompactObject_quasiCoherentDerivedPushforward_of_perfect_proper` — `Rf_*`
  carries compact objects of `D_QCoh(𝒪_X)` to compact objects of `D_QCoh(𝒪_Y)`.
* `Stacks.Duality.preservesCoproducts_twistedInverseImage_of_perfect_proper` —
  [Stacks, Tag 0A9R], unconditionally.

## References

* [Stacks Project, Tag 0A9R](https://stacks.math.columbia.edu/tag/0A9R)
* [Stacks Project, Tag 0B6G](https://stacks.math.columbia.edu/tag/0B6G)
* [Stacks Project, Tag 09M1](https://stacks.math.columbia.edu/tag/09M1)
* [Stacks Project, Tag 09IS](https://stacks.math.columbia.edu/tag/09IS)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsNoetherian X] [IsNoetherian Y] [IsProper f]
  [AlgebraicGeometry.Perfect f]

open Stacks.AlgebraicGeometry.PerfectProperDirectImage in
/-- **`Rf_*` preserves compactness along a perfect proper morphism of Noetherian schemes.** A
compact object of `D_QCoh(𝒪_X)` is perfect ([Stacks, Tag 09M1]), its derived direct image is
perfect ([Stacks, Tag 0B6G]), hence compact in `D_QCoh(𝒪_Y)` ([Stacks, Tag 09M1]). -/
@[sga "6 III 4.8.1" "special case"]
theorem isCompactObject_quasiCoherentDerivedPushforward_of_perfect_proper
    (K : quasiCoherentDerivedCategory X) (hK : IsCompactObject.{u} K) :
    IsCompactObject.{u} ((quasiCoherentDerivedPushforward f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj K) :=
  isCompactObject_of_isPerfect _
    (isPerfect_derivedPushforward_of_isPerfect_locallySmall
      f K.obj (isPerfect_of_isCompactObject K hK))

/-- **[Stacks, Tag 0A9R].** Let `f : X ⟶ Y` be a perfect proper morphism of Noetherian schemes.
The twisted inverse image `a = f^×`, the right adjoint of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` ([Stacks, Tag 0A9E]), commutes with direct sums: it
preserves coproducts indexed by every `J : Type u`, the universe of the schemes, which is the
universe of the hom-sets of `D_QCoh` and the one at which it has all direct sums. -/
@[stacks 0A9R "a = f^× commutes with direct sums indexed by every type J in the universe of \
X and Y, the universe of the hom-sets of D_QCoh"]
theorem preservesCoproducts_twistedInverseImage_of_perfect_proper (J : Type u) :
    PreservesColimitsOfShape (Discrete J)
      (twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)) := by
  have := DerivedPushforward.hasCoproducts_quasiCoherentDerivedCategory X
  have := DerivedPushforward.hasCoproducts_quasiCoherentDerivedCategory Y
  have : (twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).Additive :=
    (twistedInverseImageAdjunction f _).right_adjoint_additive
  exact Pretriangulated.preservesCoproducts_of_isCompactlyGenerated_of_isCompactObject_map
    (twistedInverseImageAdjunction f _)
    (QcqsGeneration.isCompactlyGenerated_quasiCoherentDerivedCategory X)
    (isCompactObject_quasiCoherentDerivedPushforward_of_perfect_proper f) J

end Stacks.Duality

end
