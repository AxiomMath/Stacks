module

public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.Duality
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonFlat
public import
  StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonUnconditional
public import StacksFrontier.CategoryTheory.Monoidal.PullbackComparisonTwoVariable

/-!
# The two-variable comparison map for a proper flat morphism of finite presentation

Let `Y` be quasi-compact and quasi-separated and `f : X ⟶ Y` proper, flat and of finite
presentation, with `a` the right adjoint of `Rf_*` of [Stacks, Tag 0A9E]. The two-variable map
`Lf^*K ⊗ᴸ a(L) ⟶ a(K ⊗ᴸ L)` of [Stacks, Tag 0A9S] is an isomorphism for all `K`, `L` in
`D_QCoh(𝒪_Y)`: as in [Stacks, Tag 0E4K], which is the case `L = 𝒪_Y`, `a` commutes with direct
sums ([Stacks, Tag 0E4I]), and the dévissage of [Stacks, Tag 0A9U] in `K` applies.

## Main results

* `Stacks.Duality.isIso_twistedInverseImageCompareWithPullbackTensor_of_flat`
* `Stacks.Duality.isIso_twistedInverseImageCompareWithPullback_pullbackCotensorator_of_flat`: the
  map of Equation 48.8.0.1 built from the cotensorator `pullbackCotensorator f` of the monoidal
  functor `Lf^*` and the right unitor of `D_QCoh(𝒪_Y)` is an isomorphism ([Stacks, Tag 0E4K]).

## References

* [Stacks Project, Tag 0A9S](https://stacks.math.columbia.edu/tag/0A9S)
* [Stacks Project, Tag 0E4K](https://stacks.math.columbia.edu/tag/0E4K)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.Duality.DerivedPushforward

universe u

namespace Stacks.Duality

/-- **[Stacks, Tag 0A9E] for a quasi-compact quasi-separated morphism to a quasi-compact
quasi-separated scheme**, as an instance found from the morphism: the source is then
quasi-compact and quasi-separated as well, so the restricted `Rf_*` has a right adjoint. -/
instance isLeftAdjoint_quasiCoherentDerivedPushforward_of_qcqs_morphism {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward f).obj K.obj)).IsQuasicoherent) :
    (quasiCoherentDerivedPushforward f hpush).IsLeftAdjoint :=
  isLeftAdjoint_quasiCoherentDerivedPushforward_of_quasiCompact f hpush

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace Y] [QuasiSeparatedSpace Y] [IsProper f]
  [Flat f] [LocallyOfFinitePresentation f]

/-- **The two-variable comparison map of [Stacks, Tag 0A9S] is an isomorphism** for `f` proper,
flat and of finite presentation over a quasi-compact quasi-separated base: the map
`Lf^*K ⊗ᴸ a(L) ⟶ a(K ⊗ᴸ L)` is invertible for all `K`, `L` in `D_QCoh(𝒪_Y)`. -/
theorem isIso_twistedInverseImageCompareWithPullbackTensor_of_flat
    (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
    (K L : quasiCoherentDerivedCategory Y) :
    IsIso (compareWithPullbackTensor f hpush (pullbackCotensorator f)
      (twistedInverseImageAdjunction f hpush) K L) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  let := quasiCoherentDerivedMonoidal X
  let := quasiCoherentDerivedMonoidal Y
  let := quasiCoherentDerivedPullbackMonoidal f
  let := commShift_quasiCoherentDerivedPullback f (isQuasicoherent_homology_derivedPullback' f)
      hpush
  have := isTriangulated_quasiCoherentDerivedPullback' f hpush
  have := hasCoproducts_quasiCoherentDerivedCategory Y
  have hF : PreservesColimitsOfSize.{u, u} _ := (quasiCoherentDerivedAdjunction f
    (isQuasicoherent_homology_derivedPullback' f) hpush).leftAdjoint_preservesColimits
  let adj := twistedInverseImageAdjunction f hpush
  let := adj.rightAdjointCommShift ℤ
  let := adj.commShift_of_leftAdjoint ℤ
  have : (twistedInverseImage f hpush).IsTriangulated := adj.isTriangulated_rightAdjoint
  have : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) (twistedInverseImage f hpush) :=
    preservesColimitsOfShape_rightAdjoint_quasiCoherentDerivedPushforward_of_flat f adj
  have : ∀ (E : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y),
      IsIso (MonoidalProjectionFormula.projectionFormulaMap
        (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f) hpush)
        E K) := fun E K => by
    rw [← projectionFormulaMap_pullbackCotensorator]
    infer_instance
  obtain ⟨ι, G, hGc, hG⟩ := QcqsGeneration.isCompactlyGenerated_quasiCoherentDerivedCategory Y
  exact MonoidalProjectionFormula.isIso_comparison_app _ adj L G hGc hG
    (fun i n => (nonempty_hasRightDual_of_isCompactObject Y _
      (isCompactObject_shift (hGc i) n)).some) K

/-- **[Stacks, Tag 0E4K], for the monoidal-functor form of Equation 48.8.0.1.** Let `Y` be a
quasi-compact and quasi-separated scheme and let `f : X ⟶ Y` be proper, flat and of finite
presentation. The map `Lf^*K ⊗ᴸ a(𝒪_Y) ⟶ a(K)` of Equation 48.8.0.1 ([Stacks, Tag 0A9S]), built
from the cotensorator `pullbackCotensorator f` of `Lf^*` and the right unitor of `D_QCoh(𝒪_Y)`,
is an isomorphism for every `K ∈ D_QCoh(𝒪_Y)`, for every proof `hpush` that `Rf_*` preserves
quasi-coherence of cohomology: `a` commutes with direct sums ([Stacks, Tag 0E4I]) and the
dévissage of [Stacks, Tag 0A9U] applies. -/
theorem isIso_twistedInverseImageCompareWithPullback_pullbackCotensorator_of_flat
    (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
    (K : quasiCoherentDerivedCategory Y) :
    IsIso (twistedInverseImageCompareWithPullback f hpush (pullbackCotensorator f)
      quasiCoherentRightUnitor K) :=
  isIso_compareWithPullback_of_hasRightDual f hpush (nonempty_hasRightDual_of_isCompactObject Y)
    (twistedInverseImageAdjunction f hpush)
    (preservesColimitsOfShape_rightAdjoint_quasiCoherentDerivedPushforward_of_flat f
      (twistedInverseImageAdjunction f hpush)) K

end Stacks.Duality

end
