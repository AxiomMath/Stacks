module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.RestrictionSupport
public import
  StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.TorIndependentBaseChangeIsIso

/-!
# The support criterion of Tag 0A9N, with the base change isomorphism proved

Let `f : X ⟶ Y` be a morphism of quasi-compact quasi-separated schemes and `V ⊆ Y` a quasi-compact
open with inverse image `U`. The map `(j')^* ∘ a ⟶ a' ∘ j^*` of [Stacks, Tag 0A9L] is built from
the inverse of `ξ : Rj'_* ∘ a' ⟶ a ∘ Rj_*`. Here `ξ` is shown invertible by [Stacks, Tag 0A9K],
since `j : V ⟶ Y` is flat and hence Tor independent from `f`, and [Stacks, Tag 0A9N] holds as
stated.

## Main results

* `Stacks.Duality.qcqs_twistedInverseImageRestrictionMap_isIso_iff` — **[Stacks, Tag 0A9N]**,
  parts (1), (2) and (3).

## References

* [Stacks Project, Tag 0A9N](https://stacks.math.columbia.edu/tag/0A9N)
* [Stacks Project, Tag 0A9K](https://stacks.math.columbia.edu/tag/0A9K)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

open OpenImmersion

variable {U X V Y : Scheme.{u}} (j' : U ⟶ X) (f' : U ⟶ V) (f : X ⟶ Y) (j : V ⟶ Y)
  [IsOpenImmersion j] [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
  [QuasiSeparatedSpace Y] [CompactSpace V]

/-- Let `f : X ⟶ Y` be a morphism of quasi-compact quasi-separated schemes, `a` the right adjoint
of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`, `j : V ⟶ Y` the inclusion of a quasi-compact open and
`j' : U ⟶ X` its base change, with `f' : U ⟶ V` and `a'` the right adjoint of `Rf'_*`. The
transformation `ξ : Rj'_* ∘ a' ⟶ a ∘ Rj_*` is invertible by [Stacks, Tag 0A9K] (`j` is flat, so Tor
independent from `f`). Writing `φ : (j')^* ∘ a ⟶ a' ∘ j^*` for the map of [Stacks, Tag 0A9L]:
1. `a` carries every `Q ∈ D^+_QCoh(𝒪_Y)` supported on `Y ∖ V` to an object supported on `X ∖ U` if
   and only if `φ` is invertible on `D^+_QCoh(𝒪_Y)`;
2. the same holds with `D_QCoh(𝒪_Y)` in place of `D^+_QCoh(𝒪_Y)`;
3. if `a` commutes with direct sums, the conditions of (1) imply those of (2).
"Supported on `Y ∖ V`" is "restricts to zero on `V`". -/
@[stacks 0A9N]
theorem qcqs_twistedInverseImageRestrictionMap_isIso_iff (sq : IsPullback j' f' f j) :
    haveI : IsOpenImmersion j' := MorphismProperty.of_isPullback sq.flip inferInstance
    haveI : QuasiSeparatedSpace V := j.isOpenEmbedding.quasiSeparatedSpace
    haveI : QuasiSeparatedSpace U := j'.isOpenEmbedding.quasiSeparatedSpace
    haveI : CompactSpace U := compactSpace_of_isPullback sq
    haveI : IsIso (twistedInverseImagePushforwardBaseChange j' f' f j
        (isQuasicoherent_homology_derivedPushforward_of_qcqs j')
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
        (isQuasicoherent_homology_derivedPushforward_of_qcqs j) sq) :=
      isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent sq
        (torIndependent_of_flat_right f j)
    let a := twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    let φ := twistedInverseImageRestrictionMap j' f' f j
      (isQuasicoherent_homology_derivedPushforward_of_qcqs j')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs j)
      (isQuasicoherent_homology_derivedRestrict j) (isQuasicoherent_homology_derivedRestrict j') sq
    ((∀ Q : quasiCoherentDerivedCategory Y, DerivedCategoryB.IsBoundedBelow Q.obj →
        IsZero ((derivedRestrict j).obj Q.obj) → IsZero ((derivedRestrict j').obj (a.obj Q).obj)) ↔
      ∀ K : quasiCoherentDerivedCategory Y, DerivedCategoryB.IsBoundedBelow K.obj →
        IsIso (φ.app K)) ∧
    ((∀ Q : quasiCoherentDerivedCategory Y,
        IsZero ((derivedRestrict j).obj Q.obj) → IsZero ((derivedRestrict j').obj (a.obj Q).obj)) ↔
      ∀ K : quasiCoherentDerivedCategory Y, IsIso (φ.app K)) ∧
    ((∀ α : Type u, PreservesColimitsOfShape (Discrete α) a) →
      (∀ K : quasiCoherentDerivedCategory Y, DerivedCategoryB.IsBoundedBelow K.obj →
        IsIso (φ.app K)) → ∀ K : quasiCoherentDerivedCategory Y, IsIso (φ.app K)) := by
  have : IsOpenImmersion j' := MorphismProperty.of_isPullback sq.flip inferInstance
  have : QuasiSeparatedSpace V := j.isOpenEmbedding.quasiSeparatedSpace
  have : QuasiSeparatedSpace U := j'.isOpenEmbedding.quasiSeparatedSpace
  have : CompactSpace U := compactSpace_of_isPullback sq
  have := isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent sq
    (torIndependent_of_flat_right f j)
  exact twistedInverseImageRestrictionMap_isIso_iff j' f' f j sq

end Stacks.Duality

end
