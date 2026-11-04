module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.ProperFlatRestriction
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.ProperRestriction
public import
  StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.TorIndependentBaseChangeIsIso

/-!
# The twisted inverse image of a proper morphism and restriction to quasi-compact opens

Let `Y` be quasi-compact and quasi-separated, `f : X ⟶ Y` proper, and `V ⊆ Y` a quasi-compact open
with inverse image `U`. If `f` is flat and of finite presentation, or `Y` is Noetherian, then both
equivalent conditions of [Stacks, Tag 0A9N] (1) hold: `a` carries every `Q ∈ D^+_QCoh(𝒪_Y)`
supported on `Y ∖ V` to an object supported on `X ∖ U`, and the map `(j')^* ∘ a ⟶ a' ∘ j^*` of
[Stacks, Tag 0A9L] is invertible on `D^+_QCoh(𝒪_Y)` ([Stacks, Tag 0A9P]).

The map of Tag 0A9L is built from the inverse of `ξ : Rj'_* ∘ a' ⟶ a ∘ Rj_*`; here `ξ` is shown
invertible inside each statement by [Stacks, Tag 0A9K], since the open immersion `j` is flat and
hence Tor independent from `f`.

## Main results

* `Stacks.Duality.restrictionSupport_and_isIso_twistedInverseImageRestrictionMap_of_flat` —
  [Stacks, Tag 0A9P] (1).
* `Stacks.Duality.restrictionSupport_and_isIso_twistedInverseImageRestrictionMap_of_isNoetherian`
  — [Stacks, Tag 0A9P] (2).

"Supported on `Y ∖ V`" is read as "restricts to zero on `V`".

## References

* [Stacks Project, Tag 0A9P](https://stacks.math.columbia.edu/tag/0A9P)
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

section Flat

variable {U X V Y : Scheme.{u}} (j' : U ⟶ X) (f' : U ⟶ V) (f : X ⟶ Y) (j : V ⟶ Y)
  [IsOpenImmersion j] [CompactSpace Y] [QuasiSeparatedSpace Y] [IsProper f] [Flat f]
  [LocallyOfFinitePresentation f] [CompactSpace V]

/-- **[Stacks, Tag 0A9P] (1).** Let `Y` be a quasi-compact quasi-separated scheme, `f : X ⟶ Y` a
proper, flat morphism of finite presentation, `j : V ⟶ Y` the inclusion of a quasi-compact open and
`j' : U ⟶ X` its base change, with `f' : U ⟶ V`; let `a`, `a'` be the right adjoints of `Rf_*`,
`Rf'_*` on `D_QCoh`. With `ξ : Rj'_* ∘ a' ⟶ a ∘ Rj_*` invertible by [Stacks, Tag 0A9K], the
equivalent conditions of [Stacks, Tag 0A9N] (1) hold: `a` carries every `Q ∈ D^+_QCoh(𝒪_Y)`
supported on `Y ∖ V` to an object supported on `X ∖ U`, and the map `φ : (j')^* ∘ a ⟶ a' ∘ j^*`
of [Stacks, Tag 0A9L] is invertible on `D^+_QCoh(𝒪_Y)`. -/
@[stacks 0A9P "(1)"]
theorem restrictionSupport_and_isIso_twistedInverseImageRestrictionMap_of_flat
    (sq : IsPullback j' f' f j) :
    haveI : IsOpenImmersion j' := MorphismProperty.of_isPullback sq.flip inferInstance
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : CompactSpace U := compactSpace_of_isPullback sq
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    haveI : QuasiSeparatedSpace V := j.isOpenEmbedding.quasiSeparatedSpace
    haveI : QuasiSeparatedSpace U := j'.isOpenEmbedding.quasiSeparatedSpace
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
    (∀ Q : quasiCoherentDerivedCategory Y, DerivedCategoryB.IsBoundedBelow Q.obj →
        IsZero ((derivedRestrict j).obj Q.obj) → IsZero ((derivedRestrict j').obj (a.obj Q).obj)) ∧
      ∀ K : quasiCoherentDerivedCategory Y, DerivedCategoryB.IsBoundedBelow K.obj →
        IsIso (φ.app K) := by
  have : AlgebraicGeometry.QuasiCompact j := (quasiCompact_iff_compactSpace j).2 inferInstance
  exact ⟨fun Q hQb hQ => isZero_restrict_twistedInverseImage_of_isPseudoCoherent j' f' f j sq
      (isPseudoCoherent_derivedPushforward_of_isCompactObject_of_flat f) Q hQb hQ,
    fun K hK => isIso_twistedInverseImageRestrictionMap_app_of_flat j' f' f j sq K hK⟩

end Flat

section Noetherian

variable {U X V Y : Scheme.{u}} (j' : U ⟶ X) (f' : U ⟶ V) (f : X ⟶ Y) (j : V ⟶ Y)
  [IsOpenImmersion j] [IsNoetherian Y] [IsProper f]

/-- **[Stacks, Tag 0A9P] (2).** Let `Y` be a Noetherian scheme, `f : X ⟶ Y` a proper morphism,
`j : V ⟶ Y` the inclusion of an open (quasi-compact, as `Y` is Noetherian) and `j' : U ⟶ X` its
base change, with `f' : U ⟶ V`; let `a`, `a'` be the right adjoints of `Rf_*`, `Rf'_*` on
`D_QCoh`. With `ξ : Rj'_* ∘ a' ⟶ a ∘ Rj_*` invertible by [Stacks, Tag 0A9K], the equivalent
conditions of [Stacks, Tag 0A9N] (1) hold: `a` carries every `Q ∈ D^+_QCoh(𝒪_Y)` supported on
`Y ∖ V` to an object supported on `X ∖ U`, and the map `φ : (j')^* ∘ a ⟶ a' ∘ j^*` of
[Stacks, Tag 0A9L] is invertible on `D^+_QCoh(𝒪_Y)`. -/
@[stacks 0A9P "(2)"]
theorem restrictionSupport_and_isIso_twistedInverseImageRestrictionMap_of_isNoetherian
    (sq : IsPullback j' f' f j) :
    haveI : IsOpenImmersion j' := MorphismProperty.of_isPullback sq.flip inferInstance
    haveI := isNoetherian_of_isProper f
    haveI : IsProper f' := MorphismProperty.of_isPullback sq inferInstance
    haveI := isNoetherian_of_isOpenImmersion j
    haveI := isNoetherian_of_isProper f'
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
    (∀ Q : quasiCoherentDerivedCategory Y, DerivedCategoryB.IsBoundedBelow Q.obj →
        IsZero ((derivedRestrict j).obj Q.obj) → IsZero ((derivedRestrict j').obj (a.obj Q).obj)) ∧
      ∀ K : quasiCoherentDerivedCategory Y, DerivedCategoryB.IsBoundedBelow K.obj →
        IsIso (φ.app K) :=
  ⟨fun Q hQb hQ => isZero_restrict_twistedInverseImage_of_isProper j' f' f j sq Q hQb hQ,
    fun K hK => isIso_twistedInverseImageRestrictionMap_app_of_isProper j' f' f j sq K hK⟩

end Noetherian

end Stacks.Duality

end
