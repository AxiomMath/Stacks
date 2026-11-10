module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.RightAdjointDirectSumsFlat
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.OpenBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.RestrictionSupport
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.SupportedCompactGeneration
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeBoundedComplex
public import StacksFrontier.Homology.DerivedCategory.IsZero

/-!
# Supports and restriction to opens for the twisted inverse image of a proper flat morphism

Let `Y` be quasi-compact and quasi-separated and `f : X ⟶ Y` proper, flat and of finite
presentation, with `a` the right adjoint of `Rf_*` on `D_QCoh`. Then `a` commutes with direct
sums ([Stacks, Tag 0E4I]), so by [Stacks, Tag 0A9N] the map of [Stacks, Tag 0A9L] is invertible on
all of `D_QCoh(𝒪_Y)` and not only on `D^+_QCoh(𝒪_Y)` ([Stacks, Tag 0A9P]), and `a` preserves
supports: [Stacks, Tag 0E4J].
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
  [IsOpenImmersion j] [CompactSpace Y] [QuasiSeparatedSpace Y] [IsProper f] [Flat f]
  [LocallyOfFinitePresentation f] [AlgebraicGeometry.QuasiCompact j]

/-- Let `Y` be a quasi-compact and quasi-separated scheme, `f : X ⟶ Y` proper, flat and of finite
presentation, and `j : V ⟶ Y` the inclusion of a quasi-compact open, with base change
`j' : U ⟶ X`. The map `(j')^* ∘ a ⟶ a' ∘ j^*` of [Stacks, Tag 0A9L] is an isomorphism at every
`K ∈ D_QCoh(𝒪_Y)`. -/
@[stacks 0E4J "(2)"]
theorem isIso_twistedInverseImageRestrictionMap_app_of_flat_of_unbounded
    (sq : IsPullback j' f' f j) (K : quasiCoherentDerivedCategory Y) :
    haveI : IsOpenImmersion j' := MorphismProperty.of_isPullback sq.flip inferInstance
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace j
    haveI : CompactSpace U := compactSpace_of_isPullback sq
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    haveI : QuasiSeparatedSpace V := j.isOpenEmbedding.quasiSeparatedSpace
    haveI : QuasiSeparatedSpace U := j'.isOpenEmbedding.quasiSeparatedSpace
    IsIso ((twistedInverseImageRestrictionMap j' f' f j
      (isQuasicoherent_homology_derivedPushforward_of_qcqs j')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs j)
      (isQuasicoherent_homology_derivedRestrict j) (isQuasicoherent_homology_derivedRestrict j')
      sq).app K) := by
  have : IsOpenImmersion j' := MorphismProperty.of_isPullback sq.flip inferInstance
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace j
  have : CompactSpace U := compactSpace_of_isPullback sq
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : QuasiSeparatedSpace V := j.isOpenEmbedding.quasiSeparatedSpace
  have : QuasiSeparatedSpace U := j'.isOpenEmbedding.quasiSeparatedSpace
  exact (twistedInverseImageRestrictionMap_isIso_iff j' f' f j sq).2.2
    (fun J => preservesColimitsOfShape_rightAdjoint_quasiCoherentDerivedPushforward_of_flat f
      (twistedInverseImageAdjunction f _) J)
    (fun K hK => isIso_twistedInverseImageRestrictionMap_app_of_flat j' f' f j sq K hK) K

/-- **The base change map `α : L(j')^* ∘ a ⟶ a' ∘ Lj^*` of [Stacks, Tag 0AA6] along a
quasi-compact open immersion is invertible at every `K`** for `f` proper, flat and of finite
presentation over a quasi-compact quasi-separated base. -/
theorem isIso_rightAdjointBaseChange_app_of_isOpenImmersion_of_flat (sq : IsPullback j' f' f j)
    (K : quasiCoherentDerivedCategory Y) :
    haveI : IsOpenImmersion j' := MorphismProperty.of_isPullback sq.flip inferInstance
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace j
    haveI : CompactSpace U := compactSpace_of_isPullback sq
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    haveI : QuasiSeparatedSpace V := j.isOpenEmbedding.quasiSeparatedSpace
    haveI : QuasiSeparatedSpace U := j'.isOpenEmbedding.quasiSeparatedSpace
    haveI := isIso_rightAdjointSquare_of_isOpenImmersion j' f' f j sq
    IsIso ((Stacks.CategoryTheory.BaseChange.rightAdjointBaseChange
        (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
        (quasiCoherentDerivedAdjunction f' (isQuasicoherent_homology_derivedPullback' f')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))
        (quasiCoherentDerivedAdjunction j (isQuasicoherent_homology_derivedPullback' j)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs j))
        (quasiCoherentDerivedAdjunction j' (isQuasicoherent_homology_derivedPullback' j')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs j'))
        (quasiCoherentDerivedPullbackCompIso f' j)
        (quasiCoherentDerivedPullbackCompIso j' f ≪≫ quasiCoherentDerivedPullbackCongr sq.w)
        (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
        (twistedInverseImageAdjunction f'
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))).app K) := by
  have : IsOpenImmersion j' := MorphismProperty.of_isPullback sq.flip inferInstance
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace j
  have : CompactSpace U := compactSpace_of_isPullback sq
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : QuasiSeparatedSpace V := j.isOpenEmbedding.quasiSeparatedSpace
  have : QuasiSeparatedSpace U := j'.isOpenEmbedding.quasiSeparatedSpace
  exact isIso_rightAdjointBaseChange_app_of_isIso_twistedInverseImageRestrictionMap j' f' f j sq K
    (isIso_twistedInverseImageRestrictionMap_app_of_flat_of_unbounded j' f' f j sq K)

/-- **Vanishing of the restriction of a complex to an open is a condition on stalks of its
cohomology sheaves**: `E|_U = 0` exactly when every cohomology sheaf of `E` has vanishing stalks
at the points of `U`. -/
theorem isZero_derivedRestrict_iff_forall_isZero_stalk {Z : Scheme.{u}} (W : Z.Opens)
    (E : DerivedCategory Z.Modules) :
    IsZero ((derivedRestrict W.ι).obj E) ↔
      ∀ (n : ℤ), ∀ z ∈ W,
        IsZero (((DerivedCategory.homologyFunctor Z.Modules n).obj E).presheaf.stalk z) := by
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  refine forall_congr' fun n => ?_
  have e := ((Scheme.Modules.restrictFunctor W.ι).mapDerivedCategoryHomologyIso n).app E
  rw [← Scheme.Modules.isZero_restrict_iff_forall_isZero_stalk]
  exact ⟨fun h => h.of_iso e.symm, fun h => h.of_iso e⟩

/-- Let `Y` be a quasi-compact and quasi-separated scheme and `f : X ⟶ Y` proper, flat and of
finite presentation, with `a` the right adjoint of `Rf_*` on `D_QCoh`. For every closed `T ⊆ Y`,
if `Q ∈ D_QCoh(𝒪_Y)` is supported on `T` then `a(Q)` is supported on `f⁻¹(T)`. Here `T` is the
complement of the open `W`, and "supported on `T`" is "restricts to zero on `W`". -/
@[stacks 0E4J "(1)"]
theorem isZero_derivedRestrict_twistedInverseImage_of_flat (W : Y.Opens)
    (Q : quasiCoherentDerivedCategory Y) (hQ : IsZero ((derivedRestrict W.ι).obj Q.obj)) :
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    IsZero ((derivedRestrict (f ⁻¹ᵁ W).ι).obj
      ((twistedInverseImage f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj Q).obj) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  rw [isZero_derivedRestrict_iff_forall_isZero_stalk] at hQ ⊢
  intro n x hx
  obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset (x := f.base x) (U := W) hx
  have : IsAffine V.toScheme := hV
  have sq := (isPullback_morphismRestrict f V).flip
  have hQV : IsZero ((derivedRestrict V.ι).obj Q.obj) := by
    rw [isZero_derivedRestrict_iff_forall_isZero_stalk]
    exact fun m z hz => hQ m z (hVW hz)
  have h := ((twistedInverseImageRestrictionMap_isIso_iff (f ⁻¹ᵁ V).ι (f ∣_ V) f V.ι sq).2.1.2
    (fun K => isIso_twistedInverseImageRestrictionMap_app_of_flat_of_unbounded (f ⁻¹ᵁ V).ι
      (f ∣_ V) f V.ι sq K)) Q hQV
  rw [isZero_derivedRestrict_iff_forall_isZero_stalk] at h
  exact h n x hxV

end Stacks.Duality
