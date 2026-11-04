module

public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.TwistedInverseImageRestrictionQcqs
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.RightAdjointDirectSumsUnconditional
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.OpenBaseChangeComparison

/-!
# Supports and restriction to opens for the twisted inverse image of a perfect proper morphism

Let `f : X ⟶ Y` be a perfect proper morphism of Noetherian schemes, with `a` the right adjoint of
`Rf_*` on `D_QCoh` ([Stacks, Tag 0A9E]). Then `a` commutes with direct sums
([Stacks, Tag 0A9R]), so by [Stacks, Tag 0A9N] (3) the map of [Stacks, Tag 0A9L], which is
invertible on `D^+_QCoh(𝒪_Y)` by [Stacks, Tag 0A9P] (2), is invertible on all of `D_QCoh(𝒪_Y)`;
and `a` preserves supports. This is [Stacks, Tag 0AAA].

The map of Tag 0A9L contains the inverse of `ξ : Rj'_* ∘ a' ⟶ a ∘ Rj_*`, which is invertible by
[Stacks, Tag 0A9K]: for an open immersion this is
`Stacks.Duality.isIso_twistedInverseImagePushforwardBaseChange_of_isOpenImmersion`, and the
general Tor-independent case is
`Stacks.Duality.isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent`.

## Main results

* `Stacks.Duality.isIso_qcqsTwistedInverseImageRestrictionMap_app_of_perfect` —
  [Stacks, Tag 0AAA] (2), for every open `V ⊆ Y`, at the map
  `Stacks.Duality.OpenImmersion.qcqsTwistedInverseImageRestrictionMap`, every argument of which
  is discharged.
* `Stacks.Duality.isIso_twistedInverseImageRestrictionMap_app_of_perfect` — the same for a
  supplied cartesian square along an open immersion.
* `Stacks.Duality.isZero_derivedRestrict_twistedInverseImage_of_perfect` —
  [Stacks, Tag 0AAA] (1).
* `Stacks.Duality.isIso_rightAdjointBaseChange_app_of_isOpenImmersion_of_perfect` — the base
  change map `L(j')^* ∘ a ⟶ a' ∘ Lj^*` of [Stacks, Tag 0AA6] along an open immersion is
  invertible at every object.

## References

* [Stacks Project, Tag 0AAA](https://stacks.math.columbia.edu/tag/0AAA)
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
  [IsOpenImmersion j] [IsNoetherian X] [IsNoetherian Y] [IsProper f] [AlgebraicGeometry.Perfect f]

/-- **[Stacks, Tag 0AAA] (2), for a supplied cartesian square.** Let `f : X ⟶ Y` be a perfect
proper morphism of Noetherian schemes and `j : V ⟶ Y` an open immersion, with base change
`j' : U ⟶ X` and `f' : U ⟶ V`. The map `(j')^* ∘ a ⟶ a' ∘ j^*` of [Stacks, Tag 0A9L] is an
isomorphism at every `K ∈ D_QCoh(𝒪_Y)`. The invertibility of `ξ : Rj'_* ∘ a' ⟶ a ∘ Rj_*` that
the map contains is the open-immersion case of [Stacks, Tag 0A9K],
`Stacks.Duality.isIso_twistedInverseImagePushforwardBaseChange_of_isOpenImmersion`. The tag, for
every open `V ⊆ Y`, is `Stacks.Duality.isIso_qcqsTwistedInverseImageRestrictionMap_app_of_perfect`.
-/
@[stacks 0AAA "(2) variant: for a supplied cartesian square with open immersion `j`; the tag is
`isIso_qcqsTwistedInverseImageRestrictionMap_app_of_perfect`"]
theorem isIso_twistedInverseImageRestrictionMap_app_of_perfect (sq : IsPullback j' f' f j)
    (K : quasiCoherentDerivedCategory Y) :
    haveI : IsOpenImmersion j' := MorphismProperty.of_isPullback sq.flip inferInstance
    haveI : IsProper f' := MorphismProperty.of_isPullback sq inferInstance
    haveI := isNoetherian_of_isOpenImmersion j
    haveI := isNoetherian_of_isProper f'
    haveI := isIso_twistedInverseImagePushforwardBaseChange_of_isOpenImmersion j' f' f j
      (isQuasicoherent_homology_derivedPushforward_of_qcqs j')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs j) sq
    IsIso ((twistedInverseImageRestrictionMap j' f' f j
      (isQuasicoherent_homology_derivedPushforward_of_qcqs j')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs j)
      (isQuasicoherent_homology_derivedRestrict j) (isQuasicoherent_homology_derivedRestrict j')
      sq).app K) := by
  have : IsOpenImmersion j' := MorphismProperty.of_isPullback sq.flip inferInstance
  have : IsProper f' := MorphismProperty.of_isPullback sq inferInstance
  have := isNoetherian_of_isOpenImmersion j
  have := isNoetherian_of_isProper f'
  exact (twistedInverseImageRestrictionMap_isIso_iff j' f' f j sq).2.2
    (fun J => preservesCoproducts_twistedInverseImage_of_perfect_proper f J)
    (fun K hK => isIso_twistedInverseImageRestrictionMap_app_of_isProper j' f' f j sq K hK) K

/-- **[Stacks, Tag 0AAA] (2).** Let `f : X ⟶ Y` be a perfect proper morphism of Noetherian
schemes and `V ⊆ Y` an open, with `U = f⁻¹(V)`. The map `(j')^* ∘ a ⟶ a' ∘ j^*` of
[Stacks, Tag 0A9L], `Stacks.Duality.OpenImmersion.qcqsTwistedInverseImageRestrictionMap`, is an
isomorphism at every `K ∈ D_QCoh(𝒪_Y)`. The schemes `X`, `Y` are quasi-compact and
quasi-separated and `V` is quasi-compact because they are Noetherian. -/
@[stacks 0AAA "(2)"]
theorem isIso_qcqsTwistedInverseImageRestrictionMap_app_of_perfect (V : Y.Opens)
    (K : quasiCoherentDerivedCategory Y) :
    haveI := isNoetherian_of_isOpenImmersion V.ι
    IsIso ((qcqsTwistedInverseImageRestrictionMap f V).app K) := by
  have := isNoetherian_of_isOpenImmersion V.ι
  have := isNoetherian_of_isOpenImmersion (f ⁻¹ᵁ V).ι
  exact isIso_twistedInverseImageRestrictionMap_app_of_perfect (f ⁻¹ᵁ V).ι (f ∣_ V) f V.ι
    (isPullback_morphismRestrict f V).flip K

/-- **The base change map `α : L(j')^* ∘ a ⟶ a' ∘ Lj^*` of [Stacks, Tag 0AA6] along an open
immersion is invertible at every `K`** for a perfect proper morphism of Noetherian schemes: it is
the map of [Stacks, Tag 0A9L] conjugated by the comparisons of the left adjoints of `Rj_*` and
`Rj'_*`, and that map is invertible by [Stacks, Tag 0AAA] (2). -/
theorem isIso_rightAdjointBaseChange_app_of_isOpenImmersion_of_perfect (sq : IsPullback j' f' f j)
    (K : quasiCoherentDerivedCategory Y) :
    haveI : IsOpenImmersion j' := MorphismProperty.of_isPullback sq.flip inferInstance
    haveI : IsProper f' := MorphismProperty.of_isPullback sq inferInstance
    haveI := isNoetherian_of_isOpenImmersion j
    haveI := isNoetherian_of_isProper f'
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
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))).natTrans.app K) := by
  have : IsOpenImmersion j' := MorphismProperty.of_isPullback sq.flip inferInstance
  have : IsProper f' := MorphismProperty.of_isPullback sq inferInstance
  have := isNoetherian_of_isOpenImmersion j
  have := isNoetherian_of_isProper f'
  exact isIso_rightAdjointBaseChange_app_of_isIso_twistedInverseImageRestrictionMap j' f' f j sq K
    (isIso_twistedInverseImageRestrictionMap_app_of_perfect j' f' f j sq K)

/-- **[Stacks, Tag 0AAA] (1).** Let `f : X ⟶ Y` be a perfect proper morphism of Noetherian
schemes, with `a` the right adjoint of `Rf_*` on `D_QCoh`. For every closed `T ⊆ Y`, if
`Q ∈ D_QCoh(𝒪_Y)` is supported on `T` then `a(Q)` is supported on `f⁻¹(T)`. Here `T` is the
complement of the open `W`, and "supported on `T`" is "restricts to zero on `W`". The functor `a`
exists by [Stacks, Tag 0A9E],
`Stacks.Duality.DerivedPushforward.isLeftAdjoint_quasiCoherentDerivedPushforward_of_qcqs`. -/
@[stacks 0AAA "(1)"]
theorem isZero_derivedRestrict_twistedInverseImage_of_perfect (W : Y.Opens)
    (Q : quasiCoherentDerivedCategory Y) (hQ : IsZero ((derivedRestrict W.ι).obj Q.obj)) :
    haveI := DerivedPushforward.isLeftAdjoint_quasiCoherentDerivedPushforward_of_qcqs f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    IsZero ((derivedRestrict (f ⁻¹ᵁ W).ι).obj
      ((twistedInverseImage f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj Q).obj) := by
  have sq := (isPullback_morphismRestrict f W).flip
  have := isNoetherian_of_isOpenImmersion W.ι
  have := isNoetherian_of_isOpenImmersion (f ⁻¹ᵁ W).ι
  exact ((twistedInverseImageRestrictionMap_isIso_iff (f ⁻¹ᵁ W).ι (f ∣_ W) f W.ι sq).2.1.2
    (fun K => isIso_twistedInverseImageRestrictionMap_app_of_perfect (f ⁻¹ᵁ W).ι (f ∣_ W) f W.ι
      sq K)) Q hQ

end Stacks.Duality
