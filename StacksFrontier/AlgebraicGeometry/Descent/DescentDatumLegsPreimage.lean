module

public import StacksFrontier.AlgebraicGeometry.Descent.DescentDatumStepThreeToFive
public import StacksFrontier.AlgebraicGeometry.Descent.IntersectionEmbeddingBaseChange
public import StacksFrontier.AlgebraicGeometry.Groupoids.DescentDatumGroupoid

/-!
# The two comparison legs agree on the image of an invariant open

Let `f : X ⟶ S` be a flat morphism of affine schemes, let `D` be a descent datum relative to `f`
whose scheme `V` over `X` is ind-quasi-affine, let `E ⊆ V` be a set-theoretically invariant
intersection of a nonempty family of quasi-compact opens, and let `W ⊆ E` be an invariant open of
`V`. The two comparison legs
```
  Γ(E, 𝒪_V|_E) ⟶ Γ(E ×_S X, 𝒪) --Φ--→ Γ(X ×_S E, 𝒪)    and    Γ(E, 𝒪_V|_E) ⟶ Γ(X ×_S E, 𝒪)
```
of [Stacks, Tag 0APJ](https://stacks.math.columbia.edu/tag/0APJ) have, after applying `Spec`, the
same inverse image of the image `j(W)` of `W` under the canonical embedding of
[Stacks, Tag 0API](https://stacks.math.columbia.edu/tag/0API).

## Main results

* `AlgebraicGeometry.DescentDatum.preimage_specMap_legs_subsetΓSpecImage` : **the two legs agree
  on `j(W)`**, which is the obligation `hlegs` of
  `AlgebraicGeometry.DescentDatum.isEffective_of_legs_of_restrictOpen` and of
  `AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc_of_legs_of_restrictOpen`.

## Implementation notes

*Both legs are restriction maps.* The first leg is the restriction along the projection
`E ×_S X ⟶ V` followed by `Φ`, which is the restriction along `φ⁻¹`; by functoriality of the
restriction maps it is therefore the restriction along the single morphism
`φ⁻¹ ∘ pr₁ : X ×_S E ⟶ V`. The second leg is the restriction along `pr₂ : X ×_S E ⟶ V`.

*Each leg is a flat base change.* The projection `pr₂` is the base change of `f` along
`V ⟶ S`, and `φ⁻¹ ∘ pr₁` is that same square precomposed with an isomorphism, so
`AlgebraicGeometry.preimage_specMap_sectionsRingOnSubsetMap_subsetΓSpecImage` computes both
inverse images as images under the canonical embedding at `X ×_S E`.

*Where invariance of `W` enters.* The two images so obtained are the images of the inverse images
of `W` under the two morphisms, and invariance of `W` says exactly that those two subsets of
`X ×_S E` coincide. Invariance of `E` enters earlier, as the identification of `X ×_S E` with the
inverse image of `E` under `φ⁻¹ ∘ pr₁`.

## References

* [Stacks Project, Tag 0API](https://stacks.math.columbia.edu/tag/0API)
* [Stacks Project, Tag 0APJ](https://stacks.math.columbia.edu/tag/0APJ)
* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
* [Stacks Project, Tag 041Z](https://stacks.math.columbia.edu/tag/041Z)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

namespace DescentDatum

variable {S X : Scheme.{u}} {f : X ⟶ S} (D : DescentDatum f)

/-- **The two comparison legs agree on the image of an invariant open.**  For a flat morphism `f`
of affine schemes and a descent datum `D` relative to `f` whose scheme is ind-quasi-affine over
`X`, let `E` be a set-theoretically invariant intersection of a nonempty family of quasi-compact
opens and let `W ⊆ E` be an invariant open.  Then the two legs of
[Stacks, Tag 0APJ](https://stacks.math.columbia.edu/tag/0APJ) have the same inverse image of the
image of `W` under the canonical embedding of
[Stacks, Tag 0API](https://stacks.math.columbia.edu/tag/0API).

This is the obligation `hlegs` of
`AlgebraicGeometry.DescentDatum.isEffective_of_legs_of_restrictOpen` and, character for
character, of `AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc_of_legs_of_restrictOpen`. -/
theorem preimage_specMap_legs_subsetΓSpecImage [IsAffine S] [IsAffine X] [Flat f]
    [IsIndQuasiAffineHom D.over.hom]
    (E : Set D.over.left) {I : Type u} [Nonempty I] (U : I → D.over.left.Opens)
    (hU : ∀ i, IsCompact (U i : Set D.over.left))
    (hE : E = ⋂ i, (U i : Set D.over.left)) (hEinv : D.IsTransitionInvariantSet E)
    (W : D.over.left.Opens) (hWinv : D.IsTransitionInvariant W)
    (hWE : (W : Set D.over.left) ⊆ E) :
    (Spec.map (Scheme.sectionsRingOnSubsetMap (pullback.fst (D.over.hom ≫ f) f) E
          (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) (Set.Subset.refl _) ≫
        (D.transitionSectionsIso E
          (D.subset_preimage_transitionPullbackIso_hom_of_invariantSet E hEinv)
          (D.subset_preimage_transitionPullbackIso_inv_of_invariantSet E hEinv)).hom)).base ⁻¹'
        subsetΓSpecImage D.over.left E (W : Set D.over.left) =
      (Spec.map (Scheme.sectionsRingOnSubsetMap (pullback.snd f (D.over.hom ≫ f)) E
          (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) (Set.Subset.refl _))).base ⁻¹'
        subsetΓSpecImage D.over.left E (W : Set D.over.left) := by
  have hV : IsIndQuasiAffine D.over.left := isIndQuasiAffine_of_isIndQuasiAffineHom_hom D.over
  have h₁ := D.subset_preimage_transitionPullbackIso_hom_of_invariantSet E hEinv
  have h₂ := D.subset_preimage_transitionPullbackIso_inv_of_invariantSet E hEinv
  have hq : (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) ⊆
      (D.transitionPullbackIso.inv ≫ pullback.fst (D.over.hom ≫ f) f).base ⁻¹' E :=
    fun z hz ↦ h₂ hz
  have hqE : (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) =
      ⇑(D.transitionPullbackIso.inv ≫ pullback.fst (D.over.hom ≫ f) f) ⁻¹' E := by
    refine Set.Subset.antisymm hq fun z hz ↦ ?_
    have hzz : D.transitionPullbackIso.hom (D.transitionPullbackIso.inv z) = z :=
      (Scheme.homeoOfIso D.transitionPullbackIso).apply_symm_apply z
    have hmem : (pullback.snd f (D.over.hom ≫ f))
        (D.transitionPullbackIso.hom (D.transitionPullbackIso.inv z)) ∈ E := h₁ hz
    rw [hzz] at hmem
    exact hmem
  have hpre : ∀ {P : Scheme.{u}} (q : P ⟶ D.over.left),
      ⇑q ⁻¹' E = ⋂ i, ((q ⁻¹ᵁ U i : P.Opens) : Set P) := by
    intro P q
    rw [hE, Set.preimage_iInter]
    rfl
  have hcomp : Scheme.sectionsRingOnSubsetMap (pullback.fst (D.over.hom ≫ f) f) E
        (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) (Set.Subset.refl _) ≫
      (D.transitionSectionsIso E h₁ h₂).hom =
      Scheme.sectionsRingOnSubsetMap
        (D.transitionPullbackIso.inv ≫ pullback.fst (D.over.hom ≫ f) f) E
        (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) hq :=
    Scheme.sectionsRingOnSubsetMap_comp D.transitionPullbackIso.inv
      (pullback.fst (D.over.hom ≫ f) f) E (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E)
      (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) (Set.Subset.refl _) h₂
  have hsq₁ : IsPullback (D.transitionPullbackIso.inv ≫ pullback.fst (D.over.hom ≫ f) f)
      (D.transitionPullbackIso.inv ≫ pullback.snd (D.over.hom ≫ f) f) (D.over.hom ≫ f) f :=
    (IsPullback.of_hasPullback (D.over.hom ≫ f) f).of_iso D.transitionPullbackIso
      (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ((Category.comp_id _).trans (Iso.hom_inv_id_assoc _ _).symm)
      ((Category.comp_id _).trans (Iso.hom_inv_id_assoc _ _).symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  have hleg₁ := preimage_specMap_sectionsRingOnSubsetMap_subsetΓSpecImage hsq₁ U hU E
    (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) (W : Set D.over.left) hE
    (hqE.trans (hpre _)) hq hWE W.2
  have hleg₂ := preimage_specMap_sectionsRingOnSubsetMap_subsetΓSpecImage
    (IsPullback.of_hasPullback f (D.over.hom ≫ f)).flip U hU E
    (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) (W : Set D.over.left) hE (hpre _)
    (Set.Subset.refl _) hWE W.2
  have hWeq : (D.transitionPullbackIso.inv ≫ pullback.fst (D.over.hom ≫ f) f).base ⁻¹'
      (W : Set D.over.left) =
      (pullback.snd f (D.over.hom ≫ f)).base ⁻¹' (W : Set D.over.left) := by
    refine Set.Subset.antisymm (fun z hz ↦ ?_)
      fun z hz ↦ D.mem_of_isTransitionInvariant' W hWinv z hz
    have hzz : D.transitionPullbackIso.hom (D.transitionPullbackIso.inv z) = z :=
      (Scheme.homeoOfIso D.transitionPullbackIso).apply_symm_apply z
    have hw : (pullback.snd f (D.over.hom ≫ f))
        (D.transitionPullbackIso.hom (D.transitionPullbackIso.inv z)) ∈ W :=
      D.mem_of_isTransitionInvariant W hWinv (D.transitionPullbackIso.inv z) hz
    rw [hzz] at hw
    exact hw
  rw [hcomp, hleg₁, hleg₂, hWeq]

end DescentDatum

end AlgebraicGeometry

end

end
