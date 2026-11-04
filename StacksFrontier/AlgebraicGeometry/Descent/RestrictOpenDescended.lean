module

public import StacksFrontier.AlgebraicGeometry.Descent.DescentInvariantsOpenPullback
public import StacksFrontier.AlgebraicGeometry.Descent.DescentInvariantsProjections
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.DescendedScheme

/-!
# The restriction of a descent datum to an invariant open is effective

Let `f : X ⟶ S` be a flat morphism of affine schemes, let `D` be a descent datum relative to `f`
whose scheme `V` is ind-quasi-affine over `X` and quasi-separated, let `E ⊆ V` be an intersection
of a nonempty family of quasi-compact opens whose two preimages are carried into one another by
the gluing isomorphism, and let `W ⊆ E` be an invariant open of `V`. Write `C = Γ(E, 𝒪_V|_E)`. If
`C` is the base change to `Γ(X, ⊤)` of a `Γ(S, ⊤)`-algebra `C₀` whose inclusion equalises the two
comparison legs of [Stacks, Tag 0APJ](https://stacks.math.columbia.edu/tag/0APJ), and if an open
`W₀` of `Spec C₀` pulls back to the image of `W` under the canonical embedding of
[Stacks, Tag 0API](https://stacks.math.columbia.edu/tag/0API), then `W₀` descends the restriction
of `D` to `W`.

`AlgebraicGeometry.DescentDatum.exists_isPullback_restrictOpen_descentInvariants` already supplies
the fibre-product condition. What is added here is the second condition of
`AlgebraicGeometry.DescentDatum.Descended`: the projection onto `W₀` equalises the two legs of the
gluing isomorphism.

## Main definitions

* `AlgebraicGeometry.DescentDatum.descendedRestrictOpen`: **the scheme over `S` descending the
  restriction of the datum to an invariant open**, namely `W₀`.

## Main results

* `AlgebraicGeometry.DescentDatum.subsetΓSpecLift_homTargetMap_comp_sectionsRingOnSubsetMap_snd`
  and `AlgebraicGeometry.DescentDatum.subsetΓSpecLift_homTargetMap_comp_legFst`: **the canonical
  embedding of `X ×_S W` carries the two legs of Stacks 0APJ to the two projections of `X ×_S W`
  followed by the canonical embedding of `W`.**
* `AlgebraicGeometry.DescentDatum.subsetΓSpecLift_opensι_legs`: the projection onto `Spec C₀`
  equalises the two legs of the restricted gluing isomorphism.
* `AlgebraicGeometry.DescentDatum.isEffective_restrictOpen_of_isPushout`: that restriction is
  effective.
* `AlgebraicGeometry.DescentDatum.isEffective_restrictOpen_descentInvariants`: **the obligation
  `hrestrict` of `AlgebraicGeometry.DescentDatum.isEffective_of_legs_of_restrictOpen`**, with `C₀`
  the subalgebra of invariants of the transition isomorphism.

## Implementation notes

*How the projection is shown to be invariant.* The condition is an identity of morphisms
`W ×_S X ⟶ Spec C₀`, and the inclusion `W₀ ⟶ Spec C₀` is a monomorphism, so it suffices to prove
it after composing with that inclusion; there the projection becomes the canonical embedding `k`
of `W` followed by `Spec` of the inclusion of `C₀`. Both legs then factor through the canonical
embedding `ℓ` of `X ×_S W` into `Spec Γ(X ×_S E, 𝒪)`, by naturality of that embedding in the
subset — `AlgebraicGeometry.subsetΓSpecLift_comp_specMap_sectionsRingOnSubsetMap` — together with
its naturality in the source, `AlgebraicGeometry.comp_subsetΓSpecLift`. The remaining identity of
ring maps out of `C₀` is the hypothesis `hcompat`, which for the invariants is
`AlgebraicGeometry.ModuleCat.descentInvariants_comp_transition`.

*Why the embedding has to be a named morphism.* The two legs must be composites of **one** named
morphism `ℓ` with two different maps on sections, so that a single identity of ring maps closes
both. An existentially bound embedding is pinned only on points and against the restriction of
global functions, which does not determine it as a morphism into the affine scheme `Spec C`.

*Why `hcompat` is a hypothesis.* It is the only place where `C₀` has to be the invariants, so
taking it as a hypothesis keeps the construction independent of step 4 of the proof of Stacks
0APK; the specialisation below supplies it.

*No tag is placed.* These are steps in the proof of
[Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK), which is stated for arbitrary fpqc
covering families.

## References

* [Stacks Project, Tag 0API](https://stacks.math.columbia.edu/tag/0API)
* [Stacks Project, Tag 0APJ](https://stacks.math.columbia.edu/tag/0APJ)
* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace DescentDatum

variable {S X : Scheme.{u}} {f : X ⟶ S} (D : DescentDatum f) (E : Set D.over.left)
    (W : D.over.left.Opens) (hWinv : D.IsTransitionInvariant W)
    (hWE : (W : Set D.over.left) ⊆ E)

/-! ### The canonical embedding of `X ×_S W` -/

include hWE in
/-- The base change along `f` of the inclusion of an invariant open contained in `E` lands in the
preimage of `E` under the second projection. -/
lemma univ_subset_preimage_homTargetMap :
    (Set.univ : Set ↥(pullback f ((D.restrictOpen W hWinv).over.hom ≫ f))) ⊆
      ⇑(homTargetMap (D.restrictOpenHom W hWinv)) ⁻¹'
        (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) := by
  intro z _
  have hz : (pullback.snd f (D.over.hom ≫ f))
        ((homTargetMap (D.restrictOpenHom W hWinv)) z) =
      W.ι ((pullback.snd f ((D.restrictOpen W hWinv).over.hom ≫ f)) z) := by
    rw [← Scheme.Hom.comp_apply, homTargetMap_comp_snd, Scheme.Hom.comp_apply,
      restrictOpenHom_hom_left]
    rfl
  rw [Set.mem_preimage, Set.mem_preimage, hz]
  exact hWE ((pullback.snd f ((D.restrictOpen W hWinv).over.hom ≫ f)) z).2

variable (h₁ : (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) ⊆
      ⇑D.transitionPullbackIso.hom ⁻¹' (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E))
    (h₂ : (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) ⊆
      ⇑D.transitionPullbackIso.inv ⁻¹' (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E))

include hWE in
/-- **The canonical embedding of `X ×_S W` carries the second leg of Stacks 0APJ to the second
projection** followed by the canonical embedding of `W`. -/
@[reassoc]
lemma subsetΓSpecLift_homTargetMap_comp_sectionsRingOnSubsetMap_snd :
    subsetΓSpecLift (homTargetMap (D.restrictOpenHom W hWinv))
          (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E)
          (univ_subset_preimage_homTargetMap D E W hWinv hWE) ≫
        Spec.map (Scheme.sectionsRingOnSubsetMap (pullback.snd f (D.over.hom ≫ f)) E
          (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) (Set.Subset.refl _)) =
      pullback.snd f ((D.restrictOpen W hWinv).over.hom ≫ f) ≫
        subsetΓSpecLift W.ι E (univ_subset_preimage_opensι E W hWE) := by
  have he : homTargetMap (D.restrictOpenHom W hWinv) ≫ pullback.snd f (D.over.hom ≫ f) =
      pullback.snd f ((D.restrictOpen W hWinv).over.hom ≫ f) ≫ W.ι :=
    (homTargetMap_comp_snd (D.restrictOpenHom W hWinv)).trans
      (congrArg (fun t ↦ pullback.snd f ((D.restrictOpen W hWinv).over.hom ≫ f) ≫ t)
        (restrictOpenHom_hom_left D W hWinv))
  have hc : (Set.univ : Set ↥(pullback f ((D.restrictOpen W hWinv).over.hom ≫ f))) ⊆
      (pullback.snd f ((D.restrictOpen W hWinv).over.hom ≫ f) ≫ W.ι).base ⁻¹' E :=
    univ_subset_preimage_comp _ W.ι (univ_subset_preimage_opensι E W hWE)
      (univ_subset_preimage_univ _)
  rw [subsetΓSpecLift_comp_specMap_sectionsRingOnSubsetMap]
  exact (subsetΓSpecLift_congr he E _ hc).trans
    (subsetΓSpecLift_comp_left _ W.ι E (univ_subset_preimage_opensι E W hWE) hc)

include hWE h₂ in
/-- **The canonical embedding of `X ×_S W` carries the first leg of Stacks 0APJ to the first
projection**, read through the restricted gluing isomorphism. -/
@[reassoc]
lemma subsetΓSpecLift_homTargetMap_comp_legFst :
    subsetΓSpecLift (homTargetMap (D.restrictOpenHom W hWinv))
          (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E)
          (univ_subset_preimage_homTargetMap D E W hWinv hWE) ≫
        Spec.map (Scheme.sectionsRingOnSubsetMap (pullback.fst (D.over.hom ≫ f) f) E
            (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) (Set.Subset.refl _) ≫
          (D.transitionSectionsIso E h₁ h₂).hom) =
      (D.restrictOpen W hWinv).transitionPullbackIso.inv ≫
        pullback.fst ((D.restrictOpen W hWinv).over.hom ≫ f) f ≫
          subsetΓSpecLift W.ι E (univ_subset_preimage_opensι E W hWE) := by
  have hq : (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) ⊆
      ⇑(D.transitionPullbackIso.inv ≫ pullback.fst (D.over.hom ≫ f) f) ⁻¹' E :=
    fun _ hz ↦ h₂ hz
  have hleg : Scheme.sectionsRingOnSubsetMap (pullback.fst (D.over.hom ≫ f) f) E
        (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) (Set.Subset.refl _) ≫
      (D.transitionSectionsIso E h₁ h₂).hom =
      Scheme.sectionsRingOnSubsetMap
        (D.transitionPullbackIso.inv ≫ pullback.fst (D.over.hom ≫ f) f) E
        (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) hq :=
    Scheme.sectionsRingOnSubsetMap_comp D.transitionPullbackIso.inv
      (pullback.fst (D.over.hom ≫ f) f) E (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E)
      (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) (Set.Subset.refl _) h₂
  have hminv : homTargetMap (D.restrictOpenHom W hWinv) ≫ D.transitionPullbackIso.inv =
      (D.restrictOpen W hWinv).transitionPullbackIso.inv ≫
        homSourceMap (D.restrictOpenHom W hWinv) := by
    rw [Iso.comp_inv_eq, Category.assoc,
      transitionPullbackIso_naturality (D.restrictOpenHom W hWinv), Iso.inv_hom_id_assoc]
  have hmφ : homTargetMap (D.restrictOpenHom W hWinv) ≫
        D.transitionPullbackIso.inv ≫ pullback.fst (D.over.hom ≫ f) f =
      (D.restrictOpen W hWinv).transitionPullbackIso.inv ≫
        pullback.fst ((D.restrictOpen W hWinv).over.hom ≫ f) f ≫ W.ι := by
    rw [← Category.assoc, hminv, Category.assoc,
      homSourceMap_comp_fst (D.restrictOpenHom W hWinv), restrictOpenHom_hom_left]
  have hc2 : (Set.univ : Set ↥(pullback ((D.restrictOpen W hWinv).over.hom ≫ f) f)) ⊆
      (pullback.fst ((D.restrictOpen W hWinv).over.hom ≫ f) f ≫ W.ι).base ⁻¹' E :=
    univ_subset_preimage_comp _ W.ι (univ_subset_preimage_opensι E W hWE)
      (univ_subset_preimage_univ _)
  have hc1 : (Set.univ : Set ↥(pullback f ((D.restrictOpen W hWinv).over.hom ≫ f))) ⊆
      ((D.restrictOpen W hWinv).transitionPullbackIso.inv ≫
        pullback.fst ((D.restrictOpen W hWinv).over.hom ≫ f) f ≫ W.ι).base ⁻¹' E :=
    univ_subset_preimage_comp _ _ hc2 (univ_subset_preimage_univ _)
  rw [hleg, subsetΓSpecLift_comp_specMap_sectionsRingOnSubsetMap]
  refine (subsetΓSpecLift_congr hmφ E _ hc1).trans
    ((subsetΓSpecLift_comp_left _ _ E hc2 hc1).trans ?_)
  exact congrArg (fun t ↦ (D.restrictOpen W hWinv).transitionPullbackIso.inv ≫ t)
    (subsetΓSpecLift_comp_left _ W.ι E (univ_subset_preimage_opensι E W hWE) hc2)

include hWE h₁ h₂ in
/-- **The projection onto `Spec R₀` equalises the two legs of the restricted gluing
isomorphism**, as soon as the ring map `R₀ ⟶ Γ(E, 𝒪_V|_E)` equalises the two comparison legs of
[Stacks, Tag 0APJ](https://stacks.math.columbia.edu/tag/0APJ). -/
theorem subsetΓSpecLift_opensι_legs {R₀ : CommRingCat.{u}}
    (ι₀ : R₀ ⟶ D.over.left.sectionsRingOnSubset E)
    (hcompat : ι₀ ≫ (Scheme.sectionsRingOnSubsetMap (pullback.fst (D.over.hom ≫ f) f) E
            (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) (Set.Subset.refl _) ≫
          (D.transitionSectionsIso E h₁ h₂).hom) =
        ι₀ ≫ Scheme.sectionsRingOnSubsetMap (pullback.snd f (D.over.hom ≫ f)) E
          (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) (Set.Subset.refl _)) :
    (D.restrictOpen W hWinv).transitionPullbackIso.hom ≫
        pullback.snd f ((D.restrictOpen W hWinv).over.hom ≫ f) ≫
          subsetΓSpecLift W.ι E (univ_subset_preimage_opensι E W hWE) ≫ Spec.map ι₀ =
      pullback.fst ((D.restrictOpen W hWinv).over.hom ≫ f) f ≫
        subsetΓSpecLift W.ι E (univ_subset_preimage_opensι E W hWE) ≫ Spec.map ι₀ := by
  have hmid : Spec.map (Scheme.sectionsRingOnSubsetMap (pullback.snd f (D.over.hom ≫ f)) E
          (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) (Set.Subset.refl _)) ≫ Spec.map ι₀ =
      Spec.map (Scheme.sectionsRingOnSubsetMap (pullback.fst (D.over.hom ≫ f) f) E
            (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) (Set.Subset.refl _) ≫
          (D.transitionSectionsIso E h₁ h₂).hom) ≫ Spec.map ι₀ := by
    rw [← Spec.map_comp, ← Spec.map_comp, hcompat]
  have hsnd := subsetΓSpecLift_homTargetMap_comp_sectionsRingOnSubsetMap_snd_assoc D E W hWinv
    hWE (Spec.map ι₀)
  have hfst := subsetΓSpecLift_homTargetMap_comp_legFst_assoc D E W hWinv hWE h₁ h₂
    (Spec.map ι₀)
  rw (config := { transparency := .default }) [Category.assoc (pullback.snd _ _)] at hsnd
  rw (config := { transparency := .default }) [Category.assoc (pullback.fst _ _)] at hfst
  rw [← hsnd, hmid, hfst, Iso.hom_inv_id_assoc]

/-! ### The descended scheme -/

variable [Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤)] [Algebra ↥Γ(S, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
    [Algebra ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
    [IsScalarTower ↥Γ(S, ⊤) ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
    [IsAffine S] [IsAffine X] [Flat f] [QuasiSeparatedSpace D.over.left]
    [IsIndQuasiAffineHom D.over.hom]
    {I : Type u} [Nonempty I] (U : I → D.over.left.Opens)
    (hU : ∀ i, IsCompact (U i : Set D.over.left)) (hE : E = ⋂ i, (U i : Set D.over.left))
    (C₀ : Type u) [CommRing C₀] [Algebra ↥Γ(S, ⊤) C₀]
    [Algebra C₀ ↥(D.over.left.sectionsRingOnSubset E)]
    [IsScalarTower ↥Γ(S, ⊤) C₀ ↥(D.over.left.sectionsRingOnSubset E)]

include hWE h₁ h₂ hU hE in
/-- **The scheme over `S` descending the restriction of a descent datum to an invariant open.**
Its scheme is the open `W₀` of `Spec C₀` which the image of `W` under the canonical embedding of
[Stacks, Tag 0API](https://stacks.math.columbia.edu/tag/0API) pulls back from, and its projection
is the canonical embedding of `W` followed by the spectrum of the inclusion of `C₀`. -/
def descendedRestrictOpen
    (hRA : CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)) = f.appTop)
    (hAC : CommRingCat.ofHom (algebraMap ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)) =
      D.over.hom.appTop ≫ D.over.left.topToSubset E)
    (hpo : Algebra.IsPushout ↥Γ(S, ⊤) ↥Γ(X, ⊤) C₀ ↥(D.over.left.sectionsRingOnSubset E))
    (hcompat : CommRingCat.ofHom (algebraMap C₀ ↥(D.over.left.sectionsRingOnSubset E)) ≫
          (Scheme.sectionsRingOnSubsetMap (pullback.fst (D.over.hom ≫ f) f) E
              (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) (Set.Subset.refl _) ≫
            (D.transitionSectionsIso E h₁ h₂).hom) =
        CommRingCat.ofHom (algebraMap C₀ ↥(D.over.left.sectionsRingOnSubset E)) ≫
          Scheme.sectionsRingOnSubsetMap (pullback.snd f (D.over.hom ≫ f)) E
            (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) (Set.Subset.refl _))
    (W₀ : (Spec (CommRingCat.of C₀)).Opens)
    (hW₀ : ((Spec.map (CommRingCat.ofHom
            (algebraMap C₀ ↥(D.over.left.sectionsRingOnSubset E))) ⁻¹ᵁ W₀ :
          (Spec (CommRingCat.of ↥(D.over.left.sectionsRingOnSubset E))).Opens) :
        Set (Spec (CommRingCat.of ↥(D.over.left.sectionsRingOnSubset E)))) =
      subsetΓSpecImage D.over.left E (W : Set D.over.left)) :
    (D.restrictOpen W hWinv).Descended := by
  have hV : IsIndQuasiAffine D.over.left := isIndQuasiAffine_of_isIndQuasiAffineHom_hom D.over
  have hpre : Set.range (subsetΓSpecLift W.ι E (univ_subset_preimage_opensι E W hWE)).base =
      ((Spec.map (CommRingCat.ofHom (algebraMap C₀ ↥(D.over.left.sectionsRingOnSubset E)))
            ⁻¹ᵁ W₀ :
          (Spec (CommRingCat.of ↥(D.over.left.sectionsRingOnSubset E))).Opens) :
        Set (Spec (CommRingCat.of ↥(D.over.left.sectionsRingOnSubset E)))) :=
    (range_subsetΓSpecLift_opensι E W hWE).trans hW₀.symm
  have hoi : IsOpenImmersion (subsetΓSpecLift W.ι E (univ_subset_preimage_opensι E W hWE)) :=
    isOpenImmersion_subsetΓSpecLift_opensι D.over.left U hU E hE W hWE
  have he : subsetΓSpecLift W.ι E (univ_subset_preimage_opensι E W hWE) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E))) ≫ X.isoSpec.inv =
      (D.restrictOpen W hWinv).over.hom :=
    (congrArg (fun ψ ↦ subsetΓSpecLift W.ι E (univ_subset_preimage_opensι E W hWE) ≫
        Spec.map ψ ≫ X.isoSpec.inv) hAC).trans
      (comp_specMap_appTop_isoSpec_inv_eq D.over.hom (D.over.left.topToSubset E) W
        (subsetΓSpecLift_comp_specMap_topToSubset W.ι E
          (univ_subset_preimage_opensι E W hWE)))
  refine
    { base := Over.mk (W₀.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) C₀)) ≫
        S.isoSpec.inv)
      proj := liftOpenPreimage (subsetΓSpecLift W.ι E (univ_subset_preimage_opensι E W hWE))
        (Spec.map (CommRingCat.ofHom (algebraMap C₀ ↥(D.over.left.sectionsRingOnSubset E))))
        W₀ hpre
      isPullback := by
        rw [← he]
        exact isPullback_liftOpenPreimage
          (isPullback_specMap_algebraMap_of_isPushout f C₀
            ↥(D.over.left.sectionsRingOnSubset E) hRA hpo) W₀
          (subsetΓSpecLift W.ι E (univ_subset_preimage_opensι E W hWE)) hpre
      proj_invariant := ?_ }
  refine (cancel_mono W₀.ι).mp ?_
  have hpι : liftOpenPreimage (subsetΓSpecLift W.ι E (univ_subset_preimage_opensι E W hWE))
        (Spec.map (CommRingCat.ofHom
          (algebraMap C₀ ↥(D.over.left.sectionsRingOnSubset E)))) W₀ hpre ≫ W₀.ι =
      subsetΓSpecLift W.ι E (univ_subset_preimage_opensι E W hWE) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap C₀ ↥(D.over.left.sectionsRingOnSubset E))) :=
    liftOpenPreimage_comp_ι _ _ W₀ hpre
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z ↦ (D.restrictOpen W hWinv).transitionPullbackIso.hom ≫ z)
        ((Category.assoc _ _ _).trans
          (congrArg (fun z ↦ pullback.snd f ((D.restrictOpen W hWinv).over.hom ≫ f) ≫ z)
            hpι))).trans
      ((subsetΓSpecLift_opensι_legs D E W hWinv hWE h₁ h₂ _ hcompat).trans
        ((congrArg (fun z ↦ pullback.fst ((D.restrictOpen W hWinv).over.hom ≫ f) f ≫ z)
            hpι.symm).trans (Category.assoc _ _ _).symm)))



omit [Flat f] [QuasiSeparatedSpace D.over.left] in
include hWE h₁ h₂ hU hE in
/-- **The restriction of a descent datum to an invariant open is effective**, as soon as the
functions on `E` are the base change of a `Γ(S, ⊤)`-algebra `C₀` whose inclusion equalises the two
comparison legs of [Stacks, Tag 0APJ](https://stacks.math.columbia.edu/tag/0APJ) and the image of
`W` descends to an open of `Spec C₀`. -/
theorem isEffective_restrictOpen_of_isPushout
    (hRA : CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)) = f.appTop)
    (hAC : CommRingCat.ofHom (algebraMap ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)) =
      D.over.hom.appTop ≫ D.over.left.topToSubset E)
    (hpo : Algebra.IsPushout ↥Γ(S, ⊤) ↥Γ(X, ⊤) C₀ ↥(D.over.left.sectionsRingOnSubset E))
    (hcompat : CommRingCat.ofHom (algebraMap C₀ ↥(D.over.left.sectionsRingOnSubset E)) ≫
          (Scheme.sectionsRingOnSubsetMap (pullback.fst (D.over.hom ≫ f) f) E
              (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) (Set.Subset.refl _) ≫
            (D.transitionSectionsIso E h₁ h₂).hom) =
        CommRingCat.ofHom (algebraMap C₀ ↥(D.over.left.sectionsRingOnSubset E)) ≫
          Scheme.sectionsRingOnSubsetMap (pullback.snd f (D.over.hom ≫ f)) E
            (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) (Set.Subset.refl _))
    (W₀ : (Spec (CommRingCat.of C₀)).Opens)
    (hW₀ : ((Spec.map (CommRingCat.ofHom
            (algebraMap C₀ ↥(D.over.left.sectionsRingOnSubset E))) ⁻¹ᵁ W₀ :
          (Spec (CommRingCat.of ↥(D.over.left.sectionsRingOnSubset E))).Opens) :
        Set (Spec (CommRingCat.of ↥(D.over.left.sectionsRingOnSubset E)))) =
      subsetΓSpecImage D.over.left E (W : Set D.over.left)) :
    DescentData.IsEffective (D.restrictOpen W hWinv) :=
  (descendedRestrictOpen D E W hWinv hWE h₁ h₂ U hU hE C₀ hRA hAC hpo hcompat W₀
    hW₀).isEffective

/-! ### The obligation `hrestrict` at the subalgebra of invariants -/

variable [Surjective f]
    (hRC : CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥(D.over.left.sectionsRingOnSubset E)) =
      (D.over.hom ≫ f).appTop ≫ D.over.left.topToSubset E)

include hWE h₁ h₂ hU hE hRC in
/-- **The obligation `hrestrict` of
`AlgebraicGeometry.DescentDatum.isEffective_of_legs_of_restrictOpen`.** For a surjective flat
morphism of affine schemes, an intersection `E` of a nonempty family of quasi-compact opens and an
invariant open `W ⊆ E`, the restriction of the datum to `W` is effective as soon as the image of
`W` under the canonical embedding of
[Stacks, Tag 0API](https://stacks.math.columbia.edu/tag/0API) descends to an open `W₀` of `Spec`
of the subalgebra of invariants of the transition isomorphism. -/
theorem isEffective_restrictOpen_descentInvariants
    (hRA : CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)) = f.appTop)
    (hAC : CommRingCat.ofHom (algebraMap ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)) =
      D.over.hom.appTop ≫ D.over.left.topToSubset E)
    (W₀ : (Spec (CommRingCat.of ↥(ModuleCat.descentInvariants ↥Γ(S, ⊤) ↥Γ(X, ⊤)
        ↥(D.over.left.sectionsRingOnSubset E)
        (D.descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂)))).Opens)
    (hW₀ : ((Spec.map (CommRingCat.ofHom (algebraMap
          (ModuleCat.descentInvariants ↥Γ(S, ⊤) ↥Γ(X, ⊤)
            ↥(D.over.left.sectionsRingOnSubset E)
            (D.descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂))
          ↥(D.over.left.sectionsRingOnSubset E))) ⁻¹ᵁ W₀ :
          (Spec (CommRingCat.of ↥(D.over.left.sectionsRingOnSubset E))).Opens) :
        Set (Spec (CommRingCat.of ↥(D.over.left.sectionsRingOnSubset E)))) =
      subsetΓSpecImage D.over.left E (W : Set D.over.left)) :
    DescentData.IsEffective (D.restrictOpen W hWinv) :=
  isEffective_restrictOpen_of_isPushout D E W hWinv hWE h₁ h₂ U hU hE
    ↥(ModuleCat.descentInvariants ↥Γ(S, ⊤) ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)
      (D.descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂))
    hRA hAC (D.isPushout_descentInvariants E hRA hRC hAC U hU hE h₁ h₂)
    (ModuleCat.descentInvariants_comp_transition
      (D.isPushout_algebraMap_transitionSource E hRA hRC U hU hE)
      (D.isPushout_algebraMap_transitionTarget E hRA hRC U hU hE)
      (D.transitionSectionsIso E h₁ h₂)
      (D.algebraMap_comp_transitionSectionsIso_hom E hAC h₁ h₂)
      (D.transitionSectionsIso_hom_eq_algebraMap_comp E hAC h₁ h₂))
    W₀ hW₀

end DescentDatum

end AlgebraicGeometry

end

end
