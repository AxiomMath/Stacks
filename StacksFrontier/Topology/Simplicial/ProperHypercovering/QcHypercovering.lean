module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ProperSurjectiveQcCovering
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiComparisonNaturality
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Map
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBySimplicialObject
public import StacksFrontier.Topology.Simplicial.ProperHypercoveringDescent
public import StacksFrontier.Topology.Simplicial.QcComparisonSquare
public import StacksFrontier.Topology.Sheaves.Functors.Pushforward.ProperPushforward

/-!
# A proper hypercovering is a hypercovering of the quasi-compact site

Let `U` be a simplicial object of the category `LC` of Hausdorff, locally quasi-compact spaces
and let `a : U → X` be an augmentation which is a proper hypercovering of `X` in the sense of
Stacks Section 09XA: `U₀ → X`, `U₁ → U₀ ×_X U₀` and the matching maps
`U_{n+1} → (cosk_n sk_n U)_{n+1}`, `n ≥ 1`, are proper and surjective. Let `LC_qc` be a site of
Stacks 09X2 containing `X` and every `U_n`. Then `U` is a hypercovering of `X` in `LC_qc` in the
sense of Stacks Section 09X8.

## Main results

* `Stacks.Topology.Simplicial.ProperHypercovering.singleton_mem_pretopology`: a morphism of
  `LC_qc` whose underlying map is proper and surjective generates a covering of the chosen
  pretopology of `LC_qc` (Stacks 09X5).
* `Stacks.Topology.Simplicial.ProperHypercovering.isHypercoveringAugmentation_qcLift`: a proper
  hypercovering of `LC`, read in a site `LC_qc` containing all its terms, is a hypercovering
  augmentation of `LC_qc` (Stacks 09X8).

## References

* [Stacks Project, Section 09XA](https://stacks.math.columbia.edu/tag/09XA)
* [Stacks Project, Tag 09X5](https://stacks.math.columbia.edu/tag/09X5)
* [Stacks Project, Section 09X8](https://stacks.math.columbia.edu/tag/09X8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open Stacks.CategoryTheory.Hypercovering

universe u w

namespace Stacks.Topology.Simplicial.ProperHypercovering

open Stacks.Topology Stacks.Topology.LocallyQuasiCompactZariskiSituation

/-! ### Proper surjections up to isomorphism -/

/-- Properness and surjectivity of the underlying map of a morphism of `LC`, in Mathlib's sense
of proper, are invariant under isomorphisms of arrows. -/
theorem isProperMap_surjective_of_arrowIso {f g : Arrow LocallyQuasiCompactHausdorff.{u}}
    (e : f ≅ g) (hf : _root_.IsProperMap (f.hom : f.left → f.right) ∧
      Function.Surjective (f.hom : f.left → f.right)) :
    _root_.IsProperMap (g.hom : g.left → g.right) ∧
      Function.Surjective (g.hom : g.left → g.right) := by
  let eL := TopCat.homeoOfIso (locallyQuasiCompactHausdorffToTop.mapIso (Arrow.leftFunc.mapIso e))
  let eR := TopCat.homeoOfIso
    (locallyQuasiCompactHausdorffToTop.mapIso (Arrow.rightFunc.mapIso e))
  have hg : (g.hom : g.left → g.right) = eR ∘ (f.hom : f.left → f.right) ∘ eL.symm := by
    rw [show g.hom = e.inv.left ≫ f.hom ≫ e.hom.right by simp]
    rfl
  rw [hg]
  exact ⟨eR.isProperMap.comp (hf.1.comp eL.symm.isProperMap),
    eR.surjective.comp (hf.2.comp eL.symm.surjective)⟩

/-- A proper surjection of `LC` in the sense of Stacks Section 09XA is proper in Mathlib's sense
and surjective. -/
theorem isProperMap_surjective_of_properSurjective {A B : LocallyQuasiCompactHausdorff.{u}}
    {f : A ⟶ B} (hf : properSurjective f) :
    _root_.IsProperMap (f : A → B) ∧ Function.Surjective (f : A → B) :=
  ⟨isProperMap_of_isProperMap (ConcreteCategory.hom f).continuous hf.1, hf.2⟩

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)

/-- **Stacks 09X5 in the site `LC_qc`.** A morphism of `LC_qc` whose underlying continuous map is
proper and surjective generates a covering of the chosen pretopology of `LC_qc`. -/
theorem singleton_mem_pretopology {A B : S.category} (f : A ⟶ B)
    (hf : _root_.IsProperMap (S.qcSite.inclusion.map f : A.obj → B.obj) ∧
      Function.Surjective (S.qcSite.inclusion.map f : A.obj → B.obj)) :
    Presieve.singleton f ∈ S.qcSite.pretopology B := by
  have hE : S.qcSite.IsQcCovering (PreZeroHypercover.singleton.{0} f) := by
    intro y
    obtain ⟨E, hEc, hE⟩ :=
      (isQcCovering_iff_single _).1 (proper_surjective_isQcCovering _ hf.1 hf.2) y
    exact ⟨{PUnit.unit}, fun _ => E, fun _ _ => hEc, Filter.mem_of_superset hE fun x hx =>
      Set.mem_biUnion (x := PUnit.unit) (Finset.mem_singleton_self _) hx⟩
  have h := (S.qcSite.isCovering_iff_isQcCovering _).2 hE
  rwa [LocallyQuasiCompactQcSite.IsCovering, PreZeroHypercover.presieve₀_singleton] at h

/-! ### The comparison of the defining families -/

section Comparison

attribute [local instance] boundedSiteInclusionCreatesPullbacks

variable {Y : SimplicialObject LocallyQuasiCompactHausdorff.{u}}
  {T : LocallyQuasiCompactHausdorff.{u}} (b : Y ⟶ (SimplicialObject.const _).obj T)
  (hY : ∀ n, S.qcSite.Contains (Y.obj n)) (hT : S.qcSite.Contains T)

/-- The inclusion `LC_qc ⥤ LC` preserves pullbacks. -/
instance preservesPullbacks_inclusion :
    PreservesLimitsOfShape WalkingCospan S.qcSite.inclusion :=
  preservesLimitOfShape_of_createsLimitsOfShape_and_hasLimitsOfShape _

/-- The two face maps `U₁ → U₀` of a simplicial object of `LC` agree after the augmentation,
read through the lift to `LC_qc`. -/
theorem faceMaps_comp_augmentation :
    Y.δ 1 ≫ S.qcSite.inclusion.map ((qcLiftAugmentation S b hY hT).app (op ⦋0⦌)) =
      Y.δ 0 ≫ S.qcSite.inclusion.map ((qcLiftAugmentation S b hY hT).app (op ⦋0⦌)) :=
  (by simp [SimplicialObject.δ, b.naturality] : Y.δ 1 ≫ b.app _ = Y.δ 0 ≫ b.app _)

/-- The degree-one map `U₁ → U₀ ×_X U₀` of the lift to `LC_qc`, read in `LC` and composed with
the comparison of fibre products, has the two face maps as components. -/
theorem inclusion_map_oneSimplexToFiberProduct_comp :
    S.qcSite.inclusion.map
        (oneSimplexToFiberProduct (qcLift S Y hY) (qcLiftAugmentation S b hY hT)) ≫
      pullbackComparison S.qcSite.inclusion ((qcLiftAugmentation S b hY hT).app (op ⦋0⦌))
        ((qcLiftAugmentation S b hY hT).app (op ⦋0⦌)) =
      pullback.lift (Y.δ 1) (Y.δ 0) (faceMaps_comp_augmentation S b hY hT) := by
  apply pullback.hom_ext <;>
    simp only [Category.assoc, pullbackComparison_comp_fst, pullbackComparison_comp_snd,
      ← Functor.map_comp, oneSimplexToFiberProduct, pullback.lift_fst, pullback.lift_snd] <;> rfl

/-- The degree-one map `U₁ → U₀ ×_X U₀` of the lift to `LC_qc`, read in `LC`, is proper and
surjective when the augmentation is a proper hypercovering. -/
theorem isProperMap_surjective_oneSimplexToFiberProduct
    (hyp : MorphismProperty.IsHypercovering properSurjective ⟨Y, T, b⟩) :
    _root_.IsProperMap (S.qcSite.inclusion.map
        (oneSimplexToFiberProduct (qcLift S Y hY) (qcLiftAugmentation S b hY hT)) : _ → _) ∧
      Function.Surjective (S.qcSite.inclusion.map
        (oneSimplexToFiberProduct (qcLift S Y hY) (qcLiftAugmentation S b hY hT)) : _ → _) := by
  have h : _root_.IsProperMap
        (pullback.lift (Y.δ 1) (Y.δ 0) (faceMaps_comp_augmentation S b hY hT) : _ → _) ∧
      Function.Surjective
        (pullback.lift (Y.δ 1) (Y.δ 0) (faceMaps_comp_augmentation S b hY hT) : _ → _) :=
    isProperMap_surjective_of_properSurjective hyp.map_one
  refine isProperMap_surjective_of_arrowIso (Arrow.isoMk
    (f := Arrow.mk (S.qcSite.inclusion.map
      (oneSimplexToFiberProduct (qcLift S Y hY) (qcLiftAugmentation S b hY hT))))
    (g := Arrow.mk (pullback.lift (Y.δ 1) (Y.δ 0) (faceMaps_comp_augmentation S b hY hT)))
    (Iso.refl _)
    (asIso (pullbackComparison S.qcSite.inclusion ((qcLiftAugmentation S b hY hT).app (op ⦋0⦌))
      ((qcLiftAugmentation S b hY hT).app (op ⦋0⦌)))) ?_).symm h
  rw [Iso.refl_hom, Category.id_comp, asIso_hom]
  exact (inclusion_map_oneSimplexToFiberProduct_comp S b hY hT).symm

/-- The simplicial object of `LC/X` attached to the lift of the augmentation to `LC_qc`, carried
back to `LC`, is the simplicial object of `LC/X` attached to the augmentation itself. -/
theorem overLift_comp_post :
    Over.lift (qcLift S Y hY) (qcLiftAugmentation S b hY hT) ⋙
        Over.post (X := (⟨T, hT⟩ : S.category)) S.qcSite.inclusion =
      SimplicialObject.Augmented.over ⟨Y, T, b⟩ :=
  rfl

/-- The `n`-th matching map of the lift to `LC_qc`, read in `LC`, is the `n`-th matching map of
the augmentation in `LC`, up to an isomorphism of arrows. -/
theorem nonempty_matchingArrowIso (n : ℕ) :
    Nonempty (Arrow.mk (S.qcSite.inclusion.map
        (matchingMap (qcLift S Y hY) (qcLiftAugmentation S b hY hT) n)) ≅
      SimplicialObject.Augmented.matchingArrow ⟨Y, T, b⟩ n) := by
  let F := Over.post (X := (⟨T, hT⟩ : S.category)) S.qcSite.inclusion
  have : PreservesFiniteLimits F := Over.preservesFiniteLimitsPost _ _
  obtain ⟨e, he⟩ := exists_iso_map_coskAdj_unit_app n
    (Over.lift (qcLift S Y hY) (qcLiftAugmentation S b hY hT)) F (op ⦋n + 1⦌)
  refine ⟨Arrow.isoMk (Iso.refl _) ((Over.forget T).mapIso e) ?_⟩
  have h := congrArg (fun φ => (Over.forget T).map φ) he
  simp only [Functor.map_comp] at h
  exact (Category.id_comp _).trans h.symm

end Comparison

/-! ### The proper hypercovering is a hypercovering of `LC_qc` -/

/-- A proper hypercovering is a hypercovering of the quasi-compact site. Let `U` be a simplicial
object of `LC` and `a : U → X` an augmentation which is a proper hypercovering of `X` (Stacks
Section 09XA), and let `LC_qc` be a site of Stacks 09X2 containing `X` and every `U_n`. Then
`U → X`, read in `LC_qc`, is a hypercovering of `X` in `LC_qc` in the sense of Stacks
Section 09X8. -/
theorem isHypercoveringAugmentation_qcLift {Y : SimplicialObject LocallyQuasiCompactHausdorff.{u}}
    {T : LocallyQuasiCompactHausdorff.{u}} (b : Y ⟶ (SimplicialObject.const _).obj T)
    (hyp : MorphismProperty.IsHypercovering properSurjective ⟨Y, T, b⟩)
    (hY : ∀ n, S.qcSite.Contains (Y.obj n)) (hT : S.qcSite.Contains T) :
    IsHypercoveringAugmentation S.qcSite.pretopology (qcLift S Y hY)
      (qcLiftAugmentation S b hY hT) := by
  refine ⟨?_, ?_, fun n _ => ?_⟩
  · exact singleton_mem_pretopology S _ (isProperMap_surjective_of_properSurjective hyp.map_zero)
  · exact singleton_mem_pretopology S _
      (isProperMap_surjective_oneSimplexToFiberProduct S b hY hT hyp)
  · obtain ⟨e⟩ := nonempty_matchingArrowIso S b hY hT n
    exact singleton_mem_pretopology S _ (isProperMap_surjective_of_arrowIso e.symm
      (isProperMap_surjective_of_properSurjective (hyp.matching n ‹_›)))

end Stacks.Topology.Simplicial.ProperHypercovering

end
