module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemmaLocallyNoetherianBase
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowNoetherianCase
public import StacksFrontier.AlgebraicGeometry.Stacks.RefinedValuativeCriterionAffine

/-!
# The refined Noetherian valuative criterion of properness for algebraic stacks (Stacks 0CQM)

Let `f : 𝒳 ⟶ 𝒴` and `h : 𝒰 ⟶ 𝒳` be 1-morphisms of algebraic stacks, with `𝒴` locally Noetherian,
`f` and `h` of finite type, `f` separated and the image of `|h| : |𝒰| → |𝒳|` dense in `|𝒳|`.
If every 2-commutative diagram `Spec K ⟶ 𝒰 ⟶ 𝒳`, `Spec A ⟶ 𝒴`, with `A` a discrete valuation
ring with fraction field `K`, admits a dotted arrow for `f` after an extension `K'/K` of fields
and passage to a valuation ring `A' ⊂ K'` dominating `A`, then `f` is proper. This is
[Stacks, Tag 0CQM].

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isProper_of_discreteExistenceAlong`: Stacks 0CQM.
* `AlgebraicGeometry.Stack.AlgebraicStacks.universallyClosed_of_discreteExistenceAlong_affineCore`:
  its affine case: an affine locally Noetherian base and an affine source.

## Implementation notes

The hypothesis is `AlgebraicGeometry.Stack.ValuativeCriterion.DiscreteExistenceAlong`: every
valuative square for `f` (Stacks 0CLK, `AlgebraicGeometry.Stack.ValuativeSquare`, whose `γ` is
the 2-arrow of the diagram) over a discrete valuation ring whose generic point is `u ≫ h` admits
a dotted arrow (Stacks 0CLA) after an extension of the fraction field and passage to a
dominating valuation ring. As everywhere in this library, the spectra of the valuation rings and
of the fields involved are objects of the chosen big fppf site.

The proof is the source's. The reduction to an affine locally Noetherian base and an affine
source is `AlgebraicStacks.isProper_of_discreteExistenceAlong_of_affineCore`.
The affine case is the proof of
`AlgebraicGeometry.Stack.AlgebraicStacks.universallyClosed_of_discreteExistenceAlong_of_chow`,
with Chow's lemma for algebraic stacks (Stacks 0CQ8) over the Noetherian algebraic space of the
base, which is `AlgebraicGeometry.Stack.AlgebraicStacks.hasChowCover_of_isNoetherian`.

## References

* [Stacks Project, Tag 0CQM](https://stacks.math.columbia.edu/tag/0CQM)
* [Stacks Project, Tag 0CQ8](https://stacks.math.columbia.edu/tag/0CQ8)
* [Stacks Project, Tag 0CMD](https://stacks.math.columbia.edu/tag/0CMD)
* [Stacks Project, Tag 0CQK](https://stacks.math.columbia.edu/tag/0CQK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace AlgebraicStacks

/-- **The affine case of Stacks 0CQM.** Let `V` be an affine locally Noetherian scheme of the
site, `f : 𝒳 ⟶ V` a separated 1-morphism of finite type from an algebraic stack, and
`h : U ⟶ 𝒳` a 1-morphism locally of finite type from an affine scheme `U` with dense image, such
that `f` satisfies the discrete existence part of the valuative criterion along `h`. Then `f` is
universally closed.

The proof is the source's, as in `universallyClosed_of_discreteExistenceAlong_of_chow`. Chow's
lemma over the Noetherian algebraic space `h_V` (`hasChowCover_of_isNoetherian`) gives a proper
surjective `a : X ⟶ 𝒳` from an algebraic space whose composite to `V` is a morphism of
algebraic spaces `g`. The 2-fibre product `W = X ×_𝒳 U` is an algebraic space of finite type over
`X`. On the reduced closed subspace `X'` of `X` on the closure of the image of `W`, the morphism
`X' ⟶ V` is proper by the case of algebraic spaces (Stacks 0CMD), fed by the claim
`exists_dominatingExtension_lift_of_discreteExistenceAlong` and Stacks 0ARH; `X' ⟶ 𝒳` is still
surjective because its image is closed and contains the dense image of `h`, so Stacks 0CQK
makes `f` universally closed. -/
theorem universallyClosed_of_discreteExistenceAlong_affineCore
    (V : BigFppfOver B S hS) (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (hVN : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V))
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (f : 𝒳 ⟶ schemeStack.{u, w} B S hS V)
    (hf : IsFiniteType B S hS f) (hsep : IsSeparated B S hS f)
    (U : BigFppfOver B S hS) (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (h : schemeStack.{u, w} B S hS U ⟶ 𝒳) (hh : IsLocallyOfFiniteType B S hS h)
    (hdense : @Dense _ (pointTopology B S hS 𝒳.val) (Set.range (pointsMap B S hS h)))
    (hlift : ValuativeCriterion.DiscreteExistenceAlong B S hS h f) :
    UniversallyClosed B S hS f := by
  classical
  have hY := isAlgebraicSpace_yoneda B S hS V
  have hVN' := (Space.exists_atlas_iff_of_representable B S hS (yoneda.obj V)
    (fun T : Scheme.{u} => IsLocallyNoetherian T) V (Iso.refl _)).mpr hVN
  -- the algebraic stack of `V` against that of the algebraic space `h_V`
  obtain ⟨e, he⟩ := exists_oneMorphism_representingMap_eq B S hS
    (𝒳 := schemeStack.{u, w} B S hS V) (𝒴 := algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) hY)
    (yoneda.obj V) (yoneda.obj V) (PresheafOfCategories.sliceElementsEquivalenceOver V)
    (StacksRepresentableCFG.EquivalenceOver.refl
      (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) hY).val.val.p) (𝟙 _)
  have heP : IsProper B S hS e := by
    refine (isProper_iff_isProper_representingMap B S hS (yoneda.obj V) (yoneda.obj V)
      (PresheafOfCategories.sliceElementsEquivalenceOver V)
      (StacksRepresentableCFG.EquivalenceOver.refl
        (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) hY).val.val.p) e hY hY).2 ?_
    rw [he]
    exact Space.isProper_of_isIso B S hS _
  -- Chow's lemma for `𝒳 ⟶ h_V`
  obtain ⟨X, Xbar, hX, -, a, i, p, ha, hasurj, -, -, ⟨θ⟩⟩ := hasChowCover_of_isNoetherian hY
    ⟨Space.isQuasiCompactSpace_yoneda_of_isAffine B S hS V hV,
      Space.isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS _
        (Space.isAffineSpace_yoneda B S hS V hV),
      hVN'⟩ (f ≫ e)
    (isSeparated_comp B S hS f e hsep heP.1) (isFiniteType_comp B S hS f e hf heP.2.1)
  have hg : representingMap B S hS (algebraicSpaceStack.{u, w} B S hS X hX).val
      (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) hY).val X (yoneda.obj V)
      (StacksRepresentableCFG.EquivalenceOver.refl
        (algebraicSpaceStack.{u, w} B S hS X hX).val.val.p)
      (StacksRepresentableCFG.EquivalenceOver.refl
        (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) hY).val.val.p)
      (a.hom ≫ f.hom ≫ e.hom) = i ≫ p :=
    (representingMap_congr_twoIso B S hS X (yoneda.obj V)
      (StacksRepresentableCFG.EquivalenceOver.refl
        (algebraicSpaceStack.{u, w} B S hS X hX).val.val.p)
      (StacksRepresentableCFG.EquivalenceOver.refl
        (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) hY).val.val.p)
      (InducedBicategory.isoHom θ)).trans (representingMap_associatedMap B S hS X (yoneda.obj V) _)
  have hgsep : Space.IsSeparated B S hS (i ≫ p) := by
    rw [← hg]
    exact (isSeparated_iff_isSeparated_representingMap B S hS X (yoneda.obj V) _ _ (a ≫ f ≫ e)
      hX hY).1 (isSeparated_comp B S hS a (f ≫ e) ha.1 (isSeparated_comp B S hS f e hsep heP.1))
  have hgft : Space.IsFiniteType B S hS (i ≫ p) := by
    rw [← hg]
    exact (isFiniteType_iff_isFiniteType_representingMap B S hS X (yoneda.obj V) _ _ (a ≫ f ≫ e)
      hX hY).1 (isFiniteType_comp B S hS a (f ≫ e) ha.2.1 (isFiniteType_comp B S hS f e hf heP.2.1))
  -- `W = X ×_𝒳 U` is an algebraic space (Stacks 0300)
  obtain ⟨W, hW, ⟨eW⟩⟩ := Stack.isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒳.val
    (schemeStack.{u, w} B S hS U).val (algebraicSpaceStack.{u, w} B S hS X hX).val h.hom.hom
    a.hom.hom (isRepresentableByAlgebraicSpaces_of_representing B S hS X a hX
      (StacksRepresentableCFG.EquivalenceOver.refl
        (algebraicSpaceStack.{u, w} B S hS X hX).val.val.p))
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U)
  have eW' : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductSquareAlgebraicStacks B S hS h a).pt.val.val.p
      (presheafOfCategories (W ⋙ typeToCat)).p := eW
  clear eW
  have hP := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS h a
  -- the projection `W ⟶ X` is of finite type
  have hwft : Space.IsFiniteType B S hS (representingMap B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS h a).pt.val
      (algebraicSpaceStack.{u, w} B S hS X hX).val W X eW'
      (StacksRepresentableCFG.EquivalenceOver.refl
        (algebraicSpaceStack.{u, w} B S hS X hX).val.val.p)
      (twoFibreProductSquareAlgebraicStacks B S hS h a).snd.hom) := by
    refine ⟨(isLocallyOfFiniteType_iff_isLocallyOfFiniteType_representingMap B S hS W X eW' _
      (twoFibreProductSquareAlgebraicStacks B S hS h a).snd hW hX).1
        (isLocallyOfFiniteType_baseChange B S hS h a
          (twoFibreProductSquareAlgebraicStacks B S hS h a).swap
          (Bicategory.isTwoFibreProduct_swap hP) hh), ?_⟩
    have hU' : Space.IsProper B S hS (representingMap B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS h a).pt.val
        (schemeStack.{u, w} B S hS U).val W (yoneda.obj U) eW'
        (PresheafOfCategories.sliceElementsEquivalenceOver U)
        (twoFibreProductSquareAlgebraicStacks B S hS h a).fst.hom) :=
      (isProper_iff_isProper_representingMap B S hS W (yoneda.obj U) eW' _
        (twoFibreProductSquareAlgebraicStacks B S hS h a).fst hW
        (isAlgebraicSpace_yoneda B S hS U)).1 (isProper_baseChange B S hS a h _ hP ha)
    have hcomp := representingMap_fst_comp_eq B S hS h hX a hY (f ≫ e) W eW'
    rw [show (f ≫ e).hom = f.hom ≫ e.hom from rfl, hg] at hcomp
    have hUV : representingMap B S hS (schemeStack.{u, w} B S hS U).val
        (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) hY).val (yoneda.obj U) (yoneda.obj V)
        (PresheafOfCategories.sliceElementsEquivalenceOver U)
        (StacksRepresentableCFG.EquivalenceOver.refl
          (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) hY).val.val.p)
        (h.hom ≫ f.hom ≫ e.hom) = yoneda.map (siteMap B S hS (h ≫ f)) := by
      rw [representingMap_congr_twoIso B S hS (𝒜 := (schemeStack.{u, w} B S hS U).val)
        (𝒞 := (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) hY).val) _ _
        (PresheafOfCategories.sliceElementsEquivalenceOver U)
        (StacksRepresentableCFG.EquivalenceOver.refl
          (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) hY).val.val.p)
        (α_ h.hom f.hom e.hom).symm,
        representingMap_comp B S hS (𝒜 := (schemeStack.{u, w} B S hS U).val)
          (ℬ := (schemeStack.{u, w} B S hS V).val)
          (𝒞 := (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) hY).val) _ _ _
          (PresheafOfCategories.sliceElementsEquivalenceOver U)
          (PresheafOfCategories.sliceElementsEquivalenceOver V)
          (StacksRepresentableCFG.EquivalenceOver.refl
            (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) hY).val.val.p) (h.hom ≫ f.hom) e.hom,
        he, Category.comp_id]
      exact representingMap_eq_yoneda_map_siteMap B S hS (h ≫ f)
    rw [representingMap_comp B S hS (𝒜 := (twoFibreProductSquareAlgebraicStacks B S hS h a).pt.val)
      (ℬ := (schemeStack.{u, w} B S hS U).val)
      (𝒞 := (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) hY).val) W _ _ eW'
      (PresheafOfCategories.sliceElementsEquivalenceOver U)
      (StacksRepresentableCFG.EquivalenceOver.refl
        (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) hY).val.val.p) _ _, hUV] at hcomp
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj V) := hV
    refine Space.isQuasiCompact_of_comp_of_isQuasiSeparated B S hS _ (i ≫ p) hW hY ?_
      (Space.isQuasiSeparated_of_isSeparated B S hS hgsep)
    rw [← hcomp]
    exact Space.IsQuasiCompact.comp B S hS (isAlgebraicSpace_yoneda B S hS U) hY hU'.2.1.2
      (Space.isQuasiCompact_yoneda_map_of_isAffineHom B S hS _ inferInstance)
  obtain ⟨wX, hwX⟩ : ∃ wX, representingMap B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS h a).pt.val
      (algebraicSpaceStack.{u, w} B S hS X hX).val W X eW'
      (StacksRepresentableCFG.EquivalenceOver.refl
        (algebraicSpaceStack.{u, w} B S hS X hX).val.val.p)
      (twoFibreProductSquareAlgebraicStacks B S hS h a).snd.hom = wX := ⟨_, rfl⟩
  rw [hwX] at hwft
  -- the reduced closed subspace `X'` of `X` on the closure of the image of `W`
  let := Space.pointTopology B S hS X
  have hZ : _root_.IsClosed (closure (Set.range (Space.pointsMap B S hS W wX))) := isClosed_closure
  have hX' := Space.isAlgebraicSpace_reducedClosedSubspace B S hS X hX _ hZ
  have hι := Space.isClosedImmersion_ι_reducedClosedSubspace B S hS hX _ hZ
  have hιrange := Space.range_pointsMap_ι_reducedClosedSubspace B S hS X hX _ hZ
  -- the reduction `W_red` of `W` and its morphism to `X'` (Stacks 03JJ)
  let := Space.pointTopology B S hS W
  have hWr := Space.isAlgebraicSpace_reducedClosedSubspace B S hS W hW Set.univ isClosed_univ
  have hρrange := Space.range_pointsMap_ι_reducedClosedSubspace B S hS W hW Set.univ isClosed_univ
  have hρci := Space.isClosedImmersion_ι_reducedClosedSubspace B S hS hW Set.univ isClosed_univ
  obtain ⟨k, hk⟩ := (Space.exists_lift_reducedClosedSubspace_iff_pointsMap_range_subset B S hS X hX
    _ hZ hWr (Space.hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS W hW Set.univ
      isClosed_univ) ((Space.reducedClosedSubspace B S hS W hW Set.univ isClosed_univ).ι ≫ wX)).2
    (by
      rw [Space.pointsMap_comp, Set.range_comp]
      exact (Set.image_subset_range _ _).trans subset_closure)
  have := Space.mono_of_isClosedImmersion B S hS _ hι
  -- `X' ⟶ h_V` is proper (Stacks 0CMD)
  have hprop : Space.IsProper B S hS
      ((Space.reducedClosedSubspace B S hS X hX _ hZ).ι ≫ i ≫ p) := by
    have hkft : Space.IsFiniteType B S hS k := by
      have hcomp : Space.IsFiniteType B S hS
          (k ≫ (Space.reducedClosedSubspace B S hS X hX _ hZ).ι) := by
        rw [hk]
        exact Space.isFiniteType_comp B S hS hWr hW hX _ _
          (Space.isFiniteType_of_isClosedImmersion B S hS _ hρci) hwft
      exact ⟨Space.isLocallyOfFiniteType_of_comp B S hS hWr hX' hX _ _ hcomp.1,
        Space.isQuasiCompact_of_comp_mono B S hS _ _ hcomp.2⟩
    have hsepX' : Space.IsSeparated B S hS
        ((Space.reducedClosedSubspace B S hS X hX _ hZ).ι ≫ i ≫ p) :=
      Space.isSeparated_comp B S hS _ _ (Space.isSeparated_of_isClosedImmersion B S hS _ hι) hgsep
    refine Space.isProper_of_denseRange_of_exists_discreteLift hX' hY hWr _ k
      hVN'
      (Space.isFiniteType_comp B S hS hX' hX hY _ _
        (Space.isFiniteType_of_isClosedImmersion B S hS _ hι) hgft) hkft
      hsepX' ?_ ?_
    · -- the image of `W_red` is dense in `X'`
      let := Space.pointTopology B S hS (Space.reducedClosedSubspace B S hS X hX _ hZ).toFunctor
      have hemb := Space.isClosedEmbedding_pointsMap_of_isClosedImmersion B S hS hX hι
      refine dense_iff_closure_eq.2 ?_
      rw [hemb.isInducing.closure_eq_preimage_closure_image, ← Set.range_comp,
        ← Space.pointsMap_comp, hk, Space.pointsMap_comp, Set.range_comp, hρrange, Set.image_univ,
        Set.eq_univ_iff_forall]
      intro x
      have hx := Set.mem_range_self (f := Space.pointsMap B S hS _
        (Space.reducedClosedSubspace B S hS X hX _ hZ).ι) x
      rw [hιrange] at hx
      exact hx
    · -- the claim, and the passage from `X` to the closed subspace `X'`
      intro q hq t ht
      let q₀ : Space.ValuativeSquare (i ≫ p) :=
        { q with
          generic := q.generic ≫ (Space.reducedClosedSubspace B S hS X hX _ hZ).ι
          comm := by rw [Category.assoc]; exact q.comm }
      obtain ⟨E₀, ⟨ℓ₀⟩⟩ := exists_dominatingExtension_lift_of_discreteExistenceAlong B S hS f h
        hlift e he hX a ha (i ≫ p) hg W eW' q₀ hq
        (t ≫ (Space.reducedClosedSubspace B S hS W hW Set.univ isClosed_univ).ι)
        (by
          rw [hwX, Category.assoc, ← hk, ← Category.assoc, ht])
      have hgc : E₀.square.generic = yoneda.map E₀.genericOver ≫ q.generic ≫
          (Space.reducedClosedSubspace B S hS X hX _ hZ).ι := E₀.generic_comm
      let qι : Space.ValuativeSquare (Space.reducedClosedSubspace B S hS X hX _ hZ).ι :=
        { E₀.square with
          generic := yoneda.map E₀.genericOver ≫ q.generic
          special := ℓ₀.map
          comm := by rw [Category.assoc, ← hgc, ℓ₀.generic_comm] }
      obtain ⟨ℓι⟩ := Space.nonempty_valuativeSquareLift_of_isClosedImmersion B S hS _ hι qι
      let E : q.DominatingExtension :=
        { square :=
            { E₀.square with
              generic := yoneda.map E₀.genericOver ≫ q.generic
              comm := by
                rw [← E₀.square.comm, hgc]
                simp only [Category.assoc] }
          ringMap := E₀.ringMap
          fieldMap := E₀.fieldMap
          isLocalHom := E₀.isLocalHom
          fraction_comm := E₀.fraction_comm
          base_comm := E₀.base_comm
          genericOver := E₀.genericOver
          genericOver_left := E₀.genericOver_left
          specialOver := E₀.specialOver
          specialOver_left := E₀.specialOver_left
          generic_comm := rfl
          special_comm := E₀.special_comm }
      exact Space.exists_lift_of_dominatingExtension hX' hY hsepX' q E
        ⟨{ map := ℓι.map, generic_comm := ℓι.generic_comm
           special_comm := (Category.assoc _ _ _).symm.trans
             ((congrArg (· ≫ (i ≫ p)) ℓι.special_comm).trans ℓ₀.special_comm) }⟩
  -- `X' ⟶ 𝒳 ⟶ h_V` is universally closed
  have hUC : UniversallyClosed B S hS ((algebraicSpaceStackMap.{u, w} B S hS hX' hX
      (Space.reducedClosedSubspace B S hS X hX _ hZ).ι ≫ a) ≫ f ≫ e) := by
    refine (universallyClosed_iff_universallyClosed_representingMap B S hS _ (yoneda.obj V)
      (StacksRepresentableCFG.EquivalenceOver.refl
        (algebraicSpaceStack.{u, w} B S hS _ hX').val.val.p)
      (StacksRepresentableCFG.EquivalenceOver.refl
        (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) hY).val.val.p) _ hX' hY).2 ?_
    have hrm : representingMap B S hS (algebraicSpaceStack.{u, w} B S hS _ hX').val
        (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) hY).val _ (yoneda.obj V)
        (StacksRepresentableCFG.EquivalenceOver.refl
          (algebraicSpaceStack.{u, w} B S hS _ hX').val.val.p)
        (StacksRepresentableCFG.EquivalenceOver.refl
          (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) hY).val.val.p)
        (((algebraicSpaceStackMap.{u, w} B S hS hX' hX
          (Space.reducedClosedSubspace B S hS X hX _ hZ).ι).hom ≫ a.hom) ≫ f.hom ≫ e.hom) =
        (Space.reducedClosedSubspace B S hS X hX _ hZ).ι ≫ i ≫ p := by
      rw [representingMap_congr_twoIso B S hS
        (𝒜 := (algebraicSpaceStack.{u, w} B S hS _ hX').val)
        (𝒞 := (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) hY).val) _ _
        (StacksRepresentableCFG.EquivalenceOver.refl
          (algebraicSpaceStack.{u, w} B S hS _ hX').val.val.p)
        (StacksRepresentableCFG.EquivalenceOver.refl
          (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) hY).val.val.p) (α_ _ _ _),
        representingMap_comp B S hS (𝒜 := (algebraicSpaceStack.{u, w} B S hS _ hX').val)
          (ℬ := (algebraicSpaceStack.{u, w} B S hS X hX).val)
          (𝒞 := (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) hY).val) _ X (yoneda.obj V)
          (StacksRepresentableCFG.EquivalenceOver.refl
            (algebraicSpaceStack.{u, w} B S hS _ hX').val.val.p)
          (StacksRepresentableCFG.EquivalenceOver.refl
            (algebraicSpaceStack.{u, w} B S hS X hX).val.val.p)
          (StacksRepresentableCFG.EquivalenceOver.refl
            (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) hY).val.val.p) _
          (a.hom ≫ f.hom ≫ e.hom), hg]
      exact congrArg (· ≫ i ≫ p) (representingMap_associatedMap B S hS _ X _)
    exact hrm ▸ hprop.2.2
  -- `X' ⟶ 𝒳` is surjective
  have hsurj : IsSurjective B S hS (algebraicSpaceStackMap.{u, w} B S hS hX' hX
      (Space.reducedClosedSubspace B S hS X hX _ hZ).ι ≫ a) := by
    let _ := pointTopology B S hS 𝒳.val
    let _ := pointTopology B S hS (algebraicSpaceStack.{u, w} B S hS X hX).val
    -- the points of `X` and of its algebraic stack
    have hσX := isHomeomorph_spacePointMap_representing B S hS X hX
      (algebraicSpaceStack.{u, w} B S hS X hX).val
      (StacksRepresentableCFG.EquivalenceOver.refl
        (algebraicSpaceStack.{u, w} B S hS X hX).val.val.p)
    set σX := spacePointMap B S hS X (algebraicSpaceStack.{u, w} B S hS X hX).val
      (representingEquivalence B S hS X (algebraicSpaceStack.{u, w} B S hS X hX).val
        (StacksRepresentableCFG.EquivalenceOver.refl
          (algebraicSpaceStack.{u, w} B S hS X hX).val.val.p)).functor with hσXdef
    -- the image of `|a|` on `σX(Z)` is closed and contains the image of `|h|`
    have hT : _root_.IsClosed (pointsMap B S hS a ''
        (σX '' closure (Set.range (Space.pointsMap B S hS W wX)))) :=
      isClosed_of_universallyClosed B S hS a ha.2.2 _ (hσX.isClosedMap _ hZ)
    have hsub : Set.range (pointsMap B S hS h) ⊆ pointsMap B S hS a ''
        (σX '' closure (Set.range (Space.pointsMap B S hS W wX))) := by
      rintro _ ⟨v, rfl⟩
      obtain ⟨x, hx⟩ := hasurj (pointsMap B S hS h v)
      obtain ⟨pt, -, hpt⟩ := exists_point_of_isTwoFibreProduct B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS h a) hP v x hx.symm
      obtain ⟨wpt, rfl⟩ := (bijective_spacePointMap_representing B S hS W
        (twoFibreProductSquareAlgebraicStacks B S hS h a).pt.val eW').2 pt
      refine ⟨x, ⟨Space.pointsMap B S hS W wX wpt, subset_closure ⟨wpt, rfl⟩, ?_⟩, hx⟩
      rw [← hpt, ← hwX]
      exact spacePointMap_representing_naturality B S hS W X _ _ eW' _ _ wpt
    have huniv := (hdense.closure_eq.symm.subset.trans (hT.closure_subset_iff.2 hsub))
    intro y
    obtain ⟨_, ⟨z, hz, rfl⟩, hy⟩ := huniv (Set.mem_univ y)
    rw [← hιrange] at hz
    obtain ⟨x', rfl⟩ := hz
    refine ⟨spacePointMap B S hS _ (algebraicSpaceStack.{u, w} B S hS _ hX').val
      (representingEquivalence B S hS _ (algebraicSpaceStack.{u, w} B S hS _ hX').val
        (StacksRepresentableCFG.EquivalenceOver.refl
          (algebraicSpaceStack.{u, w} B S hS _ hX').val.val.p)).functor x', ?_⟩
    rw [pointsMap_comp, Function.comp_apply, ← hy]
    congr 1
    have hnat := spacePointMap_representing_naturality B S hS _ X
      (algebraicSpaceStack.{u, w} B S hS _ hX').val (algebraicSpaceStack.{u, w} B S hS X hX).val
      (StacksRepresentableCFG.EquivalenceOver.refl
        (algebraicSpaceStack.{u, w} B S hS _ hX').val.val.p)
      (StacksRepresentableCFG.EquivalenceOver.refl
        (algebraicSpaceStack.{u, w} B S hS X hX).val.val.p)
      (algebraicSpaceStackMap.{u, w} B S hS hX' hX
        (Space.reducedClosedSubspace B S hS X hX _ hZ).ι).hom x'
    rw [representingMap_associatedMap] at hnat
    exact hnat.symm
  exact universallyClosed_of_comp_of_isSeparated B S hS f e
    (universallyClosed_of_surjective_comp B S hS _ (f ≫ e) hUC hsurj) heP.1

/-- **Stacks 0CQM.** Let `f : 𝒳 ⟶ 𝒴` and `h : 𝒰 ⟶ 𝒳` be 1-morphisms of algebraic stacks over
`S`. Assume that `𝒴` is locally Noetherian, that `f` and `h` are of finite type, that `f` is
separated, and that the image of `|h| : |𝒰| → |𝒳|` is dense in `|𝒳|`. If for every
2-commutative diagram `Spec K ⟶ 𝒰 ⟶ 𝒳 ⟶ 𝒴`, `Spec A ⟶ 𝒴`, with `A` a discrete valuation ring
with field of fractions `K` and a 2-arrow `γ : y ∘ j → f ∘ h ∘ u`, there are an extension
`K'/K` of fields and a valuation ring `A' ⊂ K'` dominating `A` such that the category of dotted
arrows of the induced diagram for `f` is nonempty, then `f` is proper.

`𝒴` locally Noetherian is the existence of a smooth surjective atlas by a locally Noetherian
scheme (`HasPropertyOnSomeSchemeAtlas`). The valuative hypothesis is
`ValuativeCriterion.DiscreteExistenceAlong B S hS h f`: a diagram of the statement is a valuative
square for `f` (Stacks 0CLK) over a discrete valuation ring whose generic point `x` is `u ≫ h`,
its 2-arrow being the square's `γ`; the induced diagram over `A'` with its 2-arrow `γ'` is the
square's restriction along the dominating extension (`e.inducedGamma`), and its category of
dotted arrows is that of Stacks 0CLA (`CategoryTheory.DottedArrow`).

The proof is the source's: the reduction to an affine locally Noetherian base and an affine
source (`isProper_of_discreteExistenceAlong_of_affineCore`), and the affine case
(`universallyClosed_of_discreteExistenceAlong_affineCore`), which uses
Chow's lemma for algebraic stacks over a Noetherian base. -/
@[stacks 0CQM]
theorem isProper_of_discreteExistenceAlong
    {𝒰 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (h : 𝒰 ⟶ 𝒳) (f : 𝒳 ⟶ 𝒴)
    (h𝒴 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴)
    (hf : IsFiniteType B S hS f) (hh : IsFiniteType B S hS h) (hsep : IsSeparated B S hS f)
    (hdense : @Dense _ (pointTopology B S hS 𝒳.val) (Set.range (pointsMap B S hS h)))
    (hlift : ValuativeCriterion.DiscreteExistenceAlong B S hS h f) :
    IsProper B S hS f :=
  isProper_of_discreteExistenceAlong_of_affineCore B S hS
    (universallyClosed_of_discreteExistenceAlong_affineCore B S hS) h f h𝒴
    hf hh hsep hdense hlift

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
