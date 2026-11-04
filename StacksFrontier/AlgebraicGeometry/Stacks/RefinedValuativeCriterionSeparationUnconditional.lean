module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.RefinedValuativeCriterionAffine
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace
import all StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedSmoothLocal

/-!
# The refined valuative criterion of separation for algebraic stacks (Stacks 0E95)

Stacks 0E95: let `f : 𝒳 ⟶ 𝒴` and `h : 𝒰 ⟶ 𝒳` be 1-morphisms of algebraic stacks, with `𝒴`
locally Noetherian, `f` locally of finite type and quasi-separated, `h` of finite type and the
image of `|h|` dense in `|𝒳|`. If for every valuative diagram for `f` over a discrete valuation
ring whose generic point factors through `h` the category of dotted arrows is either empty or a
setoid with exactly one isomorphism class, then `f` is separated.

The source proves this by applying Stacks 0CQM to `h` and the relative diagonal `Δ_f`, first
with `Δ_f` replaced by `Δ_{Δ_f}`. The library has the deduction of Stacks 0E95 from the statement
of Stacks 0CQM
(`AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_of_denseRange_of_discreteUniquenessAlong`)
and the proof of Stacks 0CQM from Chow's lemma for algebraic stacks, Stacks 0CQ8
(`AlgebraicGeometry.Stack.AlgebraicStacks.isProper_of_discreteExistenceAlong_of_chow`). Both
1-morphisms Stacks 0CQM is applied to are representable by algebraic spaces, and for those Chow's
lemma is not needed: after the reduction to an affine locally Noetherian base `V`, the source
`𝒳 ×_𝒴 V` is itself represented by an algebraic space (Stacks 0300), which serves as the proper
surjective cover. This file proves Stacks 0CQM for 1-morphisms representable by algebraic spaces
this way and registers Stacks 0E95 with no hypothesis beyond the source's.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_of_discreteUniquenessAlong_of_dense`:
  **Stacks 0E95**.

## References

* [Stacks Project, Tag 0E95](https://stacks.math.columbia.edu/tag/0E95)
* [Stacks Project, Tag 0CQM](https://stacks.math.columbia.edu/tag/0CQM)
* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace AlgebraicStacks

/-- A 1-morphism between algebraic stacks represented by the same algebraic space `X`, inducing
the identity of `X` on representing presheaves, exists and is proper. -/
private theorem exists_isProper_representingMap_eq_id
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒳.val.val.p (presheafOfCategories (X ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒴.val.val.p (presheafOfCategories (X ⋙ typeToCat)).p) :
    ∃ a : 𝒳 ⟶ 𝒴, representingMap B S hS 𝒳.val 𝒴.val X X eF eG a.hom = 𝟙 X ∧
      IsProper B S hS a := by
  obtain ⟨a, ha⟩ := exists_oneMorphism_representingMap_eq B S hS X X eF eG (𝟙 X)
  refine ⟨a, ha, (isProper_iff_isProper_representingMap B S hS X X eF eG a hX hX).2 ?_⟩
  rw [ha]
  exact Space.isProper_of_isIso B S hS _

/-- **An algebraic stack represented by an algebraic space `X` receives a proper surjective
1-morphism from the algebraic stack of `X`**: the 1-morphism inducing the identity of `X` on
representing presheaves (Stacks 04SW). It is proper since the identity of `X` is, and surjective
since a 1-morphism in the other direction inducing the identity is a section of it up to a
2-isomorphism. -/
private theorem exists_isProper_isSurjective_of_isRepresentableByAlgebraicSpace
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (h𝒳 : IsRepresentableByAlgebraicSpace B S hS 𝒳.val) :
    ∃ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
      (a : algebraicSpaceStack.{u, w} B S hS X hX ⟶ 𝒳),
      IsProper B S hS a ∧ IsSurjective B S hS a := by
  obtain ⟨X, hX, ⟨eX⟩⟩ := h𝒳
  set eR := StacksRepresentableCFG.EquivalenceOver.refl
    (algebraicSpaceStack.{u, w} B S hS X hX).val.val.p
  obtain ⟨a, ha, haP⟩ := exists_isProper_representingMap_eq_id B S hS
    (𝒳 := algebraicSpaceStack.{u, w} B S hS X hX) (𝒴 := 𝒳) X hX eR eX
  obtain ⟨b, hb, -⟩ := exists_isProper_representingMap_eq_id B S hS
    (𝒳 := 𝒳) (𝒴 := algebraicSpaceStack.{u, w} B S hS X hX) X hX eX eR
  refine ⟨X, hX, a, haP, fun x => ⟨pointsMap B S hS b x, ?_⟩⟩
  have hba : representingMap B S hS 𝒳.val 𝒳.val X X eX eX (b.hom ≫ a.hom) =
      representingMap B S hS 𝒳.val 𝒳.val X X eX eX (𝟙 𝒳.val) := by
    rw [representingMap_comp B S hS X X X eX eR eX, ha, hb, representingMap_id,
      Category.comp_id]
  obtain ⟨hU⟩ := nonempty_unique_twoIso_of_representingMap_eq B S hS 𝒳.val 𝒳.val X X eX eX hba
  have θ : b ≫ a ≅ 𝟙 𝒳 := Bicategory.InducedBicategory.isoMk hU.default
  have hpts := pointsMap_eq_of_hom₂ B S hS θ.hom
  rw [← Function.comp_apply (f := pointsMap B S hS a), ← pointsMap_comp, hpts,
    pointsMap_id, id]

/-- **The affine case of Stacks 0CQM for a source represented by an algebraic space.** Let `V`
be an affine locally Noetherian scheme of the site, `f : 𝒳 ⟶ V` a separated 1-morphism of finite
type whose source is represented by an algebraic space, and `h : U ⟶ 𝒳` a 1-morphism locally of
finite type from an affine scheme `U` with dense image, such that `f` satisfies the discrete
existence part of the valuative criterion along `h`. Then `f` is universally closed.

This is the proof of
`AlgebraicGeometry.Stack.AlgebraicStacks.universallyClosed_of_discreteExistenceAlong_of_chow`,
with the proper surjective cover of Chow's lemma replaced by the one of
`exists_isProper_isSurjective_of_isRepresentableByAlgebraicSpace`: the source's argument only uses
that the cover is proper and surjective and that its composite to `V` is a morphism of algebraic
spaces `g`. -/
private theorem universallyClosed_of_discreteExistenceAlong_of_representable
    (V : BigFppfOver B S hS) (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (hVN : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V))
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (h𝒳 : IsRepresentableByAlgebraicSpace B S hS 𝒳.val)
    (f : 𝒳 ⟶ schemeStack.{u, w} B S hS V)
    (hf : IsFiniteType B S hS f) (hsep : IsSeparated B S hS f)
    (U : BigFppfOver B S hS) (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (h : schemeStack.{u, w} B S hS U ⟶ 𝒳) (hh : IsLocallyOfFiniteType B S hS h)
    (hdense : @Dense _ (pointTopology B S hS 𝒳.val) (Set.range (pointsMap B S hS h)))
    (hlift : ValuativeCriterion.DiscreteExistenceAlong B S hS h f) :
    UniversallyClosed B S hS f := by
  classical
  have hY := isAlgebraicSpace_yoneda B S hS V
  -- the algebraic stack of `V` against that of the algebraic space `h_V`
  obtain ⟨e, he, heP⟩ := exists_isProper_representingMap_eq_id B S hS
    (𝒳 := schemeStack.{u, w} B S hS V) (𝒴 := algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) hY)
    (yoneda.obj V) hY (PresheafOfCategories.sliceElementsEquivalenceOver V)
    (StacksRepresentableCFG.EquivalenceOver.refl
      (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) hY).val.val.p)
  -- the algebraic space representing `𝒳`, in place of Chow's lemma
  obtain ⟨X, hX, a, ha, hasurj⟩ :=
    exists_isProper_isSurjective_of_isRepresentableByAlgebraicSpace B S hS 𝒳 h𝒳
  obtain ⟨g, hg⟩ : ∃ g, representingMap B S hS (algebraicSpaceStack.{u, w} B S hS X hX).val
      (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) hY).val X (yoneda.obj V)
      (StacksRepresentableCFG.EquivalenceOver.refl
        (algebraicSpaceStack.{u, w} B S hS X hX).val.val.p)
      (StacksRepresentableCFG.EquivalenceOver.refl
        (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) hY).val.val.p)
      (a.hom ≫ f.hom ≫ e.hom) = g := ⟨_, rfl⟩
  have hgsep : Space.IsSeparated B S hS g := by
    rw [← hg]
    exact (isSeparated_iff_isSeparated_representingMap B S hS X (yoneda.obj V) _ _ (a ≫ f ≫ e)
      hX hY).1 (isSeparated_comp B S hS a (f ≫ e) ha.1 (isSeparated_comp B S hS f e hsep heP.1))
  have hgft : Space.IsFiniteType B S hS g := by
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
    refine Space.isQuasiCompact_of_comp_of_isQuasiSeparated B S hS _ g hW hY ?_
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
      ((Space.reducedClosedSubspace B S hS X hX _ hZ).ι ≫ g) := by
    have hkft : Space.IsFiniteType B S hS k := by
      have hcomp : Space.IsFiniteType B S hS
          (k ≫ (Space.reducedClosedSubspace B S hS X hX _ hZ).ι) := by
        rw [hk]
        exact Space.isFiniteType_comp B S hS hWr hW hX _ _
          (Space.isFiniteType_of_isClosedImmersion B S hS _ hρci) hwft
      exact ⟨Space.isLocallyOfFiniteType_of_comp B S hS hWr hX' hX _ _ hcomp.1,
        Space.isQuasiCompact_of_comp_mono B S hS _ _ hcomp.2⟩
    refine Space.isProper_of_denseRange_of_exists_discreteLift hX' hY hWr _ k
      ((Space.exists_atlas_iff_of_representable B S hS (yoneda.obj V)
        (fun T : Scheme.{u} => IsLocallyNoetherian T) V (Iso.refl _)).2 hVN)
      (Space.isFiniteType_comp B S hS hX' hX hY _ _
        (Space.isFiniteType_of_isClosedImmersion B S hS _ hι) hgft) hkft
      (Space.isSeparated_comp B S hS _ _ (Space.isSeparated_of_isClosedImmersion B S hS _ hι)
        hgsep) ?_ ?_
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
      have hsepX' : Space.IsSeparated B S hS
          ((Space.reducedClosedSubspace B S hS X hX _ hZ).ι ≫ g) :=
        Space.isSeparated_comp B S hS _ _ (Space.isSeparated_of_isClosedImmersion B S hS _ hι)
          hgsep
      let q₀ : Space.ValuativeSquare g :=
        { R := q.R, K := q.K, ring_mem := q.ring_mem, field_mem := q.field_mem, base := q.base
          generic := q.generic ≫ (Space.reducedClosedSubspace B S hS X hX _ hZ).ι
          special := q.special
          comm := by rw [Category.assoc]; exact q.comm }
      obtain ⟨E₀, ⟨ℓ₀⟩⟩ := exists_dominatingExtension_lift_of_discreteExistenceAlong B S hS f h
        hlift e he hX a ha g hg W eW' q₀ hq
        (t ≫ (Space.reducedClosedSubspace B S hS W hW Set.univ isClosed_univ).ι)
        (by
          rw [hwX, Category.assoc, ← hk, ← Category.assoc, ht])
      have hgc : E₀.square.generic = yoneda.map E₀.genericOver ≫ q.generic ≫
          (Space.reducedClosedSubspace B S hS X hX _ hZ).ι := E₀.generic_comm
      let qι : Space.ValuativeSquare (Space.reducedClosedSubspace B S hS X hX _ hZ).ι :=
        { R := E₀.square.R, K := E₀.square.K, ring_mem := E₀.square.ring_mem,
          field_mem := E₀.square.field_mem, base := E₀.square.base
          generic := yoneda.map E₀.genericOver ≫ q.generic
          special := ℓ₀.map
          comm := by rw [Category.assoc, ← hgc, ℓ₀.generic_comm] }
      obtain ⟨ℓι⟩ := Space.nonempty_valuativeSquareLift_of_isClosedImmersion B S hS _ hι qι
      let E : q.DominatingExtension :=
        { square :=
            { R := E₀.square.R, K := E₀.square.K, ring_mem := E₀.square.ring_mem,
              field_mem := E₀.square.field_mem, base := E₀.square.base
              generic := yoneda.map E₀.genericOver ≫ q.generic
              special := E₀.square.special
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
             ((congrArg (· ≫ g) ℓι.special_comm).trans ℓ₀.special_comm) }⟩
  -- `X' ⟶ 𝒳 ⟶ h_V` is universally closed
  have hX'Fn := Space.isAlgebraicSpace_reducedClosedSubspace B S hS X hX _ hZ
  have hUC : UniversallyClosed B S hS ((algebraicSpaceStackMap.{u, w} B S hS hX'Fn hX
      (Space.reducedClosedSubspace B S hS X hX _ hZ).ι ≫ a) ≫ f ≫ e) := by
    refine (universallyClosed_iff_universallyClosed_representingMap B S hS _ (yoneda.obj V)
      (StacksRepresentableCFG.EquivalenceOver.refl
        (algebraicSpaceStack.{u, w} B S hS _ hX'Fn).val.val.p)
      (StacksRepresentableCFG.EquivalenceOver.refl
        (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) hY).val.val.p) _ hX'Fn hY).2 ?_
    have hrm : representingMap B S hS (algebraicSpaceStack.{u, w} B S hS _ hX'Fn).val
        (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) hY).val _ (yoneda.obj V)
        (StacksRepresentableCFG.EquivalenceOver.refl
          (algebraicSpaceStack.{u, w} B S hS _ hX'Fn).val.val.p)
        (StacksRepresentableCFG.EquivalenceOver.refl
          (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) hY).val.val.p)
        (((algebraicSpaceStackMap.{u, w} B S hS hX'Fn hX
          (Space.reducedClosedSubspace B S hS X hX _ hZ).ι).hom ≫ a.hom) ≫ f.hom ≫ e.hom) =
        (Space.reducedClosedSubspace B S hS X hX _ hZ).ι ≫ g := by
      rw [representingMap_congr_twoIso B S hS
        (𝒜 := (algebraicSpaceStack.{u, w} B S hS _ hX'Fn).val)
        (𝒞 := (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) hY).val) _ _
        (StacksRepresentableCFG.EquivalenceOver.refl
          (algebraicSpaceStack.{u, w} B S hS _ hX'Fn).val.val.p)
        (StacksRepresentableCFG.EquivalenceOver.refl
          (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) hY).val.val.p) (α_ _ _ _),
        representingMap_comp B S hS (𝒜 := (algebraicSpaceStack.{u, w} B S hS _ hX'Fn).val)
          (ℬ := (algebraicSpaceStack.{u, w} B S hS X hX).val)
          (𝒞 := (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) hY).val) _ X (yoneda.obj V)
          (StacksRepresentableCFG.EquivalenceOver.refl
            (algebraicSpaceStack.{u, w} B S hS _ hX'Fn).val.val.p)
          (StacksRepresentableCFG.EquivalenceOver.refl
            (algebraicSpaceStack.{u, w} B S hS X hX).val.val.p)
          (StacksRepresentableCFG.EquivalenceOver.refl
            (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) hY).val.val.p) _
          (a.hom ≫ f.hom ≫ e.hom), hg]
      exact congrArg (· ≫ g) (representingMap_associatedMap B S hS _ X _)
    exact hrm ▸ hprop.2.2
  -- `X' ⟶ 𝒳` is surjective
  have hsurj : IsSurjective B S hS (algebraicSpaceStackMap.{u, w} B S hS hX'Fn hX
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
    refine ⟨spacePointMap B S hS _ (algebraicSpaceStack.{u, w} B S hS _ hX'Fn).val
      (representingEquivalence B S hS _ (algebraicSpaceStack.{u, w} B S hS _ hX'Fn).val
        (StacksRepresentableCFG.EquivalenceOver.refl
          (algebraicSpaceStack.{u, w} B S hS _ hX'Fn).val.val.p)).functor x', ?_⟩
    rw [pointsMap_comp, Function.comp_apply, ← hy]
    congr 1
    have hnat := spacePointMap_representing_naturality B S hS _ X
      (algebraicSpaceStack.{u, w} B S hS _ hX'Fn).val (algebraicSpaceStack.{u, w} B S hS X hX).val
      (StacksRepresentableCFG.EquivalenceOver.refl
        (algebraicSpaceStack.{u, w} B S hS _ hX'Fn).val.val.p)
      (StacksRepresentableCFG.EquivalenceOver.refl
        (algebraicSpaceStack.{u, w} B S hS X hX).val.val.p)
      (algebraicSpaceStackMap.{u, w} B S hS hX'Fn hX
        (Space.reducedClosedSubspace B S hS X hX _ hZ).ι).hom x'
    rw [representingMap_associatedMap] at hnat
    exact hnat.symm
  exact universallyClosed_of_comp_of_isSeparated B S hS f e
    (universallyClosed_of_surjective_comp B S hS _ (f ≫ e) hUC hsurj) heP.1

/-- **The first reduction of the proof of Stacks 0CQM, for a 1-morphism representable by
algebraic spaces.** Let `f : 𝒳 ⟶ 𝒴` be representable by algebraic spaces, separated and of finite
type over a locally Noetherian `𝒴`, and let `h : 𝒰 ⟶ 𝒳` be of finite type with dense image, such
that `f` satisfies the discrete existence part of the valuative criterion along `h`. Then `f` is
universally closed.

The reduction is that of
`AlgebraicGeometry.Stack.AlgebraicStacks.universallyClosed_of_discreteExistenceAlong_of_affine`
and `universallyClosed_of_discreteExistenceAlong_of_affineSource`: universal closedness descends
along the smooth 1-morphisms `V ⟶ 𝒴` from affine opens `V` of a locally Noetherian scheme chart,
the hypotheses pass to the base change `𝒰_V ⟶ 𝒳_V ⟶ V`, and the source `𝒳_V` is represented by
an algebraic space since `f` is representable by algebraic spaces (Stacks 0300), so the affine
case is `universallyClosed_of_discreteExistenceAlong_of_representable`. -/
private theorem universallyClosed_of_discreteExistenceAlong_of_isRepresentable
    {𝒰 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (h : 𝒰 ⟶ 𝒳) (f : 𝒳 ⟶ 𝒴)
    (hrep : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (h𝒴 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴)
    (hf : IsFiniteType B S hS f) (hh : IsFiniteType B S hS h) (hsep : IsSeparated B S hS f)
    (hdense : @Dense _ (pointTopology B S hS 𝒳.val) (Set.range (pointsMap B S hS h)))
    (hlift : ValuativeCriterion.DiscreteExistenceAlong B S hS h f) :
    UniversallyClosed B S hS f := by
  classical
  let _ : ObjectProperty.IsLocal (fun T : Scheme.{u} => IsLocallyNoetherian T)
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) :=
    ObjectProperty.IsLocal.of_le Scheme.smoothPrecoverage_le_fppfPrecoverage
  have hchart := (exists_scheme_atlas_iff_forall_scheme B S hS
    (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴).1 h𝒴
  obtain ⟨U, a, hasu, hasm, -⟩ := h𝒴
  have hvsm : ∀ i : ((BigFppfOver.toScheme B S hS).obj U).affineOpens,
      IsSmooth B S hS (schemeStackMap.{u, w} B S hS (affineChartHom U i) ≫ a) := fun i =>
    isSmooth_comp B S hS _ a
      (isSmooth_schemeStackMap B S hS _ (smooth_affineChartHom U i)) hasm
  refine universallyClosed_of_universallyClosed_smooth_cover B S hS f
    (fun i : ((BigFppfOver.toScheme B S hS).obj U).affineOpens =>
      schemeStack.{u, w} B S hS (affineChart U i))
    (fun i => schemeStackMap.{u, w} B S hS (affineChartHom U i) ≫ a) hvsm (fun y => ?_)
    (fun i => ?_)
  · obtain ⟨z, rfl⟩ := hasu y
    obtain ⟨i, w, rfl⟩ := exists_affineChart_point.{u, w} B S hS U z
    exact ⟨i, w, by rw [pointsMap_comp]; rfl⟩
  · set v := schemeStackMap.{u, w} B S hS (affineChartHom U i) ≫ a
    set P := twoFibreProductSquareAlgebraicStacks B S hS v f
    have hP := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS v f
    set Q := twoFibreProductSquareAlgebraicStacks B S hS P.snd h
    have hQ := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS P.snd h
    have hPsnd : IsSmooth B S hS P.snd :=
      isSmooth_baseChange B S hS v f P.swap (Bicategory.isTwoFibreProduct_swap hP) (hvsm i)
    -- the base change `𝒳_V` is represented by an algebraic space (Stacks 0300)
    have hPrep : IsRepresentableByAlgebraicSpace B S hS P.pt.val := by
      obtain ⟨W, hW, ⟨eW⟩⟩ := Stack.isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒴.val
        (schemeStack.{u, w} B S hS (affineChart U i)).val 𝒳.val v.hom.hom f.hom.hom hrep
        (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS (affineChart U i))
      exact ⟨W, hW, ⟨eW⟩⟩
    have hfP : IsFiniteType B S hS P.fst := isFiniteType_baseChange B S hS f v P hP hf
    have hsepP : IsSeparated B S hS P.fst :=
      isSeparated_baseChange_of_isTwoFibreProduct B S hS f v P.swap
        (Bicategory.isTwoFibreProduct_swap hP) hsep
    exact universallyClosed_of_discreteExistenceAlong_of_affineSource B S hS (affineChart U i)
      (isAffine_affineChart U i) P.fst
      (fun U' hU' h' hlft hd hl => universallyClosed_of_discreteExistenceAlong_of_representable
        B S hS (affineChart U i) (isAffine_affineChart U i) (hchart _ v (hvsm i)) P.pt hPrep
        P.fst hfP hsepP U' hU' h' hlft hd hl)
      Q.fst hfP (isFiniteType_baseChange B S hS h P.snd Q hQ hh)
      (dense_range_pointsMap_fst_of_isFlat B S hS P.snd h (isFlat_of_isSmooth B S hS _ hPsnd)
        (isLocallyOfFinitePresentation_of_isSmooth B S hS _ hPsnd) hdense)
      (ValuativeCriterion.DiscreteExistenceAlong.baseChange B S hS f v h P hP Q hlift)

/-- **Stacks 0CQM for a 1-morphism representable by algebraic spaces.** Let `f : 𝒳 ⟶ 𝒴` and
`h : 𝒰 ⟶ 𝒳` be 1-morphisms of algebraic stacks, with `𝒴` locally Noetherian, `f` and `h` of
finite type, `f` separated and representable by algebraic spaces, and the image of `|h|` dense in
`|𝒳|`. If `f` satisfies the discrete existence part of the valuative criterion along `h`, then `f`
is proper. -/
private theorem isProper_of_discreteExistenceAlong_of_isRepresentable
    {𝒰 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (h : 𝒰 ⟶ 𝒳) (f : 𝒳 ⟶ 𝒴)
    (hrep : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (h𝒴 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴)
    (hf : IsFiniteType B S hS f) (hh : IsFiniteType B S hS h) (hsep : IsSeparated B S hS f)
    (hdense : @Dense _ (pointTopology B S hS 𝒳.val) (Set.range (pointsMap B S hS h)))
    (hlift : ValuativeCriterion.DiscreteExistenceAlong B S hS h f) :
    IsProper B S hS f :=
  ⟨hsep, hf, universallyClosed_of_discreteExistenceAlong_of_isRepresentable B S hS h f hrep h𝒴
    hf hh hsep hdense hlift⟩

/-- **The first case of the proof of Stacks 0E95, where the relative diagonal is separated.** Let
`f : 𝒳 ⟶ 𝒴` be locally of finite type over a locally Noetherian `𝒴`, with quasi-compact relative
diagonal, and let `h : 𝒰 ⟶ 𝒳` be of finite type with dense image. If `Δ_f` is separated and `f`
satisfies the discrete uniqueness part of the valuative criterion along `h`, then `f` is separated.

Stacks 0CQM applies to `h` and `Δ_f`, which is representable by algebraic spaces, through
`isProper_of_discreteExistenceAlong_of_isRepresentable`; existence along `h` for `Δ_f` is
Stacks 0E8L. This is the argument of
`isSeparated_of_discreteUniquenessAlong_of_isSeparated_relativeDiagonal` with that input in place
of the statement of Stacks 0CQM. -/
private theorem isSeparated_of_isSeparated_relativeDiagonal_of_discreteUniquenessAlong
    {𝒰 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (h : 𝒰 ⟶ 𝒳) (f : 𝒳 ⟶ 𝒴)
    (h𝒴 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴)
    (hf : IsLocallyOfFiniteType B S hS f)
    (hqc : Stack.IsQuasiCompact.{u, u, u + 1} B S hS
      (Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom))
    (hh : IsFiniteType B S hS h)
    (hdense : @Dense _ (pointTopology B S hS 𝒳.val) (Set.range (pointsMap B S hS h)))
    (hΔ : IsSeparated B S hS (relativeDiagonal B S hS f))
    (huniq : ValuativeCriterion.DiscreteUniquenessAlong B S hS h f) :
    IsSeparated B S hS f := by
  have hrep := Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f
  have hP := isProper_of_discreteExistenceAlong_of_isRepresentable B S hS h
    (relativeDiagonal B S hS f) hrep (isLocallyNoetherian_twoFibreProduct B S hS f hf h𝒴)
    ⟨isLocallyOfFiniteType_relativeDiagonal_of_isLocallyOfFiniteType B S hS f hf,
      (isQuasiCompact_iff_baseChange_quasiCompact B S hS (relativeDiagonal B S hS f) hrep).1 hqc⟩
    hh hΔ hdense
    (ValuativeCriterion.DiscreteUniquenessAlong.discreteExistenceAlong_relativeDiagonal B S hS
      huniq)
  exact (isProper_iff_isProper_hom B S hS (relativeDiagonal B S hS f) hrep).1 hP

/-- **Stacks 0E95.** Let `f : 𝒳 ⟶ 𝒴` and `h : 𝒰 ⟶ 𝒳` be 1-morphisms of algebraic stacks over
`S`. Assume that `𝒴` is locally Noetherian, that `f` is locally of finite type and
quasi-separated, that `h` is of finite type, and that the image of `|h| : |𝒰| ⟶ |𝒳|` is dense in
`|𝒳|`. If for every 2-commutative diagram for `f` over a discrete valuation ring `A` with fraction
field `K` whose generic point is `h ∘ u` for some `u : Spec K ⟶ 𝒰`, the category of dotted arrows
is either empty or a setoid with exactly one isomorphism class, then `f` is separated.

The hypothesis on dotted arrows is
`AlgebraicGeometry.Stack.ValuativeCriterion.DiscreteUniquenessAlong`. The proof is the source's:
the first case (`isSeparated_of_isSeparated_relativeDiagonal_of_discreteUniquenessAlong`) applied
to `Δ_f` in place of `f` shows that `Δ_f` is separated, and the first case applied to `f`
concludes. For the first application, `Δ_f` is representable by algebraic spaces, so every
category of dotted arrows of a diagram for `Δ_f` is a setoid (Stacks 0E8L, Stacks 0CLC), whence
`Δ_{Δ_f}` is separated; uniqueness along `h` passes from `f` to `Δ_f` by Stacks 0E8L; `Δ_f` is
quasi-separated because `f` is; and `𝒳 ×_𝒴 𝒳` is locally Noetherian (Stacks 06R6). -/
@[stacks 0E95]
theorem isSeparated_of_discreteUniquenessAlong_of_dense
    {𝒰 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (h : 𝒰 ⟶ 𝒳) (f : 𝒳 ⟶ 𝒴)
    (h𝒴 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴)
    (hf : IsLocallyOfFiniteType B S hS f) (hqs : IsQuasiSeparated B S hS f)
    (hh : IsFiniteType B S hS h)
    (hdense : @Dense _ (pointTopology B S hS 𝒳.val) (Set.range (pointsMap B S hS h)))
    (huniq : ValuativeCriterion.DiscreteUniquenessAlong B S hS h f) :
    IsSeparated B S hS f := by
  set δ := relativeDiagonal B S hS f
  have hrep : IsRepresentableByAlgebraicSpaces B S hS δ.hom.hom :=
    Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f
  have hrep₂ : IsRepresentableByAlgebraicSpaces B S hS (relativeDiagonal B S hS δ).hom.hom :=
    Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS δ
  -- `Δ_f` is quasi-separated: its relative diagonal is quasi-compact
  have hqc₂ : Stack.IsQuasiCompact.{u, u, u + 1} B S hS
      (Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val (twoFibreProduct B S hS f f).val
        δ.hom) :=
    (Stack.isQuasiCompact_relativeDiagonal_iff_isQuasiSeparated B S hS δ hrep).2 hqs.2
  have hqsΔ : IsQuasiSeparated B S hS δ :=
    (isQuasiSeparated_iff_isQuasiCompact_relativeDiagonal B S hS δ hrep).2 hqc₂
  -- `Δ_{Δ_f}` is separated, every category of dotted arrows for `Δ_f` being a setoid
  have hsep₂ : IsSeparated B S hS (relativeDiagonal B S hS δ) :=
    ((Stack.isSeparated_relativeDiagonal_tfae B S hS (relativeDiagonal B S hS δ) hrep₂).out 3 1).2
      (Stack.isSeparated_relativeDiagonal_of_isSetoidCategory_dottedArrow B S hS δ hqsΔ.2
        fun D => isSetoidCategory_dottedArrow_relativeDiagonal B S hS D)
  -- the first case for `Δ_f`
  have hsepΔ : IsSeparated B S hS δ :=
    isSeparated_of_isSeparated_relativeDiagonal_of_discreteUniquenessAlong B S hS h δ
      (isLocallyNoetherian_twoFibreProduct B S hS f hf h𝒴)
      (isLocallyOfFiniteType_relativeDiagonal_of_isLocallyOfFiniteType B S hS f hf) hqc₂ hh
      hdense hsep₂ (ValuativeCriterion.DiscreteUniquenessAlong.relativeDiagonal B S hS huniq)
  -- the first case for `f`
  exact isSeparated_of_isSeparated_relativeDiagonal_of_discreteUniquenessAlong B S hS h f
    h𝒴 hf hqs.1 hh hdense hsepΔ huniq

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
