module

public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedSubsetSeparationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PasteInnerSquareAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsCartesianSquare
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactFieldValuedPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactQuasiSeparatedStack
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedSmoothLocal
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap
import all StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedSmoothLocal

/-!
# The converse implications of Stacks 0H2A

`StacksFrontier/AlgebraicGeometry/Stacks/UniversallyClosedSmoothLocal.lean` proves the implications of
**Stacks 0H2A** out of universal closedness, together with three steps of the two converse ones.
This file proves the converse implications themselves, for a quasi-compact 1-morphism of
algebraic stacks, and assembles the full equivalence of the three clauses.

## Main results

* `AlgebraicGeometry.Stack.isTwoFibreProduct_factorInnerSquare`: the horizontal comparison square
  of the diagram of **Stacks 0H29** is 2-cartesian.
* `AlgebraicGeometry.Stack.AlgebraicStacks.IsClosedOnSiteFinitePresentationBases`: clause (2) at
  bases reached by a morphism of the site, with
  `.isClosed_baseChange_of_isClosedOnSiteFinitePresentationBases` the point-set heart of (2)
  implies (1) and `.universallyClosed_of_isClosedOnSiteFinitePresentationBases` its consequence
  at a target represented by a scheme of the site.
* `AlgebraicGeometry.Stack.AlgebraicStacks.universallyClosed_of_universallyClosed_smooth_cover`:
  universal closedness descends along a jointly surjective family of smooth base changes.
* `AlgebraicGeometry.Stack.AlgebraicStacks`
  `.universallyClosed_of_isQuasiCompactMorphism_of_isClosed_affine_lfp`: **Stacks 0H2A**, (2)
  implies (1).
* `AlgebraicGeometry.Stack.AlgebraicStacks`
  `.universallyClosed_of_exists_chart_forall_isClosed_baseChange_affineSpaceChart`:
  **Stacks 0H2A**, (3) implies (1).
* `AlgebraicGeometry.Stack.AlgebraicStacks.universallyClosed_tfae_of_isQuasiCompactMorphism`:
  **Stacks 0H2A**, the full equivalence of the three clauses.

## Implementation notes

The proofs use the module-local helpers of
`StacksFrontier/AlgebraicGeometry/Stacks/UniversallyClosedSmoothLocal.lean` (closedness of a base
change along an isomorphism of cospans, descent of closedness along a smooth cover, and the
affine-chart family of a scheme of the site). Those are private there, so this file reaches them
with `import all` rather than restating them.

(2) implies (1) is the limit argument, and its one input beyond the base module is the separation
lemma of **Stacks 0H29** for algebraic stacks,
`AlgebraicGeometry.Stack.exists_affine_finitePresentation_separation`. Stacks 0H29 is stated for
a quasi-compact 1-morphism, which is the hypothesis Stacks 0H2A itself carries, so the
implication is unconditional; it is the hypothesis-free form of
`AlgebraicGeometry.Stack.AlgebraicStacks`
`.universallyClosed_of_forall_schemeStack_target_of_isClosed_affine_lfp`, which carries the
Stacks 0H29 input as `hred`.

Both converse implications are routed through
`AlgebraicGeometry.Stack.AlgebraicStacks.IsClosedOnSiteFinitePresentationBases`, in which the base
is reached by a *morphism of the site* locally of finite presentation rather than by a 1-morphism
of stacks locally of finite presentation. Clause (2) implies that form by
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFinitePresentation_schemeStackMap`, and that
form is all the proof consumes, because Stacks 0H29 hands back a base reached by a morphism of
the site of finite presentation; the converse transfer, which is not available at this level, is
never needed.

The point-set heart of (2) implies (1) needs the comparison 1-morphism
`AlgebraicGeometry.Stack.factorMap` of the diagram of Stacks 0H29 to sit in a 2-cartesian square
over the open immersion `V ⟶ Z`, since the two projections alone do not determine a point of a
2-fibre product (`|𝒳 ×_𝒴 Z| → |𝒳| ×_{|𝒴|} |Z|` of **Stacks 04XH** is only surjective). That
square is `AlgebraicGeometry.Stack.factorInnerSquare`, cut out of the base change `𝒳 ×_Y V` by
`CategoryTheory.Bicategory.pasteInnerSq`.

(2) implies (1) is proved first at an affine target, where Stacks 0H29 applies, and then
transported to a target represented by an arbitrary scheme of the site along its affine opens,
which needs universal closedness to descend along a jointly surjective family of smooth base
changes. (3) implies (1) factors through (2) implies (1).

## References

* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 0H29](https://stacks.math.columbia.edu/tag/0H29)
* [Stacks Project, Tag 0H2A](https://stacks.math.columbia.edu/tag/0H2A)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The horizontal comparison square of the diagram of Stacks 0H29 is 2-cartesian -/

section Factor

variable {Y : BigFppfOver B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
  (f : 𝒳 ⟶ schemeStack.{u, w} B S hS Y) {V Z' : BigFppfOver B S hS}
  (k : V ⟶ Y) (a : V ⟶ Z') (b : Z' ⟶ Y) (hab : k = a ≫ b)

/-- The base change `𝒳 ×_Y V` of the diagram of Stacks 0H29, read as a square over the cospan
whose first leg is the *composite* `Stack.schemeStackMap a ≫ Stack.schemeStackMap b` rather than
`Stack.schemeStackMap k`. Reindexing the cospan along `AlgebraicGeometry.Stack.schemeStackMap_comp`
changes neither the apex nor the two projections. -/
noncomputable def factorOuterSquare :
    Bicategory.TwoCommSq
      (schemeStackMap.{u, w} B S hS a ≫ schemeStackMap.{u, w} B S hS b) f :=
  (baseChangeSquare B S hS f k).reindexFst
    (eqToIso ((schemeStackMap_comp B S hS a b).trans
      (congrArg (schemeStackMap.{u, w} B S hS) hab.symm))).symm

/-- `AlgebraicGeometry.Stack.factorPreHom`, read as a pre-morphism out of the rectangle that
`AlgebraicGeometry.Stack.factorOuterSquare` defines over the cospan `(Stack.schemeStackMap b, f)`.
The two squares are definitionally equal: pasting `Stack.schemeStackMap a` onto the reindexed
base change is `AlgebraicGeometry.Stack.factorSquare` on the nose. -/
noncomputable def factorOuterPreHom :
    Bicategory.TwoCommSq.PreHom
      (Bicategory.pasteOuterSq (schemeStackMap.{u, w} B S hS a)
        (factorOuterSquare B S hS f k a b hab)) (baseChangeSquare B S hS f b) :=
  factorPreHom B S hS f k a b hab

/-- **The horizontal comparison square of the diagram of Stacks 0H29.** The comparison
1-morphism `𝒳 ×_Y V ⟶ 𝒳 ×_Y Z'` and the projection `𝒳 ×_Y V ⟶ V`, read as a square over the
cospan `(V ⟶ Z', 𝒳 ×_Y Z' ⟶ Z')`. -/
noncomputable def factorInnerSquare :
    Bicategory.TwoCommSq (schemeStackMap.{u, w} B S hS a)
      (baseChangeSquare B S hS f b).fst :=
  Bicategory.pasteInnerSq (baseChangeSquare B S hS f b)
    (factorOuterPreHom B S hS f k a b hab)

/-- The first leg of the horizontal comparison square is the projection `𝒳 ×_Y V ⟶ V`. -/
theorem factorInnerSquare_fst :
    (factorInnerSquare B S hS f k a b hab).fst = (baseChangeSquare B S hS f k).fst := rfl

/-- The second leg of the horizontal comparison square is the comparison 1-morphism. -/
theorem factorInnerSquare_snd :
    (factorInnerSquare B S hS f k a b hab).snd = factorMap B S hS f k a b hab := rfl

/-- **The horizontal comparison square of the diagram of Stacks 0H29 is 2-cartesian.** The base
change `𝒳 ×_Y V` is a 2-fibre product of the composed cospan and `𝒳 ×_Y Z'` is one of the inner
cospan, so cancelling the inner square exhibits `𝒳 ×_Y V` as `(𝒳 ×_Y Z') ×_{Z'} V`. -/
noncomputable def isTwoFibreProduct_factorInnerSquare :
    Bicategory.IsTwoFibreProduct (factorInnerSquare B S hS f k a b hab) :=
  isTwoFibreProduct_pasteInnerSqAlgebraicStacks B S hS (baseChangeSquare B S hS f b)
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
      (schemeStackMap.{u, w} B S hS b) f)
    (Bicategory.isTwoFibreProduct_reindexFst _
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
        (schemeStackMap.{u, w} B S hS k) f))
    (factorOuterPreHom B S hS f k a b hab)

/-- **The comparison 1-morphism commutes with the projections, on points.** -/
theorem pointsMap_baseChangeSquare_fst_factorMap
    (x : AlgebraicStacks.points B S hS (baseChangeSquare B S hS f k).pt) :
    AlgebraicStacks.pointsMap B S hS (baseChangeSquare B S hS f b).fst
        (AlgebraicStacks.pointsMap B S hS (factorMap B S hS f k a b hab) x) =
      AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS a)
        (AlgebraicStacks.pointsMap B S hS (baseChangeSquare B S hS f k).fst x) := by
  have h := AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS
    (factorIsoFst B S hS f k a b hab).hom
  rw [AlgebraicStacks.pointsMap_comp, AlgebraicStacks.pointsMap_comp] at h
  exact (congrFun h x).symm

/-- **The image of the preimage of a closed subset along the comparison 1-morphism.** For a
subset `T` of `|𝒳 ×_Y Z'|`, the image in `|V|` of its preimage in `|𝒳 ×_Y V|` is the preimage in
`|V|` of the image of `T` in `|Z'|`. This is **Stacks 04XH** at the horizontal comparison square
of the diagram of Stacks 0H29. -/
theorem image_preimage_factorMap_eq
    (T : Set (AlgebraicStacks.points B S hS (baseChangeSquare B S hS f b).pt)) :
    AlgebraicStacks.pointsMap B S hS (baseChangeSquare B S hS f k).fst ''
        (AlgebraicStacks.pointsMap B S hS (factorMap B S hS f k a b hab) ⁻¹' T) =
      AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS a) ⁻¹'
        (AlgebraicStacks.pointsMap B S hS (baseChangeSquare B S hS f b).fst '' T) :=
  AlgebraicStacks.image_preimage_eq_preimage_image_of_isTwoFibreProduct B S hS
    (factorInnerSquare B S hS f k a b hab).swap
    (Bicategory.isTwoFibreProduct_swap (isTwoFibreProduct_factorInnerSquare B S hS f k a b hab)) T

end Factor

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Clause (2) of Stacks 0H2A at bases reached by a morphism of the site -/

/-- Clause (2) of **Stacks 0H2A** for a 1-morphism `f : 𝒲 ⟶ Stack.schemeStack Y` whose target is
represented by an object of the site, with the base reached by a *morphism of the site*
`π : Z ⟶ Y` whose underlying morphism of schemes is locally of finite presentation.

Clause (2) itself quantifies over 1-morphisms `Stack.schemeStack Z ⟶ 𝒴` locally of finite
presentation and implies this form by
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFinitePresentation_schemeStackMap`. This form
is all the proof of (2) implies (1) consumes, because Stacks 0H29 hands back a base reached by a
morphism of the site of finite presentation. -/
abbrev IsClosedOnSiteFinitePresentationBases {𝒲 : Stack.AlgebraicStacks.{u, w} B S hS}
    {Y : BigFppfOver B S hS} (f : 𝒲 ⟶ Stack.schemeStack.{u, w} B S hS Y) : Prop :=
  ∀ Z : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
    ∀ π : Z ⟶ Y, LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map π) →
      IsClosed B S hS (Stack.baseChangeSquare B S hS f π).fst

/-! ### Stacks 0H2A, (2) implies (1) at a target represented by an affine scheme -/

/-- **Stacks 0H2A, the point-set heart of (2) implies (1).** Let `Y` be an object of the site with
affine underlying scheme and let `f : 𝒲 ⟶ Stack.schemeStack Y` be a quasi-compact 1-morphism of
algebraic stacks over `S` whose base change to every *affine* scheme of the site along a morphism
of the site locally of finite presentation is closed on points. Then the base change of `f` to
every affine scheme of the site along *any* morphism of the site is closed on points.

Let `T ⊆ |𝒲 ×_Y Z|` be closed and let `z ∈ |Z|` miss the image of `T`. **Stacks 0H29** produces an
open neighbourhood `j : V ⟶ Z` of `z`, a factorization `j ≫ π = a ≫ b` with `b : Z' ⟶ Y` of finite
presentation and `Z'` affine, and a closed `T' ⊆ |𝒲 ×_Y Z'|` whose image in `|Z'|` misses `a(z)`
and which contains the image of the preimage of `T` in `|𝒲 ×_Y V|`. The hypothesis applies to
`(Z', b)`, so the image of `T'` in `|Z'|` is closed; pulling its complement back to `|V|` and
pushing forward along the open immersion `j` gives an open neighbourhood of `z`, and that
neighbourhood misses the image of `T`: a point of `|V|` whose image in `|Z|` is hit by `T` lifts
to `|𝒲 ×_Y V|` over a point of `T`, because the horizontal comparison square of the diagram of
Stacks 0H29 is 2-cartesian (`AlgebraicGeometry.Stack.isTwoFibreProduct_factorInnerSquare`, read
through **Stacks 04XH**), and its image in `|𝒲 ×_Y Z'|` then lands in `T'`. -/
theorem isClosed_baseChange_of_isClosedOnSiteFinitePresentationBases
    {Y : BigFppfOver B S hS} (hY : IsAffine ((BigFppfOver.toScheme B S hS).obj Y))
    {𝒲 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒲 ⟶ Stack.schemeStack.{u, w} B S hS Y)
    (hf : Stack.IsQuasiCompactMorphism.{u, w} B S hS f)
    (h : IsClosedOnSiteFinitePresentationBases B S hS f)
    {Z : BigFppfOver B S hS} (hZ : IsAffine ((BigFppfOver.toScheme B S hS).obj Z))
    (π : Z ⟶ Y) :
    IsClosed B S hS (Stack.baseChangeSquare B S hS f π).fst := by
  have h𝒲 : Stack.IsQuasiCompactStack.{u, w} B S hS 𝒲.val 𝒲.property :=
    Stack.isQuasiCompactStack_of_isQuasiCompactMorphism B S hS f hf
      (Stack.isQuasiCompactStack_schemeStack_of_isAffine.{u, w} B S hS Y hY)
  let _ := Stack.pointTopology B S hS (Stack.baseChangeSquare B S hS f π).pt.val
  let _ := Stack.pointTopology B S hS (Stack.schemeStack.{u, w} B S hS Z).val
  intro T hT
  rw [← isOpen_compl_iff]
  refine isOpen_iff_forall_mem_open.2 fun z hz => ?_
  obtain ⟨V, j, hj, v, hv, Z', b, hZ', hbfp, a, hab, T', hT', hz', hsub⟩ :=
    Stack.exists_affine_finitePresentation_separation B S hS hY hZ π f hf h𝒲 z T hT hz
  let _ := Stack.pointTopology B S hS (Stack.baseChangeSquare B S hS f b).pt.val
  let _ := Stack.pointTopology B S hS (Stack.schemeStack.{u, w} B S hS Z').val
  let _ := Stack.pointTopology B S hS (Stack.schemeStack.{u, w} B S hS V).val
  have himg := h Z' hZ' b hbfp.locallyOfFinitePresentation T' hT'
  have hsmooth : IsSmooth B S hS (Stack.schemeStackMap.{u, w} B S hS j) := by
    refine Stack.isSmooth_schemeStackMap.{u, w} B S hS j ?_
    have := hj
    infer_instance
  refine ⟨pointsMap B S hS (Stack.schemeStackMap.{u, w} B S hS j) ''
      (pointsMap B S hS (Stack.schemeStackMap.{u, w} B S hS a) ⁻¹'
        (pointsMap B S hS (Stack.baseChangeSquare B S hS f b).fst '' T')ᶜ), ?_, ?_, ?_⟩
  · rintro - ⟨w, hw, rfl⟩ ⟨t, htT, hteq⟩
    have hmem : w ∈ pointsMap B S hS (Stack.schemeStackMap.{u, w} B S hS j) ⁻¹'
        (pointsMap B S hS (Stack.baseChangeSquare B S hS f π).fst '' T) := ⟨t, htT, hteq⟩
    rw [← Stack.image_preimage_factorMap_eq B S hS f (j ≫ π) j π rfl T] at hmem
    obtain ⟨s, hs, hsw⟩ := hmem
    refine hw ⟨_, hsub ⟨s, hs, rfl⟩, ?_⟩
    rw [Stack.pointsMap_baseChangeSquare_fst_factorMap B S hS f (j ≫ π) a b hab s, hsw]
  · exact isOpenMap_pointsMap_of_isSmooth B S hS _ hsmooth _
      (himg.isOpen_compl.preimage (Stack.continuous_pointsMap B S hS
        (Stack.schemeStack.{u, w} B S hS V).val (Stack.schemeStack.{u, w} B S hS Z').val
        (Stack.schemeStackMap.{u, w} B S hS a).hom.hom))
  · exact ⟨v, hz', hv⟩

/-! ### Universal closedness descends along a jointly surjective family of smooth base changes -/

/-- **Universal closedness descends along a jointly surjective family of smooth base changes.**
If a family of smooth 1-morphisms `g i : 𝒵 i ⟶ 𝒴` covers the points of `𝒴` and the base change
of `f` along every `g i` is universally closed, then `f` is universally closed.

This is the family form of
`AlgebraicGeometry.Stack.AlgebraicStacks.universallyClosed_of_baseChange`: a test 1-morphism
`k : 𝒯 ⟶ 𝒴` is base changed against the whole family, the base changes of the `g i` are smooth
and jointly surjective on the points of `𝒯` by Stacks 04XH, and closedness is read on that family
by `AlgebraicGeometry.Stack.AlgebraicStacks.isClosed_of_isClosed_smooth_cover`. -/
theorem universallyClosed_of_universallyClosed_smooth_cover
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    {I : Type*} (𝒵 : I → Stack.AlgebraicStacks.{u, w} B S hS) (g : ∀ i, 𝒵 i ⟶ 𝒴)
    (hg : ∀ i, IsSmooth B S hS (g i))
    (hcover : ∀ y : points B S hS 𝒴,
      ∃ (i : I) (z : points B S hS (𝒵 i)), pointsMap B S hS (g i) z = y)
    (h : ∀ i, UniversallyClosed B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS (g i) f).fst) :
    UniversallyClosed B S hS f := by
  intro 𝒯 k
  refine isClosed_of_isClosed_smooth_cover B S hS
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS k f).fst
    (fun i => (Stack.twoFibreProductSquareAlgebraicStacks B S hS k (g i)).pt)
    (fun i => (Stack.twoFibreProductSquareAlgebraicStacks B S hS k (g i)).fst)
    (fun i => ?_) ?_ (fun i => ?_)
  · exact isSmooth_baseChange B S hS (g i) k _
      (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS k (g i)) (hg i)
  · intro t
    obtain ⟨i, z, hz⟩ := hcover (pointsMap B S hS k t)
    obtain ⟨r, hr, -⟩ := exists_point_of_isTwoFibreProduct B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS k (g i))
      (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS k (g i)) t z hz.symm
    exact ⟨i, r, hr⟩
  · set R := Stack.twoFibreProductSquareAlgebraicStacks B S hS k (g i) with hR
    refine (isClosed_baseChange_comp_iff B S hS f k R.fst).2 ?_
    refine isClosed_baseChange_of_iso B S hS f R.iso.symm ?_
    exact (isClosed_baseChange_comp_iff B S hS f (g i) R.snd).1 (h i R.pt R.snd)

/-! ### Stacks 0H2A, (2) implies (1) -/

/-- **Stacks 0H2A, (2) implies (1) at a target represented by an affine scheme of the site.**
Closedness of the base change to every affine scheme of the site along a morphism of the site
locally of finite presentation gives closedness of the base change to every affine scheme of the
site along *every* 1-morphism, which is clause (3) of **Stacks 0CL3**.

A 1-morphism of represented algebraic stacks is 2-isomorphic to the one induced by the morphism
of the site underlying it (`AlgebraicGeometry.Stack.schemeStackMapIso`), and closedness of a base
change only depends on the 2-isomorphism class of the base, so
`isClosed_baseChange_of_isClosedOnSiteFinitePresentationBases` applies. -/
theorem universallyClosed_of_isClosedOnSiteFinitePresentationBases_of_isAffine
    {Y : BigFppfOver B S hS} (hY : IsAffine ((BigFppfOver.toScheme B S hS).obj Y))
    {𝒲 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒲 ⟶ Stack.schemeStack.{u, w} B S hS Y)
    (hf : Stack.IsQuasiCompactMorphism.{u, w} B S hS f)
    (h : IsClosedOnSiteFinitePresentationBases B S hS f) :
    UniversallyClosed B S hS f := by
  refine ((universallyClosed_tfae B S hS f).out 3 1).1 fun Z hZ g => ?_
  refine isClosed_baseChange_of_iso B S hS f (Stack.schemeStackMapIso B S hS g).symm ?_
  exact isClosed_baseChange_of_isClosedOnSiteFinitePresentationBases B S hS hY f hf h hZ _

/-- **Stacks 0H2A, (2) implies (1) at a target represented by a scheme of the site.** The affine
opens of that scheme give a jointly surjective family of smooth base changes; the hypothesis is
inherited by each of them, because an affine base reached by a morphism of the site locally of
finite presentation from an affine open of the target is reached by one from the target, and
universal closedness descends along the family. -/
theorem universallyClosed_of_isClosedOnSiteFinitePresentationBases
    {Y : BigFppfOver B S hS} {𝒲 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒲 ⟶ Stack.schemeStack.{u, w} B S hS Y)
    (hf : Stack.IsQuasiCompactMorphism.{u, w} B S hS f)
    (h : IsClosedOnSiteFinitePresentationBases B S hS f) :
    UniversallyClosed B S hS f := by
  refine universallyClosed_of_universallyClosed_smooth_cover B S hS f
    (fun i : ((BigFppfOver.toScheme B S hS).obj Y).affineOpens =>
      Stack.schemeStack.{u, w} B S hS (affineChart Y i))
    (fun i => Stack.schemeStackMap.{u, w} B S hS (affineChartHom Y i))
    (fun i => isSmooth_schemeStackMap B S hS _ (smooth_affineChartHom Y i))
    (exists_affineChart_point.{u, w} B S hS Y) (fun i => ?_)
  refine universallyClosed_of_isClosedOnSiteFinitePresentationBases_of_isAffine B S hS
    (isAffine_affineChart Y i) _
    (Stack.isQuasiCompactMorphism_baseChange B S hS f
      (Stack.schemeStackMap.{u, w} B S hS (affineChartHom Y i)) _
      (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
        (Stack.schemeStackMap.{u, w} B S hS (affineChartHom Y i)) f) hf) ?_
  intro Z hZ π hπ
  refine (isClosed_baseChange_comp_iff B S hS f
    (Stack.schemeStackMap.{u, w} B S hS (affineChartHom Y i))
    (Stack.schemeStackMap.{u, w} B S hS π)).2 ?_
  rw [Stack.schemeStackMap_comp]
  refine h Z hZ (π ≫ affineChartHom Y i) ?_
  have := hπ
  have := smooth_affineChartHom Y i
  rw [Functor.map_comp]
  infer_instance

/-- Universal closedness of a quasi-compact `f` follows from the hypothesis of clause (2) for its
base change along a smooth surjective chart `a : Stack.schemeStack V ⟶ 𝒴`. -/
private theorem universallyClosed_of_isClosedOnSiteFinitePresentationBases_baseChange
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : Stack.IsQuasiCompactMorphism.{u, w} B S hS f) {V : BigFppfOver B S hS}
    (a : Stack.schemeStack.{u, w} B S hS V ⟶ 𝒴) (hasu : Stack.IsSurjective B S hS a)
    (hasm : IsSmooth B S hS a)
    (h : IsClosedOnSiteFinitePresentationBases B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS a f).fst) :
    UniversallyClosed B S hS f :=
  universallyClosed_of_baseChange B S hS f a hasu hasm
    (universallyClosed_of_isClosedOnSiteFinitePresentationBases B S hS _
      (Stack.isQuasiCompactMorphism_baseChange B S hS f a _
        (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS a f) hf) h)

/-- **Stacks 0H2A, (2) implies (1), with the reduction to a target represented by a scheme.** Let
`f : 𝒳 ⟶ 𝒴` be a quasi-compact 1-morphism of algebraic stacks over `S` such that the base change
of `f` to every affine scheme of the site along a 1-morphism locally of finite presentation is
closed on points. Then `f` is universally closed.

Pick a smooth surjective chart `a : Stack.schemeStack V ⟶ 𝒴` of `𝒴` by a scheme of the site.
Universal closedness descends along `a`, so it is enough to prove it for the base change of `f`
along `a`, whose target is represented by a scheme of the site; that base change is quasi-compact
by **Stacks 050V**, and it inherits the hypothesis because `a` is locally of finite presentation
by Stacks 0DNP and clause (2) is inherited by a base change along a 1-morphism locally of finite
presentation. -/
@[stacks 0H2A "(2) implies (1), with the reduction to a target represented by a scheme"]
theorem universallyClosed_of_isQuasiCompactMorphism_of_isClosed_affine_lfp
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : Stack.IsQuasiCompactMorphism.{u, w} B S hS f)
    (h : ∀ Z : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
      ∀ g : Stack.schemeStack.{u, w} B S hS Z ⟶ 𝒴, IsLocallyOfFinitePresentation B S hS g →
        IsClosed B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS g f).fst) :
    UniversallyClosed B S hS f := by
  obtain ⟨V, a, hasm, hasu⟩ := Stack.exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒴
  refine universallyClosed_of_isClosedOnSiteFinitePresentationBases_baseChange B S hS f hf a
    hasu hasm fun Z hZ π hπ => ?_
  exact isClosed_baseChange_affine_isLocallyOfFinitePresentation_baseChange B S hS f a
    (isLocallyOfFinitePresentation_of_isSmooth B S hS a hasm) h Z hZ
    (Stack.schemeStackMap.{u, w} B S hS π)
    (isLocallyOfFinitePresentation_schemeStackMap B S hS π hπ)

/-! ### Stacks 0H2A, (3) implies (1) -/

/-- **Stacks 0H2A, (3) implies (1).** Suppose there are a scheme `V` of the site and a smooth
surjective 1-morphism `a : Stack.schemeStack V ⟶ 𝒴` such that the base change of the quasi-compact
`f` to affine `n`-space over `V` is closed on points for every `n ≥ 0`. Then `f` is universally
closed.

Universal closedness descends along `a`, so it is enough to prove it for the base change `f'` of
`f` along `a`, whose target is represented by a scheme of the site. By (2) implies (1) at such a
target it is enough to show that the base change of `f'` to every affine scheme of the site along
a morphism of the site locally of finite presentation is closed on points; an affine scheme is
quasi-affine and a morphism locally of finite presentation is locally of finite type, so this is
the step of (3) implies (2) at a target represented by a scheme, which goes through the immersion
into affine `n`-space of **Stacks 04II**. -/
@[stacks 0H2A "(3) implies (1)"]
theorem universallyClosed_of_exists_chart_forall_isClosed_baseChange_affineSpaceChart
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : Stack.IsQuasiCompactMorphism.{u, w} B S hS f)
    (h : ∃ (V : BigFppfOver B S hS) (a : Stack.schemeStack.{u, w} B S hS V ⟶ 𝒴),
      Stack.IsSurjective B S hS a ∧ IsSmooth B S hS a ∧
        ∀ n : ℕ, IsClosed B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS
          (Stack.schemeStackMap.{u, w} B S hS (affineSpaceChartHom B S hS V n) ≫ a) f).fst) :
    UniversallyClosed B S hS f := by
  obtain ⟨V, a, hasu, hasm, hn⟩ := h
  refine universallyClosed_of_isClosedOnSiteFinitePresentationBases_baseChange B S hS f hf a
    hasu hasm fun Z hZ π hπ => ?_
  have := hZ
  have := hπ
  refine isClosed_baseChange_schemeStackMap_of_forall_isClosed_baseChange_affineSpaceChart
    B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS a f).fst (fun n => ?_) π
    inferInstance inferInstance
  exact (isClosed_baseChange_comp_iff B S hS f a
    (Stack.schemeStackMap.{u, w} B S hS (affineSpaceChartHom B S hS V n))).2 (hn n)

/-! ### Stacks 0H2A -/

/-- **Stacks 0H2A.** Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact 1-morphism of algebraic stacks over `S`.
The following are equivalent:

1. `f` is universally closed;
2. for every object `Z` of the site whose underlying scheme is affine and every 1-morphism
   `Stack.schemeStack Z ⟶ 𝒴` locally of finite presentation, the map `|𝒳 ×_𝒴 Z| → |Z|` is closed;
3. there are an object `V` of the site and a smooth surjective 1-morphism
   `a : Stack.schemeStack V ⟶ 𝒴` such that `|𝐀^n × (𝒳 ×_𝒴 V)| → |𝐀^n × V|` is closed for every
   `n ≥ 0`.

Clause (3) is read as closedness of the base change of `f` along the composite
`𝐀^n_V ⟶ V ⟶ 𝒴`, which is what `|𝐀^n × (𝒳 ×_𝒴 V)| → |𝐀^n × V|` is over `V`. -/
@[stacks 0H2A]
theorem universallyClosed_tfae_of_isQuasiCompactMorphism
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : Stack.IsQuasiCompactMorphism.{u, w} B S hS f) :
    List.TFAE
      [UniversallyClosed B S hS f,
        ∀ Z : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
          ∀ g : Stack.schemeStack.{u, w} B S hS Z ⟶ 𝒴, IsLocallyOfFinitePresentation B S hS g →
            IsClosed B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS g f).fst,
        ∃ (V : BigFppfOver B S hS) (a : Stack.schemeStack.{u, w} B S hS V ⟶ 𝒴),
          Stack.IsSurjective B S hS a ∧ IsSmooth B S hS a ∧
            ∀ n : ℕ, IsClosed B S hS
              (Stack.twoFibreProductSquareAlgebraicStacks B S hS
                (Stack.schemeStackMap.{u, w} B S hS (affineSpaceChartHom B S hS V n) ≫ a)
                f).fst] := by
  tfae_have 1 → 2 :=
    isClosed_baseChange_affine_isLocallyOfFinitePresentation_of_universallyClosed B S hS f
  tfae_have 2 → 3 :=
    exists_chart_forall_isClosed_baseChange_affineSpaceChart_of_isClosed_affine_lfp B S hS f
  tfae_have 3 → 1 :=
    universallyClosed_of_exists_chart_forall_isClosed_baseChange_affineSpaceChart B S hS f hf
  tfae_finish

end AlgebraicGeometry.Stack.AlgebraicStacks

end
