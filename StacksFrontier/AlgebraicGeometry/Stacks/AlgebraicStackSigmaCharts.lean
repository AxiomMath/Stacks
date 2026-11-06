module

public import Mathlib.AlgebraicGeometry.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelative
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothTfae
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaProductsToDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySchemeMap
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeSmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentedTwoFibreProductProjections
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveOnObjectsRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalChartSmoothNeighbourhood
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ZariskiLimits
public import StacksFrontier.CategoryTheory.FiberedCategory.FiberedInSetoids
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.PullbackFiber
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Stack
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.Dictionary
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting
public import StacksFrontier.CategoryTheory.TwoYoneda.Basic
import all StacksFrontier.AlgebraicGeometry.Spaces.SmoothTfae
import all StacksFrontier.AlgebraicGeometry.Stacks.ArtinCriterion

/-!
# An algebraic stack from smooth scheme charts whose coproduct is in the site

Let `𝒳` be a stack in groupoids over the big fppf site of a scheme `S` whose diagonal is
representable by algebraic spaces, and let `a i : (Sch/W i) ⟶ 𝒳` be a family of smooth
1-morphisms from schemes `W i` over `S` which is jointly surjective. If the big fppf site contains
the coproduct `W = ∐ W i`, then the `a i` glue to a surjective smooth 1-morphism
`(Sch/W) ⟶ 𝒳`, and `𝒳` is an algebraic stack. This is the step "we set `W = ∐ W_i` and we
obtain a surjective smooth morphism `W → 𝒳`" of the proof of Stacks 0DLN (reduction to an
affine base), stated for an arbitrary stack.

## Main results

* `AlgebraicGeometry.Stack.exists_fiber_sigmaOver`: objects of an fppf stack in groupoids over
  the members of a family of schemes glue to an object over their coproduct.
* `AlgebraicGeometry.Stack.exists_sigmaOver_hom`: the corresponding 1-morphism out of the
  coproduct, restricting to the given 1-morphisms up to 2-isomorphism.
* `AlgebraicGeometry.Stack.hasRelativeProperty_smooth_of_openCover`: smoothness of a 1-morphism
  out of a represented category is local on the source for Zariski coverings.
* `AlgebraicGeometry.Stack.isAlgebraicStack_of_sigmaCharts`: the assembly.

## Implementation notes

**The set-theoretic hypothesis.** The coproduct is only a scheme *of the site* when its size is
below the cutoff of the big fppf site. The cutoff is a strong prelimit cardinal of uncountable
cofinality but need not be regular, so a family of fewer than `B.cutoff` members, each of size
below `B.cutoff`, may have a coproduct that is not in the site. The hypothesis `B.Contains (∐ W i)`
is therefore kept as it stands; it is implied by a bound on the index set together with a bound
on the sizes of the members (`AlgebraicGeometry.schemeSize_coproduct_le`).

**Gluing.** The members `W i ⟶ W` form a Zariski covering whose pairwise overlaps between
distinct members are empty, so a descent datum for it is the family of objects alone; the empty
sieve covers the empty scheme, which makes every comparison isomorphism over an empty overlap
unique.

**Smoothness.** By Stacks 04XC it suffices to test the base change along a 1-morphism from an
algebraic space `𝒵`. Pasting the base change `F` with the canonical 2-fibre products along the
members `(Sch/W i) ⟶ (Sch/W)` gives, by Stacks 04SD for represented stacks, open subspaces
`F i` of `F` that cover it, with `F i ⟶ F ⟶ 𝒵` the base change of the smooth composite
`(Sch/W i) ⟶ 𝒳`; smoothness of a morphism of algebraic spaces is local on the source.

**Surjectivity** is surjectivity on objects (Stacks 06D4, compared with the relative notion by
Stacks 06D7), which the family has by hypothesis and the glued 1-morphism inherits through the
2-isomorphisms.

**Universes.** The statements are at `CatFiberedInGroupoids.{u, u, u + 1, u + 1}`, where Stacks
04SD and 04XC are available.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 04SD](https://stacks.math.columbia.edu/tag/04SD)
* [Stacks Project, Tag 04XC](https://stacks.math.columbia.edu/tag/04XC)
* [Stacks Project, Tag 06D7](https://stacks.math.columbia.edu/tag/06D7)
* [Stacks Project, Tag 0DLN](https://stacks.math.columbia.edu/tag/0DLN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u v w t


section Sigma

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The coproduct of a family of objects of the big fppf category of `S`, when the big fppf site
contains the coproduct of the underlying schemes. -/
def sigmaOver {ι : Type u} (W : ι → BigFppfOver B S hS)
    (hW : B.Contains (∐ fun i => (W i).left.1)) : BigFppfOver B S hS :=
  Over.mk (ObjectProperty.homMk (Sigma.desc fun i => B.inclusion.map (W i).hom) :
    B.obj hW ⟶ B.obj hS)

/-- The coprojections of `AlgebraicGeometry.Stack.sigmaOver`. -/
def sigmaOverι {ι : Type u} (W : ι → BigFppfOver B S hS)
    (hW : B.Contains (∐ fun i => (W i).left.1)) (i : ι) : W i ⟶ sigmaOver B S hS W hW :=
  Over.homMk (ObjectProperty.homMk (Sigma.ι (fun j => (W j).left.1) i))
    (ObjectProperty.hom_ext _ (Sigma.ι_desc _ _))

/-- The underlying morphism of schemes of `AlgebraicGeometry.Stack.sigmaOverι B S hS W hW i` is
the coprojection `Sigma.ι` of the coproduct of the schemes `(W j).left.1`. -/
theorem toScheme_map_sigmaOverι {ι : Type u} (W : ι → BigFppfOver B S hS)
    (hW : B.Contains (∐ fun i => (W i).left.1)) (i : ι) :
    (BigFppfOver.toScheme B S hS).map (sigmaOverι B S hS W hW i) =
      Sigma.ι (fun j => (W j).left.1) i :=
  rfl

/-- The underlying morphism of schemes of each coprojection
`AlgebraicGeometry.Stack.sigmaOverι B S hS W hW i` is an open immersion. -/
instance isOpenImmersion_sigmaOverι {ι : Type u} (W : ι → BigFppfOver B S hS)
    (hW : B.Contains (∐ fun i => (W i).left.1)) (i : ι) :
    IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (sigmaOverι B S hS W hW i)) := by
  change _root_.AlgebraicGeometry.IsOpenImmersion (Sigma.ι (fun j => (W j).left.1) i)
  infer_instance

/-- Every point of the coproduct `AlgebraicGeometry.Stack.sigmaOver B S hS W hW` lies in the
image of one of the coprojections `AlgebraicGeometry.Stack.sigmaOverι B S hS W hW i`. -/
theorem exists_sigmaOverι_apply {ι : Type u} (W : ι → BigFppfOver B S hS)
    (hW : B.Contains (∐ fun i => (W i).left.1))
    (x : (BigFppfOver.toScheme B S hS).obj (sigmaOver B S hS W hW)) :
    ∃ i, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (sigmaOverι B S hS W hW i)) := by
  obtain ⟨⟨i, y⟩, h⟩ := (sigmaMk (fun i => (W i).left.1)).surjective x
  refine ⟨i, y, ?_⟩
  rw [toScheme_map_sigmaOverι]
  exact (sigmaMk_mk (fun j => (W j).left.1) i y).symm.trans h

/-- The empty sieve on an object of the big fppf category of `S` whose underlying scheme is empty
is a covering sieve. -/
theorem bot_mem_topology_of_isEmpty {Y : BigFppfOver B S hS}
    (hY : IsEmpty ((BigFppfOver.toScheme B S hS).obj Y)) :
    (⊥ : Sieve Y) ∈ BigFppfOver.topology B S hS Y := by
  have h := BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS
    (ι := PEmpty.{1}) (X := PEmpty.elim) (T := Y) (fun i => i.elim) (fun i => i.elim)
    (fun x => isEmptyElim x)
  simpa only [Sieve.ofArrows, Presieve.ofArrows_of_isEmpty, Sieve.generate_bot] using h

/-- Each coprojection `AlgebraicGeometry.Stack.sigmaOverι B S hS W hW i` is a monomorphism. -/
theorem mono_sigmaOverι {ι : Type u} (W : ι → BigFppfOver B S hS)
    (hW : B.Contains (∐ fun i => (W i).left.1)) (i : ι) : Mono (sigmaOverι B S hS W hW i) :=
  (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance

/-- If `Y` maps to two distinct members `W i` and `W k` compatibly with the coprojections into the
coproduct, then the empty sieve on `Y` is a covering sieve. -/
theorem bot_mem_topology_of_sigmaOverι {ι : Type u} (W : ι → BigFppfOver B S hS)
    (hW : B.Contains (∐ fun i => (W i).left.1)) {i k : ι} (hik : i ≠ k)
    {Y : BigFppfOver B S hS} (a : Y ⟶ W i) (b : Y ⟶ W k)
    (hab : a ≫ sigmaOverι B S hS W hW i = b ≫ sigmaOverι B S hS W hW k) :
    (⊥ : Sieve Y) ∈ BigFppfOver.topology B S hS Y := by
  let T := BigFppfOver.toScheme B S hS
  have hh : T.map a ≫ Sigma.ι (fun j => (W j).left.1) i =
      T.map b ≫ Sigma.ι (fun j => (W j).left.1) k := by
    show T.map a ≫ T.map (sigmaOverι B S hS W hW i) = T.map b ≫ T.map (sigmaOverι B S hS W hW k)
    rw [← T.map_comp, ← T.map_comp, hab]
  exact bot_mem_topology_of_isEmpty B S hS (isEmpty_of_commSq_sigmaι_of_ne ⟨hh⟩ hik)

open CategoryTheory.Functor in
/-- **Gluing objects of a stack over a coproduct.** Objects of a stack in groupoids for the fppf
topology over the members of a family glue to an object over their coproduct. -/
theorem exists_fiber_sigmaOver {D : Type w} [Category.{v} D] (p : D ⥤ BigFppfOver B S hS)
    (hp : p.IsStackInGroupoids.{u + 1} (BigFppfOver.topology B S hS))
    {ι : Type u} (W : ι → BigFppfOver B S hS)
    (hW : B.Contains (∐ fun i => (W i).left.1)) (xs : ∀ i, p.Fiber (W i)) :
    haveI : p.IsFibered := hp.isFiberedInGroupoids.isFibered
    ∃ x : p.Fiber (sigmaOver B S hS W hW),
      ∀ i, Nonempty (pullbackFiber p x (sigmaOverι B S hS W hW i) ≅ xs i) := by
  let : p.IsFibered := hp.isFiberedInGroupoids.isFibered
  let X' : ULift.{u + 1} ι → BigFppfOver B S hS := fun i => W i.down
  let j' : ∀ i, X' i ⟶ sigmaOver B S hS W hW := fun i => sigmaOverι B S hS W hW i.down
  have hj' : Sieve.ofArrows X' j' ∈ BigFppfOver.topology B S hS (sigmaOver B S hS W hW) :=
    BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS j'
      (fun i => isOpenImmersion_sigmaOverι B S hS W hW i.down) (fun x => by
        obtain ⟨i, hi⟩ := exists_sigmaOverι_apply B S hS W hW x
        exact ⟨ULift.up i, hi⟩)
  obtain ⟨x, hx⟩ := exists_fiber_of_disjoint_cover hp X' j' hj'
    (fun i => mono_sigmaOverι B S hS W hW i.down)
    (fun {i k} hik {Y} a b hab => bot_mem_topology_of_sigmaOverι B S hS W hW
      (fun hh => hik (ULift.ext hh)) a b hab) (fun i => xs i.down)
  exact ⟨x, fun i => hx (ULift.up i)⟩

end Sigma


section Smooth

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Smoothness of a scheme chart is local on its source for Zariski coverings.** Let
`g : (Sch/W) ⟶ 𝒳` be a 1-morphism representable by algebraic spaces and let `j i : U i ⟶ W`
be open immersions covering `W`. If every composite `(Sch/U i) ⟶ (Sch/W) ⟶ 𝒳` is smooth, then
so is `g`.

The base change of `g` along a 1-morphism from an algebraic space `𝒵` is tested through
Stacks 04XC: it is represented by an algebraic space `F`, the base changes of the `j i` along
`F ⟶ W` are open subspaces `F i` of `F` covering it (Stacks 04SD for the representing
presheaves of a 2-fibre product), and `F i ⟶ F ⟶ 𝒵` represents the base change of the composite
`(Sch/U i) ⟶ 𝒳`, because pasting two 2-fibre product squares gives one. -/
theorem hasRelativeProperty_smooth_of_openCover
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {W : BigFppfOver B S hS} (g : schemeFibredCategory B S hS W ⟶ 𝒳)
    (hg : IsRepresentableByAlgebraicSpaces B S hS g.hom)
    {ι : Type u} (U : ι → BigFppfOver B S hS) (j : ∀ i, U i ⟶ W)
    (hj : ∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (j i)))
    (hcover : ∀ w : W.left.1, ∃ i u, ((BigFppfOver.toScheme B S hS).map (j i)) u = w)
    (hsmooth : ∀ i, IsRelativelySmooth B S hS (schemeFibredCategoryMap B S hS (j i) ≫ g)) :
    HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.smoothMorphismProperty B S hS) g hg := by
  refine hasRelativeProperty_of_forall_space_baseChange.{u, u} B S hS
    (Space.smoothMorphismProperty B S hS) g hg ?_
  intro 𝒵 _h𝒵 g' Q hQ F G hF hG eF eG
  let rW := representingMap B S hS Q.pt (schemeFibredCategory B S hS W) F (yoneda.obj W) eF
    (PresheafOfCategories.sliceElementsEquivalenceOver W) Q.snd
  have key : ∀ i, ∃ (Fi : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Fi)
      (q : Fi ⟶ F) (r : Fi ⟶ yoneda.obj (U i)),
      IsPullback q r rW (yoneda.map (j i)) ∧
        Space.IsSmooth B S hS (q ≫ representingMap B S hS Q.pt 𝒵 F G eF eG Q.fst) := by
    intro i
    let ji := schemeFibredCategoryMap B S hS (j i)
    let T := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} Q.snd ji
    have hT := CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      Q.snd ji
    obtain ⟨Fi, hFi, ⟨eFi⟩⟩ := isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u}
      B S hS _ _ _ ji Q.snd T hT
      (isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS (j i)) ⟨F, hF, ⟨eF⟩⟩
    obtain ⟨hrep, hP⟩ := hsmooth i
    have h1 := prop_representingMap_of_hasRelativeProperty B S hS
      (Space.smoothMorphismProperty B S hS) _ hrep hP 𝒵 g' (Q.paste T)
      (Bicategory.isTwoFibreProduct_paste hQ hT) Fi G hFi hG eFi eG
    have : (twoFibreProductStructureFunctor B S hS Q.pt (schemeFibredCategory B S hS (U i))
        (schemeFibredCategory B S hS W) Q.snd ji).IsFibered := T.pt.property.isFibered
    have hpb := isPullback_representingMap_twoFibreProduct B S hS Q.pt
      (schemeFibredCategory B S hS (U i)) (schemeFibredCategory B S hS W) F (yoneda.obj (U i))
      (yoneda.obj W) eF (PresheafOfCategories.sliceElementsEquivalenceOver (U i))
      (PresheafOfCategories.sliceElementsEquivalenceOver W) Q.snd ji Fi eFi
    refine ⟨Fi, hFi, representingMap B S hS T.pt Q.pt Fi F eFi eF T.fst,
      representingMap B S hS T.pt (schemeFibredCategory B S hS (U i)) Fi (yoneda.obj (U i)) eFi
        (PresheafOfCategories.sliceElementsEquivalenceOver (U i)) T.snd, ?_, ?_⟩
    · have hji := representingMap_schemeFibredCategoryMap B S hS (j i)
      rw [hji] at hpb
      exact hpb.flip
    · have hc := representingMap_comp B S hS Fi F G eFi eF eG T.fst Q.fst
      rw [← hc]
      exact h1
  choose Fi hFi q r hpb hsm using key
  have hopen : ∀ i, Space.IsOpenImmersion B S hS (q i) := by
    intro i
    have hst := BigFppfOver.isStableUnderBaseChange_inverseImage B S hS
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
    have hbc := MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) (F := yoneda)
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (hpb i).flip
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ (j i)).2 (hj i))
  exact isSmooth_of_openImmersion_cover B S hS hF hG _ Fi hFi q hopen
    (points_cover_of_pullback_of_scheme_cover B S hS U W j hj hcover Fi rW q r hpb) hsm

end Smooth


section Charts

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The 2-Yoneda 1-morphism of an object evaluates back to that object. -/
theorem nonempty_twoYonedaEvaluation_objectMorphism_iso
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    {U : BigFppfOver B S hS} (x : 𝒳.val.p.Fiber U) :
    Nonempty ((𝒳.val.p.twoYonedaEvaluation U).obj (objectMorphism B S hS 𝒳 x).hom ≅ x) := by
  have h : 𝒳.val.p.IsHomLift (𝟙 U)
      (Functor.TwoYoneda.chosenLift 𝒳.val.p 𝒳.isFiberedInGroupoids U x (Over.mk (𝟙 U))).φ :=
    (Functor.TwoYoneda.chosenLift 𝒳.val.p 𝒳.isFiberedInGroupoids U x
      (Over.mk (𝟙 U))).isStronglyCartesian.toIsHomLift
  exact ⟨fiberIsoOfHomLift B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids U _ h⟩

/-- Two 1-morphisms out of the category represented by a scheme are 2-isomorphic as soon as their
values at the identity are isomorphic: the evaluation functor of the 2-Yoneda lemma
(Stacks 004B) is an equivalence. -/
theorem nonempty_iso_of_twoYonedaEvaluation_iso
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    {U : BigFppfOver B S hS} (a b : schemeFibredCategory B S hS U ⟶ 𝒳)
    (e : (𝒳.val.p.twoYonedaEvaluation U).obj a.hom ≅
      (𝒳.val.p.twoYonedaEvaluation U).obj b.hom) :
    Nonempty (a ≅ b) := by
  have := Functor.twoYonedaEvaluation_isEquivalence 𝒳.val.p 𝒳.isFiberedInGroupoids U
  exact ⟨Bicategory.InducedBicategory.isoMk
    ((𝒳.val.p.twoYonedaEvaluation U).preimageIso e)⟩

/-- **A family of smooth scheme charts glued along a coproduct.** Let `a i : (Sch/W i) ⟶ 𝒳` be
1-morphisms into a stack in groupoids over the big fppf site of `S`, and suppose the site contains
the coproduct `W` of the schemes `W i`. Then there is a 1-morphism `g : (Sch/W) ⟶ 𝒳` whose
restriction to each `W i` is 2-isomorphic to `a i`: the objects of `𝒳` over the `W i` named by the
`a i` glue, by the stack condition for the Zariski covering of `W` by the `W i`, whose overlaps are
empty. -/
theorem exists_sigmaOver_hom
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (hstack : 𝒳.val.p.IsStack (BigFppfOver.topology B S hS))
    {ι : Type u} (W : ι → BigFppfOver B S hS) (a : ∀ i, schemeFibredCategory B S hS (W i) ⟶ 𝒳)
    (hW : B.Contains (∐ fun i => (W i).left.1)) :
    ∃ g : schemeFibredCategory B S hS (sigmaOver B S hS W hW) ⟶ 𝒳,
      ∀ i, Nonempty (a i ≅ schemeFibredCategoryMap B S hS (sigmaOverι B S hS W hW i) ≫ g) := by
  have hp : 𝒳.val.p.IsStackInGroupoids.{u + 1} (BigFppfOver.topology B S hS) :=
    hstack.isStackInGroupoids 𝒳.isFiberedInGroupoids
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  obtain ⟨z, hz⟩ := exists_fiber_sigmaOver B S hS 𝒳.val.p hp W hW
    (fun i => (𝒳.val.p.twoYonedaEvaluation (W i)).obj (a i).hom)
  refine ⟨objectMorphism B S hS 𝒳 z, fun i => ?_⟩
  let ιi := sigmaOverι B S hS W hW i
  obtain ⟨e₁⟩ := nonempty_objectMorphism_iso_of_isHomLift B S hS 𝒳 z
    (Functor.pullbackFiber 𝒳.val.p z ιi) ιi (Functor.IsPreFibered.pullbackMap z.2 ιi) inferInstance
  obtain ⟨e₂⟩ := hz i
  obtain ⟨e₃⟩ := nonempty_twoYonedaEvaluation_objectMorphism_iso B S hS 𝒳
    (Functor.pullbackFiber 𝒳.val.p z ιi)
  obtain ⟨e₄⟩ := nonempty_iso_of_twoYonedaEvaluation_iso B S hS 𝒳 (a i)
    (objectMorphism B S hS 𝒳 (Functor.pullbackFiber 𝒳.val.p z ιi)) (e₂.symm ≪≫ e₃.symm)
  exact ⟨e₄ ≪≫ e₁⟩

/-- **An algebraic stack from smooth scheme charts whose coproduct is in the site.** Let `𝒳` be a
stack in groupoids over the big fppf site of `S` whose diagonal is representable by algebraic
spaces. Let `a i : (Sch/W i) ⟶ 𝒳`, `i ∈ I`, be smooth 1-morphisms from the categories represented
by schemes `W i` over `S`, which are jointly surjective: every object of `𝒳` over the spectrum of a
field becomes, after an extension of the field, the image of an object of some `(Sch/W i)`. If the
big fppf site contains the coproduct `W = ∐ W i`, then `𝒳` is an algebraic stack: the `a i` glue to
a surjective smooth 1-morphism `(Sch/W) ⟶ 𝒳`.

This is the step "set `W = ∐ W i`; we obtain a surjective smooth morphism `W → 𝒳`" of the proof
of Stacks 0DLN. The hypothesis that the site contains the coproduct is the set-theoretic content
of that step; see the module docstring. -/
theorem isAlgebraicStack_of_sigmaCharts
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (hstack : 𝒳.val.p.IsStack (BigFppfOver.topology B S hS))
    (hdiag : HasRepresentableDiagonal B S hS 𝒳)
    {ι : Type u} (W : ι → BigFppfOver B S hS) (a : ∀ i, schemeFibredCategory B S hS (W i) ⟶ 𝒳)
    (hsmooth : ∀ i, IsRelativelySmooth B S hS (a i))
    (hsurj : ∀ (U : BigFppfOver B S hS), IsFieldObject B S hS U →
      ∀ (y : 𝒳.val.obj), 𝒳.val.p.obj y = U →
        ∃ (i : ι) (V : BigFppfOver B S hS), IsFieldObject B S hS V ∧
          ∃ (f : V ⟶ U) (x : (schemeFibredCategory B S hS (W i)).val.obj),
            (schemeFibredCategory B S hS (W i)).val.p.obj x = V ∧
            ∃ α : (CatFiberedInGroupoids.homFunctor (a i)).obj x ⟶ y, 𝒳.val.p.IsHomLift f α)
    (hW : B.Contains (∐ fun i => (W i).left.1)) :
    IsAlgebraicStack.{u, w} B S hS 𝒳.val := by
  obtain ⟨g, hg⟩ := exists_sigmaOver_hom B S hS 𝒳 hstack W a hW
  let e := fun i => (hg i).some
  have hgrep : IsRepresentableByAlgebraicSpaces B S hS g.hom :=
    (isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS 𝒳).mp
      ((hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳).mp hdiag) _ g.hom
  have hsm : HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.smoothMorphismProperty B S hS)
      g hgrep :=
    hasRelativeProperty_smooth_of_openCover B S hS g hgrep W (sigmaOverι B S hS W hW)
      (fun i => isOpenImmersion_sigmaOverι B S hS W hW i)
      (exists_sigmaOverι_apply B S hS W hW)
      (fun i => isRelativelySmooth_congr_twoIso B S hS (e i) (hsmooth i))
  have hsu : HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.surjectiveMorphismProperty B S hS)
      g hgrep := by
    refine (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u} B S hS g hgrep).mp ?_
    unfold IsSurjectiveOnObjects
    intro U hU y hy
    obtain ⟨i, V, hV, f, x, hx, α, hα⟩ := hsurj U hU y hy
    refine ⟨V, hV, f, (Over.map (sigmaOverι B S hS W hW i)).obj x, hx,
      (e i).inv.hom.app x ≫ α, ?_⟩
    have : 𝒳.val.p.IsHomLift (𝟙 V) ((e i).inv.hom.app x) := by
      have h := (e i).inv.hom.isHomLift' x
      rwa [hx] at h
    exact IsHomLift.comp_lift_id_left 𝒳.val.p f α ((e i).inv.hom.app x)
  refine ⟨𝒳.isFiberedInGroupoids, ⟨hstack, hstack.isStackInGroupoids 𝒳.isFiberedInGroupoids⟩,
    hdiag, sigmaOver B S hS W hW, g.hom, hgrep,
    fun V y hy F hF he => ⟨hsu V y hy F hF he, hsm V y hy F hF he⟩⟩

end Charts

end AlgebraicGeometry.Stack

end
