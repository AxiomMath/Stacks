module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedSubspaceMaps
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseOpenSchemeLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtensionAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.NoetherianRefinedValuativeCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactAffineMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.Valuative.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Valuative.PushDownSolution
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopologyRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperBaseChangeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperCancellation
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperImageAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackMapProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.RefinedValuativeCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.RefinedValuativeCriterionSeparation
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySchemeMap
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionProperness

/-!
# The affine case of the refined valuative criteria of properness and separation (Stacks 0CQM)

The proof of Stacks 0CQM reduces to an affine locally Noetherian base `V` and a source `U` which
is an affine scheme
(`AlgebraicGeometry.Stack.AlgebraicStacks.isProper_of_discreteExistenceAlong_of_affineCore`).
In that case Chow's lemma (Stacks 0CQ8) supplies a proper surjective 1-morphism `a : X ⟶ 𝒳` from
an algebraic space whose composite to `V` is a morphism of algebraic spaces `g`, the algebraic
space `W = X ×_𝒳 U` is formed, and the source checks that `X ⟶ V` (after replacing `X` by the
closure of the image of `W`) satisfies the discrete existence part of the valuative criterion of
algebraic spaces along `W ⟶ X`. This file carries out that case and derives Stacks 0CQM and
Stacks 0E95 from it.

## Main results

All in the namespace `AlgebraicGeometry.Stack.AlgebraicStacks`:

* `exists_dominatingExtension_lift_of_discreteExistenceAlong`: the claim of the source's proof: a
  valuative square for `g` over a discrete valuation ring whose generic point factors through `W`
  has a dotted arrow after an extension of the fraction field and passage to a dominating
  valuation ring.
* `universallyClosed_of_discreteExistenceAlong_of_chow`: the affine case of Stacks 0CQM, from the
  statement of Stacks 0CQ8.
* `isProper_of_discreteExistenceAlong_of_chow` and
  `isSeparated_of_discreteUniquenessAlong_of_chow`: Stacks 0CQM and Stacks 0E95 with the statement
  of Stacks 0CQ8 as their only hypothesis beyond the source's.

## Implementation notes

Every algebraic stack occurring in the translation except `𝒳` is represented by an algebraic
space (the algebraic stack of a scheme by its Yoneda presheaf, that of an algebraic space by the
space itself, the 2-fibre product by `W`), and 1-morphisms between represented stacks are
compared through the morphisms of representing presheaves they induce (Stacks 04SW,
`AlgebraicGeometry.Stack.representingMap`): two such 1-morphisms are 2-isomorphic exactly when
those morphisms agree. Composites through `𝒳` are therefore always bracketed so that `𝒳` is never
the source or target of a factor whose representing map is taken.

## References

* [Stacks Project, Tag 0CQM](https://stacks.math.columbia.edu/tag/0CQM)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 0CLZ](https://stacks.math.columbia.edu/tag/0CLZ)
* [Stacks Project, Tag 0CMD](https://stacks.math.columbia.edu/tag/0CMD)
* [Stacks Project, Tag 0CQ8](https://stacks.math.columbia.edu/tag/0CQ8)
* [Stacks Project, Tag 0CQK](https://stacks.math.columbia.edu/tag/0CQK)
* [Stacks Project, Tag 0E95](https://stacks.math.columbia.edu/tag/0E95)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The morphism of representing presheaves of a 1-morphism of slices with a canonical
functor.** A 1-morphism `k` between the categories fibred in groupoids represented by two
objects of the site whose underlying functor is `Over.map m` induces `yoneda.map m`. -/
theorem representingMap_eq_yoneda_map_of_toFunctor_eq {T T' : BigFppfOver B S hS} (m : T ⟶ T')
    (k : schemeFibredCategory B S hS T ⟶ schemeFibredCategory B S hS T')
    (hk : k.hom.toFunctor = Over.map m) :
    representingMap B S hS (schemeFibredCategory B S hS T) (schemeFibredCategory B S hS T')
      (yoneda.obj T) (yoneda.obj T') (PresheafOfCategories.sliceElementsEquivalenceOver T)
      (PresheafOfCategories.sliceElementsEquivalenceOver T') k = yoneda.map m := by
  have hkm : k = schemeFibredCategoryMap B S hS m :=
    Bicategory.InducedBicategory.hom_ext (BasedCategory.BasedFunctor.ext' hk)
  subst hkm
  exact representingMap_schemeFibredCategoryMap B S hS m

namespace AlgebraicStacks

/-- **The two projections of the 2-fibre product of `h` and `a` induce compatible morphisms of
representing presheaves.** Let `W` represent the 2-fibre product of `h : U ⟶ 𝒳` and of a
1-morphism `a` from the algebraic stack of an algebraic space `X`, and let `k : 𝒳 ⟶ G` be a
1-morphism to the algebraic stack of an algebraic space `G`. Then the first projection followed
by `h ≫ k` induces the composite of the morphism `W ⟶ X` induced by the second projection with
the morphism `X ⟶ G` induced by `a ≫ k`. -/
theorem representingMap_fst_comp_eq {U : BigFppfOver B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (h : schemeStack.{u, w} B S hS U ⟶ 𝒳) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (a : algebraicSpaceStack.{u, w} B S hS X hX ⟶ 𝒳)
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hG : IsAlgebraicSpace B S hS G)
    (k : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS G hG) (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eW : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductSquareAlgebraicStacks B S hS h a).pt.val.val.p
      (presheafOfCategories (W ⋙ typeToCat)).p) :
    representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS h a).pt.val
      (algebraicSpaceStack.{u, w} B S hS G hG).val W G eW
      (StacksRepresentableCFG.EquivalenceOver.refl
        (algebraicSpaceStack.{u, w} B S hS G hG).val.val.p)
      ((twoFibreProductSquareAlgebraicStacks B S hS h a).fst.hom ≫ h.hom ≫ k.hom) =
    representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS h a).pt.val
      (algebraicSpaceStack.{u, w} B S hS X hX).val W X eW
      (StacksRepresentableCFG.EquivalenceOver.refl
        (algebraicSpaceStack.{u, w} B S hS X hX).val.val.p)
      (twoFibreProductSquareAlgebraicStacks B S hS h a).snd.hom ≫
    representingMap B S hS (algebraicSpaceStack.{u, w} B S hS X hX).val
      (algebraicSpaceStack.{u, w} B S hS G hG).val X G
      (StacksRepresentableCFG.EquivalenceOver.refl
        (algebraicSpaceStack.{u, w} B S hS X hX).val.val.p)
      (StacksRepresentableCFG.EquivalenceOver.refl
        (algebraicSpaceStack.{u, w} B S hS G hG).val.val.p) (a.hom ≫ k.hom) := by
  have η : (twoFibreProductSquareAlgebraicStacks B S hS h a).fst.hom ≫ h.hom ≫ k.hom ≅
      (twoFibreProductSquareAlgebraicStacks B S hS h a).snd.hom ≫ a.hom ≫ k.hom :=
    (α_ _ _ _).symm ≪≫ whiskerRightIso
      (InducedBicategory.isoHom (twoFibreProductSquareAlgebraicStacks B S hS h a).iso) k.hom ≪≫
        α_ _ _ _
  refine (representingMap_congr_twoIso B S hS W G eW
    (StacksRepresentableCFG.EquivalenceOver.refl
      (algebraicSpaceStack.{u, w} B S hS G hG).val.val.p) η).trans ?_
  exact representingMap_comp B S hS W X G eW
    (StacksRepresentableCFG.EquivalenceOver.refl
      (algebraicSpaceStack.{u, w} B S hS X hX).val.val.p)
    (StacksRepresentableCFG.EquivalenceOver.refl
      (algebraicSpaceStack.{u, w} B S hS G hG).val.val.p)
    (twoFibreProductSquareAlgebraicStacks B S hS h a).snd.hom (a.hom ≫ k.hom)

/-- Composing with a comparison 1-morphism `e` that induces the identity does not change the
representing map. -/
private theorem representingMap_comp_comparison_eq {V : BigFppfOver B S hS}
    (e : schemeStack.{u, w} B S hS V ⟶
      algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V))
    (he : representingMap B S hS (schemeStack.{u, w} B S hS V).val
      (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)).val
      (yoneda.obj V) (yoneda.obj V)
      (PresheafOfCategories.sliceElementsEquivalenceOver V)
      (StacksRepresentableCFG.EquivalenceOver.refl _) e.hom = 𝟙 _)
    {𝒜 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver 𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (m : 𝒜 ⟶ (schemeStack.{u, w} B S hS V).val) :
    representingMap B S hS 𝒜
      (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)).val
      F (yoneda.obj V) eF (StacksRepresentableCFG.EquivalenceOver.refl _) (m ≫ e.hom) =
    representingMap B S hS 𝒜 (schemeStack.{u, w} B S hS V).val F (yoneda.obj V) eF
      (PresheafOfCategories.sliceElementsEquivalenceOver V) m :=
  (representingMap_comp B S hS (𝒜 := 𝒜) (ℬ := (schemeStack.{u, w} B S hS V).val)
    (𝒞 := (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V)
      (isAlgebraicSpace_yoneda B S hS V)).val) F (yoneda.obj V) (yoneda.obj V) eF
    (PresheafOfCategories.sliceElementsEquivalenceOver V)
    (StacksRepresentableCFG.EquivalenceOver.refl _) m e.hom).trans
    (by rw [he, Category.comp_id])

/-- **The claim in the proof of Stacks 0CQM.** Let `f : 𝒳 ⟶ V` be a 1-morphism to the algebraic
stack of a scheme `V` of the site satisfying the discrete existence part of the valuative
criterion along `h : U ⟶ 𝒳`, let `e : V ⟶ h_V` be a 1-morphism to the algebraic stack of the
algebraic space `h_V` inducing the identity of `h_V`, let `a : X ⟶ 𝒳` be a proper 1-morphism from
the algebraic stack of an algebraic space `X` whose composite with `f` and `e` induces
`g : X ⟶ h_V`, and let `W` represent the 2-fibre product of `h` and `a`, with `w : W ⟶ X` induced
by its second projection. Then every valuative square for `g` over a discrete valuation ring whose
generic point factors through `w` has a dotted arrow after an extension of the fraction field and
passage to a dominating valuation ring.

The square is read as a valuative square for `f` with generic point through `h`, by the
comparison of representing presheaves; the hypothesis gives a dotted arrow `Spec A' ⟶ 𝒳` after a
dominating extension, and the existence part of the valuative criterion for the proper `a`
(Stacks 0CLZ) lifts it to `Spec A'' ⟶ X` after a further one. -/
theorem exists_dominatingExtension_lift_of_discreteExistenceAlong
    {V U : BigFppfOver B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ schemeStack.{u, w} B S hS V) (h : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (hlift : ValuativeCriterion.DiscreteExistenceAlong B S hS h f)
    (e : schemeStack.{u, w} B S hS V ⟶
      algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V))
    (he : representingMap B S hS (schemeStack.{u, w} B S hS V).val
      (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)).val
      (yoneda.obj V) (yoneda.obj V)
      (PresheafOfCategories.sliceElementsEquivalenceOver V)
      (StacksRepresentableCFG.EquivalenceOver.refl _) e.hom = 𝟙 _)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (a : algebraicSpaceStack.{u, w} B S hS X hX ⟶ 𝒳) (ha : IsProper B S hS a)
    (g : X ⟶ yoneda.obj V)
    (hg : representingMap B S hS (algebraicSpaceStack.{u, w} B S hS X hX).val
      (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)).val
      X (yoneda.obj V)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) (a.hom ≫ f.hom ≫ e.hom) = g)
    (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eW : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductSquareAlgebraicStacks B S hS h a).pt.val.val.p
      (presheafOfCategories (W ⋙ typeToCat)).p)
    (q : Space.ValuativeSquare g) (hq : IsDiscreteValuationRing q.R)
    (t : yoneda.obj (siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ W)
    (ht : t ≫ representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS h a).pt.val
      (algebraicSpaceStack.{u, w} B S hS X hX).val W X eW
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (twoFibreProductSquareAlgebraicStacks B S hS h a).snd.hom = q.generic) :
    ∃ E : q.DominatingExtension, Nonempty E.square.Lift := by
  classical
  -- the first projection followed by `h ≫ f ≫ e` induces `w ≫ g`
  have hF1 := representingMap_fst_comp_eq B S hS h hX a (isAlgebraicSpace_yoneda B S hS V)
    (f ≫ e) W eW
  rw [show (f ≫ e).hom = f.hom ≫ e.hom from rfl, hg] at hF1
  -- the canonical map of the square, and its bottom edge as a morphism of the site
  let cm : siteObject B S hS q.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base) ⟶
      siteObject B S hS q.ring_mem q.base :=
    Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K))) :
      B.obj q.field_mem ⟶ B.obj q.ring_mem)
  have hcomm : q.generic ≫ g = yoneda.map cm ≫ q.special := q.comm
  obtain ⟨s, hs⟩ : ∃ s, yoneda.map s = q.special :=
    ⟨yoneda.preimage q.special, yoneda.map_preimage _⟩
  -- the generic point of `W`, read as a 1-morphism into the 2-fibre product
  obtain ⟨c, hc⟩ := exists_oneMorphism_representingMap_eq B S hS
    (𝒳 := schemeStack.{u, w} B S hS (siteObject B S hS q.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)))
    (𝒴 := (twoFibreProductSquareAlgebraicStacks B S hS h a).pt) _ W
    (PresheafOfCategories.sliceElementsEquivalenceOver _) eW t
  -- the valuative square for `f` with generic point through `h`
  have hγ : representingMap B S hS
      (schemeFibredCategory B S hS (siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)))
      (schemeStack.{u, w} B S hS V).val (yoneda.obj _) (yoneda.obj V)
      (PresheafOfCategories.sliceElementsEquivalenceOver _)
      (PresheafOfCategories.sliceElementsEquivalenceOver V)
      (schemeMorphism B cm ≫ (schemeStackMap.{u, w} B S hS s).hom) =
    representingMap B S hS
      (schemeFibredCategory B S hS (siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)))
      (schemeStack.{u, w} B S hS V).val (yoneda.obj _) (yoneda.obj V)
      (PresheafOfCategories.sliceElementsEquivalenceOver _)
      (PresheafOfCategories.sliceElementsEquivalenceOver V)
      (((c.hom ≫ (twoFibreProductSquareAlgebraicStacks B S hS h a).fst.hom) ≫ h.hom) ≫
        f.hom) := by
    refine (representingMap_comp B S hS
      (𝒜 := schemeFibredCategory B S hS (siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)))
      (ℬ := schemeFibredCategory B S hS (siteObject B S hS q.ring_mem q.base))
      (𝒞 := (schemeStack.{u, w} B S hS V).val) (yoneda.obj _) (yoneda.obj _) (yoneda.obj V)
      (PresheafOfCategories.sliceElementsEquivalenceOver _)
      (PresheafOfCategories.sliceElementsEquivalenceOver _)
      (PresheafOfCategories.sliceElementsEquivalenceOver V) (schemeMorphism B cm)
      (schemeStackMap.{u, w} B S hS s).hom).trans ?_
    rw [representingMap_eq_yoneda_map_of_toFunctor_eq B S hS cm _ rfl,
      representingMap_eq_yoneda_map_of_toFunctor_eq B S hS s _ rfl, hs, ← hcomm, ← ht,
      ← representingMap_comp_comparison_eq B S hS e he
        (𝒜 := schemeFibredCategory B S hS _) _
        (PresheafOfCategories.sliceElementsEquivalenceOver _)]
    have η : (((c.hom ≫ (twoFibreProductSquareAlgebraicStacks B S hS h a).fst.hom) ≫ h.hom) ≫
        f.hom) ≫ e.hom ≅
        c.hom ≫ (twoFibreProductSquareAlgebraicStacks B S hS h a).fst.hom ≫ h.hom ≫ f.hom ≫ e.hom :=
      α_ _ _ _ ≪≫ α_ _ _ _ ≪≫ α_ _ _ _
    rw [representingMap_congr_twoIso B S hS
      (𝒜 := schemeFibredCategory B S hS (siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)))
      (𝒞 := (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V)
        (isAlgebraicSpace_yoneda B S hS V)).val) _ _
      (PresheafOfCategories.sliceElementsEquivalenceOver _)
      (StacksRepresentableCFG.EquivalenceOver.refl
        (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V)
          (isAlgebraicSpace_yoneda B S hS V)).val.val.p) η,
      representingMap_comp B S hS
        (𝒜 := schemeFibredCategory B S hS (siteObject B S hS q.field_mem
          (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)))
        (ℬ := (twoFibreProductSquareAlgebraicStacks B S hS h a).pt.val)
        (𝒞 := (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V)
          (isAlgebraicSpace_yoneda B S hS V)).val) _ W _
        (PresheafOfCategories.sliceElementsEquivalenceOver _) eW
        (StacksRepresentableCFG.EquivalenceOver.refl
          (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V)
            (isAlgebraicSpace_yoneda B S hS V)).val.val.p) c.hom _, hc, hF1, Category.assoc]
  obtain ⟨γu⟩ := nonempty_unique_twoIso_of_representingMap_eq B S hS _ _ _ _ _ _ hγ
  let Q₁ : ValuativeSquare B S hS f :=
    { R := q.R, K := q.K, ring_mem := q.ring_mem, field_mem := q.field_mem, base := q.base,
      genericMap := cm, genericMap_left := rfl, j := schemeMorphism B cm, j_canonical := rfl,
      x := (c ≫ (twoFibreProductSquareAlgebraicStacks B S hS h a).fst).hom ≫ h.hom,
      y := (schemeStackMap.{u, w} B S hS s).hom, γ := γu.default.hom }
  obtain ⟨E, ⟨d⟩⟩ := hlift Q₁ hq (c ≫ (twoFibreProductSquareAlgebraicStacks B S hS h a).fst).hom rfl
  -- the extended generic point of `X`
  obtain ⟨c₂, hc₂⟩ := exists_oneMorphism_representingMap_eq B S hS
    (𝒳 := schemeStack.{u, w} B S hS (siteObject B S hS E.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap E.R' E.K')) ≫
        Spec.map (CommRingCat.ofHom E.ringMap) ≫ q.base)))
    (𝒴 := algebraicSpaceStack.{u, w} B S hS X hX) _ X
    (PresheafOfCategories.sliceElementsEquivalenceOver _)
    (StacksRepresentableCFG.EquivalenceOver.refl
      (algebraicSpaceStack.{u, w} B S hS X hX).val.val.p)
    (yoneda.map E.genericOver ≫ t ≫ representingMap B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS h a).pt.val
      (algebraicSpaceStack.{u, w} B S hS X hX).val W X eW
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (twoFibreProductSquareAlgebraicStacks B S hS h a).snd.hom)
  have h₃ : representingMap B S hS
      (schemeFibredCategory B S hS (siteObject B S hS E.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap E.R' E.K')) ≫
          Spec.map (CommRingCat.ofHom E.ringMap) ≫ q.base)))
      (algebraicSpaceStack.{u, w} B S hS X hX).val _ X
      (PresheafOfCategories.sliceElementsEquivalenceOver _)
      (StacksRepresentableCFG.EquivalenceOver.refl
        (algebraicSpaceStack.{u, w} B S hS X hX).val.val.p)
      (E.k ≫ c.hom ≫ (twoFibreProductSquareAlgebraicStacks B S hS h a).snd.hom) =
    representingMap B S hS
      (schemeFibredCategory B S hS (siteObject B S hS E.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap E.R' E.K')) ≫
          Spec.map (CommRingCat.ofHom E.ringMap) ≫ q.base)))
      (algebraicSpaceStack.{u, w} B S hS X hX).val _ X
      (PresheafOfCategories.sliceElementsEquivalenceOver _)
      (StacksRepresentableCFG.EquivalenceOver.refl
        (algebraicSpaceStack.{u, w} B S hS X hX).val.val.p) c₂.hom := by
    rw [hc₂, representingMap_comp B S hS
        (𝒜 := schemeFibredCategory B S hS (siteObject B S hS E.field_mem
          (Spec.map (CommRingCat.ofHom (algebraMap E.R' E.K')) ≫
            Spec.map (CommRingCat.ofHom E.ringMap) ≫ q.base)))
        (ℬ := schemeFibredCategory B S hS (siteObject B S hS q.field_mem
          (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)))
        (𝒞 := (algebraicSpaceStack.{u, w} B S hS X hX).val) _ _ X
        (PresheafOfCategories.sliceElementsEquivalenceOver _)
        (PresheafOfCategories.sliceElementsEquivalenceOver _)
        (StacksRepresentableCFG.EquivalenceOver.refl
          (algebraicSpaceStack.{u, w} B S hS X hX).val.val.p) E.k _,
      representingMap_eq_yoneda_map_of_toFunctor_eq B S hS E.genericOver _ E.k_canonical,
      representingMap_comp B S hS
        (𝒜 := schemeFibredCategory B S hS (siteObject B S hS q.field_mem
          (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)))
        (ℬ := (twoFibreProductSquareAlgebraicStacks B S hS h a).pt.val)
        (𝒞 := (algebraicSpaceStack.{u, w} B S hS X hX).val) _ W X
        (PresheafOfCategories.sliceElementsEquivalenceOver _) eW
        (StacksRepresentableCFG.EquivalenceOver.refl
          (algebraicSpaceStack.{u, w} B S hS X hX).val.val.p) c.hom _, hc]
  obtain ⟨u₃⟩ := nonempty_unique_twoIso_of_representingMap_eq B S hS _ _ _ _ _ _ h₃
  let ι₂ : E.k ≫ Q₁.x ≅ c₂.hom ≫ a.hom :=
    whiskerLeftIso E.k (α_ c.hom (twoFibreProductSquareAlgebraicStacks B S hS h a).fst.hom h.hom ≪≫
      whiskerLeftIso c.hom
        (InducedBicategory.isoHom (twoFibreProductSquareAlgebraicStacks B S hS h a).iso) ≪≫
      (α_ c.hom (twoFibreProductSquareAlgebraicStacks B S hS h a).snd.hom a.hom).symm) ≪≫
    (α_ E.k (c.hom ≫ (twoFibreProductSquareAlgebraicStacks B S hS h a).snd.hom) a.hom).symm ≪≫
    whiskerRightIso u₃.default a.hom
  -- the valuative square for `a`
  let Q₂ : ValuativeSquare B S hS a :=
    { R := E.R', K := E.K', ring_mem := E.ring_mem, field_mem := E.field_mem,
      base := Spec.map (CommRingCat.ofHom E.ringMap) ≫ q.base,
      genericMap := E.genericMap, genericMap_left := E.genericMap_left, j := E.j,
      j_canonical := E.j_canonical, x := c₂.hom, y := d.a, γ := d.α ≫ ι₂.hom }
  obtain ⟨E₂, ⟨d₂⟩⟩ :=
    (valuativeCriterion_of_isProper B S hS a (isQuasiSeparated_of_isSeparated B S hS ha.1) ha).2 Q₂
  -- the dotted arrow `Spec A'' ⟶ X`, as a morphism of presheaves
  let ℓ := representingMap B S hS
    (schemeFibredCategory B S hS (siteObject B S hS E₂.ring_mem
      (Spec.map (CommRingCat.ofHom E₂.ringMap) ≫ Spec.map (CommRingCat.ofHom E.ringMap) ≫ q.base)))
    (algebraicSpaceStack.{u, w} B S hS X hX).val _ X
    (PresheafOfCategories.sliceElementsEquivalenceOver _)
    (StacksRepresentableCFG.EquivalenceOver.refl
      (algebraicSpaceStack.{u, w} B S hS X hX).val.val.p) d₂.a
  -- its upper triangle
  have hR₁ : yoneda.map E₂.genericMap ≫ ℓ =
      yoneda.map E₂.genericOver ≫ yoneda.map E.genericOver ≫ q.generic := by
    have hd := representingMap_congr_twoIso B S hS
      (𝒜 := schemeFibredCategory B S hS (siteObject B S hS E₂.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap E₂.R' E₂.K')) ≫
          Spec.map (CommRingCat.ofHom E₂.ringMap) ≫ Spec.map (CommRingCat.ofHom E.ringMap) ≫
            q.base)))
      (𝒞 := (algebraicSpaceStack.{u, w} B S hS X hX).val) _ X
      (PresheafOfCategories.sliceElementsEquivalenceOver _)
      (StacksRepresentableCFG.EquivalenceOver.refl
        (algebraicSpaceStack.{u, w} B S hS X hX).val.val.p)
      (@asIso _ _ _ _ d₂.α ((CatFiberedInGroupoids.homGroupoid _ _).all_isIso _))
    rw [representingMap_comp B S hS
        (𝒜 := schemeFibredCategory B S hS (siteObject B S hS E₂.field_mem
          (Spec.map (CommRingCat.ofHom (algebraMap E₂.R' E₂.K')) ≫
            Spec.map (CommRingCat.ofHom E₂.ringMap) ≫ Spec.map (CommRingCat.ofHom E.ringMap) ≫
              q.base)))
        (ℬ := schemeFibredCategory B S hS (siteObject B S hS E₂.ring_mem
          (Spec.map (CommRingCat.ofHom E₂.ringMap) ≫ Spec.map (CommRingCat.ofHom E.ringMap) ≫
            q.base)))
        (𝒞 := (algebraicSpaceStack.{u, w} B S hS X hX).val) _ _ X
        (PresheafOfCategories.sliceElementsEquivalenceOver _)
        (PresheafOfCategories.sliceElementsEquivalenceOver _)
        (StacksRepresentableCFG.EquivalenceOver.refl
          (algebraicSpaceStack.{u, w} B S hS X hX).val.val.p) E₂.j d₂.a,
      representingMap_comp B S hS
        (𝒜 := schemeFibredCategory B S hS (siteObject B S hS E₂.field_mem
          (Spec.map (CommRingCat.ofHom (algebraMap E₂.R' E₂.K')) ≫
            Spec.map (CommRingCat.ofHom E₂.ringMap) ≫ Spec.map (CommRingCat.ofHom E.ringMap) ≫
              q.base)))
        (ℬ := schemeFibredCategory B S hS (siteObject B S hS E.field_mem
          (Spec.map (CommRingCat.ofHom (algebraMap E.R' E.K')) ≫
            Spec.map (CommRingCat.ofHom E.ringMap) ≫ q.base)))
        (𝒞 := (algebraicSpaceStack.{u, w} B S hS X hX).val) _ _ X
        (PresheafOfCategories.sliceElementsEquivalenceOver _)
        (PresheafOfCategories.sliceElementsEquivalenceOver _)
        (StacksRepresentableCFG.EquivalenceOver.refl
          (algebraicSpaceStack.{u, w} B S hS X hX).val.val.p) E₂.k c₂.hom,
      representingMap_eq_yoneda_map_of_toFunctor_eq B S hS E₂.genericMap _ E₂.j_canonical,
      representingMap_eq_yoneda_map_of_toFunctor_eq B S hS E₂.genericOver _ E₂.k_canonical,
      hc₂, ht] at hd
    exact hd
  -- its lower triangle
  have hR₂ : ℓ ≫ g = yoneda.map E₂.specialOver ≫ yoneda.map E.specialOver ≫ q.special := by
    let ι₄ : d₂.a ≫ a.hom ≫ f.hom ≫ e.hom ≅ E₂.a ≫ E.a ≫ Q₁.y ≫ e.hom :=
      (α_ d₂.a a.hom (f.hom ≫ e.hom)).symm ≪≫
        whiskerRightIso
          (@asIso _ _ _ _ d₂.β ((CatFiberedInGroupoids.homGroupoid _ _).all_isIso _)).symm
          (f.hom ≫ e.hom) ≪≫ α_ E₂.a d.a (f.hom ≫ e.hom) ≪≫
        whiskerLeftIso E₂.a ((α_ d.a f.hom e.hom).symm ≪≫
          whiskerRightIso
            (@asIso _ _ _ _ d.β ((CatFiberedInGroupoids.homGroupoid _ _).all_isIso _)).symm
            e.hom ≪≫ α_ E.a Q₁.y e.hom)
    have hd := representingMap_congr_twoIso B S hS
      (𝒜 := schemeFibredCategory B S hS (siteObject B S hS E₂.ring_mem
        (Spec.map (CommRingCat.ofHom E₂.ringMap) ≫ Spec.map (CommRingCat.ofHom E.ringMap) ≫
          q.base)))
      (𝒞 := (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V)
        (isAlgebraicSpace_yoneda B S hS V)).val) _ (yoneda.obj V)
      (PresheafOfCategories.sliceElementsEquivalenceOver _)
      (StacksRepresentableCFG.EquivalenceOver.refl
        (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V)
          (isAlgebraicSpace_yoneda B S hS V)).val.val.p) ι₄
    rw [representingMap_comp B S hS
        (𝒜 := schemeFibredCategory B S hS (siteObject B S hS E₂.ring_mem
          (Spec.map (CommRingCat.ofHom E₂.ringMap) ≫ Spec.map (CommRingCat.ofHom E.ringMap) ≫
            q.base)))
        (ℬ := (algebraicSpaceStack.{u, w} B S hS X hX).val)
        (𝒞 := (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V)
          (isAlgebraicSpace_yoneda B S hS V)).val) _ X (yoneda.obj V)
        (PresheafOfCategories.sliceElementsEquivalenceOver _)
        (StacksRepresentableCFG.EquivalenceOver.refl
          (algebraicSpaceStack.{u, w} B S hS X hX).val.val.p)
        (StacksRepresentableCFG.EquivalenceOver.refl
          (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V)
            (isAlgebraicSpace_yoneda B S hS V)).val.val.p) d₂.a _,
      hg,
      representingMap_comp B S hS
        (𝒜 := schemeFibredCategory B S hS (siteObject B S hS E₂.ring_mem
          (Spec.map (CommRingCat.ofHom E₂.ringMap) ≫ Spec.map (CommRingCat.ofHom E.ringMap) ≫
            q.base)))
        (ℬ := schemeFibredCategory B S hS (siteObject B S hS E.ring_mem
          (Spec.map (CommRingCat.ofHom E.ringMap) ≫ q.base)))
        (𝒞 := (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V)
          (isAlgebraicSpace_yoneda B S hS V)).val) _ _ (yoneda.obj V)
        (PresheafOfCategories.sliceElementsEquivalenceOver _)
        (PresheafOfCategories.sliceElementsEquivalenceOver _)
        (StacksRepresentableCFG.EquivalenceOver.refl
          (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V)
            (isAlgebraicSpace_yoneda B S hS V)).val.val.p) E₂.a _,
      representingMap_comp B S hS
        (𝒜 := schemeFibredCategory B S hS (siteObject B S hS E.ring_mem
          (Spec.map (CommRingCat.ofHom E.ringMap) ≫ q.base)))
        (ℬ := schemeFibredCategory B S hS (siteObject B S hS q.ring_mem q.base))
        (𝒞 := (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V)
          (isAlgebraicSpace_yoneda B S hS V)).val) _ _ (yoneda.obj V)
        (PresheafOfCategories.sliceElementsEquivalenceOver _)
        (PresheafOfCategories.sliceElementsEquivalenceOver _)
        (StacksRepresentableCFG.EquivalenceOver.refl
          (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V)
            (isAlgebraicSpace_yoneda B S hS V)).val.val.p) E.a _,
      representingMap_comp_comparison_eq B S hS e he
        (𝒜 := schemeFibredCategory B S hS _) _
        (PresheafOfCategories.sliceElementsEquivalenceOver _),
      representingMap_eq_yoneda_map_of_toFunctor_eq B S hS E₂.specialOver _ E₂.a_canonical,
      representingMap_eq_yoneda_map_of_toFunctor_eq B S hS E.specialOver _ E.a_canonical,
      representingMap_eq_yoneda_map_of_toFunctor_eq B S hS s _ rfl, hs] at hd
    exact hd
  -- the composite dominating extension, and the dotted arrow over it
  have hgm : E₂.genericMap = Over.homMk (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (algebraMap E₂.R' E₂.K'))) :
        B.obj E₂.field_mem ⟶ B.obj E₂.ring_mem) :=
    Over.OverMorphism.ext (B.inclusion.map_injective E₂.genericMap_left)
  rw [hgm] at hR₁
  let E₀ : q.DominatingExtension := {
    square :=
      { R := E₂.R', K := E₂.K', ring_mem := E₂.ring_mem, field_mem := E₂.field_mem
        base := Spec.map (CommRingCat.ofHom E₂.ringMap) ≫
          Spec.map (CommRingCat.ofHom E.ringMap) ≫ q.base
        generic := yoneda.map E₂.genericOver ≫ yoneda.map E.genericOver ≫ q.generic
        special := yoneda.map E₂.specialOver ≫ yoneda.map E.specialOver ≫ q.special
        comm := by rw [← hR₁, Category.assoc, hR₂] }
    ringMap := E₂.ringMap.comp E.ringMap
    fieldMap := E₂.fieldMap.comp E.fieldMap
    isLocalHom := by
      have : IsLocalHom E.ringMap := E.isLocalHom
      have : IsLocalHom E₂.ringMap := E₂.isLocalHom
      exact RingHom.isLocalHom_comp E₂.ringMap E.ringMap
    fraction_comm := by
      change (algebraMap E₂.R' E₂.K').comp (E₂.ringMap.comp E.ringMap) = _
      rw [← RingHom.comp_assoc, E₂.fraction_comm, RingHom.comp_assoc, E.fraction_comm,
        RingHom.comp_assoc]
    base_comm := by
      change Spec.map (CommRingCat.ofHom E₂.ringMap) ≫ Spec.map (CommRingCat.ofHom E.ringMap) ≫
        q.base = Spec.map (CommRingCat.ofHom (E₂.ringMap.comp E.ringMap)) ≫ q.base
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    genericOver := E₂.genericOver ≫ E.genericOver
    genericOver_left := by
      change (B.inclusion).map (E₂.genericOver.left ≫ E.genericOver.left) =
        Spec.map (CommRingCat.ofHom (E₂.fieldMap.comp E.fieldMap))
      rw [Functor.map_comp, E₂.genericOver_left, E.genericOver_left, CommRingCat.ofHom_comp,
        Spec.map_comp]
    specialOver := E₂.specialOver ≫ E.specialOver
    specialOver_left := by
      change (B.inclusion).map (E₂.specialOver.left ≫ E.specialOver.left) =
        Spec.map (CommRingCat.ofHom (E₂.ringMap.comp E.ringMap))
      rw [Functor.map_comp, E₂.specialOver_left, E.specialOver_left, CommRingCat.ofHom_comp,
        Spec.map_comp]
    generic_comm := by
      change yoneda.map E₂.genericOver ≫ yoneda.map E.genericOver ≫ q.generic =
        yoneda.map (E₂.genericOver ≫ E.genericOver) ≫ q.generic
      rw [Functor.map_comp, Category.assoc]
    special_comm := by
      change yoneda.map E₂.specialOver ≫ yoneda.map E.specialOver ≫ q.special =
        yoneda.map (E₂.specialOver ≫ E.specialOver) ≫ q.special
      rw [Functor.map_comp, Category.assoc] }
  exact ⟨E₀, ⟨{ map := ℓ, generic_comm := hR₁, special_comm := hR₂ }⟩⟩

/-- **The affine case of Stacks 0CQM, from Chow's lemma.** Let `V` be an affine locally Noetherian
scheme of the site, `f : 𝒳 ⟶ V` a separated 1-morphism of finite type from an algebraic stack, and
`h : U ⟶ 𝒳` a 1-morphism locally of finite type from an affine scheme `U` with dense image, such
that `f` satisfies the discrete existence part of the valuative criterion along `h`. Then `f` is
universally closed. `h0CQ8` is the statement of Chow's lemma for algebraic stacks (Stacks 0CQ8),
exactly as the source states it, which is applied to `𝒳 ⟶ V` read over the algebraic space `h_V`.

The proof is the source's. Chow's lemma gives a proper surjective `a : X ⟶ 𝒳` from an algebraic
space whose composite to `V` is a morphism of algebraic spaces `g`. The 2-fibre product
`W = X ×_𝒳 U` is an algebraic space (Stacks 0300) of finite type over `X`. On the reduced closed
subspace `X'` of `X` on the closure of the image of `W`, the morphism `X' ⟶ V` is proper by the
case of algebraic spaces (Stacks 0CMD), applied along the reduction of `W` and fed by the claim
`AlgebraicGeometry.Stack.AlgebraicStacks.exists_dominatingExtension_lift_of_discreteExistenceAlong`
and Stacks 0ARH; `X' ⟶ 𝒳` is still surjective because its image is closed and contains the
dense image of `h`, so Stacks 0CQK makes `f` universally closed. -/
theorem universallyClosed_of_discreteExistenceAlong_of_chow
    (h0CQ8 : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY : IsAlgebraicSpace B S hS Y),
      Space.IsQuasiCompactSpace B S hS Y →
      Space.IsAbsolutelyQuasiSeparated B S hS (BigFppfSite.contains_terminal B) Y →
      ∀ (𝒳 : AlgebraicStacks.{u, w} B S hS) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY),
        IsSeparated B S hS f → IsFiniteType B S hS f →
        ∃ (X Xbar : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X),
          IsAlgebraicSpace B S hS Xbar ∧
          ∃ (a : algebraicSpaceStack.{u, w} B S hS X hX ⟶ 𝒳) (i : X ⟶ Xbar) (p : Xbar ⟶ Y),
          IsProper B S hS a ∧ IsSurjective B S hS a ∧ Space.IsOpenImmersion B S hS i ∧
            Space.IsProper B S hS p ∧
            Nonempty (a ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hX hY (i ≫ p)))
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
  obtain ⟨X, Xbar, hX, -, a, i, p, ha, hasurj, -, -, ⟨θ⟩⟩ := h0CQ8 (yoneda.obj V) hY
    (Space.isQuasiCompactSpace_yoneda_of_isAffine B S hS V hV)
    (Space.isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS _
      (Space.isAffineSpace_yoneda B S hS V hV)) 𝒳 (f ≫ e)
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
        representingMap_comp_comparison_eq B S hS e he
          (𝒜 := (schemeStack.{u, w} B S hS U).val) _
          (PresheafOfCategories.sliceElementsEquivalenceOver U)]
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
          ((Space.reducedClosedSubspace B S hS X hX _ hZ).ι ≫ i ≫ p) :=
        Space.isSeparated_comp B S hS _ _ (Space.isSeparated_of_isClosedImmersion B S hS _ hι)
          hgsep
      let q₀ : Space.ValuativeSquare (i ≫ p) :=
        { R := q.R, K := q.K, ring_mem := q.ring_mem, field_mem := q.field_mem, base := q.base
          generic := q.generic ≫ (Space.reducedClosedSubspace B S hS X hX _ hZ).ι
          special := q.special
          comm := by rw [Category.assoc]; exact q.comm }
      obtain ⟨E₀, ⟨ℓ₀⟩⟩ := exists_dominatingExtension_lift_of_discreteExistenceAlong B S hS f h
        hlift e he hX a ha (i ≫ p) hg W eW' q₀ hq
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

/-- **Stacks 0CQM, from the statement of Chow's lemma (Stacks 0CQ8).** Let `f : 𝒳 ⟶ 𝒴` and
`h : 𝒰 ⟶ 𝒳` be 1-morphisms of algebraic stacks over `S`, with `𝒴` locally Noetherian, `f` and `h`
of finite type, `f` separated and the image of `|h|` dense in `|𝒳|`. If every valuative square for
`f` over a discrete valuation ring whose generic point factors through `h` admits a dotted arrow
after an extension of the fraction field and passage to a dominating valuation ring, then `f` is
proper.

`h0CQ8` is the statement of Stacks 0CQ8; with it discharged this is Stacks 0CQM with no further
hypothesis. The reduction to
an affine Noetherian base and an affine source is
`AlgebraicGeometry.Stack.AlgebraicStacks.isProper_of_discreteExistenceAlong_of_affineCore`, and
the affine case is
`AlgebraicGeometry.Stack.AlgebraicStacks.universallyClosed_of_discreteExistenceAlong_of_chow`. -/
theorem isProper_of_discreteExistenceAlong_of_chow
    (h0CQ8 : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY : IsAlgebraicSpace B S hS Y),
      Space.IsQuasiCompactSpace B S hS Y →
      Space.IsAbsolutelyQuasiSeparated B S hS (BigFppfSite.contains_terminal B) Y →
      ∀ (𝒳 : AlgebraicStacks.{u, w} B S hS) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY),
        IsSeparated B S hS f → IsFiniteType B S hS f →
        ∃ (X Xbar : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X),
          IsAlgebraicSpace B S hS Xbar ∧
          ∃ (a : algebraicSpaceStack.{u, w} B S hS X hX ⟶ 𝒳) (i : X ⟶ Xbar) (p : Xbar ⟶ Y),
          IsProper B S hS a ∧ IsSurjective B S hS a ∧ Space.IsOpenImmersion B S hS i ∧
            Space.IsProper B S hS p ∧
            Nonempty (a ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hX hY (i ≫ p)))
    {𝒰 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (h : 𝒰 ⟶ 𝒳) (f : 𝒳 ⟶ 𝒴)
    (h𝒴 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴)
    (hf : IsFiniteType B S hS f) (hh : IsFiniteType B S hS h) (hsep : IsSeparated B S hS f)
    (hdense : @Dense _ (pointTopology B S hS 𝒳.val) (Set.range (pointsMap B S hS h)))
    (hlift : ValuativeCriterion.DiscreteExistenceAlong B S hS h f) :
    IsProper B S hS f :=
  isProper_of_discreteExistenceAlong_of_affineCore B S hS
    (universallyClosed_of_discreteExistenceAlong_of_chow B S hS h0CQ8) h f h𝒴 hf hh hsep hdense
    hlift

/-- **Stacks 0E95, from the statement of Chow's lemma (Stacks 0CQ8).** Let `f : 𝒳 ⟶ 𝒴` and
`h : 𝒰 ⟶ 𝒳` be 1-morphisms of algebraic stacks over `S`, with `𝒴` locally Noetherian, `f` locally
of finite type and quasi-separated, `h` of finite type, and the image of `|h|` dense in `|𝒳|`. If
for every valuative diagram for `f` over a discrete valuation ring whose generic point factors
through `h` the category of dotted arrows is empty or a setoid with exactly one isomorphism class,
then `f` is separated.

`h0CQ8` is the statement of Stacks 0CQ8. This is
`AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_of_denseRange_of_discreteUniquenessAlong`
fed with `AlgebraicGeometry.Stack.AlgebraicStacks.isProper_of_discreteExistenceAlong_of_chow`. -/
theorem isSeparated_of_discreteUniquenessAlong_of_chow
    (h0CQ8 : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY : IsAlgebraicSpace B S hS Y),
      Space.IsQuasiCompactSpace B S hS Y →
      Space.IsAbsolutelyQuasiSeparated B S hS (BigFppfSite.contains_terminal B) Y →
      ∀ (𝒳 : AlgebraicStacks.{u, w} B S hS) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY),
        IsSeparated B S hS f → IsFiniteType B S hS f →
        ∃ (X Xbar : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X),
          IsAlgebraicSpace B S hS Xbar ∧
          ∃ (a : algebraicSpaceStack.{u, w} B S hS X hX ⟶ 𝒳) (i : X ⟶ Xbar) (p : Xbar ⟶ Y),
          IsProper B S hS a ∧ IsSurjective B S hS a ∧ Space.IsOpenImmersion B S hS i ∧
            Space.IsProper B S hS p ∧
            Nonempty (a ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hX hY (i ≫ p)))
    {𝒰 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (h : 𝒰 ⟶ 𝒳) (f : 𝒳 ⟶ 𝒴)
    (h𝒴 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴)
    (hf : IsLocallyOfFiniteType B S hS f) (hqs : IsQuasiSeparated B S hS f)
    (hh : IsFiniteType B S hS h)
    (hdense : @Dense _ (pointTopology B S hS 𝒳.val) (Set.range (pointsMap B S hS h)))
    (huniq : ValuativeCriterion.DiscreteUniquenessAlong B S hS h f) :
    IsSeparated B S hS f :=
  isSeparated_of_denseRange_of_discreteUniquenessAlong B S hS
    (fun _ _ _ h' f' h𝒴' hf' hh' hsep' hdense' hlift' =>
      isProper_of_discreteExistenceAlong_of_chow B S hS h0CQ8 h' f' h𝒴' hf' hh' hsep' hdense'
        hlift')
    h f h𝒴 hf hqs hh hdense huniq

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
