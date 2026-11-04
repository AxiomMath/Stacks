module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackSmallModel
public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBigSiteAlgebraicStack
public import StacksFrontier.CategoryTheory.Bicategory.PseudofunctorOfUniversalArrows
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackStackUniversalArrow

/-!
# The 2-functor of an enlargement of the big fppf site on algebraic stacks (Stacks 04X3)

Let `B` be a big fppf site contained in a larger one `B'`, let `S` be a scheme of `B` and write `f`
for the morphism of sites that the localized inclusion `u` determines. Stacks 04X3 says that the
rule `𝒳 ↦ f⁻¹𝒳` of Stacks 04X2 is a functor of 2-categories from the algebraic stacks over `S`
for `B` to those for `B'`, which induces equivalences of morphism categories.

## Main definitions

* `AlgebraicGeometry.Stack.ChangeOfBigSite.inclusionPseudofunctor`: an algebraic stack over the
  smaller site, read as a category over the larger one through `u`.
* `AlgebraicGeometry.Stack.ChangeOfBigSite.forgetPseudofunctor`: an algebraic stack over the larger
  site, read as a category over it.
* `AlgebraicGeometry.Stack.ChangeOfBigSite.pullbackObj`: the object `f⁻¹𝒳` of the 2-category of
  algebraic stacks over `S` for `B'`, the small model of the inverse image.
* `AlgebraicGeometry.Stack.ChangeOfBigSite.pullbackUnit`: the canonical 1-morphism `𝒳 ⟶ f⁻¹𝒳`
  over `u`.
* `AlgebraicGeometry.Stack.ChangeOfBigSite.pullbackPseudofunctor`: **the functor of 2-categories
  `Algebraic-Stacks/S ⟶ Algebraic-Stacks'/S` of Stacks 04X3**.

## Main results

* `AlgebraicGeometry.Stack.ChangeOfBigSite.isEquivalence_homFunctor_universalArrows`: the arrows
  `𝒳 ⥤ f⁻¹𝒳` are universal among functors over `u` into algebraic stacks of the form `f⁻¹𝒳'`
  (Stacks 04W9 and Stacks 04WI).
* `AlgebraicGeometry.Stack.ChangeOfBigSite.isEquivalence_mapFunctor_comp_postcomp_unit`:
  composing 1-morphisms over the smaller site with `𝒴 ⥤ f⁻¹𝒴` is an equivalence
  (Stacks 04WS (1)).
* `AlgebraicGeometry.Stack.ChangeOfBigSite.isEquivalence_mapFunctor_pullbackPseudofunctor`:
  **Stacks 04X3, the equivalences of morphism categories**
  `Mor(𝒳, 𝒴) ⥤ Mor(f⁻¹𝒳, f⁻¹𝒴)`.

## Implementation notes

The 2-functor is built from the universal arrows `𝒳 ⥤ f⁻¹𝒳` by
`CategoryTheory.Pseudofunctor.UniversalArrows.pseudofunctor`: the image of `g : 𝒳 ⟶ 𝒴` is the
1-morphism `f⁻¹𝒳 ⟶ f⁻¹𝒴` through which `𝒳 ⟶ 𝒴 ⥤ f⁻¹𝒴` factors, as in the source, where it is
the functoriality of the stackification. The object `f⁻¹𝒳` is the small model
`AlgebraicGeometry.Stack.AlgebraicStacks.smallModel` of `AlgebraicGeometry.Stack.pullbackStack`,
whose morphisms, being those of a stackification, live a universe above those of the objects of
the 2-category of Stacks 03YP; `pullbackObjEquivalenceOver` compares the two.

That `f⁻¹𝒳` is an algebraic stack, so an object of the target 2-category, is Stacks 04X2
part (3) (`AlgebraicGeometry.Stack.isAlgebraicStack_pullbackStack`).

## References

* [Stacks Project, Tag 04WS](https://stacks.math.columbia.edu/tag/04WS)
* [Stacks Project, Tag 04X2](https://stacks.math.columbia.edu/tag/04X2)
* [Stacks Project, Tag 04X3](https://stacks.math.columbia.edu/tag/04X3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Bicategory

namespace AlgebraicGeometry.Stack.ChangeOfBigSite

universe u w

variable {B B' : BigFppfSite.{u}} (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S)

/-- The localized inclusion `u` of Stacks 04X2, with its source and target written as the
localized big fppf sites rather than as the `CategoryTheory.Over` categories they unfold to. -/
abbrev inclusionFppfOver : BigFppfOver B S hS ⥤ BigFppfOver B' S (largerContains h hS) :=
  inclusionOver h S hS

/-- The localized inclusion `inclusionFppfOver` preserves finite limits. -/
instance preservesFiniteLimits_inclusionFppfOver :
    PreservesFiniteLimits (inclusionFppfOver h S hS) :=
  inclusionOver_preservesFiniteLimits (τ := .fppf) B B' h S hS

/-- The localized inclusion `inclusionFppfOver` is faithful. -/
instance faithful_inclusionFppfOver : (inclusionFppfOver h S hS).Faithful :=
  inclusionOver_faithful (τ := .fppf) h S hS

/-- The localized inclusion `inclusionFppfOver` is full. -/
instance full_inclusionFppfOver : (inclusionFppfOver h S hS).Full :=
  inclusionOver_full (τ := .fppf) h S hS

/-- The localized inclusion `inclusionFppfOver` is continuous for the fppf topologies. -/
instance isContinuous_inclusionFppfOver :
    (inclusionFppfOver h S hS).IsContinuous (BigFppfOver.topology B S hS)
      (BigFppfOver.topology B' S (largerContains h hS)) :=
  inclusionOver_isContinuous (τ := .fppf) B B' h S hS

/-- The localized inclusion `inclusionFppfOver` is cocontinuous for the fppf topologies. -/
instance isCocontinuous_inclusionFppfOver :
    (inclusionFppfOver h S hS).IsCocontinuous (BigFppfOver.topology B S hS)
      (BigFppfOver.topology B' S (largerContains h hS)) :=
  inclusionOver_isCocontinuous (τ := .fppf) B B' h S hS

universe v t in
/-- A category over the smaller localized big fppf site, read as a category over the larger one
through the localized inclusion `u`. -/
abbrev inclusionBased (𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS)) :
    BasedCategory.{v, t} (BigFppfOver B' S (largerContains h hS)) :=
  BasedCategory.ofFunctor (𝒳.p ⋙ inclusionFppfOver h S hS)

/-- A 1-morphism of algebraic stacks over the smaller site, read as a functor over the larger
site. -/
def inclusionMap {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    inclusionBased h S hS 𝒳.val.val ⥤ᵇ inclusionBased h S hS 𝒴.val.val where
  toFunctor := f.hom.hom.toFunctor
  w := congrArg (· ⋙ inclusionFppfOver h S hS) f.hom.hom.w

/-- A 2-morphism of algebraic stacks over the smaller site, read over the larger site. -/
def inclusionMap₂ {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {f g : 𝒳 ⟶ 𝒴} (η : f ⟶ g) :
    inclusionMap h S hS f ⟶ inclusionMap h S hS g where
  toNatTrans := η.hom.hom.toNatTrans
  isHomLift' a :=
    Functor.isHomLift_id_comp_functor (inclusionFppfOver h S hS) (η.hom.hom.isHomLift' a)

/-- **Algebraic stacks over the smaller site, read as categories over the larger one** through
the localized inclusion, as a pseudofunctor into the bicategory of categories over the larger
site. It is strict: its comparison 2-isomorphisms are identities. -/
def inclusionPseudofunctor :
    AlgebraicStacks.{u, w} B S hS ⥤ᵖ
      BasedCategory.{u, u + 1} (BigFppfOver B' S (largerContains h hS)) :=
  (StrictPseudofunctor.mk'' {
    obj 𝒳 := inclusionBased h S hS 𝒳.val.val
    map := inclusionMap h S hS
    map₂ := inclusionMap₂ h S hS
    map₂_id _ := rfl
    map₂_comp _ _ := rfl
    map₂_whisker_left := by
      intros
      apply BasedNatTrans.ext
      ext
      change _ = 𝟙 _ ≫ _ ≫ 𝟙 _
      exact (Category.comp_id _).symm.trans (Category.id_comp _).symm
    map₂_whisker_right := by
      intros
      apply BasedNatTrans.ext
      ext
      change _ = 𝟙 _ ≫ _ ≫ 𝟙 _
      exact (Category.comp_id _).symm.trans (Category.id_comp _).symm }).toPseudofunctor

/-- **Algebraic stacks over the larger site, read as categories over it**: the composite of the
two forgetful pseudofunctors of the induced bicategories. -/
abbrev forgetPseudofunctor :
    AlgebraicStacks.{u, w} B' S (largerContains h hS) ⥤ᵖ
      BasedCategory.{u, u + 1} (BigFppfOver B' S (largerContains h hS)) :=
  (InducedBicategory.forget).toPseudofunctor.comp (InducedBicategory.forget).toPseudofunctor

/-- The functor of hom-categories `(𝒳 ⟶ 𝒴) ⥤ (𝒳.val.val ⥤ᵇ 𝒴.val.val)` of the 2-category of
algebraic stacks into that of categories over the site: the identity on the underlying based
functors and natural transformations, hence an equivalence. -/
instance isEquivalence_forget_mapFunctor {B₀ : BigFppfSite.{u}} {S₀ : Scheme.{u}}
    {hS₀ : B₀.Contains S₀} (𝒳 𝒴 : AlgebraicStacks.{u, w} B₀ S₀ hS₀) :
    (((InducedBicategory.forget).toPseudofunctor.comp
      (InducedBicategory.forget).toPseudofunctor :
        AlgebraicStacks.{u, w} B₀ S₀ hS₀ ⥤ᵖ
          BasedCategory.{u, u + 1} (BigFppfOver B₀ S₀ hS₀)).mapFunctor
          𝒳 𝒴).IsEquivalence where
  faithful := ⟨fun {_ _} _ _ hθ => InducedBicategory.Hom₂.ext (InducedBicategory.Hom₂.ext hθ)⟩
  full := ⟨fun {_ _} θ => ⟨⟨⟨θ⟩⟩, rfl⟩⟩
  essSurj := ⟨fun F => ⟨InducedBicategory.mkHom (InducedBicategory.mkHom F), ⟨Iso.refl _⟩⟩⟩

section Pullback

/-- **`f⁻¹𝒳` as an object of the 2-category of algebraic stacks over `S` for `B'`**: the small
model of the inverse image `AlgebraicGeometry.Stack.pullbackStack`, which is an algebraic stack by
Stacks 04X2 part (3). -/
noncomputable def pullbackObj (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    AlgebraicStacks.{u, w} B' S (largerContains h hS) :=
  letI := 𝒳.val.isFiberedInGroupoids.isFibered
  AlgebraicStacks.smallModel B' S (largerContains h hS) (pullbackStack h S hS 𝒳.val.val)
    (isAlgebraicStack_pullbackStack h S hS 𝒳.val 𝒳.property)

/-- `f⁻¹𝒳` is equivalent over the larger site to the inverse image `pullbackStack`. -/
noncomputable def pullbackObjEquivalenceOver (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    letI := 𝒳.val.isFiberedInGroupoids.isFibered
    StacksRepresentableCFG.EquivalenceOver (pullbackStack h S hS 𝒳.val.val).p
      (pullbackObj h S hS 𝒳).val.val.p :=
  letI := 𝒳.val.isFiberedInGroupoids.isFibered
  AlgebraicStacks.smallModelEquivalenceOver B' S (largerContains h hS) _ _

/-- **The canonical functor `𝒳 ⥤ f⁻¹𝒳` over the localized inclusion**: the unit `ι` of
Stacks 04WG followed by the stackification of Stacks 02ZN, into the small model. -/
noncomputable def pullbackUnit (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    inclusionBased h S hS 𝒳.val.val ⥤ᵇ (pullbackObj h S hS 𝒳).val.val :=
  letI := 𝒳.val.isFiberedInGroupoids.isFibered
  haveI : HasFiniteLimits B.Schemes := hasFiniteLimits_siteCategory (τ := .fppf) B
  haveI : HasFiniteLimits (BigFppfOver B S hS) := inferInstanceAs (HasFiniteLimits (Over _))
  haveI : LocallySmall.{u} (pullbackStack h S hS 𝒳.val.val).obj :=
    locallySmall_of_isAlgebraicStack B' S (largerContains h hS)
      (isAlgebraicStack_pullbackStack h S hS 𝒳.val 𝒳.property)
  BasedFunctor.comp
    (Comma.pullbackStackUnitBased 𝒳.val.val.p (inclusionFppfOver h S hS)
      (Functor.isFibredOneMorphism_toStageThree (pullbackStackProj h S hS 𝒳.val.val)
        (BigFppfOver.topology B' S (largerContains h hS))))
    (⟨ShrinkHoms.functor.{u} (pullbackStack h S hS 𝒳.val.val).obj,
      BasedCategory.shrinkHoms_functor_comp (pullbackStack h S hS 𝒳.val.val)⟩ :
      pullbackStack h S hS 𝒳.val.val ⥤ᵇ (pullbackStack h S hS 𝒳.val.val).shrinkHoms)

/-- **The family of arrows `𝒳 ⥤ f⁻¹𝒳` over the localized inclusion**, whose universality makes
`𝒳 ↦ f⁻¹𝒳` a pseudofunctor. -/
noncomputable def universalArrows :
    Pseudofunctor.UniversalArrows (inclusionPseudofunctor.{u, w} h S hS)
      (forgetPseudofunctor.{u, w} h S hS) where
  obj := pullbackObj h S hS
  unit := pullbackUnit h S hS

/-- **The arrows `𝒳 ⥤ f⁻¹𝒳` are universal.** For algebraic stacks `𝒳`, `𝒳'` over the smaller
site, composing with `𝒳 ⥤ f⁻¹𝒳` is an equivalence from the 1-morphisms `f⁻¹𝒳 ⟶ f⁻¹𝒳'` over the
larger site onto the functors `𝒳 ⥤ f⁻¹𝒳'` over the localized inclusion. This is Stacks 04W9 and
Stacks 04WI, through `CategoryTheory.Comma.isEquivalence_precompFunctor_pullbackStackUnitBased`,
transported to the small models. -/
instance isEquivalence_homFunctor_universalArrows (𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS) :
    ((universalArrows h S hS).homFunctor 𝒳
      ((universalArrows h S hS).obj 𝒳')).IsEquivalence := by
  let := 𝒳.val.isFiberedInGroupoids.isFibered
  let := 𝒳'.val.isFiberedInGroupoids.isFibered
  have : HasFiniteLimits B.Schemes := hasFiniteLimits_siteCategory (τ := .fppf) B
  have : HasFiniteLimits (BigFppfOver B S hS) := inferInstanceAs (HasFiniteLimits (Over _))
  have halg' := isAlgebraicStack_pullbackStack h S hS 𝒳'.val 𝒳'.property
  have : LocallySmall.{u} (BasedCategory.ofFunctor
      ((pullbackStackProj h S hS 𝒳.val.val).stageThreeProj
        (BigFppfOver.topology B' S (largerContains h hS)))).obj :=
    locallySmall_of_isAlgebraicStack B' S (largerContains h hS)
      (isAlgebraicStack_pullbackStack h S hS 𝒳.val 𝒳.property)
  have : LocallySmall.{u} (BasedCategory.ofFunctor
      ((pullbackStackProj h S hS 𝒳'.val.val).stageThreeProj
        (BigFppfOver.topology B' S (largerContains h hS)))).obj :=
    locallySmall_of_isAlgebraicStack B' S (largerContains h hS) halg'
  have : LocallySmall.{u} (BasedCategory.ofFunctor (pullbackStack h S hS 𝒳'.val.val).p).obj :=
    locallySmall_of_isAlgebraicStack B' S (largerContains h hS) halg'
  have hst := Functor.isStackification_toStageThree.{u, u + 1, u + 1, u}
    (pullbackStackProj h S hS 𝒳.val.val) (BigFppfOver.topology B' S (largerContains h hS))
  have h₁ := Comma.isEquivalence_precompFunctor_comp_shrinkHoms.{u} 𝒳.val.val.p
    (inclusionFppfOver h S hS)
    (Functor.isFibredOneMorphism_toStageThree (pullbackStackProj h S hS 𝒳.val.val)
      (BigFppfOver.topology B' S (largerContains h hS))) hst.2.1 hst.2.2
    (isStack_pullbackStack h S hS 𝒳'.val.val) halg'.1
  exact @Functor.isEquivalence_trans _ _ _ _ _ _ _ _
    (isEquivalence_forget_mapFunctor (pullbackObj h S hS 𝒳) (pullbackObj h S hS 𝒳')) h₁

/-- **Composing with the arrows `𝒴 ⥤ f⁻¹𝒴` is an equivalence on 1-morphisms of the smaller
site.** For algebraic stacks `𝒳`, `𝒴` over the smaller site, sending a 1-morphism `𝒳 ⟶ 𝒴` to the
composite `𝒳 ⟶ 𝒴 ⥤ f⁻¹𝒴`, a functor over the localized inclusion, is an equivalence. This is
Stacks 04WS (1), through
`CategoryTheory.Comma.isEquivalence_compPullbackStackUnitBased_shrinkHoms`. -/
instance isEquivalence_mapFunctor_comp_postcomp_unit (𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS) :
    ((inclusionPseudofunctor h S hS).mapFunctor 𝒳 𝒴 ⋙
      postcomp ((inclusionPseudofunctor h S hS).obj 𝒳)
        ((universalArrows h S hS).unit 𝒴)).IsEquivalence := by
  let := 𝒳.val.isFiberedInGroupoids.isFibered
  let := 𝒴.val.isFiberedInGroupoids.isFibered
  have : HasFiniteLimits B.Schemes := hasFiniteLimits_siteCategory (τ := .fppf) B
  have : HasFiniteLimits (BigFppfOver B S hS) := inferInstanceAs (HasFiniteLimits (Over _))
  have halg := isAlgebraicStack_pullbackStack h S hS 𝒴.val 𝒴.property
  have : LocallySmall.{u} (BasedCategory.ofFunctor
      ((pullbackStackProj h S hS 𝒴.val.val).stageThreeProj
        (BigFppfOver.topology B' S (largerContains h hS)))).obj :=
    locallySmall_of_isAlgebraicStack B' S (largerContains h hS) halg
  have hst := Functor.isStackification_toStageThree.{u, u + 1, u + 1, u}
    (pullbackStackProj h S hS 𝒴.val.val) (BigFppfOver.topology B' S (largerContains h hS))
  have h₂ := Comma.isEquivalence_compPullbackStackUnitBased_shrinkHoms.{u} 𝒳.val.val.p
    (inclusionFppfOver h S hS)
    (Functor.isFibredOneMorphism_toStageThree (pullbackStackProj h S hS 𝒴.val.val)
      (BigFppfOver.topology B' S (largerContains h hS)))
    (J := BigFppfOver.topology B S hS) 𝒴.property.2.1.1
    (isStack_pullbackStack h S hS 𝒴.val.val) 𝒴.val.isFiberedInGroupoids halg.1 hst.2.1 hst.2.2
  refine @Functor.isEquivalence_of_iso _ _ _ _ _ _ ?_
    (@Functor.isEquivalence_trans _ _ _ _ _ _ _ _ (isEquivalence_forget_mapFunctor 𝒳 𝒴) h₂)
  exact NatIso.ofComponents (fun _ => Iso.refl _) fun _ => by
    apply BasedNatTrans.ext
    ext
    exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- **The 2-functor `𝒳 ↦ f⁻¹𝒳`** from the algebraic stacks over `S` for the smaller big fppf site
to those for the larger one. Its value at `𝒳` is `pullbackObj`, equivalent over the larger site to
the inverse image `AlgebraicGeometry.Stack.pullbackStack` of Stacks 04X2
(`pullbackObjEquivalenceOver`), and its value at a 1-morphism `g : 𝒳 ⟶ 𝒴` is the 1-morphism
`f⁻¹𝒳 ⟶ f⁻¹𝒴` through which `𝒳 ⟶ 𝒴 ⥤ f⁻¹𝒴` factors by the universal property of `𝒳 ⥤ f⁻¹𝒳`. -/
@[stacks 04X3 "the functor of 2-categories"]
noncomputable def pullbackPseudofunctor :
    AlgebraicStacks.{u, w} B S hS ⥤ᵖ AlgebraicStacks.{u, w} B' S (largerContains h hS) :=
  (universalArrows h S hS).pseudofunctor

/-- The value of `pullbackPseudofunctor` at `𝒳` is `pullbackObj`. -/
@[simp]
lemma pullbackPseudofunctor_obj (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    (pullbackPseudofunctor h S hS).obj 𝒳 = pullbackObj h S hS 𝒳 := rfl

/-- **The 2-functor `𝒳 ↦ f⁻¹𝒳` induces equivalences of morphism categories**
`Mor(𝒳, 𝒴) ≌ Mor(f⁻¹𝒳, f⁻¹𝒴)`. -/
@[stacks 04X3 "the equivalences of morphism categories"]
theorem isEquivalence_mapFunctor_pullbackPseudofunctor (𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS) :
    ((pullbackPseudofunctor h S hS).mapFunctor 𝒳 𝒴).IsEquivalence :=
  (universalArrows h S hS).isEquivalence_mapFunctor 𝒳 𝒴

end Pullback

end AlgebraicGeometry.Stack.ChangeOfBigSite

end
