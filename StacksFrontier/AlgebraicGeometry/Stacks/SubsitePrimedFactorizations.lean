module

public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteLocalFactorizations
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleSmoothObject
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.EtaleLocalLifts
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsitePushforwardAmbientClosure
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveFlatFppfLocalSections
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.CategoryTheory.FiberedCategory.SliceFunctorComparison

/-!
# Local factorizations through the primed 2-fibre product

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over a scheme `S` and let `y` be a smooth
(respectively flat) object of `𝒴` lying over a scheme `V`. The primed 2-fibre product
`(V ×_{y, 𝒴} 𝒳)'` is the full subcategory of `V ×_{y, 𝒴} 𝒳` cut out by smoothness (respectively
flatness) of the `𝒳`-component. Its inclusion into `V ×_{y, 𝒴} 𝒳` satisfies the
local-factorization condition of Stacks 07AK: every object of the 2-fibre product is covered, in
the topology it inherits from the base, by objects admitting a morphism to a primed object.

## Main definitions

* `AlgebraicGeometry.Stack.ambientSliceMorphism`: the 1-morphism `V ⟶ 𝒴` named by `y`, built
  from the chosen pullbacks of `𝒴`.
* `AlgebraicGeometry.Stack.ambientSquare`: the 2-fibre product `V ×_{y, 𝒴} 𝒳` as a
  2-commutative square of algebraic stacks, with apex that 2-fibre product on the nose.

## Main results

* `AlgebraicGeometry.Stack.ambientSliceMorphism_twoIso`: the 2-Yoneda comparison (Stacks 004B)
  between the 1-morphism built from the chosen pullbacks of `y` and the one
  `AlgebraicGeometry.Stack.objectMorphism` names.
* `AlgebraicGeometry.Stack.LisseEtale.isSmooth_ambientSquare_snd` and
  `AlgebraicGeometry.Stack.FlatFppf.isFlat_ambientSquare_snd`: the projection
  `pr : V ×_{y, 𝒴} 𝒳 ⟶ 𝒳` is smooth (respectively flat).
* `AlgebraicGeometry.Stack.LisseEtale.exists_primed_atlas` and
  `AlgebraicGeometry.Stack.FlatFppf.exists_primed_atlas`: Stacks 07AK (2) for the primed
  2-fibre product, a smooth surjective atlas by a scheme whose distinguished object is a primed
  object.
* `AlgebraicGeometry.Stack.LisseEtale.hasLocalFactorizations_primedInclusion` and
  `AlgebraicGeometry.Stack.FlatFppf.hasLocalFactorizations_primedInclusion`: the
  local-factorization condition, in the smooth and in the flat case.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
* [Stacks Project, Tag 075W](https://stacks.math.columbia.edu/tag/075W)
* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
  {Q : ObjectProperty 𝒴.val.val.obj} (y : Q.FullSubcategory)

/-- The 1-morphism `V ⟶ 𝒴` of algebraic stacks named by an object `y` of `𝒴` lying over the scheme
`V`: the 1-morphism `(k : W ⟶ V) ↦ k^* y` built from the chosen pullbacks of the ambient stack. -/
def ambientSliceMorphism :
    schemeStack.{u, w} B S hS (𝒴.val.val.p.obj y.obj) ⟶ 𝒴 :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor := (ambientChoiceOfPullbacks B S hS 𝒴).sliceFunctor ⟨y.obj, rfl⟩
      w := Functor.ChoiceOfPullbacks.sliceFunctor_comp _ _ })

/-- The 2-fibre product `V ×_{y, 𝒴} 𝒳` as a 2-commutative square of algebraic stacks, with apex
`CategoryTheory.SubsitePushforward.ambientTwoFibreProduct` and structure functor
`CategoryTheory.SubsitePushforward.ambientStructureFunctor`. -/
def ambientSquare : Bicategory.TwoCommSq (ambientSliceMorphism B S hS y) f :=
  twoFibreProductSquareAlgebraicStacks B S hS (ambientSliceMorphism B S hS y) f

/-- The apex of `AlgebraicGeometry.Stack.ambientSquare` is the 2-fibre product
`V ×_{y, 𝒴} 𝒳`. -/
lemma ambientSquare_pt_obj :
    (ambientSquare B S hS f y).pt.val.val.obj =
      SubsitePushforward.ambientTwoFibreProduct 𝒳.val.val.p 𝒴.val.val.p f.hom.hom.toFunctor
        (ambientChoiceOfPullbacks B S hS 𝒴) y :=
  rfl

/-- The structure functor of the apex of `AlgebraicGeometry.Stack.ambientSquare` is the structure
functor of the 2-fibre product. -/
lemma ambientSquare_pt_p :
    (ambientSquare B S hS f y).pt.val.val.p =
      SubsitePushforward.ambientStructureFunctor 𝒳.val.val.p 𝒴.val.val.p f.hom.hom.toFunctor
        (ambientChoiceOfPullbacks B S hS 𝒴) y :=
  rfl

/-- The second leg of `AlgebraicGeometry.Stack.ambientSquare` is the projection
`pr : V ×_{y, 𝒴} 𝒳 ⥤ 𝒳`. -/
lemma ambientSquare_snd :
    (ambientSquare B S hS f y).snd.hom.hom.toFunctor =
      SubsitePushforward.ambientProjection 𝒳.val.val.p 𝒴.val.val.p f.hom.hom.toFunctor
        (ambientChoiceOfPullbacks B S hS 𝒴) y :=
  rfl

/-- The swap of `AlgebraicGeometry.Stack.ambientSquare` is a 2-fibre product. -/
private def isTwoFibreProduct_ambientSquare_swap :
    Bicategory.IsTwoFibreProduct (ambientSquare B S hS f y).swap :=
  Bicategory.isTwoFibreProduct_swap
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS _ f)

/-- The 1-morphism `AlgebraicGeometry.Stack.ambientSliceMorphism` built from the chosen pullbacks
of `y` and the 1-morphism `AlgebraicGeometry.Stack.objectMorphism` named by `y` are 2-isomorphic
(Stacks 004B). -/
def ambientSliceMorphism_twoIso :
    (Bicategory.InducedBicategory.mkHom
        (objectMorphism B S hS 𝒴.val (Functor.Fiber.mk (a := y.obj) rfl)) :
      schemeStack.{u, w} B S hS (𝒴.val.val.p.obj y.obj) ⟶ 𝒴).hom ≅
      (ambientSliceMorphism B S hS y).hom := by
  set pY := 𝒴.val.val.p with hpY
  set V := pY.obj y.obj with hV
  set yF : pY.Fiber V := ⟨y.obj, rfl⟩ with hyF
  set c := ambientChoiceOfPullbacks B S hS 𝒴 with hc
  set E := Functor.twoYonedaEvaluation pY V with hE
  set L := Functor.TwoYoneda.liftBased pY 𝒴.val.isFiberedInGroupoids V yF with hL
  set Sl : BasedCategory.ofFunctor (Over.forget V) ⥤ᵇ BasedCategory.ofFunctor pY :=
    { toFunctor := c.sliceFunctor yF
      w := Functor.ChoiceOfPullbacks.sliceFunctor_comp _ _ } with hSl
  have eL : E.obj L ≅ yF :=
    fiberIsoOfHomLift B S hS pY 𝒴.val.isFiberedInGroupoids V
      (a := E.obj L) (b := yF)
      (Functor.TwoYoneda.chosenLift pY 𝒴.val.isFiberedInGroupoids V yF (Over.mk (𝟙 V))).φ
      (Functor.TwoYoneda.chosenLift pY 𝒴.val.isFiberedInGroupoids V yF
        (Over.mk (𝟙 V))).isStronglyCartesian.toIsHomLift
  have eS : E.obj Sl ≅ yF :=
    fiberIsoOfHomLift B S hS pY 𝒴.val.isFiberedInGroupoids V
      (a := E.obj Sl) (b := yF) (c.map (𝟙 V) yF)
      (c.isStronglyCartesian (𝟙 V) yF).toIsHomLift
  letI : E.IsEquivalence :=
    Functor.twoYonedaEvaluation_isEquivalence pY 𝒴.val.isFiberedInGroupoids V
  have hff : E.FullyFaithful := E.asEquivalence.fullyFaithfulFunctor
  have e := hff.preimageIso (eL ≪≫ eS.symm)
  exact
    { hom := Bicategory.InducedBicategory.Hom₂.mk e.hom
      inv := Bicategory.InducedBicategory.Hom₂.mk e.inv
      hom_inv_id := by ext; exact e.hom_inv_id
      inv_hom_id := by ext; exact e.inv_hom_id }

/-- Let `𝒜` be an algebraic stack, let `P` be a property of its objects holding at the object named
by a 1-morphism `a : U₀ ⟶ 𝒜` out of the category of a scheme, and suppose every object of `𝒜` lifts
along `a` after a `τ`-covering of the scheme it lies over. Then every object of `𝒜` is covered, in
the topology inherited from `τ`, by objects admitting a morphism to an object with `P`. -/
private theorem hasLocalFactorizations_of_atlas
    {𝒜 : Stack.AlgebraicStacks.{u, w} B S hS} (P : ObjectProperty 𝒜.val.val.obj)
    {U₀ : BigFppfOver B S hS} (a : schemeStack.{u, w} B S hS U₀ ⟶ 𝒜)
    (hP : P ((CatFiberedInGroupoids.homFunctor a.hom).obj (Over.mk (𝟙 U₀)))) (τ : SiteKind)
    (hcov : ∀ (U : BigFppfOver B S hS) (z : 𝒜.val.val.p.Fiber U),
      ∃ R ∈ BigFppfOver.baseOverTopology B S hS τ U,
        ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
          ∃ (x : Over U₀) (α : (CatFiberedInGroupoids.homFunctor a.hom).obj x ⟶ z.1),
            𝒜.val.val.p.IsHomLift k α) :
    Stacks.Sites.HasLocalFactorizations
      (BigFppfOver.associatedTopology B S hS 𝒜.val.val.p τ) P.ι := by
  let : 𝒜.val.val.p.IsFibered := 𝒜.val.isFiberedInGroupoids.isFibered
  intro T
  obtain ⟨R, hR, hlift⟩ := hcov (𝒜.val.val.p.obj T) ⟨T, rfl⟩
  refine GrothendieckTopology.superset_covering _ ?_
    (Functor.functorPullback_mem_inheritedTopology 𝒜.val.val.p _ T hR)
  intro T' h hh
  obtain ⟨x, α, hα⟩ := hlift hh
  have : 𝒜.val.val.p.IsStronglyCartesian (𝒜.val.val.p.map h) α :=
    𝒜.val.isFiberedInGroupoids.isStronglyCartesian_homLift _ α
  exact ⟨⟨_, hP⟩, ⟨Functor.IsStronglyCartesian.map 𝒜.val.val.p (𝒜.val.val.p.map h) α
    (Category.id_comp _).symm h ≫
      (CatFiberedInGroupoids.homFunctor a.hom).map (Over.homMk x.hom (by simp))⟩⟩

namespace LisseEtale

/-- The 1-morphism `V ⟶ 𝒴` built from the chosen pullbacks of a smooth object `y` of `𝒴` is a
smooth 1-morphism of algebraic stacks. -/
theorem isSmooth_ambientSliceMorphism (y : LisseEtale.{u, w} B S hS 𝒴) :
    AlgebraicStacks.IsSmooth B S hS (ambientSliceMorphism B S hS y) :=
  hasPropertyOnSomeSmoothDiagram_of_twoIso B S hS _
    (ambientSliceMorphism_twoIso B S hS y) y.property

/-- At a smooth object `y` of `𝒴`, the projection `pr : V ×_{y, 𝒴} 𝒳 ⟶ 𝒳` is smooth, as the base
change along `f` of the smooth 1-morphism `V ⟶ 𝒴` named by `y` (Stacks 075W). -/
theorem isSmooth_ambientSquare_snd (y : LisseEtale.{u, w} B S hS 𝒴) :
    AlgebraicStacks.IsSmooth B S hS (ambientSquare B S hS f y).snd :=
  AlgebraicStacks.isSmooth_baseChange B S hS (ambientSliceMorphism B S hS y) f
    (ambientSquare B S hS f y).swap
    (isTwoFibreProduct_ambientSquare_swap B S hS f y)
    (isSmooth_ambientSliceMorphism B S hS y)

/-- Stacks 07AK (2) for the primed 2-fibre product, the smooth case: the 2-fibre product
`V ×_{y, 𝒴} 𝒳` at a smooth object `y` of `𝒴` has a smooth surjective atlas by a scheme whose
distinguished object is a smooth object of `𝒳`, that is, lies in the primed subcategory. -/
theorem exists_primed_atlas (y : LisseEtale.{u, w} B S hS 𝒴) :
    ∃ (U₀ : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS U₀ ⟶
      (ambientSquare B S hS f y).pt),
      AlgebraicStacks.IsSmooth B S hS a ∧ IsSurjective B S hS a ∧
        primedObjectProperty B S hS f y
          ((CatFiberedInGroupoids.homFunctor a.hom).obj (Over.mk (𝟙 U₀))) := by
  obtain ⟨U₀, a, hasm, hasurj⟩ :=
    exists_smooth_surjective_schemeStack.{u, w} B S hS (ambientSquare B S hS f y).pt
  exact ⟨U₀, a, hasm, hasurj, smoothObject_map.{u, w} B S hS (ambientSquare B S hS f y).snd
    (isSmooth_ambientSquare_snd B S hS f y)
    ⟨_, smoothObject_map.{u, w} B S hS a hasm ⟨_, smoothObject_schemeStack_id B S hS U₀⟩⟩⟩

/-- The local-factorization condition of Stacks 07AK for the primed 2-fibre product, the smooth
case: every object of `V ×_{y, 𝒴} 𝒳` is covered, in the étale topology it inherits from the base,
by objects admitting a morphism to an object whose `𝒳`-component is smooth. -/
theorem hasLocalFactorizations_primedInclusion (y : LisseEtale.{u, w} B S hS 𝒴) :
    Stacks.Sites.HasLocalFactorizations
      (ambientTwoFibreProductTopology B S hS f y .etale)
      (primedObjectProperty B S hS f y).ι := by
  obtain ⟨U₀, a, hasm, hasurj, hP⟩ := exists_primed_atlas B S hS f y
  exact hasLocalFactorizations_of_atlas B S hS _ a hP .etale
    (exists_etaleCovering_fibre_lift B S hS a hasurj hasm)

end LisseEtale

namespace FlatFppf

/-- The 1-morphism `V ⟶ 𝒴` built from the chosen pullbacks of a flat object `y` of `𝒴` is a flat
1-morphism of algebraic stacks. -/
theorem isFlat_ambientSliceMorphism (y : FlatFppf B S hS 𝒴) :
    AlgebraicStacks.IsFlat B S hS (ambientSliceMorphism B S hS y) :=
  hasPropertyOnSomeSmoothDiagram_of_twoIso B S hS _
    (ambientSliceMorphism_twoIso B S hS y) y.property

/-- At a flat object `y` of `𝒴`, the projection `pr : V ×_{y, 𝒴} 𝒳 ⟶ 𝒳` is flat, as the base change
along `f` of the flat 1-morphism `V ⟶ 𝒴` named by `y` (Stacks 06PY). -/
theorem isFlat_ambientSquare_snd (y : FlatFppf B S hS 𝒴) :
    AlgebraicStacks.IsFlat B S hS (ambientSquare B S hS f y).snd :=
  AlgebraicStacks.isFlat_baseChange B S hS (ambientSliceMorphism B S hS y) f
    (ambientSquare B S hS f y).swap
    (isTwoFibreProduct_ambientSquare_swap B S hS f y)
    (isFlat_ambientSliceMorphism B S hS y)

/-- Stacks 07AK (2) for the primed 2-fibre product, the flat case: the 2-fibre product
`V ×_{y, 𝒴} 𝒳` at a flat object `y` of `𝒴` has a smooth surjective atlas by a scheme whose
distinguished object is a flat object of `𝒳`, that is, lies in the primed subcategory. -/
theorem exists_primed_atlas (y : FlatFppf B S hS 𝒴) :
    ∃ (U₀ : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS U₀ ⟶
      (ambientSquare B S hS f y).pt),
      AlgebraicStacks.IsSmooth B S hS a ∧ IsSurjective B S hS a ∧
        primedObjectProperty B S hS f y
          ((CatFiberedInGroupoids.homFunctor a.hom).obj (Over.mk (𝟙 U₀))) := by
  obtain ⟨U₀, a, hasm, hasurj⟩ :=
    exists_smooth_surjective_schemeStack.{u, w} B S hS (ambientSquare B S hS f y).pt
  exact ⟨U₀, a, hasm, hasurj, flatObject_map B S hS (ambientSquare B S hS f y).snd
    (isFlat_ambientSquare_snd B S hS f y)
    ⟨_, flatObject_map B S hS a (AlgebraicStacks.isFlat_of_isSmooth B S hS a hasm)
      ⟨_, AlgebraicStacks.isFlat_of_isSmooth B S hS _
        (smoothObject_schemeStack_id.{u, w} B S hS U₀)⟩⟩⟩

/-- The local-factorization condition of Stacks 07AK for the primed 2-fibre product, the flat case:
every object of `V ×_{y, 𝒴} 𝒳` is covered, in the fppf topology it inherits from the base, by
objects admitting a morphism to an object whose `𝒳`-component is flat. -/
theorem hasLocalFactorizations_primedInclusion (y : FlatFppf B S hS 𝒴) :
    Stacks.Sites.HasLocalFactorizations
      (ambientTwoFibreProductTopology B S hS f y .fppf)
      (primedObjectProperty B S hS f y).ι := by
  obtain ⟨U₀, a, hasm, hasurj, hP⟩ := exists_primed_atlas B S hS f y
  exact hasLocalFactorizations_of_atlas B S hS _ a hP .fppf
    (exists_fppfCovering_fibre_lift B S hS a hasurj
      (AlgebraicStacks.isFlat_of_isSmooth B S hS a hasm)
      (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS a hasm))

end FlatFppf

end AlgebraicGeometry.Stack

end
