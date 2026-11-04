module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackDiagonalUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.SmoothQuotientStackModel

/-!
# A small model of the quotient stack of a smooth groupoid

The quotient stack `[U/R]` of a groupoid in algebraic spaces,
`AlgebraicGeometry.Stack.quotientStack`, is a stackification, and its morphisms live in
`Type (u + 1)`. The 2-category `AlgebraicGeometry.Stack.AlgebraicStacks` of Stacks 03YP asks for
morphisms in `Type u`, so `[U/R]` is not literally one of its objects. Its morphism types are,
however, essentially small, and this file replaces it by an equivalent category over the site
with the same objects and morphisms in `Type u`.

## Main definitions

* `AlgebraicGeometry.Stack.smallQuotientStackBased`: the quotient stack with its hom types
  replaced by `u`-small models (`CategoryTheory.ShrinkHoms`), as a category over the site.
* `AlgebraicGeometry.Stack.smallQuotientStack`: for a smooth groupoid over the base, that
  category as an object of `AlgebraicGeometry.Stack.AlgebraicStacks`.
* `AlgebraicGeometry.Stack.smallQuotientStackPresentation`: its presentation, in the sense of
  Stacks 04TI, by the groupoid it was built from.

## Main results

* `AlgebraicGeometry.Stack.small_hom_quotientStack`: every hom type of `[U/R]` is `u`-small.
* `AlgebraicGeometry.Stack.isAlgebraicStack_of_equivalence'`: Stacks 03YQ for algebraic stacks
  across an equivalence over the site whose two sides have unrelated universes.

## Implementation notes

Smallness of a hom type `a ⟶ b` of `[U/R]` is read off Stacks 04TB
(`AlgebraicGeometry.Stack.lemma04TB`). A morphism `a ⟶ b` is a morphism `f` of the base together
with a vertical morphism from `a` to the chosen pullback of `b` along `f`; the base morphisms form
a type in `Type u`. A vertical morphism `x ⟶ y` of the fibre over `T` is, after composing with the
canonical vertical isomorphisms from the chosen pullbacks along `𝟙 T`, a section of the
isomorphism presheaf `Isom(x, y)` over the final object of the slice (the fibres are groupoids, so
every vertical morphism is an isomorphism), and these sections are in bijection with the points
of an algebraic space by Stacks 04TB, a type in `Type u`.

The algebraicity transport `AlgebraicGeometry.Stack.isAlgebraicStack_of_equivalence` is stated
for two categories over the site with the same universes, while `[U/R]` and its small model
differ in the morphism universe. Every ingredient of its proof is universe-heterogeneous, so the
same argument is repeated here at that generality.
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u w v t v' t'

section Transport

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **One direction of Stacks 03YQ for algebraic stacks, with unrelated universes.** A category
over the big fppf site of `S` equivalent over that site to an algebraic stack is an algebraic
stack; the two categories may live in different object and morphism universes.

This is `AlgebraicGeometry.Stack.isAlgebraicStack_of_equivalence`, whose statement asks for a
common pair of universes, with the same proof. -/
theorem isAlgebraicStack_of_equivalence'
    {𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS)}
    {𝒴 : BasedCategory.{v', t'} (BigFppfOver B S hS)}
    (e : BasedCategory.Equivalence 𝒳 𝒴)
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳) :
    IsAlgebraicStack.{u, w} B S hS 𝒴 := by
  obtain ⟨hfib, hst, hdiag, U, f, -, hprops⟩ := h𝒳
  have hfib' : 𝒴.p.IsFiberedInGroupoids :=
    (BasedCategory.isFiberedInGroupoids_iff_of_equivalence e).1 hfib
  have hst' : 𝒴.p.IsStack (BigFppfOver.topology B S hS) :=
    (BasedCategory.isStack_iff_of_equivalence e (BigFppfOver.topology B S hS)).1 hst.1
  have hinv : Functor.IsEquivalence e.inverse.toFunctor :=
    e.symm.equiv.isEquivalence_functor
  have hidU :
      Functor.IsEquivalence (BasedFunctor.id (schemeFibredCategory B S hS U).val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 (schemeFibredCategory B S hS U).val.obj))
  -- condition (3) of Stacks 045G for `𝒳`, from its diagonal clause
  have h₃ : IsRepresentableFromSchemes B S hS (CatFiberedInGroupoids.mk 𝒳 hfib) :=
    (isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS
        (CatFiberedInGroupoids.mk 𝒳 hfib)).1
      ((hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS
        (CatFiberedInGroupoids.mk 𝒳 hfib)).1 hdiag)
  -- the same condition for `𝒴`: compose a scheme-valued 1-morphism with the quasi-inverse
  have h₃' : IsRepresentableFromSchemes B S hS (CatFiberedInGroupoids.mk 𝒴 hfib') :=
    fun V x => (isRepresentableByAlgebraicSpaces_iff_of_equivalence_target B S hS
      (𝒳 := schemeFibredCategory B S hS V) (𝒴' := CatFiberedInGroupoids.mk 𝒴 hfib')
      (𝒴 := CatFiberedInGroupoids.mk 𝒳 hfib)
      (BasedFunctor.comp x e.inverse) x e.inverse (Iso.refl _)).1
      (h₃ V (BasedFunctor.comp x e.inverse))
  -- the unit of `e`, whiskered by the atlas of `𝒳`
  let α : BasedFunctor.comp (BasedFunctor.id _) f ≅
      BasedFunctor.comp (BasedFunctor.comp f e.functor) e.inverse :=
    BasedNatIso.mkNatIso
      (Functor.isoWhiskerLeft f.toFunctor
        (BasedFunctor.toFunctorIso e.functor e.inverse e.unitIso).symm)
      (fun a => e.unitIso.inv.isHomLift (f.w_obj a))
  refine ⟨hfib', ⟨hst', hst'.isStackInGroupoids hfib'⟩,
    (hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS
        (CatFiberedInGroupoids.mk 𝒴 hfib')).2
      ((isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS
        (CatFiberedInGroupoids.mk 𝒴 hfib')).2 h₃'),
    U, BasedFunctor.comp f e.functor, h₃' U (BasedFunctor.comp f e.functor), ?_⟩
  exact relativeProperty_of_equivalences B S hS
    (Space.surjectiveMorphismProperty B S hS ⊓ Space.smoothMorphismProperty B S hS)
    (𝒳' := schemeFibredCategory B S hS U) (𝒴' := CatFiberedInGroupoids.mk 𝒴 hfib')
    (𝒳 := schemeFibredCategory B S hS U) (𝒴 := CatFiberedInGroupoids.mk 𝒳 hfib)
    (BasedFunctor.comp f e.functor) f (BasedFunctor.id _) e.inverse α hprops

end Transport

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

section Smallness

variable {A : AlgebraicSpaces C S hS}

/-- **The vertical morphisms of the quotient stack form a `u`-small type.** For objects `x`, `y`
of the fibre of `[U/R]` over `T`, the morphisms `x ⟶ y` of the fibre correspond, through the
canonical vertical isomorphisms from the chosen pullbacks along `𝟙 T`, to sections of the
isomorphism presheaf `Isom(x, y)` over the final object of the slice over `T`; by Stacks 04TB
(`AlgebraicGeometry.Stack.lemma04TB`) these are in bijection with the points of an algebraic
space. -/
theorem small_fiber_hom_quotientStack (G : GroupoidInAlgebraicSpaces C S hS A)
    {T : BigFppfOver C S hS} (x y : (quotientStack G).p.Fiber T) : Small.{u} (x ⟶ y) := by
  have hgpd : IsGroupoid ((quotientStack G).p.Fiber T) :=
    (isFiberedInGroupoids_quotientStack G).fiber_isGroupoid T
  obtain ⟨F, -, e, -⟩ := lemma04TB C S hS A G T x y
  let g : Over T := Over.mk (𝟙 T)
  let i : g ≅ (Over.iteratedSliceBackward T).obj ((Over.iteratedSliceForward T).obj g) :=
    (Over.iteratedSliceEquiv T).unitIso.app g
  let cx : (quotientStack G).p.pullbackFiber x (𝟙 T) ⟶ x :=
    Functor.Fiber.homMk _ T (Functor.IsPreFibered.pullbackMap x.2 (𝟙 T))
  let cy : (quotientStack G).p.pullbackFiber y (𝟙 T) ⟶ y :=
    Functor.Fiber.homMk _ T (Functor.IsPreFibered.pullbackMap y.2 (𝟙 T))
  have hcx : IsIso cx := hgpd.all_isIso cx
  have hcy : IsIso cy := hgpd.all_isIso cy
  let j : (x ⟶ y) → ((quotientStack G).p.isomPresheaf x y).obj (op g) :=
    fun m => ⟨cx ≫ m ≫ inv cy, hgpd.all_isIso _⟩
  have hj : Function.Injective j := by
    intro m₁ m₂ h
    have h' : cx ≫ m₁ ≫ inv cy = cx ≫ m₂ ≫ inv cy := congrArg Subtype.val h
    rwa [cancel_epi, cancel_mono] at h'
  exact small_of_injective (f := fun m =>
    e (op ((Over.iteratedSliceForward T).obj g))
      ((((quotientStack G).p.isomPresheaf x y).mapIso i.symm.op).toEquiv (j m)))
    ((e _).injective.comp ((Iso.toEquiv _).injective.comp hj))

/-- **The hom types of the quotient stack are `u`-small.** A morphism `a ⟶ b` of `[U/R]` is the
composite of a vertical morphism from `a` to the chosen pullback of `b` along its image `f` in
the base with the chosen cartesian lift of `f`; the base morphisms form a type in `Type u`, and
the vertical morphisms are `u`-small by
`AlgebraicGeometry.Stack.small_fiber_hom_quotientStack`. -/
theorem small_hom_quotientStack (G : GroupoidInAlgebraicSpaces C S hS A)
    (x y : (quotientStack G).obj) : Small.{u} (x ⟶ y) := by
  let p := (quotientStack G).p
  let γ : (p.obj x ⟶ p.obj y) → Type (u + 1) := fun f =>
    (Functor.Fiber.mk (rfl : p.obj x = p.obj x) : p.Fiber (p.obj x)) ⟶
      p.pullbackFiber (Functor.Fiber.mk (rfl : p.obj y = p.obj y)) f
  have hγ : ∀ f, Small.{u} (γ f) := fun f => small_fiber_hom_quotientStack G _ _
  exact @small_of_surjective (Σ f, γ f) (x ⟶ y) inferInstance (fun φ =>
    Functor.Fiber.fiberInclusion.map φ.2 ≫
      Functor.IsPreFibered.pullbackMap (rfl : p.obj y = p.obj y) φ.1) fun φ =>
    ⟨⟨p.map φ, Functor.Fiber.homMk p (p.obj x)
      (Functor.IsCartesian.map p (p.map φ)
        (Functor.IsPreFibered.pullbackMap (rfl : p.obj y = p.obj y) (p.map φ)) φ)⟩,
      Functor.IsCartesian.fac p (p.map φ)
        (Functor.IsPreFibered.pullbackMap (rfl : p.obj y = p.obj y) (p.map φ)) φ⟩

/- The quotient stack of a groupoid in algebraic spaces is locally `u`-small: this is the base's
`AlgebraicGeometry.Stack.locallySmall_quotientStack`, made an instance here. -/
attribute [instance] locallySmall_quotientStack

/-- The quotient stack `[U/R]` with its hom types replaced by their `u`-small models
`CategoryTheory.ShrinkHoms`, as a category over the big fppf site of `S`: the structure functor
is the inverse of `CategoryTheory.ShrinkHoms.equivalence` followed by that of `[U/R]`. -/
noncomputable abbrev smallQuotientStackBased (G : GroupoidInAlgebraicSpaces C S hS A) :
    BasedCategory.{u, u + 1} (BigFppfOver C S hS) where
  obj := ShrinkHoms (quotientStack G).obj
  p := ShrinkHoms.inverse (quotientStack G).obj ⋙ (quotientStack G).p

/-- The comparison of `[U/R]` with its small model is an equivalence over the site: the forward
functor is `CategoryTheory.ShrinkHoms.functor`, the backward one
`CategoryTheory.ShrinkHoms.inverse`, and the unit and counit those of
`CategoryTheory.ShrinkHoms.equivalence`, whose components are identities. -/
noncomputable def smallQuotientStackEquivalenceOver (G : GroupoidInAlgebraicSpaces C S hS A) :
    StacksRepresentableCFG.EquivalenceOver (quotientStack G).p (smallQuotientStackBased G).p where
  hom := ⟨ShrinkHoms.functor (quotientStack G).obj,
    CategoryTheory.Functor.ext (fun _ => rfl) fun _ _ f =>
      congrArg (quotientStack G).p.map ((equivShrink _).symm_apply_apply f)⟩
  inv := ⟨ShrinkHoms.inverse (quotientStack G).obj, rfl⟩
  unitIso := (ShrinkHoms.equivalence (quotientStack G).obj).unitIso
  counitIso := (ShrinkHoms.equivalence (quotientStack G).obj).counitIso
  unit_over := by
    refine NatTrans.ext (funext fun a => ?_)
    simp only [Functor.whiskerRight_app, eqToHom_app]
    exact ((quotientStack G).p.map_id a).trans (eqToHom_refl _ _).symm
  counit_over := by
    refine NatTrans.ext (funext fun a => ?_)
    simp only [Functor.whiskerRight_app, eqToHom_app]
    exact ((smallQuotientStackBased G).p.map_id a).trans (eqToHom_refl _ _).symm

/-- The forward functor of the comparison of `[U/R]` with its small model is
`CategoryTheory.ShrinkHoms.functor`. -/
@[simp]
theorem smallQuotientStackEquivalenceOver_hom_functor (G : GroupoidInAlgebraicSpaces C S hS A) :
    (smallQuotientStackEquivalenceOver G).hom.functor =
      ShrinkHoms.functor (quotientStack G).obj :=
  rfl

end Smallness

/-- **The small model of the quotient stack of a smooth groupoid, as an algebraic stack.** For a
smooth groupoid `G` in algebraic spaces over `S`, the category
`AlgebraicGeometry.Stack.smallQuotientStackBased G` is an algebraic stack: it is equivalent over
the site to `[U/R]`, which is one by Stacks 04TK
(`AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_of_isSmooth_unconditional`). -/
noncomputable def smallQuotientStack
    (G : GroupoidInAlgebraicSpaces C S hS (baseSpace C S hS))
    (hG : GroupoidInAlgebraicSpaces.IsSmooth C S hS G) : AlgebraicStacks.{u, w} C S hS :=
  have h := isAlgebraicStack_of_equivalence'.{u, w} C S hS
    (smallQuotientStackEquivalenceOver G).toBasedEquivalence
    (isAlgebraicStack_quotientStack_of_isSmooth_unconditional.{u, w} hG)
  ⟨⟨smallQuotientStackBased G, h.1⟩, h⟩

/-- The underlying category over the site of `AlgebraicGeometry.Stack.smallQuotientStack G hG`
is `AlgebraicGeometry.Stack.smallQuotientStackBased G`. -/
@[simp]
theorem smallQuotientStack_val_val
    (G : GroupoidInAlgebraicSpaces C S hS (baseSpace C S hS))
    (hG : GroupoidInAlgebraicSpaces.IsSmooth C S hS G) :
    (smallQuotientStack.{u, w} G hG).val.val = smallQuotientStackBased G :=
  rfl

/-- **The small model of `[U/R]` is presented by `G`** (Stacks 04TI): the presenting groupoid is
`G` itself, and the equivalence is `AlgebraicGeometry.Stack.smallQuotientStackEquivalenceOver`,
whose forward functor is `CategoryTheory.ShrinkHoms.functor`. -/
noncomputable def smallQuotientStackPresentation
    (G : GroupoidInAlgebraicSpaces C S hS (baseSpace C S hS))
    (hG : GroupoidInAlgebraicSpaces.IsSmooth C S hS G) :
    GroupoidPresentation C S hS (smallQuotientStack.{u, w} G hG).val.val where
  groupoid := G
  smooth := hG
  equivalence := smallQuotientStackEquivalenceOver G

/-- The presenting groupoid of `AlgebraicGeometry.Stack.smallQuotientStackPresentation G hG` is
`G`. -/
@[simp]
theorem smallQuotientStackPresentation_groupoid
    (G : GroupoidInAlgebraicSpaces C S hS (baseSpace C S hS))
    (hG : GroupoidInAlgebraicSpaces.IsSmooth C S hS G) :
    (smallQuotientStackPresentation.{u, w} G hG).groupoid = G :=
  rfl

/-- The presenting equivalence of `AlgebraicGeometry.Stack.smallQuotientStackPresentation G hG`
has `CategoryTheory.ShrinkHoms.functor` as its forward functor. -/
@[simp]
theorem smallQuotientStackPresentation_equivalence_hom_functor
    (G : GroupoidInAlgebraicSpaces C S hS (baseSpace C S hS))
    (hG : GroupoidInAlgebraicSpaces.IsSmooth C S hS G) :
    (smallQuotientStackPresentation.{u, w} G hG).equivalence.hom.functor =
      ShrinkHoms.functor (quotientStack G).obj :=
  rfl

end AlgebraicGeometry.Stack

end
