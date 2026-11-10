module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackGerbe
public import StacksFrontier.AlgebraicGeometry.Quot.TestSchemeTotalPresheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackSmallModel
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeOverOpenSubscheme
public import StacksFrontier.CategoryTheory.Sites.Gerbe.BaseEquivalence
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.FibrewiseEquivalence

/-!
# The Picard stack is a gerbe over a model of the Picard functor, as algebraic stacks

The morphism `Picardstack_{X/B} ⟶ Pic_{X/B}` makes the Picard stack a gerbe over the category
attached to the relative Picard functor
(`AlgebraicGeometry.Space.PicardSituation.isGerbeOver_toPicardFunctorBased`). This file restates
that as a 1-morphism of algebraic stacks.

* A *model* of `Pic_{X/B}` is a functor `F` on the big fppf site of `S` with a morphism
  `q : F ⟶ B` whose fibres are identified with `Pic_{X/B}`, naturally in the test scheme. The
  category attached to `Pic_{X/B}` is equivalent over the site to the category attached to `F`
  (`AlgebraicGeometry.Space.PicardSituation.picardFunctorToModelIsEquivalenceOver`).
* The Picard stack has hom types one universe above the schemes; when it is algebraic (a
  hypothesis `h`), its object of the 2-category of algebraic stacks is its small model
  (`AlgebraicGeometry.Stack.AlgebraicStacks.smallModel`).

## Main definitions

* `AlgebraicGeometry.Space.PicardSituation.picardFunctorToModelFunctor`: the comparison from the
  category attached to `Pic_{X/B}` to the category attached to a model `F`.
* `AlgebraicGeometry.Space.PicardSituation.picardToModelAlgebraic`: the 1-morphism
  `Picardstack_{X/B} ⟶ F` of algebraic stacks.

## Main results

* `AlgebraicGeometry.Space.PicardSituation.isGerbeOver_toPicardFunctorBased_comp_model`: the
  Picard stack is a gerbe over the category attached to a model of `Pic_{X/B}`.
* `AlgebraicGeometry.Space.PicardSituation.isGerbeOver_picardToModelAlgebraic`: the same for
  the 1-morphism of algebraic stacks, in the sense of Stacks 06QC.

## References

* [Stacks Project, Tag 0DME](https://stacks.math.columbia.edu/tag/0DME)
* [Stacks Project, Tag 0D04](https://stacks.math.columbia.edu/tag/0D04)
* [Stacks Project, Tag 06P0](https://stacks.math.columbia.edu/tag/06P0)
* [Stacks Project, Tag 06QC](https://stacks.math.columbia.edu/tag/06QC)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space.PicardSituation

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (s : PicardSituation B S hS) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (q : F ⟶ s.base.1)
  (e : ∀ T : s.SchemesOver, s.picardFunctor.obj (op T) ≃
    {x : F.obj (op T.left) //
      q.app (op T.left) x = yonedaEquiv (show yoneda.obj T.left ⟶ s.base.1 from T.hom.hom)})
  (he : ∀ (T U : s.SchemesOver) (g : T ⟶ U) (x : s.picardFunctor.obj (op U)),
    (e T (s.picardFunctor.map g.op x)).val = F.map g.left.op (e U x).val)

include he in
/-- **The comparison from `Pic_{X/B}` to a model.** An element `ξ` of `Pic_{X/B}(T)` over a test
scheme `T` goes to the point `e_T(ξ)` of the model `F` over the underlying scheme of `T`, and a
morphism of test schemes to its underlying morphism of schemes. -/
def picardFunctorToModelFunctor :
    s.picardFunctorBasedCategory.obj ⥤ (Stack.fibredCategory B S hS F).val.obj where
  obj X := ⟨X.base.left, Discrete.mk (e X.base X.fiber.as).val⟩
  map {X Y} g := ⟨g.base.left, Discrete.eqToHom (by
    change (e X.base X.fiber.as).val = F.map g.base.left.op (e Y.base Y.fiber.as).val
    rw [Discrete.eq_of_hom g.fiber]
    exact he _ _ _ _)⟩
  map_id X := Pseudofunctor.CoGrothendieck.Hom.ext _ _ rfl Discrete.hom_eq
  map_comp f g := Pseudofunctor.CoGrothendieck.Hom.ext _ _ rfl Discrete.hom_eq

/-- A morphism `g : T ⟶ U` of the underlying schemes of two test schemes over the base, along
which the points of the model named by two elements of the Picard functor correspond, is a
morphism of test schemes: it commutes with the structure morphisms to the base. -/
theorem schemeSpaceFunctor_map_comp_hom_of_model {T U : s.SchemesOver} (g : T.left ⟶ U.left)
    (x : s.picardFunctor.obj (op T)) (y : s.picardFunctor.obj (op U))
    (h : (e T x).val = F.map g.op (e U y).val) :
    (schemeSpaceFunctor B S hS).map g ≫ U.hom = T.hom := by
  apply InducedCategory.hom_ext
  apply yonedaEquiv.injective
  change yonedaEquiv (yoneda.map g ≫ U.hom.hom) = yonedaEquiv T.hom.hom
  have h₁ : s.base.1.map g.op (yonedaEquiv U.hom.hom) = yonedaEquiv (yoneda.map g ≫ U.hom.hom) :=
    yonedaEquiv_naturality _ _
  have h₂ : q.app _ (F.map g.op (e U y).val) = s.base.1.map g.op (q.app _ (e U y).val) :=
    NatTrans.naturality_apply q g.op _
  have h₃ : q.app _ (e U y).val = yonedaEquiv U.hom.hom := (e U y).property
  have h₄ : q.app _ (e T x).val = yonedaEquiv T.hom.hom := (e T x).property
  rw [← h₁, ← h₃, ← h₂, ← h, h₄]

/-- The comparison from `Pic_{X/B}` to a model is faithful. -/
instance faithful_picardFunctorToModelFunctor :
    (s.picardFunctorToModelFunctor F q e he).Faithful where
  map_injective {X Y} g g' h := by
    refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ ?_ Discrete.hom_eq
    exact CostructuredArrow.hom_ext _ _ (congrArg Pseudofunctor.CoGrothendieck.Hom.base h)

/-- The comparison from `Pic_{X/B}` to a model is full. -/
instance full_picardFunctorToModelFunctor :
    (s.picardFunctorToModelFunctor F q e he).Full where
  map_surjective {X Y} k := by
    have hk : (e X.base X.fiber.as).val = F.map k.base.op (e Y.base Y.fiber.as).val :=
      Discrete.eq_of_hom k.fiber
    let g : X.base ⟶ Y.base := CostructuredArrow.homMk k.base
      (s.schemeSpaceFunctor_map_comp_hom_of_model F q e k.base _ _ hk)
    refine ⟨⟨g, Discrete.eqToHom ?_⟩, ?_⟩
    · exact (e X.base).injective (Subtype.ext (hk.trans (he _ _ g _).symm))
    · exact Pseudofunctor.CoGrothendieck.Hom.ext _ _ rfl Discrete.hom_eq

/-- Every object `(U, x)` of the category attached to the model is, by an identity over `U`, the
image of the element of `Pic_{X/B}` over the test scheme `(U, q(x))` that `x` names. -/
theorem hasVerticalPreimages_picardFunctorToModelFunctor :
    Functor.HasVerticalPreimages s.picardFunctorBasedCategory.p
      (Stack.fibredCategory B S hS F).val.p (s.picardFunctorToModelFunctor F q e he) := by
  rintro ⟨U, ⟨x⟩⟩
  let T := pointTestScheme (Y := s.base) U (q.app _ x)
  let o : s.picardFunctorBasedCategory.obj :=
    ⟨T, ⟨(e T).symm ⟨x, (testPoint_pointTestScheme _ (q.app _ x)).symm⟩⟩⟩
  have h : (⟨U, ⟨x⟩⟩ : (Stack.fibredCategory B S hS F).val.obj) =
      (s.picardFunctorToModelFunctor F q e he).obj o := by
    change (⟨U, ⟨x⟩⟩ : (Stack.fibredCategory B S hS F).val.obj) =
      ⟨U, ⟨(e T ((e T).symm ⟨x, (testPoint_pointTestScheme _ (q.app _ x)).symm⟩)).val⟩⟩
    rw [Equiv.apply_symm_apply]
  exact ⟨o, rfl, eqToIso h, IsHomLift.eqToHom_domain_lift_id h rfl⟩

/-- The comparison from the category attached to `Pic_{X/B}` to the category attached to its
model is an equivalence over the big fppf site of `S`. -/
noncomputable def picardFunctorToModelIsEquivalenceOver :
    Functor.IsEquivalenceOver s.picardFunctorBasedCategory.p
      (Stack.fibredCategory B S hS F).val.p (s.picardFunctorToModelFunctor F q e he) :=
  Functor.isEquivalenceOver_of_exists_vertical_iso rfl
    (s.hasVerticalPreimages_picardFunctorToModelFunctor F q e he)

/-- **The Picard stack is a gerbe over a model of the Picard functor.** The morphism
`Picardstack_{X/B} ⟶ Pic_{X/B}`, followed by the identification of `Pic_{X/B}` with the category
attached to the model `F`, makes the Picard stack a gerbe over `F`. -/
theorem isGerbeOver_toPicardFunctorBased_comp_model :
    IsGerbeOver (BigFppfOver.topology B S hS) (Stack.fibredCategory B S hS F).val.p
      (s.toPicardFunctorBased.toFunctor ⋙ s.picardFunctorToModelFunctor F q e he) :=
  IsGerbeOver.comp s.isGerbeOver_toPicardFunctorBased
    (isGerbeOver_of_isEquivalenceOver _ rfl (s.picardFunctorToModelIsEquivalenceOver F q e he)
      (Stack.fibredCategory B S hS F).isFiberedInGroupoids)

/-! ### The Picard stack as an algebraic stack -/

section Algebraic

universe w

/-- **The 1-morphism `Picardstack_{X/B} ⟶ Pic_{X/B}` of algebraic stacks**, given that the
Picard stack is algebraic (`h`) and that the model `F` of `Pic_{X/B}` is an algebraic space
(`hF`): the morphism `Picardstack_{X/B} ⟶ Pic_{X/B}` read on the small model of the Picard stack
and on the algebraic stack of `F`. -/
noncomputable def picardToModelAlgebraic
    (h : Stack.IsAlgebraicStack.{u, w} B S hS
      (picardCFG (modulePushforwardCoherence B S hS) s).val)
    (hF : IsAlgebraicSpace B S hS F) :
    Stack.AlgebraicStacks.smallModel B S hS _ h ⟶ Stack.algebraicSpaceStack.{u, w} B S hS F hF :=
  letI : LocallySmall.{u} (picardBasedCategory (modulePushforwardCoherence B S hS) s).obj :=
    Stack.locallySmall_of_isAlgebraicStack B S hS h
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    ⟨ShrinkHoms.inverse.{u} (picardBasedCategory (modulePushforwardCoherence B S hS) s).obj ⋙
      s.toPicardFunctorBased.toFunctor ⋙ s.picardFunctorToModelFunctor F q e he, rfl⟩)

/-- **The Picard stack is a gerbe over a model, as algebraic stacks.** Given that the Picard
stack is algebraic (`h`) and that the model `F` is an algebraic space (`hF`), the 1-morphism
`Picardstack_{X/B} ⟶ Pic_{X/B}` of algebraic stacks makes the Picard stack a gerbe over the model
`F` of the Picard functor, in the sense of `AlgebraicGeometry.Stack.AlgebraicStacks.IsGerbeOver`.
-/
theorem isGerbeOver_picardToModelAlgebraic
    (h : Stack.IsAlgebraicStack.{u, w} B S hS
      (picardCFG (modulePushforwardCoherence B S hS) s).val)
    (hF : IsAlgebraicSpace B S hS F) :
    Stack.AlgebraicStacks.IsGerbeOver B S hS (s.picardToModelAlgebraic F q e he h hF) := by
  let : LocallySmall.{u} (picardBasedCategory (modulePushforwardCoherence B S hS) s).obj :=
    Stack.locallySmall_of_isAlgebraicStack B S hS h
  refine IsGerbeOver.of_isEquivalenceOver_base
    (a := ShrinkHoms.functor.{u} (picardBasedCategory (modulePushforwardCoherence B S hS) s).obj)
    (F := s.toPicardFunctorBased.toFunctor ⋙ s.picardFunctorToModelFunctor F q e he) ?_
    (BasedCategory.shrinkHomsIsEquivalenceOver _)
    (s.isGerbeOver_toPicardFunctorBased_comp_model F q e he)
  exact (Functor.assoc _ _ _).symm.trans
    ((congrArg (· ⋙ (s.toPicardFunctorBased.toFunctor ⋙ s.picardFunctorToModelFunctor F q e he))
      (BasedCategory.shrinkHoms_functor_comp_inverse
        (picardBasedCategory (modulePushforwardCoherence B S hS) s))).trans (Functor.id_comp _))

end Algebraic

end AlgebraicGeometry.Space.PicardSituation

end
