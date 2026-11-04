module

public import StacksFrontier.AlgebraicGeometry.Stacks.DescendingStacksAlongLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.BaseChangeQuotientStackComparisonFibreFull
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFirstFactor

/-!
# The base-change comparison of quotient stacks in the 2-category of algebraic stacks

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `Y`, let
`g : Y' ⟶ Y` be a morphism of algebraic spaces and let `M` be an algebraic stack with a
1-morphism `m : M ⟶ Y` identified, over `Y`, with the structure 1-morphism `[U/R] ⟶ Y` of
Stacks 044R. Then the quotient stack of the base change `G ×_Y Y'` is, over `Y'`, the 2-fibre
product `M ×_Y Y'` taken in the 2-category of algebraic stacks.

This is the last paragraph of the proof of Stacks 0CN4, and it is the input
`AlgebraicGeometry.Stack.StackDescentSystem.ModelBaseChangeComparison` of
`AlgebraicGeometry.Stack.StackDescentSystem.exists_stage_model_of_inputs`, which is discharged
here as `AlgebraicGeometry.Stack.StackDescentSystem.modelBaseChangeComparison`.

## Main results

* `AlgebraicGeometry.Stack.invariantTargetGroupoid_id`: reading a groupoid over its own base, as a
  groupoid over the invariant morphism `U ⟶ Y`, returns the groupoid itself.
* `AlgebraicGeometry.Stack.isEquivalence_baseChangeQuotientStackComparison_id`: the comparison
  1-morphism of Stacks 0DTG for the invariant morphism `U ⟶ Y` is an equivalence.
* `AlgebraicGeometry.Stack.nonempty_equivalenceOver_baseChange_twoFibreProduct`: the comparison
  above, for any model `M` of `[U/R]` over `Y`.
* `AlgebraicGeometry.Stack.StackDescentSystem.modelBaseChangeComparison`: the same at a stage of a
  descent system.

## Implementation notes

The comparison is Stacks 0DTG
(`AlgebraicGeometry.Stack.baseChangeQuotientStackSquare_isTwoFibreProduct`) read at the invariant
morphism `U ⟶ Y` and the identity of `Y`. That statement lives in the 2-category of stacks in
groupoids whose morphisms are one universe above those of the site, because the hom sets of a
quotient stack are; the 2-fibre product of the conclusion is the explicit one of Stacks 04T2 in
the 2-category of algebraic stacks, whose hom sets are those of the site. The two are compared
through explicit functors between explicit 2-fibre products: the comparison functor of 0DTG,
then lowering the target of the cospan (`CategoryTheory.TwoFibreProductOver.mapBase`), replacing
the first leg by the model along its 2-isomorphism (`CategoryTheory.TwoFibreProductOver.reindex`
and `CategoryTheory.TwoFibreProductOver.precomposeFst`), and lowering the second factor
(`CategoryTheory.TwoFibreProductOver.precomposeSnd`). Each is an equivalence strictly over the
site, the composite followed by the second projection is the structure 1-morphism of the base
change on the nose, and Stacks 003Z (2) turns the composite into an equivalence over the site.

## References

* [Stacks Project, Tag 0CN4](https://stacks.math.columbia.edu/tag/0CN4)
* [Stacks Project, Tag 0DTG](https://stacks.math.columbia.edu/tag/0DTG)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The structure morphism `U ⟶ Y` of the object space of a groupoid over `Y` is invariant
(Stacks 048E): the source and the target maps are both morphisms over `Y`. -/
theorem isInvariant_objectsToBase {Y : AlgebraicSpaces B S hS}
    (G : GroupoidInAlgebraicSpaces B S hS Y) :
    Space.IsInvariant (Space.groupoidPreRelation G) G.objectsToBase.hom :=
  (isInvariant_iff G G.objectsToBase).2 (G.target_over.trans G.source_over.symm)

/-- **Reading a groupoid over its own base as a groupoid over its invariant structure morphism
changes nothing.** The groupoid of `AlgebraicGeometry.Stack.invariantTargetGroupoid` for the
invariant morphism `U ⟶ Y` and the identity of `Y` is the given groupoid: its arrow space is put
over `Y` through the source map, which is what the source map being over `Y` says. -/
theorem invariantTargetGroupoid_id {Y : AlgebraicSpaces B S hS}
    (G : GroupoidInAlgebraicSpaces B S hS Y) :
    invariantTargetGroupoid G (𝟙 Y) G.objectsToBase (Category.comp_id _)
      (isInvariant_objectsToBase G) = G := by
  obtain ⟨U, R, oB, aB, s, t, so, tov, c, co, pg⟩ := G
  subst so
  rfl

variable {Y X' : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS Y) (g : X' ⟶ Y)

/-- **The comparison 1-morphism of Stacks 0DTG, at the invariant morphism `U ⟶ Y`, is an
equivalence.** It is full, faithful and locally essentially surjective on fibres, which is what
`AlgebraicGeometry.Stack.isEquivalenceOver_baseChangeTwoFibreProduct` asks for. -/
theorem isEquivalence_baseChangeQuotientStackComparison_id :
    (baseChangeQuotientStackComparison.{u, u} G (𝟙 Y) g g (Category.comp_id g)
      G.objectsToBase (Category.comp_id _) (isInvariant_objectsToBase G)).IsEquivalence := by
  have hinv := (isInvariant_objectsToBase G)
  have := full_baseChangeQuotientStackComparison.{u, u} G (𝟙 Y) g g (Category.comp_id g)
    G.objectsToBase (Category.comp_id _) hinv
  have := faithful_comparison.{u, u} G (𝟙 Y) g g (Category.comp_id g)
    G.objectsToBase (Category.comp_id _) hinv
  have hst := isStack_quotientStack
    (invariantBaseChangeGroupoid G (𝟙 Y) g G.objectsToBase (Category.comp_id _) hinv)
  have : (quotientStack (invariantBaseChangeGroupoid G (𝟙 Y) g G.objectsToBase
      (Category.comp_id _) hinv)).p.IsFibered := hst.isFibered
  obtain ⟨hequiv⟩ := isEquivalenceOver_baseChangeTwoFibreProduct G (𝟙 Y) g G.objectsToBase
    (Category.comp_id _) hinv hst.hasEffectiveDescent
    (isFibredOneMorphism_baseChangeQuotientStackComparison.{u, u} G (𝟙 Y) g g
      (Category.comp_id g) G.objectsToBase (Category.comp_id _) hinv)
    (locallyEssSurjOnFibers_baseChangeQuotientStackComparison.{u, u} G (𝟙 Y) g g
      (Category.comp_id g) G.objectsToBase (Category.comp_id _) hinv)
  exact (CategoryTheory.Equivalence.mk _ hequiv.inv hequiv.unitIso.symm
    hequiv.counitIso).isEquivalence_functor

/-- **The base-change comparison for the groupoid read over its invariant structure morphism.**
For a model `M` of `[U/R]` over `Y`, the quotient stack of the base change along `g : X' ⟶ Y` is,
over `X'`, the 2-fibre product `M ×_Y X'` of the 2-category of algebraic stacks. See the module
documentation for the chain of equivalences. -/
theorem nonempty_equivalenceOver_invariantBaseChangeGroupoid (M : AlgebraicStacks.{u, w} B S hS)
    (m : M ⟶ algebraicSpaceStack.{u, w} B S hS Y.obj Y.property)
    (E : BasedCategory.EquivalenceOver
      (quotientStackToBase (invariantTargetGroupoid G (𝟙 Y) G.objectsToBase
        (Category.comp_id _) (isInvariant_objectsToBase G))) m.hom.hom) :
    Nonempty (BasedCategory.EquivalenceOver
      (quotientStackToBase (invariantBaseChangeGroupoid G (𝟙 Y) g G.objectsToBase
        (Category.comp_id _) (isInvariant_objectsToBase G)))
      (twoFibreProductSquareAlgebraicStacks.{u, w} B S hS m
        (Bicategory.InducedBicategory.mkHom (associatedMap B S hS g.hom).1 :
          algebraicSpaceStack.{u, w} B S hS X'.obj X'.property ⟶
            algebraicSpaceStack.{u, w} B S hS Y.obj Y.property)).snd.hom.hom) := by
  have hinv := (isInvariant_objectsToBase G)
  let H := invariantTargetGroupoid G (𝟙 Y) G.objectsToBase (Category.comp_id _) hinv
  let G' := invariantBaseChangeGroupoid G (𝟙 Y) g G.objectsToBase (Category.comp_id _) hinv
  let c := baseChangeQuotientStackComparison.{u, u} G (𝟙 Y) g g (Category.comp_id g)
      G.objectsToBase (Category.comp_id _) hinv
  let F₁ := TwoFibreProductOver.mapBase (pT := (quotientStack H).p)
    (p𝒜 := (liftedFibredCategory X').p)
    (liftedQuotientStackToBase H).toFunctor (liftedAssociatedMap g).toFunctor
    (liftedFibredCategoryDown Y).toFunctor (liftedFibredCategoryDown Y).w
  let α : (liftedQuotientStackToBase H).toFunctor ⋙ (liftedFibredCategoryDown Y).toFunctor ≅
      E.equiv.functor.toFunctor ⋙ m.hom.hom.toFunctor :=
    (BasedNatTrans.forgetful _ _).mapIso E.compIso.symm
  let F₂ := TwoFibreProductOver.reindex (p𝒴 := (liftedFibredCategory X').p)
    (G := (liftedAssociatedMap g).toFunctor ⋙ (liftedFibredCategoryDown Y).toFunctor) α
    (fun x => E.compIso.inv.isHomLift' x)
  let F₃ := TwoFibreProductOver.precomposeFst (quotientStack H).p M.val.val.p
    (liftedFibredCategory X').p (fibredCategory B S hS Y.obj).val.p m.hom.hom.toFunctor
    ((liftedAssociatedMap g).toFunctor ⋙ (liftedFibredCategoryDown Y).toFunctor)
    E.equiv.functor.toFunctor E.equiv.functor.w
  let F₄ := TwoFibreProductOver.precomposeSnd (pT := M.val.val.p)
    (pℬ := (fibredCategory B S hS Y.obj).val.p)
    m.hom.hom.toFunctor (associatedMap B S hS g.hom).1.hom.toFunctor
    (liftedFibredCategoryDown X').toFunctor (liftedFibredCategoryDown X').w
  let sq := twoFibreProductSquareAlgebraicStacks.{u, w} B S hS m
    (Bicategory.InducedBicategory.mkHom (associatedMap B S hS g.hom).1 :
      algebraicSpaceStack.{u, w} B S hS X'.obj X'.property ⟶
        algebraicSpaceStack.{u, w} B S hS Y.obj Y.property)
  let K : (quotientStack G').obj ⥤ sq.pt.val.val.obj := c ⋙ F₁ ⋙ F₂ ⋙ F₃ ⋙ F₄
  have hK : K ⋙ sq.pt.val.val.p = (quotientStack G').p :=
    baseChangeQuotientStackComparison_comp.{u, u} G (𝟙 Y) g g (Category.comp_id g)
      G.objectsToBase (Category.comp_id _) hinv
  -- the five factors are equivalences
  have hgH : (quotientStack H).p.IsFiberedInGroupoids := isFiberedInGroupoids_quotientStack H
  have hgM : M.val.val.p.IsFiberedInGroupoids := M.val.property
  have hgL : (liftedFibredCategory X').p.IsFiberedInGroupoids :=
    isFiberedInGroupoids_liftedFibredCategory X'
  have hgX : (fibredCategory B S hS X'.obj).val.p.IsFiberedInGroupoids :=
    (fibredCategory B S hS X'.obj).property
  have h0 : c.IsEquivalence := isEquivalence_baseChangeQuotientStackComparison_id G g
  have h1 : F₁.IsEquivalence := TwoFibreProductOver.isEquivalence_mapBase _
  have h2 : F₂.IsEquivalence := TwoFibreProductOver.isEquivalence_reindex _ _
  have h3 : F₃.IsEquivalence := TwoFibreProductOver.isEquivalence_precomposeFst _ _ _ _ _ _ _ _
    hgL hgH hgM E.equiv.equiv.isEquivalence_functor m.hom.hom.w
  have : (liftedFibredCategoryDown X').toFunctor.IsEquivalence :=
    isEquivalence_liftedFibredCategoryDown X'
  have h4 : F₄.IsEquivalence := TwoFibreProductOver.isEquivalence_precomposeSnd hgM hgL hgX _
    (associatedMap B S hS g.hom).1.hom.w
  have hKe : K.IsEquivalence := by
    refine @Functor.isEquivalence_trans _ _ _ _ _ _ c _ h0 ?_
    refine @Functor.isEquivalence_trans _ _ _ _ _ _ F₁ _ h1 ?_
    exact @Functor.isEquivalence_trans _ _ _ _ _ _ F₂ _ h2
      (@Functor.isEquivalence_trans _ _ _ _ _ _ F₃ F₄ h3 h4)
  obtain ⟨Finv, hF, η, ε, hη, hε⟩ := Functor.IsFiberedInGroupoids.isEquivalence_over
    (quotientStack G').p sq.pt.val.val.p (isFiberedInGroupoids_quotientStack G')
    sq.pt.val.property K hK hKe
  let EO := StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver hK
    { inv := Finv, inv_over := hF, unitIso := η, counitIso := ε
      unit_vertical := fun X => by
        have hx : (quotientStack G').p.obj ((K ⋙ Finv).obj X) = (quotientStack G').p.obj X := by
          show ((K ⋙ Finv) ⋙ (quotientStack G').p).obj X = _
          rw [Functor.assoc, hF, hK]
        rw [hx]
        exact hη X
      counit_vertical := fun y => by
        have hy : sq.pt.val.val.p.obj ((Finv ⋙ K).obj y) = sq.pt.val.val.p.obj y :=
          Functor.congr_obj ((Functor.assoc Finv K sq.pt.val.val.p).trans
            ((congrArg (Finv ⋙ ·) hK).trans hF)) y
        rw [hy]
        exact hε y }
  exact ⟨{ equiv := EO.toBasedEquivalence, compIso := Iso.refl _ }⟩

/-- **The base-change comparison of quotient stacks in the 2-category of algebraic stacks.** Let
`G` be a groupoid in algebraic spaces over `Y`, `g : X' ⟶ Y` a morphism of algebraic spaces and
`M` an algebraic stack with a 1-morphism `m : M ⟶ Y` identified over `Y` with the structure
1-morphism `[U/R] ⟶ Y`. Then the quotient stack of the base change of `G` along `g` is, over
`X'`, the 2-fibre product `M ×_{m, Y, g} X'` of the 2-category of algebraic stacks. -/
theorem nonempty_equivalenceOver_baseChange_twoFibreProduct (M : AlgebraicStacks.{u, w} B S hS)
    (m : M ⟶ algebraicSpaceStack.{u, w} B S hS Y.obj Y.property)
    (E : BasedCategory.EquivalenceOver (quotientStackToBase G) m.hom.hom) :
    Nonempty (BasedCategory.EquivalenceOver
      (quotientStackToBase (Space.baseChange G g).groupoid)
      (twoFibreProductSquareAlgebraicStacks.{u, w} B S hS m
        (Bicategory.InducedBicategory.mkHom (associatedMap B S hS g.hom).1 :
          algebraicSpaceStack.{u, w} B S hS X'.obj X'.property ⟶
            algebraicSpaceStack.{u, w} B S hS Y.obj Y.property)).snd.hom.hom) := by
  have h := nonempty_equivalenceOver_invariantBaseChangeGroupoid G g M m
    ((invariantTargetGroupoid_id G).symm ▸ E)
  rwa [invariantBaseChangeGroupoid, invariantTargetGroupoid_id G] at h

namespace StackDescentSystem

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  [Nonempty I]

/-- **The Stacks 044P, 044R, 046Q and 04Y1 input of Stacks 0CN4, discharged.** At a stage `X_i`
of a descent system, the quotient stack of the base change of a groupoid `G_i` over `X_i` to the
limit `X` is, over `X`, the 2-fibre product of any model of `[U_i/R_i]` with `X` over `X_i`. -/
theorem modelBaseChangeComparison (C : StackDescentSystem B S hS hZ I) :
    C.ModelBaseChangeComparison.{u, w} := fun i Gᵢ M =>
  nonempty_equivalenceOver_baseChange_twoFibreProduct Gᵢ (C.limitProjection i) M.stack
    M.structureMorphism M.equivOver

end StackDescentSystem

end AlgebraicGeometry.Stack
