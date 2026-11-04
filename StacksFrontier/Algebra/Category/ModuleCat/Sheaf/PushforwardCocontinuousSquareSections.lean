module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardCocontinuousSquare
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.Final.Type

/-!
# The exchange of direct image and restriction over a square, read on compatible families

Let
```
  C' --v'--> C
  |          |
  u'         u
  v          v
  D' --v---> D
```
be a commutative square of functors of sites as in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PushforwardCocontinuousSquare.lean`, and let `M` be
a sheaf of `O_C`-modules. The value at `V'` of the comparison
`Stacks.SheafOfModules.squareComparison : f_* ∘ g^* ⟶ (g')^* ∘ f'_*` is a map between two
limits, `f_*M(v(V')) = lim_{(U, v(V') ⟶ u(U))} M(U)` and
`f'_*(M|_{C'})(V') = lim_{(U', V' ⟶ u'(U'))} M(v'(U'))`, and on the legs of the limit cones it is
restriction along the comparison functor of index categories of Stacks 0FN1
(`Stacks.SheafOfModules.squareComparisonApp_π`).

This file records the consequence: the comparison is invertible as soon as, for every `V'`,
restriction of compatible families of sections of `M` along that comparison functor is a
bijection. That is weaker than the cofinality hypothesis of
`Stacks.SheafOfModules.isIso_squareComparison_app`, which makes the restriction bijective for
*every* presheaf; here it is only asked for the one sheaf `M`, which is the form in which the
local-factorization conditions of Stacks 07AK deliver it.

## Main results

* `Stacks.SheafOfModules.bijective_squareComparisonApp`: the component at `V'` is bijective when
  restriction of compatible families along the comparison functor is.
* `Stacks.SheafOfModules.isIso_squareComparison_app_of_bijective`: the comparison is an
  isomorphism at `M` when that holds for every `V'`.

## References

* [Stacks Project, Tag 0FN1](https://stacks.math.columbia.edu/tag/0FN1)
* [Stacks Project, Tag 0FN3](https://stacks.math.columbia.edu/tag/0FN3)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe v r v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

namespace Stacks.SheafOfModules

variable {C' : Type u₁} [Category.{v₁} C'] {C : Type u₂} [Category.{v₂} C] {D' : Type u₃}
  [Category.{v₃} D'] {D : Type u₄} [Category.{v₄} D] {J' : GrothendieckTopology C'}
  {J : GrothendieckTopology C} {K' : GrothendieckTopology D'} {K : GrothendieckTopology D}
  {u' : C' ⥤ D'} {u : C ⥤ D} {v' : C' ⥤ C} {v : D' ⥤ D} [u.IsCocontinuous J K]
  [u'.IsCocontinuous J' K'] [v.IsContinuous K' K] [v.IsCocontinuous K' K]
  [v'.IsContinuous J' J] [v'.IsCocontinuous J' J]
  [∀ G : Cᵒᵖ ⥤ AddCommGrpCat.{v}, u.op.HasPointwiseRightKanExtension G]
  [∀ G : C'ᵒᵖ ⥤ AddCommGrpCat.{v}, u'.op.HasPointwiseRightKanExtension G]
  {OC : Sheaf J RingCat.{r}} {OD : Sheaf K RingCat.{r}}

/-- **The comparison at `V'` is restriction of compatible families, hence bijective when that
restriction is.** The two limits are identified with the compatible families of sections over
their index categories, the forgetful functor of abelian groups preserving limits, and under these
identifications the component of the base-change transformation at `V'` is restriction along the
comparison functor `TwoSquare.structuredArrowDownwards` of the opposite square, by
`Stacks.SheafOfModules.squareComparisonApp_π`. -/
lemma bijective_squareComparisonApp (hsq : u' ⋙ v = v' ⋙ u)
    (M : _root_.SheafOfModules.{v} OC) (V' : D'ᵒᵖ)
    (h : Function.Bijective (Functor.sectionsPrecomp
      ((Stacks.Sites.CocontinuousExchange.twoSquare hsq).op.structuredArrowDownwards V')
      (P := StructuredArrow.proj (v.op.obj V') u.op ⋙ M.val.presheaf ⋙
        forget AddCommGrpCat.{v}))) :
    Function.Bijective (squareComparisonApp (J' := J') hsq M V') := by
  let G := M.val.presheaf
  let G' := ((inverseImage.{v} J' J v' OC).obj M).val.presheaf
  let eA := Types.isLimitEquivSections
    (isLimitOfPreserves (forget AddCommGrpCat.{v}) (ranIsLimit u.op G (v.op.obj V')))
  let eB := Types.isLimitEquivSections
    (isLimitOfPreserves (forget AddCommGrpCat.{v}) (ranIsLimit u'.op G' V'))
  let Ψ := (Stacks.Sites.CocontinuousExchange.twoSquare hsq).op.structuredArrowDownwards V'
  -- the two sets of compatible families over the index category of `f'_*` are the same
  let τ : (Ψ ⋙ StructuredArrow.proj (v.op.obj V') u.op ⋙ G ⋙
      forget AddCommGrpCat.{v}).sections →
      (StructuredArrow.proj V' u'.op ⋙ G' ⋙ forget AddCommGrpCat.{v}).sections :=
    fun t => ⟨t.val, t.property⟩
  have hτ : Function.Bijective τ :=
    ⟨fun t₁ t₂ h => Subtype.ext (congrArg Subtype.val h),
      fun t => ⟨⟨t.val, t.property⟩, rfl⟩⟩
  have key : ∀ x, eB (squareComparisonApp (J' := J') hsq M V' x) =
      τ (Functor.sectionsPrecomp Ψ (eA x)) := fun x => Subtype.ext <| funext fun j => by
    rw [Types.isLimitEquivSections_apply]
    exact congrArg (fun g => g x)
      (congrArg ConcreteCategory.hom (squareComparisonApp_π (J' := J') hsq M V' j))
  have hfun : eB ∘ (squareComparisonApp (J' := J') hsq M V' : _ → _) =
      τ ∘ Functor.sectionsPrecomp Ψ ∘ eA := funext key
  refine (Function.Bijective.of_comp_iff' eB.bijective _).1 ?_
  rw [hfun]
  exact hτ.comp (h.comp eA.bijective)

variable [∀ G : Cᵒᵖ ⥤ RingCat.{r}, u.op.HasPointwiseRightKanExtension G]
  [∀ G : C'ᵒᵖ ⥤ RingCat.{r}, u'.op.HasPointwiseRightKanExtension G]
  (fSharp : OD ⟶ (u.sheafPushforwardCocontinuous RingCat.{r} J K).obj OC)

/-- **The comparison of the two composites is invertible at `M`** as soon as, at every object `V'`
of `D'`, restriction of compatible families of sections of `M` along the comparison functor of
index categories is bijective. The forgetful functors to sheaves and to presheaves of abelian
groups reflect isomorphisms, and a natural transformation of presheaves of abelian groups all of
whose components are bijective is an isomorphism. -/
lemma isIso_squareComparison_app_of_bijective (hsq : u' ⋙ v = v' ⋙ u)
    (M : _root_.SheafOfModules.{v} OC)
    (h : ∀ V' : D'ᵒᵖ, Function.Bijective (Functor.sectionsPrecomp
      ((Stacks.Sites.CocontinuousExchange.twoSquare hsq).op.structuredArrowDownwards V')
      (P := StructuredArrow.proj (v.op.obj V') u.op ⋙ M.val.presheaf ⋙
        forget AddCommGrpCat.{v}))) :
    IsIso ((squareComparison (J' := J') (K' := K') fSharp hsq).app M) := by
  have h0 : ∀ V' : D'ᵒᵖ, IsIso ((squareComparisonPresheaf (J' := J') hsq M).app V') :=
    fun V' => (ConcreteCategory.isIso_iff_bijective _).2
      (bijective_squareComparisonApp hsq M V' (h V'))
  have h1 : IsIso (squareComparisonPresheaf (J' := J') hsq M) := NatIso.isIso_of_isIso_app _
  have h2 : IsIso ((sheafToPresheaf K' AddCommGrpCat.{v}).map
      ((_root_.SheafOfModules.toSheaf.{v} (inverseImageRing K' K v OD)).map
        ((squareComparison (J' := J') (K' := K') fSharp hsq).app M))) := h1
  have h3 : IsIso ((_root_.SheafOfModules.toSheaf.{v} (inverseImageRing K' K v OD)).map
      ((squareComparison (J' := J') (K' := K') fSharp hsq).app M)) :=
    isIso_of_reflects_iso _ (sheafToPresheaf K' AddCommGrpCat.{v})
  exact isIso_of_reflects_iso _
    (_root_.SheafOfModules.toSheaf.{v} (inverseImageRing K' K v OD))

end Stacks.SheafOfModules

end
