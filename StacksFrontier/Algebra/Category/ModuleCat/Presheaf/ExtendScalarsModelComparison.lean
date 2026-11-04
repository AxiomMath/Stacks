module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ChangeOfRingsAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PullbackModel

/-!
# The two presheaf-level models of extension of scalars agree

Extension of scalars for presheaves of modules along a morphism `α : R ⟶ R'` of presheaves of
commutative rings is built twice in this development, by two routes that never meet:

* `Stacks.PullbackModel.extendScalars`, which takes the objectwise `ModuleCat.extendScalars` and
  assembles the restriction maps by base change, and is the left half of the concrete model of
  `CategoryTheory.PresheafOfModules.pullback`;
* `Stacks.PresheafOfModules.ChangeOfRings.changeOfRings`, the sectionwise tensor product
  `R' ⊗_{α, R} -` of Stacks 03CU, which is the functor the sheafification comparisons of
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ChangeOfRingsLocalIso.lean` are stated for.

They are the same functor, and this file says so. Both are left adjoint to *the same* functor:
restriction of scalars along `α`, which each of the two constructions spells as
`CategoryTheory.PresheafOfModules.restrictScalars (Functor.whiskerRight α (forget₂ CommRingCat
RingCat))` — `Stacks.PullbackModel.toRingCat α` on one side and
`Stacks.PresheafOfModules.ChangeOfRings.restrictScalars α` on the other are that one term. So the
comparison is uniqueness of a left adjoint and nothing else.

## Main definitions

* `Stacks.PullbackModel.extendScalarsIsoChangeOfRings`: the comparison.

## Implementation notes

The comparison is needed because the two models carry disjoint APIs. The objectwise model is what
the direct-sum formula of Stacks 0D72 in case (B) is proved with
(`Stacks.Sites.ComponentModuleSumFormula.transitionPullbackPresheafModules` is
`PresheafOfModules.pushforward₀OfCommRingCat` followed by
`Stacks.PullbackModel.extendScalars`), whereas the tensor model is the one known to commute with
sheafification: `Stacks.Sheaves.RingedToposModules.extendScalarsSheafifyIso` and
`…sheafifyChangeOfRingsNatIso` are stated for
`Stacks.PresheafOfModules.ChangeOfRings.changeOfRings`, and
`Stacks.Sheaves.RingedToposModules.extendScalars` — the sheaf-level extension of scalars out of
which `…extendScalarsFSharp` and hence the pullback of modules along a morphism of ringed topoi
is built — is the tensor model followed by sheafification. Comparing the summand of the case-(B)
formula with the pullback along the transition morphism of ringed topoi therefore has to pass
through this isomorphism first.

Neither of the two modules imports the other, and their import closures are disjoint, so the
comparison cannot live in either; this module is their join.

## References

* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u u₁ v₁

namespace Stacks.PullbackModel

/-- **The objectwise and the tensor model of extension of scalars for presheaves of modules are
the same functor.** Both are left adjoint to restriction of scalars along the same morphism of
presheaves of rings, so they agree by uniqueness of left adjoints. -/
def extendScalarsIsoChangeOfRings {C : Type u₁} [Category.{v₁} C]
    {R R' : Cᵒᵖ ⥤ CommRingCat.{u}} (α : R ⟶ R') :
    extendScalars.{u} α ≅ Stacks.PresheafOfModules.ChangeOfRings.changeOfRings α :=
  Adjunction.leftAdjointUniq (extendScalarsAdjunction α)
    (Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction α)

end Stacks.PullbackModel

end
