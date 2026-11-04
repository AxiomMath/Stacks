module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.RingedToposOfAMorphism
import StacksCore.Tactic.StacksAttribute

/-!
# The structure sheaf of the source in Situation 08PA is a restriction along `p'`

In Situation 08PA the source ringed topos carries, by
`Stacks.Sites.FibredCategory.MorphismSituation.sourceTopos_O`, the structure sheaf

`O_{C'} = (π')⁻¹ O_D`,

a *topos* inverse image: the sheaf obtained by transporting the ring operations of `O_D` along
the inverse-image functor of the geometric morphism `π'` of Stacks 06NW. Every later step of the
reduction of Stacks 08PC part (2) speaks instead of the *restriction* of `O_D` along the
continuous functor `p' : C' ⥤ D`, which is what
`Stacks.Sites.FibredCategory.MorphismSituation.overPullback_comp_sourceSliceProjection_eq`
localises. This file identifies the two.

The identification is `Stacks.Sheaves.ToposPullback.restrictionCommRingIso` at `π'`, and that it
applies here at all is the content: the inverse image of `π'` *is* restriction along `p'` by
`MorphismSituation.pi'_inverseImage`, so the transported ring operations are the original ones
read inside a sections functor, and the comparison is the identity on underlying sheaves of sets.
`MorphismSituation.restrictionRingIsoU` is the same comparison for the 1-morphism `u` rather than
for `p'`; the two are independent instances of one construction.

## Main definitions

* `Stacks.Sites.FibredCategory.MorphismSituation.sourceToposORestrictionIso`: the identification
  `(π')⁻¹O_D ≅ p'^{-1}O_D` of sheaves of commutative rings.
* `Stacks.Sites.FibredCategory.MorphismSituation.sourceStructureRingSheafRestrictionIso`: the
  same for the underlying sheaves of rings, which is the level `SheafOfModules` is taken over.
* `Stacks.Sites.FibredCategory.MorphismSituation.sourceStructureAbelianSheafRestrictionIso`: the
  same for the underlying abelian sheaves, which is the level the forgetful square of
  Stacks 08PC part (2) is phrased at.

## Main results

* `Stacks.Sites.FibredCategory.MorphismSituation.sourceToposORestrictionIso_hom_forget`: the
  identification is the identity on underlying sheaves of sets.

## Implementation notes

The two derived forms are obtained by applying `sheafCompose` to the commutative-ring one. That
their stated targets are the right objects at all is the `rfl` of
`CategoryTheory.Functor.sheafComposeSheafPushforwardIso`: restriction along a continuous functor
is postcomposition of underlying presheaves, so it commutes with a change of coefficient category
on the nose, and `sheafCompose J' G` applied to `p'^{-1}O_D` *is* `p'^{-1}` applied to
`sheafCompose J_D G` of `O_D`. No transport is needed, and in particular the abelian form needs
no comparison of `forget₂ RingCat AddCommGrpCat` with restriction beyond that definitional
equality.

## References

* [Stacks Project, Tag 06NW](https://stacks.math.columbia.edu/tag/06NW)
* [Stacks Project, Tag 08PA](https://stacks.math.columbia.edu/tag/08PA)
* [Stacks Project, Tag 08PC](https://stacks.math.columbia.edu/tag/08PC)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Stacks.Sites.FibredCategory.MorphismSituation

universe u₀ u₁ u₂ v₀ v₁ v₂ w

variable (S : MorphismSituation.{u₀, u₁, u₂, v₀, v₁, v₂, max w u₀ u₁ u₂ v₀ v₁ v₂})

/-- **The structure sheaf of the source ringed topos of Situation 08PA is the restriction of the
base structure sheaf along `p'`.** The source ringed topos carries `(π')⁻¹O_D`, the inverse image
of `O_D` along the geometric morphism `π'` of Stacks 06NW; since the inverse image of `π'` is
restriction along the continuous functor `p'` (`MorphismSituation.pi'_inverseImage`), the
transported ring structure is the original one and the comparison is the identity on sections.

This is `Stacks.Sheaves.ToposPullback.restrictionCommRingIso` at `π'`, with no hypothesis beyond
the situation's own data. -/
def sourceToposORestrictionIso :
    (S.sourceTopos S.pi').O ≅
      (S.p'.sheafPushforwardContinuous CommRingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
        S.sourceTopology S.base.J).obj S.base.O :=
  Stacks.Sheaves.ToposPullback.restrictionCommRingIso S.sourceTopology S.base.J S.p' S.base.O

/-- The identification of the source structure sheaf with a restriction is the identity on
underlying sheaves of sets. -/
@[simp]
theorem sourceToposORestrictionIso_hom_forget :
    (sheafCompose S.sourceTopology (forget CommRingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})).map
        S.sourceToposORestrictionIso.hom =
      𝟙 ((S.p'.sheafPushforwardContinuous (Type (max w u₀ u₁ u₂ v₀ v₁ v₂))
        S.sourceTopology S.base.J).obj
          ((sheafCompose S.base.J (forget CommRingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})).obj
            S.base.O)) :=
  rfl

/-- **The same identification on underlying sheaves of rings**, which is the level sheaves of
modules are taken over: the sheaf of rings underlying the structure sheaf of the source ringed
topos is the restriction along `p'` of the one underlying `O_D`. -/
def sourceStructureRingSheafRestrictionIso :
    Stacks.SheafOfModules.Tensor.ringSheaf (S.sourceTopos S.pi').O ≅
      (S.p'.sheafPushforwardContinuous RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
          S.sourceTopology S.base.J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf S.baseTopos.O) :=
  (sheafCompose S.sourceTopology
    (forget₂ CommRingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
      RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})).mapIso S.sourceToposORestrictionIso

/-- **The same identification on underlying abelian sheaves**, which is the level the forgetful
square of Stacks 08PC part (2) is phrased at: the abelian sheaf underlying `O_{C'}` is the
restriction along `p'` of the abelian sheaf underlying `O_D`. -/
def sourceStructureAbelianSheafRestrictionIso
    [S.sourceTopology.HasSheafCompose
      (forget₂ RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})]
    [S.base.J.HasSheafCompose
      (forget₂ RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})] :
    (sheafCompose S.sourceTopology
          (forget₂ RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
            AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (S.sourceTopos S.pi').O) ≅
      (S.p'.sheafPushforwardContinuous AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
          S.sourceTopology S.base.J).obj
        ((sheafCompose S.base.J
            (forget₂ RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
              AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})).obj
          (Stacks.SheafOfModules.Tensor.ringSheaf S.baseTopos.O)) :=
  (sheafCompose S.sourceTopology
    (forget₂ RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
      AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})).mapIso
    S.sourceStructureRingSheafRestrictionIso

end Stacks.Sites.FibredCategory.MorphismSituation

end
