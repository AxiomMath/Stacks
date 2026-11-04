module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedToposColimit
public import StacksCore.Tactic.StacksAttribute

/-!
# Direct sums and filtered colimits of good differential graded modules

Let `Y` be a ringed topos and let `A` be a sheaf of differential graded `O_Y`-algebras on it. **An
arbitrary direct sum of good right differential graded `A`-modules is good, and a filtered colimit
of good right differential graded `A`-modules is good**, goodness being
`SheafOfModules.IsGoodToposBaseChange` — Tag 0FSA, with condition (3) read over the source's own
base changes, the morphisms of ringed topoi.

## Main results

* `SheafOfModules.isGoodToposBaseChange_of_isColimitCofan`: **an arbitrary direct sum of good
  right differential graded modules is good.**
* `SheafOfModules.isGoodToposBaseChange_of_isColimit_isFiltered`: **a filtered colimit of good
  right differential graded modules is good.**

## Implementation notes

The index type of the direct sum and the index category of the filtered colimit lie in the module
universe `w`, which is where the relative tensor product commutes with colimits. No pullback
functor is assumed: condition (3) of `SheafOfModules.IsGoodToposBaseChange` asserts that a
pullback exists, as an object corepresenting `Q ↦ Hom_A(P, f_{*,ψ}Q)`.

## References

* [Stacks Project, Tag 0FSD](https://stacks.math.columbia.edu/tag/0FSD)
* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe w v₁ u₁ v₂ u₂

namespace SheafOfModules

open DifferentialGradedModule

variable {Y : AlgebraicGeometry.RingedTopos.{v₂, u₂, w}}
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  [HasSheafify Y.J (Type w)]
  {A : DifferentialGradedAlgebra.{w, w} (toRingCat Y.J Y.O)}

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

/-- **An arbitrary direct sum of good right differential graded modules is good**, goodness being
`SheafOfModules.IsGoodToposBaseChange`: conditions (1) and (2) of Tag 0FSA together with
condition (3) read over the morphisms of ringed topoi out of the base. -/
@[stacks 0FSD]
theorem isGoodToposBaseChange_of_isColimitCofan {ι : Type w}
    {P : ι → DifferentialGradedModule.{w, w, w} A} {c : Cofan P} (hc : IsColimit c)
    (hP : ∀ i, IsGoodToposBaseChange.{w, v₁, u₁} (P i)) :
    IsGoodToposBaseChange.{w, v₁, u₁} c.pt := by
  have := ab4OfSize.{w, w} (toRingCat Y.J Y.O)
  exact isGoodToposBaseChange_of_isColimit
    (fun X _ _ _ ↦ by have := ab4OfSize.{w, w} (toRingCat X.J X.O); infer_instance)
    hc fun i ↦ hP i.as

/-- **A filtered colimit of good right differential graded modules is good**, goodness being
`SheafOfModules.IsGoodToposBaseChange`. -/
@[stacks 0FSD]
theorem isGoodToposBaseChange_of_isColimit_isFiltered {D : Type w} [SmallCategory D]
    [IsFiltered D] {K : D ⥤ DifferentialGradedModule.{w, w, w} A} {c : Cocone K}
    (hc : IsColimit c) (hK : ∀ d : D, IsGoodToposBaseChange.{w, v₁, u₁} (K.obj d)) :
    IsGoodToposBaseChange.{w, v₁, u₁} c.pt :=
  isGoodToposBaseChange_of_isColimit (fun _ ↦ inferInstance) hc hK

end SheafOfModules

end
