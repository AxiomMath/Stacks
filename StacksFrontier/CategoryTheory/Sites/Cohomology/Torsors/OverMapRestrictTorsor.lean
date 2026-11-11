module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackTrivialActionClass

/-!
# Restricting a torsor along a morphism of localized sites

For a morphism `f : X ⟶ Y` of a site `(C, J)` and a torsor `P` under an abelian sheaf `H` on the
site localized at `Y`, the sections of `P` over the objects `f_* W`, for `W` over `X`, form a
torsor under the restriction `f^* H` of `H` to the site localized at `X`. Its class is the
restriction along `f` of the class of `P`.

## Main definitions

* `Stacks.Cohomology.Torsors.AbelianTorsor.overMapRestrict`: the restriction of a torsor along
  `CategoryTheory.Over.map f`.

## Main results

* `Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1_overMapRestrict`: the class of the
  restricted torsor is the restriction of the class
  (`Stacks.Cohomology.Torsors.overMapH1Restrict`).

## References

* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w t v u

namespace Stacks.Cohomology.Torsors

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {X Y : C} (f : X ⟶ Y)

/-- **The restriction of a torsor along a morphism of localized sites.** For `f : X ⟶ Y` and a
torsor `P` under an abelian sheaf `H` on the site localized at `Y`, the torsor under `f^* H` on
the site localized at `X` whose sections over `W` are the sections of `P` over `f_* W`. It is
locally nonempty because `CategoryTheory.Over.map f` is cocontinuous. -/
def AbelianTorsor.overMapRestrict {H : Sheaf (J.over Y) AddCommGrpCat.{t}}
    (P : AbelianTorsor H) : AbelianTorsor ((J.overMapPullback AddCommGrpCat.{t} f).obj H) :=
  ⟨{ presheaf := (Over.map f).op ⋙ P.1.presheaf
     isSheaf := (Over.map f).op_comp_isSheaf_of_isSheaf (J.over X) (J.over Y) P.1.presheaf
       P.1.isSheaf
     act := fun U g s => P.1.act ((Over.map f).op.obj U) g s
     one_act := fun U s => P.1.one_act ((Over.map f).op.obj U) s
     mul_act := fun U g h s => P.1.mul_act ((Over.map f).op.obj U) g h s
     naturality := fun g a s => P.1.naturality ((Over.map f).op.map g) a s
     simplyTransitive := fun U h s t => P.1.simplyTransitive ((Over.map f).op.obj U) h s t },
    fun U => by
      obtain ⟨S, hS, hne⟩ := P.2 ((Over.map f).obj U)
      exact ⟨S.functorPullback (Over.map f), (Over.map f).cover_lift (J.over X) (J.over Y) hS,
        fun V g hg => hne hg⟩⟩

/-- The sections of the restricted torsor over `W` are the sections of the torsor over
`f_* W`. -/
theorem AbelianTorsor.overMapRestrict_presheaf {H : Sheaf (J.over Y) AddCommGrpCat.{t}}
    (P : AbelianTorsor H) : (P.overMapRestrict J f).1.presheaf = (Over.map f).op ⋙ P.1.presheaf :=
  rfl

variable [HasSheafify (J.over X) AddCommGrpCat.{t}] [HasSheafify (J.over Y) AddCommGrpCat.{t}]
  [HasExt.{w} (Sheaf (J.over X) AddCommGrpCat.{t})]
  [HasExt.{w} (Sheaf (J.over Y) AddCommGrpCat.{t})]
  [PreservesFiniteColimits (J.overMapPullback AddCommGrpCat.{t} f)]

/-- **The class of a restricted torsor is the restricted class**: the restriction map
`Stacks.Cohomology.Torsors.overMapH1Restrict` along `f` carries the class of a torsor `P` to the
class of `Stacks.Cohomology.Torsors.AbelianTorsor.overMapRestrict`. -/
theorem torsorIsoClassesEquivH1_overMapRestrict (H : Sheaf (J.over Y) AddCommGrpCat.{t})
    (P : AbelianTorsor H) :
    torsorIsoClassesEquivH1 _ (Quotient.mk (torsorSetoid _) (P.overMapRestrict J f)) =
      overMapH1Restrict J f H 1 (torsorIsoClassesEquivH1 H (Quotient.mk (torsorSetoid H) P)) :=
  torsorIsoClassesEquivH1_eq_overMapH1Restrict J f H P _ (𝟙 _)
    (fun _ => Function.bijective_id) (fun _ _ _ => rfl)

end Stacks.Cohomology.Torsors

end
