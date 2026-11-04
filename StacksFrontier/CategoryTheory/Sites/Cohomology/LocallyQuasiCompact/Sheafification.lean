module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiSite

/-!
# Sheafification on the Zariski sites of a locally quasi-compact situation

Both sites attached to an object `X` of a locally quasi-compact Zariski situation — the small site
`Opens X.obj` and the big slice site `LC_Zar / X` — admit sheafification for abelian groups in the
situation's coefficient universe.

## Main results

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.hasSheafify_zariskiOver`: the big slice
  site admits sheafification.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.hasSheafify_opens`: the small site admits
  sheafification.

## References

* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Stacks.Topology

universe u w v

namespace LocallyQuasiCompactZariskiSituation

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}

/-- The big Zariski site over an object of the situation admits sheafification for abelian groups
in the situation's coefficient universe. -/
public instance hasSheafify_zariskiOver
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v} := by
  let : ∀ Y : Over X, Small.{max (u + 1) v} ((S.zariskiTopology.over X).Cover Y)ᵒᵖ :=
    fun Y ↦ small_lift.{u + 1, v, u + 1} ((S.zariskiTopology.over X).Cover Y)ᵒᵖ
  let : ∀ α : Type (max (u + 1) v), Small.{max (u + 1) v} α := fun α ↦ small_self α
  let : PreservesLimits (forget AddCommGrpCat.{max (u + 1) v}) :=
    AddCommGrpCat.forget_preservesLimits
  let : PreservesFilteredColimitsOfSize.{u + 1, u + 1}
      (forget AddCommGrpCat.{max (u + 1) v}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max (u + 1) v, max (u + 1) v, u + 1, u + 1} _
  let : ∀ Y : Over X, PreservesColimitsOfShape
      ((S.zariskiTopology.over X).Cover Y)ᵒᵖ (forget AddCommGrpCat.{max (u + 1) v}) :=
    fun _ ↦ inferInstance
  infer_instance

/-- The small Zariski site of an object of the situation admits sheafification for abelian groups
in the situation's coefficient universe. -/
public instance hasSheafify_opens
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v} := by
  let : ∀ U : Opens X.obj,
      Small.{max (u + 1) v} ((Opens.grothendieckTopology X.obj).Cover U)ᵒᵖ :=
    fun U ↦ small_lift.{u, u, max (u + 1) v}
      ((Opens.grothendieckTopology X.obj).Cover U)ᵒᵖ
  let : PreservesLimits (forget AddCommGrpCat.{max (u + 1) v}) :=
    AddCommGrpCat.forget_preservesLimits
  let : PreservesFilteredColimitsOfSize.{u, u}
      (forget AddCommGrpCat.{max (u + 1) v}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max (u + 1) v, max (u + 1) v, u, u} _
  let : ∀ U : Opens X.obj, PreservesColimitsOfShape
      ((Opens.grothendieckTopology X.obj).Cover U)ᵒᵖ (forget AddCommGrpCat.{max (u + 1) v}) :=
    fun _ ↦ inferInstance
  infer_instance

end LocallyQuasiCompactZariskiSituation

end Stacks.Topology

end
