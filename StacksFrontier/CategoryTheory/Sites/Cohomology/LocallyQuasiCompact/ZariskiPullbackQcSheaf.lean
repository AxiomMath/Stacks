module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiComparisonSituationData
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.AbelianProperDirectImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.QcComparisonNaturality
import StacksCore.Tactic.StacksAttribute

/-!
# The sheaves pulled back from the space satisfy the quasi-compact sheaf condition

Over an object `X` of the locally quasi-compact Zariski site, the class of abelian sheaves
distinguished by Stacks 0EZI is the class of those of the form `π_X^{-1}G` for `G` an abelian
sheaf on the space `X`. This file proves that such a sheaf, a sheaf for the Zariski topology by
construction, is already a sheaf for the finer quasi-compact topology — equivalently that the unit
`F' → ε_{X,*}ε_X^{-1}F'` of the comparison of the two topologies is an isomorphism on it.

## Main results

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.zariskiPullbackClass_isSheaf_qc`: a sheaf
  pulled back from the space is a sheaf for the quasi-compact topology.

## Implementation notes

The coefficients are `AddCommGrpCat.{max (u + 1) v}`, the universe at which the abelian
comparison adjunction exists.

## References

* [Stacks Project, Tag 0EZI](https://stacks.math.columbia.edu/tag/0EZI)
* [Stacks Project, Tag 0EZ3](https://stacks.math.columbia.edu/tag/0EZ3)
* [Stacks Project, Tag 09X3](https://stacks.math.columbia.edu/tag/09X3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w v

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}

/-- An abelian sheaf on the localized Zariski site over `X` which is pulled back from the space `X`
is already a sheaf for the quasi-compact topology: `F' = ε_{X,*}ε_X^{-1}F'`. -/
@[stacks 0EZI "condition (0EZ6) of Situation 0EZ3 for the sheaves pulled back from the space"]
theorem zariskiPullbackClass_isSheaf_qc
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category)
    (F : Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})
    (hF : S.zariskiPullbackClass.{u, w, v} X F) :
    Presheaf.IsSheaf (S.qcSite.grothendieckTopology.over X) F.obj := by
  rw [zariskiPullbackClass, ObjectProperty.prop_map_iff] at hF
  obtain ⟨G, -, ⟨e⟩⟩ := hF
  refine (Presheaf.isSheaf_of_iso_iff ((sheafToPresheaf (S.zariskiTopology.over X)
    AddCommGrpCat.{max (u + 1) v}).mapIso e)).mp ?_
  refine (Presheaf.isSheaf_iff_isSheaf_comp (S.qcSite.grothendieckTopology.over X)
    ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj G).obj
    (forget AddCommGrpCat.{max (u + 1) v})).mpr ?_
  refine (Presheaf.isSheaf_of_iso_iff ((sheafToPresheaf (S.zariskiTopology.over X)
    (Type (max (u + 1) v))).mapIso
      ((abelianComparisonInverseImageForgetIso.{u, w, v} S X).app G))).mpr ?_
  exact isSheaf_qc_comparisonInverseImage.{u, w, max (u + 1) v} S X _

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end

