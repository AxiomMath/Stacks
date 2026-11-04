module

public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.AbelianHigherDirectImageSheafification
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.AcyclicityReduction

/-!
# The derived clause of Stacks 0DCU from a comparison of cohomology presheaves

Let `f : X ⟶ Y` be a proper map and `J` an injective abelian sheaf on the small Zariski site of
`X`. For `i > 0`, `R^i f_{Zar,*}(π_X^{-1} J)` is the sheafification of the presheaf
`Z ↦ H^i(Z ×_Y X, π_X^{-1} J)` on the big site over `Y` ([Stacks, Tag 072W]), and the
sheafification of a higher cohomology presheaf `Z ↦ H^i(Z, G)` of the big site over `Y` is zero
([Stacks, Tag 01FW]). So `R^i f_{Zar,*}(π_X^{-1} J)` vanishes as soon as the first presheaf is
isomorphic to one of the second kind, and then the derived Zariski base-change comparison map of
[Stacks, Tag 0DCU] is invertible.

## Main results

* `isIso_properDerivedImageComparison_of_cohomologyPresheafIso`, in the namespace
  `Stacks.Topology.LocallyQuasiCompactZariskiSituation`: for a proper map, the derived Zariski
  base-change comparison map is invertible as soon as, for every injective `J` and every `p > 0`,
  the `p`-th cohomology presheaf of `π_X^{-1} J` for the morphism of sites `f_{Zar}` is isomorphic
  to the `p`-th cohomology presheaf of some abelian sheaf on the big site over `Y`.

## References

* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 01FW](https://stacks.math.columbia.edu/tag/01FW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.SheafifiedHigherDirectImage

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w v

attribute [local instance] HasDerivedCategory.standard

-- The cheap instance for `HasPointwiseRightDerivedFunctor` on `K⁺` has to be given precedence,
-- or synthesis tries to prove termwise injectivity of an unknown complex and times out.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X Y : S.category} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v})]
  [EnoughInjectives (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})]
  [EnoughInjectives (Sheaf (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v})]

/-- Let `f : X ⟶ Y` be proper. The derived Zariski base-change comparison map of `f` is invertible
as soon as, for every injective abelian sheaf `J` on the small Zariski site of `X` and every
`p > 0`, the `p`-th cohomology presheaf `Z ↦ H^p(Z ×_Y X, π_X^{-1} J)` of the morphism of sites
`f_{Zar}` is isomorphic to the `p`-th cohomology presheaf `Z ↦ H^p(Z, G)` of some abelian sheaf
`G` on the big site over `Y`. -/
theorem isIso_properDerivedImageComparison_of_cohomologyPresheafIso
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u}
      (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) : X.obj → Y.obj))
    (hcoh : ∀ J : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v},
      Injective J → ∀ p : ℕ, 0 < p →
        ∃ G : Sheaf (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v},
          Nonempty
            (((pushforwardCohomologyPresheaf AddCommGrpCat.{max (u + 1) v}
                  (Over.pullback f)).rightDerived p).obj
                ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj J) ≅
              (((sheafToPresheaf (S.zariskiTopology.over Y)
                  AddCommGrpCat.{max (u + 1) v}).rightDerived p).obj G))) :
    IsIso (properDerivedImageComparison.{u, w, v} S f) := by
  refine isIso_properDerivedImageComparison_of_isZero_rightDerivedPlus.{u, w, v} S f hf
    fun J hJ i hi => ?_
  obtain ⟨p, hp⟩ : ∃ p : ℕ, i = (p : ℤ) := ⟨i.toNat, (Int.toNat_of_nonneg hi.le).symm⟩
  have hp0 : 0 < p := by lia
  obtain ⟨G, ⟨e⟩⟩ := hcoh J hJ p hp0
  rw [Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff _ hp]
  exact isZero_rightDerived_pushforward_of_cohomologyPresheafIso
    AddCommGrpCat.{max (u + 1) v} (Over.pullback f) p hp0 _ G e

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
