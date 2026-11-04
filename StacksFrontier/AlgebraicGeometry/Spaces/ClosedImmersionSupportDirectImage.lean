module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionGeometricLength
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportGeometricStalkCriterion

/-!
# The support of the direct image of a module along a closed immersion of algebraic spaces

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S` contained in a big
fppf site `B` and let `G` be an `𝒪_Z`-module. The stalk of the direct image `i_*G` at the image
`i(z̄)` of a geometric point `z̄` of `Z` is the stalk of `G` at `z̄`
(`AlgebraicGeometry.Space.geometricStalkPushforwardAddEquiv`), so one vanishes exactly when the
other does. For quasi-coherent `G` and `i_*G`, Stacks 07TZ reads the support of Stacks 04KA off
the stalk at any geometric point above a given point, and so

`Supp(i_*G) ∩ |i|(|Z|) = |i|(Supp(G))`.

The direct image is `AlgebraicGeometry.Space.chartDirectImage`
(`AlgebraicGeometry.Space.smallBaseChangeModulePushforward`), the direct image of modules along
base change of étale scheme charts; it is not identified here with
`AlgebraicGeometry.Space.modulePushforward`, the direct image of Stacks 03LU.

## Main results

* `AlgebraicGeometry.Space.nontrivial_geometricModuleStalk_chartDirectImage_iff`: the stalk of
  `i_*G` at `i(z̄)` is nonzero exactly when the stalk of `G` at `z̄` is.
* `AlgebraicGeometry.Space.mem_supportOfSheaf_chartDirectImage_iff`: at a geometric point of
  `Z`, membership of `i(z̄)` in `Supp(i_*G)` is membership of `z̄` in `Supp(G)`.
* `AlgebraicGeometry.Space.image_supportOfSheaf_subset_supportOfSheaf_chartDirectImage`:
  `|i|(Supp(G)) ⊆ Supp(i_*G)`.
* `AlgebraicGeometry.Space.supportOfSheaf_chartDirectImage_inter_range`: the support of `i_*G`
  meets the image of `|Z|` exactly in the image of the support of `G`.

## References

* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 04KB](https://stacks.math.columbia.edu/tag/04KB)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
* [Stacks Project, Tag 0EE3](https://stacks.math.columbia.edu/tag/0EE3)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Z X : AlgebraicSpaces B S hS}

/-- For a closed immersion `i : Z ⟶ X` of algebraic spaces, an `𝒪_Z`-module `G` and a geometric
point `z̄` of `Z`, the stalk of `i_*G` at `i(z̄)` is nonzero exactly when the stalk of `G` at `z̄`
is. -/
theorem nontrivial_geometricModuleStalk_chartDirectImage_iff (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (G : Modules.{u, m} B S hS Z.1 Z.2)
    (zbar : GeometricPoint B S hS Z.1) :
    Nontrivial (geometricModuleStalk B S hS X (geometricPointMap i.hom zbar)
        (chartDirectImage B S hS i hi G)) ↔
      Nontrivial (geometricModuleStalk B S hS Z zbar G) :=
  (geometricStalkPushforwardAddEquiv B S hS i hi zbar G).toEquiv.nontrivial_congr

/-- For a closed immersion `i : Z ⟶ X` and a quasi-coherent `𝒪_Z`-module `G` with quasi-coherent
direct image, the image `i(z̄)` of a geometric point `z̄` of `Z` lies in `Supp(i_*G)` exactly when
`z̄` lies in `Supp(G)`. -/
theorem mem_supportOfSheaf_chartDirectImage_iff (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (G : Modules.{u, u} B S hS Z.1 Z.2)
    [G.IsQuasicoherentOnSite]
    [(chartDirectImage B S hS i hi G).IsQuasicoherentOnSite]
    (zbar : GeometricPoint B S hS Z.1) :
    (geometricPointMap i.hom zbar).image ∈ supportOfSheaf B S hS X.1
        ((SheafOfModules.toSheaf _).obj (chartDirectImage B S hS i hi G)) ↔
      zbar.image ∈ supportOfSheaf B S hS Z.1 ((SheafOfModules.toSheaf _).obj G) := by
  rw [mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk_of_liesOver B S hS X
      (chartDirectImage B S hS i hi G) (geometricPointMap i.hom zbar) _ rfl,
    mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk_of_liesOver B S hS Z G zbar _ rfl]
  exact nontrivial_geometricModuleStalk_chartDirectImage_iff B S hS i hi G zbar

/-- For a closed immersion `i : Z ⟶ X` and a quasi-coherent `𝒪_Z`-module `G` with quasi-coherent
direct image, `|i|(Supp(G)) ⊆ Supp(i_*G)`. -/
theorem image_supportOfSheaf_subset_supportOfSheaf_chartDirectImage (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (G : Modules.{u, u} B S hS Z.1 Z.2)
    [G.IsQuasicoherentOnSite]
    [(chartDirectImage B S hS i hi G).IsQuasicoherentOnSite] :
    pointsMap B S hS Z.1 i.hom '' supportOfSheaf B S hS Z.1
        ((SheafOfModules.toSheaf _).obj G) ⊆
      supportOfSheaf B S hS X.1
        ((SheafOfModules.toSheaf _).obj (chartDirectImage B S hS i hi G)) := by
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨zbar, hzbar⟩ := exists_geometricRepresentative B S hS Z.1 x
  subst hzbar
  exact (mem_supportOfSheaf_chartDirectImage_iff B S hS i hi G zbar).2 hx

/-- For a closed immersion `i : Z ⟶ X` and a quasi-coherent `𝒪_Z`-module `G` with quasi-coherent
direct image, `Supp(i_*G) ∩ |i|(|Z|) = |i|(Supp(G))`. -/
theorem supportOfSheaf_chartDirectImage_inter_range (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (G : Modules.{u, u} B S hS Z.1 Z.2)
    [G.IsQuasicoherentOnSite]
    [(chartDirectImage B S hS i hi G).IsQuasicoherentOnSite] :
    supportOfSheaf B S hS X.1
          ((SheafOfModules.toSheaf _).obj (chartDirectImage B S hS i hi G)) ∩
        Set.range (pointsMap B S hS Z.1 i.hom) =
      pointsMap B S hS Z.1 i.hom '' supportOfSheaf B S hS Z.1
        ((SheafOfModules.toSheaf _).obj G) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro y ⟨hy, x, rfl⟩
    obtain ⟨zbar, hzbar⟩ := exists_geometricRepresentative B S hS Z.1 x
    subst hzbar
    exact ⟨zbar.image, (mem_supportOfSheaf_chartDirectImage_iff B S hS i hi G zbar).1 hy, rfl⟩
  · exact Set.subset_inter
      (image_supportOfSheaf_subset_supportOfSheaf_chartDirectImage B S hS i hi G)
      (Set.image_subset_range _ _)

end AlgebraicGeometry.Space

end
