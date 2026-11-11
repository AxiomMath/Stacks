module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartStalkTensorIsomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportChartZariski

/-!
# The support of a quasi-coherent module is nonvanishing of the stalk at a geometric point

Let `X` be an algebraic space over a scheme `S` and let `F` be a quasi-coherent `𝒪_X`-module.
The support of `F` in the sense of Stacks 04KA is defined by nonvanishing of the stalk at
*some* geometric point over the given point of `X`.  For a quasi-coherent module the choice of
geometric point is immaterial: a point of `X` lies in the support exactly when the stalk of `F`
at *any* one geometric point over it is nonzero.  This is the first equivalence of Stacks 07TZ
part (2).

The passage from "some" to "any" is the comparison

`(φ^* F)_u ⊗_{𝒪_{U, u}} 𝒪_{X, x̄} ≅ F_{x̄}`

of Stacks 05VP along an étale neighbourhood `φ : (U, ū) → (X, x̄)` with `U` a scheme.  Through
that comparison nonvanishing of `F_{x̄}` is nonvanishing of the Zariski stalk of the chart
restriction of `F` at the point `u` under `x̄`, because the base change is along a faithfully
flat ring map; and nonvanishing of that Zariski stalk is membership of `u` in the support of
the chart restriction, which by Stacks 07TY is the inverse image of the support of `F`.  Since
`|φ|` carries `u` to the image of `x̄`, the resulting criterion no longer mentions the
neighbourhood, so it holds for every geometric point over the point.

The same comparison supplies the comparison hypothesis of
`AlgebraicGeometry.Space.supp_restrictToChart_eq_preimage_supportOfSheaf`, the support equality
for an arbitrary `𝒪_X`-module satisfying the comparison; for a quasi-coherent module, the
setting of Stacks 07TY, this gives the support equality of Stacks 07TY with no further
hypothesis.

## Main results

* `AlgebraicGeometry.Space.supp_restrictToChart_eq_preimage_supportOfSheaf_of_isQuasicoherent`
  is **Stacks 07TY** for a quasi-coherent module: the support of the restriction of `F` to an
  étale scheme chart is the inverse image of the support of `F`.
* `AlgebraicGeometry.Space.nontrivial_geometricModuleStalk_iff_mem_supp_restrictToChart`
  identifies nonvanishing of the stalk of a quasi-coherent module at a geometric point with
  membership of the chart point of any small étale neighbourhood in the support of the chart
  restriction.
* `AlgebraicGeometry.Space.mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk_of_liesOver`
  is the **first equivalence of Stacks 07TZ part (2)**: for a quasi-coherent module and a
  geometric point lying over a point of `X`, that point lies in the support exactly when the
  stalk at that geometric point is nonzero.

## Implementation notes

Stacks 05VP is available at module universe `m = u`, so the results below are stated for
`AlgebraicGeometry.Space.Modules.{u, u}`.

The second equivalence of Stacks 07TZ part (2), nonvanishing of the stalk against nonvanishing
of its fibre over the residue field of `𝒪_{X, x̄}`, is Nakayama's lemma and needs the stalk to
be a finite `𝒪_{X, x̄}`-module.  That finiteness is
`AlgebraicGeometry.Space.module_finite_geometricModuleStalk` and the equivalence is
`AlgebraicGeometry.Space.nontrivial_geometricModuleStalk_iff_nontrivial_residueFibre`; neither
is proved in this file, because both live in modules that import this one.

## References

* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
* [Stacks Project, Tag 07TY](https://stacks.math.columbia.edu/tag/07TY)
* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Stacks 07TY for a quasi-coherent module -/

/-- **Stacks 07TY.** Let `X` be an algebraic space over `S`, let `F` be a quasi-coherent
`𝒪_X`-module and let `φ : U ⟶ X` be an étale morphism from a scheme, that is, an object of the
small étale site of `X`.  Then the support of `φ^* F` as a module on the *scheme* `U` is the
inverse image under `|φ|` of the support of `F`:
`Supp(φ^* F) = |φ|^{-1}(Supp(F))`.

The proof is `AlgebraicGeometry.Space.supp_restrictToChart_eq_preimage_supportOfSheaf` with its
comparison `(φ^* F)_u ⊗_{𝒪_{U, u}} 𝒪_{X, x̄} ≅ F_{x̄}` supplied by Stacks 05VP,
`AlgebraicGeometry.Space.isIso_chartStalkTensorComparison`, which holds because `F` is
quasi-coherent. -/
@[stacks 07TY "the support of a quasi-coherent module pulled back along an étale chart"]
theorem supp_restrictToChart_eq_preimage_supportOfSheaf_of_isQuasicoherent
    (X : AlgebraicSpaces B S hS) (U : SmallEtale B S hS X.1)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] :
    SheafOfModules.supp (restrictToChart B S hS X.2 F U) =
      (fun u => pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U))
          U.obj.hom
          ((pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj U)).symm u)) ⁻¹'
        supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) :=
  supp_restrictToChart_eq_preimage_supportOfSheaf B S hS X U F
    (fun _ V => ⟨let := isIso_chartStalkTensorComparison B S hS X.2 V F
      asIso (chartStalkTensorComparison B S hS X.2 V F)⟩)

/-! ### The stalk at a geometric point against the support -/

/-- **The stalk of a quasi-coherent module at a geometric point is nonzero exactly when the
chart point of a small étale neighbourhood lies in the support of the chart restriction.**

This transports `AlgebraicGeometry.Space.nontrivial_chartStalkTensorEtaleLocalRing_iff_mem_supp`
along the comparison isomorphism of Stacks 05VP. -/
theorem nontrivial_geometricModuleStalk_iff_mem_supp_restrictToChart
    (X : AlgebraicSpaces B S hS) {x : GeometricPoint B S hS X.1}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] :
    Nontrivial (geometricModuleStalk B S hS X x F) ↔
      chartPoint B S hS X.1 V ∈
        SheafOfModules.supp (restrictToChart B S hS X.2 F V.chart) := by
  let _ := isIso_chartStalkTensorComparison B S hS X.2 V F
  refine Iff.trans ?_
    (nontrivial_chartStalkTensorEtaleLocalRing_iff_mem_supp B S hS X.1 X.2 V F)
  exact (Equiv.ofBijective _ (ConcreteCategory.bijective_of_isIso
    (chartStalkTensorComparison B S hS X.2 V F))).nontrivial_congr.symm

/-- **Stacks 07TZ, part (2), first equivalence.** Let `F` be a quasi-coherent `𝒪_X`-module on an
algebraic space `X` and let `x̄` be a geometric point lying over a point `x` of `X`.  Then

`x ∈ Supp(F) ↔ F_{x̄} ≠ 0`.

The support of Stacks 04KA is defined by nonvanishing of the stalk at some geometric point over
`x`; the content here is that for a quasi-coherent module every geometric point over `x`
detects the support, so the equivalence holds at the given `x̄`.

Pick a small étale neighbourhood of `x̄`.  Nonvanishing of `F_{x̄}` is membership of the chart
point in the support of the chart restriction, and that support is the inverse image of the
support of `F` by Stacks 07TY; the chart point maps to the image of `x̄`, which is `x`. -/
@[stacks 07TZ "part (2), first equivalence: the support against the stalk at a geometric point"]
theorem mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk_of_liesOver
    (X : AlgebraicSpaces B S hS) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] (x : GeometricPoint B S hS X.1)
    (pt : points B S hS X.1) (hx : x.LiesOver pt) :
    pt ∈ supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) ↔
      Nontrivial (geometricModuleStalk B S hS X x F) := by
  have := isCofiltered_smallEtaleNeighborhood B S hS X.1 X.2 x
  obtain ⟨V⟩ := (IsCofiltered.nonempty : Nonempty (SmallEtaleNeighborhood x))
  have hpt : pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V.chart))
      V.chart.obj.hom
      ((pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj V.chart)).symm
        (chartPoint B S hS X.1 V)) = pt := by
    have hsymm : (pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj V.chart)).symm
        (chartPoint B S hS X.1 V) = (neighborhoodPoint B S hS X.1 V).image :=
      (Equiv.symm_apply_eq _).2
        (chartPoint_ofChartGeometricPoint B S hS X V.chart
          (neighborhoodPoint B S hS X.1 V))
    rw [hsymm, neighborhoodPoint_image B S hS X.1 V]
    exact hx
  rw [nontrivial_geometricModuleStalk_iff_mem_supp_restrictToChart B S hS X V F,
    supp_restrictToChart_eq_preimage_supportOfSheaf_of_isQuasicoherent B S hS X V.chart F]
  exact Iff.of_eq (congrArg _ hpt.symm)

end AlgebraicGeometry.Space

end
