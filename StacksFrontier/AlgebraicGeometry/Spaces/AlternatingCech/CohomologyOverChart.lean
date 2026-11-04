module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.CohomologyOverQuotientSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.KoszulComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.CohomologyOfALocalizedSite

/-!
# Cohomology over an object of the spaces-étale site, and the column `p = 0` of the `E₁`-page

For an object `U` of the spaces-étale site, the site of elements of the representable is the
slice site `(C/U, J/U)`, with extension by zero
`AlgebraicGeometry.Space.SpacesEtale.extensionByZeroAdjunction`, and [Stacks, Tag 07A0] reads
`Ext^q(j_{U!} ℤ, ℱ) ≅ H^q(U, ℱ|_U)`. Since `K^0 = ∧^1 j_{U!} ℤ = j_{U!} ℤ`, this identifies the
column `p = 0` of the first page of the alternating Čech spectral sequence of [Stacks, Tag 0728]:

`Ext^q(K^0, ℱ) ≅ H^q(U, ℱ|_U)`.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.zExtExtensionByZeroConstantAddEquiv`:
  [Stacks, Tag 07A0] over an object of the spaces-étale site,
  `Ext^q(j_{U!} ℤ, ℱ) ≅ H^q(U, ℱ|_U)`.
* `AlgebraicGeometry.Space.SpacesEtale.zExtKoszulComplexXZeroAddEquiv`: the same read on `K^0`,
  which is the column `p = 0` of the `E₁`-page of [Stacks, Tag 0728].
* `AlgebraicGeometry.Space.SpacesEtale.isZero_zExt_koszulComplex_X_zero_of_subsingleton_sheafH`:
  its vanishing form, `Ext^q(K^0, ℱ) = 0` whenever `H^q(U, ℱ|_U) = 0`.

## Implementation notes

The comparisons are additive equivalences rather than isomorphisms in `AddCommGrpCat`:
`Abelian.zExt` of `K^p` lives in `Type (u + 2)` and `CategoryTheory.Sheaf.H` of the restricted
coefficients in `Type (u + 1)`, and the transport across the universe gap is
`Stacks.Cohomology.SimplicialComponent.extChgUnivAddEquiv`.

## Remark

For a general abelian sheaf `ℱ` on the spaces-étale site, `H^q(U, ℱ|_U)` need not vanish for
`q > 0`, even for an affine chart `U`. Take `k` a field that is not separably closed,
`X := Spec k` as an algebraic space over `S := Spec k`, and the identity chart, which is affine,
surjective, étale and separated with universally bounded fibres. The slice site at the final
object is the spaces-étale site of `Spec k` itself, equivalent by [Stacks, Tag 03G1] to its small
étale site, so `H^q(U, ℱ|_U)` is Galois cohomology; for `k = 𝔽_q` and `ℱ` a constant sheaf `ℤ/n`
it is nonzero in degree one. In [Stacks, Tag 072B] the rows `q > 0` vanish by Serre vanishing
for quasi-coherent modules on an affine scheme ([Stacks, Tag 01XB], with [Stacks, Tag 072A] for
the quasi-coherence of `ℱ|_{U_p} ⊗_ℤ ℤ(χ_p)`).

## References

* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 072A](https://stacks.math.columbia.edu/tag/072A)
* [Stacks Project, Tag 072B](https://stacks.math.columbia.edu/tag/072B)
* [Stacks Project, Tag 0728](https://stacks.math.columbia.edu/tag/0728)
* [Stacks Project, Tag 07A0](https://stacks.math.columbia.edu/tag/07A0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.Space.SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- **[Stacks, Tag 07A0] over an object of the spaces-étale site, in the `Abelian.zExt`
spelling**: for an object `U` of the spaces-étale site of `X`, `Ext^p` out of `j_{U!} ℤ` is the
cohomology of the slice site `C/U` with coefficients in the restriction of `ℱ`.

This is `Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfAdjunction` at the
extension-by-zero adjunction `AlgebraicGeometry.Space.SpacesEtale.extensionByZeroAdjunction`,
applied to the constant sheaf `ℤ` on the slice, `Ext` out of which is sheaf cohomology of the
slice site by definition. It is the representable case of
`Stacks.Cohomology.SheafOfSets.cohomologyOnSheafIso`, and cheaper, the site of elements of a
representable being the slice site itself.

The universe gap is crossed exactly as in
`AlgebraicGeometry.Space.SpacesEtale.zExtFreeAbelianSheafOnAddEquiv`: `Abelian.zExt` is at the
`u + 2` of `CategoryTheory.HasDerivedCategory.standard` while the comparison lands at the
morphism universe `u + 1` of the sheaf category, and
`Stacks.Cohomology.SimplicialComponent.extChgUnivAddEquiv` crosses it additively. -/
def zExtExtensionByZeroConstantAddEquiv (U : SpacesEtale B S hS X)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) (p : ℕ) :
    Abelian.zExt (extensionByZeroConstant B S hS X U) F (p : ℤ) ≃+
      Sheaf.H.{u + 1, u + 1}
        (((topology B S hS X).overPullback AddCommGrpCat.{u + 1} U).obj F) p :=
  haveI := Stacks.Cohomology.LocalizedSite.preservesFiniteColimits_overPullback.{u + 1, u + 1,
    u + 1} (topology B S hS X) U
  haveI := Stacks.Cohomology.LocalizedSite.preservesInjectiveObjects_overPullback.{u + 1, u + 1,
    u + 1} (topology B S hS X) U
  haveI := (extensionByZeroAdjunction B S hS X U).left_adjoint_additive
  let e1 : Abelian.Ext.{u + 2} (extensionByZeroConstant B S hS X U) F p ≃+
      Abelian.zExt (extensionByZeroConstant B S hS X U) F (p : ℤ) :=
    Abelian.Ext.homAddEquiv
  let e2 : Abelian.Ext.{u + 2} (extensionByZeroConstant B S hS X U) F p ≃+
      Abelian.Ext.{u + 1} (extensionByZeroConstant B S hS X U) F p :=
    Stacks.Cohomology.SimplicialComponent.extChgUnivAddEquiv
  let e3 : Abelian.Ext.{u + 1} (extensionByZeroConstant B S hS X U) F p ≃+
      Sheaf.H.{u + 1, u + 1}
        (((topology B S hS X).overPullback AddCommGrpCat.{u + 1} U).obj F) p :=
    ((Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfAdjunction
      (extensionByZeroAdjunction B S hS X U)
      ((constantSheaf ((topology B S hS X).over U) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))) p).app F).addCommGroupIsoToAddEquiv
  e1.symm.trans (e2.trans e3)

/-- **The column `p = 0` of the first page of [Stacks, Tag 0728].** The term `K^0` of the Koszul
complex is `∧^1 j_{U!} ℤ = j_{U!} ℤ` by
`AlgebraicGeometry.Space.SpacesEtale.koszulComplexXZeroIso`, so `Ext^p` out of it is the
cohomology of the chart `U` with coefficients in the restriction of `ℱ`:
`Ext^p(K^0, ℱ) ≅ H^p(U, ℱ|_U)`. -/
def zExtKoszulComplexXZeroAddEquiv (U : SpacesEtale B S hS X)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) (p : ℕ) :
    Abelian.zExt ((koszulComplex B S hS X U).X 0) F (p : ℤ) ≃+
      Sheaf.H.{u + 1, u + 1}
        (((topology B S hS X).overPullback AddCommGrpCat.{u + 1} U).obj F) p :=
  haveI := Stacks.Cohomology.LocalizedSite.preservesFiniteColimits_overPullback.{u + 1, u + 1,
    u + 1} (topology B S hS X) U
  haveI := Stacks.Cohomology.LocalizedSite.preservesInjectiveObjects_overPullback.{u + 1, u + 1,
    u + 1} (topology B S hS X) U
  haveI := (extensionByZeroAdjunction B S hS X U).left_adjoint_additive
  let e1 : Abelian.Ext.{u + 2} ((koszulComplex B S hS X U).X 0) F p ≃+
      Abelian.zExt ((koszulComplex B S hS X U).X 0) F (p : ℤ) :=
    Abelian.Ext.homAddEquiv
  let e2 : Abelian.Ext.{u + 2} ((koszulComplex B S hS X U).X 0) F p ≃+
      Abelian.Ext.{u + 1} ((koszulComplex B S hS X U).X 0) F p :=
    Stacks.Cohomology.SimplicialComponent.extChgUnivAddEquiv
  let e3 : Abelian.Ext.{u + 1} ((koszulComplex B S hS X U).X 0) F p ≃+
      Sheaf.H.{u + 1, u + 1}
        (((topology B S hS X).overPullback AddCommGrpCat.{u + 1} U).obj F) p :=
    ((Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIso
      (extensionByZeroAdjunction B S hS X U)
      (koszulComplexXZeroIso B S hS X U).symm p).app F).addCommGroupIsoToAddEquiv
  e1.symm.trans (e2.trans e3)

/-- **The vanishing form of the column `p = 0`.** If the cohomology of the chart `U` with
coefficients in the restriction of `ℱ` vanishes in degree `p`, then so does `Ext^p(K^0, ℱ)`.
This is the shape the row hypothesis `hUpVanishing` of
`AlgebraicGeometry.Space.SpacesEtale.isZero_sheafH_of_isEmpty_diagonalComplement` and the column
hypothesis of `AlgebraicGeometry.Space.SpacesEtale.isZero_sheafH_of_zExt_column_bounds` consume
at `p = 0`. -/
theorem isZero_zExt_koszulComplex_X_zero_of_subsingleton_sheafH (U : SpacesEtale B S hS X)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) (p : ℕ)
    (h : Subsingleton (Sheaf.H.{u + 1, u + 1}
      (((topology B S hS X).overPullback AddCommGrpCat.{u + 1} U).obj F) p)) :
    IsZero (AddCommGrpCat.of
      (Abelian.zExt ((koszulComplex B S hS X U).X 0) F (p : ℤ))) := by
  have : Subsingleton (Abelian.zExt ((koszulComplex B S hS X U).X 0) F (p : ℤ)) :=
    (zExtKoszulComplexXZeroAddEquiv B S hS X U F p).toEquiv.subsingleton_congr.mpr h
  exact AddCommGrpCat.isZero_of_subsingleton _

end AlgebraicGeometry.Space.SpacesEtale

end
