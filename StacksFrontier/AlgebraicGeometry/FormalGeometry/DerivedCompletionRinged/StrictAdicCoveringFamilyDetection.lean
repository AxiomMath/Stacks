module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.StrictAdicRestrictionToAnOpen
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.QuasiIsomorphismLocality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionDerivedProducts

/-!
# The comparison map `K̃ ⟶ R lim (K̃ ⊗_𝒪 𝒪/ℐⁿ⁺¹)` is invertible when it is so on a covering family

Let `(𝒞, 𝒪)` be a ringed site, `ℐ ⊂ 𝒪` a sheaf of ideals and `K̃` a complex of sheaves of
modules. `AlgebraicGeometry.RingedSite.quasiIso_strictAdicComparison_of_forall_restrict` reduces
invertibility of the comparison map `AlgebraicGeometry.RingedSite.strictAdicComparison` to the
same assertion on the slice site over each member of a family `V : ι → 𝒞`, modulo two
hypotheses that are not about the cone:

* `hpc`, that each restriction `-|_{V i}` preserves the countable product of the terms of the
  strictified adic quotient tower, and
* `hdetect`, that the restrictions jointly detect quasi-isomorphisms out of `K̃`.

This file discharges both and states the conclusion for a family covering the final object. The
result carries **no quasi-compactness and no global generation**: the only hypothesis is
`CategoryTheory.GrothendieckTopology.CoversTop`, and only
`CategoryTheory.Limits.HasProductsOfShape ℕ` is used — no exactness of countable products
anywhere.

## Implementation notes

`hdetect` is `Stacks.SheafOfModules.quasiIso_of_coversTop` ([Stacks, Tag 01SB]): a morphism of
complexes of sheaves of modules whose degreewise restriction to the slice over each member of a
covering family is a quasi-isomorphism is one. Its restriction functor is
`SheafOfModules.overFunctor`, which is what `AlgebraicGeometry.RingedSite.restrictModulesToSlice`
is an abbreviation for, so it applies directly.

`hpc` comes from `Stacks.Cohomology.Localization.preservesProducts_overFunctor`: restriction to a
slice preserves countable products, by right adjointness of restriction against extension by
zero ([Stacks, Tag 08FJ]). Three steps lead from that to the `IsIso` statement the Milnor
construction asks for: countable products of cochain complexes are
computed degreewise, so restriction of complexes preserves them, and
`Stacks.MilnorTower.towerProductComparison` is by definition
`CategoryTheory.Limits.piComparison` of the degreewise restriction, which a product-preserving
functor inverts.

Note that `AlgebraicGeometry.RingedSite.preservesProducts_mapDerivedCategory_overFunctor` is
*not* this statement: it is the same assertion about the induced functor on derived categories,
which is a strictly later consequence obtained through K-injective resolutions. The underived
statement below is the input to that one, not a corollary of it.

## Main results

* `AlgebraicGeometry.RingedSite.preservesProducts_restrictModulesToSlice`: restriction of sheaves
  of modules to a slice site preserves countable products.
* `AlgebraicGeometry.RingedSite.preservesProducts_restrictComplexes`: the same for the
  degreewise restriction of complexes.
* `AlgebraicGeometry.RingedSite.isIso_towerProductComparison_restrictModulesToSlice`: **`hpc`** —
  the product comparison map of restriction at any tower of complexes is invertible.
* `AlgebraicGeometry.RingedSite.quasiIso_strictAdicComparison_of_coversTop`: **invertibility of
  the comparison map of [Stacks, Tag 0A0K] part (1) on a covering family implies invertibility
  of the comparison map**, with no further hypothesis on the site, the ideal or the complex.

## References

* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
* [Stacks Project, Tag 0CQH](https://stacks.math.columbia.edu/tag/0CQH)
* [Stacks Project, Tag 08FJ](https://stacks.math.columbia.edu/tag/08FJ)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

/-! ### Restriction to an open preserves the countable products of the tower -/

section Products

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Restriction of sheaves of modules to a slice site preserves countable products.** This is
`Stacks.Cohomology.Localization.preservesProducts_overFunctor` — restriction is a right adjoint,
extension by zero along `Over.forget U` being a left adjoint of it ([Stacks, Tag 08FJ]) — stated
for the `AlgebraicGeometry.RingedSite.restrictModulesToSlice` spelling that the strict adic cone is
base-changed along. -/
theorem preservesProducts_restrictModulesToSlice :
    PreservesLimitsOfShape (Discrete ℕ) (restrictModulesToSlice X U) :=
  Stacks.Cohomology.Localization.preservesProducts_overFunctor X.J
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U

omit [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Degreewise restriction of complexes to a slice site preserves countable products.**
Products of cochain complexes are computed degreewise, so this is
`AlgebraicGeometry.RingedSite.preservesProducts_restrictModulesToSlice` in each degree. -/
theorem preservesProducts_restrictComplexes :
    PreservesLimitsOfShape (Discrete ℕ)
      ((restrictModulesToSlice X U).mapHomologicalComplex (ComplexShape.up ℤ)) :=
  let := preservesProducts_restrictModulesToSlice X U
  inferInstance

omit [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The hypothesis `hpc` of
`AlgebraicGeometry.RingedSite.quasiIso_strictAdicComparison_of_forall`, at restriction to an
open**: the canonical map from the restriction of the product of the terms of a tower to the
product of their restrictions is invertible.

`Stacks.MilnorTower.towerProductComparison` is by definition the
`CategoryTheory.Limits.piComparison` of the degreewise restriction functor at the family
`n ↦ F(n)`, and a functor preserving products of shape `Discrete ℕ` inverts it. -/
theorem isIso_towerProductComparison_restrictModulesToSlice
    (F : ℕᵒᵖ ⥤ CochainComplex (Modules X) ℤ) :
    IsIso (Stacks.MilnorTower.towerProductComparison (restrictModulesToSlice X U) F) :=
  let := preservesProducts_restrictComplexes X U
  inferInstance

end Products

/-! ### Invertibility of the comparison map on a covering family -/

section Cover

variable (X : RingedSite.{u, u, u})
  (I : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
  (Kt : CochainComplex (Modules X) ℤ) {ι : Type*} (V : ι → X.C)

/-- **The comparison map `K̃ ⟶ R lim (K̃ ⊗_𝒪 𝒪/ℐⁿ⁺¹)` of [Stacks, Tag 0A0K] part (1) is a
quasi-isomorphism as soon as it is one on each member of a family of objects covering the final
object of the site.**

This is `AlgebraicGeometry.RingedSite.quasiIso_strictAdicComparison_of_forall_restrict` with its
two remaining hypotheses discharged: `hpc` by
`AlgebraicGeometry.RingedSite.isIso_towerProductComparison_restrictModulesToSlice`, which holds
because restriction to a slice is a right adjoint ([Stacks, Tag 08FJ]), and `hdetect` by
`Stacks.SheafOfModules.quasiIso_of_coversTop`, which is locality of quasi-isomorphy ([Stacks,
Tag 01SB]).

The hypothesis `hlocal` is the same assertion one site down, by the identification of the base
change of the strict adic augmentation along restriction in
`StrictAdicRestrictionToAnOpen.lean`. There is no quasi-compactness hypothesis, no hypothesis
that `ℐ` be of finite type or globally generated, no K-flatness of `K̃` and no exactness of
countable products: the strict Milnor fibre and the comparison map out of it are formulas,
needing only `CategoryTheory.Limits.HasProductsOfShape ℕ` to be written down. -/
theorem quasiIso_strictAdicComparison_of_coversTop (hV : X.J.CoversTop V)
    (hlocal : ∀ i, QuasiIso (strictAdicComparison (X.over (V i)) (overIdeal I (V i))
      (restrictComplex X Kt (V i)))) :
    QuasiIso (strictAdicComparison X I Kt) :=
  quasiIso_strictAdicComparison_of_forall_restrict X I Kt V
    (fun i => isIso_towerProductComparison_restrictModulesToSlice X (V i)
      (strictAdicReductionTower X I Kt))
    (fun _ hf => Stacks.SheafOfModules.quasiIso_of_coversTop hV _ hf) hlocal

end Cover

end AlgebraicGeometry.RingedSite

end
