module

public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedObjects
public import StacksFrontier.AlgebraicGeometry.QcohRestrictEquiv.IsoLocality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingSheafProductFactorLimit
public import StacksFrontier.AlgebraicGeometry.MeromorphicGenericPointDecomposition.Coproduct

/-!
# The coproduct of the factors of a product decomposition is the structure sheaf

Let `(X, 𝒪_X)` be a ringed space with a locally finite direct product decomposition
`𝒪_X = ∏_{n ∈ ℤ} 𝒪_n` of its structure sheaf, in the sense of
`Stacks.Cohomology.InvertibleDerived.ProductDecomposition`. Then the canonical morphism
`∐_n 𝒪_n ⟶ ∏_n 𝒪_n` of `𝒪_X`-modules is an isomorphism, and the product is the structure sheaf
itself, so that `∐_n 𝒪_n ≅ 𝒪_X`.

That identification is the third obligation of the implication `(2) ⟹ (1)` of Stacks 0FPG, and it
is complete here: the first half is `isIso_sigmaPiComparison_toOXMod_unit` and the second half is
`piIsoUnit`, their composite being `sigmaIsoUnit`.

## Main results

* `Stacks.Cohomology.InvertibleDerived.ProductDecomposition.isIso_sigmaPiComparison_toOXMod_unit`
  and the isomorphism `sigmaIsoPiToOXModUnit` it gives: `∐_n 𝒪_n ≅ ∏_n 𝒪_n`.
* `Stacks.Cohomology.InvertibleDerived.ProductDecomposition.piIsoUnit`: `∏_n 𝒪_n ≅ 𝒪_X`, with
  `piIsoUnit_inv_comp_π` identifying it by its composites with the product projections.
* `Stacks.Cohomology.InvertibleDerived.ProductDecomposition.sigmaIsoUnit`: the composite
  `∐_n 𝒪_n ≅ 𝒪_X`.

## Implementation notes

Being an isomorphism is local, so the comparison may be checked on a covering, and the covering
is the one the local finiteness of the decomposition supplies: near every point all but finitely
many of the `𝒪_n` have no sections, and a family of modules almost all of which are zero objects
has its coproduct equal to its product. The three generic inputs
(`CategoryTheory.Limits.isIso_sigmaPiComparison_of_isZero`,
`CategoryTheory.Limits.isIso_map_sigmaPiComparison` and
`Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_over`) are stated elsewhere; the only
new step is the vanishing of the restricted factor, which is
`Stacks.SheafOfModules.isZero_over_restrictScalars`.

The module docstring of `StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedObjects`
recorded two things as missing for this: that restriction preserve products of shape
`Discrete ℤ`, and that isomorphisms of `𝒪_X`-modules be detectable on an open covering. **Both
are available**, at the slice-site spelling rather than at `restrictModules`:
`SheafOfModules.preservesLimitOverFunctor` is the first (for every small shape, with no
hypothesis beyond those already in force) and
`Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_over` the second. That is why the
proof below restricts along `SheafOfModules.overFunctor` and not along
`AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules`.

The second half, `piIsoUnit`, uses none of that machinery: a product decomposition presents every
section of `𝒪_X` uniquely by its components, which is literally the universal property of the
product, so `𝒪_X` is exhibited as a limit fan of the factors and no comparison with the
categorical product `∏ᶜ` has to be computed. That argument is generic over a site and lives in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingSheafProductFactorLimit`. The same module
docstring of `InvertibleDerivedObjects` proposed instead to reflect the isomorphism along
`SheafOfModules.toSheaf`, which would additionally have needed that functor's comparison with
products.

Passing the product presentation to the generic results **by name** rather than leaving it to
unification is not optional: with `_` in its place, `piIsoUnit_inv_comp_π` below exhausts the
200000-heartbeat budget in a single `isDefEq`, while with the presentation named the whole file
checks in under three seconds.

This file is separate from `InvertibleDerivedObjects` because the generic comparison lemmas it
uses live in `StacksFrontier.AlgebraicGeometry.MeromorphicGenericPointDecomposition.Coproduct`,
whose import closure is much larger than that file's; nothing of the mathematics requires the
separation.

## References

* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG) — the implication
  `(2) ⟹ (1)`, whose proof uses this identification.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.Cohomology.InvertibleDerived.ProductDecomposition

variable {X : RingedSpace.{u, u}}

/-- **The coproduct of the factors of a locally finite product decomposition is their product.**

Being an isomorphism is local on `X`, and on a neighbourhood on which all but finitely many of
the factors have no sections all but finitely many of the restricted modules are zero objects,
for which the comparison from the coproduct to the product is invertible.

A step of the proof of the implication `(2) ⟹ (1)` of Stacks 0FPG, not a clause of the tag, so it
carries no `@[stacks]` attribute. -/
public theorem isIso_sigmaPiComparison_toOXMod_unit (D : ProductDecomposition X) :
    IsIso (sigmaPiComparison fun n : ℤ => (D.toOXMod n).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))) := by
  classical
  choose U hxU hfin using D.locallyFinite
  have hcover : (Opens.grothendieckTopology X.carrier).CoversTop U :=
    (Opens.coversTop_iff _ U).mpr
      (le_antisymm le_top fun x _ => Opens.mem_iSup.mpr ⟨x, hxU x⟩)
  refine Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_over hcover _ fun x => ?_
  have hz : ∀ n : ℤ, ¬ (¬ Subsingleton ((D.factor n).obj.obj (op (U x)))) →
      IsZero ((SheafOfModules.overFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) (U x)).obj
        ((D.toOXMod n).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))))) :=
    fun n hn =>
      Stacks.SheafOfModules.isZero_over_restrictScalars (D.proj n) _ (U x) (not_not.mp hn)
  let : Finite {n : ℤ // ¬ Subsingleton ((D.factor n).obj.obj (op (U x)))} :=
    (hfin x).to_subtype
  exact isIso_map_sigmaPiComparison _ _
    (isIso_sigmaPiComparison_of_isZero _
      (fun n : ℤ => ¬ Subsingleton ((D.factor n).obj.obj (op (U x)))) hz)

/-- The identification `∐_n 𝒪_n ≅ ∏_n 𝒪_n` of `isIso_sigmaPiComparison_toOXMod_unit`. -/
public def sigmaIsoPiToOXModUnit (D : ProductDecomposition X) :
    (∐ fun n : ℤ => (D.toOXMod n).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))) ≅
      ∏ᶜ fun n : ℤ => (D.toOXMod n).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))) :=
  have := D.isIso_sigmaPiComparison_toOXMod_unit
  asIso (sigmaPiComparison _)

/-- **The product of the factors of a product decomposition is the structure sheaf**:
`∏_n 𝒪_n ≅ 𝒪_X` as `𝒪_X`-modules.

This is the ringed-space reading of
`Stacks.SheafOfModules.RingSheafProductFactor.piIsoUnit`: the product presentation of `𝒪_X` that
`ProductDecomposition.iso` supplies exhibits `𝒪_X`, with the projections onto the factors, as a
limit fan of the family of factors, so it *is* their product.

The module docstring of `StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedObjects`
proposed to obtain this by reflecting the isomorphism along `SheafOfModules.toSheaf`, which would
have needed the comparison of that functor with products; no such comparison is used, because the
universal property is checked directly on sections, where a product presentation is by
definition a bijection.

The second half of the third obligation of the implication `(2) ⟹ (1)` of Stacks 0FPG, hence a
step of a proof and not a clause of the tag; it carries no `@[stacks]` attribute. -/
public def piIsoUnit (D : ProductDecomposition X) :
    (∏ᶜ fun n : ℤ => (D.toOXMod n).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) :=
  Stacks.SheafOfModules.RingSheafProductFactor.piIsoUnit
    (Stacks.SheafOfModules.RingSheafProductFactor.ProductPresentation.ofIso D.iso)

/-- **The coproduct of the factors of a product decomposition is the structure sheaf**:
`∐_n 𝒪_n ≅ 𝒪_X` as `𝒪_X`-modules. This is the third obligation of the implication `(2) ⟹ (1)` of
Stacks 0FPG in full, the composite of `sigmaIsoPiToOXModUnit` with `piIsoUnit`.

A step of the proof of an implication of Stacks 0FPG, not a clause of it, so it carries no
`@[stacks]` attribute. -/
public def sigmaIsoUnit (D : ProductDecomposition X) :
    (∐ fun n : ℤ => (D.toOXMod n).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) :=
  D.sigmaIsoPiToOXModUnit ≪≫ D.piIsoUnit

/-- The identification `∏_n 𝒪_n ≅ 𝒪_X` is the one carrying the `n`-th product projection to the
projection `𝒪_X ⟶ 𝒪_n` of the decomposition. This pins it down: it is not merely an abstract
isomorphism between the two objects. -/
public theorem piIsoUnit_inv_comp_π (D : ProductDecomposition X) (n : ℤ) :
    D.piIsoUnit.inv ≫ Pi.π (fun n : ℤ => (D.toOXMod n).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))) n =
      Stacks.SheafOfModules.RingSheafProductFactor.factorProjection
        (Stacks.SheafOfModules.RingSheafProductFactor.ProductPresentation.ofIso D.iso) n :=
  Stacks.SheafOfModules.RingSheafProductFactor.piIsoUnit_inv_comp_π
    (Stacks.SheafOfModules.RingSheafProductFactor.ProductPresentation.ofIso D.iso) n

end Stacks.Cohomology.InvertibleDerived.ProductDecomposition

end
