module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingSheafProductFactorRetract
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSingleTensorIso
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorKFlatOneSided
public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedObjects

/-!
# The off-diagonal terms of the assembly of `(2) ⟹ (1)` for Stacks 0FPG

Let `(X, 𝒪_X)` be a ringed space with a locally finite direct product decomposition
`𝒪_X = ∏_{n ∈ ℤ} 𝒪_n` of its structure sheaf. The source's proof of the implication
`(2) ⟹ (1)` of Stacks 0FPG tensors `M = ⨁_n ℋ^n[-n]` against `N = ⨁_m (ℋ^m)^{-1}[m]`,
distributes `⊗^L` over the two direct sums, and kills every off-diagonal term `n ≠ m`. This file
provides that vanishing, for the modules the assembly actually meets.

The orthogonality already available
(`Stacks.Cohomology.InvertibleDerived.ProductDecomposition.isZero_tensor_toOXMod_unit` and its
derived form `isZero_derivedTensor_toOXMod_unit`) is the vanishing of `𝒪_n ⊗ 𝒪_m`, i.e. of the
tensor product of the two *factors*. The assembly's off-diagonal term is not that: it is
`ℋ^n ⊗ (ℋ^m)^{-1}`, the tensor product of an arbitrary `𝒪_n`-module with an arbitrary
`𝒪_m`-module, each read as an `𝒪_X`-module. The passage is not formal — a vanishing tensor
product of two modules says nothing about the tensor products of modules over them — but it is
free here, because the section of `𝒪_X` which does the killing depends only on the two ring
homomorphisms `𝒪_X(U) ⟶ 𝒪_n(U)` and `𝒪_X(U) ⟶ 𝒪_m(U)` and not on the modules: it is `1` in the
`n`-th component and `0` elsewhere, so it acts as the identity on the sections of *every*
`𝒪_n`-module and as zero on the sections of *every* `𝒪_m`-module. That observation is
`Stacks.SheafOfModules.RingSheafProductFactor.ProductPresentation`
`.exists_idempotentSection_restrictScalars`, and the two unit-module statements of the library are
now its specializations rather than independent proofs.

## Main results

* `Stacks.Cohomology.InvertibleDerived.ProductDecomposition.isZero_tensor_toOXMod`: for `n ≠ m`,
  an `𝒪_n`-module and an `𝒪_m`-module have vanishing tensor product over `𝒪_X`.
* `Stacks.Cohomology.InvertibleDerived.ProductDecomposition.isZero_derivedTensor_toOXMod` and
  `isZero_derivedTensor_toOXMod_right`: the same in `D(𝒪_X)`, for the derived tensor product of
  Stacks 0FPB, when *one* of the two modules is flat over `𝒪_X` — either one.
* `Stacks.Cohomology.InvertibleDerived.ProductDecomposition.isZero_derivedTensor_toOXMod_factor`
  and `isZero_derivedTensor_toOXMod_factor_right`: the derived vanishing **with no flatness
  hypothesis at all**, when the module on one side is the factor `𝒪_n` itself and the module on
  the other side is an arbitrary module over a different factor.
* `Stacks.Cohomology.InvertibleDerived.ProductDecomposition.nonempty_retract_tensor_toOXMod`: an
  `𝒪_n`-module is a retract of `𝒪_n ⊗_{𝒪_X}` itself in `Mod(𝒪_X)` — the sheaf-level statement
  that removes the flatness, and
  `Stacks.Cohomology.InvertibleDerived.ProductDecomposition.nonempty_retract_derivedTensor_toOXMod`
  its transport into `D(𝒪_X)`.
* `Stacks.Cohomology.InvertibleDerived.ProductDecomposition`
  `.isZero_derivedTensor_toOXMod_of_retract`: the derived vanishing for arbitrary modules over
  distinct factors **with no flatness hypothesis at all**, carrying the retract as an explicit
  hypothesis in `D(𝒪_X)`, and
  `Stacks.Cohomology.InvertibleDerived.ProductDecomposition.isZero_derivedTensor_toOXMod_of_ne`,
  **the same with that hypothesis discharged, so with no hypothesis at all** beyond `n ≠ m`.
  This last is what the assembly of `(2) ⟹ (1)` consumes.

## Implementation notes

**Where flatness entered, and why one hypothesis sufficed.** The vanishing of
the *total* tensor product of two modules placed in degree zero needs no flatness whatever
(`Stacks.SheafOfModules.DerivedMonoidal.isZero_tensorObj_single_of_isZero`); flatness entered
the derived statement only to make the K-flat comparison of the derived monoidal structure
applicable, and that comparison needs only *one* K-flat argument
(`CochainComplex.KFlatMonoidal.derivedTensorLeftKFlatIso`, in
`StacksFrontier/Topology/Sheaves/Cohomology/InternalHom/DerivedTensorKFlatOneSided.lean`). So the
derived statements here carry a single flatness hypothesis, on whichever side the caller can
discharge it, and when that side is the factor `𝒪_n` it is discharged outright by
`ProductDecomposition.isFlat_toOXMod_unit`.

**The flatness is gone, and not by flatness transitivity.** In the assembly of `(2) ⟹ (1)` the
two modules are `ℋ^n` and `(ℋ^m)^{-1}`, neither of them a factor, and neither is known flat over
`𝒪_X`: `Stacks.SheafOfModules.isFlat_of_isInvertible` gives flatness over `𝒪_n`, and composing
that with `ProductDecomposition.isFlat_toOXMod_unit` would need the transitivity of flatness
along a restriction of scalars for sheaves of modules, which is absent. That transitivity is *not*
the right thing to build, because the conclusion is true with no flatness at all: over orthogonal
factors the idempotent of `ProductPresentation.exists_idempotentSection_restrictScalars` kills
every `Tor`, not merely the tensor product. The route taken below is

* `𝒪_n ⊗^L_{𝒪_X} N = 0` for every module `N` over a different factor — that is
  `isZero_derivedTensor_toOXMod_factor`, **unconditional**; and
* `M` is a retract of `𝒪_n ⊗_{𝒪_X} M` in `Mod(𝒪_X)` for every `𝒪_n`-module `M`, which is the
  monoidal form of "the idempotent acts as the identity on an `𝒪_n`-module" — that is
  `nonempty_retract_tensor_toOXMod`, a statement purely about sheaves of modules, with no derived
  category and no flatness, whose content is the surjectivity of a product projection on sections
  (`ProductPresentation.surjective`), the same fact as the invertibility of
  `Stacks.SheafOfModules.TensorRestrictScalars.laxComparison` at a surjective ring map.

Given the second, `M ⊗^L N` is a retract of `M ⊗^L (𝒪_m ⊗^L N) ≅ (M ⊗^L 𝒪_m) ⊗^L N = 0`, and a
retract of a zero object is a zero object. That derivation is
`isZero_derivedTensor_toOXMod_of_retract`, which carries the retract as an explicit hypothesis in
`D(𝒪_X)`; the sheaf-level
retract is carried into `D(𝒪_X)` by `nonempty_retract_derivedTensor_toOXMod`, through the
transport `Stacks.Cohomology.MonoidalDerived.derivedTensorSingleIso` of
`StacksFrontier/Topology/Sheaves/Cohomology/InternalHom/DerivedSingleTensorIso.lean`
(`M[0] ⊗^𝐋 N[0] ≅ (M ⊗ N)[0]` for `M` flat, the flatness being that of the factor and hence
discharged by `isFlat_toOXMod_unit`); and the result is
`isZero_derivedTensor_toOXMod_of_ne`, **with no hypothesis beyond `n ≠ m`**.

The flatness-carrying statements `isZero_derivedTensor_toOXMod` and
`isZero_derivedTensor_toOXMod_right` are kept: they are the general one-sided form, applicable to
modules over the *same* factor, where the orthogonality argument is unavailable.

Nothing in this file is a clause of Stacks 0FPG; everything is a step of the proof of one of its
implications, so no declaration carries the project tag and the four existing attribute sites of
that tag are untouched.

## References

* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG) — the implication
  `(2) ⟹ (1)`, whose assembly consumes this vanishing.
* [Stacks Project, Tag 0FPB](https://stacks.math.columbia.edu/tag/0FPB) — the derived tensor
  product on `D(𝒪_X)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.SheafOfModules.DerivedMonoidal

universe u d

namespace Stacks.Cohomology.InvertibleDerived.ProductDecomposition

variable {X : RingedSpace.{u, u}}

/-- `Mod(𝒪_X)` has binary biproducts, as a lemma since instance search here is too expensive. -/
private theorem hasBinaryBiproducts_ringSheaf (X : RingedSpace.{u, u}) :
    HasBinaryBiproducts (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) :=
  inferInstanceAs (HasBinaryBiproducts (StrictlyPerfect.OXMod.{u, u} X))

/-- **The orthogonality of the factors, for arbitrary modules over them.** For `n ≠ m`, an
`𝒪_n`-module `L` and an `𝒪_m`-module `L'`, each read as an `𝒪_X`-module by restriction of scalars
along the projections of a product decomposition, have vanishing tensor product over `𝒪_X`.

Over each open set the section of `𝒪_X` with `n`-th component `1` and all other components zero
acts as the identity on the sections of `L` and as zero on those of `L'`, which kills every pure
tensor; the acting section depends only on the two projections, not on the two modules.

This generalizes `isZero_tensor_toOXMod_unit`, which is the case of the unit modules, and it is
the shape the assembly of the implication `(2) ⟹ (1)` of Stacks 0FPG consumes: there `L` is the
invertible `ℋ^n` of clause (2) and `L'` is `(ℋ^m)^{-1}`, neither of them a factor.

A step of the proof of an implication of Stacks 0FPG, not a clause of it, so it carries no
`@[stacks]` attribute. -/
public theorem isZero_tensor_toOXMod (D : ProductDecomposition X) {n m : ℤ} (hmn : m ≠ n)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))
    (L' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor m))) :
    letI := SheafOfModules.monoidalCategorySheafTensor X.sheaf
    IsZero (MonoidalCategory.tensorObj ((D.toOXMod n).obj L) ((D.toOXMod m).obj L')) :=
  -- pinned by name: resolving the instance by search exhausts the typeclass budget.
  let := hasBinaryBiproducts_ringSheaf X
  Stacks.SheafOfModules.RingSheafProductFactor.isZero_tensorObj_restrictScalars
    (Stacks.SheafOfModules.RingSheafProductFactor.ProductPresentation.ofIso D.iso) hmn L L'

/-- **A module over a factor is a retract of its tensor product with that factor.** For `L` an
`𝒪_n`-module read as an `𝒪_X`-module, `L` is a retract of `𝒪_n ⊗_{𝒪_X} L` in `Mod(𝒪_X)`.

This is the monoidal form of "the idempotent cutting out the `n`-th factor acts as the identity
on an `𝒪_n`-module": the retraction is `a ⊗ x ↦ a • x` and the inclusion is `x ↦ 1 ⊗ x`, whose
composite is multiplication by the section of `𝒪_X` with `n`-th component `1` and all others
zero. Its content is the surjectivity half of
`Stacks.SheafOfModules.RingSheafProductFactor.ProductPresentation`, which produces that section;
there is no derived category and no flatness anywhere in it.

**Restriction of scalars is load-bearing, not bookkeeping.** The statement is false for a general
`𝒪_X`-module `N` in place of `L`: at `N = 𝒪_X` and two nonzero factors it would say that
`𝒪_n ⊗_{𝒪_X} 𝒪_X = 𝒪_n` is a retract of `𝒪_X` in the wrong direction, i.e. that `𝒪_X` is a
retract of `𝒪_n`, which fails on the sections of the other factors.

This is the ringed-space instance of
`Stacks.SheafOfModules.RingSheafProductFactor.nonempty_retract_tensorObj_restrictScalars` at the
product presentation supplied by `ProductDecomposition.iso`, and it is the sheaf-level statement
the module docstring records as the last remaining ingredient of the off-diagonal vanishing.

A step of the proof of an implication of Stacks 0FPG, not a clause of it, so it carries no
`@[stacks]` attribute. -/
public theorem nonempty_retract_tensor_toOXMod (D : ProductDecomposition X) (n : ℤ)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))) :
    letI := SheafOfModules.monoidalCategorySheafTensor X.sheaf
    Nonempty (Retract ((D.toOXMod n).obj L)
      (MonoidalCategory.tensorObj
        ((D.toOXMod n).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))))
        ((D.toOXMod n).obj L))) :=
  -- pinned by name: resolving the instance by search exhausts the typeclass budget.
  let := hasBinaryBiproducts_ringSheaf X
  Stacks.SheafOfModules.RingSheafProductFactor.nonempty_retract_tensorObj_restrictScalars
    (Stacks.SheafOfModules.RingSheafProductFactor.ProductPresentation.ofIso D.iso) n L

variable [HasDerivedCategory.{d} (Mod X.sheaf)]

/-- **The derived orthogonality of the factors, for arbitrary modules over them, one of which is
flat.** For `n ≠ m`, an `𝒪_n`-module `L` which is flat over `𝒪_X` and an *arbitrary* `𝒪_m`-module
`L'` have vanishing derived tensor product in `D(𝒪_X)`, each placed in degree zero.

This is `isZero_tensor_toOXMod` read through
`Stacks.Cohomology.MonoidalDerived.isZero_derivedTensor_of_isZero_tensor_of_isFlat_left`, and it
generalizes `isZero_derivedTensor_toOXMod_unit` from the two factors to arbitrary modules over
them. It is the form in which the off-diagonal terms of the assembly of `(2) ⟹ (1)` of Stacks
0FPG are killed.

Only one flatness hypothesis is carried, and it is the hypothesis of the one-sided K-flat
comparison rather than of the orthogonality: the ordinary vanishing it is read through needs no
flatness, and neither does the vanishing of the total tensor product of complexes. See the module
docstring for how the remaining hypothesis is to be removed; it is not to be discharged by
transitivity of flatness.

A step of the proof of an implication of Stacks 0FPG, not a clause of it, so it carries no
`@[stacks]` attribute. -/
public theorem isZero_derivedTensor_toOXMod (D : ProductDecomposition X) {n m : ℤ} (hmn : m ≠ n)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))
    (L' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor m)))
    (hL : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf)
      ((D.toOXMod n).obj L)) :
    letI := Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory.{u, d} X
    IsZero (MonoidalCategory.tensorObj
      ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj ((D.toOXMod n).obj L))
      ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj ((D.toOXMod m).obj L'))) :=
  Stacks.Cohomology.MonoidalDerived.isZero_derivedTensor_of_isZero_tensor_of_isFlat_left X _ _ hL
    (D.isZero_tensor_toOXMod hmn L L')

/-- **The same with the flatness on the other side.** For `n ≠ m`, an arbitrary `𝒪_n`-module `L`
and an `𝒪_m`-module `L'` which is flat over `𝒪_X` have vanishing derived tensor product. The two
statements are independent: each discharges the K-flatness of the comparison on a different
argument, and the assembly may use whichever side it can. -/
public theorem isZero_derivedTensor_toOXMod_right (D : ProductDecomposition X) {n m : ℤ}
    (hmn : m ≠ n)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))
    (L' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor m)))
    (hL' : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf)
      ((D.toOXMod m).obj L')) :
    letI := Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory.{u, d} X
    IsZero (MonoidalCategory.tensorObj
      ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj ((D.toOXMod n).obj L))
      ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj ((D.toOXMod m).obj L'))) :=
  Stacks.Cohomology.MonoidalDerived.isZero_derivedTensor_of_isZero_tensor_of_isFlat_right X _ _
    hL' (D.isZero_tensor_toOXMod hmn L L')

/-- **The derived orthogonality of a factor against an arbitrary module over another factor, with
no flatness hypothesis.** For `n ≠ m` and `L'` an arbitrary `𝒪_m`-module, the factor `𝒪_n` and
`L'`, each read as an `𝒪_X`-module and placed in degree zero, have vanishing derived tensor
product in `D(𝒪_X)`.

Nothing is assumed: the one flatness hypothesis of `isZero_derivedTensor_toOXMod` is the flatness
of the module on the left over `𝒪_X`, and here that module is the factor `𝒪_n`, which is flat by
`ProductDecomposition.isFlat_toOXMod_unit` because it is a retract of `𝒪_X`.

This generalizes `isZero_derivedTensor_toOXMod_unit`, which is the case `L' = 𝒪_m`, in the
direction the assembly of `(2) ⟹ (1)` of Stacks 0FPG needs: the second module there is
`(ℋ^m)^{-1}`, not a factor. A step of that proof, not a clause of the tag, so it carries no
`@[stacks]` attribute. -/
public theorem isZero_derivedTensor_toOXMod_factor (D : ProductDecomposition X) {n m : ℤ}
    (hmn : m ≠ n)
    (L' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor m))) :
    letI := Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory.{u, d} X
    IsZero (MonoidalCategory.tensorObj
      ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj
        ((D.toOXMod n).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))))
      ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj ((D.toOXMod m).obj L'))) :=
  D.isZero_derivedTensor_toOXMod hmn _ L' (D.isFlat_toOXMod_unit n)

/-- **The same with the factor on the right, again with no flatness hypothesis.** For `n ≠ m` and
`L` an arbitrary `𝒪_n`-module, `L` and the factor `𝒪_m` have vanishing derived tensor product. -/
public theorem isZero_derivedTensor_toOXMod_factor_right (D : ProductDecomposition X) {n m : ℤ}
    (hmn : m ≠ n)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))) :
    letI := Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory.{u, d} X
    IsZero (MonoidalCategory.tensorObj
      ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj ((D.toOXMod n).obj L))
      ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj
        ((D.toOXMod m).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor m)))))) :=
  D.isZero_derivedTensor_toOXMod_right hmn L _ (D.isFlat_toOXMod_unit m)

/-- **The derived orthogonality for arbitrary modules over distinct factors, with no flatness
hypothesis**, conditional on the one remaining ingredient: that an `𝒪_m`-module in degree zero is
a retract of `𝒪_m ⊗^L` itself in `D(𝒪_X)`.

Given that retract the flatness disappears entirely, and this is the derivation:
`M ⊗^L N` is a retract of `M ⊗^L (𝒪_m ⊗^L N)` because `M ⊗^L -` is a functor; the associator
rewrites that as `(M ⊗^L 𝒪_m) ⊗^L N`; `M ⊗^L 𝒪_m` is a zero object by
`isZero_derivedTensor_toOXMod_factor_right`, which assumes nothing; a zero object tensored with
anything is a zero object (`Stacks.Cohomology.MonoidalDerived.isZero_tensorObj_of_isZero_left`);
and a retract of a zero object is a zero object.

So the whole of the remaining obligation of the off-diagonal terms of `(2) ⟹ (1)` is the retract
hypothesis, which is a statement about *sheaves* of modules — it says that the idempotent cutting
out the `m`-th factor acts as the identity on an `𝒪_m`-module — and contains no derived category
and no flatness.  Its sheaf-level form, stated in the module docstring, implies this one through
the one-sided K-flat comparison `CochainComplex.KFlatMonoidal.derivedTensorLeftKFlatIso`
(`𝒪_m` is flat, hence K-flat in degree zero) together with the identification of the total tensor
product of two complexes in degree zero with the tensor product in degree zero, for which
`TotalTensorComplex.SingleTensor.singleTensorIso` and Mathlib's
`HomologicalComplex.singleMapHomologicalComplex` are the two available halves.

The hypothesis is a stand-in for that sheaf-level statement.  It is carried explicitly rather
than hidden, and no declaration here is a clause of Stacks 0FPG, so nothing tagged depends on
it. -/
public theorem isZero_derivedTensor_toOXMod_of_retract (D : ProductDecomposition X) {n m : ℤ}
    (hmn : m ≠ n)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))
    (L' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor m)))
    (ret : letI := Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory.{u, d} X
      Retract ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj ((D.toOXMod m).obj L'))
        (MonoidalCategory.tensorObj
          ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj
            ((D.toOXMod m).obj
              (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor m)))))
          ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj ((D.toOXMod m).obj L')))) :
    letI := Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory.{u, d} X
    IsZero (MonoidalCategory.tensorObj
      ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj ((D.toOXMod n).obj L))
      ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj ((D.toOXMod m).obj L'))) := by
  let := Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory.{u, d} X
  refine isZero_of_retract (ret.map (MonoidalCategory.tensorLeft
    ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj ((D.toOXMod n).obj L)))) ?_
  exact (Stacks.Cohomology.MonoidalDerived.isZero_tensorObj_of_isZero_left X _
      (D.isZero_derivedTensor_toOXMod_factor_right hmn L)).of_iso
    (MonoidalCategory.associator _ _ _).symm

/-- **The retract of `isZero_derivedTensor_toOXMod_of_retract`, discharged.** An `𝒪_m`-module
placed in degree zero is a retract of `𝒪_m ⊗^𝐋` itself in `D(𝒪_X)`.

This is the sheaf-level `nonempty_retract_tensor_toOXMod` carried into the derived category by
`Stacks.Cohomology.MonoidalDerived.derivedTensorSingleIso`, whose flatness hypothesis is on the
factor `𝒪_m` and is discharged outright by `ProductDecomposition.isFlat_toOXMod_unit`. So this
theorem assumes nothing beyond the decomposition itself.

A step of the proof of an implication of Stacks 0FPG, not a clause of it, so it carries no
`@[stacks]` attribute. -/
public theorem nonempty_retract_derivedTensor_toOXMod (D : ProductDecomposition X) (m : ℤ)
    (L' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor m))) :
    letI := Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory.{u, d} X
    Nonempty (Retract ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj ((D.toOXMod m).obj L'))
      (MonoidalCategory.tensorObj
        ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj
          ((D.toOXMod m).obj
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor m)))))
        ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj ((D.toOXMod m).obj L')))) := by
  let := Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory.{u, d} X
  obtain ⟨ret⟩ := D.nonempty_retract_tensor_toOXMod m L'
  exact ⟨(ret.map (DerivedCategory.singleFunctor (Mod X.sheaf) 0)).trans
    (Retract.ofIso (Stacks.Cohomology.MonoidalDerived.derivedTensorSingleIso.{u, d} X
      ((D.toOXMod m).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor m))))
      ((D.toOXMod m).obj L') (D.isFlat_toOXMod_unit m)).symm)⟩

/-- **The derived orthogonality of the factors for arbitrary modules over distinct factors, with
no hypothesis at all.** For `n ≠ m`, an arbitrary `𝒪_n`-module `L` and an arbitrary
`𝒪_m`-module `L'`, each read as an `𝒪_X`-module and placed in degree zero, have vanishing
derived tensor product in `D(𝒪_X)`.

This is `isZero_derivedTensor_toOXMod_of_retract` with its hypothesis discharged by
`nonempty_retract_derivedTensor_toOXMod`, and it is the form the assembly of the implication
`(2) ⟹ (1)` of Stacks 0FPG consumes: there `L` is the invertible `ℋ^n` of clause (2) and `L'` is
`(ℋ^m)^{-1}`, neither of them a factor and neither known to be flat over `𝒪_X`. The flatness
hypotheses of `isZero_derivedTensor_toOXMod` and of its `_right` twin are gone, and not by
proving transitivity of flatness: over orthogonal factors the idempotent cutting out a factor
kills every `Tor`, which is exactly what the retract expresses.

A step of the proof of an implication of Stacks 0FPG, not a clause of it, so it carries no
`@[stacks]` attribute. -/
public theorem isZero_derivedTensor_toOXMod_of_ne (D : ProductDecomposition X) {n m : ℤ}
    (hmn : m ≠ n)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))
    (L' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor m))) :
    letI := Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory.{u, d} X
    IsZero (MonoidalCategory.tensorObj
      ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj ((D.toOXMod n).obj L))
      ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj ((D.toOXMod m).obj L'))) := by
  obtain ⟨ret⟩ := D.nonempty_retract_derivedTensor_toOXMod.{u, d} m L'
  exact D.isZero_derivedTensor_toOXMod_of_retract hmn L L' ret

end Stacks.Cohomology.InvertibleDerived.ProductDecomposition

end
