module

public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.Branches
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.FibreCoordinate

/-!
# The line bundle over `D` presenting a branch of the zero scheme of a tensor product

Let `Y` be a scheme, let `L₁` and `L₂` be invertible `𝒪_Y`-modules, let `s` be a global section
of `L₁ ⊗_{𝒪_Y} L₂` and let `i : D → Y` be the zero scheme of `s`, as in [Stacks, Tag 0F97]. The
tag's condition (4) identifies each branch `Dᵢ` of the decomposition with

  `\underline{\Spec}_D(\Sym^*(L_{3-i}^{⊗ -1}|_D))`,

the line bundle over `D` whose module of sections is the restriction to `D` of the inverse of the
*other* invertible module. This file names that line bundle.

## Main definitions

* `Stacks.Chow.TensorZeroScheme.inverseModule`: **the inverse `N^{⊗ -1}`** of an invertible module
  on `Y`, at the spelling of [Stacks, Tag 01CU] that the line bundle of [Stacks, Tag 01M2] is
  built from.
* `Stacks.Chow.TensorZeroScheme.branchSituation`: **the line bundle
  `\underline{\Spec}_D(\Sym^*(N^{⊗ -1}|_D))` over `D`**, as a `Stacks.LineBundle.Situation` whose
  total space and structure morphism are the scheme and the morphism of the tag's condition (4).

## Implementation notes

The source writes the module of condition (4) as `L_{1-i}^{⊗ -1}|_D`; as its own proof and the
proof of [Stacks, Tag 0F98] make explicit ("`D₁` is the line bundle which is the relative spectrum
of the inverse of `L₂`"), the index is the *other* one, so `D₁` uses `L₂` and `D₂` uses `L₁`. The
definitions here take the module as an argument and leave that choice to the consumer.

The tensor power of [Stacks, Tag 01CU] is written at the `presheaf` spelling of the structure
sheaf, which is the one `Stacks.LineBundle.inverseSituation` uses and the one the base change of
the inverse is stated at; the three instances a tensor power needs at that spelling are declared
in `StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.FibreCoordinate`, so nothing further has to be
supplied here. Quasi-coherence and finite local freeness of rank one, which the line-bundle
construction consumes, are not extra hypotheses: on a scheme they follow from invertibility by
[Stacks, Tag 0B8M].

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open Stacks.SheafInternalHom (isSheaf_structureRingPresheaf)

universe u

namespace Stacks.Chow.TensorZeroScheme

variable (Y : Scheme.{u})

/-- **The inverse `N^{⊗ -1}` of an invertible module on a scheme**, at the spelling of [Stacks,
Tag 01CU] that the line bundle of [Stacks, Tag 01M2] is built from. -/
def inverseModule (N : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property N] :
    Y.Modules :=
  _root_.Stacks.SheafOfModules.TensorPower.tensorPower Y.presheaf
    (isSheaf_structureRingPresheaf Y) N (-1)

/-- The inverse of an invertible module is invertible. -/
instance isInvertible_inverseModule (N : Y.Modules)
    [hN : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property N] :
    AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property
      (inverseModule Y N) :=
  haveI hS : _root_.Stacks.SheafOfModules.IsInvertible Y.presheaf
      (isSheaf_structureRingPresheaf Y) N :=
    _root_.Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hN
  (_root_.Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
    (@_root_.Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower _ _ _ Y.presheaf
      (isSheaf_structureRingPresheaf Y) _ _ N hS (-1))

variable (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤))

include h₁ h₂ in
/-- **The line bundle `\underline{\Spec}_D(\Sym^*(N^{⊗ -1}|_D))` over the zero scheme `D` of
`s`**, as a line-bundle situation. Its total space and structure morphism are the scheme and the
morphism over `D` of [Stacks, Tag 0F97](4). -/
def branchSituation (N : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property N] :
    Stacks.LineBundle.Situation.{u} :=
  haveI : AlgebraicGeometry.SheafOfModules.IsInvertible
      (zeroIdeal Y L₁ L₂ s).subscheme.sheaf.obj
      (zeroIdeal Y L₁ L₂ s).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj (inverseModule Y N)) :=
    Stacks.Divisors.pullback_isInvertible _ _
  { X := (zeroIdeal Y L₁ L₂ s).subscheme
    S := (zeroIdeal Y L₁ L₂ s).subscheme
    f := CategoryTheory.CategoryStruct.id _
    L := (Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj (inverseModule Y N) }

include h₁ h₂ in
/-- The base of the line bundle presenting a branch is the zero scheme `D` of `s`. -/
@[simp] theorem branchSituation_X (N : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property N] :
    (branchSituation Y L₁ L₂ s N).X = (zeroIdeal Y L₁ L₂ s).subscheme :=
  rfl

end Stacks.Chow.TensorZeroScheme

end
