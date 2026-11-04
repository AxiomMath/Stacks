module

public import StacksFrontier.AlgebraicGeometry.Cohomology.AffineOpenTruncationLift
public import StacksFrontier.CategoryTheory.Sites.Modules.SingleExtensionByZeroUnitFreeCofan

/-!
# The lifting step of Stacks 08HE (2) ⇒ (1) out of a finite free module, on an affine scheme

The affine-chart lifting step `AlgebraicGeometry.exists_lift_truncGEπ_zero_cofan_of_isAffineOpen`
takes its source as a colimiting `CategoryTheory.Limits.Cofan` of copies of
`Stacks.Sites.ExtensionByZero.singleExtensionByZeroUnit`, because that is the shape in which the
hypercohomology computation behind it produces the vanishing of the obstruction group.  The
induction step `AlgebraicGeometry.RingedSite.exists_distTriang_free_of_lift` takes it as
`(DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.free ι)`, because that is what a
surjection `O^{⊕t} ⟶ Hⁿ(E)` of modules produces.

This file is the handshake, and it is where the two shapes are checked to be the same one: on a
scheme whose total space is an affine open, `⊤` is a terminal object of the site, so
`Stacks.Sites.ExtensionByZero.isColimitFreeCofanSingleExtensionByZeroUnit` exhibits the free
module in degree zero as a colimiting cofan of copies of `j_{⊤!} O`, and the lift applies to it
with nothing shrunk.

## Main results

* `AlgebraicGeometry.exists_lift_truncGEπ_zero_single_free_of_isAffineOpen_top`: **the lift out of
  a finite free module.**

## Implementation notes

The affineness of `X` is carried as `(⊤ : X.Opens) ∈ X.affineOpens` rather than as
`AlgebraicGeometry.IsAffine X`, which is what the affine-chart statement consumes and is weaker as
a hypothesis.

No `@[stacks]` attribute is carried: this is the composition of two tagged statements, and the
tags stay where they are.

## References

* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (F : DerivedCategory X.Modules)

/-- **A morphism out of a finite free module in degree zero into a truncation lifts, on a scheme
whose total space is affine.**  For `F` in `D(𝒪_X)` with quasi-coherent cohomology, a finite index
type `ι` and `⊤` an affine open of `X`, every morphism
`g : 𝒪_X^{⊕ι}[0] ⟶ τ^{≥0}F` is `f ≫ π` for some `f : 𝒪_X^{⊕ι}[0] ⟶ F`, with nothing shrunk.

This is `AlgebraicGeometry.exists_lift_truncGEπ_zero_cofan_of_isAffineOpen` at `U = ⊤`, whose
source is read as a coproduct of copies of `j_{⊤!} 𝒪_X` by
`Stacks.Sites.ExtensionByZero.isColimitFreeCofanSingleExtensionByZeroUnit`: at the terminal object
of the site the extension by zero of the structure sheaf is the structure sheaf. -/
theorem exists_lift_truncGEπ_zero_single_free_of_isAffineOpen_top
    (hF : ∀ q : ℤ, ((DerivedCategory.homologyFunctor X.Modules q).obj F).IsQuasicoherent)
    (hX : (⊤ : X.Opens) ∈ X.affineOpens) (ι : Type u) [Finite ι]
    (g : (DerivedCategory.singleFunctor X.Modules 0).obj
        (SheafOfModules.free
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O)) ι) ⟶
      (DerivedCategory.TStructure.t.truncGE 0).obj F) :
    ∃ f : (DerivedCategory.singleFunctor X.Modules 0).obj
        (SheafOfModules.free
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O)) ι) ⟶ F,
      f ≫ (DerivedCategory.TStructure.t.truncGEπ 0).app F = g :=
  exists_lift_truncGEπ_zero_cofan_of_isAffineOpen X F hF ⊤ hX
    (Stacks.Sites.ExtensionByZero.freeCofanSingleExtensionByZeroUnit
      X.zariskiRingedSite ⊤ isTerminalTop ι)
    (Stacks.Sites.ExtensionByZero.isColimitFreeCofanSingleExtensionByZeroUnit
      X.zariskiRingedSite ⊤ isTerminalTop ι) g

end AlgebraicGeometry

end
