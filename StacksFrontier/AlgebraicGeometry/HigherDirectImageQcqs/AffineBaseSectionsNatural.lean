module

public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.AffineBaseSections

/-!
# Cohomology over an affine base, naturally and in natural-number degrees

`Stacks.AlgebraicGeometry.HigherDirectImageQcoh.cohomologyIsoGlobalSectionsRightDerivedPushforward`
states [Stacks, Tag 01XK] as a natural isomorphism of functors on the quasi-coherent modules, in
the integer degrees of `CategoryTheory.Functor.rightDerivedPlus`. This file restates it in the
natural-number degrees of Mathlib's `CategoryTheory.Functor.rightDerived`, **keeping the
naturality**:

`H ⁱ(X, −) ≅ Γ(S, R ⁱ f_*(−))`

as functors on the quasi-coherent `𝒪_X`-modules, for `f : X ⟶ S` quasi-compact and
quasi-separated with `S` affine.

`StacksFrontier/AlgebraicGeometry/HigherDirectImageQcqs/AffineBaseSectionsNatIndexed.lean` restates
the same tag at a *single* module; that is enough whenever only one module is in play, and it is
not enough for a consumer that has to move the isomorphism along a morphism of modules. The
transport of [Stacks, Tag 02O8] from an affine chart of the base to the sheaf on the base is such
a consumer: there the morphisms moved along are the multiplications by local sections of the
Rees algebra.

## Main definitions

* `Stacks.AlgebraicGeometry.HigherDirectImageQcoh.sectionsRightDerivedPushforwardNatIso`:
  **[Stacks, Tag 01XK] as a natural isomorphism, in natural-number degrees.**

## Implementation notes

The two indexings are compared by `Stacks.DerivedIndexing.rightDerivedIso`, which is a natural
isomorphism of functors; the objectwise statement uses its components under the name
`Stacks.AlgebraicGeometry.HigherDirectImageQcoh.derivedPlusIsoNat`.

This is a separate module, rather than a further declaration in
`StacksFrontier/AlgebraicGeometry/HigherDirectImageQcqs/AffineBaseSections.lean`, for the reason
given in the implementation notes of the objectwise restatement: the repository runs two choices
of `CategoryTheory.HasDerivedCategory` side by side, the integer-degree statement is pinned to
the one that `AffineBaseSections.lean` resolves, and the natural-number degrees of
`CategoryTheory.Functor.rightDerived` take no such argument, so the statement below may be used
from a module that resolves the other one.

## References

* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.HigherDirectImageQcoh

/-- **[Stacks, Tag 01XK] as a natural isomorphism, in natural-number degrees.** For a
quasi-compact and quasi-separated morphism `f : X ⟶ S` of schemes with `S` affine, cohomology in
degree `n`, read as a `Γ(S, ⊤)`-module by restriction of scalars along `Γ(S, ⊤) ⟶ Γ(X, ⊤)`, is
naturally isomorphic on the quasi-coherent modules to the global sections of the degree-`n`
higher direct image. -/
def sectionsRightDerivedPushforwardNatIso {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    [QuasiSeparated f] [IsAffine S] (n : ℕ) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙
        (moduleGlobalSections X).rightDerived n ⋙ ModuleCat.restrictScalars f.appTop.hom ≅
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙
        (Scheme.Modules.pushforward f).rightDerived n ⋙ moduleGlobalSections S :=
  Functor.isoWhiskerLeft (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι
      (Functor.isoWhiskerRight (Stacks.DerivedIndexing.rightDerivedIso (moduleGlobalSections X) n)
        (ModuleCat.restrictScalars f.appTop.hom)) ≪≫
    cohomologyIsoGlobalSectionsRightDerivedPushforward f (n : ℤ) ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι
      (Functor.isoWhiskerRight
        (Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) n).symm
        (moduleGlobalSections S))

end Stacks.AlgebraicGeometry.HigherDirectImageQcoh

end
