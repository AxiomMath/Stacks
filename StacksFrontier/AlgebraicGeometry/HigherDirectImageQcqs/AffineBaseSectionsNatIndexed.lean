module

public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.AffineBaseSections

/-!
# Cohomology over an affine base, at one module and in natural-number degrees

`Stacks.AlgebraicGeometry.HigherDirectImageQcoh.cohomologyIsoGlobalSectionsRightDerivedPushforward`
states [Stacks, Tag 01XK] as a natural isomorphism of functors on the quasi-coherent modules, in
the integer degrees of `CategoryTheory.Functor.rightDerivedPlus`. This file restates it at a
single quasi-coherent module and in the natural-number degrees of Mathlib's
`CategoryTheory.Functor.rightDerived`:

`H ⁱ(X, F) ≅ Γ(S, R ⁱ f_* F)`

as `Γ(S, ⊤)`-modules, for `f : X ⟶ S` quasi-compact and quasi-separated with `S` affine and `F`
quasi-coherent.

## Main definitions

* `Stacks.AlgebraicGeometry.HigherDirectImageQcoh.sectionsRightDerivedPushforwardIso`:
  **[Stacks, Tag 01XK] at one module, in natural-number degrees.**

## Implementation notes

The two indexings are compared by
`Stacks.AlgebraicGeometry.HigherDirectImageQcoh.derivedPlusIsoNat`.

This is a separate module, rather than a further declaration in
`StacksFrontier/AlgebraicGeometry/HigherDirectImageQcqs/AffineBaseSections.lean`, because of the
import closure. `CategoryTheory.Functor.rightDerivedPlus` takes the chosen localization
`CategoryTheory.HasDerivedCategory` of cochain complexes as an instance argument, and the
repository runs two choices side by side, with morphisms in different universes; the integer-degree
statement is pinned to the one that
`StacksFrontier/AlgebraicGeometry/HigherDirectImageQcqs/AffineBaseSections.lean` resolves. The
natural-number degrees of `CategoryTheory.Functor.rightDerived` take no such argument, so the
statement below is independent of that choice and may be used from a module that resolves the
other one.

## References

* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.HigherDirectImageQcoh

/-- **[Stacks, Tag 01XK] at one quasi-coherent module and in natural-number degrees.** For a
quasi-compact and quasi-separated morphism `f : X ⟶ S` of schemes with `S` affine and a
quasi-coherent `𝒪_X`-module `F`, the cohomology `H ⁱ(X, F)`, read as a `Γ(S, ⊤)`-module by
restriction of scalars along `Γ(S, ⊤) ⟶ Γ(X, ⊤)`, is the module of global sections of the higher
direct image `R ⁱ f_* F`. -/
def sectionsRightDerivedPushforwardIso {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    [QuasiSeparated f] [IsAffine S] (F : X.Modules) [F.IsQuasicoherent] (i : ℕ) :
    (ModuleCat.restrictScalars f.appTop.hom).obj
        (((moduleGlobalSections X).rightDerived i).obj F) ≅
      (moduleGlobalSections S).obj (((Scheme.Modules.pushforward f).rightDerived i).obj F) :=
  (ModuleCat.restrictScalars f.appTop.hom).mapIso
      (derivedPlusIsoNat (moduleGlobalSections X) F i).symm ≪≫
    (cohomologyIsoGlobalSectionsRightDerivedPushforward f (i : ℤ)).app ⟨F, inferInstance⟩ ≪≫
    (moduleGlobalSections S).mapIso (derivedPlusIsoNat (Scheme.Modules.pushforward f) F i)

end Stacks.AlgebraicGeometry.HigherDirectImageQcoh

end
