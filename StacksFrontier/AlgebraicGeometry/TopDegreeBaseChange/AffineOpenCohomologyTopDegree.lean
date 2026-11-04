module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineOpenCohomologyIndexing

/-!
# The cohomology over an affine open is the module conclusion (b) tensors with

For a top-degree base-change situation and an affine open `V` of its base, the module
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.affineOpenCohomology`, into which both ends of the
canonical map `γ⁺` of [Stacks, Tag 0EX3] (c) are computed, is isomorphic to
`Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.topDegreeCohomology` of the situation
restricted to `V`, the module that conclusion (b) tensors with.

## Main definitions

* `affineOpenCohomologyIsoRestrictBaseTopDegreeCohomology`: the isomorphism, read over the
  functions on `V` rather than over the functions on the ambient base. Only `V` is assumed
  affine.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.modulesLinear baseSectionsAlgebra

/-- **The top-degree cohomology over an affine open of the base is the module conclusion (b) of
[Stacks, Tag 0EX3] tensors with.**  For a top-degree base-change situation with **no hypothesis
on its base** and an affine open `V` of that base, the module
`affineOpenCohomology S.f' V F' S.d` — into which both ends of the canonical map `γ⁺` of
conclusion (c) are computed — is
`Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.topDegreeCohomology` of the situation
restricted to `V`, read over `Γ(Y', V)` through
`AlgebraicGeometry.Scheme.Opens.topIso`. -/
def affineOpenCohomologyIsoRestrictBaseTopDegreeCohomology
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u}) (V : S.Y'.Opens)
    [IsAffine (V : Scheme)] (F' : S.X'.Modules) [F'.IsQuasicoherent] :
    affineOpenCohomology S.f' V F' S.d ≅
      (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).obj
        ((S.restrictBase V).topDegreeCohomology
          ⟨(Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F',
            (inferInstance :
              ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F').IsQuasicoherent)⟩) :=
  (affineOpenCohomologyNatIso S.f' V F' S.d).symm ≪≫
    eqToIso (congrArg
      (fun φ : (S.restrictBase V).affineBaseRing →+*
            Γ(((S.restrictBase V).affineBaseOver).left, ⊤) =>
        (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).obj
          ((ModuleCat.restrictScalars φ).obj
            (((moduleGlobalSections (S.f' ⁻¹ᵁ V : Scheme)).rightDerived S.d).obj
              ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F'))))
      (S.restrictBase_appTop_eq_algebraMap V).symm)

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
