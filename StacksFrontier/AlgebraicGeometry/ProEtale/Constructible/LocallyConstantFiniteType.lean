module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeLocallyConstant
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.InverseImage
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.StratificationSupplement

/-!
# Locally constant sheaves of finite type on the small pro-étale site are constructible

A sheaf of `Λ`-modules which is locally constant of finite type
(`Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf`) is locally constant
(`CategoryTheory.IsLocallyConstant`), on any site: this is
`Stacks.ConstantSheaf.isLocallyConstant_of_isFiniteTypeLocallyConstantModuleSheaf` in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FiniteTypeLocallyConstant.lean`. On
the small pro-étale site of a scheme it is moreover constructible (Stacks 09AJ), with the trivial
partition of every affine open: its inverse image to the open is again locally constant of
finite type.

## Main results

* `AlgebraicGeometry.ProEtale.isConstructibleModuleSheaf'_of_isFiniteTypeLocallyConstant`.

## References

* [Stacks Project, Tag 09AJ](https://stacks.math.columbia.edu/tag/09AJ)
* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
-/

@[expose] public noncomputable section

open CategoryTheory

universe w v u r

namespace AlgebraicGeometry.ProEtale

/-- **A locally constant sheaf of finite type on the small pro-étale site is constructible**:
every affine open is its own single stratum, on which the inverse image is locally constant of
finite type. -/
theorem isConstructibleModuleSheaf'_of_isFiniteTypeLocallyConstant {X : Scheme.{u}} {Λ : Type v}
    [CommRing Λ] [IsNoetherianRing Λ]
    (G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ))
    (hG : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, max v w, v}
      (Scheme.ProEt.topology X) Λ G) :
    IsConstructibleModuleSheaf'.{u, v, w} X Λ G := fun U ↦
  ⟨Scheme.ConstructibleStratification.single X U.1, fun _ ↦
    isFiniteTypeLocallyConstantModuleSheaf_proetaleModuleInverseImage U.1.ι G hG⟩

end AlgebraicGeometry.ProEtale

end
