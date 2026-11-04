module

public import StacksFrontier.AlgebraicGeometry.Quot.StableCurvesPolarizationOfModules
public import StacksFrontier.AlgebraicGeometry.Quot.StableCurveFamilyTotalScheme
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyRelativeDualizingSheafExists

/-!
# The polarization of stable curves by the relative dualizing sheaf

`AlgebraicGeometry.stableCurvesPolarizationOfModules` polarizes stable families of curves from an
invertible, relatively ample choice of modules compatible with morphisms. The relative dualizing
sheaf `ω_{X/S}` is such a choice: it is invertible and its formation commutes with base change
(Stacks 0E6R, `AlgebraicGeometry.CurveFamily.isInvertible_relativeDualizingSheafOfNodal`,
`AlgebraicGeometry.CurveFamily.Hom.relativeDualizingSheafOfNodalPullbackIso`), and on a stable
family it is relatively ample (Stacks 0E74,
`AlgebraicGeometry.CurveFamily.isRelativelyAmple_of_isStableCurveFamily`).

## Main definitions

* `AlgebraicGeometry.stableCurvesPolarization`: the polarization of stable families of curves by
  their relative dualizing sheaves.

## Implementation notes

Nothing here carries a `stacks` attribute.

## References

* [Stacks Project, Tag 0E6R](https://stacks.math.columbia.edu/tag/0E6R)
* [Stacks Project, Tag 0E74](https://stacks.math.columbia.edu/tag/0E74)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **The polarization of stable families of curves by the relative dualizing sheaf**: a stable
family `F` is polarized by `ω_{X/S}`, which is invertible, ample relative to `F` (Stacks 0E74) and
compatible with every morphism of stable families (Stacks 0E6R). -/
def stableCurvesPolarization : StableCurvesPolarization B hZ :=
  stableCurvesPolarizationOfModules (fun F hF => F.relativeDualizingSheafOfNodal hF.1.1)
    (fun F hF => F.isInvertible_relativeDualizingSheafOfNodal hF.1.1)
    (fun F hF => CurveFamily.isRelativelyAmple_of_isStableCurveFamily hF
      (F.isRelativeDualizingSheaf_relativeDualizingSheafOfNodal hF.1))
    (fun hF hG φ => ⟨φ.relativeDualizingSheafOfNodalPullbackIso hG.1.1 hF.1.1⟩)

end AlgebraicGeometry

end
