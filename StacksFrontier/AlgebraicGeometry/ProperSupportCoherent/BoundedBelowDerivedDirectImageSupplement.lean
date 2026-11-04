module

public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.BoundedBelowDerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.DerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.DerivedDirectImageSupplement
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.BoundedBelowUnconditional

/-!
# Further results on `BoundedBelowDerivedDirectImage`

Results about the objects of
`StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.BoundedBelowDerivedDirectImage` that need
imports beyond those of that module.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

universe u

namespace Stacks.AlgebraicGeometry.ProperSupportCoherent

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section DerivedPushforward

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The dévissage hypothesis of [Stacks, Tag 08E2] at the cohomology sheaves of `τ_{≤n}E`.** In
degrees `≤ n` these are the cohomology sheaves of `E`, where it is
`hasCoherentBoundedDirectImages_of_isProperOver_supp_unconditional`; in degrees `> n` they
vanish. -/
theorem hasCoherentBoundedDirectImages_homology_truncLE_unconditional [IsNoetherian S]
    [LocallyOfFiniteType f]
    (E : DerivedCategory X.Modules)
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsCoherent)
    (hsupp : ∀ j : ℤ, IsProperOver f
      ⟨SheafOfModules.supp ((DerivedCategory.homologyFunctor X.Modules j).obj E),
        @SheafOfModules.isClosed_supp _ _ _ (hcoh j).isFiniteType⟩)
    (n j : ℤ) :
    HasCoherentBoundedDirectImages f ((DerivedCategory.homologyFunctor X.Modules j).obj
      ((DerivedCategory.TStructure.t.truncLE n).obj E)) := by
  by_cases hj : j ≤ n
  · have := AlgebraicGeometry.isIso_homology_truncLE E n j hj
    exact HasCoherentBoundedDirectImages.of_iso f
      (asIso ((DerivedCategory.homologyFunctor X.Modules j).map
        ((DerivedCategory.TStructure.t.truncLEι n).app E))).symm
      (hasCoherentBoundedDirectImages_of_isProperOver_supp_unconditional f _ (hcoh j) (hsupp j))
  · exact HasCoherentBoundedDirectImages.of_isZero f
      (DerivedCategory.isZero_of_isLE _ n j (by omega))

end DerivedPushforward

end Stacks.AlgebraicGeometry.ProperSupportCoherent

end
