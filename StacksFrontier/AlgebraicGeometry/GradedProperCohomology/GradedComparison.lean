module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyComparison.Natural
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.CohomologyCoproductDirectSum
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.ReesCmpAssembly
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.ReesSmulCompatible
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.GradedBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.CohomologyCoproductDirectSumIndexed

/-!
# The additive comparison `⨁ₙ Hᵖ(X, Fₙ) ≅ Hᵖ(X', F')` of [Stacks, Tag 0897]

With `X' = Spec_X(𝓑)` the relative spectrum of a sheaf of graded `𝒪_X`-algebras and `F'` the
quasi-coherent `𝒪_{X'}`-module attached to a graded `𝓑`-module `F` by [Stacks, Tag 01SB]
(`StacksFrontier.AlgebraicGeometry.GradedProperCohomology.GradedBaseChange`), **this file builds the
comparison of the graded cohomology of `F` with the cohomology of `F'`**, as an isomorphism of
abelian groups. It is the composite of three identifications:

* `Hᵖ(X, ∐ₙ Fₙ) ≅ ⨁ₙ Hᵖ(X, Fₙ)` on a quasi-compact quasi-separated scheme
  ([Stacks, Tag 01FF]);
* `Hᵖ(X, −)` of the identification `ε : ∐ₙ Fₙ ≅ π_* F'`;
* `Hᵖ(X, π_* F') ≅ Hᵖ(X', F')` for the affine `π : X' ⟶ X` ([Stacks, Tag 089W]).

The coproduct is taken over **all** integer degrees, so no hypothesis on the degrees in which `F`
is concentrated is needed.

## Main definitions

* `GradedQcohAlgebra.coprodPushforwardIso`: **`ε : ∐_{n : ℤ} Fₙ ≅ π_* F'`.**
* `GradedQcohAlgebra.cmpAddEquiv`: **the comparison `⨁_{n : ℤ} Hᵖ(X, Fₙ) ≃+ Hᵖ(X', F')`.**

## Main results

* `GradedQcohAlgebra.cmpAddEquiv_of`: **the comparison on a generator** is `Hᵖ(X, −)` of the
  `n`-th coproduct injection followed by `ε`, read through [Stacks, Tag 089W]. This is what
  reduces the linearity of the comparison to one identity of morphisms of sheaves in each
  degree.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence
open Stacks.Cohomology.AffineBase Stacks.Cohomology.FormalFunctions
open scoped DirectSum AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.GradedProperCohomology

namespace GradedQcohAlgebra

variable {X : Scheme.{u}} (D : GradedQcohAlgebra X)
  (M : _root_.SheafOfModules.GradedModule.{u, u, u} D.alg)
  (hqc : ∀ n : ℤ, (pieceModule M n).IsQuasicoherent)

/-- **`ε : ∐_{n : ℤ} Fₙ ≅ π_* F'`**: the coproduct comparison
`SheafOfModules.GradedModule.coprodIntIsoUngradedSheaf` followed by the defining property
`GradedQcohAlgebra.baseChangeModuleIso` of `F'`, read as a statement about the direct image by
`Stacks.Cohomology.FormalFunctions.restrictScalars_relativeSpecQcohEquivalence_functor_obj_obj`. -/
def coprodPushforwardIso :
    (∐ fun n : ℤ => M.piece n) ≅
      (_root_.AlgebraicGeometry.Scheme.Modules.pushforward D.relSpec.hom).obj
        (D.baseChangeModule M hqc) :=
  M.coprodIntIsoUngradedSheaf ≪≫
    ((_root_.SheafOfModules.restrictScalars (AlgebraSheaf.structureMap D.sheaf)).mapIso
      ((ObjectProperty.ι _).mapIso (D.baseChangeModuleIso M hqc))).symm ≪≫
    eqToIso (restrictScalars_relativeSpecQcohEquivalence_functor_obj_obj D.sheaf _)

variable (p : ℕ) [CompactSpace (X : Type u)] [QuasiSeparatedSpace (X : Type u)]

/-- **The comparison `⨁_{n : ℤ} Hᵖ(X, Fₙ) ≃+ Hᵖ(X', F')`**: the direct-sum comparison of
[Stacks, Tag 01FF], then `Hᵖ(X, ε)`, then [Stacks, Tag 089W] for the affine `π`. -/
def cmpAddEquiv :
    gradedCohomologySum M p ≃+
      (cohomologyOf D.relSpec.left p (D.baseChangeModule M hqc) : Type u) :=
  (addEquivOfModuleIso
      (Stacks.Cohomology.CoproductDirectSum.indexedCohomologyCoprodDirectSumIso X p
        (fun n : ℤ => M.piece n)).symm).trans
    ((addEquivOfModuleIso
        (((moduleGlobalSections X).rightDerived p).mapIso (D.coprodPushforwardIso M hqc))).trans
      (addEquivOfModuleIso
        (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward D.relSpec.hom
          (D.baseChangeModule M hqc) p).symm))

/-- **The value of the comparison on a generator**: `Hᵖ(X, −)` of the `n`-th coproduct
injection, then of `ε`, read through [Stacks, Tag 089W]. -/
theorem cmpAddEquiv_of (n : ℤ) (x : (cohomologyOf X p (pieceModule M n) : Type u)) :
    D.cmpAddEquiv M hqc p
        (DirectSum.of (fun m : ℤ => (cohomologyOf X p (pieceModule M m) : Type u)) n x) =
      (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward D.relSpec.hom
          (D.baseChangeModule M hqc) p).inv.hom
        ((((moduleGlobalSections X).rightDerived p).map
            (D.coprodPushforwardIso M hqc).hom).hom
          ((((moduleGlobalSections X).rightDerived p).map
            (Sigma.ι (fun m : ℤ => M.piece m) n)).hom x)) := by
  open Stacks.Cohomology.CoproductDirectSum in
  have h2 := map_sigmaι_comp_indexedCohomologyCoprodDirectSumIso_hom X p
    (fun m : ℤ => M.piece m) n
  have h3 := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h2) x
  refine congrArg (fun w =>
    (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward D.relSpec.hom
        (D.baseChangeModule M hqc) p).inv.hom
      ((((moduleGlobalSections X).rightDerived p).map
        (D.coprodPushforwardIso M hqc).hom).hom w)) ?_
  exact Eq.trans (congrArg (fun w =>
    (Stacks.Cohomology.CoproductDirectSum.indexedCohomologyCoprodDirectSumIso X p
      (fun m : ℤ => M.piece m)).inv.hom w) h3.symm) (moduleIso_inv_hom_apply _ _)

end GradedQcohAlgebra

end Stacks.AlgebraicGeometry.GradedProperCohomology

end
