module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DerivedStalkModel
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartHomologyFreeness
public import StacksFrontier.Homology.Eta.Perfect.BoundedComplexExtendScalars
public import StacksFrontier.Homology.Eta.Perfect.BoundedComplexPerfectModel

/-!
# The complex of an affine chart, read at a stalk

Let `(X, D, M)` be a triple as in Situation 0F8S and let `(U, A, f, M^•)` be an affine chart for
it, with `A = Γ(X, U)`.  For a point `x ∈ U` the local ring `𝒪_{X,x}` is the localization of `A`
at the prime of `x` (`Stacks.Duality.isLocalization_affineGermRingHom`), and this file shows that
the base change `M^• ⊗_A 𝒪_{X,x}` of the chart's complex represents the derived stalk of `M`
at `x`.

## Main results

* `ComplexAndDivisorSituation.AffineChart.nonempty_q_baseChange_iso_derivedStalk`: the base
  change of the chart's complex along `Γ(X, U) ⟶ 𝒪_{X,x}` and the derived stalk at `x` of any
  complex representing `M` are isomorphic in `D(𝒪_{X,x})`.

## Implementation notes

The whole content is `Stacks.Duality.nonempty_derivedStalkOfComplex_iso_extendScalars`, which
says that the derived stalk of an object of `D(𝒪_X)` is the extension of scalars of any model of
it over an affine open neighbourhood; the chart's `represents` field is such a model, repackaged
as a derived isomorphism by
`AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.representsDerivedIso`.  What is added
here is the passage from the extension of scalars of `M^•` to the bounded complex
`M^• ⊗_A 𝒪_{X,x}`, which is `BoundedComplex.extendScalarsIso`.

The derived stalk is written as `Stacks.Duality.derivedStalkOfComplex`, the degreewise stalk
followed by `CategoryTheory.DerivedCategory.Q`; it agrees by `rfl` with
`Stacks.IdealTorsion.Eta.stalkComplex`, the spelling the décalage calculus uses, both being
`Stacks.Duality.schemeStalkModuleFunctor` applied degreewise.

## References

* [Stacks Project, Tag 0F8S](https://stacks.math.columbia.edu/tag/0F8S)
* [Stacks Project, Tag 01HV](https://stacks.math.columbia.edu/tag/01HV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u d

namespace AlgebraicGeometry.ComplexAndDivisorSituation

attribute [local instance 10] HasDerivedCategory.standard

attribute [local instance 100000] modulesHasDerivedCategory

namespace AffineChart

variable {S : ComplexAndDivisorSituation.{u, d}}

/-- Extension of scalars along the germ map `Γ(X, U) ⟶ 𝒪_{X,x}` of an affine open is exact: the
germ map is a localization, hence flat. -/
theorem preservesFiniteLimits_extendScalars_affineGermRingHom {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u}
      (Stacks.Duality.affineGermRingHom hU x hx)) :=
  let := (Stacks.Duality.affineGermRingHom hU x hx).toAlgebra
  have := Stacks.Duality.isLocalization_affineGermRingHom hU x hx
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl))

/-- **The complex of an affine chart, base changed to a stalk, represents the derived stalk.**
Let `(U, A, f, M^•)` be an affine chart for `(X, D, M)` and let `x ∈ U`.  Then for every complex
`E` of `𝒪_X`-modules representing `M` the bounded complex `M^• ⊗_A 𝒪_{X,x}` and the derived
stalk of `E` at `x` are isomorphic in `D(𝒪_{X,x})`. -/
theorem nonempty_q_baseChange_iso_derivedStalk (C : AffineChart S) (x : S.X)
    (hx : x ∈ (C.U.1 : Set S.X)) (E : CochainComplex S.X.Modules ℤ)
    (hE : Nonempty ((@DerivedCategory.Q _ _ _ S.hasDerivedCategory).obj E ≅ S.M)) :
    Nonempty (DerivedCategory.Q.obj
        (C.complex.baseChange
          (Stacks.Duality.affineGermRingHom C.U.2 x hx)).toCochainComplex ≅
      Stacks.Duality.derivedStalkOfComplex x E) := by
  let := (Stacks.Duality.affineGermRingHom C.U.2 x hx).toAlgebra
  let : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u}
      (Stacks.Duality.affineGermRingHom C.U.2 x hx)) :=
    preservesFiniteLimits_extendScalars_affineGermRingHom C.U.2 x hx
  obtain ⟨e⟩ := Stacks.Duality.nonempty_derivedStalkOfComplex_iso_extendScalars E hE C.U.2 x hx
    (DerivedCategory.Q.obj C.complex.toCochainComplex) ⟨C.representsDerivedIso⟩
  exact ⟨(DerivedCategory.Q.mapIso
      (BoundedComplex.extendScalarsIso
        (Stacks.Duality.affineGermRingHom C.U.2 x hx) C.complex)).symm ≪≫
    ((ModuleCat.extendScalars.{u, u, u}
        (Stacks.Duality.affineGermRingHom C.U.2 x hx)).mapDerivedCategoryFactors.app
      C.complex.toCochainComplex).symm ≪≫ e.symm⟩

end AffineChart

end AlgebraicGeometry.ComplexAndDivisorSituation

end
