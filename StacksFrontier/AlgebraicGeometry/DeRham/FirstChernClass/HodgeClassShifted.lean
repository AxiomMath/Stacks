module

public import StacksFrontier.AlgebraicGeometry.DeRham.CechCupProduct
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.ShiftedFormsComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerDegreeOne

/-!
# The Hodge first Chern class in the graded piece `Ω¹[-1]` of the de Rham complex

Let `p : X ⟶ S` be a morphism of schemes and `Ω = Ω_{X/S}`. The Hodge first Chern class
`c₁^{Hodge}(L) ∈ H¹(X, Ω)` of an invertible module ([Stacks, Section 0FLE]) lives in the first
cohomology of the abelian sheaf underlying `Ω`. The degree-one generator `Ω ⟶ ⋀¹Ω = Ω¹` is an
isomorphism, and `H¹(X, Ω¹) ≅ H²(X, Ω¹[-1])` with `Ω¹[-1]` the graded piece of the de Rham complex
of sheaves of `p⁻¹𝒪_S`-modules. This file assembles the resulting identification
`H¹(X, Ω) ≅ H²(X, Ω¹[-1])` and records that it carries `c₁^{Hodge}(L)` to the image of the
Hodge-filtered first Chern class `γ₁(L) ∈ H²(X, σ^{≥1}Ω^•)` in the graded piece, which is the
second assertion of [Stacks, Remark 0FME].

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.hodgeOneShiftedEquiv`: the identification
  `H¹(X, Ω_{X/S}) ≅ H²(X, Ω¹[-1])`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.hypercohomologyMap_truncPlusπ_filteredFirstChernClassModule`:
  the projection of `γ₁(L)` to the graded piece is the image of `c₁^{Hodge}(L)`.

## References

* [Stacks Project, Remark 0FME](https://stacks.math.columbia.edu/tag/0FME)
* [Stacks Project, Section 0FLE](https://stacks.math.columbia.edu/tag/0FLE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.Leray (AbelianSheaf sectionsFunctor)
open Stacks.Cech.Hypercohomology

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (p : X ⟶ S)

/-- The degree-one generator `Ω_{X/S} ⟶ ⋀¹Ω_{X/S}` is an isomorphism. -/
theorem isIso_exteriorGenerator_relativeDifferentials :
    IsIso (Scheme.Modules.exteriorGenerator (relativeDifferentials p)) :=
  (_root_.SheafOfModules.algebras _ (relativeDifferentials p)).isIso_exteriorGenerator

/-- **The identification `H¹(X, Ω_{X/S}) ≅ H²(X, Ω¹[-1])`**: the degree-one generator
`Ω ⟶ ⋀¹Ω`, which is an isomorphism, followed by the identification of
`AlgebraicGeometry.SheafOfModules.shiftedFormsOneComparison` of `H¹(X, Ω¹)` with the
hypercohomology of the graded piece `Ω¹[-1]` of the de Rham complex of sheaves of
`p⁻¹𝒪_S`-modules. -/
def hodgeOneShiftedEquiv :
    ((sectionsFunctor X.carrier ⊤).rightDerived 1).obj
        ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj (relativeDifferentials p)) ≃+
      hypercohomology ((TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj S.sheaf)
        (singlePlus _ ((SheafOfModules.deRhamComplexInt (deRhamAlgebras p)
          (SheafOfModules.deRhamDifferential (deRhamAlgebras p))).X 1) 1) 2 :=
  (((sectionsFunctor X.carrier ⊤).rightDerived 1).mapIso
      ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).mapIso
        (@asIso _ _ _ _ (Scheme.Modules.exteriorGenerator (relativeDifferentials p))
          (isIso_exteriorGenerator_relativeDifferentials p)))).addCommGroupIsoToAddEquiv.trans
    (SheafOfModules.shiftedFormsOneComparison (deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (deRhamAlgebras p)))

/-- The identification on an element. -/
theorem hodgeOneShiftedEquiv_apply
    (x : ((sectionsFunctor X.carrier ⊤).rightDerived 1).obj
      ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj (relativeDifferentials p))) :
    hodgeOneShiftedEquiv p x =
      SheafOfModules.shiftedFormsOneComparison (deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (deRhamAlgebras p))
        ((((sectionsFunctor X.carrier ⊤).rightDerived 1).map
          ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).map
            (Scheme.Modules.exteriorGenerator (relativeDifferentials p)))).hom x) :=
  rfl

attribute [local instance] Stacks.Cohomology.Generators.picardGroupAddCommGroup in
/-- **The projection of the Hodge-filtered first Chern class of `L` onto the graded piece
`H²(X, Ω¹[-1])` is the image of the Hodge first Chern class `c₁^{Hodge}(L) ∈ H¹(X, Ω_{X/S})`**
([Stacks, Remark 0FME]). -/
theorem hypercohomologyMap_truncPlusπ_filteredFirstChernClassModule (L : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf
      (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace).property L) :
    hypercohomologyMap ((TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj S.sheaf)
        (truncPlusπ (SheafOfModules.deRhamComplexInt (deRhamAlgebras p)
          (SheafOfModules.deRhamDifferential (deRhamAlgebras p))) 1) 2
        (SheafOfModules.filteredFirstChernClassModule (deRhamAlgebras p)
          (SheafOfModules.deRhamDifferential (deRhamAlgebras p))
          (Stacks.SheafOfModules.Picard.classOf X.toRingedSpace.sheaf.obj
            (structureSheaf X.toRingedSpace.sheaf).property L hL)) =
      hodgeOneShiftedEquiv p (hodgeFirstChernClass p
        (Stacks.SheafOfModules.picardClass X.toRingedSpace.presheaf
          (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace) L hL)) := by
  rw [SheafOfModules.hypercohomologyMap_truncPlusπ_filteredFirstChernClassModule,
    SheafOfModules.rightDerived_logarithmicDifferential_classOf]
  rfl

end AlgebraicGeometry.Scheme.Hom

end
