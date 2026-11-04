module

public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.CechChernPowers
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.ShiftedFormsComparison
public import StacksFrontier.AlgebraicGeometry.DeRham.ProjectiveSpaceFormsVanishing
public import StacksFrontier.AlgebraicGeometry.DeRham.ProjectiveSpaceHodgeCohomology
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearMapRestrictScalars
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologySinglePairingAtCompat

/-!
# The de Rham complex of projective space, in the Čech framework

Let `A` be a commutative ring, `n = m + 1` and `p : ℙⁿ_A ⟶ Spec A` the structure morphism. This
file records the facts about the relative de Rham complex `Ω^•_{ℙⁿ_A/A}`, a complex of sheaves of
`p⁻¹𝒪_{Spec A}`-modules, that the computation of its hypercohomology uses: its terms vanish above
degree `n`, its terms are the sheaves `Ωᵏ_{ℙⁿ_A/A}` read over `p⁻¹𝒪_{Spec A}`, and its wedge product
is the wedge product of differential forms read over `p⁻¹𝒪_{Spec A}`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveSpaceDeRham.baseRingSheaf`: the base ring sheaf
  `p⁻¹𝒪_{Spec A}` of the relative de Rham complex.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceDeRham.deRhamComplexIntTerm`: the identification of
  the term of degree `k ≥ 0` with `Ωᵏ_{ℙⁿ_A/A}` read over `p⁻¹𝒪_{Spec A}`.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceDeRham.formsMul`: the wedge product of differential
  forms read over `p⁻¹𝒪_{Spec A}`.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveSpaceDeRham.isZero_deRhamComplexInt_X_of_lt`: the terms
  vanish above degree `n`.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceDeRham.pairingHom_deRhamCechPairing`: the wedge
  product of the de Rham complex on its graded pieces is the wedge product of forms.

## References

* [Stacks Project, Tag 0FMJ](https://stacks.math.columbia.edu/tag/0FMJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace AlgebraicGeometry
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cech.Hypercohomology

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceDeRham

open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjectiveSpaceHodge

attribute [local instance] AlgebraicGeometry.SheafOfModules.sectionCommRingTopCat

variable (A : Type u) [CommRing A] (m : ℕ)

/-- The structure morphism `ℙⁿ_A ⟶ Spec A`, `n = m + 1`. -/
abbrev structureMorphism : projSpace A m ⟶ Spec (CommRingCat.of A) :=
  projToSpecCoeff A (m + 1)

/-- **The base ring sheaf `p⁻¹𝒪_{Spec A}`** of the relative de Rham complex of `ℙⁿ_A` over `A`. -/
abbrev baseRingSheaf : TopCat.Sheaf CommRingCat.{u} (projSpace A m).carrier :=
  (TopCat.Sheaf.pullback CommRingCat.{u} (structureMorphism A m).base).obj
    (Spec (CommRingCat.of A)).sheaf

/-- The relative de Rham complex of `ℙⁿ_A` over `A`, extended by zero to negative degrees. -/
abbrev deRhamComplexIntCech :=
  SheafOfModules.deRhamComplexInt (Scheme.Hom.deRhamAlgebras (structureMorphism A m))
    (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (structureMorphism A m)))

/-- The structure map `p⁻¹𝒪_{Spec A} ⟶ 𝒪_{ℙⁿ_A}`, on the underlying sheaves of rings. -/
abbrev baseRingHom : ringSheaf (baseRingSheaf A m) ⟶ ringSheaf (projSpace A m).sheaf :=
  SheafOfModules.underlyingRingHom (φ := _root_.AlgebraicGeometry.inverseImageStructureMap
    (structureMorphism A m))

/-- **The term of degree `k ≥ 0` of the relative de Rham complex is `Ωᵏ_{ℙⁿ_A/A}`** read over
`p⁻¹𝒪_{Spec A}`. -/
theorem deRhamComplexIntTerm (k : ℕ) :
    (deRhamComplexIntCech A m).X (k : ℤ) =
      (_root_.SheafOfModules.restrictScalars (baseRingHom A m)).obj (forms A m k) :=
  SheafOfModules.deRhamComplexInt_X_of_nonneg
    (Scheme.Hom.deRhamAlgebras (structureMorphism A m))
    (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (structureMorphism A m)))
    (k : ℤ) (Int.natCast_nonneg k)

/-- **The terms of the relative de Rham complex of `ℙⁿ_A` vanish above degree `n`**, because
`Ωᵏ_{ℙⁿ_A/A} = 0` for `k > n`. -/
theorem isZero_deRhamComplexInt_X_of_lt (q : ℤ) (hq : (m : ℤ) + 1 < q) :
    IsZero ((deRhamComplexIntCech A m).X q) := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ q by omega)
  rw [deRhamComplexIntTerm]
  exact Functor.map_isZero _
    (Stacks.AlgebraicGeometry.ProjectiveSpaceForms.isZero_relativeDifferentialForms_of_lt m k
      (by omega))

/-- **The scalars of `ℙⁿ_A` through the base ring sheaf are the coefficients**: an element `a` of
`A`, carried to the global sections of `p⁻¹𝒪_{Spec A}` along `A ≅ Γ(Spec A, 𝒪)` and the unit of
the inverse-image adjunction, and then to `Γ(ℙⁿ_A, 𝒪)` along the structure map, is the
coefficient `a`. -/
theorem baseRingHom_app_top (a : A) :
    ((baseRingHom A m).hom.app (op ⊤)).hom
        ((Scheme.Hom.inverseImageGlobalSections (structureMorphism A m)).hom
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) =
      Stacks.ProjectiveSpace.Cohomology.coeffScalar A (m + 1) a :=
  congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))
    (Scheme.Hom.inverseImageGlobalSections_comp_inverseImageStructureMap_app
      (structureMorphism A m))

/-- The wedge product `Ωᵏ × Ωˡ ⟶ Ω^{k+l}` of differential forms on `ℙⁿ_A`, read over
`p⁻¹𝒪_{Spec A}`. -/
abbrev formsMul (k l : ℕ) :
    Stacks.BilinearMap ((_root_.SheafOfModules.restrictScalars (baseRingHom A m)).obj
        (forms A m k)).val
      ((_root_.SheafOfModules.restrictScalars (baseRingHom A m)).obj (forms A m l)).val
      ((_root_.SheafOfModules.restrictScalars (baseRingHom A m)).obj (forms A m (k + l))).val :=
  Stacks.BilinearMap.restrictScalars (baseRingHom A m).hom
    ((Scheme.Modules.exteriorAlgebra (X := projSpace A m)
      (Scheme.Hom.relativeDifferentials (structureMorphism A m))).mul (k : ℤ) (l : ℤ))

/-- **The wedge product of the relative de Rham complex of `ℙⁿ_A` is the wedge product of
differential forms**, read over `p⁻¹𝒪_{Spec A}`, under the identification of its terms with the
sheaves of differential forms. -/
theorem formsMul_eqToHom (k l : ℕ) (Z : (Opens (projSpace A m).carrier)ᵒᵖ)
    (x : ((deRhamComplexIntCech A m).X (k : ℤ)).val.obj Z)
    (y : ((deRhamComplexIntCech A m).X (l : ℤ)).val.obj Z) :
    (formsMul A m k l).app Z ((eqToHom (deRhamComplexIntTerm A m k)).val.app Z x)
        ((eqToHom (deRhamComplexIntTerm A m l)).val.app Z y) =
      (eqToHom (deRhamComplexIntTerm A m (k + l))).val.app Z
        (((SheafOfModules.deRhamDifferentialGradedAlgebra
          (Scheme.Hom.deRhamAlgebras (structureMorphism A m))
          (SheafOfModules.deRhamDifferential
            (Scheme.Hom.deRhamAlgebras (structureMorphism A m)))).mul (k : ℤ) (l : ℤ)).app Z
          x y) := by
  have key : ∀ {M N : _root_.SheafOfModules.{u} (ringSheaf (baseRingSheaf A m))} (h : M = N)
      (z : M.val.obj Z), HEq ((eqToHom h).val.app Z z) z := by
    intro M N h z
    subst h
    rfl
  refine eq_of_heq ((SheafOfModules.deRhamDifferentialGradedAlgebra_mul _ _ k l Z x y _ _
    (key _ x).symm (key _ y).symm).symm.trans (key _ _).symm)

/-- **The wedge product of the relative de Rham complex of `ℙⁿ_A`, on its graded pieces, is the
wedge product of differential forms**: the identifications of the terms of degrees `k`, `l` and
`k + l` with the sheaves of differential forms carry the pairing of the pieces placed in degrees
`k` and `l` induced by the multiplication of the de Rham complex to the one induced by the wedge
product of forms. -/
theorem pairingHom_deRhamCechPairing (k l : ℕ) :
    PairingHom (baseRingSheaf A m)
      (singlePlusMapAt (baseRingSheaf A m) (eqToHom (deRhamComplexIntTerm A m k)) (k : ℤ))
      (singlePlusMapAt (baseRingSheaf A m) (eqToHom (deRhamComplexIntTerm A m l)) (l : ℤ))
      (singlePlusMapAt (baseRingSheaf A m) (eqToHom (deRhamComplexIntTerm A m (k + l)))
        ((k : ℤ) + (l : ℤ)))
      (singlePairingAt (k : ℤ) (l : ℤ)
        ((SheafOfModules.deRhamCechPairing
          (Scheme.Hom.deRhamAlgebras (structureMorphism A m))
          (SheafOfModules.deRhamDifferential
            (Scheme.Hom.deRhamAlgebras (structureMorphism A m)))).μ (k : ℤ) (l : ℤ)
          ((k : ℤ) + (l : ℤ)) rfl))
      (singlePairingAt (k : ℤ) (l : ℤ) (bilinearPairing (formsMul A m k l))) := by
  have := pairingHom_singlePairingAt (O := baseRingSheaf A m)
    (eqToHom (deRhamComplexIntTerm A m k)) (eqToHom (deRhamComplexIntTerm A m l))
    (eqToHom (deRhamComplexIntTerm A m (k + l))) _ (formsMul A m k l) (k : ℤ) (l : ℤ)
    (formsMul_eqToHom A m k l)
  convert this using 2
  exact congrArg (singlePairingAt (k : ℤ) (l : ℤ)) (differentialGradedPairingμ_rfl _ _ _)

end Stacks.AlgebraicGeometry.ProjectiveSpaceDeRham

end
