module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedFractionNaturality
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.FractionClassMap
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.CechSupportTransport
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinFractionDeRham

/-!
# The two spellings of multiplication by a global function agree

The class map `c_{f₁, …, f_c}` of [Stacks, Tag 0G7Q] has two constructions here: the one in
`Stacks.Perfect.FractionClass`, from which `AlgebraicGeometry.Scheme.Hom.formFractionClass` and the
Gysin map `AlgebraicGeometry.Scheme.Hom.gysinMap` of [Stacks, Tag 0G83] are built, and the one in
`Stacks.Perfect.SupportedFraction`, which carries the determinant rule of [Stacks, Tag 0G7S] and
the functoriality of [Stacks, Tag 0G7T]. The multiplication-by-a-global-function morphisms
`Stacks.Perfect.FractionClass.smulHom` and `Stacks.Perfect.SupportedFraction.globalSmul` they are
built from are equal, hence so are the two presentations of `i_*i^*ℱ` as a cokernel, and the two
class maps agree.

## Main definitions

* `Stacks.Perfect.FractionClass.classMapToSupport`: the class map `ℱ ⟶ i_*ℋ ᶜ_T(ℱ)` of
  [Stacks, Tag 0G7Q] in the support spelling, for any number of equations.

## Main results

* `Stacks.Perfect.smulHom_eq_globalSmul`: the two multiplication morphisms agree.
* `Stacks.Perfect.equationsMap_eq_equationsMultiplication`: the two presentations of `i_*i^*ℱ`
  as a cokernel of a map out of `ℱ^{⊕c}` agree.
* `Stacks.Perfect.supportedFractionSource_comp_supportCohomologyToPushforward`: the class map
  `Stacks.Perfect.SupportedFraction.supportedFractionSource` followed by
  `Stacks.Perfect.CechSupportTransport.supportCohomologyToPushforward` is the class map of
  `Stacks.Perfect.FractionClass`.
* `Stacks.Perfect.FractionClass.classMapToSupport_comp_supportCohomologyToPushforward`: the same
  for `Stacks.Perfect.FractionClass.classMapToSupport`, for any number of equations.

## References

* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Perfect

variable {X : Scheme.{u}}

/-- The morphism `Stacks.Perfect.FractionClass.smulHom r M`, obtained by evaluating an
endomorphism of the identity functor, is `Stacks.Perfect.SupportedFraction.globalSmul r M`, built
from its values on sections: multiplication by the global function `r`. -/
theorem smulHom_eq_globalSmul (r : Γ(X, ⊤)) (M : X.Modules) :
    FractionClass.smulHom r M = SupportedFraction.globalSmul r M :=
  rfl

/-- The two presentations of `i_*i^*ℱ` as a cokernel agree:
`Stacks.Perfect.FractionClass.equationsMap f F` and
`Stacks.Perfect.SupportedFraction.equationsMultiplication f F` are the same map `ℱ^{⊕c} ⟶ ℱ`,
whose restriction to the `j`-th summand is multiplication by `f j`. -/
theorem equationsMap_eq_equationsMultiplication {c : ℕ} (f : Fin c → Γ(X, ⊤)) (F : X.Modules) :
    FractionClass.equationsMap f F = SupportedFraction.equationsMultiplication f F :=
  rfl

section Assembly

attribute [local instance 10000] HasDerivedCategory.standard

open CategoryTheory.Limits Stacks.Perfect.CechDerivedSupport

/-- The cokernel projection of `Stacks.Perfect.FractionClass.equationsMap` followed by
`Stacks.Perfect.FractionClass.pushforwardFractionClass` is the class map, transported along the
Čech comparison isomorphisms, in degree `c`. -/
private theorem cokernelπ_equationsMap_comp_pushforwardFractionClass {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (F : X.Modules) [F.IsQuasicoherent] :
    cokernel.π (FractionClass.equationsMap f F) ≫
        FractionClass.pushforwardFractionClass f F =
      (FractionClass.classMap f F ≫ HomologicalComplex.homologyMap
          (CechComparison.complexIso f F).inv c) ≫
        (CechLocalCohomology.pushforwardLocalCohomologyIso f F c).inv := by
  rw [← FractionClass.cokernelπ_comp_quotientClassMapData]
  rfl

/-- The two constructions of the class map of [Stacks, Tag 0G7Q] agree: the class map
`Stacks.Perfect.SupportedFraction.supportedFractionSource` of [Stacks, Tag 0G7S] and
[Stacks, Tag 0G7T], followed by the comparison
`Stacks.Perfect.CechSupportTransport.supportCohomologyToPushforward` of the two places at which the
degree-`c` cohomology sheaf is taken, is `Stacks.Perfect.FractionClass.pushforwardFractionClass`
precomposed with the cokernel projection of `Stacks.Perfect.FractionClass.equationsMap`. -/
theorem supportedFractionSource_comp_supportCohomologyToPushforward {n : ℕ}
    (f : Fin (n + 1) → Γ(X, ⊤)) (F : X.Modules) [F.IsQuasicoherent] :
    SupportedFraction.supportedFractionSource f F (isClosed_equationsClosedSet f) subset_rfl ≫
        (CechSupportTransport.supportCohomologyToPushforward f F).hom =
      cokernel.π (FractionClass.equationsMap f F) ≫ FractionClass.pushforwardFractionClass f F := by
  have hleft : SupportedFraction.supportedFractionSource f F
        (isClosed_equationsClosedSet f) subset_rfl ≫
      (CechSupportTransport.supportCohomologyToPushforward f F).hom =
      SupportedFraction.fractionHom f F n ≫ cokernel.π (SupportedFraction.lastDif f F) ≫
        SupportedFraction.cokernelLastDifToSupport f F (isClosed_equationsClosedSet f)
            subset_rfl ≫
          (CechSupportTransport.supportCohomologyToPushforward f F).hom := by
    rw [SupportedFraction.supportedFractionSource, Category.assoc, Category.assoc,
      ← Category.assoc (cokernel.π (SupportedFraction.equationsMultiplication f F)),
      SupportedFraction.supportedFractionClass, cokernel.π_desc]
    simp only [Category.assoc]
  have hright : cokernel.π (FractionClass.equationsMap f F) ≫
        FractionClass.pushforwardFractionClass f F =
      FractionClass.fracTerm f F ≫ cokernel.π (SupportedFraction.lastDif f F) ≫
        GysinFractionDeRham.cokernelLastDifToPushforward f F := by
    rw [cokernelπ_equationsMap_comp_pushforwardFractionClass,
      GysinFractionDeRham.classMap_eq_fracTerm_comp]
    rfl
  rw [hleft, hright, CechSupportTransport.cokernelLastDifToPushforward_eq,
    GysinFractionDeRham.fracTerm_eq_fractionHom]

/-! ### The class map of Tag 0G7Q in the support spelling, for any number of equations -/

/-- The class map `c_{f₁, …, f_c} : ℱ ⟶ i_*ℋ ᶜ_T(ℱ)` of [Stacks, Tag 0G7Q] for any number
`c` of equations, zero included: the class `Stacks.Perfect.FractionClass.classMap` of the fraction
in the degree-`c` cohomology of the extended alternating Čech complex, followed by the comparison
`Stacks.Perfect.SupportedFraction.cechHomologyToSupport` of [Stacks, Tag 0G7L] in degree `c`. -/
def FractionClass.classMapToSupport {c : ℕ} (f : Fin c → Γ(X, ⊤)) (F : X.Modules)
    {T : Set X} (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T) :
    F ⟶ SupportedFraction.supportCohomologySheaf hT F (c : ℤ) :=
  FractionClass.classMap f F ≫ SupportedFraction.cechHomologyToSupport f F hT hTf c

/-- For any number of equations, `Stacks.Perfect.FractionClass.classMapToSupport` followed by
`Stacks.Perfect.CechSupportTransport.supportCohomologyToPushforward` is
`Stacks.Perfect.FractionClass.pushforwardFractionClass` precomposed with the cokernel projection
of `Stacks.Perfect.FractionClass.equationsMap`: the map
`AlgebraicGeometry.Scheme.Hom.formFractionClass` is defined as. -/
theorem FractionClass.classMapToSupport_comp_supportCohomologyToPushforward {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (F : X.Modules) [F.IsQuasicoherent] :
    FractionClass.classMapToSupport f F (isClosed_equationsClosedSet f) subset_rfl ≫
        (CechSupportTransport.supportCohomologyToPushforward f F).hom =
      cokernel.π (FractionClass.equationsMap f F) ≫
        FractionClass.pushforwardFractionClass f F := by
  exact (Category.assoc _ _ _).trans <|
    (congrArg (FractionClass.classMap f F ≫ ·)
      (CechSupportTransport.homologyMap_cplxIsoInv_comp_pflIso_inv f F).symm).trans
        ((Category.assoc _ _ _).symm.trans
          (cokernelπ_equationsMap_comp_pushforwardFractionClass f F).symm)

end Assembly

end Stacks.Perfect

end
