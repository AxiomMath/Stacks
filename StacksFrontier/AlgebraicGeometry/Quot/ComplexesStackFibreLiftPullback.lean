module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFibreLiftDerived
public import StacksFrontier.Deformation.ToposThickening.DerivedExtensionOfScalarsCompShift

/-!
# The classes of lifts of the fibre of `Complexes_{X/Y}` under base change of coefficients

Let `x₀` be a field point of `Complexes_{X/Y}` over `Spec k`, `E₀` its complex and
`K₀ = E₀⟦m⟧`. The class of lifts of `E₀⟦m⟧` attached to a class of lifts `a` of the base point of
the fibre over `k[V]` (`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftClass`) is the shift
of the class of the lift of `E₀` of a representative. The base change of classes of lifts along
`𝒪_{X₀}[V] ⟶ 𝒪_{X₀}[W]` commutes with the shift
(`Deformation.ComplexLift.DerivedLift.liftClassMap_classShift`, through
`Deformation.ComplexLift.coefficientReductionBaseChange_functor_commShift` and
`Deformation.ComplexLift.coefficientReductionBaseChange_baseChangeIso_commShift`), so the
`toLift_pullback` field of the coefficient lift comparison of Stacks 0DLL reduces to the same
statement for the unshifted lifts of `E₀`
(`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftClass_eq_liftClassMap_of_isomorphic`).

Nothing here is registered.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
-/

@[expose] public noncomputable section

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

open CategoryTheory CategoryTheory.Limits Opposite Deformation.Artin Deformation.ComplexLift
  Stacks.TensorByBaseModule

universe d u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance 10000] HasDerivedCategory.standard

namespace ComplexesSituation

variable {D : ComplexesSituation B S hS}

attribute [local instance] complexesCategory

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {iΛ : Spec (.of Λ) ⟶ S}
  {x₀ : ComplexesObject D}
  {hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
  {hk : B.Contains (Spec (.of k))}
  [hDer : ∀ V : FGModuleCat.{u} k, HasDerivedCategory.{d} (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)))]

/-- **The base change of the class of lifts of `E₀⟦m⟧` of a lift of `w₀` over `k[V]` along
`𝒪_{X₀}[V] ⟶ 𝒪_{X₀}[W]` is the class of a lift over `k[W]`**, as soon as the base change of the
unshifted lift of `E₀` of a representative of the first is isomorphic to the lift of `E₀` of a
representative of the second: shifting classes of lifts commutes with base change. -/
theorem fibreLiftClass_eq_liftClassMap_of_isomorphic
    (hK : DerivedCategory.TStructure.t.minus x₀.E) (m : ℤ)
    (hKm : DerivedCategory.TStructure.t.minus (x₀.E⟦m⟧)) {V W : FGModuleCat.{u} k} (f : V ⟶ W)
    (a : squareZeroLiftClasses k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
      (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
        (baseProj D.Y) (complexesToBaseObjects D) (schemePointToBase D.Y x₀.T.left x₀.T.hom))
      (fibreBasePoint D x₀) (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk)
      ((fgSiteModule B hk).obj V))
    (b : squareZeroLiftClasses k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
      (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
        (baseProj D.Y) (complexesToBaseObjects D) (schemePointToBase D.Y x₀.T.left x₀.T.hom))
      (fibreBasePoint D x₀) (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk)
      ((fgSiteModule B hk).obj W))
    (h : DerivedLift.Isomorphic
      ((fibreLiftDerivedLift a.out hK).baseChange
        (coefficientReductionBaseChange.{d, u + 1} (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) f))
      (fibreLiftDerivedLift b.out hK)) :
    fibreLiftClass hK m hKm b =
      (coefficientReductionBaseChange.{d, u + 1} (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)
        f).liftClassMap (fibreLiftClass hK m hKm a) := by
  have key := DerivedLift.liftClassMap_classShift
    (coefficientReductionBaseChange.{d, u + 1} (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) f) m
    (K₀' := ⟨x₀.E⟦m⟧, hKm⟩) (Iso.refl _) (Quotient.mk _ (fibreLiftDerivedLift a.out hK))
  unfold fibreLiftClass
  rw [key]
  exact congrArg _ (Quotient.sound h.symm)

end ComplexesSituation

end AlgebraicGeometry.Space

end
