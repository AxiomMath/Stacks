module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFibreLiftSeparates
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFibreLiftPullback
public import StacksFrontier.Deformation.ToposThickening.CoefficientReferenceLift

/-!
# The coefficient lift comparison of the fibre of `Complexes_{X/Y}`

Let `x₀` be a field point of `Complexes_{X/Y}` over `Spec k`, `E₀` its complex, `X₀ = X_{x₀}`,
`w₀` the base point of the fibre of `Complexes_{X/Y}` over the point `Spec k ⟶ Y`, and `m` an
integer with `E₀⟦m⟧ ∈ D^{≤ 0}`. This file assembles the coefficient lift comparison
`Deformation.Artin.CoefficientLiftComparison` of the proof of Stacks 0DLL at the coefficient map
of the field point and at `K₀ = E₀⟦m⟧`
(`AlgebraicGeometry.Space.ComplexesSituation.fibreCoefficientLiftComparison`):

* a class of lifts of `w₀` over `k[V]` goes to the shift by `m` of the class of the lift of `E₀`
  of a representative (`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftClass`);
* the reference lifts are the trivial lifts `s^*(E₀⟦m⟧)`
  (`Deformation.ComplexLift.coefficientBaseLift`), in `D^{≤ 0}` and compatible with base change;
* lifts over `k[ε]` with the same image in `(Sch/V)` and the same class are equal
  (`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftClass_separates`).

The compatibility of the classes with pullback along linear maps `V ⟶ W`
(`AlgebraicGeometry.Space.ComplexesSituation.FibreLiftClassPullback`) is taken as a hypothesis:
it is **internal, 0DLL-G4-2, pending** (the geometric comparison of pulled-back lifts of `w₀`).

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

/-- **The compatibility of the classes of lifts of `E₀⟦m⟧` with pullback of lifts of `w₀`**: if
a lift class `b` of `w₀` over `k[W]` is the pullback of a lift class `a` over `k[V]` along a
linear map `f : V ⟶ W`, then the class of lifts of `E₀⟦m⟧` of `b` is the derived base change
along `𝒪_{X₀}[V] ⟶ 𝒪_{X₀}[W]` of that of `a`. This is the `toLift_pullback` field of the
coefficient lift comparison of Stacks 0DLL; it is **internal, 0DLL-G4-2, pending**. -/
def FibreLiftClassPullback (hK : DerivedCategory.TStructure.t.minus x₀.E) (m : ℤ)
    (hKm : DerivedCategory.TStructure.t.minus (x₀.E⟦m⟧)) : Prop :=
  ∀ {V W : FGModuleCat.{u} k} (f : V ⟶ W)
    (a : squareZeroLiftClasses k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
      (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
        (baseProj D.Y) (complexesToBaseObjects D) (schemePointToBase D.Y x₀.T.left x₀.T.hom))
      (fibreBasePoint D x₀) (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk)
      ((fgSiteModule B hk).obj V))
    (b : squareZeroLiftClasses k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
      (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
        (baseProj D.Y) (complexesToBaseObjects D) (schemePointToBase D.Y x₀.T.left x₀.T.hom))
      (fibreBasePoint D x₀) (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk)
      ((fgSiteModule B hk).obj W)),
    IsPullbackOfSquareZeroLift k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
        (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
          (baseProj D.Y) (complexesToBaseObjects D) (schemePointToBase D.Y x₀.T.left x₀.T.hom))
        (fibreBasePoint D x₀) (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk)
        ((fgSiteModule B hk).map f) a b →
      fibreLiftClass (hDer := hDer W) hK m hKm b =
        (coefficientReductionBaseChange.{d, u + 1} (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)
          f).liftClassMap (fibreLiftClass (hDer := hDer V) hK m hKm a)

/-- **Stacks 0DLL: the coefficient lift comparison of the fibre of `Complexes_{X/Y}`**, at the
coefficient map of the field point `x₀` and at `K₀ = E₀⟦m⟧ ∈ D^{≤ 0}`: lifts of `w₀` go to the
shifted classes of lifts of `E₀` (`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftClass`),
the reference lifts are the trivial lifts (`Deformation.ComplexLift.coefficientBaseLift`), and
separation is `AlgebraicGeometry.Space.ComplexesSituation.fibreLiftClass_separates`. The
compatibility with pullback `hpull` is **internal, 0DLL-G4-2, pending**. -/
def fibreCoefficientLiftComparison (hK : DerivedCategory.TStructure.t.minus x₀.E) (m : ℤ)
    (hm : (x₀.E⟦m⟧).IsLE 0) (hpull : FibreLiftClassPullback (hDer := hDer) hK m ⟨0, hm⟩) :
    CoefficientLiftComparison.{d, u + 1} B S hS iΛ hk (complexesFunctor D) (baseProj D.Y)
      (Over.map x₀.T.left.hom) (complexesToBaseObjects D)
      (schemePointToBase D.Y x₀.T.left x₀.T.hom) (fibreBasePoint D x₀)
      (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk) (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)
      ⟨x₀.E⟦m⟧, ⟨0, hm⟩⟩ where
  toLift V := fibreLiftClass (hDer := hDer V) hK m ⟨0, hm⟩
  toLift_pullback f a b h := hpull f a b h
  base V := coefficientBaseLift.{d, u + 1} (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)
    ⟨x₀.E⟦m⟧, ⟨0, hm⟩⟩ V
  base_isLE V :=
    haveI : (x₀.E⟦m⟧).IsLE 0 := hm
    coefficientBaseLift_isLE.{d, u + 1} (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)
      ⟨x₀.E⟦m⟧, ⟨0, hm⟩⟩ V
  base_baseChange f := coefficientBaseLift_baseChange.{d, u + 1}
    (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) ⟨x₀.E⟦m⟧, ⟨0, hm⟩⟩ f
  separates a b h𝒵 h := fibreLiftClass_separates (hDer := hDer _) hK m ⟨0, hm⟩ a b h𝒵 h

end ComplexesSituation

end AlgebraicGeometry.Space

end
