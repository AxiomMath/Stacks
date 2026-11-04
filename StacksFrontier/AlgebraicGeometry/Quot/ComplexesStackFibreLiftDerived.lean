module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFibreLift
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RetractionDerivedPullback
public import StacksFrontier.Deformation.ToposThickening.DerivedLiftBoundedAbove
public import StacksFrontier.Deformation.ToposThickening.DerivedLiftShift
public import StacksFrontier.Deformation.Artin.FiniteDimensional.CoefficientLiftComparison

/-!
# Derived pullback to the base point of the fibre of `Complexes_{X/Y}` as derived base change

Let `x₀` be a field point of `Complexes_{X/Y}` over `Spec k`, `X₀ = X_{x₀}`, and `y` a lift of the
base point of the fibre over `k[V]`, with test scheme `T = Spec k[V]` and base map `b : T₀ ⟶ T`.
Through the derived equivalence
`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftDerivedEquivalence`
`D(𝒪_{X₀}[𝒪_{X₀} ⊗_k V]) ≌ D(𝒪_{X_T})`, the derived pullback along `X_b : X₀ ⟶ X_T` is a derived
base change along the projection `𝒪_{X₀}[𝒪_{X₀} ⊗_k V] ⟶ 𝒪_{X₀}`
(`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftDerivedExtensionOfScalars`), hence is
isomorphic to every derived base change along it
(`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftDerivedPullbackIso`). This is the
comparison `c2` of the proof of Stacks 0DLL, at the coefficient map of the field point and in the
ringed-site spelling of `Deformation.Artin.CoefficientLiftComparison`.

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
  {hk : B.Contains (Spec (.of k))} {V : FGModuleCat.{u} k}
  [hDer : HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)))]

/-- **The derived pullback along `X_b : X₀ ⟶ X_T` of a lift of `w₀` over `k[V]`, read through
`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftDerivedEquivalence`, is a derived base change
along the projection** `𝒪_{X₀}[𝒪_{X₀} ⊗_k V] ⟶ 𝒪_{X₀}`, at the coefficient map of the field
point (`AlgebraicGeometry.Space.CoherentSituation.testSchemeDerivedExtensionOfScalars`). -/
def fibreLiftDerivedExtensionOfScalars
    (y : FibreLift D iΛ x₀ hx₀ hk ((fgSiteModule B hk).obj V)) :
    DerivedExtensionOfScalars.{d, u + 1}
      (sqZeroExtSheafAnySiteProj
        ((coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj V)) := by
  let e := D.testSchemeDerivedExtensionOfScalars (hDer := hDer)
    (fibreLiftSection_comp_retraction y)
    (isSquareZeroClosedImmersion_fibreLiftSection y)
    (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) (fibreLiftScheme_left_eq y)
    (fibreLiftSection_conj y)
  exact e

/-- **Stacks 0DLL, `c2`, on the fibre: every derived base change along
`𝒪_{X₀}[𝒪_{X₀} ⊗_k V] ⟶ 𝒪_{X₀}` is the derived pullback along `X_b : X₀ ⟶ X_T`**, for a lift `y`
of `w₀` over `k[V]` with base map `b`, read through
`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftDerivedEquivalence`. -/
def fibreLiftDerivedPullbackIso (y : FibreLift D iΛ x₀ hx₀ hk ((fgSiteModule B hk).obj V))
    (T : DerivedExtensionOfScalars.{d, u + 1}
      (sqZeroExtSheafAnySiteProj
        ((coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj V))) :
    T.baseChange ≅ (fibreLiftDerivedEquivalence y).functor ⋙
      derivedPull B S hS (hasDerivedModulePullbacks B S hS) (D.relativeMap (fibreLiftSection y)) :=
  DerivedExtensionOfScalars.baseChangeIso T (fibreLiftDerivedExtensionOfScalars y)

/-- The identification `(eD⁻¹ E_y) ⊗^L 𝒪_{X₀} ≅ E₀` of a lift `y` of `w₀` over `k[V]`, for any
derived base change `T` along the projection: `c2`
(`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftDerivedPullbackIso`), the counit of the
derived equivalence, and the comparison `L(X_b)^* E_y ≅ E₀` of `y`. -/
def fibreLiftIdentification (y : FibreLift D iΛ x₀ hx₀ hk ((fgSiteModule B hk).obj V))
    (T : DerivedExtensionOfScalars.{d, u + 1}
      (sqZeroExtSheafAnySiteProj
        ((coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj V))) :
    T.baseChange.obj ((fibreLiftDerivedEquivalence y).inverse.obj y.1.right.x.E) ≅ x₀.E :=
  (fibreLiftDerivedPullbackIso y T).app _ ≪≫
    (derivedPull B S hS (hasDerivedModulePullbacks B S hS)
      (D.relativeMap (fibreLiftSection y))).mapIso
        ((fibreLiftDerivedEquivalence y).counitIso.app y.1.right.x.E) ≪≫
    @asIso _ _ _ _ y.1.hom.a.fibre y.1.hom.a.isIso_fibre

/-- **The lift of `E₀` to `𝒪_{X₀}[𝒪_{X₀} ⊗_k V]` attached to a lift `y` of `w₀` over `k[V]`**
(Stacks 0DIZ): the complex `E_y` of `y` on `X_T`, carried to the site of `X₀` by the derived
equivalence, with the identification
`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftIdentification`. It is bounded above because
its reduction `E₀` is (`Deformation.ComplexLift.isLE_of_isLE_baseChange_sqZeroExt`). -/
def fibreLiftDerivedLift (y : FibreLift D iΛ x₀ hx₀ hk ((fgSiteModule B hk).obj V))
    (hK : DerivedCategory.TStructure.t.minus x₀.E) :
    DerivedLift (derivedExtensionOfScalarsData.{d, u + 1}
      (sqZeroExtSheafAnySiteProj
        ((coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj V))) ⟨x₀.E, hK⟩ where
  K := ⟨(fibreLiftDerivedEquivalence y).inverse.obj y.1.right.x.E, by
    obtain ⟨n, hn⟩ := hK
    have : x₀.E.IsLE n := hn
    exact ⟨n, isLE_of_isLE_baseChange_sqZeroExt _ n _
      (DerivedCategory.TStructure.t.isLE_of_iso (fibreLiftIdentification y _).symm n)⟩⟩
  identification := fibreLiftIdentification y _

/-- **The class of lifts of `E₀⟦m⟧` attached to a class of lifts of `w₀` over `k[V]`**: the
shift by `m` (`Deformation.ComplexLift.DerivedLift.classShift`) of the class of the lift
`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftDerivedLift` of a representative. This is the
`toLift` field of the coefficient lift comparison of Stacks 0DLL, at `K₀ = E₀⟦m⟧`. -/
def fibreLiftClass (hK : DerivedCategory.TStructure.t.minus x₀.E) (m : ℤ)
    (hKm : DerivedCategory.TStructure.t.minus (x₀.E⟦m⟧))
    (a : squareZeroLiftClasses k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
      (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
        (baseProj D.Y) (complexesToBaseObjects D) (schemePointToBase D.Y x₀.T.left x₀.T.hom))
      (fibreBasePoint D x₀) (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk)
      ((fgSiteModule B hk).obj V)) :
    Quotient (DerivedLift.setoid
      (T := derivedExtensionOfScalarsData.{d, u + 1}
        (sqZeroExtSheafAnySiteProj
          ((coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj V)))
      (K₀ := ⟨x₀.E⟦m⟧, hKm⟩)) :=
  DerivedLift.classShift.{d, u + 1, u, u, u + 1}
    (T := derivedExtensionOfScalarsData.{d, u + 1}
      (sqZeroExtSheafAnySiteProj
        ((coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj V)))
    (K₀ := ⟨x₀.E, hK⟩) m (Iso.refl _) (Quotient.mk _ (fibreLiftDerivedLift a.out hK))

end ComplexesSituation

end AlgebraicGeometry.Space

end
