module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFibreLiftAutomorphisms

/-!
# The comparison of the lifts of `E₀` of a lift of `w₀` and of a pullback of it

Let `f : V ⟶ W` be a linear map, `a` a lift of `w₀` over `k[V]`, `b` a lift of `w₀` over `k[W]`
and `φ : b ⟶ a` a morphism of lifts lying over `Spec k[W] ⟶ Spec k[V]`. The comparison of
Stacks 0DLL is an isomorphism `e` from the derived base change along `𝒪_{X₀}[V] ⟶ 𝒪_{X₀}[W]` of
the lift of `E₀` of `a` to the lift of `E₀` of `b`, compatible with the identifications with
`E₀`, and carrying the automorphisms of the complex of `a` to those of the complex of `b`
through the comparison of `φ`
(`AlgebraicGeometry.Space.ComplexesSituation.FibreLiftAutPullback`). It is the input of the
naturality of `g ↦ 1 + g` (`AlgebraicGeometry.Space.ComplexesSituation.FibreTrivialAutNatural`).

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

/-- **The comparison of the lifts of `E₀` of a lift of `w₀` and of a pullback of it, natural in
automorphisms** (step 4 of the proof of Stacks 0DLL): for a linear map `f : V ⟶ W`, lifts `a`
over `k[V]` and `b` over `k[W]` of `w₀`, and a morphism `φ : b ⟶ a` of lifts lying over
`Spec k[W] ⟶ Spec k[V]`, an isomorphism `e : L_f K_a ≅ K_b` from the derived base change along
`𝒪_{X₀}[V] ⟶ 𝒪_{X₀}[W]` of the lift of `E₀` of `a` to that of `b`, which

* is an isomorphism of lifts of `E₀`: it is compatible with the two identifications with `E₀`;
* intertwines, for every automorphism `α` of `K_a`, the automorphism of `E_a` attached to `α`
  pulled back along the base map of `φ`, with the automorphism of `E_b` attached to
  `e⁻¹ ∘ L_f α ∘ e`, through the comparison of `φ`.

It is **internal, 0DLL-G4-2, pending**. -/
def FibreLiftAutPullback (hK : DerivedCategory.TStructure.t.minus x₀.E) : Prop :=
  ∀ {V W : FGModuleCat.{u} k} (f : V ⟶ W)
    (a : FibreLift D iΛ x₀ hx₀ hk ((fgSiteModule B hk).obj V))
    (b : FibreLift D iΛ x₀ hx₀ hk ((fgSiteModule B hk).obj W)) (φ : b.1.right ⟶ a.1.right),
    (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
        (baseProj D.Y) (complexesToBaseObjects D)
        (schemePointToBase D.Y x₀.T.left x₀.T.hom)).IsHomLift
      (squareZeroOverMap k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
        ((fgSiteModule B hk).map f)) φ →
    b.1.hom ≫ φ = a.1.hom →
    ∃ e : (coefficientReductionBaseChange.{d, u + 1} (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)
          f).functor.obj (fibreLiftDerivedLift (hDer := hDer V) a hK).K.obj ≅
        (fibreLiftDerivedLift (hDer := hDer W) b hK).K.obj,
      (derivedExtensionOfScalarsData.{d, u + 1}
          (sqZeroExtSheafAnySiteProj
            ((coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj W))).baseChange.map
          e.hom ≫ (fibreLiftDerivedLift (hDer := hDer W) b hK).identification.hom =
        ((fibreLiftDerivedLift (hDer := hDer V) a hK).baseChange
          (coefficientReductionBaseChange.{d, u + 1}
            (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) f)).identification.hom ∧
      ∀ α : Aut (fibreLiftDerivedLift (hDer := hDer V) a hK).K.obj,
        φ.a.fibre ≫ (fibreDataComplexAut (hDer := hDer W) b.1.right.x b.1.hom.a
            (fibreLiftRetraction b) (fibreLiftSection_comp_retraction b)
            (isSquareZeroClosedImmersion_fibreLiftSection b) (fibreLiftScheme_left_eq b)
            (fibreLiftSection_conj b) hK
            (Aut.of (e.symm ≪≫ (coefficientReductionBaseChange.{d, u + 1}
              (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) f).functor.mapIso α.asIso ≪≫ e))).hom =
          ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap φ.a.base)).map
            (fibreDataComplexAut (hDer := hDer V) a.1.right.x a.1.hom.a
              (fibreLiftRetraction a) (fibreLiftSection_comp_retraction a)
              (isSquareZeroClosedImmersion_fibreLiftSection a) (fibreLiftScheme_left_eq a)
              (fibreLiftSection_conj a) hK α).hom ≫ φ.a.fibre

/-- The comparison of `AlgebraicGeometry.Space.ComplexesSituation.FibreLiftAutPullback` makes the
base change of the lift of `E₀` of `a` isomorphic to the lift of `E₀` of `b`: the input of
`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftClass_eq_liftClassMap_of_isomorphic`. -/
theorem FibreLiftAutPullback.isomorphic {hK : DerivedCategory.TStructure.t.minus x₀.E}
    (h : FibreLiftAutPullback (hDer := hDer) hK) {V W : FGModuleCat.{u} k} (f : V ⟶ W)
    (a : FibreLift D iΛ x₀ hx₀ hk ((fgSiteModule B hk).obj V))
    (b : FibreLift D iΛ x₀ hx₀ hk ((fgSiteModule B hk).obj W)) (φ : b.1.right ⟶ a.1.right)
    (hφ : (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
        (baseProj D.Y) (complexesToBaseObjects D)
        (schemePointToBase D.Y x₀.T.left x₀.T.hom)).IsHomLift
      (squareZeroOverMap k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
        ((fgSiteModule B hk).map f)) φ)
    (hw : b.1.hom ≫ φ = a.1.hom) :
    DerivedLift.Isomorphic
      ((fibreLiftDerivedLift (hDer := hDer V) a hK).baseChange
        (coefficientReductionBaseChange.{d, u + 1} (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) f))
      (fibreLiftDerivedLift (hDer := hDer W) b hK) :=
  Exists.elim (h f a b φ hφ hw) fun e he => ⟨e, he.1⟩

end ComplexesSituation

end AlgebraicGeometry.Space

end
