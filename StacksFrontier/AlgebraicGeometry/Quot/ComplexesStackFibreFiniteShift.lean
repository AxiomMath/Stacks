module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFibreFiniteExt
public import StacksFrontier.Deformation.ToposThickening.CoefficientExtUnitShift

/-!
# The fibre hypotheses of Stacks 0DLL at a shift of the complex of a field point

The coefficient lift comparisons of `Deformation.Artin.CoefficientLiftComparison` carry reference
lifts in `D^{≤ 0}`, so they exist only for complexes `K₀ ∈ D^{≤ 0}`. The complex `E₀` of a field
point `x₀` of `Complexes_{X/Y}` is bounded but in general not in `D^{≤ 0}`; its shift `E₀⟦m⟧` is,
for `m` large. This file states the two consumers of the bridge file
`StacksFrontier/AlgebraicGeometry/Quot/ComplexesStackFibreFiniteExt.lean` at `K₀ = E₀⟦m⟧`
(`fibreTangentFinite_of_coefficientLiftComparison_fieldPointShift`,
`fibreInfFinite_of_coefficientHom_fieldPointShift` in the namespace
`AlgebraicGeometry.Space.ComplexesSituation`),
the finiteness of Stacks 0D0T being moved across the shift by
`Deformation.ComplexLift.finiteDimensional_coefficientExt_unit_shift` and
`Deformation.ComplexLift.finiteDimensional_coefficientHom_unit_shift`.

`h0D0T` is **Stacks 0D0T, not yet proved here**.

Nothing here is registered.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
* [Stacks Project, Tag 0D0T](https://stacks.math.columbia.edu/tag/0D0T)
-/

@[expose] public noncomputable section

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify

namespace ComplexesSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : ComplexesSituation B S hS)

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

attribute [local instance] complexesCategory

open Deformation Deformation.Artin Deformation.ComplexLift

/-- **The tangent-space hypothesis on the fibre from a comparison with derived lifts of `E₀⟦m⟧`
and Stacks 0D0T.**
`AlgebraicGeometry.Space.ComplexesSituation.fibreTangentFinite_of_coefficientLiftComparison`
at the coefficient map of the field point
(`AlgebraicGeometry.Space.ComplexesSituation.fieldPointCoefficientMap`) and at `K₀ = E₀⟦m⟧`, the
shift putting `K₀` in `D^{≤ 0}` as the reference lifts of a comparison require, with the
finiteness of `Ext¹(E₀, E₀)` discharged by
`AlgebraicGeometry.Space.ComplexesSituation.finiteDimensional_coefficientExt_unit_of_fieldPoint`
and moved across the shift by
`Deformation.ComplexLift.finiteDimensional_coefficientExt_unit_shift`.

`h0D0T` is **Stacks 0D0T, not yet proved here**. -/
theorem fibreTangentFinite_of_coefficientLiftComparison_fieldPointShift
    (h0D0T : ∀ (A : Type u) [CommRing A] (hA : B.Contains (Spec (.of A)))
      (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
      (hX : IsAlgebraicSpace B (Spec (.of A)) hA X),
      letI : Linear A (Modules.{u, u} B (Spec (.of A)) hA X hX) :=
        Linear.ofRingHom (baseRingHom A B hA X hX)
      ∀ [IsNoetherianRing A] (f : X ⟶ yoneda.obj (baseObject A B hA)),
        IsProper B (Spec (.of A)) hA f →
        ∀ (K L : DerivedCategory (Modules.{u, u} B (Spec (.of A)) hA X hX)),
          DerivedCategoryB.derivedCategoryBMinus (isCoherent.{u, u} B (Spec (.of A)) hA X hX) K →
          DerivedCategoryB.derivedCategoryBPlus (isCoherent.{u, u} B (Spec (.of A)) hA X hX) L →
          ∀ n : ℤ, Module.Finite A (K ⟶ L⟦n⟧))
    (hfib : (complexesFunctor D).IsFiberedInGroupoids)
    (rsC : SatisfiesRSStar B S hS (complexesFunctor D) hfib)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
    (x₀ : ComplexesObject D)
    (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hk : B.Contains (Spec (.of k)))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    [∀ V : FGModuleCat.{u} k, HasDerivedCategory.{u + 1} (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)))]
    (m : ℤ) (hKm : DerivedCategory.TStructure.t.minus (x₀.E⟦m⟧))
    (Φ : CoefficientLiftComparison.{u + 1, u + 1} B S hS iΛ hk (complexesFunctor D) (baseProj D.Y)
      (Over.map x₀.T.left.hom) (complexesToBaseObjects D)
      (schemePointToBase D.Y x₀.T.left x₀.T.hom) (fibreBasePoint D x₀)
      (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk) (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)
      ⟨x₀.E⟦m⟧, hKm⟩) :
    FibreTangentFinite D iΛ x₀ hx₀ := by
  have := finiteDimensional_coefficientExt_unit_of_fieldPoint D h0D0T hk _ x₀.T
    (fieldPoint_left_eq D iΛ x₀ hx₀ hk) _
    (globalSectionRingHomOfHom_smallerBaseCoefficientMap _ _ _ _ _ _ _) x₀.E x₀.relativelyPerfect
  have := finiteDimensional_coefficientExt_unit_shift (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)
    x₀.E m
  exact fibreTangentFinite_of_coefficientLiftComparison D hfib rsC iΛ x₀ hx₀ hfinite hqc hk _ _ Φ

/-- **The infinitesimal-automorphism hypothesis on the fibre from the groups
`Hom(E₀, E₀ ⊗^L (𝒪 ⊗_k V))` and Stacks 0D0T.**
`AlgebraicGeometry.Space.ComplexesSituation.fibreInfFinite_of_coefficientHom` at the coefficient
map of the field point (`AlgebraicGeometry.Space.ComplexesSituation.fieldPointCoefficientMap`)
and at `K₀ = E₀⟦m⟧`, with the finiteness of `Ext⁰(E₀, E₀)` discharged by
`AlgebraicGeometry.Space.ComplexesSituation.finiteDimensional_coefficientHom_unit_of_fieldPoint`
and moved across the shift by
`Deformation.ComplexLift.finiteDimensional_coefficientHom_unit_shift`.

`h0D0T` is **Stacks 0D0T, not yet proved here**. -/
theorem fibreInfFinite_of_coefficientHom_fieldPointShift
    (h0D0T : ∀ (A : Type u) [CommRing A] (hA : B.Contains (Spec (.of A)))
      (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
      (hX : IsAlgebraicSpace B (Spec (.of A)) hA X),
      letI : Linear A (Modules.{u, u} B (Spec (.of A)) hA X hX) :=
        Linear.ofRingHom (baseRingHom A B hA X hX)
      ∀ [IsNoetherianRing A] (f : X ⟶ yoneda.obj (baseObject A B hA)),
        IsProper B (Spec (.of A)) hA f →
        ∀ (K L : DerivedCategory (Modules.{u, u} B (Spec (.of A)) hA X hX)),
          DerivedCategoryB.derivedCategoryBMinus (isCoherent.{u, u} B (Spec (.of A)) hA X hX) K →
          DerivedCategoryB.derivedCategoryBPlus (isCoherent.{u, u} B (Spec (.of A)) hA X hX) L →
          ∀ n : ℤ, Module.Finite A (K ⟶ L⟦n⟧))
    (hfib : (complexesFunctor D).IsFiberedInGroupoids)
    (rsC : SatisfiesRSStar B S hS (complexesFunctor D) hfib)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
    (x₀ : ComplexesObject D)
    (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hk : B.Contains (Spec (.of k)))
    [∀ V : FGModuleCat.{u} k, HasDerivedCategory.{u + 1} (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)))]
    (m : ℤ) (hKm : DerivedCategory.TStructure.t.minus (x₀.E⟦m⟧))
    (aut : ∀ V : FGModuleCat.{u} k,
      (coefficientHomLinearFunctor.{u + 1} (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)
        (x₀.E⟦m⟧)).obj V →
      (trivialDeformation k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
          (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
            (baseProj D.Y) (complexesToBaseObjects D) (schemePointToBase D.Y x₀.T.left x₀.T.hom))
          (fibreBasePoint D x₀) (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk)
          (TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ hfib
            (Functor.IsFiberedInGroupoids.over_map x₀.T.left.hom)
            (baseProj_isFiberedInGroupoids D.Y) (complexesToBaseObjects_comp D)
            (schemePointToBase_comp D.Y x₀.T.left x₀.T.hom))
          ((fgSiteModule B hk).obj V) ⟶
        trivialDeformation k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
          (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
            (baseProj D.Y) (complexesToBaseObjects D) (schemePointToBase D.Y x₀.T.left x₀.T.hom))
          (fibreBasePoint D x₀) (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk)
          (TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ hfib
            (Functor.IsFiberedInGroupoids.over_map x₀.T.left.hom)
            (baseProj_isFiberedInGroupoids D.Y) (complexesToBaseObjects_comp D)
            (schemePointToBase_comp D.Y x₀.T.left x₀.T.hom))
          ((fgSiteModule B hk).obj V)))
    (haut : ∀ {V W : FGModuleCat.{u} k} (f : V ⟶ W)
      (g : (coefficientHomLinearFunctor.{u + 1} (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)
        (x₀.E⟦m⟧)).obj V),
      aut W ((coefficientHomLinearFunctor.{u + 1} (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)
        (x₀.E⟦m⟧)).map f g) =
        (infinitesimalAutomorphismSetFunctor k B S hS
          (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
          (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
            (baseProj D.Y) (complexesToBaseObjects D) (schemePointToBase D.Y x₀.T.left x₀.T.hom))
          (fibreBasePoint D x₀) (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk)
          (TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ hfib
            (Functor.IsFiberedInGroupoids.over_map x₀.T.left.hom)
            (baseProj_isFiberedInGroupoids D.Y) (complexesToBaseObjects_comp D)
            (schemePointToBase_comp D.Y x₀.T.left x₀.T.hom))).map
          ((fgSiteModule B hk).map f) (aut V g))
    (hsurj : Function.Surjective (aut (FGModuleCat.of k k))) :
    FibreInfFinite D iΛ x₀ hx₀ := by
  have := finiteDimensional_coefficientHom_unit_of_fieldPoint D h0D0T hk _ x₀.T
    (fieldPoint_left_eq D iΛ x₀ hx₀ hk) _
    (globalSectionRingHomOfHom_smallerBaseCoefficientMap _ _ _ _ _ _ _) x₀.E x₀.relativelyPerfect
  have := finiteDimensional_coefficientHom_unit_shift (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)
    x₀.E m
  exact fibreInfFinite_of_coefficientHom D hfib rsC iΛ x₀ hx₀ hk _ (K₀ := ⟨x₀.E⟦m⟧, hKm⟩) aut haut
    hsurj


/-- **The tangent-space hypothesis on the fibre from a comparison with derived lifts of `E₀⟦m⟧`**
(unregistered): `fibreTangentFinite_of_coefficientLiftComparison_fieldPointShift` with its
hypothesis `h0D0T` discharged by Stacks 0D0T,
`AlgebraicGeometry.Space.moduleFinite_hom_shift_of_isProper_ofRingHom` (the base's
`AlgebraicGeometry.Space.moduleFinite_hom_shift_of_isProper`). -/
theorem fibreTangentFinite_fieldPointShift_of_coefficientLiftComparison
    (hfib : (complexesFunctor D).IsFiberedInGroupoids)
    (rsC : SatisfiesRSStar B S hS (complexesFunctor D) hfib)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
    (x₀ : ComplexesObject D)
    (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hk : B.Contains (Spec (.of k)))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    [∀ V : FGModuleCat.{u} k, HasDerivedCategory.{u + 1} (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)))]
    (m : ℤ) (hKm : DerivedCategory.TStructure.t.minus (x₀.E⟦m⟧))
    (Φ : CoefficientLiftComparison.{u + 1, u + 1} B S hS iΛ hk (complexesFunctor D) (baseProj D.Y)
      (Over.map x₀.T.left.hom) (complexesToBaseObjects D)
      (schemePointToBase D.Y x₀.T.left x₀.T.hom) (fibreBasePoint D x₀)
      (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk) (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)
      ⟨x₀.E⟦m⟧, hKm⟩) :
    FibreTangentFinite D iΛ x₀ hx₀ :=
  fibreTangentFinite_of_coefficientLiftComparison_fieldPointShift D
    (fun A _ hA X hX => moduleFinite_hom_shift_of_isProper_ofRingHom B A hA X hX)
    hfib rsC iΛ x₀ hx₀ hk hfinite hqc m hKm Φ

/-- **The infinitesimal-automorphism hypothesis on the fibre from the groups
`Hom(E₀, E₀ ⊗^L (𝒪 ⊗_k V))`** (unregistered):
`AlgebraicGeometry.Space.ComplexesSituation.fibreInfFinite_of_coefficientHom_fieldPointShift` with
its hypothesis `h0D0T` discharged by Stacks 0D0T,
`AlgebraicGeometry.Space.moduleFinite_hom_shift_of_isProper_ofRingHom` (the base's
`AlgebraicGeometry.Space.moduleFinite_hom_shift_of_isProper`). -/
theorem fibreInfFinite_fieldPointShift_of_coefficientHom
    (hfib : (complexesFunctor D).IsFiberedInGroupoids)
    (rsC : SatisfiesRSStar B S hS (complexesFunctor D) hfib)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
    (x₀ : ComplexesObject D)
    (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hk : B.Contains (Spec (.of k)))
    [∀ V : FGModuleCat.{u} k, HasDerivedCategory.{u + 1} (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)))]
    (m : ℤ) (hKm : DerivedCategory.TStructure.t.minus (x₀.E⟦m⟧))
    (aut : ∀ V : FGModuleCat.{u} k,
      (coefficientHomLinearFunctor.{u + 1} (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)
        (x₀.E⟦m⟧)).obj V →
      (trivialDeformation k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
          (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
            (baseProj D.Y) (complexesToBaseObjects D) (schemePointToBase D.Y x₀.T.left x₀.T.hom))
          (fibreBasePoint D x₀) (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk)
          (TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ hfib
            (Functor.IsFiberedInGroupoids.over_map x₀.T.left.hom)
            (baseProj_isFiberedInGroupoids D.Y) (complexesToBaseObjects_comp D)
            (schemePointToBase_comp D.Y x₀.T.left x₀.T.hom))
          ((fgSiteModule B hk).obj V) ⟶
        trivialDeformation k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
          (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
            (baseProj D.Y) (complexesToBaseObjects D) (schemePointToBase D.Y x₀.T.left x₀.T.hom))
          (fibreBasePoint D x₀) (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk)
          (TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ hfib
            (Functor.IsFiberedInGroupoids.over_map x₀.T.left.hom)
            (baseProj_isFiberedInGroupoids D.Y) (complexesToBaseObjects_comp D)
            (schemePointToBase_comp D.Y x₀.T.left x₀.T.hom))
          ((fgSiteModule B hk).obj V)))
    (haut : ∀ {V W : FGModuleCat.{u} k} (f : V ⟶ W)
      (g : (coefficientHomLinearFunctor.{u + 1} (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)
        (x₀.E⟦m⟧)).obj V),
      aut W ((coefficientHomLinearFunctor.{u + 1} (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)
        (x₀.E⟦m⟧)).map f g) =
        (infinitesimalAutomorphismSetFunctor k B S hS
          (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
          (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
            (baseProj D.Y) (complexesToBaseObjects D) (schemePointToBase D.Y x₀.T.left x₀.T.hom))
          (fibreBasePoint D x₀) (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk)
          (TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ hfib
            (Functor.IsFiberedInGroupoids.over_map x₀.T.left.hom)
            (baseProj_isFiberedInGroupoids D.Y) (complexesToBaseObjects_comp D)
            (schemePointToBase_comp D.Y x₀.T.left x₀.T.hom))).map
          ((fgSiteModule B hk).map f) (aut V g))
    (hsurj : Function.Surjective (aut (FGModuleCat.of k k))) :
    FibreInfFinite D iΛ x₀ hx₀ :=
  fibreInfFinite_of_coefficientHom_fieldPointShift D
    (fun A _ hA X hX => moduleFinite_hom_shift_of_isProper_ofRingHom B A hA X hX)
    hfib rsC iΛ x₀ hx₀ hk m hKm aut haut hsurj

end ComplexesSituation

end AlgebraicGeometry.Space

end
