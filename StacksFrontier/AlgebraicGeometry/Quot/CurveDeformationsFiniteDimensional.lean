module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveDeformationsSchemes
public import StacksFrontier.Deformation.Examples.Geometric.SchemesFiniteDimensional
public import StacksFrontier.Deformation.Examples.Linear.RimSchlessingerTransportEquivalence
public import StacksFrontier.Deformation.Artin.FiniteDimensional.TangentTransfer
public import StacksFrontier.Deformation.Artin.FiniteDimensional.ChangeOfFieldsDescent
public import StacksFrontier.Deformation.ArtinCriteria.Predeformation
public import StacksFrontier.Deformation.ArtinCriteria.TangentSpace
public import StacksFrontier.Deformation.CofiberedPresentation.Criteria

/-!
# The deformation category of a curve over a field is finite dimensional
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Deformation Deformation.Examples

namespace AlgebraicGeometry.CurveDeformation

universe u

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase} {Λ k : Type u} [CommRing Λ]
  [Field k] [Algebra Λ k] {iΛ : Spec (.of Λ) ⟶ integerBase} (x : CurveFamily B hZ)
  (hx : (projection B hZ).obj x = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))

/-- The category of families of curves is fibred in groupoids over the big fppf site of the
integers, read in the slice over `Spec ℤ`. -/
theorem curvesProjectionOver_isFiberedInGroupoids :
    (curvesProjectionOver B hZ).IsFiberedInGroupoids :=
  Functor.IsFiberedInGroupoids.of_comp_over (B.obj hZ) (curvesProjection B hZ)
    (curvesProjectionOver B hZ) rfl (curvesProjection_isFiberedInGroupoids B hZ)

/-- The predeformation category of a family of curves over a field is a deformation category:
it is equivalent, over `𝒞_Λ`, to the deformation category of the underlying scheme. -/
theorem isDeformationCategory_predeformation :
    letI := (predeformation x hx).category
    IsDeformationCategory (predeformation x hx).projection := by
  let := (predeformation x hx).category
  have := toSchemeDeformationFunctor_full x hx
  have := toSchemeDeformationFunctor_faithful x hx
  have : (toSchemeDeformationFunctor x hx).EssSurj :=
    ⟨fun P => toSchemeDeformationFunctor_essSurj x hx P⟩
  have hpre := Artin.predeformationCategory_isPredeformationCategory B hZ iΛ
    (curvesProjectionOver B hZ) x hx curvesProjectionOver_isFiberedInGroupoids
  obtain ⟨E⟩ := hpre.specialFiber
  exact isDeformationCategory_comp_of_essSurj (toSchemeDeformationFunctor x hx)
    (schemeDeformationCategoryProjection (Λ := Λ) (scheme x hx)) hpre.cofibered
    ⟨E.inverse.obj ⟨PUnit.unit⟩⟩
    (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (scheme x hx))

/-- **Stacks Project, Tag 0D57, part (1).** Let `k` be a field and let `x = (X → Spec k)` be a
family of curves over `Spec k`, lying over `Spec k → Spec Λ → Spec ℤ`. Then the predeformation
category `𝓕_{𝒳,k,x}` over `𝒞_Λ` is a deformation category, its tangent space `T𝓕_{𝒳,k,x}` is a
finite-dimensional `k`-vector space, and so are its infinitesimal automorphisms
`Inf(𝓕_{𝒳,k,x})`, the kernel of `Aut_{k[ε]}(x'₀) → Aut_k(x₀)`, at every object of the special
fibre and for every choice of its pushforwards.

This generalizes the source: `k` need not be of finite type over `ℤ`, and `Λ` is any ring with
a `Λ`-algebra structure on `k` and any morphism `Spec Λ ⟶ Spec ℤ`. The proof identifies
`𝓕_{𝒳,k,x}` with the deformation category of the scheme `X` (the total space of a curve over a
field is a scheme, Stacks 0ADD) and applies the finiteness of Stacks 0DYA for that category, in
place of the source's appeal to Stacks 0D1K. -/
@[stacks 0D57 "(1): for a family of curves x over any field k and any Λ with Spec k → Spec Λ, \
the predeformation category F_{X,k,x} is a deformation category whose tangent space T F and \
infinitesimal automorphisms Inf(F) are finite dimensional; k need not be of finite type over Z"]
theorem finiteDimensional_predeformation :
    letI := (predeformation x hx).category
    ∃ hD : IsDeformationCategory.{u, u, u} (predeformation x hx).projection,
      (letI : Fact (IsPredeformationCategory
          (BasedCategory.ofFunctor (predeformation x hx).projection).p) := ⟨hD.predeformation⟩;
        letI : Fact (SchlessingerConditionS2 (CategoryOfElements.π
          (isomorphismClasses (BasedCategory.ofFunctor (predeformation x hx).projection)
            hD.predeformation.cofibered))) := ⟨tangentConditionS2.{u, u, u} hD⟩;
        FiniteDimensional k (artinianTangentSpace Λ k
          (isomorphismClasses (BasedCategory.ofFunctor (predeformation x hx).projection)
            hD.predeformation.cofibered))) ∧
      ∀ y, (predeformation x hx).projection.obj y = residueFieldObject.{u, u, u} Λ k →
        ∀ PF : ChosenPushforwardsAt (predeformation x hx).projection y,
          FiniteDimensional k ↥((infinitesimalAutomorphismLinearLift.{u, u, u} PF
            hD.satisfiesRS).functor.obj (FGModuleCat.of k (ULift.{u} k))) := by
  let := (predeformation x hx).category
  have := isProper_scheme_hom x hx
  have hD := isDeformationCategory_predeformation x hx
  have hDef := isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (scheme x hx)
  let Φ : BasedCategory.ofFunctor (predeformation x hx).projection ⥤ᵇ
      BasedCategory.ofFunctor (schemeDeformationCategoryProjection (Λ := Λ) (scheme x hx)) :=
    { toFunctor := toSchemeDeformationFunctor x hx
      w := rfl }
  have : Φ.toFunctor.Full := toSchemeDeformationFunctor_full x hx
  have : Φ.toFunctor.Faithful := toSchemeDeformationFunctor_faithful x hx
  refine ⟨hD, ?_, ?_⟩
  · have hfin := (finiteDimensional_artinianTangentSpace_iff_tangentModuleAt hDef).mp
      (finiteDimensional_schemeTangentSpace (Λ := Λ) (scheme x hx))
    exact (finiteDimensional_artinianTangentSpace_iff_tangentModuleAt hD).mpr
      (finiteDimensional_tangentModuleAt_of_fullyFaithful hD hDef Φ _ hfin)
  · intro y _ PF
    refine finiteDimensional_infinitesimalAutomorphismLinearLift_of_localized hD.satisfiesRS PF ?_
    exact finiteDimensional_localizedAutomorphismFunctorTangent_of_faithful
      (p := (predeformation x hx).projection)
      (q := schemeDeformationCategoryProjection (Λ := Λ) (scheme x hx))
      Φ.toFunctor Φ.w hD.satisfiesRS hDef.satisfiesRS PF
      (chosenPushforwardsAtOfCofiberedInGroupoids hDef.predeformation.cofibered _)
      (finiteDimensional_localizedAutomorphismFunctorTangent_schemeDeformation (scheme x hx) _)

end AlgebraicGeometry.CurveDeformation
