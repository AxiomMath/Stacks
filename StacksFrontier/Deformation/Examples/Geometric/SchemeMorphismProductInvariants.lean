module

public import StacksFrontier.Deformation.Cofibered.ProductInvariants
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismSixTermExactInterior
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismsRimSchlessingerUnconditional
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismEndpointsSupplied

/-!
# The terms `Inf(Def_X × Def_Y)` and `T(Def_X × Def_Y)` of Stacks 0E3V

Let `f : X → Y` be a morphism of schemes over a field `k`, in the setting of Example 0DY7.
The second and the fifth terms of the exact sequence of [Stacks Project, Tag 0E3V] are
`Inf(Def_X × Def_Y)` and `T(Def_X × Def_Y)`: the infinitesimal automorphisms and the tangent
space of the product `Def_X × Def_Y` of the deformation categories of the two endpoints, the
product of Tag 0DZJ (`Deformation.cofiberedProduct`, the `2`-fibre product `Def_X ×_{𝒞_Λ} Def_Y`
over the base category). The arrows of the sequence out of `Inf(Def_{X → Y})` and out of
`T Def_{X → Y}` are induced by the obvious morphism of deformation categories
`Def_{X → Y} → Def_X × Def_Y`.

The library states those two arrows, `Deformation.Examples.schemeMorphismInfinitesimalPair'` and
`Deformation.Examples.schemeMorphismTangentPair'`, as maps into `Inf(Def_X) × Inf(Def_Y)` and into
`T Def_X × T Def_Y`: the pairs of the maps induced by the two endpoint-forgetting morphisms. This
file identifies the source's terms with those, and the source's arrows with the library's:

* `Def_X × Def_Y` is a deformation category
  (`Deformation.Examples.isDeformationCategory_schemeEndpointsProduct`);
* `Inf(Def_X × Def_Y) ≃ₗ[k] Inf(Def_X) × Inf(Def_Y)`
  (`Deformation.Examples.schemeEndpointsProductInfEquiv`) and
  `T(Def_X × Def_Y) ≃ₗ[k] T Def_X × T Def_Y`
  (`Deformation.Examples.schemeEndpointsProductTangentEquiv`), each the pair of the maps induced
  by the two projections of the product;
* the library's arrows are the maps induced by `Def_{X → Y} → Def_X × Def_Y`
  (`Deformation.Examples.schemeMorphismEndpointsBased`) followed by these equivalences
  (`Deformation.Examples.schemeMorphismInfinitesimalPair'_apply_eq`,
  `Deformation.Examples.schemeMorphismTangentPair'_eq`), and at the canonical data of the
  six-term sequence (`Deformation.Examples.schemeMorphismInfinitesimalPair'_canonical_eq`).

## Main definitions

* `Deformation.Examples.schemeEndpointsProduct`: the product `Def_X × Def_Y`.
* `Deformation.Examples.schemeMorphismEndpointsBased`: the morphism
  `Def_{X → Y} → Def_X × Def_Y` of deformation categories.
* `Deformation.Examples.schemeEndpointsProductPushforwards`: the chosen pushforwards of the base
  point of `Def_X × Def_Y`, the image of the trivial deformation of `f`, obtained from the fixed
  pushforwards of that trivial deformation.
* `Deformation.Examples.schemeEndpointsProductInfEquiv`,
  `Deformation.Examples.schemeEndpointsProductTangentEquiv`: the two identifications.

## References

* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
* [Stacks Project, Tag 0DZJ](https://stacks.math.columbia.edu/tag/0DZJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (pX : X ⟶ baseSpec (residueFieldBase Λ k)) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
  (hf : f ≫ pY = pX)

/-! ### The product `Def_X × Def_Y` and the morphism into it -/

/-- The product `Def_X × Def_Y` of the deformation categories of the two endpoints of `f`: the
product of Tag 0DZJ, i.e. their `2`-fibre product over `𝒞_Λ`. -/
abbrev schemeEndpointsProduct : BasedCategory (ArtinianLocalAlgCat.{u, u, u} Λ k) :=
  cofiberedProduct
    (BasedCategory.ofFunctor (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
    (BasedCategory.ofFunctor (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)))

/-- `Def_X × Def_Y` is a deformation category. -/
theorem isDeformationCategory_schemeEndpointsProduct :
    IsDeformationCategory.{u, u, u} (schemeEndpointsProduct (Λ := Λ) (k := k) pX pY).p :=
  isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id
    (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX))
    (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY))

/-- **The morphism `Def_{X → Y} → Def_X × Def_Y` of Tag 0E3V**: a deformation of `f` goes to the
pair of the deformations of its source and of its target. -/
def schemeMorphismEndpointsBased :
    BasedCategory.ofFunctor (schemeMorphismDeformationCategoryProjection f pX pY hf) ⥤ᵇ
      schemeEndpointsProduct (Λ := Λ) (k := k) pX pY :=
  cofiberedProductLift (schemeMorphismSourceBased f pX pY hf) (schemeMorphismTargetBased f pX pY hf)

/-! ### The tangent term -/

/-- **`T(Def_X × Def_Y) ≃ₗ[k] T Def_X × T Def_Y`**, at every coordinate module `M` (the tangent
space proper being the rank-one module, i.e. first-order deformations over `k[ε]`): the pair of
the maps induced by the two projections of the product. -/
def schemeEndpointsProductTangentEquiv (M : FGModuleCat.{u} k) :
    ↥(tangentModuleAt.{u, u, u} (schemeEndpointsProduct (Λ := Λ) (k := k) pX pY)
        (isDeformationCategory_schemeEndpointsProduct pX pY) M) ≃ₗ[k]
      ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
          (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
          (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)) M) ×
        ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
          (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)))
          (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)) M) :=
  cofiberedProductTangentEquiv
    (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX))
    (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)) M

/-- **The arrow `T Def_{X → Y} → T(Def_X × Def_Y)` of Tag 0E3V**: the library's
`Deformation.Examples.schemeMorphismTangentPair'` is the map induced on tangent modules by
`Def_{X → Y} → Def_X × Def_Y` followed by the identification
`T(Def_X × Def_Y) ≅ T Def_X × T Def_Y`. -/
theorem schemeMorphismTangentPair'_eq
    (hM : IsDeformationCategory.{u, u, u}
      (schemeMorphismDeformationCategoryProjection f pX pY hf))
    (M : FGModuleCat.{u} k) :
    schemeMorphismTangentPair' f pX pY hf hM M =
      (schemeEndpointsProductTangentEquiv pX pY M).toLinearMap ∘ₗ
        tangentMapAt.{u, u, u} hM (isDeformationCategory_schemeEndpointsProduct pX pY)
          (schemeMorphismEndpointsBased f pX pY hf) M :=
  prod_tangentMapAt_eq_cofiberedProductTangentEquiv_comp
    (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX))
    (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)) hM
    (schemeMorphismSourceBased f pX pY hf) (schemeMorphismTargetBased f pX pY hf) M

/-! ### The infinitesimal term -/

/-- **`Inf(Def_X × Def_Y) ≃ₗ[k] Inf(Def_X) × Inf(Def_Y)`** at a base point `w₀` of
`Def_X × Def_Y` and its two components, with the `k`-structures of Tag 06JV at the given choices
of pushforwards: the pair of the maps induced by the two projections of the product. -/
def schemeEndpointsProductInfEquivAt
    {w₀ : (schemeEndpointsProduct (Λ := Λ) (k := k) pX pY).obj}
    (PW : ChosenPushforwardsAt (schemeEndpointsProduct (Λ := Λ) (k := k) pX pY).p w₀)
    (QX : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))
      ((cofiberedProductFst _ _).obj w₀))
    (QY : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))
      ((cofiberedProductSnd _ _).obj w₀)) :
    letI := naturalLocalizedTangentAddCommGroup PW
      (isDeformationCategory_schemeEndpointsProduct pX pY).satisfiesRS
    letI := naturalLocalizedTangentModule PW
      (isDeformationCategory_schemeEndpointsProduct pX pY).satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup QX
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
    letI := naturalLocalizedTangentModule QX
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup QY
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
    letI := naturalLocalizedTangentModule QY
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
    localizedAutomorphismFunctorTangent PW ≃ₗ[k]
      localizedAutomorphismFunctorTangent QX × localizedAutomorphismFunctorTangent QY :=
  cofiberedProductInfEquiv
    (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX))
    (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)) PW QX QY

/-- **The arrow `Inf(Def_{X → Y}) → Inf(Def_X × Def_Y)` of Tag 0E3V**, at an arbitrary base
point and choices of pushforwards: the library's
`Deformation.Examples.schemeMorphismInfinitesimalPair'` is the map induced on infinitesimal
automorphisms by `Def_{X → Y} → Def_X × Def_Y` followed by the identification
`Inf(Def_X × Def_Y) ≅ Inf(Def_X) × Inf(Def_Y)`. -/
theorem schemeMorphismInfinitesimalPair'_apply_eq
    (hM : SatisfiesRS (schemeMorphismDeformationCategoryProjection f pX pY hf))
    {x₀ : schemeMorphismDeformationCategory f pX pY hf}
    (PM : ChosenPushforwardsAt (schemeMorphismDeformationCategoryProjection f pX pY hf) x₀)
    (PW : ChosenPushforwardsAt (schemeEndpointsProduct (Λ := Λ) (k := k) pX pY).p
      ((schemeMorphismEndpointsBased f pX pY hf).obj x₀))
    (QX : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))
      ((schemeMorphismSourceForgetful f pX pY hf).obj x₀))
    (QY : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))
      ((schemeMorphismTargetForgetful f pX pY hf).obj x₀)) :
    letI := naturalLocalizedTangentAddCommGroup PM hM
    letI := naturalLocalizedTangentModule PM hM
    letI := naturalLocalizedTangentAddCommGroup PW
      (isDeformationCategory_schemeEndpointsProduct pX pY).satisfiesRS
    letI := naturalLocalizedTangentModule PW
      (isDeformationCategory_schemeEndpointsProduct pX pY).satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup QX
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
    letI := naturalLocalizedTangentModule QX
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup QY
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
    letI := naturalLocalizedTangentModule QY
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
    ∀ t : localizedAutomorphismFunctorTangent PM,
      schemeMorphismInfinitesimalPair' f pX pY hf hM PM QX QY t =
        schemeEndpointsProductInfEquivAt pX pY PW QX QY
          (inducedInfinitesimalLinearMapOfEq (schemeMorphismEndpointsBased f pX pY hf).toFunctor
            (schemeMorphismEndpointsBased f pX pY hf).w hM
            (isDeformationCategory_schemeEndpointsProduct pX pY).satisfiesRS PM PW t) :=
  prod_inducedInfinitesimalLinearMapOfEq_apply_eq_cofiberedProductInfEquiv
    (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX))
    (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)) hM
    (schemeMorphismSourceBased f pX pY hf) (schemeMorphismTargetBased f pX pY hf) PM PW QX QY

/-! ### At the canonical data of the six-term sequence -/

/-- The chosen pushforwards of the base point of `Def_X × Def_Y`, the image of the trivial
deformation of `f`: the images of the fixed pushforwards
`Deformation.Examples.schemeMorphismTrivialPushforwards` of the trivial deformation. -/
def schemeEndpointsProductPushforwards :
    ChosenPushforwardsAt (schemeEndpointsProduct (Λ := Λ) (k := k) pX pY).p
      ((schemeMorphismEndpointsBased f pX pY hf).obj (schemeMorphismTrivialObject f pX pY hf)) :=
  ChosenPushforwardsAt.ofComp (schemeMorphismEndpointsBased f pX pY hf).toFunctor
    (isDeformationCategory_schemeEndpointsProduct pX pY).predeformation.cofibered
    (schemeMorphismTrivialPushforwards f pX pY hf)

/-- **`Inf(Def_X × Def_Y) ≃ₗ[k] Inf(Def_X) × Inf(Def_Y)` at the canonical data of Tag 0E3V**: at
the image of the trivial deformation of `f`, with the pushforwards
`Deformation.Examples.schemeEndpointsProductPushforwards`,
`Deformation.Examples.schemeMorphismSourcePushforwards` and
`Deformation.Examples.schemeMorphismTargetPushforwards` at which the six-term sequence is
stated. -/
def schemeEndpointsProductInfEquiv :
    letI := naturalLocalizedTangentAddCommGroup (schemeEndpointsProductPushforwards f pX pY hf)
      (isDeformationCategory_schemeEndpointsProduct pX pY).satisfiesRS
    letI := naturalLocalizedTangentModule (schemeEndpointsProductPushforwards f pX pY hf)
      (isDeformationCategory_schemeEndpointsProduct pX pY).satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup (schemeMorphismSourcePushforwards f pX pY hf)
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
    letI := naturalLocalizedTangentModule (schemeMorphismSourcePushforwards f pX pY hf)
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup (schemeMorphismTargetPushforwards f pX pY hf)
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
    letI := naturalLocalizedTangentModule (schemeMorphismTargetPushforwards f pX pY hf)
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
    localizedAutomorphismFunctorTangent (schemeEndpointsProductPushforwards f pX pY hf) ≃ₗ[k]
      localizedAutomorphismFunctorTangent (schemeMorphismSourcePushforwards f pX pY hf) ×
        localizedAutomorphismFunctorTangent (schemeMorphismTargetPushforwards f pX pY hf) :=
  schemeEndpointsProductInfEquivAt pX pY (schemeEndpointsProductPushforwards f pX pY hf)
    (schemeMorphismSourcePushforwards f pX pY hf) (schemeMorphismTargetPushforwards f pX pY hf)

/-- **The arrow `Inf(Def_{X → Y}) → Inf(Def_X × Def_Y)` of Tag 0E3V at the canonical data**: the
first arrow of `Deformation.Examples.schemeMorphismDeformation_exact_inf_der_tangent` is the map
induced on infinitesimal automorphisms by `Def_{X → Y} → Def_X × Def_Y` followed by the
identification `Inf(Def_X × Def_Y) ≅ Inf(Def_X) × Inf(Def_Y)`. -/
theorem schemeMorphismInfinitesimalPair'_canonical_eq :
    letI := naturalLocalizedTangentAddCommGroup (schemeMorphismTrivialPushforwards f pX pY hf)
      (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf).satisfiesRS
    letI := naturalLocalizedTangentModule (schemeMorphismTrivialPushforwards f pX pY hf)
      (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf).satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup (schemeEndpointsProductPushforwards f pX pY hf)
      (isDeformationCategory_schemeEndpointsProduct pX pY).satisfiesRS
    letI := naturalLocalizedTangentModule (schemeEndpointsProductPushforwards f pX pY hf)
      (isDeformationCategory_schemeEndpointsProduct pX pY).satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup (schemeMorphismSourcePushforwards f pX pY hf)
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
    letI := naturalLocalizedTangentModule (schemeMorphismSourcePushforwards f pX pY hf)
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup (schemeMorphismTargetPushforwards f pX pY hf)
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
    letI := naturalLocalizedTangentModule (schemeMorphismTargetPushforwards f pX pY hf)
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
    ∀ t : localizedAutomorphismFunctorTangent (schemeMorphismTrivialPushforwards f pX pY hf),
      schemeMorphismInfinitesimalPair' f pX pY hf
          (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf).satisfiesRS
          (schemeMorphismTrivialPushforwards f pX pY hf)
          (schemeMorphismSourcePushforwards f pX pY hf)
          (schemeMorphismTargetPushforwards f pX pY hf) t =
        schemeEndpointsProductInfEquiv f pX pY hf
          (inducedInfinitesimalLinearMapOfEq (schemeMorphismEndpointsBased f pX pY hf).toFunctor
            (schemeMorphismEndpointsBased f pX pY hf).w
            (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY
              hf).satisfiesRS
            (isDeformationCategory_schemeEndpointsProduct pX pY).satisfiesRS
            (schemeMorphismTrivialPushforwards f pX pY hf)
            (schemeEndpointsProductPushforwards f pX pY hf) t) :=
  schemeMorphismInfinitesimalPair'_apply_eq f pX pY hf
    (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf).satisfiesRS
    (schemeMorphismTrivialPushforwards f pX pY hf) (schemeEndpointsProductPushforwards f pX pY hf)
    (schemeMorphismSourcePushforwards f pX pY hf) (schemeMorphismTargetPushforwards f pX pY hf)

end Deformation.Examples
