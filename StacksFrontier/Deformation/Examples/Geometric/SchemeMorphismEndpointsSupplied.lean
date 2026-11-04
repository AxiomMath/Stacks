module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismEndpoints
public import StacksFrontier.Deformation.Examples.Geometric.SchemesDeformationCategory

/-!
# The endpoint arrows of Tag 0E3V with the endpoint inputs supplied

`StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismEndpoints` builds the two arrows
`Inf(Def_{X ⟶ Y}) → Inf(Def_X) × Inf(Def_Y)` and `T Def_{X ⟶ Y} → T Def_X × T Def_Y` of
[Stacks Project, Tag 0E3V] and the three assertions about them, taking all three deformation
hypotheses — `hM` on `Def_{X ⟶ Y}` and `hX`, `hY` on the two endpoint categories — as inputs,
because the interior arrows of the sequence are built at an arbitrary such triple.

The primed declarations here supply `hX` and `hY` from
`Deformation.Examples.isDeformationCategory_schemeDeformationCategoryProjection`, the
fixed-scheme clause of [Stacks Project, Tag 0DY8], which holds for every scheme over the residue
field with no hypothesis; they are what the full statement of Tag 0E3V,
`Deformation.Examples.schemeMorphismDeformation_sixTermExact`, uses, since the source assumes
nothing about `Def_X` and `Def_Y`. The one input they still take is `hM`, the deformation
condition on `Def_{X ⟶ Y}`, which
`Deformation.Examples.isDeformationCategory_schemeMorphismDeformationCategoryProjection` proves.

## Main definitions

* `Deformation.Examples.schemeMorphismInfinitesimalPair'`,
  `Deformation.Examples.schemeMorphismTangentPair'`: the two arrows with the two endpoint
  inputs supplied.

## Main results

* `Deformation.Examples.injective_schemeMorphismInfinitesimalPair'`,
  `Deformation.Examples.exists_schemeMorphismTangentPair'_eq_iff`,
  `Deformation.Examples.schemeMorphismDeformation_endpointArrows'`.

## References

* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
* [Stacks Project, Tag 0DY8](https://stacks.math.columbia.edu/tag/0DY8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

section TargetForgetful

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (pX : X ⟶ baseSpec (residueFieldBase Λ k)) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
  (hf : f ≫ pY = pX)

/-! ### The same two arrows with the endpoint inputs supplied -/

/-- The arrow `Inf(Def_{X ⟶ Y}) → Inf(Def_X × Def_Y)` with its two endpoint inputs supplied.
This is `Deformation.Examples.schemeMorphismInfinitesimalPair` at the proofs that `Def_X` and
`Def_Y` are deformation categories, which
`Deformation.Examples.isDeformationCategory_schemeDeformationCategoryProjection` gives for every
scheme over the residue field with no hypothesis. -/
def schemeMorphismInfinitesimalPair'
    (hM : SatisfiesRS (schemeMorphismDeformationCategoryProjection f pX pY hf))
    {x₀ : schemeMorphismDeformationCategory f pX pY hf}
    (PM : ChosenPushforwardsAt (schemeMorphismDeformationCategoryProjection f pX pY hf) x₀)
    (QX : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))
      ((schemeMorphismSourceForgetful f pX pY hf).obj x₀))
    (QY : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))
      ((schemeMorphismTargetForgetful f pX pY hf).obj x₀)) :
    letI := naturalLocalizedTangentAddCommGroup PM hM
    letI := naturalLocalizedTangentModule PM hM
    letI := naturalLocalizedTangentAddCommGroup QX
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
    letI := naturalLocalizedTangentModule QX
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup QY
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
    letI := naturalLocalizedTangentModule QY
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
    localizedAutomorphismFunctorTangent PM →ₗ[k]
      localizedAutomorphismFunctorTangent QX × localizedAutomorphismFunctorTangent QY :=
  schemeMorphismInfinitesimalPair f pX pY hf hM
    (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
    (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
    PM QX QY

/-- **Stacks 0E3V, exactness at the first spot**, with the two endpoint inputs supplied. The
arrow `Inf(Def_{X ⟶ Y}) → Inf(Def_X × Def_Y)` is injective, so the sequence
`0 → Inf(Def_{X ⟶ Y}) → Inf(Def_X × Def_Y)` is exact. This is
`Deformation.Examples.injective_schemeMorphismInfinitesimalPair` at the proofs that `Def_X` and
`Def_Y` are deformation categories. -/
theorem injective_schemeMorphismInfinitesimalPair'
    (hM : SatisfiesRS (schemeMorphismDeformationCategoryProjection f pX pY hf))
    {x₀ : schemeMorphismDeformationCategory f pX pY hf}
    (PM : ChosenPushforwardsAt (schemeMorphismDeformationCategoryProjection f pX pY hf) x₀)
    (QX : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))
      ((schemeMorphismSourceForgetful f pX pY hf).obj x₀))
    (QY : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))
      ((schemeMorphismTargetForgetful f pX pY hf).obj x₀)) :
    letI := naturalLocalizedTangentAddCommGroup PM hM
    letI := naturalLocalizedTangentModule PM hM
    letI := naturalLocalizedTangentAddCommGroup QX
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
    letI := naturalLocalizedTangentModule QX
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup QY
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
    letI := naturalLocalizedTangentModule QY
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
    Function.Injective (schemeMorphismInfinitesimalPair' f pX pY hf hM PM QX QY) :=
  injective_schemeMorphismInfinitesimalPair f pX pY hf hM
    (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
    (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
    PM QX QY

/-- The arrow `T Def_{X ⟶ Y} → T(Def_X × Def_Y)` with its two endpoint inputs supplied. This is
`Deformation.Examples.schemeMorphismTangentPair` at the proofs that `Def_X` and `Def_Y` are
deformation categories. -/
def schemeMorphismTangentPair'
    (hM : IsDeformationCategory.{u, u, u}
      (schemeMorphismDeformationCategoryProjection f pX pY hf))
    (M : FGModuleCat.{u} k) :
    ↥(tangentModuleAt.{u, u, u}
        (BasedCategory.ofFunctor (schemeMorphismDeformationCategoryProjection f pX pY hf))
        hM M) →ₗ[k]
      ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
          (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
          (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)) M) ×
        ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
          (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)))
          (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)) M) :=
  schemeMorphismTangentPair f pX pY hf hM
    (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX))
    (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)) M

/-- The arrow `schemeMorphismTangentPair'` sends a tangent vector `t` of `Def_{X ⟶ Y}` to the pair
of its images under the tangent maps to `Def_X` and `Def_Y`. -/
@[simp]
theorem schemeMorphismTangentPair'_apply
    (hM : IsDeformationCategory.{u, u, u}
      (schemeMorphismDeformationCategoryProjection f pX pY hf))
    (M : FGModuleCat.{u} k)
    (t : ↥(tangentModuleAt.{u, u, u}
      (BasedCategory.ofFunctor (schemeMorphismDeformationCategoryProjection f pX pY hf))
      hM M)) :
    schemeMorphismTangentPair' f pX pY hf hM M t =
      (tangentMapAt.{u, u, u} hM
          (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX))
          (schemeMorphismSourceBased f pX pY hf) M t,
        tangentMapAt.{u, u, u} hM
          (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY))
          (schemeMorphismTargetBased f pX pY hf) M t) :=
  rfl

/-- **Stacks 0E3V**, the image of the arrow `T Def_{X ⟶ Y} → T(Def_X × Def_Y)`, with the two
endpoint inputs supplied. A pair of first-order deformations `X_ε` of `X` and `Y_ε` of `Y` is in
the image exactly when `f` deforms along it. This is
`Deformation.Examples.exists_schemeMorphismTangentPair_eq_iff` at the proofs that `Def_X` and
`Def_Y` are deformation categories. -/
theorem exists_schemeMorphismTangentPair'_eq_iff
    (hM : IsDeformationCategory.{u, u, u}
      (schemeMorphismDeformationCategoryProjection f pX pY hf))
    (M : FGModuleCat.{u} k)
    (xε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)).Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))
    (yε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)) :
    (∃ t, schemeMorphismTangentPair' f pX pY hf hM M t =
        (tangentClassAt.{u, u, u} (BasedCategory.ofFunctor
            (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
            (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)) M xε,
          tangentClassAt.{u, u, u} (BasedCategory.ofFunctor
            (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)))
            (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)) M yε)) ↔
      ∃ mε : (schemeMorphismDeformationCategoryProjection f pX pY hf).Fiber
          ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M),
        IsIsomorphic ((fiberFunctor (schemeMorphismSourceBased f pX pY hf)
            ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).obj mε) xε ∧
          IsIsomorphic ((fiberFunctor (schemeMorphismTargetBased f pX pY hf)
            ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).obj mε) yε :=
  exists_schemeMorphismTangentPair_eq_iff f pX pY hf hM
    (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX))
    (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)) M xε yε

/-- **Stacks 0E3V, the part of the six-term exact sequence that this file establishes**, with
the two endpoint inputs supplied. This is
`Deformation.Examples.schemeMorphismDeformation_endpointArrows` at the proofs that `Def_X` and
`Def_Y` are deformation categories, so the only input left is condition (RS) for the category
of all flat families of morphisms of schemes, the first assertion of
[Stacks Project, Tag 0E3U]. -/
theorem schemeMorphismDeformation_endpointArrows'
    (hM : IsDeformationCategory.{u, u, u}
      (schemeMorphismDeformationCategoryProjection f pX pY hf))
    {x₀ : schemeMorphismDeformationCategory f pX pY hf}
    (PM : ChosenPushforwardsAt (schemeMorphismDeformationCategoryProjection f pX pY hf) x₀)
    (QX : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))
      ((schemeMorphismSourceForgetful f pX pY hf).obj x₀))
    (QY : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))
      ((schemeMorphismTargetForgetful f pX pY hf).obj x₀))
    (M : FGModuleCat.{u} k) :
    letI := naturalLocalizedTangentAddCommGroup PM hM.satisfiesRS
    letI := naturalLocalizedTangentModule PM hM.satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup QX
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
    letI := naturalLocalizedTangentModule QX
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup QY
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
    letI := naturalLocalizedTangentModule QY
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
    Function.Injective (schemeMorphismInfinitesimalPair' f pX pY hf hM.satisfiesRS PM QX QY) ∧
      (∀ t, schemeMorphismTangentPair' f pX pY hf hM M t =
        (tangentMapAt.{u, u, u} hM
            (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX))
            (schemeMorphismSourceBased f pX pY hf) M t,
          tangentMapAt.{u, u, u} hM
            (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY))
            (schemeMorphismTargetBased f pX pY hf) M t)) ∧
      ∀ (xε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)).Fiber
          ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))
        (yε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).Fiber
          ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)),
        (∃ t, schemeMorphismTangentPair' f pX pY hf hM M t =
            (tangentClassAt.{u, u, u} (BasedCategory.ofFunctor
                (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
                (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)) M xε,
              tangentClassAt.{u, u, u} (BasedCategory.ofFunctor
                (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)))
                (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY))
                M yε)) ↔
          ∃ mε : (schemeMorphismDeformationCategoryProjection f pX pY hf).Fiber
              ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M),
            IsIsomorphic ((fiberFunctor (schemeMorphismSourceBased f pX pY hf)
                ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).obj mε) xε ∧
              IsIsomorphic ((fiberFunctor (schemeMorphismTargetBased f pX pY hf)
                ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).obj mε) yε :=
  ⟨injective_schemeMorphismInfinitesimalPair' f pX pY hf hM.satisfiesRS PM QX QY,
    fun _ => rfl,
    fun xε yε => exists_schemeMorphismTangentPair'_eq_iff f pX pY hf hM M xε yε⟩

end TargetForgetful

end Deformation.Examples

end
