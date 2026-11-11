module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardDimensionDrop
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenChartOrderOfVanishing

/-!
# The order of vanishing along a prime divisor, compared with the schematic locus

Let `S` be a scheme, let `X` be a locally Noetherian integral algebraic space over `S`, let
`f ∈ R(X)^*`, and let `Z ⊂ X` be a prime divisor meeting the schematic locus of `X`. This file
proves **Stacks 0ENM**: the order of vanishing `ord_Z(f)` of Definition 0ENL agrees with the
order of vanishing of Divisors, Definition 02RJ, of the restriction of `f` to a scheme `X'`
representing the schematic locus, at the point of `X'` over the generic point of `Z`.

## Main definitions

* `AlgebraicGeometry.Space.IsOpenChartRestriction`: a rational function of the scheme of an open
  chart is the restriction of a rational function of the space.

## Main results

* `AlgebraicGeometry.Space.isOpenImmersion_hom_comp_schematicLocus_ι`: a scheme representing the
  schematic locus is an open chart.
* `AlgebraicGeometry.Space.PrimeDivisor.ord_eq_ord_schematicLocus`: **Stacks 0ENM.**

## References

* [Stacks Project, Tag 02RJ](https://stacks.math.columbia.edu/tag/02RJ)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 0ENL](https://stacks.math.columbia.edu/tag/0ENL)
* [Stacks Project, Tag 0ENM](https://stacks.math.columbia.edu/tag/0ENM)
-/

@[expose] public noncomputable section

open CategoryTheory Order

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

section Restriction

variable {V : BigFppfOver B S hS} (β : yoneda.obj V ⟶ X) (hβ : IsOpenImmersion B S hS β)
    [IsIntegral ((BigFppfOver.toScheme B S hS).obj V)]
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]

/-- **The restriction of a rational function to an open chart.** A rational function `g` of
the scheme `V` of an open chart `β : h_V ⟶ X` is the restriction `f|_V` of a rational function
`f` of `X` when, on every affine open `U` of `V`, the reading of `f` on the chart `U ⟶ V ⟶ X`
is the restriction of `g` to `U`. Such a `g` exists by
`AlgebraicGeometry.Space.exists_functionField_forall_openChartRationalFunction` and is unique,
the restriction of rational functions to a nonempty open being injective. -/
def IsOpenChartRestriction (f : rationalFunctions B S hS hX)
    (g : ((BigFppfOver.toScheme B S hS).obj V).functionField) : Prop :=
  ∀ (U : ((BigFppfOver.toScheme B S hS).obj V).Opens) (hU : IsAffineOpen U)
    (w : (BigFppfOver.toScheme B S hS).obj (openChartObject B S hS V U)),
    haveI : Nonempty ((BigFppfOver.toScheme B S hS).obj (openChartObject B S hS V U)) := ⟨w⟩
    haveI := isIntegral_toScheme_obj_openChartObject B S hS U
    haveI := isDominant_toScheme_map_openChartMap B S hS U
    openChartRationalFunction B S hS hX β hβ U hU w f =
      dominantFunctionFieldMap ((BigFppfOver.toScheme B S hS).map (openChartMap B S hS V U)) g

end Restriction

include hX in
/-- A scheme representing the schematic locus of an algebraic space, with the composite of the
representing isomorphism and the inclusion of the schematic locus, is an open chart. -/
theorem isOpenImmersion_hom_comp_schematicLocus_ι {W : BigFppfOver B S hS}
    (e : yoneda.obj W ≅ (schematicLocus B S hS X).toFunctor) :
    IsOpenImmersion B S hS (e.hom ≫ (schematicLocus B S hS X).ι) :=
  MorphismProperty.RespectsIso.precomp _ e.hom _
    (isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hX).1.2

/-- **Stacks 0ENM.** Let `S` be a scheme, let `X` be a locally Noetherian integral algebraic
space over `S` and let `f ∈ R(X)^*`. Let `Z ⊂ X` be a prime divisor meeting the schematic locus
of `X`, and let `X'` be a scheme representing the schematic locus, through an isomorphism
`e : h_{X'} ≅ (schematicLocus X)`, so that `X' ⟶ X` is an open immersion; such an `X'` exists
by Stacks 03JH,
`AlgebraicGeometry.Space.isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace`.
Then:

* the generic point `ξ` of `Z` is the image of a point `ξ'` of `X'`;
* for every such `ξ'` (it is unique, `X' ⟶ X` being a monomorphism), the scheme `X'` is integral
  and locally Noetherian, `ξ'` has codimension one in `X'`, so that it is the generic point of
  the prime divisor `Z ∩ X'` of `X'`, the restriction `f|_{X'}` of `f` to `X'` exists in the
  function field of `X'`, and for it `ord_Z(f) = ord_{ξ'}(f|_{X'})`: the order of vanishing of
  Definition 0ENL agrees with the order of vanishing of Divisors, Definition 02RJ, on the scheme
  `X'`.

Integrality of `X` includes decency (Stacks 0AD4, `AlgebraicGeometry.Space.IsIntegralSpace`),
which the henselian local ring of Definition 0ENL is built from; it is taken from `hInt`.

The point `ξ'` exists because the point set of the schematic locus is open in `|X|` and meets
`|Z|`, so contains its generic point. The comparison is
`AlgebraicGeometry.Space.PrimeDivisor.ord_eq_scheme_ord_of_isOpenImmersion`: on an affine open of
`X'` around `ξ'` the henselian local ring `𝒪^h_{X, ξ}` is a henselization of `𝒪_{X', ξ'}`, which
preserves the lengths both orders of vanishing are differences of. -/
@[stacks 0ENM "the order of vanishing along a prime divisor `Z` meeting the schematic locus is
  the order of vanishing, in the sense of Divisors 02RJ, of the restriction of `f` to a scheme
  `X'` representing the schematic locus, at the point of `X'` over the generic point of `Z`"]
theorem PrimeDivisor.ord_eq_ord_schematicLocus (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    (Z : PrimeDivisor B S hS X)
    (hmeet : (Z.support B S hS X ∩
      subspacePointSet B S hS X (schematicLocus B S hS X)).Nonempty)
    {W : BigFppfOver B S hS} (e : yoneda.obj W ≅ (schematicLocus B S hS X).toFunctor)
    (f : (rationalFunctions B S hS hX)ˣ) :
    (∃ ξ' : (BigFppfOver.toScheme B S hS).obj W,
      pointsMap B S hS (yoneda.obj W) (e.hom ≫ (schematicLocus B S hS X).ι)
        ((pointsEquivScheme B S hS W).symm ξ') = Z.genericPoint B S hS X) ∧
    ∀ ξ' : (BigFppfOver.toScheme B S hS).obj W,
      pointsMap B S hS (yoneda.obj W) (e.hom ≫ (schematicLocus B S hS X).ι)
        ((pointsEquivScheme B S hS W).symm ξ') = Z.genericPoint B S hS X →
      ∃ (_ : IsIntegral ((BigFppfOver.toScheme B S hS).obj W))
        (_ : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj W)),
        coheight ξ' = 1 ∧
        (∃ f' : ((BigFppfOver.toScheme B S hS).obj W).functionField,
          IsOpenChartRestriction B S hS hX (e.hom ≫ (schematicLocus B S hS X).ι)
            (isOpenImmersion_hom_comp_schematicLocus_ι B S hS hX e)
            (f : rationalFunctions B S hS hX) f') ∧
        ∀ f' : ((BigFppfOver.toScheme B S hS).obj W).functionField,
          IsOpenChartRestriction B S hS hX (e.hom ≫ (schematicLocus B S hS X).ι)
            (isOpenImmersion_hom_comp_schematicLocus_ι B S hS hX e)
            (f : rationalFunctions B S hS hX) f' →
          (genericFractionEmbedding B S hS hX (hInt.isDecentSpace B S hS X) hInt hN).ord f Z =
            ((BigFppfOver.toScheme B S hS).obj W).ord f' ξ' := by
  set β := e.hom ≫ (schematicLocus B S hS X).ι with hβdef
  have hβ : IsOpenImmersion B S hS β := isOpenImmersion_hom_comp_schematicLocus_ι B S hS hX e
  have hdec : IsDecentSpace B S hS X := hInt.isDecentSpace B S hS X
  set E := pointsEquivScheme B S hS W
  -- the generic point of `Z` lies in the point set of the schematic locus
  have hj := isOpenEmbedding_pointsMap_pointsEquivScheme_symm B S hS hX β hβ
  have hrange : Set.range (pointsMap B S hS (yoneda.obj W) β ∘ E.symm) =
      subspacePointSet B S hS X (schematicLocus B S hS X) := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨pointsMap B S hS (yoneda.obj W) e.hom (E.symm v),
        (congrFun (pointsMap_comp B S hS (F := yoneda.obj W) e.hom
          (schematicLocus B S hS X).ι) (E.symm v)).symm⟩
    · rintro ⟨q, rfl⟩
      refine ⟨E (pointsMap B S hS (schematicLocus B S hS X).toFunctor e.inv q), ?_⟩
      have hcomp := congrFun
        (pointsMap_comp B S hS (F := (schematicLocus B S hS X).toFunctor) e.inv β) q
      rw [show e.inv ≫ β = (schematicLocus B S hS X).ι by
        rw [hβdef, Iso.inv_hom_id_assoc]] at hcomp
      change pointsMap B S hS (yoneda.obj W) β (E.symm (E _)) = _
      rw [E.symm_apply_apply]
      exact hcomp.symm
  refine ⟨?_, fun ξ' hξ' ↦ ?_⟩
  · have hmem : Z.genericPoint B S hS X ∈
        Set.range (pointsMap B S hS (yoneda.obj W) β ∘ E.symm) :=
      hrange ▸ ((Z.isGenericPoint_genericPoint B S hS X).mem_open_set_iff
        (hrange ▸ hj.isOpen_range)).2 hmeet
    obtain ⟨v, hv⟩ := hmem
    exact ⟨v, hv⟩
  have _ : Nonempty ((BigFppfOver.toScheme B S hS).obj W) := ⟨ξ'⟩
  have hWint := isIntegral_toScheme_obj_of_isOpenImmersion B S hS hX β hβ hInt
  have hWN := isLocallyNoetherian_toScheme_obj_of_isOpenImmersion B S hS hX β hβ hN
  have hcoh : coheight ξ' = 1 := by
    have hc := coheight_eq_codimension_pointsMap B S hS hX β hβ hdec ξ'
    have hξ'' : pointsMap B S hS (yoneda.obj W) β ((pointsEquivScheme B S hS W).symm ξ') =
        Z.genericPoint B S hS X := hξ'
    rw [hξ''] at hc
    exact hc.trans (Z.codimension_genericPoint B S hS X)
  refine ⟨hWint, hWN, hcoh,
    exists_functionField_forall_openChartRationalFunction B S hS hX β hβ _, fun f' hf' ↦ ?_⟩
  exact Z.ord_eq_scheme_ord_of_isOpenImmersion B S hS hX β hβ hInt hN hdec ξ' hξ' hcoh f f' hf'

end AlgebraicGeometry.Space

end
