module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorFunctionFieldChartIndependence
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicNeighborhoodOfPrimeDivisor
public import StacksFrontier.AlgebraicGeometry.TotalFractionRingFunctionField

/-!
# The order of vanishing along a prime divisor meeting the schematic locus

Let `S` be a scheme, let `X` be a locally Noetherian integral algebraic space over `S`, let
`f ∈ R(X)^*`, and let `Z ⊂ X` be a prime divisor meeting the schematic locus of `X`. This file
proves **Stacks 0ENM**: the order of vanishing `ord_Z(f)` of Definition 0ENL agrees with the
order of vanishing of Divisors, Definition 02RJ.

The three ingredients are already in place.

* The shrinking step of the source's proof, "after shrinking `X` we may assume `X` is an
  integral Noetherian scheme", is
  `AlgebraicGeometry.Space.PrimeDivisor.exists_schematic_neighborhood`: the schematic locus is
  an elementary étale neighbourhood of the generic point `ξ` of `Z` whose scheme is integral,
  locally Noetherian and of codimension one at the marked point. Restricting it to an affine
  open around the marked point keeps all four properties, which gives the affine neighbourhood
  the comparison needs.
* The comparison itself, on a given neighbourhood, is
  `AlgebraicGeometry.Space.PrimeDivisor.ord_functionFieldToTotalFractionRing`: both orders of
  vanishing are a difference of lengths, and the canonical map from the stalk into
  `𝒪^h_{X, ξ}` is the structure map of a henselization, so it leaves those lengths unchanged.
  This is the source's appeal to Algebra, Lemma 10.52.13.
* That the rational function may be read on *that* neighbourhood, rather than on the chart of
  Stacks 0BBP through which the order of vanishing of Definition 0ENL is defined, is
  `AlgebraicGeometry.Space.PrimeDivisor.neighborhoodTotalFractionRingToGeneric_pullback_eq`.

## Main definitions

* `AlgebraicGeometry.Space.rationalFunctionsToFunctionField` is the source's `R(X) → R(U)`, the
  pullback of rational functions to an integral affine étale chart.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.exists_affine_schematic_neighborhood`: a prime divisor
  meeting the schematic locus has at its generic point an *affine* elementary étale
  neighbourhood whose scheme is integral, locally Noetherian and of codimension one at the
  marked point.
* `AlgebraicGeometry.Space.PrimeDivisor.ord_eq_scheme_ord_of_chart`: on such a neighbourhood
  the two orders of vanishing agree.
* `AlgebraicGeometry.Space.PrimeDivisor.ord_eq_scheme_ord`: **Stacks 0ENM**.

## References

* [Stacks Project, Tag 02RJ](https://stacks.math.columbia.edu/tag/02RJ)
* [Stacks Project, Tag 0BBP](https://stacks.math.columbia.edu/tag/0BBP)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0ENL](https://stacks.math.columbia.edu/tag/0ENL)
* [Stacks Project, Tag 0ENM](https://stacks.math.columbia.edu/tag/0ENM)
-/

@[expose] public section

open CategoryTheory Order
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

/-! ### The pullback of rational functions to the function field of a chart -/

/-- **The source's `R(X) → R(U)`.** The pullback of rational functions of an algebraic space to
the function field of an integral affine étale chart: a rational function is read in the total
ring of fractions of the global sections of the chart, which maps to the function field of the
chart. -/
noncomputable def rationalFunctionsToFunctionField (W : BigFppfOver B S hS) [IsAffine W.left.1]
    [AlgebraicGeometry.IsIntegral W.left.1] [IsLocallyNoetherian W.left.1] (w : W.left.1)
    (c : yoneda.obj W ⟶ X) (hc : IsEtale B S hS c) :
    rationalFunctions B S hS hX →+* ↥W.left.1.functionField :=
  (W.left.1.totalFractionRingToFunctionField w).comp
    (rationalFunctionsToTotalFractionRing B S hS hX W c hc)

/-! ### The affine shrinking of the schematic locus -/

variable (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    (Z : PrimeDivisor B S hS X)

include hX hInt hN in
/-- **Stacks 0ENM**, the shrinking step of the proof in affine form. If a prime divisor `Z` of a
locally Noetherian integral algebraic space `X` meets the schematic locus of `X`, then the
generic point of `Z` has an *affine* elementary étale neighbourhood whose scheme is integral,
locally Noetherian and of codimension one at the marked point.

The schematic locus itself is such a neighbourhood except for affineness, by
`AlgebraicGeometry.Space.PrimeDivisor.exists_schematic_neighborhood`; restricting it to an
affine open around the marked point preserves integrality and local Noetherianness, as
properties of an open subscheme, and preserves the codimension of the marked point because
codimension is computed in any open neighbourhood. -/
@[stacks 0ENM "the shrinking step of the proof, with the neighbourhood affine: from the
  hypothesis that the prime divisor meets the schematic locus, an affine elementary étale
  neighbourhood of its generic point whose scheme is integral, locally Noetherian and of
  codimension one at the marked point"]
theorem PrimeDivisor.exists_affine_schematic_neighborhood
    (hmeet : (Z.support B S hS X ∩
      subspacePointSet B S hS X (schematicLocus B S hS X)).Nonempty) :
    ∃ U : ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X),
      IsAffine U.scheme.left.1 ∧
      AlgebraicGeometry.IsIntegral U.scheme.left.1 ∧
      IsLocallyNoetherian U.scheme.left.1 ∧
      coheight U.point = 1 := by
  obtain ⟨V, -, hVint, hVN, hVcoh⟩ :=
    Z.exists_schematic_neighborhood B S hS hX hInt hN hmeet
  obtain ⟨W, hW, hvW⟩ : ∃ W : V.scheme.left.1.Opens, IsAffineOpen W ∧ V.point ∈ W := by
    obtain ⟨-, ⟨W, hW, rfl⟩, hvW, -⟩ :=
      V.scheme.left.1.isBasis_affineOpens.exists_subset_of_mem_open
        (show V.point ∈ (⊤ : V.scheme.left.1.Opens) from trivial)
        (⊤ : V.scheme.left.1.Opens).2
    exact ⟨W, hW, hvW⟩
  have := hVint
  have := hVN
  have : Nonempty ↥W := ⟨⟨V.point, hvW⟩⟩
  have : Nonempty W.toScheme := ⟨⟨V.point, hvW⟩⟩
  have hpt : W.ι.base (⟨V.point, hvW⟩ : W.toScheme) = V.point := rfl
  refine ⟨openRestrictionNeighborhood B S hS X hX (Z.genericPoint B S hS X) V W hvW, hW,
    ?_, ?_, ?_⟩
  · show AlgebraicGeometry.IsIntegral W.toScheme
    exact AlgebraicGeometry.isIntegral_of_isOpenImmersion W.ι
  · show IsLocallyNoetherian W.toScheme
    infer_instance
  · rw [← Scheme.coheight_opens W (⟨V.point, hvW⟩ : W.toScheme), hpt]
    exact hVcoh

/-! ### The comparison of the two orders of vanishing -/

variable (hdec : IsDecentSpace B S hS X)

/-- The map from the function field of an integral affine elementary étale neighbourhood of the
generic point of a prime divisor into the total ring of fractions of the henselian local ring
agrees, on the image of the total ring of fractions of the global sections, with the map used to
define the embedding of Stacks 0ENK. -/
theorem PrimeDivisor.functionFieldToTotalFractionRing_totalFractionRingToFunctionField
    [IsLocalRing ↥(Z.genericHenselianLocalRing B S hS hX hdec)]
    (hCofiltered :
      IsCofiltered (ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X)))
    (U : ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X))
    [IsAffine U.scheme.left.1] [AlgebraicGeometry.IsIntegral U.scheme.left.1]
    (b : FractionRing Γ(U.scheme.left.1, ⊤)) :
    Z.functionFieldToTotalFractionRing B S hS hX hdec U
        (U.scheme.left.1.totalFractionRingToFunctionField U.point b) =
      Z.neighborhoodTotalFractionRingToGeneric B S hS hX hdec U hCofiltered b := by
  have key : (Z.functionFieldToTotalFractionRing B S hS hX hdec U).comp
      (U.scheme.left.1.totalFractionRingToFunctionField U.point) =
      Z.neighborhoodTotalFractionRingToGeneric B S hS hX hdec U hCofiltered := by
    refine IsLocalization.ringHom_ext (Γ(U.scheme.left.1, ⊤))⁰ ?_
    ext a
    have h1 : Z.functionFieldToTotalFractionRing B S hS hX hdec U
        (algebraMap ↥(U.scheme.left.1.presheaf.stalk U.point) ↥U.scheme.left.1.functionField
          ((U.scheme.left.1.presheaf.germ ⊤ U.point trivial) a)) =
        algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
          (Z.genericTotalFractionRing B S hS hX hdec)
          (stalkToHenselianLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec U
            ((U.scheme.left.1.presheaf.germ ⊤ U.point trivial) a)) :=
      IsLocalization.map_eq _ _
    have h2 : Z.neighborhoodTotalFractionRingToGeneric B S hS hX hdec U hCofiltered
        (algebraMap Γ(U.scheme.left.1, ⊤) (FractionRing Γ(U.scheme.left.1, ⊤)) a) =
        algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
          (Z.genericTotalFractionRing B S hS hX hdec)
          (Z.neighborhoodSectionsToGenericHenselianLocalRing B S hS hX hdec U a) :=
      IsLocalization.map_eq _ _
    simp only [RingHom.comp_apply, Scheme.totalFractionRingToFunctionField_algebraMap]
    rw [h1, h2]
    rfl
  exact RingHom.congr_fun key b

include hInt hN in
/-- **Stacks 0ENM on a given affine chart.** Let `Z` be a prime divisor of a decent, locally
Noetherian, integral algebraic space `X`, and let `(U, u)` be an affine elementary étale
neighbourhood of the generic point of `Z` whose scheme is integral, locally Noetherian and of
codimension one at `u`. Then the order of vanishing along `Z` of an invertible rational function
`f` of `X` is the order of vanishing at `u` of the pullback of `f` to the function field of `U`,
in the sense of Divisors, Definition 02RJ. -/
theorem PrimeDivisor.ord_eq_scheme_ord_of_chart
    (U : ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X))
    [IsAffine U.scheme.left.1] [AlgebraicGeometry.IsIntegral U.scheme.left.1]
    [IsLocallyNoetherian U.scheme.left.1] (hcoh : coheight U.point = 1)
    (f : (rationalFunctions B S hS hX)ˣ) :
    (genericFractionEmbedding B S hS hX hdec hInt hN).ord f Z =
      U.scheme.left.1.ord
        (rationalFunctionsToFunctionField B S hS hX U.scheme U.point U.toSpace U.etale_toSpace
          (f : rationalFunctions B S hS hX)) U.point := by
  have : IsLocalRing ↥(Z.genericHenselianLocalRing B S hS hX hdec) :=
    henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  have : Nontrivial ↥(Z.genericHenselianLocalRing B S hS hX hdec) :=
    Z.nontrivial_genericHenselianLocalRing B S hS hX hdec hInt hN
  have : IsNoetherianRing ↥(Z.genericHenselianLocalRing B S hS hX hdec) :=
    Z.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hN
  have : Ring.KrullDimLE 1 ↥(Z.genericHenselianLocalRing B S hS hX hdec) :=
    Z.krullDimLE_genericHenselianLocalRing B S hS hX hdec hInt hN
  have hCof := ElementaryEtaleNeighborhood.isCofiltered_of_nonempty B S hS X hX
    (Z.genericPoint B S hS X) ⟨Z.genericChart B S hS hX hdec⟩
  set g := rationalFunctionsToFunctionField B S hS hX U.scheme U.point U.toSpace U.etale_toSpace
    (f : rationalFunctions B S hS hX) with hgdef
  have hg : g ≠ 0 :=
    (f.isUnit.map (rationalFunctionsToFunctionField B S hS hX U.scheme U.point U.toSpace
      U.etale_toSpace)).ne_zero
  -- the image of `f` under the embedding of Stacks 0ENK is computed on `U`
  have himage : (genericFractionEmbedding B S hS hX hdec hInt hN).emb Z
        (f : rationalFunctions B S hS hX) =
      Z.functionFieldToTotalFractionRing B S hS hX hdec U g := by
    rw [hgdef, rationalFunctionsToFunctionField, RingHom.comp_apply,
      Z.functionFieldToTotalFractionRing_totalFractionRingToFunctionField B S hS hX hdec hCof U,
      Z.neighborhoodTotalFractionRingToGeneric_pullback_eq B S hS hX hdec hInt hN U hCof]
    rfl
  calc (genericFractionEmbedding B S hS hX hdec hInt hN).ord f Z
      = Z.ord B S hS hX hdec ((genericFractionEmbedding B S hS hX hdec hInt hN).emb Z
          (f : rationalFunctions B S hS hX))
          (f.isUnit.map ((genericFractionEmbedding B S hS hX hdec hInt hN).emb Z)) := rfl
    _ = Z.ord B S hS hX hdec (Z.functionFieldToTotalFractionRing B S hS hX hdec U g)
          ((isUnit_iff_ne_zero.mpr hg).map _) := Z.ord_congr B S hS hX hdec _ _ himage
    _ = U.scheme.left.1.ord g U.point :=
        Z.ord_functionFieldToTotalFractionRing B S hS hX hdec U hcoh g hg

include hX hInt hN in
/-- **Stacks 0ENM.** Let `S` be a scheme, let `X` be a locally Noetherian integral algebraic
space over `S` and let `f ∈ R(X)^*`. If the prime divisor `Z ⊂ X` meets the schematic locus of
`X`, then the order of vanishing `ord_Z(f)` of Definition 0ENL agrees with the order of
vanishing of Divisors, Definition 02RJ.

After shrinking `X` to the schematic locus and then to an affine open around the generic point
`ξ` of `Z` we are on an integral Noetherian affine scheme `U` with a point of codimension one;
there `𝒪^h_{X, ξ}` is a henselization of `𝒪_{U, u}`, so the two orders of vanishing, each a
difference of lengths, agree.

The hypotheses are exactly those of the source: decency, which the henselian local ring and
hence the order of vanishing of Definition 0ENL are defined from, is part of integrality of an
algebraic space — Stacks 0AD4, `AlgebraicGeometry.Space.IsIntegralSpace` — and is taken from
`hInt` rather than assumed separately. -/
@[stacks 0ENM]
theorem PrimeDivisor.ord_eq_scheme_ord
    (hmeet : (Z.support B S hS X ∩
      subspacePointSet B S hS X (schematicLocus B S hS X)).Nonempty)
    (f : (rationalFunctions B S hS hX)ˣ) :
    ∃ (U : ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X))
      (_ : IsAffine U.scheme.left.1) (_ : AlgebraicGeometry.IsIntegral U.scheme.left.1)
      (_ : IsLocallyNoetherian U.scheme.left.1),
      coheight U.point = 1 ∧
        (genericFractionEmbedding B S hS hX (hInt.isDecentSpace B S hS X) hInt hN).ord f Z =
          U.scheme.left.1.ord
            (rationalFunctionsToFunctionField B S hS hX U.scheme U.point U.toSpace
              U.etale_toSpace (f : rationalFunctions B S hS hX)) U.point := by
  obtain ⟨U, hAff, hUint, hUN, hUcoh⟩ :=
    Z.exists_affine_schematic_neighborhood B S hS hX hInt hN hmeet
  exact ⟨U, hAff, hUint, hUN, hUcoh,
    Z.ord_eq_scheme_ord_of_chart B S hS hX hInt hN (hInt.isDecentSpace B S hS X) U hUcoh f⟩

end AlgebraicGeometry.Space

end
