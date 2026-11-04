module

public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreNormalConeIso
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafComapMul

/-!
# Change of centre for the blowup at infinity

Let `X` be a scheme and `ℐ_Y ⊆ ℐ_Z` quasi-coherent ideal sheaves on `X`, cutting out closed
subschemes `Z ⊆ Y ⊆ X`. Let `W_Z ⟶ 𝐏¹_X` and `W_Y ⟶ 𝐏¹_X` be the blowups at infinity of
Stacks 0FBG, in the centres `∞(Z) ⊆ ∞(Y)`, with exceptional divisors `E_Z`, `E_Y`, fibres at
infinity `W_{Z,∞}`, `W_{Y,∞}` and strict transforms `X'_Z`, `X'_Y` of `X`, and write
`U_Z = W_Z ∖ X'_Z`, `U_Y = W_Y ∖ X'_Y`.

The ideal of `∞(Y)` is `ℐ_Y·𝒪_{𝐏¹_X} + ℐ_{(𝐏¹_X)_∞}`. Its inverse image on `W_Z` lies between
`W_{Z,∞}` and `E_Z`, since `∞(Y) ⊇ ∞(Z)`, and on `U_Z` these two agree (`W_∞ = X' + E`). So the
inverse image of `∞(Y)` on `U_Z` is the effective Cartier divisor `W_{Z,∞} ∩ U_Z`, and the
universal property of the blowup (Stacks 0806) gives a morphism `ρ : U_Z ⟶ W_Y` over `𝐏¹_X`.
Along `ρ` both `E_Y` and `W_{Y,∞}` pull back to `W_{Z,∞} ∩ U_Z`; pulling back
`W_{Y,∞} = E_Y + X'_Y` and cancelling the effective Cartier divisor `W_{Z,∞} ∩ U_Z` shows that
`X'_Y` pulls back to the empty divisor, so `ρ` lands in `U_Y`.

Restricted to the normal cones `C_ZX = E_Z ∖ X'_Z ⊆ U_Z` and `C_YX = W_{Y,∞} ∖ X'_Y` of
Stacks 0FBH, `ρ` gives a morphism `C_ZX ⟶ C_YX` over `X`. On the chart over an affine open
`U = Spec A` of `X` it is the spectrum of the map of associated graded rings
`Gr_{ℐ_Y(U)}(A) ⟶ Gr_{ℐ_Z(U)}(A)` induced by `ℐ_Y(U) ⊆ ℐ_Z(U)`: it is the canonical morphism of
normal cones induced by the inclusion of ideals (Stacks 0634).

## Main definitions

* `Stacks.Chow.blowupAtInfinityChangeOfCentre` — the morphism `ρ : W_Z ∖ X'_Z ⟶ W_Y`.
* `Stacks.Chow.blowupAtInfinityChangeOfCentreCompl` — its corestriction
  `W_Z ∖ X'_Z ⟶ W_Y ∖ X'_Y`.
* `Stacks.Chow.normalConeToStrictTransformComplAtInfinity` — the closed immersion
  `C_ZX ⟶ W_Z ∖ X'_Z`.
* `Stacks.Chow.normalConeChangeOfCentreMap` — the morphism of normal cones `C_ZX ⟶ C_YX` of
  closed immersions `Z ⟶ X`, `Y ⟶ X` with `ker (Y ⟶ X) ≤ ker (Z ⟶ X)`.
* `Stacks.Chow.conormalSectionsChangeOfCentre` — the map of conormal algebras on the chart over
  an affine open of `X`.

## Main results

* `Stacks.Chow.comap_infinityCentreIdeal_strictTransformComplAtInfinity_ι` — `∞(Y)` pulls back
  to `W_{Z,∞} ∩ U_Z` on `U_Z`.
* `Stacks.Chow.comap_exceptionalIdealAtInfinity_changeOfCentre`,
  `Stacks.Chow.comap_fibreIdealAtInfinity_changeOfCentre`,
  `Stacks.Chow.comap_strictTransformIdealAtInfinity_changeOfCentre` — along `ρ`, `E_Y` and
  `W_{Y,∞}` pull back to `W_{Z,∞} ∩ U_Z` and `X'_Y` to the empty divisor.
* `Stacks.Chow.preimage_strictTransformComplAtInfinity_changeOfCentre` — `ρ` lands in `U_Y`.
* `Stacks.Chow.normalConeChangeOfCentreMap_comp_strictTransformCompl` — the morphism of normal
  cones is the restriction of `ρ`.
* `Stacks.Chow.normalConeChangeOfCentreMap_toBase` — it lies over `Z ⟶ Y`.
* `Stacks.Chow.specMap_conormalSectionsChangeOfCentre_normalConeChart` and
  `Stacks.Chow.conormalSectionsChangeOfCentre_conormalAlgebraSheafSectionsEquiv` — on the charts
  it is the spectrum of `Gr_{ℐ_Y(U)}(A) ⟶ Gr_{ℐ_Z(U)}(A)`.

## Implementation notes

The morphism `ρ` is only defined on the open `U_Z = W_Z ∖ X'_Z` of `W_Z`: over all of `W_Z` the
inverse image of `∞(Y)` need not be an effective Cartier divisor. This open contains the normal
cone `C_ZX`, which is all the comparison of normal cones uses.

The morphism of normal cones is built through the exceptional divisors, `C_ZX ≅ E_Z ∖ X'_Z` and
`C_YX ≅ E_Y ∖ X'_Y` (`Stacks.Chow.normalConeToExceptionalDivisor`), so it involves no morphism
`X ⟶ S`. Its compatibility with the open immersions `j : C_ZX ⟶ W_∞` into the fibres at infinity
of the modifications of `X ×_S 𝐏¹_S`, for any `X ⟶ S`, is
`Stacks.Chow.normalConeChangeOfCentreMap_comp_inclusion`.

## References

* [Stacks Project, Tag 0FBG](https://stacks.math.columbia.edu/tag/0FBG)
* [Stacks Project, Tag 0FBH](https://stacks.math.columbia.edu/tag/0FBH)
* [Stacks Project, Tag 0806](https://stacks.math.columbia.edu/tag/0806)
* [Stacks Project, Tag 0634](https://stacks.math.columbia.edu/tag/0634)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}}

section Blowup

variable {ℐY ℐZ : X.IdealSheafData} (h : ℐY ≤ ℐZ)

include h in
/-- The centre at infinity is monotone in the ideal: `∞(Z) ⊆ ∞(Y)` for `Z ⊆ Y`. -/
theorem infinityCentreIdeal_mono : infinityCentreIdeal ℐY ≤ infinityCentreIdeal ℐZ :=
  Scheme.IdealSheafData.map_mono (lineInfinitySection X) h

include h in
/-- **The centre `∞(Y)` pulls back to `W_{Z,∞}` on `W_Z ∖ X'_Z`.** Its inverse image on `W_Z`
lies between the fibre at infinity `W_{Z,∞}` and the exceptional divisor `E_Z`, because
`(𝐏¹_X)_∞ ⊆ ∞(Z) ⊆ ∞(Y)`, and on `W_Z ∖ X'_Z` these two agree. -/
theorem comap_infinityCentreIdeal_strictTransformComplAtInfinity_ι :
    (infinityCentreIdeal ℐY).comap
        ((strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToLine ℐZ) =
      (fibreIdealAtInfinity ℐZ).comap (strictTransformComplAtInfinity ℐZ).ι := by
  rw [Scheme.IdealSheafData.comap_comp]
  refine le_antisymm ?_ ?_
  · rw [comap_fibreIdealAtInfinity_ι_compl]
    exact Scheme.IdealSheafData.comap_mono _ (Scheme.IdealSheafData.comap_mono _
      (infinityCentreIdeal_mono h))
  · exact Scheme.IdealSheafData.comap_mono _ (Scheme.IdealSheafData.comap_mono _
      (lineInfinityDivisor_le_infinityCentreIdeal ℐY))

/-- The fibre at infinity `W_{Z,∞}` pulls back to an effective Cartier divisor on `W_Z ∖ X'_Z`. -/
private theorem isEffectiveCartierDivisor_comap_fibreIdealAtInfinity_ι (ℐ : X.IdealSheafData) :
    Stacks.Divisors.IsEffectiveCartierDivisor
      ((fibreIdealAtInfinity ℐ).comap (strictTransformComplAtInfinity ℐ).ι) :=
  Stacks.Blowup.isEffectiveCartierDivisor_comap_of_isOpenImmersion _
    (isEffectiveCartierDivisor_fibreIdealAtInfinity ℐ) _

include h in
/-- The centre `∞(Y)` pulls back to an effective Cartier divisor along
`W_Z ∖ X'_Z ⟶ W_Z ⟶ 𝐏¹_X`: it is the fibre at infinity there. -/
theorem isCartierOver_infinityCentreIdeal_strictTransformComplAtInfinity_ι :
    Stacks.Blowup.IsCartierOver (infinityCentreIdeal ℐY)
      (Over.mk ((strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToLine ℐZ)) := by
  change Stacks.Divisors.IsEffectiveCartierDivisor
    ((infinityCentreIdeal ℐY).comap
      ((strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToLine ℐZ))
  rw [comap_infinityCentreIdeal_strictTransformComplAtInfinity_ι h]
  exact isEffectiveCartierDivisor_comap_fibreIdealAtInfinity_ι ℐZ

/-- **The change of centre `ρ : W_Z ∖ X'_Z ⟶ W_Y` of the blowups at infinity**, for
`ℐ_Y ≤ ℐ_Z`: the classifying morphism (Stacks 0806) of `W_Z ∖ X'_Z ⟶ W_Z ⟶ 𝐏¹_X`, along which
the centre `∞(Y)` pulls back to the effective Cartier divisor `W_{Z,∞} ∩ (W_Z ∖ X'_Z)`. -/
def blowupAtInfinityChangeOfCentre :
    (strictTransformComplAtInfinity ℐZ).toScheme ⟶ blowupAtInfinity ℐY :=
  blowUpLift (infinityCentreIdeal ℐY)
    ((strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToLine ℐZ)
    (isCartierOver_infinityCentreIdeal_strictTransformComplAtInfinity_ι h)

/-- The change of centre lies over `𝐏¹_X`. -/
@[reassoc]
theorem blowupAtInfinityChangeOfCentre_comp :
    blowupAtInfinityChangeOfCentre h ≫ blowupAtInfinityToLine ℐY =
      (strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToLine ℐZ :=
  blowUpLift_comp _ _ _

/-- The change of centre lies over `X`. -/
@[reassoc]
theorem blowupAtInfinityChangeOfCentre_toBase :
    blowupAtInfinityChangeOfCentre h ≫ blowupAtInfinityToBase ℐY =
      (strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToBase ℐZ := by
  rw [blowupAtInfinityToBase, blowupAtInfinityChangeOfCentre_comp_assoc, blowupAtInfinityToBase]

/-- The change of centre lies over `X ×_S 𝐏¹_S`, through the identifications
`𝐏¹_X ≅ X ×_S 𝐏¹_S`. -/
@[reassoc]
theorem blowupAtInfinityChangeOfCentre_comp_toProjectiveLineProduct {S : Scheme.{u}}
    (sX : X ⟶ S) :
    blowupAtInfinityChangeOfCentre h ≫ blowupAtInfinityToProjectiveLineProduct ℐY sX =
      (strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToProjectiveLineProduct ℐZ sX := by
  rw [blowupAtInfinityToProjectiveLineProduct, blowupAtInfinityChangeOfCentre_comp_assoc,
    blowupAtInfinityToProjectiveLineProduct]

/-- The fibre at infinity `W_{Y,∞}` pulls back to `W_{Z,∞}` along the change of centre. -/
theorem comap_fibreIdealAtInfinity_changeOfCentre :
    (fibreIdealAtInfinity ℐY).comap (blowupAtInfinityChangeOfCentre h) =
      (fibreIdealAtInfinity ℐZ).comap (strictTransformComplAtInfinity ℐZ).ι := by
  change ((lineInfinityDivisor X).comap (blowupAtInfinityToLine ℐY)).comap _ =
    ((lineInfinityDivisor X).comap (blowupAtInfinityToLine ℐZ)).comap _
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    blowupAtInfinityChangeOfCentre_comp]

/-- The exceptional divisor `E_Y` pulls back to `W_{Z,∞}` along the change of centre. -/
theorem comap_exceptionalIdealAtInfinity_changeOfCentre :
    (exceptionalIdealAtInfinity ℐY).comap (blowupAtInfinityChangeOfCentre h) =
      (fibreIdealAtInfinity ℐZ).comap (strictTransformComplAtInfinity ℐZ).ι := by
  change ((infinityCentreIdeal ℐY).comap (blowupAtInfinityToLine ℐY)).comap _ = _
  rw [← Scheme.IdealSheafData.comap_comp, blowupAtInfinityChangeOfCentre_comp,
    comap_infinityCentreIdeal_strictTransformComplAtInfinity_ι h]

/-- **The strict transform `X'_Y` pulls back to the empty divisor along the change of centre.**
Pulling back `W_{Y,∞} = E_Y + X'_Y` gives `D = D + ρ⁻¹X'_Y` for the effective Cartier divisor
`D = W_{Z,∞} ∩ (W_Z ∖ X'_Z)`, and `D` can be cancelled. -/
theorem comap_strictTransformIdealAtInfinity_changeOfCentre :
    (strictTransformIdealAtInfinity ℐY).comap (blowupAtInfinityChangeOfCentre h) = ⊤ := by
  refine (Stacks.Divisors.eq_of_mul_eq_mul_of_isEffectiveCartierDivisor
    (isEffectiveCartierDivisor_comap_fibreIdealAtInfinity_ι ℐZ) ?_).symm
  rw [Scheme.IdealSheafData.mul_top, ← comap_exceptionalIdealAtInfinity_changeOfCentre h,
    ← Stacks.IdealSheaf.comap_mul, ← fibreIdealAtInfinity_eq_mul_strictTransformIdealAtInfinity,
    comap_fibreIdealAtInfinity_changeOfCentre h,
    comap_exceptionalIdealAtInfinity_changeOfCentre h]

/-- **The change of centre lands in `W_Y ∖ X'_Y`.** -/
theorem preimage_strictTransformComplAtInfinity_changeOfCentre :
    blowupAtInfinityChangeOfCentre h ⁻¹ᵁ strictTransformComplAtInfinity ℐY = ⊤ := by
  refine eq_top_iff.2 fun x _ hx => ?_
  have hmem : x ∈ (((strictTransformIdealAtInfinity ℐY).comap
      (blowupAtInfinityChangeOfCentre h)).support : Set _) := by
    rw [Scheme.IdealSheafData.support_comap]
    exact hx
  rw [comap_strictTransformIdealAtInfinity_changeOfCentre h] at hmem
  simp at hmem

/-- **The change of centre `W_Z ∖ X'_Z ⟶ W_Y ∖ X'_Y`**, the corestriction of
`Stacks.Chow.blowupAtInfinityChangeOfCentre`. -/
def blowupAtInfinityChangeOfCentreCompl :
    (strictTransformComplAtInfinity ℐZ).toScheme ⟶
      (strictTransformComplAtInfinity ℐY).toScheme :=
  IsOpenImmersion.lift (strictTransformComplAtInfinity ℐY).ι (blowupAtInfinityChangeOfCentre h) (by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hx : x ∈ blowupAtInfinityChangeOfCentre h ⁻¹ᵁ strictTransformComplAtInfinity ℐY := by
      rw [preimage_strictTransformComplAtInfinity_changeOfCentre h]
      trivial
    exact hx)

/-- The corestricted change of centre followed by the inclusion of `W_Y ∖ X'_Y` is the change of
centre. -/
@[reassoc (attr := simp)]
theorem blowupAtInfinityChangeOfCentreCompl_ι :
    blowupAtInfinityChangeOfCentreCompl h ≫ (strictTransformComplAtInfinity ℐY).ι =
      blowupAtInfinityChangeOfCentre h :=
  IsOpenImmersion.lift_fac _ _ _

end Blowup

section NormalCone

variable {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- **The closed immersion `C_ZX ⟶ W ∖ X'`**: the identification `C_ZX ≅ E ∖ X'` of
Stacks 0FBH followed by the closed immersion `E ∖ X' ⟶ W ∖ X'`. -/
def normalConeToStrictTransformComplAtInfinity :
    Stacks.Conormal.normalCone i ⟶ (strictTransformComplAtInfinity i.ker).toScheme :=
  (normalConeIsoExceptionalCompl i).hom ≫
    ((exceptionalIdealAtInfinity i.ker).subschemeι ∣_ strictTransformComplAtInfinity i.ker)

/-- `C_ZX ⟶ W ∖ X'` is a closed immersion: it is `E ∖ X' ⟶ W ∖ X'` up to isomorphism. -/
instance : IsClosedImmersion (normalConeToStrictTransformComplAtInfinity i) := by
  dsimp only [normalConeToStrictTransformComplAtInfinity]
  infer_instance

/-- `C_ZX ⟶ W ∖ X' ⟶ W` is `C_ZX ⟶ E ⟶ W`. -/
@[reassoc (attr := simp)]
theorem normalConeToStrictTransformComplAtInfinity_ι :
    normalConeToStrictTransformComplAtInfinity i ≫ (strictTransformComplAtInfinity i.ker).ι =
      normalConeToExceptionalDivisor i ≫ (exceptionalIdealAtInfinity i.ker).subschemeι := by
  rw [normalConeToStrictTransformComplAtInfinity, Category.assoc, morphismRestrict_ι,
    normalConeToExceptionalDivisor, Category.assoc]

/-- `C_ZX ⟶ W ∖ X' ⟶ W` is `j : C_ZX ⟶ W_∞` followed by `W_∞ ⟶ W`. -/
@[reassoc]
theorem normalConeToStrictTransformComplAtInfinity_ι_eq {S : Scheme.{u}} (sX : X ⟶ S) :
    normalConeToStrictTransformComplAtInfinity i ≫ (strictTransformComplAtInfinity i.ker).ι =
      normalConeToFibreAtInfinity i sX ≫
        modificationInclusionAtInfinity sX (blowupAtInfinityToProjectiveLineProduct i.ker sX) := by
  rw [normalConeToStrictTransformComplAtInfinity_ι, normalConeToFibreAtInfinity_inclusion]

end NormalCone

section Charts

variable (ℐ : X.IdealSheafData) (U : X.affineOpens)

/-- The chart `D₊(S)` of the blowup at infinity over an affine open `U` of `X`, as a morphism into
`W ∖ X'`: the chart misses the strict transform. -/
def blowupAtInfinityChartSCompl :
    Spec (.of (infinityChartAlgebra (ℐ.ideal U))) ⟶ (strictTransformComplAtInfinity ℐ).toScheme :=
  IsOpenImmersion.lift (strictTransformComplAtInfinity ℐ).ι (blowupAtInfinityChartS ℐ U) (by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact notMem_strictTransform_of_mem_range_chartS ℐ U ⟨z, rfl⟩)

/-- The chart `D₊(S)` into `W ∖ X'` followed by the inclusion into `W` is the chart `D₊(S)`. -/
@[reassoc (attr := simp)]
theorem blowupAtInfinityChartSCompl_ι :
    blowupAtInfinityChartSCompl ℐ U ≫ (strictTransformComplAtInfinity ℐ).ι =
      blowupAtInfinityChartS ℐ U :=
  IsOpenImmersion.lift_fac _ _ _

/-- The chart `D₊(S)` into `W ∖ X'` is an open immersion. -/
instance : IsOpenImmersion (blowupAtInfinityChartSCompl ℐ U) := by
  have : IsOpenImmersion
      (blowupAtInfinityChartSCompl ℐ U ≫ (strictTransformComplAtInfinity ℐ).ι) := by
    rw [blowupAtInfinityChartSCompl_ι]
    infer_instance
  exact IsOpenImmersion.of_comp _ (strictTransformComplAtInfinity ℐ).ι

variable {ℐY ℐZ : X.IdealSheafData} (h : ℐY ≤ ℐZ)

include h in
/-- An inclusion `ℐ_Y ≤ ℐ_Z` of ideal sheaves, on the sections over an affine open, in the form
the maps of affine charts take. -/
theorem map_id_ideal_le_of_le : (ℐY.ideal U).map (RingHom.id Γ(X, U.1)) ≤ ℐZ.ideal U := by
  rw [Ideal.map_id]
  exact h U

/-- **The charts `D₊(S)` are compatible with the change of centre.** The chart of `W_Z` over `U`,
followed by `ρ`, is `Spec` of the map `A[s][J_Z/s] ⟵ A[s][J_Y/s]` of affine blowup algebras
induced by `ℐ_Y(U) ⊆ ℐ_Z(U)`, followed by the chart of `W_Y` over `U`: both lift the chart
`D₊(S) ⟶ 𝐏¹_X` through the blowup `W_Y`, along which `∞(Y)` pulls back to the effective Cartier
divisor `(s)` (Stacks 0806). -/
theorem specMap_infinityChartAlgebraMap_blowupAtInfinityChartS_changeOfCentre :
    Spec.map (CommRingCat.ofHom (infinityChartAlgebraMap (RingHom.id Γ(X, U.1))
        (map_id_ideal_le_of_le U h))) ≫ blowupAtInfinityChartS ℐY U =
      blowupAtInfinityChartSCompl ℐZ U ≫ blowupAtInfinityChangeOfCentre h := by
  have hg : Stacks.Blowup.IsCartierOver (infinityCentreIdeal ℐY)
      (Over.mk (blowupAtInfinityChartS ℐZ U ≫ blowupAtInfinityToLine ℐZ)) := by
    change Stacks.Divisors.IsEffectiveCartierDivisor
      ((infinityCentreIdeal ℐY).comap (blowupAtInfinityChartS ℐZ U ≫ blowupAtInfinityToLine ℐZ))
    rw [← blowupAtInfinityChartSCompl_ι, Category.assoc, Scheme.IdealSheafData.comap_comp]
    exact Stacks.Blowup.isEffectiveCartierDivisor_comap_of_isOpenImmersion _
      (isCartierOver_infinityCentreIdeal_strictTransformComplAtInfinity_ι h) _
  have h1 : (Spec.map (CommRingCat.ofHom (infinityChartAlgebraMap (RingHom.id Γ(X, U.1))
        (map_id_ideal_le_of_le U h))) ≫ blowupAtInfinityChartS ℐY U) ≫
          blowUpToBase (infinityCentreIdeal ℐY) =
      blowupAtInfinityChartS ℐZ U ≫ blowupAtInfinityToLine ℐZ := by
    change _ ≫ blowupAtInfinityToLine ℐY = _
    rw [Category.assoc, blowupAtInfinityChartS, blowupAtInfinityChartS,
      blowupAtInfinityPolyChart_comp, blowupAtInfinityPolyChart_comp, ← Category.assoc,
      ← Spec.map_comp]
    congr 2
    apply CommRingCat.hom_ext
    refine RingHom.ext fun p => ?_
    change infinityChartAlgebraMap _ (map_id_ideal_le_of_le U h) (algebraMap _ _ p) = _
    rw [infinityChartAlgebraMap_algebraMap, Polynomial.map_id]
    rfl
  have h2 : (blowupAtInfinityChartSCompl ℐZ U ≫ blowupAtInfinityChangeOfCentre h) ≫
      blowUpToBase (infinityCentreIdeal ℐY) =
      blowupAtInfinityChartS ℐZ U ≫ blowupAtInfinityToLine ℐZ := by
    change _ ≫ blowupAtInfinityToLine ℐY = _
    rw [Category.assoc, blowupAtInfinityChangeOfCentre_comp, blowupAtInfinityChartSCompl_ι_assoc]
  exact (blowUpLift_unique _ _ hg _ h1).trans (blowUpLift_unique _ _ hg _ h2).symm

end Charts

section NormalConeCharts

variable {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- On the chart over an affine open `U`, the closed immersion `C_ZX ⟶ W ∖ X'` is the quotient
`A[s][J/s] ⟶ A[s][J/s] ⧸ (s) ≅ Gr_{ℐ(U)}(A)` followed by the chart `D₊(S)`. -/
theorem normalConeChart_normalConeToStrictTransformComplAtInfinity (U : X.affineOpens) :
    normalConeChart i U ≫ normalConeToStrictTransformComplAtInfinity i =
      Spec.map ((exceptionalChartSectionsIso i U).hom) ≫
        Spec.map (exceptionalChartQuotient i.ker U) ≫ blowupAtInfinityChartSCompl i.ker U := by
  rw [← cancel_mono (strictTransformComplAtInfinity i.ker).ι, Category.assoc,
    normalConeToStrictTransformComplAtInfinity_ι, Category.assoc, Category.assoc,
    blowupAtInfinityChartSCompl_ι]
  simp only [normalConeToExceptionalDivisor, Category.assoc,
    normalConeChart_normalConeIsoExceptionalCompl_hom_assoc, exceptionalComplChartT,
    exceptionalComplChart_ι_assoc, exceptionalChartS_subschemeι]

end NormalConeCharts

section ChangeOfCentre

variable {Z Y : Scheme.{u}} (iZ : Z ⟶ X) [IsClosedImmersion iZ] (iY : Y ⟶ X)
  [IsClosedImmersion iY] (h : iY.ker ≤ iZ.ker)

/-- The restriction `C_ZX ⟶ E_Y` of the change of centre to the normal cone
`C_ZX ⊆ W_Z ∖ X'_Z`: along it the exceptional divisor `E_Y` pulls back to `W_{Z,∞}`, which
contains `C_ZX ⊆ E_Z`. -/
def normalConeToExceptionalDivisorChangeOfCentre :
    Stacks.Conormal.normalCone iZ ⟶ (exceptionalIdealAtInfinity iY.ker).subscheme :=
  IsClosedImmersion.lift (exceptionalIdealAtInfinity iY.ker).subschemeι
    (normalConeToStrictTransformComplAtInfinity iZ ≫ blowupAtInfinityChangeOfCentre h) (by
      have hfib : fibreIdealAtInfinity iZ.ker ≤
          (exceptionalIdealAtInfinity iZ.ker).subschemeι.ker := by
        rw [Scheme.IdealSheafData.ker_subschemeι]
        exact fibreIdealAtInfinity_le_exceptionalIdealAtInfinity iZ.ker
      rw [Scheme.IdealSheafData.ker_subschemeι, AlgebraicGeometry.le_ker_iff_comap_eq_bot,
        Scheme.IdealSheafData.comap_comp, comap_exceptionalIdealAtInfinity_changeOfCentre h,
        ← Scheme.IdealSheafData.comap_comp, normalConeToStrictTransformComplAtInfinity_ι,
        Scheme.IdealSheafData.comap_comp,
        (AlgebraicGeometry.le_ker_iff_comap_eq_bot _ _).1 hfib, Scheme.IdealSheafData.comap_bot])

omit [IsClosedImmersion iY] in
/-- `C_ZX ⟶ E_Y ⟶ W_Y` is the restriction of the change of centre to `C_ZX`. -/
@[reassoc (attr := simp)]
theorem normalConeToExceptionalDivisorChangeOfCentre_subschemeι :
    normalConeToExceptionalDivisorChangeOfCentre iZ iY h ≫
        (exceptionalIdealAtInfinity iY.ker).subschemeι =
      normalConeToStrictTransformComplAtInfinity iZ ≫ blowupAtInfinityChangeOfCentre h :=
  IsClosedImmersion.lift_fac _ _ _

/-- **The morphism of normal cones `C_ZX ⟶ C_YX` induced by `ker (Y ⟶ X) ≤ ker (Z ⟶ X)`**: the
restriction of the change of centre `W_Z ∖ X'_Z ⟶ W_Y ∖ X'_Y` to `C_ZX = E_Z ∖ X'_Z`, which lands
in `C_YX = E_Y ∖ X'_Y` (Stacks 0FBH). -/
def normalConeChangeOfCentreMap :
    Stacks.Conormal.normalCone iZ ⟶ Stacks.Conormal.normalCone iY :=
  IsOpenImmersion.lift (normalConeToExceptionalDivisor iY)
    (normalConeToExceptionalDivisorChangeOfCentre iZ iY h) (by
      rintro _ ⟨x, rfl⟩
      have hx : normalConeToExceptionalDivisorChangeOfCentre iZ iY h x ∈
          (normalConeToExceptionalDivisor iY).opensRange := by
        rw [opensRange_normalConeToExceptionalDivisor, Scheme.Hom.mem_preimage,
          ← Scheme.Hom.comp_apply, normalConeToExceptionalDivisorChangeOfCentre_subschemeι,
          ← blowupAtInfinityChangeOfCentreCompl_ι h, ← Category.assoc, Scheme.Hom.comp_apply]
        exact (_ : (strictTransformComplAtInfinity iY.ker).toScheme).2
      exact hx)

/-- The morphism of normal cones is `C_ZX ⟶ E_Y`, through the open immersion `C_YX ⟶ E_Y` of
Stacks 0FBH. -/
@[reassoc (attr := simp)]
theorem normalConeChangeOfCentreMap_comp :
    normalConeChangeOfCentreMap iZ iY h ≫ normalConeToExceptionalDivisor iY =
      normalConeToExceptionalDivisorChangeOfCentre iZ iY h :=
  IsOpenImmersion.lift_fac _ _ _

/-- The morphism of normal cones is the restriction of the change of centre, read through the
open immersion `C_YX ⟶ E_Y` of Stacks 0FBH. -/
@[reassoc]
theorem normalConeChangeOfCentreMap_comp_exceptionalDivisor :
    normalConeChangeOfCentreMap iZ iY h ≫ normalConeToExceptionalDivisor iY ≫
        (exceptionalIdealAtInfinity iY.ker).subschemeι =
      normalConeToStrictTransformComplAtInfinity iZ ≫ blowupAtInfinityChangeOfCentre h := by
  rw [normalConeChangeOfCentreMap_comp_assoc,
    normalConeToExceptionalDivisorChangeOfCentre_subschemeι]

/-- **The morphism of normal cones is the restriction of the change of centre
`W_Z ∖ X'_Z ⟶ W_Y ∖ X'_Y`** to the closed subschemes `C_ZX` and `C_YX`. -/
@[reassoc]
theorem normalConeChangeOfCentreMap_comp_strictTransformCompl :
    normalConeChangeOfCentreMap iZ iY h ≫ normalConeToStrictTransformComplAtInfinity iY =
      normalConeToStrictTransformComplAtInfinity iZ ≫ blowupAtInfinityChangeOfCentreCompl h := by
  rw [← cancel_mono (strictTransformComplAtInfinity iY.ker).ι, Category.assoc,
    normalConeToStrictTransformComplAtInfinity_ι,
    normalConeChangeOfCentreMap_comp_exceptionalDivisor,
    Category.assoc, blowupAtInfinityChangeOfCentreCompl_ι]

/-- The morphism of normal cones lies over `X`. -/
@[reassoc (attr := simp)]
theorem normalConeChangeOfCentreMap_toX :
    normalConeChangeOfCentreMap iZ iY h ≫ normalConeToX iY = normalConeToX iZ := by
  change normalConeChangeOfCentreMap iZ iY h ≫ Stacks.Conormal.normalConeToBase iY ≫ iY =
    Stacks.Conormal.normalConeToBase iZ ≫ iZ
  rw [← normalConeToExceptionalDivisor_comp_toBase, ← normalConeToExceptionalDivisor_comp_toBase,
    normalConeChangeOfCentreMap_comp_exceptionalDivisor_assoc,
    blowupAtInfinityChangeOfCentre_toBase, ← normalConeToStrictTransformComplAtInfinity_ι_assoc]

/-- The morphism of normal cones lies over `Z ⟶ Y`. -/
@[reassoc]
theorem normalConeChangeOfCentreMap_toBase (g : Z ⟶ Y) (hg : g ≫ iY = iZ) :
    normalConeChangeOfCentreMap iZ iY h ≫ Stacks.Conormal.normalConeToBase iY =
      Stacks.Conormal.normalConeToBase iZ ≫ g := by
  rw [← cancel_mono iY, Category.assoc, Category.assoc, hg]
  exact normalConeChangeOfCentreMap_toX iZ iY h

/-- The morphism of normal cones is the restriction of the change of centre, read through the
open immersion `j : C_YX ⟶ W_{Y,∞}` of Stacks 0FBH into the fibre at infinity, for any morphism
`X ⟶ S`; on the source, `C_ZX ⟶ W_Z ∖ X'_Z ⟶ W_Z` is `j : C_ZX ⟶ W_{Z,∞} ⟶ W_Z`
(`Stacks.Chow.normalConeToStrictTransformComplAtInfinity_ι_eq`). -/
@[reassoc]
theorem normalConeChangeOfCentreMap_comp_inclusion {S : Scheme.{u}} (sX : X ⟶ S) :
    normalConeChangeOfCentreMap iZ iY h ≫ normalConeToFibreAtInfinity iY sX ≫
        modificationInclusionAtInfinity sX (blowupAtInfinityToProjectiveLineProduct iY.ker sX) =
      normalConeToStrictTransformComplAtInfinity iZ ≫ blowupAtInfinityChangeOfCentre h := by
  rw [normalConeToFibreAtInfinity_inclusion, normalConeChangeOfCentreMap_comp_exceptionalDivisor]

/-- The morphism of normal cones commutes with the open immersions `j` of Stacks 0FBH followed by
the projections of the fibres at infinity to `X`, for any morphism `X ⟶ S`. -/
@[reassoc]
theorem normalConeChangeOfCentreMap_comp_projection {S : Scheme.{u}} (sX : X ⟶ S) :
    normalConeChangeOfCentreMap iZ iY h ≫ normalConeToFibreAtInfinity iY sX ≫
        modificationProjectionAtInfinity sX (blowupAtInfinityToProjectiveLineProduct iY.ker sX) =
      normalConeToFibreAtInfinity iZ sX ≫
        modificationProjectionAtInfinity sX
          (blowupAtInfinityToProjectiveLineProduct iZ.ker sX) := by
  rw [normalConeToFibreAtInfinity_comp_projection, normalConeToFibreAtInfinity_comp_projection]
  exact normalConeChangeOfCentreMap_toX iZ iY h

/-- **The map of conormal algebras on the chart over an affine open `U = Spec A`**: the ring map
`Γ(Y ∩ U, 𝒞_{Y/X,*}) ⟶ Γ(Z ∩ U, 𝒞_{Z/X,*})` which, read through
`Γ(Z ∩ U, 𝒞_{Z/X,*}) ≅ A[s][J/s] ⧸ (s)` (Stacks 0FBH), is the map of fibres of the charts
`D₊(S)` induced by `ℐ_Y(U) ⊆ ℐ_Z(U)`. -/
def conormalSectionsChangeOfCentre (U : X.affineOpens) :
    (conormalSituation iY).algebra.sections (subschemeAffineOpen iY U).1 ⟶
      (conormalSituation iZ).algebra.sections (subschemeAffineOpen iZ U).1 :=
  (exceptionalChartSectionsIso iY U).inv ≫
    CommRingCat.ofHom (infinityChartFibreMap (RingHom.id Γ(X, U.1))
      (map_id_ideal_le_of_le U h)) ≫
    (exceptionalChartSectionsIso iZ U).hom

/-- **The morphism of normal cones on the charts over an affine open `U`** is the spectrum of
the map of conormal algebras. -/
theorem specMap_conormalSectionsChangeOfCentre_normalConeChart (U : X.affineOpens) :
    Spec.map (conormalSectionsChangeOfCentre iZ iY h U) ≫ normalConeChart iY U =
      normalConeChart iZ U ≫ normalConeChangeOfCentreMap iZ iY h := by
  rw [← cancel_mono (normalConeToExceptionalDivisor iY ≫
      (exceptionalIdealAtInfinity iY.ker).subschemeι), Category.assoc, Category.assoc,
    normalConeChangeOfCentreMap_comp_exceptionalDivisor, ← Category.assoc (normalConeChart iZ U),
    normalConeChart_normalConeToStrictTransformComplAtInfinity, Category.assoc, Category.assoc,
    ← specMap_infinityChartAlgebraMap_blowupAtInfinityChartS_changeOfCentre]
  simp only [normalConeToExceptionalDivisor, Category.assoc,
    normalConeChart_normalConeIsoExceptionalCompl_hom_assoc, exceptionalComplChartT,
    exceptionalComplChart_ι_assoc, exceptionalChartS_subschemeι]
  simp only [← Spec.map_comp_assoc]
  congr 2
  rw [conormalSectionsChangeOfCentre, Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc]
  congr 1

/-- The map of conormal algebras is the map of fibres of the charts `D₊(S)`, through the
identifications `exceptionalChartSectionsEquiv`. -/
theorem conormalSectionsChangeOfCentre_exceptionalChartSectionsEquiv (U : X.affineOpens)
    (x : infinityChartAlgebra (iY.ker.ideal U) ⧸ infinityChartFibreIdeal (iY.ker.ideal U)) :
    (conormalSectionsChangeOfCentre iZ iY h U).hom (exceptionalChartSectionsEquiv iY U x) =
      exceptionalChartSectionsEquiv iZ U
        (infinityChartFibreMap (RingHom.id Γ(X, U.1)) (map_id_ideal_le_of_le U h) x) := by
  have h' : (conormalSectionsChangeOfCentre iZ iY h U).hom
      ((exceptionalChartSectionsIso iY U).hom.hom x) =
        (exceptionalChartSectionsIso iZ U).hom.hom
          (infinityChartFibreMap (RingHom.id Γ(X, U.1)) (map_id_ideal_le_of_le U h) x) := by
    rw [conormalSectionsChangeOfCentre, CommRingCat.comp_apply, CommRingCat.comp_apply,
      Iso.hom_inv_id_apply]
    rfl
  exact h'

/-- **The map of conormal algebras is the map of associated graded rings
`Gr_{ℐ_Y(U)}(A) ⟶ Gr_{ℐ_Z(U)}(A)` induced by `ℐ_Y(U) ⊆ ℐ_Z(U)`**, through the identifications
`Stacks.Conormal.conormalAlgebraSheafSectionsEquiv` of the sections of the conormal algebras with
the associated graded rings. -/
theorem conormalSectionsChangeOfCentre_conormalAlgebraSheafSectionsEquiv (U : X.affineOpens)
    (w : AssociatedGraded.gradedRing (Stacks.Conormal.chartIdeal iY U)) :
    (conormalSectionsChangeOfCentre iZ iY h U).hom
        (Stacks.Conormal.conormalAlgebraSheafSectionsEquiv iY U inferInstance w) =
      Stacks.Conormal.conormalAlgebraSheafSectionsEquiv iZ U inferInstance
        (AssociatedGraded.gradedRingMapOfRingHom (RingHom.id Γ(X, U.1)) (by
          rw [Ideal.map_id, chartIdeal_eq_ker_ideal, chartIdeal_eq_ker_ideal]
          exact h U) w) := by
  obtain ⟨z, rfl⟩ := (AssociatedGraded.gradedRingEquivOfEq
    (chartIdeal_eq_ker_ideal iY U).symm).surjective w
  rw [AssociatedGraded.gradedRingEquivOfEq_apply, ← exceptionalChartSectionsEquiv_conormalEquiv,
    conormalSectionsChangeOfCentre_exceptionalChartSectionsEquiv,
    infinityChartFibreMap_conormalEquiv, exceptionalChartSectionsEquiv_conormalEquiv]
  have hh : (iY.ker.ideal U).map ((RingHom.id Γ(X, U.1)).comp (RingHom.id Γ(X, U.1))) ≤
      Stacks.Conormal.chartIdeal iZ U := by
    rw [RingHom.comp_id, Ideal.map_id]
    exact (h U).trans (chartIdeal_eq_ker_ideal iZ U).ge
  have e1 := AssociatedGraded.gradedRingMapOfRingHom_comp_apply (RingHom.id Γ(X, U.1))
    (RingHom.id Γ(X, U.1)) (I := iY.ker.ideal U) (I' := iZ.ker.ideal U)
    (I'' := Stacks.Conormal.chartIdeal iZ U) (map_id_ideal_le_of_le U h)
    (by rw [Ideal.map_id, chartIdeal_eq_ker_ideal]) hh z
  have e2 := AssociatedGraded.gradedRingMapOfRingHom_comp_apply (RingHom.id Γ(X, U.1))
    (RingHom.id Γ(X, U.1)) (I := iY.ker.ideal U) (I' := Stacks.Conormal.chartIdeal iY U)
    (I'' := Stacks.Conormal.chartIdeal iZ U) (by rw [Ideal.map_id, chartIdeal_eq_ker_ideal])
    (by rw [Ideal.map_id, chartIdeal_eq_ker_ideal, chartIdeal_eq_ker_ideal]; exact h U) hh z
  exact congrArg (Stacks.Conormal.conormalAlgebraSheafSectionsEquiv iZ U inferInstance)
    (e1.trans e2.symm)

/-- The morphism of normal cones is locally of finite type when `X` is locally Noetherian: its
composite with `C_YX ⟶ X` is `C_ZX ⟶ X`, which is. -/
instance locallyOfFiniteType_normalConeChangeOfCentreMap [IsLocallyNoetherian X] :
    LocallyOfFiniteType (normalConeChangeOfCentreMap iZ iY h) := by
  have : LocallyOfFiniteType (normalConeToX iZ) := by
    change LocallyOfFiniteType (Stacks.Conormal.normalConeToBase iZ ≫ iZ)
    rw [← normalConeToExceptionalDivisor_comp_toBase]
    infer_instance
  have : LocallyOfFiniteType (normalConeChangeOfCentreMap iZ iY h ≫ normalConeToX iY) := by
    rw [normalConeChangeOfCentreMap_toX]
    infer_instance
  exact locallyOfFiniteType_of_comp _ (normalConeToX iY)

/-- The morphism of normal cones is locally of finite type when `X` is locally of finite type
over a locally Noetherian base. -/
theorem locallyOfFiniteType_normalConeChangeOfCentreMap_of_locallyOfFiniteType {S : Scheme.{u}}
    (sX : X ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType sX] :
    LocallyOfFiniteType (normalConeChangeOfCentreMap iZ iY h) := by
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  infer_instance

end ChangeOfCentre

end Stacks.Chow

end
