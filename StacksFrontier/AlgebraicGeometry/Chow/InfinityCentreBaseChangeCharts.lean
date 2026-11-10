module

public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreBaseChange

/-!
# The base change of the blowup at infinity on affine charts

Let `f : X' ⟶ X` be a morphism of schemes, `i : Z ⟶ X` a closed immersion and
`i' : Z' = Z ×_X X' ⟶ X'` its base change. Let `U = Spec A` be an affine open of `X` and
`U' = Spec A'` an affine open of `X'` with `f(U') ⊆ U`, and write `φ : A ⟶ A'` for the induced
ring map, `I ⊆ A` and `I' ⊆ A'` for the ideals of `Z` and `Z'`. Then `φ(I) ⊆ I'`, and the
comparison `W' ⟶ W` of the blowups at infinity carries the chart `D₊(S') = Spec A'[s][J'/s]` of
`W'` into the chart `D₊(S) = Spec A[s][J/s]` of `W` by the spectrum of the map of affine blowup
algebras induced by `φ`. Restricted to the exceptional divisors, and read through Stacks 0FBH, this
says that the comparison `C_{Z'}X' ⟶ C_ZX` of the normal cones is, over `U'`, the spectrum of the
map `Gr_I(A) ⟶ Gr_{I'}(A')` of associated graded rings induced by `φ`.

## Main results

* `Stacks.Chow.specMap_map_infinityChartOver_baseChange` — the charts at infinity of `𝐏¹_{X'}` and
  `𝐏¹_X` are compatible with `𝐏¹_{X'} ⟶ 𝐏¹_X`.
* `Stacks.Chow.specMap_infinityChartAlgebraMap_blowupAtInfinityChartS_baseChange` — the charts
  `D₊(S)` are compatible with the comparison `W' ⟶ W`.
* `Stacks.Chow.specMap_conormalSectionsBaseChange_normalConeChart` — the comparison of the normal
  cones on the charts over `U'` and `U`.

## References

* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBH](https://stacks.math.columbia.edu/tag/0FBH)
* [Stacks Project, Tag 0806](https://stacks.math.columbia.edu/tag/0806)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Chow

variable {X X' : Scheme.{u}} (f : X' ⟶ X)

/-- The second affine chart of `𝐏¹` is compatible with base change. -/
@[reassoc]
theorem affineYChart_comp_projectiveLineBaseChange :
    affineYChart X' ≫ projectiveLineBaseChange f = affineLineOverMap f ≫ affineYChart X := by
  refine pullback.hom_ext ?_ ?_
  · change (affineYChart X' ≫ projectiveLineBaseChange f) ≫ (relativeProjectiveLine X ↘ X) =
      affineLineOverMap f ≫ affineYChart X ≫ (relativeProjectiveLine X ↘ X)
    rw [Category.assoc, projectiveLineBaseChange_over, ← Category.assoc, affineYChart_comp,
      affineYChart_comp, affineLineOverMap_fst]
  · rw [Category.assoc, Category.assoc, projectiveLineBaseChange_comp_snd]
    simp only [affineYChart, pullback.lift_snd, affineLineOverMap_snd_assoc]

section Charts

variable {U : X.affineOpens} {U' : X'.affineOpens} (hUU' : U'.1 ≤ f ⁻¹ᵁ U.1)

/-- The ring map `Γ(X, U) ⟶ Γ(X', U')` induced by `f`, for affine opens with `f(U') ⊆ U`. -/
abbrev affineBaseChangeMap : Γ(X, U.1) →+* Γ(X', U'.1) :=
  (f.appLE U.1 U'.1 hUU').hom

/-- **The charts at infinity are compatible with base change**: `Spec` of the polynomial map of
`Γ(X, U) ⟶ Γ(X', U')`, followed by the chart at infinity over `U`, is the chart at infinity over
`U'` followed by `𝐏¹_{X'} ⟶ 𝐏¹_X`. -/
theorem specMap_map_infinityChartOver_baseChange :
    Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (affineBaseChangeMap f hUU'))) ≫
      infinityChartOver U = infinityChartOver U' ≫ projectiveLineBaseChange f := by
  have key : ∀ {Y : Scheme.{u}} (W : Y.affineOpens),
      infinityChartOver W = infinityChartBase W ≫ affineYChart Y :=
    fun _ => (Category.assoc _ _ _).symm
  rw [key, key, Category.assoc, affineYChart_comp_projectiveLineBaseChange, ← Category.assoc,
    ← Category.assoc]
  congr 1
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, infinityChartBase_fst, Category.assoc, affineLineOverMap_fst,
      ← Category.assoc (infinityChartBase U'), infinityChartBase_fst, Category.assoc,
      ← IsAffineOpen.SpecMap_appLE_fromSpec f U.2 U'.2 hUU', ← Category.assoc,
      ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    apply CommRingCat.hom_ext
    refine RingHom.ext fun a => ?_
    simp
  · rw [Category.assoc, infinityChartBase_snd, Category.assoc, affineLineOverMap_snd,
      infinityChartBase_snd, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    refine polynomial_ulift_int_ringHom_ext ?_
    simp

/-- The ideal of a closed immersion `i : Z ⟶ X` on `U` is carried into the ideal of a closed
immersion `i' : Z' ⟶ X'` on `U'` over it. -/
theorem map_ideal_ker_le {Z Z' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (i' : Z' ⟶ X')
    [IsClosedImmersion i'] (g : Z' ⟶ Z) (hcomm : i' ≫ f = g ≫ i) :
    (i.ker.ideal U).map (affineBaseChangeMap f hUU') ≤ i'.ker.ideal U' := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Scheme.Hom.ker_apply] at ha
  rw [Ideal.mem_comap, Scheme.Hom.ker_apply, RingHom.mem_ker]
  have hle : i' ⁻¹ᵁ U'.1 ≤ (g ≫ i) ⁻¹ᵁ U.1 := by
    rw [← hcomm]
    exact fun x hx => hUU' hx
  have key : ∀ (p : Z' ⟶ X) (hp : i' ⁻¹ᵁ U'.1 ≤ p ⁻¹ᵁ U.1),
      p = g ≫ i → (p.appLE U.1 (i' ⁻¹ᵁ U'.1) hp).hom a = 0 := by
    rintro p hp rfl
    rw [← Scheme.Hom.appLE_comp_appLE g i U.1 (i ⁻¹ᵁ U.1) _ le_rfl
      (fun x hx => hp hx), CommRingCat.comp_apply, Scheme.Hom.appLE_eq_app]
    change g.appLE _ _ _ ((i.app U.1).hom a) = 0
    rw [RingHom.mem_ker.mp ha, map_zero]
  have hsplit : f.appLE U.1 U'.1 hUU' ≫ i'.app U'.1 =
      (i' ≫ f).appLE U.1 (i' ⁻¹ᵁ U'.1) (by rw [hcomm]; exact hle) := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  change (i'.app U'.1).hom ((f.appLE U.1 U'.1 hUU').hom a) = 0
  rw [← CommRingCat.comp_apply, hsplit]
  exact key _ _ hcomm

variable (ℐ : X.IdealSheafData) (ℐ' : X'.IdealSheafData) (h : ℐ' = ℐ.comap f)
  (hI : (ℐ.ideal U).map (affineBaseChangeMap f hUU') ≤ ℐ'.ideal U')

/-- **The charts `D₊(S)` are compatible with the comparison `W' ⟶ W`.** The chart over `U'`
followed by `W' ⟶ W` is `Spec` of the map of affine blowup algebras induced by
`Γ(X, U) ⟶ Γ(X', U')`, followed by the chart over `U`. -/
theorem specMap_infinityChartAlgebraMap_blowupAtInfinityChartS_baseChange :
    Spec.map (CommRingCat.ofHom (infinityChartAlgebraMap (affineBaseChangeMap f hUU') hI)) ≫
        blowupAtInfinityChartS ℐ U =
      blowupAtInfinityChartS ℐ' U' ≫ blowupAtInfinityComap f ℐ ℐ' h := by
  have hg : Stacks.Blowup.IsCartierOver (infinityCentreIdeal ℐ)
      (Over.mk (blowupAtInfinityChartS ℐ' U' ≫ blowupAtInfinityToLine ℐ' ≫
        projectiveLineBaseChange f)) := by
    change Stacks.Divisors.IsEffectiveCartierDivisor
      ((infinityCentreIdeal ℐ).comap
        (blowupAtInfinityChartS ℐ' U' ≫ blowupAtInfinityToLine ℐ' ≫ projectiveLineBaseChange f))
    rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp,
      comap_infinityCentreIdeal_projectiveLineBaseChange_eq, ← h]
    exact isEffectiveCartierDivisor_comap_blowupAtInfinityChartS ℐ' U'
  have h1 : (Spec.map (CommRingCat.ofHom (infinityChartAlgebraMap (affineBaseChangeMap f hUU')
        hI)) ≫ blowupAtInfinityChartS ℐ U) ≫ blowUpToBase (infinityCentreIdeal ℐ) =
      blowupAtInfinityChartS ℐ' U' ≫ blowupAtInfinityToLine ℐ' ≫ projectiveLineBaseChange f := by
    change _ ≫ blowupAtInfinityToLine ℐ = _
    rw [Category.assoc, blowupAtInfinityChartS, blowupAtInfinityChartS,
      blowupAtInfinityPolyChart_comp, blowupAtInfinityPolyChart_comp_assoc,
      ← specMap_map_infinityChartOver_baseChange f hUU', ← Category.assoc, ← Spec.map_comp,
      ← Category.assoc, ← Spec.map_comp]
    congr 2
    apply CommRingCat.hom_ext
    exact RingHom.ext fun p => infinityChartAlgebraMap_algebraMap _ hI p
  have h2 : (blowupAtInfinityChartS ℐ' U' ≫ blowupAtInfinityComap f ℐ ℐ' h) ≫
      blowUpToBase (infinityCentreIdeal ℐ) =
      blowupAtInfinityChartS ℐ' U' ≫ blowupAtInfinityToLine ℐ' ≫ projectiveLineBaseChange f := by
    change _ ≫ blowupAtInfinityToLine ℐ = _
    rw [Category.assoc, blowupAtInfinityComap_comp]
  exact (blowUpLift_unique _ _ hg _ h1).trans (blowUpLift_unique _ _ hg _ h2).symm

end Charts

section NormalCone

variable {S : Scheme.{u}} (sX : X ⟶ S) {Z Z' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  (i' : Z' ⟶ X') [IsClosedImmersion i'] (g : Z' ⟶ Z) (hcomm : i' ≫ f = g ≫ i)
  (hker : i'.ker = i.ker.comap f)
  {U : X.affineOpens} {U' : X'.affineOpens} (hUU' : U'.1 ≤ f ⁻¹ᵁ U.1)

/-- **The comparison of the conormal algebras on the charts over `U'` and `U`**: the ring map
`Γ(Z ∩ U, 𝒞_{Z/X,*}) ⟶ Γ(Z' ∩ U', 𝒞_{Z'/X',*})` which, read through
`Γ(Z ∩ U, 𝒞_{Z/X,*}) ≅ A[s][J/s] ⧸ (s)` (Stacks 0FBH), is the map of fibres of the charts
`D₊(S)` induced by `φ : Γ(X, U) ⟶ Γ(X', U')`. -/
def conormalSectionsBaseChange :
    (conormalSituation i).algebra.sections (subschemeAffineOpen i U).1 ⟶
      (conormalSituation i').algebra.sections (subschemeAffineOpen i' U').1 :=
  (exceptionalChartSectionsIso i U).inv ≫
    CommRingCat.ofHom (infinityChartFibreMap (affineBaseChangeMap f hUU')
      (map_ideal_ker_le f hUU' i i' g hcomm)) ≫
    (exceptionalChartSectionsIso i' U').hom

/-- **The comparison `C_{Z'}X' ⟶ C_ZX` of the normal cones on the charts over `U'` and `U`** is
the spectrum of the comparison of the conormal algebras. -/
theorem specMap_conormalSectionsBaseChange_normalConeChart :
    Spec.map (conormalSectionsBaseChange f i i' g hcomm hUU') ≫ normalConeChart i U =
      normalConeChart i' U' ≫ normalConeBaseChangeMap f sX i i' hker := by
  rw [← cancel_mono (normalConeToFibreAtInfinity i sX), Category.assoc, Category.assoc,
    normalConeBaseChangeMap_comp,
    ← cancel_mono (modificationInclusionAtInfinity sX
      (blowupAtInfinityToProjectiveLineProduct i.ker sX)),
    Category.assoc, Category.assoc, Category.assoc, normalConeToFibreAtInfinity_inclusion]
  simp only [Category.assoc]
  rw [blowupAtInfinityFibreComap_inclusion, ← Category.assoc (normalConeToFibreAtInfinity _ _),
    normalConeToFibreAtInfinity_inclusion]
  simp only [normalConeToExceptionalDivisor, Category.assoc,
    normalConeChart_normalConeIsoExceptionalCompl_hom_assoc, exceptionalComplChartT,
    exceptionalComplChart_ι_assoc, exceptionalChartS_subschemeι_assoc,
    exceptionalChartS_subschemeι]
  rw [← specMap_infinityChartAlgebraMap_blowupAtInfinityChartS_baseChange f hUU' i.ker
    i'.ker hker (map_ideal_ker_le f hUU' i i' g hcomm)]
  simp only [← Spec.map_comp_assoc]
  congr 2
  rw [conormalSectionsBaseChange, Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc]
  congr 1

end NormalCone

end Stacks.Chow

end
