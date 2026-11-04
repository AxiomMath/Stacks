module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinClass
public import StacksFrontier.AlgebraicGeometry.Chow.GysinGysinPulledBackModule
public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreResidualGysin
public import StacksFrontier.AlgebraicGeometry.Chow.NormalConeZeroSection

/-!
# The Gysin map of the zero section of a normal line cone (Stacks 0FEB)

Let `(S, δ)` be as in Situation 02QL, `X` locally of finite type over `S` with `dim_δ(X) ≤ n`,
and `Z ⊆ Y ⊆ X` closed subschemes with `Y` an effective Cartier divisor. Let `o : Y ⟶ C_YX` be the
zero section of the normal line cone and `o^* ∈ A^1(Y ⟶ C_YX)` its Gysin class (Stacks 0B79).
Stacks 0FEB says

  `o^*[C_ZX]_n = [C_ZY]_{n-1}`  in  `CH_{n-1}(Y ×_{o, C_YX} C_ZX)`.

Only `dim_δ(X) ≤ n` is assumed: the source's hypotheses that `X` is integral of `δ`-dimension
exactly `n` and that `Z` is an effective Cartier divisor are not needed.

## Main results

* `Stacks.Chow.gysinBivariantClass_cap_normalCone` — **Stacks 0FEB**.
* `Stacks.Chow.gysinBivariantClass_cap_normalCone_eq` — the same, with the inclusions `ℐ_Y ⊆ ℐ_Z`
  and `ℐ_{Z ⊆ Y} = ℐ_Z · 𝒪_Y` as data.
* `Stacks.Chow.normalConeToZeroSectionPullback` — the closed immersion
  `C_ZY ⟶ Y ×_{o, C_YX} C_ZX`, with `Stacks.Chow.normalConeToZeroSectionPullback_snd`.
* `Stacks.Chow.gysin_normalConeResidual_fundamentalChowClass` — Stacks 0B73 on `W_Z ∖ X'_Z`,
  evaluated.

## References

* [Stacks Project, Tag 0FEB](https://stacks.math.columbia.edu/tag/0FEB)
* [Stacks Project, Tag 0B73](https://stacks.math.columbia.edu/tag/0B73)
* [Stacks Project, Tag 0B79](https://stacks.math.columbia.edu/tag/0B79)
* [Stacks Project, Tag 0FBG](https://stacks.math.columbia.edu/tag/0FBG)
* [Stacks Project, Tag 02TB](https://stacks.math.columbia.edu/tag/02TB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section Fibres

variable {X Z : Scheme.{u}} (iZ : Z ⟶ X) [IsClosedImmersion iZ]

omit [IsClosedImmersion iZ] in
/-- The zero scheme of the pulled-back canonical section of `𝒪(D_∞)` on `W ∖ X'` is the fibre at
infinity of `W ∖ X'`. -/
theorem zeroScheme_lineInfinityModule_strictTransformComplAtInfinity :
    Stacks.Divisors.zeroScheme _
        (lineInfinityModule ((strictTransformComplAtInfinity iZ.ker).ι ≫
          blowupAtInfinityToLine iZ.ker))
        (lineInfinityModuleSection ((strictTransformComplAtInfinity iZ.ker).ι ≫
          blowupAtInfinityToLine iZ.ker)) =
      (fibreIdealAtInfinity iZ.ker).comap (strictTransformComplAtInfinity iZ.ker).ι := by
  rw [zeroScheme_lineInfinityModuleSection, Scheme.IdealSheafData.comap_comp]
  rfl

/-- **`C_ZX` as the zero scheme of `1_{D_∞}` on `W ∖ X'`** (Stacks 0FBH). -/
def normalConeIsoLineInfinityZeroScheme :
    (Stacks.Divisors.zeroScheme _
        (lineInfinityModule ((strictTransformComplAtInfinity iZ.ker).ι ≫
          blowupAtInfinityToLine iZ.ker))
        (lineInfinityModuleSection ((strictTransformComplAtInfinity iZ.ker).ι ≫
          blowupAtInfinityToLine iZ.ker))).subscheme ≅ Stacks.Conormal.normalCone iZ :=
  eqToIso (congrArg Scheme.IdealSheafData.subscheme
      (zeroScheme_lineInfinityModule_strictTransformComplAtInfinity iZ)) ≪≫
    (normalConeIsoFibreAtInfinityCompl iZ).symm

/-- The identification `Z(1_{D_∞}) ≅ C_ZX` is compatible with the inclusions into `W ∖ X'`. -/
@[reassoc (attr := simp)]
theorem normalConeIsoLineInfinityZeroScheme_hom_comp :
    (normalConeIsoLineInfinityZeroScheme iZ).hom ≫ normalConeToStrictTransformComplAtInfinity iZ =
      (Stacks.Divisors.zeroScheme _
        (lineInfinityModule ((strictTransformComplAtInfinity iZ.ker).ι ≫
          blowupAtInfinityToLine iZ.ker))
        (lineInfinityModuleSection ((strictTransformComplAtInfinity iZ.ker).ι ≫
          blowupAtInfinityToLine iZ.ker))).subschemeι := by
  rw [normalConeIsoLineInfinityZeroScheme, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    ← normalConeIsoFibreAtInfinityCompl_hom_subschemeι, Iso.inv_hom_id_assoc, eqToIso.hom]
  exact subschemeι_eqToHom (zeroScheme_lineInfinityModule_strictTransformComplAtInfinity iZ)

/-- `C_ZX ⟶ W ∖ X' ⟶ W ⟶ X` is the structure morphism of the normal cone. -/
@[reassoc]
theorem normalConeToStrictTransformComplAtInfinity_toBase :
    normalConeToStrictTransformComplAtInfinity iZ ≫ (strictTransformComplAtInfinity iZ.ker).ι ≫
        blowupAtInfinityToBase iZ.ker = normalConeToX iZ := by
  rw [normalConeToStrictTransformComplAtInfinity_ι_assoc]
  exact normalConeToExceptionalDivisor_comp_toBase iZ

/-- `C_ZX ⟶ C_YX ⟶ X ⟶ S` is `C_ZX ⟶ W_Z ∖ X'_Z ⟶ W_Z ⟶ X ⟶ S`. -/
private theorem normalConeChangeOfCentreMap_comp_toX_comp_eq {Y S : Scheme.{u}} (sX : X ⟶ S)
    (iY : Y ⟶ X) [IsClosedImmersion iY] (h : iY.ker ≤ iZ.ker) :
    normalConeChangeOfCentreMap iZ iY h ≫ normalConeToX iY ≫ sX =
      normalConeToStrictTransformComplAtInfinity iZ ≫ (strictTransformComplAtInfinity iZ.ker).ι ≫
        blowupAtInfinityToBase iZ.ker ≫ sX := by
  rw [← Category.assoc, normalConeChangeOfCentreMap_toX,
    ← normalConeToStrictTransformComplAtInfinity_toBase iZ]
  simp only [Category.assoc]

end Fibres

section Intersection

variable {X Y Z : Scheme.{u}} (iY : Y ⟶ X) [IsClosedImmersion iY]
  [Stacks.Divisors.IsEffectiveCartierDivisor iY.ker] (iZ : Z ⟶ X) [IsClosedImmersion iZ]
  (h : iY.ker ≤ iZ.ker)

/-- The morphism `C_ZX ⟶ C_YX ⟶ W_Y` along which the residual divisor `𝒟_Y` is pulled back. -/
abbrev normalConeChangeOfCentreToBlowup :
    Stacks.Conormal.normalCone iZ ⟶ blowupAtInfinity iY.ker :=
  normalConeChangeOfCentreMap iZ iY h ≫ normalConeToBlowupAtInfinity iY

/-- The zero scheme `F` of `(C_ZX ⟶ W_Y)^* 1_{𝒟_Y}` on `C_ZX`. -/
abbrev normalConeResidualZeroScheme : (Stacks.Conormal.normalCone iZ).IdealSheafData :=
  Stacks.Divisors.zeroScheme _
    ((Scheme.Modules.pullback (normalConeChangeOfCentreToBlowup iY iZ h)).obj
      (Stacks.Divisors.divisorSheaf (residualIdealAtInfinity iY.ker iY.ker)))
    (AlgebraicGeometry.pullbackGlobalSections (normalConeChangeOfCentreToBlowup iY iZ h) _
      (Stacks.Divisors.divisorSheafGlobalSection (residualIdealAtInfinity iY.ker iY.ker)))

omit [Stacks.Divisors.IsEffectiveCartierDivisor iY.ker] in
/-- `C_ZX ⟶ C_YX ⟶ W_Y` is `C_ZX ⟶ W_Z ∖ X'_Z ⟶ W_Y`. -/
theorem normalConeChangeOfCentreToBlowup_eq :
    normalConeChangeOfCentreToBlowup iY iZ h =
      normalConeToStrictTransformComplAtInfinity iZ ≫ blowupAtInfinityChangeOfCentre h :=
  normalConeChangeOfCentreMap_comp_exceptionalDivisor iZ iY h

omit [IsClosedImmersion iY] in
/-- The zero scheme of the canonical section of `𝒪(𝒟_Y)` is `𝒟_Y`. -/
theorem zeroScheme_divisorSheaf_residualIdealAtInfinity_self :
    Stacks.Divisors.zeroScheme _
        (Stacks.Divisors.divisorSheaf (residualIdealAtInfinity iY.ker iY.ker))
        (Stacks.Divisors.divisorSheafGlobalSection (residualIdealAtInfinity iY.ker iY.ker)) =
      residualIdealAtInfinity iY.ker iY.ker :=
  Stacks.Divisors.zeroScheme_canonicalSection _

/-- `F` is the zero section of `C_YX` pulled back along `C_ZX ⟶ C_YX`. -/
theorem normalConeResidualZeroScheme_eq_comap_zeroSection :
    normalConeResidualZeroScheme iY iZ h =
      (normalConeZeroSectionIdeal iY).comap (normalConeChangeOfCentreMap iZ iY h) := by
  rw [normalConeResidualZeroScheme, Stacks.Divisors.zeroScheme_pullback,
    zeroScheme_divisorSheaf_residualIdealAtInfinity_self, normalConeChangeOfCentreToBlowup,
    Scheme.IdealSheafData.comap_comp, normalConeZeroSectionIdeal_eq_comap]

/-- `F` is the residual divisor `𝒟_Z` of `W_Z ∖ X'_Z` restricted to `C_ZX`. -/
theorem normalConeResidualZeroScheme_eq :
    normalConeResidualZeroScheme iY iZ h =
      ((residualIdealAtInfinity iY.ker iZ.ker).comap
        (strictTransformComplAtInfinity iZ.ker).ι).comap
          (normalConeToStrictTransformComplAtInfinity iZ) := by
  rw [normalConeResidualZeroScheme, Stacks.Divisors.zeroScheme_pullback,
    zeroScheme_divisorSheaf_residualIdealAtInfinity_self, normalConeChangeOfCentreToBlowup_eq,
    Scheme.IdealSheafData.comap_comp, comap_residualIdealAtInfinity_changeOfCentre h]

omit [IsClosedImmersion iY] [IsClosedImmersion iZ] in
/-- The fibre at infinity of the residual zero scheme `Z₂` is the fibre at infinity of `W_Z ∖ X'_Z`
restricted to `Z₂`. -/
theorem residualFibreAtInfinity_eq :
    residualFibreAtInfinity h =
      ((fibreIdealAtInfinity iZ.ker).comap (strictTransformComplAtInfinity iZ.ker).ι).comap
        (residualZeroSchemeAtInfinity h).subschemeι := by
  rw [residualFibreAtInfinity, zeroScheme_lineInfinityModuleSection,
    Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]
  rfl

/-- **The two presentations of `W_∞ ∩ Z₂`**: the zero scheme `F` of the residual section on
`C_ZX = W_∞ ∩ (W ∖ X')` and the fibre at infinity `D` of the residual zero scheme `Z₂` are the same
closed subscheme of `W_Z ∖ X'_Z`. -/
theorem exists_iso_normalConeResidualZeroScheme_residualFibreAtInfinity :
    ∃ w : (normalConeResidualZeroScheme iY iZ h).subscheme ≅ (residualFibreAtInfinity h).subscheme,
      w.hom ≫ (residualFibreAtInfinity h).subschemeι ≫ (residualZeroSchemeAtInfinity h).subschemeι =
        (normalConeResidualZeroScheme iY iZ h).subschemeι ≫
          normalConeToStrictTransformComplAtInfinity iZ := by
  set Fi := (fibreIdealAtInfinity iZ.ker).comap (strictTransformComplAtInfinity iZ.ker).ι
  set Dz := (residualIdealAtInfinity iY.ker iZ.ker).comap (strictTransformComplAtInfinity iZ.ker).ι
  obtain ⟨e₁, he₁⟩ := Stacks.ChernCap42.exists_iso_comap_sup Fi Dz
    (normalConeToStrictTransformComplAtInfinity iZ) (normalConeIsoFibreAtInfinityCompl iZ).symm
    (normalConeIsoFibreAtInfinityCompl_hom_subschemeι iZ)
  have hZ₂ := residualZeroSchemeAtInfinity_eq h
  obtain ⟨e₂, he₂⟩ := Stacks.ChernCap42.exists_iso_comap_sup Dz Fi
    (residualZeroSchemeAtInfinity h).subschemeι
    (eqToIso (congrArg Scheme.IdealSheafData.subscheme hZ₂.symm))
    (by rw [eqToIso.inv]; exact subschemeι_eqToHom hZ₂)
  have hF := normalConeResidualZeroScheme_eq iY iZ h
  have hD := residualFibreAtInfinity_eq iY iZ h
  refine ⟨eqToIso (congrArg Scheme.IdealSheafData.subscheme hF) ≪≫ e₁ ≪≫
    eqToIso (congrArg Scheme.IdealSheafData.subscheme (sup_comm Fi Dz)) ≪≫ e₂.symm ≪≫
    eqToIso (congrArg Scheme.IdealSheafData.subscheme hD.symm), ?_⟩
  simp only [Iso.trans_hom, eqToIso.hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc (eqToHom _) (residualFibreAtInfinity h).subschemeι,
    subschemeι_eqToHom hD.symm, ← he₂, Iso.inv_hom_id_assoc,
    subschemeι_eqToHom (sup_comm Fi Dz), he₁, ← Category.assoc, subschemeι_eqToHom hF]

/-- The identification `F ≅ D` of
`Stacks.Chow.exists_iso_normalConeResidualZeroScheme_residualFibreAtInfinity`. -/
def normalConeResidualZeroSchemeIso :
    (normalConeResidualZeroScheme iY iZ h).subscheme ≅ (residualFibreAtInfinity h).subscheme :=
  (exists_iso_normalConeResidualZeroScheme_residualFibreAtInfinity iY iZ h).choose

/-- `F ≅ D` is compatible with the inclusions into `W_Z ∖ X'_Z`. -/
@[reassoc]
theorem normalConeResidualZeroSchemeIso_hom_comp :
    (normalConeResidualZeroSchemeIso iY iZ h).hom ≫ (residualFibreAtInfinity h).subschemeι ≫
        (residualZeroSchemeAtInfinity h).subschemeι =
      (normalConeResidualZeroScheme iY iZ h).subschemeι ≫
        normalConeToStrictTransformComplAtInfinity iZ :=
  (exists_iso_normalConeResidualZeroScheme_residualFibreAtInfinity iY iZ h).choose_spec

omit [Stacks.Divisors.IsEffectiveCartierDivisor iY.ker] in
/-- `C_ZX ⟶ W_Y` lies over `C_ZX ⟶ W_Z ∖ X'_Z ⟶ W_Y`, read on the zero scheme of `1_{D_∞}`. -/
theorem normalConeIsoLineInfinityZeroScheme_hom_comp_changeOfCentreToBlowup :
    (normalConeIsoLineInfinityZeroScheme iZ).hom ≫ normalConeChangeOfCentreToBlowup iY iZ h =
      (Stacks.Divisors.zeroScheme _
        (lineInfinityModule ((strictTransformComplAtInfinity iZ.ker).ι ≫
          blowupAtInfinityToLine iZ.ker))
        (lineInfinityModuleSection ((strictTransformComplAtInfinity iZ.ker).ι ≫
          blowupAtInfinityToLine iZ.ker))).subschemeι ≫ blowupAtInfinityChangeOfCentre h := by
  rw [normalConeChangeOfCentreToBlowup_eq, normalConeIsoLineInfinityZeroScheme_hom_comp_assoc]

end Intersection

section Main

attribute [local instance] lineInfinityDivisor_isEffectiveCartierDivisor

variable (C : ChowSituation.{u}) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (iY : Y ⟶ X) [IsClosedImmersion iY] [Stacks.Divisors.IsEffectiveCartierDivisor iY.ker]
  (iZ : Z ⟶ X) [IsClosedImmersion iZ] (h : iY.ker ≤ iZ.ker)
  (iZY : Z ⟶ Y) [IsClosedImmersion iZY] (hZY : iZY.ker = iZ.ker.comap iY)

/-- `C_ZX ⟶ C_YX ⟶ S` is locally of finite type: it is the structure morphism of `C_ZX`. -/
instance locallyOfFiniteType_normalConeChangeOfCentreMap_comp :
    LocallyOfFiniteType (normalConeChangeOfCentreMap iZ iY h ≫ normalConeToX iY ≫ sX) := by
  rw [← Category.assoc, normalConeChangeOfCentreMap_toX]
  infer_instance

omit [IsClosedImmersion iZ] in
/-- **Stacks 02TB at infinity on `W_Z ∖ X'_Z`**:
`1_{D_∞}^*[W_Z ∖ X'_Z]_{k+2} = [W_∞ ∩ (W_Z ∖ X'_Z)]_{k+1}` when `dim_δ(X) ≤ k + 1`. -/
theorem gysinSystemOfInvertible_lineInfinityModule_strictTransformComplAtInfinity {k : ℤ}
    (hX : schemeDeltaDimension C sX ≤ ((k + 1 : ℤ) : EInt)) :
    (gysinSystemOfInvertible C).onChow
        ((strictTransformComplAtInfinity iZ.ker).ι ≫ blowupAtInfinityToBase iZ.ker ≫ sX)
        (lineInfinityModule ((strictTransformComplAtInfinity iZ.ker).ι ≫
          blowupAtInfinityToLine iZ.ker))
        (lineInfinityModuleSection ((strictTransformComplAtInfinity iZ.ker).ι ≫
          blowupAtInfinityToLine iZ.ker)) (k + 1)
        (fundamentalChowClass C
          ((strictTransformComplAtInfinity iZ.ker).ι ≫ blowupAtInfinityToBase iZ.ker ≫ sX)
          (k + 1 + 1)) =
      fundamentalChowClass C ((Stacks.Divisors.zeroScheme _
        (lineInfinityModule ((strictTransformComplAtInfinity iZ.ker).ι ≫
          blowupAtInfinityToLine iZ.ker))
        (lineInfinityModuleSection ((strictTransformComplAtInfinity iZ.ker).ι ≫
          blowupAtInfinityToLine iZ.ker))).subschemeι ≫
          (strictTransformComplAtInfinity iZ.ker).ι ≫ blowupAtInfinityToBase iZ.ker ≫ sX)
        (k + 1) := by
  rw [gysinSystemOfInvertible_onChow_eq_gysinChowOfInvertible]
  refine gysinChowOfInvertible_fundamentalChowClass C _ (k + 1) _ _
    (schemeDeltaDimension_strictTransformComplAtInfinity_le C sX iZ.ker hX) ?_
  rw [zeroScheme_lineInfinityModule_strictTransformComplAtInfinity]
  exact Stacks.Blowup.isEffectiveCartierDivisor_comap_of_isOpenImmersion _
    (isEffectiveCartierDivisor_fibreIdealAtInfinity iZ.ker) _

omit [LocallyOfFiniteType sX] in
/-- The comparison `F ≅ D` lies over the base. -/
theorem normalConeResidualZeroSchemeIso_hom_comp_toBase :
    (normalConeResidualZeroSchemeIso iY iZ h).hom ≫ ((residualFibreAtInfinity h).subschemeι ≫
        (residualZeroSchemeAtInfinity h).subschemeι ≫
          (strictTransformComplAtInfinity iZ.ker).ι ≫ blowupAtInfinityToBase iZ.ker ≫ sX) =
      (normalConeResidualZeroScheme iY iZ h).subschemeι ≫ normalConeChangeOfCentreMap iZ iY h ≫
        normalConeToX iY ≫ sX := by
  rw [normalConeResidualZeroSchemeIso_hom_comp_assoc,
    normalConeToStrictTransformComplAtInfinity_toBase_assoc]
  exact congrArg _ (normalConeChangeOfCentreMap_toX_assoc iZ iY h sX).symm

/-- **Stacks 0B73 on `W_Z ∖ X'_Z`, evaluated.** For `Y ⊆ X` an effective Cartier divisor,
`ℐ_Y ⊆ ℐ_Z` and `dim_δ(X) ≤ k + 1`: the Gysin map of `(C_ZX ⟶ W_Y)^* 1_{𝒟_Y}` on `[C_ZX]_{k+1}`,
carried to `D = W_∞ ∩ Z₂` by `F ≅ D`, is the pushforward of `[C_ZY]_k`. -/
theorem gysin_normalConeResidual_fundamentalChowClass {k : ℤ}
    (hX : schemeDeltaDimension C sX ≤ ((k + 1 : ℤ) : EInt)) :
    properChowPushforward C ((normalConeResidualZeroScheme iY iZ h).subschemeι ≫
        normalConeChangeOfCentreMap iZ iY h ≫ normalConeToX iY ≫ sX) _
        (normalConeResidualZeroSchemeIso iY iZ h).hom
        (normalConeResidualZeroSchemeIso_hom_comp_toBase C sX iY iZ h) k
        (properPushforwardDescends C _ _ _ _ _)
        ((gysinSystemOfInvertible C).onChow
          (normalConeChangeOfCentreMap iZ iY h ≫ normalConeToX iY ≫ sX)
          ((Scheme.Modules.pullback (normalConeChangeOfCentreToBlowup iY iZ h)).obj
            (Stacks.Divisors.divisorSheaf (residualIdealAtInfinity iY.ker iY.ker)))
          (AlgebraicGeometry.pullbackGlobalSections (normalConeChangeOfCentreToBlowup iY iZ h) _
            (Stacks.Divisors.divisorSheafGlobalSection (residualIdealAtInfinity iY.ker iY.ker))) k
          (fundamentalChowClass C
            (normalConeChangeOfCentreMap iZ iY h ≫ normalConeToX iY ≫ sX) (k + 1))) =
      properChowPushforward C (normalConeToX iZY ≫ iY ≫ sX) _
        (normalConeToResidualFibreAtInfinity iY h iZY hZY)
        (comp_toBase_of_comp_residualFibreAtInfinity_subschemeι C sX iY h iZY hZY _
          (normalConeToResidualFibreAtInfinity_subschemeι iY h iZY hZY)) k
        (properPushforwardDescends C _ _ _ _ _)
        (fundamentalChowClass C (normalConeToX iZY ≫ iY ≫ sX) k) := by
  have hu₁ : (normalConeIsoLineInfinityZeroScheme iZ).hom ≫
      normalConeChangeOfCentreMap iZ iY h ≫ normalConeToX iY ≫ sX =
      (Stacks.Divisors.zeroScheme _
        (lineInfinityModule ((strictTransformComplAtInfinity iZ.ker).ι ≫
          blowupAtInfinityToLine iZ.ker))
        (lineInfinityModuleSection ((strictTransformComplAtInfinity iZ.ker).ι ≫
          blowupAtInfinityToLine iZ.ker))).subschemeι ≫
        (strictTransformComplAtInfinity iZ.ker).ι ≫ blowupAtInfinityToBase iZ.ker ≫ sX := by
    rw [normalConeChangeOfCentreMap_comp_toX_comp_eq iZ sX iY h,
      ← normalConeIsoLineInfinityZeroScheme_hom_comp_assoc]
  have h73 := gysinSystemOfInvertible_comm_properPushforward C
    (pV := (strictTransformComplAtInfinity iZ.ker).ι ≫ blowupAtInfinityToBase iZ.ker ≫ sX)
    (pY₁ := normalConeChangeOfCentreMap iZ iY h ≫ normalConeToX iY ≫ sX)
    (pY₂ := (residualZeroSchemeAtInfinity h).subschemeι ≫
      (strictTransformComplAtInfinity iZ.ker).ι ≫ blowupAtInfinityToBase iZ.ker ≫ sX)
    (q₁ := (strictTransformComplAtInfinity iZ.ker).ι ≫ blowupAtInfinityToLine iZ.ker)
    (q₂ := blowupAtInfinityChangeOfCentre h)
    (K₁ := Stacks.Divisors.divisorSheaf (lineInfinityDivisor X))
    (K₂ := Stacks.Divisors.divisorSheaf (residualIdealAtInfinity iY.ker iY.ker))
    (t₁ := Stacks.Divisors.divisorSheafGlobalSection (lineInfinityDivisor X))
    (t₂ := Stacks.Divisors.divisorSheafGlobalSection (residualIdealAtInfinity iY.ker iY.ker))
    (u₁ := (normalConeIsoLineInfinityZeroScheme iZ).hom) (hu₁ := hu₁)
    (r₂ := normalConeChangeOfCentreToBlowup iY iZ h)
    (hr₂ := normalConeIsoLineInfinityZeroScheme_hom_comp_changeOfCentreToBlowup iY iZ h)
    (y₁ := normalConeToStrictTransformComplAtInfinity iZ)
    (hy₁ := normalConeIsoLineInfinityZeroScheme_hom_comp iZ)
    (u₂ := 𝟙 _) (hu₂ := Category.id_comp _) (r₁ := residualZeroSchemeToLine h)
    (hr₁ := Category.id_comp _) (y₂ := (residualZeroSchemeAtInfinity h).subschemeι)
    (hy₂ := Category.id_comp _) (w := (normalConeResidualZeroSchemeIso iY iZ h).hom)
    (hw := normalConeResidualZeroSchemeIso_hom_comp_toBase C sX iY iZ h)
    (hwy := normalConeResidualZeroSchemeIso_hom_comp iY iZ h) (k := k)
    (x := fundamentalChowClass C
      ((strictTransformComplAtInfinity iZ.ker).ι ≫ blowupAtInfinityToBase iZ.ker ≫ sX)
      (k + 1 + 1))
  have hA := gysinSystemOfInvertible_lineInfinityModule_strictTransformComplAtInfinity C sX iZ hX
  have hB : properChowPushforward C _ (normalConeChangeOfCentreMap iZ iY h ≫ normalConeToX iY ≫ sX)
      (normalConeIsoLineInfinityZeroScheme iZ).hom hu₁ (k + 1)
      (properPushforwardDescends C _ _ _ _ _) (fundamentalChowClass C _ (k + 1)) =
      fundamentalChowClass C (normalConeChangeOfCentreMap iZ iY h ≫ normalConeToX iY ≫ sX)
        (k + 1) := by
    rw [properChowPushforward_eq_chowPushforwardOfIso]
    exact chowPushforwardOfIso_fundamentalChowClass C _ _ _ hu₁ (k + 1)
  simp only [hA, hB] at h73
  refine h73.trans ?_
  rw [properChowPushforward_id,
    gysinSystemOfInvertible_residualModuleAtInfinity_fundamentalChowClass C sX h hX]
  exact gysinSystemOfInvertible_lineInfinityModule_residualZeroScheme_eq_normalCone C sX iY h iZY
    hZY hX (normalConeToResidualFibreAtInfinity iY h iZY hZY)
    (normalConeToResidualFibreAtInfinity_subschemeι iY h iZY hZY)

/-- The closed immersion `C_ZY ⟶ F` of the normal cone of `Z ⊆ Y` into the zero scheme `F` of the
residual section on `C_ZX`: `C_ZY ⟶ D = W_∞ ∩ Z₂` followed by `D ≅ F`. -/
def normalConeToNormalConeResidualZeroScheme :
    Stacks.Conormal.normalCone iZY ⟶ (normalConeResidualZeroScheme iY iZ h).subscheme :=
  normalConeToResidualFibreAtInfinity iY h iZY hZY ≫ (normalConeResidualZeroSchemeIso iY iZ h).inv

/-- `C_ZY ⟶ F` is a closed immersion. -/
instance : IsClosedImmersion (normalConeToNormalConeResidualZeroScheme iY iZ h iZY hZY) := by
  rw [normalConeToNormalConeResidualZeroScheme]
  infer_instance

/-- `C_ZY ⟶ F ⟶ C_ZX ⟶ W_Z ∖ X'_Z` is `C_ZY ⟶ W_{Z∩Y} ∖ X'' ⟶ Z₂ ⟶ W_Z ∖ X'_Z`. -/
@[reassoc]
theorem normalConeToNormalConeResidualZeroScheme_comp :
    normalConeToNormalConeResidualZeroScheme iY iZ h iZY hZY ≫
        (normalConeResidualZeroScheme iY iZ h).subschemeι ≫
          normalConeToStrictTransformComplAtInfinity iZ =
      normalConeToStrictTransformComplAtInfinity iZY ≫
        strictTransformToResidualZeroScheme iY h iZY.ker hZY ≫
          (residualZeroSchemeAtInfinity h).subschemeι := by
  rw [normalConeToNormalConeResidualZeroScheme, Category.assoc,
    ← normalConeResidualZeroSchemeIso_hom_comp, Iso.inv_hom_id_assoc,
    reassoc_of% normalConeToResidualFibreAtInfinity_subschemeι]

omit [LocallyOfFiniteType sX] in
/-- `C_ZY ⟶ F` lies over the base. -/
theorem normalConeToNormalConeResidualZeroScheme_toBase :
    normalConeToNormalConeResidualZeroScheme iY iZ h iZY hZY ≫
        (normalConeResidualZeroScheme iY iZ h).subschemeι ≫
          normalConeChangeOfCentreMap iZ iY h ≫ normalConeToX iY ≫ sX =
      normalConeToX iZY ≫ iY ≫ sX := by
  rw [normalConeChangeOfCentreMap_comp_toX_comp_eq iZ sX iY h,
    normalConeToNormalConeResidualZeroScheme_comp_assoc,
    ← normalConeToResidualFibreAtInfinity_subschemeι_assoc]
  exact comp_toBase_of_comp_residualFibreAtInfinity_subschemeι C sX iY h iZY hZY _
    (normalConeToResidualFibreAtInfinity_subschemeι iY h iZY hZY)

/-- **Stacks 0B73 on `W_Z ∖ X'_Z`, on `F`.** The Gysin map of the residual section on
`[C_ZX]_{k+1}` is the pushforward of `[C_ZY]_k` into its zero scheme `F`. -/
theorem gysin_normalConeResidual_fundamentalChowClass_eq {k : ℤ}
    (hX : schemeDeltaDimension C sX ≤ ((k + 1 : ℤ) : EInt)) :
    (gysinSystemOfInvertible C).onChow
        (normalConeChangeOfCentreMap iZ iY h ≫ normalConeToX iY ≫ sX)
        ((Scheme.Modules.pullback (normalConeChangeOfCentreToBlowup iY iZ h)).obj
          (Stacks.Divisors.divisorSheaf (residualIdealAtInfinity iY.ker iY.ker)))
        (AlgebraicGeometry.pullbackGlobalSections (normalConeChangeOfCentreToBlowup iY iZ h) _
          (Stacks.Divisors.divisorSheafGlobalSection (residualIdealAtInfinity iY.ker iY.ker))) k
        (fundamentalChowClass C
          (normalConeChangeOfCentreMap iZ iY h ≫ normalConeToX iY ≫ sX) (k + 1)) =
      properChowPushforward C (normalConeToX iZY ≫ iY ≫ sX) _
        (normalConeToNormalConeResidualZeroScheme iY iZ h iZY hZY)
        (normalConeToNormalConeResidualZeroScheme_toBase C sX iY iZ h iZY hZY) k
        (properPushforwardDescends C _ _ _ _ _)
        (fundamentalChowClass C (normalConeToX iZY ≫ iY ≫ sX) k) := by
  set w := normalConeResidualZeroSchemeIso iY iZ h
  have hw := normalConeResidualZeroSchemeIso_hom_comp_toBase C sX iY iZ h
  have hwinv : w.inv ≫ ((normalConeResidualZeroScheme iY iZ h).subschemeι ≫
      normalConeChangeOfCentreMap iZ iY h ≫ normalConeToX iY ≫ sX) =
      (residualFibreAtInfinity h).subschemeι ≫ (residualZeroSchemeAtInfinity h).subschemeι ≫
        (strictTransformComplAtInfinity iZ.ker).ι ≫ blowupAtInfinityToBase iZ.ker ≫ sX := by
    rw [← hw, Iso.inv_hom_id_assoc]
  have key := congrArg (properChowPushforward C _ _ w.inv hwinv k
    (properPushforwardDescends C _ _ _ _ _))
    (gysin_normalConeResidual_fundamentalChowClass C sX iY iZ h iZY hZY hX)
  rwa [← properChowPushforward_comp_apply C _ _ _ w.hom w.inv (𝟙 _) w.hom_inv_id hw hwinv
      (Category.id_comp _) k _ _ (properPushforwardDescends C _ _ _ _ _),
    properChowPushforward_id,
    ← properChowPushforward_comp_apply C _ _ _ (normalConeToResidualFibreAtInfinity iY h iZY hZY)
      w.inv _ rfl _ hwinv _ k _ _ (properPushforwardDescends C _ _ _ _ _)] at key

/-- The zero scheme of the residual section on `C_ZX` is the base change of the zero section
`D0 = o(Y) ⊆ C_YX` along `C_ZX ⟶ C_YX`, presented as the `gysinTripleDivisor` of Stacks 0B6Y. -/
theorem normalConeResidualZeroScheme_eq_gysinTripleDivisor :
    normalConeResidualZeroScheme iY iZ h =
      gysinTripleDivisor (Stacks.Divisors.divisorSheaf (normalConeZeroSectionIdeal iY))
        (Stacks.Divisors.divisorSheafGlobalSection (normalConeZeroSectionIdeal iY))
        (normalConeChangeOfCentreMap iZ iY h) := by
  have h1 : Stacks.Divisors.zeroScheme _
      (Stacks.Divisors.divisorSheaf (normalConeZeroSectionIdeal iY))
      (Stacks.Divisors.divisorSheafGlobalSection (normalConeZeroSectionIdeal iY)) =
        normalConeZeroSectionIdeal iY :=
    Stacks.Divisors.zeroScheme_canonicalSection _
  rw [normalConeResidualZeroScheme_eq_comap_zeroSection, gysinTripleDivisor,
    Stacks.Divisors.zeroScheme_pullback, h1]

/-- **The closed immersion `C_ZY ⟶ Y ×_{o, C_YX} C_ZX`**, read through the zero scheme
`o(Y) = D0` of the canonical section of the zero section and the identification of Stacks 0B6Y. -/
def normalConeToZeroSectionPullback :
    Stacks.Conormal.normalCone iZY ⟶
      pullback (gysinTripleInclusion (Stacks.Divisors.divisorSheaf (normalConeZeroSectionIdeal iY))
        (Stacks.Divisors.divisorSheafGlobalSection (normalConeZeroSectionIdeal iY)))
        (normalConeChangeOfCentreMap iZ iY h) :=
  normalConeToNormalConeResidualZeroScheme iY iZ h iZY hZY ≫
    eqToHom (congrArg Scheme.IdealSheafData.subscheme
      (normalConeResidualZeroScheme_eq_gysinTripleDivisor iY iZ h)) ≫
    (gysinDivisorBaseChangeIso _ _ (normalConeChangeOfCentreMap iZ iY h)).hom

/-- `C_ZY ⟶ Y ×_{o, C_YX} C_ZX` is a closed immersion. -/
instance : IsClosedImmersion (normalConeToZeroSectionPullback iY iZ h iZY hZY) := by
  rw [normalConeToZeroSectionPullback]
  infer_instance

omit [LocallyOfFiniteType sX] in
/-- `C_ZY ⟶ Y ×_{o, C_YX} C_ZX` lies over the base. -/
theorem normalConeToZeroSectionPullback_toBase :
    normalConeToZeroSectionPullback iY iZ h iZY hZY ≫
        (pullback.fst (gysinTripleInclusion
          (Stacks.Divisors.divisorSheaf (normalConeZeroSectionIdeal iY))
          (Stacks.Divisors.divisorSheafGlobalSection (normalConeZeroSectionIdeal iY)))
          (normalConeChangeOfCentreMap iZ iY h) ≫
        (gysinTripleInclusion (Stacks.Divisors.divisorSheaf (normalConeZeroSectionIdeal iY))
          (Stacks.Divisors.divisorSheafGlobalSection (normalConeZeroSectionIdeal iY)) ≫
            normalConeToX iY ≫ sX)) =
      normalConeToX iZY ≫ iY ≫ sX := by
  rw [normalConeToZeroSectionPullback, Category.assoc, Category.assoc,
    gysinDivisorBaseChangeIso_hom_comp_structureMorphism, ← Category.assoc (eqToHom _),
    subschemeι_eqToHom (normalConeResidualZeroScheme_eq_gysinTripleDivisor iY iZ h)]
  exact normalConeToNormalConeResidualZeroScheme_toBase C sX iY iZ h iZY hZY

/-- **Stacks 0FEB, with the inclusions as data**: `o^*[C_ZX]_n = [C_ZY]_{n-1}` for `ℐ_Y ⊆ ℐ_Z`,
`ℐ_{Z ⊆ Y} = ℐ_Z · 𝒪_Y` and `dim_δ(X) ≤ n`. -/
theorem gysinBivariantClass_cap_normalCone_eq {n : ℤ}
    (hX : schemeDeltaDimension C sX ≤ (n : EInt)) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian sX
    (gysinBivariantClass C (normalConeToX iY ≫ sX)
        (Stacks.Divisors.divisorSheaf (normalConeZeroSectionIdeal iY))
        (Stacks.Divisors.divisorSheafGlobalSection (normalConeZeroSectionIdeal iY))).1.cap
        (normalConeChangeOfCentreMap iZ iY h) n
        (fundamentalChowClass C (normalConeChangeOfCentreMap iZ iY h ≫ normalConeToX iY ≫ sX) n) =
      properChowPushforward C (normalConeToX iZY ≫ iY ≫ sX) _
        (normalConeToZeroSectionPullback iY iZ h iZY hZY)
        (normalConeToZeroSectionPullback_toBase C sX iY iZ h iZY hZY) (n - 1)
        (properPushforwardDescends C _ _ _ _ _)
        (fundamentalChowClass C (normalConeToX iZY ≫ iY ≫ sX) (n - 1)) := by
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  have hX' : schemeDeltaDimension C sX ≤ ((n - 1 + 1 : ℤ) : EInt) := by rwa [sub_add_cancel]
  set φ := normalConeChangeOfCentreMap iZ iY h
  set L := Stacks.Divisors.divisorSheaf (normalConeZeroSectionIdeal iY)
  set σ := Stacks.Divisors.divisorSheafGlobalSection (normalConeZeroSectionIdeal iY)
  have hD := normalConeResidualZeroScheme_eq_gysinTripleDivisor iY iZ h
  let e : (Scheme.Modules.pullback (normalConeChangeOfCentreToBlowup iY iZ h)).obj
      (Stacks.Divisors.divisorSheaf (residualIdealAtInfinity iY.ker iY.ker)) ≅
      gysinTripleModule L φ :=
    ((Scheme.Modules.pullbackComp φ (normalConeToBlowupAtInfinity iY)).app _).symm ≪≫
      (Scheme.Modules.pullback φ).mapIso (normalConeZeroSectionDivisorSheafIso iY)
  have hG : (gysinSystemOfInvertible C).onChow (φ ≫ normalConeToX iY ≫ sX)
      ((Scheme.Modules.pullback (normalConeChangeOfCentreToBlowup iY iZ h)).obj
        (Stacks.Divisors.divisorSheaf (residualIdealAtInfinity iY.ker iY.ker)))
      (AlgebraicGeometry.pullbackGlobalSections (normalConeChangeOfCentreToBlowup iY iZ h) _
        (Stacks.Divisors.divisorSheafGlobalSection (residualIdealAtInfinity iY.ker iY.ker)))
      (n - 1) ≍ (gysinSystemOfInvertible C).onChow (φ ≫ normalConeToX iY ≫ sX)
        (gysinTripleModule L φ) (gysinTripleSection L σ φ) (n - 1) :=
    heq_gysinHomomorphismOnChowOfInvertible C (φ ≫ normalConeToX iY ≫ sX) (n - 1) _ _
      _ _ e hD (gysinOfInvertibleDescends C _ _ _ _) (gysinOfInvertibleDescends C _ _ _ _)
  have hT := chowPushforwardOfIso_eqToHom_apply_of_heq C (φ ≫ normalConeToX iY ≫ sX) (n - 1) hD
    _ _ hG (fundamentalChowClass C (φ ≫ normalConeToX iY ≫ sX) (n - 1 + 1))
  rw [(gysinBivariantClass C (normalConeToX iY ≫ sX) L σ).2, gysinBivariantCap_apply,
    chowGroupDegreeEquiv_fundamentalChowClass, ← hT,
    gysin_normalConeResidual_fundamentalChowClass_eq C sX iY iZ h iZY hZY hX',
    ← properChowPushforward_eq_chowPushforwardOfIso C _ _ (eqToHom _) _ (n - 1)
      (properPushforwardDescends C _ _ _ _ _),
    ← properChowPushforward_eq_chowPushforwardOfIso C _ _ (gysinDivisorBaseChangeIso L σ φ).hom _
      (n - 1) (properPushforwardDescends C _ _ _ _ _),
    ← properChowPushforward_comp_apply C _ _ _
      (normalConeToNormalConeResidualZeroScheme iY iZ h iZY hZY) (eqToHom _) _ rfl _ _ (by
        rw [Category.assoc, ← Category.assoc (eqToHom _), subschemeι_eqToHom hD]
        exact normalConeToNormalConeResidualZeroScheme_toBase C sX iY iZ h iZY hZY) (n - 1) _ _
      (properPushforwardDescends C _ _ _ _ _),
    ← properChowPushforward_comp_apply C _ _ _ _ (gysinDivisorBaseChangeIso L σ φ).hom
      (normalConeToZeroSectionPullback iY iZ h iZY hZY)
      (by rw [normalConeToZeroSectionPullback, Category.assoc]) _ _ _ (n - 1) _ _
      (properPushforwardDescends C _ _ _ _ _)]

omit [LocallyOfFiniteType sX] in
/-- **`C_ZY ⟶ Y ×_{o, C_YX} C_ZX` is the canonical map**: its second component is the comparison
`C_ZY ⟶ C_ZX` of the normal cones of `Z ⊆ Y` and `Z ⊆ X` (`Stacks.Chow.normalConeBaseChangeMap`,
the morphism of normal cones of Stacks 0634 for `Y ⟶ X`). Its first component is then forced:
`Y ×_{o, C_YX} C_ZX ⟶ C_ZX` is a monomorphism. -/
theorem normalConeToZeroSectionPullback_snd :
    normalConeToZeroSectionPullback iY iZ h iZY hZY ≫ pullback.snd _ _ =
      normalConeBaseChangeMap iY sX iZ iZY hZY := by
  rw [← cancel_mono (normalConeToStrictTransformComplAtInfinity iZ),
    ← cancel_mono (strictTransformComplAtInfinity iZ.ker).ι]
  simp only [normalConeToZeroSectionPullback, Category.assoc, gysinDivisorBaseChangeIso_hom_snd]
  rw [← Category.assoc (eqToHom _),
    subschemeι_eqToHom (normalConeResidualZeroScheme_eq_gysinTripleDivisor iY iZ h),
    normalConeToNormalConeResidualZeroScheme_comp_assoc,
    strictTransformToResidualZeroScheme_subschemeι_assoc, strictTransformComplAtInfinityComap_ι,
    normalConeToStrictTransformComplAtInfinity_ι_eq iZ sX,
    normalConeBaseChangeMap_comp_assoc, blowupAtInfinityFibreComap_inclusion,
    ← Category.assoc, normalConeToStrictTransformComplAtInfinity_ι_eq iZY (iY ≫ sX),
    Category.assoc]

end Main

section Source

/-- A morphism followed by a monomorphism is the base change of the composite along it. -/
private theorem isPullback_id_of_comp_eq {C : Type*} [Category C] {Z Y X : C} (f : Z ⟶ Y)
    (g : Y ⟶ X) [Mono g] (k : Z ⟶ X) (hk : f ≫ g = k) : IsPullback f (𝟙 Z) g k := by
  subst hk
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => s.snd) (fun s => ?_) (fun s => by simp)
    (fun s m _ hm => by simpa using hm)⟩⟩
  rw [← cancel_mono g, Category.assoc]
  exact s.condition.symm

/-- For closed immersions `Z ⟶ Y ⟶ X`, the ideal of `Z` in `Y` is the inverse image of the ideal
of `Z` in `X`. -/
theorem ker_eq_comap_ker_of_comp_eq {X Y Z : Scheme.{u}} (iY : Y ⟶ X) [IsClosedImmersion iY]
    (iZ : Z ⟶ X) [IsClosedImmersion iZ] (iZY : Z ⟶ Y) (hZY : iZY ≫ iY = iZ) :
    iZY.ker = iZ.ker.comap iY :=
  ker_eq_comap_ker_of_isPullback (isPullback_id_of_comp_eq iZY iY iZ hZY)

end Source

section Tag

variable (C : ChowSituation.{u}) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (iY : Y ⟶ X) [IsClosedImmersion iY] [Stacks.Divisors.IsEffectiveCartierDivisor iY.ker]
  (iZ : Z ⟶ X) [IsClosedImmersion iZ] (iZY : Z ⟶ Y) [IsClosedImmersion iZY]

/-- **Stacks 0FEB.** Let `(S, δ)` be as in Situation 02QL, let `X` be a scheme locally of finite
type over `S` with `dim_δ(X) ≤ n` (the source: `X` integral of `δ`-dimension `n`), and let
`Z ⊆ Y ⊆ X` be closed subschemes, `iZY : Z ⟶ Y` the inclusion, with `Y` an effective Cartier
divisor in `X` (the source also asks it of `Z`; that is not used). Let `o : Y ⟶ C_YX` be the zero
section of the normal line cone, `o(Y) = D0 = normalConeZeroSectionIdeal iY`
(`Stacks.Chow.ker_normalConeZeroSection`), an effective Cartier divisor of `C_YX`
(`Stacks.Chow.isEffectiveCartierDivisor_normalConeZeroSectionIdeal`), and let
`o^* ∈ A^1(Y ⟶ C_YX)` be its Gysin class (Stacks 0B79, `Stacks.Chow.gysinBivariantClass`, for the
canonical section of `𝒪(D0)`). Let `φ : C_ZX ⟶ C_YX` be the canonical morphism of normal cones
induced by `ℐ_Y ⊆ ℐ_Z` (`Stacks.Chow.normalConeChangeOfCentreMap`; on charts it is
`Spec Gr_{ℐ_Z} ⟶ Spec Gr_{ℐ_Y}`). Then

  `o^*[C_ZX]_n = [C_ZY]_{n-1}`  in  `CH_{n-1}(Y ×_{o, C_YX} C_ZX)`,

where the fibre product is the base change of `o(Y) ⊆ C_YX` along `φ` (Stacks 0B6Y) and
`[C_ZY]_{n-1}` is pushed forward along the closed immersion
`Stacks.Chow.normalConeToZeroSectionPullback`, whose component to `C_ZX` is the comparison
`C_ZY ⟶ C_ZX` of normal cones (`Stacks.Chow.normalConeToZeroSectionPullback_snd`). -/
@[stacks 0FEB]
theorem gysinBivariantClass_cap_normalCone {n : ℤ} (hZY : iZY ≫ iY = iZ)
    (hX : schemeDeltaDimension C sX ≤ (n : EInt)) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian sX
    (gysinBivariantClass C (normalConeToX iY ≫ sX)
        (Stacks.Divisors.divisorSheaf (normalConeZeroSectionIdeal iY))
        (Stacks.Divisors.divisorSheafGlobalSection (normalConeZeroSectionIdeal iY))).1.cap
        (normalConeChangeOfCentreMap iZ iY (hZY ▸ Scheme.Hom.le_ker_comp iZY iY)) n
        (fundamentalChowClass C (normalConeChangeOfCentreMap iZ iY
          (hZY ▸ Scheme.Hom.le_ker_comp iZY iY) ≫ normalConeToX iY ≫ sX) n) =
      properChowPushforward C (normalConeToX iZY ≫ iY ≫ sX) _
        (normalConeToZeroSectionPullback iY iZ (hZY ▸ Scheme.Hom.le_ker_comp iZY iY) iZY
          (ker_eq_comap_ker_of_comp_eq iY iZ iZY hZY))
        (normalConeToZeroSectionPullback_toBase C sX iY iZ _ iZY _) (n - 1)
        (properPushforwardDescends C _ _ _ _ _)
        (fundamentalChowClass C (normalConeToX iZY ≫ iY ≫ sX) (n - 1)) :=
  gysinBivariantClass_cap_normalCone_eq C sX iY iZ _ iZY _ hX

end Tag

end Stacks.Chow

end
