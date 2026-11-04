module

public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.FunctionFieldDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicCascade.GenericValue

/-!
# The generic value of the meromorphic section attached to a rational function

Let `X` be an integral scheme and `g` a nonzero rational function on `X`. The meromorphic
section `AlgebraicGeometry.meromorphicSectionOfFunctionField` of `𝒪_X` attached to `g` has
generic value `g`: under the identification
`Stacks.Ample.unitStalkEquiv` of the stalk of `𝒪_X` as a module over itself with the local ring,
the element of the generic stalk corresponding to that section is `g`.

Together with
`AlgebraicGeometry.orderOfVanishingMeromorphic_unitModule_eq_ord` this makes the order of
vanishing of the section along every prime divisor `Z` equal to `ord_ξ(g)`, and so makes the
coefficient identity

`m_{𝒪_X/gI}(ξ) − m_{𝒪_X/I}(ξ) = ord_ξ(g)`

of the proof of Stacks 0FDS unconditional at every prime divisor.

## Main results

* `Stacks.Divisors.bijective_toMeromorphicSectionStalk_genericPoint` — the canonical map
  `F_η → 𝒦_X(F)_η` is bijective: the regular germs at the generic point are units.
* `Stacks.Divisors.genericValue_eq_of_toMeromorphicSectionStalk_eq` — hence the generic value is
  determined by its image, which is the germ of the section at the generic point.
* `AlgebraicGeometry.toMeromorphicSectionSheafAsModule_eq` — the canonical map
  `𝒪_X ⟶ 𝒦_X(𝒪_X)` is the canonical map `𝒪_X ⟶ K_X` followed by the identification
  `K_X ≅ 𝒦_X(𝒪_X)`.
* `AlgebraicGeometry.genericValue_meromorphicSectionOfFunctionField` — **the generic value is
  `g`.**
* `AlgebraicGeometry.orderOfVanishingMeromorphic_meromorphicSectionOfFunctionField` — the order
  of vanishing along a prime divisor is the order of vanishing of `g` at its generic point.
* `AlgebraicGeometry.sheafMultiplicity_denominator_sub_eq_orderOfVanishing` — the coefficient
  identity at a prime divisor, with no hypothesis beyond integrality and local Noetherianness.

## Implementation notes

The generic value is characterised by `Stacks.Divisors.toMeromorphicSectionStalk_genericValue`
together with the injectivity of `Stacks.Divisors.toMeromorphicSectionStalk` at the generic
point; the bijectivity there is already used inside the proof of
`Stacks.Divisors.bijective_stalkSpecializes_meromorphicSectionSheaf` but was not stated
separately, so it is extracted here. The module structures on the two stalks have to be supplied
by `Stacks.ModuleStalk.moduleStalk` and
`Stacks.Divisors.moduleStalkMeromorphicSectionSheaf`: instance search finds the first only when
the indexing presheaf of rings appears literally as `O ⋙ forget₂ CommRingCat RingCat`.

The computation then runs on one open neighbourhood `W` of the generic point on which `g` is the
germ of a section `t` of `𝒪_X`. The canonical map `𝒪_X ⟶ 𝒦_X(𝒪_X)` factors as the ring map
`𝒪_X ⟶ K_X` followed by `K_X ≅ 𝒦_X(𝒪_X)`, which is
`AlgebraicGeometry.unit_comp_meromorphicUnitToUnit` rearranged, so the stalk map sends the germ
of `t` to the germ of the image of `t` in `K_X`; and the germ of the section at the top open set
restricts to the same thing, the comparison out of the constant presheaf on the function field
having identity restriction maps.

`Stacks.ModuleStalk.stalkMap_comp` is deliberately **not** used: it quantifies over a third
module and the instance for the middle term — the restriction of scalars of `K_X` as a module
over itself — is not synthesizable. A single `Stacks.ModuleStalk.stalkMap_germ` applied to the
composite avoids it, the value of a composite on a section being the iterated application. For
the same reason nothing here is proved by `rw` on a goal mentioning both spellings of the
structure sheaf: those goals report as not type-correct at `implicit` transparency, and every
such step is an explicit `Eq.trans` of `congrArg`s instead.

## References

* [Stacks Project, Tag 01X5](https://stacks.math.columbia.edu/tag/01X5)
* [Stacks Project, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF)
* [Stacks Project, Tag 0FDS](https://stacks.math.columbia.edu/tag/0FDS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Ample (unitModule unitStalkEquiv)
open Stacks.ModuleStalk (germ stalkMap presheafOn moduleStalk)
open Stacks.Divisors (toMeromorphicSectionStalk genericValue
  isLocalizedModule_toMeromorphicSectionStalk regularGerms regularGerms_genericPoint_le_isUnit
  moduleStalkMeromorphicSectionSheaf toMeromorphicSectionStalk_genericValue)

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} [IsIntegral X] (F : X.Modules) [F.IsQuasicoherent]

omit [SheafOfModules.IsQuasicoherent F] in
/-- **The canonical map `F_η → 𝒦_X(F)_η` is bijective.** The stalk of `𝒦_X(F)` at the generic
point is the localization of `F_η` at the regular germs there, and on an integral scheme those
are units of the function field. -/
theorem bijective_toMeromorphicSectionStalk_genericPoint :
    Function.Bijective (toMeromorphicSectionStalk X.sheaf F (genericPoint X)) :=
  let _mFg : Module (X.sheaf.presheaf.stalk (genericPoint X))
      ((presheafOn F.val).stalk (genericPoint X)) := moduleStalk F.val (genericPoint X)
  let _mKg : Module (X.sheaf.presheaf.stalk (genericPoint X))
      ((presheafOn (meromorphicSectionSheaf X.sheaf F).val).stalk (genericPoint X)) :=
    moduleStalkMeromorphicSectionSheaf X.sheaf F (genericPoint X)
  have := isLocalizedModule_toMeromorphicSectionStalk X.sheaf F (genericPoint X)
  Stacks.Localization.bijective_of_isLocalizedModule_of_isUnit
    (S := regularGerms X.sheaf (genericPoint X)) _
    fun _ hs => regularGerms_genericPoint_le_isUnit hs

/-- **The generic value is determined by the germ of the section at the generic point.** An
element of the generic stalk whose image under the canonical map is that germ is the generic
value. -/
theorem genericValue_eq_of_toMeromorphicSectionStalk_eq
    (s : AlgebraicGeometry.MeromorphicSection X.sheaf F)
    (v : (presheafOn F.val).stalk (genericPoint X))
    (h : toMeromorphicSectionStalk X.sheaf F (genericPoint X) v =
      germ (meromorphicSectionSheaf X.sheaf F).val ⊤ (genericPoint X) trivial (s.val (op ⊤))) :
    genericValue F s = v :=
  (bijective_toMeromorphicSectionStalk_genericPoint F).injective
    ((toMeromorphicSectionStalk_genericValue F s).trans h.symm)

end Stacks.Divisors

namespace AlgebraicGeometry

variable (X : Scheme.{u}) [IsIntegral X] (g : X.functionFieldˣ)

omit [IsIntegral X] in
/-- **The canonical map `𝒪_X ⟶ 𝒦_X(𝒪_X)` factors through `K_X`**: it is the canonical map
`𝒪_X ⟶ K_X` followed by the identification `K_X ≅ 𝒦_X(𝒪_X)`. This is
`AlgebraicGeometry.unit_comp_meromorphicUnitToUnit` with the identification moved to the other
side. -/
theorem toMeromorphicSectionSheafAsModule_eq :
    toMeromorphicSectionSheafAsModule X (unitModule X) =
      toKUnit X ≫ (SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).map
        (unitIsoMeromorphicSectionSheafUnit X).hom :=
  ((((Category.comp_id _).symm.trans
    (congrArg (fun q => toMeromorphicSectionSheafAsModule X (unitModule X) ≫ q)
      ((SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).map_id _).symm)).trans
    (congrArg (fun q => toMeromorphicSectionSheafAsModule X (unitModule X) ≫
        (SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).map q)
      (unitIsoMeromorphicSectionSheafUnit X).inv_hom_id.symm)).trans
    (congrArg (fun q => toMeromorphicSectionSheafAsModule X (unitModule X) ≫ q)
      ((SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).map_comp
        (unitIsoMeromorphicSectionSheafUnit X).inv
        (unitIsoMeromorphicSectionSheafUnit X).hom))).trans
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun q => q ≫ (SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).map
        (unitIsoMeromorphicSectionSheafUnit X).hom) (unit_comp_meromorphicUnitToUnit X)))

/-- The section over the top open set of the meromorphic section attached to `g`: the image of
`g` in `K_X(X)` under the identification `K_X ≅ 𝒦_X(𝒪_X)`. -/
theorem meromorphicSectionOfFunctionField_val_top :
    (meromorphicSectionOfFunctionField X g).val (op ⊤) =
      (unitIsoMeromorphicSectionSheafUnit X).hom.val.app (op ⊤)
        ((functionFieldToTotalQuotientSheaf X).app (op ⊤) (g : X.functionField)) :=
  (SheafOfModules.unitHomEquiv_apply_coe
      (meromorphicSectionSheaf X.sheaf (unitModule X))
      ((unitIsoOfFunctionFieldUnit X g).hom ≫
        (unitIsoMeromorphicSectionSheafUnit X).hom) (op ⊤)).trans
    (congrArg (fun y => (unitIsoMeromorphicSectionSheafUnit X).hom.val.app (op ⊤) y)
      (one_smul _ ((meromorphicFunctionsSectionOfFunctionField X
        (g : X.functionField)).eval (op ⊤))))

/-- The stalk map of `𝒪_X ⟶ K_X ≅ 𝒦_X(𝒪_X)` sends the germ of a section `t` of `𝒪_X` to the
germ of the image of `t` in `K_X`. -/
theorem stalkMap_toKUnit_comp_germ (W : X.Opens) (hW : genericPoint X ∈ W) (t : Γ(X, W)) :
    stalkMap ((toKUnit X ≫ (SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).map
          (unitIsoMeromorphicSectionSheafUnit X).hom).val) (genericPoint X)
        (germ (unitModule X).val W (genericPoint X) hW (show Γ(unitModule X, W) from t)) =
      germ (meromorphicSectionSheaf X.sheaf (unitModule X)).val W (genericPoint X) hW
        ((unitIsoMeromorphicSectionSheafUnit X).hom.val.app (op W)
          ((toTotalQuotientRingSheaf X).hom.app (op W) t)) :=
  (Stacks.ModuleStalk.stalkMap_germ
      ((toKUnit X ≫ (SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).map
        (unitIsoMeromorphicSectionSheafUnit X).hom).val) (genericPoint X) W hW
      (show Γ(unitModule X, W) from t)).trans
    (congrArg (fun y => germ (meromorphicSectionSheaf X.sheaf (unitModule X)).val W
        (genericPoint X) hW
        ((unitIsoMeromorphicSectionSheafUnit X).hom.val.app (op W) y))
      (toKUnit_val_app_apply X (op W) (show Γ(unitModule X, W) from t)))

/-- The germ at the generic point of the section over the top open set, read on a neighbourhood
`W` on which `g` is the germ of a section `t` of `𝒪_X`. -/
theorem germ_meromorphicSectionOfFunctionField_val_top (W : X.Opens)
    (hW : genericPoint X ∈ W) (t : Γ(X, W))
    (ht : X.presheaf.germ W (genericPoint X) hW t = (g : X.functionField)) :
    germ (meromorphicSectionSheaf X.sheaf (unitModule X)).val ⊤ (genericPoint X) trivial
        ((meromorphicSectionOfFunctionField X g).val (op ⊤)) =
      germ (meromorphicSectionSheaf X.sheaf (unitModule X)).val W (genericPoint X) hW
        ((unitIsoMeromorphicSectionSheafUnit X).hom.val.app (op W)
          ((toTotalQuotientRingSheaf X).hom.app (op W) t)) := by
  refine (congrArg (fun y => germ (meromorphicSectionSheaf X.sheaf (unitModule X)).val ⊤
      (genericPoint X) trivial y) (meromorphicSectionOfFunctionField_val_top X g)).trans ?_
  refine (Stacks.ModuleStalk.germ_res
    (M := ((SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).obj
      (meromorphicSectionSheaf X.sheaf (unitModule X))).val)
    (le_top : W ≤ ⊤) hW _).symm.trans ?_
  refine congrArg (fun y => germ (meromorphicSectionSheaf X.sheaf (unitModule X)).val W
      (genericPoint X) hW y) ?_
  refine (Stacks.ModuleStalk.res_app
      (((SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).map
        (unitIsoMeromorphicSectionSheafUnit X).hom).val) (le_top : W ≤ ⊤) _).trans ?_
  refine congrArg
    (fun y => (unitIsoMeromorphicSectionSheafUnit X).hom.val.app (op W) y) ?_
  refine (ConcreteCategory.congr_hom
    ((functionFieldToTotalQuotientSheaf X).naturality
      (homOfLE (le_top : W ≤ ⊤)).op) (g : X.functionField)).symm.trans ?_
  exact (congrArg (fun y => (functionFieldToTotalQuotientSheaf X).app (op W) y) ht).symm.trans
    (functionFieldToTotalQuotientSheaf_germ X W t hW)

/-- **The generic value of the meromorphic section attached to `g` is `g`.** -/
theorem genericValue_meromorphicSectionOfFunctionField :
    genericValue (unitModule X) (meromorphicSectionOfFunctionField X g) =
      (unitStalkEquiv X (genericPoint X)).symm (g : X.functionField) := by
  obtain ⟨W, hW, t, ht⟩ := X.presheaf.exists_germ_eq (g : X.functionField)
  have hv : (unitStalkEquiv X (genericPoint X)).symm (g : X.functionField) =
      germ (unitModule X).val W (genericPoint X) hW (show Γ(unitModule X, W) from t) :=
    (unitStalkEquiv X (genericPoint X)).injective
      ((LinearEquiv.apply_symm_apply _ _).trans
        ((Stacks.Ample.unitStalkFun_germ X (genericPoint X) W hW
          (show Γ(unitModule X, W) from t)).trans ht).symm)
  refine Stacks.Divisors.genericValue_eq_of_toMeromorphicSectionStalk_eq _ _ _ ?_
  exact (congrArg (fun y => toMeromorphicSectionStalk X.sheaf (unitModule X)
        (genericPoint X) y) hv).trans
    ((congrArg (fun φ : unitModule X ⟶ meromorphicSectionSheafAsModule X (unitModule X) =>
          stalkMap φ.val (genericPoint X)
            (germ (unitModule X).val W (genericPoint X) hW (show Γ(unitModule X, W) from t)))
        (toMeromorphicSectionSheafAsModule_eq X)).trans
      ((stalkMap_toKUnit_comp_germ X W hW t).trans
        (germ_meromorphicSectionOfFunctionField_val_top X g W hW t ht).symm))

variable [IsLocallyNoetherian X]

/-- **Stacks 02SF for a rational function.** The order of vanishing along a prime divisor `Z` of
the meromorphic section of `𝒪_X` attached to `g` is the order of vanishing of `g` at the generic
point of `Z`. -/
theorem orderOfVanishingMeromorphic_meromorphicSectionOfFunctionField
    (Z : Stacks.Divisors.PrimeDivisor X) :
    Stacks.Divisors.orderOfVanishingMeromorphic X (unitModule X)
        (meromorphicSectionOfFunctionField X g)
        (isRegularMeromorphicSection_meromorphicSectionOfFunctionField X g) Z =
      X.ord (g : X.functionField) Z.genericPoint :=
  orderOfVanishingMeromorphic_unitModule_eq_ord X (g : X.functionField) _ _
    (genericValue_meromorphicSectionOfFunctionField X g) Z

/-- **The coefficient identity of the proof of Stacks 0FDS at one prime divisor.** The
multiplicity of `𝒪_X/gI` minus the multiplicity of `𝒪_X/I` at the generic point of a prime
divisor `Z` is the order of vanishing of `g` along `Z`, where `I` is the ideal of denominators
of `g`.

This is the orientation that the distance function of Stacks 02MG actually gives: additivity
along `𝒪_X ⊇ I, gI` reads `d(𝒪_X, gI) − d(𝒪_X, I) = d(I, gI) = ord(g)`. The source states the
difference the other way round. -/
theorem sheafMultiplicity_denominator_sub_eq_orderOfVanishing
    (Z : Stacks.Divisors.PrimeDivisor X) :
    Stacks.Chow.sheafMultiplicity (cokernel (denominatorIdealMul X (unitModule X)
          (meromorphicSectionOfFunctionField X g))) Z.genericPoint -
        Stacks.Chow.sheafMultiplicity (cokernel (denominatorIdealι X (unitModule X)
          (meromorphicSectionOfFunctionField X g))) Z.genericPoint =
      Stacks.Divisors.orderOfVanishingMeromorphic X (unitModule X)
        (meromorphicSectionOfFunctionField X g)
        (isRegularMeromorphicSection_meromorphicSectionOfFunctionField X g) Z :=
  sheafMultiplicity_denominator_sub_eq_orderOfVanishingMeromorphic X g
    (genericValue_meromorphicSectionOfFunctionField X g) Z

end AlgebraicGeometry
