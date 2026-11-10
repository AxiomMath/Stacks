module

public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.StalkTransport
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ResidueTrdeg

/-!
# The order of vanishing is unchanged along a dominant preimmersion

Let `i : Z ⟶ X` be a dominant preimmersion of integral schemes. Then the stalk maps of `i` are
isomorphisms, `i` induces an isomorphism of function fields, and `i` preserves codimension. If
moreover `X` and `Z` are locally Noetherian, the order of vanishing of a rational function `f` on
`X` at `i z` equals the order of vanishing of its image on `Z` at `z`.

## Main results

* `Stacks.Chow.dominantFunctionFieldMap_algebraMap`: the function-field map of a dominant
  morphism of integral schemes is compatible with its stalk map at every point.
* `Stacks.Chow.isIso_stalkMap_of_isDominant_of_isPreimmersion`: a dominant preimmersion of
  integral schemes has isomorphisms as stalk maps.
* `Stacks.Chow.functionFieldEquivOfIsDominantOfIsPreimmersion`: the isomorphism of function
  fields induced by a dominant preimmersion of integral schemes.
* `Stacks.Chow.coheight_eq_of_isDominant_of_isPreimmersion`: a dominant preimmersion of integral
  schemes preserves codimension.
* `Stacks.Chow.ord_dominantFunctionFieldMap_of_isPreimmersion`: the order of vanishing of a
  rational function is unchanged along a dominant preimmersion of locally Noetherian integral
  schemes.

## References

* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 02JU](https://stacks.math.columbia.edu/tag/02JU)
* [Stacks Project, Tag 02RK](https://stacks.math.columbia.edu/tag/02RK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Order

universe u

namespace Stacks.Chow

section Compatibility

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsIntegral X] [IsIntegral Z] [IsDominant i]

/-- For a dominant morphism `i : Z ⟶ X` of integral schemes, a point `z` of `Z` and a germ `a` at
`i z`, the function-field map carries the image of `a` in `R(X)` to the image in `R(Z)` of the germ
`i^* a` at `z`. -/
theorem dominantFunctionFieldMap_algebraMap (z : Z) (a : X.presheaf.stalk (i.base z)) :
    dominantFunctionFieldMap i (algebraMap (X.presheaf.stalk (i.base z)) X.functionField a) =
      algebraMap (Z.presheaf.stalk z) Z.functionField ((i.stalkMap z).hom a) := by
  have hη : i.base (genericPoint Z) = genericPoint X :=
    ((tfae_isDominant_of_isIntegral i).out 1 2).mp (inferInstance : IsDominant i)
  have htransport := stalkMap_cast_target i (genericPoint Z) hη
  have hgen := (genericPoint_spec Z).specializes (Set.mem_univ z)
  have hgenX : genericPoint X ⤳ i.base z := by
    rw [← hη]
    exact hgen.map i.continuous
  have hfieldMap (b : X.presheaf.stalk (genericPoint X)) :
      dominantFunctionFieldMap i b =
        (i.stalkMap (genericPoint Z)).hom
          ((eqToHom (congrArg X.presheaf.stalk hη.symm)).hom b) := by
    change (hη ▸ i.stalkMap (genericPoint Z)).hom b = _
    rw [htransport, eqToHom_stalkCongr X.presheaf hη.symm, stalkCongr_inv_hom X.presheaf hη]
    rfl
  change dominantFunctionFieldMap i ((X.presheaf.stalkSpecializes hgenX).hom a) =
    (Z.presheaf.stalkSpecializes hgen).hom ((i.stalkMap z).hom a)
  have hmap := i.base.hom.map_specializes hgen
  have hstalkHom :
      X.presheaf.stalkSpecializes hgenX ≫ eqToHom (congrArg X.presheaf.stalk hη.symm) =
        X.presheaf.stalkSpecializes hmap := by
    rw [eqToHom_stalkCongr X.presheaf hη.symm, TopCat.Presheaf.stalkCongr_inv,
      TopCat.Presheaf.stalkSpecializes_comp X.presheaf (Inseparable.of_eq hη).le hgenX]
  have hc := congrArg (fun g : X.presheaf.stalk (i.base z) ⟶ Z.presheaf.stalk (genericPoint Z) ↦
    g a) (Scheme.Hom.stalkSpecializes_stalkMap i (genericPoint Z) z hgen)
  calc _ = (i.stalkMap (genericPoint Z)).hom
          ((eqToHom (congrArg X.presheaf.stalk hη.symm)).hom
            ((X.presheaf.stalkSpecializes hgenX).hom a)) := hfieldMap _
    _ = (i.stalkMap (genericPoint Z)).hom ((X.presheaf.stalkSpecializes hmap).hom a) :=
        congrArg _ (congrArg (fun g ↦ g a) hstalkHom)
    _ = (Z.presheaf.stalkSpecializes hgen).hom ((i.stalkMap z).hom a) := by
        simpa only [CommRingCat.comp_apply] using hc

end Compatibility

section Preimmersion

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsIntegral X] [IsIntegral Z] [IsDominant i]
  [IsPreimmersion i]

/-- A dominant preimmersion of integral schemes has isomorphisms as stalk maps. -/
instance isIso_stalkMap_of_isDominant_of_isPreimmersion (z : Z) : IsIso (i.stalkMap z) := by
  refine (ConcreteCategory.isIso_iff_bijective (i.stalkMap z)).2
    ⟨fun a b hab ↦ IsFractionRing.injective (X.presheaf.stalk (i.base z)) X.functionField
      ((dominantFunctionFieldMap i).injective ?_), i.stalkMap_surjective z⟩
  rw [dominantFunctionFieldMap_algebraMap i z a, dominantFunctionFieldMap_algebraMap i z b, hab]

/-- A dominant preimmersion of integral schemes induces an isomorphism of function fields. -/
def functionFieldEquivOfIsDominantOfIsPreimmersion : X.functionField ≃+* Z.functionField := by
  have hη : i.base (genericPoint Z) = genericPoint X :=
    ((tfae_isDominant_of_isIntegral i).out 1 2).mp (inferInstance : IsDominant i)
  have htransport := stalkMap_cast_target i (genericPoint Z) hη
  refine RingEquiv.ofBijective (dominantFunctionFieldMap i) ⟨RingHom.injective _, fun b ↦ ?_⟩
  obtain ⟨a, ha⟩ := i.stalkMap_surjective (genericPoint Z) b
  refine ⟨(eqToHom (congrArg X.presheaf.stalk hη)).hom a, ?_⟩
  calc dominantFunctionFieldMap i ((eqToHom (congrArg X.presheaf.stalk hη)).hom a)
      = (i.stalkMap (genericPoint Z)).hom a := by
        change (hη ▸ i.stalkMap (genericPoint Z)).hom
          ((eqToHom (congrArg X.presheaf.stalk hη)).hom a) = _
        rw [htransport, eqToHom_stalkCongr X.presheaf hη]
        have hcancel := congrArg (i.stalkMap (genericPoint Z)).hom
          (congrArg (fun m : CommRingCat.Hom _ _ ↦ m.hom a)
            (Iso.inv_hom_id (X.presheaf.stalkCongr (Inseparable.of_eq hη.symm))))
        simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
          CommRingCat.hom_id, RingHom.id_apply] using hcancel
    _ = b := ha

/-- The isomorphism of function fields induced by a dominant preimmersion is the function-field
map `dominantFunctionFieldMap i`. -/
@[simp]
theorem functionFieldEquivOfIsDominantOfIsPreimmersion_apply (f : X.functionField) :
    functionFieldEquivOfIsDominantOfIsPreimmersion i f = dominantFunctionFieldMap i f :=
  rfl

/-- A dominant preimmersion of integral schemes preserves codimension. -/
theorem coheight_eq_of_isDominant_of_isPreimmersion (z : Z) :
    coheight (i.base z) = coheight z := by
  have h := ringKrullDim_eq_of_ringEquiv (asIso (i.stalkMap z)).commRingCatIsoToRingEquiv
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at h
  exact_mod_cast h

/-- The order of vanishing of a rational function is unchanged along a dominant preimmersion of
locally Noetherian integral schemes. -/
theorem ord_dominantFunctionFieldMap_of_isPreimmersion [IsLocallyNoetherian X]
    [IsLocallyNoetherian Z] (f : X.functionField) (z : Z) :
    Z.ord (dominantFunctionFieldMap i f) z = X.ord f (i.base z) := by
  set E := functionFieldEquivOfIsDominantOfIsPreimmersion i with hE
  change Z.ord (E f) z = X.ord f (i.base z)
  set e : X.presheaf.stalk (i.base z) ≃+* Z.presheaf.stalk z :=
    (asIso (i.stalkMap z)).commRingCatIsoToRingEquiv with he
  have hfield (a : X.presheaf.stalk (i.base z)) :
      E (algebraMap (X.presheaf.stalk (i.base z)) X.functionField a) =
        algebraMap (Z.presheaf.stalk z) Z.functionField (e a) :=
    dominantFunctionFieldMap_algebraMap i z a
  have hcoh := coheight_eq_of_isDominant_of_isPreimmersion i z
  by_cases hz : coheight z = 1
  · have hiz : coheight (i.base z) = 1 := hcoh.trans hz
    let _ : Ring.KrullDimLE 1 (X.presheaf.stalk (i.base z)) := krullDimLE_of_coheight_le hiz.le
    let _ : Ring.KrullDimLE 1 (Z.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
    rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hz, Scheme.ord_eq_ordHom_of_coheight_eq_one hiz]
    exact congrArg (fun v ↦ Multiplicative.toAdd (WithZero.unzeroD 1 v))
      (ordFrac_congr e E hfield f)
  · have hiz : coheight (i.base z) ≠ 1 := fun h ↦ hz (hcoh.symm.trans h)
    simp [hz, hiz]

end Preimmersion

end Stacks.Chow

end
