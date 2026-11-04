module

public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.Factorization
public import StacksFrontier.AlgebraicGeometry.Descent.FlatBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineTilde
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.Locality

/-!
# The comparison map of a twist over an open on which the morphism is an isomorphism

Let `f : Z ⟶ X` be a morphism of schemes, `T` an `𝒪_Z`-module and `s : 𝒪_Z ⟶ T` a global section
of it, and let `V ⊆ X` be an open over which `f` is an isomorphism. This file proves that the
comparison map `𝒪_X ⟶ f_*T` of `Stacks.DeRham.BlowupTwist.twistUnitComparison` becomes
invertible on `V` as soon as `s` does on `f⁻¹V`.

For the blowing up of a scheme in a closed point this is the half of the statement away from the
point: the blowup is an isomorphism over the complement of the centre
(`AlgebraicGeometry.isIso_blowUp_restrict_compl_support`), and the canonical section of the
exceptional twist is invertible there because the exceptional divisor lies over the centre.

## The argument

The comparison map is the adjunction unit followed by the direct image of its own section,
`Stacks.DeRham.BlowupTwist.twistUnitComparison_eq_unit_comp`, so there are two factors.

*The direct image of the section* is handled by
`Stacks.AffineProjectionFormula.isIso_pullback_pushforward_map`: the direct image commutes with
restriction to an open of the target well enough to transport invertibility, by the naturality of
the base-change morphism of the restriction square.

*The unit* is handled by the second triangle identity of that same base-change morphism,
`Stacks.Modules.map_unit_comp_baseChangeNatTrans_app`: restricting the unit of `f^* ⊣ f_*` to `V`
and composing with the base-change morphism gives the unit of `(f∣_V)^* ⊣ (f∣_V)_*`, and that is
invertible because `f ∣_ V` is an isomorphism, so its inverse image is an equivalence and the
unit of an adjunction with fully faithful left adjoint is invertible. The base-change morphism of
a restriction square is invertible with no hypothesis
(`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_baseChangeNatTrans_restrictSquare`), so the
restricted unit is invertible.

No compatibility of the comparison map itself with restriction is used: both factors travel by
naturality, which is the technique of
`StacksFrontier/AlgebraicGeometry/ProjectionFormula/Locality.lean`.

## Main results

* `Stacks.BlowupTwistUnit.isIso_pullback_unit_of_isIso_morphismRestrict`: **the unit of
  `f^* ⊣ f_*` is invertible on an open of the target over which `f` is an isomorphism**, at every
  module.
* `Stacks.BlowupTwistUnit.isIso_pullback_twistUnitComparison`: **the comparison map of a twist
  is invertible on such an open as soon as the section is invertible upstairs.**

## References

* [Stacks Project, Tag 0G5H](https://stacks.math.columbia.edu/tag/0G5H)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.RingedSpace
open Stacks.AlgebraicGeometry Stacks.AlgebraicGeometry.AffineBaseChange

universe u

namespace Stacks.BlowupTwistUnit

variable {Z X : Scheme.{u}} (f : Z ⟶ X) (V : X.Opens)

/-- **The unit of `f^* ⊣ f_*` is invertible on an open of the target over which `f` is an
isomorphism.**

The second triangle identity of the base-change morphism of the restriction square
(`Stacks.Modules.map_unit_comp_baseChangeNatTrans_app`) identifies the restricted unit followed
by that morphism with the unit of `(f ∣_ V)^* ⊣ (f ∣_ V)_*` followed by an isomorphism. The
base-change morphism of a restriction square is invertible, and the unit upstairs is invertible
because `f ∣_ V` is an isomorphism, hence its inverse image is an equivalence. -/
theorem isIso_pullback_unit_of_isIso_morphismRestrict [IsIso (f ∣_ V)] (M : X.Modules) :
    IsIso ((Scheme.Modules.pullback V.ι).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)) := by
  have hnat := Stacks.Modules.map_unit_comp_baseChangeNatTrans_app (restrictSquare f V) M
  have hbc : IsIso ((AffinePushforward.baseChangeNatTrans (restrictSquare f V)).app
      ((Scheme.Modules.pullback f).obj M)) :=
    isIso_baseChangeNatTrans_restrictSquare f V _
  have hu : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ V)).unit) :=
    inferInstance
  have key : IsIso ((Scheme.Modules.pullback V.ι).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
      (AffinePushforward.baseChangeNatTrans (restrictSquare f V)).app
        ((Scheme.Modules.pullback f).obj M)) := by
    rw [hnat]
    infer_instance
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hbc key

/-- **The comparison map of a twist is invertible on an open over which the morphism is an
isomorphism, as soon as the section is invertible over the preimage of that open.**

The comparison map is the unit followed by the direct image of the section
(`Stacks.DeRham.BlowupTwist.twistUnitComparison_eq_unit_comp`); the unit restricts to an
isomorphism by `Stacks.BlowupTwistUnit.isIso_pullback_unit_of_isIso_morphismRestrict`, and the
direct image of the section does by
`Stacks.AffineProjectionFormula.isIso_pullback_pushforward_map`. -/
theorem isIso_pullback_twistUnitComparison [IsIso (f ∣_ V)]
    (T : SheafOfModules.{u} (structureRingSheaf Z.toRingedSpace))
    (s : SheafOfModules.unit (structureRingSheaf Z.toRingedSpace) ⟶ T)
    (hs : IsIso ((pullbackFunctor (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).map s)) :
    IsIso ((pullbackFunctor V.ι.toLRSHom.toShHom).map
      (Stacks.DeRham.BlowupTwist.twistUnitComparison f T s)) := by
  have hβ : IsIso ((pullbackFunctor V.ι.toLRSHom.toShHom).map
      ((pullbackAdjunction f.toLRSHom.toShHom).unit.app
        (SheafOfModules.unit (structureRingSheaf X.toRingedSpace)))) :=
    isIso_pullback_unit_of_isIso_morphismRestrict f V
      (show X.Modules from SheafOfModules.unit (structureRingSheaf X.toRingedSpace))
  have hps : IsIso ((pullbackFunctor V.ι.toLRSHom.toShHom).map
      ((pushforwardFunctor f.toLRSHom.toShHom).map s)) :=
    Stacks.AffineProjectionFormula.isIso_pullback_pushforward_map f V
      (show (show Z.Modules from _) ⟶ (show Z.Modules from T) from s) hs
  have hsplit : Stacks.DeRham.BlowupTwist.twistUnitComparison f T s =
      (pullbackAdjunction f.toLRSHom.toShHom).unit.app
          (SheafOfModules.unit (structureRingSheaf X.toRingedSpace)) ≫
        (pushforwardFunctor f.toLRSHom.toShHom).map
          ((pullbackObjUnitIso f.toLRSHom.toShHom).hom ≫ s) := by
    dsimp only [Stacks.DeRham.BlowupTwist.twistUnitComparison]
    rw [Adjunction.homEquiv_unit]
  rw [hsplit, Functor.map_comp, Functor.map_comp, Functor.map_comp]
  infer_instance

end Stacks.BlowupTwistUnit

end
