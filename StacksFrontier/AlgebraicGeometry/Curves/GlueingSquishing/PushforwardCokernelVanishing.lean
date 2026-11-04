module

public import Mathlib.AlgebraicGeometry.Restrict
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.StalkSupport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseChangeUnitor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposUnitStructureMap

/-!
# Vanishing of the cokernel stalk on the almost-isomorphism locus

Let `f : X' ⟶ X` be a morphism of schemes and let `U` be an open of `X` on which the
restriction `f ∣_ U` is an isomorphism. This file proves that the stalk of the cokernel of the
unit map `𝒪_X ⟶ f_* 𝒪_{X'}` vanishes at every point of `U`.

The unit map is read as `Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit` applied
to the structure morphism of the pushforward algebra `pushforwardAlgebra f`, whose underlying
module `AlgebraSheaf.underlyingModule (pushforwardAlgebra f)` is `f_* 𝒪_{X'}` read as an
`𝒪_X`-module. By the stalkwise criterion for surjectivity
(`AlgebraicGeometry.Scheme.Modules.surjective_stalkLinearMap_iff_notMem_supp_cokernel`), vanishing
of the cokernel stalk at `x ∈ U` follows from surjectivity of the stalk map of the unit at `x`,
which is checked by hand: a section of `f_* 𝒪_{X'}` near `x` is a section of `𝒪_{X'}` on some
small open `W' ≤ U`, on which `f.app W'` is an isomorphism since `f ∣_ U` is, so it is the image
of its own preimage under the unit map (which, on sections over opens contained in `U`, agrees
with `f.app` itself).

## Main results

* `Stacks.GlueSquishFactor.isIso_app_of_isIso_morphismRestrict`: if `f ∣_ W` is an isomorphism
  and `U ≤ W`, then `f.app U` is an isomorphism.
* `Stacks.GlueSquishFactor.isZero_stalk_cokernel_structureUnitHom`: the stalk of the cokernel of
  the unit map `𝒪_X ⟶ f_* 𝒪_{X'}` vanishes at every point of an open `U` on which `f` restricts
  to an isomorphism.

## Implementation notes

`unitModule X` is `SheafOfModules.unit X.ringCatSheaf` with its return type ascribed to
`X.Modules`; without the ascription on a named declaration, dot notation into the
`SheafOfModules` API fails to resolve on the unascribed term. The component identity used to
identify the unit map's action on sections with `f.app` is a bare `rfl` once both sides are
unfolded to the structure morphism of the pushforward algebra.

## References

* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.GlueSquishFactor

/-- If `f` restricts to an isomorphism on `W` then `f.app U` is an isomorphism for every open
`U ≤ W`: shrink `U` to its image under the inclusion of `W`, where the restricted morphism is
already known to be an isomorphism on the corresponding preimage. -/
theorem isIso_app_of_isIso_morphismRestrict {X' X : Scheme.{u}} (f : X' ⟶ X)
    (W : X.Opens) [IsIso (f ∣_ W)] (U : X.Opens) (hUW : U ≤ W) : IsIso (f.app U) := by
  have he : W.ι ''ᵁ (W.ι ⁻¹ᵁ U) = U := by
    ext x
    show (∃ y : W.toScheme, y ∈ W.ι ⁻¹ᵁ U ∧ W.ι y = x) ↔ x ∈ U
    refine ⟨?_, fun hx => ⟨⟨x, hUW hx⟩, hx, rfl⟩⟩
    rintro ⟨y, hy, rfl⟩
    exact hy
  have h1 : IsIso ((f ∣_ W).app (W.ι ⁻¹ᵁ U)) := inferInstance
  have hcomp : IsIso (f.app (W.ι ''ᵁ (W.ι ⁻¹ᵁ U)) ≫
      X'.presheaf.map
        (eqToHom (image_morphismRestrict_preimage f W (W.ι ⁻¹ᵁ U))).op) := by
    rw [← morphismRestrict_app f W (W.ι ⁻¹ᵁ U)]
    exact h1
  have hpart : IsIso (f.app (W.ι ''ᵁ (W.ι ⁻¹ᵁ U))) :=
    IsIso.of_isIso_comp_right _
      (X'.presheaf.map (eqToHom (image_morphismRestrict_preimage f W (W.ι ⁻¹ᵁ U))).op)
  exact he ▸ hpart

/-- The structure sheaf of a scheme, read as a module over itself via the unit of
`SheafOfModules`. -/
def unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- The unit map `𝒪_X ⟶ f_* 𝒪_{X'}` of a morphism of schemes `f : X' ⟶ X`, read as a morphism
of `𝒪_X`-modules, where the pushforward `f_* 𝒪_{X'}` is the underlying module of the
pushforward algebra `pushforwardAlgebra f`. -/
def structureUnitHom {X' X : Scheme.{u}} (f : X' ⟶ X) :
    unitModule X ⟶ (AlgebraSheaf.underlyingModule (pushforwardAlgebra f) : X.Modules) :=
  Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit
    (AlgebraSheaf.structureMap (pushforwardAlgebra f))

/-- The stalk map of the unit `𝒪_X ⟶ f_* 𝒪_{X'}` at a point `x` of an open `U` on which `f`
restricts to an isomorphism is surjective: a germ of `f_* 𝒪_{X'}` at `x` comes from a section on
some small open `W' ≤ U`, on which `f.app W'` is an isomorphism, so that section is the image of
its own preimage under `f.app W'`, which agrees with the unit map on sections over opens
contained in `U`. -/
theorem surjective_stalkLinearMap_structureUnitHom {X' X : Scheme.{u}} (f : X' ⟶ X)
    (U : X.Opens) [IsIso (f ∣_ U)] {x : X} (hx : x ∈ U) :
    Function.Surjective (AlgebraicGeometry.stalkLinearMap
      (unitModule X) (AlgebraSheaf.underlyingModule (pushforwardAlgebra f))
      (structureUnitHom f) x) := by
  intro t
  obtain ⟨W, hxW, s, hs⟩ :=
    (AlgebraSheaf.underlyingModule (pushforwardAlgebra f)).presheaf.exists_germ_eq t
  set W' : X.Opens := W ⊓ U
  have hxW' : x ∈ W' := ⟨hxW, hx⟩
  set s' : (AlgebraSheaf.underlyingModule (pushforwardAlgebra f)).presheaf.obj (op W') :=
    (AlgebraSheaf.underlyingModule (pushforwardAlgebra f)).presheaf.map
      (homOfLE (inf_le_left : W' ≤ W)).op s with hs'def
  have hs' :
      (AlgebraSheaf.underlyingModule (pushforwardAlgebra f)).presheaf.germ W' x hxW' s' = t := by
    rw [hs'def, (AlgebraSheaf.underlyingModule (pushforwardAlgebra f)).presheaf.germ_res_apply
      (homOfLE (inf_le_left : W' ≤ W)) x hxW' s, hs]
  have hiso : IsIso (f.app W') := isIso_app_of_isIso_morphismRestrict f U W' inf_le_right
  set a' : X.presheaf.obj (op W') := CategoryTheory.inv (f.app W') s'
  have hfa' : f.app W' a' = s' := IsIso.inv_hom_id_apply (f.app W') s'
  refine ⟨(unitModule X).presheaf.germ W' x hxW' a', ?_⟩
  rw [stalkLinearMap_germ (unitModule X) (AlgebraSheaf.underlyingModule (pushforwardAlgebra f))
    (structureUnitHom f) W' x hxW' a']
  have hcomp : (structureUnitHom f).val.app (op W') a' =
      (AlgebraSheaf.structureMap (pushforwardAlgebra f)).hom.app (op W') a' :=
    Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit_val_app
      (AlgebraSheaf.structureMap (pushforwardAlgebra f)) (op W') a'
  have hrfl : (AlgebraSheaf.structureMap (pushforwardAlgebra f)).hom.app (op W') a' =
      (f.app W') a' := rfl
  rw [hcomp, hrfl, hfa', hs']

/-- **The main result.** The stalk of the cokernel of the unit `𝒪_X ⟶ f_* 𝒪_{X'}` vanishes at
every point of an open `U` on which `f` restricts to an isomorphism. -/
public theorem isZero_stalk_cokernel_structureUnitHom {X' X : Scheme.{u}} (f : X' ⟶ X)
    (U : X.Opens) [IsIso (f ∣_ U)] {x : X} (hx : x ∈ U) :
    IsZero ((AlgebraicGeometry.Scheme.Modules.stalkFunctor X x).obj
      (cokernel (structureUnitHom f))) :=
  (Scheme.Modules.notMem_supp_iff_isZero_stalk (cokernel (structureUnitHom f)) x).mp
    ((Scheme.Modules.surjective_stalkLinearMap_iff_notMem_supp_cokernel
      (structureUnitHom f) x).mp (surjective_stalkLinearMap_structureUnitHom f U hx))

end Stacks.GlueSquishFactor

end
