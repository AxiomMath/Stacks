module

public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalk.Colimit

/-!
# The stalk of the sectionwise differentials is the differentials of the stalks

Let `φ : O₁ ⟶ O₂` be a morphism of presheaves of commutative rings on a topological space `X` and
let `x : X`.  **This file proves that the stalk at `x` of the presheaf of sectionwise relative
differentials of `φ` is the module of Kähler differentials of the stalk map of `φ` at `x`,**
linearly over the stalk of `O₂`, by the identification carrying the germ of the universal
differential of a local section to the universal differential of its germ.

This is the presheaf-level form of the displayed identification in part (4) of Stacks Tag 01V9,
and of Stacks Tag 01V0 — "the stalk of `Ω` is `Ω` of the stalks" — for the sectionwise
construction.

## Main definitions

* `Stacks.RelativeDifferentialStalk.stalkLinearEquiv`: the identification, as a linear
  equivalence over the stalk of `O₂`.

## Main results

* `Stacks.RelativeDifferentialStalk.stalkLinearEquiv_germ_D`: the identification carries the germ
  of the universal differential of a local section of `O₂` to the universal differential of the
  germ of that section.  This pins the identification down.

## Implementation notes

The three ingredients are assembled here:
`Stacks.RelativeDifferentialStalk.omegaColimStalkAddEquiv`, which identifies the stalk with the
colimit of the sectionwise differentials;
`Stacks.RelativeDifferentialStalk.omegaColimStalkEquiv`, which identifies that colimit with the
Kähler differentials of the stalk map; and
`AlgebraicGeometry.SheafOfModules.linearEquivOfRingEquivScalars`, which reads the composite as
linear over the stalk of `O₂` rather than over the colimit ring.

For that last step both the stalk and the Kähler differentials of the stalk map are given a module
structure over the colimit ring, in each case as the stalk action read through
`Stacks.RelativeDifferentialStalk.stalkRingEquiv`; the hypotheses of the scalar transfer then hold
by definition, and the composite is linear for those structures by
`Stacks.RelativeDifferentialStalk.omegaColimStalkAddEquiv_smul`.

## What is *not* here

This is about the stalk of Mathlib's *presheaf* `relativeDifferentials'`, not about the stalk of
the *sheaf* `AlgebraicGeometry.SheafOfModules.moduleOfDifferentials`, and so not about
`AlgebraicGeometry.Scheme.Hom.relativeDifferentials` either.  The step from here to there is the
statement that the unit of sheafification
`AlgebraicGeometry.SheafOfModules.toSectionwiseDifferentialsSheaf` induces an isomorphism on
stalks, together with
`AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsIsoSectionwise`.  No `stacks` attribute is
attached here for that reason.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.SheafOfModules PresheafOfModules

universe u

namespace Stacks.RelativeDifferentialStalk

variable {X : TopCat.{u}} {O₁ O₂ : X.Presheaf CommRingCat.{u}} (φ : O₁ ⟶ O₂) (x : X)
  [DecidableEq (OrderDual (TopologicalSpace.OpenNhds x))]

/-- The module structure over the colimit ring on the stalk of the sectionwise differentials,
given by reading the stalk action through the identification
`Stacks.RelativeDifferentialStalk.stalkRingEquiv` of the colimit ring with the stalk of `O₂`. -/
public noncomputable abbrev moduleSinfStalk :
    Module (Stacks.KaehlerDifferential.Colimit.Sinf (trans O₂ (x := x)))
      (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' φ).presheaf x)) :=
  Module.compHom _ (stalkRingEquiv O₂ x).toRingHom

/-- The composite of the two identifications, as a linear equivalence over the colimit ring. -/
public noncomputable def stalkSinfLinearEquiv :
    letI := algebraNhd φ x
    letI := algebraStalk φ x
    letI := moduleSinfStalk φ x
    letI := moduleSinfOmegaStalk φ x
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' φ).presheaf x)
      ≃ₗ[Stacks.KaehlerDifferential.Colimit.Sinf (trans O₂ (x := x))]
      KaehlerDifferential (ToType (O₁.stalk x)) (ToType (O₂.stalk x)) := by
  letI := algebraNhd φ x
  letI := algebraStalk φ x
  letI := moduleSinfOmegaColim φ x
  letI := moduleSinfStalk φ x
  letI := moduleSinfOmegaStalk φ x
  have h : ∀ (s : Stacks.KaehlerDifferential.Colimit.Sinf (trans O₂ (x := x)))
      (m : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' φ).presheaf x)),
      (omegaColimStalkAddEquiv φ x).symm (s • m) =
        s • (omegaColimStalkAddEquiv φ x).symm m := by
    intro s m
    apply (omegaColimStalkAddEquiv φ x).injective
    rw [AddEquiv.apply_symm_apply, omegaColimStalkAddEquiv_smul, AddEquiv.apply_symm_apply]
    rfl
  let g := (omegaColimStalkAddEquiv φ x).symm.trans (omegaColimStalkEquiv φ x).toAddEquiv
  exact
    { toFun := g
      map_add' := g.map_add
      map_smul' := fun s m => by
        change omegaColimStalkEquiv φ x ((omegaColimStalkAddEquiv φ x).symm (s • m)) = _
        rw [h s m, map_smul, RingHom.id_apply]
        rfl
      invFun := g.symm
      left_inv := g.left_inv
      right_inv := g.right_inv }

/-- **The stalk of the sectionwise relative differentials is the Kähler differentials of the stalk
map**, as a linear equivalence over the stalk of `O₂`. -/
public noncomputable def stalkLinearEquiv :
    letI := algebraStalk φ x
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' φ).presheaf x)
      ≃ₗ[ToType (O₂.stalk x)]
      KaehlerDifferential (ToType (O₁.stalk x)) (ToType (O₂.stalk x)) := by
  letI := algebraNhd φ x
  letI := algebraStalk φ x
  letI := moduleSinfStalk φ x
  letI := moduleSinfOmegaStalk φ x
  exact linearEquivOfRingEquivScalars (stalkRingEquiv O₂ x) (fun _ _ => rfl) (fun _ _ => rfl)
    (stalkSinfLinearEquiv φ x)

/-- **The identification carries universal differentials to universal differentials.** The germ at
`x` of the universal differential of a section of `O₂` over a neighbourhood of `x` goes to the
universal differential of the germ of that section. -/
public theorem stalkLinearEquiv_germ_D (i : OrderDual (TopologicalSpace.OpenNhds x))
    (a : nhdRing O₂ i) :
    letI := algebraStalk φ x
    stalkLinearEquiv φ x
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' φ).presheaf (nhdOpen i) x
          (mem_nhdOpen i)
          (CommRingCat.KaehlerDifferential.d (f := φ.app (op (nhdOpen i))) a)) =
      KaehlerDifferential.D (ToType (O₁.stalk x)) (ToType (O₂.stalk x))
        (O₂.germ (nhdOpen i) x (mem_nhdOpen i) a) := by
  let := algebraNhd φ x
  let := algebraStalk φ x
  let := moduleSinfOmegaColim φ x
  let := moduleSinfStalk φ x
  let := moduleSinfOmegaStalk φ x
  show omegaColimStalkEquiv φ x
      ((omegaColimStalkAddEquiv φ x).symm
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' φ).presheaf (nhdOpen i) x
          (mem_nhdOpen i)
          (KaehlerDifferential.D (nhdRing O₁ i) (nhdRing O₂ i) a))) = _
  rw [show (omegaColimStalkAddEquiv φ x).symm
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' φ).presheaf (nhdOpen i) x
          (mem_nhdOpen i) (KaehlerDifferential.D (nhdRing O₁ i) (nhdRing O₂ i) a)) =
      Stacks.KaehlerDifferential.Colimit.ofΩ (trans O₁) (trans O₂) (isCompatible φ x) i
        (KaehlerDifferential.D (nhdRing O₁ i) (nhdRing O₂ i) a) from
    (AddEquiv.symm_apply_eq _).mpr (omegaColimStalkAddEquiv_ofΩ φ x i _).symm]
  exact omegaColimStalkEquiv_ofΩ_D φ x i a

end Stacks.RelativeDifferentialStalk

end
