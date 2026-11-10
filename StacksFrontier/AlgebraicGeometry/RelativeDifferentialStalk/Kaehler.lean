module

public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalk.Diagram

/-!
# The colimit of the sectionwise differentials is the differentials of the stalks

Let `φ : O₁ ⟶ O₂` be a morphism of presheaves of commutative rings on a topological space `X`
and let `x : X`.  **This file identifies the colimit, over the open neighbourhoods of `x`, of the
modules of Kähler differentials of the sections of `φ` with the module of Kähler differentials of
the stalk map of `φ` at `x`.**

This is the Kähler-differential half of the computation of the stalk of the sheaf of relative
differentials: the stalk of a presheaf is the colimit over the neighbourhoods of the point, so
once the colimit of the sectionwise differentials is known to be `Ω` of the stalks, the remaining
work is purely the identification of the stalk with that colimit.

## Main definitions

* `Stacks.RelativeDifferentialStalk.omegaColimStalkEquiv`: the comparison, as a linear
  equivalence over the colimit ring.
* `Stacks.RelativeDifferentialStalk.omegaColimStalkLinearEquiv`: the same comparison read as a
  linear equivalence over the stalk of `O₂`, which is the form a statement about the stalk of a
  sheaf of modules needs.

## Main results

* `Stacks.RelativeDifferentialStalk.omegaColimStalkEquiv_ofΩ_D`: the comparison carries the class
  of the differential of a section over a neighbourhood of `x` to the differential of its germ.
  This is what pins the comparison down; without it the equivalence says only that the two
  modules are abstractly isomorphic.

## Implementation notes

Three transports are composed.

*The colimit of differentials is the differentials of the colimit.*  This is Stacks Tag 031G,
available as `AlgebraicGeometry.SheafOfModules.omegaColimLinearEquiv`; its hypotheses are the
compatibility of the system and the directedness of the transition maps of `O₂`, both supplied by
`StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalk.Diagram`.

*The colimit rings are the stalks.*  This is
`AlgebraicGeometry.SheafOfModules.presheafStalkRingDirectLimitIso`, and the transport of Kähler
differentials along the resulting pair of ring isomorphisms is
`AlgebraicGeometry.SheafOfModules.kaehlerDifferentialRingEquiv`, whose commuting-square hypothesis
is `Stacks.RelativeDifferentialStalk.stalkRingEquiv_uinf`.

*The scalars are transferred.*  The composite of the first two is linear over the colimit ring
`Stacks.KaehlerDifferential.Colimit.Sinf`;
  `AlgebraicGeometry.SheafOfModules.linearEquivOfRingEquivScalars` reads it as
a linear equivalence over the stalk of `O₂` instead.  Both module structures in play on the target
are, by construction, the stalk action read through the ring isomorphism, so the hypotheses of
that transfer hold by definition on the right; on the left the module structure over the stalk is
*defined* to be the colimit action read backwards through the ring isomorphism, which is what
makes the same hypothesis hold there.

Every module structure involved has to be named explicitly in the statements.
  `Stacks.KaehlerDifferential.Colimit.Sinf`
and `Stacks.KaehlerDifferential.Colimit.OmegaColim` are reducible definitions over
  `Ring.DirectLimit` and
`Module.DirectLimit`, and the actions on them — `Stacks.KaehlerDifferential.Colimit.alginf`,
`Stacks.KaehlerDifferential.Colimit.omegaColimModule` — are definitions rather than instances, so
  instance search finds
none of them.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.SheafOfModules

universe u

namespace Stacks.RelativeDifferentialStalk

variable {X : TopCat.{u}} {O₁ O₂ : X.Presheaf CommRingCat.{u}} (φ : O₁ ⟶ O₂) (x : X)
  [DecidableEq (OrderDual (TopologicalSpace.OpenNhds x))]

/-- The algebra structure on the stalk of `O₂` over the stalk of `O₁` induced by `φ`. -/
public noncomputable abbrev algebraStalk :
    Algebra (ToType (O₁.stalk x)) (ToType (O₂.stalk x)) :=
  ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map φ).hom.toAlgebra

/-- The algebra structure on the stalk of `O₂` over the colimit of the sections of `O₂` over the
neighbourhoods of `x`, given by the identification of the two. -/
public noncomputable abbrev algebraSinfStalk :
    Algebra (Stacks.KaehlerDifferential.Colimit.Sinf (trans O₂ (x := x))) (ToType (O₂.stalk x)) :=
  (stalkRingEquiv O₂ x).toRingHom.toAlgebra

/-- The module structure over the colimit ring on the Kähler differentials of the stalk map,
obtained by reading the stalk action through the identification of the colimit with the stalk. -/
public noncomputable abbrev moduleSinfOmegaStalk :
    letI := algebraStalk φ x
    Module (Stacks.KaehlerDifferential.Colimit.Sinf (trans O₂ (x := x)))
      (KaehlerDifferential (ToType (O₁.stalk x)) (ToType (O₂.stalk x))) := by
  letI := algebraStalk φ x
  exact Module.compHom _ (stalkRingEquiv O₂ x).toRingHom

/-- The module structure over the colimit ring on the colimit of the sectionwise differentials. -/
public noncomputable abbrev moduleSinfOmegaColim :
    letI := algebraNhd φ x
    Module (Stacks.KaehlerDifferential.Colimit.Sinf (trans O₂ (x := x)))
      (Stacks.KaehlerDifferential.Colimit.OmegaColim (trans O₁) (trans O₂) (isCompatible φ x)) := by
  letI := algebraNhd φ x
  exact Stacks.KaehlerDifferential.Colimit.omegaColimModule (trans O₁) (trans O₂) (isCompatible φ x)
    (directedSystem O₂ x)

/-- **The colimit of the sectionwise Kähler differentials is the Kähler differentials of the
stalks**, as a linear equivalence over the colimit ring. -/
public noncomputable def omegaColimStalkEquiv :
    letI := algebraNhd φ x
    letI := algebraStalk φ x
    letI := moduleSinfOmegaColim φ x
    letI := moduleSinfOmegaStalk φ x
    Stacks.KaehlerDifferential.Colimit.OmegaColim (trans O₁) (trans O₂) (isCompatible φ x)
        ≃ₗ[Stacks.KaehlerDifferential.Colimit.Sinf (trans O₂ (x := x))]
      KaehlerDifferential (ToType (O₁.stalk x)) (ToType (O₂.stalk x)) := by
  letI := algebraNhd φ x
  letI := algebraStalk φ x
  letI := moduleSinfOmegaColim φ x
  letI := Stacks.KaehlerDifferential.Colimit.alginf (trans O₁) (trans O₂) (isCompatible φ x)
  letI := moduleSinfOmegaStalk φ x
  exact
    (omegaColimLinearEquiv (trans O₁) (trans O₂) (isCompatible φ x)
        (directedSystem O₂ x)).trans
      (kaehlerDifferentialRingEquiv (stalkRingEquiv O₁ x) (stalkRingEquiv O₂ x)
        (stalkRingEquiv_uinf φ x))

/-- `Stacks.RelativeDifferentialStalk.omegaColimStalkEquiv` is the composite of Stacks Tag 031G
with the transport along the two identifications of the colimit rings with the stalks. -/
public theorem omegaColimStalkEquiv_apply
    (z : letI := algebraNhd φ x
      Stacks.KaehlerDifferential.Colimit.OmegaColim (trans O₁) (trans O₂) (isCompatible φ x)) :
    letI := algebraNhd φ x
    letI := algebraStalk φ x
    letI := moduleSinfOmegaColim φ x
    letI := moduleSinfOmegaStalk φ x
    letI := Stacks.KaehlerDifferential.Colimit.alginf (trans O₁) (trans O₂) (isCompatible φ x)
    omegaColimStalkEquiv φ x z =
      kaehlerDifferentialRingEquiv (stalkRingEquiv O₁ x) (stalkRingEquiv O₂ x)
        (stalkRingEquiv_uinf φ x)
        (omegaColimLinearEquiv (trans O₁) (trans O₂) (isCompatible φ x)
          (directedSystem O₂ x) z) :=
  rfl

/-- **The comparison carries sectionwise differentials to differentials of germs.** The class in
the colimit of the differential of a section of `O₂` over a neighbourhood of `x` goes to the
differential of the germ of that section.

This is what pins the comparison down: without it the equivalence says only that the two modules
are abstractly isomorphic. -/
public theorem omegaColimStalkEquiv_ofΩ_D (i : OrderDual (TopologicalSpace.OpenNhds x))
    (a : nhdRing O₂ i) :
    letI := algebraNhd φ x
    letI := algebraStalk φ x
    letI := moduleSinfOmegaColim φ x
    letI := moduleSinfOmegaStalk φ x
    omegaColimStalkEquiv φ x
        (Stacks.KaehlerDifferential.Colimit.ofΩ (trans O₁) (trans O₂) (isCompatible φ x) i
          (KaehlerDifferential.D (nhdRing O₁ i) (nhdRing O₂ i) a)) =
      KaehlerDifferential.D (ToType (O₁.stalk x)) (ToType (O₂.stalk x))
        (O₂.germ (nhdOpen i) x (mem_nhdOpen i) a) := by
  let := algebraNhd φ x
  let := algebraStalk φ x
  let := moduleSinfOmegaColim φ x
  let := Stacks.KaehlerDifferential.Colimit.alginf (trans O₁) (trans O₂) (isCompatible φ x)
  let := moduleSinfOmegaStalk φ x
  rw [omegaColimStalkEquiv_apply]
  have h₁ : omegaColimLinearEquiv (trans O₁) (trans O₂) (isCompatible φ x) (directedSystem O₂ x)
        (Stacks.KaehlerDifferential.Colimit.ofΩ (trans O₁) (trans O₂) (isCompatible φ x) i
          (KaehlerDifferential.D (nhdRing O₁ i) (nhdRing O₂ i) a)) =
      KaehlerDifferential.D (Stacks.KaehlerDifferential.Colimit.Rinf (trans O₁ (x := x)))
        (Stacks.KaehlerDifferential.Colimit.Sinf (trans O₂ (x := x)))
        (Ring.DirectLimit.of _ _ i a) := by
    change Stacks.KaehlerDifferential.Colimit.Theta (trans O₁) (trans O₂) (isCompatible φ x) _ = _
    rw [omegaColimTheta_ofΩ]
    exact Stacks.KaehlerDifferential.Colimit.sqMap_D _ _ _ _ _ _ _ a
  rw [h₁, kaehlerDifferentialRingEquiv_D, stalkRingEquiv_of]

end Stacks.RelativeDifferentialStalk

end
