module

public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalk.Kaehler

/-!
# The stalk of the presheaf of sectionwise differentials

Let `φ : O₁ ⟶ O₂` be a morphism of presheaves of commutative rings on a topological space `X` and
let `x : X`.  **This file identifies the stalk at `x` of Mathlib's presheaf of sectionwise
relative differentials `PresheafOfModules.DifferentialsConstruction.relativeDifferentials'` with
the colimit over the open neighbourhoods of `x` of the sectionwise modules of Kähler
differentials**, and records that the identification is semilinear for the colimit ring acting on
the one side and the stalk of `O₂` acting on the other.

Composed with
`Stacks.RelativeDifferentialStalk.omegaColimStalkEquiv` this is the computation of the stalk of
the sectionwise differentials as the Kähler differentials of the stalk map, which is the content
of the displayed identification in part (4) of Stacks Tag 01V9 at the level of presheaves.

## Main definitions

* `Stacks.RelativeDifferentialStalk.omegaDiagram`: the diagram of sectionwise differentials over
  the open neighbourhoods of `x`.
* `Stacks.RelativeDifferentialStalk.omegaColimStalkAddEquiv`: the colimit of that diagram, as an
  additive equivalence onto the stalk.

## Main results

* `Stacks.RelativeDifferentialStalk.additiveDiagramDirectLimit_eq_omegaColim`: the direct limit of
  the diagram of sectionwise differentials *is* the colimit appearing in Stacks Tag 031G, with no
  comparison map needed.  Both are `Module.DirectLimit` over `ℤ` of the same family of modules
  with the same transition maps, and that holds by `rfl`.
* `Stacks.RelativeDifferentialStalk.omegaColimStalkAddEquiv_ofΩ`: the identification sends the
  class of a sectionwise differential to its germ.
* `Stacks.RelativeDifferentialStalk.omegaColimStalkAddEquiv_smul`: the identification is
  semilinear — it carries the action of the colimit ring to the action of the stalk of `O₂`
  through `Stacks.RelativeDifferentialStalk.stalkRingEquiv`.

## Implementation notes

The only reason this is short is
`Stacks.RelativeDifferentialStalk.additiveDiagramDirectLimit_eq_omegaColim`.  The sections of
`relativeDifferentials' φ` over an open `U` are `CommRingCat.KaehlerDifferential (φ.app (op U))`,
whose carrier is `Ω[O₂(U)⁄O₁(U)]` for the algebra structure `(φ.app (op U)).hom.toAlgebra`; its
restriction maps are `CommRingCat.KaehlerDifferential.map` of the naturality square of `φ`, whose
underlying function is `KaehlerDifferential.map` of that square.  The transition maps of the
Stacks Tag 031G system are `Stacks.KaehlerDifferential.Colimit.omegaTrans`, that is
  `Stacks.KaehlerDifferential.Colimit.sqMap`, whose
underlying function is the same `KaehlerDifferential.map` of the same square — the algebra
instances agree on the nose because `Stacks.RelativeDifferentialStalk.algebraNhd` is defined to be
`(φ.app _).hom.toAlgebra`, and the scalar-tower hypotheses are propositions.  So the two
`Module.DirectLimit`s are the same type, and the two `Module.DirectLimit.of` maps are the same
map.

Semilinearity is proved on germs rather than by induction on the colimit.  Every element of the
stalk of `O₂` and every element of the stalk of the differentials is a germ, by
`TopCat.Presheaf.exists_germ_eq`; restricting both to the intersection of their domains puts them
over a common neighbourhood, and there the statement is `PresheafOfModules.germ_smul` on one side
and `Stacks.KaehlerDifferential.Colimit.act_apply_ofΩ` on the other.  Doing it by induction on the
  colimit would need
the index-raising lemmas instead.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.SheafOfModules PresheafOfModules PresheafOfModulesOfCommRing

universe u

namespace Stacks.RelativeDifferentialStalk

variable {X : TopCat.{u}} {O₁ O₂ : X.Presheaf CommRingCat.{u}} (φ : O₁ ⟶ O₂) (x : X)
  [DecidableEq (OrderDual (TopologicalSpace.OpenNhds x))]

/-- The diagram of sectionwise Kähler differentials over the open neighbourhoods of `x`. -/
public noncomputable abbrev omegaDiagram :
    OrderDual (TopologicalSpace.OpenNhds x) ⥤ AddCommGrpCat.{u} :=
  (CategoryTheory.orderDualEquivalence (TopologicalSpace.OpenNhds x)).functor ⋙
    (TopologicalSpace.OpenNhds.inclusion x).op ⋙
      (DifferentialsConstruction.relativeDifferentials' φ).presheaf

/-- **The direct limit of the diagram of sectionwise differentials is the colimit of Stacks Tag
031G.** No comparison map is needed: both sides are the direct limit over `ℤ` of the same family
of modules along the same transition maps. -/
public theorem additiveDiagramDirectLimit_eq_omegaColim :
    letI := algebraNhd φ x
    additiveDiagramDirectLimit (omegaDiagram φ x) =
      Stacks.KaehlerDifferential.Colimit.OmegaColim (trans O₁) (trans O₂) (isCompatible φ x) :=
  rfl

/-- **The colimit of the sectionwise differentials over the neighbourhoods of `x` is the stalk at
`x` of the presheaf of sectionwise differentials.** -/
public noncomputable def omegaColimStalkAddEquiv :
    letI := algebraNhd φ x
    Stacks.KaehlerDifferential.Colimit.OmegaColim (trans O₁) (trans O₂) (isCompatible φ x) ≃+
      ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (DifferentialsConstruction.relativeDifferentials' φ).presheaf x) :=
  (presheafStalkAdditiveDirectLimitIso
    (DifferentialsConstruction.relativeDifferentials' φ).presheaf x).addCommGroupIsoToAddEquiv

/-- The identification of the colimit with the stalk sends the class of a sectionwise differential
to its germ. -/
public theorem omegaColimStalkAddEquiv_ofΩ (i : OrderDual (TopologicalSpace.OpenNhds x))
    (z : letI := algebraNhd φ x
      KaehlerDifferential (nhdRing O₁ i) (nhdRing O₂ i)) :
    letI := algebraNhd φ x
    omegaColimStalkAddEquiv φ x
        (Stacks.KaehlerDifferential.Colimit.ofΩ (trans O₁) (trans O₂) (isCompatible φ x) i z) =
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (DifferentialsConstruction.relativeDifferentials' φ).presheaf (nhdOpen i) x
        (mem_nhdOpen i) z :=
  presheafStalkAdditiveDirectLimitIso_apply_of
    (DifferentialsConstruction.relativeDifferentials' φ).presheaf x i z

/-- **The identification of the colimit with the stalk is semilinear.** It carries the action of
the colimit ring on the colimit of the sectionwise differentials to the action of the stalk of
`O₂` on the stalk of the sectionwise differentials, through the identification
`Stacks.RelativeDifferentialStalk.stalkRingEquiv` of those two rings. -/
public theorem omegaColimStalkAddEquiv_smul (s : Stacks.KaehlerDifferential.Colimit.Sinf (trans O₂
  (x := x)))
    (z : letI := algebraNhd φ x
      Stacks.KaehlerDifferential.Colimit.OmegaColim (trans O₁) (trans O₂) (isCompatible φ x)) :
    letI := algebraNhd φ x
    letI := moduleSinfOmegaColim φ x
    omegaColimStalkAddEquiv φ x (s • z) =
      stalkRingEquiv O₂ x s • omegaColimStalkAddEquiv φ x z := by
  let := algebraNhd φ x
  let := moduleSinfOmegaColim φ x
  -- At one index the statement is `germ_smul` on the stalk side and `act_apply_ofΩ` on the
  -- colimit side.
  have key : ∀ (k : OrderDual (TopologicalSpace.OpenNhds x)) (a : nhdRing O₂ k)
      (w : KaehlerDifferential (nhdRing O₁ k) (nhdRing O₂ k)),
      omegaColimStalkAddEquiv φ x
          ((Ring.DirectLimit.of _ _ k a : Stacks.KaehlerDifferential.Colimit.Sinf (trans O₂ (x :=
            x))) •
            Stacks.KaehlerDifferential.Colimit.ofΩ (trans O₁) (trans O₂) (isCompatible φ x) k w) =
        stalkRingEquiv O₂ x (Ring.DirectLimit.of _ _ k a) •
          omegaColimStalkAddEquiv φ x
            (Stacks.KaehlerDifferential.Colimit.ofΩ (trans O₁) (trans O₂) (isCompatible φ x) k w) :=
              by
    intro k a w
    rw [show (Ring.DirectLimit.of _ _ k a : Stacks.KaehlerDifferential.Colimit.Sinf (trans O₂ (x :=
      x))) •
          Stacks.KaehlerDifferential.Colimit.ofΩ (trans O₁) (trans O₂) (isCompatible φ x) k w =
        Stacks.KaehlerDifferential.Colimit.ofΩ (trans O₁) (trans O₂) (isCompatible φ x) k (a • w)
          from
      Stacks.KaehlerDifferential.Colimit.act_apply_ofΩ (trans O₁) (trans O₂) (isCompatible φ x)
        (directedSystem O₂ x) k a w]
    rw [omegaColimStalkAddEquiv_ofΩ, omegaColimStalkAddEquiv_ofΩ, stalkRingEquiv_of]
    exact PresheafOfModules.germ_smul (DifferentialsConstruction.relativeDifferentials' φ)
      x (nhdOpen k) (mem_nhdOpen k) a w
  refine s.induction_on fun i c => ?_
  refine z.induction_on fun j y => ?_
  have hd : IsDirectedOrder (OrderDual (TopologicalSpace.OpenNhds x)) := inferInstance
  obtain ⟨m, him, hjm⟩ := exists_ge_ge i j
  have hs : (Ring.DirectLimit.of _ _ i c : Stacks.KaehlerDifferential.Colimit.Sinf (trans O₂ (x :=
    x))) =
      Ring.DirectLimit.of _ _ m (trans O₂ him c) := (Ring.DirectLimit.of_f him c).symm
  have hz : Stacks.KaehlerDifferential.Colimit.ofΩ (trans O₁) (trans O₂) (isCompatible φ x) j y =
      Stacks.KaehlerDifferential.Colimit.ofΩ (trans O₁) (trans O₂) (isCompatible φ x) m
        (Stacks.KaehlerDifferential.Colimit.omegaTrans (trans O₁) (trans O₂) (isCompatible φ x) j m
          hjm y) :=
    (Stacks.KaehlerDifferential.Colimit.ofΩ_omegaTrans (trans O₁) (trans O₂) (isCompatible φ x) hjm
      y).symm
  change omegaColimStalkAddEquiv φ x
        ((Ring.DirectLimit.of _ _ i c : Stacks.KaehlerDifferential.Colimit.Sinf (trans O₂ (x := x)))
          •
          Stacks.KaehlerDifferential.Colimit.ofΩ (trans O₁) (trans O₂) (isCompatible φ x) j y) =
      stalkRingEquiv O₂ x (Ring.DirectLimit.of _ _ i c) •
        omegaColimStalkAddEquiv φ x
          (Stacks.KaehlerDifferential.Colimit.ofΩ (trans O₁) (trans O₂) (isCompatible φ x) j y)
  rw [hs, hz]
  exact key m _ _

end Stacks.RelativeDifferentialStalk

end
