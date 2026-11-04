module

public import StacksFrontier.Topology.Sheaves.Modules.Differentials.Stalk

/-!
# The directed system of sections over the open neighbourhoods of a point

Let `φ : O₁ ⟶ O₂` be a morphism of presheaves of commutative rings on a topological space `X`
and let `x : X`.  The open neighbourhoods of `x`, ordered by reverse inclusion, form a directed
index set, and the sections of `O₁` and of `O₂` over them form a directed system of ring maps in
the sense of `Stacks.KaehlerDifferential.Colimit.IsCompatible`.  **This file records that system
  and identifies its
colimit with the pair of stalks at `x`**, compatibly with the algebra structures.

The point of doing this separately is that the identification of the colimit of the *modules of
differentials* of such a system with the module of differentials of the colimit — Stacks Tag
031G, available here as
`AlgebraicGeometry.SheafOfModules.omegaColimLinearEquiv` — is stated for exactly this data, and
the stalk of a presheaf of commutative rings is identified with the algebraic direct limit over
exactly this index category by
`AlgebraicGeometry.SheafOfModules.presheafStalkRingDirectLimitIso`.

## Main definitions

* `Stacks.RelativeDifferentialStalk.nhdDiagram`: the diagram of sections of a presheaf of
  commutative rings over the open neighbourhoods of `x`.
* `Stacks.RelativeDifferentialStalk.trans`: its transition maps, as ring homomorphisms.
* `Stacks.RelativeDifferentialStalk.algebraNhd`: the algebra structure on `O₂(U)` over `O₁(U)`
  given by `φ`, in the spelling the sectionwise Kähler differentials use.
* `Stacks.RelativeDifferentialStalk.stalkRingEquiv`: the algebraic direct limit of the sections
  over the neighbourhoods of `x`, as a ring isomorphism onto the stalk at `x`.

## Main results

* `Stacks.RelativeDifferentialStalk.isCompatible`: the sections of `φ` over the neighbourhoods of
  `x` form a compatible system in the sense of Stacks Tag 031G.  This is naturality of `φ`.
* `Stacks.RelativeDifferentialStalk.directedSystem`: the transition maps of the system form a
  directed system, which is functoriality of `O₂`.
* `Stacks.RelativeDifferentialStalk.stalkRingEquiv_algebraMap`: the two ring isomorphisms onto
  the stalks carry the algebra map of the colimit to the stalk map of `φ`.  This is the
  hypothesis of
  `AlgebraicGeometry.SheafOfModules.kaehlerDifferentialRingEquiv` at this system.

## Implementation notes

The index set is `OrderDual (OpenNhds x)`, not `(OpenNhds x)ᵒᵖ`: the direct-limit API of
`Mathlib.Algebra.Colimit` is stated for a directed *preorder*, and the two are matched by
`CategoryTheory.orderDualEquivalence`.  Both the ring-level and the additive-level
identifications in `StacksFrontier.Topology.Sheaves.Modules.Differentials.Stalk` are already stated
at that index, so the diagram is spelled here exactly as they spell it.

The algebra structure `algebraNhd` must be `(φ.app U).hom.toAlgebra` on the nose, and not some
isomorphic variant: it is the instance that `CommRingCat.KaehlerDifferential (φ.app U)` carries,
so anything else makes the sectionwise differentials a different type.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.RelativeDifferentialStalk

variable {X : TopCat.{u}}

/-- The diagram of sections of a presheaf of commutative rings over the open neighbourhoods of
`x`, indexed by the order dual of `OpenNhds x`. -/
public abbrev nhdDiagram (O : X.Presheaf CommRingCat.{u}) (x : X) :
    OrderDual (TopologicalSpace.OpenNhds x) ⥤ CommRingCat.{u} :=
  (CategoryTheory.orderDualEquivalence (TopologicalSpace.OpenNhds x)).functor ⋙
    (TopologicalSpace.OpenNhds.inclusion x).op ⋙ O

/-- The open neighbourhood of `x` indexed by `i`. -/
public abbrev nhdOpen {x : X} (i : OrderDual (TopologicalSpace.OpenNhds x)) : Opens X :=
  (OrderDual.ofDual i).1

/-- `x` lies in the open neighbourhood indexed by `i`. -/
public theorem mem_nhdOpen {x : X} (i : OrderDual (TopologicalSpace.OpenNhds x)) :
    x ∈ nhdOpen i :=
  (OrderDual.ofDual i).2

/-- The sections of a presheaf of commutative rings over the open neighbourhood indexed by `i`. -/
public abbrev nhdRing (O : X.Presheaf CommRingCat.{u}) {x : X}
    (i : OrderDual (TopologicalSpace.OpenNhds x)) : Type u :=
  ToType ((nhdDiagram O x).obj i)

/-- The restriction maps of the diagram of sections over the neighbourhoods of `x`, as ring
homomorphisms. -/
public abbrev trans (O : X.Presheaf CommRingCat.{u}) {x : X}
    ⦃i j : OrderDual (TopologicalSpace.OpenNhds x)⦄ (h : i ≤ j) :
    nhdRing O i →+* nhdRing O j :=
  ((nhdDiagram O x).map (homOfLE h)).hom

/-- The transition maps of the system of sections of a presheaf of commutative rings over the
neighbourhoods of `x` form a directed system.  This is functoriality of the presheaf. -/
public theorem directedSystem (O : X.Presheaf CommRingCat.{u}) (x : X) :
    DirectedSystem (fun i => nhdRing O (x := x) i)
      (fun _ _ h => (trans O h : nhdRing O _ → nhdRing O _)) where
  map_self {i} a := by
    simpa [trans] using
      congrArg (fun m : (nhdDiagram O x).obj i ⟶ (nhdDiagram O x).obj i => m.hom a)
        ((nhdDiagram O x).map_id i)
  map_map {k j i} hij hjk a := by
    exact congrArg (fun m : (nhdDiagram O x).obj i ⟶ (nhdDiagram O x).obj k => m.hom a)
      (((nhdDiagram O x).map_comp (homOfLE hij) (homOfLE hjk)).symm)

variable {O₁ O₂ : X.Presheaf CommRingCat.{u}} (φ : O₁ ⟶ O₂)

/-- The morphism `φ`, restricted to the diagram of neighbourhoods of `x`. -/
public abbrev nhdNatTrans (x : X) : nhdDiagram O₁ x ⟶ nhdDiagram O₂ x :=
  CategoryTheory.Functor.whiskerLeft
    (CategoryTheory.orderDualEquivalence (TopologicalSpace.OpenNhds x)).functor
    (CategoryTheory.Functor.whiskerLeft (TopologicalSpace.OpenNhds.inclusion x).op φ)

/-- The algebra structure on the sections of `O₂` over a neighbourhood of `x` as an algebra over
the sections of `O₁`, induced by `φ`.  This is the instance carried by
`CommRingCat.KaehlerDifferential (φ.app _)`. -/
public noncomputable abbrev algebraNhd (x : X) (i : OrderDual (TopologicalSpace.OpenNhds x)) :
    Algebra (nhdRing O₁ i) (nhdRing O₂ i) :=
  (φ.app (op (nhdOpen i))).hom.toAlgebra

/-- **The sections of `φ` over the neighbourhoods of a point form a compatible system.** This is
naturality of `φ`, written with `algebraMap` for its components. -/
public theorem isCompatible (x : X) :
    letI := algebraNhd φ x
    Stacks.KaehlerDifferential.Colimit.IsCompatible (R := fun i : OrderDual
      (TopologicalSpace.OpenNhds x) =>
        nhdRing O₁ i)
      (S := fun i : OrderDual (TopologicalSpace.OpenNhds x) => nhdRing O₂ i)
      (trans O₁) (trans O₂) := by
  intro i j h
  exact (CommRingCat.hom_ext_iff.mp ((nhdNatTrans φ x).naturality (homOfLE h)).symm)

/-! ### The colimit of the system is the stalk -/

section StalkRing

variable (O : X.Presheaf CommRingCat.{u}) (x : X)

/-- **The colimit of the sections over the open neighbourhoods of `x` is the stalk at `x`.** This
is `AlgebraicGeometry.SheafOfModules.presheafStalkRingDirectLimitIso` read as a ring
isomorphism. -/
public noncomputable def stalkRingEquiv :
    Stacks.KaehlerDifferential.Colimit.Rinf (trans O (x := x)) ≃+* ToType (O.stalk x) :=
  (AlgebraicGeometry.SheafOfModules.presheafStalkRingDirectLimitIso O x).commRingCatIsoToRingEquiv

/-- The identification of the colimit with the stalk sends the image of a section over a
neighbourhood of `x` to its germ. -/
public theorem stalkRingEquiv_of (i : OrderDual (TopologicalSpace.OpenNhds x))
    (z : nhdRing O i) :
    stalkRingEquiv O x (Ring.DirectLimit.of _ _ i z) = O.germ (nhdOpen i) x (mem_nhdOpen i) z :=
  AlgebraicGeometry.SheafOfModules.presheafStalkRingDirectLimitIso_apply_of O x i z

end StalkRing

/-- **The colimit identifications carry the structure map of the colimit to the stalk map.** Under
`Stacks.RelativeDifferentialStalk.stalkRingEquiv` at `O₁` and at `O₂`, the ring map
`Stacks.KaehlerDifferential.Colimit.uinf` induced by `φ` on the colimits becomes the map of stalks
  induced by `φ`.

This is the commuting-square hypothesis of
`AlgebraicGeometry.SheafOfModules.kaehlerDifferentialRingEquiv` for the system of sections of `φ`
over the neighbourhoods of `x`. -/
public theorem stalkRingEquiv_uinf (x : X) :
    letI := algebraNhd φ x
    ∀ r : Stacks.KaehlerDifferential.Colimit.Rinf (trans O₁ (x := x)),
      stalkRingEquiv O₂ x
          (Stacks.KaehlerDifferential.Colimit.uinf (trans O₁) (trans O₂) (isCompatible φ x) r) =
        ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map φ).hom
          (stalkRingEquiv O₁ x r) := by
  intro r
  let := algebraNhd φ x
  induction r using Ring.DirectLimit.induction_on with
  | ih i z =>
      rw [Stacks.KaehlerDifferential.Colimit.uinf_of (trans O₁) (trans O₂) (isCompatible φ x) i z,
        stalkRingEquiv_of, stalkRingEquiv_of]
      exact
        (TopCat.Presheaf.stalkFunctor_map_germ_apply (nhdOpen i) x (mem_nhdOpen i) φ z).symm

end Stacks.RelativeDifferentialStalk

end
