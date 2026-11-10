module

public import StacksFrontier.AlgebraicGeometry.Chow.ChowGroupsEnvelopes.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.EnvelopeCycleLift
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ResidueFieldMap
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GenericResidueFieldOfSpec
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Basic
public import StacksFrontier.Topology.Dimension.SpecializingSurjection
public import StacksCore.Tactic.StacksAttribute

/-!
# Lifting an integral scheme to an envelope by a proper birational modification

Let `f : Y ⟶ X` be an envelope and let `g : W ⟶ X` be a morphism with `W` integral. Then `g`
factors through `f` after a proper birational modification of `W`: there is an integral `W'`, a
proper birational `b : W' ⟶ W` and an `a : W' ⟶ Y` with `b ≫ g = a ≫ f`. The modification is
the reduced closed subscheme of `Y ×_X W` on the closure of a point of the base-changed envelope
lying over the generic point of `W` with the same residue field.

## Main results

* `AlgebraicGeometry.IsEnvelope.exists_properBirational_modification` produces the modification
  and the factorization through the envelope.

## Implementation notes

Birationality is checked at the generic point only: an integral scheme has a single generic
point, and the chosen point of `Y ×_X W` has the same residue field as the generic point of `W`,
which upgrades to an isomorphism of local rings because the local rings at the generic points of
integral schemes are fields.

No finite type hypothesis on `g` is needed, so the statement is proved for an arbitrary
morphism `g`.

The restriction of the derived pullback of a perfect object to the modification, and the
resulting identity of Chern classes, are not covered here; see the references.

## References

* [Stacks Project, Tag 0GUF](https://stacks.math.columbia.edu/tag/0GUF)
* [Stacks Project, Tag 0GU7](https://stacks.math.columbia.edu/tag/0GU7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The closure of a point of a scheme, as a closed subset. -/
private noncomputable def closurePointSet {X : Scheme.{u}} (x : X) :
    TopologicalSpace.Closeds X :=
  ⟨TopologicalSpace.IrreducibleCloseds.closureSingleton x,
    (TopologicalSpace.IrreducibleCloseds.closureSingleton x).isClosed⟩

/-- The reduced induced closed subscheme structure on the closure of a point. -/
private noncomputable def closureSubscheme {X : Scheme.{u}} (x : X) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (closurePointSet x)

/-- The reduced induced closed subscheme on the closure of a point is supported on that
closure. -/
private theorem closureSubscheme_support {X : Scheme.{u}} (x : X) :
    (closureSubscheme x).support = closurePointSet x := by
  apply SetLike.coe_injective
  simp [closureSubscheme, Scheme.IdealSheafData.coe_support_vanishingIdeal]

/-- The reduced induced closed subscheme on the closure of a point is integral. -/
private theorem closureSubscheme_isIntegral {X : Scheme.{u}} (x : X) :
    IsIntegral (closureSubscheme x).subscheme := by
  have : IsReduced (closureSubscheme x).subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have : IrreducibleSpace (closureSubscheme x).subscheme :=
    Scheme.IdealSheafData.irreducibleSpace_subscheme X (closureSubscheme x) (by
      rw [(closureSubscheme x).range_subschemeι, closureSubscheme_support x]
      simpa [closurePointSet] using
        (TopologicalSpace.IrreducibleCloseds.closureSingleton x).isIrreducible)
  exact isIntegral_of_irreducibleSpace_of_isReduced (closureSubscheme x).subscheme

/-- The generic point of the reduced induced closed subscheme on the closure of a point is that
point. -/
private theorem closureSubscheme_genericPoint {X : Scheme.{u}} (x : X)
    [IsIntegral (closureSubscheme x).subscheme] :
    (closureSubscheme x).subschemeι
        (_root_.genericPoint (closureSubscheme x).subscheme) = x := by
  have hclos :
      closure ({((closureSubscheme x).subschemeι
        (_root_.genericPoint (closureSubscheme x).subscheme))} : Set X) =
      closure ({x} : Set X) := by
    rw [← Set.image_singleton,
      (closureSubscheme x).subschemeι.isClosedEmbedding.closure_image_eq,
      genericPoint_closure, Set.image_univ,
      (closureSubscheme x).range_subschemeι, closureSubscheme_support x]
    rfl
  exact isGenericPoint_closure.eq (hclos ▸ isGenericPoint_closure)

/-- A morphism of integral schemes mapping the generic point to the generic point and inducing
an isomorphism of residue fields there induces an isomorphism of local rings there. -/
private theorem stalkMap_isIso_of_residueFieldMap_isIso_at_generic
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) (x : X)
    (hx : x = genericPoint X) (hy : f x = genericPoint Y)
    (hres : IsIso (f.residueFieldMap x)) : IsIso (f.stalkMap x) := by
  cases hx
  have htarget : IsIso (Y.residue (f (genericPoint X))) := by
    rw [hy]
    exact isIso_residue_genericPoint Y
  have hcomp := IsIso.comp_isIso' htarget hres
  rw [Scheme.residue_residueFieldMap] at hcomp
  have := isIso_residue_genericPoint X
  exact IsIso.of_isIso_comp_right (f.stalkMap (genericPoint X)) (X.residue (genericPoint X))

section Modification

variable {X Y W : Scheme.{u}} (f : Y ⟶ X) (g : W ⟶ X)
  (hcd : IsCompletelyDecomposed f) [IsIntegral W]

/-- The reduced closed subscheme of `Y ×_X W` on the closure of a chosen point lying over the
generic point of `W` with the same residue field. -/
private noncomputable def modificationSubscheme : (pullback f g).IdealSheafData :=
  closureSubscheme (Stacks.Chow.envelopePointLift (pullback.snd f g)
    (isCompletelyDecomposed_pullback f g hcd) (genericPoint W))

/-- The modification of an integral scheme along an envelope is integral. -/
private theorem modificationSubscheme_isIntegral :
    IsIntegral (modificationSubscheme f g hcd).subscheme :=
  closureSubscheme_isIntegral _

/-- The modification maps to the original scheme. -/
private noncomputable def modificationMap :
    (modificationSubscheme f g hcd).subscheme ⟶ W :=
  (modificationSubscheme f g hcd).subschemeι ≫ pullback.snd f g

/-- The modification maps to the envelope. -/
private noncomputable def modificationLift :
    (modificationSubscheme f g hcd).subscheme ⟶ Y :=
  (modificationSubscheme f g hcd).subschemeι ≫ pullback.fst f g

/-- The two maps out of the modification form a commutative square over the original scheme. -/
private theorem modificationMap_fac :
    modificationMap f g hcd ≫ g = modificationLift f g hcd ≫ f := by
  dsimp [modificationMap, modificationLift]
  rw [Category.assoc, Category.assoc, pullback.condition]

/-- The modification of an integral scheme along an envelope is proper over it. -/
private theorem modificationMap_isProper (hproper : IsProper f) :
    IsProper (modificationMap f g hcd) :=
  MorphismProperty.comp_mem @IsProper _ _ inferInstance inferInstance

/-- The modification of an integral scheme along an envelope is birational over it. -/
private theorem modificationMap_isBirational :
    IsBirational (modificationMap f g hcd) := by
  let z := Stacks.Chow.envelopePointLift (pullback.snd f g)
    (isCompletelyDecomposed_pullback f g hcd) (genericPoint W)
  let V := modificationSubscheme f g hcd
  have : IsIntegral (closureSubscheme z).subscheme := closureSubscheme_isIntegral z
  have : IsIntegral V.subscheme := modificationSubscheme_isIntegral f g hcd
  have hηV : V.subschemeι (genericPoint V.subscheme) = z := closureSubscheme_genericPoint z
  have hηW : modificationMap f g hcd (genericPoint V.subscheme) = genericPoint W := by
    change pullback.snd f g (V.subschemeι (genericPoint V.subscheme)) = _
    rw [hηV]
    exact Stacks.Chow.envelopePointLift_map _ _ _
  have hres : IsIso ((modificationMap f g hcd).residueFieldMap
      (genericPoint V.subscheme)) := by
    have hq : IsIso ((pullback.snd f g).residueFieldMap
        (V.subschemeι (genericPoint V.subscheme))) := by
      rw [hηV]
      exact Stacks.Chow.envelopePointLift_residueFieldMap_isIso (pullback.snd f g)
        (isCompletelyDecomposed_pullback f g hcd) (genericPoint W)
    change IsIso ((V.subschemeι ≫ pullback.snd f g).residueFieldMap (genericPoint V.subscheme))
    rw [Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso' hq (isIso_residueFieldMap_of_isPreimmersion V.subschemeι _)
  refine isBirational_of_bijOn_of_isIso_stalkMap (modificationMap f g hcd) ?_ ?_
  · rw [genericPoints_eq_singleton, genericPoints_eq_singleton]
    exact Set.bijOn_singleton.mpr hηW
  · intro x hx
    rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
    subst x
    exact stalkMap_isIso_of_residueFieldMap_isIso_at_generic
      (modificationMap f g hcd) _ rfl hηW hres

end Modification

/-- **Stacks 0GUF**, the modification and the factorization. Let `f : Y ⟶ X` be an envelope and
let `g : W ⟶ X` be a morphism with `W` integral. Then there are an integral scheme `W'`, a
proper birational morphism `b : W' ⟶ W` and a morphism `a : W' ⟶ Y` with `b ≫ g = a ≫ f`. -/
@[stacks 0GUF "existence of the proper birational modification factoring through an envelope"]
theorem IsEnvelope.exists_properBirational_modification {X Y W : Scheme.{u}}
    {f : Y ⟶ X} (hf : IsEnvelope f) (g : W ⟶ X) [IsIntegral W] :
    ∃ (W' : Scheme.{u}) (b : W' ⟶ W) (a : W' ⟶ Y),
      IsIntegral W' ∧ IsProper b ∧ IsBirational b ∧ b ≫ g = a ≫ f :=
  ⟨(modificationSubscheme f g hf.isCompletelyDecomposed).subscheme,
    modificationMap f g hf.isCompletelyDecomposed,
    modificationLift f g hf.isCompletelyDecomposed,
    modificationSubscheme_isIntegral f g hf.isCompletelyDecomposed,
    modificationMap_isProper f g hf.isCompletelyDecomposed hf.isProper,
    modificationMap_isBirational f g hf.isCompletelyDecomposed,
    modificationMap_fac f g hf.isCompletelyDecomposed⟩

end AlgebraicGeometry

end
