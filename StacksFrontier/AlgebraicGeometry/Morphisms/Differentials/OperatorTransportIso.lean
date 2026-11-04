module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.OperatorOrderOpenImmersion

/-!
# Differential operators across an isomorphism of schemes

An isomorphism of schemes `e : X ⟶ X'` is an open immersion whose image is the whole of `X'`, so
the differential operators of order at most `k` on `X'/Y` between two modules on `X'` are the
differential operators of order at most `k` on `X/Y` between the restrictions of those modules
along `e`. Precomposing an open immersion with an isomorphism leaves its image unchanged, so the
same transport identifies the operators defined over the opens contained in the image of an open
immersion with the operators on any scheme isomorphic to its source.

## Main definitions

* `DiffOp.RawOp.congrBase`: reindexing an operator along an equality of base opens.

## Main results

* `AlgebraicGeometry.isGlobalDiffOpOfOrder_iff_restrict_top`: a global operator is a differential
  operator of order at most `k` on `X/Y` exactly when its restriction to the whole space is.
* `AlgebraicGeometry.globalDiffOpEquivOfIso`: the differential operators of order at most `k` on
  `X'/Y` are those on `X/Y` between the restricted modules, for an isomorphism `X ⟶ X'`.
* `AlgebraicGeometry.diffOpEquivGlobalDiffOpRestrictOfIso`: the differential operators of order at
  most `k` on `W/Y` defined over the opens contained in the image of an open immersion `j : Z ⟶ W`
  are the differential operators of order at most `k` on `Z'/Y`, for any scheme `Z'` isomorphic
  to `Z`.

## Implementation notes

The transport is not proved again: an isomorphism is an open immersion, and the two statements
follow from the comparison across an open immersion once the base open `⊤` of a global operator is
identified with the image of the isomorphism. That identification is an equality of opens rather
than a definitional one, hence the reindexing `DiffOp.RawOp.congrBase`, which is the identity after
substituting the equality and therefore preserves the order predicate.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace DiffOp.RawOp

variable {X : TopCat.{u}} {O O' : TopCat.Sheaf RingCat.{u} X} {F G : SheafOfModules.{u} O'}

/-- Reindexing an operator on local sections along an equality of its base opens. -/
def congrBase {U U' : Opens X} (h : U = U') : RawOp F G U ≃ RawOp F G U' := by
  subst h
  exact Equiv.refl _

/-- Reindexing along an equality of base opens does not change the order of an operator. -/
theorem isDiffOpOfOrder_congrBase (φ : O ⟶ O') (k : ℕ) {U U' : Opens X} (h : U = U')
    (D : RawOp F G U) :
    IsDiffOpOfOrder φ k (congrBase h D) ↔ IsDiffOpOfOrder φ k D := by
  subst h
  exact Iff.rfl

/-- Reindexing along an equality of base opens does not change the values of an operator. -/
theorem congrBase_apply {U U' : Opens X} (h : U = U') (D : RawOp F G U) (Y : Over U')
    (hY : Y.left ≤ U) : congrBase h D Y = D (Over.mk (homOfLE hY)) := by
  subst h
  rfl

end DiffOp.RawOp

namespace AlgebraicGeometry

open Scheme

/-- A global operator on local sections is a differential operator of order at most `k` on `X/Y`
exactly when its restriction to the whole space is one. -/
theorem isGlobalDiffOpOfOrder_iff_restrict_top {X Y : Scheme.{u}} (p : X ⟶ Y) (k : ℕ)
    {M M' : X.Modules} (D : DiffOp.GlobalOp M M') :
    DiffOp.IsGlobalDiffOpOfOrder p.relativeStructureSheafMap k D ↔
      DiffOp.IsDiffOpOfOrder p.relativeStructureSheafMap k (D.restrict ⊤) :=
  ⟨fun h ↦ h ⊤, fun h ↦ isGlobalDiffOpOfOrder_of_cover p k (fun _ : Unit ↦ ⊤) (by simp) D
    (DiffOp.RawOp.isNatural_of_isDiffOpOfOrder _ k _ h) fun _ ↦ h⟩

/-- **Differential operators across an isomorphism of schemes.** The differential operators of
order at most `k` on `X'/Y` between two modules on `X'` are the differential operators of order at
most `k` on `X/Y` between the restrictions of those modules along an isomorphism `e : X ⟶ X'`. -/
noncomputable def globalDiffOpEquivOfIso {X X' Y : Scheme.{u}} (e : X ⟶ X') [IsIso e]
    (p : X' ⟶ Y) (M M' : X'.Modules) (k : ℕ) :
    {D : DiffOp.GlobalOp M M' //
        DiffOp.IsGlobalDiffOpOfOrder p.relativeStructureSheafMap k D} ≃
      {E : DiffOp.GlobalOp (M.restrict e) (M'.restrict e) //
        DiffOp.IsGlobalDiffOpOfOrder (e ≫ p).relativeStructureSheafMap k E} :=
  (Equiv.subtypeEquiv
      (DiffOp.globalOpEquivRawOpTop.trans
        (DiffOp.RawOp.congrBase (Scheme.Hom.opensRange_of_isIso e).symm))
      fun D ↦ (isGlobalDiffOpOfOrder_iff_restrict_top p k D).trans
        (DiffOp.RawOp.isDiffOpOfOrder_congrBase _ k _ _).symm).trans
    (diffOpEquivGlobalDiffOpRestrict e p M M' k)

/-- **Differential operators on a chart, up to isomorphism of the chart.** The differential
operators of order at most `k` on `W/Y` defined over the opens contained in the image of an open
immersion `j : Z ⟶ W` are the differential operators of order at most `k` on `Z'/Y` between the
restrictions along `e ≫ j`, for any isomorphism `e : Z' ⟶ Z`. -/
noncomputable def diffOpEquivGlobalDiffOpRestrictOfIso {Z' Z W Y : Scheme.{u}} (e : Z' ⟶ Z)
    [IsIso e] (j : Z ⟶ W) [IsOpenImmersion j] (p : W ⟶ Y) (M M' : W.Modules) (k : ℕ) :
    {D : DiffOp.RawOp M M' j.opensRange //
        DiffOp.IsDiffOpOfOrder p.relativeStructureSheafMap k D} ≃
      {E : DiffOp.GlobalOp (M.restrict (e ≫ j)) (M'.restrict (e ≫ j)) //
        DiffOp.IsGlobalDiffOpOfOrder ((e ≫ j) ≫ p).relativeStructureSheafMap k E} :=
  (Equiv.subtypeEquiv
      (DiffOp.RawOp.congrBase (Scheme.Hom.opensRange_comp_of_isIso e j).symm)
      fun D ↦ (DiffOp.RawOp.isDiffOpOfOrder_congrBase _ k _ D).symm).trans
    (diffOpEquivGlobalDiffOpRestrict (e ≫ j) p M M' k)

/-- The differential operator on `X/Y` corresponding to one on `X'/Y` across an isomorphism is its
value at the image of the open. -/
theorem globalDiffOpEquivOfIso_coe_apply {X X' Y : Scheme.{u}} (e : X ⟶ X') [IsIso e]
    (p : X' ⟶ Y) (M M' : X'.Modules) (k : ℕ)
    (D : {D : DiffOp.GlobalOp M M' //
      DiffOp.IsGlobalDiffOpOfOrder p.relativeStructureSheafMap k D}) (V : X.Opens) :
    (globalDiffOpEquivOfIso e p M M' k D).1 (op V) = D.1 (op (e ''ᵁ V)) :=
  DiffOp.RawOp.congrBase_apply (Scheme.Hom.opensRange_of_isIso e).symm _ (imageOver e V) le_top

/-- The differential operator on `Z'/Y` corresponding to one on `W/Y` is the value of the latter at
the image of the open. -/
theorem diffOpEquivGlobalDiffOpRestrictOfIso_coe_apply {Z' Z W Y : Scheme.{u}} (e : Z' ⟶ Z)
    [IsIso e] (j : Z ⟶ W) [IsOpenImmersion j] (p : W ⟶ Y) (M M' : W.Modules) (k : ℕ)
    (D : {D : DiffOp.RawOp M M' j.opensRange //
      DiffOp.IsDiffOpOfOrder p.relativeStructureSheafMap k D}) (V : Z'.Opens)
    (hV : (e ≫ j) ''ᵁ V ≤ j.opensRange) :
    (diffOpEquivGlobalDiffOpRestrictOfIso e j p M M' k D).1 (op V) =
      D.1 (Over.mk (homOfLE hV)) :=
  DiffOp.RawOp.congrBase_apply (Scheme.Hom.opensRange_comp_of_isIso e j).symm _
    (imageOver (e ≫ j) V) hV

end AlgebraicGeometry

end
