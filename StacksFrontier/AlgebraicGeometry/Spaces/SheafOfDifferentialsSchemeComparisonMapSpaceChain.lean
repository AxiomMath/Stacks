module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDifferentialsShortExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsSchemeComparisonMapSpacesSections

/-!
# The naturality square of Stacks 04CS on sections, carried in the space-side spelling

`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeComparisonMapSections.lean` carries
the Zariski side of the sections identity of Stacks 04CS in the `Γ` of
`AlgebraicGeometry.Space.representedRelativeDifferentialsZariski` over the preimage open
`ψ^{-1}O`, and its implementation notes record that the chain does not reach its last two links
there.  This module carries the same identity in the *other* spelling the chain needs — the
sections of a module on the small étale site of the represented algebraic space over
`AlgebraicGeometry.Space.representedOpensObj` — and supplies the two bridges between the
spellings which make the crossing affordable.

## Main results

* `AlgebraicGeometry.Space.eq_of_eq_representedOpensObj` and
  `AlgebraicGeometry.Space.eq_trans_representedOpensObj`: **the two bridges.**  For a module `N` on
  the small étale site of `yoneda.obj C`, a section of its Zariski restriction over an open `P` is
  a section of `N` over `AlgebraicGeometry.Space.representedOpensObj C P`; the first bridge reads
  an equation of such sections in the second spelling, and the second composes an equation in the
  first spelling with an equation in the second.
* `AlgebraicGeometry.Space.spaceChain_unit_representedUniversalDerivation`: **the last two links of
  the Zariski side, in the space-side spelling.**  This is
  `AlgebraicGeometry.Space.zariskiChain_unit_representedUniversalDerivation` with the type of its
  two sides written out as the sections of
  `AlgebraicGeometry.Space.representedRelativeDifferentials` over
  `AlgebraicGeometry.Space.representedOpensObj`, which is the spelling the spaces side of the
  square lives in.

## Implementation notes

**Why the bridges take the module as a variable.**  The crossing they perform is the one
`AlgebraicGeometry.Space.representedRestrictModule_map_app_apply` already pays for, and it is
affordable *only* in that shape.  Without any option override: with `N` a variable both
bridges elaborate; with the module written as
`AlgebraicGeometry.Space.representedRelativeDifferentials` of a variable morphism, or as the image
of a variable module on the small étale site of the *scheme* under the equivalence of module
categories of Stacks 03DX (2), the same crossing is a `(deterministic) timeout at whnf` at 200,000
heartbeats.  The reason is that
`AlgebraicGeometry.Space.representedRelativeDifferentials` is an `abbrev`: it is reducible, so the
elaborator unfolds it and then unfolds the Zariski sheaf of differentials beneath it, while a
variable is opaque.  Instantiating the variable afterwards is substitution and re-checks nothing.

**Why the chain is built by `have` and consumed by `exact`.**  A step written as
`refine Eq.trans (link) ?_`, or as `exact (link).trans (…)`, is a `(deterministic) timeout at
whnf` at these concrete arguments even when the link itself is instantiated for nothing and
`exact (link)` alone reports an ordinary type mismatch in under a second: the expected type fixes
the equation's type from the goal, and the middle argument is then assigned with its own type
re-inferred and checked against that.  A `have` with no expected type reads every intermediate
type off the links instead, and the single `exact` which consumes it pays one cheap comparison.
That is why `AlgebraicGeometry.Space.eq_trans_representedOpensObj` exists rather than a
`Eq.trans` at the point of use: it is the join of the two halves with all three sections as
variables, so nothing is unified against the goal.

## References

* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Bridges

variable {C : BigFppfOver B S hS}

/-- **An equation of sections of the Zariski restriction of a module on the small étale site of a
represented algebraic space, read over `AlgebraicGeometry.Space.representedOpensObj`.**  The
sections of `N` restricted to the small Zariski site of the scheme underlying `C`, over an open
`P`, are the sections of `N` over the object of the small étale site of `yoneda.obj C` that `P`
cuts out, so an equation of the latter is an equation of the former.

The module is a variable, and that is what makes the crossing affordable; the implementation note
says why. -/
theorem eq_of_eq_representedOpensObj
    (N : Modules.{u, u} B S hS (schemeSpace C).1 (schemeSpace C).2)
    (P : ((BigFppfOver.toScheme B S hS).obj C).Opens)
    (x y : Γ(((representedModuleSiteEquivalence B S hS C).inverse ⋙
          _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj C) C.left.property).obj N, P))
    (h : (x : (N.val.obj (op (representedOpensObj B S hS C P)))) = y) : x = y := h

/-- **The join of the two spellings.**  An equation of sections of the Zariski restriction of `N`
over `P`, followed by an equation read over
`AlgebraicGeometry.Space.representedOpensObj C P`, is an equation of the first kind.

This is `Eq.trans` with the one crossing between the two spellings performed here, on variables,
instead of at the point of use, where it does not fit the heartbeat budget. -/
theorem eq_trans_representedOpensObj
    (N : Modules.{u, u} B S hS (schemeSpace C).1 (schemeSpace C).2)
    (P : ((BigFppfOver.toScheme B S hS).obj C).Opens)
    (x y z : Γ(((representedModuleSiteEquivalence B S hS C).inverse ⋙
          _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj C) C.left.property).obj N, P))
    (h₁ : x = y) (h₂ : (y : (N.val.obj (op (representedOpensObj B S hS C P)))) = z) : x = z :=
  h₁.trans h₂

/-- **The bridge in the other direction.**  An equation of sections of the Zariski restriction of
`N` over `P`, read as an equation of sections of `N` over
`AlgebraicGeometry.Space.representedOpensObj C P`.  This is the direction a chain needs when a
step computed in the Zariski spelling has to be carried under a morphism of `N`. -/
theorem eq_representedOpensObj_of_eq
    (N : Modules.{u, u} B S hS (schemeSpace C).1 (schemeSpace C).2)
    (P : ((BigFppfOver.toScheme B S hS).obj C).Opens)
    (x y : Γ(((representedModuleSiteEquivalence B S hS C).inverse ⋙
          _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj C) C.left.property).obj N, P))
    (h : x = y) : (x : (N.val.obj (op (representedOpensObj B S hS C P)))) = y := h

/-- **The join whose target is already a section over
`AlgebraicGeometry.Space.representedOpensObj`.**
`AlgebraicGeometry.Space.eq_trans_representedOpensObj`
with the right-hand end taken in the space-side spelling rather than the Zariski one, which is
what a chain needs when it continues in that spelling instead of coming back. -/
theorem eq_representedOpensObj_trans
    (N : Modules.{u, u} B S hS (schemeSpace C).1 (schemeSpace C).2)
    (P : ((BigFppfOver.toScheme B S hS).obj C).Opens)
    (x y : Γ(((representedModuleSiteEquivalence B S hS C).inverse ⋙
          _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj C) C.left.property).obj N, P))
    (z : (N.val.obj (op (representedOpensObj B S hS C P))))
    (h₁ : x = y) (h₂ : (y : (N.val.obj (op (representedOpensObj B S hS C P)))) = z) :
    (x : (N.val.obj (op (representedOpensObj B S hS C P)))) = z := h₁.trans h₂

/-- **Carrying an equation of sections under a morphism, over
`AlgebraicGeometry.Space.representedOpensObj`.**  `congrArg` for the action of a morphism of
modules on the small étale site of `yoneda.obj C` on sections over the object an open cuts out.

Stated with the two modules as variables: a `congrArg` written out at the concrete morphism of the
square of Stacks 04CS is a `(deterministic) timeout at whnf`, because the morphism's source is an
`abbrev` which the elaborator unfolds while matching the function's domain against the equation's
type. -/
theorem congrArg_val_app_representedOpensObj {C : BigFppfOver B S hS}
    {N N' : Modules.{u, u} B S hS (schemeSpace C).1 (schemeSpace C).2} (h : N ⟶ N')
    (P : ((BigFppfOver.toScheme B S hS).obj C).Opens)
    {x y : (N.val.obj (op (representedOpensObj B S hS C P)))} (e : x = y) :
    (h.val.app (op (representedOpensObj B S hS C P))).hom x =
      (h.val.app (op (representedOpensObj B S hS C P))).hom y :=
  congrArg ((h.val.app (op (representedOpensObj B S hS C P))).hom) e

/-- **The same, for an equation of sections read in the Zariski spelling.**  This is
`AlgebraicGeometry.Space.congrArg_val_app_representedOpensObj` with the two sections presented as
sections of the Zariski restriction of `N` over `P`, which is the spelling the links of the
Zariski chain leave them in; the one crossing between the spellings is paid here, on variables. -/
theorem congrArg_val_app_representedOpensObj_of_zariski {C : BigFppfOver B S hS}
    {N N' : Modules.{u, u} B S hS (schemeSpace C).1 (schemeSpace C).2} (h : N ⟶ N')
    (P : ((BigFppfOver.toScheme B S hS).obj C).Opens)
    {x y : Γ(((representedModuleSiteEquivalence B S hS C).inverse ⋙
          _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj C) C.left.property).obj N, P)}
    (e : x = y) :
    (h.val.app (op (representedOpensObj B S hS C P))).hom x =
      (h.val.app (op (representedOpensObj B S hS C P))).hom y :=
  congrArg ((h.val.app (op (representedOpensObj B S hS C P))).hom) e

end Bridges

/-- **The last two links of the Zariski side of the sections identity of Stacks 04CS, in the
space-side spelling.**  `AlgebraicGeometry.Space.zariskiChain_unit_representedUniversalDerivation`
with the type of its two sides written out as the sections of
`AlgebraicGeometry.Space.representedRelativeDifferentials` of `α` over
`AlgebraicGeometry.Space.representedOpensObj C P`.

The ascription is affordable here — it is the crossing
`AlgebraicGeometry.Space.zariskiChain_unit_representedUniversalDerivation` already performs
internally — and it is what lets the rest of the chain be carried in the spelling the spaces side
of the square lives in, rather than in the Zariski one. -/
theorem spaceChain_unit_representedUniversalDerivation {C D : BigFppfOver B S hS} (α : C ⟶ D)
    (P : ((BigFppfOver.toScheme B S hS).obj C).Opens)
    (a : Γ(((BigFppfOver.toScheme B S hS).obj C), P)) :
    ((((representedModuleSiteEquivalence B S hS C).unit.app
              ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj C) C.left.property).obj
                (Scheme.Hom.relativeDifferentials
                  ((BigFppfOver.toScheme B S hS).map α)))).val.app
            (op (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj C) C.left.property P))).hom
          ((representedAssociatedDerivation B S hS α).d
              (X := op (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj C) C.left.property P))
            (((_root_.AlgebraicGeometry.SmallEtale.commRingStructureMap (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj C) C.left.property).hom.app (op P)).hom a)) :
        ((representedRelativeDifferentials B S hS α).val.obj
          (op (representedOpensObj B S hS C P)))) =
      (representedUniversalDerivation B S hS α).d
          (X := op (representedOpensObj B S hS C P))
        ((_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj C) C.left.property).obj.map
          ((representedSmallEtaleEquivalence B S hS C).counit.app
            (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj C) C.left.property P)).op
          (((_root_.AlgebraicGeometry.SmallEtale.commRingStructureMap (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj C) C.left.property).hom.app (op P)).hom a)) :=
  zariskiChain_unit_representedUniversalDerivation B S hS α P a


section Square

variable {U V W : BigFppfOver B S hS}

/-- **The `k` half of the spaces side of the sections identity of Stacks 04CS.**  The transpose
across the transported associated-module adjunction of `V` of the comparison map of Stacks 04CS of
`χ` followed by the transpose of the comparison map of Stacks 04CX, read over an open `O` of the
scheme underlying `V` on the universal differential `d_{V/W}(a)`, is the direct image along `ψ̃` of
the canonical derivation `d^a` of `ψ ≫ χ`, evaluated on the pullback of `a`.

Six links: `AlgebraicGeometry.Space.app_homEquiv_representedAssociatedModuleAdjunction` and
`AlgebraicGeometry.Space.representedRestrictModule_map_app_apply` split the transpose, the four
general links of the Zariski chain at `α = χ` and the open `O` — the last two through
`AlgebraicGeometry.Space.spaceChain_unit_representedUniversalDerivation` — identify the unit on
`d_{V/W}(a)` with `d^a` of `χ`, and
`AlgebraicGeometry.Space.representedDifferentialsComparison_comp_homEquiv_
representedUniversalDerivation`
evaluates the arrow on it. -/
theorem spaceChain_homEquiv_representedDifferentialsComparison (ψ : U ⟶ V) (χ : V ⟶ W)
    (O : ((BigFppfOver.toScheme B S hS).obj V).Opens)
    (a : Γ(((BigFppfOver.toScheme B S hS).obj V), O)) :
    ((representedAssociatedModuleAdjunction B S hS V).homEquiv
          (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map χ))
          ((modulePushforward B S hS (schemeSpaceMap ψ)).obj
            ((representedAssociatedModule B S hS U (schemeSpace U).property).obj
              (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map (ψ ≫ χ)))))
          (representedDifferentialsComparison B S hS χ ≫
            (modulePullbackAdjunction B S hS (schemeSpaceMap ψ)).homEquiv
              (sheafOfDifferentials B S hS (schemeSpaceMap χ))
              ((representedAssociatedModule B S hS U (schemeSpace U).property).obj
                (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map (ψ ≫ χ))))
              (pullbackDifferentialsMap B S hS (schemeSpaceMap ψ) (schemeSpaceMap χ) ≫
                (sheafOfDifferentialsRepresentedIso B S hS (ψ ≫ χ)).hom))).app O
        ((Scheme.Hom.universalRelativeDerivation ((BigFppfOver.toScheme B S hS).map χ)).d a) =
      (((smallEtaleDirectImage B S hS (schemeSpaceMap ψ)).map
            (representedUniversalDerivationHom B S hS (ψ ≫ χ))).hom.app
          (op (representedOpensObj B S hS V O)))
        (((structureSharpSet B S hS (schemeSpaceMap ψ)).hom.app
            (op (representedOpensObj B S hS V O)))
          (((_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj V) V.left.property).obj.map
              ((representedSmallEtaleEquivalence B S hS V).counit.app
                (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
                  ((BigFppfOver.toScheme B S hS).obj V) V.left.property O)).op)
            ((((_root_.AlgebraicGeometry.SmallEtale.commRingStructureMap (associatedBigEtaleSite B)
                  ((BigFppfOver.toScheme B S hS).obj V) V.left.property).hom.app
                  (op O)).hom a)))) := by
  generalize hf : (representedDifferentialsComparison B S hS χ ≫
    (modulePullbackAdjunction B S hS (schemeSpaceMap ψ)).homEquiv
      (sheafOfDifferentials B S hS (schemeSpaceMap χ))
      ((representedAssociatedModule B S hS U (schemeSpace U).property).obj
        (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map (ψ ≫ χ))))
      (pullbackDifferentialsMap B S hS (schemeSpaceMap ψ) (schemeSpaceMap χ) ≫
        (sheafOfDifferentialsRepresentedIso B S hS (ψ ≫ χ)).hom)) = f
  have sA := app_homEquiv_representedAssociatedModuleAdjunction B S hS V
    (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map χ))
    f
    O ((Scheme.Hom.universalRelativeDerivation ((BigFppfOver.toScheme B S hS).map χ)).d a)
  have sB := representedRestrictModule_map_app_apply B S hS V
    f
    O (((representedAssociatedModuleAdjunction B S hS V).unit.app
        (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map χ))).app O
      ((Scheme.Hom.universalRelativeDerivation ((BigFppfOver.toScheme B S hS).map χ)).d a))
  have sAB := sA.trans sB
  have hz := (zariskiChain_representedAssociatedModuleAdjunction_unit B S hS χ O a).trans
    (zariskiChain_associatedModuleAdjunction_unit_d B S hS χ O a)
  have hc1 := congrArg_val_app_representedOpensObj_of_zariski B S hS f O hz
  have hc2 := congrArg_val_app_representedOpensObj B S hS f O
    (spaceChain_unit_representedUniversalDerivation B S hS χ O a)
  have hcarry := hc1.trans hc2
  have sABC := eq_representedOpensObj_trans B S hS
    ((modulePushforward B S hS (schemeSpaceMap ψ)).obj
      (representedRelativeDifferentials B S hS (ψ ≫ χ))) O _ _ _ sAB hcarry
  have hG := representedDifferentialsComparison_comp_homEquiv_representedUniversalDerivation
    B S hS ψ χ (op (representedOpensObj B S hS V O))
    ((_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj V) V.left.property).obj.map
      ((representedSmallEtaleEquivalence B S hS V).counit.app
        (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj V) V.left.property O)).op
      (((_root_.AlgebraicGeometry.SmallEtale.commRingStructureMap (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj V) V.left.property).hom.app (op O)).hom a))
  subst hf
  exact sABC.trans hG



/-- **The spaces side of the sections identity of Stacks 04CS, reduced to the chart comparison and
the tail of Stacks 03LC (1).**  The transposed spaces side, read over an open `O` of the scheme
underlying `V` on the universal differential `d_{V/W}(a)`, is the three remaining factors of the
inverse of `AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso` applied to the direct
image along `ψ̃` of the canonical derivation `d^a` of `ψ ≫ χ`.

Three steps: `AlgebraicGeometry.Scheme.Modules.comp_app_apply` splits the comparison off,
`AlgebraicGeometry.Space.spaceChain_homEquiv_representedDifferentialsComparison` computes the
other factor, and
`AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso_inv_app_proj_chartFirst` splits
the comparison three ways at the projection `fun m => m.app O z` — the section being one of the
comparison's own source, which is the projection that keeps the split within budget once the
other factor has already been rewritten. -/
theorem spaceChain_chartFirst (ψ : U ⟶ V) (χ : V ⟶ W)
    (O : ((BigFppfOver.toScheme B S hS).obj V).Opens)
    (a : Γ(((BigFppfOver.toScheme B S hS).obj V), O)) :
    (((representedAssociatedModuleAdjunction B S hS V).homEquiv
          (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map χ))
          ((modulePushforward B S hS (schemeSpaceMap ψ)).obj
            ((representedAssociatedModule B S hS U (schemeSpace U).property).obj
              (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map (ψ ≫ χ)))))
          (representedDifferentialsComparison B S hS χ ≫
            (modulePullbackAdjunction B S hS (schemeSpaceMap ψ)).homEquiv
              (sheafOfDifferentials B S hS (schemeSpaceMap χ))
              ((representedAssociatedModule B S hS U (schemeSpace U).property).obj
                (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map (ψ ≫ χ))))
              (pullbackDifferentialsMap B S hS (schemeSpaceMap ψ) (schemeSpaceMap χ) ≫
                (sheafOfDifferentialsRepresentedIso B S hS (ψ ≫ χ)).hom))) ≫
          (representedRestrictModuleBaseChangeIso B S hS ψ).inv.app
            (representedRelativeDifferentials B S hS (ψ ≫ χ))).app O
        ((Scheme.Hom.universalRelativeDerivation ((BigFppfOver.toScheme B S hS).map χ)).d a) =
      (((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
            ((representedSmallEtaleModuleEquivalence B S hS V).inverse.map
              ((modulePushforwardChartIso B S hS (representedSpaceMap B S hS ψ)
                (relativelyRepresentable_yoneda_map B S hS ψ)).hom.app
                  (representedRelativeDifferentials B S hS (ψ ≫ χ)))) ≫
          (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
                  ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
                ((representedSmallEtaleModuleEquivalence B S hS V).inverse.map
                    ((smallBaseChangeModulePushforward.{u, u} B S hS
                            (representedSpaceMap B S hS ψ)
                            (relativelyRepresentable_yoneda_map B S hS ψ)).map
                          ((representedSmallEtaleModuleEquivalence B S hS U).counitInv.app
                            (representedRelativeDifferentials B S hS (ψ ≫ χ))) ≫
                      (representedModulePushforwardSquareRestrictIso B S hS ψ
                            (relativelyRepresentable_yoneda_map B S hS ψ)).inv.app
                          ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj
                            (representedRelativeDifferentials B S hS (ψ ≫ χ)))) ≫
                  (representedModulePushforwardSquareInverseIsoUnit B S hS ψ).inv.app
                    (representedRelativeDifferentials B S hS (ψ ≫ χ))) ≫
            (representedRestrictModuleBaseChangeIsoBaseChange B S hS ψ).inv.app
              (representedRelativeDifferentials B S hS (ψ ≫ χ)))).app O
        ((((smallEtaleDirectImage B S hS (schemeSpaceMap ψ)).map
              (representedUniversalDerivationHom B S hS (ψ ≫ χ))).hom.app
            (op (representedOpensObj B S hS V O)))
          (((structureSharpSet B S hS (schemeSpaceMap ψ)).hom.app
              (op (representedOpensObj B S hS V O)))
            (((_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf
                  (associatedBigEtaleSite B)
                  ((BigFppfOver.toScheme B S hS).obj V) V.left.property).obj.map
                ((representedSmallEtaleEquivalence B S hS V).counit.app
                  (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
                    ((BigFppfOver.toScheme B S hS).obj V) V.left.property O)).op)
              ((((_root_.AlgebraicGeometry.SmallEtale.commRingStructureMap
                    (associatedBigEtaleSite B)
                    ((BigFppfOver.toScheme B S hS).obj V) V.left.property).hom.app
                  (op O)).hom a))))) := by
  have h1 := Scheme.Modules.comp_app_apply
    ((representedAssociatedModuleAdjunction B S hS V).homEquiv
          (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map χ))
          ((modulePushforward B S hS (schemeSpaceMap ψ)).obj
            ((representedAssociatedModule B S hS U (schemeSpace U).property).obj
              (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map (ψ ≫ χ)))))
          (representedDifferentialsComparison B S hS χ ≫
            (modulePullbackAdjunction B S hS (schemeSpaceMap ψ)).homEquiv
              (sheafOfDifferentials B S hS (schemeSpaceMap χ))
              ((representedAssociatedModule B S hS U (schemeSpace U).property).obj
                (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map (ψ ≫ χ))))
              (pullbackDifferentialsMap B S hS (schemeSpaceMap ψ) (schemeSpaceMap χ) ≫
                (sheafOfDifferentialsRepresentedIso B S hS (ψ ≫ χ)).hom)))
    ((representedRestrictModuleBaseChangeIso B S hS ψ).inv.app
      (representedRelativeDifferentials B S hS (ψ ≫ χ))) O
    ((Scheme.Hom.universalRelativeDerivation ((BigFppfOver.toScheme B S hS).map χ)).d a)
  have h2 := congrArg (fun z =>
      ((representedRestrictModuleBaseChangeIso B S hS ψ).inv.app
        (representedRelativeDifferentials B S hS (ψ ≫ χ))).app O z)
    (spaceChain_homEquiv_representedDifferentialsComparison B S hS ψ χ O a)
  have h3 := representedRestrictModuleBaseChangeIso_inv_app_proj_chartFirst B S hS ψ
    (representedRelativeDifferentials B S hS (ψ ≫ χ))
    (fun m => m.app O ((((smallEtaleDirectImage B S hS (schemeSpaceMap ψ)).map
              (representedUniversalDerivationHom B S hS (ψ ≫ χ))).hom.app
            (op (representedOpensObj B S hS V O)))
          (((structureSharpSet B S hS (schemeSpaceMap ψ)).hom.app
              (op (representedOpensObj B S hS V O)))
            (((_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf
                  (associatedBigEtaleSite B)
                  ((BigFppfOver.toScheme B S hS).obj V) V.left.property).obj.map
                ((representedSmallEtaleEquivalence B S hS V).counit.app
                  (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
                    ((BigFppfOver.toScheme B S hS).obj V) V.left.property O)).op)
              ((((_root_.AlgebraicGeometry.SmallEtale.commRingStructureMap
                    (associatedBigEtaleSite B)
                    ((BigFppfOver.toScheme B S hS).obj V) V.left.property).hom.app
                  (op O)).hom a))))))
  exact h1.trans (h2.trans h3)

end Square

end AlgebraicGeometry.Space

end
