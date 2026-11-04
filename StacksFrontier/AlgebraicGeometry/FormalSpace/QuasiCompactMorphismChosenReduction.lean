module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.GeneralReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphismReductions
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Recompletion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionSmoothBaseChange

/-!
# Condition (1) of Stacks 0AJB at the chosen reductions

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of formal
algebraic spaces over `S`. Condition (1) of **Stacks 0AJB** is that the induced morphism
`f_red : X_red ⟶ Y_red` of reductions be a quasi-compact morphism of algebraic spaces. Stacks
0AIN, the existence of the reduction of a formal algebraic space, is available in this library in
general — `AlgebraicGeometry.FormalSpace.reduction` is the chosen reduction — so `f_red` is a
morphism this library can name, and that is what this file does: `f_red` is the morphism of the
chosen reductions of `X` and of `Y` induced by `f`.

`AlgebraicGeometry.FormalSpace.IsQuasiCompactOnReductions`, condition (1) with the two reductions
and the morphism between them quantified over, is equivalent to quasi-compactness of that one
morphism, because two reductions of one sheaf are isomorphic over it and the induced morphisms of
reductions correspond under those isomorphisms. The two phrasings of condition (1) therefore say
the same thing, and the implications of Stacks 0AJB already proved for the quantified phrasing
hold for `f_red` itself.

## Main definitions

* `AlgebraicGeometry.FormalSpace.chosenReductionMap`: the morphism `f_red : X_red ⟶ Y_red` of the
  chosen reductions induced by a morphism `f : X ⟶ Y` of formal algebraic spaces over `S`.

## Main results

* `FormalSpace.isQuasiCompactOnReductions_iff_isQuasiCompactULift_chosenReductionMap`:
  **Stacks 0AJB**, condition (1), in the source's own form — quasi-compactness of `f_red` — and
  its identification with the phrasing that quantifies over the reductions.
* `FormalSpace.IsQuasiCompact.isQuasiCompactULift_chosenReductionMap`:
  **Stacks 0AJB**, the implication condition (3) ⇒ condition (1) for `f_red`.
* `FormalSpace.IsQuasiCompactOnSchemeBaseChanges.isQuasiCompactULift_chosenReductionMap`:
  **Stacks 0AJB**, the implication condition (2) ⇒ condition (1) for `f_red`.

## What is assumed

Nothing. The chosen reduction is `AlgebraicGeometry.FormalSpace.reduction`, which is Stacks 0AIN
for a general formal algebraic space, and the morphism between two given reductions is
`AlgebraicGeometry.FormalSpace.reductionMap`, the factorisation supplied by the universal
property of the target's reduction.

The implications not proved here are proved, with the four conditions assembled into one
`List.TFAE`, in `StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphismTFAE`: condition
(4) implies condition (3) by refining the covering, along a point `T ⟶ Y` with `T` affine, to
finitely many *affine* objects of the site étale over `T` (Stacks 0AIG makes the base changes of
the members objects of the site), over each of which the fibre product has a single affine formal
chart by Stacks 0AN3 clause (1). No form of Stacks 0AJ3 or Stacks 0AIU is used: the fibre product
`X ×_Y T` is shown to be a formal algebraic space by exhibiting that chart, not by a colimit
argument. With (1) ⇒ (4) this gives (1) ⇒ (3), and (3) ⇒ (1) closes the cycle.

## Implementation notes

Quasi-compactness of `f_red` is `AlgebraicGeometry.Space.IsQuasiCompactULift`, the condition of
Stacks 03HE for a value universe independent of the universe of the schemes, since a formal
algebraic space is a sheaf of `Type (u + 1)` and so its reduction is an algebraic space with
values in that universe.

The chosen reduction is packaged as `AlgebraicGeometry.FormalSpace.Reduction`, whose underlying
algebraic space lives in `AlgebraicGeometry.AlgebraicSpaces`; `f_red` is therefore stated as a
morphism of the fppf sheaves `AlgebraicGeometry.FormalSpace.liftSheaf` of those algebraic spaces,
which is the shape `AlgebraicGeometry.FormalSpace.IsQuasiCompactOnReductions` quantifies over.

## References

* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0AJ9](https://stacks.math.columbia.edu/tag/0AJ9)
* [Stacks Project, Tag 0AJB](https://stacks.math.columbia.edu/tag/0AJB)
* [Stacks Project, Tag 0AJC](https://stacks.math.columbia.edu/tag/0AJC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The morphism of the chosen reductions -/

/-- The morphism `f_red : X_red ⟶ Y_red` of the chosen reductions induced by a morphism
`f : X ⟶ Y` of formal algebraic spaces over `S`. The chosen reductions are the ones Stacks 0AIN
produces, `AlgebraicGeometry.FormalSpace.reduction`, and the induced morphism is the
factorisation of `X_red ⟶ X ⟶ Y` through the reduction of `Y`. -/
noncomputable def chosenReductionMap {X Y : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    liftSheaf B S hS (reduction B S hS X hX).space ⟶
      liftSheaf B S hS (reduction B S hS Y hY).space :=
  reductionMap (reduction B S hS X hX).isReduction (reduction B S hS Y hY).isReduction f

/-- The morphism of the chosen reductions is compatible with the given morphism. -/
theorem chosenReductionMap_comp {X Y : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    chosenReductionMap B S hS hX hY f ≫ (reduction B S hS Y hY).inclusion
      = (reduction B S hS X hX).inclusion ≫ f :=
  reductionMap_comp (reduction B S hS X hX).isReduction
    (reduction B S hS Y hY).isReduction f

/-! ### Condition (1) of Stacks 0AJB -/

/-- **Stacks 0AJB, condition (1).** Let `f : X ⟶ Y` be a morphism of formal algebraic spaces over
`S`. The morphism `f_red : X_red ⟶ Y_red` of the chosen reductions is a quasi-compact morphism of
algebraic spaces if and only if every morphism between reductions of `X` and of `Y` compatible
with `f` is one. The second condition is
`AlgebraicGeometry.FormalSpace.IsQuasiCompactOnReductions`, the phrasing of condition (1) which
quantifies over the reductions instead of choosing them.

Given reductions `iX : Xred ⟶ X` and `iY : Yred ⟶ Y` and a compatible `fred`, the universal
properties of the chosen reductions supply comparison morphisms `a : Xred ⟶ X_red` and
`b : Yred ⟶ Y_red` over `X` and over `Y`, and these are isomorphisms because two reductions of
one sheaf are isomorphic over it. The inclusion of the reduction of `Y` is a monomorphism, so
`a ≫ f_red = fred ≫ b`, and `fred` is `f_red` conjugated by the two isomorphisms. -/
@[stacks 0AJB "condition (1), in the source's own form — quasi-compactness of the morphism \
f_red of the chosen reductions — identified with the phrasing of the condition that quantifies \
over the reductions"]
theorem isQuasiCompactOnReductions_iff_isQuasiCompactULift_chosenReductionMap
    {X Y : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsQuasiCompactOnReductions B S hS f ↔
      Space.IsQuasiCompactULift.{u + 1} B S hS (chosenReductionMap B S hS hX hY f).hom := by
  refine ⟨fun h => h _ _ (reduction B S hS X hX).inclusion (reduction B S hS Y hY).inclusion
      (reduction B S hS X hX).isReduction (reduction B S hS Y hY).isReduction _
      (chosenReductionMap_comp B S hS hX hY f), fun h Xred Yred iX iY hiX hiY fred hfred => ?_⟩
  obtain ⟨a, ha, -⟩ := (reduction B S hS X hX).isReduction.universal Xred hiX.algebraic
    hiX.reduced iX
  obtain ⟨b, hb, -⟩ := (reduction B S hS Y hY).isReduction.universal Yred hiY.algebraic
    hiY.reduced iY
  have _ : IsIso a :=
    IsReduction.isIso_of_comp_eq B S hS hiX (reduction B S hS X hX).isReduction ha
  have _ : IsIso b :=
    IsReduction.isIso_of_comp_eq B S hS hiY (reduction B S hS Y hY).isReduction hb
  have _ : Mono (reduction B S hS Y hY).inclusion :=
    mono_of_isRepresentableThickening B S hS _
      (reduction B S hS Y hY).isReduction.isRepresentableThickening
  -- the two comparison morphisms intertwine `fred` and `f_red`
  have hsq : a ≫ chosenReductionMap B S hS hX hY f = fred ≫ b := by
    rw [← cancel_mono (reduction B S hS Y hY).inclusion, Category.assoc,
      chosenReductionMap_comp, reassoc_of% ha, Category.assoc, hb, hfred]
  have hfr : fred = a ≫ chosenReductionMap B S hS hX hY f ≫ inv b := by
    rw [← Category.assoc, hsq, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  -- the comparison isomorphisms, read on the underlying presheaves
  let ea := (sheafToPresheaf _ _).mapIso (asIso a)
  let eb := (sheafToPresheaf _ _).mapIso (asIso b).symm
  have hhom : fred.hom = ea.hom ≫ (chosenReductionMap B S hS hX hY f).hom ≫ eb.hom :=
    congrArg (fun k : Xred ⟶ Yred => k.hom) hfr
  rw [hhom]
  exact Space.isQuasiCompactULift_precomp.{u + 1} B S hS ea _
    (Space.isQuasiCompactULift_postcomp.{u + 1} B S hS eb _ h)

/-! ### The implications into condition (1) -/

/-- **Stacks 0AJB, condition (3) implies condition (1).** Let `f : X ⟶ Y` be a morphism of formal
algebraic spaces over `S` such that every fibre product of `f` with an affine scheme over `S` in
the site mapping to `Y` is a quasi-compact formal algebraic space — that is, let `f` be
quasi-compact in the sense of Stacks 0AJC. Then the morphism `f_red : X_red ⟶ Y_red` of the
chosen reductions is a quasi-compact morphism of algebraic spaces. -/
@[stacks 0AJB "condition (3) implies condition (1), for the morphism f_red of the chosen \
reductions"]
theorem IsQuasiCompact.isQuasiCompactULift_chosenReductionMap {X Y : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (h : IsQuasiCompact B S hS f) :
    Space.IsQuasiCompactULift.{u + 1} B S hS (chosenReductionMap B S hS hX hY f).hom :=
  (isQuasiCompactOnReductions_iff_isQuasiCompactULift_chosenReductionMap B S hS hX hY f).mp
    (IsQuasiCompact.isQuasiCompactOnReductions B S hS h)

/-- **Stacks 0AJB, condition (2) implies condition (1).** The fibre product condition over the
quasi-compact schemes over `S` in the site restricts to the affine ones, which already makes the
morphism `f_red` of the chosen reductions a quasi-compact morphism of algebraic spaces. -/
@[stacks 0AJB "condition (2) implies condition (1), for the morphism f_red of the chosen \
reductions"]
theorem IsQuasiCompactOnSchemeBaseChanges.isQuasiCompactULift_chosenReductionMap
    {X Y : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (h : IsQuasiCompactOnSchemeBaseChanges B S hS f) :
    Space.IsQuasiCompactULift.{u + 1} B S hS (chosenReductionMap B S hS hX hY f).hom :=
  IsQuasiCompact.isQuasiCompactULift_chosenReductionMap B S hS hX hY
    (h.isQuasiCompact B S hS)

end AlgebraicGeometry.FormalSpace

end
