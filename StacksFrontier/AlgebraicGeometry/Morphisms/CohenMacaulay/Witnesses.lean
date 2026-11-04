module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Stalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.RingTheory.CohenMacaulay.OpenLocus

/-!
# Morphisms of schemes that are Cohen–Macaulay: open immersions and the identity

`AlgebraicGeometry.Scheme.Hom.IsCohenMacaulayAt` asks a morphism to be flat at a point and the
local ring of the fibre through that point to be Cohen–Macaulay, and
`AlgebraicGeometry.Scheme.Hom.IsCohenMacaulay` asks this at every point of the source. The
library develops both at length — composition, base change, openness of the locus, restriction
along an open immersion, descent — but each of those results carries Cohen–Macaulayness of
something in its hypotheses, so none of them exhibits a morphism that is Cohen–Macaulay. This
file exhibits one: every open immersion is, and in particular so is the identity of every scheme.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isCohenMacaulayAt_of_isOpenImmersion`: an open immersion is
  Cohen–Macaulay at every point of its source.
* `AlgebraicGeometry.Scheme.Hom.isCohenMacaulay_of_isOpenImmersion`: hence it is a Cohen–Macaulay
  morphism.
* `AlgebraicGeometry.Scheme.Hom.isCohenMacaulay_id`: the identity of a scheme is a Cohen–Macaulay
  morphism. Isomorphisms are covered by the same two results, `IsOpenImmersion` holding for any
  isomorphism.

## What this file inhabits, and the sense in which it is not degenerate

The conclusions are genuine inhabitants of the two morphism-level predicates: the hypotheses are
`IsOpenImmersion i` and, for the identity, nothing at all, and neither mentions depth, dimension
or Cohen–Macaulayness. The quantifier `∀ x : X` is not satisfied by having no points: `𝟙 (Spec R)`
for any nonzero `R` has a source with a point, and `isCohenMacaulay_id` applies to every scheme,
including every nonempty one. What is Cohen–Macaulay here is nevertheless cheap: the fibres of an
open immersion are spectra of fields, so the fibre local rings have dimension `0`, and the content
of the Cohen–Macaulay conjunct is `depth = dim = 0`. A morphism whose fibres have positive
dimension is not produced here.

## Implementation notes

The proof that the fibres are locally Noetherian is taken as an argument rather than pinned to
`isLocallyNoetherian_fiber_of_locallyOfFinitePresentation`, so that a caller may pass whichever
witness its own statement carries; `IsLocallyNoetherian` is a `Prop`-valued class, so the choice
does not affect the statement. That is what makes this statement subsume the pinned form, which
is why `StacksFrontier/AlgebraicGeometry/Groupoids/More/CohenMacaulayLocus.lean` now applies this
theorem instead of carrying its own copy.

Flatness comes from `AlgebraicGeometry.Flat.iff_flat_stalkMap` together with the instance making
an open immersion flat. For the fibre stalk, `i.fiberToSpecResidueField (i x)` is an open immersion
by construction and surjective because `Spec` of a field has one point, hence an isomorphism; the
fibre stalk is therefore the stalk of `Spec (Y.residueField (i x))` at its closed point, which is
`Y.residueField (i x)` itself, a field. A field has Krull dimension zero, and a local ring of
dimension zero is Cohen–Macaulay.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- **An open immersion is Cohen–Macaulay at every point of its source.** It is flat, and its
fibres are spectra of fields, so the local rings of the fibres have Krull dimension zero and are
Cohen–Macaulay for that reason. -/
public theorem isCohenMacaulayAt_of_isOpenImmersion {X Y : Scheme.{u}} (i : X ⟶ Y)
    [IsOpenImmersion i] (hf : ∀ y : Y, IsLocallyNoetherian (i.fiber y)) (x : X) :
    Scheme.Hom.IsCohenMacaulayAt i hf x := by
  show IsFlatAt i.toLRSHom.toShHom x ∧
    IsCohenMacaulayLocalRing ((i.fiber (i x)).presheaf.stalk (i.asFiber x))
  refine ⟨(Flat.iff_flat_stalkMap i).mp inferInstance x, ?_⟩
  let g := i.fiberToSpecResidueField (i x)
  have : IsIso g := by
    have : IsOpenImmersion g := by
      show IsOpenImmersion (pullback.snd i (Y.fromSpecResidueField (i x)))
      infer_instance
    have : Epi g.base :=
      (TopCat.epi_iff_surjective _).mpr fun _ => ⟨i.asFiber x, Subsingleton.elim _ _⟩
    exact IsOpenImmersion.isIso g
  have : IsLocallyNoetherian (i.fiber (i x)) := hf (i x)
  let eCongr : (Spec (Y.residueField (i x))).presheaf.stalk (g (i.asFiber x)) ≅
      (Spec (Y.residueField (i x))).presheaf.stalk
        (IsLocalRing.closedPoint (Y.residueField (i x))) :=
    eqToIso (by rw [i.fiberToSpecResidueField_apply (i x) (i.asFiber x)])
  let e : (i.fiber (i x)).presheaf.stalk (i.asFiber x) ≃+* _ :=
    ((asIso (g.stalkMap (i.asFiber x))).commRingCatIsoToRingEquiv).symm.trans
      eCongr.commRingCatIsoToRingEquiv |>.trans
      (stalkClosedPointIso (Y.residueField (i x))).commRingCatIsoToRingEquiv
  exact (isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay _).mpr
    (Module.isMaximalCohenMacaulay_self_of_ringKrullDim_eq_zero
      ((ringKrullDim_eq_of_ringEquiv e).trans (ringKrullDim_eq_zero_of_field _)))

/-- **An open immersion is a Cohen–Macaulay morphism.** This holds for every open immersion, in
particular for every isomorphism, with no hypothesis on either scheme. -/
public theorem isCohenMacaulay_of_isOpenImmersion {X Y : Scheme.{u}} (i : X ⟶ Y)
    [IsOpenImmersion i] (hf : ∀ y : Y, IsLocallyNoetherian (i.fiber y)) :
    Scheme.Hom.IsCohenMacaulay i hf :=
  fun x => isCohenMacaulayAt_of_isOpenImmersion i hf x

/-- **The identity of a scheme is a Cohen–Macaulay morphism.** Its fibres are the spectra of the
residue fields of the scheme, which have dimension zero. -/
public theorem isCohenMacaulay_id (X : Scheme.{u})
    (hf : ∀ y : X, IsLocallyNoetherian ((𝟙 X : X ⟶ X).fiber y)) :
    Scheme.Hom.IsCohenMacaulay (𝟙 X) hf :=
  isCohenMacaulay_of_isOpenImmersion (𝟙 X) hf

/-- The fibres of the identity of a scheme are locally Noetherian, with no hypothesis on the
scheme: the identity is locally of finite presentation. This discharges the hypothesis of
`AlgebraicGeometry.Scheme.Hom.isCohenMacaulay_id`, so that predicate is inhabited outright. -/
public theorem isLocallyNoetherian_fiber_id (X : Scheme.{u}) (y : X) :
    IsLocallyNoetherian ((𝟙 X : X ⟶ X).fiber y) :=
  isLocallyNoetherian_fiber_of_locallyOfFinitePresentation (𝟙 X) y

end AlgebraicGeometry.Scheme.Hom

end
