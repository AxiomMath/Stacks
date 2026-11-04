module

public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.FunctorialFirstQuadrantAbutment
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Filtered abutments of first-quadrant spectral sequences, non-functorially

`Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo` is the *functorial*
filtered abutment of a first-quadrant `E₂` cohomological spectral sequence, carried by
`CategoryTheory.FilteredObject`.  This file supplies its non-functorial companion
`FirstQuadrantAbutsTo`: the same finite decreasing filtration
`H^n = F^0H^n ⊇ F^1H^n ⊇ ⋯ ⊇ F^{n+1}H^n = 0` with graded pieces the terms of the infinity page,
for a single spectral sequence and a single graded abutment.

Two shapes for the same notion already sit in the tree and neither is this one.
`Stacks.Cohomology.Leray.FirstQuadrantAbutment` carries
the filtration as a raw family of steps and inclusions `obj n p`, `ι n p`, and expresses the
graded pieces as literal cokernels; it is the shape the five-term exact sequence of
[Stacks, Tag 01F2] is proved against.  `FunctorialFirstQuadrantAbutsTo` carries a
`FilteredObject`-valued *functor*.  The shape wanted by a consumer that has one spectral
sequence in hand but still wants `FilteredObject`'s bundled filtration API -- notably the
abutment clause of [Stacks, Tag 03AZ], the Čech-to-cohomology spectral sequence -- is the
`FilteredObject`-based filtration taken at a single object, which is what is defined here.

The three shapes are connected in both directions: `FunctorialFirstQuadrantAbutsTo.obj`
evaluates a functorial abutment at an object of the parameter category, and
`FirstQuadrantAbutsTo.toFirstQuadrantAbutment` unbundles a `FilteredObject` filtration into the
raw family, so the five-term exact sequence applies.  Their composite is
`FunctorialFirstQuadrantAbutsTo.toFirstQuadrantAbutment`, which was already available directly;
`FunctorialFirstQuadrantAbutsTo.obj_toFirstQuadrantAbutment` records that the two routes agree.

## Main definitions

* `Stacks.Cohomology.Leray.FirstQuadrantAbutsTo`: a finite filtered abutment of a
  first-quadrant `E₂` cohomological spectral sequence, with the filtration carried by
  `CategoryTheory.FilteredObject A ℤᵒᵖ`.
* `Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.obj`: the abutment at an individual
  object of the parameter category of a functorial abutment.
* `Stacks.Cohomology.Leray.FirstQuadrantAbutsTo.toFirstQuadrantAbutment`: the raw
  step-and-inclusion form of the filtration, to which the five-term exact sequence of
  [Stacks, Tag 01F2] applies.
* `Stacks.Cohomology.Leray.FirstQuadrantAbutsTo.ofIsoAbutment`: transport of an abutment along
  an isomorphism of the abutment.

## Main results

* `Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.obj_toFirstQuadrantAbutment`:
  unbundling the abutment at an object of a functorial abutment gives the same raw abutment as
  restricting the functorial one directly.

## Implementation notes

**The `hasPageInfinityAt` field is redundant and is kept deliberately.**  A first-quadrant
cohomological spectral sequence has an infinity page at every bidegree, by the instance
`CategoryTheory.SpectralSequence.CohomologicalSpectralSequenceNat.instHasPageInfinityAt` of
`StacksCore/Algebra/Homology/SpectralSequence/PageInfinity.lean`, so the field can always be
discharged by `inferInstance` and `FunctorialFirstQuadrantAbutsTo` omits it.  It is retained
here because the consumers of this structure read the stabilisation off the abutment datum
rather than re-deriving it from the shape of the index category, and because a structure
recording convergence ought to say that the sequence converges.

`isTop` and `isBot` are stated as equalities of `Subobject`s rather than as `IsIso` of the
inclusion and `IsZero` of the step, matching
`Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo`; `Filtration.subobject_eq_top_iff` and
`Filtration.subobject_eq_bot_iff` convert, and `toFirstQuadrantAbutment` is where that
conversion happens.

## References

* [Stacks Project, Tag 01F6](https://stacks.math.columbia.edu/tag/01F6)
* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
* [Stacks Project, Tag 0121](https://stacks.math.columbia.edu/tag/0121)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology.Leray

variable {D A : Type*} [Category* D] [Category* A] [Abelian A]

/-- A finite filtered abutment of a first-quadrant `E₂` cohomological spectral sequence `E` by a
graded object `H`: a finite decreasing filtration
`H^n = F^0H^n ⊇ F^1H^n ⊇ ⋯ ⊇ F^{n+1}H^n = 0` of each `H^n`, carried by
`CategoryTheory.FilteredObject A ℤᵒᵖ`, whose graded pieces are the terms of the infinity page of
`E`, `gr^pH^{p+q} ≅ E_∞^{p,q}`.

This is the non-functorial companion of `FunctorialFirstQuadrantAbutsTo`, and differs from
`FirstQuadrantAbutment` only in carrying the filtration as a bundled filtered object rather than
as a raw family of steps and inclusions; `toFirstQuadrantAbutment` passes between them. -/
@[ega "0 11.1.1" "(e), special case"]
structure FirstQuadrantAbutsTo (E : E₂CohomologicalSpectralSequenceNat A) (H : ℕ → A) where
  /-- The spectral sequence stabilizes at every bidegree. -/
  hasPageInfinityAt (p q : ℕ) : E.HasPageInfinityAt (p, q)
  /-- The filtration of the abutment in each total degree. -/
  filtration (n : ℕ) : FilteredObject A ℤᵒᵖ
  /-- The underlying object of the filtration is the asserted abutment. -/
  abutmentIso (n : ℕ) : (filtration n).X ≅ H n
  /-- The filtration of every abutment object is finite. -/
  isFinite (n : ℕ) : Filtration.IsFinite (filtration n).filtration
  /-- In total degree `n`, the zeroth filtration step is the whole abutment. -/
  isTop (n : ℕ) :
    (filtration n).filtration.subobject (op (0 : ℤ)) = ⊤
  /-- In total degree `n`, the `(n + 1)`-st filtration step is zero. -/
  isBot (n : ℕ) :
    (filtration n).filtration.subobject (op ((n : ℤ) + 1)) = ⊥
  /-- The infinity term is the corresponding associated graded object. -/
  gradedIso (p q : ℕ) :
    E.pageInfinity (p, q) ≅
      (FilteredObject.gr (p : ℤ)).obj (filtration (p + q))

namespace FunctorialFirstQuadrantAbutsTo

variable {E : D ⥤ E₂CohomologicalSpectralSequenceNat A} {H : ℕ → D ⥤ A}

/-- **The filtered abutment at an individual object of the parameter category.**  Every field is
the corresponding field of the functorial abutment evaluated at `K`; `hasPageInfinityAt` is the
instance carried by every first-quadrant cohomological spectral sequence, which is why the
functorial structure does not record it.

The field `gradedIso_naturality` is discarded: it relates the graded identifications at
different objects of `D`, and there is nothing for it to say at a single one. -/
def obj (h : FunctorialFirstQuadrantAbutsTo E H) (K : D) :
    FirstQuadrantAbutsTo (E.obj K) (fun n ↦ (H n).obj K) where
  hasPageInfinityAt _ _ := inferInstance
  filtration n := (h.filtration n).obj K
  abutmentIso n := (h.abutmentIso n).app K
  isFinite n := h.isFinite K n
  isTop n := h.isTop K n
  isBot n := h.isBot K n
  gradedIso p q := h.gradedIso K p q

/-- The filtered abutment in total degree `n` of the abutment at `K` is the filtered abutment
in total degree `n` of the functorial abutment, evaluated at `K`. -/
@[simp]
lemma obj_filtration (h : FunctorialFirstQuadrantAbutsTo E H) (K : D) (n : ℕ) :
    (h.obj K).filtration n = (h.filtration n).obj K :=
  rfl

end FunctorialFirstQuadrantAbutsTo

namespace FirstQuadrantAbutsTo

variable {E : E₂CohomologicalSpectralSequenceNat A} {H : ℕ → A}

/-- **A `FilteredObject`-carried abutment unbundles to a raw one.**  The filtration steps are the
steps of the filtered object `F^•H^n` at the non-negative integers, the top step is the whole
abutment because the zeroth step is, the bottom step vanishes because the `(n + 1)`-st step
does, and the graded identification is the one carried by the abutment -- `FilteredObject.gr p`
is the cokernel of the step `F^{p+1} ⟶ F^p` by definition of `FilteredObject.grMap`.

Consequently the five-term exact sequence of `FirstQuadrantAbutment` -- `inflation`,
`restriction`, `transgression` with `mono_inflation`, `exact_inflation_restriction`,
`exact_restriction_d` and `exact_d_transgression` -- applies to every abutment of this shape. -/
def toFirstQuadrantAbutment (h : FirstQuadrantAbutsTo E H) :
    FirstQuadrantAbutment E H where
  obj n p := (h.filtration n).filtration.obj (op (p : ℤ))
  ι n p := (h.filtration n).filtration.step (FilteredObject.succHom (p : ℤ))
  mono_ι _ _ := inferInstance
  topIso n :=
    have : IsIso ((h.filtration n).filtration.ι.app (op (0 : ℤ))) :=
      (Filtration.subobject_eq_top_iff _ _).1 (h.isTop n)
    asIso ((h.filtration n).filtration.ι.app (op (0 : ℤ))) ≪≫ h.abutmentIso n
  isZero_bot n := ((Filtration.subobject_eq_bot_iff _ _).1 (h.isBot n)).some.isZero
  gradedIso p q := h.gradedIso p q

/-- **An abutment transports along an isomorphism of the abutment.**  The structure mentions `H`
in the single field `abutmentIso`, so replacing `H` by an isomorphic graded object changes
nothing else: the filtration, its finiteness, its top and bottom steps and the graded
identification are all independent of `H`.

This is what lets the abutment be built against the cohomology that the filtration is literally
the filtration *of*, and the asserted abutment be substituted at the end. -/
def ofIsoAbutment (h : FirstQuadrantAbutsTo E H) {H' : ℕ → A} (e : ∀ n, H n ≅ H' n) :
    FirstQuadrantAbutsTo E H' :=
  { h with abutmentIso n := h.abutmentIso n ≪≫ e n }

/-- The filtration of a transported abutment is the original one. -/
@[simp]
lemma ofIsoAbutment_filtration (h : FirstQuadrantAbutsTo E H) {H' : ℕ → A}
    (e : ∀ n, H n ≅ H' n) (n : ℕ) : (h.ofIsoAbutment e).filtration n = h.filtration n :=
  rfl

end FirstQuadrantAbutsTo

/-- Unbundling the abutment at an object `K` of a functorial abutment gives the same raw
abutment as restricting the functorial abutment to `K` directly: both routes read the same
fields off the same functorial data. -/
theorem FunctorialFirstQuadrantAbutsTo.obj_toFirstQuadrantAbutment
    {E : D ⥤ E₂CohomologicalSpectralSequenceNat A} {H : ℕ → D ⥤ A}
    (h : FunctorialFirstQuadrantAbutsTo E H) (K : D) :
    (h.obj K).toFirstQuadrantAbutment = h.toFirstQuadrantAbutment K :=
  rfl

end Stacks.Cohomology.Leray

end
