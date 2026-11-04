module

public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningPushout
public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionChartCartesian

/-!
# The chart of a square-zero extension as a chart of the site

Let `0 ⟶ ℐ ⟶ 𝒜 ⟶ 𝒪_X ⟶ 0` be a square-zero extension of the structure sheaf of an algebraic
space `X` over `Y`, in the sense of `AlgebraicGeometry.Space.SquareZeroExtension`.  The chart
diagram `AlgebraicGeometry.Space.SquareZeroExtension.chartSpec` sends an affine chart `U` of the
small étale site of `X` to the affine scheme `Spec(𝒜(U))`, inside which `U` is a first-order
thickening.  Before that scheme can be a chart *of an algebraic space* two things are owed, and
this file supplies both.

**Its opens are the opens of `U`.**  The thickening
`AlgebraicGeometry.Space.SquareZeroExtension.chartThickeningOfIsAffine` is a homeomorphism on
underlying spaces, so `Stacks.Thickenings.IsThickening.opensCongr` identifies the opens of `U`
with the opens of `Spec(𝒜(U))`, with taking preimages along the thickening for its inverse.  This
is what matches a Zariski cover of the chart `U` with a Zariski cover of `Spec(𝒜(U))`.

**It is an object of the site.**  An object of `AlgebraicGeometry.BigFppfSite` is a scheme whose
size is below the site's cutoff, so `Spec(𝒜(U))` has to be shown small.
`AlgebraicGeometry.Space.SquareZeroExtension.contains_chartSpec_obj_of_isAffine` propagates the
bound along a basic open but says nothing about where to start, and **nothing in the datum of a
square-zero extension bounds `#𝒜(U)`**: the module `ℐ` is an arbitrary quasi-coherent
`𝒪_X`-module, whose sections carry no cardinality bound at all.  The base case is therefore
stated here with that bound as an explicit hypothesis, in terms of the sections of `ℐ`, which is
the datum's own input.

**That hypothesis is an artefact of this development's cutoff-bounded site, not a hypothesis of
[Stacks Project, Tag 05ZT].**  The source's algebraic spaces are sheaves on a big site whose
objects are *all* schemes, so the question never arises there; here the cutoff is what makes the
big fppf site a site at all (`AlgebraicGeometry.BigPHSite.cutoff`), and a scheme above it is not
an object.  It is not a weakening of the mathematics and it is not hidden: it is named, it is
discharged by nothing, and it is exactly what any construction of the ambient space out of these
charts will have to carry — or else obtain from a bound on `ℐ` imposed when the extension datum
is produced.

## Main definitions

* `AlgebraicGeometry.Space.SquareZeroExtension.chartThickeningOpensCongr`: **the opens of
  `Spec(𝒜(U))` are the opens of the affine chart `U`**, as an order isomorphism.

## Main results

* `AlgebraicGeometry.Space.SquareZeroExtension.preimage_chartThickeningOpensCongr`: its inverse is
  taking preimages along the thickening `U ⟶ Spec(𝒜(U))`.
* `AlgebraicGeometry.Space.SquareZeroExtension.mk_structureSheaf_app_lt_cutoff_of_isAffine`: the
  sections of `𝒪_X` over an affine chart are fewer than the cutoff — the chart is an object of
  the site and over an affine chart it is the spectrum of those sections.
* `AlgebraicGeometry.Space.SquareZeroExtension.mk_app_le_mul_ker_of_isAffine`: over an affine
  chart `#𝒜(U) ≤ #ker(π_U) · #𝒪_X(U)`, the reduction being surjective there.
* `AlgebraicGeometry.Space.SquareZeroExtension.contains_chartSpec_obj_of_mk_ideal_lt_cutoff`:
  **the base case of the cutoff bookkeeping**: if the sections of `ℐ` over an affine chart are
  fewer than the cutoff, then `Spec(𝒜(U))` is an object of the big fppf site.

## Implementation notes

The cardinality estimate is the splitting of the extension as a set: the reduction is surjective
over an affine chart (`…surjective_π_app_of_isAffine`), so choosing a set-theoretic section of it
embeds `𝒜(U)` into `ker(π_U) × 𝒪_X(U)` by `a ↦ (a - s(π_U a), π_U a)`.  The kernel is the
sections of `ℐ` by `…idealAddEquivKer`, and `Cardinal.mul_lt_of_lt` closes the product under the
cutoff, which needs only that the cutoff is uncountable (`AlgebraicGeometry.BigPHSite`'s field
`aleph0_lt_cutoff`) and not the strong-prelimit field.

The bound on `#𝒪_X(U)` is `AlgebraicGeometry.Scheme.size_Spec` applied to
`…structureSheafChartSpecIso`: over an affine chart, `Spec(𝒪_X(U))` is isomorphic to the chart's
own scheme, which is an object of the site, and the size of a spectrum is `max {ℵ₀, #R}`.

**No `@[stacks]` attribute.**  Tag 05ZT concludes that the datum is realized by a first-order
thickening of `X` over `Y`; this file records two properties of one of the charts out of which
that thickening is built.  Nothing here constructs an algebraic space, and the size hypothesis
would in any case not be one of the source's.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R), the cutoff bookkeeping.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace SquareZeroExtension

variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)

/-- **The opens of `Spec(𝒜(U))` are the opens of the affine chart `U`.**

The inclusion `U ⟶ Spec(𝒜(U))` is a first-order thickening by
`AlgebraicGeometry.Space.SquareZeroExtension.isFirstOrderThickening_chartThickening_of_isAffine`,
hence a homeomorphism on underlying spaces, and this is the resulting order isomorphism of
`Stacks.Thickenings.IsThickening.opensCongr`.  Its inverse is taking preimages along the
thickening, which is
`AlgebraicGeometry.Space.SquareZeroExtension.preimage_chartThickeningOpensCongr`. -/
def chartThickeningOpensCongr (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U).Opens ≃o
      ((chartSpec B S hS E).obj U).Opens :=
  Stacks.Thickenings.IsThickening.opensCongr
    (isFirstOrderThickening_chartThickening_of_isAffine B S hS E U hU).isThickening

/-- The open of `Spec(𝒜(U))` matching an open `W` of the affine chart `U` has preimage `W` along
the thickening. -/
theorem preimage_chartThickeningOpensCongr (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U))
    (W : ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U).Opens) :
    chartThickeningOfIsAffine B S hS E U hU ⁻¹ᵁ chartThickeningOpensCongr B S hS E U hU W = W :=
  Stacks.Thickenings.IsThickening.preimage_opensCongr
    (isFirstOrderThickening_chartThickening_of_isAffine B S hS E U hU).isThickening W

/-- **Over an affine chart the sections of the structure sheaf are fewer than the cutoff.**  The
chart's own scheme is an object of the big fppf site, over an affine chart it is isomorphic to
`Spec(𝒪_X(U))` by `AlgebraicGeometry.Space.structureSheafChartSpecIso`, and the size of a
spectrum is `max {ℵ₀, #R}` by `AlgebraicGeometry.Scheme.size_Spec`. -/
theorem mk_structureSheaf_app_lt_cutoff_of_isAffine (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    Cardinal.mk ((smallEtaleRingedTopos B S hS X).O.val.obj (op U)) < B.cutoff := by
  have hle : ((structureSheafChartSpec B S hS X).obj U).size ≤
      ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U).size :=
    Scheme.size_le_of_isOpenImmersion (structureSheafChartSpecIso B S hS X U hU).inv
  have hsize : ((structureSheafChartSpec B S hS X).obj U).size
      = max ℵ₀ (Cardinal.mk ((smallEtaleRingedTopos B S hS X).O.val.obj (op U))) :=
    Scheme.size_Spec _
  exact lt_of_le_of_lt ((le_max_right _ _).trans (hsize.symm.le.trans hle))
    U.obj.left.left.property

/-- **Over an affine chart the extension has at most `#ker(π) · #𝒪_X(U)` sections.**

The reduction is surjective over an affine chart
(`AlgebraicGeometry.Space.SquareZeroExtension.surjective_π_app_of_isAffine`), so a set-theoretic
section `s` of it embeds `𝒜(U)` into `ker(π_U) × 𝒪_X(U)` by `a ↦ (a - s(π_U a), π_U a)`: the
second component determines `s(π_U a)` and the first then determines `a`. -/
theorem mk_app_le_mul_ker_of_isAffine (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    Cardinal.mk (E.A.val.obj (op U)) ≤
      Cardinal.mk (RingHom.ker (E.π.hom.app (op U)).hom) *
        Cardinal.mk ((smallEtaleRingedTopos B S hS X).O.val.obj (op U)) := by
  have hsurj := SquareZeroExtension.surjective_π_app_of_isAffine B S hS E U hU
  classical
  have hinj : Cardinal.mk (E.A.val.obj (op U)) ≤
      Cardinal.mk (RingHom.ker (E.π.hom.app (op U)).hom ×
        (smallEtaleRingedTopos B S hS X).O.val.obj (op U)) := by
    refine mk_le_of_injective (f := fun a => (⟨a - Function.surjInv hsurj
        ((E.π.hom.app (op U)).hom a), RingHom.mem_ker.mpr
        (by rw [map_sub, Function.surjInv_eq hsurj, sub_self])⟩,
      (E.π.hom.app (op U)).hom a)) ?_
    intro a b hab
    have hsnd : (E.π.hom.app (op U)).hom a = (E.π.hom.app (op U)).hom b := congrArg Prod.snd hab
    have hfst : a - Function.surjInv hsurj ((E.π.hom.app (op U)).hom a) =
        b - Function.surjInv hsurj ((E.π.hom.app (op U)).hom b) :=
      congrArg (fun p => (Prod.fst p).1) hab
    rw [hsnd] at hfst
    linear_combination hfst
  simpa [Cardinal.mk_prod] using hinj

/-- **The base case of the cutoff bookkeeping: `Spec(𝒜(U))` is an object of the big fppf site as
soon as the sections of `ℐ` over the affine chart `U` are fewer than the cutoff.**

Together with
`AlgebraicGeometry.Space.SquareZeroExtension.contains_chartSpec_obj_of_isAffine`, which propagates
the bound to the basic opens of `U`, this is the whole of the smallness the charts of the diagram
of [Stacks Project, Tag 05ZT] need.

**The hypothesis `hI` is an artefact of this development's cutoff-bounded big fppf site, not a
hypothesis of the source.**  The sections of `ℐ` over `U` are the kernel of the reduction
(`AlgebraicGeometry.Space.SquareZeroExtension.idealAddEquivKer`) and `ℐ` is an arbitrary
quasi-coherent `𝒪_X`-module, so the datum of a square-zero extension bounds nothing about them;
the source's algebraic spaces live on a big site containing every scheme and never face the
question. -/
theorem contains_chartSpec_obj_of_mk_ideal_lt_cutoff (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hI : Cardinal.mk (E.I.val.obj (op U)) < B.cutoff) :
    B.Contains ((chartSpec B S hS E).obj U) := by
  have hker : Cardinal.mk (RingHom.ker (E.π.hom.app (op U)).hom) < B.cutoff :=
    (mk_congr (SquareZeroExtension.idealAddEquivKer B S hS E (op U)).toEquiv).symm.le.trans_lt hI
  have hA : Cardinal.mk (E.A.val.obj (op U)) < B.cutoff :=
    lt_of_le_of_lt (mk_app_le_mul_ker_of_isAffine B S hS E U hU)
      (Cardinal.mul_lt_of_lt B.aleph0_lt_cutoff.le hker
        (mk_structureSheaf_app_lt_cutoff_of_isAffine B S hS U hU))
  show ((chartSpec B S hS E).obj U).size < B.cutoff
  rw [chartSpec_obj, Scheme.size_Spec]
  exact max_lt B.aleph0_lt_cutoff hA

end SquareZeroExtension

end AlgebraicGeometry.Space

end
