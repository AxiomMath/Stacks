module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartwiseConditionsFromSite
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleLocusOpen

/-!
# The flat locus of a module in a triangle of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` whose source and target are given
over a third algebraic space `Z` by `p : X ⟶ Z` and `q : Y ⟶ Z` with `f ≫ q = p`.  If `p` is
locally of finite presentation and `q` is locally of finite type, then the locus of points of
`|X|` at which a module of finite presentation is flat over `Y` is open.

## Main results

* `AlgebraicGeometry.Space.isOpen_flatLocus_of_isLocallyOfFinitePresentation_comp` is the
  openness assertion of **Stacks 05X2**, with the two hypotheses on the module read chartwise.
* `AlgebraicGeometry.Space.isOpen_flatLocus_of_isFinitePresentationOnSite_comp` is the same
  assertion with hypothesis (2) of the source read on the small étale site, which is the reading
  that implies both chartwise ones.

## Implementation notes

Being locally of finite presentation cancels against being locally of finite type, so `f` is
locally of finite presentation and the openness assertion of Stacks 05WV applies.  Flatness of
the module over `Z`, hypothesis (3) of Stacks 05X2, is not needed for openness and is omitted;
it is what the base-change assertion of that lemma rests on.

Stacks 05WV consumes quasi-coherence and finite presentation of the module in their chartwise
readings, `AlgebraicGeometry.Space.IsQuasicoherentOnCharts` and
`AlgebraicGeometry.Space.IsFinitePresentationOnCharts`, which is the only form in which a module
on an algebraic space is compared with a module on a scheme.  Those are the hypotheses of
`AlgebraicGeometry.Space.isOpen_flatLocus_of_isLocallyOfFinitePresentation_comp`.  Both follow
from hypothesis (2) of Stacks 05X2 read on the small étale site, by
`StacksFrontier/AlgebraicGeometry/Spaces/ChartwiseConditionsFromSite.lean`, and
`AlgebraicGeometry.Space.isOpen_flatLocus_of_isFinitePresentationOnSite_comp` asks for that
reading instead.

## References

* [Stacks Project, Tag 05X2](https://stacks.math.columbia.edu/tag/05X2)
* [Stacks Project, Tag 05WV](https://stacks.math.columbia.edu/tag/05WV)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 05X2, the openness assertion.** Let `f : X ⟶ Y` be a morphism of algebraic spaces
over `S` whose source and target are given over an algebraic space `Z` by `p : X ⟶ Z` and
`q : Y ⟶ Z` with `f ≫ q = p`.  If `p` is locally of finite presentation and `q` is locally of
finite type, then the locus of points of `|X|` at which an `𝒪_X`-module which is quasi-coherent
of finite presentation on charts is flat over `Y` is open.

The tag sits on
`AlgebraicGeometry.Space.isOpen_flatLocus_of_isFinitePresentationOnSite_comp`, which is this
assertion with hypothesis (2) of the source read where the source reads it, on the small étale
site; this form is the special case of it at a module whose finite presentation is available
only chartwise. -/
@[stacks 05X2 "openness; hypothesis (3), flatness over the base, is not needed for this half"]
theorem isOpen_flatLocus_of_isLocallyOfFinitePresentation_comp
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z) (hfq : f ≫ q = p)
    (F : Modules.{u, u} B S hS X hX)
    (hp : IsLocallyOfFinitePresentation B S hS p)
    (hq : IsLocallyOfFiniteType B S hS q)
    (hqc : IsQuasicoherentOnCharts B S hS hX F)
    (hfp : IsFinitePresentationOnCharts B S hS hX F) :
    IsOpen (flatLocus B S hS hX f F) :=
  isOpen_flatLocus_of_isFinitePresentationOnCharts B S hS hX f F
    (isLocallyOfFinitePresentation_of_comp B S hS hX hY hZ f q
      (by rw [hfq]; exact hp) hq) hqc hfp

/-- **Stacks 05X2, the openness assertion, from finite presentation on the small étale site.**
Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` whose source and target are given
over an algebraic space `Z` by `p : X ⟶ Z` and `q : Y ⟶ Z` with `f ≫ q = p`.  If `p` is locally
of finite presentation and `q` is locally of finite type, then the locus of points of `|X|` at
which an `𝒪_X`-module of finite presentation on the small étale site is flat over `Y` is open.

Hypothesis (2) of the source, finite presentation of the module, is Stacks 03DL (7) on the small
étale site of `X`; the quasi-coherence of the module which the source assumes in its preamble
follows from it, by `SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite`.  Both
are passed to the charts by
`AlgebraicGeometry.Space.isFinitePresentationOnCharts_of_isFinitePresentationOnSite` and
`AlgebraicGeometry.Space.isQuasicoherentOnCharts_of_isFinitePresentationOnSite`, so this form
asks no chartwise hypothesis and
`AlgebraicGeometry.Space.isOpen_flatLocus_of_isLocallyOfFinitePresentation_comp` is the special
case of it at a module whose finite presentation is only available chartwise. -/
@[stacks 05X2 "openness; hypothesis (3), flatness over the base, is not needed for this half"]
theorem isOpen_flatLocus_of_isFinitePresentationOnSite_comp
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z) (hfq : f ≫ q = p)
    (F : Modules.{u, u} B S hS X hX)
    (hp : IsLocallyOfFinitePresentation B S hS p)
    (hq : IsLocallyOfFiniteType B S hS q)
    (hFfp : SheafOfModules.IsFinitePresentationOnSite F) :
    IsOpen (flatLocus B S hS hX f F) := by
  have : SheafOfModules.IsFinitePresentationOnSite F := hFfp
  exact isOpen_flatLocus_of_isLocallyOfFinitePresentation_comp B S hS hX hY hZ f p q hfq F hp hq
    (isQuasicoherentOnCharts_of_isFinitePresentationOnSite B S hS hX F hFfp)
    (isFinitePresentationOnCharts_of_isFinitePresentationOnSite B S hS ⟨X, hX⟩ F
      (SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite F) hFfp)

end AlgebraicGeometry.Space

end
