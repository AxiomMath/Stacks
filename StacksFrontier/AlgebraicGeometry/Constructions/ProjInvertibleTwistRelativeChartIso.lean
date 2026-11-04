module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeAffinePiece
public import StacksFrontier.AlgebraicGeometry.RelativeProjChain.EventualBijective

/-!
# Tag 02NC over a base scheme: the comparison is an isomorphism over one chart of the base

Tag 02NC compares `Proj_S(𝒜)` with `Proj_S(ℬ)` for `ℬ_d = 𝒜_d ⊗_{𝒪_S} ℒ^{⊗ d}` over an
arbitrary base **scheme** `S`. Its proof says to *"choose an open covering of `S` such that `ℒ`
is trivialized over the pieces and glue the corresponding maps"*.

This file carries out the first half of that instruction: it produces the map over one piece,
and shows it to be an isomorphism. The input is a section `x` of `ℒ` over a single open `V` of
the base whose powers trivialize the powers of `ℒ` there — no **global** section of `ℒ` is
needed, and a locally trivial `ℒ` has none. The output is an isomorphism of the absolute
homogeneous spectra of the graded rings of sections,

`Proj ℬ(V) ≅ Proj 𝒜(V)`,

which by `Stacks.AlgebraicGeometry.RelativeProjTwistQcoh.chartIsoPreimage` is the tag's `g` over
the preimage of `V` when `V` is affine.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.TrivializesPower`: the hypothesis that the
  `d`-th power of the local section trivializes the `d`-th tensor power of the twisting module
  over the open.

## Main results

* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.bijective_gradedAddHom_psiSectionAt`: the
  chart comparison is bijective on the degree-`d` homogeneous component of the graded ring of
  sections. This is the passage from the sheaf-level bijectivity of
  `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.bijective_psiPieceAt` to the shape the
  absolute machinery of Tag 07ZE consumes.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.mapDomain_psiSectionAt_eq_top`: **the
  comparison is defined on all of `Proj ℬ(V)`.**
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.isIso_mapHom_psiSectionAt`: **the comparison
  `Proj ℬ(V) ⟶ Proj 𝒜(V)` is an isomorphism.**
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.isIso_twistMap_psiSectionAt`: every chart
  comparison map of Tag 07ZG on the twisting sheaves, attached to the comparison homomorphism, is
  an isomorphism.

## Why the degreewise hypothesis is eventual

`Stacks.AlgebraicGeometry.RelativeProjChain.isIso_mapHom_of_eventually_bijective` asks for
bijectivity in all sufficiently large degrees, not in every degree, because the homogeneous
spectrum only sees the positive degrees. So the hypothesis below is eventual, and a section
trivializing `ℒ` over `V` supplies it in every degree `d ≥ 1`.

## Scope

The isomorphisms produced here are indexed by a pair (open of the base, trivializing section over
it). Their independence of the section and their compatibility with the chart transitions are
proved in `ProjInvertibleTwistRelativeGluing.lean`, which glues them over the basis of
trivializing affine opens into the tag's isomorphism
`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.relativeTwistIso`. Nothing here carries a
`stacks` attribute: these are statements over one chart.

## References

* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 02NB](https://stacks.math.columbia.edu/tag/02NB)
* [Stacks Project, Tag 07ZE](https://stacks.math.columbia.edu/tag/07ZE)
* [Stacks Project, Tag 07ZJ](https://stacks.math.columbia.edu/tag/07ZJ)
-/

@[expose] public noncomputable section

open CategoryTheory Filter Opposite
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.GradedAlgebraTwist

universe u

namespace Stacks.AlgebraicGeometry.RelativeInvertibleTwist

variable {S : Scheme.{u}} (L : S.Modules)
  [Stacks.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property L]
  (𝒜 : SheafGradedAlgebra S)

/-- **The `d`-th power of a local section trivializes the `d`-th tensor power of the twisting
module over the open.** This is the hypothesis
`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.bijective_psiPieceAt` consumes, named so that
it can be quantified over the degree. -/
def TrivializesPower (V : S.Opens) (x : (tp L 1).val.obj (op V)) (d : ℕ) : Prop :=
  ∃ e : (tp L (d : ℤ)).over V ≅ SheafOfModules.unit
      (Stacks.SheafOfModules.SliceRestriction.sliceStructureSheaf
        S.sheaf.obj S.ringCatSheaf.property V),
    Stacks.SheafOfModules.TensorGenerator.generator S.sheaf.obj S.ringCatSheaf.property V
      (tp L (d : ℤ)) e = powSecAt L (op V) x d

/-- The comparison in a degree whose tensor power the section trivializes is bijective on
sections. This is `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.bijective_psiPieceAt` with
the trivializing isomorphism packaged. -/
theorem bijective_psiPieceAt_of_trivializesPower {V : S.Opens} {x : (tp L 1).val.obj (op V)}
    {d : ℕ} (h : TrivializesPower L V x d) :
    Function.Bijective (psiPieceAt L 𝒜 V x d) := by
  obtain ⟨e, he⟩ := h
  exact bijective_psiPieceAt L 𝒜 V x d e he

/-- **The chart comparison is bijective on the degree-`d` homogeneous component of the graded
ring of sections.**

If the comparison `psiPieceAt L 𝒜 V x d` on the sections of the degree-`d` homogeneous piece is
bijective, then so is the degree-`d` component of the graded ring homomorphism
`psiSectionAt L 𝒜 V x`. -/
theorem bijective_gradedAddHom_psiSectionAt {V : S.Opens} {x : (tp L 1).val.obj (op V)} {d : ℕ}
    (h : Function.Bijective (psiPieceAt L 𝒜 V x d)) :
    Function.Bijective (GradedRingHom.gradedAddHom (psiSectionAt L 𝒜 V x) d) := by
  constructor
  · intro p q hpq
    obtain ⟨-, a, rfl⟩ := p
    obtain ⟨-, b, rfl⟩ := q
    have h0 : psiSectionAt L 𝒜 V x (DirectSum.of (𝒜.sectionPieces V) d a) =
        psiSectionAt L 𝒜 V x (DirectSum.of (𝒜.sectionPieces V) d b) := congrArg Subtype.val hpq
    rw [psiSectionAt_of L 𝒜 V x a, psiSectionAt_of L 𝒜 V x b] at h0
    exact Subtype.ext
      (congrArg (DirectSum.of (𝒜.sectionPieces V) d) (h.1 (DirectSum.of_injective d h0)))
  · rintro ⟨-, b, rfl⟩
    obtain ⟨a, rfl⟩ := h.2 b
    exact ⟨⟨_, 𝒜.of_mem_grading V a⟩, Subtype.ext (psiSectionAt_of L 𝒜 V x a)⟩

/-- The degreewise hypothesis the absolute machinery consumes, assembled from a family of
trivializations of the tensor powers. -/
theorem eventually_bijective_gradedAddHom_psiSectionAt {V : S.Opens}
    {x : (tp L 1).val.obj (op V)} (hx : ∀ᶠ d : ℕ in atTop, TrivializesPower L V x d) :
    ∀ᶠ d : ℕ in atTop,
      Function.Bijective (GradedRingHom.gradedAddHom (psiSectionAt L 𝒜 V x) d) :=
  hx.mono fun _ hd =>
    bijective_gradedAddHom_psiSectionAt L 𝒜 (bijective_psiPieceAt_of_trivializesPower L 𝒜 hd)

/-! ### The isomorphism over one chart of the base -/

/-- **The comparison is defined on all of `Proj ℬ(V)`.** -/
theorem mapDomain_psiSectionAt_eq_top {V : S.Opens} {x : (tp L 1).val.obj (op V)}
    (hx : ∀ᶠ d : ℕ in atTop, TrivializesPower L V x d) :
    mapDomain (𝒜.grading V) ((twist 𝒜 L).grading V) (psiSectionAt L 𝒜 V x) = ⊤ :=
  RelativeProjChain.mapDomain_eq_top_of_eventually_bijective _ _ _
    (eventually_bijective_gradedAddHom_psiSectionAt L 𝒜 hx)

/-- **Tag 02NC over one chart of the base: the comparison `Proj ℬ(V) ⟶ Proj 𝒜(V)` is an
isomorphism.**

No global section of the twisting module is used: the input is a section over the single open
`V`, whose powers trivialize the powers of `ℒ` there. For `V` an affine open of the base the two
homogeneous spectra are the preimages of `V` in `Proj_S(𝒜)` and `Proj_S(ℬ)` by
`Stacks.AlgebraicGeometry.RelativeProjTwistQcoh.chartIsoPreimage`, so this is the tag's `g` over
that chart. -/
theorem isIso_mapHom_psiSectionAt {V : S.Opens} {x : (tp L 1).val.obj (op V)}
    (hx : ∀ᶠ d : ℕ in atTop, TrivializesPower L V x d) :
    IsIso (mapHom (𝒜.grading V) ((twist 𝒜 L).grading V) (psiSectionAt L 𝒜 V x)) :=
  RelativeProjChain.isIso_mapHom_of_eventually_bijective _ _ _
    (eventually_bijective_gradedAddHom_psiSectionAt L 𝒜 hx)

/-- **The chart comparison maps of Tag 07ZG are isomorphisms over one chart of the base**: for
the comparison homomorphism `𝒜(V) ⟶ ℬ(V)` attached to a trivializing section, every comparison
map `(Proj.map)^*𝒪_{Proj 𝒜(V)}(n) ⟶ 𝒪_{Proj ℬ(V)}(n)` on the twisting sheaves is an isomorphism.

These are maps in the direction of Tag 07ZG, not the `θ_n` of clause (1) of Tag 02NC, which are
`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.twistThetaIso`. -/
theorem isIso_twistMap_psiSectionAt {V : S.Opens} {x : (tp L 1).val.obj (op V)}
    (hx : ∀ᶠ d : ℕ in atTop, TrivializesPower L V x d) (n : ℤ) :
    IsIso ((projMapData (𝒜.grading V) ((twist 𝒜 L).grading V)
      (psiSectionAt L 𝒜 V x)).twistMap n) :=
  RelativeProjChain.isIso_projMapData_twistMap_of_eventually_bijective _ _ _
    (eventually_bijective_gradedAddHom_psiSectionAt L 𝒜 hx) n

end Stacks.AlgebraicGeometry.RelativeInvertibleTwist

end
