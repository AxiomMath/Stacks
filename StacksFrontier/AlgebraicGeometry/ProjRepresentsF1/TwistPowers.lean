module

public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.TwistComparison
public import StacksFrontier.AlgebraicGeometry.ProjTwistMono.Trivialized
public import StacksFrontier.AlgebraicGeometry.TwistTensor.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.AlgebraicGeometry.Ample.AmpleCriteria

/-!
# The twists are tensor powers: from invertibility to surjectivity

`Stacks.AlgebraicGeometry.ProjRepresentsF1.TwistsAreTensorPowers` is the sole open mathematical
input to the canonicality clause of Tag 01O4, isolated by
`Stacks.AlgebraicGeometry.ProjRepresentsF1.isCanonicalTwistPair_iff`: the canonical comparison
out of the tensor algebra of the degree-one twist is an *isomorphism* in every nonnegative
degree. Degree one is free, by `isIso_pairTwistComparison_app_one`.

This file weakens what remains from an isomorphism to a **surjection**. Both sides of the
comparison are invertible sheaves of modules on the relative `Proj` — the target by the closed
sibling clause of this very tag, the source because the tensor powers of an invertible sheaf are
invertible — and an epimorphism between invertible sheaves of modules on a scheme is an
isomorphism. So `TwistsAreTensorPowers` holds as soon as the comparison is epi in each degree,
which is `twistsAreTensorPowers_iff_epi`.

## Main results

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.isInvertible_tensorPowerNat`: the tensor powers of
  an invertible sheaf of modules on a scheme are invertible.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.isInvertible_tensorPiece` and
  `isInvertibleModule_tensorPiece`: hence so is every nonnegative homogeneous piece of the
  tensor algebra of an invertible sheaf, in each of the two classes this repository carries for
  Tag 01CS.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.isIso_pairTwistComparison_app_of_epi`: **the
  reduction.** In each nonnegative degree the canonical comparison of a pair is an isomorphism as
  soon as it is an epimorphism.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.twistsAreTensorPowers_iff_epi`:
  `TwistsAreTensorPowers` is equivalent to epimorphy of the comparison in every nonnegative degree
  other than one.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.isIso_twistMultiplicationMap_of_adjoin`: on an
  *absolute* `Proj` of a ring generated in degree one, the multiplication
  `𝒪(n) ⊗ 𝒪(m) ⟶ 𝒪(n + m)` is an isomorphism, in all integer degrees. This is the absolute
  shadow of the remaining gap, recorded here because it is the next input (see below).

## Implementation notes

**There are two unrelated tensor powers in this library, and only one of them is the bundle's.**
`SheafOfModules.tensorPower J F n` is `ℕ`-indexed, defined by the three-case recursion
`0 ↦ 𝒪`, `1 ↦ F`, `n + 2 ↦ F ⊗ (n + 1)`, and is the one the field `tensorPieceIso` of
`SheafOfModules.TensorExteriorSymmetricAlgebras` identifies the homogeneous pieces with.
`Stacks.SheafOfModules.TensorPower.tensorPower O hO L n` is `ℤ`-indexed, defined only for
invertible `L` as the image of the unit under a power of the tensoring autoequivalence, and it
is the one Tag 01CU's `Stacks.SheafOfModules.isInvertible_tensorPower` is about. That lemma
therefore does **not** apply here, and `isInvertible_tensorPowerNat` below is proved by its own
recursion over the bundle's three cases; the name carries `Nat` for exactly this reason. The
recursion is sound because `SheafOfModules.tensorPower J L (n + 2)` and
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf X.presheaf X.ringCatSheaf.2 L
  (SheafOfModules.tensorPower J L (n + 1))`
are equal by `rfl`, as are `Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf
  X.ringCatSheaf.2` and
`X.ringCatSheaf`, so Tag 01CT's `isInvertible_tensorSheaf` applies to the successor case with no
transport.

**Three lemmas are applied with all arguments explicit.** `isInvertible_tensorSheaf`,
`isInvertible_of_iso` and `isIso_of_epi_of_isInvertible` carry their invertibility hypotheses as
instance arguments, and instance search does not find them: the sheaf of rings is reached as
`(sheafToPresheaf _ CommRingCat).obj X.sheaf` rather than as `X.presheaf`, and the class takes
the sheaf condition as a *value*, so two spellings of one proof do not match syntactically. This
is the same Category-instance mismatch recorded in
`StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.TwistComparison`, met in its instance-argument
form rather than its `rw` form.

**The two invertibility classes both occur and neither can be dropped.** `F1Pair.invertible`
supplies `Stacks.SheafOfModules.IsInvertible`, which is the class Tag 01CU's tensor-power API is
stated for, so the induction runs there; `isIso_of_epi_of_isInvertible` consumes
`AlgebraicGeometry.SheafOfModules.IsInvertible`, which is the class
`TwistMapsInvertible.twistData_isInvertible` produces for the target. The crossing is done once,
in `isInvertibleModule_tensorPiece`, by
`Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible`.

## What remains, and what the next input is

**`TwistsAreTensorPowers` is not proved, and no project tag is attached in this directory.** What
this file leaves is epimorphy of the comparison in degree zero and in the degrees at least two.
The degrees at least two are no longer open: the induction over degrees, using the field
`tensorPieceIso_mul_left` of the bundle, is
`Stacks.AlgebraicGeometry.ProjRepresentsF1.isIso_hom_app_succ` of
`StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.TensorAlgebraMul`, and its input on the twist
side is the multiplication clause of this same tag,
`Stacks.AlgebraicGeometry.TwistMapsInvertible.twistData_isIso_mulSheaf`. The bidegree `(1, k)`
compatibility between `tensorPieceIso` and the graded multiplication, which nothing in the
library stated, is `isIso_generatorMul_tensorGenerator` there. So what remains of
`TwistsAreTensorPowers` is **degree zero alone**, which is
`twistsAreTensorPowers_iff_isIso_app_zero`, and it holds as soon as the degree-zero twist is the
structure sheaf (`twistsAreTensorPowers_of_pieceZeroIsoUnit`).

The absolute multiplication statement `isIso_twistMultiplicationMap_of_adjoin` below is
therefore no longer the next input; it is recorded as the absolute shadow of the relative
multiplication clause, whose relative form is proved.

**The pair's `degreeOneSurjective` is no longer open, and of it this file supplies only the
covering family.** That clause is epimorphy of `π^* A₁ ⟶ 𝒪(1)`, and it is proved — for the
transpose of the homogeneous-section map of any twist datum of an algebra generated in degree
one — by `Stacks.AlgebraicGeometry.RelativeProjDegreeOne.epi_psiTranspose`. What this file
contributes to that proof is `iSup_basicOpen_degreeOne_eq_top` below, the covering family on a
chart, consumed through
`Stacks.AlgebraicGeometry.ProjDegreeOneTriv.exists_mem_basicOpen_degreeOne`.

Two claims of an earlier draft of this docstring are false, and are corrected here rather than
deleted, because each cost a later reader a search. The trivializing section of Tag 01MS *is*
identified with `degreeSection 𝒜 1 f`, by
`Stacks.AlgebraicGeometry.ProjDegreeOneTriv.degreeOneSection_eq_trivializingSection`, which also
reads off that a degree-one element freely generates `𝒪(1)` on its own standard open; the
identification is in a file of its own, which is why it is invisible to a grep of
`ProjTrivialization`. And the library's only epimorphy criterion for a morphism into a twisting
sheaf is not the Tag 01N0 comparison: the criterion the proof uses is the local one,
`Stacks.SheafOfModules.StalkEpiMono.epi_of_exists_sections`, which asks for a lift of each
section near each point and so needs neither a faithful pushforward nor an inducing base map.
What had genuinely been missing was the *relative* half — `ChartData.mapSection`, the chart
identification read on sections, was stated and used only at the top open of a chart, so no
absolute statement about a standard open could be carried through it. That is supplied by
`StacksFrontier.AlgebraicGeometry.RelativeProjDegreeOne.Chart`.

That is about *proving* `degreeOneSurjective` for the universal pair. The opposite direction —
*consuming* it, for an arbitrary pair on an arbitrary test scheme — is no longer open:
`StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.DegreeOneCover` turns the clause into an open
cover of the test scheme on which a named degree-one image is a basis of `ℒ`
(`iSup_nonvanishingChart_pairGeneratingSections_eq_top`), whenever `𝒜₁` is generated by global
sections, and trivializes `ℒ` on each member.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01MW](https://stacks.math.columbia.edu/tag/01MW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjInvertibleLocus
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

namespace Stacks.AlgebraicGeometry.ProjRepresentsF1

universe u w

/-! ### Tensor powers of an invertible sheaf -/

/-- **The tensor powers of an invertible sheaf of modules on a scheme are invertible.**

This is about the `ℕ`-indexed `SheafOfModules.tensorPower` of the tensor-algebra bundle, not
about the `ℤ`-indexed power of Tag 01CU; see the implementation notes. The three cases are the
three cases of the definition: the zeroth power is the structure sheaf, the first is the sheaf
itself, and a power at least two is a tensor product of invertible sheaves by Tag 01CT. -/
public theorem isInvertible_tensorPowerNat {X : Scheme.{u}} (L : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L) :
    ∀ n : ℕ, Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (SheafOfModules.tensorPower (Opens.grothendieckTopology ↥X) L n)
  | 0 => Stacks.SheafOfModules.isInvertible_unit _ _
  | 1 => hL
  | (n + 2) =>
      @Stacks.SheafOfModules.isInvertible_tensorSheaf _ _ _ X.presheaf X.ringCatSheaf.2 _ _
        L (SheafOfModules.tensorPower (Opens.grothendieckTopology ↥X) L (n + 1)) hL
        (isInvertible_tensorPowerNat L hL (n + 1))

/-- **Every nonnegative homogeneous piece of the tensor algebra of an invertible sheaf is
invertible**, transported from the tensor power along the bundle's degree-`n` identification. -/
public theorem isInvertible_tensorPiece {X : Scheme.{u}} (TA : TensorAlgebras.{u}) (L : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L) (n : ℕ) :
    Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      ((TA X L).tensor.piece (n : ℤ)) :=
  @Stacks.SheafOfModules.isInvertible_of_iso _ _ _ X.presheaf X.ringCatSheaf.2 _ _ _ _
    ((TA X L).tensorPieceIso n).symm (isInvertible_tensorPowerNat L hL n)

/-- `isInvertible_tensorPiece` in the repository's *other* class realising Tag 01CS, which is the
one the epimorphism criterion consumes. -/
public theorem isInvertibleModule_tensorPiece {X : Scheme.{u}} (TA : TensorAlgebras.{u})
    (L : X.Modules) (hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L)
    (n : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      ((TA X L).tensor.piece (n : ℤ)) :=
  (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
    X.presheaf X.ringCatSheaf.2 _).mp (isInvertible_tensorPiece TA L hL n)

/-! ### The comparison: from isomorphy to epimorphy -/

section Relative

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} (TA : TensorAlgebras.{u})
  (D : TwistData A)

/-- **The reduction.** In every nonnegative degree the canonical comparison attached to a pair on
relative `Proj` is an isomorphism as soon as it is an epimorphism.

Its source is a homogeneous piece of the tensor algebra of the pair's invertible sheaf, hence
invertible by `isInvertibleModule_tensorPiece`; its target is a twist, hence invertible by the
closed `twists_invertible` clause of this same tag. An epimorphism between invertible sheaves of
modules on a scheme is an isomorphism. -/
public theorem isIso_pairTwistComparison_app_of_epi (hgen : IsGeneratedInDegreeOne A)
    (P : F1Pair A TA (relativeProj A).toBase) (β : P.L ≅ D.algebra.piece 1) (n : ℕ)
    (h : Epi ((pairTwistComparison TA D P β).app (n : ℤ))) :
    IsIso ((pairTwistComparison TA D P β).app (n : ℤ)) :=
  @Stacks.AlgebraicGeometry.ProjTwistMono.isIso_of_epi_of_isInvertible
    (relativeProj A).scheme _ _ _ h
    (isInvertibleModule_tensorPiece TA P.L P.invertible n)
    (Stacks.AlgebraicGeometry.TwistMapsInvertible.twistData_isInvertible D hgen (n : ℤ))

/-- **`TwistsAreTensorPowers` is a surjectivity statement.** Under generation in degree one it
holds exactly when the canonical comparison is an epimorphism in every nonnegative degree other
than one — degree one being free, by `isIso_pairTwistComparison_app_one`.

This is the statement of the remaining input to the canonicality clause of Tag 01O4 in the form a
local argument can attack: epimorphy of a morphism of sheaves of modules is local surjectivity,
whereas invertibility is not local in the form Tag 01CS defines it. -/
public theorem twistsAreTensorPowers_iff_epi (hgen : IsGeneratedInDegreeOne A)
    (P : F1Pair A TA (relativeProj A).toBase) (β : P.L ≅ D.algebra.piece 1) :
    TwistsAreTensorPowers TA D P β ↔
      ∀ n : ℕ, n ≠ 1 → Epi ((pairTwistComparison TA D P β).app (n : ℤ)) := by
  refine ⟨fun h n _ => ?_, fun h => (twistsAreTensorPowers_iff TA D P β).mpr fun n hn => ?_⟩
  · have : IsIso ((pairTwistComparison TA D P β).app (n : ℤ)) := h n
    infer_instance
  · exact isIso_pairTwistComparison_app_of_epi TA D hgen P β n (h n hn)

end Relative

/-! ### The absolute input -/

section Absolute

variable {R : Type u} {σ : Type w} [CommRing R] [SetLike σ R] [AddSubgroupClass σ R]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **On an absolute `Proj` of a graded ring generated in degree one the multiplication of twists
is an isomorphism**, in all integer degrees: `𝒪(n) ⊗ 𝒪(m) ⟶ 𝒪(n + m)`.

Generation in degree one makes the degree-one ratio locus the whole of `Proj`, and the
multiplication maps are isomorphisms over the ratio locus. Both halves are proved elsewhere; this
composes them. The transport is the substitution of `1 * n` for `n`,
done after `revert` because the index occurs in the type of the morphism. -/
public theorem isIso_twistMultiplicationMap_of_adjoin
    (hgen : Algebra.adjoin (𝒜 0) (𝒜 1 : Set R) = ⊤) (n m : ℤ) :
    IsIso (twistMultiplicationMap 𝒜 n m) := by
  have key := Stacks.AlgebraicGeometry.TwistTensor.isIso_twistMultiplicationMap_of_ratioLocus_eq_top
      𝒜 (k := 1)
      (Stacks.AlgebraicGeometry.ProjTwistMono.ratioLocus_eq_top_of_adjoin_coe_degree_one 𝒜 hgen 1)
      n m
  revert key
  rw [Nat.cast_one, one_mul, one_mul]
  exact id

/-- **The standard opens of the homogeneous elements of degree one cover an absolute `Proj` of a
ring generated in degree one.**

This is Mathlib's `AlgebraicGeometry.Proj.iSup_basicOpen_eq_top'` instantiated at the inclusion
of `𝒜 1`, with the generating set at the spelling the relative-`Proj` statements use. The library
performs that instantiation inside the proof of
`Stacks.AlgebraicGeometry.ProjShared.ratioLocus_eq_top_of_adjoin_degree_one` and nowhere states
it on its own; it is recorded here because it is the covering family on which the degree-one
surjectivity of Tag 01O4's universal pair has to be checked. -/
public theorem iSup_basicOpen_degreeOne_eq_top
    (hgen : Algebra.adjoin (𝒜 0) (𝒜 1 : Set R) = ⊤) :
    (⨆ f : 𝒜 1, AlgebraicGeometry.Proj.basicOpen 𝒜 (f : R)) = ⊤ :=
  AlgebraicGeometry.Proj.iSup_basicOpen_eq_top' 𝒜 (fun f : 𝒜 1 => (f : R))
    (fun f => ⟨1, f.2⟩)
    (by rw [Stacks.AlgebraicGeometry.ProjTwistMono.range_coe_degree_one]; exact hgen)

end Absolute

end Stacks.AlgebraicGeometry.ProjRepresentsF1

end
