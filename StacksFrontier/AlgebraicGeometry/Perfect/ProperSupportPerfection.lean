module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Comparison
public import StacksFrontier.AlgebraicGeometry.Perfect.TorDimension
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedScalarRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.PullbackPushforwardAdjunction
public import
  StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PseudoCoherentAndFiniteTorDimension
import StacksCore.Tactic.StacksAttribute

/-!
# Producing perfect complexes: proper cohomological support

Let `S` be a locally Noetherian scheme and `f : X ⟶ S` a morphism locally of finite type.  Let
`E` be an object of `D(𝒪_X)` which is bounded with coherent cohomology sheaves, whose cohomology
sheaves are supported on subsets proper over `S`, and which has finite Tor dimension as an object
of `D(f⁻¹𝒪_S)`.  [Stacks, Tag 08EV] asserts that `Rf_*E` is then a perfect object of `D(𝒪_S)`.

That tag is proved unconditionally, under exactly the source's hypotheses, as
`Stacks.AlgebraicGeometry.ProperSupportCoherent.isPerfect_derivedPushforward_of_isProperOver_supp`
in `StacksFrontier/AlgebraicGeometry/ProperSupportCoherent/TorDimensionDirectImage.lean`, at the
`AlgebraicGeometry.Scheme.Modules` spelling of the categories of modules and with the canonical
derived tensor product on `(X, f⁻¹𝒪_S)`.  This file gives the *conditional* form of it at the
`StrictlyPerfect.OXMod` spelling with an arbitrary derived tensor datum, the form that
[Stacks, Tag 0DJQ] and [Stacks, Tag 0B6F] in
`StacksFrontier/AlgebraicGeometry/Perfect/PerfectPushforward.lean` consume.

## Main definitions

* `Stacks.Cohomology.ProperSupportPerfection.SuppHomologySubset` says that every cohomology sheaf
  of an object of `D(𝒪_X)` has its support inside a given closed subset of `X`.
* `Stacks.Cohomology.ProperSupportPerfection.derivedPushforwardOX` is `Rf_*` for a morphism of
  schemes, at the `StrictlyPerfect.OXMod` spelling of the two categories of modules: the total
  right derived functor of degreewise pushforward.

## Main results

* `Stacks.Cohomology.ProperSupportPerfection.exists_isProperOver_of_eventually_empty`: a family of
  subsets of `X`, indexed by `ℤ`, each contained in a closed subset proper over `S` and all but
  finitely many of them empty, is contained in a *single* closed subset proper over `S`.
* `Stacks.Cohomology.ProperSupportPerfection.exists_isProperOver_supp_homology`: the same
  statement for the supports of the cohomology sheaves of a bounded object of `D(𝒪_X)`.  This is
  the sentence "let `T ⊂ X` be the union of the supports of the `H^i(E)`; then `T` is proper over
  `S`" of the source's proof of [Stacks, Tag 08EV].
* `isPerfect_of_isPseudoCoherent_of_hasFiniteTorDimension`, in the namespace of this file:
  a pseudo-coherent object of `D(𝒪_Y)` whose Tor amplitude is contained in one interval globally
  is perfect.  This is [Stacks, Tag 08CQ] together with the inheritance of Tor amplitude by a
  restriction to an open subspace, applied at the trivial covering of `Y` by `⊤`.
* `Stacks.Cohomology.ProperSupportPerfection.isPerfect_derivedPushforward_of_properSupport`: the
  conclusion of [Stacks, Tag 08EV] at this spelling, granted the two named residual hypotheses
  described below.  It is not the tag, and does not carry its label.
  `Stacks.Cohomology.ProperSupportPerfection.supp_eq_empty_of_isZero` is the auxiliary fact that a
  zero sheaf of modules has empty support.

## Implementation notes

**What is proved and what is carried.**  The conclusion of [Stacks, Tag 08EV] is reached here from
the hypothesis of that tag together with two residual hypotheses, one for each half of the
conclusion under [Stacks, Tag 08CQ]:

* `hpushforwardCoherence`: `Rf_*K` is pseudo-coherent, which is [Stacks, Tag 08E2] read through
  [Stacks, Tag 08E8].
* `hpushforwardTorDimension`: `Rf_*K` has finite Tor dimension over `𝒪_S`, the closing step of
  the source's proof.

Both are proved, at the `AlgebraicGeometry.Scheme.Modules` spelling and for the canonical derived
tensor product, in the proof of the complete theorem named above.  They stay hypotheses *here*
because the Tor-dimension clause of this file is stated for an arbitrary
`AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring` `D` on `(X, f⁻¹𝒪_S)`, whose
underived tensor product is a field of the datum rather than the tensor product of modules, so
`D.HasFiniteTorDimension` is not the Tor dimension of the source and does not imply it.  Removing
them from the consumers downstream is a matter of restating those consumers at the canonical
derived tensor product, which is their item and not this one.

Both residues take as arguments the clauses of the hypothesis of [Stacks, Tag 08EV] that the
source feeds into them, so each of the four clauses of that hypothesis is consumed: the
boundedness and proper-support clauses through
`Stacks.Cohomology.ProperSupportPerfection.exists_isProperOver_supp_homology`, the coherence
clause through the first residue, and the Tor-dimension clause through the second.

**What the glue consists of.**  The reduction to a single closed subset proper over `S` is
genuinely proved, from [Stacks, Tag 0CYR] in the finite-union form
`AlgebraicGeometry.isProperOver_iSup`: the covering interval of the boundedness clause has
finitely many integers in it, the proper-support clause gives a proper closed subset for each of
them, and the cohomology sheaves in the remaining degrees vanish, hence have empty support.  The
passage from pseudo-coherence and a Tor-amplitude interval to perfectness is [Stacks, Tag 08CQ],
`Stacks.Cohomology.TorAmplitude.isPerfect_of_isPseudoCoherent_of_locallyHasFiniteTorDimension`,
reached across two spelling comparisons that the tree already carries:
`Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent'` for the two predicates of
[Stacks, Tag 08CB] and `Stacks.Cohomology.PerfectComplexes.isPerfect_iff_ringedSpace` for the two
predicates of [Stacks, Tag 08CM].

**The shape of the statement.**  The direct image is
`Stacks.Cohomology.ProperSupportPerfection.derivedPushforwardOX f`, the total right derived
functor of degreewise pushforward, and not a functor left unspecified.  The two residues are
hypotheses about that same functor.  Their quantified forms downstream,
`Stacks.Cohomology.PerfectPushforward.PushforwardCoherenceResidue` and
`Stacks.Cohomology.PerfectPushforward.PushforwardTorDimensionResidue`, do keep a functor
parameter, since each is a property *of* a functor; the two tags there apply them to this one.
The derived tensor product on `(X, f⁻¹𝒪_S)` is an arbitrary
`AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring`, and the four clauses of the
hypothesis are written exactly as the fields of
`Stacks.Cohomology.PerfectPushforward.PushforwardPerfectionInput` are, so that
`Stacks.Cohomology.PerfectPushforward.PushforwardPerfectionCriterion` is discharged by this
theorem as soon as the two residues are available.  That is what
`Stacks.Cohomology.PerfectPushforward.pushforwardPerfectionCriterion_of_residues` does: this
module is imported by
`StacksFrontier/AlgebraicGeometry/Perfect/PerfectPushforward.lean`, and [Stacks, Tag 0DJQ] and
[Stacks, Tag 0B6F] there carry the two residues.  No comparison lemma stands
between the two files; the four hypotheses here are applied to the four fields there directly.

**Generality.**  The source assumes `S` Noetherian; `AlgebraicGeometry.IsLocallyNoetherian` is
assumed instead, which is weaker.  The hypothesis
is not used by the glue — the source uses it only inside [Stacks, Tag 08E2] — and is retained
because it is part of the hypothesis of the tag.

**The derived categories.**  `HasDerivedCategory.standard` is a local instance throughout, as it
is in [Stacks, Tag 08DP] and in `StacksFrontier/AlgebraicGeometry/Perfect/PerfectPushforward.lean`.
This is forced rather than chosen: [Stacks, Tag 08CQ] and the restriction of Tor amplitude name
the derived categories of the open subspaces of `Y` at the same hom universe as that of `Y`
itself, so no free hom universe survives.  `StrictlyPerfect.structureSheafOfRings` is
`implicit_reducible` so that `SheafOfModules.supp`, stated for a sheaf of rings on a topological
space, applies to it.

**A declaration to retire.**  `Stacks.Cohomology.ProperSupportPerfection.supp_eq_empty_of_isZero`
duplicates, at the `StrictlyPerfect.OXMod` spelling, a statement of the same name on its way into
`StacksFrontier/AlgebraicGeometry/Morphisms/Support/Functoriality.lean`; when that is available this
one should be deleted rather than kept beside it.

## References

* [Stacks Project, Tag 08EV](https://stacks.math.columbia.edu/tag/08EV)
* [Stacks Project, Tag 08CQ](https://stacks.math.columbia.edu/tag/08CQ)
* [Stacks Project, Tag 0CYR](https://stacks.math.columbia.edu/tag/0CYR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace StrictlyPerfect

namespace Stacks.Cohomology.ProperSupportPerfection

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local implicit_reducible] StrictlyPerfect.structureSheafOfRings
  structureSheafRing

/-! ### The derived direct image -/

section DerivedDirectImage

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **`Rf_*`, the derived direct image along a morphism of schemes**, at the
`StrictlyPerfect.OXMod` spelling of the two categories of modules.  This is
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward` — the total right derived
functor of degreewise pushforward, which exists unconditionally because every complex of modules
on a ringed space admits a quasi-isomorphism into a K-injective one — taken at the morphism of
ringed spaces underlying `f`.

Only the spelling changes.  The pushforward development writes the structure sheaf of rings as
`structureSheafRing` and the perfect-complex development writes it as
`StrictlyPerfect.structureSheafOfRings`; the two are the same term
(`AlgebraicGeometry.RingedSpace.structureSheafOfRings_eq_ringSheaf`), so the two categories of
modules are equal by `rfl` and so are the two derived categories.  The binder is written out
here, where the `attribute [local implicit_reducible]` above lets instance search cross between
them, exactly as `AlgebraicGeometry.RingedSpace.pushforwardOXMod` does for the degreewise
functor.

[Stacks, Tag 0DJQ] and [Stacks, Tag 0B6F] in
`StacksFrontier/AlgebraicGeometry/Perfect/PerfectPushforward.lean` name this same functor, which is
why it is defined here, at the upstream tag, rather than there. -/
abbrev derivedPushforwardOX :
    DerivedCategory (OXMod.{u, u} X.toRingedSpace) ⥤
      DerivedCategory (OXMod.{u, u} S.toRingedSpace) :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f.toLRSHom.toShHom

end DerivedDirectImage

/-! ### Perfectness from pseudo-coherence and one Tor-amplitude interval -/

section Assembly

variable {Y : RingedSpace.{u, u}}

/-- **A zero sheaf of modules has empty support.** Its stalk at any point is a zero object, hence
a subsingleton, hence has no nonzero element. -/
theorem supp_eq_empty_of_isZero {M : OXMod.{u, u} Y} (h : Limits.IsZero M) :
    SheafOfModules.supp M = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rw [SheafOfModules.mem_supp_iff_nontrivial_stalk M x, not_nontrivial_iff_subsingleton,
    ← AddCommGrpCat.isZero_iff_subsingleton,
    ← AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj_iff]
  exact Functor.map_isZero _ h

/-- **A pseudo-coherent object of `D(𝒪_Y)` of finite Tor dimension is perfect.**

This is [Stacks, Tag 08CQ], whose statement is in terms of *locally* finite Tor dimension; a
global Tor-amplitude interval gives one at the trivial covering of `Y` by `⊤`, because Tor
amplitude is inherited by the restriction to an open subspace
(`Stacks.Cohomology.TorAmplitude.hasFiniteTorDimension_restrictModules`).  The two predicates of
[Stacks, Tag 08CB] and the two predicates of [Stacks, Tag 08CM] both occur, in the spellings that
[Stacks, Tag 08CQ] is stated at and in the spellings this file's conclusion is stated at; they are
the same propositions and the tree carries both comparisons. -/
theorem isPerfect_of_isPseudoCoherent_of_hasFiniteTorDimension
    (E : DerivedCategory (OXMod.{u, u} Y))
    (hpc : RingedSpace.IsPseudoCoherent (X := Y) E)
    (htor : Stacks.Cohomology.TorAmplitude.HasFiniteTorDimension Y E) :
    RingedSpace.IsPerfect (X := Y) E :=
  (Stacks.Cohomology.PerfectComplexes.isPerfect_iff_ringedSpace E).1
    (Stacks.Cohomology.TorAmplitude.isPerfect_of_isPseudoCoherent_of_locallyHasFiniteTorDimension
      E ((Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent' E).2 hpc)
      ⟨PUnit.{u + 1}, fun _ => ⊤, by simp, fun _ =>
        Stacks.Cohomology.TorAmplitude.hasFiniteTorDimension_restrictModules ⊤ E htor⟩)

end Assembly

/-! ### One closed subset proper over the base carrying all the cohomological support -/

section ProperSupport

variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]

/-- **A `ℤ`-indexed family of subsets of `X`, almost all empty and each inside a closed subset
proper over `S`, lies inside one closed subset proper over `S`.**

Only the members indexed by the interval `[a, b]` can be nonempty, and that interval contains
finitely many integers, so the supremum of the closed subsets attached to them is a finite
supremum and [Stacks, Tag 0CYR] applies to it in the form
`AlgebraicGeometry.isProperOver_iSup`. -/
theorem exists_isProperOver_of_eventually_empty (s : ℤ → Set X) (a b : ℤ)
    (hvanish : ∀ i : ℤ, i ∉ Set.Icc a b → s i = ∅)
    (hmem : ∀ i : ℤ, ∃ Z : Closeds X, IsProperOver f Z ∧ s i ⊆ (Z : Set X)) :
    ∃ T : Closeds X, IsProperOver f T ∧ ∀ i : ℤ, s i ⊆ (T : Set X) := by
  classical
  choose Z hZproper hZsub using hmem
  have hfin : Finite (Set.Icc a b : Set ℤ) := (Set.finite_Icc a b).to_subtype
  refine ⟨⨆ j : (Set.Icc a b : Set ℤ), Z j, isProperOver_iSup f _ fun j => hZproper j, fun i => ?_⟩
  by_cases hi : i ∈ Set.Icc a b
  · exact (hZsub i).trans
      (SetLike.coe_subset_coe.mpr (le_iSup (fun j : (Set.Icc a b : Set ℤ) => Z j) ⟨i, hi⟩))
  · rw [hvanish i hi]
    exact Set.empty_subset _

variable (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace))

/-- **The cohomological support of a bounded object of `D(𝒪_X)` with proper supports is carried by
one closed subset proper over `S`.**

This is the third step of the source's proof of [Stacks, Tag 08EV]: the union `T` of the supports
of the cohomology sheaves of `K` is proper over `S`.  Outside the interval supplied by the
boundedness clause the cohomology sheaves vanish, so their supports are empty, and the remaining
finitely many are handled by `AlgebraicGeometry.isProperOver_iSup`.  As in
`Stacks.Cohomology.PerfectPushforward.PushforwardPerfectionInput`, the proper-support clause is
read as the existence of a proper closed subset *containing* each support rather than as
properness of the support itself; the two agree, and the containment form is what composes. -/
theorem exists_isProperOver_supp_homology
    (hbounded : ∃ a b : ℤ, ∀ i : ℤ, i ∉ Set.Icc a b →
      Limits.IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) i).obj K))
    (hproperSupport : ∀ i : ℤ, ∃ Z : Closeds X, IsProperOver f Z ∧
      SheafOfModules.supp
          ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) i).obj K) ⊆
        (Z : Set X)) :
    ∃ T : Closeds X, IsProperOver f T ∧ ∀ i : ℤ,
      SheafOfModules.supp
          ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) i).obj K) ⊆
        (T : Set X) := by
  obtain ⟨a, b, hab⟩ := hbounded
  exact exists_isProperOver_of_eventually_empty f _ a b
    (fun i hi => supp_eq_empty_of_isZero (hab i hi)) hproperSupport

/-! ### Stacks 08EV -/

/-- Every cohomology sheaf of `K` has its support inside the closed subset `T` of `X`. -/
def SuppHomologySubset (T : Closeds X) : Prop :=
  ∀ i : ℤ, SheafOfModules.supp
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) i).obj K) ⊆ (T : Set X)

variable (D : RingedSpace.CertifiedDerivedSheafTensoring
    (RingedSpace.inverseImage S.toRingedSpace f.base))

/-- **The conclusion of [Stacks, Tag 08EV] at the `StrictlyPerfect.OXMod` spelling, granted two
residues.**  Let `S` be a locally Noetherian scheme and `f : X ⟶ S` a morphism locally of finite
type.  Let `K` be an object of `D(𝒪_X)` which

1. is bounded with coherent cohomology sheaves, that is, lies in `D^b_{Coh}(𝒪_X)`;
2. has the support of each of its cohomology sheaves inside a closed subset proper over `S`; and
3. has finite Tor dimension as an object of `D(f⁻¹𝒪_S)`, for the derived tensor datum `D`.

If moreover `hpushforwardCoherence` and `hpushforwardTorDimension` hold, then `Rf_*K` is a
perfect object of `D(𝒪_S)`, with `Rf_*` the derived direct image
`Stacks.Cohomology.ProperSupportPerfection.derivedPushforwardOX`.

`hpushforwardCoherence` says that `Rf_*K` is pseudo-coherent ([Stacks, Tag 08E2] read through
[Stacks, Tag 08E8]) and `hpushforwardTorDimension` that it has finite Tor dimension over `𝒪_S`;
what is proved here is the production of the closed subset — the source's "let `T ⊂ X` be the
union of the supports of the `H^i(E)`" — and the passage from the two residues to perfectness
through [Stacks, Tag 08CQ].

This is a conditional form and does not carry the label of the tag: [Stacks, Tag 08EV] itself,
with no residue, is
`Stacks.AlgebraicGeometry.ProperSupportCoherent.isPerfect_derivedPushforward_of_isProperOver_supp`.
The residues cannot be dropped at this spelling because `D` is an arbitrary certified derived
tensor datum, see the implementation notes of this file. -/
theorem isPerfect_derivedPushforward_of_properSupport [IsLocallyNoetherian S]
    (hbounded : ∃ a b : ℤ, ∀ i : ℤ, i ∉ Set.Icc a b →
      Limits.IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) i).obj K))
    (hcoherent : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) i).obj K).IsCoherent)
    (hproperSupport : ∀ i : ℤ, ∃ Z : Closeds X, IsProperOver f Z ∧
      SheafOfModules.supp
          ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) i).obj K) ⊆
        (Z : Set X))
    (hTor : D.HasFiniteTorDimension ((Scheme.Hom.derivedScalarRestriction f).obj K))
    (hpushforwardCoherence : ∀ T : Closeds X, IsProperOver f T → SuppHomologySubset K T →
      (∀ i : ℤ,
        ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) i).obj K).IsCoherent) →
      RingedSpace.IsPseudoCoherent (X := S.toRingedSpace)
        ((derivedPushforwardOX f).obj K))
    (hpushforwardTorDimension : ∀ T : Closeds X, IsProperOver f T → SuppHomologySubset K T →
      D.HasFiniteTorDimension ((Scheme.Hom.derivedScalarRestriction f).obj K) →
      Stacks.Cohomology.TorAmplitude.HasFiniteTorDimension S.toRingedSpace
        ((derivedPushforwardOX f).obj K)) :
    RingedSpace.IsPerfect (X := S.toRingedSpace) ((derivedPushforwardOX f).obj K) := by
  obtain ⟨T, hTproper, hTsupp⟩ := exists_isProperOver_supp_homology f K hbounded hproperSupport
  exact isPerfect_of_isPseudoCoherent_of_hasFiniteTorDimension _
    (hpushforwardCoherence T hTproper hTsupp hcoherent)
    (hpushforwardTorDimension T hTproper hTsupp hTor)

end ProperSupport

end Stacks.Cohomology.ProperSupportPerfection

end
