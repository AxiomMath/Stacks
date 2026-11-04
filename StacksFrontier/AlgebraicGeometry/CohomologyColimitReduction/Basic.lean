module

public import StacksFrontier.AlgebraicGeometry.HighTwistDevissage.AffineFromNegativeTwists
public import StacksFrontier.AlgebraicGeometry.AmpleLocalGeneration.FromExtension
public import StacksFrontier.AlgebraicGeometry.ColimitClose.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.GlobalSections
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredColimits.CohomologyOverAQuasiCompactOpen
public import StacksFrontier.Topology.Sheaves.Limits.DescendOpensAbelian
public import StacksFrontier.AlgebraicGeometry.SerreCriterionH1.Hgroup
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.OpensSheafificationInstances
public import StacksFrontier.AlgebraicGeometry.SheafOfModulesEnoughInjectives

/-!
# Affineness from the vanishing of the cohomology of negative ample twists

A scheme carrying an ample invertible module `L` is affine as soon as there is an integer `n₀`
with `Hᵖ(X, L^{⊗ -n}) = 0` for every `n ≥ n₀` and every `p > 0`
([Stacks, Tag 0EBD](https://stacks.math.columbia.edu/tag/0EBD)).  The dévissage that proves it
is `Stacks.HighTwistDevissage.isAffine_of_isZero_cohomology_negative_tensorPower`; this file
supplies three of the inputs that dévissage takes as hypotheses -- the colimit reduction, Serre's
criterion and a cohomological dimension bound -- and concludes the tag.

**The colimit reduction.** The step that brings a quasi-coherent module of infinite type into the
range of the dévissage is a presentation, in each positive degree, of `Hᵖ(X, F)` as a colimit of
the `Hᵖ` of the quasi-coherent submodules of `F` of finite type.  It is
[Stacks, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG), which exhibits `F` as the filtered
colimit of those submodules, together with Cohomology, Lemma 20.19.1 =
[Stacks, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF), the commutation of cohomology over
a quasi-compact open with filtered colimits.

Tag 01FF needs the two topological hypotheses of
[Stacks, Tag 0069](https://stacks.math.columbia.edu/tag/0069) -- a basis of quasi-compact opens,
and quasi-compactness of the intersection of two quasi-compact opens -- and Tag 01PG needs
quasi-compactness and quasi-separatedness of the scheme.  The basis is free, every scheme being
prespectral; the remaining topological condition is quasi-separatedness of the underlying space;
and both quasi-compactness and quasi-separatedness follow from ampleness, the second by
[Stacks, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV), the affine nonvanishing opens of
the sections of the positive powers of `L` being a basis with affine pairwise intersections.

**The cohomological dimension bound.** The dévissage is a descending induction on the degree,
started from a degree beyond which the cohomology of *every* quasi-coherent module vanishes.  The
source produces one from [Stacks, Tag 01XI], for a separated scheme covered by `e + 1` affine
opens.  Here it is `AlgebraicGeometry.exists_isZero_hgroup_top`, the same bound in the form
[Stacks, Tag 071L](https://stacks.math.columbia.edu/tag/071L) gives it for a quasi-compact
quasi-separated scheme and a finite affine open covering, which needs no separatedness.

**Serre's criterion** ([Stacks, Tag 01XF]) turns the resulting vanishing of `Hᵖ` on all
quasi-coherent modules in all positive degrees into affineness.  It is needed only in degree one
and only for the quasi-coherent sheaves of ideals, which is the form
`SerreCriterionH1.isAffine_of_forall_isZero_hgroup_one_ideal` has.

## Main results

* `finiteTypeQuasicoherentSmallPresentation`: Tag 01PG's colimit, as a
  `CategoryTheory.Limits.ColimitPresentation` over a **small** index category.
* `exists_colimitPresentation_mapCocone_hfunctor`: the colimit reduction, in the shape the
  dévissage consumes.
* `isAffine_of_forall_isZero_hgroup`: Serre's criterion, [Stacks, Tag 01XF], for the vanishing of
  `Hᵖ` on all quasi-coherent modules in all positive degrees.
* `isAffine_of_isZero_cohomology_negative_tensorPower_of_quasiSeparated`: affineness from the
  vanishing hypothesis on the negative twists, a cohomological dimension bound and the dévissage
  sequence at the modules of finite type ([Stacks, Tag 01Q3], clause (8)), for a quasi-separated
  scheme.
* `isAffine_of_isZero_cohomology_negative_tensorPower`: **[Stacks, Tag 0EBD]**, with no
  hypothesis beyond the tag's own.

## Implementation notes

**Why a small model is needed, and where it comes from.** The dévissage asks for an index
category in `Type u` with a `SmallCategory` instance, because Tag 01FF does; Tag 01PG's diagram
is indexed by the quasi-coherent finite-type subobjects of `F`, which is only *essentially* small
(`AlgebraicGeometry.essentiallySmall_finiteTypeQuasicoherentSubobject`).  So the presentation is
transported along `CategoryTheory.equivSmallModel`: `IsColimit.whiskerEquivalence` moves the
colimit, `IsFiltered.of_equivalence` moves filteredness, and the quasi-coherence and finite type
of each diagram object are read off the `FullSubcategory` property of the subobject the small
index names.

**`PreservesColimit` is passed explicitly, not installed as a local instance.** It is a `Prop`
class, and a `let`-bound hypothesis of that class is not found by instance search at an
`isColimitOfPreserves` call.  Its field `preserves` already returns
`Nonempty (IsColimit (F.mapCocone c))`, which is exactly the shape the dévissage wants, so it is
applied directly and `isColimitOfPreserves` is not used at all.

**The instance hypotheses** -- `HasSheafify`, `WEqualsLocallyBijective`, `EnoughInjectives` for
the site of opens of a scheme -- hold for every scheme, and none of them is assumed here.  Each
of the three is in fact reachable by instance search on its own: at these universes the site of
opens is small, so Mathlib's `SheafOfModules.instIsGrothendieckAbelian` and the global
`CategoryTheory.IsGrothendieckAbelian.enoughInjectives` settle the injectives, and
`Stacks.Cohomology.enoughInjectives_sheafOfModules_ringCatSheaf` states that instance at
`X.ringCatSheaf` directly.  The two `attribute [local instance]` lines below seat the
sheafification pair to keep instance search cheap, not because it would otherwise fail.

## References

* [Stacks Project, Tag 0EBD](https://stacks.math.columbia.edu/tag/0EBD)
* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
* [Stacks Project, Tag 0069](https://stacks.math.columbia.edu/tag/0069)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01XF](https://stacks.math.columbia.edu/tag/01XF)
* [Stacks Project, Tag 071L](https://stacks.math.columbia.edu/tag/071L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.Tag01PGColimitClose

universe u

namespace Stacks.AlgebraicGeometry.CohomologyColimitReduction

-- Sheafification for the site of opens of a scheme, and its weak equivalences, from
-- `Stacks.OpensSheafification`.
attribute [local instance]
  Stacks.OpensSheafification.hasSheafifyOpens
  Stacks.OpensSheafification.wEqualsLocallyBijectiveOpens

variable {X : Scheme.{u}}

/-- **[Stacks, Tag 01PG] as a colimit presentation over a small index category.**  On a
quasi-compact quasi-separated scheme a quasi-coherent module is the colimit of its quasi-coherent
finite-type subobjects; those form an essentially small filtered category, and this is that
colimit transported to its small model. -/
def finiteTypeQuasicoherentSmallPresentation (F : X.Modules) [F.IsQuasicoherent]
    [CompactSpace ↥X] [QuasiSeparatedSpace ↥X] :
    ColimitPresentation (SmallModel (FiniteTypeQuasicoherentSubobject F)) F where
  diag := (equivSmallModel (FiniteTypeQuasicoherentSubobject F)).inverse ⋙
    finiteTypeQuasicoherentSubobjectFunctor F
  ι := ((finiteTypeQuasicoherentSubobjectCocone F).whisker
    (equivSmallModel (FiniteTypeQuasicoherentSubobject F)).inverse).ι
  isColimit := (isColimit_finiteTypeQuasicoherentSubobjectCocone F).whiskerEquivalence
    (equivSmallModel (FiniteTypeQuasicoherentSubobject F)).symm

/-- The small index category of Tag 01PG's presentation is filtered. -/
theorem isFiltered_smallModel (F : X.Modules) [F.IsQuasicoherent] :
    IsFiltered (SmallModel (FiniteTypeQuasicoherentSubobject F)) :=
  IsFiltered.of_equivalence (equivSmallModel (FiniteTypeQuasicoherentSubobject F))

/-- Every object of Tag 01PG's diagram is quasi-coherent and of finite type: it is the module
underlying a subobject of `F` chosen for exactly those two properties. -/
theorem isQuasicoherent_and_isFiniteType_diag_obj (F : X.Modules) [F.IsQuasicoherent]
    [CompactSpace ↥X] [QuasiSeparatedSpace ↥X]
    (j : SmallModel (FiniteTypeQuasicoherentSubobject F)) :
    ((finiteTypeQuasicoherentSmallPresentation F).diag.obj j).IsQuasicoherent ∧
      SheafOfModules.IsFiniteType.{u, u, u}
        ((finiteTypeQuasicoherentSmallPresentation F).diag.obj j) :=
  ⟨((equivSmallModel (FiniteTypeQuasicoherentSubobject F)).inverse.obj j).property.1,
    ((equivSmallModel (FiniteTypeQuasicoherentSubobject F)).inverse.obj j).property.2⟩

/-- **Cohomology commutes with Tag 01PG's presentation.**  On a quasi-compact quasi-separated
scheme, `Hᵖ(X, -)` carries the colimit expressing a quasi-coherent module as the filtered colimit
of its quasi-coherent finite-type subobjects to a colimit, by [Stacks, Tag 01FF]: the two
topological hypotheses of [Stacks, Tag 0069] hold for a scheme, and `⊤` is quasi-compact. -/
theorem nonempty_isColimit_mapCocone_hfunctor (F : X.Modules) [F.IsQuasicoherent]
    [CompactSpace ↥X] [QuasiSeparatedSpace ↥X] (p : ℕ) :
    Nonempty (IsColimit ((Hfunctor X.ringCatSheaf ⊤ p).mapCocone
      (finiteTypeQuasicoherentSmallPresentation F).cocone)) := by
  let : IsFiltered (SmallModel (FiniteTypeQuasicoherentSubobject F)) := isFiltered_smallModel F
  let : IsIso (colimit.post (finiteTypeQuasicoherentSmallPresentation F).diag
      (Hfunctor X.ringCatSheaf ⊤ p)) :=
    Stacks.Cohomology.Vanishing.isIso_colimit_post_Hfunctor_of_isCompact X.ringCatSheaf
      inferInstance inferInstance (finiteTypeQuasicoherentSmallPresentation F).diag ⊤
      (by simpa using isCompact_univ (X := ↥X)) p
  have hp : PreservesColimit (finiteTypeQuasicoherentSmallPresentation F).diag
      (Hfunctor X.ringCatSheaf ⊤ p) := preservesColimit_of_isIso_post _ _
  exact hp.preserves (finiteTypeQuasicoherentSmallPresentation F).isColimit

/-- **The colimit hypothesis of the Tag 0EBD reduction, proved.**  The `hcolim` argument of
`Stacks.HighTwistDevissage.isAffine_of_isZero_cohomology_negative_tensorPower`: every
quasi-coherent module has a presentation as a small filtered colimit of quasi-coherent modules of
finite type whose image under `Hᵖ(X, -)` is again a colimit.

The consumer asks this only in positive degrees; it is proved in **every** degree, because Tag
01FF is, so the positivity hypothesis is not stated here and is discarded at the call site. -/
theorem exists_colimitPresentation_mapCocone_hfunctor
    [CompactSpace ↥X] [QuasiSeparatedSpace ↥X] (p : ℕ) (F : X.Modules)
    (hF : F.IsQuasicoherent) :
    ∃ (J : Type u) (_ : SmallCategory J) (pres : ColimitPresentation J F),
      (∀ j, (pres.diag.obj j).IsQuasicoherent) ∧
      (∀ j, SheafOfModules.IsFiniteType.{u, u, u} (pres.diag.obj j)) ∧
      Nonempty (IsColimit ((Hfunctor X.ringCatSheaf ⊤ p).mapCocone pres.cocone)) := by
  let : F.IsQuasicoherent := hF
  exact ⟨SmallModel (FiniteTypeQuasicoherentSubobject F), inferInstance,
    finiteTypeQuasicoherentSmallPresentation F,
    fun j => (isQuasicoherent_and_isFiniteType_diag_obj F j).1,
    fun j => (isQuasicoherent_and_isFiniteType_diag_obj F j).2,
    nonempty_isColimit_mapCocone_hfunctor F p⟩

/-- **Serre's cohomological criterion for affineness, in the form the Tag 0EBD reduction wants
it.**  The `serre` argument of
`Stacks.HighTwistDevissage.isAffine_of_isZero_cohomology_negative_tensorPower`, proved: it asks
for the vanishing of `Hᵖ` on every quasi-coherent module in every positive degree, and
[Stacks, Tag 01XF] needs only degree one and only the quasi-coherent sheaves of ideals.

This is `Stacks.SerreCriterionH1.isAffine_of_forall_isZero_hgroup_one_ideal`, which is
already stated at `Hgroup` -- the abelian-group-valued cohomology used here -- rather
than at the module-valued right derived functor the Tag 01XF attribute sits on; the two are
bridged there by [Stacks, Tag 01F1]. -/
theorem isAffine_of_forall_isZero_hgroup (hX : CompactSpace ↥X)
    (hvanish : ∀ (F : X.Modules) (p : ℕ), 0 < p → F.IsQuasicoherent →
      IsZero (Hgroup X.ringCatSheaf ⊤ p F)) :
    IsAffine X :=
  let : CompactSpace ↥X := hX
  Stacks.SerreCriterionH1.isAffine_of_forall_isZero_hgroup_one_ideal X
    fun I hI => hvanish (Subobject.underlying.obj I) 1 Nat.one_pos hI

/-- **[Stacks, Tag 0EBD] from two hypotheses and quasi-separatedness.**  A scheme carrying an
ample invertible module whose sufficiently negative tensor powers have no higher cohomology is
affine.

This is `Stacks.HighTwistDevissage.isAffine_of_isZero_cohomology_negative_tensorPower` with two
of its four hypotheses discharged: the colimit reduction ([Stacks, Tag 01PG] with
[Stacks, Tag 01FF]) by `exists_colimitPresentation_mapCocone_hfunctor`, and Serre's criterion
([Stacks, Tag 01XF]) by `isAffine_of_forall_isZero_hgroup`.  What is left is a cohomological
vanishing bound on quasi-coherent modules ([Stacks, Tag 01XI]), the dévissage sequence from
global generation after an ample twist for the modules of finite type ([Stacks, Tag 01Q3], clause
(8)), and quasi-separatedness of the underlying space -- which follows from ampleness, and which
is used by both of the discharged lemmas.

`isAffine_of_isZero_cohomology_negative_tensorPower` discharges all three and is the tag
itself. -/
theorem isAffine_of_isZero_cohomology_negative_tensorPower_of_quasiSeparated
    [QuasiSeparatedSpace ↥X] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (hL : Stacks.Ample.IsAmple X L) {n₀ : ℤ}
    (hvan : ∀ (n : ℤ) (p : ℕ), n₀ ≤ n → 0 < p →
      IsZero (Hgroup X.ringCatSheaf ⊤ p (Stacks.Ample.tensorPowModule X L (-n))))
    (e : ℕ)
    (hdim : ∀ (F : X.Modules) (p : ℕ), e < p → F.IsQuasicoherent →
      IsZero (Hgroup X.ringCatSheaf ⊤ p F))
    (hgen : ∀ F : X.Modules, F.IsQuasicoherent → SheafOfModules.IsFiniteType.{u, u, u} F →
      ∃ (S : ShortComplex X.Modules) (r : ℕ) (d : Fin r → ℤ)
        (b : Bicone fun j : Fin r => Stacks.Ample.tensorPowModule X L (-(d j)))
        (_ : b.IsBilimit) (_ : S.X₂ ≅ b.pt),
        S.ShortExact ∧ S.X₃ = F ∧ S.X₁.IsQuasicoherent ∧ ∀ j, n₀ ≤ d j) :
    IsAffine X :=
  let : CompactSpace ↥X := hL.1
  Stacks.HighTwistDevissage.isAffine_of_isZero_cohomology_negative_tensorPower X L hL hvan
    isAffine_of_forall_isZero_hgroup e hdim hgen
    fun p _ F hF => exists_colimitPresentation_mapCocone_hfunctor p F hF

/-- **[Stacks, Tag 0EBD].** Let `L` be an ample invertible module on a scheme `X` and let `n₀` be
an integer such that `Hᵖ(X, L^{⊗ -n}) = 0` for every `n ≥ n₀` and every `p > 0`. Then `X` is
affine.

Everything the dévissage of the tag needs beyond this hypothesis comes from ampleness itself:
quasi-compactness is part of ampleness and quasi-separatedness follows from it
([Stacks, Tag 01PV]), which makes the colimit reduction ([Stacks, Tag 01PG] with
[Stacks, Tag 01FF]) available and supplies a degree beyond which the cohomology of every
quasi-coherent module vanishes ([Stacks, Tag 071L], in the form
`AlgebraicGeometry.exists_isZero_hgroup_top`); the dévissage sequence presenting a quasi-coherent
module of finite type as a quotient of a finite direct sum of negative twists of `L` is clause
(8) of [Stacks, Tag 01Q3]; and the vanishing of `Hᵖ` on all quasi-coherent modules in all
positive degrees gives affineness by Serre's criterion ([Stacks, Tag 01XF]). -/
@[stacks 0EBD]
theorem isAffine_of_isZero_cohomology_negative_tensorPower (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L) (n₀ : ℤ)
    (hvan : ∀ (n : ℤ) (p : ℕ), n₀ ≤ n → 0 < p →
      IsZero (Hgroup X.ringCatSheaf ⊤ p (Stacks.Ample.tensorPowModule X L (-n)))) :
    IsAffine X :=
  let _ : CompactSpace ↥X := hL.1
  let _ : QuasiSeparatedSpace ↥X :=
    Stacks.AmplePullbackPart1.quasiSeparatedSpace_of_isAmple L hL
  have ⟨N, hN⟩ := AlgebraicGeometry.exists_isZero_hgroup_top X
  isAffine_of_isZero_cohomology_negative_tensorPower_of_quasiSeparated L hL hvan N
    (fun F p hp hF => hN F hF p hp.le)
    (Stacks.AmpleLocalGeneration.isQuotientOfNegativeTwists_of_isAmple L hL n₀)

end Stacks.AlgebraicGeometry.CohomologyColimitReduction

end
