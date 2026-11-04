module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.Defined
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFiniteFreeSummand.OnSpace
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomFiniteFree
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.LocallyBoundedDerivedDual
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.CohomologyFiniteness
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.LocallyStrictlyPerfectComplex

/-!
# The derived dual of the complex of an envelope presentation

Let `Y` be a scheme and let `𝓔^•` be a locally bounded complex of finite locally free
`𝒪_Y`-modules — the complex of an envelope presentation of [Stacks, Tag 0F9E] (1), as produced by
`Stacks.Chow.EnvelopePresentation`. This file identifies the derived dual of the object of
`D(𝒪_Y)` that `𝓔^•` represents with the class of the ordinary internal Hom complex of `𝓔^•`
into the structure sheaf:

`(Q 𝓔^•)^∨ ≅ Q(SheafHom^•(𝓔^•, 𝒪_Y))`.

This is the half of [Stacks, Tag 0FAE] that is about the derived category rather than about Chow
groups. The other half, the sign rules for the characteristic classes of a termwise dual complex,
is `StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.DualComplexChern`.

## Main results

* `Stacks.Chow.isLocallyStrictlyPerfect_of_isLocallyBoundedFiniteLocallyFree` — the local
  boundedness condition of [Stacks, Tag 0GUJ] is the local strict perfectness of
  [Stacks, Tag 0FP9].
* `Stacks.Chow.locallyBoundedSplit_of_isLocallyStrictlyPerfect` — local strict perfectness read
  at the slice sites, which is the hypothesis
  `Stacks.SheafOfModules.derivedDualQIso` consumes.
* `Stacks.Chow.derivedDualQIsoOfLocallyBounded` — **`(Q 𝓔^•)^∨ ≅ Q(SheafHom^•(𝓔^•, 𝒪_Y))`.**

## Implementation notes

### Why the global form of Tag 08DM does not apply

`Stacks.SheafOfModules.strictlyPerfectHomComparison_isIso` asks the source to be bounded on `Y`
with every term a direct summand of a finite free `𝒪_Y`-module. Neither holds here: the complex
of an envelope presentation is only *locally* bounded, and on an envelope that is not
quasi-compact no global bound exists; and a finite locally free module is not in general a global
summand of a finite free one — on `P^1` there is no nonzero morphism `𝒪(1) ⟶ 𝒪^{⊕n}` at all. The
input used instead is `Stacks.SheafOfModules.derivedDualQIso`, which asks only for the covering
form of the hypothesis.

### The three seams, all of which are `rfl`

A compiler probe established that no transport is paid in passing between the Chow vocabulary and
the ringed-space one: for `Y : Scheme`, the category `AlgebraicGeometry.Scheme.Modules Y` is
`SheafOfModules (structureSheafRing Y.toRingedSpace)` by `rfl`, so a Chow complex is directly a
complex of the kind `Stacks.SheafOfModules.OnSpace.IsLocallyStrictlyPerfect` speaks about; the
degree-`n` term of `AlgebraicGeometry.RingedSite.restrictComplex` at the site of opens is the
`SheafOfModules.over` of the term by `rfl`; and
`AlgebraicGeometry.RingedSite.sheafHomComplex (Stacks.SheafOfModules.ringedSite Y.sheaf) 𝓔^• 𝒪`
is itself an object of `CochainComplex Y.Modules ℤ`, which is the category
`Stacks.Chow.complexChern` is stated for.

### The one non-`rfl` passage

Local boundedness in the Chow sense is stated with
`StrictlyPerfect.restrictModules`, restriction to the *open subspace* `Y|_U`, while local
boundedness in the sense of [Stacks, Tag 0FP9] is stated with `SheafOfModules.over`, restriction
to the *slice site* over `U`. The two differ by the equivalence
`AlgebraicGeometry.RingedSpace.PseudoCoherence.sheafOfModulesEquivRestrict`, and
`AlgebraicGeometry.RingedSpace.overEquivRestrictedUnitIso` is its unit read at a module; a zero
object is carried to a zero object across it. (The underlying functors agree on the nose:
`AlgebraicGeometry.RingedSpace.restrictModulesIsoOverComp` is `Iso.refl`.)

## References

* [Stacks Project, Tag 0FAE](https://stacks.math.columbia.edu/tag/0FAE)
* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
* [Stacks Project, Tag 0F9E](https://stacks.math.columbia.edu/tag/0F9E)
* [Stacks Project, Tag 0FP9](https://stacks.math.columbia.edu/tag/0FP9)
* [Stacks Project, Tag 0GUJ](https://stacks.math.columbia.edu/tag/0GUJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open StrictlyPerfect

universe u

namespace Stacks.Chow

attribute [local instance] HasDerivedCategory.standard

/-- **A locally bounded complex of finite locally free modules is locally strictly perfect.**
The two conditions of `Stacks.SheafOfModules.OnSpace.IsStrictlyPerfectOn` are supplied
separately and `Stacks.SheafOfModules.OnSpace.isLocallyStrictlyPerfect_iff` assembles one
neighbourhood out of the per-degree ones: local boundedness is the first component of
`Stacks.Chow.IsLocallyBoundedFiniteLocallyFree`, read across the equivalence between modules on
the open subspace and modules on the slice site, and each term is locally a direct summand of a
finite free module by
`Stacks.SheafOfModules.OnSpace.isLocallyFiniteFreeSummand_of_isFiniteLocallyFree`. -/
theorem isLocallyStrictlyPerfect_of_isLocallyBoundedFiniteLocallyFree
    {X : RingedSpace.{u, u}} {P : CochainComplex (OXMod.{u, u, u} X) ℤ}
    (hP : IsLocallyBoundedFiniteLocallyFree P) :
    Stacks.SheafOfModules.OnSpace.IsLocallyStrictlyPerfect X P := by
  classical
  refine (Stacks.SheafOfModules.OnSpace.isLocallyStrictlyPerfect_iff X P).mpr ⟨fun x => ?_,
    fun i => ?_⟩
  · obtain ⟨U, hxU, lo, hi, hz⟩ := hP.2 x
    refine ⟨U, hxU, Finset.Icc lo hi, fun n hn => ?_⟩
    have hwin : n < lo ∨ hi < n := by
      rcases lt_or_ge n lo with h | h
      · exact Or.inl h
      · refine Or.inr ?_
        by_contra hc
        exact hn (Finset.mem_Icc.2 ⟨h, le_of_not_gt hc⟩)
    exact (Functor.map_isZero
      (AlgebraicGeometry.RingedSpace.PseudoCoherence.sheafOfModulesEquivRestrict X U).inverse
      (hz n hwin)).of_iso
        (AlgebraicGeometry.RingedSpace.overEquivRestrictedUnitIso X U (P.X n)).symm
  · exact @Stacks.SheafOfModules.OnSpace.isLocallyFiniteFreeSummand_of_isFiniteLocallyFree X
      (P.X i) (hP.1 i)

/-- **Local strict perfectness, read at the slice sites of the site of opens.** Every point has
an open neighbourhood over which the restriction of the complex has finitely many nonzero terms,
each of them a direct summand of a finite free module in the iterated-biproduct sense of
`AlgebraicGeometry.RingedSite.IsFiniteFreeSummand`.

This is the hypothesis `Stacks.SheafOfModules.derivedDualQIso` consumes. The degreewise
restriction to the slice is `AlgebraicGeometry.RingedSite.restrictComplex`, whose terms are the
`SheafOfModules.over` of the terms on the nose, and
`AlgebraicGeometry.RingedSite.isFiniteFreeSummand_of_retract_free` converts a retract of a free
module on a finite index type into the iterated-biproduct spelling. -/
theorem locallyBoundedSplit_of_isLocallyStrictlyPerfect {Y : Scheme.{u}}
    {P : CochainComplex Y.Modules ℤ}
    (hP : Stacks.SheafOfModules.OnSpace.IsLocallyStrictlyPerfect Y.toRingedSpace P) :
    ∀ x : (Y : TopCat.{u}), ∃ U : Opens (Y : TopCat.{u}), x ∈ U ∧
      {n : ℤ | ¬ IsZero ((AlgebraicGeometry.RingedSite.restrictComplex
        (Stacks.SheafOfModules.ringedSite Y.sheaf) P U).X n)}.Finite ∧
      ∀ n : ℤ, AlgebraicGeometry.RingedSite.IsFiniteFreeSummand
        ((Stacks.SheafOfModules.ringedSite Y.sheaf).over U)
        ((AlgebraicGeometry.RingedSite.restrictComplex
          (Stacks.SheafOfModules.ringedSite Y.sheaf) P U).X n) := by
  classical
  intro x
  obtain ⟨U, hxU, hU⟩ := hP x
  obtain ⟨s, hs⟩ := hU.boundedOn
  refine ⟨U, hxU, Set.Finite.subset s.finite_toSet fun n hn => ?_, fun n => ?_⟩
  · by_contra hns
    exact hn (hs n hns)
  · obtain ⟨r, ⟨ρ⟩⟩ := hU.summandOn n
    exact AlgebraicGeometry.RingedSite.isFiniteFreeSummand_of_retract_free
      ((Stacks.SheafOfModules.ringedSite Y.sheaf).over U) (ULift.{u} (Fin r)) ρ

/-- **`(Q 𝓔^•)^∨ ≅ Q(SheafHom^•(𝓔^•, 𝒪_Y))`** for a locally bounded complex `𝓔^•` of finite
locally free modules on a scheme `Y` — in particular for the complex of an envelope presentation
of [Stacks, Tag 0F9E] (1).

The derived dual of a perfect object is the derived internal Hom into the structure sheaf; this
says that for such a complex no injective resolution of the structure sheaf is needed, exactly as
[Stacks, Tag 08DM] says for a strictly perfect source, with the global bound and the global
splittings of that tag replaced by their local forms. -/
def derivedDualQIsoOfLocallyBounded {Y : Scheme.{u}} {P : CochainComplex Y.Modules ℤ}
    (hP : IsLocallyBoundedFiniteLocallyFree (X := Y.toRingedSpace) P) :
    Stacks.SheafOfModules.derivedDual Y.sheaf (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj (AlgebraicGeometry.RingedSite.sheafHomComplex
        (Stacks.SheafOfModules.ringedSite Y.sheaf) P
        (AlgebraicGeometry.RingedSite.structureSheafComplex
          (Stacks.SheafOfModules.ringedSite Y.sheaf))).obj :=
  Stacks.SheafOfModules.derivedDualQIso Y.sheaf P
    (locallyBoundedSplit_of_isLocallyStrictlyPerfect
      (isLocallyStrictlyPerfect_of_isLocallyBoundedFiniteLocallyFree hP))

end Stacks.Chow

end
