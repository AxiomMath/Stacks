module

public import Mathlib.AlgebraicGeometry.Properties
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismToAffineScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace

/-!
# Global regular functions of a reduced algebraic space

Let `F` be an algebraic space over a scheme `S` of a big fppf site.  Its global regular
functions `AlgebraicGeometry.Space.globalFunctions` are the compatible families of regular
functions on its étale charts, that is the sections of the structure presheaf of the small
étale site.  This file proves the two remaining assertions of Stacks 0BGS about them when `F`
is reduced: the ring of global functions is reduced, and a global function whose vanishing
locus is all of `F` is zero.

Both come from one observation.  A surjective étale chart covers the final object of the small
étale site, so restriction of global functions to it is injective — the structure presheaf is
a sheaf, and a sheaf separates sections over a covering family.  A reduced algebraic space has
a surjective étale chart whose underlying scheme is reduced, by the very definition of
reducedness through the étale-local property of Stacks 03E6.  Restriction to that chart
therefore embeds the global functions of `F` into the global functions of a reduced scheme,
which gives reducedness, and it detects vanishing, which gives the second assertion through
`AlgebraicGeometry.eq_zero_of_basicOpen_eq_bot`.

## Main results

* `AlgebraicGeometry.Space.injective_globalFunctions_val_of_isSurjective` and
  `AlgebraicGeometry.Space.injective_globalFunctionsChartRestriction_of_isSurjective`:
  restriction of global functions to an étale chart which is surjective on points is
  injective.
* `AlgebraicGeometry.Space.exists_isReduced_chart_injective_globalFunctions`: a reduced
  algebraic space has an étale chart with reduced underlying scheme to which restriction of
  global functions is injective.
* `AlgebraicGeometry.Space.sectionSupport_eq_empty_iff`: the vanishing locus of a global
  function is all of `F` exactly when its zero locus on every étale chart is the whole chart.
* `AlgebraicGeometry.Space.isReduced_globalFunctions`: **Stacks 0BGS**, the global regular
  functions of a reduced algebraic space form a reduced ring.
* `AlgebraicGeometry.Space.eq_zero_of_forall_zeroLocus_eq_univ`: **Stacks 0BGS**, a global
  regular function on a reduced algebraic space whose vanishing locus is all of `F` is zero,
  with `AlgebraicGeometry.Space.eq_zero_of_sectionSupport_eq_empty` the same statement phrased
  through the support of a global function.

## Implementation notes

Reducedness of `F` is `AlgebraicGeometry.Space.HasEtaleLocalProperty` for reducedness of
schemes, the étale-local property of Stacks 03E6; destructuring it hands over a surjective
étale chart with reduced underlying scheme directly, so Stacks 03E8 is not needed.  The
covering fact is `AlgebraicGeometry.Space.SmallEtale.coversTop_of_isSurjective`, already
available for Stacks 03M0, and the separation it feeds is Mathlib's
`CategoryTheory.GrothendieckTopology.CoversTop.sections_ext` at the one-element index type.
The sheaf is the structure presheaf composed with the forgetful functor to types, a sheaf by
`AlgebraicGeometry.Space.isSheaf_globalSections`.

Stacks 0BGS writes the hypothesis of its last assertion as `X = V(f)`.  Two renderings of it
are given and proved equivalent in `sectionSupport_eq_empty_iff`: vanishing of
`AlgebraicGeometry.Space.sectionSupport`, the set of points of `F` at which `f` does not
vanish, and the chartwise condition that `Scheme.zeroLocus {f}` is the whole of every étale
chart.  They differ only in whether the points are read on `F` or on its charts, and
`AlgebraicGeometry.Space.surjective_pointsToScheme` matches the two.

## References

* [Stacks Project, Tag 0BGS](https://stacks.math.columbia.edu/tag/0BGS)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

/-- A section of the structure sheaf of a scheme over an open set vanishes at every point of
the scheme exactly when its basic open set is empty. -/
theorem Scheme.zeroLocus_singleton_eq_univ_iff {X : Scheme.{u}} {W : X.Opens} (r : Γ(X, W)) :
    X.zeroLocus {r} = Set.univ ↔ X.basicOpen r = ⊥ := by
  rw [Scheme.zeroLocus_singleton, Set.compl_univ_iff, ← TopologicalSpace.Opens.coe_inj,
    TopologicalSpace.Opens.coe_bot]

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-! ### Restriction of global functions to a surjective étale chart -/

/-- Restriction of global regular functions to an étale chart whose structure morphism is
surjective on points is injective: the chart covers the final object of the small étale site
by `AlgebraicGeometry.Space.SmallEtale.coversTop_of_isSurjective`, and the structure presheaf
is a sheaf, so it separates sections over that covering. -/
theorem injective_globalFunctions_val_of_isSurjective (hF : IsAlgebraicSpace B S hS F)
    (V : SmallEtale B S hS F) (hV : IsSurjective B S hS V.obj.hom) :
    Function.Injective fun s : globalFunctions B S hS F => s.val (op V) := by
  intro x y hxy
  exact (SmallEtale.coversTop_of_isSurjective B S hS F hF V hV).sections_ext
    ⟨structurePresheaf B S hS F ⋙ CategoryTheory.forget CommRingCat.{u},
      (isSheaf_iff_isSheaf_of_type _ _).2 (isSheaf_globalSections B S hS F)⟩
    fun _ => hxy

/-- `AlgebraicGeometry.Space.globalFunctionsChartRestriction` at an étale chart whose structure
morphism is surjective on points is injective. -/
theorem injective_globalFunctionsChartRestriction_of_isSurjective
    (X : AlgebraicSpaces B S hS) (V : SmallEtale B S hS X.obj)
    (hV : IsSurjective B S hS V.obj.hom) :
    Function.Injective (globalFunctionsChartRestriction B S hS X V) :=
  injective_globalFunctions_val_of_isSurjective B S hS X.obj X.property V hV

/-- A reduced algebraic space has an étale chart whose underlying scheme is reduced and to
which restriction of global regular functions is injective.  Reducedness of `F` is the
étale-local property of Stacks 03E6, which supplies a surjective étale chart with reduced
underlying scheme; `injective_globalFunctions_val_of_isSurjective` makes restriction to it
injective. -/
theorem exists_isReduced_chart_injective_globalFunctions (hF : IsAlgebraicSpace B S hS F)
    (hred : HasEtaleLocalProperty B S hS F
      (fun X : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced X)) :
    ∃ V : SmallEtale B S hS F,
      _root_.AlgebraicGeometry.IsReduced ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj V)) ∧
      Function.Injective fun s : globalFunctions B S hS F => s.val (op V) := by
  obtain ⟨U, φ, hsurj, hetale, hredU⟩ := hred
  exact ⟨⟨CostructuredArrow.mk φ, hetale⟩, hredU, injective_globalFunctions_val_of_isSurjective
    B S hS F hF _ ((presheafSurjective_iff_isSurjective_yoneda B S hS F hF U φ).1 hsurj)⟩

/-! ### The vanishing locus of a global function -/

/-- The zero locus of the value of a global regular function on an étale chart is the whole
chart exactly when the basic open of that value is empty. -/
theorem zeroLocus_val_eq_univ_iff (f : globalFunctions B S hS F) (U : SmallEtale B S hS F) :
    ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj U)).zeroLocus
        {f.val (op U)} = Set.univ ↔
      ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj U)).basicOpen
        (f.val (op U)) = ⊥ :=
  Scheme.zeroLocus_singleton_eq_univ_iff _

/-- The two readings of the vanishing locus of a global regular function being all of `F`: the
support `AlgebraicGeometry.Space.sectionSupport`, the points of `F` at which the function does
not vanish, is empty exactly when the scheme-theoretic zero locus of the function on every
étale chart is the whole chart.  The points of a chart exhaust the points of `F` lying under
it by `AlgebraicGeometry.Space.surjective_pointsToScheme`. -/
theorem sectionSupport_eq_empty_iff (f : globalFunctions B S hS F) :
    sectionSupport B S hS F f = ∅ ↔
      ∀ U : SmallEtale B S hS F,
        ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj U)).zeroLocus
          {f.val (op U)} = Set.univ := by
  constructor
  · intro h U
    refine (zeroLocus_val_eq_univ_iff B S hS F f U).2 ?_
    apply SetLike.coe_injective
    rw [TopologicalSpace.Opens.coe_bot]
    refine Set.eq_empty_of_forall_notMem fun x hx => ?_
    obtain ⟨p, rfl⟩ := surjective_pointsToScheme B S hS U.obj.left x
    simpa [h] using (mem_sectionSupport_iff B S hS F f U p).2 hx
  · intro h
    refine Set.eq_empty_of_forall_notMem ?_
    rintro x ⟨U, p, hp, -⟩
    have hp' : pointsToScheme B S hS U.obj.left p ∈
        ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj U)).basicOpen
          (f.val (op U)) := hp
    rwa [(zeroLocus_val_eq_univ_iff B S hS F f U).1 (h U)] at hp'

/-! ### Stacks 0BGS -/

/-- **Stacks 0BGS.** The ring of global regular functions of a reduced algebraic space is
reduced.  Restriction to a reduced surjective étale chart embeds it into the ring of global
regular functions of a reduced scheme. -/
@[stacks 0BGS "global_sections_reduced"]
theorem isReduced_globalFunctions (hF : IsAlgebraicSpace B S hS F)
    (hred : HasEtaleLocalProperty B S hS F
      (fun X : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced X)) :
    _root_.IsReduced (globalFunctions B S hS F) := by
  obtain ⟨V, hVred, hinj⟩ := exists_isReduced_chart_injective_globalFunctions B S hS F hF hred
  have : _root_.AlgebraicGeometry.IsReduced ((BigFppfOver.toScheme B S hS).obj
    ((SmallEtale.toOver B S hS F).obj V)) := hVred
  have hinj' : Function.Injective
      (globalFunctionsChartRestriction B S hS (⟨F, hF⟩ : AlgebraicSpaces B S hS) V) := hinj
  exact isReduced_of_injective _ hinj'

/-- **Stacks 0BGS.** A global regular function on a reduced algebraic space whose vanishing
locus is all of `F` — its zero locus on every étale chart is the whole chart — is zero.  It
vanishes on a reduced surjective étale chart, hence is zero there by
`AlgebraicGeometry.eq_zero_of_basicOpen_eq_bot`, and restriction to that chart is injective. -/
@[stacks 0BGS "zero_of_full_vanishing_locus"]
theorem eq_zero_of_forall_zeroLocus_eq_univ (hF : IsAlgebraicSpace B S hS F)
    (hred : HasEtaleLocalProperty B S hS F
      (fun X : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced X))
    (f : globalFunctions B S hS F)
    (hf : ∀ U : SmallEtale B S hS F,
      ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj U)).zeroLocus
        {f.val (op U)} = Set.univ) :
    f = 0 := by
  obtain ⟨V, hVred, hinj⟩ := exists_isReduced_chart_injective_globalFunctions B S hS F hF hred
  have : _root_.AlgebraicGeometry.IsReduced ((BigFppfOver.toScheme B S hS).obj
    ((SmallEtale.toOver B S hS F).obj V)) := hVred
  -- Name the value of `f` at `V` with its scheme-theoretic type, so that the basic-open
  -- lemmas of `Scheme` apply to it without unfolding the structure presheaf.
  obtain ⟨r, hr⟩ : ∃ r : Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj V), ⊤), r = f.val (op V) := ⟨f.val (op V), rfl⟩
  have hbot : ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj V)).basicOpen r = ⊥ :=
    (Scheme.zeroLocus_singleton_eq_univ_iff r).1 (hr ▸ hf V)
  exact hinj (hr.symm.trans (AlgebraicGeometry.eq_zero_of_basicOpen_eq_bot r hbot))

/-- **Stacks 0BGS**, with the hypothesis `F = V(f)` read on the points of `F`: a global regular
function with empty support on a reduced algebraic space is zero.  This is
`eq_zero_of_forall_zeroLocus_eq_univ` across `sectionSupport_eq_empty_iff`. -/
theorem eq_zero_of_sectionSupport_eq_empty (hF : IsAlgebraicSpace B S hS F)
    (hred : HasEtaleLocalProperty B S hS F
      (fun X : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced X))
    (f : globalFunctions B S hS F) (hf : sectionSupport B S hS F f = ∅) :
    f = 0 :=
  eq_zero_of_forall_zeroLocus_eq_univ B S hS F hF hred f
    ((sectionSupport_eq_empty_iff B S hS F f).1 hf)

end Space

end AlgebraicGeometry

end
