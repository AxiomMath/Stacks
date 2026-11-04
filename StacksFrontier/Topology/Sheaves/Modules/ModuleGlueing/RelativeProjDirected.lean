module

public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.Descent
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjTwist
/-!
# The twisting sheaves of a relative projective spectrum, from directed chart data

`StacksFrontier/Topology/Sheaves/Modules/ModuleGlueing/RelativeProjTwist.lean` glues the absolute
twisting sheaves of the charts of a relative projective spectrum into `O_{Proj(s)}(n)`, with the
*pairwise* transition datum `Stacks.RelativeProj.Situation.TwistTransition` as a hypothesis. But
the relative `Proj` is glued over a locally directed cover: the comparison morphism of charts
`Stacks.RelativeProj.Situation.projInclusionMap` exists only for an inclusion `W ≤ W'` of affine
opens of the base, and since `W ⊓ W'` need not be affine there is no chart over it to compare the
charts over `W` and `W'` through. So a pairwise transition datum cannot be written down directly,
and that was the structural obstruction to Stacks 01NR.

This file removes it. The two topological hypotheses of
`Stacks.SheafOfModules.ModulesDirectedGlueData` are discharged for the charts of a relative `Proj`
— they are monotonicity of `W ↦ Proj (s.sectionRingGrading W)` and the fact that the affine opens
contained in `W ⊓ W'` cover it — and the directed transition datum
`Stacks.RelativeProj.Situation.DirectedTwistTransition`, which asks for a comparison only along an
inclusion `W ≤ W'`, is turned into a `TwistTransition` by the descent of
`StacksFrontier/Topology/Sheaves/Modules/ModuleGlueing/Descent.lean`.

What remains for Stacks 01NR is therefore exactly the *chart-level* content of Stacks 01NO clauses
(3) and (4): the comparison `θ_n` of twisting sheaves across `projInclusionMap`, which is a
statement about two absolute projective spectra and the morphism between them, with no glueing in
it. `DirectedTwistTransition` is the signature that content has to be delivered in.

Accordingly nothing here may be read as a proof of Stacks 01NR either: `twist` below is still
parameterised by a `DirectedTwistTransition`. The tag belongs on the unconditional form, once that
structure is constructed.

## Main definitions

* `Stacks.RelativeProj.Situation.DirectedTwistTransition`: directed transition data for the chart
  twists — a comparison for each inclusion `W ≤ W'` of affine opens of the base, functorial in the
  inclusion.
* `Stacks.RelativeProj.Situation.DirectedTwistTransition.toModulesDirectedGlueData`: the chart
  twists and a directed transition datum, as a locally directed glueing datum of sheaves of
  modules.
* `Stacks.RelativeProj.Situation.DirectedTwistTransition.toTwistTransition`: **the pairwise
  transition datum obtained from a directed one.** This is the descent step 01NR was blocked on.
* `Stacks.RelativeProj.Situation.DirectedTwistTransition.twist`: `O_{Proj(s)}(n)`, glued from the
  chart twists along directed transition data.

## Main results

* `Stacks.RelativeProj.Situation.locallyDirected_relativeProjChart`: **the charts of a relative
  projective spectrum form a locally directed cover.**
* `Stacks.RelativeProj.Situation.DirectedTwistTransition.toTwistTransition_trans_eq`: the glued
  pairwise comparison of the charts over `W` and `W'` is the comparison through the chart over any
  affine open `W'' ≤ W ⊓ W'`.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.SheafOfModules

universe u

namespace Stacks.RelativeProj.Situation

variable (s : Situation.{u})

/-- The charts of a relative projective spectrum are ordered by inclusion of affine opens of the
base. -/
theorem opensRange_relativeProjChart_mono {W W' : s.base.affineOpens} (h : W ≤ W') :
    (relativeProjChart s W).opensRange ≤ (relativeProjChart s W').opensRange := by
  rw [opensRange_relativeProjChart, opensRange_relativeProjChart]
  exact fun x hx => h hx

/-- **The charts of a relative projective spectrum form a locally directed cover**: the overlap of
the charts over two affine opens `W`, `W'` of the base is covered by the charts over the affine
opens contained in `W ⊓ W'`. This is the hypothesis that a pairwise glueing datum cannot be read
off directly, and the reason the transition data of a relative `Proj` is directed rather than
pairwise. -/
theorem locallyDirected_relativeProjChart (W W' : s.base.affineOpens) :
    (relativeProjChart s W).opensRange ⊓ (relativeProjChart s W').opensRange
      ≤ ⨆ m : {m : s.base.affineOpens // m ≤ W ∧ m ≤ W'},
          (relativeProjChart s m.1).opensRange := by
  rw [opensRange_relativeProjChart, opensRange_relativeProjChart]
  intro x hx
  obtain ⟨-, ⟨V, hVaff, rfl⟩, hxV, hVle⟩ :=
    s.base.isBasis_affineOpens.exists_subset_of_mem_open
      (show relativeProjToBase s x ∈ ((W.1 ⊓ W'.1 : s.base.Opens) : Set s.base) from ⟨hx.1, hx.2⟩)
      (W.1 ⊓ W'.1).isOpen
  refine TopologicalSpace.Opens.mem_iSup.mpr
    ⟨⟨⟨V, hVaff⟩, fun y hy => (hVle hy).1, fun y hy => (hVle hy).2⟩, ?_⟩
  rw [opensRange_relativeProjChart]
  exact hxV

variable (n : ℤ)

/-- **Directed transition data for the chart twists of a relative projective spectrum**: for each
*inclusion* `W ≤ W'` of affine opens of the base and each open `V` of the relative `Proj` lying in
the chart over `W`, a comparison of the sections of the two chart twists over `V`, linear over the
functions on `V`, commuting with restriction and functorial in the inclusion.

This is the shape in which Stacks 01NO clauses (3) and (4) actually produce transition data: the
comparison `θ_n : r^* O_{Proj(A')}(n) ≅ O_{Proj(A)}(n)` exists across the morphism of projective
spectra `Stacks.RelativeProj.Situation.projInclusionMap` induced by the restriction of graded
section rings, which is defined only for `W ≤ W'`. There is in general no chart over `W ⊓ W'`, so
there is no comparison of the charts over `W` and `W'` to be had directly;
`Stacks.RelativeProj.Situation.DirectedTwistTransition.toTwistTransition` manufactures one by
descent along the locally directed cover. -/
structure DirectedTwistTransition where
  /-- The comparison of the sections of the two chart twists over `V`. -/
  trans : ∀ {W W' : s.base.affineOpens} (_h : W ≤ W') {V : (relativeProj s).Opens}
    (_hV : V ≤ (relativeProjChart s W).opensRange),
    openSections (relativeProjChart s W) (twistChart s n W) V
      ≃ₗ[ToType ((relativeProj s).ringCatSheaf.obj.obj (op V))]
      openSections (relativeProjChart s W') (twistChart s n W') V
  /-- The comparisons commute with the restriction maps. -/
  trans_map : ∀ {W W' : s.base.affineOpens} (h : W ≤ W') {V U : (relativeProj s).Opens}
      (hV : V ≤ (relativeProjChart s W).opensRange) (hUV : U ≤ V)
      (t : ToType (openSections (relativeProjChart s W) (twistChart s n W) V)),
    trans h (hUV.trans hV)
        (((Scheme.Modules.pushforward (relativeProjChart s W)).obj
          (twistChart s n W)).val.map (homOfLE hUV).op t)
      = ((Scheme.Modules.pushforward (relativeProjChart s W')).obj
          (twistChart s n W')).val.map (homOfLE hUV).op (trans h hV t)
  /-- The comparisons are functorial in the inclusion. -/
  trans_trans : ∀ {W W' W'' : s.base.affineOpens} (h : W ≤ W') (h' : W' ≤ W'')
      {V : (relativeProj s).Opens} (hV : V ≤ (relativeProjChart s W).opensRange)
      (t : ToType (openSections (relativeProjChart s W) (twistChart s n W) V)),
    trans h' (hV.trans (opensRange_relativeProjChart_mono s h)) (trans h hV t)
      = trans (h.trans h') hV t

namespace DirectedTwistTransition

variable {s n} (t : DirectedTwistTransition s n)

/-- The chart twists of a relative projective spectrum, together with directed transition data, as
a locally directed glueing datum of sheaves of modules on the relative `Proj`. -/
noncomputable def toModulesDirectedGlueData :
    ModulesDirectedGlueData (relativeProj s) (relativeProjChart s) where
  mod := twistChart s n
  opensRange_mono := opensRange_relativeProjChart_mono s
  locallyDirected := locallyDirected_relativeProjChart s
  trans := t.trans
  trans_map := t.trans_map
  trans_trans := t.trans_trans

/-- **Directed transition data for the chart twists yields pairwise transition data.** This is the
descent step that unblocks Stacks 01NR: `Stacks.SheafOfModules.ModulesGlueData` — the form of
Stacks 00AM that the glueing of `O_{Proj(s)}(n)` goes through — demands a comparison of any two
charts over an *arbitrary* open `V` lying in both, and a relative `Proj` is glued over a locally
directed cover which supplies comparisons only along inclusions. The pairwise comparison is glued
from the comparisons through the charts over the affine opens contained in `W ⊓ W'`. -/
noncomputable def toTwistTransition : TwistTransition s n where
  trans := t.toModulesDirectedGlueData.toModulesGlueData.trans
  trans_map := t.toModulesDirectedGlueData.toModulesGlueData.trans_map
  trans_trans := t.toModulesDirectedGlueData.toModulesGlueData.trans_trans

/-- `O_{Proj(s)}(n)`, glued from the chart twists along directed transition data. -/
noncomputable abbrev twist : (relativeProj s).Modules :=
  Situation.twist t.toTwistTransition

/-- `O_{Proj(s)}(n)` restricts on the chart over `W` to the absolute twisting sheaf `O(n)` of
`Proj (s.sectionRingGrading W)`. -/
noncomputable abbrev twistChartIso (W : s.base.affineOpens) :
    (t.twist).restrict (relativeProjChart s W) ≅ twistChart s n W :=
  Situation.twistChartIso t.toTwistTransition W

/-- **The pairwise comparison is the comparison through the chart over `W''`** whenever
`W'' ≤ W ⊓ W'` and `V` lies in the chart over `W''`. Together with the sheaf condition this
characterises the glued transition datum. -/
theorem toTwistTransition_trans_eq {W W' W'' : s.base.affineOpens} (h : W'' ≤ W) (h' : W'' ≤ W')
    {V : (relativeProj s).Opens} (hV : V ≤ (relativeProjChart s W'').opensRange)
    (x : ToType (openSections (relativeProjChart s W) (twistChart s n W) V)) :
    t.toTwistTransition.trans W W'
        (hV.trans (opensRange_relativeProjChart_mono s h))
        (hV.trans (opensRange_relativeProjChart_mono s h')) x
      = t.trans h' hV ((t.trans h hV).symm x) :=
  t.toModulesDirectedGlueData.pairTrans_eq W W' h h' hV x

/-- **The pairwise comparison from the chart over `W` down to the chart over a smaller affine open
`W'` is the inverse of the directed comparison attached to `W' ≤ W`**, over an open lying in the
chart over `W'`. This is the case `W'' = W'` of `toTwistTransition_trans_eq`, where the second leg
of the comparison through `W''` is the identity. -/
theorem toTwistTransition_trans_eq_trans_symm {W W' : s.base.affineOpens} (h : W ≤ W')
    {V : (relativeProj s).Opens} (hV : V ≤ (relativeProjChart s W).opensRange)
    (x : ToType (openSections (relativeProjChart s W') (twistChart s n W') V)) :
    t.toTwistTransition.trans W' W (hV.trans (opensRange_relativeProjChart_mono s h)) hV x
      = (t.trans h hV).symm x :=
  t.toModulesDirectedGlueData.pairTrans_eq_trans_symm h hV x

end DirectedTwistTransition

end Stacks.RelativeProj.Situation

end
