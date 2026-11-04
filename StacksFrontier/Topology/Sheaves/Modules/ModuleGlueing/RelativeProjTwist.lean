module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwist
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Charts.Descent
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.BaseChangeGluing
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.Basic

/-!
# The twisting sheaves of a relative projective spectrum (Stacks 01NR)

Let `s` be a relative `Proj` situation. Its relative projective spectrum
`Stacks.RelativeProj.Situation.relativeProj s` is glued from the absolute projective spectra
`Proj (s.sectionRingGrading W)` of the graded section rings over the affine opens `W` of the
base, and the chart over `W` is the open immersion
`Stacks.RelativeProj.Situation.relativeProjChart s W`. Each chart carries the absolute twisting
sheaf `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf` of Stacks 01MN, and
`O_{Proj(s)}(n)` is the sheaf of modules obtained by glueing those along the charts.

This file performs that glueing. The glueing machinery is
`Stacks.SheafOfModules.ModulesGlueData`, which takes a family of open immersions into the glued
scheme, and the only input it still needs is the *transition data*: for each pair of charts and
each open `V` of the relative `Proj` lying in both of their images, an `O(V)`-linear comparison
of the sections of the two chart twists over `V`, commuting with restriction and satisfying the
cocycle condition. That input is bundled here as
`Stacks.RelativeProj.Situation.TwistTransition`, and it is exactly the content of Stacks 01NO
clauses (3) and (4) — the comparison `θ_n : r^* O_{Proj(A')}(n) ≅ O_{Proj(A)}(n)` across the
morphism of projective spectra induced by a homomorphism of graded rings, and its compatibility
with the tensor products. Until that comparison is available the construction below is stated
with `TwistTransition` as a hypothesis, in the same way that
`Stacks.RelativeProj.Situation.localData` is stated with the two topological properties of the
comparison morphism of charts as hypotheses and
`StacksFrontier/AlgebraicGeometry/RelativeProj/Charts/Descent.lean` discharges them.

Accordingly nothing in this file may be read as a proof of Stacks 01NR: the tag belongs on the
unconditional form of `twist`, once `TwistTransition` is constructed.

## Main definitions

* `Stacks.RelativeProj.Situation.twistChart`: the absolute twisting sheaf `O(n)` on the chart of
  the relative `Proj` over an affine open of the base.
* `Stacks.RelativeProj.Situation.TwistTransition`: the transition data for the chart twists.
* `Stacks.RelativeProj.Situation.twistGlueData`: the chart twists and a transition datum, as a
  glueing datum of sheaves of modules on the relative `Proj`.
* `Stacks.RelativeProj.Situation.twist`: `O_{Proj(s)}(n)`, the glued sheaf of modules.

## Main results

* `Stacks.RelativeProj.Situation.twistChartIso`: `O_{Proj(s)}(n)` restricts on the chart over `W`
  to the absolute twisting sheaf `O(n)` of `Proj (s.sectionRingGrading W)`.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.SheafOfModules

universe u

namespace Stacks.RelativeProj.Situation

variable (s : Situation.{u}) (n : ℤ)

/-- The `n`-th twisting sheaf of the chart of a relative projective spectrum over an affine open
`W` of the base: the absolute twisting sheaf `O(n)` of Stacks 01MN on
`Proj (s.sectionRingGrading W)`. -/
noncomputable abbrev twistChart (W : s.base.affineOpens) :
    (AlgebraicGeometry.Proj (s.sectionRingGrading W.1)).Modules :=
  ProjectiveSpectrum.Proj.twistingSheaf (s.sectionRingGrading W.1) n

/-- Transition data for the twisting sheaves of a relative projective spectrum: for each pair of
charts and each open `V` of the relative `Proj` contained in the images of both, a comparison of
the sections of the two chart twists over `V`, linear over the functions on `V`, commuting with
restriction and satisfying the cocycle condition.

This is the content of Stacks 01NO clauses (3) and (4): the comparison
`θ_n : r^* O_{Proj(A')}(n) ≅ O_{Proj(A)}(n)` across the morphism of projective spectra induced by
a homomorphism of graded rings, read on sections over `V`. -/
structure TwistTransition where
  /-- The comparison of the sections of the two chart twists over `V`. -/
  trans : ∀ (i j : s.base.affineOpens) {V : (relativeProj s).Opens}
    (_hi : V ≤ (relativeProjChart s i).opensRange)
    (_hj : V ≤ (relativeProjChart s j).opensRange),
    openSections (relativeProjChart s i) (twistChart s n i) V
      ≃ₗ[ToType ((relativeProj s).ringCatSheaf.obj.obj (op V))]
      openSections (relativeProjChart s j) (twistChart s n j) V
  /-- The comparisons commute with the restriction maps. -/
  trans_map : ∀ (i j : s.base.affineOpens) {V W : (relativeProj s).Opens}
    (hi : V ≤ (relativeProjChart s i).opensRange)
    (hj : V ≤ (relativeProjChart s j).opensRange) (hWV : W ≤ V)
    (t : ToType (openSections (relativeProjChart s i) (twistChart s n i) V)),
    trans i j (hWV.trans hi) (hWV.trans hj)
        (((Scheme.Modules.pushforward (relativeProjChart s i)).obj
          (twistChart s n i)).val.map (homOfLE hWV).op t)
      = ((Scheme.Modules.pushforward (relativeProjChart s j)).obj
          (twistChart s n j)).val.map (homOfLE hWV).op (trans i j hi hj t)
  /-- The cocycle condition `θ j k ∘ θ i j = θ i k`. -/
  trans_trans : ∀ (i j k : s.base.affineOpens) {V : (relativeProj s).Opens}
    (hi : V ≤ (relativeProjChart s i).opensRange)
    (hj : V ≤ (relativeProjChart s j).opensRange)
    (hk : V ≤ (relativeProjChart s k).opensRange)
    (t : ToType (openSections (relativeProjChart s i) (twistChart s n i) V)),
    trans j k hj hk (trans i j hi hj t) = trans i k hi hk t

variable {s n}

/-- The chart twists of a relative projective spectrum, together with a transition datum, as a
glueing datum of sheaves of modules along the charts. -/
noncomputable def twistGlueData (t : TwistTransition s n) :
    ModulesGlueData (relativeProj s) (relativeProjChart s) where
  mod W := twistChart s n W
  trans := t.trans
  trans_map := t.trans_map
  trans_trans := t.trans_trans

/-- The sections of the chart twists are the members of the glueing datum. -/
@[simp] theorem twistGlueData_mod (t : TwistTransition s n) (W : s.base.affineOpens) :
    (twistGlueData t).mod W = twistChart s n W := rfl

/-- **The `n`-th twisting sheaf `O_{Proj(s)}(n)` of a relative projective spectrum**, glued from
the absolute twisting sheaves of its charts along the transition datum `t`. -/
noncomputable def twist (t : TwistTransition s n) : (relativeProj s).Modules :=
  (twistGlueData t).glued

/-- `O_{Proj(s)}(n)` restricts on the chart over `W` to the absolute twisting sheaf `O(n)` of
`Proj (s.sectionRingGrading W)`. -/
noncomputable def twistChartIso (t : TwistTransition s n) (W : s.base.affineOpens) :
    (twist t).restrict (relativeProjChart s W) ≅ twistChart s n W :=
  (twistGlueData t).chartIso W

/-- The sections of `O_{Proj(s)}(n)` over an open `V` lying in the chart over `W` are, linearly
over the functions on `V`, the sections of the absolute twisting sheaf `O(n)` over the preimage
of `V`. -/
noncomputable def twistSectionsIso (t : TwistTransition s n) (W : s.base.affineOpens)
    {V : (relativeProj s).Opens} (hV : V ≤ (relativeProjChart s W).opensRange) :
    (twist t).val.obj (op V) ≅ openSections (relativeProjChart s W) (twistChart s n W) V :=
  (twistGlueData t).chartSectionsIso W hV

/-- **Reading a section of `O_{Proj(s)}(n)` on the chart over `W` commutes with restriction.** -/
theorem twistSectionsIso_restrict (t : TwistTransition s n) (W : s.base.affineOpens)
    {V V' : (relativeProj s).Opens} (hV : V ≤ (relativeProjChart s W).opensRange)
    (hV'V : V' ≤ V) (x : ToType ((twist t).val.obj (op V))) :
    (twistSectionsIso t W (hV'V.trans hV)).hom ((twist t).val.restrictₛₗ (homOfLE hV'V).op x)
      = ((Scheme.Modules.pushforward (relativeProjChart s W)).obj
          (twistChart s n W)).val.restrictₛₗ (homOfLE hV'V).op ((twistSectionsIso t W hV).hom x) :=
  (twistGlueData t).chartSectionsIso_restrict W hV hV'V x

end Stacks.RelativeProj.Situation

end
