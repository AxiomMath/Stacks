module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.ProjectiveOverAmpleBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.LocallyProjective
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleProjOpenImmersion
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleAffineBase.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProj.FiniteTypeConditions
public import StacksFrontier.AlgebraicGeometry.RelativeProj.LocalAtBase
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local projectivity and properness of the relative homogeneous spectrum

Let `S` be a scheme carrying a quasi-coherent, commutative, nonnegatively graded `𝒪_S`-algebra
`𝒜`, and let `p : X = Proj_S(𝒜) ⟶ S` be its relative homogeneous spectrum. If `𝒜_0` is a finite
type `𝒪_S`-module and `𝒜` is of finite type over `𝒜_0` — equivalently, by
`Stacks.RelativeProj.Situation.properFiniteType_tfae`, over `𝒪_S` — then `p` is locally
projective, and in particular proper.

Over an affine open `U` of the base the chart structure morphism factors as
`Proj (𝒜(U)) ⟶ Spec (𝒜_0(U)) ⟶ U`. The first leg is proper because `𝒜(U)` is a finite type
algebra over its degree-zero part, the second because `Γ(S, U) → 𝒜_0(U)` is finite; so the chart
is proper, and its source is quasi-compact. A quasi-compact open subscheme of a `Proj` carries an
ample twist (Stacks 01Q2), ampleness over an affine base is relative ampleness (Stacks 01VK), and
the chart is locally of finite type, so the chart is quasi-projective. Over a base carrying an
ample invertible module — an affine one does — quasi-projective and proper is projective
(Stacks 0B45). The charts being the restrictions of `p` to an open cover of `S`, this is local
projectivity of `p`, and a locally projective morphism is proper (Stacks 01WC).

## Main results

* `Stacks.RelativeProj.Situation.isProjective_projInclusionToOpen` — the chart over an affine
  open of the base is projective.
* `Stacks.RelativeProj.Situation.isLocallyProjective_relativeProjToBase` — the local
  projectivity clause of Stacks 0800, with the degree-zero condition spelled affine-locally: the
  structure morphism of the relative homogeneous spectrum is locally projective.
* `Stacks.RelativeProj.Situation.isProper_relativeProjToBase_of_isDegreeZeroFiniteType` — the
  properness clause, in the same form.
* `Stacks.RelativeProj.Situation.isLocallyProjective_relativeProjToBase_of_isFiniteTypeOverBase`
  and
  `Stacks.RelativeProj.Situation.isProper_relativeProjToBase_of_isFiniteTypeOverBase` — the same
  two conclusions read off condition (2) of the source rather than condition (1), through the
  equivalence of the two.

Here the degree-zero condition is spelled affine-locally, through
`Stacks.RelativeProj.Situation.IsDegreeZeroFiniteType`. The tag itself is registered in
`StacksFrontier/AlgebraicGeometry/RelativeProj/DegreeZeroFiniteType.lean`, where the source's
conditions (1) and (2) are stated with the degree-zero condition as finite type of the sheaf
`𝒜_0`, the source's own reading of it, and where their equivalence is proved; the results here
are the chart-by-chart argument those registrations are deduced from.

## Implementation notes

The hypotheses are the source's and nothing else: no noetherian hypothesis on the base, no local
freeness, and no restriction of `𝒜` to a symmetric algebra. In particular this subsumes, for the
properness conclusion, the two existing registrations of this tag on projective bundles,
`Stacks.RelativeProj.isProper_projectiveBundleToBase_of_isFiniteType` and
`Stacks.RelativeProj.isProper_projectiveBundleToBase`, which are the case `𝒜 = Sym(ℰ)` and prove
only properness; those stay where they are, their `@[stacks 0800 …]` comments scoping each to its
special case.

Both hypotheses are read over every affine open of the base, which is the shape the sibling
predicates `Stacks.RelativeProj.Situation.IsFiniteTypeOverDegreeZero` of Stacks 07ZX and
`Stacks.RelativeProj.Situation.IsIntegralInDegreeZero` of Stacks 07ZZ already use, and the shape
the chart-by-chart argument consumes.

The source reduces to an affine base and then constructs a closed immersion into a projective
space by hand, remarking that the reader should do the same. The route taken here is the source's
own fallback argument — finite type, an ample twist, quasi-projectivity, and properness — but
assembled through Stacks 0B45 rather than through Morphisms 29.44.12 and 29.42.7: over the affine
chart base the eight conditions of Tag 0B45 are available unconditionally, since the structure
sheaf of an affine scheme is ample (`Stacks.Ample.isAmple_unitModule_of_isAffine`), and (3) ⟹ (1)
of that tag is exactly "quasi-projective and proper is projective". The source's universal
closedness input (Stacks 07ZZ) is subsumed: properness of the chart is got from properness of
`AlgebraicGeometry.Proj.toSpecZero` and finiteness of `Γ(S, U) → 𝒜_0(U)` directly, so the
integrality hypothesis of
`Stacks.RelativeProj.Situation.universallyClosed_relativeProjToBase_of_isIntegralInDegreeZero`
is not needed separately here.

`Stacks.RelativeProj.Situation.isProper_relativeProjToBase` of
`StacksFrontier/AlgebraicGeometry/ProjectiveBundle/SectionRings.lean` is *not* this statement: its
hypothesis is that every `Stacks.RelativeProj.Situation.sectionRingZeroMap` is an isomorphism,
the special case `𝒜_0 = 𝒪_S`. The names here are qualified to keep the two apart.

## References

* [Stacks Project, Tag 0800](https://stacks.math.columbia.edu/tag/0800)
* [Stacks Project, Tag 01Q2](https://stacks.math.columbia.edu/tag/01Q2)
* [Stacks Project, Tag 01VK](https://stacks.math.columbia.edu/tag/01VK)
* [Stacks Project, Tag 01WC](https://stacks.math.columbia.edu/tag/01WC)
* [Stacks Project, Tag 0B45](https://stacks.math.columbia.edu/tag/0B45)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.RelativeProj.Situation

variable (s : Situation.{u})

/-! ### The chart over an affine open of the base -/

/-- **The chart structure morphism is proper.** Over an affine open `U` of the base the chart
factors as `Proj (𝒜(U)) ⟶ Spec (𝒜_0(U)) ⟶ U`; the first leg is proper because `𝒜(U)` is a
finite type algebra over its degree-zero part, and the second is proper because it is `Spec` of
a finite ring map, hence a finite morphism. -/
theorem isProper_projInclusionToOpen (U : s.base.Opens) (hU : IsAffineOpen U)
    (hzero : (show Γ(s.base, U) →+* s.sectionRingGrading U 0 from
      (s.sectionRingZeroMap U).hom).Finite)
    (hdeg : Algebra.FiniteType (s.sectionRingGrading U 0) (s.sectionRing U)) :
    IsProper (projInclusionToOpen s U hU) := by
  have : IsFinite (Spec.map (sectionRingZeroMap s U)) := (IsFinite.SpecMap_iff _).mpr hzero
  have : Algebra.FiniteType (s.sectionRingGrading U 0) (s.sectionRing U) := hdeg
  change IsProper (Proj.toSpecZero (s.sectionRingGrading U) ≫
    Spec.map (sectionRingZeroMap s U) ≫ hU.isoSpec.inv)
  infer_instance

/-- **The chart structure morphism is quasi-projective.** It is locally of finite type and
quasi-compact for the same reason it is proper, and the ample invertible module it needs is a
twist of the structure sheaf of its source: the source is a quasi-compact `Proj`, so some
`𝒪(d)` with `d > 0` is ample on it by Stacks 01Q2, and over the affine base `U` ampleness is
relative ampleness by Stacks 01VK. -/
@[ega "II 4.6.18" "special case"]
theorem isQuasiProjective_projInclusionToOpen (U : s.base.Opens) (hU : IsAffineOpen U)
    (hzero : (show Γ(s.base, U) →+* s.sectionRingGrading U 0 from
      (s.sectionRingZeroMap U).hom).Finite)
    (hdeg : Algebra.FiniteType (s.sectionRingGrading U 0) (s.sectionRing U)) :
    IsQuasiProjective (projInclusionToOpen s U hU) := by
  have : IsAffine U.toScheme := hU
  have hproper : IsProper (projInclusionToOpen s U hU) :=
    isProper_projInclusionToOpen s U hU hzero hdeg
  have hloft : LocallyOfFiniteType (projInclusionToOpen s U hU) := inferInstance
  have hqc : QuasiCompact (projInclusionToOpen s U hU) := inferInstance
  have : CompactSpace (AlgebraicGeometry.Proj (s.sectionRingGrading U)) :=
    QuasiCompact.compactSpace_of_compactSpace (projInclusionToOpen s U hU)
  obtain ⟨d, -, hinv, hample⟩ :=
    Stacks.AlgebraicGeometry.ProjAmpleTwist.exists_isAmple_pullback_twistingSheaf
      (s.sectionRingGrading U) (𝟙 (AlgebraicGeometry.Proj (s.sectionRingGrading U)))
  refine ⟨⟨hloft, hqc⟩, _, hinv, ?_⟩
  have : Stacks.Ample.IsInvertibleModule (AlgebraicGeometry.Proj (s.sectionRingGrading U)) _ :=
    hinv
  exact (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple _ _).mpr hample

/-- **The chart structure morphism is projective.** Its base is affine, so the structure sheaf of
the base is ample and the eight conditions of Stacks 0B45 are equivalent there; the chart is
quasi-projective and proper, which is condition (3). -/
theorem isProjective_projInclusionToOpen (U : s.base.Opens) (hU : IsAffineOpen U)
    (hzero : (show Γ(s.base, U) →+* s.sectionRingGrading U 0 from
      (s.sectionRingZeroMap U).hom).Finite)
    (hdeg : Algebra.FiniteType (s.sectionRingGrading U 0) (s.sectionRing U)) :
    IsProjective (projInclusionToOpen s U hU) := by
  have : IsAffine U.toScheme := hU
  have htfae := (isProjective_tfae_seven_of_exists_isAmple (projInclusionToOpen s U hU)
    ⟨Stacks.Ample.unitModule U.toScheme, inferInstance,
      Stacks.Ample.isAmple_unitModule_of_isAffine _⟩).out 3 1
  exact htfae.mp ⟨isQuasiProjective_projInclusionToOpen s U hU hzero hdeg,
    isProper_projInclusionToOpen s U hU hzero hdeg⟩

/-! ### Stacks 0800 -/

/-- **The local projectivity clause of Stacks 0800, affine-locally.** If over every affine open
of the base the degree-zero part of the graded ring of sections is finite over the functions and
the graded ring of sections is of finite type over its degree-zero part, then the structure
morphism of the relative homogeneous spectrum is locally projective.

The affine opens of the base cover it, and over each one the structure morphism restricts to the
chart, which is projective. -/
theorem isLocallyProjective_relativeProjToBase (h₀ : s.IsDegreeZeroFiniteType)
    (hft : s.IsFiniteTypeOverDegreeZero) :
    IsLocallyProjective (relativeProjToBase s) := by
  refine ⟨s.base.affineOpens, fun U => (U : s.base.Opens), iSup_affineOpens_eq_top s.base,
    fun U => ?_⟩
  have key : IsProjective
      (((chartData s).chartIso U).hom ≫ (chartData s).toBase ∣_ (U : s.base.Opens)) := by
    rw [(chartData s).chartIso_hom_morphismRestrict U]
    exact isProjective_projInclusionToOpen s U.1 U.2 (h₀ U.1 U.2) (hft U.1 U.2)
  have hcancel := IsProjective.comp_iso ((chartData s).chartIso U).symm key
  rw [Iso.symm_hom, Iso.inv_hom_id_assoc] at hcancel
  exact hcancel

/-- **The properness clause of Stacks 0800, affine-locally.** Under the same hypotheses the
structure morphism of the relative homogeneous spectrum is proper, because a locally projective
morphism is proper (Stacks 01WC). -/
theorem isProper_relativeProjToBase_of_isDegreeZeroFiniteType (h₀ : s.IsDegreeZeroFiniteType)
    (hft : s.IsFiniteTypeOverDegreeZero) :
    IsProper (relativeProjToBase s) :=
  isProper_of_isLocallyProjective (isLocallyProjective_relativeProjToBase s h₀ hft)

/-- **The local projectivity clause of Stacks 0800 read off condition (2), affine-locally.** The
same conclusion when the graded ring of sections is instead of finite type over the functions,
which `Stacks.RelativeProj.Situation.properFiniteType_tfae` identifies with condition (1). -/
theorem isLocallyProjective_relativeProjToBase_of_isFiniteTypeOverBase
    (h₀ : s.IsDegreeZeroFiniteType) (hb : s.IsFiniteTypeOverBase) :
    IsLocallyProjective (relativeProjToBase s) := by
  have htfae := (properFiniteType_tfae s).out 2 1
  have h := htfae.mp ⟨h₀, hb⟩
  exact isLocallyProjective_relativeProjToBase s h.1 h.2

/-- **The properness clause of Stacks 0800 read off condition (2), affine-locally.** -/
theorem isProper_relativeProjToBase_of_isFiniteTypeOverBase (h₀ : s.IsDegreeZeroFiniteType)
    (hb : s.IsFiniteTypeOverBase) :
    IsProper (relativeProjToBase s) :=
  isProper_of_isLocallyProjective
    (isLocallyProjective_relativeProjToBase_of_isFiniteTypeOverBase s h₀ hb)

end Stacks.RelativeProj.Situation

end
