module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartAlphaInstance
public import StacksFrontier.AlgebraicGeometry.ProjF1DegreeOneChart.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.Ratio

/-!
# The absolute twist on a morphism landing in one standard open

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `r` a homogeneous element of degree `d`, and
`g : Y ⟶ Proj A` a morphism whose source lands wholly inside the standard open `D₊(r)`. **Then
`g⁎𝒪_X(d)` is free of rank one on the pullback of the degree-`d` section of `r`**, and the
freeness is pinned on that section: over every open of `Y` multiplication by the pulled-back
section is a bijection from the structure sheaf.

## Why this file exists

The normalisation clause of [Stacks, Tag 0B3V]'s bijection reduces to an absolute statement:
*the pullback of `twistingSheaf 𝒜 d` along
`Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.fromOfIsUnit` is free of rank one on the
pulled-back `degreeSection 𝒜 d r`, pinned on the sections.* That is
`isUnit_free_of_fromOfIsUnit` below, and `fromOfIsUnit` meets the hypothesis by
`Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.fromOfIsUnit_preimage_basicOpen`.

**No gluing is involved, and no reindexing of a coordinate family.** This step was
priced as a port of
`Stacks.TwistPullbackPinned.exists_iso_pullback_twistingSheafAtUniverse` from `coordGrading` to
an arbitrary graded ring, with the `Fin (r + 1)` coordinates reindexed by the degree-one elements
of `𝒜`. That pricing is for the *covering* statement, where the nonvanishing opens `X_{sᵢ}` of a
generating family cover `Y` and the per-chart trivialisations have to be glued across overlaps.
Here the hypothesis `g ⁻¹ᵁ D₊(r) = ⊤` says the source is a *single* chart, so there is one
trivialisation and nothing to glue: the statement follows from [Stacks, Tag 01MV] and
[Stacks, Tag 0H78] in the general form in which they are already formalized.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTwistPinnedChart.chartFactor`: the morphism read as a morphism
  into the open `U_d` of [Stacks, Equation 01N5], which is where the degree-`d` twist is
  invertible.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistPinnedChart.nvOpen_pullbackDegreeSection_eq_top`: **the
  pulled-back degree-`d` section of `r` vanishes nowhere on `Y`.** This is the geometric content:
  by [Stacks, Tag 01MV] the section of `𝒪_X(d)` attached to `r` is nonvanishing exactly on
  `D₊(r)`, and by [Stacks, Tag 0H78] the nonvanishing locus of a pulled-back section is the
  preimage of the nonvanishing locus, which the hypothesis makes all of `Y`.
* `Stacks.AlgebraicGeometry.ProjTwistPinnedChart.bijective_smul_pullbackDegreeSection`: **free of
  rank one, pinned on the section.** Over every open `W` of `Y`, multiplication by the
  pulled-back section is a bijection `Γ(Y, W) ≃ Γ(g⁎𝒪_X(d), W)`, so that section is a basis. A
  bare isomorphism `g⁎𝒪_X(d) ≅ 𝒪_Y` would not say this, and the bijection of
  [Stacks, Tag 0B3V] needs the pinning.
* `Stacks.AlgebraicGeometry.ProjTwistPinnedChart.isUnit_free_of_fromOfIsUnit`: the two statements
  above at `g = fromOfIsUnit 𝒜 φ hd hr hu`, which is the form
  the normalisation clause of [Stacks, Tag 0B3V] asks for.
* `Stacks.AlgebraicGeometry.ProjTwistPinnedChart.pinnedFrameHom`,
  `…ProjTwistPinnedChart.isIso_pinnedFrameHom` and
  `…ProjTwistPinnedChart.pinnedFrameIso`: **the same freeness as a named isomorphism
  `𝒪_Y ≅ g⁎𝒪_X(d)`, still pinned.** The morphism is the one the pulled-back section determines
  out of the structure sheaf, so `pinnedFrameHom_app` says it *is* multiplication by that
  section; `AlgebraicGeometry.Scheme.Modules.Hom.isIso_iff_isIso_app` then turns the open-by-open
  bijection into invertibility with no cover and no gluing.
* `Stacks.AlgebraicGeometry.ProjTwistPinnedChart.pinnedFrameIso_inv_smul_resT`: that isomorphism
  **inverted** on a multiple of the frame. This is the direction a consumer holding a pinning
  identity reads it in: it turns "the pulled-back section of `m` is `c` times the frame" into
  "the frame isomorphism carries the pulled-back section of `m` to the scalar `c`", which is an
  identity of *morphisms* read on sections and can therefore be composed with another one.

## Implementation notes

**The degree-`d` twist is invertible on `U_d`, not on `Proj A`.** So the statements are phrased
through `Stacks.AlgebraicGeometry.MorphismsIntoProj.pullbackTwist`, the pullback along a morphism
*into `U_d`*, and `chartFactor` supplies that factorisation from the hypothesis — `D₊(r)` lies in
`U_d` because `r` has degree `d`. The invertibility instance is then
`Stacks.AlgebraicGeometry.ProjChartAlphaInstance.isInvertibleModule_pullbackTwist`, and no
hypothesis that `𝒜` is generated in degree one is needed anywhere below. `toProj_chartFactor`
says the factorisation composes back to `g`, so a consumer holding `g` can rewrite.

**Nothing here is new mathematics and nothing is restated.** Every input is used in the general
form in which it is already formalized:
`Stacks.AlgebraicGeometry.ProjChartAlphaInstance.le_nonvanishingOpen_pullbackDegreeSection` is
[Stacks, Tag 01MV] and [Stacks, Tag 0H78] combined for a morphism into `U_d`, and
`Stacks.NonvanishingSpelling.bijective_smul` is the trivialisation clause of [Stacks, Tag 01CY].
In particular no part of `StacksFrontier/AlgebraicGeometry/TwistPullbackRatio/Comparison.lean` is
reproved at a general grading: that file's coordinate-specific half is about the covering
statement, and its general half (`div_add`, `bijective_div` and the rest of its `Div` section) is
not needed here.

**What a consumer still has to supply, and what it does not.** The primary conclusion is freeness
pinned on the section, stated as a bijection over each open rather than as a named isomorphism
`g⁎𝒪_X(d) ≅ 𝒪_Y`. That is deliberate: it is the form the division machinery of
`StacksFrontier/AlgebraicGeometry/ProjectiveFromSections/Ratio.lean` runs on
(`Stacks.ProjectiveFromSections.div` is defined from exactly this bijection), and it carries the
pinning without a transport. The named isomorphism is `pinnedFrameIso` below, got from
`AlgebraicGeometry.Scheme.Modules.Hom.isIso_iff_isIso_app` together with that bijection, with no
cover and no gluing; it is stated second because it is the derived form, and it keeps the pinning
through `pinnedFrameHom_app`.

**No `@[stacks ...]` attribute is attached.** [Stacks, Tag 01MV] already carries its attribute at
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.nonvanishingLocus_degreeSection_inter` and
[Stacks, Tag 0H78] at `Stacks.NonvanishingPullback.preimage_nonvanishingLocus`; nothing below
restates either, and [Stacks, Tag 0B3V] is not reached here.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01MV](https://stacks.math.columbia.edu/tag/01MV)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
* [Stacks Project, Equation 01N5](https://stacks.math.columbia.edu/tag/01N5)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Proj (degreeOpen)
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.MorphismsIntoProj
open Stacks.AlgebraicGeometry.ProjChartAlphaInstance
open Stacks.ProjectiveFromSections (nvOpen resT)

universe u w

namespace Stacks.AlgebraicGeometry.ProjTwistPinnedChart

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {Y : Scheme.{u}} {d : ℕ}

/-! ### Reading the morphism as a morphism into `U_d` -/

/-- **A morphism landing in `D₊(r)` lands in `U_d`**, for `r` homogeneous of degree `d`: the
standard open of a degree-`d` element is one of the opens whose union is `U_d`. -/
theorem preimage_degreeOpen_eq_top {r : A} (hr : r ∈ 𝒜 d) (g : Y ⟶ AlgebraicGeometry.Proj 𝒜)
    (hg : g ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 r = ⊤) :
    g ⁻¹ᵁ degreeOpen 𝒜 d = ⊤ :=
  top_le_iff.mp (hg.ge.trans ((Opens.map g.base).map
    (homOfLE (AlgebraicGeometry.Proj.basicOpen_le_degreeOpen 𝒜 hr))).le)

/-- **The morphism read as a morphism into `U_d`.** The degree-`d` twist is invertible on `U_d`
and not on all of `Proj A`, so this is the shape every statement below is phrased in. -/
def chartFactor {r : A} (hr : r ∈ 𝒜 d) (g : Y ⟶ AlgebraicGeometry.Proj 𝒜)
    (hg : g ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 r = ⊤) :
    Y ⟶ (degreeOpen 𝒜 d).toScheme :=
  ProjF1DegreeOneChart.opensHomEquiv (degreeOpen 𝒜 d)
    ⟨g, preimage_degreeOpen_eq_top 𝒜 hr g hg⟩

/-- The factorisation composes back to the original morphism. -/
@[simp] theorem toProj_chartFactor {r : A} (hr : r ∈ 𝒜 d) (g : Y ⟶ AlgebraicGeometry.Proj 𝒜)
    (hg : g ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 r = ⊤) :
    toProj 𝒜 (chartFactor 𝒜 hr g hg) = g :=
  congrArg Subtype.val
    ((ProjF1DegreeOneChart.opensHomEquiv (X := Y) (degreeOpen 𝒜 d)).symm_apply_apply
      ⟨g, preimage_degreeOpen_eq_top 𝒜 hr g hg⟩)

/-! ### Freeness of rank one, pinned on the pulled-back section -/

/-- **The pulled-back degree-`d` section of `r` vanishes nowhere on `Y`.**

This is the geometric content of the file. By [Stacks, Tag 01MV] the global section of `𝒪_X(d)`
attached to `r` is nonvanishing exactly on `D₊(r)`, and by [Stacks, Tag 0H78] the nonvanishing
locus of a pulled-back section is the preimage of the nonvanishing locus; the hypothesis says
that preimage is all of `Y`. -/
theorem nvOpen_pullbackDegreeSection_eq_top (r : 𝒜 d) (g : Y ⟶ AlgebraicGeometry.Proj 𝒜)
    (hg : g ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (r : A) = ⊤) :
    nvOpen (pullbackTwist 𝒜 (chartFactor 𝒜 r.2 g hg) (d : ℤ))
        (pullbackDegreeSection 𝒜 (chartFactor 𝒜 r.2 g hg) r) = ⊤ :=
  top_le_iff.mp (le_nonvanishingOpen_pullbackDegreeSection 𝒜 (chartFactor 𝒜 r.2 g hg) r
    (by rw [toProj_chartFactor]; exact hg.ge))

/-- **`g⁎𝒪_X(d)` is free of rank one on the pulled-back degree-`d` section of `r`, pinned on that
section.** Over every open `W` of `Y`, multiplication by the pulled-back section is a bijection
from `Γ(Y, W)`: the section is a basis of the pullback there.

This is the trivialisation clause of [Stacks, Tag 01CY] at
`nvOpen_pullbackDegreeSection_eq_top`. The pinning is the point — a bare isomorphism
`g⁎𝒪_X(d) ≅ 𝒪_Y` says nothing about which section is the basis, and the bijection of
[Stacks, Tag 0B3V] is normalised by that section. -/
theorem bijective_smul_pullbackDegreeSection (r : 𝒜 d) (g : Y ⟶ AlgebraicGeometry.Proj 𝒜)
    (hg : g ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (r : A) = ⊤) (W : Y.Opens) :
    Function.Bijective fun a : Γ(Y, W) =>
      a • resT W (pullbackDegreeSection 𝒜 (chartFactor 𝒜 r.2 g hg) r) :=
  Stacks.NonvanishingSpelling.bijective_smul Y
    (pullbackTwist 𝒜 (chartFactor 𝒜 r.2 g hg) (d : ℤ))
    (pullbackDegreeSection 𝒜 (chartFactor 𝒜 r.2 g hg) r)
    (le_top.trans_eq (nvOpen_pullbackDegreeSection_eq_top 𝒜 r g hg).symm)

/-! ### The freeness as a named isomorphism, still pinned -/

/-- **The frame, as a morphism out of the structure sheaf.** The morphism `𝒪_Y ⟶ g⁎𝒪_X(d)`
determined by the pulled-back degree-`d` section of `r`, in the spelling
`Stacks.NonvanishingSpelling.unitHom_app` computes on: `AlgebraicGeometry.SheafOfModules`'s
`unitHomEquiv` identifies the morphisms out of the unit object with the global sections, and this
is the morphism named by `pullbackDegreeSection 𝒜 (chartFactor 𝒜 r.2 g hg) r`. -/
def pinnedFrameHom (r : 𝒜 d) (g : Y ⟶ AlgebraicGeometry.Proj 𝒜)
    (hg : g ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (r : A) = ⊤) :
    SheafOfModules.unit Y.ringCatSheaf ⟶ pullbackTwist 𝒜 (chartFactor 𝒜 r.2 g hg) (d : ℤ) :=
  (Stacks.NonvanishingSpelling.toSheafOfModules Y
      (pullbackTwist 𝒜 (chartFactor 𝒜 r.2 g hg) (d : ℤ))).unitHomEquiv.symm
    ((Stacks.NonvanishingSpelling.sectionsEquiv Y
        (pullbackTwist 𝒜 (chartFactor 𝒜 r.2 g hg) (d : ℤ))).symm
      (pullbackDegreeSection 𝒜 (chartFactor 𝒜 r.2 g hg) r))

/-- **The frame morphism is multiplication by the pulled-back degree-`d` section**, over every
open of `Y`. This is `Stacks.NonvanishingSpelling.unitHom_app`, and it is what carries the
pinning into the isomorphism below: the isomorphism is not merely *some* trivialisation, it is
the one sending `1` to the frame. -/
theorem pinnedFrameHom_app (r : 𝒜 d) (g : Y ⟶ AlgebraicGeometry.Proj 𝒜)
    (hg : g ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (r : A) = ⊤) (W : Y.Opens) (a : Γ(Y, W)) :
    Scheme.Modules.Hom.app (pinnedFrameHom 𝒜 r g hg) W a
      = a • resT W (pullbackDegreeSection 𝒜 (chartFactor 𝒜 r.2 g hg) r) :=
  Stacks.NonvanishingSpelling.unitHom_app Y
    (pullbackTwist 𝒜 (chartFactor 𝒜 r.2 g hg) (d : ℤ))
    (pullbackDegreeSection 𝒜 (chartFactor 𝒜 r.2 g hg) r) W a

/-- **The frame morphism is an isomorphism.** `pinnedFrameHom_app` identifies its component over
an open `W` with multiplication by the frame, which
`bijective_smul_pullbackDegreeSection` says is bijective; a morphism of `𝒪_Y`-modules that is
bijective over every open is invertible
(`AlgebraicGeometry.Scheme.Modules.Hom.isIso_iff_isIso_app`). No cover and no gluing: the
hypothesis `hg` already says the source is a single chart. -/
theorem isIso_pinnedFrameHom (r : 𝒜 d) (g : Y ⟶ AlgebraicGeometry.Proj 𝒜)
    (hg : g ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (r : A) = ⊤) :
    IsIso (pinnedFrameHom 𝒜 r g hg) := by
  refine Scheme.Modules.Hom.isIso_iff_isIso_app.mpr fun W =>
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mpr ?_
  have h := bijective_smul_pullbackDegreeSection 𝒜 r g hg W
  refine ⟨fun x y hxy => h.1 ?_, fun z => ?_⟩
  · exact ((pinnedFrameHom_app 𝒜 r g hg W x).symm.trans hxy).trans
      (pinnedFrameHom_app 𝒜 r g hg W y)
  · obtain ⟨a, ha⟩ := h.2 z
    exact ⟨a, (pinnedFrameHom_app 𝒜 r g hg W a).trans ha⟩

/-- **`g⁎𝒪_X(d)` is free of rank one, as a named isomorphism `𝒪_Y ≅ g⁎𝒪_X(d)` pinned on the
pulled-back degree-`d` section of `r`.** Its `hom` is `pinnedFrameHom`, so `pinnedFrameHom_app`
reads it on sections and the pinning is not lost.

This is the trivialisation clause of [Stacks, Tag 01CY] in the shape a consumer that has to
*compare two morphisms of modules* needs — a bijection over each open cannot be composed with a
morphism, an isomorphism can. -/
def pinnedFrameIso (r : 𝒜 d) (g : Y ⟶ AlgebraicGeometry.Proj 𝒜)
    (hg : g ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (r : A) = ⊤) :
    (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ≅
      pullbackTwist 𝒜 (chartFactor 𝒜 r.2 g hg) (d : ℤ) :=
  @asIso _ _ _ _ (pinnedFrameHom 𝒜 r g hg) (isIso_pinnedFrameHom 𝒜 r g hg)

/-- The forward morphism of `pinnedFrameIso` is `pinnedFrameHom`. -/
@[simp] theorem pinnedFrameIso_hom (r : 𝒜 d) (g : Y ⟶ AlgebraicGeometry.Proj 𝒜)
    (hg : g ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (r : A) = ⊤) :
    (pinnedFrameIso 𝒜 r g hg).hom = pinnedFrameHom 𝒜 r g hg := rfl

/-- **The frame isomorphism inverted, read on a multiple of the frame.** Over an open `W` of `Y`
the inverse of `pinnedFrameIso` sends `a · (m r)|_W` back to `a`.

This is the form in which the pinning is *consumed*: a statement of the shape "the pulled-back
degree-`d` section of `m` is `c · (m r)|_W`" — of which
`Stacks.RelativeProj.resT_pullbackDegreeSection_localChartMap` is an instance — becomes, through
this, "the frame isomorphism carries the pulled-back section of `m` to the scalar `c`", which is
an identity of *morphisms* read on sections and can therefore be fed to a comparison of two
quotient maps. `pinnedFrameHom_app` is the same fact in the other direction; the two together are
what makes the isomorphism pinned rather than merely existent. -/
theorem pinnedFrameIso_inv_smul_resT (r : 𝒜 d) (g : Y ⟶ AlgebraicGeometry.Proj 𝒜)
    (hg : g ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (r : A) = ⊤) (W : Y.Opens) (a : Γ(Y, W)) :
    (pinnedFrameIso 𝒜 r g hg).inv.val.app (op W)
        (a • resT W (pullbackDegreeSection 𝒜 (chartFactor 𝒜 r.2 g hg) r)) = a :=
  (congrArg
      (fun z : Γ(pullbackTwist 𝒜 (chartFactor 𝒜 r.2 g hg) (d : ℤ), W) =>
        (pinnedFrameIso 𝒜 r g hg).inv.val.app (op W) z)
      (pinnedFrameHom_app 𝒜 r g hg W a)).symm.trans
    (congrArg
      (fun φ : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶
          SheafOfModules.unit Y.ringCatSheaf => φ.val.app (op W) a)
      (pinnedFrameIso 𝒜 r g hg).hom_inv_id)

/-! ### The form `ChartTwistTransport` asks for -/

/-- **The absolute step of [Stacks, Tag 0B3V]'s normalisation.** For a ring map `φ` out of a
graded ring sending a positive-degree homogeneous `r` to a unit, the pullback of `𝒪_X(d)` along
`Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.fromOfIsUnit` is free of rank one on the pullback
of the degree-`d` section of `r`, pinned on that section.

This is the absolute statement the normalisation clause of [Stacks, Tag 0B3V] reduces to;
the hypothesis it runs on is
`Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.fromOfIsUnit_preimage_basicOpen`, which says the
source lands wholly inside `D₊(r)`. -/
theorem isUnit_free_of_fromOfIsUnit (φ : A →+* Γ(Y, ⊤)) (hd : 0 < d) (r : 𝒜 d)
    (hu : IsUnit (φ (r : A))) (W : Y.Opens) :
    Function.Bijective fun a : Γ(Y, W) =>
      a • resT W (pullbackDegreeSection 𝒜
        (chartFactor 𝒜 r.2 (ProjF1DegreeOneChart.fromOfIsUnit 𝒜 φ hd r.2 hu)
          (ProjF1DegreeOneChart.fromOfIsUnit_preimage_basicOpen 𝒜 φ hd r.2 hu)) r) :=
  bijective_smul_pullbackDegreeSection 𝒜 r _ _ W

end Stacks.AlgebraicGeometry.ProjTwistPinnedChart

end
