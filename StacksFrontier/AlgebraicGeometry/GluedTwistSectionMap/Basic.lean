module

public import StacksFrontier.AlgebraicGeometry.ChartTransNonNested.DegreeSection
public import StacksFrontier.AlgebraicGeometry.GluedTwistChartData.Basic
public import StacksFrontier.AlgebraicGeometry.ProjShared.RelevantCover
public import StacksFrontier.AlgebraicGeometry.RelativeProjFlat.Twists

/-!
# The chart description of Tag 01NR's homogeneous-section map, for the glued twists

`Stacks.AlgebraicGeometry.GluedTwistChartData.mk` reduces
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData` — the structure Stacks Tag 01NR asserts
the existence of — to four fields: a graded algebra `B` on the relative projective spectrum whose
homogeneous pieces are identified with the glued twists
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.gluedTwist`, the condition that those
identifications respect the product and the unit, the homogeneous-section map `ψ`, and `ψ`'s chart
description.

**This file discharges the fourth of those four, relative to the third**, and does so for the
glued twist directly, so that it is independent of the algebra structure: once a degreewise map
from the base algebra into the direct image of the *glued twists* satisfies the chart description
below, the `ψ_chart` field of a twist datum holds for the map obtained by transporting it along
any identification `e` of `B`'s pieces with the glued twists.

## Main definitions

* `Stacks.AlgebraicGeometry.GluedTwistSectionMap.gluedMapSection`: the chart comparison of the
  glued twist read on sections — the glued-twist analogue of
  `Stacks.AlgebraicGeometry.RelativeProjTwists.ChartData.mapSection`, with
  `Stacks.Tag01VMVeryAmple.gluedChartIso` in place of a chart datum's `chartIso` and
  `gluedTwist` in place of `B.piece`.
* `Stacks.AlgebraicGeometry.GluedTwistSectionMap.PsiGluedChart`: **the chart description of the
  homogeneous-section map, for the glued twist.** Over an affine open `U` of the base the chart
  comparison carries the degree-`n` homogeneous section of Tag 01MP attached to a local section
  `a` of the base algebra to the candidate map's value at `a`, transported along the equality of
  the chart's image with the inverse image of `U`.

## Main results

* `Stacks.AlgebraicGeometry.GluedTwistSectionMap.chartData_mapSection`: the chart comparison of
  `Stacks.AlgebraicGeometry.GluedTwistChartData.chartData` on sections is the glued twist's own
  chart comparison followed by `(e n).inv`.
* `Stacks.AlgebraicGeometry.GluedTwistSectionMap.psiChart_of_psiGluedChart`: **the transport.**
  For any graded algebra `B` on the relative Proj and any identification `e` of its pieces with
  the glued twists, a map satisfying `PsiGluedChart` yields, after composition with the direct
  image of `(e n).inv`, a map satisfying
  `Stacks.AlgebraicGeometry.Tag01NRPsiCompat.PsiChart` for
  `Stacks.AlgebraicGeometry.GluedTwistChartData.chartData`.
* `Stacks.AlgebraicGeometry.GluedTwistSectionMap.mk`: **Tag 01NR's twist datum from three
  fields** — the graded algebra with its identification of pieces, the condition on its product
  and unit, and a homogeneous-section map for the glued twists satisfying `PsiGluedChart`. The
  `ψ_chart` field is no longer among them.
* `Stacks.AlgebraicGeometry.GluedTwistSectionMap.chart_appTop`: **the chart's ring map on the
  global sections of a projective spectrum.** Over an affine open `U` of the base, the morphism
  `Proj (A.grading U) ⟶ S` through the chart carries a function `r` on `U` to the global section
  of `𝒪` that Tag 01M7 attaches to the degree-zero element `A.strHom U r`.
* `Stacks.AlgebraicGeometry.GluedTwistSectionMap.degreeSection_smul`: **the degree-`n`
  homogeneous section map of Tag 01MP is linear for the scalars of the base.**
* `Stacks.AlgebraicGeometry.GluedTwistSectionMap.gluedDegreeSection` and `psiGluedAffine`: **the
  homogeneous-section map of the glued twist over one affine open of the base**, the second as a
  `Γ(S, U)`-linear map, with `gluedMapSection_degreeSection` its chart description in the shape
  `PsiGluedChart` asks for.

## Implementation notes

`Stacks.AlgebraicGeometry.GluedTwistChartData.chartData` assembles its chart identification as
`(restrictFunctor (chart U hU)).mapIso (e n) ≪≫ gluedChartIso A n (hcoc n) U hU`, and
`AlgebraicGeometry.Scheme.Modules.restrictAppIso` is `CategoryTheory.Iso.refl` while
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` is a presheaf pushforward along the opens
functor; so the chart comparison of that datum is the glued twist's own comparison followed by
`(e n).inv` *at the image open*, on the nose. `chartData_mapSection` is that `rfl`, taken once
and at variable degree, and every later step is an application of a lemma with the opens as
variables.

The transport along the equality `chart ''ᵁ ⊤ = toBase ⁻¹ᵁ U` of opens is handled exactly as
`Stacks.AlgebraicGeometry.Tag01NRPsiCompat` handles it: `app_eqRec_symm` has the two opens as
*variables* and is proved by substituting the equality away. It is stated here rather than reused
from `PsiCompat/Basic.lean` because the lemmas there are all about the pieces of a fixed graded
algebra, whereas the morphism moved across the transport here has the glued twist as its source
and a piece of `B` as its target.

## What is not done here

**No term of `PsiGluedChart` is constructed, and consequently no
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData` is built.** `mk` and
`psiChart_of_psiGluedChart` take the homogeneous-section map for the glued twists as a hypothesis.

Constructing one has *two* independent halves. The first is done here; the second is not.

* **Scalar linearity — done.** A term of the type
  `A.piece (n : ℤ) ⟶ (Scheme.Modules.pushforward (relativeProj A).toBase).obj _` is a morphism of
  *sheaves of modules*, so its component over an affine open `U` must be `Γ(S, U)`-linear; by
  `AlgebraicGeometry.Scheme.Modules.pushforward_obj_smul` the scalar action on the target is the
  one obtained along `(relativeProj A).toBase.app U`. This is an obligation that the restriction
  lemmas of `ChartTransNonNested/DegreeSection.lean` say nothing about, and the library had no
  statement of the ring map it needs: `Stacks.AlgebraicGeometry.RelativeProjFlat.chart_appLE`
  gives it on a *positive-degree standard open* `D₊(f)` only. `chart_appTop` lifts that to `⊤`
  and `psiGluedAffine` is the resulting linear map.

* **Restriction compatibility — not done.** For affine opens `W ≤ U` of the base,
  `gluedDegreeSection A hcoc n W hW (A.resPiece h n a)` must be the restriction of
  `gluedDegreeSection A hcoc n U hU a` along the inclusion of inverse images. Only with that does
  `Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis` — the affine opens of a scheme being
  a basis, and `IsCompatibleOnBasis` asking precisely for this — assemble the components into the
  sheaf-level morphism, and only then does `gluedMapSection_degreeSection` become a term of
  `PsiGluedChart`.

  On the *comparison of the two charts' pushforwards* the corresponding identity is
  `Stacks.AlgebraicGeometry.ChartTransRelativeProj.pushNested_degreeSection` and
  `cmpNested_resTop_degreeSection`. What is missing is the bridge from those to the glued twist.
  The shortest route through the existing API, not carried out here:
  `Stacks.AlgebraicGeometry.GluedTwistAlgebra.trans_chartSections` and `chartSections_resLE`
  relate two charts' section equivalences through
  `Stacks.AlgebraicGeometry.ChartTransNonNested.ModelData.trans`, and `trans_app_cmpGen` writes
  that transition in terms of
  `Stacks.AlgebraicGeometry.ChartTransRelativeProj.cmpGen`; `cmpGen_agreeOn_meetLoc` and
  `isComposite_meetLoc` then reduce `cmpGen` to `cmpNested`. Two auxiliary lemmas do not exist and
  would have to be written: a computation of
  `Stacks.Tag01VMVeryAmple.gluedChartIso` on sections against
  `GluedTwistAlgebra.chartSections` (`ModelData.chartIso` has no `_hom_app`/`_inv_app` lemma at
  all), and `cmpGen` over an open and itself being the identity.

Nothing here constructs the graded algebra `B`, its multiplication, its unit, or
`Stacks.AlgebraicGeometry.RelativeProjTwists.IsGradedChartIso`.

No `stacks` attribute is attached. Tag 01NR's existence assertion is earned only by a term of
`TwistData`; a reduction of one of its four remaining fields to another is not a covering set
for it.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ChartTransRelativeProj
open Stacks.AlgebraicGeometry.ProjInclusionDegreeSection
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

namespace Stacks.AlgebraicGeometry.GluedTwistSectionMap

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S}

/-! ### The chart comparison of the glued twist, on sections -/

/-- **The chart comparison of the glued twist, read on sections.** Over an affine open `U` of the
base and an open `V` of the chart, the inverse of `Stacks.Tag01VMVeryAmple.gluedChartIso` carries
a section of the absolute twist over `V` to a section of the glued twist over the image of `V`.

This is `Stacks.AlgebraicGeometry.RelativeProjTwists.ChartData.mapSection` with `gluedTwist` in
place of the piece of a graded algebra and `gluedChartIso` in place of a chart datum's
`chartIso`. -/
public def gluedMapSection (n : ℤ) (hcoc : IsNestedCocycle A n) (U : S.Opens)
    (hU : IsAffineOpen U) (V : (AlgebraicGeometry.Proj (A.grading U)).Opens)
    (a : (twistingSheaf (A.grading U) n).val.obj (op V)) :
    (gluedTwist A n hcoc).val.obj (op ((relativeProj A).chart U hU ''ᵁ V)) :=
  (Scheme.Modules.restrictAppIso ((relativeProj A).chart U hU) (gluedTwist A n hcoc) V).hom
    ((Tag01VMVeryAmple.gluedChartIso A n hcoc U hU).inv.val.app (op V) a)

/-! ### The chart description of the homogeneous-section map -/

/-- **The chart description of the homogeneous-section map, for the glued twist.** Over an affine
open `U` of the base the chart comparison of the glued twist carries the degree-`n` homogeneous
section of Tag 01MP attached to a local section `a` of the base algebra to `ψ(a)`, transported
along the equality of the chart's image with the inverse image of `U`.

This is `Stacks.AlgebraicGeometry.Tag01NRPsiCompat.PsiChart` with `gluedTwist` in place of the
piece of a graded algebra and `Stacks.Tag01VMVeryAmple.gluedChartIso` in place of a chart datum's
`chartIso`; it is a condition on the glued twist alone, so it mentions neither a graded algebra
nor its chart data. -/
public def PsiGluedChart (hcoc : ∀ n : ℤ, IsNestedCocycle A n)
    (psi : ∀ n : ℕ, A.piece (n : ℤ) ⟶
      (Scheme.Modules.pushforward (relativeProj A).toBase).obj
        (gluedTwist A (n : ℤ) (hcoc (n : ℤ)))) : Prop :=
  ∀ (U : S.Opens) (hU : IsAffineOpen U) (n : ℕ) (a : A.sectionPieces U n),
    gluedMapSection (n : ℤ) (hcoc (n : ℤ)) U hU ⊤
        (degreeSection (A.grading U) n
          ⟨DirectSum.of (A.sectionPieces U) n a, A.of_mem_grading U a⟩) =
      (RelativeProjTwistGlue.chart_image_top (relativeProj A) U hU).symm ▸
        ((psi n).val.app (op U) a)

/-! ### The transport along an identification of the pieces with the glued twists -/

/-- **A morphism of sheaves of modules commutes with the transport along an equality of opens.**
The two opens are variables, so this is proved by substituting the equality away. -/
public theorem app_eqRec_symm {M N : (relativeProj A).scheme.Modules} (φ : M ⟶ N)
    {W₁ W₂ : (relativeProj A).scheme.Opens} (h : W₁ = W₂) (y : M.val.obj (op W₂)) :
    φ.val.app (op W₁) (h.symm ▸ y : M.val.obj (op W₁)) =
      (h.symm ▸ φ.val.app (op W₂) y : N.val.obj (op W₁)) := by
  cases h
  rfl

/-- **The chart comparison of `Stacks.AlgebraicGeometry.GluedTwistChartData.chartData` on
sections** is the glued twist's own chart comparison followed by `(e n).inv` at the image open.

`AlgebraicGeometry.Scheme.Modules.restrictAppIso` is the identity isomorphism and
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` is a presheaf pushforward along the opens
functor, so the two sides are the same term; this is the one delta step taken here, and it is
taken at variable degree and variable open. -/
public theorem chartData_mapSection (hcoc : ∀ n : ℤ, IsNestedCocycle A n)
    (B : SchemeGradedAlgebra (relativeProj A).scheme)
    (e : ∀ n : ℤ, B.piece n ≅ gluedTwist A n (hcoc n)) (U : S.Opens) (hU : IsAffineOpen U)
    (n : ℤ) (V : (AlgebraicGeometry.Proj (A.grading U)).Opens)
    (a : (twistingSheaf (A.grading U) n).val.obj (op V)) :
    (GluedTwistChartData.chartData hcoc B e).mapSection U hU n V a =
      (e n).inv.val.app (op ((relativeProj A).chart U hU ''ᵁ V))
        (gluedMapSection n (hcoc n) U hU V a) :=
  rfl

/-- **The transport of the chart description along an identification of the pieces with the
glued twists.** For a graded algebra `B` on the relative projective spectrum together with an
identification `e` of its homogeneous pieces with the glued twists, a homogeneous-section map for
the glued twists satisfying `PsiGluedChart` yields one for `B`, by composing with the direct image
of `(e n).inv`, satisfying `Stacks.AlgebraicGeometry.Tag01NRPsiCompat.PsiChart` for
`Stacks.AlgebraicGeometry.GluedTwistChartData.chartData`.

Three steps: `chartData_mapSection` reads the chart comparison of the chart datum as the glued
twist's own comparison followed by `(e n).inv`, `PsiGluedChart` computes the latter, and
`app_eqRec_symm` moves `(e n).inv` across the transport. -/
public theorem psiChart_of_psiGluedChart (hcoc : ∀ n : ℤ, IsNestedCocycle A n)
    (B : SchemeGradedAlgebra (relativeProj A).scheme)
    (e : ∀ n : ℤ, B.piece n ≅ gluedTwist A n (hcoc n))
    {psi : ∀ n : ℕ, A.piece (n : ℤ) ⟶
      (Scheme.Modules.pushforward (relativeProj A).toBase).obj
        (gluedTwist A (n : ℤ) (hcoc (n : ℤ)))}
    (hpsi : PsiGluedChart hcoc psi) :
    Tag01NRPsiCompat.PsiChart (GluedTwistChartData.chartData hcoc B e)
      fun n => psi n ≫
        (Scheme.Modules.pushforward (relativeProj A).toBase).map (e (n : ℤ)).inv := by
  intro U hU n a
  refine Eq.trans (chartData_mapSection hcoc B e U hU (n : ℤ) ⊤ _) ?_
  refine Eq.trans (congrArg ((e (n : ℤ)).inv.val.app
    (op ((relativeProj A).chart U hU ''ᵁ (⊤ : (AlgebraicGeometry.Proj (A.grading U)).Opens))))
    (hpsi U hU n a)) ?_
  exact app_eqRec_symm (e (n : ℤ)).inv
    (RelativeProjTwistGlue.chart_image_top (relativeProj A) U hU) _

/-! ### The scalar action: the chart's ring map on global sections, and linearity

These are the ingredients of the *other* half of a construction of the section map — the half the
restriction lemmas of `ChartTransNonNested/DegreeSection.lean` say nothing about. A term of the
section map's type is a morphism of sheaves of modules, so its component over an affine open `U`
of the base is `Γ(S, U)`-linear; the scalar action on the target is the one obtained along
`(relativeProj A).toBase.app U` (`AlgebraicGeometry.Scheme.Modules.pushforward_obj_smul`), and
reading it through the chart means knowing the ring map `Γ(S, U) ⟶ Γ(Proj (A.grading U), 𝒪)`.
-/

section Scalars

variable (A)

/-- **The chart's ring map on the global sections of the projective spectrum, restricted to a
standard open of positive degree.** Over such an open both the structure morphism of the chart and
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroRingToGlobalSections` are the
degree-zero localization map `a ↦ a / 1`, so the two composites agree.

This is `Stacks.AlgebraicGeometry.RelativeProjFlat.chart_appLE` against
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroRingToGlobalSections_basicOpen`,
joined by `AlgebraicGeometry.Scheme.Hom.appLE_map`. Every step is taken in term mode: the two
spellings of the opens of a projective spectrum are definitionally but not syntactically equal, so
`rw` fails its motive check on the composite. -/
public theorem chart_appTop_basicOpen (U : S.Opens) (hU : IsAffineOpen U)
    (h : (⊤ : (AlgebraicGeometry.Proj (A.grading U)).Opens) ≤
      ((relativeProj A).chart U hU ≫ (relativeProj A).toBase) ⁻¹ᵁ U) (r : Γ(S, U))
    (d : ℕ) (f : A.sectionRing U) (hf : f ∈ A.grading U d) (hd : 0 < d) :
    ((ProjectiveSpectrum.Proj.structureSheaf (A.grading U)).1.map
        (homOfLE (le_top : Proj.basicOpen (A.grading U) f ≤ ⊤)).op).hom
      ((((relativeProj A).chart U hU ≫ (relativeProj A).toBase).appLE U ⊤ h).hom r) =
    ((ProjectiveSpectrum.Proj.structureSheaf (A.grading U)).1.map
        (homOfLE (le_top : Proj.basicOpen (A.grading U) f ≤ ⊤)).op).hom
      (degreeZeroRingToGlobalSections (A.grading U) ⟨A.strHom U r, A.strHom_mem U r⟩) := by
  let _ := A.sectionRingAlgebra U
  refine Eq.trans ?_ (degreeZeroRingToGlobalSections_basicOpen (A.grading U) f
      ⟨A.strHom U r, A.strHom_mem U r⟩).symm
  refine Eq.trans (congrArg (fun φ : Γ(S, U) ⟶
      Γ(AlgebraicGeometry.Proj (A.grading U), Proj.basicOpen (A.grading U) f) => φ.hom r)
      ((Scheme.Hom.appLE_map _ h
        (homOfLE (le_top : Proj.basicOpen (A.grading U) f ≤ ⊤)).op).trans
        (RelativeProjFlat.chart_appLE A U hU hf hd (le_top.trans h)))) ?_
  rfl

/-- **The chart's ring map on the global sections of the projective spectrum.** Over an affine
open `U` of the base, the morphism `Proj (A.grading U) ⟶ S` through the chart carries a function
on `U` to the global section of `𝒪` attached, by Tag 01M7, to the degree-zero element
`A.strHom U r` of the graded ring of sections.

This is the statement the library did not have: `Stacks.AlgebraicGeometry.RelativeProjFlat`
proves it on a standard open of positive degree, and such opens cover the projective spectrum
(`Stacks.AlgebraicGeometry.ProjShared.exists_homogeneous_pos_notMem`). Sections of the structure
sheaf of a projective spectrum are subtypes of dependent families on points and restriction is
evaluation on the nose, so the passage from the cover to `⊤` is `Subtype.ext` followed by
`congrArg` of evaluation at one point; nothing is invoked from the sheaf condition. -/
public theorem chart_appTop (U : S.Opens) (hU : IsAffineOpen U)
    (h : (⊤ : (AlgebraicGeometry.Proj (A.grading U)).Opens) ≤
      ((relativeProj A).chart U hU ≫ (relativeProj A).toBase) ⁻¹ᵁ U) (r : Γ(S, U)) :
    (((relativeProj A).chart U hU ≫ (relativeProj A).toBase).appLE U ⊤ h).hom r =
      degreeZeroRingToGlobalSections (A.grading U) ⟨A.strHom U r, A.strHom_mem U r⟩ := by
  refine Subtype.ext (funext fun x => ?_)
  obtain ⟨d, g, hd, hg, hgx⟩ := ProjShared.exists_homogeneous_pos_notMem (A.grading U) x.1
  exact congrArg (fun s => s.1 ⟨x.1, (hgx : x.1 ∈ Proj.basicOpen (A.grading U) g)⟩)
    (chart_appTop_basicOpen A U hU h r d g hg hd)

/-- The homogeneous section attached to a local section `a` is the degree-zero section map
evaluated at any degree-zero element of the shifted graded ring that has the same underlying
element. -/
private theorem degreeSection_eq_degreeZero (U : S.Opens) (n : ℕ) (a : A.sectionPieces U n)
    (s : twistGrading (A.grading U) (n : ℤ) 0)
    (h : (s : A.sectionRing U) = DirectSum.of (A.sectionPieces U) n a) :
    degreeSection (A.grading U) n
        ⟨DirectSum.of (A.sectionPieces U) n a, A.of_mem_grading U a⟩ =
      degreeZeroToGlobalSections (A.grading U) (twistGrading (A.grading U) (n : ℤ)) s :=
  congrArg (degreeZeroToGlobalSections (A.grading U) (twistGrading (A.grading U) (n : ℤ)))
    (Subtype.ext h.symm)

/-- **The degree-`n` homogeneous section map is linear for the scalars of the base.** Scaling a
local section `a` of the degree-`n` piece by a function `r` on the open scales the homogeneous
section of Tag 01MP attached to it by the global section of `𝒪` attached to `A.strHom U r`.

The multiple `DirectSum.of n (r • a)` is `A.strHom U r * DirectSum.of n a`
(`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.strHom_mul_of`), which is the
action of a degree-zero element on the degree-zero part of the `n`-th shift of the graded ring; and
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroToGlobalSections`, of which
`degreeSection` is an instance, is bundled as a linear map for exactly that action. So this is one
application of `LinearMap.map_smul`. -/
public theorem degreeSection_smul (U : S.Opens) (n : ℕ) (r : Γ(S, U))
    (y : A.sectionPieces U n) :
    degreeSection (A.grading U) n
        ⟨DirectSum.of (A.sectionPieces U) n (r • y), A.of_mem_grading U (r • y)⟩ =
      degreeZeroRingToGlobalSections (A.grading U) ⟨A.strHom U r, A.strHom_mem U r⟩ •
        degreeSection (A.grading U) n
          ⟨DirectSum.of (A.sectionPieces U) n y, A.of_mem_grading U y⟩ := by
  let _ : Module ((A.grading U) 0)
      ((twistingSheaf (A.grading U) (n : ℤ)).val.obj (op ⊤)) :=
    Module.compHom _ (degreeZeroRingToGlobalSections (A.grading U))
  exact (degreeSection_eq_degreeZero A U n (r • y)
      ((⟨A.strHom U r, A.strHom_mem U r⟩ : A.grading U 0) •
        ⟨DirectSum.of (A.sectionPieces U) n y,
          mem_twistGrading_zero (A.grading U) ⟨_, A.of_mem_grading U y⟩⟩)
      (A.strHom_mul_of U r y)).trans (LinearMap.map_smul _ _ _)

end Scalars

/-! ### The homogeneous-section map over one affine open of the base

With the scalar action identified, the degree-`n` homogeneous section map *over a single affine
open* is an honest morphism of modules — which is what the sheaf-level map is assembled from.
-/

section Affine

/-- The transport of a section of a module on the relative Proj, over an open equal to the inverse
image of an open of the base, to a section of the direct image. The open is a variable, so every
statement about this is proved by substituting the equality away. -/
public def pushTransport (M : (relativeProj A).scheme.Modules) (U : S.Opens)
    {W : (relativeProj A).scheme.Opens} (hW : W = (relativeProj A).toBase ⁻¹ᵁ U)
    (z : Γ(M, W)) : Γ((Scheme.Modules.pushforward (relativeProj A).toBase).obj M, U) :=
  (show Γ(M, (relativeProj A).toBase ⁻¹ᵁ U) from hW ▸ z)

/-- The transport is additive. -/
public theorem pushTransport_add (M : (relativeProj A).scheme.Modules) (U : S.Opens)
    {W : (relativeProj A).scheme.Opens} (hW : W = (relativeProj A).toBase ⁻¹ᵁ U)
    (z w : Γ(M, W)) :
    pushTransport M U hW (z + w) = pushTransport M U hW z + pushTransport M U hW w := by
  cases hW
  rfl

/-- **The transport turns the action of the functions on the inverse image into the action of the
functions on the base open.** Over the inverse image itself the comparison map of the direct image
is the component of the morphism of schemes, so this is
`AlgebraicGeometry.Scheme.Hom.appLE_eq_app` together with
`AlgebraicGeometry.Scheme.Modules.pushforward_obj_smul`. -/
public theorem pushTransport_smul (M : (relativeProj A).scheme.Modules) (U : S.Opens)
    {W : (relativeProj A).scheme.Opens} (hW : W = (relativeProj A).toBase ⁻¹ᵁ U)
    (e : W ≤ (relativeProj A).toBase ⁻¹ᵁ U) (r : Γ(S, U)) (z : Γ(M, W)) :
    pushTransport M U hW (((relativeProj A).toBase.appLE U W e).hom r • z) =
      r • pushTransport M U hW z := by
  cases hW
  exact congrArg (fun w => w • z)
    (ConcreteCategory.congr_hom
      (Scheme.Hom.appLE_eq_app (f := (relativeProj A).toBase) (U := U)) r)

/-- Transporting a section and transporting it back is the identity. This is what turns a
statement about `pushTransport` into one in the shape `PsiGluedChart` asks for. -/
public theorem eqRec_pushTransport (M : (relativeProj A).scheme.Modules) (U : S.Opens)
    {W : (relativeProj A).scheme.Opens} (hW : W = (relativeProj A).toBase ⁻¹ᵁ U)
    (z : Γ(M, W)) : (hW.symm ▸ pushTransport M U hW z : Γ(M, W)) = z := by
  cases hW
  rfl

variable (A)

/-- The chart over an affine open of the base, followed by the structure morphism, has the whole
chart as the inverse image of that open: the chart's image is the inverse image of the open, and
the chart is an open immersion. -/
public theorem chart_comp_preimage (U : S.Opens) (hU : IsAffineOpen U) :
    ((relativeProj A).chart U hU ≫ (relativeProj A).toBase) ⁻¹ᵁ U = ⊤ := by
  rw [Scheme.Hom.comp_preimage,
    ← RelativeProjTwistGlue.chart_image_top (relativeProj A) U hU,
    Scheme.Hom.preimage_image_eq]

/-- The degree-`n` homogeneous section map is additive. -/
public theorem degreeSection_of_add (U : S.Opens) (n : ℕ) (a b : A.sectionPieces U n) :
    degreeSection (A.grading U) n
        ⟨DirectSum.of (A.sectionPieces U) n (a + b), A.of_mem_grading U (a + b)⟩ =
      degreeSection (A.grading U) n
          ⟨DirectSum.of (A.sectionPieces U) n a, A.of_mem_grading U a⟩ +
        degreeSection (A.grading U) n
          ⟨DirectSum.of (A.sectionPieces U) n b, A.of_mem_grading U b⟩ := by
  exact (degreeSection_eq_degreeZero A U n (a + b)
    (⟨DirectSum.of (A.sectionPieces U) n a,
        mem_twistGrading_zero (A.grading U) ⟨_, A.of_mem_grading U a⟩⟩ +
      ⟨DirectSum.of (A.sectionPieces U) n b,
        mem_twistGrading_zero (A.grading U) ⟨_, A.of_mem_grading U b⟩⟩)
    (map_add _ a b).symm).trans (map_add _ _ _)

/-- The chart comparison of the glued twist is additive on sections. -/
public theorem gluedMapSection_add (n : ℤ) (hcoc : IsNestedCocycle A n) (U : S.Opens)
    (hU : IsAffineOpen U) (V : (AlgebraicGeometry.Proj (A.grading U)).Opens)
    (x y : (twistingSheaf (A.grading U) n).val.obj (op V)) :
    gluedMapSection n hcoc U hU V (x + y) =
      gluedMapSection n hcoc U hU V x + gluedMapSection n hcoc U hU V y :=
  (congrArg (fun z => (Scheme.Modules.restrictAppIso ((relativeProj A).chart U hU)
      (gluedTwist A n hcoc) V).hom z)
    (map_add ((Tag01VMVeryAmple.gluedChartIso A n hcoc U hU).inv.val.app (op V)).hom x y)).trans
    (map_add _ _ _)

/-- **The scalar comparison of the chart, read through the identification of restriction with
sections on the image.** The global section of `𝒪` attached to the degree-zero element
`A.strHom U r` corresponds, under the chart's isomorphism on functions, to the image of `r` under
the structure morphism of the relative Proj.

This is `chart_appTop` together with `AlgebraicGeometry.Scheme.Hom.appIso_hom'` and
`appLE_comp_appLE`, which factor the chart's composite with the structure morphism through the
chart's isomorphism on functions. -/
public theorem chart_appIso_inv_appTop (U : S.Opens) (hU : IsAffineOpen U)
    (e : (relativeProj A).chart U hU ''ᵁ ⊤ ≤ (relativeProj A).toBase ⁻¹ᵁ U) (r : Γ(S, U)) :
    ((((relativeProj A).chart U hU).appIso
          (⊤ : (AlgebraicGeometry.Proj (A.grading U)).Opens)).inv
        (degreeZeroRingToGlobalSections (A.grading U) ⟨A.strHom U r, A.strHom_mem U r⟩)) =
      (((relativeProj A).toBase.appLE U ((relativeProj A).chart U hU ''ᵁ ⊤) e).hom r) := by
  have hpre := (chart_comp_preimage A U hU).ge
  have key : ((relativeProj A).toBase.appLE U ((relativeProj A).chart U hU ''ᵁ ⊤) e ≫
      (((relativeProj A).chart U hU).appIso
        (⊤ : (AlgebraicGeometry.Proj (A.grading U)).Opens)).hom) =
      ((relativeProj A).chart U hU ≫ (relativeProj A).toBase).appLE U ⊤ hpre := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE]
  refine Eq.trans (congrArg
    (fun w => (((relativeProj A).chart U hU).appIso
      (⊤ : (AlgebraicGeometry.Proj (A.grading U)).Opens)).inv w)
    ((chart_appTop A U hU hpre r).symm.trans
      (ConcreteCategory.congr_hom key.symm r))) ?_
  exact ConcreteCategory.congr_hom
    (((relativeProj A).chart U hU).appIso
      (⊤ : (AlgebraicGeometry.Proj (A.grading U)).Opens)).hom_inv_id _

/-- **The degree-`n` homogeneous section of the glued twist attached to a local section of the base
algebra over an affine open.** The absolute homogeneous section of Tag 01MP on the chart, read in
the glued twist through `Stacks.Tag01VMVeryAmple.gluedChartIso`, and then as a section of the
direct image over the affine open. -/
public def gluedDegreeSection (hcoc : ∀ n : ℤ, IsNestedCocycle A n) (n : ℕ) (U : S.Opens)
    (hU : IsAffineOpen U) (a : A.sectionPieces U n) :
    Γ((Scheme.Modules.pushforward (relativeProj A).toBase).obj
      (gluedTwist A (n : ℤ) (hcoc (n : ℤ))), U) :=
  pushTransport (gluedTwist A (n : ℤ) (hcoc (n : ℤ))) U
    (RelativeProjTwistGlue.chart_image_top (relativeProj A) U hU)
    (gluedMapSection (n : ℤ) (hcoc (n : ℤ)) U hU ⊤
      (degreeSection (A.grading U) n
        ⟨DirectSum.of (A.sectionPieces U) n a, A.of_mem_grading U a⟩))

/-- **The chart description of `gluedDegreeSection`**, in the shape `PsiGluedChart` asks for: it
is the transport back of the chart comparison of the homogeneous section. -/
public theorem gluedMapSection_degreeSection (hcoc : ∀ n : ℤ, IsNestedCocycle A n) (n : ℕ)
    (U : S.Opens) (hU : IsAffineOpen U) (a : A.sectionPieces U n) :
    gluedMapSection (n : ℤ) (hcoc (n : ℤ)) U hU ⊤
        (degreeSection (A.grading U) n
          ⟨DirectSum.of (A.sectionPieces U) n a, A.of_mem_grading U a⟩) =
      (RelativeProjTwistGlue.chart_image_top (relativeProj A) U hU).symm ▸
        gluedDegreeSection A hcoc n U hU a :=
  (eqRec_pushTransport (gluedTwist A (n : ℤ) (hcoc (n : ℤ))) U
    (RelativeProjTwistGlue.chart_image_top (relativeProj A) U hU) _).symm

/-- `gluedDegreeSection` is additive. -/
public theorem gluedDegreeSection_add (hcoc : ∀ n : ℤ, IsNestedCocycle A n) (n : ℕ) (U : S.Opens)
    (hU : IsAffineOpen U) (a b : A.sectionPieces U n) :
    gluedDegreeSection A hcoc n U hU (a + b) =
      gluedDegreeSection A hcoc n U hU a + gluedDegreeSection A hcoc n U hU b :=
  (congrArg (pushTransport (gluedTwist A (n : ℤ) (hcoc (n : ℤ))) U
      (RelativeProjTwistGlue.chart_image_top (relativeProj A) U hU))
    ((congrArg (gluedMapSection (n : ℤ) (hcoc (n : ℤ)) U hU ⊤)
      (degreeSection_of_add A U n a b)).trans
      (gluedMapSection_add A (n : ℤ) (hcoc (n : ℤ)) U hU ⊤ _ _))).trans
    (pushTransport_add _ U _ _ _)

/-- **The chart comparison carries the homogeneous section of a scaled local section to the scaled
homogeneous section**, with the scalar read through the structure morphism of the relative Proj.
Stated separately from `gluedDegreeSection_smul` so that the kernel checks the two apart: inlined
into the `LinearMap` structure the composite proof term exceeds the kernel's step limit. -/
public theorem gluedMapSection_degreeSection_smul (hcoc : ∀ n : ℤ, IsNestedCocycle A n) (n : ℕ)
    (U : S.Opens) (hU : IsAffineOpen U) (r : Γ(S, U)) (a : A.sectionPieces U n) :
    gluedMapSection (n : ℤ) (hcoc (n : ℤ)) U hU ⊤
        (degreeSection (A.grading U) n
          ⟨DirectSum.of (A.sectionPieces U) n (r • a), A.of_mem_grading U (r • a)⟩) =
      ((gluedTwist A (n : ℤ) (hcoc (n : ℤ))).smul
          (((relativeProj A).toBase.appLE U ((relativeProj A).chart U hU ''ᵁ ⊤)
            (RelativeProjTwistGlue.chart_image_top (relativeProj A) U hU).le).hom r)).asHom.hom
        (gluedMapSection (n : ℤ) (hcoc (n : ℤ)) U hU ⊤
          (degreeSection (A.grading U) n
            ⟨DirectSum.of (A.sectionPieces U) n a, A.of_mem_grading U a⟩)) :=
  ((congrArg (gluedMapSection (n : ℤ) (hcoc (n : ℤ)) U hU ⊤)
      (degreeSection_smul A U n r a)).trans
    ((congrArg (fun z => (Scheme.Modules.restrictAppIso ((relativeProj A).chart U hU)
          (gluedTwist A (n : ℤ) (hcoc (n : ℤ))) ⊤).hom z)
        (((Tag01VMVeryAmple.gluedChartIso A (n : ℤ) (hcoc (n : ℤ)) U hU).inv.val.app
          (op (⊤ : (AlgebraicGeometry.Proj (A.grading U)).Opens))).hom.map_smul _ _)).trans
      (Scheme.Modules.smul_restrictAppIso_hom_apply _ _ _ _ _))).trans
    (congrArg (fun s => ((gluedTwist A (n : ℤ) (hcoc (n : ℤ))).smul s).asHom.hom
        (gluedMapSection (n : ℤ) (hcoc (n : ℤ)) U hU ⊤
          (degreeSection (A.grading U) n
            ⟨DirectSum.of (A.sectionPieces U) n a, A.of_mem_grading U a⟩)))
      (chart_appIso_inv_appTop A U hU
        (RelativeProjTwistGlue.chart_image_top (relativeProj A) U hU).le r))

/-- **`gluedDegreeSection` is `Γ(S, U)`-linear.** -/
public theorem gluedDegreeSection_smul (hcoc : ∀ n : ℤ, IsNestedCocycle A n) (n : ℕ) (U : S.Opens)
    (hU : IsAffineOpen U) (r : Γ(S, U)) (a : A.sectionPieces U n) :
    gluedDegreeSection A hcoc n U hU (r • a) = r • gluedDegreeSection A hcoc n U hU a :=
  (congrArg (pushTransport (gluedTwist A (n : ℤ) (hcoc (n : ℤ))) U
      (RelativeProjTwistGlue.chart_image_top (relativeProj A) U hU))
    (gluedMapSection_degreeSection_smul A hcoc n U hU r a)).trans
    (pushTransport_smul (gluedTwist A (n : ℤ) (hcoc (n : ℤ))) U
      (RelativeProjTwistGlue.chart_image_top (relativeProj A) U hU)
      (RelativeProjTwistGlue.chart_image_top (relativeProj A) U hU).le r _)

/-- **The homogeneous-section map of the glued twist over one affine open of the base**, as a
`Γ(S, U)`-linear map. This is the component over an affine open that a term of
`PsiGluedChart`'s section map must have, and it is the whole content of the scalar half of such a
term: what remains is the compatibility of these components with restriction between two affine
opens, from which the sheaf-level morphism follows by
`Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis`. -/
public def psiGluedAffine (hcoc : ∀ n : ℤ, IsNestedCocycle A n) (n : ℕ) (U : S.Opens)
    (hU : IsAffineOpen U) :
    A.sectionPieces U n →ₗ[Γ(S, U)]
      Γ((Scheme.Modules.pushforward (relativeProj A).toBase).obj
        (gluedTwist A (n : ℤ) (hcoc (n : ℤ))), U) where
  toFun := gluedDegreeSection A hcoc n U hU
  map_add' := gluedDegreeSection_add A hcoc n U hU
  map_smul' := gluedDegreeSection_smul A hcoc n U hU

end Affine

/-! ### The reduced constructor -/

/-- **Tag 01NR's twist datum, assembled from three fields.** On top of the four fields
`Stacks.AlgebraicGeometry.GluedTwistChartData.mk` asks for, the chart description of the
homogeneous-section map is no longer among them: it is `psiChart_of_psiGluedChart`, provided the
section map is given for the glued twists and satisfies `PsiGluedChart`.

What remains is the algebra `B` together with the identification `e` of its pieces with the glued
twists, the condition that its product and unit agree on the charts with those of the absolute
twists, and a homogeneous-section map for the glued twists with its chart description. -/
public def mk (hcoc : ∀ n : ℤ, IsNestedCocycle A n)
    (B : SchemeGradedAlgebra (relativeProj A).scheme)
    (e : ∀ n : ℤ, B.piece n ≅ gluedTwist A n (hcoc n))
    (hD : IsGradedChartIso (GluedTwistChartData.chartData hcoc B e))
    (psi : ∀ n : ℕ, A.piece (n : ℤ) ⟶
      (Scheme.Modules.pushforward (relativeProj A).toBase).obj
        (gluedTwist A (n : ℤ) (hcoc (n : ℤ))))
    (hpsi : PsiGluedChart hcoc psi) : TwistData A :=
  GluedTwistChartData.mk hcoc B e hD
    (fun n => psi n ≫
      (Scheme.Modules.pushforward (relativeProj A).toBase).map (e (n : ℤ)).inv)
    (psiChart_of_psiGluedChart hcoc B e hpsi)

end Stacks.AlgebraicGeometry.GluedTwistSectionMap

end
