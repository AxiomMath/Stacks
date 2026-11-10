module

public import StacksFrontier.AlgebraicGeometry.GluedTwistAlgebra.Assemble
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.DegreeOne

/-!
# Sections and rational sections of `𝒪_{𝐏(E)}(1)` over a general base

Let `X` be a scheme and `E` a quasi-coherent `𝒪_X`-module, let `π : 𝐏(E) ⟶ X` be its projective
bundle — the relative homogeneous spectrum of `Sym(E)`, Stacks 01NQ — and let `𝒪_{𝐏(E)}(1)` be
its first twist, `Stacks.Tag01VMVeryAmple.twistOne`. Stacks 01OB's section map in degree one is a
morphism of `𝒪_X`-modules

`E ⟶ π_* 𝒪_{𝐏(E)}(1)`,

so an element of `E` over an open `U` of the base determines a section of `𝒪_{𝐏(E)}(1)` over
`π^{-1}(U)`, and its germ at a point of `π^{-1}(U)` depends only on the germ of that element at
the image point — that is, only on the element of the fibre of `E` there. The germ at the generic
point is the *rational section* of `𝒪_{𝐏(E)}(1)` attached to an element of the fibre `E_ξ`, which
is the form in which the divisor and first-Chern-class machinery of
`StacksFrontier/AlgebraicGeometry/Chow/MeromorphicOrder.lean` consumes a meromorphic section: there
a meromorphic section of an invertible module `L` on an integral scheme *is* an element of the
stalk `L_η` at the generic point.

This file builds all of that. The degree-one case of Stacks 01OB's map is read off the
homogeneous-section map `ψ` of Stacks 01NR, which
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra` supplies for every
quasi-coherent graded algebra with no further hypothesis, composed with the degree-one generator
`E ⟶ Sym(E)_1` of `AlgebraicGeometry.Scheme.Modules.symmetricAlgebraGen`. Nothing is assumed
about `E` beyond quasi-coherence: neither finite local freeness, nor a rank, nor anything about
`X`.

## Main definitions

* `Stacks.ProjectiveBundleTwist.toPushforwardTwist`: **Stacks 01OB's section map in degree one**,
  `E ⟶ π_* 𝒪_{𝐏(E)}(1)`.
* `Stacks.ProjectiveBundleTwist.twistSection`: **the section of `𝒪_{𝐏(E)}(1)` over `π^{-1}(U)`
  attached to a section of `E` over `U`.**
* `Stacks.ProjectiveBundleTwist.twistSectionGerm`: **its germ at a point of `π^{-1}(U)`** — the
  rational section of `𝒪_{𝐏(E)}(1)` attached to an element of the fibre of `E`.

## Main results

* `Stacks.ProjectiveBundleTwist.isInvertible_twistOne`: `𝒪_{𝐏(E)}(1)` is invertible, in the
  spelling the Chow and divisor machinery asks for. This makes the sections below sections of an
  invertible module, so that `Stacks.Divisors.zeroScheme`,
  `Stacks.Divisors.orderOfVanishing` and `Stacks.Chow.firstChernComponentCycleRule` apply to
  them.
* `Stacks.ProjectiveBundleTwist.twistSection_add`, `twistSection_zero` and
  `twistSection_res`: the section map is additive and compatible with restriction on the base.
* `Stacks.ProjectiveBundleTwist.twistSectionGerm_eq_of_germ_eq`: **the germ depends only on the
  germ of the element of `E`**, so the rational section attached to an element of the fibre `E_ξ`
  is well defined, independently of the open on which a representative is chosen.
* `Stacks.ProjectiveBundleTwist.twistSection_chart`: **the chart formula.** Over an affine open
  `V` of the base, the section attached to `e` is, under the identification of `π^{-1}(V)` with
  `Proj Γ(V, Sym(E))`, the canonical section `degreeSection` of the absolute `𝒪(1)` attached to
  the degree-one homogeneous element that `e` names. This is the bridge along which the
  vanishing locus of the section is computed: for the absolute twist the nonvanishing locus of
  `degreeSection 𝒮 1 a` is the standard open `D₊(a)`, which is
  `AlgebraicGeometry.ProjectiveSpectrum.Proj.nonvanishingLocus_degreeSection_one` of
  `StacksFrontier/AlgebraicGeometry/ProjectiveBundle/TwistSectionLocus.lean`.

## Implementation notes

**Which `𝐏(E)` and which `𝒪(1)`.** Both are the ones built over
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`: the bundle is
`Stacks.AlgebraicGeometry.RelativeProj.relativeProj` applied to
`Stacks.Tag01VMRelativeVeryAmple.symAlgebra E`, which is
`Stacks.SymGraded.schemeProjectiveBundle E _` by definition, and the twist is
`Stacks.Tag01VMVeryAmple.twistOne E`. The twist that Stacks 01NR's graded algebra carries in degree
one is the *same term*: `Stacks.ProjectiveBundleTwist.algebra_piece_one_eq_twistOne` is `rfl`,
because both are `Stacks.AlgebraicGeometry.ChartTransRelativeProj.gluedTwist` of the symmetric
algebra in degree one and the nested-cocycle hypothesis they are indexed by is a `Prop`. That
identity is what lets the section map of Stacks 01NR and the chart identification and invertibility
of Stacks 01O4 be used about one and the same module.

`Stacks.RelativeProj.projectiveBundle`, the bundle carrying the `01OB` attribute, is built
instead over `Stacks.RelativeProj.Situation`, and the two glueings are not compared anywhere in
this repository — as the implementation notes of
`StacksFrontier/AlgebraicGeometry/ProjectiveBundle/FlatAndRelativeDimension.lean` record. So the
sections built here live on the `SheafGradedAlgebra` bundle, which is the one the twist exists
on. A consumer such as
`StacksFrontier/AlgebraicGeometry/Chow/ChernClassHigher/ProjectiveBundleProjectionFormula.lean`
takes its `π : P ⟶ X` and its invertible `L` on `P` as parameters, so this costs it nothing.

**The target of the section map.** `toPushforwardTwist` is a morphism of `𝒪_X`-modules into
`π_* 𝒪_{𝐏(E)}(1)` rather than a family of maps on sections, which is what makes additivity and
compatibility with restriction on the base theorems about a morphism of presheaves of modules
instead of computations: `Γ(π_* M, U)` and `Γ(M, π^{-1} U)` are the same group, and the
restriction maps of the two agree on the nose, which is
`Stacks.ProjectiveBundleTwist.pushforward_map_eq`.

**The degree index.** `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.ψ` is indexed by a
natural number and the homogeneous pieces by an integer, so the degree reads `((1 : ℕ) : ℤ)` on
one side and `(1 : ℤ)` on the other; the two are the same integer and no transport is needed.

## What is not done here

**The vanishing locus is not transported off the chart.** `twistSection_chart` identifies the
section with `degreeSection` through
`Stacks.AlgebraicGeometry.RelativeProjTwists.ChartData.mapSection`, and the nonvanishing locus of
`degreeSection` is known — it is the standard open `D₊(a)`,
`AlgebraicGeometry.ProjectiveSpectrum.Proj.nonvanishingLocus_degreeSection_one` — but the
equality

`π^{-1}(V) ∩ X_{s(e)} = chart '' D₊(e)`

is not proved. Every ingredient except one is available: Stacks 0H78 for a section over an open is
`Stacks.NonvanishingLocusRestrict.preimage_nonvanishingLocusOn`, a section over `π^{-1}(V)` is
read as a global section on the open subscheme by
`Stacks.NonvanishingLocusRestrict.restrictSection` with
`Stacks.NonvanishingLocusRestrict.nonvanishingLocus_restrictSection`, the nonvanishing locus
transports along an isomorphism of modules by `Stacks.Ample.nonvanishingLocus_congr`, and the
isomorphism to transport along is `Stacks.Tag01VNChartBasis.chartTwistIso`, which identifies the
pullback of the absolute `𝒪(1)` along `Stacks.AlgebraicGeometry.RelativeProjTwistQcoh`
`.chartIsoPreimage` with the restriction of the glued twist to `π^{-1}(V)`.

What is missing is the *section-level* compatibility of that isomorphism with `mapSection`: that
`chartTwistIso` carries the pullback of `degreeSection 𝒮 1 a` to `restrictSection` of
`twistSection`. `chartTwistIso` is a four-step composite of
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` — itself a
`CategoryTheory.Adjunction.leftAdjointUniq` — and
`AlgebraicGeometry.ProjectiveSpectrum.Proj.restrictIsoOfIsoOver`, and none of the four steps has
a formula on sections in the library. Until one of them does, the equality above cannot be
derived from `twistSection_chart`, which is why that lemma is stated in the `mapSection`
spelling rather than as a statement about loci.

**The common zero scheme of `r - 1` sections is not identified with the image of a section of
`π`.** That is the geometric step the `s = r - 1` case of Stacks 02TW needs beyond the sections
themselves, and it needs the mapping-in half of the universal property of relative `Proj`
(Constructions, Section 01NS), which this repository carries as the hypothesis
`Stacks.RelativeProj.TautologicalDatum.IsUniversal` and inhabits only over a scheme with no
points.

## References

* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 01MV](https://stacks.math.columbia.edu/tag/01MV)
* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.Tag01VMRelativeVeryAmple

namespace Stacks.ProjectiveBundleTwist

universe u

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]

/-! ### The twist datum of the projective bundle -/

/-- **Stacks 01NR's twist datum on the projective bundle `𝐏(E) = Proj_X(Sym(E))`**, which
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra` supplies for a
quasi-coherent graded algebra with no hypothesis beyond the algebra. -/
abbrev twistData : TwistData (symAlgebra E) :=
  Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra (symAlgebra E)

/-- **The degree-one piece of Stacks 01NR's graded algebra on `𝐏(E)` is the twist
`𝒪_{𝐏(E)}(1)`** of `Stacks.Tag01VMVeryAmple.twistOne`, on the nose. Both are the degree-one
glued twist of Stacks 01NO for `Sym(E)`, and the nested-cocycle hypothesis they are indexed by
is a `Prop`. -/
theorem algebra_piece_one_eq_twistOne :
    (twistData E).algebra.piece 1 = Stacks.Tag01VMVeryAmple.twistOne E := rfl

/-- **`𝒪_{𝐏(E)}(1)` is invertible**, in the spelling the zero-scheme, divisor and Chow machinery
asks for. This is Stacks 01O4 in degree one,
`Stacks.Tag01VMVeryAmple.isInvertibleModule_twistOne`, with the sheaf condition on the structure
sheaf of rings written as `ringCatSheaf.property` rather than as
`Stacks.SheafInternalHom.isSheaf_structureRingPresheaf`; instance search does not unfold either
spelling into the other. -/
instance isInvertible_twistOne :
    AlgebraicGeometry.SheafOfModules.IsInvertible
      (relativeProj (symAlgebra E)).scheme.sheaf.obj
      (relativeProj (symAlgebra E)).scheme.ringCatSheaf.property
      (Stacks.Tag01VMVeryAmple.twistOne E) :=
  Stacks.Tag01VMVeryAmple.isInvertibleModule_twistOne E

/-! ### Stacks 01OB's section map in degree one -/

/-- **Stacks 01OB's section map in degree one: `E ⟶ π_* 𝒪_{𝐏(E)}(1)`.** It is the degree-one
generator `E ⟶ Sym(E)_1` of `AlgebraicGeometry.Scheme.Modules.symmetricAlgebraGen` followed by
the homogeneous-section map `ψ_1` of Stacks 01NR.

Nothing is assumed about `E` beyond quasi-coherence. -/
def toPushforwardTwist :
    E ⟶ (Scheme.Modules.pushforward (relativeProj (symAlgebra E)).toBase).obj
      (Stacks.Tag01VMVeryAmple.twistOne E) :=
  Scheme.Modules.symmetricAlgebraGen X E ≫ (twistData E).ψ 1

/-- The restriction maps of `π_* M` are the restriction maps of `M` along the inverse images. -/
theorem pushforward_map_eq {U V : X.Opens} (h : U ≤ V) :
    ((Scheme.Modules.pushforward (relativeProj (symAlgebra E)).toBase).obj
          (Stacks.Tag01VMVeryAmple.twistOne E)).presheaf.map (homOfLE h).op =
      (Stacks.Tag01VMVeryAmple.twistOne E).presheaf.map
        (homOfLE (TopologicalSpace.Opens.comap_mono
          (relativeProj (symAlgebra E)).toBase.base.hom h)).op := rfl

/-- **The section of `𝒪_{𝐏(E)}(1)` over `π^{-1}(U)` attached to a section of `E` over `U`.** -/
def twistSection (U : X.Opens) (e : Γ(E, U)) :
    Γ(Stacks.Tag01VMVeryAmple.twistOne E, (relativeProj (symAlgebra E)).toBase ⁻¹ᵁ U) :=
  (toPushforwardTwist E).app U e

/-- The section map is additive. -/
theorem twistSection_add (U : X.Opens) (e f : Γ(E, U)) :
    twistSection E U (e + f) = twistSection E U e + twistSection E U f := map_add _ e f

/-- The section attached to the zero section of `E` is zero. -/
@[simp] theorem twistSection_zero (U : X.Opens) : twistSection E U 0 = 0 := map_zero _

/-- **The section map commutes with restriction on the base.** -/
theorem twistSection_res (U V : X.Opens) (h : U ≤ V) (e : Γ(E, V)) :
    (Stacks.Tag01VMVeryAmple.twistOne E).presheaf.map
        (homOfLE (TopologicalSpace.Opens.comap_mono
          (relativeProj (symAlgebra E)).toBase.base.hom h)).op (twistSection E V e) =
      twistSection E U (E.presheaf.map (homOfLE h).op e) :=
  (PresheafOfModules.naturality_apply (toPushforwardTwist E).val (homOfLE h).op e).symm

/-! ### Rational sections: the germ at a point of the bundle -/

/-- **The rational section of `𝒪_{𝐏(E)}(1)` attached to a section of `E` over `U`**: the germ at
a point `y` of `π^{-1}(U)` of the section of the twist that `e` determines.

By `Stacks.ProjectiveBundleTwist.twistSectionGerm_eq_of_germ_eq` this depends only on the germ of
`e` at `π(y)`, hence only on the element of the fibre of `E` at `π(y)` that `e` names. At the
generic point of an integral `𝐏(E)` it is a meromorphic section of the invertible module
`𝒪_{𝐏(E)}(1)` in the sense of `StacksFrontier/AlgebraicGeometry/Chow/MeromorphicOrder.lean`, where
a meromorphic section is an element of the stalk at the generic point. -/
def twistSectionGerm (U : X.Opens) (e : Γ(E, U))
    (y : (relativeProj (symAlgebra E)).scheme)
    (hy : y ∈ (relativeProj (symAlgebra E)).toBase ⁻¹ᵁ U) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (Stacks.Tag01VMVeryAmple.twistOne E).presheaf y :=
  ((Stacks.Tag01VMVeryAmple.twistOne E).presheaf.germ
    ((relativeProj (symAlgebra E)).toBase ⁻¹ᵁ U) y hy).hom (twistSection E U e)

/-- The rational section attached to `e` is additive in `e`. -/
theorem twistSectionGerm_add (U : X.Opens) (e f : Γ(E, U))
    (y : (relativeProj (symAlgebra E)).scheme)
    (hy : y ∈ (relativeProj (symAlgebra E)).toBase ⁻¹ᵁ U) :
    twistSectionGerm E U (e + f) y hy =
      twistSectionGerm E U e y hy + twistSectionGerm E U f y hy := by
  change ((Stacks.Tag01VMVeryAmple.twistOne E).presheaf.germ _ y hy).hom
      (twistSection E U (e + f)) = _
  rw [twistSection_add, map_add]
  rfl

/-- **Restricting the section of `E` does not change the rational section.** -/
theorem twistSectionGerm_res (U V : X.Opens) (h : U ≤ V) (e : Γ(E, V))
    (y : (relativeProj (symAlgebra E)).scheme)
    (hy : y ∈ (relativeProj (symAlgebra E)).toBase ⁻¹ᵁ U) :
    twistSectionGerm E U (E.presheaf.map (homOfLE h).op e) y hy =
      twistSectionGerm E V e y
        (TopologicalSpace.Opens.comap_mono
          (relativeProj (symAlgebra E)).toBase.base.hom h hy) := by
  unfold twistSectionGerm
  rw [← twistSection_res E U V h e]
  exact TopCat.Presheaf.germ_res_apply (Stacks.Tag01VMVeryAmple.twistOne E).presheaf
    (homOfLE (TopologicalSpace.Opens.comap_mono
      (relativeProj (symAlgebra E)).toBase.base.hom h)) y hy (twistSection E V e)

/-- **The rational section attached to an element of the fibre of `E` is well defined.** Two
sections of `E`, over possibly different opens, with the same germ at `π(y)` have the same
rational section at `y`.

So for `ξ` a point of `X` and an element of the stalk `E_ξ` — the fibre of `E` at `ξ` — the
rational section of `𝒪_{𝐏(E)}(1)` it determines at any point of the fibre `π^{-1}(ξ)` does not
depend on the representative chosen for it. -/
theorem twistSectionGerm_eq_of_germ_eq (U V : X.Opens) (e : Γ(E, U)) (f : Γ(E, V))
    (y : (relativeProj (symAlgebra E)).scheme)
    (hyU : y ∈ (relativeProj (symAlgebra E)).toBase ⁻¹ᵁ U)
    (hyV : y ∈ (relativeProj (symAlgebra E)).toBase ⁻¹ᵁ V)
    (h : E.presheaf.germ U ((relativeProj (symAlgebra E)).toBase.base y) hyU e =
      E.presheaf.germ V ((relativeProj (symAlgebra E)).toBase.base y) hyV f) :
    twistSectionGerm E U e y hyU = twistSectionGerm E V f y hyV := by
  obtain ⟨W, hW, iU, iV, heq⟩ := TopCat.Presheaf.germ_eq E.presheaf
    ((relativeProj (symAlgebra E)).toBase.base y) hyU hyV e f h
  have h1 := twistSectionGerm_res E W U iU.le e y hW
  have h2 := twistSectionGerm_res E W V iV.le f y hW
  have h3 : E.presheaf.map (homOfLE iU.le).op e = E.presheaf.map (homOfLE iV.le).op f := heq
  rw [← h1, ← h2, h3]

/-! ### The chart formula -/

/-- **The chart formula.** Over an affine open `V` of the base, the section of `𝒪_{𝐏(E)}(1)` over
`π^{-1}(V)` attached to `e ∈ Γ(E, V)` is the canonical section `degreeSection` of the absolute
twist `𝒪(1)` on `Proj Γ(V, Sym(E))` attached to the degree-one homogeneous element that `e`
names, read through the chart identification of Stacks 01NR.

This is the clause `ψ_chart` of Stacks 01NR in degree one, with the degree-one element produced
by `AlgebraicGeometry.Scheme.Modules.symmetricAlgebraGen`. It is the bridge along which the
vanishing locus of `twistSection` is computed: for the absolute twist the nonvanishing locus of
`degreeSection 𝒮 1 a` is the standard open `D₊(a)`, by
`AlgebraicGeometry.ProjectiveSpectrum.Proj.nonvanishingLocus_degreeSection_one`. -/
theorem twistSection_chart (V : X.Opens) (hV : IsAffineOpen V) (e : Γ(E, V)) :
    letI := (twistData E).chartData.chart_isOpenImmersion V hV
    (twistData E).chartData.mapSection V hV ((1 : ℕ) : ℤ) ⊤
      (degreeSection ((symAlgebra E).grading V) 1
        ⟨DirectSum.of ((symAlgebra E).sectionPieces V) 1
            (Scheme.Modules.Hom.app (Scheme.Modules.symmetricAlgebraGen X E) V e),
          (symAlgebra E).of_mem_grading V
            (Scheme.Modules.Hom.app (Scheme.Modules.symmetricAlgebraGen X E) V e)⟩) =
      ((twistData E).chartData.chart_range V hV).symm ▸ twistSection E V e :=
  (twistData E).ψ_chart V hV 1 _

end Stacks.ProjectiveBundleTwist

end
