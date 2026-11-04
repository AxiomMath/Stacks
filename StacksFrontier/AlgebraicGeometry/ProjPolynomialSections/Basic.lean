module

public import StacksFrontier.AlgebraicGeometry.ProjPolynomialSections.Integral
public import StacksFrontier.AlgebraicGeometry.ProjBundleProjectiveSpace.IntegralCharts
public import StacksFrontier.AlgebraicGeometry.FiniteMorphismProjective.Basic

/-!
# A relative homogeneous spectrum whose section rings are polynomial rings IS projective space

`Stacks.AlgebraicGeometry.RelativeProjIsProjectiveSpace.IntegralCharts` reduces
`Proj_S(𝒜) ≅ ℙⁿ_S` over `S` to a compatible family of morphisms from the charts to the integral
model `ℙⁿ_ℤ`, each inducing an isomorphism onto `ℙⁿ_U`. **This file discharges that input from a
purely algebraic hypothesis**: a compatible family of graded ring isomorphisms of the section
rings `Γ(U, 𝒜)` with the polynomial rings `Γ(S, U)[T₀, …, Tₙ]`.

The geometry needed is already in the library and is used here without being redone:
`Stacks.AlgebraicGeometry.ProjBaseChange.isIso_projCompare` says
`Proj R[T₀, …, Tₙ] ≅ ℙⁿ_{Spec R}` over `Spec R`, and
`Stacks.FiniteMorphismProjective.baseTransport` moves `ℙⁿ` along the isomorphism
`U ≅ Spec Γ(S, U)` of an affine open with the spectrum of its sections. So
each chart of `Proj_S(𝒜)` is identified with `ℙⁿ_U` by a composite of three isomorphisms, and the
glued statement follows.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjPolynomialSections.PolynomialSections`: **the hypothesis.** A
  pair of mutually inverse graded ring homomorphisms between `Γ(U, 𝒜)` and
  `Γ(S, U)[T₀, …, Tₙ]` for every affine open `U` of the base, carrying constants to the
  structure morphism of `𝒜` and compatible with restriction.
* `Stacks.AlgebraicGeometry.ProjPolynomialSections.PolynomialSections.projIso`: the induced
  identification `Proj Γ(U, 𝒜) ≅ Proj Γ(S, U)[T₀, …, Tₙ]`.
* `Stacks.AlgebraicGeometry.ProjPolynomialSections.PolynomialSections.toIntegralCharts`: the
  chart data of `Stacks.AlgebraicGeometry.RelativeProjIsProjectiveSpace.IntegralCharts`.
* `Stacks.AlgebraicGeometry.ProjPolynomialSections.PolynomialSections.toProjectiveSpaceCharts`:
  the chart data of
  `Stacks.AlgebraicGeometry.RelativeProjIsProjectiveSpace.ProjectiveSpaceCharts`.

## Main results

* `Stacks.AlgebraicGeometry.ProjPolynomialSections.PolynomialSections.chart_eq`: the induced
  morphism `Proj Γ(U, 𝒜) ⟶ ℙⁿ_U` **is** the comparison of the polynomial and base-change models
  of projective space, read through the identification of the chart with the polynomial model and
  through the identification of `U` with `Spec Γ(S, U)`.
* `Stacks.AlgebraicGeometry.ProjPolynomialSections.PolynomialSections.isIso_chart`: consequently
  **each chart is an isomorphism onto `ℙⁿ_U`**, by composition of three isomorphisms, with no
  further hypothesis.
* `Stacks.AlgebraicGeometry.ProjPolynomialSections.PolynomialSections.exists_schemeIso`:
  **`Proj_S(𝒜) ≅ ℙⁿ_S` over `S`.**
* `Stacks.AlgebraicGeometry.ProjPolynomialSections.exists_iso_relativeProj`: the same at
  `Stacks.AlgebraicGeometry.RelativeProj.relativeProj` of a sheaf-level graded algebra,
  which is the form `Stacks.Tag087SBundle.projectiveBundle` is built at.

## Implementation notes

**Everything is phrased with `Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop`, never with
`AlgebraicGeometry.Proj.map` directly.** The transition morphisms of `𝒜` are `mapHomOfTop` by
definition and `Stacks.AlgebraicGeometry.ProjPolyChart.coordinateProjMap` is `mapHomOfTop`
by `rfl`, so the composition law
`Stacks.AlgebraicGeometry.ProjBundleSurjection.mapHomOfTop_comp` applies to every composite that
occurs, and no equation has to be transported across the retyping of the integral model.

**The compatibility with the transitions is proved generically and instantiated.** The inclusion
of affine opens is a plain variable in
`PolynomialSections.toIntegral_transition_of`, which is instantiated by `exact`; stating it
directly at `AlgebraicGeometry.Scheme.AffineZariskiSite.toOpens_mono` of a morphism of the site
is the failure recorded in the implementation notes of
`StacksDraft.AlgebraicGeometry.F3.ProjBundleProjectiveSpace.IntegralCharts`.

**The two gradings are valued in different carriers and that is unavoidable.**
`Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra` grades by `AddSubgroup` and
`Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading` by `Submodule`, so the identification can
only be a graded ring homomorphism, never an equality of gradings; see
`StacksDraft.AlgebraicGeometry.F3.ProjPolynomialSections.GradedIso`.

## References

* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 087S](https://stacks.math.columbia.edu/tag/087S)

## Not done here

**No project tag is attached.** Nothing here is the statement of a tag: Tag 01NF's labels are
about projective space itself, and the two labels of Tag 087S quantify over projectivity of a
morphism.

`PolynomialSections` is not constructed for the sheafified symmetric algebra of a free module.
`StacksDraft.AlgebraicGeometry.F3.ProjPolynomialSections.Polynomial` constructs it for the
polynomial graded algebra `𝒪_S[T₀, …, Tₙ]`, which makes the hypothesis non-vacuous and gives
`Proj_S(𝒪_S[T₀, …, Tₙ]) ≅ ℙⁿ_S` unconditionally; what is still owed for
`𝐏(𝒪_S^{⊕(n+1)}) ≅ ℙⁿ_S`, and hence for part (1) of Tag 087S, is the **algebra**: a graded ring
isomorphism of `Γ(U, Sym(𝒪_S^{⊕(n+1)}))` with `Γ(S, U)[T₀, …, Tₙ]` natural in the affine open
`U`. The pieces of that are the sheafification unit
(`Stacks.SymGraded.unitSection`, multiplicative by `Stacks.SymGraded.unitSection_mul` and
surjective over an affine open by `Stacks.SymGraded.surjective_unitSection`) being *injective*
over an affine open — not proved anywhere, and for a free module it should hold because the
sectionwise symmetric power is already a sheaf — together with
`SymPow.symmetricPowerEquivHomogeneousSubmodule` identifying each graded piece with
`MvPolynomial.homogeneousSubmodule`. None of that is here.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomogeneousIdeal MvPolynomial
open Stacks.AlgebraicGeometry.RelativeProj Stacks.AlgebraicGeometry.RelativeProjGlue
open Stacks.AlgebraicGeometry.ProjShared
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjBundleSurjection
open Stacks.AlgebraicGeometry.RelativeProjIsProjectiveSpace

namespace Stacks.AlgebraicGeometry.ProjPolynomialSections

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {S : Scheme.{u}} (𝒜 : GradedAlgebra S) (n : ℕ)

/-- The restriction homomorphism of the structure sheaf along an inclusion of opens. -/
public abbrev resHom {U V : S.Opens} (h : U ≤ V) : ↥Γ(S, V) →+* ↥Γ(S, U) :=
  (S.presheaf.map (homOfLE h).op).hom

/-- **A compatible family of identifications of the section rings of `𝒜` with polynomial rings.**
-/
public structure PolynomialSections where
  /-- The identification, from the polynomial ring to the sections. -/
  ofPoly (U : S.AffineZariskiSite) :
    polyGrading ↥Γ(S, U.toOpens) n →+*ᵍ 𝒜.grading U
  /-- Its inverse. -/
  toPoly (U : S.AffineZariskiSite) :
    𝒜.grading U →+*ᵍ polyGrading ↥Γ(S, U.toOpens) n
  /-- The two are inverse, one way. -/
  ofPoly_toPoly (U : S.AffineZariskiSite) (a : 𝒜.ring U) : ofPoly U (toPoly U a) = a
  /-- The two are inverse, the other way. -/
  toPoly_ofPoly (U : S.AffineZariskiSite) (p : MvPolynomial (Fin (n + 1)) ↥Γ(S, U.toOpens)) :
    toPoly U (ofPoly U p) = p
  /-- The identification carries a constant polynomial to the structure morphism's value. -/
  ofPoly_C (U : S.AffineZariskiSite) (r : ↥Γ(S, U.toOpens)) :
    ofPoly U (MvPolynomial.C r) = 𝒜.str U r
  /-- The identifications are compatible with restriction. -/
  res_ofPoly {U V : S.AffineZariskiSite} (h : U.toOpens ≤ V.toOpens)
      (p : MvPolynomial (Fin (n + 1)) ↥Γ(S, V.toOpens)) :
    𝒜.res h (ofPoly V p) = ofPoly U (MvPolynomial.map (resHom h) p)

namespace PolynomialSections

variable {𝒜 n} (hp : PolynomialSections 𝒜 n)

/-- The identification of the chart over an affine open with the polynomial projective
spectrum. -/
public def projIso (U : S.AffineZariskiSite) :
    𝒜.projOver U ≅ AlgebraicGeometry.Proj (polyGrading ↥Γ(S, U.toOpens) n) :=
  projIsoOfGradedSections _ _ (hp.ofPoly U) (hp.toPoly U) (hp.ofPoly_toPoly U)
    (hp.toPoly_ofPoly U)


/-- The morphism from the chart over an affine open to the integral model of projective
`n`-space: the identification with the polynomial model, followed by the morphism induced by the
canonical coefficient homomorphism. -/
public def toIntegral (U : S.AffineZariskiSite) :
    𝒜.projOver U ⟶ projectiveSpaceAtUniverse.{u} n :=
  (hp.projIso U).hom ≫ polyToIntegral ↥Γ(S, U.toOpens) n

/-- Mathlib's hypothesis for `AlgebraicGeometry.Proj.map`, for the identification. -/
public theorem irrelevant_le_map_ofPoly (U : S.AffineZariskiSite) :
    irrelevant (𝒜.grading U) ≤
      (irrelevant (polyGrading ↥Γ(S, U.toOpens) n)).map (hp.ofPoly U) :=
  irrelevant_le_map_of_graded_section _ _ (hp.ofPoly U) (hp.toPoly U) (hp.ofPoly_toPoly U)

/-- The identification is everywhere defined. -/
public theorem mapDomain_ofPoly_eq_top (U : S.AffineZariskiSite) :
    mapDomain (polyGrading ↥Γ(S, U.toOpens) n) (𝒜.grading U) (hp.ofPoly U) = ⊤ :=
  mapDomain_eq_top_of_irrelevant_le_map _ _ _ (hp.irrelevant_le_map_ofPoly U)

public theorem projIso_hom (U : S.AffineZariskiSite) :
    (hp.projIso U).hom =
      mapHomOfTop (polyGrading ↥Γ(S, U.toOpens) n) (𝒜.grading U) (hp.ofPoly U)
        (hp.mapDomain_ofPoly_eq_top U) :=
  rfl

/-! ### Compatibility with the transition morphisms -/

/-- **The generic form of the compatibility of the morphisms to the integral model.** The
inclusion of affine opens is a plain variable, so that the statement is type-correct at every
transparency; see the implementation notes of
`StacksDraft.AlgebraicGeometry.F3.ProjBundleProjectiveSpace.IntegralCharts`. -/
public theorem toIntegral_transition_of {U V : S.AffineZariskiSite} (h : U.toOpens ≤ V.toOpens)
    (hdom : mapDomain (𝒜.grading V) (𝒜.grading U) (𝒜.res h) = ⊤)
    (hi : irrelevant (𝒜.grading U) ≤ (irrelevant (𝒜.grading V)).map (𝒜.res h)) :
    𝒜.transition h hdom ≫ hp.toIntegral V = hp.toIntegral U := by
  have hres : (𝒜.res h).comp (hp.ofPoly V) =
      (hp.ofPoly U).comp (coeffGradedHom ↥Γ(S, V.toOpens) n (resHom h)) :=
    GradedRingHom.ext fun p => hp.res_ofPoly h p
  have hdc : mapDomain (polyGrading ↥Γ(S, V.toOpens) n) (𝒜.grading U)
      ((𝒜.res h).comp (hp.ofPoly V)) = ⊤ :=
    mapDomain_eq_top_of_irrelevant_le_map _ _ _
      (irrelevant_le_map_comp (hp.irrelevant_le_map_ofPoly V) hi)
  have hdc' : mapDomain (polyGrading ↥Γ(S, V.toOpens) n) (𝒜.grading U)
      ((hp.ofPoly U).comp (coeffGradedHom ↥Γ(S, V.toOpens) n (resHom h))) = ⊤ :=
    hres ▸ hdc
  have key : 𝒜.transition h hdom ≫ (hp.projIso V).hom =
      (hp.projIso U).hom ≫ coeffMap n (resHom h) := by
    rw [projIso_hom, projIso_hom, coeffMap]
    refine Eq.trans ?_ (mapHomOfTop_comp (polyGrading ↥Γ(S, V.toOpens) n)
      (polyGrading ↥Γ(S, U.toOpens) n) (𝒜.grading U)
      (coeffGradedHom ↥Γ(S, V.toOpens) n (resHom h)) (hp.ofPoly U)
      (irrelevant_le_map_coeffGradedHom ↥Γ(S, V.toOpens) n (resHom h))
      (hp.irrelevant_le_map_ofPoly U) (mapDomain_coeffGradedHom_eq_top _ n (resHom h))
      (hp.mapDomain_ofPoly_eq_top U) hdc')
    refine Eq.trans ?_ (mapHomOfTop_congr _ _ hres hdc hdc')
    exact (mapHomOfTop_comp (polyGrading ↥Γ(S, V.toOpens) n) (𝒜.grading V) (𝒜.grading U)
      (hp.ofPoly V) (𝒜.res h) (hp.irrelevant_le_map_ofPoly V) hi
      (hp.mapDomain_ofPoly_eq_top V) hdom hdc).symm
  calc 𝒜.transition h hdom ≫ hp.toIntegral V
      = (𝒜.transition h hdom ≫ (hp.projIso V).hom) ≫
          polyToIntegral ↥Γ(S, V.toOpens) n := by rw [toIntegral, Category.assoc]
    _ = (hp.projIso U).hom ≫ coeffMap n (resHom h) ≫
          polyToIntegral ↥Γ(S, V.toOpens) n := by rw [key, Category.assoc]
    _ = hp.toIntegral U := by rw [coeffMap_polyToIntegral, toIntegral]

/-- The morphisms to the integral model are compatible with the transition morphisms of the
chart functor. -/
public theorem toIntegral_transition {U V : S.AffineZariskiSite} (φ : U ⟶ V) :
    (chartFunctor 𝒜).map φ ≫ hp.toIntegral V = hp.toIntegral U :=
  hp.toIntegral_transition_of (Scheme.AffineZariskiSite.toOpens_mono φ.le)
    (mapDomain_res_eq_top_of_le 𝒜 φ.le _) (irrelevant_le_map_res_of_le 𝒜 φ.le _)

/-- **The chart data of a projective space, in the form of
`Stacks.AlgebraicGeometry.RelativeProjIsProjectiveSpace.IntegralCharts`.** -/
public def toIntegralCharts : IntegralCharts 𝒜 n where
  toIntegral := hp.toIntegral
  toIntegral_transition φ := hp.toIntegral_transition φ

/-! ### The charts are isomorphisms -/

/-- **The identification respects the degree-zero parts.** On the degree-zero part of the
polynomial grading, which is the coefficient ring, the identification is the structure
morphism of `𝒜`. -/
public theorem zeroHom_ofPoly_comp (U : S.AffineZariskiSite) :
    (zeroHom (polyGrading ↥Γ(S, U.toOpens) n) (𝒜.grading U) (hp.ofPoly U)).comp
        ((GradedRing.projZeroRingHom' (polyGrading ↥Γ(S, U.toOpens) n)).comp
          (algebraMap ↥Γ(S, U.toOpens)
            (MvPolynomial (Fin (n + 1)) ↥Γ(S, U.toOpens)))) =
      (GradedRing.projZeroRingHom' (𝒜.grading U)).comp (𝒜.str U).hom := by
  refine RingHom.ext fun r => Subtype.ext ?_
  have hC : (algebraMap ↥Γ(S, U.toOpens) (MvPolynomial (Fin (n + 1)) ↥Γ(S, U.toOpens))) r =
      MvPolynomial.C r := by simp [MvPolynomial.algebraMap_eq]
  have hmem : (MvPolynomial.C r : MvPolynomial (Fin (n + 1)) ↥Γ(S, U.toOpens)) ∈
      polyGrading ↥Γ(S, U.toOpens) n 0 :=
    (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_C _ _)
  rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, coe_zeroHom_apply, hC,
    projZeroRingHom'_coe_of_mem _ hmem, projZeroRingHom'_coe_of_mem _ (𝒜.str_mem U r)]
  exact hp.ofPoly_C U r

/-- **The identification is a morphism over the affine open.** It carries the structure morphism
of the polynomial model to the structure morphism of the chart. -/
public theorem projIso_projToSpecCoeff (U : S.AffineZariskiSite) :
    (hp.projIso U).hom ≫ projToSpecCoeff ↥Γ(S, U.toOpens) n =
      Proj.toSpecZero (𝒜.grading U) ≫ Spec.map (𝒜.strZero U) := by
  rw [projToSpecCoeff, projIso_hom, ← Category.assoc,
    mapHomOfTop_toSpecZero (polyGrading ↥Γ(S, U.toOpens) n) (𝒜.grading U) (hp.ofPoly U)
      (hp.mapDomain_ofPoly_eq_top U),
    Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hp.zeroHom_ofPoly_comp U,
    GradedAlgebra.strZero]

/-- **The induced morphism to `ℙⁿ_U` is the comparison of the two models of projective space,
read through the identification of the chart with the polynomial model.** -/
public theorem chart_eq (U : S.AffineZariskiSite) :
    hp.toIntegralCharts.chart U =
      (hp.projIso U).hom ≫ projCompare ↥Γ(S, U.toOpens) n ≫
        Stacks.FiniteMorphismProjective.baseTransport n U.2.isoSpec.symm := by
  refine pullback.hom_ext ?_ ?_
  · rw [IntegralCharts.chart_fst]
    simp only [Category.assoc, Stacks.FiniteMorphismProjective.baseTransport_fst, Iso.symm_hom]
    rw [reassoc_of% projCompare_fst, reassoc_of% hp.projIso_projToSpecCoeff U,
      GradedAlgebra.toOpen]
  · rw [IntegralCharts.chart_snd]
    simp only [Category.assoc, Stacks.FiniteMorphismProjective.baseTransport_snd]
    rw [projCompare_snd]
    rfl

/-- **Each chart is an isomorphism onto the relative projective space over its affine open.** It
is the identification with the polynomial model, the comparison of the polynomial and
base-change models of projective space
(`Stacks.AlgebraicGeometry.ProjBaseChange.isIso_projCompare`) and the comparison of projective
spaces over isomorphic bases, all three of which are isomorphisms. -/
public instance isIso_chart (U : S.AffineZariskiSite) : IsIso (hp.toIntegralCharts.chart U) := by
  rw [hp.chart_eq U]
  infer_instance

/-! ### The conclusion -/

include hp in
/-- **`Proj_S(𝒜) ≅ ℙⁿ_S` over `S`**, for a graded algebra whose section rings over the affine
opens of the base are polynomial rings in `n + 1` variables, compatibly. -/
public theorem exists_schemeIso :
    ∃ e : relativeProj 𝒜 ≅ projectiveSpaceOver n S,
      e.hom ≫ pullback.fst (terminal.from S)
        (terminal.from (projectiveSpaceAtUniverse.{u} n)) = relativeProjToBase 𝒜 :=
  IntegralCharts.exists_schemeIso hp.toIntegralCharts fun U => hp.isIso_chart U

/-- **The chart data of a projective space**, from an identification of the section rings with
polynomial rings. This is the input
`Stacks.AlgebraicGeometry.RelativeProjIsProjectiveSpace.exists_iso_relativeProj` consumes. -/
public def toProjectiveSpaceCharts : ProjectiveSpaceCharts 𝒜 n :=
  hp.toIntegralCharts.toProjectiveSpaceCharts fun U => hp.isIso_chart U

end PolynomialSections

/-- **`Proj_S(A) ≅ ℙⁿ_S` over `S` in the assembled form.** For a sheaf-level graded algebra whose
section rings over the affine opens of the base are polynomial rings in `n + 1` variables,
compatibly, the relative homogeneous spectrum built by
`Stacks.AlgebraicGeometry.RelativeProj.relativeProj` is `ℙⁿ_S` over `S`.

This is the form `Stacks.Tag087SBundle.projectiveBundle` is built at, so it is the shape part (1)
of Stacks Tag 087S consumes. -/
public theorem exists_iso_relativeProj (A : RelativeProjBridge.SheafGradedAlgebra S) (n : ℕ)
    (hp : PolynomialSections A.toGradedAlgebra n) :
    ∃ e : (RelativeProj.relativeProj A).scheme ≅ projectiveSpaceOver n S,
      e.hom ≫ pullback.fst (terminal.from S)
        (terminal.from (projectiveSpaceAtUniverse.{u} n)) =
        (RelativeProj.relativeProj A).toBase :=
  RelativeProjIsProjectiveSpace.exists_iso_relativeProj A n hp.toProjectiveSpaceCharts

end Stacks.AlgebraicGeometry.ProjPolynomialSections

end
