module

public import StacksFrontier.AlgebraicGeometry.ProjF1DegreeOneChart.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Assembled

/-!
# Mapping into the chart of a relative `Proj`, over an affine open, on the sheaf-level substrate

Let `A` be a sheaf-level graded `𝒪_S`-algebra
(`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`) and let `U ⊆ S` be an affine
open. The chart of `Proj_S(A)` over `U` is `Proj (A.grading U)`, the projective spectrum of the
graded ring `⨁ₙ Γ(Aₙ, U)` of homogeneous sections over `U`, and its structure morphism to `U` is
`Stacks.AlgebraicGeometry.RelativeProj.projInclusionToOpen`.

This file computes the composite of `AlgebraicGeometry.Proj.fromOfGlobalSections` with that
structure morphism: a ring map `ψ : ⨁ₙ Γ(Aₙ, U) ⟶ Γ(W, ⊤)` which agrees in degree zero with a
given `w : W ⟶ U` classifies a morphism into the chart **over `U`**, not merely into the chart.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProj.fromOfGlobalSections_comp_projInclusionToOpen`: the
  composite is `w` itself.
* `Stacks.AlgebraicGeometry.RelativeProj.fromOfIsUnit_comp_projInclusionToOpen`: the same for
  the morphism built by inverting one positive-degree homogeneous section, which is the shape a
  dehomogenized invertible quotient takes.
* `Stacks.AlgebraicGeometry.RelativeProj.chartHomEquivOver`: **morphisms into `Proj_S(A)` over an
  affine open `U` of the base are exactly the morphisms into the chart over `U`**, and
  `chartHomEquivOver_apply_coe` and `chartHomEquivOver_symm_apply_comp_chart` say that the
  bijection is "compose with the chart" in both directions. This is what carries *uniqueness* of
  a morphism into the chart — which, through
  `Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.eq_of_chartHomEquiv_eq`, is Tag 01NA's
  uniqueness — into a statement about morphisms into the relative `Proj`; without it, local
  morphisms into `Proj_S(A)` cannot be shown to agree on overlaps and so cannot be glued.

## Implementation notes

This is the sheaf-level counterpart of
`Stacks.RelativeProj.Situation.fromOfGlobalSections_comp_projInclusionToOpen` and of
`Stacks.RelativeProj.Situation.exists_hom_projInclusionToOpen`, which prove the same thing for
the other substrate for a relative `Proj` in this repository, the `Situation` of Tag 01NN. The
two substrates have different carriers for the graded ring of sections — there the ring comes
with a named degree-zero map `sectionRingZeroMap`, here the degree-zero map is
`GradedRing.projZeroRingHom'` composed with `SheafGradedAlgebra.strHom` — but the proof is the
same four steps and uses no property of either substrate: `projInclusionToOpen` is
`AlgebraicGeometry.Proj.toSpecZero` followed by `Spec` of the degree-zero map and the affine
identification of `U`, `AlgebraicGeometry.Proj.fromOfGlobalSections_toSpecZero` computes the
first leg, and what remains is `AlgebraicGeometry.Scheme.toSpecΓ_naturality` together with
`AlgebraicGeometry.IsAffineOpen.toSpecΓ_isoSpec_inv`.

The statement is duplicated rather than deduced from the `Situation` version because passing
between the substrates is the ring comparison
`Stacks.AlgebraicGeometry.projectiveBundlePresentationsAgree`, which is far more expensive than
the four lines below and is exactly what a consumer working on the sheaf-level substrate is
avoiding.

Why the sheaf-level substrate needs this at all: its only statement of this kind was
`Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.toRelativeProjOfIsUnit_comp_toBase`, which
computes the composite with the structure morphism of `Proj_S(A)` as
`fromOfIsUnit … ≫ projInclusionToOpen A U hU ≫ U.ι` and so stops one step short of saying that
the morphism lies over a *given* `w : W ⟶ U`. That last step is what the bijection of Tag 0B3V
needs in order to produce a *section* of `𝐏(ℰ) ⟶ X`.

The degree-zero hypothesis is stated as an equality of ring maps `Γ(S, U) ⟶ Γ(W, ⊤)` rather than
of scheme morphisms, because that is the form the `Spec`–global-sections adjunction consumes; see
the same choice in `StacksFrontier/AlgebraicGeometry/RelativeProj/MappingIn.lean`.

No `@[stacks]` attribute is attached. Section 01NS asserts that `Proj_S(A)` represents the
functor of quadruples `(d, f, L, ψ)` up to strict equivalence; what is computed here is a single
composite of named morphisms, which is neither that statement nor a covering part of it.

## References

* [Stacks Project, Tag 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge

namespace Stacks.AlgebraicGeometry.RelativeProj

universe u

variable {S : Scheme.{u}} (A : SheafGradedAlgebra.{u} S) {U : S.Opens} (hU : IsAffineOpen U)
  {W : Scheme.{u}}

/-- The degree-zero map of the chart over `U`, followed by a ring map out of the section ring,
is the ring map of a morphism `W ⟶ U` as soon as the two agree on the image of `Γ(S, U)`. This
is the one computation the composite below needs, isolated because the degree-zero map of the
sheaf-level substrate is a composition with `GradedRing.projZeroRingHom'` rather than a named
morphism. -/
public theorem projZeroRingHom'_strHom_comp_ofHom (w : W ⟶ U.toScheme)
    (ψ : A.sectionRing U →+* Γ(W, ⊤))
    (hψ0 : ∀ x : Γ(S, U), ψ (A.strHom U x) = (U.topIso.inv ≫ w.appTop).hom x) :
    CommRingCat.ofHom ((GradedRing.projZeroRingHom' (A.grading U)).comp (A.strHom U)) ≫
        CommRingCat.ofHom
          (ψ.comp (algebraMap (↥(A.grading U 0)) (A.sectionRing U))) =
      U.topIso.inv ≫ w.appTop := by
  ext x
  have hcoe : ((GradedRing.projZeroRingHom' (A.grading U) (A.strHom U x) :
      ↥(A.grading U 0)) : A.sectionRing U) = A.strHom U x :=
    congrArg Subtype.val
      (GradedRing.projZeroRingHom'_apply_coe _ ⟨_, A.strHom_mem U x⟩)
  show ψ ((GradedRing.projZeroRingHom' (A.grading U) (A.strHom U x) :
    ↥(A.grading U 0)) : A.sectionRing U) = _
  rw [hcoe]
  exact hψ0 x

/-- **A morphism into the chart of a relative `Proj` built from global sections lies over a given
morphism to the affine open.** A ring map `ψ` from the graded ring of homogeneous sections of `A`
over an affine open `U` to the global sections of `W`, whose image of the irrelevant ideal is the
unit ideal, classifies a morphism `W ⟶ Proj (A.grading U)`; if moreover `ψ` agrees in degree zero
with the ring map of `w : W ⟶ U`, then that morphism composed with the chart's structure morphism
is `w`.

This is the sheaf-level counterpart of
`Stacks.RelativeProj.Situation.fromOfGlobalSections_comp_projInclusionToOpen`. -/
public theorem fromOfGlobalSections_comp_projInclusionToOpen (w : W ⟶ U.toScheme)
    (ψ : A.sectionRing U →+* Γ(W, ⊤))
    (hψtop : (HomogeneousIdeal.irrelevant (A.grading U)).toIdeal.map ψ = ⊤)
    (hψ0 : ∀ x : Γ(S, U), ψ (A.strHom U x) = (U.topIso.inv ≫ w.appTop).hom x) :
    AlgebraicGeometry.Proj.fromOfGlobalSections (A.grading U) ψ hψtop ≫
        projInclusionToOpen A U hU = w := by
  have hdef : projInclusionToOpen A U hU =
      AlgebraicGeometry.Proj.toSpecZero (A.grading U) ≫
        Spec.map (CommRingCat.ofHom
          ((GradedRing.projZeroRingHom' (A.grading U)).comp (A.strHom U))) ≫
            hU.isoSpec.inv := rfl
  rw [hdef, ← Category.assoc, AlgebraicGeometry.Proj.fromOfGlobalSections_toSpecZero,
    Category.assoc, ← Spec.map_comp_assoc,
    projZeroRingHom'_strHom_comp_ofHom A w ψ hψ0, Spec.map_comp_assoc, ← Category.assoc,
    ← Scheme.toSpecΓ_naturality, Category.assoc]
  have h2 : (U.toScheme).toSpecΓ ≫ Spec.map U.topIso.inv ≫ hU.isoSpec.inv = 𝟙 _ := by
    rw [← Category.assoc]
    exact hU.toSpecΓ_isoSpec_inv
  rw [h2, Category.comp_id]

/-- **The morphism into the chart obtained by inverting one positive-degree homogeneous section
lies over a given morphism to the affine open.** This is the shape in which an invertible
quotient of a quasi-coherent module presents itself after dehomogenization at a trivializing
section: a plain ring map to global sections, one positive-degree section of which becomes a
unit. -/
public theorem fromOfIsUnit_comp_projInclusionToOpen (w : W ⟶ U.toScheme)
    (φ : A.sectionRing U →+* Γ(W, ⊤)) {d : ℕ} {r : A.sectionRing U} (hd : 0 < d)
    (hr : r ∈ A.grading U d) (hu : IsUnit (φ r))
    (hφ0 : ∀ x : Γ(S, U), φ (A.strHom U x) = (U.topIso.inv ≫ w.appTop).hom x) :
    ProjF1DegreeOneChart.fromOfIsUnit (A.grading U) φ hd hr hu ≫
        projInclusionToOpen A U hU = w :=
  fromOfGlobalSections_comp_projInclusionToOpen A hU w φ
    (ProjF1DegreeOneChart.map_irrelevant_eq_top_of_isUnit _ φ hd hr hu) hφ0

/-! ### Morphisms over an affine open of the base are morphisms into the chart -/

/-- **Morphisms into the relative `Proj` lying over an affine open `U` of the base are exactly
the morphisms into the chart over `U`.** This is the cartesian square
`Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData.chart_isPullback` read as a bijection;
the forward map is composition with the chart.

The sheaf-level counterpart of `Stacks.RelativeProj.Situation.chartHomEquivOver`. Nothing beyond
the square is used, so no quasi-coherence, no degree-one generation and no affineness of `W`
appears. -/
public def chartHomEquivOver (D : RelativeProjData A) (w : W ⟶ U.toScheme) :
    { h : W ⟶ AlgebraicGeometry.Proj (A.grading U) //
        h ≫ projInclusionToOpen A U hU = w } ≃
      { g : W ⟶ D.scheme // g ≫ D.toBase = w ≫ U.ι } where
  toFun h := ⟨h.1 ≫ D.chart U hU, by
    rw [Category.assoc, (D.chart_isPullback U hU).w, ← Category.assoc, h.2]⟩
  invFun g := ⟨(D.chart_isPullback U hU).lift g.1 w g.2,
    (D.chart_isPullback U hU).lift_snd g.1 w g.2⟩
  left_inv h := by
    refine Subtype.ext ((D.chart_isPullback U hU).hom_ext ?_ ?_)
    · exact (D.chart_isPullback U hU).lift_fst _ _ _
    · rw [(D.chart_isPullback U hU).lift_snd, h.2]
  right_inv g := Subtype.ext ((D.chart_isPullback U hU).lift_fst g.1 w g.2)

/-- The morphism underlying the image of `h` under `chartHomEquivOver` is the composite of `h`
with the chart over `U`. -/
@[simp]
public theorem chartHomEquivOver_apply_coe (D : RelativeProjData A) (w : W ⟶ U.toScheme)
    (h : { h : W ⟶ AlgebraicGeometry.Proj (A.grading U) //
      h ≫ projInclusionToOpen A U hU = w }) :
    (chartHomEquivOver A hU D w h).1 = h.1 ≫ D.chart U hU :=
  rfl

/-- The inverse of the bijection is inverse to composition with the chart. So a consumer that
knows a morphism into the chart knows the morphism into the relative `Proj` on the nose, and
conversely two morphisms into the relative `Proj` over `U` are equal as soon as the morphisms
into the chart they come from are. -/
@[simp]
public theorem chartHomEquivOver_symm_apply_comp_chart (D : RelativeProjData A)
    (w : W ⟶ U.toScheme) (g : { g : W ⟶ D.scheme // g ≫ D.toBase = w ≫ U.ι }) :
    ((chartHomEquivOver A hU D w).symm g).1 ≫ D.chart U hU = g.1 :=
  (D.chart_isPullback U hU).lift_fst g.1 w g.2

/-- **Two morphisms into the relative `Proj` over the same morphism to an affine open of the base
are equal as soon as the morphisms into the chart they are composed from are equal.** This is the
injectivity the bijection carries, in the form a gluing argument uses it. -/
public theorem comp_chart_injective (D : RelativeProjData A) (w : W ⟶ U.toScheme)
    {h h' : W ⟶ AlgebraicGeometry.Proj (A.grading U)}
    (hh : h ≫ projInclusionToOpen A U hU = w) (hh' : h' ≫ projInclusionToOpen A U hU = w)
    (hcomp : h ≫ D.chart U hU = h' ≫ D.chart U hU) :
    h = h' :=
  congrArg Subtype.val
    ((chartHomEquivOver A hU D w).injective (Subtype.ext hcomp :
      chartHomEquivOver A hU D w ⟨h, hh⟩ = chartHomEquivOver A hU D w ⟨h', hh'⟩))

end Stacks.AlgebraicGeometry.RelativeProj

end
