module

public import StacksFrontier.AlgebraicGeometry.RelativeProjTwists.Statement

/-!
# The chart comparison of a twist datum, on an arbitrary open of the chart

Tag 01NR's twist datum carries, over every affine open `U` of the base and in every integer
degree, an identification of the restriction of the glued twist to the projective-spectrum chart
with the absolute twisting sheaf there. `RelativeProjTwists.ChartData.mapSection` reads that
identification on sections: it carries a section of `𝒪_{Proj Γ(U, 𝒜)}(n)` over an open `V` of
the chart to a section of the twist over the image of `V`.

The library states `mapSection` and uses it only at `V = ⊤`, which is the open the field
`RelativeProjTwists.TwistData.ψ_chart` quantifies over. This file supplies the three structural
properties it has at a general `V`, which is what a *local* argument on the relative projective
spectrum needs: it is surjective, it commutes with restriction, and it is semilinear for the
chart's isomorphism on functions.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjDegreeOne.mapSection_surjective`: on every open of the
  chart the comparison is surjective; the preimage is written down, so no abstract
  bijectivity-of-an-iso-component lemma is needed.
* `Stacks.AlgebraicGeometry.RelativeProjDegreeOne.mapSection_res`: it commutes with restriction
  along `V₂ ≤ V₁`, the two restrictions being taken along `V₂ ≤ V₁` on the chart and along the
  image inclusion on the relative projective spectrum.
* `Stacks.AlgebraicGeometry.RelativeProjDegreeOne.mapSection_smul`: it carries the action of
  `Γ(Proj Γ(U, 𝒜), V)` to the action of `Γ(Proj_S 𝒜, chart ''ᵁ V)` through
  `AlgebraicGeometry.Scheme.Hom.appIso` of the chart.

## Implementation notes

**Both halves of `mapSection` are components of isomorphisms, and only one of them is
interesting.** `AlgebraicGeometry.Scheme.Modules.restrictAppIso` is `Iso.refl` at this pin — the
sections of a restriction along an open immersion over `V` *are* the sections over the image —
so `mapSection_res` is the naturality of the chart identification and nothing else, and
`mapSection_smul` is its linearity followed by Mathlib's `smul_restrictAppIso_hom_apply`, which
is where the chart's ring isomorphism enters.

**The scalar actions are written through `AlgebraicGeometry.Scheme.Modules.smul` rather than
`•`.** `algebra.piece n` has type `SheafOfModules (RingedSite.ofScheme _).ringSheaf`, which is
the scheme's category of modules only up to an unfolding that instance search does not perform,
so `r • x` reports a missing `HSMul` instead of the spelling mismatch; `smul` applied as a
morphism takes the module as an explicit argument, where a `show` fixes the spelling. This is
the same discipline as
`Stacks.AlgebraicGeometry.GluedTwistSectionMap.gluedMapSection_degreeSection_smul`.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.ProjTwistSections

namespace Stacks.AlgebraicGeometry.RelativeProjDegreeOne

universe u

/-- Applying the two components of an isomorphism of sheaves of modules on a scheme in turn
over one open is the identity. -/
public theorem iso_inv_hom_app {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R} (e : M ≅ N)
    (W : Cᵒᵖ) (x : (M.val.obj W : Type u)) :
    (e.inv.val.app W) ((e.hom.val.app W) x) = x :=
  congrArg (fun φ : M ⟶ M => (φ.val.app W) x) e.hom_inv_id

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S}
  {algebra : RelativeProjTwists.SchemeGradedAlgebra (relativeProj A).scheme}
  (C : RelativeProjTwists.ChartData A algebra)
  (U : S.Opens) (hU : IsAffineOpen U) (n : ℤ)

/-- Surjectivity of the chart comparison on an arbitrary open of the chart. -/
public theorem mapSection_surjective
    (V : (AlgebraicGeometry.Proj (A.grading U)).Opens) :
    letI := C.chart_isOpenImmersion U hU
    Function.Surjective (C.mapSection U hU n V) := by
  let := C.chart_isOpenImmersion U hU
  intro t
  refine ⟨(C.chartIso U hU n).hom.val.app (op V)
    ((Scheme.Modules.restrictAppIso ((relativeProj A).chart U hU) (algebra.piece n) V).inv t),
    ?_⟩
  change (Scheme.Modules.restrictAppIso ((relativeProj A).chart U hU) (algebra.piece n) V).hom
      ((C.chartIso U hU n).inv.val.app (op V)
        ((C.chartIso U hU n).hom.val.app (op V) _)) = t
  exact (congrArg _ (iso_inv_hom_app (C.chartIso U hU n) (op V) _)).trans
    (Iso.inv_hom_id_apply _ _)

/-- The chart comparison commutes with restriction to a smaller open of the chart. -/
public theorem mapSection_res {V₁ V₂ : (AlgebraicGeometry.Proj (A.grading U)).Opens}
    (h : V₂ ≤ V₁) (a : (twistingSheaf (A.grading U) n).val.obj (op V₁)) :
    letI := C.chart_isOpenImmersion U hU
    (algebra.piece n).val.map
        (homOfLE (Scheme.Hom.image_mono ((relativeProj A).chart U hU) h)).op
        (C.mapSection U hU n V₁ a) =
      C.mapSection U hU n V₂
        ((twistingSheaf (A.grading U) n).val.map (homOfLE h).op a) := by
  let := C.chart_isOpenImmersion U hU
  exact (PresheafOfModules.naturality_apply (C.chartIso U hU n).inv.val (homOfLE h).op a).symm

/-- The chart comparison is semilinear for the chart's isomorphism on functions. -/
public theorem mapSection_smul (V : (AlgebraicGeometry.Proj (A.grading U)).Opens)
    (r : Γ(AlgebraicGeometry.Proj (A.grading U), V))
    (a : (twistingSheaf (A.grading U) n).val.obj (op V)) :
    letI := C.chart_isOpenImmersion U hU
    C.mapSection U hU n V
        (((show (AlgebraicGeometry.Proj (A.grading U)).Modules from
            twistingSheaf (A.grading U) n).smul r).asHom.hom a) =
      ((show (relativeProj A).scheme.Modules from algebra.piece n).smul
          ((((relativeProj A).chart U hU).appIso V).inv r)).asHom.hom
        (C.mapSection U hU n V a) := by
  let := C.chart_isOpenImmersion U hU
  exact (congrArg _ (((C.chartIso U hU n).inv.val.app (op V)).hom.map_smul r a)).trans
    (Scheme.Modules.smul_restrictAppIso_hom_apply _ _ _ _ _)

end Stacks.AlgebraicGeometry.RelativeProjDegreeOne

end
