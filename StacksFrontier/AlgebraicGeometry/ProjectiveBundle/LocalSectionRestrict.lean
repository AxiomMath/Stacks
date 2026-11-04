module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocalSectionCanonical
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceSections.GradedNaturality

/-!
# Restricting the local section of a projective bundle to a smaller affine open

`Stacks.RelativeProj.localSection` is a named morphism `V ⟶ 𝐏(F)` over an affine open `V` of the
base, built from an invertible quotient `q : F ⟶ L` trivialized on `V`, and
`Stacks.RelativeProj.localSection_congr` shows it is a function of `(V, q)` alone. **This file
reduces the remaining step of the gluing — that it is also compatible with shrinking `V` — to a
single equation of ring homomorphisms.**

## What the reduction is

Both `localChartMap V q e hq` and `localChartMap W q e' hq'` are
`AlgebraicGeometry.Proj.fromOfGlobalSections` of a dehomogenization, so the comparison of the two
is the comparison of the two ring maps, through two naturalities of that construction that are
already available:

* `AlgebraicGeometry.Proj.comp_fromOfGlobalSections` moves the inclusion `W ⟶ V` of the source
  into the ring map, as `(W ⟶ V)^♯ ∘ ψ_V`;
* `AlgebraicGeometry.Proj.fromOfGlobalSections_comp_map` moves the transition morphism
  `Proj Γ(W, Sym F) ⟶ Proj Γ(V, Sym F)` of [Stacks, Tag 01NO] into the ring map, as `ψ_W ∘ res`,
  the transition being Mathlib's `AlgebraicGeometry.Proj.map` of the restriction of homogeneous
  sections by
  `Stacks.AlgebraicGeometry.RelativeProjGeneral.transition_eq_map_of_le_opens`.

So the two sides are `fromOfGlobalSections` of `(W ⟶ V)^♯ ∘ ψ_V` and of `ψ_W ∘ res`, and
`AlgebraicGeometry.Proj.fromOfGlobalSections_congr` closes the comparison from the equality of
those two ring maps. That equality is the hypothesis `hres` below: a statement about
`Stacks.SymmetricDehomogenize.dehomogenize` and
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.resRingHom` with no `Proj` in it.

It is **discharged** in `StacksFrontier/AlgebraicGeometry/ProjectiveBundle/LocalSectionShrink.lean`,
by `Stacks.RelativeProj.localDehomogenize_res`, from one equation of morphisms of sheaves of
modules on `X` — that restriction of functions along `X.homOfLE hWV` carries the trivialized
quotient over `V` to the one over `W`. So the hypothesis below is kept, and the two results of
this file are the general form; the specialization that needs only the sheaf-level equation is
`Stacks.RelativeProj.homOfLE_comp_localSection_of_trivializedQuotientHom_res` there.

The irrelevant-ideal hypotheses of the two naturalities are not extra assumptions: the image of
an ideal under a composite is the image of its image (`Ideal.map_map`), and the image of the unit
ideal under a ring map is the unit ideal (`Ideal.map_top`), so both follow from
`Stacks.RelativeProj.map_irrelevant_localDehomogenize_eq_top` over `V` alone.

## Main results

* `Stacks.RelativeProj.localChartMap_comp_projInclusionMap`: the morphism into the chart over `V`,
  precomposed with the inclusion of `W`, is the morphism into the chart over `W` followed by the
  transition — given the ring equation.
* `Stacks.RelativeProj.homOfLE_comp_localSection`: **the local section of `π : 𝐏(F) ⟶ X` over `V`,
  restricted to `W`, is the local section over `W`** — given the ring equation. The trivialization
  over `W` in the conclusion is arbitrary, by `Stacks.RelativeProj.localSection_congr`.

## Implementation notes

The ring equation is stated with
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.resRingHom` rather than with the
graded homomorphism `…SheafGradedAlgebra.res`, because `resRingHom` is the form
`…SheafGradedAlgebra.resRingHom_ext` reduces to the homogeneous summands, which is how the
equation is to be checked; the two are the same term by `…SheafGradedAlgebra.res_toRingHom`.

Proof irrelevance does the bookkeeping twice: once because `AlgebraicGeometry.Proj.map` carries
its generation hypothesis as a `Prop` argument, so the hypothesis
`Stacks.AlgebraicGeometry.RelativeProjGeneral.transition_eq_map_of_le_opens` produces and the one
assembled here are interchangeable, and once because
`AlgebraicGeometry.Proj.fromOfGlobalSections_congr` has to carry the irrelevant-ideal hypothesis
across a change of ring map.

No `@[stacks]` attribute is attached. Tag 0B3V is the bijection between the sections of `π` and
the invertible quotients of `F`; the compatibility of a local construction with shrinking the open
it is built over is not a covering part of it.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NS](https://stacks.math.columbia.edu/tag/01NS)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
open Stacks.AlgebraicGeometry.ProjF1Dehomogenization
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.SymGraded

universe u

namespace Stacks.RelativeProj

variable {X : Scheme.{u}} {F L : X.Modules} [F.IsQuasicoherent] (W V : X.Opens) (q : F ⟶ L)
  (e : L.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V))
  (e' : L.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W))

/-- **The morphism into the chart of `𝐏(F)` over `V` is compatible with shrinking `V` to `W`**,
given that the two dehomogenizations are compatible with restriction of homogeneous sections. Both
sides are `AlgebraicGeometry.Proj.fromOfGlobalSections` of the two composites the hypothesis
equates. -/
public theorem localChartMap_comp_projInclusionMap (hWV : W ≤ V)
    (hW : IsAffineOpen W) (hV : IsAffineOpen V)
    (hq : Function.Surjective (q.val.app (op V)))
    (hq' : Function.Surjective (q.val.app (op W)))
    (hres : (X.homOfLE hWV).appTop.hom.comp (localDehomogenize V q e) =
      (localDehomogenize W q e').comp
        ((schemeSheafGradedAlgebra F
          (isQuasicoherentPieces_of_isQuasicoherent F)).resRingHom hWV)) :
    X.homOfLE hWV ≫ localChartMap V q e hq =
      localChartMap W q e' hq' ≫ projInclusionMap
        (schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F))
        W V hWV hW hV := by
  have hirr : HomogeneousIdeal.irrelevant ((schemeSheafGradedAlgebra F
        (isQuasicoherentPieces_of_isQuasicoherent F)).grading W) ≤
      (HomogeneousIdeal.irrelevant ((schemeSheafGradedAlgebra F
        (isQuasicoherentPieces_of_isQuasicoherent F)).grading V)).map
        ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).res hWV) :=
    Stacks.AlgebraicGeometry.RelativeProjGeneral.irrelevant_le_map_res_of_le_opens
      (schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).toGradedAlgebra
      (U := ⟨W, hW⟩) (V := ⟨V, hV⟩) hWV
  have hmap : projInclusionMap (schemeSheafGradedAlgebra F
        (isQuasicoherentPieces_of_isQuasicoherent F)) W V hWV hW hV =
      AlgebraicGeometry.Proj.map ((schemeSheafGradedAlgebra F
        (isQuasicoherentPieces_of_isQuasicoherent F)).res hWV) hirr :=
    Stacks.AlgebraicGeometry.RelativeProjGeneral.transition_eq_map_of_le_opens
      (schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).toGradedAlgebra
      (U := ⟨W, hW⟩) (V := ⟨V, hV⟩) hWV _
  have hcomp : (HomogeneousIdeal.irrelevant ((schemeSheafGradedAlgebra F
        (isQuasicoherentPieces_of_isQuasicoherent F)).grading V)).toIdeal.map
      ((X.homOfLE hWV).appTop.hom.comp (localDehomogenize V q e)) = ⊤ := by
    rw [← Ideal.map_map, map_irrelevant_localDehomogenize_eq_top V q e hq, Ideal.map_top]
  have hcomp' : (HomogeneousIdeal.irrelevant ((schemeSheafGradedAlgebra F
        (isQuasicoherentPieces_of_isQuasicoherent F)).grading V)).toIdeal.map
      ((localDehomogenize W q e').comp
        ((schemeSheafGradedAlgebra F
          (isQuasicoherentPieces_of_isQuasicoherent F)).resRingHom hWV)) = ⊤ := by
    rw [← hres]; exact hcomp
  rw [localChartMap, localChartMap, hmap,
    AlgebraicGeometry.Proj.comp_fromOfGlobalSections _ (X.homOfLE hWV)
      (localDehomogenize V q e) (map_irrelevant_localDehomogenize_eq_top V q e hq) hcomp,
    AlgebraicGeometry.Proj.fromOfGlobalSections_comp_map
      ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).res hWV) hirr
      (localDehomogenize W q e') (map_irrelevant_localDehomogenize_eq_top W q e' hq') hcomp']
  exact AlgebraicGeometry.Proj.fromOfGlobalSections_congr hres _ _

/-- **The local section of `π : 𝐏(F) ⟶ X` over `V`, restricted to an affine open `W ⊆ V`, is the
local section over `W`** — given that the two dehomogenizations are compatible with restriction of
homogeneous sections for *some* trivialization over `W`. The trivialization in the conclusion is
arbitrary, by `Stacks.RelativeProj.localSection_congr`.

This is the agreement on overlaps that a gluing argument consumes: applied to an affine open `W`
of the intersection of two members of a cover it compares the two local sections there. -/
public theorem homOfLE_comp_localSection (hWV : W ≤ V)
    (hW : IsAffineOpen W) (hV : IsAffineOpen V)
    (hq : Function.Surjective (q.val.app (op V)))
    (hq' : Function.Surjective (q.val.app (op W)))
    (e'' : L.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W))
    (hres : (X.homOfLE hWV).appTop.hom.comp (localDehomogenize V q e) =
      (localDehomogenize W q e'').comp
        ((schemeSheafGradedAlgebra F
          (isQuasicoherentPieces_of_isQuasicoherent F)).resRingHom hWV)) :
    X.homOfLE hWV ≫ localSection V q e hV hq = localSection W q e' hW hq' :=
  calc X.homOfLE hWV ≫ localSection V q e hV hq
      = (X.homOfLE hWV ≫ localChartMap V q e hq) ≫
          (symGradedBundle F).chart V hV ≫ (bundlePresentationIso F).hom := by
        rw [localSection]; simp only [Category.assoc]
    _ = (localChartMap W q e'' hq' ≫ projInclusionMap (schemeSheafGradedAlgebra F
            (isQuasicoherentPieces_of_isQuasicoherent F)) W V hWV hW hV) ≫
          (symGradedBundle F).chart V hV ≫ (bundlePresentationIso F).hom := by
        rw [localChartMap_comp_projInclusionMap W V q e e'' hWV hW hV hq hq' hres]
    _ = localChartMap W q e'' hq' ≫ (projInclusionMap (schemeSheafGradedAlgebra F
            (isQuasicoherentPieces_of_isQuasicoherent F)) W V hWV hW hV ≫
          (symGradedBundle F).chart V hV) ≫ (bundlePresentationIso F).hom := by
        simp only [Category.assoc]
    _ = localSection W q e'' hW hq' := by
        rw [(symGradedBundle F).chart_transition W V hWV hW hV, localSection]
    _ = localSection W q e' hW hq' := localSection_congr W q hW e'' e' hq' hq'

end Stacks.RelativeProj

end
