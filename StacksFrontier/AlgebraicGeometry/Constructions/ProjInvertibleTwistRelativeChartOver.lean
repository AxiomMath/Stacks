module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeChartCanonical
public import StacksFrontier.AlgebraicGeometry.ProjBundleSurjection.Chart
public import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.GradedSectionsCore

/-!
# Tag 02NC over a base scheme: the chart comparison is a morphism over the open of the base

The comparison of Tag 02NC over an open `V` of the base, `Proj ℬ(V) ⟶ Proj 𝒜(V)`, is a morphism
**over `V`**: it commutes with the structure morphisms
`Stacks.AlgebraicGeometry.RelativeProj.projInclusionToOpen` of the two charts.

This is the triangle of the source's diagram, read over one chart of the base, and it is not
implied by the comparison being an isomorphism of homogeneous spectra: the comparison is
`AlgebraicGeometry.Proj.map` of a graded ring homomorphism whose degree-zero part is the canonical
`𝒜_0(V) → 𝒜_0(V) ⊗ 𝒪(V)`, not an identity, so the two structure morphisms have to be compared
through that.

## Main results

* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.psiSectionAt_strHom`: the comparison carries
  the structure map of `𝒜`'s graded ring of sections to the structure map of `ℬ`'s.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.projMap_psiSectionAt_comp_projInclusionToOpen`:
  **the comparison is a morphism over the open of the base.**

## Implementation notes

The route is the one `Stacks.AlgebraicGeometry.ProjBundleSurjection.chartMap_comp_toOpen` takes
for a surjection of graded algebras, with
`Stacks.AlgebraicGeometry.ProjBundleSurjection.strZeroSheaf_comp_zeroHom` replaced by the
analogous statement for the comparison. The comparison crosses from
`AlgebraicGeometry.Proj.map` to `Stacks.AlgebraicGeometry.ProjShared.mapHomOfTop` by
`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.mapHomOfTop_psiSectionAt_eq_projMap`, which is
what makes `Stacks.AlgebraicGeometry.ProjShared.mapHomOfTop_toSpecZero` — Tag 01NO's commuting
square — available.

The identification of the affine open with the spectrum of its functions is kept as a *variable*
`i` inside the proof and instantiated only at the end, exactly as in `chartMap_comp_toOpen`: the
term `hV.isoSpec.inv` makes the goal ill-typed at implicit transparency and every `rw` then fails
with "did not find an occurrence" on a pattern that is present.

## References

* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjBundleSurjection
open Stacks.AlgebraicGeometry.ProjShared
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.GradedAlgebraTwist

universe u

namespace Stacks.AlgebraicGeometry.RelativeInvertibleTwist

attribute [local instance] Stacks.Algebraization.sectionsModuleΓ
  Stacks.Algebraization.sectionsModuleΓSheaf Stacks.Algebraization.sectionsSMulCommClassΓ
  Stacks.Algebraization.sectionsModuleΓPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafVal

variable {S : Scheme.{u}} (L : S.Modules)
  [Stacks.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property L]
  (𝒜 : SheafGradedAlgebra S)

/-- **The chart comparison carries the structure map of `𝒜` to the structure map of `ℬ`.**

The structure map sends a function on the open to its multiple of the unit, the comparison is
`Γ(S, V)`-linear on each homogeneous piece, and it carries the unit to the unit
(`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.psiPieceAt_one`). So the comparison is a
homomorphism of `Γ(S, V)`-algebras, which is what makes the induced morphism of homogeneous
spectra a morphism over the open. -/
theorem psiPieceAt_smul_left (V : S.Opens) (x : (tp L 1).val.obj (op V)) (d : ℕ)
    (r : Γ(S, V)) (a : 𝒜.sectionPieces V d) :
    psiPieceAt L 𝒜 V x d (r • a) = r • psiPieceAt L 𝒜 V x d a := by
  rw [psiPieceAt_apply L 𝒜 V x d (r • a), psiPieceAt_apply L 𝒜 V x d a]
  exact (Stacks.SheafOfModules.tensorSectionsAt_smul_comm S (𝒜.piece (d : ℤ)) (tp L (d : ℤ))
    (op V) r a (powSecAt L (op V) x d)).trans
    (Stacks.TwistActionLinear.tensorSectionsAt_smul_right S.sheaf.obj S.ringCatSheaf.property
      (op V) (𝒜.piece (d : ℤ)) (tp L (d : ℤ)) r a (powSecAt L (op V) x d))

/-- **The chart comparison carries the structure map of `𝒜` to the structure map of `ℬ`.** -/
theorem psiSectionAt_strHom (V : S.Opens) (x : (tp L 1).val.obj (op V)) (r : Γ(S, V)) :
    psiSectionAt L 𝒜 V x (𝒜.strHom V r) = (twist 𝒜 L).strHom V r :=
  (psiSectionAt_of L 𝒜 V x (r • 𝒜.one V)).trans
    (congrArg (DirectSum.of ((twist 𝒜 L).sectionPieces V) 0)
      ((psiPieceAt_smul_left L 𝒜 V x 0 r (𝒜.one V)).trans
        (congrArg (fun z => r • z) (psiPieceAt_one L 𝒜 V x))))

/-- **The degree-zero part of the chart comparison is compatible with the corestricted structure
maps of the two charts.** This is the analogue, for the comparison of Tag 02NC, of
`Stacks.AlgebraicGeometry.ProjBundleSurjection.strZeroSheaf_comp_zeroHom`. -/
theorem strZeroSheaf_comp_zeroHom_psiSectionAt (V : S.Opens) (x : (tp L 1).val.obj (op V)) :
    strZeroSheaf 𝒜 V ≫
        CommRingCat.ofHom
          (zeroHom (𝒜.grading V) ((twist 𝒜 L).grading V) (psiSectionAt L 𝒜 V x)) =
      strZeroSheaf (twist 𝒜 L) V := by
  ext r : 2
  refine Subtype.ext ?_
  refine Eq.trans (coe_zeroHom_apply (𝒜.grading V) ((twist 𝒜 L).grading V)
    (psiSectionAt L 𝒜 V x) _) ?_
  refine Eq.trans (congrArg (fun z => psiSectionAt L 𝒜 V x z)
    (coe_strZeroSheaf_apply 𝒜 V r)) ?_
  exact Eq.trans (psiSectionAt_strHom L 𝒜 V x r) (coe_strZeroSheaf_apply (twist 𝒜 L) V r).symm

/-- **The chart comparison commutes with the structure morphisms to the spectrum of the functions
on the open**, before the identification of that spectrum with the open itself. -/
theorem projMap_psiSectionAt_comp_toSpecZero {V : S.Opens} {x : (tp L 1).val.obj (op V)}
    (hx : ∀ d : ℕ, 0 < d → TrivializesPower L V x d) :
    projMap_psiSectionAt L 𝒜 hx ≫
        AlgebraicGeometry.Proj.toSpecZero (𝒜.grading V) ≫ Spec.map (strZeroSheaf 𝒜 V) =
      AlgebraicGeometry.Proj.toSpecZero ((twist 𝒜 L).grading V) ≫
        Spec.map (strZeroSheaf (twist 𝒜 L) V) := by
  rw [← mapHomOfTop_psiSectionAt_eq_projMap L 𝒜 hx (mapDomain_psiSectionAt_eq_top' L 𝒜 hx),
    mapHomOfTop_toSpecZero_assoc, ← Spec.map_comp, strZeroSheaf_comp_zeroHom_psiSectionAt]

/-- **The chart comparison of Tag 02NC is a morphism over the open of the base.**

This is the triangle of the source's diagram over one chart: the comparison
`Proj ℬ(V) ⟶ Proj 𝒜(V)` commutes with the structure morphisms of the two charts down to the
affine open `V` of the base.

Together with
`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.projInclusionMap_comp_projMap_psiSectionAt` and
`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.projMap_psiSectionAt_eq_of_unit_smul` this is
what makes the charts of `Proj_S(𝒜)`, composed with the comparisons, a second solution of the
glueing problem that the charts of `Proj_S(ℬ)` solve, over the basis of affine opens of `S`
trivializing `ℒ`. -/
@[reassoc]
theorem projMap_psiSectionAt_comp_projInclusionToOpen {V : S.Opens} (hV : IsAffineOpen V)
    {x : (tp L 1).val.obj (op V)} (hx : ∀ d : ℕ, 0 < d → TrivializesPower L V x d) :
    projMap_psiSectionAt L 𝒜 hx ≫ RelativeProj.projInclusionToOpen 𝒜 V hV =
      RelativeProj.projInclusionToOpen (twist 𝒜 L) V hV := by
  have generic : ∀ {Z : Scheme.{u}} (i : Spec Γ(S, V) ⟶ Z),
      projMap_psiSectionAt L 𝒜 hx ≫ AlgebraicGeometry.Proj.toSpecZero (𝒜.grading V) ≫
          Spec.map (strZeroSheaf 𝒜 V) ≫ i =
        AlgebraicGeometry.Proj.toSpecZero ((twist 𝒜 L).grading V) ≫
          Spec.map (strZeroSheaf (twist 𝒜 L) V) ≫ i := by
    intro Z i
    rw [← Category.assoc (AlgebraicGeometry.Proj.toSpecZero (𝒜.grading V)), ← Category.assoc,
      projMap_psiSectionAt_comp_toSpecZero L 𝒜 hx, Category.assoc]
  exact generic _

end Stacks.AlgebraicGeometry.RelativeInvertibleTwist

end
