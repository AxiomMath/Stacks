module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.AffineRestrictTwist
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.AffineTwistSections
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.DegreeSectionBaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeProjDegreeOne.Epi
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.BasicOpenSection
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.CanonicalRestriction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The chart of a projective bundle over an affine open, with the tautological map

Let `X` be a scheme, `ℰ` a quasi-coherent `𝒪_X`-module and `W ⊆ X` an affine open. Write
`A = Γ(X, W)` and `M = Γ(ℰ, W)`. This file identifies the part of the projective bundle
`π : 𝐏(ℰ) ⟶ X` lying over `W` with the **absolute** projective spectrum
`Proj(Sym_A M)`, and carries the tautological map `u : π^*ℰ ⟶ 𝒪_{𝐏(ℰ)}(1)` across that
identification to the canonical degree-one section map `SymmetricAlgebra.toTwistSections`.

## The presentation

Everything is stated at the `Stacks.SymGraded.schemeSheafGradedAlgebra` presentation of the
bundle, i.e. at `relativeProj (schemeSheafGradedAlgebra E hqc)`, and **not** at
`Stacks.RelativeProj.projectiveBundle`. That is where `Sym(ℰ)`'s twist datum
`Stacks.SymGraded.projectiveBundleTwistData` and the tautological map
`Stacks.ProjectiveBundleSplitting.tautologicalMap` live, so no transport along
`AlgebraicGeometry.projectiveBundlePresentationsAgree` appears anywhere below; a caller holding
the `Stacks.RelativeProj.Situation` presentation transports once, at the end, rather than at
every step of the twist computation.

## The route

The chart of the relative `Proj` over `W` is `Proj` of the graded ring of sections
`Γ(W, Sym(ℰ))`, and `Stacks.SymGraded.AffinePieces.symSectionRingEquiv` identifies that graded
ring with `Sym_A(M)`. So the chart is already the absolute `Proj(Sym_A M)`, up to the
`AlgebraicGeometry.Proj.map` of that graded isomorphism, which is an isomorphism by
`AlgebraicGeometry.Proj.isIso_map`. The twist travels with it: on the chart the degree-one twist
is the absolute twisting sheaf by `Stacks.ProjectiveBundle.chartTwistIso`, and the remaining
comparison across `Proj.map` is `Stacks.ProjTwistComparison.twistMap`, invertible because a
graded isomorphism is a degreewise localization away from `1`.

On sections the computation is three existing equations and no new mathematics:
`Stacks.AlgebraicGeometry.RelativeProjDegreeOne.app_homEquiv_symm` (the transpose of `ψ₁`
evaluated at a pulled-back section is `ψ₁` of that section),
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.ψ_chart` (the chart identification carries
the absolute degree-one section to `ψ₁`), and
`Stacks.ProjTwistComparison.twistMap_degreeSection` (the twist comparison carries a degree-one
section to the degree-one section of the image).

## Main definitions

* `Stacks.ProjectiveBundleConormal.chartGradedHom`: `Γ(W, Sym(ℰ)) ≅ Sym_A(M)` as a homomorphism
  of graded rings, with `chartGradedInv` its inverse.
* `Stacks.ProjectiveBundleConormal.chartProjMap` and `chartIso`: **`Proj(Sym_A M)` is the chart
  of `𝐏(ℰ)` over `W`.**
* `Stacks.ProjectiveBundleConormal.chartMap`: the resulting morphism
  `Proj(Sym_A M) ⟶ 𝐏(ℰ)`.
* `Stacks.ProjectiveBundleConormal.chartTwistHom` and `chartTwistIso`:
  **`chartMap^*𝒪_{𝐏(ℰ)}(1) ≅ 𝒪(1)`** on `Proj(Sym_A M)`, the isomorphism being `asIso` of the
  named morphism so that it can be read on a local section; see the implementation note at
  `chartTwistIso`.

## Main results

* `Stacks.ProjectiveBundleConormal.isOpenImmersion_chartMap` and
  `opensRange_chartMap`: **`chartMap` is an open immersion onto `π⁻¹ W`.**
* `Stacks.ProjectiveBundleConormal.chartMap_comp_toBase`: it lies over `W`.
* `Stacks.ProjectiveBundleConormal.mapSection_degreeSection_tautologicalMap` and
  `twistMap_degreeSection_chartPiece`, combined in
  `exists_chartDegreeOneSection_tautologicalMap_toTwistSections`: **the tautological map, read on
  the chart over `W`, is the canonical degree-one section map of `Sym_A(M)`.**
* `Stacks.ProjectiveBundleConormal.projectiveBundle_chartTwistIso_hom_pullbackSection` and
  `chartTwistIso_hom_pullbackSection`: the same statement **on sections**, first across the
  chart's own twist comparison and then across `chartTwistIso`, where the value of the
  tautological map at `m` becomes `SymmetricAlgebra.toTwistSections Γ(X, W) Γ(E, W) m`.
* `Stacks.ProjectiveBundleConormal.basicOpen_eq_nonvanishingLocus_pullbackSection` and
  `basicOpen_eq_top_of_forall_mem_nonvanishingLocus`: **`D₊(ι m)` is exactly where the
  pulled-back tautological section at `m` does not vanish**, so a section of `π` whose pullback
  of the tautological map generates everywhere covers the whole chart over `W`. This is the local
  step of clause 3 of [Stacks, Tag 0B3V] in the shape a consumer holding the section can use.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.SymGraded

universe u

namespace Stacks.ProjectiveBundleConormal

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]
  (hqc : IsQuasicoherentPieces E) {W : X.Opens} (hW : IsAffineOpen W)

/-! ### The graded rings agree -/

/-- **`Γ(W, Sym(ℰ)) ≅ Sym_{Γ(X, W)}(Γ(ℰ, W))` as graded rings.** The underlying ring
isomorphism is `Stacks.SymGraded.AffinePieces.symSectionRingEquiv` and the grading is respected
by `Stacks.SymGraded.AffinePieces.mem_symmetricPower_symSectionRingEquiv`. -/
def chartGradedHom :
    (schemeSheafGradedAlgebra E hqc).grading W →+*ᵍ
      SymmetricAlgebra.grading Γ(X, W) Γ(E, W) where
  toRingHom := (AffinePieces.symSectionRingEquiv E hW hqc).toRingHom
  map_mem {n _} hx :=
    (AffinePieces.mem_symmetricPower_symSectionRingEquiv E hW hqc n _).2 hx

/-- The inverse graded homomorphism, `Sym_{Γ(X, W)}(Γ(ℰ, W)) ≅ Γ(W, Sym(ℰ))`. -/
def chartGradedInv :
    SymmetricAlgebra.grading Γ(X, W) Γ(E, W) →+*ᵍ
      (schemeSheafGradedAlgebra E hqc).grading W where
  toRingHom := (AffinePieces.symSectionRingEquiv E hW hqc).symm.toRingHom
  map_mem {n y} hy := by
    refine (AffinePieces.mem_symmetricPower_symSectionRingEquiv E hW hqc n _).1 ?_
    change AffinePieces.symSectionRingEquiv E hW hqc
      ((AffinePieces.symSectionRingEquiv E hW hqc).symm y) ∈ _
    rw [RingEquiv.apply_symm_apply]
    exact hy

/-- The two graded comparisons are mutually inverse, one way round. -/
theorem chartGradedHom_comp_inv :
    (chartGradedHom E hqc hW).comp (chartGradedInv E hqc hW) = GradedRingHom.id _ :=
  GradedRingHom.ext fun x => (AffinePieces.symSectionRingEquiv E hW hqc).apply_symm_apply x

/-- The two graded comparisons are mutually inverse, the other way round. -/
theorem chartGradedInv_comp_hom :
    (chartGradedInv E hqc hW).comp (chartGradedHom E hqc hW) = GradedRingHom.id _ :=
  GradedRingHom.ext fun x => (AffinePieces.symSectionRingEquiv E hW hqc).symm_apply_apply x

/-- The irrelevant-ideal hypothesis of `AlgebraicGeometry.Proj.map` for `chartGradedHom`. -/
theorem irrelevant_le_map_chartGradedHom :
    HomogeneousIdeal.irrelevant (SymmetricAlgebra.grading Γ(X, W) Γ(E, W)) ≤
      (HomogeneousIdeal.irrelevant ((schemeSheafGradedAlgebra E hqc).grading W)).map
        (chartGradedHom E hqc hW) :=
  Stacks.GradedRegrading.irrelevant_le_map_of_comp_eq_id (chartGradedHom_comp_inv E hqc hW)

/-- The irrelevant-ideal hypothesis of `AlgebraicGeometry.Proj.map` for `chartGradedInv`. -/
theorem irrelevant_le_map_chartGradedInv :
    HomogeneousIdeal.irrelevant ((schemeSheafGradedAlgebra E hqc).grading W) ≤
      (HomogeneousIdeal.irrelevant (SymmetricAlgebra.grading Γ(X, W) Γ(E, W))).map
        (chartGradedInv E hqc hW) :=
  Stacks.GradedRegrading.irrelevant_le_map_of_comp_eq_id (chartGradedInv_comp_hom E hqc hW)

/-! ### `Proj(Sym_A M)` is the chart over `W` -/

/-- The morphism of projective spectra induced by `chartGradedHom`, from the absolute
`Proj(Sym_A M)` to the chart `Proj(Γ(W, Sym(ℰ)))` of the bundle over `W`. -/
abbrev chartProjMap :
    AlgebraicGeometry.Proj (SymmetricAlgebra.grading Γ(X, W) Γ(E, W)) ⟶
      AlgebraicGeometry.Proj ((schemeSheafGradedAlgebra E hqc).grading W) :=
  Proj.map (chartGradedHom E hqc hW) (irrelevant_le_map_chartGradedHom E hqc hW)

/-- **The comparison of projective spectra is an isomorphism**, the graded comparison having a
two-sided graded inverse. -/
instance isIso_chartProjMap : IsIso (chartProjMap E hqc hW) :=
  Proj.isIso_map _ (irrelevant_le_map_chartGradedInv E hqc hW)
    (chartGradedInv_comp_hom E hqc hW) (chartGradedHom_comp_inv E hqc hW)

/-- **The absolute `Proj(Sym_A M)` is the chart of `𝐏(ℰ)` over the affine open `W`.** -/
def chartIso :
    AlgebraicGeometry.Proj (SymmetricAlgebra.grading Γ(X, W) Γ(E, W)) ≅
      AlgebraicGeometry.Proj ((schemeSheafGradedAlgebra E hqc).grading W) :=
  asIso (chartProjMap E hqc hW)

/-- The chart of `𝐏(ℰ)` over `W` is an open immersion. -/
instance isOpenImmersion_relativeProjChart :
    IsOpenImmersion ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart W hW) :=
  (projectiveBundleTwistData E hqc).chartData.chart_isOpenImmersion W hW

/-- **The chart of `𝐏(ℰ)` over `W`, read on the absolute `Proj(Sym_A M)`.** -/
def chartMap :
    AlgebraicGeometry.Proj (SymmetricAlgebra.grading Γ(X, W) Γ(E, W)) ⟶
      (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme :=
  chartProjMap E hqc hW ≫ (relativeProj (schemeSheafGradedAlgebra E hqc)).chart W hW

/-- **`chartMap` is an open immersion**: an isomorphism followed by the chart. -/
instance isOpenImmersion_chartMap : IsOpenImmersion (chartMap E hqc hW) := by
  unfold chartMap
  infer_instance

/-- **The image of `chartMap` is the part of `𝐏(ℰ)` lying over `W`.** -/
theorem opensRange_chartMap :
    (chartMap E hqc hW).opensRange =
      (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ W := by
  change (chartProjMap E hqc hW ≫
    (relativeProj (schemeSheafGradedAlgebra E hqc)).chart W hW).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso, ← Scheme.Hom.image_top_eq_opensRange]
  exact Stacks.AlgebraicGeometry.RelativeProjTwistGlue.chart_image_top _ W hW

/-- **The part of `𝐏(ℰ)` lying over `W` is the absolute `Proj(Sym_A M)`.** -/
def bundleOverIso :
    AlgebraicGeometry.Proj (SymmetricAlgebra.grading Γ(X, W) Γ(E, W)) ≅
      ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ W).toScheme :=
  (chartMap E hqc hW).isoOpensRange ≪≫ Scheme.isoOfEq _ (opensRange_chartMap E hqc hW)

/-- **`chartMap` lies over `W`**: composed with the projection of the bundle it factors through
the inclusion of `W`. -/
theorem chartMap_comp_toBase :
    chartMap E hqc hW ≫ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase =
      (chartProjMap E hqc hW ≫
        projInclusionToOpen (schemeSheafGradedAlgebra E hqc) W hW) ≫ W.ι :=
  ((Category.assoc (chartProjMap E hqc hW)
      ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart W hW) _).trans
    (congrArg (fun g => chartProjMap E hqc hW ≫ g)
      (Stacks.AlgebraicGeometry.RelativeProjMapDomain.chart_comp_toBase
        (schemeSheafGradedAlgebra E hqc) W hW))).trans
    (Category.assoc _ _ _).symm

/-! ### The twists agree -/

/-- The comparison of graded rings is a degreewise localization away from `1`: it is an
isomorphism, so no denominator is needed. -/
theorem isAwayDegreewise_chartGradedHom :
    Stacks.GradedLocalization.IsAwayDegreewise (chartGradedHom E hqc hW) 1 where
  isUnit_map := by rw [map_one]; exact isUnit_one
  surj n y hy := by
    refine ⟨0, chartGradedInv E hqc hW y, (chartGradedInv E hqc hW).map_mem hy, ?_⟩
    rw [pow_zero, one_mul]
    exact (AffinePieces.symSectionRingEquiv E hW hqc).apply_symm_apply y
  torsion n x _ h := by
    refine ⟨0, ?_⟩
    rw [pow_zero, one_mul]
    exact (AffinePieces.symSectionRingEquiv E hW hqc).injective (h.trans (map_zero _).symm)

/-- **The twisting sheaves are carried to each other by `chartProjMap`**, in every degree. -/
instance isIso_chartTwistMap (n : ℤ) :
    IsIso (Stacks.ProjTwistComparison.twistMap (chartGradedHom E hqc hW)
      (irrelevant_le_map_chartGradedHom E hqc hW) n) :=
  Stacks.ProjTwistComparison.isIso_twistMap _ _ n
    (isAwayDegreewise_chartGradedHom E hqc hW) (SetLike.one_mem_graded _)

/-- **The comparison `chartMap^* 𝒪_{𝐏(ℰ)}(1) ⟶ 𝒪(1)`** on `Proj(Sym_A M)`, as a single named
morphism: the pullback along `chartMap = chartProjMap ≫ chart` read as two successive pullbacks,
then the degree-one twist of the bundle identified with the absolute twist on the chart over `W`
(`Stacks.ProjectiveBundle.chartTwistIso`), then the comparison of twists across `chartProjMap`
(`Stacks.ProjTwistComparison.twistMap`).

It is named, rather than left as the `.hom` of a three-fold `Iso.trans`, precisely so that
`chartTwistIso_hom_val_app` can split it on a local section by `rfl`. Reading the `.hom` of a
three-fold `Iso.trans` on a section exhausts the elaborator's budget, while the same split at a
named composite is free; see the implementation note of `chartTwistIso`. -/
def chartTwistHom :
    (Scheme.Modules.pullback (chartMap E hqc hW)).obj
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc) ⟶
      twistingSheaf (SymmetricAlgebra.grading Γ(X, W) Γ(E, W)) 1 :=
  ((Scheme.Modules.pullbackComp (chartProjMap E hqc hW)
        ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart W hW)).inv.app
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)) ≫
    (Scheme.Modules.pullback (chartProjMap E hqc hW)).map
      (Stacks.ProjectiveBundle.chartTwistIso E hqc hW).hom ≫
    Stacks.ProjTwistComparison.twistMap (chartGradedHom E hqc hW)
      (irrelevant_le_map_chartGradedHom E hqc hW) 1

/-- **`chartTwistHom` is an isomorphism**: each of its three factors is one.

Every factor is supplied by hand, through `CategoryTheory.IsIso.comp_isIso'`, and none is left to
instance search: `AlgebraicGeometry.Scheme.Modules` is a semireducible definition, so neither
`CategoryTheory.Functor.map_isIso` nor the component instances for a natural isomorphism fire at
`(Scheme.Modules.pullback _).map` and `(Scheme.Modules.pullbackComp _ _).inv.app _`. The outer two
factors are therefore named as the forward map of `CategoryTheory.Functor.mapIso` and the backward
map of `CategoryTheory.Iso.app`, which are the same two morphisms. -/
instance isIso_chartTwistHom : IsIso (chartTwistHom E hqc hW) := by
  unfold chartTwistHom
  exact IsIso.comp_isIso'
    (((Scheme.Modules.pullbackComp (chartProjMap E hqc hW)
          ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart W hW)).app
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)).isIso_inv)
    (IsIso.comp_isIso'
      (((Scheme.Modules.pullback (chartProjMap E hqc hW)).mapIso
        (Stacks.ProjectiveBundle.chartTwistIso E hqc hW)).isIso_hom)
      (isIso_chartTwistMap E hqc hW 1))

/-- **`chartMap^* 𝒪_{𝐏(ℰ)}(1)` is the first twisting sheaf of `Proj(Sym_A M)`.** The degree-one
twist of the bundle is the absolute twist on the chart over `W`
(`Stacks.ProjectiveBundle.chartTwistIso`), and the comparison across `chartProjMap` is
`Stacks.ProjTwistComparison.twistMap`, invertible by `isIso_chartTwistMap`.

## Implementation note

The isomorphism is `asIso` of the named morphism `chartTwistHom` and **not** a chain of `≪≫`.
The two spellings are definitionally equal, but a three-fold `Iso.trans` cannot be read on a
local section within the elaborator's budget: pushing
`(chartTwistIso …).hom.val.app (op ⊤)` down to its three factors exceeds 200000 heartbeats
whether the section is written out, generalized to a variable, or split at the level of
morphisms. The same split at the two-fold `Stacks.ProjectiveBundle.chartTwistIso` is free, so it
is the third layer specifically. With a named `.hom` the split is `rfl`
(`chartTwistIso_hom_val_app`) and `chartTwistIso_hom_pullbackSection` goes through. -/
def chartTwistIso :
    (Scheme.Modules.pullback (chartMap E hqc hW)).obj
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc) ≅
      twistingSheaf (SymmetricAlgebra.grading Γ(X, W) Γ(E, W)) 1 :=
  asIso (chartTwistHom E hqc hW)

/-- The isomorphism's forward map is the named morphism it was built from. -/
theorem chartTwistIso_hom : (chartTwistIso E hqc hW).hom = chartTwistHom E hqc hW := rfl

/-- **`chartTwistIso` read on a local section**: the three factors of `chartTwistHom`, applied in
turn. This is the split that the `Iso.trans` spelling could not afford, and with a named `.hom` it
is `rfl`. -/
theorem chartTwistIso_hom_val_app
    (V : (AlgebraicGeometry.Proj (SymmetricAlgebra.grading Γ(X, W) Γ(E, W))).Opensᵒᵖ)
    (x : ((Scheme.Modules.pullback (chartMap E hqc hW)).obj
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)).val.obj V) :
    (chartTwistIso E hqc hW).hom.val.app V x =
      (Stacks.ProjTwistComparison.twistMap (chartGradedHom E hqc hW)
          (irrelevant_le_map_chartGradedHom E hqc hW) 1).val.app V
        (((Scheme.Modules.pullback (chartProjMap E hqc hW)).map
            (Stacks.ProjectiveBundle.chartTwistIso E hqc hW).hom).val.app V
          (((Scheme.Modules.pullbackComp (chartProjMap E hqc hW)
                ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart W hW)).inv.app
              (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)).val.app V x)) :=
  rfl

/-! ### The tautological map on the chart -/

/-- **The degree-one section of `Sym(ℰ)` over `W` attached to `m : Γ(ℰ, W)`**: the sheafification
unit applied to `m` read as a degree-one element of `Sym_{Γ(X, W)}(Γ(ℰ, W))`. It is
`Stacks.SymGraded.unitSection E W hqc 1 (SymmetricAlgebra.toGradingOne _ _ m)`, spelled through
`Stacks.SymGraded.AffinePieces.pieceSectionsEquiv` so that
`Stacks.SymGraded.AffinePieces.symSectionRingEquiv_of` applies to it on the nose. -/
def chartPiece (m : Γ(E, W)) : (schemeSheafGradedAlgebra E hqc).sectionPieces W 1 :=
  AffinePieces.pieceSectionsEquiv E hW ((1 : ℕ) : ℤ)
    (SymmetricAlgebra.toGradingOne Γ(X, W) Γ(E, W) m)

/-- **The graded comparison carries the degree-one section attached to `m` to `ι m`.** This is
`Stacks.SymGraded.AffinePieces.symSectionRingEquiv_of` in degree one: the comparison undoes the
sheafification unit, so what is left of `chartPiece` is `m` itself, read in `Sym¹_A(M)`. -/
theorem chartGradedHom_of_chartPiece (m : Γ(E, W)) :
    chartGradedHom E hqc hW
        (DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces W) 1
          (chartPiece E hqc hW m)) =
      SymmetricAlgebra.ι Γ(X, W) Γ(E, W) m := by
  change AffinePieces.symSectionRingEquiv E hW hqc
      (DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces W) 1
        (AffinePieces.pieceSectionsEquiv E hW ((1 : ℕ) : ℤ)
          (SymmetricAlgebra.toGradingOne Γ(X, W) Γ(E, W) m))) = _
  refine (AffinePieces.symSectionRingEquiv_of E hW hqc 1 _).trans ?_
  refine Eq.trans (congrArg
    (fun y : Stacks.SymGraded.gradedPiece (R := Γ(X, W)) Γ(E, W) ((1 : ℕ) : ℤ) =>
      (y : SymmetricAlgebra Γ(X, W) Γ(E, W)))
    ((AffinePieces.pieceSectionsEquiv E hW ((1 : ℕ) : ℤ)).symm_apply_apply
      (SymmetricAlgebra.toGradingOne Γ(X, W) Γ(E, W) m))) ?_
  exact SymmetricAlgebra.coe_toGradingOne Γ(X, W) Γ(E, W) m

/-- **The absolute degree-one global section of `𝒪(1)` on the chart over `W` attached to
`m : Γ(ℰ, W)`**: the section of `Stacks.AlgebraicGeometry.ProjTwistSections.degreeSection`
attached to the degree-one homogeneous element `chartPiece E hqc hW m` of `Γ(W, Sym(ℰ))`. -/
def chartDegreeOneSection (m : Γ(E, W)) :
    twistGlobalSections ((schemeSheafGradedAlgebra E hqc).grading W) 1 :=
  degreeSection ((schemeSheafGradedAlgebra E hqc).grading W) 1
    ⟨DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces W) 1 (chartPiece E hqc hW m),
      (schemeSheafGradedAlgebra E hqc).of_mem_grading W (chartPiece E hqc hW m)⟩

/-- **The chart comparison of twists carries the degree-one section attached to `m` to
`SymmetricAlgebra.toTwistSections`.** This is
`Stacks.ProjTwistComparison.twistMap_degreeSection` for the graded isomorphism
`chartGradedHom`, with `chartGradedHom_of_chartPiece` identifying the image. -/
theorem twistMap_degreeSection_chartPiece (m : Γ(E, W)) :
    ((Stacks.ProjTwistComparison.twistMap (chartGradedHom E hqc hW)
          (irrelevant_le_map_chartGradedHom E hqc hW) ((1 : ℕ) : ℤ)).val.app (op ⊤)).hom'
        ((((Scheme.Modules.pullbackPushforwardAdjunction (chartProjMap E hqc hW)).unit.app
              (twistingSheaf ((schemeSheafGradedAlgebra E hqc).grading W)
                ((1 : ℕ) : ℤ))).val.app (op ⊤)).hom'
          (degreeSection ((schemeSheafGradedAlgebra E hqc).grading W) 1
            ⟨DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces W) 1
                (chartPiece E hqc hW m),
              (schemeSheafGradedAlgebra E hqc).of_mem_grading W (chartPiece E hqc hW m)⟩)) =
      SymmetricAlgebra.toTwistSections Γ(X, W) Γ(E, W) m :=
  (Stacks.ProjTwistComparison.twistMap_degreeSection (chartGradedHom E hqc hW)
      (irrelevant_le_map_chartGradedHom E hqc hW) 1 _).trans
    (congrArg (degreeSection (SymmetricAlgebra.grading Γ(X, W) Γ(E, W)) 1)
      (Subtype.ext (chartGradedHom_of_chartPiece E hqc hW m)))

/-- **The degree-one generator `ℰ ⟶ Sym¹(ℰ)` sends a section `m` over `W` to the degree-one
section `chartPiece` attached to `m`.**

The generator is the sheafified sectionwise generator precomposed with the inverse of the
counit isomorphism of the sheafification; that inverse *is* the sheafification unit on local
sections (`PresheafOfModules.sheafifyCounitIso_inv_apply`), and
`Stacks.GradedAlgebra.sheafifyGen_unit` then says the sheafified generator agrees with the
sectionwise one on unit images. The sectionwise generator is `SymmetricAlgebra.ι`, which is what
`SymmetricAlgebra.toGradingOne` is. -/
theorem symmetricAlgebraGen_app (m : Γ(E, W)) :
    (Scheme.Modules.symmetricAlgebraGen X E).val.app (op W) m = chartPiece E hqc hW m := by
  refine Eq.trans (congrArg
    (fun z => ((PresheafOfModules.symPowIntGradedAlgebra E.val).sheafifyGen
        (𝟙 X.ringCatSheaf.obj) (PresheafOfModules.symPowIntGen E.val)).val.app (op W) z)
    (PresheafOfModules.sheafifyCounitIso_inv_apply (𝟙 X.ringCatSheaf.obj) E (op W) m)) ?_
  exact (PresheafOfModules.symPowIntGradedAlgebra E.val).sheafifyGen_unit
    (𝟙 X.ringCatSheaf.obj) (PresheafOfModules.symPowIntGen E.val) (op W) m

omit [E.IsQuasicoherent] in
/-- **The chart identification of the twist datum carries the absolute degree-one section
attached to a section `a` of `Sym¹(ℰ)` over `W` to the value at `a` of the degree-one
tautological twist map `π^*Sym¹(ℰ) ⟶ 𝒪_{𝐏(ℰ)}(1)`.**

Two equations: `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.ψ_chart` for the
canonical twist datum of `Sym(ℰ)`, and
`Stacks.AlgebraicGeometry.RelativeProjDegreeOne.app_homEquiv_symm`, which says the transpose of
`ψ₁` evaluated at a pulled-back section is the value of `ψ₁` — the transpose being
`Stacks.ProjectiveBundleSplitting.tautologicalTwistMap` by definition. -/
theorem mapSection_degreeSection_tautologicalTwistMap
    (a : (schemeSheafGradedAlgebra E hqc).sectionPieces W 1) :
    (projectiveBundleTwistData E hqc).chartData.mapSection W hW ((1 : ℕ) : ℤ) ⊤
        (degreeSection ((schemeSheafGradedAlgebra E hqc).grading W) 1
          ⟨DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces W) 1 a,
            (schemeSheafGradedAlgebra E hqc).of_mem_grading W a⟩) =
      ((projectiveBundleTwistData E hqc).chartData.chart_range W hW).symm ▸
        ((Stacks.ProjectiveBundleSplitting.tautologicalTwistMap E hqc 1).val.app
            (op ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ W))
          (Stacks.AlgebraicGeometry.RelativeProjDegreeOne.unitSection
            (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase
            ((schemeSheafGradedAlgebra E hqc).piece ((1 : ℕ) : ℤ)) W a)) :=
  ((projectiveBundleTwistData E hqc).ψ_chart W hW 1 a).trans
    (congrArg (fun z => ((projectiveBundleTwistData E hqc).chartData.chart_range W hW).symm ▸ z)
      (Stacks.AlgebraicGeometry.RelativeProjDegreeOne.app_homEquiv_symm
          (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase
          ((projectiveBundleTwistData E hqc).ψ 1) W a).symm)

omit [E.IsQuasicoherent] in
/-- **The chart of `𝐏(ℰ)` over `W` lies entirely over `W`**, as the inclusion of opens that
`AlgebraicGeometry.Scheme.Modules.pullbackSection` takes as its hypothesis. -/
theorem top_le_chart_preimage :
    (⊤ : (AlgebraicGeometry.Proj ((schemeSheafGradedAlgebra E hqc).grading W)).Opens) ≤
      (relativeProj (schemeSheafGradedAlgebra E hqc)).chart W hW ⁻¹ᵁ
        ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ W) := by
  rw [← Scheme.Hom.comp_preimage,
    Stacks.AlgebraicGeometry.RelativeProjMapDomain.chart_comp_toBase,
    Scheme.Hom.comp_preimage, W.ι_preimage_self, Scheme.Hom.preimage_top]

/-- The same inclusion for `chartMap`, the chart precomposed with an isomorphism. -/
theorem top_le_chartMap_preimage :
    (⊤ : (AlgebraicGeometry.Proj (SymmetricAlgebra.grading Γ(X, W) Γ(E, W))).Opens) ≤
      chartMap E hqc hW ⁻¹ᵁ
        ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ W) :=
  fun x _ => top_le_chart_preimage E hqc hW (x := (chartProjMap E hqc hW).base x) trivial

/-- **The tautological map `π^*ℰ ⟶ 𝒪_{𝐏(ℰ)}(1)`, read on the chart over `W`, is the absolute
degree-one section attached to `m`.**

Together with `twistMap_degreeSection_chartPiece` — which says that the same absolute degree-one
section is `SymmetricAlgebra.toTwistSections Γ(X, W) Γ(E, W) m` once transported to
`Proj(Sym_A M)` along `chartProjMap` — this is the transport asked for by clause 3 of
[Stacks, Tag 0B3V]: on the chart over `W` the tautological map *is* the canonical degree-one
section map of `Sym_A(M)`, so a section `σ` of `π` whose pullback of `u` is an epimorphism onto
an invertible module feeds the hypothesis of
`Stacks.ProjectiveBundleConormal.preimage_basicOpen_eq_top`.

The extra step over `mapSection_degreeSection_tautologicalTwistMap` is the degree-one generator
`ℰ ⟶ Sym¹(ℰ)` that `Stacks.ProjectiveBundleSplitting.tautologicalMap` is precomposed with:
`AlgebraicGeometry.Scheme.Modules.unit_app_val_app_naturality` carries it across the unit of
`π^* ⊣ π_*` and `symmetricAlgebraGen_app` evaluates it at `m`. -/
@[ega "II 4.1.5" "Identification of α₁♯"]
theorem mapSection_degreeSection_tautologicalMap (m : Γ(E, W)) :
    (projectiveBundleTwistData E hqc).chartData.mapSection W hW ((1 : ℕ) : ℤ) ⊤
        (degreeSection ((schemeSheafGradedAlgebra E hqc).grading W) 1
          ⟨DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces W) 1
              (chartPiece E hqc hW m),
            (schemeSheafGradedAlgebra E hqc).of_mem_grading W (chartPiece E hqc hW m)⟩) =
      ((projectiveBundleTwistData E hqc).chartData.chart_range W hW).symm ▸
        ((Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc).val.app
            (op ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ W))
          (Stacks.AlgebraicGeometry.RelativeProjDegreeOne.unitSection
            (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase E W m)) :=
  (mapSection_degreeSection_tautologicalTwistMap E hqc hW (chartPiece E hqc hW m)).trans
    (congrArg (fun z => ((projectiveBundleTwistData E hqc).chartData.chart_range W hW).symm ▸ z)
      (congrArg
        (fun z : Γ((Scheme.Modules.pullback
              (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).obj
            ((schemeSheafGradedAlgebra E hqc).piece ((1 : ℕ) : ℤ)),
            (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ W) =>
          (Stacks.ProjectiveBundleSplitting.tautologicalTwistMap E hqc 1).val.app
            (op ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ W)) z)
        (((Scheme.Modules.unit_app_val_app_naturality
            (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase
            (Scheme.Modules.symmetricAlgebraGen X E) W m).trans
          (congrArg
            (Stacks.AlgebraicGeometry.RelativeProjDegreeOne.unitSection
              (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase
              ((schemeSheafGradedAlgebra E hqc).piece ((1 : ℕ) : ℤ)) W)
            (symmetricAlgebraGen_app E hqc hW m))).symm)))

/-- **The tautological map of the bundle, read on the chart over `W`, is the canonical degree-one
section map of `Sym_A(M)`.**

For each `m : Γ(ℰ, W)` there is a single global section `τ` of the absolute `𝒪(1)` on the chart
of `𝐏(ℰ)` over `W` which is simultaneously

* the value at `m` of the tautological map `u : π^*ℰ ⟶ 𝒪_{𝐏(ℰ)}(1)` over `π⁻¹ W`, read through
  the chart identification of the canonical twist datum of `Sym(ℰ)`, and
* `SymmetricAlgebra.toTwistSections Γ(X, W) Γ(E, W) m` once transported along `chartProjMap` to
  the absolute `Proj(Sym_A M)` by `Stacks.ProjTwistComparison.twistMap`, the comparison whose
  isomorphism `chartTwistIso` is built from.

That is the transport step of clause 3 of [Stacks, Tag 0B3V]: it is what turns a hypothesis about
`σ^*u` into the hypothesis of
`Stacks.ProjectiveBundleConormal.preimage_basicOpen_eq_top`, which is stated for
`SymmetricAlgebra.toTwistSections`. The witness is `chartDegreeOneSection E hqc hW m`. -/
theorem exists_chartDegreeOneSection_tautologicalMap_toTwistSections (m : Γ(E, W)) :
    ∃ τ : twistGlobalSections ((schemeSheafGradedAlgebra E hqc).grading W) 1,
      (projectiveBundleTwistData E hqc).chartData.mapSection W hW ((1 : ℕ) : ℤ) ⊤ τ =
          ((projectiveBundleTwistData E hqc).chartData.chart_range W hW).symm ▸
            ((Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc).val.app
              (op ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ W))
              (Stacks.AlgebraicGeometry.RelativeProjDegreeOne.unitSection
                (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase E W m)) ∧
        ((Stacks.ProjTwistComparison.twistMap (chartGradedHom E hqc hW)
              (irrelevant_le_map_chartGradedHom E hqc hW) ((1 : ℕ) : ℤ)).val.app (op ⊤)).hom'
            ((((Scheme.Modules.pullbackPushforwardAdjunction (chartProjMap E hqc hW)).unit.app
                  (twistingSheaf ((schemeSheafGradedAlgebra E hqc).grading W)
                    ((1 : ℕ) : ℤ))).val.app (op ⊤)).hom' τ) =
          SymmetricAlgebra.toTwistSections Γ(X, W) Γ(E, W) m :=
  ⟨chartDegreeOneSection E hqc hW m,
    mapSection_degreeSection_tautologicalMap E hqc hW m,
    twistMap_degreeSection_chartPiece E hqc hW m⟩

/-! ### The twist comparison on sections -/

/-- The comparison `chartMap^* ≅ chartProjMap^* ∘ chart^*` carries a section pulled back along
`chartMap` to the same section pulled back in two stages. This is
`AlgebraicGeometry.Scheme.Modules.pullbackSection_comp` read through the inverse. -/
theorem pullbackComp_inv_app_pullbackSection
    (a : Γ(Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc,
      (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ W)) :
    ((Scheme.Modules.pullbackComp (chartProjMap E hqc hW)
          ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart W hW)).inv.app
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)).val.app (op ⊤)
        (Scheme.Modules.pullbackSection (chartMap E hqc hW)
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)
          ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ W) ⊤
          (top_le_chartMap_preimage E hqc hW) a) =
      Scheme.Modules.pullbackSection (chartProjMap E hqc hW)
        ((Scheme.Modules.pullback
            ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart W hW)).obj
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)) ⊤ ⊤
        (Scheme.Hom.preimage_top (chartProjMap E hqc hW)).ge
        (Scheme.Modules.pullbackSection
          ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart W hW)
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)
          ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ W) ⊤
          (top_le_chart_preimage E hqc hW) a) := by
  refine Eq.trans (congrArg
    (fun z => ((Scheme.Modules.pullbackComp (chartProjMap E hqc hW)
        ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart W hW)).inv.app
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)).val.app (op ⊤) z)
    (Scheme.Modules.pullbackSection_comp (chartProjMap E hqc hW)
      ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart W hW)
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)
      ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ W) ⊤ ⊤
      (top_le_chart_preimage E hqc hW)
      (Scheme.Hom.preimage_top (chartProjMap E hqc hW)).ge
      (top_le_chartMap_preimage E hqc hW) a).symm) ?_
  exact Stacks.AlgebraicGeometry.RelativeProjDegreeOne.iso_inv_hom_app
    ((Scheme.Modules.pullbackComp (chartProjMap E hqc hW)
      ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart W hW)).app
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)) (op ⊤) _

/-- **The degree-one twist on the chart over `W`, on sections**: the chart identification of the
canonical twist datum carries the pullback of the value at `m` of the tautological map to the
absolute degree-one section `chartDegreeOneSection`.

`Stacks.ProjectiveBundle.chartTwistIso` is the comparison of the restriction with the pullback
followed by the chart identification, so this is
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback_inv_pullbackSection` followed by
`mapSection_degreeSection_tautologicalMap` with the `mapSection` wrapper
(`Stacks.AlgebraicGeometry.ModuleLimits.restrictAppIso_hom_apply`) and the transport along
`ChartData.chart_range` (`RelativeProjDegreeOne.map_eqRec`) removed. -/
theorem projectiveBundle_chartTwistIso_hom_pullbackSection (m : Γ(E, W)) :
    (Stacks.ProjectiveBundle.chartTwistIso E hqc hW).hom.val.app (op ⊤)
        (Scheme.Modules.pullbackSection
          ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart W hW)
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)
          ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ W) ⊤
          (top_le_chart_preimage E hqc hW)
          ((Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc).val.app
            (op ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ W))
            (Stacks.AlgebraicGeometry.RelativeProjDegreeOne.unitSection
              (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase E W m))) =
      chartDegreeOneSection E hqc hW m := by
  have hrange := (projectiveBundleTwistData E hqc).chartData.chart_range W hW
  have hstrip : (projectiveBundleTwistData E hqc).chartData.mapSection W hW ((1 : ℕ) : ℤ) ⊤
      (chartDegreeOneSection E hqc hW m) =
      ((projectiveBundleTwistData E hqc).chartData.chartIso W hW ((1 : ℕ) : ℤ)).inv.val.app
        (op ⊤) (chartDegreeOneSection E hqc hW m) :=
    Stacks.AlgebraicGeometry.ModuleLimits.restrictAppIso_hom_apply _ _ _ _
  have key : ∀ (U₁ U₂ : (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.Opens)
      (e : U₁ = U₂) (x : Γ(Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc, U₂)),
      (e ▸ x : Γ(Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc, U₁)) =
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc).val.map
          (homOfLE e.le).op x := by
    rintro U₁ U₂ rfl x
    have hid : (homOfLE (le_refl U₁)).op = 𝟙 (op U₁) := Subsingleton.elim _ _
    rw [hid]
    simp
    rfl
  have happ : (Stacks.ProjectiveBundle.chartTwistIso E hqc hW).hom.val.app (op ⊤)
        (Scheme.Modules.pullbackSection
          ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart W hW)
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)
          ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ W) ⊤
          (top_le_chart_preimage E hqc hW)
          ((Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc).val.app
            (op ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ W))
            (Stacks.AlgebraicGeometry.RelativeProjDegreeOne.unitSection
              (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase E W m))) =
      ((projectiveBundleTwistData E hqc).chartData.chartIso W hW ((1 : ℕ) : ℤ)).hom.val.app
        (op ⊤)
        (((Scheme.Modules.restrictFunctorIsoPullback
            ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart W hW)).inv.app
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)).val.app (op ⊤)
          (Scheme.Modules.pullbackSection
          ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart W hW)
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)
          ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ W) ⊤
          (top_le_chart_preimage E hqc hW)
          ((Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc).val.app
            (op ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ W))
            (Stacks.AlgebraicGeometry.RelativeProjDegreeOne.unitSection
              (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase E W m)))) := rfl
  rw [happ, Scheme.Modules.restrictFunctorIsoPullback_inv_pullbackSection
      ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart W hW)
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)
      ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ W) ⊤
      (top_le_chart_preimage E hqc hW) hrange.le]
  refine Eq.trans (congrArg
    (fun z => ((projectiveBundleTwistData E hqc).chartData.chartIso W hW
        ((1 : ℕ) : ℤ)).hom.val.app (op ⊤) z)
    (((hstrip.symm.trans (mapSection_degreeSection_tautologicalMap E hqc hW m)).trans
      (key _ _ hrange _)).symm)) ?_
  exact Stacks.AlgebraicGeometry.RelativeProjDegreeOne.iso_inv_hom_app
    ((projectiveBundleTwistData E hqc).chartData.chartIso W hW ((1 : ℕ) : ℤ)).symm (op ⊤) _

/-- Pullback of `chartTwistIso` along `g`, read on the pulled-back tautological section. -/
private theorem pullback_chartTwistIso_hom_pullbackSection_aux {Y : Scheme.{u}}
    (g : Y ⟶ AlgebraicGeometry.Proj ((schemeSheafGradedAlgebra E hqc).grading W))
    (U : Y.Opens) (hU : U ≤ g ⁻¹ᵁ ⊤) (m : Γ(E, W)) :
    ((Scheme.Modules.pullback g).map
          (Stacks.ProjectiveBundle.chartTwistIso E hqc hW).hom).val.app (op U)
        (Scheme.Modules.pullbackSection g
          ((Scheme.Modules.pullback
              ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart W hW)).obj
            (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)) ⊤ U hU
          (Scheme.Modules.pullbackSection
            ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart W hW)
            (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)
            ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ W) ⊤
            (top_le_chart_preimage E hqc hW)
            ((Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc).val.app
              (op ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ W))
              (Stacks.AlgebraicGeometry.RelativeProjDegreeOne.unitSection
                (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase E W m)))) =
      Scheme.Modules.pullbackSection g
        (twistingSheaf ((schemeSheafGradedAlgebra E hqc).grading W) 1) ⊤ U hU
        (chartDegreeOneSection E hqc hW m) :=
  (Scheme.Modules.pullbackSection_naturality g
      (Stacks.ProjectiveBundle.chartTwistIso E hqc hW).hom ⊤ U hU _).trans
    (congrArg
      (Scheme.Modules.pullbackSection g
        (twistingSheaf ((schemeSheafGradedAlgebra E hqc).grading W) 1) ⊤ U hU)
      (projectiveBundle_chartTwistIso_hom_pullbackSection E hqc hW m))

/-- **The tautological map, pulled back to the absolute `Proj(Sym_A M)` and read through
`chartTwistIso`, is the canonical degree-one section map of `Sym_A(M)`.**

This is the transport of clause 3 of [Stacks, Tag 0B3V] at the *absolute* chart: the value at
`m : Γ(ℰ, W)` of the tautological map `u : π^*ℰ ⟶ 𝒪_{𝐏(ℰ)}(1)` over `π⁻¹W`, pulled back along
`chartMap` and carried across `chartTwistIso`, is
`SymmetricAlgebra.toTwistSections Γ(X, W) Γ(E, W) m` — the section whose nonvanishing locus
`Stacks.ProjectiveBundleConormal.preimage_basicOpen_eq_top` is stated for.

Three legs and no new mathematics. `chartTwistIso_hom_val_app` splits the comparison into its
three factors, and then

* `pullbackComp_inv_app_pullbackSection` turns one pullback along `chartMap` into two,
* `AlgebraicGeometry.Scheme.Modules.pullbackSection_naturality` moves the inner comparison
  `Stacks.ProjectiveBundle.chartTwistIso` under the outer pullback, where
  `projectiveBundle_chartTwistIso_hom_pullbackSection` evaluates it to
  `chartDegreeOneSection E hqc hW m`,
* `AlgebraicGeometry.Scheme.Modules.pullbackSection_top` strips the restriction map from the
  remaining pullback over `⊤`, leaving exactly the adjunction unit that
  `twistMap_degreeSection_chartPiece` consumes. -/
theorem chartTwistIso_hom_pullbackSection (m : Γ(E, W)) :
    (chartTwistIso E hqc hW).hom.val.app (op ⊤)
        (Scheme.Modules.pullbackSection (chartMap E hqc hW)
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)
          ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ W) ⊤
          (top_le_chartMap_preimage E hqc hW)
          ((Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc).val.app
            (op ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ W))
            (Stacks.AlgebraicGeometry.RelativeProjDegreeOne.unitSection
              (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase E W m))) =
      SymmetricAlgebra.toTwistSections Γ(X, W) Γ(E, W) m := by
  have h₁ := pullbackComp_inv_app_pullbackSection E hqc hW
    ((Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc).val.app
      (op ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ W))
      (Stacks.AlgebraicGeometry.RelativeProjDegreeOne.unitSection
        (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase E W m))
  have h₂ := pullback_chartTwistIso_hom_pullbackSection_aux E hqc hW (chartProjMap E hqc hW) ⊤
    (Scheme.Hom.preimage_top (chartProjMap E hqc hW)).ge m
  have h₄ := Scheme.Modules.pullbackSection_top (chartProjMap E hqc hW)
    (twistingSheaf ((schemeSheafGradedAlgebra E hqc).grading W) 1)
    (Scheme.Hom.preimage_top (chartProjMap E hqc hW)).ge
    (chartDegreeOneSection E hqc hW m)
  have hmid := (congrArg
      (fun z => ((Scheme.Modules.pullback (chartProjMap E hqc hW)).map
        (Stacks.ProjectiveBundle.chartTwistIso E hqc hW).hom).val.app (op ⊤) z) h₁).trans
    (h₂.trans h₄)
  exact (chartTwistIso_hom_val_app E hqc hW (op ⊤) _).trans
    ((congrArg
      (fun z => (Stacks.ProjTwistComparison.twistMap (chartGradedHom E hqc hW)
        (irrelevant_le_map_chartGradedHom E hqc hW) 1).val.app (op ⊤) z) hmid).trans
      (twistMap_degreeSection_chartPiece E hqc hW m))

/-! ### Where the pulled-back tautological section does not vanish -/

/-- **On the chart over `W`, the standard open `D₊(ι m)` is exactly the locus where the
pulled-back tautological section attached to `m` does not vanish.**

`Stacks.ProjectiveBundleConormal.preimage_basicOpen_eq_top` and
`SymmetricAlgebra.nonvanishingLocus_toTwistSections` are stated for
`SymmetricAlgebra.toTwistSections`, the canonical degree-one section of the absolute `𝒪(1)`;
what a section `σ` of `π : 𝐏(ℰ) ⟶ X` hands over is instead a generator of the pullback of the
tautological twist. `chartTwistIso_hom_pullbackSection` says the two agree on the chart over `W`,
and `Stacks.Ample.nonvanishingLocus_congr` then moves the nonvanishing locus across
`chartTwistIso` — the nonvanishing locus of a section is unchanged by an isomorphism of the module
it is a section of. So this is the local step of clause 3 of [Stacks, Tag 0B3V] in the shape a
consumer holding `σ` can use. -/
theorem basicOpen_eq_nonvanishingLocus_pullbackSection (m : Γ(E, W)) :
    (AlgebraicGeometry.Proj.basicOpen (SymmetricAlgebra.grading Γ(X, W) Γ(E, W))
          (SymmetricAlgebra.ι Γ(X, W) Γ(E, W) m) :
        Set (AlgebraicGeometry.Proj (SymmetricAlgebra.grading Γ(X, W) Γ(E, W)))) =
      Stacks.Ample.nonvanishingLocus
        ((Scheme.Modules.pullback (chartMap E hqc hW)).obj
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc))
        (Scheme.Modules.pullbackSection (chartMap E hqc hW)
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)
          ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ W) ⊤
          (top_le_chartMap_preimage E hqc hW)
          ((Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc).val.app
            (op ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ W))
            (Stacks.AlgebraicGeometry.RelativeProjDegreeOne.unitSection
              (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase E W m))) :=
  ((SymmetricAlgebra.nonvanishingLocus_toTwistSections Γ(X, W) Γ(E, W) m).symm.trans
      (congrArg
        (Stacks.Ample.nonvanishingLocus
          (X := AlgebraicGeometry.Proj (SymmetricAlgebra.grading Γ(X, W) Γ(E, W)))
          (twistingSheaf (SymmetricAlgebra.grading Γ(X, W) Γ(E, W)) 1))
        (chartTwistIso_hom_pullbackSection E hqc hW m).symm)).trans
    (Stacks.Ample.nonvanishingLocus_congr (chartTwistIso E hqc hW) _)

/-- **A section of `π` whose pullback of the tautological map generates everywhere covers the
whole chart over `W`.** With `D₊(ι m)` identified as the nonvanishing locus by
`basicOpen_eq_nonvanishingLocus_pullbackSection`, a pulled-back tautological section that
vanishes nowhere on `Proj(Sym_A M)` forces that standard open to be everything. This is the
conclusion of `Stacks.ProjectiveBundleConormal.preimage_basicOpen_eq_top` read at the chart
itself, where the morphism to `Proj(Sym_A M)` is the identity. -/
theorem basicOpen_eq_top_of_forall_mem_nonvanishingLocus (m : Γ(E, W))
    (hs : ∀ y : AlgebraicGeometry.Proj (SymmetricAlgebra.grading Γ(X, W) Γ(E, W)),
      y ∈ Stacks.Ample.nonvanishingLocus
        ((Scheme.Modules.pullback (chartMap E hqc hW)).obj
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc))
        (Scheme.Modules.pullbackSection (chartMap E hqc hW)
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)
          ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ W) ⊤
          (top_le_chartMap_preimage E hqc hW)
          ((Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc).val.app
            (op ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ W))
            (Stacks.AlgebraicGeometry.RelativeProjDegreeOne.unitSection
              (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase E W m)))) :
    AlgebraicGeometry.Proj.basicOpen (SymmetricAlgebra.grading Γ(X, W) Γ(E, W))
      (SymmetricAlgebra.ι Γ(X, W) Γ(E, W) m) = ⊤ := by
  refine TopologicalSpace.Opens.ext
    (((basicOpen_eq_nonvanishingLocus_pullbackSection E hqc hW m).trans
      (Set.eq_univ_of_forall hs)).trans ?_)
  simp

/-! ### The chart comparison under a further pullback -/

/-- **The chart comparison of twists, moved under a further pullback and off `⊤` of the chart.**
Let `g` be any morphism into the chart `Proj(Γ(W, Sym ℰ))` of the bundle over `W`. Then over
every open `U` of the source the pullback along `g` of
`Stacks.ProjectiveBundle.chartTwistIso` carries the pullback along `g` of the section that
`projectiveBundle_chartTwistIso_hom_pullbackSection` computes to the pullback along `g` of
`chartDegreeOneSection`.

Nothing of `g` enters: this is
`AlgebraicGeometry.Scheme.Modules.pullbackSection_naturality` at the morphism of modules
`Stacks.ProjectiveBundle.chartTwistIso E hqc hW |>.hom`, followed by
`projectiveBundle_chartTwistIso_hom_pullbackSection` under the resulting pullback. It is stated
at an opaque `g` on purpose: the morphisms a consumer substitutes — `chartProjMap` here,
`Stacks.RelativeProj.localChartMap` in
`StacksFrontier/AlgebraicGeometry/ProjectiveBundle/LocalChartPinning.lean` — are then bare
`exact`s, and the chart layer of the bundle is never unfolded during elaboration. -/
theorem pullback_chartTwistIso_hom_pullbackSection {Y : Scheme.{u}}
    (g : Y ⟶ AlgebraicGeometry.Proj ((schemeSheafGradedAlgebra E hqc).grading W))
    (U : Y.Opens) (hU : U ≤ g ⁻¹ᵁ ⊤) (m : Γ(E, W)) :
    ((Scheme.Modules.pullback g).map
          (Stacks.ProjectiveBundle.chartTwistIso E hqc hW).hom).val.app (op U)
        (Scheme.Modules.pullbackSection g
          ((Scheme.Modules.pullback
              ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart W hW)).obj
            (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)) ⊤ U hU
          (Scheme.Modules.pullbackSection
            ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart W hW)
            (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)
            ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ W) ⊤
            (top_le_chart_preimage E hqc hW)
            ((Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc).val.app
              (op ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ W))
              (Stacks.AlgebraicGeometry.RelativeProjDegreeOne.unitSection
                (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase E W m)))) =
      Scheme.Modules.pullbackSection g
        (twistingSheaf ((schemeSheafGradedAlgebra E hqc).grading W) 1) ⊤ U hU
        (chartDegreeOneSection E hqc hW m) :=
  pullback_chartTwistIso_hom_pullbackSection_aux E hqc hW g U hU m

/-- **`chartDegreeOneSection` is the degree-one section of the image of `m` under the degree-one
generator of `Sym ℰ`.** The chart of `𝐏(ℰ)` over `W` enters `chartDegreeOneSection` only through
`chartPiece`, and `symmetricAlgebraGen_app` says `chartPiece` is the value over `W` of the
generator `ℰ ⟶ Sym¹(ℰ)`. So the section is written in a vocabulary with no `W`-affineness and no
graded comparison in it — which is the spelling
`Stacks.RelativeProj.localDegreeOne` is defined by, and hence the one the pinning match of
`StacksFrontier/AlgebraicGeometry/ProjectiveBundle/LocalChartPinning.lean` is stated on. -/
theorem chartDegreeOneSection_eq_degreeSection (m : Γ(E, W)) :
    chartDegreeOneSection E hqc hW m =
      degreeSection ((schemeSheafGradedAlgebra E hqc).grading W) 1
        ⟨DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces W) 1
            ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op W) m),
          (schemeSheafGradedAlgebra E hqc).of_mem_grading W _⟩ :=
  congrArg (degreeSection ((schemeSheafGradedAlgebra E hqc).grading W) 1)
    (Subtype.ext
      (congrArg (DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces W) 1)
        (symmetricAlgebraGen_app E hqc hW m).symm))

end Stacks.ProjectiveBundleConormal

end
