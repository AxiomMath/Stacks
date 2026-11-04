module

public import StacksFrontier.AlgebraicGeometry.ProjBundleProjectiveSpace.Descent
public import StacksFrontier.AlgebraicGeometry.FiniteMorphismProjective.AffineBase
public import StacksFrontier.AlgebraicGeometry.SymAlgebraQcohPieces.Basic

/-!
# Base change of a relative homogeneous spectrum, reduced to its charts

Tag 0B3V's sixth labelled assertion is the *base projection* of the canonical base-change
comparison of projective bundles: for `g : X' ⟶ X` and `E' ≅ g^*E` there is an isomorphism
`P(E') ≅ X' ×_X P(E)`, and it is an isomorphism **over `X'`**. The comparison itself is a
base-change isomorphism for the relative homogeneous spectrum of a quasi-coherent graded algebra
along an arbitrary morphism of bases, and this repository does not construct one; see
`Not done here` for the measurement.

This file does the part that is available: it **reduces that global assertion to chart-level
data**, by composing the uniqueness half of Tag 01NQ
(`Stacks.AlgebraicGeometry.RelativeProjDescent.ChartFamily`) with the fibre product
`X' ×_X P(E)` as the candidate scheme. A chart family on the fibre product is exactly a
family of chart isomorphisms over the affine opens of the new base, and it yields the labelled
assertion with nothing further to prove.

## Main results

* `Stacks.ProjBundleBaseChangeReduction.exists_iso_pullback_of_chartFamily`: **the reduction.**
  A chart family for `A'` on `X' ×_X P`, over the first projection, gives an isomorphism
  `Proj_{X'}(A') ≅ X' ×_X P` whose composite with the first projection is the structure
  morphism of `Proj_{X'}(A')`.
* `Stacks.ProjBundleBaseChangeReduction.exists_iso_pullback_of_isAffine`: over an **affine** new
  base a single chart suffices — one isomorphism `Proj Γ(X', A') ≅ X' ×_X P` over `X'` gives the
  same conclusion, with no compatibility to check.
* `Stacks.ProjBundleBaseChangeReduction.exists_iso_pullback_schemeProjectiveBundle`: the two
  above at the objects of Tag 0B3V, the projective bundle
  `Stacks.SymGraded.schemeProjectiveBundle` of a quasi-coherent module on an arbitrary scheme.
  The conclusion is **Tag 0B3V's sixth labelled assertion**, read as the existence of an
  isomorphism with the stated base projection.

## Implementation notes

**Why the conclusion is an existential and not an equation about a construction.** The
comparison `P(E') ≅ X' ×_X P(E)` is not constructed here, so the labelled assertion cannot be
stated as an equation about it. What the label asserts is that *some* isomorphism to the fibre
product has the given base projection, and that is what is stated here. The existence of the
comparison alone would be vacuous: a bare existence of data is satisfied by any term, so the
property is carried in the same statement as the data.

**Every hypothesis the proof consumes is in the signature.** The morphism of bases `g` occurs in
the fibre product, so the chart family's type mentions it; the comparison `hE : E' ≅ g^*E` is
*not* consumed by the reduction and is therefore not a hypothesis of it. `hE` is what a consumer
needs in order to *build* the chart family, and it appears in the signature of the chart-level
residue recorded below, not here.

**The two chart-level interfaces differ in what they must check.**
`Stacks.AlgebraicGeometry.RelativeProjDescent.ChartFamily` asks for a chart over *every* affine
open of the new base, each cartesian over its open, together with compatibility with the
transition morphisms. Over an affine new base
`Stacks.Tag0B3I.projTopIso` collapses the whole family to the chart at the top open, which is
why the second result needs no compatibility hypothesis at all.

**Universes.** Monomorphic in the scheme universe, as every object here is: a
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra` records its graded rings of
sections in `CommRingCat.{u}` and the glued scheme is a `Scheme.{u}`.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)

## Not done here

**No tag of 0B3V is attached and none is earned**: every result below carries a hypothesis that
Tag 0B3V does not have — the chart family, or the single chart over an affine base. The sixth
labelled assertion of Tag 0B3V is *not* proved here, so the tag is not attached.

**What remains.** What the chart family needs, for an affine open
`W` of `X'` contained in `g ⁻¹ᵁ U` with `U` an affine open of `X`, is an isomorphism of **graded
rings**
`Γ(W, Sym(E')) ≅ Γ(X', W) ⊗_{Γ(X, U)} Γ(U, Sym(E))`,
after which the Proj-level chart isomorphism is
`Stacks.AlgebraicGeometry.ProjChartBaseChange.isIso_projCompare`, which is proved and is stated
for an arbitrary graded algebra and an arbitrary base change of its degree-zero part. Of that
graded-ring isomorphism:

* the pure-algebra half is available — `SymPow.symAlgBaseChangeEquiv` and `SymPow.baseChangeEquiv`
  in `StacksFrontier.LinearAlgebra.SymmetricPower.BaseChange`;
* the sections half, `Γ(W, g^*E) ≅ Γ(X', W) ⊗_{Γ(X, U)} Γ(U, E)` for an arbitrary morphism `g`,
  is available as `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`
  (`StacksFrontier/AlgebraicGeometry/PullbackSections/Affine.lean`), normalised on `1 ⊗ a` by
  `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso_one_tmul`;
* the identification of `Γ(W, Sym(E'))` with the symmetric algebra of `Γ(W, E')` over `Γ(X', W)`
  is absent as a statement, although its ingredients are available in
  `Stacks.SymGraded.AffinePieces` (`sheafificationIsoTilde` and
  `isQuasicoherent_restrict_fromSpec_piece`);
* `Stacks.SymGraded.isBaseChange_gradedRestrictₗ_int` is **not** this statement: its hypotheses
  are an inclusion `U ≤ U'` of affine opens of one scheme, with no morphism of bases anywhere.

**A second, structural part of the residue, and it is not the graded-ring isomorphism.**
`ChartFamily` demands a chart over *every* affine open of `X'`, while the chart-level engine
above supplies one only for an affine open whose image lies in an affine open of `X`. Those form
a basis of `X'` and not all of its affine opens, so the graded-ring isomorphism alone does not
produce a `ChartFamily`. Neither of the two ways around this is available:

* a basis-restricted form of `ChartFamily` does not exist, and cannot be had cheaply: the colimit
  defining `Stacks.AlgebraicGeometry.RelativeProjGlue.relativeProj` is indexed by all of
  `AlgebraicGeometry.Scheme.AffineZariskiSite`, so a morphism out of it is a cocone on the whole
  site, and the small affine opens are not cofinal for the upward inclusions that are the site's
  arrows;
* proving the comparison over each affine open `W` of `X'` separately, which is what
  `exists_iso_pullback_of_isAffine` would be applied to along `W.ι ≫ g`, needs the *restriction*
  of `A'` to `W` as a `SheafGradedAlgebra W.toScheme`. That restriction **does** exist —
  `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.restrict`, along any open
  immersion of the base, with `restrict_grading` making `(A'|_W).grading Z` definitionally
  `A'.grading (W.ι ''ᵁ Z)`. What is missing is the step after it: the relative homogeneous spectrum of a
  restricted algebra is nowhere compared with the corresponding preimage open —
  `Stacks.AlgebraicGeometry.RelativeProj.relativeProj` is never applied to a restricted or
  pulled-back algebra anywhere in the library — so the per-`W` comparisons cannot yet be assembled.

**The pullback of a graded algebra along a morphism of bases also exists**: `...RelativeProjBridge.SheafGradedAlgebra.pullback` takes a
`SheafGradedAlgebra S` and an *arbitrary* `g : X ⟶ S` to a `SheafGradedAlgebra X`, with
`pullback_piece` identifying its pieces with the inverse images of the pieces by `rfl`. For an
open immersion the two spellings are compared by
`...RelativeProjQcohSheaf.restrictPullbackUnitalHom`, every component of which is invertible by
`isIso_restrictPullbackUnitalHom_app`. What this file does not do is *use* either of them: the new
base's algebra is supplied independently, exactly as Tag 0B3V supplies `E'` with a comparison
`hE` rather than as a pullback.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj

namespace Stacks.ProjBundleBaseChangeReduction

universe u

variable {X X' P : Scheme.{u}} (g : X' ⟶ X) (A' : SheafGradedAlgebra X') (π : P ⟶ X)

/-- **The reduction of the base-change comparison to its charts.** If the fibre product
`X' ×_X P`, with its first projection to `X'`, carries the charts of the relative homogeneous
spectrum of `A'` — one over each affine open of `X'`, cartesian over that open and compatible
with the transition morphisms — then the relative homogeneous spectrum of `A'` is isomorphic to
`X' ×_X P` by an isomorphism over `X'`.

This is the uniqueness half of Tag 01NQ, `RelativeProjDescent.ChartFamily`, applied to the fibre
product; the content of the base-change comparison is entirely in the chart family. -/
public theorem exists_iso_pullback_of_chartFamily
    (c : Stacks.AlgebraicGeometry.RelativeProjDescent.ChartFamily A'.toGradedAlgebra (pullback g π)
      (pullback.fst g π)) :
    ∃ e : (relativeProj A').scheme ≅ pullback g π,
      e.hom ≫ pullback.fst g π = (relativeProj A').toBase :=
  ⟨c.iso, c.iso_hom_comp⟩

/-- **Over an affine new base a single chart suffices.** One isomorphism from the absolute `Proj`
of the graded ring of global sections of `A'` to the fibre product, compatible with the two
structure morphisms to `X'`, already gives the base-change comparison over `X'`.

Over an affine base the chart at the top open of `Stacks.AlgebraicGeometry.RelativeProj`'
glued scheme is an isomorphism (`Stacks.Tag0B3I.projTopIso`), so no family and no compatibility
is involved. -/
public theorem exists_iso_pullback_of_isAffine [IsAffine X']
    (e : AlgebraicGeometry.Proj (A'.grading ⊤) ≅ pullback g π)
    (he : e.hom ≫ pullback.fst g π =
      projInclusionToOpen A' ⊤ (isAffineOpen_top X') ≫ (⊤ : X'.Opens).ι) :
    ∃ e' : (relativeProj A').scheme ≅ pullback g π,
      e'.hom ≫ pullback.fst g π = (relativeProj A').toBase := by
  refine ⟨(Stacks.FiniteMorphismProjective.projTopIso A' (relativeProj A')).symm ≪≫ e, ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, he,
    ← Stacks.FiniteMorphismProjective.projTopIso_hom_toBase A' (relativeProj A'),
      Iso.inv_hom_id_assoc]

/-! ### At the objects of Tag 0B3V -/

/-- **The statement of Tag 0B3V's sixth label, from a chart family.** For a quasi-coherent module
`E` on `X` and a quasi-coherent module `E'` on `X'` compared with its pullback, a chart family
for the symmetric algebra of `E'` on the fibre product `X' ×_X P(E)` gives an isomorphism
`P(E') ≅ X' ×_X P(E)` whose composite with the projection to `X'` is the projection of `P(E')`.

The projective bundle here is `Stacks.SymGraded.schemeProjectiveBundle`, which is by definition
the relative homogeneous spectrum of the sheafified sectionwise symmetric algebra, so this is the
previous result with no further argument. The quasi-coherence hypotheses on the homogeneous
pieces are the ones the bundle is built from, and they follow from the quasi-coherence of the
modules by `Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent`. -/
public theorem exists_iso_pullback_schemeProjectiveBundle (E : X.Modules)
    (hqc : Stacks.SymGraded.IsQuasicoherentPieces E) (E' : X'.Modules)
    (hqc' : Stacks.SymGraded.IsQuasicoherentPieces E')
    (c : Stacks.AlgebraicGeometry.RelativeProjDescent.ChartFamily
      (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc').toGradedAlgebra
      (pullback g (Stacks.SymGraded.schemeProjectiveBundleToBase E hqc))
      (pullback.fst g (Stacks.SymGraded.schemeProjectiveBundleToBase E hqc))) :
    ∃ e : (Stacks.SymGraded.schemeProjectiveBundle E' hqc').scheme ≅
        pullback g (Stacks.SymGraded.schemeProjectiveBundleToBase E hqc),
      e.hom ≫ pullback.fst g (Stacks.SymGraded.schemeProjectiveBundleToBase E hqc) =
        Stacks.SymGraded.schemeProjectiveBundleToBase E' hqc' :=
  exists_iso_pullback_of_chartFamily g _ _ c

end Stacks.ProjBundleBaseChangeReduction

end
