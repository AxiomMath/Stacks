module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjFunctorSurjective
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineQuadrupleRoundTrip

/-!
# A morphism into `U_d` is the classifying morphism of the class it determines

Let `S` be an **affine** scheme, `𝒜` a graded `𝒪_S`-algebra with quasi-coherent homogeneous
pieces (Situation 01NN), `A = Γ(S, 𝒜)` its graded ring of global sections, `d ≥ 1`, `T` a test
scheme and `U_d ⊆ Proj(A)` the open of Equation 27.12.0.1. [Stacks, Tag 01NU] asserts that `U_d`
represents the functor `F_d` of strict equivalence classes of quadruples of Section 01NS. Both
maps of the asserted bijection are already constructed:

* `F_d(T) → Mor(T, U_d)` is
  `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.classifyingHomOfClass`;
* `Mor(T, U_d) → F_d(T)` is
  `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.AffineTripleSections.fdOfHom`, which pulls the
  universal family of [Stacks, Tag 01N9] back along the morphism and turns the resulting triple
  of Section 01N4 into a quadruple.

**This file proves that one of the two composites is the identity**: starting from a morphism
`φ : T ⟶ U_d`, forming its class in `F_d(T)` and classifying that class again returns `φ`.

The proof is three steps, each of which is already available:

* the quadruple `fdOfHom` builds has, as its own induced triple, the pulled-back universal family
  it was built from — that is the round trip
  `...AffineTripleSections.veroneseSections_twisting`, so no new comparison of triples is needed;
* the classification of [Stacks, Tag 01N8] is natural in the test scheme
  (`Stacks.AlgebraicGeometry.ProjClassifyingPullback.classifyingHom_pullbackSections`);
* the universal family classifies the identity of `U_d`
  (`...ProjClassifyingPullback.classifyingHom_universalVeroneseSections`).

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.classifyingHom_quadrupleOfHom`: **the
  classifying morphism of the quadruple a morphism `φ : T ⟶ U_d` gives rise to is `φ`.**
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.classifyingHomOfClass_fdOfHom`: the
  same statement read on strict equivalence classes — the composite
  `Mor(T, U_d) → F_d(T) → Mor(T, U_d)` is the identity. Equivalently, `fdOfHom` is injective and
  `classifyingHomOfClass` is surjective.

## What is not here

The **other** composite, `F_d(T) → Mor(T, U_d) → F_d(T)`, is not here either, but it is no longer
missing: it is `...RelativeProjQcohSheaf.Quadruple.fdOfHom_classifyingHomOfClass` of
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/AffineQuadrupleBijection.lean`, which
consumes the theorem below, and the two composites are assembled there into the bijection
`...RelativeProjQcohSheaf.Quadruple.fdEquiv`.

The representability of `F_d` asserted by [Stacks, Tag 01NU] is **not** in this file, and
nothing below carries an attribute claiming it; it is
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.representableByDegreeOpen` of
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/AffineFdRepresentable.lean`. The one thing
between the bijection and the representability was **naturality in `T`**, which is what turns
the bijection into a `CategoryTheory.Functor.RepresentableBy` for
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.functor`. The triple-level naturality is
proved (`...ProjClassifyingPullback.classifyingHom_pullbackSections`, used below), and that the
identification `F_d = F_d^{triples}` of this directory is itself natural, i.e.
`veroneseSections (P.twisting.pullback g)
= ProjTriplePullback.pullbackSections _ (veroneseSections P.twisting) g`, is
`...RelativeProjQcohSheaf.veroneseSections_pullback` there, unconditionally. See the naturality
paragraph of
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/AffineQuadrupleRoundTrip.lean` for what it
cost.

## Implementation notes

The statement lives in its own module rather than at the end of
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/AffineQuadrupleRoundTrip.lean` because the
one import it adds — `StacksFrontier/AlgebraicGeometry/Constructions/ProjFunctorSurjective.lean`,
where the triple-level naturality lives — brings further monoidal instances into scope, and with
them instance synthesis in that file picks a different monoidal structure on sheaves of modules:
`...RelativeProjQcohSheaf.powCompare_one_comp_onePowIso` then fails with `failed to synthesize
instance of type class MonoidalCategory (SheafOfModules
(SheafOfModules.TensorSheafification.structureSheaf T.presheaf ⋯))`. Nothing here mentions a
tensor power, so the extra instances are harmless at this level.

`Stacks.AlgebraicGeometry.ProjTripleClassifying.classifyingHom` takes the generation condition as
an argument whose type mentions the graded map, so rewriting the graded map inside it is not a
`rw`; `classifyingHom_congr` below does it by `subst` followed by definitional proof
irrelevance.

## References

* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Tag 01N9](https://stacks.math.columbia.edu/tag/01N9)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Proj (degreeOpen)
open Stacks.AlgebraicGeometry.MorphismToProjUniversal (psiSection)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (VeroneseSections)
open Stacks.AlgebraicGeometry.ProjDegreeOpenUniversalTriple (universalVeroneseSections
  iSup_nonvanishingOpen_psiSection_universalVeroneseSections_eq_top)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.NonvanishingOpen (nonvanishingOpen)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {T S : Scheme.{u}} {B : SheafGradedAlgebra S} {k : ℕ}

/-- **Rewriting the graded map inside a classifying morphism.** The generation condition
`Stacks.AlgebraicGeometry.ProjTripleClassifying.classifyingHom` takes is a proposition whose
statement mentions the graded map, so an equality of graded maps cannot be rewritten under it;
after `subst` the two generation conditions are proofs of the same proposition and the two sides
are definitionally equal. -/
private theorem classifyingHom_congr {Y : Scheme.{u}} {N : Y.Modules}
    [Stacks.Ample.IsInvertibleModule Y N]
    (hk : 0 < k) {χ χ' : VeroneseSections (B.grading (⊤ : S.Opens)) k N} (h : χ = χ')
    (hg : ⨆ g : B.grading (⊤ : S.Opens) k,
      nonvanishingOpen Y N (psiSection (B.grading (⊤ : S.Opens)) χ g) = ⊤)
    (hg' : ⨆ g : B.grading (⊤ : S.Opens) k,
      nonvanishingOpen Y N (psiSection (B.grading (⊤ : S.Opens)) χ' g) = ⊤) :
    Stacks.AlgebraicGeometry.ProjTripleClassifying.classifyingHom
          (B.grading (⊤ : S.Opens)) hk χ hg
      = Stacks.AlgebraicGeometry.ProjTripleClassifying.classifyingHom
          (B.grading (⊤ : S.Opens)) hk χ' hg' := by
  subst h
  rfl

/-- **Stacks Project, Tag 01NU: the classifying morphism of the quadruple a morphism
`φ : T ⟶ U_d` gives rise to is `φ` itself.** Let `S` be affine, `𝒜` a graded `𝒪_S`-algebra with
quasi-coherent homogeneous pieces (Situation 01NN), `d ≥ 1`, `A = Γ(S, 𝒜)` and
`U_d ⊆ Proj(A)` the open of Equation 27.12.0.1.
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.AffineTripleSections.quadrupleOfHom` turns
`φ : T ⟶ U_d` into a quadruple of Section 01NS, and
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.classifyingHom` turns a quadruple back
into a morphism `T ⟶ U_d`; this says the composite is the identity of `Mor(T, U_d)`.

Three inputs, all of them already proved: the quadruple's own induced triple is the pulled-back
universal family it was built from
(`...AffineTripleSections.veroneseSections_twisting`), the classification of [Stacks, Tag 01N8]
is natural in the test scheme
(`Stacks.AlgebraicGeometry.ProjClassifyingPullback.classifyingHom_pullbackSections`), and the
universal family of [Stacks, Tag 01N9] classifies the identity of `U_d`
(`...ProjClassifyingPullback.classifyingHom_universalVeroneseSections`). -/
theorem Quadruple.classifyingHom_quadrupleOfHom [IsAffine S] (hk : 0 < k)
    (hqc : ∀ n : ℤ, ((situationAlgebra B).piece n).IsQuasicoherent)
    (φ : T ⟶ (degreeOpen (B.grading (⊤ : S.Opens)) k).toScheme) :
    Quadruple.classifyingHom hk hqc (AffineTripleSections.quadrupleOfHom B φ hk) = φ := by
  refine Eq.trans (classifyingHom_congr hk
      (AffineTripleSections.veroneseSections_twisting B
        (AffineTripleSections.pullbackUniversalSections B φ)
        (AffineTripleSections.iSup_nonvanishingOpen_pullbackUniversalSections B φ) hk)
      (Quadruple.iSup_nonvanishingOpen_psiSection_eq_top hqc
        (AffineTripleSections.quadrupleOfHom B φ hk))
      (AffineTripleSections.iSup_nonvanishingOpen_pullbackUniversalSections B φ)) ?_
  refine Eq.trans (ProjClassifyingPullback.classifyingHom_pullbackSections
      (B.grading (⊤ : S.Opens)) hk (universalVeroneseSections (B.grading (⊤ : S.Opens)) k)
      (iSup_nonvanishingOpen_psiSection_universalVeroneseSections_eq_top
        (B.grading (⊤ : S.Opens)) k) φ) ?_
  rw [ProjClassifyingPullback.classifyingHom_universalVeroneseSections
      (B.grading (⊤ : S.Opens)) k hk, Category.comp_id]

/-- **Stacks Project, Tag 01NU: the composite `Mor(T, U_d) → F_d(T) → Mor(T, U_d)` is the
identity.** `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.AffineTripleSections.fdOfHom` sends a
morphism `φ : T ⟶ U_d` to the class in `F_d(T)` of the quadruple it gives rise to, and
`Quadruple.classifyingHomOfClass` sends a class back to a morphism; classifying the class of `φ`
returns `φ`.

This is `Quadruple.classifyingHom_quadrupleOfHom` read on the quotient, on which
`Quadruple.classifyingHomOfClass` is `Quotient.lift` of `Quadruple.classifyingHom`. It says that
one of the two composites of [Stacks, Tag 01NU]'s asserted bijection is the identity:
equivalently, that `fdOfHom` is injective and `classifyingHomOfClass` surjective. -/
theorem Quadruple.classifyingHomOfClass_fdOfHom [IsAffine S] (hk : 0 < k)
    (hqc : ∀ n : ℤ, ((situationAlgebra B).piece n).IsQuasicoherent)
    (φ : T ⟶ (degreeOpen (B.grading (⊤ : S.Opens)) k).toScheme) :
    Quadruple.classifyingHomOfClass hk hqc (AffineTripleSections.fdOfHom B φ hk).2 = φ :=
  Quadruple.classifyingHom_quadrupleOfHom hk hqc φ

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
