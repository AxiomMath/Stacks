module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.PresheafCohomologyComparison
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequence

/-!
# The spectral sequence of a hypercovering of a presheaf

Let `C` be a site with equalizers and fibre products, `G` a presheaf on `C`, `K` a hypercovering
of `G` ([Stacks, Tag 09VU]) and `F` a sheaf of abelian groups on `C`.  The last clause of
[Stacks, Tag 09VX] asserts that there is a first-quadrant `E₂` cohomological spectral sequence,
functorial in `F`, whose second page is `Ȟ^p(K, H̲^q(F))` and which converges to `H^{p+q}(G, F)`,
and that it is functorial in the hypercovering `K` as well.
`PresheafHypercoveringSpectralSequenceData` bundles the first three of these and
`presheafHypercoveringSpectralSequence` supplies it; the functoriality in `K` is
`PresheafHypercoveringSpectralSequenceFunctoriality`, supplied by
`presheafHypercoveringSpectralSequenceFunctoriality`.

## The construction

Choose an injective resolution `F ⟶ I^•` and form the double complex

```
A^{p,q}(F) = s(I^p(K))^q,
```

the `q`-th term of the complex of sections of `K` with coefficients in `I^p`, with the
**resolution degree outer and the hypercovering degree inner**.  That orientation is forced: the
second spectral sequence of a double complex has `''E_2^{p,q} = H^p_{II}(H^q_I(A^{•,•}))` and
`H^q_I` differentiates the *outer* index, so it is the resolution degree that has to come first if
`''E_2^{p,q}` is to be hypercovering cohomology of a derived functor.  The inner index is extended
by zero from `ℕ` to `ℤ`, which is what makes the first-quadrant vanishing immediate.

The second page is identified in two steps.  First `HomologicalComplex₂.pageTwoNatIso` gives
`''E_2^{p,q} ≅ H^p_{II}(H^q_I(A^{•,•}))` ([Stacks, Tag 0130]).  Then the coefficient comparison
`hypercoverPresheafDoubleHomologyNatIso` rewrites the right-hand side as `Ȟ^p(K, H^q(-))`: the
functor `FormalCoproduct.cochainComplexFunctor K` is *exact on presheaves*, hence commutes with
homology, so taking homology of the double complex in the resolution direction is the same as
taking homology of the complex of presheaves underlying the resolution.  At the chosen injective
resolution that homology is `H̲^q(F)`, the `q`-th right derived functor of the inclusion of
abelian sheaves into presheaves ([Stacks, Tag 01ER]).

The abutment is the cohomology of the total complex, filtered by the hypercovering degree, which
`Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.ofFunctorialFilteredComplex` turns into a
functorial filtered abutment; `hypercoverPresheafAbutmentIso` then identifies it with
`R^nΓ(G, -)` through [Stacks, Tag 0133], the four hypotheses of which are
`hypotheses_presheafSectionsAug` -- the positive-degree acyclicity of the sections complex of an
injective sheaf is [Stacks, Tag 09VW] and the degree-zero clause is [Stacks, Tag 09VV] in
canonical-map form, and both enter through `quasiIso_hypercoverPresheafAugmentation`.

This file is the hypercovering-of-a-presheaf analogue of
`StacksFrontier/CategoryTheory/Sites/Hypercovering/SpectralSequence.lean`, which carries out the same
construction for a hypercovering of an *object* and which it mirrors throughout; the generic
exactness statements of that file (`cochainComplexFunctor_preservesHomology`,
`hasExactLimitsOfShape_discrete_addCommGrpCat`, `extendUpNatMapHomologyNatIso`) are reused rather
than restated.

## Main definitions

* `Stacks.CategoryTheory.Hypercovering.presheafCechCohomologyFunctor`: `Ȟ^p(K, -)` on presheaves
  of abelian groups on `C`.
* `Stacks.CategoryTheory.Hypercovering.hypercoverPresheafDoubleFunctor`: the double complex
  `A^{p,q} = s(Y^p(K))^q` of a complex `Y^•` of abelian sheaves.
* `Stacks.CategoryTheory.Hypercovering.hypercoverPresheafDouble`,
  `Stacks.CategoryTheory.Hypercovering.hypercoverPresheafDoubleMap`: the same at the chosen
  injective resolution of a sheaf, with the morphism induced by a morphism of sheaves.
* `Stacks.CategoryTheory.Hypercovering.hypercoverPresheafE₂Functor`,
  `Stacks.CategoryTheory.Hypercovering.hypercoverPresheafSpectralSequenceFunctor`: the resulting
  functorial `E₂` spectral sequence, on `ℤ × ℤ` and then on `ℕ × ℕ`.
* `Stacks.CategoryTheory.Hypercovering.hypercoverPresheafFiltrationFunctor`: the cohomology of
  the total complex with the filtration by the hypercovering degree, as a functor.
* `Stacks.CategoryTheory.Hypercovering.hypercoverPresheafFunctorialAbutment` and
  `Stacks.CategoryTheory.Hypercovering.hypercoverPresheafAbutment`: its functorial filtered
  abutment, abutting to the cohomology of the total complex and then to `R^nΓ(G, -)`.
* `Stacks.CategoryTheory.Hypercovering.PresheafHypercoveringSpectralSequenceData`: the data the
  spectral sequence clause of [Stacks, Tag 09VX] asserts.
* `Stacks.CategoryTheory.Hypercovering.presheafHypercoveringSpectralSequence`: that data, for a
  hypercovering of a presheaf.
* `Stacks.CategoryTheory.Hypercovering.hypercoverPresheafSpectralSequenceFunctorMap`: the morphism
  of spectral sequences induced by a morphism of hypercoverings of `G`.
* `Stacks.CategoryTheory.Hypercovering.PresheafHypercoveringSpectralSequenceFunctoriality` and
  `Stacks.CategoryTheory.Hypercovering.presheafHypercoveringSpectralSequenceFunctoriality`: the
  functoriality in `K` asserted by the spectral sequence clause of [Stacks, Tag 09VX], and its
  proof.

## Main results

* `Stacks.CategoryTheory.Hypercovering.hypercoverPresheafDoubleHomologyNatIso`: the coefficient
  comparison.
* `Stacks.CategoryTheory.Hypercovering.hypercoverPresheafPageTwoIso`: the second page is
  `Ȟ^p(K, H̲^q(F))`, naturally in `F`.
* `Stacks.CategoryTheory.Hypercovering.hypotheses_presheafSectionsAug`: the four hypotheses of
  [Stacks, Tag 0133] for the double complex.
* `Stacks.CategoryTheory.Hypercovering.hypercoverPresheafAbutmentIso`: the abutment is
  `R^nΓ(G, -)`, naturally in `F`.

## Implementation notes

Sections over the presheaf `G` are `Hom(**Z**_G^♯, -)`, which is
`Stacks.CategoryTheory.Hypercovering.presheafSectionsFunctor`; cohomology over `G` is its right
derived functor.  The cohomology presheaf `H̲^q` is represented by the right derived functors of
the inclusion `sheafToPresheaf` of abelian sheaves into presheaves, which is [Stacks, Tag 01ER]'s
description of it.  Both are Mathlib's `CategoryTheory.Functor.rightDerived`, so both are computed
from the same chosen injective resolutions as the double complex.

Unlike the case of a hypercovering of an object, sheafification and existence of enough
injectives at `AddCommGrpCat.{max (max u v) (max q w)}` are taken as *hypotheses*, as they are by
the other carriers of this chapter's presheaf-side tags.  Both are theorems for every site whose
objects lie in `Type u` and whose morphisms in `Type v`
(`CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat` and
`CategoryTheory.Sheaf.enoughInjectives_addCommGrpCat`), but they cannot be supplied as local
instances here: the coefficient universe is `max (max u v) (max q w)`, in which the parameters `q`
and `w` occur only inside a `max`, so instance search cannot recover them and reports the universe
constraint as stuck.  Discharging them at a use site is a one-line `letI`.

Functoriality in the hypercovering is provided here and, for a hypercovering of an object, by
`hypercoverSpectralSequenceHypercoveringFunctor` in the file mirrored above.  It is the
assignment `K ↦ (the spectral sequence of K)` that is functorial, which is what the source
asserts; that the second-page identification `hypercoverPresheafPageTwoIso` and the abutment
`hypercoverPresheafAbutment` are themselves natural in `K` is a finer statement and is not proved.
The morphisms allowed are all morphisms of the underlying simplicial semi-representable objects,
not only those compatible with the augmentations to `G`.

## References

* [Stacks Project, Tag 09VX](https://stacks.math.columbia.edu/tag/09VX)
* [Stacks Project, Tag 09VU](https://stacks.math.columbia.edu/tag/09VU)
* [Stacks Project, Tag 09VV](https://stacks.math.columbia.edu/tag/09VV)
* [Stacks Project, Tag 09VW](https://stacks.math.columbia.edu/tag/09VW)
* [Stacks Project, Tag 01ER](https://stacks.math.columbia.edu/tag/01ER)
* [Stacks Project, Tag 0130](https://stacks.math.columbia.edu/tag/0130)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SimplicialObject.Augmented

universe q w v u

namespace Stacks.CategoryTheory.Hypercovering

/-! ### The Čech cohomology of a hypercovering of a presheaf -/

section Cech

variable {C : Type u} [Category.{v} C] [HasEqualizers C] [HasPullbacks C]
variable (J : Pretopology C) (G : Cᵒᵖ ⥤ Type q) (K : HypercoveringOf.{q, w} J G)

/-- **`Ȟ^p(K, -)`, the `p`-th cohomology of the complex of sections of `K`**, as a functor of a
presheaf of abelian groups on `C`.  This is the coefficient functor appearing on the second page
of [Stacks, Tag 09VX]. -/
def presheafCechCohomologyFunctor (p : ℕ) :
    (Cᵒᵖ ⥤ AddCommGrpCat.{max (max u v) (max q w)}) ⥤
      AddCommGrpCat.{max (max u v) (max q w)} :=
  FormalCoproduct.cochainComplexFunctor K.toSimplicialObject ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat.{max (max u v) (max q w)}
      (ComplexShape.up ℕ) p

/-- The value of `presheafCechCohomologyFunctor` on the presheaf underlying a sheaf `F` is the
Čech cohomology group `Ȟ^p(K, F)` of [Stacks, Tag 09VX], on the nose. -/
@[sga "4 V 2.4.4" "more general"]
lemma presheafCechCohomologyFunctor_obj
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) (p : ℕ) :
    (presheafCechCohomologyFunctor J G K p).obj F.obj = cechCohomology J G K F p := rfl

end Cech

/-! ### The double complex of a complex of abelian sheaves -/

section DoubleComplex

variable {C : Type u} [Category.{v} C] [HasEqualizers C] [HasPullbacks C]
variable (J : Pretopology C) (G : Cᵒᵖ ⥤ Type q) (K : HypercoveringOf.{q, w} J G)

/-- **The double complex of a complex of abelian sheaves, with the inner index in `ℕ`**: in outer
degree `p` the complex of sections `s(Y^p(K))` of the `p`-th term.  The **degree in the given
complex is the outer index and the hypercovering degree the inner one**; see the module
documentation for why that is forced. -/
def hypercoverPresheafDoubleNatFunctor :
    CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) ℤ ⥤
      HomologicalComplex (CochainComplex AddCommGrpCat.{max (max u v) (max q w)} ℕ)
        (ComplexShape.up ℤ) :=
  (SemiRepresentable.sectionsComplexFunctor.{q, w, v, u} J.toGrothendieck
    K.toSimplicialObject).mapHomologicalComplex (ComplexShape.up ℤ)

/-- **The double complex of a complex of abelian sheaves**, over `ℤ × ℤ`: the inner index of
`hypercoverPresheafDoubleNatFunctor` extended by zero. -/
def hypercoverPresheafDoubleFunctor :
    CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) ℤ ⥤
      HomologicalComplex₂ AddCommGrpCat.{max (max u v) (max q w)} (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) :=
  (SemiRepresentable.sectionsComplexIntFunctor.{q, w, v, u} J.toGrothendieck
    K.toSimplicialObject).mapHomologicalComplex (ComplexShape.up ℤ)

/-- `hypercoverPresheafDoubleFunctor` is `hypercoverPresheafDoubleNatFunctor` with the inner index
extended by zero. -/
lemma hypercoverPresheafDoubleFunctor_eq :
    hypercoverPresheafDoubleFunctor J G K =
      hypercoverPresheafDoubleNatFunctor J G K ⋙
        (ComplexShape.embeddingUpNat.extendFunctor
          AddCommGrpCat.{max (max u v) (max q w)}).mapHomologicalComplex (ComplexShape.up ℤ) :=
  rfl

/-- **The double complex vanishes in negative inner degree**, the inner index being extended by
zero from `ℕ`. -/
lemma isZero_hypercoverPresheafDoubleFunctor_X_X_of_inner_neg
    (Y : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) ℤ)
    (p r : ℤ) (hr : r < 0) :
    IsZero ((((hypercoverPresheafDoubleFunctor J G K).obj Y).X p).X r) :=
  SemiRepresentable.isZero_sectionsComplexIntFunctor_obj_X.{q, w, v, u} J.toGrothendieck
    K.toSimplicialObject (Y.X p) r hr

/-- **The double complex vanishes in an outer degree where the given complex does**, the sections
complex functor being additive. -/
lemma isZero_hypercoverPresheafDoubleFunctor_X
    (Y : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) ℤ)
    (p : ℤ) (hp : IsZero (Y.X p)) :
    IsZero (((hypercoverPresheafDoubleFunctor J G K).obj Y).X p) :=
  (SemiRepresentable.sectionsComplexIntFunctor.{q, w, v, u} J.toGrothendieck
    K.toSimplicialObject).map_isZero hp

/-- The extension by zero along `ℕ → ℤ` of a complex vanishes in negative degrees. -/
private lemma isZero_extend_X_of_neg {D : Type*} [Category D] [Preadditive D]
    [HasZeroObject D] (X : CochainComplex D ℕ) (p : ℤ) (hp : p < 0) :
    IsZero ((X.extend ComplexShape.embeddingUpNat).X p) :=
  HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat p
    fun i => by change ((i : ℕ) : ℤ) ≠ p; omega

/-- **First-quadrant vanishing for the double complex** of a complex of abelian sheaves vanishing
in negative degrees: `H^p_{II}(H^r_I(A^{•,•}))` vanishes as soon as `p < 0` or `r < 0`.  In the
first case the complex `H^r_I(A^{•,•})` is zero in inner degree `p`, in the second the outer
complex is zero, hence exact, at `r`. -/
lemma isZero_homologyIIHomologyI_hypercoverPresheafDoubleFunctor
    (Y : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) ℤ)
    (hY : ∀ p : ℤ, p < 0 → IsZero (Y.X p)) (p r : ℤ) (h : p < 0 ∨ r < 0) :
    IsZero ((HomologicalComplex₂.homologyIIHomologyIFunctor
      AddCommGrpCat.{max (max u v) (max q w)} p r).obj
        ((hypercoverPresheafDoubleFunctor J G K).obj Y)) := by
  rcases h with hp | hr
  · refine (Iso.isZero_iff ((HomologicalComplex.homologyFunctor
        AddCommGrpCat.{max (max u v) (max q w)} (ComplexShape.up ℤ) p).mapIso
      ((Functor.mapHomologicalComplexHomologyIso
        (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{max (max u v) (max q w)})
        (ComplexShape.up ℤ) r).app
          ((hypercoverPresheafDoubleNatFunctor J G K).obj Y)))).2 ?_
    exact (HomologicalComplex.ExactAt.of_isZero
      (isZero_extend_X_of_neg _ p hp)).isZero_homology
  · refine Functor.map_isZero (HomologicalComplex.homologyFunctor
      AddCommGrpCat.{max (max u v) (max q w)} (ComplexShape.up ℤ) p) ?_
    exact (HomologicalComplex.ExactAt.of_isZero
      (isZero_hypercoverPresheafDoubleFunctor_X J G K Y r (hY r hr))).isZero_homology

variable [HasSheafify J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}]

/-- **The coefficient half of the second-page identification.**  Taking the homology of the double
complex of a complex of abelian sheaves, first in the resolution direction and then in the
hypercovering direction, is the Čech cohomology of the homology of the complex of *presheaves*
underlying it, naturally in the complex.  This is the statement that the complex-of-sections
functor of `K` commutes with homology, which it does because it is exact on presheaves
(`cochainComplexFunctor_preservesHomology`), together with the fact that extension by zero
does. -/
def hypercoverPresheafDoubleHomologyNatIso (p : ℕ) (r : ℤ) :
    hypercoverPresheafDoubleFunctor J G K ⋙
        HomologicalComplex₂.homologyIIHomologyIFunctor
          AddCommGrpCat.{max (max u v) (max q w)} (p : ℤ) r ≅
      (sheafToPresheaf J.toGrothendieck
            AddCommGrpCat.{max (max u v) (max q w)}).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{max (max u v) (max q w)})
            (ComplexShape.up ℤ) r ⋙
          presheafCechCohomologyFunctor J G K p :=
  haveI := cochainComplexFunctor_preservesHomology.{w}
    (A := AddCommGrpCat.{max (max u v) (max q w)})
    (fun I => hasExactLimitsOfShape_discrete_addCommGrpCat.{max (max u v) q, w} I)
    K.toSimplicialObject
  Functor.isoWhiskerLeft (hypercoverPresheafDoubleNatFunctor J G K)
      (Functor.isoWhiskerRight
          (Functor.mapHomologicalComplexHomologyIso
            (ComplexShape.embeddingUpNat.extendFunctor
              AddCommGrpCat.{max (max u v) (max q w)})
            (ComplexShape.up ℤ) r)
          (HomologicalComplex.homologyFunctor AddCommGrpCat.{max (max u v) (max q w)}
            (ComplexShape.up ℤ) (p : ℤ)) ≪≫
        Functor.isoWhiskerLeft
          (HomologicalComplex.homologyFunctor
            (CochainComplex AddCommGrpCat.{max (max u v) (max q w)} ℕ) (ComplexShape.up ℤ) r)
          (ComplexShape.embeddingUpNat.extendFunctorHomologyIso
            AddCommGrpCat.{max (max u v) (max q w)} p (p : ℤ) rfl)) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        ((sheafToPresheaf J.toGrothendieck
          AddCommGrpCat.{max (max u v) (max q w)}).mapHomologicalComplex (ComplexShape.up ℤ))
        (Functor.mapHomologicalComplexHomologyIso
          (FormalCoproduct.cochainComplexFunctor
            (A := AddCommGrpCat.{max (max u v) (max q w)}) K.toSimplicialObject)
          (ComplexShape.up ℤ) r))
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{max (max u v) (max q w)}
        (ComplexShape.up ℕ) p)

end DoubleComplex

/-! ### The spectral sequence -/

section Sequence

variable {C : Type u} [Category.{v} C] [HasEqualizers C] [HasPullbacks C]
variable (J : Pretopology C) (G : Cᵒᵖ ⥤ Type q) (K : HypercoveringOf.{q, w} J G)
  [HasSheafify J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}]
  [EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)})]

/-- **A chosen injective resolution, extended by zero, vanishes in negative degrees.**  Stated
for an arbitrary abelian category with enough injectives, the degrees of the resolution being
exactly those coming from `ℕ`. -/
lemma isZero_injectiveResolutionExtend_X.{t, s} {D : Type s} [Category.{t} D] [Abelian D]
    [EnoughInjectives D] (F : D) (p : ℤ) (hp : p < 0) :
    IsZero (((ComplexShape.embeddingUpNat.extendFunctor D).obj
      (injectiveResolution F).cocomplex).X p) :=
  isZero_extend_X_of_neg _ p hp

/-- **A chosen injective resolution, extended by zero, is bounded below.** -/
lemma exists_isStrictlyGE_injectiveResolutionExtend.{t, s} {D : Type s} [Category.{t} D]
    [Abelian D] [EnoughInjectives D] (F : D) :
    ∃ n : ℤ, CochainComplex.IsStrictlyGE
      ((ComplexShape.embeddingUpNat.extendFunctor D).obj (injectiveResolution F).cocomplex) n :=
  ⟨0, inferInstanceAs ((injectiveResolution F).cochainComplex.IsStrictlyGE 0)⟩

/-- **The terms of a chosen injective resolution, extended by zero, are injective.** -/
lemma injective_injectiveResolutionExtend_X.{t, s} {D : Type s} [Category.{t} D] [Abelian D]
    [EnoughInjectives D] (F : D) (n : ℤ) :
    Injective (((ComplexShape.embeddingUpNat.extendFunctor D).obj
      (injectiveResolution F).cocomplex).X n) :=
  inferInstanceAs (Injective ((injectiveResolution F).cochainComplex.X n))

/-- **The double complex of an `ℕ`-indexed complex of abelian sheaves**: the complex extended by
zero in the negative degrees, fed to `hypercoverPresheafDoubleFunctor`.  This is the functor the
chosen injective resolution is plugged into. -/
def hypercoverPresheafDoubleOfNatFunctor :
    CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) ℕ ⥤
      HomologicalComplex₂ AddCommGrpCat.{max (max u v) (max q w)} (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) :=
  ComplexShape.embeddingUpNat.extendFunctor
      (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) ⋙
    hypercoverPresheafDoubleFunctor J G K

/-- A homotopy between morphisms of complexes of sheaves induces a homotopy between the induced
morphisms of double complexes: extension by zero carries homotopies to homotopies and the
complex-of-sections functor is additive. -/
def hypercoverPresheafDoubleHomotopy
    {Y Z : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) ℕ}
    {φ ψ : Y ⟶ Z} (H : Homotopy φ ψ) :
    Homotopy ((hypercoverPresheafDoubleOfNatFunctor J G K).map φ)
      ((hypercoverPresheafDoubleOfNatFunctor J G K).map ψ) :=
  (SemiRepresentable.sectionsComplexIntFunctor.{q, w, v, u} J.toGrothendieck
    K.toSimplicialObject).mapHomotopy (H.extend ComplexShape.embeddingUpNat)

/-- **The double complex of a sheaf of abelian groups**: `A^{p,q}(F) = s(I^p(K))^q` for the chosen
injective resolution `I^•(F)` of `F`, with the resolution degree outer. -/
def hypercoverPresheafDouble
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) :
    HomologicalComplex₂ AddCommGrpCat.{max (max u v) (max q w)} (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) :=
  (hypercoverPresheafDoubleOfNatFunctor J G K).obj (injectiveResolution F).cocomplex

/-- The morphism of double complexes attached to a morphism of sheaves: the double complex of a
chosen descent of that morphism to the chosen injective resolutions.  This is functorial only up
to homotopy, which is all `HomologicalComplex₂.e₂FunctorOfHomotopyClasses` needs. -/
def hypercoverPresheafDoubleMap
    {F F' : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}} (f : F ⟶ F') :
    hypercoverPresheafDouble J G K F ⟶ hypercoverPresheafDouble J G K F' :=
  (hypercoverPresheafDoubleOfNatFunctor J G K).map
    (InjectiveResolution.desc f (injectiveResolution F') (injectiveResolution F))

/-- `hypercoverPresheafDoubleMap` sends an identity to a filtered homotopy class of the
identity. -/
lemma filteredHomotopy₂_hypercoverPresheafDoubleMap_id
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) :
    HomologicalComplex₂.FilteredHomotopy₂ (hypercoverPresheafDoubleMap J G K (𝟙 F)) (𝟙 _) :=
  HomologicalComplex₂.filteredHomotopy₂_of_homotopy
    ((hypercoverPresheafDoubleHomotopy J G K
        (InjectiveResolution.descIdHomotopy F (injectiveResolution F))).trans
      (Homotopy.ofEq ((hypercoverPresheafDoubleOfNatFunctor J G K).map_id _)))

/-- `hypercoverPresheafDoubleMap` is multiplicative up to filtered homotopy. -/
lemma filteredHomotopy₂_hypercoverPresheafDoubleMap_comp
    {F F' F'' : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}} (f : F ⟶ F')
    (g : F' ⟶ F'') :
    HomologicalComplex₂.FilteredHomotopy₂ (hypercoverPresheafDoubleMap J G K (f ≫ g))
      (hypercoverPresheafDoubleMap J G K f ≫ hypercoverPresheafDoubleMap J G K g) :=
  HomologicalComplex₂.filteredHomotopy₂_of_homotopy
    ((hypercoverPresheafDoubleHomotopy J G K
        (InjectiveResolution.descCompHomotopy f g (injectiveResolution F)
          (injectiveResolution F') (injectiveResolution F''))).trans
      (Homotopy.ofEq ((hypercoverPresheafDoubleOfNatFunctor J G K).map_comp _ _)))

/-- **The spectral sequence of a hypercovering of a presheaf, on `ℤ × ℤ`**, functorial in the
sheaf: the second spectral sequence of the double complex of an injective resolution, presented
from its second page. -/
def hypercoverPresheafE₂Functor :
    Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)} ⥤
      E₂CohomologicalSpectralSequence AddCommGrpCat.{max (max u v) (max q w)} :=
  HomologicalComplex₂.e₂FunctorOfHomotopyClasses (hypercoverPresheafDouble J G K)
    (hypercoverPresheafDoubleMap J G K) (filteredHomotopy₂_hypercoverPresheafDoubleMap_id J G K)
    (fun f g => filteredHomotopy₂_hypercoverPresheafDoubleMap_comp J G K f g)

/-- The spectral sequence of a sheaf is first quadrant from its second page on. -/
lemma isFirstQuadrant_hypercoverPresheafE₂Functor
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) :
    CategoryTheory.SpectralSequence.IsFirstQuadrant (u := fun r => (r, 1 - r))
      ((hypercoverPresheafE₂Functor J G K).obj F) :=
  HomologicalComplex₂.isFirstQuadrant_e₂SpectralSequence₂Functor _
    (hypercoverPresheafDouble J G K F) fun p q' h =>
      isZero_homologyIIHomologyI_hypercoverPresheafDoubleFunctor J G K _
        (isZero_injectiveResolutionExtend_X F) p q' h

/-- **The `sequence` field of `PresheafHypercoveringSpectralSequenceData`**: the functorial
first-quadrant `E₂` cohomological spectral sequence of the hypercovering `K`, carried on
`ℕ × ℕ`. -/
def hypercoverPresheafSpectralSequenceFunctor :
    Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)} ⥤
      E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{max (max u v) (max q w)} :=
  CategoryTheory.SpectralSequence.natRestrictE₂Comp (hypercoverPresheafE₂Functor J G K)
    (isFirstQuadrant_hypercoverPresheafE₂Functor J G K)

/-! ### The second page -/

/-- **[Stacks, Tag 0130] (6) for the spectral sequence of a hypercovering of a presheaf.**  The
second page of `hypercoverPresheafE₂Functor` at `((p : ℤ), (q' : ℤ))` is
`H^p_{II}(H^{q'}_I(A^{•,•}(F)))`. -/
def hypercoverPresheafPageTwoAppIso (p q' : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) :
    (hypercoverPresheafE₂Functor J G K ⋙
        CategoryTheory.SpectralSequence.pageFunctor _ _ 2 2 ⋙
          HomologicalComplex.eval _ _ ((p : ℤ), (q' : ℤ))).obj F ≅
      (HomologicalComplex₂.homologyIIHomologyIFunctor
        AddCommGrpCat.{max (max u v) (max q w)} (p : ℤ) (q' : ℤ)).obj
          (hypercoverPresheafDouble J G K F) :=
  HomologicalComplex₂.isoTwoPageTotalFiltration₂ (hypercoverPresheafDouble J G K F) _
    (HomologicalComplex₂.pageIso₂ _) (HomologicalComplex₂.exists_delta₂ _) (p : ℤ) (q' : ℤ)

/-- `hypercoverPresheafPageTwoAppIso` is natural in the sheaf, for the morphisms
`hypercoverPresheafDoubleMap` of double complexes.  This is
`HomologicalComplex₂.pageTwoIso_naturality_of_homotopyClasses`. -/
lemma hypercoverPresheafPageTwoAppIso_naturality (p q' : ℕ)
    {F F' : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}} (f : F ⟶ F') :
    (hypercoverPresheafE₂Functor J G K ⋙
          CategoryTheory.SpectralSequence.pageFunctor _ _ 2 2 ⋙
            HomologicalComplex.eval _ _ ((p : ℤ), (q' : ℤ))).map f ≫
        (hypercoverPresheafPageTwoAppIso J G K p q' F').hom =
      (hypercoverPresheafPageTwoAppIso J G K p q' F).hom ≫
        (HomologicalComplex₂.homologyIIHomologyIFunctor
          AddCommGrpCat.{max (max u v) (max q w)} (p : ℤ) (q' : ℤ)).map
            (hypercoverPresheafDoubleMap J G K f) :=
  HomologicalComplex₂.pageTwoIso_naturality_of_homotopyClasses
    (hypercoverPresheafDouble J G K) (hypercoverPresheafDoubleMap J G K)
    (filteredHomotopy₂_hypercoverPresheafDoubleMap_id J G K)
    (fun f g => filteredHomotopy₂_hypercoverPresheafDoubleMap_comp J G K f g) f
    (p : ℤ) (q' : ℤ)

/-- **The coefficient comparison for an `ℕ`-indexed complex of abelian sheaves**: taking the
homology of the double complex of the extension of such a complex, first in the resolution
direction and then in the hypercovering direction, is the Čech cohomology of the homology of the
underlying complex of presheaves.  Composite of `hypercoverPresheafDoubleHomologyNatIso` and
`extendUpNatMapHomologyNatIso`. -/
def hypercoverPresheafResolutionCoefficientNatIso (p q' : ℕ) :
    ComplexShape.embeddingUpNat.extendFunctor
          (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) ⋙
        hypercoverPresheafDoubleFunctor J G K ⋙
          HomologicalComplex₂.homologyIIHomologyIFunctor
            AddCommGrpCat.{max (max u v) (max q w)} (p : ℤ) (q' : ℤ) ≅
      (sheafToPresheaf J.toGrothendieck
            AddCommGrpCat.{max (max u v) (max q w)}).mapHomologicalComplex
          (ComplexShape.up ℕ) ⋙
        HomologicalComplex.homologyFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{max (max u v) (max q w)})
            (ComplexShape.up ℕ) q' ⋙
          presheafCechCohomologyFunctor J G K p :=
  Functor.isoWhiskerLeft
      (ComplexShape.embeddingUpNat.extendFunctor
        (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}))
      (hypercoverPresheafDoubleHomologyNatIso J G K p (q' : ℤ)) ≪≫
    Functor.isoWhiskerRight
      (extendUpNatMapHomologyNatIso
        (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) q')
      (presheafCechCohomologyFunctor J G K p)

/-- `hypercoverPresheafResolutionCoefficientNatIso` at the chosen injective resolution of a sheaf,
with the coefficient presheaf written as the `ℕ`-indexed homology of the underlying complex of
presheaves. -/
def hypercoverPresheafDoubleHomologyIso (p q' : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) :
    (HomologicalComplex₂.homologyIIHomologyIFunctor
        AddCommGrpCat.{max (max u v) (max q w)} (p : ℤ) (q' : ℤ)).obj
          (hypercoverPresheafDouble J G K F) ≅
      (presheafCechCohomologyFunctor J G K p).obj
        ((HomologicalComplex.homologyFunctor
          (Cᵒᵖ ⥤ AddCommGrpCat.{max (max u v) (max q w)}) (ComplexShape.up ℕ) q').obj
            (((sheafToPresheaf J.toGrothendieck
              AddCommGrpCat.{max (max u v) (max q w)}).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj (injectiveResolution F).cocomplex)) :=
  (hypercoverPresheafResolutionCoefficientNatIso J G K p q').app
    (injectiveResolution F).cocomplex

/-- `hypercoverPresheafDoubleHomologyIso` read as a naturality square for
`hypercoverPresheafDoubleMap`. -/
lemma hypercoverPresheafDoubleHomologyIso_naturality (p q' : ℕ)
    {F F' : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}} (f : F ⟶ F') :
    (HomologicalComplex₂.homologyIIHomologyIFunctor
          AddCommGrpCat.{max (max u v) (max q w)} (p : ℤ) (q' : ℤ)).map
            (hypercoverPresheafDoubleMap J G K f) ≫
        (hypercoverPresheafDoubleHomologyIso J G K p q' F').hom =
      (hypercoverPresheafDoubleHomologyIso J G K p q' F).hom ≫
        (presheafCechCohomologyFunctor J G K p).map
          ((HomologicalComplex.homologyFunctor
            (Cᵒᵖ ⥤ AddCommGrpCat.{max (max u v) (max q w)}) (ComplexShape.up ℕ) q').map
              (((sheafToPresheaf J.toGrothendieck
                AddCommGrpCat.{max (max u v) (max q w)}).mapHomologicalComplex
                  (ComplexShape.up ℕ)).map
                    (InjectiveResolution.desc f (injectiveResolution F')
                      (injectiveResolution F)))) := by
  have h := (hypercoverPresheafResolutionCoefficientNatIso J G K p q').hom.naturality
    (InjectiveResolution.desc f (injectiveResolution F') (injectiveResolution F))
  dsimp only [Functor.comp_map] at h
  exact h

/-- **The coefficient comparison at a sheaf**:
`H^p_{II}(H^{q'}_I(A^{•,•}(F))) ≅ Ȟ^p(K, H̲^{q'}(F))`.  This is
`hypercoverPresheafDoubleHomologyIso` followed by the computation of the cohomology presheaf
`H̲^{q'}(F)` by the chosen injective resolution of `F`. -/
@[simps]
def hypercoverPresheafCoefficientIso (p q' : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) :
    (HomologicalComplex₂.homologyIIHomologyIFunctor
        AddCommGrpCat.{max (max u v) (max q w)} (p : ℤ) (q' : ℤ)).obj
          (hypercoverPresheafDouble J G K F) ≅
      ((sheafToPresheaf J.toGrothendieck
          AddCommGrpCat.{max (max u v) (max q w)}).rightDerived q' ⋙
        presheafCechCohomologyFunctor J G K p).obj F where
  hom := (hypercoverPresheafDoubleHomologyIso J G K p q' F).hom ≫
    (presheafCechCohomologyFunctor J G K p).map
      ((injectiveResolution F).isoRightDerivedObj (sheafToPresheaf J.toGrothendieck
        AddCommGrpCat.{max (max u v) (max q w)}) q').inv
  inv := (presheafCechCohomologyFunctor J G K p).map
      ((injectiveResolution F).isoRightDerivedObj (sheafToPresheaf J.toGrothendieck
        AddCommGrpCat.{max (max u v) (max q w)}) q').hom ≫
    (hypercoverPresheafDoubleHomologyIso J G K p q' F).inv
  hom_inv_id := by
    rw [Category.assoc, ← Category.assoc
      ((presheafCechCohomologyFunctor J G K p).map _), ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id]
  inv_hom_id := by
    rw [Category.assoc, ← Category.assoc
      ((hypercoverPresheafDoubleHomologyIso J G K p q' F).inv), Iso.inv_hom_id,
      Category.id_comp, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
    rfl

/-- The coefficient comparison is natural in the sheaf, for the morphisms
`hypercoverPresheafDoubleMap` of double complexes. -/
lemma hypercoverPresheafCoefficientIso_naturality (p q' : ℕ)
    {F F' : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}} (f : F ⟶ F') :
    (HomologicalComplex₂.homologyIIHomologyIFunctor
          AddCommGrpCat.{max (max u v) (max q w)} (p : ℤ) (q' : ℤ)).map
            (hypercoverPresheafDoubleMap J G K f) ≫
        (hypercoverPresheafCoefficientIso J G K p q' F').hom =
      (hypercoverPresheafCoefficientIso J G K p q' F).hom ≫
        ((sheafToPresheaf J.toGrothendieck
            AddCommGrpCat.{max (max u v) (max q w)}).rightDerived q' ⋙
          presheafCechCohomologyFunctor J G K p).map f := by
  have h3 := InjectiveResolution.isoRightDerivedObj_inv_naturality f
    (injectiveResolution F) (injectiveResolution F') _
    (InjectiveResolution.desc_commutes_zero f (injectiveResolution F')
      (injectiveResolution F))
    (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) q'
  dsimp only [Functor.comp_map] at h3
  rw [hypercoverPresheafCoefficientIso_hom, hypercoverPresheafCoefficientIso_hom,
    reassoc_of% hypercoverPresheafDoubleHomologyIso_naturality J G K p q' f, ← Functor.map_comp]
  dsimp only [Functor.comp_map]
  rw [Category.assoc, ← Functor.map_comp, h3]

/-- **The second page of the spectral sequence, on `ℤ × ℤ`.**  At `((p : ℤ), (q' : ℤ))` it is
`Ȟ^p(K, H̲^{q'}(F))`, naturally in `F`: the spectral-sequence identification
`''E_2^{p,q'} ≅ H^p_{II}(H^{q'}_I(A^{•,•}(F)))` of [Stacks, Tag 0130] (6), followed by the
coefficient comparison. -/
def hypercoverPresheafPageTwoIsoInt (p q' : ℕ) :
    hypercoverPresheafE₂Functor J G K ⋙
        CategoryTheory.SpectralSequence.pageFunctor _ _ 2 2 ⋙
          HomologicalComplex.eval _ _ ((p : ℤ), (q' : ℤ)) ≅
      (sheafToPresheaf J.toGrothendieck
          AddCommGrpCat.{max (max u v) (max q w)}).rightDerived q' ⋙
        presheafCechCohomologyFunctor J G K p :=
  NatIso.ofComponents
    (fun F => hypercoverPresheafPageTwoAppIso J G K p q' F ≪≫
      hypercoverPresheafCoefficientIso J G K p q' F)
    (fun f => by
      rw [Iso.trans_hom, Iso.trans_hom, ← Category.assoc,
        hypercoverPresheafPageTwoAppIso_naturality J G K p q' f, Category.assoc,
        hypercoverPresheafCoefficientIso_naturality J G K p q' f, Category.assoc])

/-- **The `pageTwoIso` field of `PresheafHypercoveringSpectralSequenceData`**: the second page of
the spectral sequence at `(p, q') : ℕ × ℕ` is `Ȟ^p(K, H̲^{q'}(F))`, naturally in the sheaf `F`.
The passage from `ℤ × ℤ` to `ℕ × ℕ` is on the nose, by
`CategoryTheory.SpectralSequence.natRestrictE₂Comp_pageTwoIso`. -/
def hypercoverPresheafPageTwoIso (p q' : ℕ) :
    hypercoverPresheafSpectralSequenceFunctor J G K ⋙
        CategoryTheory.SpectralSequence.pageFunctor _ _ 2 2 ⋙
          HomologicalComplex.eval _ _ (p, q') ≅
      (sheafToPresheaf J.toGrothendieck
          AddCommGrpCat.{max (max u v) (max q w)}).rightDerived q' ⋙
        presheafCechCohomologyFunctor J G K p :=
  CategoryTheory.SpectralSequence.natRestrictE₂Comp_pageTwoIso
      (hypercoverPresheafE₂Functor J G K)
      (isFirstQuadrant_hypercoverPresheafE₂Functor J G K) p q' ≪≫
    hypercoverPresheafPageTwoIsoInt J G K p q'

end Sequence

end Stacks.CategoryTheory.Hypercovering

end
