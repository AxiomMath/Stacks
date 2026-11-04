module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleStructureSheafInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDirectImageChartEqualizer
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionComparisonAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionCommutationRingedTopoi
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionToAlgebraicSpaceEtale

/-!
# The comparison map of equation 075M

Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in groupoids over `(Sch/S)_{fppf}` with
`𝒳` representable by an algebraic space `F` and `𝒴` by an algebraic space `G`, and let
`fSpace : F ⟶ G` be a morphism of algebraic spaces compatible with `f` through the two chosen
presentations. Equation 075M of the source asserts
```
(f_*ℱ)|_{G_étale} = f_{small,*}(ℱ|_{F_étale}),
```
and this file builds the map that identification is: a natural transformation
`π_{G,*}f_* ⟶ f_{small,*}π_{F,*}` of the two direct images around the square of Stacks 073N.

`StacksFrontier/AlgebraicGeometry/Stacks/RestrictionDirectImage.lean` computes the left-hand side
of 075M, `AlgebraicGeometry.Space.restrictedDirectImageChartEquiv`; the right-hand side did not
appear there, and no map between the two sides existed anywhere in this library. The comparison
built here is what `AlgebraicGeometry.Space.restrictionRingedSquare` takes as its hypothesis
`cmp`: it is this one canonical map. Its invertibility is proved in
`StacksFrontier/AlgebraicGeometry/Stacks/RestrictionDirectImageComparisonIso.lean`, and Stacks 073N
is `AlgebraicGeometry.Space.restrictionRingedSquareTwoIso`.

## Main definitions

* `AlgebraicGeometry.Space.restrictedDirectImageComparisonSections`: the comparison on
  sections over a commutative diagram of étale scheme charts — restrict the section of
  `f_*ℱ` along the morphism `f(u_F W) ⟶ u_G V` of `𝒴` the diagram provides, then apply
  the counit of the right Kan extension that computes `f_*`.
* `AlgebraicGeometry.Space.restrictedDirectImageComparisonFMap`: those maps assembled
  into an `fSpace`-map in the sense of Stacks 03G3.
* `AlgebraicGeometry.Space.restrictedDirectImageComparisonHom`: **equation 075M, the
  comparison map**, for one sheaf, obtained from that `fSpace`-map by the chart
  correspondence of Stacks 03G8.
* `AlgebraicGeometry.Space.restrictedDirectImageComparison`: **equation 075M**, the
  comparison as a natural transformation of the two direct images of the legs of the
  square of Stacks 073N.
* `AlgebraicGeometry.Space.FMap.compTarget`: an `fSpace`-map precomposed on sections over
  the chart of the target, the counterpart of
  `AlgebraicGeometry.Space.FMap.compSource`.
* `AlgebraicGeometry.Space.restrictedDirectImageComparisonIso` and
  `AlgebraicGeometry.Space.restrictionRingedSquareOfIsIso`: the comparison as an
  isomorphism, and Stacks 073N, given invertibility of the canonical comparison map.

## Main results

* `AlgebraicGeometry.Space.restrictedDirectImageComparisonSections_naturality`: the
  comparison on sections is compatible with simultaneous étale restriction of the two
  charts of a diagram, which is what makes it an `fSpace`-map.
* `AlgebraicGeometry.Space.restrictedDirectImageComparisonSections_map` and
  `AlgebraicGeometry.Space.restrictedDirectImageComparisonHom_naturality`: the comparison
  is natural in the sheaf, so it is a transformation of the two direct image *functors*
  and not merely a map for each sheaf separately.
* `AlgebraicGeometry.Space.fMapEquivPushforwardHom_ringUniverse_target_map` and
  `AlgebraicGeometry.Space.fMapEquivPushforwardHom_ringUniverse_symm_target_map`:
  **Stacks 03G8**, naturality of the chart correspondence in the sheaf on the *target*.
  This is the counterpart of
  `AlgebraicGeometry.Space.fMapEquivPushforwardHom_ringUniverse_source_map`, and together
  with it is exactly what turns the sheafwise comparison into a natural transformation.
* `AlgebraicGeometry.Space.ranCounit_app_forgetFSharp_ringedToposMorphism`: the structure
  map of the 1-morphism, restricted along a morphism of `𝒴` and then read through the
  counit of the right Kan extension that computes `f_*`, is restriction of sections
  followed by the canonical identification `f⁻¹𝒪_𝒴 ⟶ 𝒪_𝒳` of Stacks 06TW. This is the
  triangle identity of the adjunction of Stacks 06NW, and it is the computation the
  structure-sheaf half of Stacks 073N needs on the leg `π_G ∘ f`.
* `AlgebraicGeometry.Space.restrictedDirectImageComparison_structureSheafCompatible_iff`:
  the hypothesis `hsq` of `AlgebraicGeometry.Space.restrictionRingedSquareOfIsIso` is
  *equivalent* to a statement about charts carrying no Kan extension and no chart
  correspondence.
* `AlgebraicGeometry.Space.forgetFSharp_projectionRingedToposHom_app` and
  `AlgebraicGeometry.Space.forgetRing_map_fSharpInverseImage_app`: **the three
  structure-sheaf identifications of the square of Stacks 073N, computed on sections.** The
  structure map of `π_F` — and, at `G` and `q`, that of `π_G` — and the identification
  `f⁻¹𝒪_𝒴 ⟶ 𝒪_𝒳` of Stacks 06TW are each pullback of regular functions along the
  identification of underlying objects of the big fppf site that the relevant functor
  equality provides.
* `AlgebraicGeometry.Space.isHomLift_comparisonChartHom` and
  `AlgebraicGeometry.Space.comparisonChartHom_fac`: the morphism `f(u_F W) ⟶ u_G V` of `𝒴`
  attached to a chart diagram lies over the diagram's vertical morphism of schemes, and
  therefore factors through it, as soon as the components of `ha` are vertical.
* `AlgebraicGeometry.Space.restrictedDirectImageComparison_structureSheafCompatible_chart`
  and `AlgebraicGeometry.Space.restrictedDirectImageComparison_structureSheafCompatible`:
  **the hypothesis `hsq` is discharged** — the chartwise identity above is proved, and hence
  so is `hsq` itself, for every pair `(fSpace, ha)` whose compatibility is vertical.
* `AlgebraicGeometry.Space.restrictionRingedSquareOfIsIsoOfIsHomLift` and
  `AlgebraicGeometry.Space.restrictionRingedSquareInduced`: **Stacks 073N given invertibility
  of the comparison map alone**, in general for a vertical `ha` and unconditionally at the
  morphism of algebraic spaces the 1-morphism induces, where verticality is the theorem
  `AlgebraicGeometry.Space.isHomLift_schemeChartPostcompIso_hom_app`. The second is the
  2-isomorphism that the hypothesis `sq` of
  `AlgebraicGeometry.Space.restrictedDerivedDirectImageIso` (Stacks 075N) asks for.
* `AlgebraicGeometry.Space.exists_restrictedDirectImageComparisonTarget_equalizer`:
  **equation 075M, the right-hand side at a chart, as an equalizer.** The sections of
  `f_{small,*}(ℱ|_{F_étale})` over an étale scheme chart `V` of `G` are the equalizer of the
  sections of `ℱ|_{F_étale}` over two étale scheme charts of `F` above `F ×_G V`. This is
  `AlgebraicGeometry.Space.exists_smallEtaleDirectImageChartEqualizerEquiv`, Properties of
  Spaces 03H7 for the direct image on the small étale sites, at the chart of 075M.
* `AlgebraicGeometry.Space.isIso_restrictedDirectImageComparison_of_bijective`:
  **invertibility of the comparison map reduced to per-chart bijectivity.** The hypothesis
  `hiso` of `AlgebraicGeometry.Space.restrictionRingedSquareOfIsIso` follows from the
  comparison being a bijection on sections over each étale scheme chart of `G`; that bijection
  is proved in
  `StacksFrontier/AlgebraicGeometry/Stacks/RestrictionDirectImageComparisonIso.lean`, so `hiso`
  holds unconditionally.

## Implementation notes

**Why the comparison map is unconditional.** The source derives 075M from Stacks 073N, whose
proof identifies the 2-fibre product `(Sch/V)_{fppf} ×_𝒴 𝒳` with the split category fibred in
groupoids of `V ×_G F` and then compares two equalizer presentations. None of that is needed to
construct the *map*. A chart diagram — an étale scheme chart `W` of `F`, an étale scheme chart
`V` of `G` and a morphism of schemes `W ⟶ V` over `fSpace` — determines a morphism
`f(u_F W) ⟶ u_G V` of `𝒴` over `W ⟶ V`, namely
`AlgebraicGeometry.Space.comparisonChartHom`, the same morphism out of which the comparison map
of equation 076Q is built. Restricting a section of `f_*ℱ` over `u_G V` along it and applying the
counit of the right Kan extension that `f_*` is gives a section of `ℱ` over `u_F W`, i.e. a
section of `π_{F,*}ℱ` over `W`. Compatibility with restriction of the two charts is naturality of
`comparisonChartHom`, and the chart correspondence of Stacks 03G8 then converts the family into a
homomorphism into `f_{small,*}(π_{F,*}ℱ)` — which is what makes the *right-hand side* of 075M
appear here at all, since the small étale direct image is not a restriction along any functor of
small étale sites but the spaces-étale one conjugated by the comparison equivalences of
Stacks 03G1.

**The hypothesis `ha`.** The compatibility of `f : 𝒳 ⥤ 𝒴` with `fSpace : F ⟶ G` through the
chosen presentations is the hypothesis `ha` of
`AlgebraicGeometry.Space.comparisonAlgebraicSpaces`, which the implementation notes of
`StacksFrontier/AlgebraicGeometry/Stacks/RestrictionCommutationRingedTopoi.lean` already name as
what a proof of `cmp` would need. **It is a genuine restriction on the pair `(f, fSpace)`**.
`AlgebraicGeometry.Space.exists_comparisonChartFunctorIso` does *not* realize `ha`
for a given `f`: it quantifies the 1-morphism existentially and its witness is a functor built
from `fSpace` by transporting postcomposition across
`AlgebraicGeometry.Space.schemeChartFunctor`, so it certifies only that the hypothesis is not
vacuous. It also delivers `Nonempty (… ≅ …)` rather than the isomorphism itself, which `ha`
carries as data.

The sharp statement that pins `fSpace` against `f` is
`AlgebraicGeometry.Space.eq_inducedSpacesHom_iff_forall_sectionOfObj` (Stacks 04SW): a morphism
of algebraic spaces is `AlgebraicGeometry.Space.inducedSpacesHom` of `f` exactly when it carries
the section named by each object `z` of `𝒳` to the section named by `f z`. That does not yet
give `ha`, which is a natural isomorphism of functors on *charts*. The missing glue is the
bridge from `CategoryTheory.PresheafOfCategories.sectionOfObj` to
`AlgebraicGeometry.Space.schemeChartFunctor`, which no declaration states although it follows
from `CategoryTheory.PresheafOfCategories.sectionOfObj_inv_obj` together with
`CategoryTheory.PresheafOfCategories.costructuredArrowToElements_obj_fiber_as`. With that
bridge, `ha` at `fSpace = inducedSpacesHom … f hf` would become a theorem rather than a
hypothesis.

`AlgebraicGeometry.Space.restrictionSquareFibredLeg` and
`AlgebraicGeometry.Space.restrictionSquareSpaceLeg` do not mention it, which is why the
comparison is stated as a transformation of their direct images and the hypothesis lives on this
file's declarations instead.

**Naturality in the target sheaf.** The chart correspondence of Stacks 03G8 is an `Equiv`, and
naturality in the source sheaf was already available
(`AlgebraicGeometry.Space.fMapEquivPushforwardHom_ringUniverse_source_map`). Naturality in the
target was not, and it is what the naturality square of the comparison needs on its left edge.
It is proved here and it is cheap: the inverse of the correspondence,
`AlgebraicGeometry.Space.fMapOfPushforwardHomTypeU`, uses the homomorphism only through
`ψ.hom.app (op d.V)`, so precomposing with `γ` before that is definitionally the same as
applying `γ` to the section first — `_symm_target_map` holds by `rfl`.

**Invertibility.** It is proved, in
`StacksFrontier/AlgebraicGeometry/Stacks/RestrictionDirectImageComparisonIso.lean`, as
`AlgebraicGeometry.Space.isIso_restrictedDirectImageComparison`. The comparison at a chart `V`
goes from the sections of `pr^{-1}ℱ` over the whole 2-fibre product `(Sch/V)_{fppf} ×_𝒴 𝒳`
(`AlgebraicGeometry.Space.restrictedDirectImageChartEquiv`, the left-hand side of 075M) to the
limit of `ℱ(u_F W)` over the chart diagrams above `V`, so invertibility says that the étale
scheme charts of `F` above `V ×_G F` compute those sections. It is *not* proved by comparing the
two equalizer presentations below, which forget all compatibility between the two sides; it is
proved chartwise, by the chart correspondence of Stacks 03G8 together with two statements about
chart diagrams over `V` — that a morphism of `𝒴` out of the image of an arbitrary object of `𝒳`
factors through the morphism of a chart diagram as soon as that object admits any morphism to the
image of an étale chart, and that two chart diagrams over `V` have a common refinement. Compared
with the library, the two ingredients of the source's own proof divide as follows:

* The **equalizer presentation of the right-hand side is held**, at the chart of equation 075M.
  Its inputs were already here — Properties of Spaces 03H7 as
  `AlgebraicGeometry.Space.exists_isLimit_fork_of_isSheaf`, Stacks 03G1 as
  `AlgebraicGeometry.Space.comparisonFunctor_sheafEquivalence` and Stacks 03G2 as
  `AlgebraicGeometry.Space.spacesBaseChange`, with Stacks 03M8 assembling Γ over the small étale
  site of an algebraic space as an equalizer over an atlas
  (`AlgebraicGeometry.Space.sectionsComparisonEquivEqualizer`,
  `AlgebraicGeometry.Space.smallEtaleSectionsEquivEqualizer`) — and the presentation itself is
  `AlgebraicGeometry.Space.exists_smallEtaleDirectImageChartEqualizerEquiv`, 03H7 for the direct
  image on the small étale sites, specialized below as
  `AlgebraicGeometry.Space.exists_restrictedDirectImageComparisonTarget_equalizer`. Earlier
  versions of this note and of the docstrings below cited that second name and recorded that no
  declaration of it existed anywhere in the library; it exists now, at the end of this section,
  and the note is corrected rather than left denying it. The same holds of
  `AlgebraicGeometry.Space.isIso_restrictedDirectImageComparison_of_bijective`, cited as
  reducing invertibility to per-chart bijectivity and likewise recorded as absent: it is below
  too, built from `CategoryTheory.Sheaf.isIso_of_bijective_app`.
* The **identification of the 2-fibre product** with a split category fibred in groupoids is
  available in substance, through
  `CategoryTheory.PresheafOfCategories.nonempty_equivalenceOver_twoFibreProductPresheaf` and
  `CategoryTheory.PresheafOfCategories.exists_isPullback_relocalize_twoFibreProductPresheaf`
  (there are no `AlgebraicGeometry.Space` copies).
  What it is still missing is **not** the topology. The
  identification is available only without the topology, and no declaration transports the
  inherited étale site across the equivalence; but no such transport is needed before the
  left-hand side can be stated, because
  the first leg of the cospan of equation 075M is `CategoryTheory.Over.forget` of a chart, so
  `CategoryTheory.TwoFibreProductOver.structureFunctor` of that 2-fibre product lands in
  `AlgebraicGeometry.BigFppfOver B S hS` itself rather than in a slice of it: its inherited étale
  topology is already a topology over the same base site as the one on `𝒳`, and no comparison of
  two topologies arises. What the two cited declarations do lack is the *base*: both present the
  2-fibre product over the slice `BigFppfOver B V.left.1 V.left.2`, with the representing presheaf
  on that smaller site, whereas what a consumer over `S` needs is an equivalence over
  `BigFppfOver B S hS` with the representing presheaf on `(BigFppfOver B S hS)ᵒᵖ` — the form of
  `AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpace` (Stacks 04SV).
  `CategoryTheory.StacksRepresentableCFG.EquivalenceOver.compRight` moves the left of the
  equivalence to the larger base; on the right it replaces the split category fibred in groupoids
  of a presheaf by that of its `CategoryTheory.OverShriek.relocalizePresheafFunctor`, and that
  identification is the one lemma still owed.
* The matching equalizer presentation of the *left-hand side* **is now present**, in
  `StacksFrontier/AlgebraicGeometry/Stacks/RestrictionDirectImageLeftEqualizer.lean` as
  `AlgebraicGeometry.Space.exists_restrictedDirectImageComparisonSource_equalizer`, with the
  representability of the 2-fibre product in the shape of the previous item as its one hypothesis.
  Its further inputs are all in the library.

  The first, invariance of `CategoryTheory.Presheaf.globalSections` under an equivalence of the
  index category, is `CategoryTheory.Presheaf.globalSectionsPrecompEquiv`, proved from
  `CategoryTheory.Functor.bijective_sectionsPrecomp` through the initial-functor form
  `CategoryTheory.Presheaf.globalSectionsPrecompEquivOfInitial`; it is computed on sections by
  `CategoryTheory.Presheaf.globalSectionsEquivSections_globalSectionsPrecompEquiv` and is
  natural in the presheaf by
  `CategoryTheory.Presheaf.globalSectionsPrecompEquiv_naturality`.

  The second, Stacks 0792 on a site, is instantiated:
  `Stacks.Sites.GlobalSectionsAsEqualizer.isColimitCoforkShYonedaTerminal` discharges the
  coequalizer hypothesis of
  `Stacks.Sites.GlobalSectionsAsEqualizer.globalSectionsForkIsLimit` — the first time that
  lemma is applied — and
  `Stacks.Sites.GlobalSectionsAsEqualizer.globalSectionsForkIsLimitOfCoversTop` is 0792 with
  nothing left but two conditions on the site: `GrothendieckTopology.CoversTop` of the
  one-element family of the atlas object, and `CategoryTheory.Presheaf.FactorsPairs` for the
  two morphisms of the relation. `CategoryTheory.Presheaf.globalSectionsEquivEqualizer` is the
  same statement for the global sections of Stacks 06UN, which is the form
  `AlgebraicGeometry.Space.restrictedDirectImageChartEquiv` delivers the left-hand side in.

  Both conditions on the inherited étale site of `(Sch/V)_{fppf} ×_𝒴 𝒳` are now discharged, and
  neither needed a transported topology. The one-element
  family of an atlas covers the final object: the proof of
  `AlgebraicGeometry.Space.restrictionFunctor_coversTop`, which covers by the family of *all*
  charts, picks a single `hF.exists_atlas` witness and produces every membership
  witness at it, so hoisting the choice gives
  `AlgebraicGeometry.Space.exists_restrictionFunctor_coversTop_singleton`, Stacks 073M by one
  chart, from which `restrictionFunctor_coversTop` is now derived rather than the other way about.
  `FactorsPairs` for the two projections does not need the morphisms of the site to be morphisms
  over `V ×_G F` either: it is the existence half of a *binary product* universal property
  (`CategoryTheory.Presheaf.factorsPairs_of_isLimit`), and
  `AlgebraicGeometry.Space.restrictionFunctor_preservesBinaryProducts` carries `A ⨯ A` from the
  small étale site of the representing space to a product in the 2-fibre product.

**The structure-sheaf compatibility `hsq`.** Invertibility is not the only thing
`AlgebraicGeometry.Space.restrictionRingedSquareOfIsIso` asks for: it also asks for `hsq`, that
the comparison map read at the structure sheaf carry the structure map of one leg to that of the
other. `restrictedDirectImageComparison_structureSheafCompatible_iff` measures that hypothesis
exactly. Through the chart correspondence of Stacks 03G8 — a bijection, so it loses nothing —
`hsq` is *equivalent* to the chartwise statement that the three canonical structure-sheaf
identifications of the square carry restriction of regular functions along
`AlgebraicGeometry.Space.comparisonChartHom` to restriction along the vertical morphism of
schemes `d.g` of the chart diagram. The Kan extension is gone from that statement, discharged by
`ranCounit_app_forgetFSharp_ringedToposMorphism`.

**`hsq` is now discharged**, by
`restrictedDirectImageComparison_structureSheafCompatible`, for every pair `(fSpace, ha)` whose
compatibility is vertical — and unconditionally at the induced morphism of algebraic spaces,
where verticality is a theorem. What remained after the equivalence above was two inputs, and
both are now in place.

* **Verticality of `ha`.** The equivalence's right-hand side says that the morphism of schemes
  underlying `comparisonChartHom` is `d.g`. That is *false* for a general pair `(fSpace, ha)`:
  `comparisonChartHom` begins with `ha.hom.app d.U.1`, and since
  `schemeChartFunctor … ⋙ f ⋙ q` and `CostructuredArrow.map fSpace.hom ⋙ schemeChartFunctor … ⋙ q`
  are both the projection to charts, `q` carries that component to an automorphism of the chart's
  base scheme which the hypothesis `ha` does not pin down. What is needed is the verticality
  hypothesis `hab` of `AlgebraicGeometry.Space.isHomLift_comparisonMorphism`. At the *induced*
  morphism of algebraic spaces, where `ha` is
  `AlgebraicGeometry.Space.schemeChartPostcompIso`, that hypothesis is now a theorem:
  `AlgebraicGeometry.Space.isHomLift_schemeChartPostcompIso_hom_app`. With it,
  `CategoryTheory.Functor.IsHomLift.fac'` puts the morphism of schemes underlying
  `comparisonChartHom` in the form `eqToHom ≫ d.g ≫ eqToHom`, which is what the right-hand side
  of the equivalence needs of it.
* **The three structure-sheaf identifications on sections.** Granted verticality, what remains is
  bookkeeping: the structure maps of `π_F` and `π_G` are `eqToHom` of
  `AlgebraicGeometry.Space.inverseImage_structureSheaf_eq` (the comparison
  `Stacks.Sheaves.ToposPullback.restrictionCommRingIso` being the identity on underlying sheaves
  of sets), and the third is `eqToHom` of
  `AlgebraicGeometry.FibredSite.inverseImageStructureSheaf_eq`. All three are `eqToHom` of one
  functor equality — `AlgebraicGeometry.Space.restrictionFunctor_comp` for the first two,
  `CategoryTheory.Functor.IsFibredOneMorphism.comp_eq` for the third — read through
  `T ↦ T.op ⋙ (BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ`, and none of them is the identity:
  neither functor equality holds by `rfl`, the first two resting on the chosen equivalence's
  `MorphismOver.w`, and in the first two the source and the target are not reducibly equal
  objects, so there is not even a sectionwise statement that the map is the identity. All three
  are now computed: `forgetFSharp_projectionRingedToposHom_app` for the first and the second,
  `forgetRing_map_fSharpInverseImage_app` for the third. Each is pullback of regular functions
  along the `eqToHom` of the big fppf site that the functor equality provides, which is what
  lets `comparisonChartHom_fac` close the chartwise statement.

So nothing is left open about Stacks 073N at the *induced* morphism of algebraic spaces:
`restrictionRingedSquareInduced` builds the square from `hiso` alone, `hiso` is
`AlgebraicGeometry.Space.isIso_restrictedDirectImageComparison`, and
`AlgebraicGeometry.Space.restrictionRingedSquareOfInduced` is the two put together — which is
exactly the hypothesis `sq` of `restrictedDerivedDirectImageIso`, Stacks 075N.

**Hosting.** The two computations and everything built on them live here rather than in
`StacksFrontier/AlgebraicGeometry/Stacks/Sheaves/RestrictionDerivedDirectImage.lean` because this
file already has every input except `AlgebraicGeometry.Space.inducedSpacesHom` and
`AlgebraicGeometry.Space.schemeChartPostcompIso`, whose module adds **one** module to this
file's import closure (2054 to 2055); importing this file into the Stacks 075N file instead
costs **40** (2042 to 2082).

## References

* [Stacks Project, Tag 075M](https://stacks.math.columbia.edu/tag/075M)
* [Stacks Project, Tag 073N](https://stacks.math.columbia.edu/tag/073N)
* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 076Q](https://stacks.math.columbia.edu/tag/076Q)
* [Stacks Project, Tag 06TW](https://stacks.math.columbia.edu/tag/06TW)
* [Stacks Project, Tag 0GQA](https://stacks.math.columbia.edu/tag/0GQA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u v w v' w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)

/-! ### Naturality of the chart correspondence in the sheaf on the target -/

section ChartCorrespondenceTarget

variable {X Y : AlgebraicSpaces B S hS}

/-- An `fSp`-map precomposed, on sections over the chart of the target, with a homomorphism of
presheaves on the small étale site of `Y`. This is the target-side counterpart of
`AlgebraicGeometry.Space.FMap.compSource`. -/
def FMap.compTarget (fSp : X ⟶ Y)
    {P : (SmallEtale B S hS X.1)ᵒᵖ ⥤ Type u}
    {Q Q' : (SmallEtale B S hS Y.1)ᵒᵖ ⥤ Type u}
    (ξ : FMap B S hS X.1 Y.1 fSp.hom P Q) (γ : Q' ⟶ Q) :
    FMap B S hS X.1 Y.1 fSp.hom P Q' where
  app d s := ξ.app d (γ.app (op d.V) s)
  naturality d d' i j hij s := by
    rw [NatTrans.naturality_apply γ j.op s]
    exact ξ.naturality d d' i j hij _

/-- **Stacks 03G8**, naturality of the chart correspondence in the sheaf on the target, read on
the `fSp`-map side and on sections: the `fSp`-map of a homomorphism precomposed with `γ` is the
`fSp`-map of the homomorphism, applied to the image of the section under `γ`.

The chart correspondence attaches to a homomorphism `β` into the direct image the restriction
of its sections along the arrow into the cartesian base change, and `γ` is applied before that
restriction; so this holds by definitional unfolding. -/
theorem fMapEquivPushforwardHom_ringUniverse_symm_target_map (fSp : X ⟶ Y)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (Q Q' : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) (γ : Q' ⟶ Q)
    (β : Q ⟶ (smallEtaleRingedToposHom B S hS fSp).toToposHom.pushforward.obj P)
    (d : ChartDiagram B S hS X.1 Y.1 fSp.hom) (s : Q'.obj.obj (op d.V)) :
    ((fMapEquivPushforwardHom_ringUniverse B S hS fSp P Q').symm (γ ≫ β)).app d s =
      ((fMapEquivPushforwardHom_ringUniverse B S hS fSp P Q).symm β).app d
        (γ.hom.app (op d.V) s) :=
  rfl

/-- **Stacks 03G8**, naturality of the chart correspondence in the sheaf on the target: the
homomorphism into the direct image attached to an `fSp`-map, precomposed with a morphism of
sheaves on the small étale site of `Y`, is the homomorphism attached to that `fSp`-map
precomposed on sections. -/
theorem fMapEquivPushforwardHom_ringUniverse_target_map (fSp : X ⟶ Y)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (Q Q' : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) (γ : Q' ⟶ Q)
    (ξ : FMap B S hS X.1 Y.1 fSp.hom P.obj Q.obj) :
    γ ≫ fMapEquivPushforwardHom_ringUniverse B S hS fSp P Q ξ =
      fMapEquivPushforwardHom_ringUniverse B S hS fSp P Q'
        (FMap.compTarget B S hS fSp ξ γ.hom) := by
  refine (Equiv.symm_apply_eq _).mp (FMap.ext_app B S hS fSp ?_)
  funext d s
  rw [fMapEquivPushforwardHom_ringUniverse_symm_target_map, Equiv.symm_apply_apply]
  rfl

end ChartCorrespondenceTarget

section Comparison

open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

attribute [local instance] hasSheafCompose_forget_ringCat
  Stacks.hasSheafCompose_forget₂_commRingCat

variable (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
  (eF : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (F ⋙ typeToCat)).p)
  (eG : StacksRepresentableCFG.EquivalenceOver q
    (presheafOfCategories (G ⋙ typeToCat)).p)
  (f : 𝒳 ⥤ 𝒴) (hf : p.IsFibredOneMorphism q f)
  (fSpace : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩)
  (ha : schemeChartFunctor B S hS F p eF ⋙ f ≅
    CostructuredArrow.map fSpace.hom ⋙ schemeChartFunctor B S hS G q eG)
  [∀ P : 𝒳ᵒᵖ ⥤ Type u, f.op.HasPointwiseRightKanExtension P]

/-- The map on sections over a commutative diagram of étale scheme charts out of which the
comparison map of equation 075M is built. -/
noncomputable def restrictedDirectImageComparisonSections
    (ℱ : Sheaf (BigFppfOver.associatedTopology B S hS p .etale) (Type u))
    (d : ChartDiagram B S hS F G fSpace.hom)
    (s : (f.op.ran.obj ℱ.obj).obj
      (op ((restrictionFunctor B S hS G q eG).obj d.V))) :
    ℱ.obj.obj (op ((restrictionFunctor B S hS F p eF).obj d.U)) :=
  (f.op.ranCounit.app ℱ.obj).app (op ((restrictionFunctor B S hS F p eF).obj d.U))
    ((f.op.ran.obj ℱ.obj).map
      (comparisonChartHom B S hS p q eF eG f fSpace ha d).op s)

/-- The maps on sections of `AlgebraicGeometry.Space.restrictedDirectImageComparisonSections` are
compatible with simultaneous étale restriction of the two charts of a diagram. -/
theorem restrictedDirectImageComparisonSections_naturality
    (ℱ : Sheaf (BigFppfOver.associatedTopology B S hS p .etale) (Type u))
    (d d' : ChartDiagram B S hS F G fSpace.hom) (i : d'.U ⟶ d.U) (j : d'.V ⟶ d.V)
    (hij : (SmallEtale.toOver B S hS F).map i ≫ d.g =
      d'.g ≫ (SmallEtale.toOver B S hS G).map j)
    (s : (f.op.ran.obj ℱ.obj).obj
      (op ((restrictionFunctor B S hS G q eG).obj d.V))) :
    restrictedDirectImageComparisonSections B S hS F G p q hF hG eF eG f fSpace ha ℱ d'
        ((f.op.ran.obj ℱ.obj).map
          ((restrictionFunctor B S hS G q eG).map j).op s) =
      ℱ.obj.map ((restrictionFunctor B S hS F p eF).map i).op
        (restrictedDirectImageComparisonSections B S hS F G p q hF hG eF eG f fSpace ha ℱ d s) := by
  have hch := comparisonChartHom_naturality B S hS p q eF eG f fSpace ha d d' i j hij
  have key : (f.op.ran.obj ℱ.obj).map
        (comparisonChartHom B S hS p q eF eG f fSpace ha d').op
        ((f.op.ran.obj ℱ.obj).map ((restrictionFunctor B S hS G q eG).map j).op s) =
      (f.op.ran.obj ℱ.obj).map
        (f.map ((restrictionFunctor B S hS F p eF).map i)).op
        ((f.op.ran.obj ℱ.obj).map
          (comparisonChartHom B S hS p q eF eG f fSpace ha d).op s) := by
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hch]
  change (f.op.ranCounit.app ℱ.obj).app _
      ((f.op.ran.obj ℱ.obj).map
          (comparisonChartHom B S hS p q eF eG f fSpace ha d').op
        ((f.op.ran.obj ℱ.obj).map
          ((restrictionFunctor B S hS G q eG).map j).op s)) = _
  rw [key]
  exact NatTrans.naturality_apply (f.op.ranCounit.app ℱ.obj)
    ((restrictionFunctor B S hS F p eF).map i).op _

/-- The maps on sections of
`AlgebraicGeometry.Space.restrictedDirectImageComparisonSections` are natural in the
sheaf `ℱ`. -/
theorem restrictedDirectImageComparisonSections_map
    (ℱ 𝒢 : Sheaf (BigFppfOver.associatedTopology B S hS p .etale) (Type u)) (η : ℱ ⟶ 𝒢)
    (d : ChartDiagram B S hS F G fSpace.hom)
    (s : (f.op.ran.obj ℱ.obj).obj
      (op ((restrictionFunctor B S hS G q eG).obj d.V))) :
    restrictedDirectImageComparisonSections B S hS F G p q hF hG eF eG f fSpace ha 𝒢 d
        ((f.op.ran.map η.hom).app
          (op ((restrictionFunctor B S hS G q eG).obj d.V)) s) =
      η.hom.app (op ((restrictionFunctor B S hS F p eF).obj d.U))
        (restrictedDirectImageComparisonSections B S hS F G p q hF hG eF eG f fSpace ha ℱ d s) := by
  have h1 := NatTrans.naturality_apply (f.op.ran.map η.hom)
    (comparisonChartHom B S hS p q eF eG f fSpace ha d).op s
  have h2 := ConcreteCategory.congr_hom
    (NatTrans.congr_app (f.op.ranCounit.naturality η.hom)
      (op ((restrictionFunctor B S hS F p eF).obj d.U)))
    ((f.op.ran.obj ℱ.obj).map
      (comparisonChartHom B S hS p q eF eG f fSpace ha d).op s)
  change (f.op.ranCounit.app 𝒢.obj).app _
      ((f.op.ran.obj 𝒢.obj).map
          (comparisonChartHom B S hS p q eF eG f fSpace ha d).op
        ((f.op.ran.map η.hom).app _ s)) = _
  rw [← h1]
  exact h2

/-- The `fSpace`-map of Stacks 03G3 out of which the comparison map of equation 075M is built:
on a diagram of étale scheme charts it is
`AlgebraicGeometry.Space.restrictedDirectImageComparisonSections`. -/
noncomputable def restrictedDirectImageComparisonFMap
    (ℱ : Sheaf (BigFppfOver.associatedTopology B S hS p .etale) (Type u)) :
    FMap B S hS F G fSpace.hom
      ((restrictionSheafFunctor B S hS F p hp eF).obj ℱ).obj
      ((restrictionSheafFunctor B S hS G q hq eG).obj
        ((etaleDirectImage B S hS p q hp f hf).obj ℱ)).obj where
  app := restrictedDirectImageComparisonSections B S hS F G p q hF hG eF eG f fSpace ha ℱ
  naturality :=
    restrictedDirectImageComparisonSections_naturality B S hS F G p q hF hG eF eG f fSpace ha ℱ

/-- **Equation 075M, the comparison map.** The map
`π_{G,*}f_*ℱ ⟶ f_{small,*}(π_{F,*}ℱ)` comparing the two legs of the square of Stacks 073N on a
sheaf `ℱ` of sets on the inherited étale site of `𝒳`. -/
noncomputable def restrictedDirectImageComparisonHom
    (ℱ : Sheaf (BigFppfOver.associatedTopology B S hS p .etale) (Type u)) :
    (restrictionSheafFunctor B S hS G q hq eG).obj
        ((etaleDirectImage B S hS p q hp f hf).obj ℱ) ⟶
      (smallEtaleRingedToposHom B S hS fSpace).toToposHom.pushforward.obj
        ((restrictionSheafFunctor B S hS F p hp eF).obj ℱ) :=
  fMapEquivPushforwardHom_ringUniverse B S hS fSpace
    ((restrictionSheafFunctor B S hS F p hp eF).obj ℱ)
    ((restrictionSheafFunctor B S hS G q hq eG).obj
      ((etaleDirectImage B S hS p q hp f hf).obj ℱ))
    (restrictedDirectImageComparisonFMap B S hS F G p q hp hq hF hG eF eG f hf fSpace ha ℱ)

/-- **Equation 075M, naturality of the comparison map in the sheaf.** -/
theorem restrictedDirectImageComparisonHom_naturality
    (ℱ 𝒢 : Sheaf (BigFppfOver.associatedTopology B S hS p .etale) (Type u)) (η : ℱ ⟶ 𝒢) :
    (restrictionSheafFunctor B S hS G q hq eG).map
          ((etaleDirectImage B S hS p q hp f hf).map η) ≫
        restrictedDirectImageComparisonHom B S hS F G p q hp hq hF hG eF eG f hf fSpace ha 𝒢 =
      restrictedDirectImageComparisonHom B S hS F G p q hp hq hF hG eF eG f hf fSpace ha ℱ ≫
        (smallEtaleRingedToposHom B S hS fSpace).toToposHom.pushforward.map
          ((restrictionSheafFunctor B S hS F p hp eF).map η) := by
  have hfmap : FMap.compTarget B S hS fSpace
        (restrictedDirectImageComparisonFMap B S hS F G p q hp hq hF hG eF eG f hf fSpace ha 𝒢)
        ((restrictionSheafFunctor B S hS G q hq eG).map
          ((etaleDirectImage B S hS p q hp f hf).map η)).hom =
      FMap.compSource B S hS fSpace
        (restrictedDirectImageComparisonFMap B S hS F G p q hp hq hF hG eF eG f hf fSpace ha ℱ)
        ((restrictionSheafFunctor B S hS F p hp eF).map η).hom :=
    FMap.ext_app B S hS fSpace (by
      funext d s
      exact restrictedDirectImageComparisonSections_map B S hS F G p q hF hG eF eG f fSpace
        ha ℱ 𝒢 η d s)
  exact Eq.trans
    (fMapEquivPushforwardHom_ringUniverse_target_map B S hS fSpace
      ((restrictionSheafFunctor B S hS F p hp eF).obj 𝒢)
      ((restrictionSheafFunctor B S hS G q hq eG).obj
        ((etaleDirectImage B S hS p q hp f hf).obj 𝒢))
      ((restrictionSheafFunctor B S hS G q hq eG).obj
        ((etaleDirectImage B S hS p q hp f hf).obj ℱ))
      ((restrictionSheafFunctor B S hS G q hq eG).map
        ((etaleDirectImage B S hS p q hp f hf).map η))
      (restrictedDirectImageComparisonFMap B S hS F G p q hp hq hF hG eF eG f hf fSpace ha 𝒢))
    (Eq.trans
      (congrArg (fun ζ ↦ fMapEquivPushforwardHom_ringUniverse B S hS fSpace
        ((restrictionSheafFunctor B S hS F p hp eF).obj 𝒢)
        ((restrictionSheafFunctor B S hS G q hq eG).obj
          ((etaleDirectImage B S hS p q hp f hf).obj ℱ)) ζ) hfmap)
      (fMapEquivPushforwardHom_ringUniverse_source_map B S hS fSpace
        ((restrictionSheafFunctor B S hS F p hp eF).obj ℱ)
        ((restrictionSheafFunctor B S hS F p hp eF).obj 𝒢)
        ((restrictionSheafFunctor B S hS G q hq eG).obj
          ((etaleDirectImage B S hS p q hp f hf).obj ℱ))
        ((restrictionSheafFunctor B S hS F p hp eF).map η)
        (restrictedDirectImageComparisonFMap B S hS F G p q hp hq hF hG eF eG f hf fSpace ha ℱ)))

/-- **Equation 075M.** The comparison of the two direct images around the square of
Stacks 073N: the canonical map `π_{G,*}f_*ℱ ⟶ f_{small,*}(ℱ|_{F_étale})`, natural in `ℱ`, whose
source is the left-hand side `(f_*ℱ)|_{G_étale}` of equation 075M and whose target is its
right-hand side.

Its value on sections over a diagram of étale scheme charts is
`AlgebraicGeometry.Space.restrictedDirectImageComparisonSections`. That it is an isomorphism,
which is what the displayed equality of the source asserts, is
`AlgebraicGeometry.Space.isIso_restrictedDirectImageComparison` of
`StacksFrontier/AlgebraicGeometry/Stacks/RestrictionDirectImageComparisonIso.lean`. -/
@[stacks 075M "the comparison map between the two sides, natural in the sheaf: both sides of the
  equation are present -- the left-hand side `(f_*F)|_{G_etale}` as the direct image of
  `restrictionSquareFibredLeg` and the right-hand side `f_{small,*}(F|_{F_etale})` as that of
  `restrictionSquareSpaceLeg` -- together with the canonical map from the first to the second and
  its naturality in the sheaf. That this map is an ISOMORPHISM, which is what the displayed
  equality asserts, is `isIso_restrictedDirectImageComparison` of
  StacksFrontier/AlgebraicGeometry/Stacks/RestrictionDirectImageComparisonIso.lean, which reduces it
  by `isIso_restrictedDirectImageComparison_of_bijective` to a bijection on sections over one
  etale scheme chart of G at a time.
  The compatibility `ha` of the 1-morphism f with the morphism fSpace of algebraic spaces through
  the two chosen presentations is a hypothesis; it is realized for every fSpace by
  `exists_comparisonChartFunctorIso`"]
noncomputable def restrictedDirectImageComparison :
    (restrictionSquareFibredLeg B S hS G p q hp hq hG eG f hf).toToposHom.pushforward ⟶
      (restrictionSquareSpaceLeg B S hS F G p hp hF hG eF fSpace).toToposHom.pushforward where
  app ℱ := restrictedDirectImageComparisonHom B S hS F G p q hp hq hF hG eF eG f hf fSpace ha ℱ
  naturality ℱ 𝒢 η :=
    restrictedDirectImageComparisonHom_naturality B S hS F G p q hp hq hF hG eF eG f hf
      fSpace ha ℱ 𝒢 η

/-- The component of `restrictedDirectImageComparison` at a sheaf `ℱ` is
`restrictedDirectImageComparisonHom` at `ℱ`. -/
@[simp] theorem restrictedDirectImageComparison_app
    (ℱ : Sheaf (BigFppfOver.associatedTopology B S hS p .etale) (Type u)) :
    (restrictedDirectImageComparison B S hS F G p q hp hq hF hG eF eG f hf fSpace ha).app ℱ =
      restrictedDirectImageComparisonHom B S hS F G p q hp hq hF hG eF eG f hf fSpace ha ℱ :=
  rfl

/-- **The right-hand side of equation 075M at a chart, as an equalizer.**  The target of the
comparison map is `f_{small,*}(ℱ|_{F_étale})`; its sections over an étale scheme chart `V` of
`G` are the equalizer of the sections of `ℱ|_{F_étale}` over an étale scheme chart `W` of `F`
covering `F ×_G V` and over a chart `W'` presenting the self-fibre product of `W` over
`F ×_G V`.

This is `AlgebraicGeometry.Space.exists_smallEtaleDirectImageChartEqualizerEquiv` — Tag 03H7 for
the direct image on the small étale sites — specialized at the chart of equation 075M.  The
target of the comparison is that direct image on the nose: the direct image of the geometric
morphism underlying `AlgebraicGeometry.Space.smallEtaleRingedToposHom` is the spaces-étale
direct image of Stacks 03G2 conjugated by the comparison equivalences of Stacks 03G1, which is
how `AlgebraicGeometry.Space.smallEtaleDirectImage` is defined. -/
@[stacks 075M "the right-hand side f_{small,*}(F|_{F_etale}), as an equalizer of sections of \
F|_{F_etale} over two etale scheme charts of F, at a chart V of G"]
theorem exists_restrictedDirectImageComparisonTarget_equalizer
    (ℱ : Sheaf (BigFppfOver.associatedTopology B S hS p .etale) (Type u))
    (V : SmallEtale B S hS G) :
    ∃ (W W' : SmallEtale B S hS F) (a b : W' ⟶ W),
      Nonempty (((smallEtaleRingedToposHom B S hS fSpace).toToposHom.pushforward.obj
            ((restrictionSheafFunctor B S hS F p hp eF).obj ℱ)).obj.obj (op V) ≃
        {y : ((restrictionSheafFunctor B S hS F p hp eF).obj ℱ).obj.obj (op W) //
          ((restrictionSheafFunctor B S hS F p hp eF).obj ℱ).obj.map a.op y =
            ((restrictionSheafFunctor B S hS F p hp eF).obj ℱ).obj.map b.op y}) :=
  exists_smallEtaleDirectImageChartEqualizerEquiv B S hS fSpace
    ((restrictionSheafFunctor B S hS F p hp eF).obj ℱ) V

/-- **Invertibility of the comparison map of equation 075M, reduced to per-chart
bijectivity.**  The canonical comparison map is an isomorphism as soon as, for every sheaf `ℱ`
and every étale scheme chart `V` of `G`, it is a bijection on sections over `V`.

A natural transformation is invertible when each of its components is
(`CategoryTheory.NatIso.isIso_of_isIso_app`), and a morphism of sheaves of sets is invertible
when each of its components is a bijection (`CategoryTheory.Sheaf.isIso_of_bijective_app`).  So
this reduces Stacks 073N, through
`AlgebraicGeometry.Space.restrictionRingedSquareOfIsIso`, to a statement about sections over one
chart at a time — which is the form in which
`AlgebraicGeometry.Space.restrictedDirectImageChartEquiv` and
`AlgebraicGeometry.Space.exists_restrictedDirectImageComparisonTarget_equalizer` present the two
sides. -/
theorem isIso_restrictedDirectImageComparison_of_bijective
    (hbij : ∀ (ℱ : Sheaf (BigFppfOver.associatedTopology B S hS p .etale) (Type u))
        (V : SmallEtale B S hS G),
      Function.Bijective
        ((restrictedDirectImageComparisonHom B S hS F G p q hp hq hF hG eF eG f hf fSpace
          ha ℱ).hom.app (op V))) :
    IsIso (restrictedDirectImageComparison B S hS F G p q hp hq hF hG eF eG f hf fSpace ha) := by
  have : ∀ ℱ, IsIso ((restrictedDirectImageComparison B S hS F G p q hp hq hF hG eF eG f hf
      fSpace ha).app ℱ) := fun ℱ =>
    Sheaf.isIso_of_bijective_app _ fun U => hbij ℱ U.unop
  exact NatIso.isIso_of_isIso_app _

/-- The comparison of the two direct images of the square of Stacks 073N, as an isomorphism,
given that the canonical comparison map
`AlgebraicGeometry.Space.restrictedDirectImageComparison` is invertible.

Invertibility is exactly what the source's proof of Stacks 073N spends its length on: the
identification of the 2-fibre product `(Sch/V)_{fppf} ×_𝒴 𝒳` with the split category fibred in
groupoids of the algebraic space `V ×_G F`, and then, when `V ×_G F` is not a scheme, the
comparison of the equalizer presentations of Properties of Spaces 03H7 and 03G2. The comparison
*map* needs neither, which is why it is unconditional above.

Of those two, the 2-fibre-product identification is available in substance, and the
category-theoretic inputs to the equalizer presentations are in the library — including
Stacks 0792, now instantiated as
`Stacks.Sites.GlobalSectionsAsEqualizer.globalSectionsForkIsLimitOfCoversTop`, and invariance of
global sections under an equivalence, `CategoryTheory.Presheaf.globalSectionsPrecompEquiv`. The
presentation of the *right-hand* side at the chart of equation 075M is assembled:
`AlgebraicGeometry.Space.exists_restrictedDirectImageComparisonTarget_equalizer`, and so is the
matching presentation of the left-hand side,
`AlgebraicGeometry.Space.exists_restrictedDirectImageComparisonSource_equalizer`.

The hypothesis `hiso` is no longer open: it is reduced to per-chart bijectivity of the comparison
by `AlgebraicGeometry.Space.isIso_restrictedDirectImageComparison_of_bijective`, and that
bijectivity is proved in
`StacksFrontier/AlgebraicGeometry/Stacks/RestrictionDirectImageComparisonIso.lean`, so `hiso` is
available unconditionally as
`AlgebraicGeometry.Space.isIso_restrictedDirectImageComparison`. -/
noncomputable def restrictedDirectImageComparisonIso
    (hiso : IsIso (restrictedDirectImageComparison B S hS F G p q hp hq hF hG eF eG f hf
      fSpace ha)) :
    (restrictionSquareFibredLeg B S hS G p q hp hq hG eG f hf).toToposHom.pushforward ≅
      (restrictionSquareSpaceLeg B S hS F G p hp hF hG eF fSpace).toToposHom.pushforward :=
  letI := hiso
  asIso (restrictedDirectImageComparison B S hS F G p q hp hq hF hG eF eG f hf fSpace ha)

/-- **Stacks 073N given invertibility of the comparison map.** The square of ringed topoi of
Stacks 073N commutes as soon as the canonical comparison map
`AlgebraicGeometry.Space.restrictedDirectImageComparison` of the two direct images is
invertible and is compatible with the two structure maps.

This is `AlgebraicGeometry.Space.restrictionRingedSquare` with its hypothesis `cmp` — the
comparison isomorphism, which that declaration takes as data — replaced by invertibility of the
*canonical* comparison constructed here. So the `cmp` argument of `restrictionRingedSquare` is
no longer an arbitrary choice: it is `restrictedDirectImageComparison`, and what remains
open is only that this one map is an isomorphism.

The second hypothesis `hsq` is no longer open either: see
`AlgebraicGeometry.Space.restrictedDirectImageComparison_structureSheafCompatible`, and
`AlgebraicGeometry.Space.restrictionRingedSquareOfIsIsoOfIsHomLift` for this declaration with
`hsq` already supplied. -/
noncomputable def restrictionRingedSquareOfIsIso
    (hiso : IsIso (restrictedDirectImageComparison B S hS F G p q hp hq hF hG eF eG f hf fSpace ha))
    (hsq : RingedToposHom.forgetFSharp (projectionRingedToposHom B S hS G q hq hG eG) ≫
        (projectionRingedToposHom B S hS G q hq hG eG).toToposHom.pushforward.map
          (RingedToposHom.forgetFSharp
            (FibredSite.ringedToposMorphism B S hS p q hp hq f hf .etale)) ≫
        (restrictedDirectImageComparison B S hS F G p q hp hq hF hG eF eG f hf fSpace ha).app
          ((FibredSite.associatedRingedTopos B S hS p hp .etale).forgetRing.obj
            (FibredSite.associatedRingedTopos B S hS p hp .etale).O) =
      RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B S hS fSpace) ≫
        (smallEtaleRingedToposHom B S hS fSpace).toToposHom.pushforward.map
          (RingedToposHom.forgetFSharp (projectionRingedToposHom B S hS F p hp hF eF))) :
    RingedToposHom.TwoIso
      (A := FibredSite.associatedRingedTopos B S hS p hp .etale)
      (B := smallEtaleRingedTopos B S hS ⟨G, hG⟩)
      (restrictionSquareFibredLeg B S hS G p q hp hq hG eG f hf)
      (restrictionSquareSpaceLeg B S hS F G p hp hF hG eF fSpace) :=
  restrictionRingedSquare B S hS F G p q hp hq hF hG eF eG f hf fSpace
    (restrictedDirectImageComparisonIso B S hS F G p q hp hq hF hG eF eG f hf fSpace ha hiso) hsq

/-! ### The structure-sheaf compatibility of the comparison map

The hypothesis `hsq` of `AlgebraicGeometry.Space.restrictionRingedSquareOfIsIso` asks that the
comparison map of equation 075M, read at the structure sheaf, carry the structure map of the leg
`π_G ∘ f` to that of the leg `f_small ∘ π_F`. The two results below cut that hypothesis down to a
statement about charts with no Kan extension and no chart correspondence left in it. -/

/-- **The structure map of a 1-morphism of fibred categories, read through the counit of the
right Kan extension that computes its direct image.**

For a morphism `h : f(Z) ⟶ T` of `𝒴`, restricting a section of `𝒪_𝒴` over `T` along the
structure map `𝒪_𝒴 ⟶ f_*𝒪_𝒳` of Stacks 06TW, then along `h`, then applying the counit of the
right Kan extension at `Z`, is restriction of the section along `h` followed by the canonical
identification `f⁻¹𝒪_𝒴 ⟶ 𝒪_𝒳` of
`AlgebraicGeometry.FibredSite.inverseImageStructureSheaf_eq`.

This is the triangle identity of the adjunction `f⁻¹ ⊣ f_*` of Stacks 06NW together with
naturality of its unit and of the Kan-extension counit; the direct-image form of the structure
map is the adjunct of its inverse-image form
(`AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget_homEquiv`), which is what puts the
unit in front of it. It is the computation the structure-sheaf half of Stacks 073N needs on the
leg `π_G ∘ f`: the comparison map of equation 075M is built out of exactly this counit and
exactly this restriction (`AlgebraicGeometry.Space.restrictedDirectImageComparisonSections`). -/
theorem ranCounit_app_forgetFSharp_ringedToposMorphism (Z : 𝒳) (T : 𝒴) (k : f.obj Z ⟶ T)
    (x : ((FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).forgetRing.obj
      (FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).O).obj.obj (op T)) :
    (f.op.ranCounit.app ((FibredSite.associatedRingedTopos B S hS p hp
      SiteKind.etale).forgetRing.obj
      (FibredSite.associatedRingedTopos B S hS p hp SiteKind.etale).O).obj).app (op Z)
        ((f.op.ran.obj ((FibredSite.associatedRingedTopos B S hS p hp SiteKind.etale).forgetRing.obj
      (FibredSite.associatedRingedTopos B S hS p hp SiteKind.etale).O).obj).map k.op
          ((RingedToposHom.forgetFSharp
            (FibredSite.ringedToposMorphism B S hS p q hp hq f hf SiteKind.etale)).hom.app
              (op T) x)) =
      ((FibredSite.associatedRingedTopos B S hS p hp SiteKind.etale).forgetRing.map
      (FibredSite.ringedToposMorphism B S hS p q hp hq f hf
        SiteKind.etale).fSharpInverseImage).hom.app (op Z)
          (((FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).forgetRing.obj
      (FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).O).obj.map k.op x) := by
  have hB : RingedToposHom.forgetFSharp
    (FibredSite.ringedToposMorphism B S hS p q hp hq f hf SiteKind.etale) =
      (FibredSite.ringedToposMorphism B S hS p q hp hq f hf SiteKind.etale).toToposHom.adj.unit.app
        ((FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).forgetRing.obj
      (FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).O) ≫
        (FibredSite.ringedToposMorphism B S hS p q hp hq f hf
          SiteKind.etale).toToposHom.pushforward.map
            ((FibredSite.associatedRingedTopos B S hS p hp SiteKind.etale).forgetRing.map
      (FibredSite.ringedToposMorphism B S hS p q hp hq f hf SiteKind.etale).fSharpInverseImage) :=
    Eq.trans
      ((congrArg (fun z ↦ (FibredSite.ringedToposMorphism B S hS p q hp hq f hf
        SiteKind.etale).toToposHom.adj.homEquiv
          ((FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).forgetRing.obj
      (FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).O)
        ((FibredSite.associatedRingedTopos B S hS p hp SiteKind.etale).forgetRing.obj
      (FibredSite.associatedRingedTopos B S hS p hp SiteKind.etale).O) z)
          (RingedToposHom.fSharpInverseImage_forget_homEquiv
            (FibredSite.ringedToposMorphism B S hS p q hp hq f hf SiteKind.etale))).trans
        (Equiv.apply_symm_apply _ _)).symm
      (Adjunction.homEquiv_apply
        (FibredSite.ringedToposMorphism B S hS p q hp hq f hf SiteKind.etale).toToposHom.adj _ _ _)
  have h1 : (RingedToposHom.forgetFSharp
    (FibredSite.ringedToposMorphism B S hS p q hp hq f hf SiteKind.etale)).hom.app (op T) x =
      ((FibredSite.ringedToposMorphism B S hS p q hp hq f hf
        SiteKind.etale).toToposHom.pushforward.map
          ((FibredSite.associatedRingedTopos B S hS p hp SiteKind.etale).forgetRing.map
      (FibredSite.ringedToposMorphism B S hS p q hp hq f hf
        SiteKind.etale).fSharpInverseImage)).hom.app (op T)
        (((FibredSite.ringedToposMorphism B S hS p q hp hq f hf
          SiteKind.etale).toToposHom.adj.unit.app
            ((FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).forgetRing.obj
      (FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).O)).hom.app (op T) x) :=
    CategoryTheory.Sheaf.hom_congr_app_apply hB (op T) x
  have h2 := (NatTrans.naturality_apply
    ((FibredSite.ringedToposMorphism B S hS p q hp hq f hf
      SiteKind.etale).toToposHom.pushforward.map
        ((FibredSite.associatedRingedTopos B S hS p hp SiteKind.etale).forgetRing.map
      (FibredSite.ringedToposMorphism B S hS p q hp hq f hf SiteKind.etale).fSharpInverseImage)).hom
        k.op
      (((FibredSite.ringedToposMorphism B S hS p q hp hq f hf
        SiteKind.etale).toToposHom.adj.unit.app
          ((FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).forgetRing.obj
      (FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).O)).hom.app (op T) x)).symm
  have h3 := ConcreteCategory.congr_hom
    (NatTrans.congr_app (f.op.ranCounit.naturality
      ((FibredSite.associatedRingedTopos B S hS p hp SiteKind.etale).forgetRing.map
      (FibredSite.ringedToposMorphism B S hS p q hp hq f hf SiteKind.etale).fSharpInverseImage).hom)
        (op Z))
    ((f.op.ran.obj ((FibredSite.ringedToposMorphism B S hS p q hp hq f hf
      SiteKind.etale).toToposHom.inverseImage.obj
        ((FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).forgetRing.obj
      (FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).O)).obj).map k.op
      (((FibredSite.ringedToposMorphism B S hS p q hp hq f hf
        SiteKind.etale).toToposHom.adj.unit.app
          ((FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).forgetRing.obj
      (FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).O)).hom.app (op T) x))
  have h4 : (f.op.ranCounit.app
          ((FibredSite.ringedToposMorphism B S hS p q hp hq f hf
            SiteKind.etale).toToposHom.inverseImage.obj
              ((FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).forgetRing.obj
      (FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).O)).obj).app (op Z)
        ((f.op.ran.obj ((FibredSite.ringedToposMorphism B S hS p q hp hq f hf
          SiteKind.etale).toToposHom.inverseImage.obj
            ((FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).forgetRing.obj
      (FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).O)).obj).map k.op
          (((FibredSite.ringedToposMorphism B S hS p q hp hq f hf
            SiteKind.etale).toToposHom.adj.unit.app
              ((FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).forgetRing.obj
      (FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).O)).hom.app (op T) x)) =
      ((FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).forgetRing.obj
      (FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).O).obj.map k.op x := by
    refine Eq.trans (congrArg (fun y ↦ (f.op.ranCounit.app
        ((FibredSite.ringedToposMorphism B S hS p q hp hq f hf
          SiteKind.etale).toToposHom.inverseImage.obj
            ((FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).forgetRing.obj
      (FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).O)).obj).app (op Z) y)
      (NatTrans.naturality_apply
        ((FibredSite.ringedToposMorphism B S hS p q hp hq f hf
          SiteKind.etale).toToposHom.adj.unit.app
            ((FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).forgetRing.obj
      (FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).O)).hom k.op x).symm) ?_
    exact CategoryTheory.Sheaf.hom_congr_app_apply
      ((FibredSite.ringedToposMorphism B S hS p q hp hq f hf
        SiteKind.etale).toToposHom.adj.left_triangle_components
          ((FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).forgetRing.obj
      (FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).O)) (op Z) _
  rw [h1]
  erw [h2]
  exact h3.trans (congrArg (fun y ↦
    ((FibredSite.associatedRingedTopos B S hS p hp SiteKind.etale).forgetRing.map
      (FibredSite.ringedToposMorphism B S hS p q hp hq f hf
        SiteKind.etale).fSharpInverseImage).hom.app (op Z) y) h4)

/-- **The structure-sheaf compatibility of the comparison map of equation 075M, reduced to
charts.** The hypothesis `hsq` of `AlgebraicGeometry.Space.restrictionRingedSquareOfIsIso` holds
if and only if, over every commutative diagram `d` of étale scheme charts, the three canonical
structure-sheaf identifications of the square — that of `π_G`, that of `π_F`, and the
identification `f⁻¹𝒪_𝒴 ⟶ 𝒪_𝒳` of Stacks 06TW — carry restriction of regular functions along the
morphism `AlgebraicGeometry.Space.comparisonChartHom` of `𝒴` to restriction along the vertical
morphism of schemes `d.g` of the diagram.

Both sides of `hsq` are homomorphisms into a small étale direct image, so the chart
correspondence of Stacks 03G8 — a bijection — identifies them with `f`-maps, and two `f`-maps
agree exactly when they agree over every diagram of charts. The left-hand side becomes the
comparison map's own `f`-map precomposed on the chart of the target
(`AlgebraicGeometry.Space.fMapEquivPushforwardHom_ringUniverse_target_map`), the right-hand side
the structure `f`-map of `f_small` postcomposed on the chart of the source
(`AlgebraicGeometry.Space.fMapEquivPushforwardHom_ringUniverse_source_map`), whose value is
pullback of regular functions along `d.g` by Stacks 03G8
(`AlgebraicGeometry.Space.structureFMap_app`); and the Kan extension on the left is discharged by
`ranCounit_app_forgetFSharp_ringedToposMorphism`, which is what leaves no Kan extension in the
right-hand side of this equivalence.

The remaining statement is the assertion that the underlying morphism of schemes of
`comparisonChartHom` is `d.g`. That is *not* automatic for an arbitrary pair `(fSpace, ha)`:
`comparisonChartHom` begins with `ha.hom.app d.U.1`, whose image under `q` is an automorphism of
the chart's base scheme which the hypothesis `ha` does not constrain. It is the verticality
hypothesis `hab` of `AlgebraicGeometry.Space.isHomLift_comparisonMorphism`, which holds at the
1-morphism's induced morphism of algebraic spaces. -/
theorem restrictedDirectImageComparison_structureSheafCompatible_iff :
    (RingedToposHom.forgetFSharp (projectionRingedToposHom B S hS G q hq hG eG) ≫
          (projectionRingedToposHom B S hS G q hq hG eG).toToposHom.pushforward.map
            (RingedToposHom.forgetFSharp
              (FibredSite.ringedToposMorphism B S hS p q hp hq f hf SiteKind.etale)) ≫
          (restrictedDirectImageComparison B S hS F G p q hp hq hF hG eF eG f hf
            fSpace ha).app ((FibredSite.associatedRingedTopos B S hS p hp
              SiteKind.etale).forgetRing.obj
      (FibredSite.associatedRingedTopos B S hS p hp SiteKind.etale).O) =
        RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B S hS fSpace) ≫
          (smallEtaleRingedToposHom B S hS fSpace).toToposHom.pushforward.map
            (RingedToposHom.forgetFSharp (projectionRingedToposHom B S hS F p hp hF eF))) ↔
      ∀ (d : ChartDiagram B S hS F G fSpace.hom) (s : ((smallEtaleRingedTopos B S hS
        (⟨G, hG⟩ : AlgebraicSpaces B S hS)).forgetRing.obj
      (smallEtaleRingedTopos B S hS (⟨G, hG⟩ : AlgebraicSpaces B S hS)).O).obj.obj (op d.V)),
        ((FibredSite.associatedRingedTopos B S hS p hp SiteKind.etale).forgetRing.map
      (FibredSite.ringedToposMorphism B S hS p q hp hq f hf
        SiteKind.etale).fSharpInverseImage).hom.app
            (op ((restrictionFunctor B S hS F p eF).obj d.U))
            (((FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).forgetRing.obj
      (FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).O).obj.map
              (comparisonChartHom B S hS p q eF eG f fSpace ha d).op
              ((RingedToposHom.forgetFSharp (projectionRingedToposHom B S hS G q hq hG eG)).hom.app
                (op d.V) s)) =
          (RingedToposHom.forgetFSharp (projectionRingedToposHom B S hS F p hp hF eF)).hom.app
            (op d.U)
            (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map d.g)) s) := by
  have hstr : (fMapEquivPushforwardHom_ringUniverse B S hS fSpace (structureSetSheaf B S hS
    (⟨F, hF⟩ : AlgebraicSpaces B S hS)) ((smallEtaleRingedTopos B S hS
      (⟨G, hG⟩ : AlgebraicSpaces B S hS)).forgetRing.obj
      (smallEtaleRingedTopos B S hS (⟨G, hG⟩ : AlgebraicSpaces B S hS)).O))
        (structureFMap B S hS fSpace) =
      RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B S hS fSpace) :=
    (fMapEquivPushforwardHom_ringUniverse B S hS fSpace (structureSetSheaf B S hS
      (⟨F, hF⟩ : AlgebraicSpaces B S hS)) ((smallEtaleRingedTopos B S hS
        (⟨G, hG⟩ : AlgebraicSpaces B S hS)).forgetRing.obj
      (smallEtaleRingedTopos B S hS (⟨G, hG⟩ : AlgebraicSpaces B S hS)).O)).apply_symm_apply _
  have hL : RingedToposHom.forgetFSharp (projectionRingedToposHom B S hS G q hq hG eG) ≫
        (projectionRingedToposHom B S hS G q hq hG eG).toToposHom.pushforward.map
          (RingedToposHom.forgetFSharp
            (FibredSite.ringedToposMorphism B S hS p q hp hq f hf SiteKind.etale)) ≫
        (restrictedDirectImageComparison B S hS F G p q hp hq hF hG eF eG f hf
          fSpace ha).app ((FibredSite.associatedRingedTopos B S hS p hp
            SiteKind.etale).forgetRing.obj
      (FibredSite.associatedRingedTopos B S hS p hp SiteKind.etale).O) =
      (fMapEquivPushforwardHom_ringUniverse B S hS fSpace
        ((restrictionSheafFunctor B S hS F p hp eF).obj
          ((FibredSite.associatedRingedTopos B S hS p hp SiteKind.etale).forgetRing.obj
      (FibredSite.associatedRingedTopos B S hS p hp SiteKind.etale).O))
        ((smallEtaleRingedTopos B S hS (⟨G, hG⟩ : AlgebraicSpaces B S hS)).forgetRing.obj
      (smallEtaleRingedTopos B S hS (⟨G, hG⟩ : AlgebraicSpaces B S hS)).O))
        (FMap.compTarget B S hS fSpace
          (restrictedDirectImageComparisonFMap B S hS F G p q hp hq hF hG eF eG f hf fSpace ha
            ((FibredSite.associatedRingedTopos B S hS p hp SiteKind.etale).forgetRing.obj
      (FibredSite.associatedRingedTopos B S hS p hp SiteKind.etale).O)) (RingedToposHom.forgetFSharp
        (projectionRingedToposHom B S hS G q hq hG eG) ≫
          (projectionRingedToposHom B S hS G q hq hG eG).toToposHom.pushforward.map
      (RingedToposHom.forgetFSharp
        (FibredSite.ringedToposMorphism B S hS p q hp hq f hf SiteKind.etale))).hom) :=
    Eq.trans
      (Category.assoc (RingedToposHom.forgetFSharp (projectionRingedToposHom B S hS G q hq hG eG))
        ((projectionRingedToposHom B S hS G q hq hG eG).toToposHom.pushforward.map
          (RingedToposHom.forgetFSharp
            (FibredSite.ringedToposMorphism B S hS p q hp hq f hf SiteKind.etale)))
        ((restrictedDirectImageComparison B S hS F G p q hp hq hF hG eF eG f hf
          fSpace ha).app ((FibredSite.associatedRingedTopos B S hS p hp
            SiteKind.etale).forgetRing.obj
      (FibredSite.associatedRingedTopos B S hS p hp SiteKind.etale).O))).symm
      (fMapEquivPushforwardHom_ringUniverse_target_map B S hS fSpace
        ((restrictionSheafFunctor B S hS F p hp eF).obj
          ((FibredSite.associatedRingedTopos B S hS p hp SiteKind.etale).forgetRing.obj
      (FibredSite.associatedRingedTopos B S hS p hp SiteKind.etale).O))
        ((restrictionSheafFunctor B S hS G q hq eG).obj ((etaleDirectImage B S hS p q hp f hf).obj
          ((FibredSite.associatedRingedTopos B S hS p hp SiteKind.etale).forgetRing.obj
      (FibredSite.associatedRingedTopos B S hS p hp SiteKind.etale).O)))
        ((smallEtaleRingedTopos B S hS (⟨G, hG⟩ : AlgebraicSpaces B S hS)).forgetRing.obj
      (smallEtaleRingedTopos B S hS (⟨G, hG⟩ : AlgebraicSpaces B S hS)).O)
        (RingedToposHom.forgetFSharp (projectionRingedToposHom B S hS G q hq hG eG) ≫
          (projectionRingedToposHom B S hS G q hq hG eG).toToposHom.pushforward.map
      (RingedToposHom.forgetFSharp
        (FibredSite.ringedToposMorphism B S hS p q hp hq f hf SiteKind.etale)))
          (restrictedDirectImageComparisonFMap B S hS F G p q hp hq hF hG eF eG f hf fSpace ha
            ((FibredSite.associatedRingedTopos B S hS p hp SiteKind.etale).forgetRing.obj
      (FibredSite.associatedRingedTopos B S hS p hp SiteKind.etale).O)))
  have hR : RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B S hS fSpace) ≫
        (smallEtaleRingedToposHom B S hS fSpace).toToposHom.pushforward.map
          (RingedToposHom.forgetFSharp (projectionRingedToposHom B S hS F p hp hF eF)) =
      (fMapEquivPushforwardHom_ringUniverse B S hS fSpace
        ((restrictionSheafFunctor B S hS F p hp eF).obj
          ((FibredSite.associatedRingedTopos B S hS p hp SiteKind.etale).forgetRing.obj
      (FibredSite.associatedRingedTopos B S hS p hp SiteKind.etale).O))
        ((smallEtaleRingedTopos B S hS (⟨G, hG⟩ : AlgebraicSpaces B S hS)).forgetRing.obj
      (smallEtaleRingedTopos B S hS (⟨G, hG⟩ : AlgebraicSpaces B S hS)).O))
        (FMap.compSource B S hS fSpace (structureFMap B S hS fSpace) (RingedToposHom.forgetFSharp
          (projectionRingedToposHom B S hS F p hp hF eF)).hom) :=
    (Eq.trans
      (fMapEquivPushforwardHom_ringUniverse_source_map B S hS fSpace (structureSetSheaf B S hS
        (⟨F, hF⟩ : AlgebraicSpaces B S hS)) ((restrictionSheafFunctor B S hS F p hp eF).obj
          ((FibredSite.associatedRingedTopos B S hS p hp SiteKind.etale).forgetRing.obj
      (FibredSite.associatedRingedTopos B S hS p hp SiteKind.etale).O))
        ((smallEtaleRingedTopos B S hS (⟨G, hG⟩ : AlgebraicSpaces B S hS)).forgetRing.obj
      (smallEtaleRingedTopos B S hS (⟨G, hG⟩ : AlgebraicSpaces B S hS)).O)
        (RingedToposHom.forgetFSharp (projectionRingedToposHom B S hS F p hp hF eF))
          (structureFMap B S hS fSpace))
      (congrArg (fun z ↦ z ≫ (smallEtaleRingedToposHom B S hS
        fSpace).toToposHom.pushforward.map (RingedToposHom.forgetFSharp
          (projectionRingedToposHom B S hS F p hp hF eF))) hstr)).symm
  refine ((Eq.congr hL hR).trans (fMapEquivPushforwardHom_ringUniverse B S hS fSpace
    ((restrictionSheafFunctor B S hS F p hp eF).obj
      ((FibredSite.associatedRingedTopos B S hS p hp SiteKind.etale).forgetRing.obj
      (FibredSite.associatedRingedTopos B S hS p hp SiteKind.etale).O))
        ((smallEtaleRingedTopos B S hS (⟨G, hG⟩ : AlgebraicSpaces B S hS)).forgetRing.obj
      (smallEtaleRingedTopos B S hS
        (⟨G, hG⟩ : AlgebraicSpaces B S hS)).O)).apply_eq_iff_eq).trans ?_
  refine Iff.trans ⟨fun h d s ↦ congrArg (fun ξ ↦ ξ.app d s) h,
    fun h ↦ FMap.ext_app B S hS fSpace (funext fun d ↦ funext fun s ↦ h d s)⟩ ?_
  refine forall_congr' fun d ↦ forall_congr' fun s ↦ ?_
  exact Eq.congr
    (ranCounit_app_forgetFSharp_ringedToposMorphism B S hS p q hp hq f hf
      ((restrictionFunctor B S hS F p eF).obj d.U)
      ((restrictionFunctor B S hS G q eG).obj d.V)
      (comparisonChartHom B S hS p q eF eG f fSpace ha d)
      ((RingedToposHom.forgetFSharp (projectionRingedToposHom B S hS G q hq hG eG)).hom.app
        (op d.V) s))
    (congrArg (fun y ↦ (RingedToposHom.forgetFSharp
      (projectionRingedToposHom B S hS F p hp hF eF)).hom.app (op d.U) y)
      (structureFMap_app B S hS fSpace d s))

/-! ### The three structure-sheaf identifications on sections

The structure-sheaf half of Stacks 073N compares three canonical identifications: the structure
map of `π_F`, that of `π_G`, and the identification `f⁻¹𝒪_𝒴 ⟶ 𝒪_𝒳` of Stacks 06TW. Each is the
transport of a functor equality, read through `T ↦ T.op ⋙ (BigFppfOver.toScheme B S hS).op ⋙ Γ`,
and none is the identity. The two results below compute all three on sections: each is pullback
of regular functions along the identification of underlying objects of the big fppf site that the
functor equality provides. -/

/-- Restriction of regular functions along a transport of the big fppf site is a cast. -/
private theorem structureSheaf_map_eqToHom_cast {X Y : BigFppfOver B S hS} (e : X = Y)
    (z : (BigFppfOver.structureSheaf B S hS).obj.obj (op Y)) :
    (BigFppfOver.structureSheaf B S hS).obj.map (eqToHom e).op z =
      cast (congrArg (fun Z : BigFppfOver B S hS ↦
        ToType ((BigFppfOver.structureSheaf B S hS).obj.obj (op Z))) e).symm z := by
  cases e
  rw [eqToHom_refl, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- Two factorizations of one morphism, one of length three and one of length two, restrict
sections of a presheaf of rings in the same way. Stated with abstract objects, so that applying
it needs no unfolding of this development's sites; the length-two step it is built from is the
counterpart of the private helper of the same shape in
`StacksFrontier/AlgebraicGeometry/Stacks/RestrictionComparisonAlgebraicSpace.lean`. -/
private theorem ring_map_op_comp_congr {C : Type*} [Category C] (K : Cᵒᵖ ⥤ RingCat.{u})
    {X Y Z T X' : C} (x : X ⟶ Y) (y : Y ⟶ Z) (z : Z ⟶ T) (x' : X ⟶ X') (y' : X' ⟶ T)
    (h : x ≫ y ≫ z = x' ≫ y') (t : K.obj (op T)) :
    K.map x.op (K.map y.op (K.map z.op t)) = K.map x'.op (K.map y'.op t) := by
  have comp : ∀ {X₀ Y₀ Z₀ : C} (a : X₀ ⟶ Y₀) (b : Y₀ ⟶ Z₀) (w : K.obj (op Z₀)),
      K.map a.op (K.map b.op w) = K.map (a ≫ b).op w := fun a b w ↦ by
    rw [op_comp, K.map_comp]
    rfl
  exact Eq.trans (Eq.trans (congrArg (fun w ↦ K.map x.op w) (comp y z t)) (comp x (y ≫ z) t))
    (Eq.trans (congrArg (fun m : X ⟶ T ↦ K.map m.op t) h) (comp x' y' t).symm)

/-- Transport along an equality of sheaves of commutative rings, read on the underlying sheaves
of sets and on sections, is a cast. -/
private theorem sheafCompose_forget_eqToHom_app_cast {C : Type*} [Category C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget CommRingCat.{u})]
    {P Q : Sheaf J CommRingCat.{u}} (h : P = Q) (W : Cᵒᵖ) (z : ToType (P.obj.obj W)) :
    ((sheafCompose J (forget CommRingCat.{u})).map (eqToHom h)).hom.app W z =
      cast (congrArg (fun T : Sheaf J CommRingCat.{u} ↦ ToType (T.obj.obj W)) h) z := by
  cases h
  rw [eqToHom_refl, CategoryTheory.Functor.map_id]
  rfl

/-- **The structure map of `π_F` on underlying sheaves of sets is the transport of
Stacks 073M.** The comparison `Stacks.Sheaves.ToposPullback.restrictionCommRingIso` of the
inverse image of a sheaf of commutative rings with its restriction is the identity on underlying
sheaves of sets, so all that survives of the structure map of
`AlgebraicGeometry.Space.projectionRingedToposHom` is the transport along
`AlgebraicGeometry.Space.inverseImage_structureSheaf_eq`. -/
theorem forgetFSharp_projectionRingedToposHom_eq :
    RingedToposHom.forgetFSharp (projectionRingedToposHom B S hS F p hp hF eF) =
      (sheafCompose (SmallEtale.topology B S hS F) (forget CommRingCat.{u})).map
        (eqToHom (inverseImage_structureSheaf_eq B S hS F p hp eF hF).symm) := by
  let := restrictionFunctor_isContinuous B S hS F p hp eF
  change (sheafCompose (SmallEtale.topology B S hS F) (forget CommRingCat.{u})).map
      (eqToHom (inverseImage_structureSheaf_eq B S hS F p hp eF hF).symm ≫
        (restrictionCommRingIso (SmallEtale.topology B S hS F)
          (BigFppfOver.associatedTopology B S hS p .etale)
          (restrictionFunctor B S hS F p eF)
          (FibredSite.structureSheaf B S hS p hp .etale)).inv) = _
  rw [Functor.map_comp, restrictionCommRingIso_inv_forget]
  exact Category.comp_id _

/-- **The structure map of `π_F` on sections.** Over an étale scheme chart `W` of `F` the
structure map of `AlgebraicGeometry.Space.projectionRingedToposHom` is pullback of regular
functions along the identification of the object of the big fppf site underlying `u_F W` with
the one underlying `W`, which is `AlgebraicGeometry.Space.restrictionFunctor_comp`.

This is the first of the three structure-sheaf identifications that
`AlgebraicGeometry.Space.restrictedDirectImageComparison_structureSheafCompatible_chart` needs,
and — applied at `G`, `q` — also the second. None of the three is the identity: the functor
equality rests on the chosen equivalence's `MorphismOver.w`, so it does not hold by `rfl`, and
the two sides of the equality are not reducibly equal objects. It is the sheaf-level counterpart
of `AlgebraicGeometry.Space.etaleChartStructureHom_app`, which computes the module-level
coefficient map of the same identification with a 1-morphism folded in. -/
theorem forgetFSharp_projectionRingedToposHom_app (W : SmallEtale B S hS F)
    (s : ((smallEtaleRingedTopos B S hS (⟨F, hF⟩ : AlgebraicSpaces B S hS)).forgetRing.obj
      (smallEtaleRingedTopos B S hS (⟨F, hF⟩ : AlgebraicSpaces B S hS)).O).obj.obj (op W)) :
    (RingedToposHom.forgetFSharp (projectionRingedToposHom B S hS F p hp hF eF)).hom.app (op W)
        s =
      (BigFppfOver.structureSheaf B S hS).obj.map
        (eqToHom (Functor.congr_obj (restrictionFunctor_comp B S hS F p eF) W)).op s := by
  refine Eq.trans (congrArg (fun m ↦ m.hom.app (op W) s)
    (forgetFSharp_projectionRingedToposHom_eq B S hS F p hp hF eF)) ?_
  refine Eq.trans (sheafCompose_forget_eqToHom_app_cast
    (inverseImage_structureSheaf_eq B S hS F p hp eF hF).symm (op W) s) ?_
  exact (structureSheaf_map_eqToHom_cast B S hS
    (Functor.congr_obj (restrictionFunctor_comp B S hS F p eF) W) s).symm

/-- **The identification `f⁻¹𝒪_𝒴 ⟶ 𝒪_𝒳` of Stacks 06TW on underlying sheaves of sets is the
transport of the functor equality.** As for `π_F`, the comparison
`Stacks.Sheaves.ToposPullback.restrictionCommRingIso` is the identity on underlying sheaves of
sets, so what survives of `AlgebraicGeometry.FibredSite.ringedToposMorphism`'s inverse-image
structure map is the transport along
`AlgebraicGeometry.FibredSite.inverseImageStructureSheaf_eq`. -/
theorem forgetRing_map_fSharpInverseImage_eq :
    (FibredSite.associatedRingedTopos B S hS p hp SiteKind.etale).forgetRing.map
        (FibredSite.ringedToposMorphism B S hS p q hp hq f hf
          SiteKind.etale).fSharpInverseImage =
      (sheafCompose (BigFppfOver.associatedTopology B S hS p .etale)
          (forget CommRingCat.{u})).map
        (eqToHom (FibredSite.inverseImageStructureSheaf_eq B S hS p q hp hq f hf .etale)) := by
  let := hp.isFibered
  let := hq.isFibered
  let := (hf.isContinuous_and_isCocontinuous_inheritedTopology
    ((B.baseTopology SiteKind.etale).over (B.obj hS))).1
  refine Eq.trans (congrArg (fun m ↦
      (FibredSite.associatedRingedTopos B S hS p hp SiteKind.etale).forgetRing.map m)
    (FibredSite.ringedToposMorphism_fSharpInverseImage B S hS p q hp hq f hf SiteKind.etale)) ?_
  refine Eq.trans
    ((FibredSite.associatedRingedTopos B S hS p hp SiteKind.etale).forgetRing.map_comp _ _) ?_
  refine Eq.trans (congrArg (fun z ↦ z ≫
      (sheafCompose (BigFppfOver.associatedTopology B S hS p .etale)
          (forget CommRingCat.{u})).map
        (eqToHom (FibredSite.inverseImageStructureSheaf_eq B S hS p q hp hq f hf .etale)))
    (restrictionCommRingIso_hom_forget (BigFppfOver.associatedTopology B S hS p .etale)
      (BigFppfOver.associatedTopology B S hS q .etale) f
      (FibredSite.structureSheaf B S hS q hq .etale))) ?_
  exact Category.id_comp _

/-- **The identification `f⁻¹𝒪_𝒴 ⟶ 𝒪_𝒳` of Stacks 06TW on sections.** Over an object `Z` of `𝒳`
it is pullback of regular functions along the identification of the object of the big fppf site
underlying `f(Z)` with the one underlying `Z`, which is the verticality
`CategoryTheory.Functor.IsFibredOneMorphism.comp_eq` of the 1-morphism.

This is the third of the three structure-sheaf identifications that
`AlgebraicGeometry.Space.restrictedDirectImageComparison_structureSheafCompatible_chart`
needs. -/
theorem forgetRing_map_fSharpInverseImage_app (Z : 𝒳)
    (s : ((FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).forgetRing.obj
      (FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).O).obj.obj (op (f.obj Z))) :
    ((FibredSite.associatedRingedTopos B S hS p hp SiteKind.etale).forgetRing.map
        (FibredSite.ringedToposMorphism B S hS p q hp hq f hf
          SiteKind.etale).fSharpInverseImage).hom.app (op Z) s =
      (BigFppfOver.structureSheaf B S hS).obj.map
        (eqToHom (Functor.congr_obj hf.comp_eq Z).symm).op s := by
  refine Eq.trans (congrArg (fun m ↦ m.hom.app (op Z) s)
    (forgetRing_map_fSharpInverseImage_eq B S hS p q hp hq f hf)) ?_
  refine Eq.trans (sheafCompose_forget_eqToHom_app_cast
    (FibredSite.inverseImageStructureSheaf_eq B S hS p q hp hq f hf .etale) (op Z) s) ?_
  exact (structureSheaf_map_eqToHom_cast B S hS
    (Functor.congr_obj hf.comp_eq Z).symm s).symm

/-! ### The structure-sheaf compatibility of the comparison map, discharged -/

omit [∀ P : 𝒳ᵒᵖ ⥤ Type u, f.op.HasPointwiseRightKanExtension P] in
/-- **The morphism `f(u_F W) ⟶ u_G V` of `𝒴` attached to a chart diagram lies over the diagram's
vertical morphism of schemes**, provided the components of the compatibility `ha` are vertical.

This is the chart-level half of `AlgebraicGeometry.Space.isHomLift_comparisonMorphism`, with no
2-morphism `φ` and no third fibred category: `comparisonChartHom` is `ha` at the chart followed
by the image under `schemeChartFunctor` of a morphism of scheme charts of `G` whose underlying
morphism of schemes is `d.g`; the first factor lies over an identity by hypothesis and the second
over `d.g`. The hypothesis is the `hab` of `isHomLift_comparisonMorphism`, and at the induced
morphism of algebraic spaces it is the theorem
`AlgebraicGeometry.Space.isHomLift_schemeChartPostcompIso_hom_app`. -/
theorem isHomLift_comparisonChartHom
    (hab : ∀ Z : CostructuredArrow yoneda F,
      q.IsHomLift (𝟙 (q.obj (f.obj ((schemeChartFunctor B S hS F p eF).obj Z))))
        (ha.hom.app Z))
    (d : ChartDiagram B S hS F G fSpace.hom) :
    q.IsHomLift d.g (comparisonChartHom B S hS p q eF eG f fSpace ha d) := by
  have : (CostructuredArrow.proj yoneda G).IsHomLift d.g
      (chartDiagramChartHom B S hS fSpace d) :=
    IsHomLift.map (CostructuredArrow.proj yoneda G) (chartDiagramChartHom B S hS fSpace d)
  have : q.IsHomLift d.g ((schemeChartFunctor B S hS G q eG).map
      (chartDiagramChartHom B S hS fSpace d)) :=
    Functor.isHomLift_map_of_comp_eq (schemeChartFunctor_comp B S hS G q eG) d.g _
  have := hab d.U.1
  exact IsHomLift.comp_lift_id_left' q
    (q.obj (f.obj ((schemeChartFunctor B S hS F p eF).obj d.U.1)))
    (ha.hom.app d.U.1) d.g
    ((schemeChartFunctor B S hS G q eG).map (chartDiagramChartHom B S hS fSpace d))

omit [∀ P : 𝒳ᵒᵖ ⥤ Type u, f.op.HasPointwiseRightKanExtension P] in
/-- **The factorization of `comparisonChartHom` over the vertical morphism of its chart
diagram.** Read in the big fppf site and framed by the two transports of
`AlgebraicGeometry.Space.restrictionFunctor_comp` and of the verticality of the 1-morphism, the
image of `AlgebraicGeometry.Space.comparisonChartHom` is the diagram's vertical morphism of
schemes. This is `CategoryTheory.Functor.IsHomLift.fac'` applied to
`AlgebraicGeometry.Space.isHomLift_comparisonChartHom`, and it is the morphism-level identity
that the chartwise structure-sheaf statement reduces to. -/
theorem comparisonChartHom_fac
    (hab : ∀ Z : CostructuredArrow yoneda F,
      q.IsHomLift (𝟙 (q.obj (f.obj ((schemeChartFunctor B S hS F p eF).obj Z))))
        (ha.hom.app Z))
    (d : ChartDiagram B S hS F G fSpace.hom) :
    eqToHom (Functor.congr_obj hf.comp_eq ((restrictionFunctor B S hS F p eF).obj d.U)).symm ≫
        q.map (comparisonChartHom B S hS p q eF eG f fSpace ha d) ≫
          eqToHom (Functor.congr_obj (restrictionFunctor_comp B S hS G q eG) d.V) =
      eqToHom (Functor.congr_obj (restrictionFunctor_comp B S hS F p eF) d.U) ≫ d.g := by
  have := isHomLift_comparisonChartHom B S hS F G p q hF hG eF eG f fSpace ha hab d
  rw [IsHomLift.fac' q d.g (comparisonChartHom B S hS p q eF eG f fSpace ha d)]
  simp

/-- The restriction maps of the structure sheaf of the inherited étale site of `𝒴` are pullback
of regular functions along the image of the morphism in the big fppf site. -/
private theorem fibredStructure_map {Z Z' : 𝒴} (m : Z ⟶ Z')
    (x : ((FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).forgetRing.obj
      (FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).O).obj.obj (op Z')) :
    ((FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).forgetRing.obj
        (FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).O).obj.map m.op x =
      (BigFppfOver.structureSheaf B S hS).obj.map (q.map m).op x :=
  rfl

/-- Pullback of regular functions along a morphism of the big fppf site is a restriction map of
the structure sheaf of that site. -/
private theorem gamma_map_eq {X Y : BigFppfOver B S hS} (m : X ⟶ Y)
    (x : (BigFppfOver.structureSheaf B S hS).obj.obj (op Y)) :
    Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map m)) x =
      (BigFppfOver.structureSheaf B S hS).obj.map m.op x :=
  rfl

section Chartwise

attribute [local irreducible] restrictionFunctor comparisonChartHom schemeChartFunctor

omit [∀ P : 𝒳ᵒᵖ ⥤ Type u, f.op.HasPointwiseRightKanExtension P] in
/-- The chartwise structure-sheaf statement with all three identifications already rewritten as
restrictions of regular functions: there it is `AlgebraicGeometry.Space.comparisonChartHom_fac`
read through the structure sheaf of the big fppf site. -/
private theorem structureSheafCompatible_chart_middle
    (hab : ∀ Z : CostructuredArrow yoneda F,
      q.IsHomLift (𝟙 (q.obj (f.obj ((schemeChartFunctor B S hS F p eF).obj Z))))
        (ha.hom.app Z))
    (d : ChartDiagram B S hS F G fSpace.hom)
    (s : (BigFppfOver.structureSheaf B S hS).obj.obj
      (op ((SmallEtale.toOver B S hS G).obj d.V))) :
    (BigFppfOver.structureSheaf B S hS).obj.map
        (eqToHom (Functor.congr_obj hf.comp_eq
          ((restrictionFunctor B S hS F p eF).obj d.U)).symm).op
        ((BigFppfOver.structureSheaf B S hS).obj.map
          (q.map (comparisonChartHom B S hS p q eF eG f fSpace ha d)).op
          ((BigFppfOver.structureSheaf B S hS).obj.map
            (eqToHom (Functor.congr_obj (restrictionFunctor_comp B S hS G q eG) d.V)).op s)) =
      (BigFppfOver.structureSheaf B S hS).obj.map
        (eqToHom (Functor.congr_obj (restrictionFunctor_comp B S hS F p eF) d.U)).op
        ((BigFppfOver.structureSheaf B S hS).obj.map d.g.op s) := by
  have key := comparisonChartHom_fac B S hS F G p q hF hG eF eG f hf fSpace ha hab d
  exact ring_map_op_comp_congr (BigFppfOver.structureSheaf B S hS).obj _ _ _ _ _ key s

/-- The left-hand side of the chartwise structure-sheaf statement, with the identification of
`π_G` and that of Stacks 06TW rewritten as restrictions of regular functions. -/
private theorem structureSheafCompatible_chart_left (d : ChartDiagram B S hS F G fSpace.hom)
    (s : ((smallEtaleRingedTopos B S hS (⟨G, hG⟩ : AlgebraicSpaces B S hS)).forgetRing.obj
      (smallEtaleRingedTopos B S hS (⟨G, hG⟩ : AlgebraicSpaces B S hS)).O).obj.obj (op d.V)) :
    ((FibredSite.associatedRingedTopos B S hS p hp SiteKind.etale).forgetRing.map
        (FibredSite.ringedToposMorphism B S hS p q hp hq f hf
          SiteKind.etale).fSharpInverseImage).hom.app
        (op ((restrictionFunctor B S hS F p eF).obj d.U))
        (((FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).forgetRing.obj
            (FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).O).obj.map
          (comparisonChartHom B S hS p q eF eG f fSpace ha d).op
          ((RingedToposHom.forgetFSharp
            (projectionRingedToposHom B S hS G q hq hG eG)).hom.app (op d.V) s)) =
      (BigFppfOver.structureSheaf B S hS).obj.map
          (eqToHom (Functor.congr_obj hf.comp_eq
            ((restrictionFunctor B S hS F p eF).obj d.U)).symm).op
        ((BigFppfOver.structureSheaf B S hS).obj.map
          (q.map (comparisonChartHom B S hS p q eF eG f fSpace ha d)).op
          ((BigFppfOver.structureSheaf B S hS).obj.map
            (eqToHom (Functor.congr_obj (restrictionFunctor_comp B S hS G q eG) d.V)).op s)) :=
  Eq.trans
    (forgetRing_map_fSharpInverseImage_app B S hS p q hp hq f hf
      ((restrictionFunctor B S hS F p eF).obj d.U)
      (((FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).forgetRing.obj
          (FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).O).obj.map
        (comparisonChartHom B S hS p q eF eG f fSpace ha d).op
        ((RingedToposHom.forgetFSharp
          (projectionRingedToposHom B S hS G q hq hG eG)).hom.app (op d.V) s)))
    (congrArg (fun y ↦ (BigFppfOver.structureSheaf B S hS).obj.map
        (eqToHom (Functor.congr_obj hf.comp_eq
          ((restrictionFunctor B S hS F p eF).obj d.U)).symm).op y)
      (Eq.trans
        (fibredStructure_map B S hS q hq (comparisonChartHom B S hS p q eF eG f fSpace ha d)
          ((RingedToposHom.forgetFSharp
            (projectionRingedToposHom B S hS G q hq hG eG)).hom.app (op d.V) s))
        (congrArg (fun y ↦ (BigFppfOver.structureSheaf B S hS).obj.map
            (q.map (comparisonChartHom B S hS p q eF eG f fSpace ha d)).op y)
          (forgetFSharp_projectionRingedToposHom_app B S hS G q hq hG eG d.V s))))

/-- The right-hand side of the chartwise structure-sheaf statement, with the identification of
`π_F` rewritten as a restriction of regular functions. -/
private theorem structureSheafCompatible_chart_right (d : ChartDiagram B S hS F G fSpace.hom)
    (s : ((smallEtaleRingedTopos B S hS (⟨G, hG⟩ : AlgebraicSpaces B S hS)).forgetRing.obj
      (smallEtaleRingedTopos B S hS (⟨G, hG⟩ : AlgebraicSpaces B S hS)).O).obj.obj (op d.V)) :
    (RingedToposHom.forgetFSharp
          (projectionRingedToposHom B S hS F p hp hF eF)).hom.app (op d.U)
        (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map d.g)) s) =
      (BigFppfOver.structureSheaf B S hS).obj.map
        (eqToHom (Functor.congr_obj (restrictionFunctor_comp B S hS F p eF) d.U)).op
        ((BigFppfOver.structureSheaf B S hS).obj.map d.g.op s) :=
  Eq.trans
    (forgetFSharp_projectionRingedToposHom_app B S hS F p hp hF eF d.U
      (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map d.g)) s))
    (congrArg (fun y ↦ (BigFppfOver.structureSheaf B S hS).obj.map
        (eqToHom (Functor.congr_obj (restrictionFunctor_comp B S hS F p eF) d.U)).op y)
      (gamma_map_eq B S hS d.g s))

/-- **The chartwise structure-sheaf identity of the comparison map of equation 075M.** Over a
commutative diagram `d` of étale scheme charts, the three canonical structure-sheaf
identifications of the square of Stacks 073N — that of `π_G`, the identification
`f⁻¹𝒪_𝒴 ⟶ 𝒪_𝒳` of Stacks 06TW, and that of `π_F` — carry restriction of regular functions along
`AlgebraicGeometry.Space.comparisonChartHom` to restriction along the diagram's vertical morphism
of schemes `d.g`.

This is the right-hand side of
`AlgebraicGeometry.Space.restrictedDirectImageComparison_structureSheafCompatible_iff`, so with
it the hypothesis `hsq` of `AlgebraicGeometry.Space.restrictionRingedSquareOfIsIso` is
discharged. The verticality hypothesis `hab` is genuinely needed and is not a weakening: without
it the statement is false, because `comparisonChartHom` begins with `ha.hom.app d.U.1`, whose
image under `q` is an automorphism of the chart's base scheme that `ha` alone does not pin down.
At the induced morphism of algebraic spaces `hab` is the theorem
`AlgebraicGeometry.Space.isHomLift_schemeChartPostcompIso_hom_app`, which is what
`AlgebraicGeometry.Space.restrictionRingedSquareInduced` uses.

All three identifications become pullback of regular functions along a morphism of the big fppf
site (`AlgebraicGeometry.Space.forgetFSharp_projectionRingedToposHom_app` for the first and the
third, `AlgebraicGeometry.Space.forgetRing_map_fSharpInverseImage_app` for the second), after
which the statement is the morphism-level identity
`AlgebraicGeometry.Space.comparisonChartHom_fac`. -/
theorem restrictedDirectImageComparison_structureSheafCompatible_chart
    (hab : ∀ Z : CostructuredArrow yoneda F,
      q.IsHomLift (𝟙 (q.obj (f.obj ((schemeChartFunctor B S hS F p eF).obj Z))))
        (ha.hom.app Z))
    (d : ChartDiagram B S hS F G fSpace.hom)
    (s : ((smallEtaleRingedTopos B S hS (⟨G, hG⟩ : AlgebraicSpaces B S hS)).forgetRing.obj
      (smallEtaleRingedTopos B S hS (⟨G, hG⟩ : AlgebraicSpaces B S hS)).O).obj.obj (op d.V)) :
    ((FibredSite.associatedRingedTopos B S hS p hp SiteKind.etale).forgetRing.map
        (FibredSite.ringedToposMorphism B S hS p q hp hq f hf
          SiteKind.etale).fSharpInverseImage).hom.app
        (op ((restrictionFunctor B S hS F p eF).obj d.U))
        (((FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).forgetRing.obj
            (FibredSite.associatedRingedTopos B S hS q hq SiteKind.etale).O).obj.map
          (comparisonChartHom B S hS p q eF eG f fSpace ha d).op
          ((RingedToposHom.forgetFSharp
            (projectionRingedToposHom B S hS G q hq hG eG)).hom.app (op d.V) s)) =
      (RingedToposHom.forgetFSharp
          (projectionRingedToposHom B S hS F p hp hF eF)).hom.app (op d.U)
        (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map d.g)) s) :=
  (structureSheafCompatible_chart_left B S hS F G p q hp hq hF hG eF eG f hf fSpace ha d s).trans
    ((structureSheafCompatible_chart_middle B S hS F G p q hF hG eF eG f hf fSpace ha hab d
        s).trans
      (structureSheafCompatible_chart_right B S hS F G p hp hF hG eF fSpace d s).symm)

/-- **The structure-sheaf compatibility `hsq` of the comparison map of equation 075M.** The
hypothesis `hsq` of `AlgebraicGeometry.Space.restrictionRingedSquareOfIsIso` holds whenever the
components of the compatibility `ha` are vertical.

It is `AlgebraicGeometry.Space.restrictedDirectImageComparison_structureSheafCompatible_iff` fed
with `AlgebraicGeometry.Space.restrictedDirectImageComparison_structureSheafCompatible_chart`. -/
theorem restrictedDirectImageComparison_structureSheafCompatible
    (hab : ∀ Z : CostructuredArrow yoneda F,
      q.IsHomLift (𝟙 (q.obj (f.obj ((schemeChartFunctor B S hS F p eF).obj Z))))
        (ha.hom.app Z)) :
    RingedToposHom.forgetFSharp (projectionRingedToposHom B S hS G q hq hG eG) ≫
        (projectionRingedToposHom B S hS G q hq hG eG).toToposHom.pushforward.map
          (RingedToposHom.forgetFSharp
            (FibredSite.ringedToposMorphism B S hS p q hp hq f hf .etale)) ≫
        (restrictedDirectImageComparison B S hS F G p q hp hq hF hG eF eG f hf fSpace ha).app
          ((FibredSite.associatedRingedTopos B S hS p hp .etale).forgetRing.obj
            (FibredSite.associatedRingedTopos B S hS p hp .etale).O) =
      RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B S hS fSpace) ≫
        (smallEtaleRingedToposHom B S hS fSpace).toToposHom.pushforward.map
          (RingedToposHom.forgetFSharp (projectionRingedToposHom B S hS F p hp hF eF)) :=
  (restrictedDirectImageComparison_structureSheafCompatible_iff B S hS F G p q hp hq hF hG
    eF eG f hf fSpace ha).mpr
      (restrictedDirectImageComparison_structureSheafCompatible_chart B S hS F G p q hp hq hF hG
        eF eG f hf fSpace ha hab)

/-- **Stacks 073N given invertibility of the comparison map alone**, for a pair `(fSpace, ha)`
whose compatibility is vertical. This is
`AlgebraicGeometry.Space.restrictionRingedSquareOfIsIso` with its second hypothesis `hsq`
discharged by `AlgebraicGeometry.Space.restrictedDirectImageComparison_structureSheafCompatible`;
nothing about the structure sheaves is left open. -/
noncomputable def restrictionRingedSquareOfIsIsoOfIsHomLift
    (hab : ∀ Z : CostructuredArrow yoneda F,
      q.IsHomLift (𝟙 (q.obj (f.obj ((schemeChartFunctor B S hS F p eF).obj Z))))
        (ha.hom.app Z))
    (hiso : IsIso
      (restrictedDirectImageComparison B S hS F G p q hp hq hF hG eF eG f hf fSpace ha)) :
    RingedToposHom.TwoIso
      (A := FibredSite.associatedRingedTopos B S hS p hp .etale)
      (B := smallEtaleRingedTopos B S hS ⟨G, hG⟩)
      (restrictionSquareFibredLeg B S hS G p q hp hq hG eG f hf)
      (restrictionSquareSpaceLeg B S hS F G p hp hF hG eF fSpace) :=
  restrictionRingedSquareOfIsIso B S hS F G p q hp hq hF hG eF eG f hf fSpace ha hiso
    (restrictedDirectImageComparison_structureSheafCompatible B S hS F G p q hp hq hF hG eF eG
      f hf fSpace ha hab)

/-- **Stacks 073N at the induced morphism of algebraic spaces, given invertibility of the
comparison map alone.** For the morphism of algebraic spaces that the 1-morphism itself induces,
with `ha` the canonical compatibility
`AlgebraicGeometry.Space.schemeChartPostcompIso`, both hypotheses of
`AlgebraicGeometry.Space.restrictionRingedSquare` beyond invertibility are theorems: `hsq` by
`AlgebraicGeometry.Space.restrictedDirectImageComparison_structureSheafCompatible`, whose
verticality input is `AlgebraicGeometry.Space.isHomLift_schemeChartPostcompIso_hom_app`.

This is the 2-isomorphism of the two legs of the square that the hypothesis `sq` of
`AlgebraicGeometry.Space.restrictedDerivedDirectImageIso` (Stacks 075N) asks for: there the
morphism of algebraic spaces is `AlgebraicGeometry.Space.inducedAlgebraicSpacesHom`, which is
this `AlgebraicGeometry.Space.inducedSpacesHom`. So for Stacks 075N nothing is left of Stacks
073N but invertibility of the canonical comparison map of equation 075M. -/
noncomputable def restrictionRingedSquareInduced
    (hiso : IsIso (restrictedDirectImageComparison B S hS F G p q hp hq hF hG eF eG f hf
      (inducedSpacesHom B S hS (X := ⟨F, hF⟩) (Y := ⟨G, hG⟩) p q eF eG f hf.comp_eq)
      (schemeChartPostcompIso B S hS (X := ⟨F, hF⟩) (Y := ⟨G, hG⟩) p q eF eG f
        hf.comp_eq))) :
    RingedToposHom.TwoIso
      (A := FibredSite.associatedRingedTopos B S hS p hp .etale)
      (B := smallEtaleRingedTopos B S hS ⟨G, hG⟩)
      (restrictionSquareFibredLeg B S hS G p q hp hq hG eG f hf)
      (restrictionSquareSpaceLeg B S hS F G p hp hF hG eF
        (inducedSpacesHom B S hS (X := ⟨F, hF⟩) (Y := ⟨G, hG⟩) p q eF eG f hf.comp_eq)) :=
  restrictionRingedSquareOfIsIsoOfIsHomLift B S hS F G p q hp hq hF hG eF eG f hf
    (inducedSpacesHom B S hS (X := ⟨F, hF⟩) (Y := ⟨G, hG⟩) p q eF eG f hf.comp_eq)
    (schemeChartPostcompIso B S hS (X := ⟨F, hF⟩) (Y := ⟨G, hG⟩) p q eF eG f hf.comp_eq)
    (isHomLift_schemeChartPostcompIso_hom_app B S hS (X := ⟨F, hF⟩) (Y := ⟨G, hG⟩) p q eF eG f
      hf.comp_eq) hiso

end Chartwise

end Comparison

end AlgebraicGeometry.Space

end
