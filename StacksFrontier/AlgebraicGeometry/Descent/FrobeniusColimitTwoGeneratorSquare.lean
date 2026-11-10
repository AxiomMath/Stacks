module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitSquare
public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorPullback
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.Twist
public import StacksFrontier.AlgebraicGeometry.Picard.FrobeniusTorsion

/-!
# The functor of Stacks Tag 0EXD for the two-generator almost blowup square

Let `p` be a prime, let `A` be a ring in which `p` vanishes and let `f₁, f₂ ∈ A`. The almost
blowup square of Stacks Example 0EVH,

```
Proj ((A/(f₁,f₂))[T₀,T₁]) ⟶ Proj (A[T₀,T₁]/(f₂T₀ - f₁T₁))
          ↓                             ↓
   Spec (A/(f₁,f₂))        ⟶          Spec A
```

is a square of schemes in characteristic `p`, and it is commutative — indeed cartesian, by
`Stacks.AlmostBlowUp.twoGenerator_isPullback`. This file instantiates at it the comparison
functor of
`StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitSquare`, so that the functor whose being
an equivalence Stacks Tag 0EXD asserts exists as a declaration.

## Main definitions

* `AlgebraicGeometry.twoGeneratorFrobeniusColimitComparison`: **the functor
  `𝒮_X ⟶ 𝒮_Z ×_{𝒮_E} 𝒮_{X'}` of Stacks Tag 0EXD** for the square of Example 0EVH, with the
  canonical transition functors of Stacks Tag 0EXE as its four legs.

## Main results

* `AlgebraicGeometry.isInCharacteristic_twoGeneratorCenter`,
  `AlgebraicGeometry.isInCharacteristic_twoGeneratorModification` and
  `AlgebraicGeometry.isInCharacteristic_twoGeneratorExceptional`: **the three other corners of
  the square are in characteristic `p`** as soon as the base is, since each of them maps to the
  base.

## Implementation notes

**No `@[stacks 0EXD]` attribute appears in this file, because nothing here proves the tag.**
What Tag 0EXD asserts is that
`AlgebraicGeometry.twoGeneratorFrobeniusColimitComparison` is an equivalence. Its full
faithfulness rests on the cartesianness of
`colim_F Γ(X, 𝒪) → colim_F Γ(Z, 𝒪) ×_{colim_F Γ(E, 𝒪)} colim_F Γ(X', 𝒪)`, combined with
internal Hom and Zariski glueing. That cartesianness is available unconditionally as
`AlgebraicGeometry.isPullback_frobeniusColimit_twoGeneratorModel`, in the module
`StacksFrontier.AlgebraicGeometry.Topologies.WeakNormalization.FrobeniusColimitGlobalSections`,
proved site-free from the two assertions of Tag 0EVJ and the section of the exceptional
projective line. The source cites Tag 0EVK for it, and that route is *not* available here:
`AlgebraicGeometry.BigHOver.existsUnique_iso_frobeniusColimitSections` — and likewise Tag 0EVD,
`AlgebraicGeometry.isPullback_of_almostBlowUpSquare_bigH`, which is what would turn an h sheaf
into a cartesian square — is quantified over an arbitrary `AlgebraicGeometry.BigHSite`, of which
this development constructs no term, so neither can be instantiated at the concrete square of
Example 0EVH.

The passage from `colim_F Γ` to `Γ(colim_F 𝒪, -)`, the object out of which the Hom sets of
`AlgebraicGeometry.frobeniusColimitVectorBundles` are built, is available:

* `AlgebraicGeometry.frobeniusColimitSectionsComparison`
  (`StacksFrontier/AlgebraicGeometry/Descent/FrobeniusColimitSectionsComparison.lean`) is the
  comparison `colim_F Γ(X, 𝒪) ⟶ Γ(colim_F 𝒪_X, X)`, with
  `AlgebraicGeometry.frobeniusColimitSectionsComparison_naturality` for its naturality in `X`
  and `AlgebraicGeometry.bijective_frobeniusColimitSectionsComparison` for its bijectivity on a
  quasi-compact quasi-separated scheme;
* over an arbitrary quasi-compact open the comparison is the sheafification map
  `AlgebraicGeometry.toFrobeniusColimitRingSheaf` itself, and
  `AlgebraicGeometry.bijective_toFrobeniusColimitRingSheaf_app` says it is bijective there —
  `(colim_F 𝒪_X)(U) = colim_j 𝒪_X(U)` for `U` quasi-compact in a quasi-separated scheme;
* and `AlgebraicGeometry.isPullback_frobeniusColimitSections_twoGenerator`
  (`StacksFrontier/AlgebraicGeometry/Descent/FrobeniusColimitSectionsSquare.lean`) transports the
  cartesian square above along that comparison at each of the four corners, giving
  `Γ(colim_F 𝒪_X, X) = Γ(colim_F 𝒪_Z, Z) ×_{Γ(colim_F 𝒪_E, E)} Γ(colim_F 𝒪_{X'}, X')`.

That is the form in which full faithfulness consumes Stacks 0EVK: for *free* modules the Hom
sets are matrices over those rings, and that reduction is
`AlgebraicGeometry.frobeniusColimitFreeHomMatrixEquiv_pullbackFreeHom`, so the square is exactly
the bijectivity full faithfulness asks for there —
`AlgebraicGeometry.isPullback_frobeniusColimitFreeHom_twoGenerator`
(`StacksFrontier/AlgebraicGeometry/Descent/FrobeniusColimitFreeHomSquare.lean`), under exactly the
hypotheses of Example 0EVH. What a cartesian square of Hom-sets gives is full faithfulness of the
comparison functor itself, by
`CategoryTheory.Limits.CategoricalPullback.fullyFaithful_squareComparison_iff_isPullback`
(`StacksFrontier/CategoryTheory/TwoFibreProduct/CategoricalPullbackHomSquare.lean`), which carries
no groupoid hypothesis. Transporting the square to the canonical cospan `g ↦ e^*g ≫ α`,
`k ↦ α ≫ d^*k` asks for the compatibility of
`AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso` at a free module with the free
identifications, and that is
`AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso_hom_app_hom_free`
(`StacksFrontier/AlgebraicGeometry/Descent/FrobeniusColimitFreeComp.lean`). With it, the cartesian
square of Hom-sets at a pair of free modules is
`AlgebraicGeometry.isPullback_squareComparison_homSquare_free_twoGenerator`
(`StacksFrontier/AlgebraicGeometry/Descent/FrobeniusColimitFreeHomFullyFaithful.lean`), under
exactly
the hypotheses of Example 0EVH: that is the full faithfulness of the comparison functor **at free
modules**.

What the square does not give at all is the general finite locally free case, which asks for the
same square over each member of a trivialising affine cover of `Spec A` — that is, the square of
Example 0EVH over a localisation `A_g`, identified with the restriction of the square over `A` to
`D(g)`. Two of the three inputs to that identification are available. The corners over `A_g` are
the base changes of the corners over `A` by
`Stacks.AlmostBlowUp.isPullback_centerToBase_coeff`,
`…isPullback_modificationToBase_coeff` and `…isPullback_exceptionalToBase_coeff`
(`StacksFrontier/AlgebraicGeometry/Blowup/TwoGeneratorCoefficientBaseChange.lean`), which are stated
for an arbitrary `R`-algebra `A` with the two generators in `R` and carry no finiteness,
flatness or Noetherian hypothesis, so they apply at `R := A`, `A := Localization.Away g`; and
`Spec (Localization.Away g) ⟶ Spec A` is an open immersion with range `D(g)` by Mathlib's
`AlgebraicGeometry.Scheme.isOpenImmersion_SpecMap_localizationAway` and
`AlgebraicGeometry.Scheme.Hom.opensRange_localizationAway`. The passage from the sections of
`colim_F 𝒪` over an open to the global sections of `colim_F 𝒪` of the open subscheme is
`AlgebraicGeometry.frobeniusColimitRingSheafOpenIso` and its sections forms
(`StacksFrontier/AlgebraicGeometry/Descent/FrobeniusColimitOpenSubscheme.lean`): note that
`AlgebraicGeometry.frobeniusColimitRingSheafOverIso` alone is *not* enough, since it lands on the
slice site `Opens(X)/U` rather than on the site of the open subscheme, and the crossing between
the two is Mathlib's `TopologicalSpace.Opens.sheafEquivOver`. The third input is available in
generic form: `AlgebraicGeometry.isoPreimageOpensRange_of_isPullback`
(`StacksFrontier/AlgebraicGeometry/Descent/PreimageOpenOfIsPullback.lean`) reads the apex of a
cartesian square one of whose legs is an open immersion as the preimage open subscheme,
compatibly with the morphisms to the base, so each of the three base-change squares above
identifies the corner over `A_g` with the preimage of `D(g)` in the corner over `A` with no
further geometry. That instantiation is now available, at all three corners and with the
compatibility with the morphism to the corner over `A`:
`Stacks.AlmostBlowUp.centerAwayIsoPreimage`, `…exceptionalAwayIsoPreimage` and
`…modificationAwayIsoPreimage`, with `…_hom_ι` for each
(`StacksFrontier/AlgebraicGeometry/Blowup/TwoGeneratorCoefficientBaseChange.lean`). At the
modification corner no extra matching against the grading isomorphisms was needed: they are
already absorbed into `Stacks.AlmostBlowUp.modificationCoeffProjMap`, which is the second leg of
`…isPullback_modificationToBase_coeff`, so the preimage identification is the generic lemma
applied to that square and nothing else. **The generators live upstream**, so the square over
`A_g` is the two-generator square at the *images* `algebraMap A (Localization.Away g) f₁` and
`…f₂`; a statement phrased with independently chosen elements of `A_g` must supply those
equalities.

The cube coherence is now available, and at both levels: on all sheaves of modules as
`AlgebraicGeometry.frobeniusColimitPullbackSquareIso_cube_app` and on the finite locally free
modules — the level the comparison functor of this tag is built at — as
`AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso_cube_app`
(`StacksFrontier/AlgebraicGeometry/Descent/FrobeniusColimitVectorBundlesCube.lean`). **Its four side
faces at the square of Example 0EVH over a localisation `A_g` are all available too**, so the cube
can be instantiated there with no transport across opens at all: the fourth corner is taken to be
the exceptional line `Proj (exceptionalGrading A_g …)` over `A_g` itself rather than an open
subscheme of the exceptional line over `A`, and the four side commutativities are
`(Stacks.AlmostBlowUp.isPullback_modificationToBase_coeff A (Localization.Away g) f₁ f₂).w`,
`(…isPullback_centerToBase_coeff …).w`,
`Stacks.AlmostBlowUp.exceptionalToModification_comp_modificationCoeffProjMap A
(Localization.Away g) f₁ f₂`
and `(…isPullback_exceptionalToCenter_coeff …).w`. The corner identifications with preimages of
`D(g)` are therefore *not* needed for the cube; they are needed only where the open-immersion
property itself is used.

**The cover by basic opens is available, and so is the local trivialisation over `A_g`
itself.** `AlgebraicGeometry.exists_cover_free_localizationAway_frobeniusColimit`
(`StacksFrontier/AlgebraicGeometry/Descent/FrobeniusColimitBasicOpenCover.lean`) produces, for a
*pair* of finite locally free `colim_F 𝒪_{Spec A}`-modules, a family `g : σ → A` whose basic
opens cover `Spec A` and over each of which both modules are carried to free modules by the
transition functor of `Spec (A_g) ⟶ Spec A` — the corner of the square over `A_g`, not the open
subscheme `D(g)`, which is the spelling the two-generator square over `A_g` consumes. The
refinement from the cover that finite local freeness supplies to a cover by members of a
*prescribed* basis is `Stacks.SheafOfModules.exists_cover_commonFree_of_isBasis`, and the
crossing between `D(g)` and `Spec (A_g)` is
`AlgebraicGeometry.frobeniusColimitPullbackObjFreeOfOpenImmersion`: it needs no equivalence,
because the transition functor carries a free module to a free one for *any* morphism, by
Mathlib's `CategoryTheory.SheafOfModules.pullbackObjFreeIso`. Where an equivalence *is* needed —
to reflect an equation of morphisms across the isomorphism `D(g) ≅ Spec (A_g)` — it is
`AlgebraicGeometry.frobeniusColimitPullbackEquivOfIso`, which was absent from the tree and is
built from the pseudofunctoriality that was present.

**Separatedness is available in the transition-functor spelling**, which is the spelling the
square comparison and the free case of full faithfulness speak:
`AlgebraicGeometry.frobeniusColimitPullback_map_injective` for a cover by opens and
`…_map_injective_of_openImmersion` for a family of open immersions whose images cover, the form
the cover by the spectra of the localisations presents. So the *faithfulness* half of the
trivialising-cover argument has all of its inputs: the local joint injectivity over `A_g`, the
localisation of the two global hypotheses by the naturality of
`AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso` at the two side faces
`(Stacks.AlmostBlowUp.isPullback_centerToBase_coeff …).w` and
`(…isPullback_modificationToBase_coeff …).w`, and this separatedness. **It is not assembled.**

What the *existence* half still owes is the compatibility hypothesis of
`Stacks.SheafOfModules.existsUnique_hom_of_over`, which is stated on components over *every*
open below two members of the cover, not merely over their intersection. Two local solutions
agree over a basic open below both members — by the local joint injectivity there, since freeness
descends — so what is missing is the passage from agreement on a basic-open cover of an arbitrary
open `W` to agreement of the components at `W`, i.e. one application of the sheaf condition on
the target. The cube coherence
`AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso_cube_app` is what converts the global
compatibility of a pair `(g, k)` into the compatibility the local square asks for; it is not yet
instantiated. Note what the cube coherence is *not*:
it is not an abstract local-to-global statement about cartesian Hom-squares, since
`CategoryTheory.Limits.CategoricalPullback.fullyFaithful_squareComparison_iff_isPullback`
together with `CategoryTheory.Limits.Types.isPullback_iff` already reduce full faithfulness to
commutativity, injectivity and existence for a square of types; all the remaining content is
geometric. The square comparison is a composite of the two composition isomorphisms
`AlgebraicGeometry.frobeniusColimitVectorBundlesPullbackComp` with an `eqToIso` from the
square's commutativity, so the cube is a pasting statement about those, for which
`AlgebraicGeometry.frobeniusColimitPullbackCompOfEq_assoc` and `…_assoc_rfl` are the tools.

**The transition functor of an open immersion is restriction to the open subscheme.** This was
asserted by a docstring long before it was proved; it is now
`AlgebraicGeometry.frobeniusColimitSiteRestrictIsoPullback`
(`StacksFrontier/AlgebraicGeometry/Descent/FrobeniusColimitOpenPullback.lean`), which identifies
extension of scalars along `AlgebraicGeometry.frobeniusColimitStructureSheafHom` at `V.ι` with
pushforward along the open-image functor of `V.ι`, by uniqueness of left adjoints: the open-image
functor is left adjoint to the preimage functor, so Mathlib's
`CategoryTheory.SheafOfModules.pushforwardPushforwardAdj` makes the two pushforwards adjoint and
both functors are left adjoint to pushforward along `V.ι`. The one piece of content is
`AlgebraicGeometry.frobeniusColimitι_comp_frobeniusColimitRingSheafRestrictIso_hom`, the
compatibility of the identification `(colim_F 𝒪_X)|_V ≅ colim_F 𝒪_V` with the stage
coprojections. **Nothing is owed there any more.** The last step of bookkeeping — identifying that
pushforward with `AlgebraicGeometry.frobeniusColimitModuleRestrict`, which is the same functor
written as slice restriction followed by `AlgebraicGeometry.frobeniusColimitModuleOpenEquiv` — is
`AlgebraicGeometry.frobeniusColimitModuleRestrictIsoSiteRestrict`, and its composite with the
identification above is `AlgebraicGeometry.frobeniusColimitModuleRestrictIsoPullback`
(`StacksFrontier/AlgebraicGeometry/Descent/FrobeniusColimitRestrictPullback.lean`). The
separatedness half of the trivialising-cover argument consumes it.

**What the existence half needs, and the separatedness half does not, is a slice-to-slice
comparison.** The two halves are asymmetric, and the asymmetry is not in the gluing theorem.
Separatedness compares two morphisms one cover member at a time, so it needs the crossing
`AlgebraicGeometry.frobeniusColimitModuleRestrictIsoPullback` at a single open and overlaps never
appear — which is why `AlgebraicGeometry.frobeniusColimitPullback_map_injective` is six lines.
Gluing compares *local solutions over two different members, on their overlap*, so it needs the
crossing to be compatible with passing to a smaller open. Writing `T_V` for the bijection between
morphisms in the transition-functor spelling along `V.ι` and morphisms `M.over V ⟶ N.over V`, what
is missing is that for `W ≤ V` the slice restriction of `T_V F` is `T_W` of the transition of `F`
along `X.homOfLE`; equivalently, a natural isomorphism
`SheafOfModules.overMap (colim_F 𝒪_X) (homOfLE h) ⋙`
`(frobeniusColimitModuleOpenEquiv … W …).functor`
`≅ (frobeniusColimitModuleOpenEquiv … V …).functor ⋙ SheafOfModules.pullback`
`(frobeniusColimitStructureSheafHom p (X.homOfLE h) …)`. Whiskering such a comparison with
`CategoryTheory.SheafOfModules.overFunctor` is *not* enough: it has to be natural at the local
solution itself, which is exactly the morphism that does not come from the base, so the whiskered
form carries none of the needed content. Both composites are left adjoints
(`CategoryTheory.SheafOfModules.overMapPushforwardAdj` for the slice factor, the pullback
adjunction for the other), so `CategoryTheory.Adjunction.leftAdjointUniq` is the available route,
as it was for `AlgebraicGeometry.frobeniusColimitSiteRestrictIsoPullback`. Expect the spelling
clash of rung 13: the nearest statement in either tree, Mathlib's
`AlgebraicGeometry.Scheme.Modules.overMapCompOverEquiv`, is this very comparison for the
*structure* sheaf and is proved under a transparency-relaxing compiler option, as
is `TopologicalSpace.Opens.sheafOfModulesEquivOver` itself.

Everything else the existence half needs is proved. The gluing is
`Stacks.SheafOfModules.existsUnique_hom_of_overMap_eq_of_isBasis`
(`StacksFrontier/Topology/Sheaves/Glueing/OModuleMapGluingSlice.lean`), whose compatibility
hypothesis is an equality of slice restrictions over the members of a *prescribed basis* — the
basic opens, the only opens over which the almost blowup square of [Stacks, Example 0EVH] is again
a two-generator square, namely the one over `A_h`; the passage from agreement over the basis opens
inside an open to agreement at that open is one application of the sheaf condition on the target,
`TopCat.Sheaf.LocalModuleHom.app_eq_of_isBasis` in the same file. Local joint injectivity over
`A_h` is `AlgebraicGeometry.jointly_injective_frobeniusColimitVectorBundles_twoGenerator`
instantiated at the ring `A_h`, which is legitimate because that theorem holds at *every* ring and
*every* pair of modules. The criterion to feed the result to is
`CategoryTheory.Limits.CategoricalPullback.full_squareComparison_of_exists`, the dual of the
`…faithful_squareComparison_of_jointly_injective` that faithfulness used, and like it it carries
no universe restriction. And the localisation of the two global data to a member of the cover is
`AlgebraicGeometry.frobeniusColimitVectorBundlesSquareLoc`
(`StacksFrontier/AlgebraicGeometry/Descent/FrobeniusColimitVectSquareLoc.lean`), whose
`…_map` says that the local datum attached to a morphism coming from the base is the one that
morphism induces locally.

The module-level half of the restriction is available: a finite locally free `colim_F 𝒪_X`-module
is free over `colim_F 𝒪_U` on each member of an open cover, by
`AlgebraicGeometry.exists_cover_free_frobeniusColimitModuleRestrict`
(`StacksFrontier/AlgebraicGeometry/Descent/FrobeniusColimitOpenSubscheme.lean`). That is what lets
`CategoryTheory.Limits.CategoricalPullback.isPullback_squareComparison_homSquare_of_iso` carry
the free case to a merely trivialised module: finite local freeness is *defined* by a
trivialisation over the slice sheaves of rings `(colim_F 𝒪_X)|_U`, and the statement above moves
it to the sheaf of rings `colim_F 𝒪_U` that the square over a localisation actually carries. No
transport of `SheafOfModules.LocalGeneratorsData` across a change of site is needed for this:
a free sheaf of modules is a coproduct of copies of the structure sheaf, so the whole transport
reduces to a transport of the structure sheaf, which is `SheafOfModules.freeIsoOfUnitIso`
together with `Stacks.Sheaves.RingedPoint.restrictScalarsObjUnitIso`.

Essential surjectivity rests on three further inputs, none of which is
assumed or proved in this file:

* **the theorem on formal functions**, Tag 02OC, available unconditionally as
  `Stacks.Cohomology.FormalFunctions.exists_formalFunctionsEquiv_unconditional`
  (`StacksFrontier/AlgebraicGeometry/FormalFunctions/ReesFiniteConsequence.lean`), which is
  `…exists_formalFunctionsEquiv_of_02O8` with its hypothesis `h02O8` discharged by
  `Stacks.FormalFunctions.isReesFinite_cohomologyIdealPowerSystem`, the quantified form of
  Tag 02O8;
* **the vanishing of `H¹(E, -)` for globally generated quasi-coherent modules on `E = P¹_Z`**,
  available unconditionally as
  `Stacks.AlmostBlowUp.isZero_cohomology_one_exceptional_of_generatingSections`
  (`StacksFrontier/AlgebraicGeometry/Blowup/TwoGeneratorExceptionalCohomology.lean`). The source
  cites Tag 0E7H only as a comparison, and that is just as well: both clauses of Tag 0E7H in this
  development carry three hypotheses — the residue of Tag 02V7 at fibre dimension one, the
  finite-type clause of Tag 0EX4 in degree one and the base-change clause of Tag 0EX3 (b) in the
  same degree — and none of the three is available unconditionally. On a projective line none of
  them is needed;
* **the Noetherian descent of a triple `(ℱ, 𝒢, φ)`** along a filtered colimit of finitely
  generated subalgebras, Tag 0B8W, available at each of the four corners of the square.
  `StacksFrontier/AlgebraicGeometry/Blowup/TwoGeneratorNoetherianApproximation.lean` presents
  `Spec A` as the cofiltered limit of the spectra of the Noetherian stages
  `ℤ[i ∪ {f₁, f₂}] ⊆ A` and descends a vector bundle on the base to a stage by Tag 0B8W (1);
  `StacksFrontier/AlgebraicGeometry/Blowup/TwoGeneratorCoefficientBaseChange.lean` identifies each
  of the three other corners `Z`, `X'` and `E` over `A` with the base change of the corresponding
  corner over the initial stage `A₀ = ℤ[f₁,f₂]`, and
  `StacksFrontier/AlgebraicGeometry/Blowup/TwoGeneratorNoetherianCorners.lean` turns those
  identifications into the three limit cones and applies Tag 0B8W (1) at each corner
  (`Stacks.AlmostBlowUp.exists_stage_isFiniteLocallyFree_pullback_iso_center`, `…_modification`
  and `…_exceptional`).

The `ℐ`-adic induction of that reduction is available too: global sections of `𝒢` surject onto
`H⁰(E, 𝒢|_E)` by
`Stacks.Cohomology.FormalFunctions.surjective_adicCohomologyProj_twoGenerator`
(`StacksFrontier/AlgebraicGeometry/FormalFunctions/AdicGradedPieceVanishing.lean`), whose four
hypotheses are discharged there.

The step identifying `α : 𝒪_{X'}^{⊕r} → 𝒢` as an isomorphism near `E` is now available, and in
two forms. In general, for a closed immersion `i : Z ⟶ X` and a morphism `α` of finite locally
free `𝒪_X`-modules on a locally Noetherian `X` whose restriction `i^*α` is an isomorphism, `α`
restricts to an isomorphism over an open neighbourhood of `Z`:
`exists_isIso_restrictFunctor_map_of_isIso_pullback_of_isLocallyNoetherian`, in the namespace
`Stacks.AlgebraicGeometry.IsoLocus`
(`StacksFrontier/AlgebraicGeometry/LocalIso/ClosedImmersionNeighbourhood.lean`). At the square of
Example 0EVH over a Noetherian ring it is
`Stacks.AlmostBlowUp.exists_isIso_restrictFunctor_map_near_exceptional`
(`StacksFrontier/AlgebraicGeometry/Blowup/TwoGeneratorNoetherianModification.lean`), whose
local Noetherianity of the modification — needed for coherence, hence for Tag 01Y3 — is
`Stacks.AlmostBlowUp.isLocallyNoetherian_proj_modificationGrading` in the same file. Note the
`[IsNoetherianRing A]`: coherence of a finite locally free module is *not* automatic for general
`A`, which is why the Noetherian reduction of Tag 0B8W has to be performed first and why the
pointwise argument cannot be carried out before it.

Two remarks about that step, each correcting a plausible but *wrong* expectation.
First, the pointwise Nakayama step does **not** have to be assembled: `lift_iso_of_quot_iso`
(`StacksFrontier/Algebra/Module/Projective/Nakayama.lean`, carrying `@[stacks 0BC6 "(1)"]`) is
exactly "a map of finite projective modules whose reduction modulo an ideal in the Jacobson
radical is bijective is bijective", and the residue-field case packaged for sheaves is
`AlgebraicGeometry.isIso_stalk_of_isIso_residuePullback`
(`StacksFrontier/AlgebraicGeometry/Flatness/Flattening/StalkIsoSpreadout.lean`), which is what the
files above actually use. Second, the route "Nakayama for surjectivity, then equal rank over
`𝒪_{X',x}` for injectivity" is **unsound** without flatness or projectivity of the target: over
`R = k[[t]]` with `I = (t)` and `M = R/(t²)`, the quotient map `R → M` has bijective reduction
modulo `I` and is not injective. Freeness of the stalks is what rules that out, and it is
supplied by `Stacks.StalkFreeBridge.freeAndFinite_stalk_of_isFiniteLocallyFree`.

**The Noetherian reduction itself is now instantiated**, over a single stage:
`Stacks.AlmostBlowUp.exists_stage_compatible_triple`
(`StacksFrontier/AlgebraicGeometry/Blowup/TwoGeneratorNoetherianCorners.lean`) descends a compatible
triple `(ℱ, 𝒢, φ)` over `A` to finite locally free modules on the centre and the modification
over one Noetherian stage together with an isomorphism of their restrictions to the exceptional
line over that stage, whose pullback to the exceptional line over `A` is `φ`. It is the generic
statement `Stacks.AlgebraicGeometry.ModuleLimits.exists_stage_compatibleTriple_single`
(`StacksFrontier/AlgebraicGeometry/ModuleLimits/TripleDescent.lean`), about an arbitrary cospan of
cofiltered limit systems, instantiated at the three stage systems; the centre-side cartesian
stage square it needs is `Stacks.AlmostBlowUp.isPullback_exceptionalToCenter_stageCone_π`, the
companion of the modification-side one. The two shrinkings of the stage — one for the modules, by
Tag 0B8W (1) at each corner, and a second for the comparison, by Tag 01ZR (2) followed by the
reflection of isomorphisms `Stacks.AlgebraicGeometry.ModuleLimits.exists_stage_iso_of_pullback_iso`
— are merged by the vertical pasting law
`Stacks.AlgebraicGeometry.ModuleLimits.sqIso_paste_vert`.

**The production of `α : 𝒪_{X'}^{⊕r} ⟶ 𝒢` from the `ℐ`-adic surjectivity is now available**, as
`Stacks.AlmostBlowUp.exists_hom_free_isIso_near_exceptional`
(`StacksFrontier/AlgebraicGeometry/Blowup/TwoGeneratorAdicFreeLift.lean`): for a finite locally free
`𝒢` on the modification over a Noetherian ring whose restriction `i^*𝒢` is free of rank `r` it
produces an `α` with `i^*α` invertible and with `α` invertible over an open neighbourhood of the
exceptional line. Its two inputs are the `ℐ`-adic surjectivity above at `n = 1` and the global
generation of `𝒢 / 𝓘 𝒢`, and that global generation carries no cohomological content: both
`𝒢 / 𝓘 𝒢` and `𝒪_{X'}^{⊕r} / 𝓘 𝒪_{X'}^{⊕r}` are the direct image along `i` of their restrictions
by Tag 0EL1, so the hypothesis `i^*𝒢 ≅ 𝒪_E^{⊕r}` already makes the quotient projection of the
free module land epimorphically on `𝒢 / 𝓘 𝒢`
(`Stacks.AlmostBlowUp.exists_epi_free_idealPowerQuotient_of_pullback_iso_free`). No passage
through `H⁰(E, i^*𝒢)` enters, and no adjunction counit either: `i^*` inverts the quotient
projection at *every* quasi-coherent module, by
`Stacks.Algebraization.isIso_pullback_map_cokernel_π_of_ker`.

**Full faithfulness is assembled.** It is
`AlgebraicGeometry.fullyFaithful_twoGeneratorFrobeniusColimitComparison`
(`StacksFrontier/AlgebraicGeometry/Descent/FrobeniusColimitVectFullAffine.lean`), under exactly the
hypotheses of Example 0EVH: faithfulness by the trivialising-cover argument
(`…faithful_twoGeneratorFrobeniusColimitComparison`,
`StacksFrontier/AlgebraicGeometry/Descent/FrobeniusColimitVectFaithfulCover.lean`) and fullness with
no Zariski glueing at all, because over an affine base every finite locally free
`colim_F 𝒪`-module is a retract of a free one (`…exists_retract_frobeniusColimitFree`) and
surjectivity of `G.map` passes to retracts (`CategoryTheory.Functor.full_of_retract`). That
retract bypass does **not** extend to essential surjectivity: `𝒢` on the modification is not a
summand of a free module, since the `α` above is invertible only *near* `E`, which is exactly why
the source's own proof finishes with a Zariski glueing.

What is still absent, and is what keeps this file from carrying the tag, is the rest of essential
surjectivity after that reduction — the Zariski reduction to the case `ℱ = 𝒪_Z^{⊕r}` and the
final glueing. Of that, the following are now available.

* **The comparison functor commutes with base change of the square.** Restriction of an object of
  the categorical fibre product along a base change of the square is
  `AlgebraicGeometry.frobeniusColimitVectorBundlesCatPullbackLoc`, and
  `AlgebraicGeometry.frobeniusColimitVectorBundlesCatPullbackLocIso` identifies `Loc (G M)` with
  `G' (ι^* M)` (`StacksFrontier/AlgebraicGeometry/Descent/FrobeniusColimitVectCatPullbackLoc.lean`).
  Both are stated with all eight corners as variables; the content is the cube coherence
  `AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso_cube_app` read through
  `AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso_flip_hom_app`, the identification of
  the square comparison of the transposed square with the inverse of the square comparison, which
  is needed because the cube is stated with the transposed spelling at the top and bottom faces
  and the comparison functor with the untransposed one. This is what lets the *local* hypothesis
  of essential surjectivity be stated at all.
* **Objects glue, over an arbitrary sheaf of rings and with free charts.**
  `AlgebraicGeometry.exists_frobeniusColimitVectorBundle_of_matrixCocycle`
  (`StacksFrontier/AlgebraicGeometry/Descent/FrobeniusColimitVectGlueCocycle.lean`) turns a
  `Stacks.SheafOfModules.MatrixCocycle` over `colim_F 𝒪_X` into a finite locally free
  `colim_F 𝒪_X`-module whose transition to each member of the cover is free of the prescribed
  rank — the spelling the square over a localisation `A_g` presents. Note that
  `Stacks.SheafOfModules.ModulesGlueData` is **not** the machine to use here: it is stated for
  modules over the structure sheaf of a *scheme*, and `colim_F 𝒪_X` is not one. The machine over
  an arbitrary sheaf of rings is `Stacks.SheafOfModules.OModuleGlueData`, whose chart comparison
  is only sectionwise (`…OModuleGlueData.chartIso`); with *free* charts the sectionwise form
  suffices, because
  `Stacks.SheafOfModules.nonempty_over_iso_free_of_combSections_bijective` upgrades a
  trivialisation by sections to an isomorphism of sheaves of modules on the slice site. Finite
  local freeness of the glued module comes from
  `Stacks.SheafOfModules.MatrixCocycle.isFiniteLocallyFree_glued` directly, not from
  `Stacks.SheafOfModules.LocalKernel.isFiniteLocallyFree_of_coversTop`. The glueing datum is also
  accepted in the form the argument actually produces it — an *isomorphism* of the two free charts
  over each overlap, which is what fullness of the comparison over that overlap gives, rather than
  a matrix — by `AlgebraicGeometry.exists_frobeniusColimitVectorBundle_of_overlap`, whose matrix
  cocycle is `Stacks.SheafOfModules.matrixCocycleOfOverlap`
  (`StacksFrontier/Topology/Sheaves/Modules/ModuleGlueing/MatrixCocycleOfOverlap.lean`): the
  components of a slice morphism are `Stacks.SheafOfModules.localModuleHomOfOver` and the matrix is
  their coordinates, the one computation being
  `Stacks.SheafOfModules.freeCoord_overlapApp_freeMk`.
* **Morphisms glue**, by `TopCat.Sheaf.existsUnique_hom_of_localModuleHom`
  (`StacksFrontier/Topology/Sheaves/Glueing/OModuleMapGluing.lean`), which is stated over an
  arbitrary sheaf of rings `𝒪 : (Opens X)ᵒᵖ ⥤ RingCat` and so applies verbatim to `colim_F 𝒪_X`,
  or — when the compatibility is only available over the basic opens, which is where the square of
  Example 0EVH is again a two-generator square — by
  `Stacks.SheafOfModules.existsUnique_hom_of_overMap_eq_of_isBasis`
  (`StacksFrontier/Topology/Sheaves/Glueing/OModuleMapGluingSlice.lean`).
* **The geometry of the final glueing is settled.** The `α` of
  `Stacks.AlmostBlowUp.exists_hom_free_isIso_near_exceptional` is invertible over an open of the
  *modification*, and the glueing needs an open of the *base*;
  `Stacks.AlmostBlowUp.exists_opens_center_isIso_restrict_hom_free`
  (`StacksFrontier/AlgebraicGeometry/Blowup/TwoGeneratorFreeNearCenter.lean`) supplies the passage,
  by properness of the modification (`…isProper_modificationToBase`, hence `b` is a closed map)
  and cartesianness of the square. The two opens the source's final glueing runs over are
  produced together by `Stacks.AlmostBlowUp.exists_opens_cover_isIso_restrict_hom_free`: an open
  over whose preimage `𝒢` is free of rank `r`, and `Stacks.AlmostBlowUp.centerComplement`, over
  which the modification maps isomorphically by Tag 0EV6
  (`…isIso_modificationToBase_restrict_centerComplement`). That they cover is
  `Stacks.AlmostBlowUp.range_exceptionalToModification_eq_preimage_support`, the exceptional line
  read as the preimage of the support of the centre.

**What remains, precisely.** Two pieces. Note that the overlap isomorphisms the first of them has
to produce are legitimate: the overlap of two basic opens `D(g) ⊓ D(h) = D(gh)` is again basic,
and `AlgebraicGeometry.full_twoGeneratorFrobeniusColimitComparison` holds at *every* ring, so
fullness of the comparison applies over it.

1. *The local case over a member of the cover.* The triple `(ℱ, 𝒢, φ)` of `colim_F`-modules has
   to be brought to the ordinary modules of one Frobenius stage — by Tag 0EXB
   (`AlgebraicGeometry.frobeniusColimitVectEquivalence`) at each of the three corners, all three
   being quasi-compact and quasi-separated — then descended to a Noetherian stage by
   `Stacks.AlmostBlowUp.exists_stage_compatible_triple`, after which the item above gives
   `𝒢 ≅ 𝒪_{X'}^{⊕r}` over the preimage of an open neighbourhood of the centre. The Zariski
   shrinking making `ℱ` free is
   `AlgebraicGeometry.exists_cover_free_localizationAway_frobeniusColimit` on the centre.

   **The passage between the two levels is available.** Identifying the structural isomorphism
   `φ` of an object of the categorical fibre product with the comparison `φ_n` of the ordinary
   triple it descends to is `AlgebraicGeometry.exists_frobeniusColimitStageTriple_iso`
   (`StacksFrontier/AlgebraicGeometry/Descent/FrobeniusColimitStageTriple.lean`): every object of
   the categorical fibre product of a cospan of transition functors over three quasi-compact
   quasi-separated corners is isomorphic to
   `AlgebraicGeometry.frobeniusColimitStageTriple n j Ec Em ψ`, the object attached to a pair of
   *ordinary* finite locally free modules `Ec` on the centre and `Em` on the modification
   together with an isomorphism `ψ` of the `j`-fold Frobenius pullbacks of their restrictions to
   the exceptional corner. It is stated with the two legs of the cospan as variables, so it
   applies at the square of Example 0EVH over `A` and over every localisation `A_g` alike. Its
   two ingredients:

   * `AlgebraicGeometry.frobeniusStageFunctorPullbackIso` — **the stage functor of Tag 0EXB
     commutes with the transition functor of Tag 0EXE**, on all sheaves of modules
     `AlgebraicGeometry.frobeniusStageExtendScalarsPullbackIso`. The one piece of content is the
     stage formula `AlgebraicGeometry.frobeniusColimitι_comp_frobeniusColimitStructureSheafHom`,
     which makes both composites extension of scalars along *one and the same* morphism of
     sheaves of rings, so the comparison is Mathlib's
     `CategoryTheory.SheafOfModules.pullbackComp` at each corner with an `eqToIso` between them.
     The two site functors `Opens.map (𝟙 Y) ⋙ Opens.map f.base` and
     `Opens.map f.base ⋙ Opens.map (𝟙 X)` are the same functor, so nothing has to be transported
     across the sites. Without this comparison the conjugate of `φ` by the two descent
     isomorphisms is a morphism between *transitions of stage images* rather than between *stage
     images of transitions*, and the ordinary triple cannot be stated at all.
   * `AlgebraicGeometry.exists_frobeniusStageIso_hom_eq` — **an isomorphism between two stage
     images is presented by an isomorphism of `𝒪_X`-modules at some Frobenius twist.** The
     comparison functor of Tag 0EXB is fully faithful unconditionally, so the isomorphism has a
     preimage in the `CategoryTheory.EndoColim` model of Tag 0EXA, where
     `CategoryTheory.EndoColim.exists_iso_hom_eq` — already in the tree — presents it at a level.
     Note the elaboration hazard: the preimage has to be taken of the isomorphism *retyped* at
     the comparison functor's own spelling of its source and target, which is definitional and
     cheap; taken directly, the unification `F.obj ?X ≅ F.obj ?Y` asks the elaborator to invert
     the comparison functor on objects and times out at `whnf`.

   The structural isomorphism of `AlgebraicGeometry.frobeniusColimitStageTriple` is carried at a
   Frobenius twist `j` rather than on the nose. That is deliberate and is what keeps the triple
   at **one** stage `n`, so that the descent needs no coherence between the bridge and the
   stage-raising isomorphisms; the passage to twist `0`, which the ordinary geometry of this file
   consumes, is item 1a below.

1a. **The pseudococone coherence of the bridge is available.** The equation `coh1` (the one-step
   compatibility of `AlgebraicGeometry.frobeniusStageExtendScalarsPullbackIso` with
   `AlgebraicGeometry.frobeniusPullbackStageIso` and
   `AlgebraicGeometry.frobeniusModulesPullbackIso`) is
   `AlgebraicGeometry.frobeniusStageBridge_coherence`, its finite locally free forms are
   `AlgebraicGeometry.frobeniusStageFunctorPullbackIso_compat` and, iterated,
   `AlgebraicGeometry.frobeniusStageFunctorPullbackIso_iterIso`, and the twist-lowering isomorphism
   `frobeniusColimitStageTriple (n + j) 0 (F^{j,*}Ec) (F^{j,*}Em) φ ≅
   frobeniusColimitStageTriple n j Ec Em ψ` is
   `AlgebraicGeometry.frobeniusColimitStageTripleUntwistIso`, with `φ` given by
   `AlgebraicGeometry.frobeniusStageTripleUntwist`
   (`StacksFrontier/AlgebraicGeometry/Descent/FrobeniusColimitStagePseudococone.lean`). The proof
   goes through `AlgebraicGeometry.frobeniusStageBridge_natTrans_square`: each of the five mates
   becomes an `eqToHom` on underlying presheaves of abelian groups, which is a faithful functor.
   The cospan transform exists as well: the comparison functor of Tag 0EXB commutes with the
   transition functors, `AlgebraicGeometry.frobeniusColimitVectComparisonPullbackIso`, the three
   comparisons form `AlgebraicGeometry.frobeniusColimitVectCospanTransform`, and
   `AlgebraicGeometry.essSurj_mapCospan_frobeniusColimitVectCospanTransform` says every object of
   the fibre product comes from the model
   (`StacksFrontier/AlgebraicGeometry/Descent/FrobeniusColimitComparisonCospan.lean`).

1b. **The comparison functor at a stage object.** `G (S_n 𝒩)` has to be identified with
   `frobeniusColimitStageTriple n 0 (z^*𝒩) (b^*𝒩)` of the ordinary square isomorphism — that is
   what turns the ordinary solution into an isomorphism in the fibre product. The component
   isomorphisms are `AlgebraicGeometry.frobeniusStageFunctorPullbackIso` at the two legs `z` and
   `b`, and the compatibility is a **single-stage** coherence: the bridges carry
   `AlgebraicGeometry.vectPullbackSquareIso` to
   `AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso`. No stage-raising enters, and since
   the square comparison is a composite of two
   `AlgebraicGeometry.frobeniusColimitVectorBundlesPullbackComp` with an `eqToIso` from the
   square's commutativity, it should reduce to `CategoryTheory.SheafOfModules.pullback_assoc`
   exactly as `AlgebraicGeometry.frobeniusColimitPullbackCompOfEq_assoc_rfl` does.

1c. **The `α` of the local case has to be compatible with the given trivialisation, and is not
   yet known to be.** `Stacks.AlmostBlowUp.exists_hom_free_isIso_near_exceptional` and
   `…exists_opens_cover_isIso_restrict_hom_free` produce an `α` with `i^*α` *invertible*; the
   source's sentence is stronger — "*we can choose a map `α : 𝒪_{X'}^{⊕r} → 𝒢` which is
   compatible with the given trivialization of `𝒢|_E`*" — and the local case needs that strength,
   because the triple over the open `U` is identified with `G (𝒪_{X_U}^{⊕r})` only if the
   automorphism `(i^*α)^{-1} ∘ φ` of `𝒪_{E_U}^{⊕r}` is trivial. The `α` that is built *is*
   compatible: it satisfies `α ≫ π_𝒢 = π_free ≫ θ` with `θ` built from the given trivialisation
   `e`, and `i^*` inverts both quotient projections, so `i^*α = i^*π_free ≫ i^*θ ≫ (i^*π_𝒢)^{-1}`
   is determined by `e`. What is owed is the computation identifying that composite with `e.inv`,
   i.e. that `i^*` of `Stacks.Algebraization.idealQuotientPushforwardIso` composed with the
   counit is the identity. The alternative — descending the automorphism from `E` to `Z` — needs
   `Γ(𝐏¹_Z, 𝒪) = Γ(Z, 𝒪)`; the nearest statement in the tree is
   `…ProjectiveSpaceHigherDirectImage.bijective_app_structureMorphism_projectiveSpaceOver` in the
   namespace `Stacks.AlgebraicGeometry` (Tag 01XW), which is for
   `AlgebraicGeometry.projectiveSpaceOver` and would first have to be matched against
   `Proj (exceptionalGrading A f₁ f₂)`.
2. *The assembly.* With items 1, 1a, 1b and 1c, essential surjectivity is: cover `Spec A` by
   basic opens over
   each of which the restricted triple is in the essential image (item 1, plus
   `…frobeniusColimitVectorBundlesCatPullbackLocIso` to state it), glue the local free solutions
   (`…exists_frobeniusColimitVectorBundle_of_overlap`), and glue the two component isomorphisms
   over the centre and
   over the modification into an isomorphism `G N ≅ T` with
   `CategoryTheory.Limits.CategoricalPullback.mkIso`, the compatibility holding because it holds
   over a cover of the exceptional corner. The corner identifications the restricted square needs
   are `Stacks.AlmostBlowUp.centerAwayIsoPreimage`, `…exceptionalAwayIsoPreimage` and
   `…modificationAwayIsoPreimage`
   (`StacksFrontier/AlgebraicGeometry/Blowup/TwoGeneratorCoefficientBaseChange.lean`).
Note that Tag 0EXC, `AlgebraicGeometry.colimVectComparison_isEquivalence`, is proved for
`AlgebraicGeometry.OneGeneratorSquare.colimVectBase`, the `CategoryTheory.EndoColim` model of
`colim_F Vect` of Tag 0EXA, not for `AlgebraicGeometry.frobeniusColimitVectorBundles`; the
comparison of the two cospans of transition functors is
`AlgebraicGeometry.frobeniusColimitVectCospanTransform` (item 1a).

The grading of `A[T₀,T₁]/(f₂T₀ - f₁T₁)` is the one the two-generator square carries,
`(Stacks.AlmostBlowUp.twoGeneratorSquare A f₁ f₂).modificationGraded`, and it is introduced by
`letI` in every type below, exactly as in `Stacks.AlmostBlowUp.twoGenerator_isPullback`, so that
the cartesianness of the square applies to the morphisms occurring here on the nose.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius Stacks.AlmostBlowUp

universe u

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable (A : Type u) [CommRing A] (f₁ f₂ : A) (p : ℕ) [Fact p.Prime] (hpA : (p : A) = 0)

include hpA

omit [Fact p.Prime] in
/-- **The center of the two-generator square is in characteristic `p`.** -/
lemma isInCharacteristic_twoGeneratorCenter :
    IsInCharacteristic (Spec (.of (centerRing A f₁ f₂))) p :=
  isInCharacteristic_of_hom (centerToBase A f₁ f₂) p (isInCharacteristic_spec A p hpA)

omit [Fact p.Prime] in
/-- **The modification of the two-generator square is in characteristic `p`.** -/
lemma isInCharacteristic_twoGeneratorModification :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    IsInCharacteristic (Proj (modificationGrading A f₁ f₂)) p :=
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  isInCharacteristic_of_hom (modificationToBase A f₁ f₂) p (isInCharacteristic_spec A p hpA)

omit [Fact p.Prime] in
/-- **The exceptional fibre of the two-generator square is in characteristic `p`.** -/
lemma isInCharacteristic_twoGeneratorExceptional :
    IsInCharacteristic (Proj (exceptionalGrading A f₁ f₂)) p :=
  isInCharacteristic_of_hom (exceptionalToCenter A f₁ f₂) p
    (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA)

/-- **The functor of Stacks Tag 0EXD.** For the almost blowup square of Example 0EVH in
characteristic `p`, this is the canonical functor

`𝒮_X ⟶ 𝒮_Z ×_{𝒮_E} 𝒮_{X'}`

from the finite locally free `colim_F 𝒪_X`-modules to the categorical fibre product of the
finite locally free `colim_F 𝒪_Z`-modules and the finite locally free `colim_F 𝒪_{X'}`-modules
over the finite locally free `colim_F 𝒪_E`-modules. Tag 0EXD asserts that it is an equivalence;
that assertion is not proved here, so this file carries no `@[stacks 0EXD]` attribute. -/
noncomputable def twoGeneratorFrobeniusColimitComparison :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    frobeniusColimitVectorBundles (Spec (.of A)) p (isInCharacteristic_spec A p hpA) ⥤
      CategoricalPullback
        (frobeniusColimitVectorBundlesPullback p (exceptionalToCenter A f₁ f₂)
          (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
          (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA))
        (frobeniusColimitVectorBundlesPullback p (exceptionalToModification A f₁ f₂)
          (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
          (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)) :=
  letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
  frobeniusColimitVectorBundlesComparison p (modificationToBase A f₁ f₂)
    (centerToBase A f₁ f₂) (exceptionalToModification A f₁ f₂) (exceptionalToCenter A f₁ f₂)
    (isInCharacteristic_spec A p hpA)
    (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)
    (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA)
    (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
    (twoGenerator_isPullback A f₁ f₂).w

end AlgebraicGeometry

end
