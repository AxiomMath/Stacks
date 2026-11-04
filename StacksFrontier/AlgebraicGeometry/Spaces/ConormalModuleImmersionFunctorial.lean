module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraAmbient
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraFunctorial
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleImmersionEtaleRestriction

/-!
# Functoriality of the conormal module of an immersion of algebraic spaces

Let
```
Z --i--→ X
|        |
f        g
↓        ↓
Z' -i'-→ X'
```
be a commutative square of algebraic spaces over a scheme `S` contained in a big fppf site `B`,
in which `i` and `i'` are **immersions** — not necessarily closed immersions.  This file
constructs the canonical map of `𝒪_Z`-modules

`f^*𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}`

of [Stacks Project, Tag 04CP], where `𝒞_{Z/X}` is the conormal module of an immersion of
`AlgebraicGeometry.Space.immersionConormalModule`, that is the degree-one piece of the conormal
algebra of the closed factorisation of Stacks 04CE.

## How the reduction to the closed case is carried

The source proves the lemma by choosing open subspaces `U ⊆ X` and `U' ⊆ X'` with `g(U) ⊆ U'` in
which `i` and `i'` become closed immersions, replacing `X` by `U` and `X'` by `U'`, and then
building the map out of the defining ideal sheaves of the two closed subspaces.  The reduction is
carried here, but it is *already carried* by the definition of the conormal module of an
immersion and by the étale-localization statement of Stacks 04CO that this development has: the
ambient open subspace is the canonical one `X ∖ ∂Z` of
`AlgebraicGeometry.Space.immersionAmbient`, the factorisation through it is the canonical
`AlgebraicGeometry.Space.immersionClosedFactorization` of Stacks 04CE, and
`AlgebraicGeometry.Space.conormalAlgebraOfImmersionPieceIso` identifies the conormal module taken
through that factorisation with `i^*Ker(i^♯)`, the degree-one piece of
`AlgebraicGeometry.Space.conormalAlgebra` of `i` itself.

That identification is what removes the choice of `U` and `U'` from the construction: the map is
built on `i^*Ker(i^♯)`, which depends on `i` alone, and is transported to the conormal modules by
the bridge at `i'` and at `i`.  No open subspace of `X` or of `X'` appears in the construction
below, and no hypothesis relating `g(U)` to `U'` is needed — the condition `g(i(Z)) ⊆ Z'` that
the source extracts from the square is used in the only place the source uses it, namely in the
containment of kernel ideal sheaves `Ker((i')^♯) ⊆ Ker((i ≫ g)^♯)` of
`AlgebraicGeometry.Space.kernelIdealSheaf_le_comp`.

## The two factors

The construction is the two-factor one that [Stacks Project, Tag 09RS] uses for conormal
algebras, taken in degree one, where it is unconditional:

`f^*𝒞_{Z'/X'} ⟶ 𝒞_{Z/X'} ⟶ 𝒞_{Z/X}`.

* The first factor replaces the source `Z'` by `Z`, and is the inverse image along `f` and `i'`
  of the containment `Ker((i')^♯) ⊆ Ker((i ≫ g)^♯)` of
  `AlgebraicGeometry.Space.kernelIdealSheaf_le_comp`, which is where the commutativity of the
  square enters.
* The second factor replaces the ambient space `X'` by `X`, and is the inverse image along `i` of
  the map `g^*Ker((i ≫ g)^♯) ⟶ Ker(i^♯)` of
  `AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap` — pullback of regular functions along
  `g`, which is the step `g^♯(𝓘') ⊆ 𝓘` of the proof of the source.

Between them sits the identification `f^*(i')^* ≅ i^*g^*` furnished by the square, which is the
step `i^{-1}g^{-1} = f^{-1}(i')^{-1}` of the proof of the source.

**Why this is unconditional while Stacks 09RS is not.**
`AlgebraicGeometry.Space.conormalAlgebraSquareMapOfPullbackHom` carries the ambient factor of
Stacks 09RS as an explicit hypothesis `Ψ`, a homomorphism of sheaves of *graded* algebras
`g^*(⨁_{n ≥ 0} 𝓙ⁿ) ⟶ ⨁_{n ≥ 0} 𝓘ⁿ`.  What is missing there is the multiplicativity of the
degreewise family, recorded in the residue section of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraAmbientGradedTransport.lean`.  The
degreewise maps themselves are unconditional — they are
`AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap` — and Stacks 04CP asks for one single
degree, so no multiplicativity is involved and no hypothesis is carried.  The implementation
notes of `StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraSquareMapDegreePropagation.lean`
record the same split from the other side: "the degree-one part of the canonical map of
Stacks 09RS is the canonical map of conormal modules of Stacks 04CP".

## Main definitions

* `AlgebraicGeometry.Space.squarePullbackCompIso`: the identification `f^*(i')^* ≅ i^*g^*` of
  inverse-image functors furnished by a commutative square of arbitrary morphisms.
* `AlgebraicGeometry.Space.conormalAlgebraSquarePieceMap`: the degree-`n` canonical map
  `f^*(𝒞_{Z'/X',n}) ⟶ 𝒞_{Z/X,n}` of a commutative square of arbitrary morphisms, unconditionally.
* `AlgebraicGeometry.Space.conormalMapOfImmersions`: **Stacks 04CP**, the canonical map
  `f^*𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` for a commutative square in which `i` and `i'` are immersions.

## Main results

* `AlgebraicGeometry.Space.conormalMapOfImmersions_eq`: the canonical map is the degree-one
  square map of conormal algebras conjugated by the bridge isomorphisms of the two immersions.
* `AlgebraicGeometry.Space.isIso_conormalAlgebraSquarePieceMap_of_isIso`,
  `AlgebraicGeometry.Space.isIso_conormalMapOfImmersions_of_isIso`: the canonical map is
  invertible when its two factors are, the comparison between them being an isomorphism.
* `AlgebraicGeometry.Space.epi_conormalAlgebraSquarePieceMap_of_epi`,
  `AlgebraicGeometry.Space.epi_conormalMapOfImmersions_of_epi`: and surjective when they are.
  This is the shape in which [Stacks Project, Tag 04CQ] is reached at the generality of
  immersions: the second factor being surjective is the statement about the ideal sheaves.

## Relation to `AlgebraicGeometry.Space.conormalMap`

`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleFunctorial.lean` carries the closed case of
Stacks 04CP, for a square of `AlgebraicGeometry.Space.ClosedSubspaces` and the defining ideal
sheaves of Stacks 03MB.  Nothing here replaces it, and its statement and type are untouched: it
is the shape its consumers use, and the identification of the defining ideal sheaf of a closed
subspace with the kernel ideal sheaf of its inclusion
(`AlgebraicGeometry.Space.kernelIdealSheaf_eq_definingIdealSheaf`) is an equality of sheaves of
ideals and not by itself an equality of the two induced maps `g^*𝓘' ⟶ 𝓘`.

**The two induced maps are now identified**, by
`AlgebraicGeometry.Space.kernelIdealSquareMap_one_eq_idealSheafMap` of
`StacksFrontier/AlgebraicGeometry/Spaces/KernelIdealSquareMapDegreeOne.lean`: for a commutative
square of the inclusions of closed subspaces, `AlgebraicGeometry.Space.kernelIdealSquareMap` in
degree one is `AlgebraicGeometry.Space.idealSheafMap`, across the transports of its source and
target along `AlgebraicGeometry.Space.kernelIdealSheafZPow_one_eq_definingIdealSheaf`.  Both
maps are pinned by their composite with the inclusion of the sheaf of ideals into the structure
sheaf, and that inclusion is a monomorphism.  The agreement is stated for the square map rather
than for the ambient factor `AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap` alone,
which on its own has no source in common with `AlgebraicGeometry.Space.idealSheafMap`; see the
implementation notes of that file.

This file still does not state the identification itself — it is not imported here — and the
statements below are unchanged.

## What part (2) of [Stacks Project, Tag 04G2] still needs

Part (2) of [Stacks Project, Tag 04G2] — that when all four spaces of
[Stacks Project, Tag 04CP] are schemes the canonical map is the one of Morphisms, Lemma
[Stacks Project, Tag 01R4] — is registered, when it is in, at
`AlgebraicGeometry.Space.conormalMapOfImmersions`, because that is where the source's hypotheses
are.  **No attribute for it is claimed here.**  What is done and what is owed:

The two canonical maps are now written in one and the same shape, with the same characterising
lemma on each side.  Schemes-side, `Stacks.Immersion.immersionConormalSheafMap` is
`Stacks.ClosedImmersion.conormalSheafMap` of the square itself conjugated by
`Stacks.Immersion.conormalSheafSelfIso`, and `conormalSheafMap` is the ringed-space square
comparison `Stacks.ClosedImmersion.pullbackCompIso` followed by the pullback along `i` of
`Stacks.ClosedImmersion.idealSheafMap`, characterised by
`Stacks.ClosedImmersion.idealSheafMap_comp_ι` and read inside `i^*𝒪` by
`Stacks.ClosedImmersion.conormalSheafMap_comp_pullback_ι`.  Spaces-side,
`AlgebraicGeometry.Space.conormalMapOfImmersions` is
`AlgebraicGeometry.Space.conormalAlgebraSquarePieceMap` of the square itself conjugated by
`AlgebraicGeometry.Space.conormalAlgebraOfImmersionPieceIso`, and
`AlgebraicGeometry.Space.conormalAlgebraSquarePieceMap_eq_comp` of
`StacksFrontier/AlgebraicGeometry/Spaces/KernelIdealSquareMap.lean` puts that into the matching
shape: the square comparison `AlgebraicGeometry.Space.squarePullbackCompIso` followed by the
inverse image along `i` of the single map
`AlgebraicGeometry.Space.kernelIdealSquareMap`, characterised by
`AlgebraicGeometry.Space.kernelIdealSquareMap_comp_ι` and read inside `i^*𝒪` by
`AlgebraicGeometry.Space.conormalAlgebraSquarePieceMap_comp_map_ι` and
`AlgebraicGeometry.Space.conormalAlgebraSquarePieceMap_comp_map_ι_unit`.  The two square
comparisons are compared at the unit module, where both have a description:
`Stacks.ClosedImmersion.pullbackCompIso_hom_comp_modulePullbackUnitToUnit` and
`AlgebraicGeometry.Space.squarePullbackCompIso_hom_comp_structureModulePullbackMap`, the second
in `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSquareComparisonSpacesUnit.lean`.  Note that the
monomorphy `CategoryTheory.eq_of_comp_eq_comp` needs for that comparison is only ever needed on
the **ringed-space** side, where the composite is invertible by
`RingedSpaceModuleAdjunction.isIso_modulePullbackUnitToUnit`; the spaces-side invertibility,
which `AlgebraicGeometry.Space.isIso_structureModulePullbackMap_of_unitSection` reduces to a
condition on the unit section and which this development does not have, is **not** needed.

Because both maps live at the "self" presentations — `i^*Ker(i^♯)` spaces-side and `i^*ℐ_i`
ringed-space side — and the two conjugating isomorphisms are structurally parallel, part (2)
reduces by formal conjugation to one statement: that the comparison

`(yoneda.map j)^*Ker((yoneda.map j)^♯) ≅ 𝒜_R(j^*ℐ_j)`

carries `conormalAlgebraSquarePieceMap` in degree one to the associated module of
`Stacks.ClosedImmersion.conormalSheafMap`.  Three things are owed for that, and the third is a
genuine obstruction rather than bookkeeping.

* The unit-module compatibility of
  `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` — **proved**, as
  `AlgebraicGeometry.Space.structureModulePullbackMap_representedAssociatedModulePullbackIso` of
  `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedAssociatedModulePullbackUnit.lean`.  It is
  the composite of the two halves,
  `AlgebraicGeometry.Space.structureModulePullbackMap_representedModuleObjPullbackIso` and
  `AlgebraicGeometry.SmallEtale.pullbackObjUnitToUnit_associatedModuleBaseChangeIso`, joined by
  the naturality below.
* The **naturality in the module** of
  `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` — **proved**, as
  `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_naturality` of
  `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedAssociatedModulePullbackNaturality.lean`,
  together with `AlgebraicGeometry.Space.representedModuleObjPullbackIso_naturality` for the
  first factor.  It is **formal** and not a missing input: the object form is a composite
  of components of natural transformations, and
  `Stacks.Equivalence.conjugateObjIso_naturality` of
  `StacksFrontier/CategoryTheory/Equivalence/ConjugateObjIsoNaturality.lean` proves the naturality
  of any family given by that formula, once and generically, with the formula discharged at the
  instantiation by `rfl` as an equation of isomorphisms.
* **The comparison of ideal sheaves itself, at immersion generality.**  The identification
  `Ker((yoneda.map j)^♯) ≅ 𝒜_V(ℐ_j)` of a represented morphism's kernel ideal sheaf with the
  associated module of `Stacks.ClosedImmersion.idealSheaf` of the underlying morphism of schemes
  exists only for a **closed** immersion, as
  `AlgebraicGeometry.Space.representedAssociatedModuleIdealSheafIso` of
  `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedZariskiDefiningIdeal.lean`.  The Zariski half
  is unconditional
  (`AlgebraicGeometry.Space.chartZariskiKernelIdealSheafSelfChartIsoIdealSheaf`, no hypothesis on
  `j`), but exhibiting the kernel ideal sheaf as the associated module of that restriction needs
  it to be **quasi-coherent on the small étale site**, and the only route in the tree is
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_kernelIdealSheaf` of
  [Stacks Project, Tag 082Z] (1), which assumes the morphism quasi-compact.  For a general
  immersion the kernel ideal sheaf is the ideal of the scheme-theoretic image, whose
  quasi-coherence Morphisms, Lemma [Stacks Project, Tag 01R8] derives from quasi-compactness, so
  this is not merely an unproved lemma.

**Why the comparison at the conormal level does not avoid it, which is worth recording.**  A
comparison

`Θ_j : (yoneda.map j)^*Ker((yoneda.map j)^♯) ≅ 𝒜_R(j^*ℐ_j)`

*does* exist at immersion generality: it is
`AlgebraicGeometry.Space.conormalAlgebraOfImmersionPieceIso` in degree one, followed by part (1)
(`AlgebraicGeometry.Space.conormalModuleOfImmersionRepresentedIso`), followed by the associated
module of `Stacks.Immersion.conormalSheafSelfIso`.  It does not help, because both canonical
maps factor as the square comparison followed by the inverse image along `i` of a **map of ideal
sheaves on the ambient**, and comparing the two factorisations needs the comparison of those
ideal sheaves *before* the inverse image along `i`, which is the display above.  Composing the
target square with the inverse image of the inclusion into the structure sheaf does not rescue
it either: `i^*` of a monomorphism of ideal sheaves is not a monomorphism, so nothing can be
cancelled there, whereas on the ambient the inclusion `ι` is a monomorphism on both sides.

**The way round is the source's own reduction, and it is available.**  The source replaces `X` by
an open `U` and `X'` by an open `U'` with `g(U) ⊆ U'` on which `i` and `i'` become closed
immersions, and such a pair can be *constructed* from the square rather than chosen: take
`U' = i'.coborderRange` and `U = i.coborderRange ⊓ g⁻¹ᵁ i'.coborderRange`.  Then `i` factors
through `U` — its image lies in `i.coborderRange`, and in `g⁻¹ᵁ i'.coborderRange` because
`i ≫ g = f ≫ i'` carries it into the image of `i'` — it is a closed immersion onto `U` since
`U ≤ i.coborderRange`, and `g` restricts to `U ⟶ U'` by construction.  So the canonical
ambient `X ∖ ∂Z` is **not** functorial in the square, but this smaller one is.

For a square of *represented* morphisms, which is the only case part (2) is about, every piece of
that construction is a declaration of the library, so the pair is three definitions away:

* the opens as objects of the site are `AlgebraicGeometry.Space.openSub` with
  `AlgebraicGeometry.Space.openSubHom`
  (`StacksFrontier/AlgebraicGeometry/Spaces/SheafSupport.lean`), for which
  `AlgebraicGeometry.Space.mono_openSubHom_of_opens` and
  `AlgebraicGeometry.Space.toScheme_map_openSubHom` are available;
* `U'` is already built, as `AlgebraicGeometry.Space.immersionCoborderObj` with the closed
  factorisation `AlgebraicGeometry.Space.immersionCoborderLift`
  (`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedImmersionCoborderLift.lean`);
* the factorisation of the upper morphism through `U` is
  `AlgebraicGeometry.Space.openSubLift`, which asks for the pointwise form of the containment of
  ranges that the two displayed facts supply, with
  `AlgebraicGeometry.Space.openSubLift_comp_openSubHom` and
  `AlgebraicGeometry.Space.toScheme_map_openSubLift`;
* the morphism `U ⟶ U'` is `AlgebraicGeometry.Space.openSubMap` of
  `StacksFrontier/AlgebraicGeometry/Spaces/AffineChartDiagramCofinal.lean`, whose hypothesis
  `O ≤ (toScheme.map γ) ⁻¹ᵁ O'` is `inf_le_right` for this pair, with
  `AlgebraicGeometry.Space.openSubMap_comp_openSubHom` for the triangle and
  `AlgebraicGeometry.Space.toScheme_map_openSubMap` for its morphism of schemes;
* the commutativity of the resulting square of lifts follows from the two triangles, the
  inclusion of the ambient being a monomorphism.

The one step that is not an application of an existing lemma is that the lift of the upper morphism
to `U` is a **closed** immersion of schemes.
`AlgebraicGeometry.Space.isClosedImmersion_liftCoborder` gives it only at
`U = i.coborderRange`; for the smaller `U` it is
`AlgebraicGeometry.isClosedImmersion_resLE_of_le_coborderRange` together with the identification
of `AlgebraicGeometry.Space.openLiftScheme` with that restriction, the preimage of `U` being the
whole source.

## What part (2) needs after that reduction

The reduction is carried by the **composition law** on each side: the change of ambient is itself
the canonical map of a restriction square, and its compatibility with the canonical map of the
original square is that law for the two stacked squares.  Schemes-side the law is proved at
immersion generality, `Stacks.Immersion.immersionConormalSheafMap_comp` of
`StacksFrontier/AlgebraicGeometry/Conormal/SquareMap.lean`, with
`Stacks.Immersion.immersionConormalSheafMap_morphismRestrict` and
`Stacks.Immersion.modulePullbackRestrictIso_comp_conormalSheafSelfRestrictIso` identifying the
restriction comparison with the canonical map of the restriction square.  **Spaces-side the law
is proved too**, at the same generality:

* `AlgebraicGeometry.Space.kernelIdealSquareMap_comp` of
  `StacksFrontier/AlgebraicGeometry/Spaces/KernelIdealSquareMapComposition.lean` is the ideal-sheaf
  level of the law, under the two commutativities alone.
* `AlgebraicGeometry.Space.squarePullbackCompIso_paste` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSquarePieceMapComposition.lean` is the
  comparison level, for arbitrary morphisms.
* Their assembly is `AlgebraicGeometry.Space.kernelIdealZPowSquareMap_comp` and
  `AlgebraicGeometry.Space.conormalMapOfImmersions_comp` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSquarePieceMapCompositionLaw.lean`, under the
  three commutativities and the three immersions alone.  The kernel deterministic timeout of a
  direct assembly is not caused by the two spellings of the degree-one piece of the conormal
  algebra meeting inside one composite, as the implementation notes of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSquarePieceMapComposition.lean` show — the chain
  carried out wholly at the `kernelIdealSheafZPow` spelling, where the `piece` spelling never
  occurs, times out just the same, and so does the pasting expanded at a *variable* module.  The
  assembly works with **no intermediate statement at the geometric instance at all**: it is one
  instantiation of `Stacks.CategoryTheory.square_map_comp`, proved at variables, whose five
  hypotheses are the two halves above and three instances of a `rfl`.
* The spaces-side change of ambient is [Stacks Project, Tag 09RR],
  `AlgebraicGeometry.Space.conormalAlgebraEtaleRestrictionPieceIso`, and it **is** an instance of
  the square map.  Its square comparison is `AlgebraicGeometry.Space.squarePullbackCompIso` of
  the same square on the nose:
  `AlgebraicGeometry.Space.modulePullbackSquareCompIso_eq` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalEtaleRestrictionSquareMap.lean` is that, by
  `rfl` — the two definitions are character-for-character the same body up to the name of a bound
  variable, so they are a duplicate pair and a dedup worth doing.  **The identification itself is
  now proved**, as
  `AlgebraicGeometry.Space.conormalAlgebraEtaleRestrictionPieceIso_hom_eq` of the same file: in
  every degree `n`, 09RR's comparison is
  `AlgebraicGeometry.Space.conormalAlgebraSquarePieceMap` of the square.

  What it took, for the record, was one equation of maps into `kernelIdealSheafZPow iU n`, whose
  inclusion `ι` is a monomorphism, namely

  `Λ.hom.app (kernelIdealSheafZPow i n) ≫ eqToHom (etaleModulePullback_kernelIdealSheafZPow_eq …)
   = kernelIdealSquareMap iU i p φ h n`

  for `Λ = AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`
  (`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_hom_app_kernelIdealSheafZPow`);
  composing with `ι` reduced it by `AlgebraicGeometry.Space.kernelIdealSquareMap_comp_ι` and the
  naturality of `Λ` to two statements, both of which are proved:

  * that the equality of modules is compatible with the two inclusions into the unit module —
    `AlgebraicGeometry.Space.etaleModulePullback_idealSheafZPow_eqToHom_comp_ι`, from the equality
    of *submodules* `AlgebraicGeometry.Space.etaleRestrictionIdealSheafZPowSheaf_eq` through the
    generic `Stacks.SheafOfModules.Submodule.eqToHom_comp_ι`;
  * that `Λ.hom.app (SheafOfModules.unit (structureRingSheaf X))` is
    `AlgebraicGeometry.Space.structureModulePullbackMap φ` —
    `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_hom_app_unit_eq` of
    `StacksFrontier/AlgebraicGeometry/Spaces/EtaleModulePullbackUnitStructureSheaf.lean`.  The
    route that proves it is **neither** of the two descriptions compared in the implementation
    notes of `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleEtaleRestriction.lean`
    (`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_unit_app` after the unit of the
    extension of scalars, and `AlgebraicGeometry.Space.structureModulePullbackMap_transpose` after
    both transposes) nor the `AlgebraicGeometry.Space.etaleModulePullbackAdjunction` route: it is the **corepresentability comparison**
    `AlgebraicGeometry.Space.modulePullbackUnitIso` as a common form, which the chartwise
    description reaches by semilinearity out of the unit module and Equation 03LW by comparing
    the transposes along Stacks 03CZ on underlying sheaves of sets.  Neither half needs the unit
    of the étale restriction adjunction on sections.
* Finally the closed case of part (2) over the constructed pair of ambients.  Its **ideal-sheaf
  level is now proved**:
  `kernelIdealSquareMap_representedAssociatedModuleKernelIdealZPowIso`, in the namespace
  `AlgebraicGeometry.Space` and written without the prefix so that it fits, of
  `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedKernelIdealSquareMapAgreement.lean` says
  that `AlgebraicGeometry.Space.kernelIdealSquareMap` in degree one is the associated module of
  `Stacks.ClosedImmersion.idealSheafMap`, across
  `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` and the two ideal-sheaf
  identifications.  The input it needed —
  `AlgebraicGeometry.Space.representedAssociatedModuleIdealSheafIso` read as a morphism-level
  `… ≫ ι = …` rather than in the transposed and sections forms
  `StacksFrontier/AlgebraicGeometry/Spaces/AssociatedModuleChartPushTranspose.lean` has — is
  `AlgebraicGeometry.Space.representedAssociatedModuleIdealSheafIso_hom_comp_ι` of
  `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedAssociatedIdealSheafInclusion.lean`.

  **What remains after that is the whole residue of part (2).**  The two square-comparison halves
  `Stacks.ClosedImmersion.pullbackCompIso_hom_comp_modulePullbackUnitToUnit` and
  `AlgebraicGeometry.Space.squarePullbackCompIso_hom_comp_structureModulePullbackMap` are proved,
  but they do not leave only the ideal-level compatibility to be shown.  Those two halves describe the square
  comparisons at the **structure sheaf**, and that does not determine them at the **ideal
  sheaf**, which is where the two canonical maps of conormal modules read them: the inverse image
  along the upper morphism of the inclusion of a sheaf of ideals is not a monomorphism, exactly as
  the paragraph above on `Θ_j` records, so nothing transports the description from the one module
  to the other.  Both square comparisons are built from the composition comparison of
  [Stacks Project, Tag 03LU] on each side, so their agreement is the compatibility of
  `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` with **composition** of
  represented morphisms.  That one statement is what the closed case of part (2) now reduces to.

  **What that statement itself reduces to.**  The compatibility of the transport with
  composition is stated and reduced in
  `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedAssociatedModulePullbackComposition.lean`.
  The reduction there is exact — nothing is left over — and it carries the statement to the same
  compatibility for `AlgebraicGeometry.Space.representedModuleObjPullbackIso`, the transport
  before the associated module is taken:
  `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_comp_of_objComp`.  The two
  comparisons of [Stacks Project, Tag 03LC] (1) which the transport at an associated module
  carries cancel against the ones that tag's own composition law produces, and **that
  composition law is proved**, as
  `AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso_comp` and
  `AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso_comp` of
  `StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/`
  `StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/SmallEtaleAssociatedModuleBaseChangeComposition.lean`.

  What is **still owed** is therefore the composition law for
  `AlgebraicGeometry.Space.representedModuleObjPullbackIso`, and the route to it is
  2-categorical bookkeeping over one genuinely missing statement.  The bookkeeping is
  `CategoryTheory.Adjunction.leftAdjointUniq_hom_comp_whisker` of
  `StacksFrontier/CategoryTheory/Adjunction/UniqueComp.lean`, which is exactly the hexagon a
  cocycle condition for a system of comparisons of left adjoints needs: it applies with the two
  systems `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`-conjugated into one
  pair of categories, where `AlgebraicGeometry.Space.representedModulePullbackIso` is
  `CategoryTheory.Adjunction.leftAdjointUniq` of two adjunctions with a *common* right adjoint,
  and `CategoryTheory.leftAdjointUniq_transport` moves the comparison between the conjugated and
  the unconjugated forms.  Its only input beyond those is the hypothesis `hcomp`, which here is
  the composition law for the comparison of *direct* images
  `AlgebraicGeometry.Space.representedModulePushforwardSquareIso`.  That comparison is assembled
  from `CategoryTheory.SheafOfModules.pushforwardComp`, from
  `CategoryTheory.SheafOfModules.pushforwardCongr₂` along
  `AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso`, and from
  `AlgebraicGeometry.Space.modulePushforwardChartIso`, so its composition law needs two things,
  neither of which any declaration in the tree states:

  * the composition law for `AlgebraicGeometry.Space.modulePushforwardChartIso` — that the
    identification of the direct image of [Stacks Project, Tag 03LU] along a *representable*
    morphism with the direct image along base change of étale scheme charts carries
    `AlgebraicGeometry.Space.modulePushforwardCompIso` to the base-change composition.  This is
    the irreducible mathematical content of part (2)'s residue: on the one side the comparison
    is `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp`, which is
    `AlgebraicGeometry.Space.spacesBaseChange_pushforward_compTypeU` — restriction along a
    composite of base-change functors — transported through the comparison equivalence of
    [Stacks Project, Tag 03G1], and on the other it is the composition of chart base changes.
    On sections the identification is `AlgebraicGeometry.Space.chartComparison`
    (`AlgebraicGeometry.Space.modulePushforwardChartIso_hom_app_apply`), whose only
    non-computable factor `AlgebraicGeometry.Space.smallEtaleComparisonRanIso` is a
    `CategoryTheory.Adjunction.rightAdjointUniq` **depending on the source alone**, so it is
    cancellable by whiskering with the comparison restriction, which is fully faithful — that is
    the route `AlgebraicGeometry.Space.smallEtaleRingedToposHom_representable` is built along,
    and `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp_comparison` is the
    compatibility of the composition isomorphism with the geometric comparison that the
    cancellation consumes.
  * the composition law for `AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso`, the
    sites-level identification of base change of schemes with base change of charts.  Nothing
    states it; `AlgebraicGeometry.Space.representedSmallEtaleBaseChangeComponent_inv_comp_snd`
    characterises its components as morphisms over the two projections, which is what a proof by
    uniqueness of a morphism into a fibre product would use.

  A composition comparison for `AlgebraicGeometry.Space.smallBaseChange` itself — the functor
  `smallBaseChange g hg ⋙ smallBaseChange f hf ≅ smallBaseChange (f ≫ g) …` together with its
  compatibility with `AlgebraicGeometry.Space.smallBaseChangeSharp` — is absent too and is what
  both bullets are stated over.

Two things the schemes side already has, so that nothing is needed there: the identification of the schemes-side change of
ambient with the canonical map of its restriction square is
`Stacks.Immersion.modulePullbackRestrictIso_comp_conormalSheafSelfRestrictIso` of
`StacksFrontier/AlgebraicGeometry/Conormal/RestrictSquareMap.lean`, and its invertibility for nested
opens is `Stacks.Immersion.isIso_immersionConormalSheafMap_homOfLE` of
`StacksFrontier/AlgebraicGeometry/Conormal/RestrictSquareIso.lean`; a naturality of
`Stacks.Immersion.conormalSheafFactorIso` in the ambient open is **not** needed, those two
statements playing its role.

Each of these is an equation between declarations that all exist; none of them names an
object this development does not have.

## References

* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO)
* [Stacks Project, Tag 04CE](https://stacks.math.columbia.edu/tag/04CE)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 09RS](https://stacks.math.columbia.edu/tag/09RS)
* [Stacks Project, Tag 04CQ](https://stacks.math.columbia.edu/tag/04CQ)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {Z X Z' X' : AlgebraicSpaces B S hS}

/-! ### The identification `f^*(i')^* ≅ i^*g^*` of a commutative square -/

/-- **The identification `f^*(i')^* ≅ i^*g^*` furnished by a commutative square.**  The two
sides are the inverse images of `𝒪`-modules along the two ways around the square, compared by
the Stacks 03LU composition comparison `AlgebraicGeometry.Space.modulePullbackCompIso` on each
side and the commutativity of the square in the middle.

This is the identification `i^{-1}g^{-1} = f^{-1}(i')^{-1}` of the last step of the proof of
[Stacks Project, Tag 04CP].  It is `AlgebraicGeometry.Space.conormalPullbackCompIso` with the
inclusions of closed subspaces replaced by arbitrary morphisms, which is all that construction
uses. -/
noncomputable def squarePullbackCompIso (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    (hsq : i ≫ g = f ≫ i') :
    modulePullback B S hS i' ⋙ modulePullback B S hS f ≅
      modulePullback B S hS g ⋙ modulePullback B S hS i :=
  modulePullbackCompIso B S hS f i' ≪≫
    eqToIso (congrArg (fun h : Z ⟶ X' => modulePullback B S hS h) hsq.symm) ≪≫
    (modulePullbackCompIso B S hS i g).symm

/-! ### The degree-`n` canonical map of a commutative square -/

/-- **The degree-`n` canonical map of conormal algebras of a commutative square**, for arbitrary
morphisms `i`, `i'`, `f`, `g` with `i ≫ g = f ≫ i'`:

`f^*(i'^*((𝓘')ⁿ)) ⟶ i^*(𝓘ⁿ)`,

where `𝓘 = Ker(i^♯)` and `𝓘' = Ker((i')^♯)`.  It is the two-factor composite of the proof of
[Stacks Project, Tag 09RS] in the single degree `n`:

* the inverse image along `f` and `i'` of the degree-`n` part of the containment
  `𝓘' ⊆ Ker((i ≫ g)^♯)` of `AlgebraicGeometry.Space.kernelIdealSheaf_le_comp`, which is where the
  commutativity of the square is used;
* the identification `f^*(i')^* ≅ i^*g^*` of `AlgebraicGeometry.Space.squarePullbackCompIso`;
* the inverse image along `i` of the map `g^*(Ker((i ≫ g)^♯)ⁿ) ⟶ 𝓘ⁿ` of
  `AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap`, which is pullback of regular
  functions along `g`.

Unlike `AlgebraicGeometry.Space.conormalAlgebraSquareMapOfPullbackHom`, which assembles these
degreewise maps into a homomorphism of sheaves of graded algebras and therefore carries the
multiplicativity as a hypothesis, this is a single degree and carries nothing. -/
noncomputable def conormalAlgebraSquarePieceMap (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z')
    (g : X ⟶ X') (hsq : i ≫ g = f ≫ i') (n : ℤ) :
    (modulePullback B S hS f).obj ((conormalAlgebra B S hS i').piece n) ⟶
      (conormalAlgebra B S hS i).piece n :=
  (modulePullback B S hS f).map ((modulePullback B S hS i').map
      ((kernelIdealGradedAlgebraCompHom B S hS i i' f g hsq).app n)) ≫
    (squarePullbackCompIso B S hS i i' f g hsq).hom.app
      (kernelIdealSheafZPow B S hS (i ≫ g) n).toSheafOfModules ≫
    (modulePullback B S hS i).map (kernelIdealSheafZPowPullbackMap B S hS i g n)

/-- The degree-`n` canonical map of a commutative square is the composite of its three steps. -/
theorem conormalAlgebraSquarePieceMap_eq (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    (hsq : i ≫ g = f ≫ i') (n : ℤ) :
    conormalAlgebraSquarePieceMap B S hS i i' f g hsq n =
      (modulePullback B S hS f).map ((modulePullback B S hS i').map
          ((kernelIdealGradedAlgebraCompHom B S hS i i' f g hsq).app n)) ≫
        (squarePullbackCompIso B S hS i i' f g hsq).hom.app
          (kernelIdealSheafZPow B S hS (i ≫ g) n).toSheafOfModules ≫
        (modulePullback B S hS i).map (kernelIdealSheafZPowPullbackMap B S hS i g n) :=
  rfl

/-- The middle comparison of the degree-`n` map of a commutative square is an isomorphism. -/
private theorem isIso_squarePullbackCompIso_hom_app_kernelIdealSheafZPow (i : Z ⟶ X)
    (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X') (hsq : i ≫ g = f ≫ i') (n : ℤ) :
    IsIso ((squarePullbackCompIso B S hS i i' f g hsq).hom.app
      (kernelIdealSheafZPow B S hS (i ≫ g) n).toSheafOfModules) :=
  inferInstanceAs (IsIso ((squarePullbackCompIso B S hS i i' f g hsq).app
    (kernelIdealSheafZPow B S hS (i ≫ g) n).toSheafOfModules).hom)

/-- **The degree-`n` canonical map of a commutative square is invertible when its two factors
are.**  The middle comparison `AlgebraicGeometry.Space.squarePullbackCompIso` is a component of a
natural isomorphism, and the two outer factors are inverse images of the given maps, so a functor
carries them to isomorphisms. -/
theorem isIso_conormalAlgebraSquarePieceMap_of_isIso (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z')
    (g : X ⟶ X') (hsq : i ≫ g = f ≫ i') (n : ℤ)
    (hcomp : IsIso ((kernelIdealGradedAlgebraCompHom B S hS i i' f g hsq).app n))
    (hambient : IsIso (kernelIdealSheafZPowPullbackMap B S hS i g n)) :
    IsIso (conormalAlgebraSquarePieceMap B S hS i i' f g hsq n) := by
  rw [conormalAlgebraSquarePieceMap_eq]
  have h₁ : IsIso ((modulePullback B S hS i').map
      ((kernelIdealGradedAlgebraCompHom B S hS i i' f g hsq).app n)) :=
    @Functor.map_isIso _ _ _ _ _ _ _ _ hcomp
  have h₂ : IsIso ((modulePullback B S hS f).map ((modulePullback B S hS i').map
      ((kernelIdealGradedAlgebraCompHom B S hS i i' f g hsq).app n))) :=
    @Functor.map_isIso _ _ _ _ _ _ _ _ h₁
  have h₃ := isIso_squarePullbackCompIso_hom_app_kernelIdealSheafZPow B S hS i i' f g hsq n
  have h₄ : IsIso ((modulePullback B S hS i).map
      (kernelIdealSheafZPowPullbackMap B S hS i g n)) :=
    @Functor.map_isIso _ _ _ _ _ _ _ _ hambient
  exact IsIso.comp_isIso' h₂ (IsIso.comp_isIso' h₃ h₄)

/-- **The degree-`n` canonical map of a commutative square is surjective when its two factors
are.**  The middle comparison is an isomorphism, hence an epimorphism, and a composite of
epimorphisms is an epimorphism.

This is the shape in which the surjectivity assertion of [Stacks Project, Tag 04CQ] is reached:
in degree one the second factor is the map `g^*𝓘' ⟶ 𝓘` of ideal sheaves, and its surjectivity is
what the source reduces the assertion to. -/
theorem epi_conormalAlgebraSquarePieceMap_of_epi (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z')
    (g : X ⟶ X') (hsq : i ≫ g = f ≫ i') (n : ℤ)
    (hcomp : Epi ((modulePullback B S hS f).map ((modulePullback B S hS i').map
      ((kernelIdealGradedAlgebraCompHom B S hS i i' f g hsq).app n))))
    (hambient : Epi ((modulePullback B S hS i).map
      (kernelIdealSheafZPowPullbackMap B S hS i g n))) :
    Epi (conormalAlgebraSquarePieceMap B S hS i i' f g hsq n) := by
  rw [conormalAlgebraSquarePieceMap_eq]
  have hmidIso := isIso_squarePullbackCompIso_hom_app_kernelIdealSheafZPow B S hS i i' f g hsq n
  have hmid := @IsIso.epi_of_iso _ _ _ _ _ hmidIso
  exact @epi_comp _ _ _ _ _ _ hcomp _ (@epi_comp _ _ _ _ _ _ hmid _ hambient)

/-! ### Stacks 04CP -/

/-- **Stacks 04CP.**  Let
```
Z --i--→ X
|        |
f        g
↓        ↓
Z' -i'-→ X'
```
be a commutative square of algebraic spaces over `S` in which `i` and `i'` are immersions.  Then
there is a canonical map of `𝒪_Z`-modules

`f^*𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}`

between the conormal modules of the two immersions.

The conormal modules are `AlgebraicGeometry.Space.immersionConormalModule`, the conormal
modules taken through the canonical closed factorisation of Stacks 04CE, which is how the
source's reduction of an immersion to a closed immersion into an open subspace is carried.  The
map is the degree-one canonical map `AlgebraicGeometry.Space.conormalAlgebraSquarePieceMap` of
the square, conjugated by the bridge `AlgebraicGeometry.Space.conormalAlgebraOfImmersionPieceIso`
at `i'` and at `i`; the module documentation of this file explains why that construction needs no
choice of ambient open subspaces and no hypothesis beyond the commutativity of the square. -/
@[stacks 04CP "the canonical map, for arbitrary immersions"]
noncomputable def conormalMapOfImmersions (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    (hi : IsImmersion B S hS i.hom) (hi' : IsImmersion B S hS i'.hom)
    (hsq : i ≫ g = f ≫ i') :
    (modulePullback B S hS f).obj (immersionConormalModule B S hS i' hi') ⟶
      immersionConormalModule B S hS i hi :=
  (modulePullback B S hS f).map (conormalAlgebraOfImmersionPieceIso B S hS i' hi' 1).inv ≫
    conormalAlgebraSquarePieceMap B S hS i i' f g hsq 1 ≫
    (conormalAlgebraOfImmersionPieceIso B S hS i hi 1).hom

/-- The canonical map of [Stacks Project, Tag 04CP] is the degree-one canonical map of conormal
algebras of the square conjugated by the bridge isomorphisms of the two immersions. -/
theorem conormalMapOfImmersions_eq (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    (hi : IsImmersion B S hS i.hom) (hi' : IsImmersion B S hS i'.hom)
    (hsq : i ≫ g = f ≫ i') :
    conormalMapOfImmersions B S hS i i' f g hi hi' hsq =
      (modulePullback B S hS f).map (conormalAlgebraOfImmersionPieceIso B S hS i' hi' 1).inv ≫
        conormalAlgebraSquarePieceMap B S hS i i' f g hsq 1 ≫
        (conormalAlgebraOfImmersionPieceIso B S hS i hi 1).hom :=
  rfl

/-- The inverse image of the inverse of the bridge isomorphism at an immersion in degree one is an
isomorphism. -/
private theorem isIso_modulePullback_map_conormalAlgebraOfImmersionPieceIso_inv (i' : Z' ⟶ X')
    (hi' : IsImmersion B S hS i'.hom) (f : Z ⟶ Z') :
    IsIso ((modulePullback B S hS f).map
      (conormalAlgebraOfImmersionPieceIso B S hS i' hi' 1).inv) :=
  @Functor.map_isIso _ _ _ _ _ _ _ _ (Iso.isIso_inv _)

/-- **The canonical map of [Stacks Project, Tag 04CP] is invertible when the degree-one square
map is.**  The two outer factors are the bridge isomorphisms of
`AlgebraicGeometry.Space.conormalAlgebraOfImmersionPieceIso`, and a functor carries an
isomorphism to an isomorphism. -/
theorem isIso_conormalMapOfImmersions_of_isIso (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z')
    (g : X ⟶ X') (hi : IsImmersion B S hS i.hom) (hi' : IsImmersion B S hS i'.hom)
    (hsq : i ≫ g = f ≫ i')
    (h : IsIso (conormalAlgebraSquarePieceMap B S hS i i' f g hsq 1)) :
    IsIso (conormalMapOfImmersions B S hS i i' f g hi hi' hsq) := by
  rw [conormalMapOfImmersions_eq]
  have h₁ := isIso_modulePullback_map_conormalAlgebraOfImmersionPieceIso_inv B S hS i' hi' f
  exact IsIso.comp_isIso' h₁ (IsIso.comp_isIso' h (Iso.isIso_hom _))

/-- **The canonical map of [Stacks Project, Tag 04CP] is surjective when the degree-one square
map is.**  The two outer factors are isomorphisms, hence epimorphisms, and a composite of
epimorphisms is an epimorphism.

This is the generality at which the surjectivity assertion of [Stacks Project, Tag 04CQ] would be
stated for immersions; `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleBaseChangeEpi.lean`
carries that assertion for closed subspaces. -/
theorem epi_conormalMapOfImmersions_of_epi (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    (hi : IsImmersion B S hS i.hom) (hi' : IsImmersion B S hS i'.hom)
    (hsq : i ≫ g = f ≫ i')
    (h : Epi (conormalAlgebraSquarePieceMap B S hS i i' f g hsq 1)) :
    Epi (conormalMapOfImmersions B S hS i i' f g hi hi' hsq) := by
  rw [conormalMapOfImmersions_eq]
  have h₁ := isIso_modulePullback_map_conormalAlgebraOfImmersionPieceIso_inv B S hS i' hi' f
  exact @epi_comp _ _ _ _ _ _ (@IsIso.epi_of_iso _ _ _ _ _ h₁) _
    (@epi_comp _ _ _ _ _ _ h _ (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom _)))

end AlgebraicGeometry.Space

end
