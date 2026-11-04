module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.Comparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.AssociatedModuleColimits
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentInternalHom
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSiteOfLe
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPreservesColimits
public import StacksCore.Tactic.StacksAttribute

/-!
# Colimits, tensor products and internal homs do not depend on the topology

Fix a category `C` carrying two Grothendieck topologies `K ≤ J` and a sheaf of rings for the
finer topology `J`.  Its underlying presheaf is then a `K`-sheaf as well, and a `J`-sheaf of
modules is a `K`-sheaf of modules with the *same* underlying presheaf of modules; that reading
is `Stacks.SheafOfModules.comparisonPushforward`.  Descent, Lemma 0GNE asserts, for the five
big sites of a scheme `S`, that three constructions on quasi-coherent modules give the same
answer whichever of the topologies is used: colimits, tensor products, and internal homs out of
a finite locally free module.

The source proves all three from one observation, which it calls the key: the equivalence
`QCoh(𝒪_S) ⟶ QCoh((Sch/S)_τ, 𝒪)`, `𝓕 ↦ 𝓕^a`, of Descent, Proposition 03DX **is given by the
same formula for every `τ`**.  That observation is available in this library without 03DX: the
pullback-sections presheaf of modules of a quasi-coherent `𝒪_S`-module is a sheaf for all five
topologies at once
(`AlgebraicGeometry.BigFppfOver.isSheaf_sectionsPresheafOfModules_baseOverTopology`, Stacks
03DT), and `𝓕^a` is the `τ`-sheafification of that presheaf
(`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSections`, Stacks 070S (1)), so the
sheafification is doing nothing and `𝓕^a` has the same underlying presheaf of modules at every
`τ`.  That is `AlgebraicGeometry.BigFppfOver.restrictTopologyAssociatedModuleIso` below, and
parts (1), (2) and (3) are read off it and from the shape of the three constructions.

Two of the three constructions are built by sheafifying a topology-independent presheaf, so for
them the comparison is a statement about sheafification alone and is proved here for an
arbitrary pair `K ≤ J`:

* sheafification for `J` factors as sheafification for `K` followed by sheafification for `J`
  (`Stacks.SheafOfModules.sheafificationFactorization`), both being left adjoint to one and the
  same functor, namely "read a `J`-sheaf of modules as a presheaf of modules";
* hence the tensor product of two `J`-sheaves of modules is the `J`-sheafification of their
  tensor product taken for `K`, and the two agree exactly when the latter is already a
  `J`-sheaf.

The third needs no sheafification at all, which is the source's own reason for part (3): the
internal hom of Stacks 03EM is a construction on presheaves of modules, and only the *proof*
that its output is a sheaf uses the sheaf condition on the target.  So the internal hom for `K`
and the internal hom for `J` have the same underlying presheaf of modules on the nose.

## Main definitions

* `Stacks.SheafOfModules.commRingOfLe`: a sheaf of commutative rings for a finer topology, read
  for a coarser one.
* `AlgebraicGeometry.RingedSite.ofLE` and `AlgebraicGeometry.RingedSite.coarsenModules`: a
  ringed site read with a coarser topology, and the induced reading of its modules.
* `AlgebraicGeometry.BigFppfOver.restrictTopology`: a module on `(Sch/S)_fppf` read as a module
  on `(Sch/S)_τ`.
* `AlgebraicGeometry.BigFppfOver.sectionsSheafOfModules`: the pullback-sections presheaf of
  modules of a quasi-coherent module on `S`, as a sheaf on `(Sch/S)_τ`.

## Main results

* `Stacks.SheafOfModules.sheafificationFactorization`: sheafification of presheaves of modules
  for a finer topology factors through sheafification for a coarser one.
* `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSectionsSheaf`: **Stacks 03FH (1) on the
  big sites** — the sections-defined `𝓕^a` of Definition 03DU (3) is the pullback of `𝓕` under
  the morphism of ringed sites `id_{τ, Zar} : ((Sch/S)_τ, 𝒪) → (S_Zar, 𝒪)`, at each of the five
  `τ`, with no sheafification left: Stacks 070S (1) presents the pullback as the
  `τ`-sheafification of the sections presheaf and Stacks 03DT says that presheaf is a `τ`-sheaf
  already, so the counit of the sheafification adjunction removes it.
* `AlgebraicGeometry.BigFppfOver.restrictTopologyAssociatedModuleIso`: **the key to Stacks
  0GNE** — the same identification read at two topologies, so the `(Sch/S)_τ` associated
  module is the `(Sch/S)_fppf` one read for the coarser topology.
* `AlgebraicGeometry.BigFppfOver.restrictTopologyAssociatedModuleQcohIso`: **the key to
  Stacks 0GNE, as an isomorphism of functors** — the same comparison, natural in the module,
  which is what comparing two colimit *cocones* needs.
* `AlgebraicGeometry.BigFppfOver.isColimitMapCoconeBaseAssociatedModuleQcoh`: **Stacks 0GNE (1)
  for `Mod((Sch/S)_τ, 𝒪)`, every `τ`** — a colimit of quasi-coherent modules on `S` is carried
  by `𝓕 ↦ 𝓕^a` to a colimit in the modules of `(Sch/S)_τ`.
* `AlgebraicGeometry.BigFppfOver.isColimitMapCoconeRestrictTopologyAssociatedModuleQcoh`:
  **Stacks 0GNE (1), the agreement** — the fppf colimit *cocone* of such a diagram, read in
  `Mod((Sch/S)_τ, 𝒪)`, is a colimit cocone there, so the five colimits are one object with one
  cocone.  The diagram is the reduced one; the clause for an arbitrary diagram in
  `QCoh((Sch/S)_fppf, 𝒪)`, which is the source's own scope, is in
  `StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherentTopologiesTwo/BigSiteColimitAgreement.lean`
  and is unconditional — see the first coverage limit.
* `Stacks.SheafOfModules.tensorLeftFactorization`: **Stacks 0GNE (2), the comparison** — the
  tensor product for the finer topology is the sheafification of the one for the coarser
  topology.  `Stacks.SheafOfModules.tensorLeftAgreement` adds that the two agree as soon as the
  latter is a sheaf for the finer one; that hypothesis is untagged here and is discharged at
  the big sites in
  `StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherentTopologiesTwo/BigSiteTensorAgreement.lean`,
  which carries the 0GNE (2) attribute — there for an arbitrary pair of quasi-coherent
  `𝒪`-modules on `(Sch/S)_fppf`, the source's own scope, as well as for a pair of associated
  modules.
* `AlgebraicGeometry.RingedSite.coarsenModules_internalHomSheaf`: **Stacks 0GNE (3), the
  agreement clause** — the internal hom computed for `J` and the internal hom computed for `K`
  are the same sheaf of modules.

## Implementation notes

`AlgebraicGeometry.RingedSite.coarsenModules_internalHomSheaf` holds by `rfl`, and that is the
mathematics of part (3) rather than a tautology: the two sides are built by different
constructions in different categories — the left one sheafifies nothing but asserts the
`J`-sheaf condition and then weakens it, the right one asserts the `K`-sheaf condition of the
internal hom of two `K`-sheaves — and what makes them equal is that the internal hom presheaf
`internalHom` of Stacks 03EM does not mention a topology (only `internalHom_isSheaf` does) and
`Stacks.SheafOfModules.comparisonPushforward` does not change the underlying presheaf of
modules.  The sheaf conditions are propositions, so they do not obstruct the equality.  Stated
as an equality rather than an isomorphism for that reason: there is nothing to compare.

The colimit clause is stated as "the image of a colimit cocone is a colimit cocone" rather than
as an equality of colimit objects, because the diagram is taken in `QCoh(𝒪_S)`: that is the
shape the source's proof has, and it avoids asking the ambient categories for colimits.  Its
inputs are the `τ`-parametric colimit preservation of
`AlgebraicGeometry.BigFppfOver.baseAssociatedModule`, which is a left adjoint at every `τ`, and
the colimit preservation of the inclusion `QCoh(𝒪_S) ⥤ Mod(𝒪_S)`, which is Stacks 06VE (2),
(3) for the source category.

**Why the comparison is built twice.**  `restrictTopologyAssociatedModuleIso` reads the
comparison off the sections description: both sides are the pullback-sections sheaf, by
Stacks 070S (1) and Stacks 03DT.  That is the source's own argument and it is an isomorphism at
each module, but it is not known to be natural in the module, because
`AlgebraicGeometry.BigFppfOver.sectionsPresheafOfModules` is constructed one quasi-coherent module
at a time and `AlgebraicGeometry.BigFppfOver.isIso_baseSheafification_map_sectionsComparison`
inverts its comparison object by object.  Naturality is what a comparison of colimit *cocones*
needs, so `restrictTopologyAssociatedModuleQcohIso` builds the same comparison a second way, off
an adjunction instead: "sheafify for fppf" is left adjoint to "read an fppf sheaf for `τ`"
(`Stacks.SheafOfModules.comparisonAdjunction`), its unit is a morphism of functors with no
hypothesis at all, and the sections description is then used only to invert that unit at one
object at a time — which is enough, since a morphism of functors that is invertible at every
object is an isomorphism of functors.  The right adjoint is fully faithful, so the unit is
invertible exactly on the objects that are already fppf sheaves, and
`AlgebraicGeometry.BigFppfOver.sectionsSheafOfModules` at `τ = fppf` exhibits `𝓕^a` on
`(Sch/S)_τ` as one of them.

`Stacks.SheafOfModules.sheafificationFactorization` is `CategoryTheory.Adjunction.leftAdjointUniq`
applied to two adjunctions with the same right adjoint.  That the right adjoints agree is
definitional: composing `Stacks.SheafOfModules.comparisonPushforward` with the forgetful functor
to presheaves of modules for the coarser topology gives the forgetful functor for the finer one,
because neither changes the underlying presheaf, and the coefficient presheaves of rings are
equal by `rfl`.

The tensor product used is `Stacks.SheafOfModules.TensorColimits.tensorLeft`, the
sheafification of the objectwise tensor product of the underlying presheaves of modules
(Stacks 05NB).  Its value at a pair is by construction the sheafification of one presheaf of
modules that does not depend on the topology, so the tensor comparison is literally one
component of the sheafification comparison.

## Coverage limits

* **Part (1), the reduction to a diagram in `QCoh(𝒪_S)`.**  The source states part (1) for an
  arbitrary diagram in `QCoh((Sch/S)_fppf, 𝒪)` and reduces it to a diagram in `QCoh(𝒪_S)` by
  writing each term as `𝓖^a`.  That reduction is the essential-surjectivity half of Descent,
  Proposition 03DX at the big site, which the library now proves — at `τ = fppf` as
  `AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule'` and at every `τ` as
  `AlgebraicGeometry.BigFppfOver.baseQuasicoherentIsEssImageAssociatedModule`.  The declarations
  of the colimit tree still take it as the hypothesis
  `AlgebraicGeometry.BigFppfOver.QuasicoherentIsEssImageAssociatedModule`
  (`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/Descent/QuasicoherentColimitsOfSize.lean`
  `:142`), which that theorem now discharges.  The two halves of part (1) that only need that
  hypothesis — that `QCoh((Sch/S)_fppf, 𝒪)` has colimits and that they are the colimits of
  `Mod((Sch/S)_fppf, 𝒪)` — are already in the library, also untagged and conditional, as
  `AlgebraicGeometry.BigFppfOver.hasColimitsOfSize_quasicoherentOnSite` and
  `AlgebraicGeometry.BigFppfOver.preservesColimitsOfSize_quasicoherentOnSite_ι`
  (same file, `:206` and `:219`).  What was missing there, and is supplied here, is exactly the
  comparison with the coarser topologies, and that file's note points here.

  **Part (1) is now closed at the source's own scope, in a downstream module.**  What is proved
  *here* is the comparison for a diagram in `QCoh(𝒪_S)`; carrying it to an arbitrary diagram in
  `QCoh((Sch/S)_fppf, 𝒪)` is the reduction above, and that is done in
  `StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherentTopologiesTwo/BigSiteColimitAgreement.lean`:
  `AlgebraicGeometry.BigFppfOver.hasColimitsOfSize_quasicoherentOnSite_fppf` is the existence half,
  `…preservesColimitsOfSize_quasicoherentOnSite_ι_fppf` the agreement with `Mod((Sch/S)_fppf, 𝒪)`,
  and `…preservesColimitsOfSize_quasicoherentOnSite_ι_comp_restrictTopology` the agreement with
  `Mod((Sch/S)_τ, 𝒪)` at every `τ` — the three ambient categories of the source's clause — all
  three with no hypothesis.  The reduction is performed there on the functor rather than on the
  diagram, using the equivalence `AlgebraicGeometry.BigFppfOver.associatedModuleEquivalence_fppf`
  of Stacks 03DX (1).  The module is kept separate because this file is upstream of the one that
  proves the essential surjectivity.

  **What the proof of that statement rests on.**  The effectivity of fpqc descent is
  available: Stacks 023T is proved, unconditionally and tagged, in both its halves — `AlgebraicGeometry.QuasicoherentDescentData.isEffective_fpqcPrecoverage`
  (`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/FpqcEffectiveUnconditional.lean:63`),
  at an arbitrary index universe, and
  `AlgebraicGeometry.nonempty_fullyFaithful_canonicalDescentFunctor'`
  (`StacksFrontier/AlgebraicGeometry/Descent/FpqcHomSheafRefinement.lean:418`) — and it is already
  *consumed*: `AlgebraicGeometry.BigFppfOver.isEffective_fpqcPrecoverage_siteIndex`
  (`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/QcohGlueEffectivity.lean:109`) reads
  it at the index universe `u + 1` that the big fppf site forces, and
  `AlgebraicGeometry.BigFppfOver.isEffective_memberQcohDatum` applies it to the datum.

  The remaining input is **one spelling transport**.  The gluing step stands over a single
  hypothesis, `hagree` of
  `AlgebraicGeometry.BigFppfOver.essImage_associatedModuleQcoh_of_agree`
  (`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/ObjRestrictRestrFunBridgeEffectivity`
  `.lean:271`), the agreement of the local isomorphisms over the fibre products `X i ×_S X j`.
  The agreement is proved in the `objRestrict` spelling by
  `AlgebraicGeometry.BigFppfOver.restrictObjRestrictIso_effectiveGlueObjRestrictIso_eq`
  (`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/EffectiveGlueAgreement.lean:462`)
  while the consumer asks for the `homRestr` spelling, and the one identity that joins them is
  `AlgebraicGeometry.BigFppfOver.objRestrictFunctor_map_homRestrPreimage`
  (`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/EffectiveGlueAgreementRestrFun.lean`
  `:563`), proved componentwise rather than by `rfl`; with it and the faithfulness of the
  reindexing of Stacks 06WI, `hagree` is discharged in
  `AlgebraicGeometry.BigFppfOver.essImage_associatedModuleQcoh_of_fpqc` (`ibid.:611`), and the
  essential surjectivity follows once the covering family is refined to an fpqc one
  (`AlgebraicGeometry.BigFppfOver.exists_coversTop_fpqc_refinement`).  The route taken is
  recorded in the implementation notes of
  `StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/EffectiveGlueAgreementRestrFun.lean`.
* **Part (2) at the big sites: proved, in a downstream module.**  What is proved *here* for an
  arbitrary pair `K ≤ J` is that the finer tensor product is the sheafification of the coarser
  one (`Stacks.SheafOfModules.tensorLeftFactorization`), and that the two agree once the
  coarser one is already a sheaf for the finer topology
  (`Stacks.SheafOfModules.tensorLeftAgreement`, over its hypothesis `hunit`).  That hypothesis
  **is discharged at the big sites of a scheme**, and the clause with it, in
  `StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherentTopologiesTwo/BigSiteTensorAgreement.lean`:
  `AlgebraicGeometry.BigFppfOver.tensorAgreementAssociatedModule` is Stacks 0GNE (2)'s
  agreement and `…isQuasicoherentOnSite_tensorAssociatedModule` its quasi-coherence clause,
  both at every one of the five topologies.  The key input is Lemma **06VE (7)** —
  *not* Lemma 0GNB (7), which has six clauses and no seventh.  It is
  `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorSheafIso`
  (`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseAssociatedModuleTensor.lean:154`),
  at every `τ` and for arbitrary `𝒪_S`-modules, obtained from Stacks 03EL
  (`Stacks.SheafOfModules.pullbackTensorIso`) once the comparison is presented as a morphism of
  ringed topoi.  The downstream module is kept separate rather than folded in here because
  importing it into *this* file makes the unqualified `underlyingRingSheaf` of the `Tensor`
  section below ambiguous, against
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposPushforward.lean:686`.

  Those two declarations are proved for `𝓗^a` and `𝓘^a`, and the **arbitrary pair** of
  quasi-coherent modules on `(Sch/S)_fppf`, which is the source's own scope, is proved in the
  same module: `AlgebraicGeometry.BigFppfOver.tensorAgreementQuasicoherentOnSite` is the
  agreement and `…isQuasicoherentOnSite_tensorRestrictTopology` the quasi-coherence of the
  common value, both at every `τ` and with no hypothesis beyond quasi-coherence of the pair.
  The reduction is the essential surjectivity of `𝓕 ↦ 𝓕^a`,
  `AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule'`, which is also
  what closes part (1); what part (2) needs over and above part (1) is that the comparison be
  carried along `𝓕 ≅ 𝓗^a` and `𝓖 ≅ 𝓘^a` *at once*, i.e. functoriality of the tensor product in
  **both** arguments, where part (1)'s comparison has a single argument.  That is supplied by
  the tensor product being a functor on the product category, so `Functor.mapIso` of a
  `CategoryTheory.Iso.prod` does it in one step.  Nothing is missing from part (2).
* **Part (3), the parenthetical equivalence: proved, in a downstream module.**  The source's
  part (3) remarks that `𝓕` is finite locally free for the fppf topology if and only if it is so
  for the étale, if and only if for the Zariski topology.  That is Descent, Lemma 05VG for
  Modules on Sites, Definition 03DL (2), and it is **now proved, at all five topologies**, in
  `StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherentTopologiesTwo/`
  `BigSiteFiniteLocallyFreeAgreement.lean`:
  `AlgebraicGeometry.BigFppfOver.isFiniteLocallyFreeOnSite_restrictTopology_iff` is the
  parenthetical for an arbitrary quasi-coherent `𝒪`-module on `(Sch/S)_fppf`, and
  `…isFiniteLocallyFreeOnSite_baseAssociatedModule_iff` is 05VG's clause for 03DL (2) at the big
  site `(Sch/S)_τ`, as an equivalence, at every `τ`.  The rest of this note explains why
  a generic route is unavailable and which inputs the route taken uses.

  A generic route would need Modules on Sites, Lemma 03DO for 03DL (2) for a
  morphism of ringed **topoi**, whose one named gap is the factorization of Stacks 03CR, the
  ringed-**sites** form being all the library has
  (`Stacks.Sheaves.LocalizedPullback.isFiniteLocallyFreeOnSite_pullbackTopos`,
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LocalizedPullbackQuasicoherent.lean:411`).  That
  route is unavailable **for a universe reason rather than for 03CR**: that
  declaration is stated for `AlgebraicGeometry.RingedSite.{u, u, u}`, and the big site of a
  scheme is `AlgebraicGeometry.RingedSite.{u + 1, u, u}` — its objects live one universe above
  its morphisms — so it does not apply here however much of 03DO is proved.  And it is not the
  route the source takes: the source's proof of the parenthetical writes `𝓕 = 𝓗^a` and compares
  both sides with "`𝓗` finite locally free on `S`".

  **The pullback direction is proved at every `τ`**, by running the source's own argument at
  the big site instead of citing a generic statement, exactly as
  `StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseOpenCoverQuasicoherence.lean` runs
  the argument of Stacks 03DV:
  `BigFppfOver.isFiniteLocallyFreeOnSite_baseAssociatedModule_of_isFiniteLocallyFreeOnSite`
  (`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseFiniteLocallyFreeComparison.lean`)
  — if `𝓗` is finite locally free on the small Zariski site of `S` then `𝓗^a` is finite locally
  free on `(Sch/S)_τ`, for every one of the five `τ`.  It needs only the analogue of 03DV at an
  **open of `S`**, `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleOverObjIso`, which exists
  at every `τ`.

  **The converse** carries the mathematics: `𝓗^a` finite
  locally free on `(Sch/S)_τ` implies `𝓗` finite locally free on `S`.  All three of its
  mathematical inputs are in the library, unconditionally:

  * Stacks 05B2, fpqc descent of finite local freeness for a quasi-coherent module on a scheme,
    `AlgebraicGeometry.isFiniteLocallyFree_of_pullback_fpqcCover`
    (`StacksFrontier/AlgebraicGeometry/Modules/FiniteLocallyFreeDescent/Fpqc.lean:53`);
  * Stacks 05VG for Modules on Sites 03DE (2) — finite **free**ness — at the big `τ`-site and at
    every `τ`, `AlgebraicGeometry.BigFppfOver.isFiniteFree_iff_baseAssociatedModule`
    (`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/GlobalTypesComparison.lean:171`),
    an *iff*, so it reflects finite freeness as well as preserving it;
  * Stacks 03DX (1) at `τ = fppf`, which reduces an arbitrary `𝓕 ∈ QCoh((Sch/S)_fppf, 𝒪)` to a
    `𝓗^a`, `AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule'`.

  What joins them is plumbing, and that is the actual gap.  Three named pieces:

  1. the analogue of 03DV functorial in an **arbitrary object** of the big site, not merely at an
     open of `S` — `AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso`
     (`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/ObjectFunctoriality.lean:307`),
     which exists at `τ = fppf` and at no other `τ`;
  2. the stability of `SheafOfModules.IsFiniteFree` under restriction along a **morphism** of the
     site, needed because `AlgebraicGeometry.BigFppfOver.exists_coversTop_fpqc_refinement`
     (`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BigSiteDescentDatum.lean:186`)
     delivers a refinement whose members map *into* the members of the trivializing family; the
     tree has it for the iterated slice only, and privately, as
     `exists_isColimitCofan_overOver`
     (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LocalOnCover/FiniteLocallyFree.lean`);
  3. monotonicity of `SheafOfModules.IsFiniteLocallyFreeOnSite` along
     `Stacks.SheafOfModules.comparisonPushforward`, which is what carries a verdict at a coarser
     `τ` to one at fppf and would let piece 1 be needed at `τ = fppf` only.  Its content is the
     transfer of `SheafOfModules.IsFiniteFree` along `comparisonPullback` — a left adjoint, so
     `Stacks.Sheaves.GlobalTypeComparison.isColimitCofanMap` applies, the remaining step being
     that the counit of `Stacks.SheafOfModules.comparisonAdjunction` is invertible, its right
     adjoint being fully faithful.

  So the precise statement of the parenthetical is: for `𝓕` a quasi-coherent `𝒪`-module on
  `(Sch/S)_fppf`, `SheafOfModules.IsFiniteLocallyFreeOnSite 𝓕` is equivalent to
  `SheafOfModules.IsFiniteLocallyFreeOnSite ((restrictTopology B S hS τ).obj 𝓕)`.  It is proved
  in `BigSiteFiniteLocallyFreeAgreement.lean` at **every** `τ`, not only at étale and Zariski.
  No clause of part (3) stated *here* asserts it:
  `coarsenModules_internalHomSheaf` asserts the agreement for arbitrary modules, so part (3)'s
  agreement clause does not depend on the parenthetical at all, and the quasi-coherence of the
  common value is Stacks 0GNC, registered below on the declaration that proves it, whose
  finite-local-freeness hypothesis is the fppf one.

  **What the three pieces turned out to be.**  Piece 2 was already in the library, public and in
  the generality wanted: `Stacks.SheafOfModules.exists_isColimitCofan_over_of_le`
  (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/OverFiniteFree.lean`) is exactly the stability
  of finite freeness under restriction along an arrow `Z ⟶ Y` of the site — the private
  `exists_isColimitCofan_overOver_symm` named above is a different statement, about the iterated
  slice, and was never the one needed.  Piece 3 is real and is proved as
  `Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_comparisonPushforward`, but **not by the
  route suggested above**: the transfer along the left adjoint `comparisonPullback` proves a
  statement about a *sheafified* module, whereas what is wanted is about the module itself, and
  `Stacks.SheafOfModules.comparisonPushforward` being **fully faithful** gives it outright —
  `Stacks.Sheaves.GlobalTypeComparison.isColimitCofanOfMap` reflects the cofan with no colimit
  preservation, no adjunction and no counit.  Piece 1 was then needed at `τ = fppf` only, as
  anticipated, which is where it exists.  So the obstruction was plumbing, the third diagnosis
  of it was the correct one, and the estimate of five to eight further lemmas was accurate.

## References

* [Stacks Project, Tag 0GNE](https://stacks.math.columbia.edu/tag/0GNE)
* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
* [Stacks Project, Tag 0GNC](https://stacks.math.columbia.edu/tag/0GNC)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w m

namespace CategoryTheory.Adjunction

/-- **A reflective unit is invertible on the reflective subcategory.**  For an adjunction
`L ⊣ R` with `R` fully faithful, the unit is invertible at every object isomorphic to `R.obj Y`:
the counit is then invertible, the triangle identity makes the unit at `R.obj Y` inverse to
`R.map (counit.app Y)`, and naturality carries that across the isomorphism.

The full faithfulness is an explicit argument rather than an instance so that the statement
applies to a functor whose `Full` and `Faithful` instances are not in scope. -/
theorem isIso_unit_app_of_iso_rightObj {C : Type u} {D : Type v} [Category.{w} C]
    [Category.{m} D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (hff : R.FullyFaithful)
    {X : C} {Y : D} (e : X ≅ R.obj Y) : IsIso (adj.unit.app X) := by
  haveI := hff.full
  haveI := hff.faithful
  exact adj.isIso_unit_app_of_iso e

end CategoryTheory.Adjunction

namespace Stacks.SheafOfModules

section Factorization

variable {C : Type u} [Category.{v} C] {J K : GrothendieckTopology C} (h : K ≤ J)
  (R : Sheaf J RingCat.{w})
  [HasWeakSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasWeakSheafify K AddCommGrpCat.{m}] [K.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- **Sheafification for a finer topology factors through sheafification for a coarser one.**
Both functors are left adjoint to the same functor — read a `J`-sheaf of modules as a presheaf
of modules — so they are isomorphic. -/
noncomputable def sheafificationFactorization :
    PresheafOfModules.sheafification.{m} (𝟙 R.obj) ≅
      PresheafOfModules.sheafification.{m} (𝟙 (ringOfLe h R).obj) ⋙
        comparisonPullback.{u, v, w, m} h R :=
  Adjunction.leftAdjointUniq (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj))
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringOfLe h R).obj)).comp
      (comparisonAdjunction.{u, v, w, m} h R))

end Factorization

section Tensor

open TensorColimits

variable {C : Type u} [Category.{v} C] {J K : GrothendieckTopology C} (h : K ≤ J)

/-- A sheaf of commutative rings for the finer topology, read for the coarser one. -/
abbrev commRingOfLe (R : Sheaf J CommRingCat.{w}) : Sheaf K CommRingCat.{w} :=
  ⟨R.obj, R.property.of_le h⟩

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (R : Sheaf J CommRingCat.{w})
  [HasWeakSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasWeakSheafify K AddCommGrpCat.{m}] [K.WEqualsLocallyBijective AddCommGrpCat.{m}]
  (F G : _root_.SheafOfModules.{m} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) R))

/-- **Stacks 0GNE (2), the comparison.**  The tensor product of two sheaves of modules for the
finer topology is the sheafification, for the finer topology, of their tensor product taken for
the coarser one.  Both are sheafifications of the objectwise tensor product of the two
underlying presheaves of modules, which does not mention a topology, so this is one component
of `Stacks.SheafOfModules.sheafificationFactorization`. -/
@[stacks 0GNE "part (2), the tensor product for the finer topology is the sheafification of \
the one for the coarser topology, for an arbitrary pair of topologies on one category"]
noncomputable def tensorLeftFactorization :
    ((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (R)).obj F).obj G ≅
      (comparisonPullback.{u, v, w, m} h ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) R)).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (J := K) ((commRingOfLe h R))).obj
            ((comparisonPushforward.{u, v, w, m} h ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) R)).obj F)).obj
          ((comparisonPushforward.{u, v, w, m} h ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) R)).obj G)) :=
  (sheafificationFactorization h ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) R)).app _

/-- **Towards Stacks 0GNE (2), the agreement.**  The tensor product computed for the finer
topology, read for the coarser one, is the tensor product computed for the coarser topology, as
soon as the latter is already a sheaf for the finer topology — which is what invertibility of
the unit at it says.

`hunit` is a hypothesis the source does not have, and the clause string of the `stacks`
attribute below says so: what is proved here is the implication.  It is discharged at the big
sites of a scheme, by Stacks 06VE (7), in
`AlgebraicGeometry.BigFppfOver.isIso_comparisonUnit_tensorRestrictTopology`
(`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherentTopologiesTwo/BigSiteTensorAgreement.lean`),
and the 0GNE (2) attribute for the clause without that hypothesis sits there, on
`…tensorAgreementQuasicoherentOnSite`, which is this declaration with `hunit` supplied for an
arbitrary pair of quasi-coherent modules on `(Sch/S)_fppf` — note that the arbitrary pair is
reached by widening `hunit`, so the isomorphism it returns is still this canonical one.  The
half of part (2) that needs no hypothesis at all is
`Stacks.SheafOfModules.tensorLeftFactorization`, which carries the tag here. -/
@[stacks 0GNE "part (2), the two tensor products agree once the coarser one is a sheaf for \
the finer topology"]
noncomputable def tensorLeftAgreement
    (hunit : IsIso ((comparisonAdjunction.{u, v, w, m} h
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) R)).unit.app
      (((Stacks.SheafOfModules.Tensor.sheafTensor (J := K) ((commRingOfLe h R))).obj
          ((comparisonPushforward.{u, v, w, m} h ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) R)).obj F)).obj
        ((comparisonPushforward.{u, v, w, m} h ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) R)).obj G)))) :
    (comparisonPushforward.{u, v, w, m} h ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) R)).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (R)).obj F).obj G) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor (J := K) ((commRingOfLe h R))).obj
          ((comparisonPushforward.{u, v, w, m} h ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) R)).obj F)).obj
        ((comparisonPushforward.{u, v, w, m} h ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) R)).obj G) :=
  (comparisonPushforward.{u, v, w, m} h ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) R)).mapIso
      (tensorLeftFactorization h R F G) ≪≫
    (@asIso _ _ _ _ _ hunit).symm

end Tensor

end Stacks.SheafOfModules

namespace AlgebraicGeometry

namespace RingedSite

/-- A ringed site, read with a coarser topology: the same category and the same structure
presheaf, asserted to be a sheaf for less. -/
def ofLE (X : RingedSite.{u, v, w}) {J' : GrothendieckTopology X.C} (h : J' ≤ X.J) :
    RingedSite.{u, v, w} where
  C := X.C
  J := J'
  O := ⟨X.O.obj, X.O.property.of_le h⟩

/-- Reading a sheaf of modules on a ringed site as a sheaf of modules for a coarser topology. -/
noncomputable abbrev coarsenModules (X : RingedSite.{u, v, w})
    {J' : GrothendieckTopology X.C} (h : J' ≤ X.J) :
    SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤ SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf (X.ofLE h).O) :=
  Stacks.SheafOfModules.comparisonPushforward h (Stacks.SheafOfModules.Tensor.ringSheaf X.O)

/-- **Stacks 0GNE (3), the agreement clause.**  The internal hom of two sheaves of modules
computed on a ringed site, read for a coarser topology, *is* the internal hom of their readings
computed for the coarser topology.

This is the source's own argument for part (3): the internal hom of Stacks 03EM is a
construction on presheaves of modules, and the topology enters only in the proof that the
result is a sheaf, which needs the sheaf condition on the target alone.  So no comparison map
is involved — the two sheaves of modules have the same underlying presheaf of modules, and
their sheaf conditions are propositions. -/
@[stacks 0GNE "part (3), the internal homs computed for two topologies agree, for arbitrary \
sheaves of modules on a ringed site"]
theorem coarsenModules_internalHomSheaf (X : RingedSite.{u, v, w})
    {J' : GrothendieckTopology X.C} (h : J' ≤ X.J)
    (A B : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (coarsenModules X h).obj (internalHomSheaf X A B) =
      internalHomSheaf (X.ofLE h) ((coarsenModules X h).obj A)
        ((coarsenModules X h).obj B) := rfl

end RingedSite

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A module on `(Sch/S)_fppf`, read as a module on the coarser big site `(Sch/S)_τ`.  The
underlying presheaf of modules does not change, and neither does the coefficient presheaf of
rings: `AlgebraicGeometry.FibredSite.baseRingStructureSheaf_obj` is an equality by `rfl`. -/
noncomputable abbrev restrictTopology (τ : SiteKind) :
    SheafOfModules.{m} (structureSheaf B S hS) ⥤
      SheafOfModules.{m} (FibredSite.baseRingStructureSheaf B S hS τ) :=
  Stacks.SheafOfModules.comparisonPushforward
    (baseOverTopology_le_fppf B S hS τ) (structureSheaf B S hS)

/-- The pullback-sections presheaf of modules of Stacks 03DS, as a sheaf of modules on
`(Sch/S)_τ`.  Its sheaf condition for every one of the five topologies is Stacks 03DT, which is
`AlgebraicGeometry.BigFppfOver.isSheaf_sectionsPresheafOfModules_baseOverTopology`. -/
noncomputable def sectionsSheafOfModules (τ : SiteKind) (F : S.Modules) [F.IsQuasicoherent] :
    SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ) :=
  ⟨sectionsPresheafOfModules B S hS F,
    isSheaf_sectionsPresheafOfModules_baseOverTopology B S hS τ F⟩

/-- The pullback-sections sheaf on `(Sch/S)_τ` is the one on `(Sch/S)_fppf` read for the
coarser topology: one presheaf of modules, two sheaf conditions. -/
theorem restrictTopology_sectionsSheafOfModules (τ : SiteKind) (F : S.Modules)
    [F.IsQuasicoherent] :
    (restrictTopology B S hS τ).obj (sectionsSheafOfModules B S hS .fppf F) =
      sectionsSheafOfModules B S hS τ F := rfl

/-- **Stacks 03FH (1) on the big sites.**  The construction `𝓕 ↦ 𝓕^a` of Definition 03DU (3) —
the sheaf on `(Sch/S)_τ` whose value at `f : T → S` is `Γ(T, f^*𝓕)` — **is** the pullback of
`𝓕` under the morphism of ringed sites
`id_{τ, Zar} : ((Sch/S)_τ, 𝒪) → (S_Zar, 𝒪)`, at each of the five
`τ ∈ {Zariski, étale, smooth, syntomic, fppf}`.

**No sheafification is left in the statement.**  Two inputs compose.  Stacks 070S (1),
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSections`, presents the pullback as the
`τ`-sheafification of the pullback-sections presheaf of modules of Stacks 03DS; and Stacks 03DT
on the five big sites,
`AlgebraicGeometry.BigFppfOver.isSheaf_sectionsPresheafOfModules_baseOverTopology`, says that for
a quasi-coherent `𝓕` that presheaf is **already** a `τ`-sheaf — it is what
`AlgebraicGeometry.BigFppfOver.sectionsSheafOfModules` packages.  So the counit of
`CategoryTheory.PresheafOfModules.sheafificationAdjunction` is invertible there and removes the
sheafification, which is the step that turns 070S (1) into the remark's own identification with
`𝓕^a` itself.

**The right-hand side is `𝓕^a` as Definition 03DU (3) defines it**, by its sections: the
underlying presheaf of modules of `AlgebraicGeometry.BigFppfOver.sectionsSheafOfModules` is
`AlgebraicGeometry.BigFppfOver.sectionsPresheafOfModules`, the presheaf of Stacks 03DS, and at
`τ = fppf` the packaging is the tagged clause-(3) definition
`AlgebraicGeometry.overAssociatedModule` on the nose —
`AlgebraicGeometry.BigFppfOver.overAssociatedModule_fppf`, in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/OverAssociatedModuleIso.lean`, which is
`rfl`.

**What the other 03FH registrations carry.**  Clause (1) of the remark offers two morphisms.
This is the first of them, `id_{τ, Zar}`, on the big site, at all five `τ`; the second,
`id_{small, étale, Zar} : (S_étale, 𝒪) → (S_Zar, 𝒪)`, is
`AlgebraicGeometry.SmallEtale.associatedModuleIsoOfSections`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleSectionsIso.lean`), with the
small Zariski reading in
`AlgebraicGeometry.SmallZariski.associatedModuleIsoOfSections`.  The two together are the whole
of clause (1).  `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSections` is the same
comparison read before the sheafification is removed, where it is Stacks 070S (1).

**Quasi-coherence is not an added hypothesis.**  The construction whose two descriptions the
remark identifies is `𝓕 ↦ 𝓕^a` of Definition 03DU (3), which is made for a quasi-coherent
`𝒪_S`-module; the sheafified form above, which is 070S's own statement, needs nothing of `𝓕`.

The declaration is also what reads the comparison of
`AlgebraicGeometry.BigFppfOver.restrictTopologyAssociatedModuleIso` below off the sections
description, and so is **the key to Stacks 0GNE**: both of the modules compared there are this
one sheaf. -/
@[stacks 03FH "part (1) for the first of the two morphisms of ringed sites that clause offers, \
id_{τ, Zar} : ((Sch/S)_τ, 𝒪) → (S_Zar, 𝒪), on the big site (Sch/S)_τ at each of the five τ: \
the construction 𝓕 ↦ 𝓕^a of Definition 03DU (3), the sheaf of sections (f : T → S) ↦ \
Γ(T, f^*𝓕), is the pullback under that morphism"]
noncomputable def baseAssociatedModuleIsoSectionsSheaf (τ : SiteKind) (F : S.Modules)
    [F.IsQuasicoherent] :
    (baseAssociatedModule B S hS τ).obj F ≅ sectionsSheafOfModules B S hS τ F :=
  baseAssociatedModuleIsoSections B S hS τ F ≪≫
    (asIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (FibredSite.baseRingStructureSheaf B S hS τ).obj)).counit)).app
        (sectionsSheafOfModules B S hS τ F)

/-- **The key to Stacks 0GNE.**  The functor `𝓕 ↦ 𝓕^a` is given by the same formula for every
`τ ∈ {Zariski, étale, smooth, syntomic, fppf}`: the associated module of a quasi-coherent
`𝒪_S`-module on `(Sch/S)_τ` is the associated module on `(Sch/S)_fppf`, read for the coarser
topology.

Every clause of the source's lemma is deduced from this, which is why it carries the tag: the
source's proof of all three parts is "the equivalence of Proposition 03DX is given by the same
formula independent of the choice of the topology", applied to a colimit, to a tensor product
and to an internal hom. -/
@[stacks 0GNE "the key to the proof: the associated-module functor is given by one formula for \
all five topologies, so its values for the five topologies agree"]
noncomputable def restrictTopologyAssociatedModuleIso (τ : SiteKind) (F : S.Modules)
    [F.IsQuasicoherent] :
    (restrictTopology B S hS τ).obj ((associatedModule B S hS).obj F) ≅
      (baseAssociatedModule B S hS τ).obj F :=
  (restrictTopology B S hS τ).mapIso (baseAssociatedModuleIsoSectionsSheaf B S hS .fppf F) ≪≫
    (baseAssociatedModuleIsoSectionsSheaf B S hS τ F).symm

section Naturality

/-- The fppf sheafification of the `τ`-associated module is the fppf associated module.  Both
functors are left adjoint to one and the same functor: restriction along the inclusion of the
small Zariski site of `S` does not see the topology of the big site, so composing
`AlgebraicGeometry.BigFppfOver.restrictTopology` with the restriction of `(Sch/S)_τ` gives the
restriction of `(Sch/S)_fppf`. -/
noncomputable def comparisonPullbackBaseAssociatedModuleIso (τ : SiteKind) :
    baseAssociatedModule B S hS τ ⋙
        Stacks.SheafOfModules.comparisonPullback
          (baseOverTopology_le_fppf B S hS τ) (structureSheaf B S hS) ≅
      associatedModule B S hS :=
  Adjunction.leftAdjointUniq
    ((baseAssociatedModuleAdjunction B S hS τ).comp
      (Stacks.SheafOfModules.comparisonAdjunction
        (baseOverTopology_le_fppf B S hS τ) (structureSheaf B S hS)))
    (associatedModuleAdjunction B S hS)

/-- **The `τ`-associated module of a quasi-coherent module is already an fppf sheaf.**  Said
through the adjunction "sheafify for fppf" ⊣ "read an fppf sheaf for `τ`": its unit is
invertible at `𝓕^a` computed on `(Sch/S)_τ`.

The input is Stacks 070S (1) and Stacks 03DT: `𝓕^a` on `(Sch/S)_τ` is the pullback-sections
sheaf `AlgebraicGeometry.BigFppfOver.sectionsSheafOfModules`, which is the reading for `τ` of
the pullback-sections sheaf of `(Sch/S)_fppf` — so it lies in the image of that reading, where a
reflective unit is invertible. -/
theorem isIso_comparisonUnit_baseAssociatedModule (τ : SiteKind) (F : S.Modules)
    [F.IsQuasicoherent] :
    IsIso ((Stacks.SheafOfModules.comparisonAdjunction
      (baseOverTopology_le_fppf B S hS τ) (structureSheaf B S hS)).unit.app
        ((baseAssociatedModule B S hS τ).obj F)) :=
  (Stacks.SheafOfModules.comparisonAdjunction
      (baseOverTopology_le_fppf B S hS τ) (structureSheaf B S hS)).isIso_unit_app_of_iso_rightObj
    (Stacks.SheafOfModules.comparisonPushforwardFullyFaithful
      (baseOverTopology_le_fppf B S hS τ) (structureSheaf B S hS))
    (Y := sectionsSheafOfModules B S hS .fppf F)
    (baseAssociatedModuleIsoSectionsSheaf B S hS τ F)

/-- The comparison of `AlgebraicGeometry.BigFppfOver.restrictTopologyAssociatedModuleIso`, as a
morphism of functors on all `𝒪_S`-modules: the unit of "sheafify for fppf" ⊣ "read for `τ`" at
`𝓕^a` computed on `(Sch/S)_τ`, followed by the identification of its fppf sheafification with
`𝓕^a` computed on `(Sch/S)_fppf`.

This exists with no quasi-coherence hypothesis; what quasi-coherence buys is that it is
invertible, which is
`AlgebraicGeometry.BigFppfOver.isIso_comparisonUnit_baseAssociatedModule`. -/
noncomputable def restrictTopologyAssociatedModuleNatTrans (τ : SiteKind) :
    baseAssociatedModule B S hS τ ⟶ associatedModule B S hS ⋙ restrictTopology B S hS τ :=
  Functor.whiskerLeft (baseAssociatedModule B S hS τ)
      (Stacks.SheafOfModules.comparisonAdjunction
        (baseOverTopology_le_fppf B S hS τ) (structureSheaf B S hS)).unit ≫
    Functor.whiskerRight (comparisonPullbackBaseAssociatedModuleIso B S hS τ).hom
      (restrictTopology B S hS τ)

/-- At a quasi-coherent module,
`AlgebraicGeometry.BigFppfOver.restrictTopologyAssociatedModuleNatTrans` is invertible: it is
the composite of the unit, invertible by
`AlgebraicGeometry.BigFppfOver.isIso_comparisonUnit_baseAssociatedModule`, with the image of an
isomorphism of functors. -/
theorem isIso_restrictTopologyAssociatedModuleNatTrans_app (τ : SiteKind) (F : S.Modules)
    [F.IsQuasicoherent] :
    IsIso ((restrictTopologyAssociatedModuleNatTrans B S hS τ).app F) := by
  haveI := isIso_comparisonUnit_baseAssociatedModule B S hS τ F
  have happ : (restrictTopologyAssociatedModuleNatTrans B S hS τ).app F =
      (asIso ((Stacks.SheafOfModules.comparisonAdjunction
            (baseOverTopology_le_fppf B S hS τ) (structureSheaf B S hS)).unit.app
          ((baseAssociatedModule B S hS τ).obj F)) ≪≫
        (restrictTopology B S hS τ).mapIso
          ((comparisonPullbackBaseAssociatedModuleIso B S hS τ).app F)).hom := rfl
  rw [happ]
  exact Iso.isIso_hom _

/-- **The key to Stacks 0GNE, naturally in the module.**  On the quasi-coherent `𝒪_S`-modules,
the associated-module functor of `(Sch/S)_τ` *is* the associated-module functor of
`(Sch/S)_fppf` read for the coarser topology — as an isomorphism of **functors**, not only at
each object.

`AlgebraicGeometry.BigFppfOver.restrictTopologyAssociatedModuleIso` gives the objectwise
isomorphism, and an objectwise isomorphism does not compare two cocones.  The naturality is
supplied here by reading the comparison off an adjunction instead of off the sections
description: "sheafify for fppf" is left adjoint to "read an fppf sheaf for `τ`", its unit is a
morphism of functors with no hypothesis, and quasi-coherence enters only through the
invertibility of its components,
`AlgebraicGeometry.BigFppfOver.isIso_restrictTopologyAssociatedModuleNatTrans_app`.

No `stacks` attribute: this is the key to the source's proof rather than one of its clauses,
and the clause it unlocks,
`AlgebraicGeometry.BigFppfOver.isColimitMapCoconeRestrictTopologyAssociatedModuleQcoh`, is a step
of 0GNE (1); the tag is on the arbitrary-diagram forms in
`StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentTopologiesTwo.BigSiteColimitAgreement`. -/
noncomputable def restrictTopologyAssociatedModuleQcohIso (τ : SiteKind) :
    baseAssociatedModuleQcoh B S hS τ ≅
      associatedModuleQcoh B S hS ⋙ restrictTopology B S hS τ := by
  haveI : ∀ M : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory,
      IsIso ((Functor.whiskerLeft (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι
        (restrictTopologyAssociatedModuleNatTrans B S hS τ)).app M) := fun M => by
    haveI : M.obj.IsQuasicoherent := M.property
    exact isIso_restrictTopologyAssociatedModuleNatTrans_app B S hS τ M.obj
  haveI := NatIso.isIso_of_isIso_app (Functor.whiskerLeft
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι
    (restrictTopologyAssociatedModuleNatTrans B S hS τ))
  exact asIso (Functor.whiskerLeft (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι
    (restrictTopologyAssociatedModuleNatTrans B S hS τ))

end Naturality

section Colimits

variable (τ : SiteKind) (K : Type v) [Category.{w} K]

/-- The associated-module functor of `(Sch/S)_τ` preserves colimits of shape `K`, recorded at
the retyping `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleOfSheaf`.  Its proof is the
instance `AlgebraicGeometry.BigFppfOver.preservesColimitsOfSize_baseAssociatedModule`, which is
Stacks 03DC applied to the adjunction, transported across the two category instances by hand. -/
theorem preservesColimitsOfShape_baseAssociatedModuleOfSheaf :
    PreservesColimitsOfShape K (baseAssociatedModuleOfSheaf B S hS τ) := by
  have h : PreservesColimitsOfShape K (baseAssociatedModule B S hS τ) := inferInstance
  exact h

variable [∀ R : CommRingCat.{u}, HasColimitsOfShape K (ModuleCat.{u} R)]
  [HasColimitsOfShape K (SheafOfModules.{u} S.ringCatSheaf)]

/-- **Stacks 06VE (3) at `(Sch/S)_τ`, every `τ`.**  The functor `𝓕 ↦ 𝓕^a` out of the
quasi-coherent modules of `S` into the modules of `(Sch/S)_τ` commutes with colimits of shape
`K`: it is the inclusion of the quasi-coherent modules, which preserves them, followed by the
associated-module functor, which is a left adjoint.

No 06VE attribute is carried here; the tag for clause (3) sits on the fppf statement
`AlgebraicGeometry.BigFppfOver.preservesColimitsOfSize_associatedModuleQcoh`, whose clause
string records that scope, and widening it is a change to that declaration rather than to this
one. -/
theorem preservesColimitsOfShape_baseAssociatedModuleQcoh :
    PreservesColimitsOfShape K (baseAssociatedModuleQcoh B S hS τ) := by
  have := preservesColimitsOfShape_isQuasicoherent_ι S K
  have := preservesColimitsOfShape_baseAssociatedModuleOfSheaf B S hS τ K
  exact Limits.comp_preservesColimitsOfShape
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι (baseAssociatedModuleOfSheaf B S hS τ)

/-- **Stacks 0GNE (1), the comparison with the modules of `(Sch/S)_τ`, every `τ`.**  A colimit
of a diagram of quasi-coherent modules on `S` is carried by `𝓕 ↦ 𝓕^a` to a colimit in
`Mod((Sch/S)_τ, 𝒪)`.  Together with
`AlgebraicGeometry.BigFppfOver.restrictTopologyAssociatedModuleIso`, which identifies the
vertex at `τ` with the vertex at fppf read for the coarser topology, this says that the
colimits computed in the five module categories agree.

The source states the clause for a diagram in `QCoh((Sch/S)_fppf, 𝒪)`, and reduces it to a
diagram in `QCoh(𝒪_S)` by the essential surjectivity of `𝓕 ↦ 𝓕^a`; the diagram here is the
reduced one.  That reduction is now available, and the clause for an arbitrary diagram is
`AlgebraicGeometry.BigFppfOver.preservesColimitsOfSize_quasicoherentOnSite_ι_comp_restrictTopology`
(`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherentTopologiesTwo/BigSiteColimitAgreement.lean`).
-/
@[stacks 0GNE "part (1), the colimit of a diagram of associated modules computed in \
Mod((Sch/S)_τ, O), for every one of the five topologies"]
noncomputable def isColimitMapCoconeBaseAssociatedModuleQcoh
    {D : K ⥤ (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory}
    {c : Cocone D} (hc : IsColimit c) :
    IsColimit ((baseAssociatedModuleQcoh B S hS τ).mapCocone c) :=
  have := preservesColimitsOfShape_baseAssociatedModuleQcoh B S hS τ K
  isColimitOfPreserves _ hc

/-- **Stacks 0GNE (1), the agreement of the colimits computed for the five topologies.**  Take a
diagram of quasi-coherent `𝒪_S`-modules and a colimit cocone for it.  Its image under
`𝓕 ↦ 𝓕^a` is a colimit cocone in `Mod((Sch/S)_fppf, 𝒪)`, by Stacks 06VE (3); this says that
**that same cocone, read in `Mod((Sch/S)_τ, 𝒪)`, is a colimit cocone there too**, for every one
of the five topologies.  So the colimit taken on the big fppf site and the colimit taken on
`(Sch/S)_τ` are the same object with the same cocone, not merely isomorphic objects.

This is the clause that
`AlgebraicGeometry.BigFppfOver.isColimitMapCoconeBaseAssociatedModuleQcoh` leaves open:
there the two colimits are compared as the values of two functors, and
`AlgebraicGeometry.BigFppfOver.restrictTopologyAssociatedModuleIso` identifies them object by
object, which is not enough to identify the two *cocones*.  What supplies the missing
naturality is
`AlgebraicGeometry.BigFppfOver.restrictTopologyAssociatedModuleQcohIso`.

The source states the clause for a diagram in `QCoh((Sch/S)_fppf, 𝒪)`, and reduces it to a
diagram in `QCoh(𝒪_S)` by the essential surjectivity of `𝓕 ↦ 𝓕^a`; the diagram here is the
reduced one.  That reduction is now available, and the cocone statement for an arbitrary
diagram is
`AlgebraicGeometry.BigFppfOver.isColimitMapCoconeRestrictTopologyQuasicoherentOnSite`
(`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherentTopologiesTwo/BigSiteColimitAgreement.lean`),
whose diagram and colimit cocone are taken in `QCoh((Sch/S)_fppf, 𝒪)` rather than in
`QCoh(𝒪_S)`; it is proved from the same two inputs as this declaration —
`AlgebraicGeometry.BigFppfOver.preservesColimitsOfShape_baseAssociatedModuleQcoh` and
`…restrictTopologyAssociatedModuleQcohIso` — together with that reduction. -/
noncomputable def isColimitMapCoconeRestrictTopologyAssociatedModuleQcoh
    {D : K ⥤ (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory}
    {c : Cocone D} (hc : IsColimit c) :
    IsColimit ((restrictTopology B S hS τ).mapCocone
      ((associatedModuleQcoh B S hS).mapCocone c)) :=
  (IsColimit.mapCoconeEquiv (restrictTopologyAssociatedModuleQcohIso B S hS τ))
    (isColimitMapCoconeBaseAssociatedModuleQcoh B S hS τ K hc)

end Colimits

end BigFppfOver

end AlgebraicGeometry

/- **Stacks 0GNE (3), the quasi-coherence clause.**  The common value of the internal homs is
quasi-coherent on the finer site; that statement is Stacks 0GNC and is already proved, so the
clause is registered on the declaration that proves it rather than restated. -/
add_to_stacks 0GNE "part (3), quasi-coherence of the common value"
  AlgebraicGeometry.RingedSite.internalHomSheaf_isQuasicoherent

end
