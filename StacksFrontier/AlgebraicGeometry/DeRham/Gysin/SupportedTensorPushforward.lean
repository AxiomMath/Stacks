module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.DeterminantChangeOfEquations
public import
  StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.LocalCohomologyVanishingDegrees
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportCounitComparison
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedPullbackTopDegree
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreeComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ShiftedDegreeZero
public import
  StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsDerivedTensor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The multiplication of Tag 0G75 read as a map of complexes on `X`

[Stacks, Tag 0G75] is the canonical map

`K|_Z ⊗^L_{𝒪_X|_Z} R𝓗_Z(M) ⟶ R𝓗_Z(K ⊗^L_{𝒪_X} M)`

of `D(𝒪_X|_Z)`, where `i : Z ⟶ X` is the inclusion of a closed subset. Every consumer in this
library of the sheaf `ℋ^c_Z` — the Čech-model pairing
`Stacks.Perfect.CechPairing.supportPair`, the Gysin class map of [Stacks, Tag 0G7Q], the wedge
pairing of `StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinPairing.lean` — works with the
*direct image* `i_*ℋ^c_Z`, that is with
`Stacks.Perfect.SupportedFraction.supportCohomologySheaf`, whose underlying complex is
`i_* R𝓗_Z` and not `R𝓗_Z`. This file pushes the map of Tag 0G75 forward to that side:

`K ⊗^L_{𝒪_X} i_*R𝓗_Z(M) ⟶ i_*R𝓗_Z(K ⊗^L_{𝒪_X} M)`,

a map of `D(𝒪_X)` in which the closed subset occurs only through `i_*R𝓗_Z`.

The pushforward is not a formality: the source of the map of Tag 0G75 is a tensor product
formed on `Z`, so `i_*` of it is not a tensor product on `X` until the projection formula of
[Stacks, Tag 0B53] is used. That map is invertible here, by [Stacks, Tag 0B55] for the
inclusion of a closed subset, and the resulting identification
`i_*(K|_Z ⊗^L R𝓗_Z(M)) ≅ K ⊗^L i_*R𝓗_Z(M)` is `supportedTensorPushIso` below. Its four legs
are the first four of `Stacks.Cohomology.SupportedComplexes.supportedTensorMateMap`, which is
where this library already assembles them; only the last two legs of that composite — the
counit and a braiding — are dropped, and a braiding on `X` is put in their place.

## Main definitions

* `Stacks.Cohomology.SupportedComplexes.supportedTensorPushIso`: the identification
  `i_*(K|_Z ⊗^L R𝓗_Z(M)) ≅ K ⊗^L i_*R𝓗_Z(M)` given by the projection formula.
* `Stacks.Cohomology.SupportedComplexes.supportedTensorPushMap`: **the multiplication of
  [Stacks, Tag 0G75] read on `X`**, `K ⊗^L i_*R𝓗_Z(M) ⟶ i_*R𝓗_Z(K ⊗^L M)`.
* `Stacks.Cohomology.SupportedComplexes.supportedTensorPushSourceIso`: the source of that map
  in degree `c`, read off as an ordinary tensor product of sheaves `A ⊗_{𝒪_X} G`.
* `Stacks.Cohomology.SupportedComplexes.supportedTensorPushDegreeMap`: **the degree-`c`
  cohomology sheaf of the multiplication**, `A ⊗_{𝒪_X} G ⟶ H^c(i_*R𝓗_Z(A[0] ⊗^L M))`.
* `Stacks.Cohomology.SupportedComplexes.supportedTensorPushTruncModel`: the `τ^{≥c}` model of
  `i_*R𝓗_Z(M)` in the shape the previous definition consumes, built from the vanishing above
  degree `c` alone.
* `Stacks.Cohomology.SupportedComplexes.supportedTensorPushTopDegreeMap`: **the degree-`c`
  read-off with that model discharged**, `A ⊗_{𝒪_Y} ℋ^c_T(ℱ) ⟶ ℋ^c_T(A[0] ⊗^L ℱ)` for a
  quasi-coherent `ℱ` on a scheme and `T` locally cut out by `c` equations.
* `Stacks.Cohomology.SupportedComplexes.supportedTopDegreeTensorMap`: the same with its target
  an *ordinary* local cohomology sheaf, `A ⊗_{𝒪_Y} ℋ^c_T(ℱ) ⟶ ℋ^c_T(A ⊗_{𝒪_Y} ℱ)`.
* `Stacks.Cohomology.SupportedComplexes.supportedTopDegreeMulMap`: **that map with a
  multiplication of sheaves put on the end**, `A ⊗_{𝒪_Y} ℋ^c_T(ℱ) ⟶ ℋ^c_T(G)` for any
  `w : A ⊗_{𝒪_Y} ℱ ⟶ G`, stated at
  `Stacks.Perfect.SupportedFraction.supportCohomologySheaf` on both sides. At the wedge of the
  de Rham algebra this is the map of [Stacks, Tag 0G88]; see
  `StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinWedgeTopDegree.lean`.

## Main results

* `Stacks.Cohomology.SupportedComplexes.isLE_derivedSupportedPushforward`: the vanishing of the
  local cohomology sheaves above degree `c` passes to the direct image, because `i_*` is exact.
* `Stacks.Cohomology.SupportedComplexes.isLE_derivedSupportedPushforward_of_locallyCutOut`:
  **[Stacks, Tag 0G7N] in the form the read-off needs**, `i_*R𝓗_T(ℱ)` has cohomology only in
  degrees `≤ c`.
* `Stacks.Cohomology.SupportedComplexes.supportedTopDegreeSheaf_eq`: the sheaf the read-off is
  stated at is the library's `Stacks.Perfect.SupportedFraction.supportCohomologySheaf`, i.e.
  `i_*ℋ^c_T(ℱ)`.
* `Stacks.Cohomology.SupportedComplexes.supportedTopDegreeMulMap_eq`: the multiplication read
  off in degree `c` is `supportedTopDegreeTensorMap` followed by `ℋ^c_T(w)`, hence functorial
  in `w` by construction.
* `Stacks.Cohomology.SupportedComplexes.supportedTensorPushMap_comp_counit`: **the adjunction
  equation that pins the map down.** Followed by the canonical map
  `i_*R𝓗_Z(K ⊗^L M) ⟶ K ⊗^L M` of [Stacks, Tag 0G72] it becomes `K ⊗^L` of the canonical map
  `i_*R𝓗_Z(M) ⟶ M`, read through the braiding that puts the tensor factors in the order the
  projection formula produces. This is `supportedTensorMap_mate` with the projection formula
  divided out, and it says the map is the canonical one rather than some composite of
  comparisons.
* `Stacks.Cohomology.SupportedComplexes.eq_supportedTensorPushMap`: **that equation is a
  characterisation** — `supportedTensorPushMap` is the *only* morphism
  `K ⊗^L i_*R𝓗_Z(M) ⟶ i_*R𝓗_Z(K ⊗^L M)` with that counit. Its source is `i_*` of something,
  by the projection formula, and `i_*` on derived categories is fully faithful, so composition
  with the counit is injective there; the formal step is
  `Stacks.Cohomology.SupportedComplexes.eq_of_comp_counit`.
* `Stacks.Cohomology.SupportedComplexes.cechToDerivedSupport_comp_counit`: **the counit of the
  Čech model**, `𝓕^• ⟶ i_*R𝓗_T(ℱ) ⟶ ℱ[0]` is the augmentation of [Stacks, Tag 0G7L]. This is
  the other half of the same handle: a candidate map built in the Čech model has a computable
  counit, and the previous result says the counit is all that has to be computed.

## Implementation notes

**Placement.** `StacksFrontier/Topology/Sheaves/Cohomology/SupportedComplexes/SupportedSectionsDerivedTensor.lean` is where `supportedTensorMap` and its mate
equation live, and where these declarations naturally belong; they are stated in this separate
file instead.

**What this is for.** [Stacks, Tag 0G88] in the generality of
[Stacks, Tag 0G86] — where `Z` is only *locally* cut out by `c` equations — needs the
degree-`c` cohomology sheaf of this map, the source's

`i^{-1}Ω^p ⊗ ℋ^c_Z(Ω^c) ⟶ ℋ^c_Z(Ω^{p+c})`,

read off because `R𝓗_Z(Ω^j)` has no cohomology sheaves above degree `c`. That display is now
reached: `supportedTopDegreeMulMap` below takes the read-off to an arbitrary multiplication of
sheaves, and `Stacks.Gysin.gysinWedgeTopDegreeMap` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinWedgeTopDegree.lean` instantiates it at the
wedge of the de Rham algebra, landing literally on `ℋ^c_Z(Ω^{p+c})`. Reading it off by
`Stacks.TopDegreeComparison.topDegreeIso` needs three facts, and **all three are now
available**:

* right t-exactness of `K ⊗^L -` is
  `Stacks.SheafOfModules.DerivedTensorProduct.isLE_tensor`, and in *both* variables with
  additive bounds;
* the single-complex model of `τ^{≥c}` is
  `Stacks.TruncGESingleHomology.homologyMap_truncGEπ_truncGELTIso`;
* the degree-zero case `H^0(M[0] ⊗^L G[0]) ≅ M ⊗ G` is
  `Stacks.DerivedTensor.RingedSite.isIso_degreeZeroTensorMap`, **with no flatness and no
  K-flatness on either factor**, natural in both and compatible with
  `DerivedTensorProduct.toTensor` by construction, since the map it inverts is `H^0` of
  `toTensor`.

  This was the one that used to be missing, and it is worth recording why the obstruction
  reported here was not real. Every *complex-level* comparison in the library is conditional on
  K-flatness of one factor or the other —
  `DerivedTensorProduct.homologyTensorSingleIso` on the left, `RingedSite.homologyTensorFlatIso`
  on the right, both fields `comparisonLeft`/`comparisonRight` of `DerivedTensorProduct`, and
  every `IsIso toTensor` — and `Ω^p_{X/S}` satisfies neither. That is not removable: without
  flatness `M[0] ⊗^L G[0]` is genuinely not `(M ⊗ G)[0]`, its lower cohomology being the Tor
  sheaves. But in degree zero alone no hypothesis is needed, and the proof is a flat
  presentation of `M` plus right exactness of `⊗` plus [Stacks, Tag 0DIV] (2) — not the
  projective resolution of `Stacks.DerivedTensor.homologyZeroIsoTensorProduct`, which is what
  does not transfer to sheaves.

  The shift between that and the display above — the read-off wants `H^c` of `K ⊗^L M[-c]` for
  `K = Ω^p[0]`, which is `H^0(Ω^p[0] ⊗^L M[0])` through the shift compatibility
  `DerivedTensorProduct.commShift_right` — is
  `Stacks.DerivedTensor.RingedSite.degreeShiftedTensorIso` of
  `StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/ShiftedDegreeZero.lean`, with
  `degreeSingleTensorIso` its form at a right factor spelled as a single complex in degree `c`.

  **There is no spelling reconciliation to do.** An earlier note here recorded one as
  outstanding, between `Stacks.DerivedTensor.RingedSite.Modules` and the ringed-space side of
  this file. That was a misreading. The library has two parallel derived-tensor-product
  structures — `Stacks.SheafOfModules.DerivedTensorProduct`, indexed by a `RingedSite`, and
  `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`, indexed by the structure sheaf alone —
  but this file is already stated at the *second* one: `derivedTensorProductFunctor X.sheaf` and
  `canonicalDerivedTensorProduct X.sheaf` above are its functor and its datum, which is the same
  structure the degree-zero comparison is proved in. The two module spellings
  `SheafOfModules (structureSheafRing X)` and
  `Stacks.DerivedTensor.RingedSite.Modules X.sheaf` unify at one definitional step — both are
  `SheafOfModules.{u}` of `X.presheaf ⋙ forget₂ CommRingCat RingCat` — which is what the
  declarations above already rely on. Where the two *structures* do have to be crossed, the
  bridge also already exists:
  `Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct` of
  `StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/RightTExactness.lean` copies every
  field across, their K-flatness hypotheses being the same abbreviation.

  The degree-`c` read-off assembled from these is `supportedTensorPushDegreeMap` below.

**The `τ^{≥c}` model is no longer an input.** `supportedTensorPushDegreeMap` takes the
identification `τ^{≥c} i_*R𝓗_Z(M) ≅ G[0]⟦-c⟧` as an explicit argument `e`, which is
`topDegreeIso`'s own design. `supportedTensorPushTopDegreeMap` below discharges it, so the
degree-`c` read-off is unconditional. The two steps are:

* **the vanishing crosses `i_*` for free.** `i_*` along the inclusion of a closed subset is
  exact ([Stacks, Tag 08KS] both ways, `pushforward_preservesFiniteLimits` and
  `pushforward_preservesFiniteColimits`), so `H^i(i_*N) ≅ i_*H^i(N)` by
  `exactFunctorDerivedHomologyIso` and an additive functor kills a zero object. That is
  `isLE_derivedSupportedPushforward`, and it is what carries
  `Stacks.Perfect.LocalCohomologyDegrees.isZero_homology_derivedSupportedSections_of_locallyCutOut`
  — [Stacks, Tag 0G7N], stated for `R𝓗_T` **on `T`** — over to `i_*R𝓗_T` on `X`.
* **the generality is not an obstruction, because it runs the easy way.** Tag 0G7N is stated for
  a `Scheme` and a quasi-coherent module, while `supportedTensorPushMap` is stated for a
  `RingedSpace` and an arbitrary complex. A note on an earlier round recorded this as a gap to
  be bridged; it is not one. The consumer is the *more* general of the two, so the tag is used
  by **instantiating** the consumer at `Y.toRingedSpace` for a scheme `Y` and at
  `M = ℱ[0]` — `isLE_derivedSupportedPushforward_of_locallyCutOut` — and the only effect is
  that the unconditional read-off carries the tag's hypotheses, which are the hypotheses
  Tag 0G86 imposes anyway. Nothing has to be re-proved at `RingedSpace` generality, and no
  hypothesis is added that Tag 0G88 does not grant. What would *not* work is the opposite
  direction: there is no unconditional `IsLE` for an arbitrary complex on an arbitrary ringed
  space, and `isLE_derivedSupportedPushforward` therefore keeps the vanishing as a hypothesis.

Then `Stacks.AlgebraicGeometry.TopDegreeBaseChange.truncGEIsoSingleHomology` turns `IsLE c` into
`τ^{≥c} ≅ H^c(-)[c]` and `Stacks.DerivedTensor.RingedSite.singleShiftIso` rewrites `[c]` as
`[0]⟦-c⟧`, which is the spelling `supportedTensorPushSourceIso` wants: that composite is
`supportedTensorPushTruncModel`. The sheaf `G` produced is `H^c(i_*R𝓗_T(ℱ[0]))`, which
`supportedTopDegreeSheaf_eq` records as being, on the nose, this library's
`Stacks.Perfect.SupportedFraction.supportCohomologySheaf`.

**An alternative route to the same map.**
`Stacks.SheafOfModules.derivedCohomologyTensorProduct` gives, unconditionally and for arbitrary
`K, L ∈ D(O_X)` on a ringed space, a cup-product *map*
`H^i(K) ⊗ H^j(L) ⟶ H^{i+j}(K ⊗^L L)` with a cocycle characterisation
(`homologyπ_derivedCohomologyTensorProduct`), built on the same canonical datum as the rest of
this chain. At `(i, j) = (0, c)` and `K = M[0]` that is exactly the map wanted. Since the tag
needs a *morphism* and not an isomorphism, this makes the pairing constructible with no
K-flatness, and `topDegreeIso`, the `τ^{≥c}` model and the 0G7N vanishing are then not needed
for the definition at all. The cost is a spelling reconciliation between
`StructureSheafModules Rc` and `SheafOfModules (structureSheafRing X.toRingedSpace)`. It is kept
on record as a second construction of the pairing, not as a way round a missing fact: the route
taken above is complete.

**What remains is the step the source itself omits.** Its proof reduces Tag 0G88
to the commutativity of a square of sheaves whose right-hand column is the read-off map above,
and then says only that the maps `γ^j_{f₁,…,f_c}` "were defined precisely so this holds": the
verification is left out. In this library that step is the identification, over an open on
which `f₁, …, f_c` cut out `Z`, of the read-off map with
`Stacks.Perfect.CechPairing.supportPair` — the Čech-model pairing, in which the already-proved
global-equations case of Tag 0G88 lives. No such comparison exists here, and nothing in this
file supplies it; what this file supplies is the map whose cohomology sheaf one side of that
comparison is.

**The route to that step, and what is still missing on it.** An earlier note here recorded the
obstruction as the failure of `supportedFractionSource` to be epi on sections — it hits only the
classes of `s/(f₁⋯f_c)`, whereas `i_*ℋ^c_T(N)` over an open `V` is the full cokernel of
`lastDif`, so `supportPair_supportedFractionSource` alone does not pin the pairing down. That
observation is correct but it is **not** where the comparison is blocked, because the comparison
does not have to be made in degree `c` at all. `eq_supportedTensorPushMap` above pins the
multiplication down at the level of complexes, where the only thing to check about a candidate
is its composite with the counit, and `cechToDerivedSupport_comp_counit` computes that composite
for a candidate built in the Čech model. Neither mentions `supportedFractionSource`.

What the comparison still has to construct, with a global family `f₁, …, f_c` cutting out `T`,
is the following, and **every fact it rests on is already in the library**:

* **a chain-level Čech tensor pairing** `A[0] ⊗ 𝓝^• ⟶ 𝓟^•`. **This is built**, as
  `Stacks.Perfect.CechPairing.cechTensorTot` of
  `StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinCechTensorPairing.lean`, out of
  `Stacks.Perfect.CechPairing.termPair` and its commutation with the differentials
  (`Stacks.Perfect.CechPairing.termPair_dif`, read as an equation of morphisms out of the tensor
  product sheaf in `Stacks.Perfect.CechPairing.cechTensorTerm_comp_dif`). The passage from that
  degreewise family to a morphism out of the total tensor complex is
  `TotalTensorComplex.SingleTensor.singleTensorIso`, which says that tensoring with a complex
  concentrated in degree zero *is* tensoring degreewise, so no
  `HomologicalComplex.mapBifunctor` sign bookkeeping had to be redone; the two indexings are
  crossed by `Stacks.DerivedIndexing.mapExtendIso`. In degree zero the pairing is `μ` itself
  (`Stacks.Perfect.CechPairing.termPair_zero`), which is the augmentation compatibility the
  counit computation needs
  (`Stacks.Perfect.CechPairing.cechTensorCplx_comp_augmentationComplex`).

  **The identification of that model with `tensorSingleToSingle` is now available.** The counit
  computation meets `DerivedTensorProduct.toTensor` followed by `Q` of
  `TotalTensorComplex.SingleTensor.singleTensorIso`, whereas `supportedTopDegreeTensorMap` above
  is stated with `Stacks.DerivedTensor.RingedSite.tensorSingleToSingle`, which is `toTensor`
  followed by `Q` of `CochainComplex.KFlatBifunctor.totalSingleIso`. The two identifications of
  `Tot(A[0] ⊗ ℱ[0])` with `(A ⊗ ℱ)[0]` are the same map, by
  `Stacks.DerivedTensor.RingedSite.totSingleIsoSingle_hom_eq_singleTensor`, so
  `Stacks.DerivedTensor.RingedSite.tensorSingleToSingle_eq_singleTensor` rewrites either into
  the other. Its degree-zero input is
  `CochainComplex.KFlatBifunctor.ι_totalSingleIso_hom_f_zero`, the component of `totalSingleIso`
  on the `(0, 0)`-summand of the total complex; both live in
  `StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/ShiftedDegreeZero.lean` and belong
  upstream next to `totalSingleIso`.

  What is *not* yet built on this leg is the `ℤ`-indexed form of
  `cechTensorCplx_comp_augmentationComplex`: the counit computation needs it against
  `Stacks.Perfect.ExtendedAlternatingCech.Augmentation.augmentation`, which is `Q` of
  `HomologicalComplex.extendMap (augmentationComplex f ℱ)` followed by
  `HomologicalComplex.extendSingleIso`, while the compatibility is proved at the `ℕ`-indexed
  `augmentationComplex`. Crossing the two needs functoriality of `HomologicalComplex.extendMap`
  and `Stacks.DerivedIndexing.mapExtendIso` on the `A ⊗ -` side, which are the ingredients
  `Stacks.Perfect.CechPairing.cechTensorExtend_f` already uses.
* **the Čech model as a derived model**, which is
  `Stacks.Perfect.SupportedFraction.isIso_cechToSupport`: the comparison of [Stacks, Tag 0G7L]
  is invertible when `T` is the common zero locus, so the multiplication can be transported to
  the Čech complex before anything is read off.
* **the degree-`c` read-off on cocycle classes.** `supportedTensorPushSourceIso` is
  `Stacks.TopDegreeComparison.topDegreeIso` followed by `degreeShiftedTensorIso`, and the first
  is `H^c` of the truncation projection, which is not a chain-level map. It does not have to be:
  `Stacks.TruncGESingleHomology.eq_truncGEπ_comp_of_homologyMap_eq_id` says the composite
  `K ⟶ τ^{≥c}K ≅ H^c(K)[-c]` is the *only* morphism inducing the identity on `H^c`, and
  `…homologyMap_truncGEπ_truncGELTIso` says it induces the identity. For the Čech complex the
  chain-level projection onto `cokernel (lastDif f ℱ)` in degree `c` induces the identity on
  `H^c` by `Stacks.Perfect.SupportedFraction.cokernelLastDifIsoHomology`, so that projection
  *is* the truncation map, and the read-off becomes chain-level. The degree-zero end is
  `Stacks.DerivedTensor.RingedSite.homologyMap_tensorSingleToSingle`, which identifies
  `H^0(toTensor)` with `degreeZeroTensorMap`.
* **the braiding leg.** The counit equation above is stated with the commutativity constraints
  the projection formula forces; a candidate written with the second tensor variable mapped has
  to be moved across them. That is
  `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingIso_hom_naturality` at
  `(f, g) = (counit, 𝟙)`, which turns `braid⁻¹ ≫ (tensor.map g).app K ≫ braid` into
  `(tensor.obj K).map g`.
* **`supportPair` naturality in the pairing**, to reduce an arbitrary `w` to the canonical
  bilinear map into `A ⊗ ℱ`; and right exactness of `A ⊗ -`, to turn
  `Stacks.Perfect.CechPairing.cokPair_cokernelπ` into a statement about all of
  `A ⊗ i_*ℋ^c_T(ℱ)` rather than about fraction classes.

**Where the candidate is compared, and why the derived tensor target is not an obstruction.** A
candidate built in the Čech model lands in `i_*R𝓗_T(𝓟[0])` for an honest sheaf `𝓟`, not in
`i_*R𝓗_T(K ⊗^L M)`, so `eq_supportedTensorPushMap` does not apply to it on the nose. It does not
have to: that result is `eq_of_comp_counit` instantiated at `N = K ⊗^L M`, and
`eq_of_comp_counit` is stated for an arbitrary `N` with the *same* isomorphism
`e = supportedTensorPushIso` out of the source. Taking `N = 𝓟[0]` therefore compares the
candidate with `supportedTensorPushMap` followed by `i_*R𝓗_T` of
`tensorSingleToSingle` and of `𝓟`'s multiplication — which is exactly
`supportedTopDegreeMulMap`'s chain-level predecessor — and again only the composites with the
counit at `𝓟[0]` have to agree. On the `supportedTensorPushMap` side that composite is
`supportedTensorPushMap_comp_counit` moved across the counit's naturality; on the Čech side it
is the augmentation computation above.

Going on from the global family to a chart of [Stacks, Tag 0G86] then needs, in addition,
restriction-compatibility of the degree-`c` read-off along an open immersion and a "sheaf
morphisms agreeing on a cover are equal" step. Both of those have their pattern in the library
already: the excision machinery for the target is
`Stacks.Gysin.supportCohomologyRestrictIso` with its transitivity
`Stacks.Gysin.supportCohomologyRestrictCompIso_hom` and its chart leg
`Stacks.Gysin.supportCohomologyRestrictIso_hom_homOfLE`, and the gluing-with-uniqueness is
`Stacks.Gysin.existsUnique_gysinHom_of_conormalRank`, which is how `γ^p` itself is glued. What
is not located is the restriction-compatibility of the read-off itself.

## References

* [Stacks Project, Tag 0G75](https://stacks.math.columbia.edu/tag/0G75)
* [Stacks Project, Tag 0G72](https://stacks.math.columbia.edu/tag/0G72)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 0B55](https://stacks.math.columbia.edu/tag/0B55)
* [Stacks Project, Tag 0A3B](https://stacks.math.columbia.edu/tag/0A3B)
* [Stacks Project, Tag 0G7N](https://stacks.math.columbia.edu/tag/0G7N)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.SheafOfModules.SupportedSections
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedProjectionFormula
open Stacks.Perfect.SupportedQuasicoherent (derivedSupportedPushforward)

universe v u

-- As in `Stacks.Perfect.SupportedFraction`: the standard model of the derived category is given
-- a priority that beats the locally small model arriving as a global instance through the
-- imports, because `supportedTensorMap` and `supportCohomologySheaf` are both elaborated at the
-- standard model. Without the priority the two spellings differ in the `Hom` universe.
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.AssociatedSheaf.hasModuleSheafify
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective

namespace Stacks.Cohomology.SupportedComplexes

/-! ### A reassociation used twice -/

/-- Cancelling an isomorphism inserted at the end of a four-fold composite. Stated at a
variable category, because that is the only shape in which a chase of this kind is affordable
here: `rw [Category.assoc]` on the composites below does not typecheck. -/
theorem comp_inv_comp_cancel {C : Type u} [Category.{v} C] {X₀ X₁ X₂ X₃ X₄ Y W₀ W₁ : C}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄) (h : X₄ ⟶ Y) (k : Y ⟶ X₄)
    (e : X₄ ⟶ W₀) (g : W₀ ⟶ W₁) (hk : h ≫ k = CategoryStruct.id X₄) :
    (a ≫ b ≫ c ≫ d ≫ h) ≫ k ≫ e ≫ g = a ≫ b ≫ c ≫ d ≫ e ≫ g := by
  simp only [Category.assoc, ← Category.assoc h k, hk, Category.id_comp]

/-- Reassociating a triple composite and rewriting the first two factors. Stated at a variable
category for the same reason as `comp_inv_comp_cancel`: `rw [Category.assoc]` on the composites
of the derived category below does not typecheck. -/
theorem comp_comp_of_comp {C : Type u} [Category.{v} C] {X₀ X₁ X₂ X₃ : C} (a : X₀ ⟶ X₁)
    (b : X₁ ⟶ X₂) (c : X₀ ⟶ X₂) (d : X₂ ⟶ X₃) (k : X₀ ⟶ X₃) (hab : a ≫ b = c)
    (hcd : c ≫ d = k) : a ≫ b ≫ d = k := by
  rw [← Category.assoc, hab, hcd]

/-! ### The projection formula as an identification of the two tensor products -/

variable (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z)
variable (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))

/-- **The direct image of the tensor product on `Z` is a tensor product on `X`.** The
identification `i_*(K|_Z ⊗^L R𝓗_Z(M)) ≅ K ⊗^L i_*R𝓗_Z(M)` of the projection formula of
[Stacks, Tag 0B53], invertible by [Stacks, Tag 0B55].

The four legs are the first four of `supportedTensorMateMap`: the commutativity constraint of
[Stacks, Tag 0FPT] on `Z`, which puts the restricted factor second as the projection formula
wants it; the comparison of the two models of derived pushforward; the inverse of the
projection-formula map; and the comparison back. The fifth leg is the commutativity constraint
on `X`, restoring the order `K ⊗^L i_*R𝓗_Z(M)`. -/
def supportedTensorPushIso :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.obj
        (((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).obj
            ((derivedPullback (closedSubsetInclusion X Z)).obj K)).obj
          ((derivedSupportedSectionsOnClosed X Z hZ).obj M)) ≅
      ((derivedTensorProductFunctor X.sheaf).obj K).obj
        ((derivedSupportedPushforward X Z hZ).obj M) :=
  letI := pushforward_preservesFiniteLimits X Z
  letI := pushforward_preservesFiniteColimits X Z hZ
  (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.mapIso
      ((canonicalDerivedTensorProduct (closedSubsetRingedSpace X Z).sheaf).braidingIso
        (AlgebraicGeometry.RingedSpace.ringedSite (closedSubsetRingedSpace X Z))
        ((derivedPullback (closedSubsetInclusion X Z)).obj K)
        ((derivedSupportedSectionsOnClosed X Z hZ).obj M)) ≪≫
    (closedPushforwardComparison X Z).app _ ≪≫
    (@asIso _ _ _ _ _
      (isIso_projectionFormulaMap_closedSubsetInclusion_of_isClosed X Z hZ _ K)).symm ≪≫
    ((derivedTensorProductFunctor X.sheaf).mapIso
      ((closedPushforwardComparison X Z).symm.app
        ((derivedSupportedSectionsOnClosed X Z hZ).obj M))).app K ≪≫
    (canonicalDerivedTensorProduct X.sheaf).braidingIso
      (AlgebraicGeometry.RingedSpace.ringedSite X)
      ((derivedSupportedPushforward X Z hZ).obj M) K

/-! ### The multiplication of Tag 0G75 on `X` -/

/-- **The multiplication of [Stacks, Tag 0G75] read on `X`**, as a map

`K ⊗^L_{𝒪_X} i_*R𝓗_Z(M) ⟶ i_*R𝓗_Z(K ⊗^L_{𝒪_X} M)`

of `D(𝒪_X)`: the direct image of the map of Tag 0G75, with its source identified with a tensor
product on `X` by `supportedTensorPushIso`.

This is the side of the closed subset on which this library's local cohomology *sheaves* live:
`Stacks.Perfect.SupportedFraction.supportCohomologySheaf hZ G p` is the degree-`p` cohomology
sheaf of `i_*R𝓗_Z(G)`, which is the target of this map read at `K ⊗^L M = G`. -/
def supportedTensorPushMap :
    ((derivedTensorProductFunctor X.sheaf).obj K).obj
        ((derivedSupportedPushforward X Z hZ).obj M) ⟶
      (derivedSupportedPushforward X Z hZ).obj
        (((derivedTensorProductFunctor X.sheaf).obj K).obj M) :=
  letI := pushforward_preservesFiniteLimits X Z
  letI := pushforward_preservesFiniteColimits X Z hZ
  (supportedTensorPushIso X Z hZ K M).inv ≫
    (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.map
      (supportedTensorMap X Z hZ K M)

/-- **The adjunction equation that pins down the multiplication of [Stacks, Tag 0G75] on `X`.**
Followed by the canonical map `i_*R𝓗_Z(K ⊗^L M) ⟶ K ⊗^L M` of [Stacks, Tag 0G72] — the counit
of the adjunction of [Stacks, Tag 0A3B] — the map `supportedTensorPushMap` becomes `K ⊗^L` of
the canonical map `i_*R𝓗_Z(M) ⟶ M`, read through the commutativity constraints that put the
tensor factors in the order the projection formula produces.

This is `supportedTensorMap_mate` with the projection formula divided out. It is what says the
map is canonical: the composite of comparisons in `supportedTensorPushIso` cancels against the
one inside `supportedTensorMateMap`, leaving only the counit. -/
theorem supportedTensorPushMap_comp_counit :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    supportedTensorPushMap X Z hZ K M ≫
        (derivedPushforwardAdjunction X Z hZ).counit.app
          (((derivedTensorProductFunctor X.sheaf).obj K).obj M) =
      ((canonicalDerivedTensorProduct X.sheaf).braidingIso
          (AlgebraicGeometry.RingedSpace.ringedSite X)
          ((derivedSupportedPushforward X Z hZ).obj M) K).inv ≫
        ((derivedTensorProductFunctor X.sheaf).map
          ((derivedPushforwardAdjunction X Z hZ).counit.app M)).app K ≫
        ((canonicalDerivedTensorProduct X.sheaf).braidingIso
          (AlgebraicGeometry.RingedSpace.ringedSite X) M K).hom := by
  let := pushforward_preservesFiniteLimits X Z
  let := pushforward_preservesFiniteColimits X Z hZ
  have hmate := supportedTensorMap_mate X Z hZ K M
  refine (Category.assoc (supportedTensorPushIso X Z hZ K M).inv _ _).trans ?_
  refine Eq.trans
    (congrArg (fun φ => (supportedTensorPushIso X Z hZ K M).inv ≫ φ) hmate) ?_
  refine (Iso.inv_comp_eq (supportedTensorPushIso X Z hZ K M)).mpr ?_
  exact (comp_inv_comp_cancel _ _ _ _ _ _ _ _
    (Iso.hom_inv_id ((canonicalDerivedTensorProduct X.sheaf).braidingIso
      (AlgebraicGeometry.RingedSpace.ringedSite X)
      ((derivedSupportedPushforward X Z hZ).obj M) K))).symm

/-! ### The counit equation pins the multiplication down -/

universe v₁ u₁ v₂ u₂

/-- **A morphism into `L(R N)` is determined by its composite with the counit**, for an
adjunction `L ⊣ R` whose left adjoint is fully faithful, out of any object `P` isomorphic to one
in the image of `L`.

For `P = L W` this is the composite bijection `Hom(L W, L R N) ≅ Hom(W, R N) ≅ Hom(L W, N)`:
full faithfulness makes the first a bijection, and the second is the adjunction bijection, whose
inverse is composition with the counit. A general `P` is handled by transporting along the
isomorphism, which is epi.

Stated at variable categories, because that is the only shape in which a chase of this kind is
affordable at the derived category below. -/
theorem eq_of_comp_counit {A : Type u₁} [Category.{v₁} A] {C : Type u₂} [Category.{v₂} C]
    {L : A ⥤ C} {R : C ⥤ A} (adj : L ⊣ R) [L.Full] [L.Faithful] {W : A} {P N : C}
    (e : L.obj W ≅ P) (u v : P ⟶ L.obj (R.obj N))
    (h : u ≫ adj.counit.app N = v ≫ adj.counit.app N) : u = v := by
  have hmap (w : P ⟶ L.obj (R.obj N)) : L.map (L.preimage (e.hom ≫ w)) = e.hom ≫ w :=
    L.map_preimage _
  have h0 : L.preimage (e.hom ≫ u) = L.preimage (e.hom ≫ v) := by
    refine (adj.homEquiv W N).symm.injective ?_
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, hmap, hmap, Category.assoc,
      Category.assoc, h]
  refine (Iso.cancel_iso_hom_left e u v).mp ?_
  rw [← hmap u, ← hmap v, h0]

/-- **The multiplication of [Stacks, Tag 0G75] on `X` is the only morphism with its counit.**
Any morphism

`K ⊗^L_{𝒪_X} i_*R𝓗_Z(M) ⟶ i_*R𝓗_Z(K ⊗^L_{𝒪_X} M)`

whose composite with the counit of [Stacks, Tag 0A3B] is `K ⊗^L` of the counit at `M`, read
through the commutativity constraints, is `supportedTensorPushMap`.

This is the converse of `supportedTensorPushMap_comp_counit`, and it is what makes that equation
a *characterisation* rather than one identity among many. The source is of the form `i_*(-)` up
to the projection-formula isomorphism `supportedTensorPushIso`, and `i_*` on derived categories
is fully faithful — the unit of [Stacks, Tag 0A3B] is invertible,
`Stacks.Cohomology.SupportedComplexes.isIso_unit_derivedPushforwardAdjunction` — so composition
with the counit is injective on morphisms out of it, by `eq_of_comp_counit`.

Nothing is assumed: `Z` is an arbitrary closed subset and `K`, `M` arbitrary complexes. -/
theorem eq_supportedTensorPushMap
    (φ : ((derivedTensorProductFunctor X.sheaf).obj K).obj
        ((derivedSupportedPushforward X Z hZ).obj M) ⟶
      (derivedSupportedPushforward X Z hZ).obj
        (((derivedTensorProductFunctor X.sheaf).obj K).obj M))
    (hφ :
      letI := pushforward_preservesFiniteLimits X Z
      letI := pushforward_preservesFiniteColimits X Z hZ
      φ ≫ (derivedPushforwardAdjunction X Z hZ).counit.app
            (((derivedTensorProductFunctor X.sheaf).obj K).obj M) =
        ((canonicalDerivedTensorProduct X.sheaf).braidingIso
            (AlgebraicGeometry.RingedSpace.ringedSite X)
            ((derivedSupportedPushforward X Z hZ).obj M) K).inv ≫
          ((derivedTensorProductFunctor X.sheaf).map
            ((derivedPushforwardAdjunction X Z hZ).counit.app M)).app K ≫
          ((canonicalDerivedTensorProduct X.sheaf).braidingIso
            (AlgebraicGeometry.RingedSpace.ringedSite X) M K).hom) :
    φ = supportedTensorPushMap X Z hZ K M := by
  let := pushforward_preservesFiniteLimits X Z
  let := pushforward_preservesFiniteColimits X Z hZ
  have := ((derivedPushforwardAdjunction X Z hZ).fullyFaithfulLOfIsIsoUnit).full
  have := ((derivedPushforwardAdjunction X Z hZ).fullyFaithfulLOfIsIsoUnit).faithful
  exact eq_of_comp_counit (derivedPushforwardAdjunction X Z hZ)
    (supportedTensorPushIso X Z hZ K M) φ (supportedTensorPushMap X Z hZ K M)
    (hφ.trans (supportedTensorPushMap_comp_counit X Z hZ K M).symm)

/-! ### The degree-`c` read-off -/

section DegreeReadOff

variable (A G : Stacks.DerivedTensor.RingedSite.Modules X.sheaf) (c : ℤ)

/-- **Tensoring with a module placed in degree zero is right t-exact**, in the form the
top-degree comparison asks for: the functor `A[0] ⊗^L_{𝒪_X} -` does not raise the degree in
which cohomology lives.

This is `Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProductFunctor` — right t-exactness
in *both* variables with additive bounds — with the left-hand bound `0` contributed by the
single complex and the sum `0 + n` normalised. -/
@[sga "6 III 1.8" "special case"]
theorem isLE_derivedTensorSingle
    (N : Stacks.DerivedTensor.RingedSite.DerivedModules X.sheaf) (n : ℤ) (hN : N.IsLE n) :
    (((derivedTensorProductFunctor X.sheaf).obj
        (DerivedCategory.Q.obj (Stacks.DerivedTensor.RingedSite.sg X.sheaf A))).obj N).IsLE n := by
  have := hN
  have h := Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProductFunctor X.sheaf
    (DerivedCategory.Q.obj (Stacks.DerivedTensor.RingedSite.sg X.sheaf A)) N 0 n
  rwa [zero_add] at h

/-- **The source of `supportedTensorPushMap` in degree `c`, read off as an ordinary tensor
product of sheaves.** Let `A` be a sheaf of modules and suppose the complex `i_*R𝓗_Z(M)` has its
truncation `τ^{≥c}` identified by `e` with a sheaf `G` placed in degree `c` — which is what
`i_*R𝓗_Z(M)` having no cohomology above degree `c` provides, through the single-complex model of
the truncation. Then

`H^c(A[0] ⊗^L_{𝒪_X} i_*R𝓗_Z(M)) ≅ A ⊗_{𝒪_X} G`.

The first leg is `Stacks.TopDegreeComparison.topDegreeIso` for the right t-exact functor
`A[0] ⊗^L_{𝒪_X} -`, which replaces `i_*R𝓗_Z(M)` by its truncation without changing degree-`c`
cohomology. The second is
`Stacks.DerivedTensor.RingedSite.degreeShiftedTensorIso`, the degree-`c` form of the
**unconditional** degree-zero comparison: no flatness and no K-flatness is assumed of `A` or of
`G`, which matters because the intended `A` is a sheaf of differential forms and satisfies
neither. -/
def supportedTensorPushSourceIso
    (e : (DerivedCategory.TStructure.t.truncGE c).obj
        ((derivedSupportedPushforward X Z hZ).obj M) ≅
      (DerivedCategory.Q.obj (Stacks.DerivedTensor.RingedSite.sg X.sheaf G))⟦-c⟧) :
    (DerivedCategory.homologyFunctor
          (Stacks.DerivedTensor.RingedSite.Modules X.sheaf) c).obj
        (((derivedTensorProductFunctor X.sheaf).obj
            (DerivedCategory.Q.obj (Stacks.DerivedTensor.RingedSite.sg X.sheaf A))).obj
          ((derivedSupportedPushforward X Z hZ).obj M)) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj A).obj G :=
  -- The `CommShift` and `IsTriangulated` data of `A[0] ⊗^L -` are the `commShift_right` and
  -- `exact_right` fields of the derived tensor product. They have to be named: instance search
  -- does not look through the `abbrev` `derivedTensorProductFunctor` to the `tensor` projection
  -- of `canonicalDerivedTensorProduct`, so the unqualified search for
  -- `((derivedTensorProductFunctor X.sheaf).obj _).CommShift ℤ` fails.
  letI := (canonicalDerivedTensorProduct X.sheaf).commShift_right
    (DerivedCategory.Q.obj (Stacks.DerivedTensor.RingedSite.sg X.sheaf A))
  letI := (canonicalDerivedTensorProduct X.sheaf).exact_right
    (DerivedCategory.Q.obj (Stacks.DerivedTensor.RingedSite.sg X.sheaf A))
  Stacks.TopDegreeComparison.topDegreeIso
      ((derivedTensorProductFunctor X.sheaf).obj
        (DerivedCategory.Q.obj (Stacks.DerivedTensor.RingedSite.sg X.sheaf A)))
      (isLE_derivedTensorSingle X A) ((derivedSupportedPushforward X Z hZ).obj M) c e ≪≫
    Stacks.DerivedTensor.RingedSite.degreeShiftedTensorIso X.sheaf G A c

/-- **The degree-`c` cohomology sheaf of the multiplication of [Stacks, Tag 0G75] on `X`**, as a
map out of an ordinary tensor product of sheaves:

`A ⊗_{𝒪_X} G ⟶ H^c(i_*R𝓗_Z(A[0] ⊗^L_{𝒪_X} M))`,

where `G` is the degree-`c` cohomology of `i_*R𝓗_Z(M)` in the form supplied by `e`. In the
intended instantiation `A = Ω^p`, `M = Ω^c[0]` and `G = ℋ^c_Z(Ω^c)`, and the target is
`ℋ^c_Z(Ω^{p+c})`; this is the map [Stacks, Tag 0G88] pairs with in the generality of
[Stacks, Tag 0G86], where `Z` is only locally cut out by `c` equations.

It is `H^c` of `supportedTensorPushMap` with its source identified by
`supportedTensorPushSourceIso`. -/
def supportedTensorPushDegreeMap
    (e : (DerivedCategory.TStructure.t.truncGE c).obj
        ((derivedSupportedPushforward X Z hZ).obj M) ≅
      (DerivedCategory.Q.obj (Stacks.DerivedTensor.RingedSite.sg X.sheaf G))⟦-c⟧) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj A).obj G ⟶
      (DerivedCategory.homologyFunctor
          (Stacks.DerivedTensor.RingedSite.Modules X.sheaf) c).obj
        ((derivedSupportedPushforward X Z hZ).obj
          (((derivedTensorProductFunctor X.sheaf).obj
            (DerivedCategory.Q.obj (Stacks.DerivedTensor.RingedSite.sg X.sheaf A))).obj M)) :=
  (supportedTensorPushSourceIso X Z hZ M A G c e).inv ≫
    (DerivedCategory.homologyFunctor
        (Stacks.DerivedTensor.RingedSite.Modules X.sheaf) c).map
      (supportedTensorPushMap X Z hZ
        (DerivedCategory.Q.obj (Stacks.DerivedTensor.RingedSite.sg X.sheaf A)) M)

/-- The degree-`c` read-off is `H^c` of `supportedTensorPushMap` preceded by the identification
of its source, which is what says it carries no information beyond the map of
[Stacks, Tag 0G75]. -/
theorem supportedTensorPushDegreeMap_eq
    (e : (DerivedCategory.TStructure.t.truncGE c).obj
        ((derivedSupportedPushforward X Z hZ).obj M) ≅
      (DerivedCategory.Q.obj (Stacks.DerivedTensor.RingedSite.sg X.sheaf G))⟦-c⟧) :
    supportedTensorPushDegreeMap X Z hZ M A G c e =
      (supportedTensorPushSourceIso X Z hZ M A G c e).inv ≫
        (DerivedCategory.homologyFunctor
            (Stacks.DerivedTensor.RingedSite.Modules X.sheaf) c).map
          (supportedTensorPushMap X Z hZ
            (DerivedCategory.Q.obj (Stacks.DerivedTensor.RingedSite.sg X.sheaf A)) M) :=
  rfl

end DegreeReadOff

/-! ### Discharging the truncation model -/

section TruncationModel

/-- **Vanishing of the local cohomology sheaves above degree `c` passes to the direct image.**
`i_*` is exact, so `H^i(i_*N) = i_*H^i(N)` by
`Stacks.Cohomology.SupportedComplexes.exactFunctorDerivedHomologyIso`, and an additive functor
kills a zero object. Hence the hypothesis of [Stacks, Tag 0G7N] — read for
`R𝓗_Z` on `Z` — gives `i_*R𝓗_Z(M)` cohomology only in degrees `≤ c`, which is the
`IsLE` input that `Stacks.TopDegreeComparison.topDegreeIso` needs. -/
theorem isLE_derivedSupportedPushforward (c : ℤ)
    (hvan : ∀ i : ℤ, c < i → IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X Z))) i).obj
        ((derivedSupportedSectionsOnClosed X Z hZ).obj M))) :
    ((derivedSupportedPushforward X Z hZ).obj M).IsLE c := by
  let := pushforward_preservesFiniteLimits X Z
  let := pushforward_preservesFiniteColimits X Z hZ
  rw [DerivedCategory.isLE_iff]
  intro i hi
  refine IsZero.of_iso ?_ ((exactFunctorDerivedHomologyIso
    (modulePushforward (closedSubsetInclusion X Z)) i).app
      ((derivedSupportedSectionsOnClosed X Z hZ).obj M))
  exact Functor.map_isZero (modulePushforward (closedSubsetInclusion X Z)) (hvan i hi)

/-- **The `τ^{≥c}` model of `i_*R𝓗_Z(M)` that the degree-`c` read-off asks for**, produced from
the vanishing above degree `c` alone. For `i_*R𝓗_Z(M)` with cohomology only in degrees `≤ c` the
truncation `τ^{≥c}` is its degree-`c` cohomology sheaf placed in degree `c`
(`Stacks.AlgebraicGeometry.TopDegreeBaseChange.truncGEIsoSingleHomology`), and
`Stacks.DerivedTensor.RingedSite.singleShiftIso` rewrites that as the degree-zero single complex
shifted by `-c`, which is the spelling `supportedTensorPushSourceIso` consumes. -/
def supportedTensorPushTruncModel (c : ℤ)
    (hM : ((derivedSupportedPushforward X Z hZ).obj M).IsLE c) :
    (DerivedCategory.TStructure.t.truncGE c).obj ((derivedSupportedPushforward X Z hZ).obj M) ≅
      (DerivedCategory.Q.obj (Stacks.DerivedTensor.RingedSite.sg X.sheaf
        ((DerivedCategory.homologyFunctor
            (Stacks.DerivedTensor.RingedSite.Modules X.sheaf) c).obj
          ((derivedSupportedPushforward X Z hZ).obj M))))⟦-c⟧ :=
  Stacks.AlgebraicGeometry.TopDegreeBaseChange.truncGEIsoSingleHomology
      ((derivedSupportedPushforward X Z hZ).obj M) c hM ≪≫
    Stacks.DerivedTensor.RingedSite.singleShiftIso X.sheaf _ c

end TruncationModel

/-! ### The read-off with the model discharged -/

section Unconditional

variable {Y : Scheme.{u}} (T : Set Y) (hT : IsClosed T) (c : ℕ)
variable (hcut : ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ ∃ f : Fin c → Γ(U.toScheme, ⊤),
  U.ι ⁻¹' T = Stacks.Perfect.CechDerivedSupport.equationsClosedSet f)
variable (F : Y.Modules) [F.IsQuasicoherent]

include hcut in
/-- **`i_*R𝓗_T(ℱ)` has no cohomology above degree `c`**, for `ℱ` quasi-coherent on a scheme and
`T` a closed subset locally cut out by `c` equations. This is [Stacks, Tag 0G7N] transported
across the exact direct image by `isLE_derivedSupportedPushforward`: the tag is stated for
`R𝓗_T` on `T`, and `H^i(i_*N) = i_*H^i(N)`. -/
theorem isLE_derivedSupportedPushforward_of_locallyCutOut :
    ((derivedSupportedPushforward Y.toRingedSpace T hT).obj
      ((DerivedCategory.singleFunctor Y.Modules 0).obj F)).IsLE (c : ℤ) :=
  isLE_derivedSupportedPushforward Y.toRingedSpace T hT
    ((DerivedCategory.singleFunctor Y.Modules 0).obj F) (c : ℤ) fun i hi =>
    Stacks.Perfect.LocalCohomologyDegrees.isZero_homology_derivedSupportedSections_of_locallyCutOut
      T hT c hcut F i hi

/-- The degree-`c` cohomology sheaf of `i_*R𝓗_T(ℱ)`: the sheaf written `ℋ^c_T(ℱ)` in
[Stacks, Tag 0G88], read on `Y` — that is as `i_*ℋ^c_T(ℱ)` — which is the side of the closed
subset on which this library's consumers meet it. -/
abbrev supportedTopDegreeSheaf :
    Stacks.DerivedTensor.RingedSite.Modules Y.toRingedSpace.sheaf :=
  (DerivedCategory.homologyFunctor
      (Stacks.DerivedTensor.RingedSite.Modules Y.toRingedSpace.sheaf) (c : ℤ)).obj
    ((derivedSupportedPushforward Y.toRingedSpace T hT).obj
      ((DerivedCategory.singleFunctor Y.Modules 0).obj F))

omit [F.IsQuasicoherent] in
/-- The sheaf `supportedTopDegreeSheaf` is the library's `i_*ℋ^c_T(ℱ)`: the two are the same
`H^c` of the same object `i_*R𝓗_T(ℱ[0])`. Recorded so that the read-off below is checkable
against `Stacks.Perfect.SupportedFraction.supportCohomologySheaf`, which is the spelling the
Čech-model pairing and the Gysin class map use. -/
theorem supportedTopDegreeSheaf_eq :
    supportedTopDegreeSheaf T hT c F =
      Stacks.Perfect.SupportedFraction.supportCohomologySheaf hT F (c : ℤ) :=
  rfl

include hcut in
/-- **The degree-`c` read-off of the multiplication of [Stacks, Tag 0G75], unconditionally.**
For `ℱ` a quasi-coherent module on a scheme `Y`, `T ⊆ Y` a closed subset locally cut out by `c`
equations — the generality of [Stacks, Tag 0G86] — and `A` any sheaf of modules,

`A ⊗_{𝒪_Y} ℋ^c_T(ℱ) ⟶ ℋ^c_T(A[0] ⊗^L_{𝒪_Y} ℱ)`.

This is `supportedTensorPushDegreeMap` with its `τ^{≥c}` model argument discharged: the model is
`supportedTensorPushTruncModel` applied to
`isLE_derivedSupportedPushforward_of_locallyCutOut`, which is [Stacks, Tag 0G7N] transported
across `i_*`. No flatness, no K-flatness and no truncation hypothesis is assumed — the first two
because the degree-zero comparison under `supportedTensorPushSourceIso` needs none, the third
because it is now proved.

In the intended instantiation `A = Ω^p_{Y/S}` and `ℱ = Ω^c_{Y/S}`, and the target is
`ℋ^c_T(Ω^{p+c}_{Y/S})`. -/
def supportedTensorPushTopDegreeMap
    (A : Stacks.DerivedTensor.RingedSite.Modules Y.toRingedSpace.sheaf) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Y.toRingedSpace.sheaf).obj A).obj
        (supportedTopDegreeSheaf T hT c F) ⟶
      (DerivedCategory.homologyFunctor
          (Stacks.DerivedTensor.RingedSite.Modules Y.toRingedSpace.sheaf) (c : ℤ)).obj
        ((derivedSupportedPushforward Y.toRingedSpace T hT).obj
          (((derivedTensorProductFunctor Y.toRingedSpace.sheaf).obj
              (DerivedCategory.Q.obj
                (Stacks.DerivedTensor.RingedSite.sg Y.toRingedSpace.sheaf A))).obj
            ((DerivedCategory.singleFunctor Y.Modules 0).obj F))) :=
  supportedTensorPushDegreeMap Y.toRingedSpace T hT
    ((DerivedCategory.singleFunctor Y.Modules 0).obj F) A (supportedTopDegreeSheaf T hT c F)
    (c : ℤ)
    (supportedTensorPushTruncModel Y.toRingedSpace T hT
      ((DerivedCategory.singleFunctor Y.Modules 0).obj F) (c : ℤ)
      (isLE_derivedSupportedPushforward_of_locallyCutOut T hT c hcut F))

include hcut in
/-- The unconditional read-off is the read-off of `supportedTensorPushDegreeMap` at the model
supplied by `supportedTensorPushTruncModel`, so it carries no information beyond the map of
[Stacks, Tag 0G75]. -/
theorem supportedTensorPushTopDegreeMap_eq
    (A : Stacks.DerivedTensor.RingedSite.Modules Y.toRingedSpace.sheaf) :
    supportedTensorPushTopDegreeMap T hT c hcut F A =
      supportedTensorPushDegreeMap Y.toRingedSpace T hT
        ((DerivedCategory.singleFunctor Y.Modules 0).obj F) A
        (supportedTopDegreeSheaf T hT c F) (c : ℤ)
        (supportedTensorPushTruncModel Y.toRingedSpace T hT
          ((DerivedCategory.singleFunctor Y.Modules 0).obj F) (c : ℤ)
          (isLE_derivedSupportedPushforward_of_locallyCutOut T hT c hcut F)) :=
  rfl

/-! ### Landing on an ordinary local cohomology sheaf -/

include hcut in
/-- **The degree-`c` read-off with its target an ordinary local cohomology sheaf**, as

`A ⊗_{𝒪_Y} ℋ^c_T(ℱ) ⟶ ℋ^c_T(A ⊗_{𝒪_Y} ℱ)`.

`supportedTensorPushTopDegreeMap` lands in `H^c(i_*R𝓗_T(A[0] ⊗^L ℱ))`, whose argument is a
*derived* tensor product; this composes it with `i_*R𝓗_T` of the canonical map
`Stacks.DerivedTensor.RingedSite.tensorSingleToSingle`, which replaces that derived tensor
product by the ordinary one. Nothing is assumed to do so: the canonical map
`A[0] ⊗^L ℱ[0] ⟶ (A ⊗ ℱ)[0]` exists without flatness or K-flatness, and only its existence is
used — it is not inverted, which is what would need a hypothesis.

Both sides are now local cohomology sheaves of honest sheaves of modules, so the map can be
post-composed with `ℋ^c_T` of any morphism out of `A ⊗ ℱ`; that is
`supportedTopDegreeMulMap`. -/
def supportedTopDegreeTensorMap
    (A : Stacks.DerivedTensor.RingedSite.Modules Y.toRingedSpace.sheaf) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Y.toRingedSpace.sheaf).obj A).obj
        (supportedTopDegreeSheaf T hT c F) ⟶
      supportedTopDegreeSheaf T hT c
        (((Stacks.SheafOfModules.Tensor.sheafTensor Y.toRingedSpace.sheaf).obj A).obj F) :=
  supportedTensorPushTopDegreeMap T hT c hcut F A ≫
    (DerivedCategory.homologyFunctor
        (Stacks.DerivedTensor.RingedSite.Modules Y.toRingedSpace.sheaf) (c : ℤ)).map
      ((derivedSupportedPushforward Y.toRingedSpace T hT).map
        (tensorSingleToSingle Y.toRingedSpace.sheaf A F))

include hcut in
/-- The read-off into an ordinary local cohomology sheaf is the read-off of
`supportedTensorPushTopDegreeMap` followed by `i_*R𝓗_T` of the canonical comparison, so it
carries no information beyond the map of [Stacks, Tag 0G75] and that comparison. -/
theorem supportedTopDegreeTensorMap_eq
    (A : Stacks.DerivedTensor.RingedSite.Modules Y.toRingedSpace.sheaf) :
    supportedTopDegreeTensorMap T hT c hcut F A =
      supportedTensorPushTopDegreeMap T hT c hcut F A ≫
        (DerivedCategory.homologyFunctor
            (Stacks.DerivedTensor.RingedSite.Modules Y.toRingedSpace.sheaf) (c : ℤ)).map
          ((derivedSupportedPushforward Y.toRingedSpace T hT).map
            (tensorSingleToSingle Y.toRingedSpace.sheaf A F)) :=
  rfl

include hcut in
/-- **The multiplication of [Stacks, Tag 0G75] in degree `c`, with a multiplication of sheaves
put on the end.** For `ℱ` quasi-coherent on a scheme `Y`, `T ⊆ Y` closed and locally cut out by
`c` equations — the generality of [Stacks, Tag 0G86] — `A` any sheaf of modules and any morphism
`w : A ⊗_{𝒪_Y} ℱ ⟶ G`,

`A ⊗_{𝒪_Y} ℋ^c_T(ℱ) ⟶ ℋ^c_T(G)`,

stated at `Stacks.Perfect.SupportedFraction.supportCohomologySheaf` on both sides — the spelling
every consumer of `ℋ^c_T` in this library uses, by `supportedTopDegreeSheaf_eq`.

This is `supportedTopDegreeTensorMap` followed by `ℋ^c_T(w)`. The intended `w` is the wedge
`Ω^p ⊗ Ω^c ⟶ Ω^{p+c}` of the de Rham algebra, for which the composite is
`Stacks.Gysin.gysinWedgeTopDegreeMap` and the display is the source's

`i^{-1}Ω^p ⊗ ℋ^c_Z(Ω^c) ⟶ ℋ^c_Z(Ω^{p+c})`,

read on `Y`. Nothing about the de Rham complex enters here, so the statement is given for an
arbitrary `w`. -/
def supportedTopDegreeMulMap
    (A G : Stacks.DerivedTensor.RingedSite.Modules Y.toRingedSpace.sheaf)
    (w : ((Stacks.SheafOfModules.Tensor.sheafTensor Y.toRingedSpace.sheaf).obj A).obj F ⟶ G) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Y.toRingedSpace.sheaf).obj A).obj
        (Stacks.Perfect.SupportedFraction.supportCohomologySheaf hT F (c : ℤ)) ⟶
      Stacks.Perfect.SupportedFraction.supportCohomologySheaf hT G (c : ℤ) :=
  supportedTopDegreeTensorMap T hT c hcut F A ≫
    (DerivedCategory.homologyFunctor
        (Stacks.DerivedTensor.RingedSite.Modules Y.toRingedSpace.sheaf) (c : ℤ)).map
      ((derivedSupportedPushforward Y.toRingedSpace T hT).map
        ((DerivedCategory.singleFunctor Y.Modules 0).map w))

include hcut in
/-- The multiplication read off in degree `c` is the read-off into an ordinary local cohomology
sheaf followed by `ℋ^c_T(w)`, so it is functorial in `w` by construction. -/
theorem supportedTopDegreeMulMap_eq
    (A G : Stacks.DerivedTensor.RingedSite.Modules Y.toRingedSpace.sheaf)
    (w : ((Stacks.SheafOfModules.Tensor.sheafTensor Y.toRingedSpace.sheaf).obj A).obj F ⟶ G) :
    supportedTopDegreeMulMap T hT c hcut F A G w =
      supportedTopDegreeTensorMap T hT c hcut F A ≫
        (DerivedCategory.homologyFunctor
            (Stacks.DerivedTensor.RingedSite.Modules Y.toRingedSpace.sheaf) (c : ℤ)).map
          ((derivedSupportedPushforward Y.toRingedSpace T hT).map
            ((DerivedCategory.singleFunctor Y.Modules 0).map w)) :=
  rfl

end Unconditional

/-! ### The Čech model and the counit -/

section CechCounit

open Stacks.Perfect.SupportedFraction Stacks.Perfect.SupportCounitComparison
open Stacks.Perfect.ExtendedAlternatingCech.Augmentation (augmentation)

variable {Y : Scheme.{u}} {m : ℕ} (e : Fin m → Γ(Y, ⊤)) (F : Y.Modules) [F.IsQuasicoherent]
variable {T : Set Y} (hT : IsClosed T)
  (hTe : Stacks.Perfect.CechDerivedSupport.equationsClosedSet e ⊆ T)

omit [F.IsQuasicoherent] in
/-- **The comparison of [Stacks, Tag 0G7L] followed by the counit of [Stacks, Tag 0A3B] is the
augmentation.** The canonical map `𝓕^• ⟶ i_*R𝓗_T(ℱ)` of [Stacks, Tag 0G7L], composed with the
canonical map `i_*R𝓗_T(ℱ) ⟶ ℱ` of [Stacks, Tag 0G72], is the augmentation `𝓕^• ⟶ ℱ[0]`.

This is the commuting triangle of [Stacks, Tag 0G7L] read the other way round:
`Stacks.Perfect.SupportedFraction.derivedSupportedSectionsToId_comp_cechToDerivedSupport`
states it with the counit *in front* of the comparison, and the counit being invertible at the
Čech complex (`Stacks.Perfect.SupportedFraction.isIso_derivedSupportedSectionsToId_cech`) plus
its naturality turn that into this form.

Together with `eq_supportedTensorPushMap` this is what reduces an identification of the
multiplication of [Stacks, Tag 0G75] with a map built in the Čech model to a statement about
augmentations: the counit of a composite through the Čech model is computed here, and
`eq_supportedTensorPushMap` says the counit is all that has to be computed. -/
theorem cechToDerivedSupport_comp_counit :
    letI := pushforward_preservesFiniteLimits Y.toRingedSpace T
    letI := pushforward_preservesFiniteColimits Y.toRingedSpace T hT
    cechToDerivedSupport e F hT hTe ≫
        (derivedPushforwardAdjunction Y.toRingedSpace T hT).counit.app
          ((DerivedCategory.singleFunctor Y.Modules 0).obj F) =
      augmentation e F := by
  let := pushforward_preservesFiniteLimits Y.toRingedSpace T
  let := pushforward_preservesFiniteColimits Y.toRingedSpace T hT
  have := isIso_derivedSupportedSectionsToId_cech e F hT hTe
  have hswitch :
      (supportPushCounit (X := Y) hT).app
          ((DerivedCategory.singleFunctor Y.Modules 0).obj F) =
        (derivedPushforwardAdjunction Y.toRingedSpace T hT).counit.app
          ((DerivedCategory.singleFunctor Y.Modules 0).obj F) :=
    NatTrans.congr_app
      (derivedSupportedSectionsToId_eq_derivedPushforwardAdjunction_counit Y.toRingedSpace T hT)
      ((DerivedCategory.singleFunctor Y.Modules 0).obj F)
  have hnat := (supportPushCounit (X := Y) hT).naturality (augmentation e F)
  have hcomp := derivedSupportedSectionsToId_comp_cechToDerivedSupport e F hT hTe
  refine ((Iso.cancel_iso_hom_left
    (@asIso _ _ _ _ _ (isIso_derivedSupportedSectionsToId_cech e F hT hTe)) _ _).mp ?_)
  rw [asIso_hom, ← hswitch]
  exact comp_comp_of_comp _ (cechToDerivedSupport e F hT hTe) _
    ((supportPushCounit (X := Y) hT).app ((DerivedCategory.singleFunctor Y.Modules 0).obj F)) _
    hcomp hnat

end CechCounit

end Stacks.Cohomology.SupportedComplexes

end
