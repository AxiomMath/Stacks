module

public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Geometry.RingedSpace.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentConeHomologySequence
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentConeMap
public import StacksFrontier.Cotangent.SheavesOfRings.CotangentComplex
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentInverseImage

/-!
# The exact sequence of naive cotangent complexes of a composition

Let `A ⟶ B ⟶ C` be morphisms of sheaves of commutative rings on a topological space `X`.  The
naive cotangent complexes of the three morphisms `A ⟶ B`, `A ⟶ C` and `B ⟶ C` are related by
the canonical chain maps

`c₁ : NL_{B/A} ⊗_B C ⟶ NL_{C/A}`  and  `g : NL_{C/A} ⟶ NL_{C/B}`

of complexes of sheaves of `C`-modules, and the composite `c₁ ≫ g` is null homotopic.  The
canonical map of **Stacks 0E1Y** is the resulting factorisation

`c : NL_{B/A} ⊗_B C ⟶ C(g)[-1]`

of `c₁` through the shift by `-1` of the cone of `g`.

For composable morphisms of ringed spaces `f : X ⟶ Y` and `g : Y ⟶ Z` this applies to the
sequence of sheaves of rings `(g ∘ f)⁻¹O_Z ⟶ f⁻¹O_Y ⟶ O_X` on `X`.  The inverse-image theorem
Stacks 08TM identifies `f⁻¹NL_{O_Y/g⁻¹O_Z}` with `NL_{f⁻¹O_Y/(g ∘ f)⁻¹O_Z}`, so that extending
scalars to `O_X` identifies the pullback `f^*NL_{Y/Z}` with the base-changed complex above.
Transporting the canonical map along that identification gives the canonical map
`f^*NL_{Y/Z} ⟶ C(NL_{X/Z} ⟶ NL_{X/Y})[-1]` of **Stacks 0E1Z**.

## Main definitions

* `Stacks.SheafOfModules.spaceNaiveCotangentConeMap`: the canonical map
  `c : NL_{B/A} ⊗_B C ⟶ C(g)[-1]` for sheaves of rings on a topological space.
* `Stacks.SheafOfModules.ringedSpaceStructureMap`: the adjoint transpose `f⁻¹O_Y ⟶ O_X` of the
  structure morphism of a morphism of ringed spaces.
* `Stacks.SheafOfModules.pulledNaiveCotangentComplex` and
  `Stacks.SheafOfModules.pulledNaiveCotangentComparison`: the pullback `f^*NL_{Y/Z}`, written
  as the inverse image of `NL_{Y/Z}` with scalars extended to `O_X`, and its identification
  with the base-changed complex `NL_{f⁻¹O_Y/(g ∘ f)⁻¹O_Z} ⊗ O_X`.
* `Stacks.SheafOfModules.ringedSpaceNaiveCotangentConeMap`: the canonical map
  `f^*NL_{Y/Z} ⟶ C(NL_{X/Z} ⟶ NL_{X/Y})[-1]`.
* `Stacks.SheafOfModules.spaceNaiveCotangentConeShortComplex` and
  `Stacks.SheafOfModules.spaceNaiveCotangentConeConnecting`: the degreewise split short exact
  sequence `0 ⟶ NL_{C/B} ⟶ C(g) ⟶ NL_{C/A}[1] ⟶ 0` of the cone and the connecting morphism of
  its long exact sequence of cohomology sheaves.  The sequence and its exactness live in
  `StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentConeHomologySequence`.
* `Stacks.SheafOfModules.ringedSpaceNaiveCotangentConeShortComplex` and
  `Stacks.SheafOfModules.ringedSpaceNaiveCotangentConeConnecting`: the same for a pair of
  composable morphisms of ringed spaces.

## Main results

* `Stacks.SheafOfModules.spaceNaiveCotangentConeMap_comp_pShift` and
  `Stacks.SheafOfModules.ringedSpaceNaiveCotangentConeMap_comp_pShift`: composing the canonical
  map with the projection of the shifted cone onto `NL_{C/A}`, respectively onto `NL_{X/Z}`,
  returns the canonical map `c₁`.  This is the property that makes the two canonical maps lifts
  of `c₁`.
* `Stacks.SheafOfModules.spaceNaiveCotangentConeMap_comp_snd` and
  `Stacks.SheafOfModules.ringedSpaceNaiveCotangentConeMap_comp_snd`: composing the canonical map
  with the degree `-1` projection of the shifted cone returns the explicit null homotopy of
  `c₁ ≫ g`, respectively that homotopy preceded by the identification
  `pulledNaiveCotangentComparison`.  Together with the previous results this pins each canonical
  map down to the pair of components produced by Stacks 08RI (2).  The homotopy itself is
  identified in `Stacks.SheafOfModules.baseChangeRelativeNullHomotopy_hom_zero_negOne`.
* `Stacks.SheafOfModules.ringedSpaceNaiveCotangentConeShortComplex_shortExact`: the degreewise
  split short exact sequence of the cone, for a pair of composable morphisms of ringed spaces.
* `Stacks.SheafOfModules.spaceNaiveCotangentConeMap_homologyMap_comp_pShift`: on cohomology
  sheaves the canonical map followed by the projection of the shifted cone is the map induced by
  `c₁`.
* `Stacks.SheafOfModules.spaceNaiveCotangentCone_homology_exact_target`,
  `Stacks.SheafOfModules.spaceNaiveCotangentCone_homology_exact_cone` and
  `Stacks.SheafOfModules.spaceNaiveCotangentCone_homology_exact_source`: **the long exact
  sequence
  `Hⁱ(NL_{C/A}) ⟶ Hⁱ(NL_{C/B}) --∂--> H^{i+1}(C(g)[-1]) ⟶ H^{i+1}(NL_{C/A}) ⟶ H^{i+1}(NL_{C/B})`
  of the cone**, in the three places the six-term sequence of Stacks 0E1Y consumes it: for
  `i = -1` the first is its exactness at `H^{-1}(NL_{C/B})` and the second its exactness at
  `H⁰(NL_{B/A} ⊗_B C)`, and the third is its exactness at `H⁰(NL_{C/A})` (`i = -1`) and at
  `H^{-1}(NL_{C/A})` (`i = -2`) — in each case read before the comparison of
  `H^j(NL_{B/A} ⊗_B C)` with `H^j(C(g)[-1])` along the canonical map.
* `Stacks.SheafOfModules.exact_spaceJacobiZariskiHomologySequence_negOne` and `_zero`,
  `Stacks.SheafOfModules.epi_homologyMap_spaceRelativeNaiveCotangentComplexMap_zero`, and their
  ringed-space counterparts, prove **exactness of the six-term sequence of Stacks 0E1Y, and of
  Stacks 0E1Z, at `H^{-1}(NL_{C/A})`, at `H⁰(NL_{C/A})` and at `H⁰(NL_{C/B})`**, the last being
  the final `⟶ 0`; they live in
  `StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentJacobiZariskiSheaves`, which is where the
  stalk computation they need is available.

## Implementation notes

Three of the assertions of the six-term exact sequence of cohomology sheaves are proved, in
`StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentJacobiZariskiSheaves`: its exactness at
`H^{-1}(NL_{C/A})` and at `H⁰(NL_{C/A})`, that is, of

`H^j(NL_{B/A} ⊗_B C) ⟶ H^j(NL_{C/A}) ⟶ H^j(NL_{C/B})`

at the middle term for `j = -1` and `j = 0`, and the final `⟶ 0`, that is, surjectivity of
`H⁰(NL_{C/A}) ⟶ H⁰(NL_{C/B})`; and the same three for a pair of composable morphisms of ringed
spaces.  None of the three involves the cone or the connecting map: they are stalkwise statements
about `c₁` and `g` alone, and at a stalk they are the exactness of Algebra, Lemma 00S2 at the
middle node, respectively its surjectivity clause, over the canonical presentations.

The other three assertions — the connecting map, exactness at `H^{-1}(NL_{C/B})` and exactness
at `H⁰(NL_{B/A} ⊗_B C)` — are proved in
`StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentJacobiZariskiSixTerm`, on top of
`Stacks.SheafOfModules.isIso_homologyMap_spaceNaiveCotangentConeMap_zero`.  What they need is
the long exact sequence of the cone, recorded in
`StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentConeHomologySequence` and instantiated
at a topological space and at a pair of morphisms of ringed spaces below, together with the two
bridges that read that sequence off the canonical map: the identification
`CochainComplex.homologyMap_pShift` of `pShift g` on cohomology with the third morphism of the
cone triangle, and the identification
`Stacks.SheafOfModules.baseChangeRelativeNullHomotopy_hom_zero_negOne` of the homotopy
component of `c`.

Half of the comparison of `NL_{B/A} ⊗_B C` with `C(g)[-1]` along the canonical map is available:
`H^{-1}(c)` is surjective, by
`Stacks.SheafOfModules.epi_homologyMap_spaceNaiveCotangentConeMap_negOne`, which needs no
comparison of connecting maps — in degree `-1` the projection of the shifted cone is a
monomorphism, so exactness at `H^{-1}(NL_{C/A})` of the sequence above already forces the
surjectivity.

The other half, that `H⁰(c)` is an isomorphism, is
`Stacks.SheafOfModules.isIso_homologyMap_spaceNaiveCotangentConeMap_zero`
(`StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentConeHomologyZero`); it is what produces the
connecting map of the sequence and with it the two remaining assertions, exactness at
`H^{-1}(NL_{C/B})` and at `H⁰(NL_{B/A} ⊗_B C)`.  It is a stalkwise statement —
`AlgebraicGeometry.SheafOfModules.isIso_homologyMap_iff_forall_stalk` localizes it and Stacks
0D09 computes the stalks of the three complexes — but it cannot be reached the way `H^{-1}(c)`
is: in degree `0` the projection of the shifted cone is not a monomorphism, its kernel being the
image of the connecting morphism of the cone, so surjectivity of `H⁰(c)` needs that image to lie
in the image of `H⁰(c)`.  The route taken reaches that through the cokernel description below
rather than through a comparison of connecting morphisms.

At a stalk the input is Algebra, Lemma 00S2 over the *canonical* presentations, which is what
0D09 delivers there:
`NaiveCotangent.jacobiZariski_sixTerm_exact_canonical`
(`StacksFrontier.RingTheory.NaiveCotangent.JacobiZariskiPresentations`) states it for the
`Algebra.Generators.self` presentations, deduced from presentation-independence, Stacks 00S1 (4);
its surjectivity clause is the one the final `⟶ 0` needs, and its two middle-node exactness
clauses are what the two assertions above are proved from.  The route actually taken avoids the
identification of the two connecting maps that a ladder for the remaining assertions would need
on its left-hand square, namely

`δ ≫ H⁰(c) = ∂`

for `δ` the snake-lemma connecting map `NaiveCotangent.connecting` of 00S2 and `∂` the cone's
`CochainComplex.coneHomologyConnecting`; `δ` cannot be obtained by transporting `∂` backwards,
since the transport would need the inverse of `H⁰(c)`.  The two handles on the two maps are
`NaiveCotangent.connecting_apply`, which computes `δ` on a zig-zag, and the definition of
`CochainComplex.coneHomologyConnecting` as `H(mappingCone.inr g)` read through
`CochainComplex.shiftedMappingConeHomologyIso`.

**The square is not the only route, and the cheaper one goes through a cokernel.**  The canonical
map `g` is an *isomorphism in degree `0`*: both degree `0` terms are built from the canonical
polynomial presentation of Stacks 07BL, whose variables are indexed by `C` in either case, and
`g` fixes those variables.  This is
`Stacks.SheafOfModules.isIso_spaceRelativeNaiveCotangentComplexMap_zero`
(`StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentRelativeDegreeZero`), proved stalkwise from
`NaiveCotangent.bijective_cotangentSpaceMap_self`.  It collapses the shifted cone in degree `0`:
writing `L = NL_{C/A}`, `M = NL_{C/B}` and `C(g)^n = L^{n+1} ⊕ M^n`, Mathlib's
`CochainComplex.mappingCone.d_fst_v` and `d_snd_v` say that the differential of the cone is
`(l, m) ↦ (-d_L l, g l + d_M m)`, so in degrees `-2, -1, 0` the cone reads

`L^{-1} ⟶ L^0 ⊕ M^{-1} ⟶ M^0`,

its cycles in degree `-1` are the pairs with `g l + d_M m = 0`, and invertibility of `g` in
degree `0` makes the second projection carry those cycles isomorphically onto `M^{-1}` and the
boundaries onto the image of `g` in degree `-1`.  Hence

`H⁰(C(g)[-1]) = H^{-1}(C(g)) ≅ coker (g^{-1} : L^{-1} ⟶ M^{-1})`,

which is `CochainComplex.mappingCone.homologyNegOneIsoCokernel`
(`StacksFrontier.Algebra.Homology.MappingConeTwoTermHomology`), proved for any morphism of
two-term complexes in an abelian category which is invertible in degree `0`.  Under that
identification `H⁰(c)` becomes the map `coker (d_{NL_{B/A} ⊗ C}) ⟶ coker g^{-1}`
induced by the degree `-1` component `h` of the null homotopy, up to the sign recorded in
`CochainComplex.factorThroughShiftedMappingCone_comp_snd` — a sign which does not matter, an
isomorphism composed with `-𝟙` being an isomorphism.  **So what remains is: the
homotopy `h` induces an isomorphism `H⁰(NL_{B/A} ⊗_B C) ≅ coker (g^{-1})`**, a statement about
one commutative square of sheaves of `C`-modules, with no cone, no shift and no connecting map
in it.  At a stalk, over the canonical presentations, it is the pair of elementwise assertions
that `J/J²` is generated by the image of the conormal module of `A_x[C_x] ⟶ C_x` together with
the classes `[X_{φ(b)} - b]`, and that a combination of the `d X_b` whose `h`-image lies in that
image is a boundary.

The shift is included: `CochainComplex.mappingCone.shiftedHomologyZeroIsoCokernel` is the
identification `H⁰(C(g)[-1]) ≅ coker (g^{-1})` itself, the shift being
`CochainComplex.shiftedMappingConeHomologyIso`.

**The compatibility of `H⁰(c)` with that identification is now proved.**  A complex `P` which
vanishes in degree `1` — as `NL_{B/A} ⊗_B C` does — has a canonical epimorphism
`CochainComplex.toHomologyZero : P^0 ⟶ H⁰(P)` killing the boundaries
(`CochainComplex.epi_toHomologyZero`, `CochainComplex.d_comp_toHomologyZero`), so `H⁰(P)` *is*
`coker (d_P^{-1})` read through it, and
`CochainComplex.mappingCone.toHomologyZero_comp_homologyMap_comp_shiftedHomologyZeroIsoCokernel`
says that the composite

`P^0 ⟶ H⁰(P) --H⁰(c)--> H⁰(C(g)[-1]) ≅ coker (g^{-1})`

is `CochainComplex.mappingCone.shiftedSndZero` — the degree `0` component of `c` read against
the second projection of the cone, which for the canonical map of Stacks 0E1Y is the degree `-1`
component of its null homotopy — followed by `cokernel.π`.  Since the first arrow is an
epimorphism this determines `H⁰(c)`; with
`CochainComplex.mappingCone.d_comp_shiftedSndZero`, which says that `shiftedSndZero` kills the
boundaries up to the image of `g^{-1}`, it says exactly that `H⁰(c)` *is* the map
`coker (d_P^{-1}) ⟶ coker (g^{-1})` induced by the homotopy.  So what remains really
is the one statement **`h` induces an isomorphism `H⁰(NL_{B/A} ⊗_B C) ≅ coker (g^{-1})`**, and
no cone, no shift and no connecting map occur in it.

(Producing that compatibility as a
`CategoryTheory.ShortComplex.LeftHomologyMapData` between the cokernel left homology data of
`NL_{B/A} ⊗_B C` in degree `0` and `CochainComplex.mappingCone.twoTermLeftHomologyData` does not
work as stated: the two short complexes to be compared are
`(NL_{B/A} ⊗_B C).sc' (-1) 0 1` and `C(g).sc' (-2) (-1) 0`, and there is no morphism between them
— they are separated by the shift, whose effect on homology is
`CategoryTheory.Functor.shiftIso`, not a morphism of short complexes of the two complexes at
hand.  The route above goes through `liftCycles` and `homologyπ` instead, and crosses the shift
with Mathlib's `CochainComplex.liftCycles_shift_homologyπ`.  That lemma states the shift
identification as `Functor.shiftIso ... .inv.app`, whose source is only definitionally
`H^{-1}(C(g))`, so a composite in which it meets
`CochainComplex.shiftedMappingConeHomologyIso` is not type-correct at `implicit` transparency and
`rw` will not act on it; the spelling is fixed once in
`CochainComplex.mappingCone.liftCycles_homologyπ_shift`.  The same obstruction is why
`CochainComplex.mappingCone.twoTermLeftHomologyData` carries `@[implicit_reducible]`.)

**At the ring level the remaining step is reduced to one computation, which is proved**, in
`StacksFrontier.RingTheory.NaiveCotangent.JacobiZariskiCokernel`.  Over the canonical presentations
`P = A[B] ⟶ B`, `N = A[C] ⟶ C`, `Q = B[C] ⟶ C` of Stacks 07BL the homotopy of Stacks 07VC is
`NaiveCotangent.towerNullHomotopy`, which sends `d[b]` to the class of `[φ(b)] - b` in `J/J²`;
`NaiveCotangent.towerNullHomotopyBaseChange` is its base change to `C`,
`NaiveCotangent.towerNullHomotopyBaseChange_comp_d` and
`NaiveCotangent.d_comp_towerNullHomotopyBaseChange` are the two identities of Stacks 07VC base
changed, and `NaiveCotangent.towerCokernelMap` is the resulting map
`H₀(NL(P) ⊗_B C) ⟶ coker (g^{-1})`.  The computation that makes it an isomorphism is

`NaiveCotangent.connecting_nullHomotopy_mem_range`: for a cycle `z` of `J/J²` there is a
representative `x` of `δ z` — `δ` being `NaiveCotangent.jacobiZariskiConnecting`, the connecting
map of Stacks 00S2 — with `z + h x` in the image of `K/K² ⟶ J/J²`.

That is the `δ`-square `δ ≫ H⁰(c) = ±∂` in elementwise form, and it is proved from the explicit
homotopy of Stacks 00S1 (2) between the *two* morphisms of presentations `A[y_c, x_b] ⟶ B[y_c]`:
`Algebra.Generators.ofComp`, which sends `x_b` to the coefficient `b`, and
`NaiveCotangent.towerCompRelHom`, which factors through `A[C]` and sends `x_b` to the variable
`y_{φ(b)}`.  Their difference on `x_b` is `b - [φ(b)]`, so that homotopy restricted along
`Algebra.Generators.toComp` is minus the homotopy of Stacks 07VC
(`NaiveCotangent.towerCompSub_comp_cotangentSpaceMap_toComp`), and evaluating it on a zig-zag for
`δ` gives the statement.

With it, **`NaiveCotangent.bijective_towerCokernelMap` settles it at the ring level**: both
of the elementwise assertions recorded above follow from the `δ`-square together with the five
exactness clauses of `NaiveCotangent.jacobiZariski_sixTerm_exact_canonical`.  Surjectivity
(`NaiveCotangent.surjective_towerCokernelMap`) uses exactness at `Ω_{C/A}` and bijectivity of `g`
in degree `0` (`NaiveCotangent.bijective_cotangentSpaceMap_towerTopHom`): the differential of a
class `j ∈ J/J²` is `g₀ l` for a unique `l`, exactness writes `l = c₁ n + d z`, and
`j - h n - g z` is then a cycle, which the `δ`-square puts in the image of `h` modulo the image
of `g` in degree `-1`.  Injectivity (`NaiveCotangent.injective_towerCokernelMap`) uses exactness
at `C ⊗_B Ω_{B/A}` and at `H₁(NL_{C/B})`: if `h n` lies in the image of `g` in degree `-1` then
`c₁ n` is a boundary, so the class of `n` is `δ ζ`, and the `δ`-square puts `ζ` itself in the
image of `g` on `H₁`, where `δ` vanishes.

**The transport of that ring-level statement to the stalks of the three sheaf complexes is
carried out in `StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentConeHomologyZero`**: the
stalk of `H⁰(c)` is identified with `NaiveCotangent.towerCokernelMap` through the stalk legs
(`Stacks.NaiveCotangentAffineStalkLegs.stalkLegNegOneLinear` and the base-changed pair
`Stacks.NaiveCotangentStalkBaseChange.stalkBaseChangeAddEquivZero`), and
`AlgebraicGeometry.SheafOfModules.isIso_cokernelDesc_comp_π_iff_forall_bijective_liftQ`
localizes the statement.  The four maps in that identification are:

* The stalk of `g` in degrees `-1` and `0` is
  `Stacks.NaiveCotangentStalkJacobiZariski.stalkLegNegOneLinear_spaceRelativeMap` and `_zero`,
  and `Stacks.NaiveCotangentTowerStalk.range_cotangentMap_stalkTowerHomRel` identifies the image
  of the degree `-1` half with the submodule that `NaiveCotangent.towerRelConormalCokernel` is
  the quotient by.
* The stalk of the differential of `NL_{B/A} ⊗_B C` is
  `Stacks.NaiveCotangentStalkBaseChange.stalkBaseChangeAddEquiv_d`: it is the base change to
  `C_z` of the cotangent complex of `Generators.self A_z B_z`, which is the submodule whose
  quotient `NaiveCotangent.towerCokernelMap` is defined on.
* The stalk of the null homotopy `h` inside `c` is
  `Stacks.NaiveCotangentStalkBaseChange.stalkLegNegOneLinear_baseChangeRelativeNullHomotopy`
  (`StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentStalkTowerHomotopy`): read through
  `stalkBaseChangeAddEquivZero` on the source and the degree `-1` leg of Stacks 0D09 on the
  target it *is* `NaiveCotangent.towerNullHomotopyBaseChange`.  The computation runs along the
  same three legs as the stalk of `c₁`, the interchange leg being the object-level
  `Opens.stalkTowerExtendScalarsObj_map_inv_tmul` — a homotopy component is a bare morphism out
  of the degree `0` term, not a chain map, so the chain-map form does not apply.  The ring-level
  homotopy is known only on the basis `Algebra.Generators.cotangentSpaceBasis`, and that is
  enough: `Stacks.NaiveCotangentStalkBaseChange.tmul_basis_ext` says two *additive* maps out of
  `C_z ⊗_{B_z} M` which agree on every `t ⊗ (basis element)` agree, the basis coefficients moving
  into the left-hand factor.  No linearity over `B_z` is needed, and none is available: the
  project's linear legs are linear over the `RingCat`-valued stalk, and an action of the
  `CommRingCat`-valued `B_z` on these stalks cannot be elaborated within the heartbeat ceiling
  (`StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentAffineStalkLegsLinear`).

* The stalk of the target `coker (g^{-1})`, presented as the quotient of the stalk by the range
  of the stalk map, is
  `AlgebraicGeometry.SheafOfModules.stalkObjCokernelRangeQuotientIso`
  (`StacksFrontier.Topology.Sheaves.Modules.StalkCokernelQuotient`): the stalk of a cokernel is the
  cokernel of the stalks
  (`AlgebraicGeometry.SheafOfModules.stalkObjCokernelIso`), followed by
  `ModuleCat.cokernelIsoRangeQuotient`.  It is what turns the criterion into a statement about
  one map of explicit quotient modules, and it is folded into
  `AlgebraicGeometry.SheafOfModules.isIso_cokernelDesc_comp_π_iff_forall_bijective_liftQ`, so
  the bijectivity of `NaiveCotangent.towerCokernelMap` can be fed in elementwise rather than as
  a bundled additive equivalence.

With those four, `CochainComplex.mappingCone.isIso_homologyMap_zero_iff` turns the stalkwise
bijectivity into `IsIso (H⁰ c)`, and
`CochainComplex.mappingCone.shiftedSndZero_factorThroughShiftedMappingCone` identifies the
morphism being descended with `h`.  All six assertions of the sequence are therefore covered,
and the clause notes below say what each declaration carries.

One tool an earlier assessment recorded as absent does exist, and it removes the stalk of the
mapping cone from the critical path altogether: for any additive functor the image of a cone is
the cone of the image, by Mathlib's
`CochainComplex.mappingCone.mapHomologicalComplexIso`.  So the reduction above, which is stated
for sheaves, does not have to be redone at a stalk.

Each statement about a fixed topological space is obtained from the corresponding statement for
an arbitrary site, which lives in
`StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentConeMap`.  The arguments measuring the
universes of the site and of the sections are given explicitly, and each proof introduces the
general result before matching it against the statement, so that the instance arguments of the
general result are resolved before the two complexes are compared: the two complexes are
produced by sheafification, and comparing them with an unresolved instance argument forces the
sheafification to unfold.

## References

* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y)
* [Stacks Project, Tag 0E1Z](https://stacks.math.columbia.edu/tag/0E1Z)
* [Stacks Project, Tag 08TM](https://stacks.math.columbia.edu/tag/08TM), the inverse image of
  the naive cotangent complex.
* [Stacks Project, Tag 08RI](https://stacks.math.columbia.edu/tag/08RI), part (2),
  factorisation through a shifted cone.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

open AlgebraicGeometry.SheafOfModules (inverseImageRingHom)

/-! ### Sheaves of rings on a topological space -/

section Space

variable {X : TopCat.{u}} (A B C : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  (a : A ⟶ B) (b : B ⟶ C)

/-- The base change `NL_{B/A} ⊗_B C` of the naive cotangent complex of `B` over `A`, for
sheaves of commutative rings on a topological space. -/
noncomputable abbrev spaceBaseChangeNaiveCotangentComplex :=
  baseChangeNaiveCotangentComplex.{u, u, u} (Opens.grothendieckTopology X) A B C a b

/-- The canonical map `c₁ : NL_{B/A} ⊗_B C ⟶ NL_{C/A}`, for sheaves of commutative rings on a
topological space. -/
noncomputable abbrev spaceBaseChangeNaiveCotangentMap :=
  baseChangeNaiveCotangentMap.{u, u, u} (Opens.grothendieckTopology X) A B C a b

/-- The canonical map `g : NL_{C/A} ⟶ NL_{C/B}`, for sheaves of commutative rings on a
topological space. -/
noncomputable abbrev spaceRelativeNaiveCotangentComplexMap :=
  relativeNaiveCotangentComplexMap.{u, u, u} (Opens.grothendieckTopology X) A B C a b

/-- **Stacks 0E1Y, the canonical map.**  For morphisms `A ⟶ B ⟶ C` of sheaves of commutative
rings on a topological space, the canonical map

`c : NL_{B/A} ⊗_B C ⟶ C(NL_{C/A} ⟶ NL_{C/B})[-1]`

of complexes of sheaves of `C`-modules, lifting the canonical map
`c₁ : NL_{B/A} ⊗_B C ⟶ NL_{C/A}` through the projection of the shifted cone.

All six assertions of the six-term exact sequence of cohomology sheaves are covered: exactness
at `H^{-1}(NL_{C/A})`, at `H^0(NL_{C/A})` and at `H^0(NL_{C/B})` (the final `→ 0`) by
`Stacks.SheafOfModules.exact_spaceJacobiZariskiHomologySequence_negOne`, `_zero` and
`Stacks.SheafOfModules.epi_homologyMap_spaceRelativeNaiveCotangentComplexMap_zero`; exactness at
`H^{-1}(NL_{C/B})` and at `H^0(NL_{B/A} ⊗ C)`, and the connecting map, by
`Stacks.SheafOfModules.exact_spaceJacobiZariskiSixTerm_negOne`, `_zero` and
`Stacks.SheafOfModules.spaceJacobiZariskiConnecting`, which rest on
`Stacks.SheafOfModules.isIso_homologyMap_spaceNaiveCotangentConeMap_zero`. -/
@[stacks 0E1Y "the canonical map NL_{B/A} ⊗ C -> C(g)[-1] to the shifted cone"]
noncomputable abbrev spaceNaiveCotangentConeMap :=
  naiveCotangentConeMap.{u, u, u} (Opens.grothendieckTopology X) A B C a b

/-- **Stacks 0E1Y, the defining property of the canonical map.**  The canonical map `c`
composed with the projection `C(g)[-1] ⟶ NL_{C/A}` of the shifted cone is the canonical map
`c₁ : NL_{B/A} ⊗_B C ⟶ NL_{C/A}`.

The six assertions of the six-term exact sequence drawn from this map are all covered; see the
docstring of `Stacks.SheafOfModules.spaceNaiveCotangentConeMap` for where each one is. -/
@[stacks 0E1Y "the defining property of the canonical map: composed with the cone projection \
it is c_1"]
theorem spaceNaiveCotangentConeMap_comp_pShift :
    spaceNaiveCotangentConeMap A B C a b ≫
        pShift (spaceRelativeNaiveCotangentComplexMap A B C a b) =
      spaceBaseChangeNaiveCotangentMap A B C a b := by
  have h := naiveCotangentConeMap_comp_pShift.{u, u, u} (Opens.grothendieckTopology X) A B C a b
  exact h

/-- The null homotopy of the composite `c₁ ≫ g`, for sheaves of commutative rings on a
topological space. -/
noncomputable abbrev spaceBaseChangeRelativeNullHomotopy :=
  baseChangeRelativeNullHomotopy.{u, u, u} (Opens.grothendieckTopology X) A B C a b

/-- **Stacks 0E1Y, the canonical map.**  The canonical map `c` composed with the degree `-1`
projection `C(g)[-1] ⟶ NL_{C/B}` of the shifted cone is the explicit null homotopy of
`c₁ ≫ g`.  This is the second of the two components out of which Stacks 08RI (2) builds `c`,
and together with `spaceNaiveCotangentConeMap_comp_pShift` it determines `c`.

The six assertions of the six-term exact sequence drawn from this map are all covered; see the
docstring of `Stacks.SheafOfModules.spaceNaiveCotangentConeMap` for where each one is. -/
@[stacks 0E1Y "the second defining property of the canonical map: its degree -1 component is \
the explicit homotopy"]
theorem spaceNaiveCotangentConeMap_comp_snd :
    (CochainComplex.HomComplex.Cochain.ofHom
          (spaceNaiveCotangentConeMap A B C a b)).comp
        ((CochainComplex.mappingCone.snd
            (spaceRelativeNaiveCotangentComplexMap A B C a b)).leftShift (-1) (-1)
          (by omega)) (by omega) =
      CochainComplex.HomComplex.Cochain.ofHomotopy
        (spaceBaseChangeRelativeNullHomotopy A B C a b) := by
  have h := naiveCotangentConeMap_comp_snd.{u, u, u} (Opens.grothendieckTopology X) A B C a b
  exact h

/-! #### The long exact sequence of the cone -/

/-- The short complex `NL_{C/B} ⟶ C(g) ⟶ NL_{C/A}[1]` of the cone of `g`, for sheaves of
commutative rings on a topological space. -/
noncomputable abbrev spaceNaiveCotangentConeShortComplex :=
  naiveCotangentConeShortComplex.{u, u, u} (Opens.grothendieckTopology X) A B C a b

/-- The sequence `0 ⟶ NL_{C/B} ⟶ C(g) ⟶ NL_{C/A}[1] ⟶ 0` is short exact, for sheaves of
commutative rings on a topological space. -/
theorem spaceNaiveCotangentConeShortComplex_shortExact :
    (spaceNaiveCotangentConeShortComplex A B C a b).ShortExact := by
  have h := naiveCotangentConeShortComplex_shortExact.{u, u, u}
    (Opens.grothendieckTopology X) A B C a b
  exact h

/-- The connecting morphism `Hⁱ(NL_{C/A}[1]) ⟶ H^{i+1}(NL_{C/B})` of the long exact sequence of
the cone, for sheaves of commutative rings on a topological space. -/
noncomputable def spaceNaiveCotangentConeConnecting (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    (spaceNaiveCotangentConeShortComplex A B C a b).X₃.homology i ⟶
      (spaceNaiveCotangentConeShortComplex A B C a b).X₁.homology j :=
  naiveCotangentConeConnecting.{u, u, u} (Opens.grothendieckTopology X) A B C a b i j hij

/-- **The canonical map of Stacks 0E1Y on cohomology sheaves, composed with the projection of
the shifted cone**, is the map induced by `c₁ : NL_{B/A} ⊗_B C ⟶ NL_{C/A}`. -/
theorem spaceNaiveCotangentConeMap_homologyMap_comp_pShift (i : ℤ) :
    HomologicalComplex.homologyMap (spaceNaiveCotangentConeMap A B C a b) i ≫
        HomologicalComplex.homologyMap
          (pShift (spaceRelativeNaiveCotangentComplexMap A B C a b)) i =
      HomologicalComplex.homologyMap (spaceBaseChangeNaiveCotangentMap A B C a b) i := by
  have h := homologyMap_naiveCotangentConeMap_comp_pShift.{u, u, u}
    (Opens.grothendieckTopology X) A B C a b i
  exact h

/-- The connecting morphism `Hⁱ(NL_{C/B}) ⟶ H^{i+1}(C(g)[-1])` of the cone, for sheaves of
commutative rings on a topological space.  For `i = -1` its target becomes
`H⁰(NL_{B/A} ⊗_B C)` once `H⁰(c)` is known to be an isomorphism, so this is the connecting arrow
of the six-term sequence of Stacks 0E1Y read before that comparison. -/
noncomputable abbrev spaceNaiveCotangentConeHomologyConnecting (i j : ℤ) (hij : -1 + j = i) :=
  naiveCotangentConeHomologyConnecting.{u, u, u} (Opens.grothendieckTopology X) A B C a b i j hij

/-- **Exactness of `Hⁱ(NL_{C/A}) ⟶ Hⁱ(NL_{C/B}) --∂--> H^{i+1}(C(g)[-1])`**, for sheaves of
commutative rings on a topological space.  For `i = -1` this is the exactness of the six-term
sequence of Stacks 0E1Y at `H^{-1}(NL_{C/B})`, read before the comparison of
`H⁰(NL_{B/A} ⊗_B C)` with `H⁰(C(g)[-1])` along the canonical map. -/
theorem spaceNaiveCotangentCone_homology_exact_target (i j : ℤ) (hij : -1 + j = i) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (spaceRelativeNaiveCotangentComplexMap A B C a b) i)
      (spaceNaiveCotangentConeHomologyConnecting A B C a b i j hij)
      (CochainComplex.homologyMap_comp_coneHomologyConnecting
        (spaceRelativeNaiveCotangentComplexMap A B C a b) i j hij)).Exact := by
  have h := naiveCotangentCone_homology_exact_target.{u, u, u}
    (Opens.grothendieckTopology X) A B C a b i j hij
  exact h

/-- **Exactness of `Hⁱ(NL_{C/B}) --∂--> Hʲ(C(g)[-1]) ⟶ Hʲ(NL_{C/A})`**, for sheaves of
commutative rings on a topological space.  For `i = -1`, so `j = 0`, this is the exactness of the
six-term sequence of Stacks 0E1Y at `H⁰(NL_{B/A} ⊗_B C)`, read before the comparison of that
term with `H⁰(C(g)[-1])` along the canonical map. -/
theorem spaceNaiveCotangentCone_homology_exact_cone (i j : ℤ) (hij : -1 + j = i) :
    (ShortComplex.mk
      (spaceNaiveCotangentConeHomologyConnecting A B C a b i j hij)
      (HomologicalComplex.homologyMap
        (pShift (spaceRelativeNaiveCotangentComplexMap A B C a b)) j)
      (CochainComplex.coneHomologyConnecting_comp_homologyMap_pShift
        (spaceRelativeNaiveCotangentComplexMap A B C a b) i j hij)).Exact := by
  have h := naiveCotangentCone_homology_exact_cone.{u, u, u}
    (Opens.grothendieckTopology X) A B C a b i j hij
  exact h

/-- **Exactness of `Hʲ(C(g)[-1]) ⟶ Hʲ(NL_{C/A}) ⟶ Hʲ(NL_{C/B})`**, for sheaves of commutative
rings on a topological space.  For `j = 0` this is the exactness of the six-term sequence of
Stacks 0E1Y at `H⁰(NL_{C/A})` and for `j = -1` its exactness at `H^{-1}(NL_{C/A})`, in both cases
read before the comparison of `H^j(NL_{B/A} ⊗_B C)` with `H^j(C(g)[-1])` along the canonical
map. -/
theorem spaceNaiveCotangentCone_homology_exact_source (i j : ℤ) (hij : -1 + j = i) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap
        (pShift (spaceRelativeNaiveCotangentComplexMap A B C a b)) j)
      (HomologicalComplex.homologyMap (spaceRelativeNaiveCotangentComplexMap A B C a b) j)
      (CochainComplex.homologyMap_pShift_comp_homologyMap
        (spaceRelativeNaiveCotangentComplexMap A B C a b) i j hij)).Exact := by
  have h := naiveCotangentCone_homology_exact_source.{u, u, u}
    (Opens.grothendieckTopology X) A B C a b i j hij
  exact h

end Space

/-! ### Ringed spaces -/

section RingedSpace

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The structure morphism `h⁻¹O_T ⟶ O_S` of a morphism `h : S ⟶ T` of ringed spaces: the
adjoint transpose of the comparison morphism `O_T ⟶ h_*O_S`. -/
noncomputable def ringedSpaceStructureMap {S T : RingedSpace.{u, u}} (h : S ⟶ T) :
    (TopCat.Sheaf.pullback CommRingCat.{u} h.hom.base).obj T.sheaf ⟶ S.sheaf :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} h.hom.base).homEquiv
    T.sheaf S.sheaf).symm ⟨h.hom.c⟩

/-- The inverse image `g⁻¹O_Z` of the structure sheaf of `Z` on `Y`. -/
noncomputable abbrev inverseImageBaseRingOnMiddle :=
  (TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj Z.sheaf

/-- The inverse image `f⁻¹O_Y` of the structure sheaf of `Y` on `X`. -/
noncomputable abbrev inverseImageMiddleRing :=
  (TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj Y.sheaf

/-- The inverse image `(g ∘ f)⁻¹O_Z` of the structure sheaf of `Z` on `X`, written as the
inverse image along `f` of the inverse image along `g`. -/
noncomputable abbrev inverseImageBaseRing :=
  (TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj (inverseImageBaseRingOnMiddle g)

/-- The first morphism `(g ∘ f)⁻¹O_Z ⟶ f⁻¹O_Y` of the sequence of sheaves of rings on `X`: the
inverse image along `f` of the structure morphism of `g`. -/
noncomputable abbrev inverseImageFirstRingMap :=
  (TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).map (ringedSpaceStructureMap g)

/-- Extension of scalars from `f⁻¹O_Y` to `O_X`, applied termwise to complexes. -/
noncomputable abbrev inverseImageExtendScalarsComplexes :=
  towerExtendScalarsComplexes.{u, u, u} (Opens.grothendieckTopology (X : TopCat))
    (inverseImageMiddleRing f) X.sheaf (ringedSpaceStructureMap f)

/-- The pullback `f^*NL_{Y/Z}`: the inverse image along `f` of the naive cotangent complex of
`O_Y` over `g⁻¹O_Z`, with scalars extended from `f⁻¹O_Y` to `O_X`. -/
noncomputable abbrev pulledNaiveCotangentComplex :=
  (inverseImageExtendScalarsComplexes f).obj
    (((_root_.SheafOfModules.pullback.{u}
        (inverseImageRingHom f.hom.base Y.sheaf)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
      (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology (Y : TopCat))
        (inverseImageBaseRingOnMiddle g) Y.sheaf (ringedSpaceStructureMap g)))

/-- **Stacks 08TM for a morphism of ringed spaces.**  The pullback `f^*NL_{Y/Z}` is the base
change to `O_X` of the naive cotangent complex of `f⁻¹O_Y` over `(g ∘ f)⁻¹O_Z`: the
inverse-image theorem identifies the two complexes of `f⁻¹O_Y`-modules, and extension of
scalars carries that identification to `O_X`. -/
noncomputable def pulledNaiveCotangentComparison :
    pulledNaiveCotangentComplex f g ≅
      spaceBaseChangeNaiveCotangentComplex (inverseImageBaseRing f g)
        (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g)
        (ringedSpaceStructureMap f) :=
  (inverseImageExtendScalarsComplexes f).mapIso
    (naiveCotangentComplexInverseImageIso f.hom.base (inverseImageBaseRingOnMiddle g) Y.sheaf
      (ringedSpaceStructureMap g))

/-- **Stacks 0E1Z, the canonical map.**  For composable morphisms of ringed spaces
`f : X ⟶ Y` and `g : Y ⟶ Z`, the canonical map

`f^*NL_{Y/Z} ⟶ C(NL_{X/Z} ⟶ NL_{X/Y})[-1]`

of complexes of `O_X`-modules: the canonical map of Stacks 0E1Y for the sheaves of rings
`(g ∘ f)⁻¹O_Z ⟶ f⁻¹O_Y ⟶ O_X` on `X`, precomposed with the identification of `f^*NL_{Y/Z}`
with the base change of `NL_{f⁻¹O_Y/(g ∘ f)⁻¹O_Z}`.

All six assertions of the six-term exact sequence of cohomology sheaves are covered: exactness
at `H^{-1}(NL_{X/Z})`, at `H^0(NL_{X/Z})` and at `H^0(NL_{X/Y})` (the final `→ 0`) by
`Stacks.SheafOfModules.exact_ringedSpaceJacobiZariskiHomologySequence_negOne`, `_zero` and
`Stacks.SheafOfModules.epi_homologyMap_ringedSpaceRelativeNaiveCotangentComplexMap_zero`;
exactness at `H^{-1}(NL_{X/Y})` and at `H^0(f^*NL_{Y/Z})`, and the connecting map, by
`Stacks.SheafOfModules.exact_ringedSpaceJacobiZariskiSixTerm_negOne`, `_zero` and
`Stacks.SheafOfModules.ringedSpaceJacobiZariskiConnecting`, which rest on
`Stacks.SheafOfModules.isIso_homologyMap_ringedSpaceNaiveCotangentConeMap_zero`. -/
@[stacks 0E1Z "the canonical map f^*NL_{Y/Z} -> C(NL_{X/Z} -> NL_{X/Y})[-1] to the shifted cone"]
noncomputable def ringedSpaceNaiveCotangentConeMap :
    pulledNaiveCotangentComplex f g ⟶
      (CategoryTheory.shiftFunctor
          (CochainComplex (_root_.SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology (X : TopCat))
              X.sheaf)) ℤ) (-1 : ℤ)).obj
        (CochainComplex.mappingCone (spaceRelativeNaiveCotangentComplexMap
          (inverseImageBaseRing f g) (inverseImageMiddleRing f) X.sheaf
          (inverseImageFirstRingMap f g) (ringedSpaceStructureMap f))) :=
  (pulledNaiveCotangentComparison f g).hom ≫
    spaceNaiveCotangentConeMap (inverseImageBaseRing f g) (inverseImageMiddleRing f) X.sheaf
      (inverseImageFirstRingMap f g) (ringedSpaceStructureMap f)

/-- **Stacks 0E1Z, the canonical map.**  The canonical map
`f^*NL_{Y/Z} ⟶ C(NL_{X/Z} ⟶ NL_{X/Y})[-1]`, composed with the projection of the shifted cone
onto `NL_{X/Z}`, is the canonical map `f^*NL_{Y/Z} ⟶ NL_{X/Z}`.

The six assertions of the six-term exact sequence drawn from this map are all covered; see the
docstring of `Stacks.SheafOfModules.ringedSpaceNaiveCotangentConeMap` for where each one is. -/
@[stacks 0E1Z "the defining property of the canonical map: composed with the cone projection \
it is the map f^*NL_{Y/Z} -> NL_{X/Z}"]
theorem ringedSpaceNaiveCotangentConeMap_comp_pShift :
    ringedSpaceNaiveCotangentConeMap f g ≫
        pShift (spaceRelativeNaiveCotangentComplexMap (inverseImageBaseRing f g)
          (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g)
          (ringedSpaceStructureMap f)) =
      (pulledNaiveCotangentComparison f g).hom ≫
        spaceBaseChangeNaiveCotangentMap (inverseImageBaseRing f g)
          (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g)
          (ringedSpaceStructureMap f) :=
  (Category.assoc _ _ _).trans
    (congrArg (fun t ↦ (pulledNaiveCotangentComparison f g).hom ≫ t)
      (spaceNaiveCotangentConeMap_comp_pShift (inverseImageBaseRing f g)
        (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g)
        (ringedSpaceStructureMap f)))

/-- The null homotopy of `c₁ ≫ g` for the tower `(g ∘ f)⁻¹O_Z ⟶ f⁻¹O_Y ⟶ O_X` attached to a
pair of composable morphisms of ringed spaces. -/
noncomputable abbrev ringedSpaceBaseChangeRelativeNullHomotopy :=
  spaceBaseChangeRelativeNullHomotopy (inverseImageBaseRing f g) (inverseImageMiddleRing f)
    X.sheaf (inverseImageFirstRingMap f g) (ringedSpaceStructureMap f)

/-- **Stacks 0E1Z, the canonical map.**  The canonical map
`f^*NL_{Y/Z} ⟶ C(NL_{X/Z} ⟶ NL_{X/Y})[-1]`, composed with the degree `-1` projection of the
shifted cone onto `NL_{X/Y}`, is the identification `f^*NL_{Y/Z} ≅ NL_{f⁻¹O_Y/(g ∘ f)⁻¹O_Z} ⊗ O_X`
followed by the explicit null homotopy of the proof of Stacks 0E1Y for the tower
`(g ∘ f)⁻¹O_Z ⟶ f⁻¹O_Y ⟶ O_X`.  Together with
`ringedSpaceNaiveCotangentConeMap_comp_pShift` this determines the canonical map.

The six assertions of the six-term exact sequence drawn from this map are all covered; see the
docstring of `Stacks.SheafOfModules.ringedSpaceNaiveCotangentConeMap` for where each one is. -/
@[stacks 0E1Z "the second defining property of the canonical map: its degree -1 component is \
the explicit homotopy"]
theorem ringedSpaceNaiveCotangentConeMap_comp_snd :
    (CochainComplex.HomComplex.Cochain.ofHom
          (ringedSpaceNaiveCotangentConeMap f g)).comp
        ((CochainComplex.mappingCone.snd
            (spaceRelativeNaiveCotangentComplexMap (inverseImageBaseRing f g)
              (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g)
              (ringedSpaceStructureMap f))).leftShift (-1) (-1) (by omega)) (by omega) =
      (CochainComplex.HomComplex.Cochain.ofHom
            (pulledNaiveCotangentComparison f g).hom).comp
        (CochainComplex.HomComplex.Cochain.ofHomotopy
          (ringedSpaceBaseChangeRelativeNullHomotopy f g)) (zero_add (-1)) := by
  rw [ringedSpaceNaiveCotangentConeMap, CochainComplex.HomComplex.Cochain.ofHom_comp,
    CochainComplex.HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain]
  exact congrArg (fun z ↦ (CochainComplex.HomComplex.Cochain.ofHom
      (pulledNaiveCotangentComparison f g).hom).comp z (zero_add (-1)))
    (spaceNaiveCotangentConeMap_comp_snd (inverseImageBaseRing f g) (inverseImageMiddleRing f)
      X.sheaf (inverseImageFirstRingMap f g) (ringedSpaceStructureMap f))

/-! #### The long exact sequence of the cone -/

/-- The short complex `NL_{X/Y} ⟶ C(NL_{X/Z} ⟶ NL_{X/Y}) ⟶ NL_{X/Z}[1]` of the cone, for a pair
of composable morphisms of ringed spaces. -/
noncomputable abbrev ringedSpaceNaiveCotangentConeShortComplex :=
  spaceNaiveCotangentConeShortComplex (inverseImageBaseRing f g) (inverseImageMiddleRing f)
    X.sheaf (inverseImageFirstRingMap f g) (ringedSpaceStructureMap f)

/-- The sequence `0 ⟶ NL_{X/Y} ⟶ C(NL_{X/Z} ⟶ NL_{X/Y}) ⟶ NL_{X/Z}[1] ⟶ 0` is short exact, for
a pair of composable morphisms of ringed spaces. -/
theorem ringedSpaceNaiveCotangentConeShortComplex_shortExact :
    (ringedSpaceNaiveCotangentConeShortComplex f g).ShortExact :=
  spaceNaiveCotangentConeShortComplex_shortExact (inverseImageBaseRing f g)
    (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g)
    (ringedSpaceStructureMap f)

/-- The connecting morphism `Hⁱ(NL_{X/Z}[1]) ⟶ H^{i+1}(NL_{X/Y})` of the long exact sequence of
the cone, for a pair of composable morphisms of ringed spaces. -/
noncomputable def ringedSpaceNaiveCotangentConeConnecting (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    (ringedSpaceNaiveCotangentConeShortComplex f g).X₃.homology i ⟶
      (ringedSpaceNaiveCotangentConeShortComplex f g).X₁.homology j :=
  spaceNaiveCotangentConeConnecting (inverseImageBaseRing f g) (inverseImageMiddleRing f)
    X.sheaf (inverseImageFirstRingMap f g) (ringedSpaceStructureMap f) i j hij

/-- The connecting morphism `Hⁱ(NL_{X/Y}) ⟶ H^{i+1}(C(NL_{X/Z} ⟶ NL_{X/Y})[-1])` of the cone, for
a pair of composable morphisms of ringed spaces.  For `i = -1` its target becomes
`H⁰(f^*NL_{Y/Z})` once `H⁰` of the canonical map is known to be an isomorphism, so this is the
connecting arrow of the six-term sequence of Stacks 0E1Z read before that comparison. -/
noncomputable abbrev ringedSpaceNaiveCotangentConeHomologyConnecting (i j : ℤ)
    (hij : -1 + j = i) :=
  spaceNaiveCotangentConeHomologyConnecting (inverseImageBaseRing f g)
    (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g)
    (ringedSpaceStructureMap f) i j hij

/-- **Exactness of `Hⁱ(NL_{X/Z}) ⟶ Hⁱ(NL_{X/Y}) --∂--> H^{i+1}(C[-1])`**, for a pair of
composable morphisms of ringed spaces.  For `i = -1` this is the exactness of the six-term
sequence of Stacks 0E1Z at `H^{-1}(NL_{X/Y})`, read before the comparison of
`H⁰(f^*NL_{Y/Z})` with `H⁰(C[-1])` along the canonical map. -/
theorem ringedSpaceNaiveCotangentCone_homology_exact_target (i j : ℤ) (hij : -1 + j = i) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (spaceRelativeNaiveCotangentComplexMap
        (inverseImageBaseRing f g) (inverseImageMiddleRing f) X.sheaf
        (inverseImageFirstRingMap f g) (ringedSpaceStructureMap f)) i)
      (ringedSpaceNaiveCotangentConeHomologyConnecting f g i j hij)
      (CochainComplex.homologyMap_comp_coneHomologyConnecting
        (spaceRelativeNaiveCotangentComplexMap (inverseImageBaseRing f g)
          (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g)
          (ringedSpaceStructureMap f)) i j hij)).Exact :=
  spaceNaiveCotangentCone_homology_exact_target (inverseImageBaseRing f g)
    (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g)
    (ringedSpaceStructureMap f) i j hij

/-- **Exactness of `Hⁱ(NL_{X/Y}) --∂--> Hʲ(C[-1]) ⟶ Hʲ(NL_{X/Z})`**, for a pair of composable
morphisms of ringed spaces.  For `i = -1`, so `j = 0`, this is the exactness of the six-term
sequence of Stacks 0E1Z at `H⁰(f^*NL_{Y/Z})`, read before the comparison of that term with
`H⁰(C[-1])` along the canonical map. -/
theorem ringedSpaceNaiveCotangentCone_homology_exact_cone (i j : ℤ) (hij : -1 + j = i) :
    (ShortComplex.mk
      (ringedSpaceNaiveCotangentConeHomologyConnecting f g i j hij)
      (HomologicalComplex.homologyMap (pShift (spaceRelativeNaiveCotangentComplexMap
        (inverseImageBaseRing f g) (inverseImageMiddleRing f) X.sheaf
        (inverseImageFirstRingMap f g) (ringedSpaceStructureMap f))) j)
      (CochainComplex.coneHomologyConnecting_comp_homologyMap_pShift
        (spaceRelativeNaiveCotangentComplexMap (inverseImageBaseRing f g)
          (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g)
          (ringedSpaceStructureMap f)) i j hij)).Exact :=
  spaceNaiveCotangentCone_homology_exact_cone (inverseImageBaseRing f g)
    (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g)
    (ringedSpaceStructureMap f) i j hij

/-- **Exactness of `Hʲ(C[-1]) ⟶ Hʲ(NL_{X/Z}) ⟶ Hʲ(NL_{X/Y})`**, for a pair of composable
morphisms of ringed spaces.  For `j = 0` this is the exactness of the six-term sequence of
Stacks 0E1Z at `H⁰(NL_{X/Z})` and for `j = -1` its exactness at `H^{-1}(NL_{X/Z})`, in both cases
read before the comparison of `H^j(f^*NL_{Y/Z})` with `H^j(C[-1])` along the canonical map. -/
theorem ringedSpaceNaiveCotangentCone_homology_exact_source (i j : ℤ) (hij : -1 + j = i) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (pShift (spaceRelativeNaiveCotangentComplexMap
        (inverseImageBaseRing f g) (inverseImageMiddleRing f) X.sheaf
        (inverseImageFirstRingMap f g) (ringedSpaceStructureMap f))) j)
      (HomologicalComplex.homologyMap (spaceRelativeNaiveCotangentComplexMap
        (inverseImageBaseRing f g) (inverseImageMiddleRing f) X.sheaf
        (inverseImageFirstRingMap f g) (ringedSpaceStructureMap f)) j)
      (CochainComplex.homologyMap_pShift_comp_homologyMap
        (spaceRelativeNaiveCotangentComplexMap (inverseImageBaseRing f g)
          (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g)
          (ringedSpaceStructureMap f)) i j hij)).Exact :=
  spaceNaiveCotangentCone_homology_exact_source (inverseImageBaseRing f g)
    (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g)
    (ringedSpaceStructureMap f) i j hij

end RingedSpace

end Stacks.SheafOfModules

end
