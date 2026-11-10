module

public import StacksFrontier.AlgebraicGeometry.DeRham.ExteriorGradedPiece.Construction
public import StacksFrontier.AlgebraicGeometry.DeRham.ExteriorGradedPiece.SplittingIndependence
public import StacksFrontier.AlgebraicGeometry.DeRham.ExteriorGradedPiece.KunnethRetraction
public import StacksFrontier.AlgebraicGeometry.DeRham.ExteriorGradedPiece.RelativeDifferentials

/-!
# The graded pieces of the wedge filtration of an exterior power

Let `X` be a topological space, `O♯` a sheaf of commutative rings on it and `iF : F ⟶ H` a
morphism of sheaves of `O♯`-modules.
`StacksFrontier.AlgebraicGeometry.DeRham.ExteriorPowerFiltration` filters `⋀ⁿH` by the images

`F^k⋀ⁿH = Im (⋀^kF ⊗_{O♯} ⋀^{n-k}H ⟶ ⋀ⁿH)`

of the wedge-product morphisms. **This file constructs the successive quotients of that
filtration and the canonical morphism onto them**, which is what the identification of the graded
pieces of [Stacks, Section 0FMK] needs and what the repository did not have.

Writing the total degree as `n = k + 1 + m`, the `k`-th graded piece is realized as a subobject
of `⋀ⁿH/F^{k+1}⋀ⁿH`: the composite

`⋀^kF ⊗ ⋀^{1+m}H ⟶ ⋀ⁿH ⟶ ⋀ⁿH/F^{k+1}⋀ⁿH`

has image `F^k⋀ⁿH/F^{k+1}⋀ⁿH`, because the first morphism has image `F^k⋀ⁿH` and precomposing
with the epimorphism onto an image does not change an image. The graded piece is therefore a
subobject of a quotient of `⋀ⁿH` rather than a quotient of a subobject, which is what makes the
statements of `StacksFrontier.AlgebraicGeometry.DeRham.UnipotentExteriorPowerModStep` — all of them
phrased against `cokernel (⋀^{k+1}F ⊗ ⋀^mH ⟶ ⋀ⁿH)` — apply to it with no comparison of
quotients.

Two facts about the canonical epimorphism `⋀^kF ⊗ ⋀^{1+m}H ↠ gr^k⋀ⁿH` are then proved, and
together they say that the local Künneth decompositions of Section 0FMK agree on the graded
piece:

* it kills `⋀^kF ⊗ F^1⋀^{1+m}H`, the first step of the wedge filtration of the second factor, so
  it only depends on the second factor modulo the forms pulled back from `F`. Because the tensor
  product of sheaves of modules preserves all colimits in each variable ([Stacks, Tag 05NB]), it
  therefore **descends, with no splitting and nothing assumed, to a morphism**
  `⋀^kF ⊗ (⋀^{1+m}H/F^1⋀^{1+m}H) ⟶ gr^k⋀ⁿH`;
* for a short exact sequence `0 ⟶ T.X₁ ⟶ T.X₂ ⟶ T.X₃ ⟶ 0` of sheaves of modules **the Künneth
  comparison `⋀^kT.X₁ ⊗ ⋀^{1+m}T.X₃ ⟶ gr^k⋀ⁿT.X₂` attached to a splitting does not depend on the
  splitting.** Two splittings differ by the unipotent transition automorphism `θ` of `T.X₂`
  (`CategoryTheory.ShortComplex.Splitting.transition`), the two comparisons differ by
  postcomposition with `⋀ⁿθ` (`SheafOfModules.prodWedgeHom_comp_pieceMap`), and `⋀ⁿθ` is the
  identity on `F^k⋀ⁿT.X₂` modulo `F^{k+1}⋀ⁿT.X₂`
  (`SheafOfModules.prodWedgeHom_comp_pieceMap_transition_sub_id_comp_cokernelπ`).

The last section instantiates all of this at the transitivity sequence
`0 ⟶ f^*Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y} ⟶ 0` of a morphism of schemes, where it gives
`gr^kΩ^n_{X/S}` and the splitting-independent comparison

`⋀^k(f^*Ω_{Y/S})|_U ⊗ ⋀^{n-k}(Ω_{X/Y})|_U ⟶ gr^k(Ω^n_{X/S}|_U)`

over an open `U` of `X` on which the sequence splits — one for every splitting, all equal.

## Main definitions

* `SheafOfModules.exteriorGradedHom`: the canonical morphism
  `⋀^kF ⊗ ⋀^{1+m}H ⟶ ⋀ⁿH/F^{k+1}⋀ⁿH`.
* `SheafOfModules.exteriorGraded`: **`gr^k⋀ⁿH`**, the `k`-th graded piece of the wedge
  filtration of `⋀ⁿH`, as its image.
* `SheafOfModules.toExteriorGraded`: the canonical epimorphism `⋀^kF ⊗ ⋀^{1+m}H ↠ gr^k⋀ⁿH`.
* `SheafOfModules.exteriorGradedDescent`: **the canonical splitting-free comparison**
  `⋀^kF ⊗ (⋀^{1+m}H/F^1⋀^{1+m}H) ⟶ gr^k⋀ⁿH`.
* `SheafOfModules.splittingToExteriorGraded`: the Künneth comparison
  `⋀^kT.X₁ ⊗ ⋀^{1+m}T.X₃ ⟶ gr^k⋀ⁿT.X₂` attached to a splitting of a short complex.
* `SheafOfModules.exteriorGradedQuotientComparison`: **the splitting-free comparison in the
  shape Section 0FMK states it**, `⋀^kT.X₁ ⊗ ⋀^{m+1}T.X₃ ⟶ gr^k⋀ⁿT.X₂`, for a short exact
  sequence.
* `SheafOfModules.exteriorGradedQuotientHom`: that same comparison read into
  `⋀ⁿT.X₂/F^{k+1}⋀ⁿT.X₂` instead of into the graded piece, where no image subobject appears —
  the morphism the localization of Section 0FMK should be carried out at.
* `SheafOfModules.exteriorKunnethRetractionDescent`: **the retraction `ρ_k` of the Künneth
  decomposition, descended** to `⋀ⁿT.X₂/F^{k+1}⋀ⁿT.X₂`.
* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsExteriorGraded`: **`gr^kΩ^n_{X/S}`**, the
  instance at the transitivity sequence,
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsExteriorGradedComparison`: the comparison
  `⋀^k(f^*Ω_{Y/S}) ⊗ Ω^{m+1}_{X/Y} ⟶ gr^kΩ^n_{X/S}` there, and
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsExteriorGradedComparisonRestrict`: the same
  over an open on which the transitivity sequence splits.

## Main results

* `SheafOfModules.imageSubobject_exteriorGradedHom_eq`: **the graded piece is `F^k/F^{k+1}`** —
  the image of the canonical morphism is the image of `F^k⋀ⁿH` in `⋀ⁿH/F^{k+1}⋀ⁿH`.
* `SheafOfModules.exteriorImageFiltration_eq_imageSubobject`: the step of
  `SheafOfModules.exteriorImageFiltration` in the spelling the graded piece is built from.
* `SheafOfModules.epi_toExteriorGraded`: the canonical morphism onto the graded piece is an
  epimorphism.
* `SheafOfModules.whiskerLeft_prodWedgeHom_comp_toExteriorGraded` and
  `SheafOfModules.tensorLeftFunctor_map_prodWedgeHom_comp_toExteriorGraded`: **it kills the first
  step of the wedge filtration of the second factor**, which is what makes it descend.
* `SheafOfModules.tensorLeftFunctor_map_cokernelπ_comp_exteriorGradedDescent`: the defining
  equation of the splitting-free comparison out of the quotient by the first step.
* `SheafOfModules.GradedAlgebra.generatorMul_eq_tensorSheafBifunctor_map_comp_mulSheaf` and
  `SheafOfModules.generatorMul_eq_generatorTensorId_comp_prodWedgeHom`: **the first morphism of
  the presentation of [Stacks, Tag 01CJ] is the wedge morphism**, precomposed with the degree-one
  generator.
* `SheafOfModules.relComplex_f_eq` and
  `SheafOfModules.tensorLeftFunctor_map_relComplex_f_comp_toExteriorGraded`: that relation, and
  the fact that the canonical morphism onto the graded piece kills it after tensoring.
* `SheafOfModules.tensorLeftFunctor_map_extHom_comp_exteriorGradedQuotientComparison`: the
  defining equation of the comparison in Section 0FMK's shape.
* `SheafOfModules.tensorLeftFunctor_map_extHom_comp_exteriorGradedQuotientHom`,
  `SheafOfModules.mono_exteriorGradedQuotientComparison_of_mono_quotientHom` and
  `SheafOfModules.mono_exteriorGradedQuotientHom_of_splitting`: the same defining equation for the
  quotient-level comparison, and monomorphy passing between the two morphisms in both directions
  — the comparison onto the graded piece is a monomorphism as soon as the quotient-level form is,
  and the quotient-level form is one as soon as the sequence splits.
* `SheafOfModules.whiskerLeft_pieceMap_comp_exteriorGradedHom`: that comparison, composed into
  the quotient by the next step of the filtration.
* `SheafOfModules.prodWedgeHom_comp_pieceMap_transition_comp_exteriorGradedHom`: the exterior
  power of the transition automorphism of two splittings acts trivially on the graded piece.
* `SheafOfModules.prodWedgeHom_splitting_comp_cokernelπ_eq` and
  `SheafOfModules.splittingToExteriorGraded_eq`: **the comparison onto the graded piece does not
  depend on the splitting**, in the quotient `⋀ⁿT.X₂/F^{k+1}⋀ⁿT.X₂` and in the graded piece
  itself.
* `SheafOfModules.exteriorGradedQuotientComparison_eq_of_splitting`: **the splitting-free
  comparison is the Künneth comparison of any splitting.** With the previous item this is the
  gluing of [Stacks, Section 0FMK] in exact form.
* `SheafOfModules.epi_exteriorGradedQuotientComparison` and
  `AlgebraicGeometry.Scheme.Hom.epi_relativeDifferentialsExteriorGradedComparison`: **the
  comparison is an epimorphism** — the surjectivity half of Section 0FMK's isomorphism claim.
* `SheafOfModules.prodWedgeHomOfEq_eq_whiskerLeft_pieceMap_comp` and
  `SheafOfModules.imageSubobject_prodWedgeHomOfEq_splitting_le`: **the Künneth summand of weight
  `p` lands in the `p`-th step of the wedge filtration** — one of the two inclusions of the
  weight-matching the injectivity half needs.
* `SheafOfModules.exteriorKunnethRetraction`: **the retraction `ρ_p`** of `⋀ⁿT.X₂` onto the
  weight-`p` Künneth summand, with
  `SheafOfModules.prodWedgeHomOfEq_comp_exteriorKunnethRetraction` and
  `SheafOfModules.prodWedgeHomOfEq_comp_exteriorKunnethRetraction_of_ne`: it retracts that
  summand and kills every other one.
* `SheafOfModules.prodWedgeHom_comp_exteriorKunnethRetraction`: **the retraction `ρ_k` kills the
  `(k+1)`-st step of the wedge filtration** — the identity (★) the injectivity rests on — and
  `SheafOfModules.exteriorKunnethRetractionDescent`: the retraction it therefore descends to
  `⋀ⁿT.X₂/F^{k+1}⋀ⁿT.X₂`.
* `SheafOfModules.mono_splittingToExteriorGraded`: **the Künneth comparison onto the graded piece
  is a split monomorphism**, and
  `SheafOfModules.exteriorGradedQuotientComparison_eq_whiskerLeft_eqToHom_comp`: the comparison in
  Section 0FMK's shape is that Künneth comparison, up to the transport of the complementary
  degree.
* `SheafOfModules.mono_exteriorGradedQuotientComparison_of_splitting` and
  `SheafOfModules.isIso_exteriorGradedQuotientComparison_of_splitting`: **the comparison is a
  monomorphism, hence an isomorphism, as soon as the sequence splits** — Section 0FMK's claim,
  with the splitting entering only through the monomorphy.
* `AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialsExteriorGradedComparisonRestrict`:
  **`⋀^k(f^*Ω_{Y/S})|_U ⊗ Ω^{m+1}_{X/Y}|_U ≅ gr^k(Ω^n_{X/S}|_U)`** over an open `U` of `X` on which
  the transitivity sequence splits.
* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsSplittingToExteriorGraded_eq`: the
  splitting-independence at the transitivity sequence of a morphism of schemes, which is the form
  [Stacks, Section 0FMK] uses to glue the local Künneth decompositions.

## Implementation notes

**The total degree is written `k + 1 + m`.** Every statement of
`StacksFrontier.AlgebraicGeometry.DeRham.UnipotentExteriorPowerModStep` is written at that spelling,
with the complementary degree `1 + m`, because it is the one in which the first-step statement
and the associativity square of the wedge product are simultaneously available with a single
transport of the total degree; the graded piece is defined at the same spelling so that those
statements apply to it verbatim. The complementary degree is therefore always `≥ 1`, and the
case `n = k` is not covered.

That case is not a degeneration with nothing to say. The quotient it
is taken in is the whole of `⋀^kH`, since `F^{k+1}⋀^kH = ⊥`
(`SheafOfModules.exteriorImageFiltration_eq_bot`); but the graded piece is not that quotient, it
is `F^k⋀^kH`, the image of `⋀^kF ⊗ ⋀^0H ⟶ ⋀^kH`
(`SheafOfModules.exteriorImageFiltration_of_le` at `k = n`, which does reach the cut), and that
image is all of `⋀^kH` only when the wedge-product morphism is an epimorphism, which for `k ≥ 1`
it is not. So both sides of Section 0FMK's identification are nonzero there, and the degree-`k`
comparison is a construction of its own rather than an instance of the one below. What it needs
is that `⋀^kF ⊗ ⋀^0H ⟶ ⋀^kH` is a *monomorphism*, so that the image is its source.
**That is now proved**, and not by the localization of
`StacksFrontier.AlgebraicGeometry.Modules.ExteriorGradedOpenSubspaceAlgebras`, whose every
comparison result is hard-wired at the complementary degree `1 + m` and so does not apply at the
cut: `SheafOfModules.exteriorKunnethRetraction` is stated for every `p + q = n`, so `q = 0` is in
range and the morphism along a splitting is a split monomorphism there, `⋀^0` of the splitting's
section is invertible whatever the section is
(`SheafOfModules.isIso_exteriorPieceMap_of_eq_zero`), and monomorphy is local —
`SheafOfModules.mono_prodWedgeHom_id_right_of_locally_split` of
`StacksFrontier.AlgebraicGeometry.Modules.WedgeDegreeZeroMono` is the globalization, and
`AlgebraicGeometry.Scheme.Hom.mono_relativeDifferentialsProdWedgeHom_of_eq_zero` its instance at
the transitivity sequence of a smooth morphism. What the degree-`k` comparison of
Section 0FMK still owes is the chain from that monomorphy to the two sides of its
identification.

**The abelian and monoidal structures are the ones the inputs are stated at.** Both are turned
on by `attribute [local instance]` rather than restated, so that the cokernel, the image
subobject and the whiskering below are the very ones
`StacksFrontier.AlgebraicGeometry.DeRham.UnipotentExteriorPowerModStep` and
`StacksFrontier.AlgebraicGeometry.DeRham.ExteriorPowerFiltration` are elaborated against; searching
for either from `SheafOfModules.instAbelian` exceeds the default instance-synthesis budget at
these binders.

**The comparison is an isomorphism as soon as the sequence splits.** It is an epimorphism with
nothing assumed beyond short exactness (`SheafOfModules.epi_exteriorGradedQuotientComparison`),
and `SheafOfModules.mono_exteriorGradedQuotientComparison_of_splitting` makes it a monomorphism
given a splitting, so
`SheafOfModules.isIso_exteriorGradedQuotientComparison_of_splitting` — sheaves of modules being a
balanced category (`Stacks.SheafOfModules.TopWedge.balanced_sheafOfModules`). The monomorphy runs
through the *retraction* `ρ_k = SheafOfModules.exteriorKunnethRetraction`, the inverse of the
Künneth isomorphism followed by the projection onto the `(k, 1+m)` summand: `ρ_k` kills
`F^{k+1}⋀ⁿT.X₂` (this is (★), `SheafOfModules.prodWedgeHom_comp_exteriorKunnethRetraction`), hence
descends to `⋀ⁿT.X₂/F^{k+1}⋀ⁿT.X₂`
(`SheafOfModules.exteriorKunnethRetractionDescent`), and the descent retracts the Künneth
comparison onto the graded piece
(`SheafOfModules.splittingToExteriorGraded_comp_arrow_comp_exteriorKunnethRetractionDescent`),
which therefore is a split monomorphism
(`SheafOfModules.mono_splittingToExteriorGraded`). The comparison of Section 0FMK's shape differs
from that Künneth comparison only by the transport between the two spellings of the complementary
degree, whiskered with `⋀^kT.X₁`
(`SheafOfModules.exteriorGradedQuotientComparison_eq_whiskerLeft_eqToHom_comp`).

**(★) is proved by decomposing the second factor.** `⋀^mT.X₂` is written as the Künneth coproduct
`∐ SheafOfModules.exteriorPowerProdSummand`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ExteriorPowerProdSheaf.lean:886`), which is a
coproduct over the antidiagonal — finite by `Stacks.Nat.finite_subtype_add_eq`, which is also what
makes it a biproduct and so gives `ρ_k` its projection. Tensoring with `⋀^{k+1}T.X₁` preserves
that coproduct, the tensor product of sheaves of modules preserving all colimits in each variable
([Stacks, Tag 05NB]); the instance is instantiated by hand at these binders as
`SheafOfModules.preservesColimit_discrete_tensorLeftFunctor`, because the generic one is not found
at the concrete site in this import closure. On the `(a, b)` summand the composite is, by the
associativity square `SheafOfModules.mulSheafTensorId_comp_prodWedgeHom`, the summand inclusion of
bidegree `(k+1+a, b)`, and `k + 1 + a ≠ k`, so
`SheafOfModules.prodWedgeHomOfEq_comp_exteriorKunnethRetraction_of_ne` kills it.

That square is used **at the second structural map `sp.s`**, not at `𝟙 T.X₂`: the summand
inclusions `ρ_k` is stated against carry the section of the quotient in their second factor. Its
generalisation from the case `iG = 𝟙 H` is the interchange of the whiskering by `⋀^{k+1}T.X₁`
with the whiskering by `⋀^b sp.s` across an associator
(`SheafOfModules.whiskerLeft_pieceMap_comp_associator_hom_comp`), and lives in
`StacksFrontier.AlgebraicGeometry.DeRham.ExteriorPowerFiltration` together with the heartbeat
accounting that forced it to be a ladder of declarations rather than one.

**What this file leaves to the localization, and where that is now done.** Monomorphy of the
comparison for a sequence that does *not* split is not proved here, and that was never a gap in
the argument above but one in the localization: monomorphy is a local condition and the
transitivity sequence of a smooth morphism splits locally
(`AlgebraicGeometry.Scheme.Hom.exists_nonempty_splitting_relativeDifferentialsRestrict`), so what
the general case needs is the compatibility of
`SheafOfModules.exteriorGradedQuotientComparison` — which is defined by a universal property —
with restriction to an open. The splitting-independence
`SheafOfModules.splittingToExteriorGraded_eq` is what makes the local answers agree.

That localization is carried out, in
`StacksFrontier.AlgebraicGeometry.Modules.ExteriorGradedOpenSubspaceAlgebras` and
`StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedComparisonGlobal`:
`SheafOfModules.isIso_exteriorGradedQuotientComparison_of_locally_split` concludes invertibility
from a splitting over the members of an open covering, and
`AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialsExteriorGradedComparison` is Section
0FMK's claim for every smooth morphism of schemes, with no splitting and no local hypothesis.

**At which morphism it was done.** Monomorphy is local on the site in the two forms the
comparison could be restricted in: `SheafOfModules.mono_of_locally_mono` for the slice site and
`Stacks.AlgebraicGeometry.Modules.mono_of_mono_restrict_cover` for an open covering of a scheme.
It is carried out not at the comparison but at `SheafOfModules.exteriorGradedQuotientHom`, the
same morphism read into `⋀ⁿT.X₂/F^{k+1}⋀ⁿT.X₂`: the comparison is a monomorphism as soon as that
one is (`SheafOfModules.mono_exteriorGradedQuotientComparison_of_mono_quotientHom`), that morphism
is a monomorphism as soon as the sequence splits
(`SheafOfModules.mono_exteriorGradedQuotientHom_of_splitting`, the converse direction, which the
localization is what needs), its target carries no image subobject, and it is pinned down by the
same universal property
(`SheafOfModules.tensorLeftFunctor_map_extHom_comp_exteriorGradedQuotientHom`) — which is how the
tensor product, the exterior power and the cokernel were crossed.

**The exterior power does cross restriction to an open, with its algebra structure.** The
restriction of `AF₁` to an open is not the open's own `SheafOfModules.ringedSpaceAlgebras` on the
nose, and `SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorAlgebraIso` is not the
comparison: it identifies two bundles over one sheaf of modules on *one* site, while the two
sides here live on different sites.
`SheafOfModules.exteriorRestrictOpenSubspaceIso`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ExteriorAlgebraRestrictOpenSubspace.lean`) is, and
it carries the generator, the multiplication and the unit — which is what the wedge-product
morphisms are built from. It factors the restriction through the slice site and the pushforward
along the site functor of `TopologicalSpace.Opens.overEquivalence`, where
`SheafOfModules.isExteriorAlgebra_over` and `SheafOfModules.isExteriorAlgebra_pushforward`
already carry that structure.

Beyond that, Section 0FMK still needs the degree-`n` bookkeeping that assembles these
sheaf-level identifications into a morphism of complexes, and the tensor product over
`f^{-1}𝒪_Y` together with the shift `[-k]`, out of which
`gr^kΩ^•_{X/S} = f^{-1}Ω^k_{Y/S}[-k] ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y}` is built.

**The total degree of Tag 01CJ is `m + 1` and of the wedge filtration `1 + m`.** The two are
equal and not definitionally equal, so one transport crosses between them;
`SheafOfModules.exteriorPiece_one_add_eq` names it once and
`Stacks.CategoryTheory.map_comp_eqToHom_comp_map_eqToHom_symm_comp` cancels it against its
inverse at generic objects, where there is nothing for `rw` to find not type-correct.

## References

* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
* [Stacks Project, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/
