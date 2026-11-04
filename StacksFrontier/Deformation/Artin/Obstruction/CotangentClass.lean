module

public import StacksFrontier.Deformation.Artin.Obstruction.CotangentClass.CotangentPushout
public import StacksFrontier.Deformation.Artin.Obstruction.CotangentClass.Thickenings
public import StacksFrontier.Deformation.Artin.Obstruction.CotangentClass.ExtensionClass
public import StacksFrontier.Deformation.Artin.Obstruction.CotangentClass.ClauseOne

/-!
# The cotangent obstruction class of a dual deformation situation

Let `x` be an object of a category fibred in groupoids lying over `Spec A`, where `A` is of
finite type over `Λ`, and suppose its deformation theory is controlled by a complex `K` of
`A`-modules as in a dual deformation situation: the tangent functor `T_x(-)` is
`H¹(K ⊗ᴸ_A -)` and every square-zero thickening `A' → A` with kernel `I` carries an
obstruction element in `H²(K ⊗ᴸ_A I)`. All of these obstruction elements are then expected
to be the images of a single class on the naive cotangent complex `NL_{A/Λ}`, which at the
same time computes the canonical element of the tangent functor.

This file builds the maps the two defining properties of such a class are phrased with, and
the extra hypothesis on short exact sequences of deformation situations under which the class
exists.

A square-zero thickening `A' → A` with kernel `I` has `NL_{A/A'}` quasi-isomorphic to `I`
placed in degree `-1`, because the surjection `A' → A` is itself a presentation of `A` over
`A'` whose conormal module is `I/I² = I` and whose module of differentials vanishes. Composing
with the base-change map `NL_{A/Λ} ⟶ NL_{A/A'}` gives the extension class
`NL_{A/Λ} ⟶ I[1]`, and applying `H¹(K ⊗ᴸ_A -)` turns it into the evaluation map
`H¹(K ⊗ᴸ_A NL_{A/Λ}) ⟶ H²(K ⊗ᴸ_A I)`.

## Main definitions

* `Deformation.Artin.derivedTensorCohomology` — `Hⁿ(K ⊗ᴸ_A -)` on the whole derived category.
* `Deformation.Artin.shiftedCohomologyIso` — the shift `H¹(K ⊗ᴸ M[1]) ≅ H²(K ⊗ᴸ M)`, with
  `Deformation.Artin.shiftedCohomologyNatIso` the natural isomorphism of functors it is the
  components of and `Deformation.Artin.shiftedCohomologyIso_naturality` its naturality.
* `Deformation.Artin.naiveCotangentToDifferentials` — the morphism `NL_{A/Λ} ⟶ Ω_{A/Λ}`.
* `Deformation.Artin.squareZeroKernelCotangentEquiv` — the conormal module of a square-zero
  quotient is its kernel.
* `Deformation.Artin.squareZeroCotangentClass` and
  `Deformation.Artin.cotangentExtensionClass` — the morphisms `NL_{A/A'} ⟶ I[1]` and
  `NL_{A/Λ} ⟶ I[1]`.
* `Deformation.Artin.obstructionEvaluation` — the evaluation
  `H¹(K ⊗ᴸ NL_{A/Λ}) ⟶ H²(K ⊗ᴸ I)` at a square-zero thickening.
* `Deformation.Artin.boundaryMap` — the connecting map of a short exact sequence of modules.
* `Deformation.Artin.IsCotangentObstructionClass` — the two defining properties of a class on
  `NL_{A/Λ}` that computes all obstruction elements.
* `Deformation.Artin.cotangentPushout` — the pushout algebra `C = A[Ω_{P/Λ} ⊗_P A]` of a
  presentation, with `Deformation.Artin.cotangentPushoutMap` the map `P ⟶ C`,
  `f ↦ (α f, df ⊗ 1)`, and `Deformation.Artin.cotangentPushoutInfinitesimalMap` its descent
  to `P/J²`.
* `Deformation.Artin.squareZeroExtMap` — the map `A[M] ⟶ A[N]` of trivial square-zero
  extensions induced by a map of modules, and
  `Deformation.Artin.cotangentPushoutToDifferentials` the resulting surjection
  `C ⟶ A[Ω_{A/Λ}]`.
* `Deformation.Artin.squareZeroExt` and `Deformation.Artin.squareZeroExtProj` — the trivial
  square-zero extension `A[M]` with its projection to `A`.
* `Deformation.Artin.cotangentPushoutImage` — the image `C'` of `P/J²` in `C`, with
  `Deformation.Artin.cotangentPushoutImageProj` its projection to `A`.
* `Deformation.Artin.cotangentPushoutHom` — the surjection `C ⟶ A[M]` of commutative rings
  induced by a map out of the cotangent space of the presentation.
* `Deformation.Artin.kerRestrict` — the restriction to kernels of a ring map over `A`
  between square-zero surjections onto `A`, as a map of `A`-modules.
* `Deformation.Artin.thickeningOverBase` and `Deformation.Artin.thickeningHom` — a
  square-zero surjection onto `A` carrying a ring map from `Λ` is a square-zero thickening
  of `Spec A` over `S`, and a ring map over `A` and over the base is a morphism of such.
* `Deformation.Artin.squareZeroExtBaseMap`, `Deformation.Artin.cotangentPushoutBaseMap`,
  `Deformation.Artin.infinitesimalBaseMap` and
  `Deformation.Artin.cotangentPushoutImageBaseMap` — the maps `Λ ⟶ A[M]`, `Λ ⟶ C`,
  `Λ ⟶ P/J²` and `Λ ⟶ C'`.
* `Deformation.Artin.squareZeroExtThickening`,
  `Deformation.Artin.squareZeroExtBaseThickening`,
  `Deformation.Artin.differentialsThickening`,
  `Deformation.Artin.differentialsBaseThickening`,
  `Deformation.Artin.cotangentPushoutThickening`,
  `Deformation.Artin.infinitesimalThickening` and
  `Deformation.Artin.cotangentPushoutImageThickening` — the square-zero thickenings
  `A[M] → A`, `C̄ = A[Ω_{A/Λ}] → A`, `C → A`, `P/J² → A` and `C' → A` of `Spec A` over `S`.
* `Deformation.Artin.thickeningOverBaseHom`,
  `Deformation.Artin.cotangentPushoutImageToPushoutHom`,
  `Deformation.Artin.infinitesimalToPushoutHom`,
  `Deformation.Artin.infinitesimalToPushoutImageHom` and
  `Deformation.Artin.cotangentPushoutToSquareZeroExtHom` — the morphisms `C' → C`,
  `P/J² → C`, `P/J² → C'` and `C → A[M]` of square-zero thickenings.
* `Deformation.Artin.thickeningOverBaseRetraction` — the retraction of a thickening onto
  `Spec A` attached to a section of its surjection over the base.
* `Deformation.Artin.cotangentPushoutSection` — the section `A ⟶ C` of the pushout algebra.
* `Deformation.Artin.presentationLift` and `Deformation.Artin.infinitesimalLift` — the maps
  `P ⟶ A'` and `P/J² ⟶ A'` of a presentation into a square-zero thickening of `A` over `Λ`,
  with `Deformation.Artin.infinitesimalToThickeningHom` the resulting morphism of square-zero
  thickenings.
* `Deformation.Artin.derivedTensorTwoTermTriangle` — the triangle of a two-term complex
  tensored with `K`, and `Deformation.Artin.derivedTensorTwoTermδ` its connecting map.
* `Deformation.Artin.cotangentPushoutToDifferentialsTwisted` — the surjection `C ⟶ C̄` of the
  source, `(a, v) ↦ (a, da - v̄)`, and
  `Deformation.Artin.cotangentPushoutToDifferentialsThickeningHom` the morphism of
  square-zero thickenings it defines.
* `Deformation.Artin.extensionKernelCotangentEquiv`,
  `Deformation.Artin.infinitesimalKernelEquiv`,
  `Deformation.Artin.squareZeroExtKernelEquiv` — the kernels of the thickenings of the
  proof, identified with `I`, `J/J²` and `M`.

## Main results

* `Deformation.Artin.squareZero_mem_site_of_finite` — the trivial square-zero extension by a
  finite module occurs in any big fppf site containing `Spec A`.
* `Deformation.Artin.differentialsSquareZero_mem_site` — the same for `A[Ω_{A/Λ}]` when `A` is
  of finite type over `Λ`.
* `Deformation.Artin.derivedCohomology_eq` — the cohomology functors of a dual deformation
  situation are the restriction of `derivedTensorCohomology` to single complexes.
* `Deformation.Artin.liftOfRetraction` and
  `Deformation.Artin.obstruction_eq_zero_of_retraction` — an object lifts along a thickening
  of `Spec A` that retracts onto `Spec A`, so the obstruction element of such a thickening
  vanishes.
* `Deformation.Artin.isDeformationSituation_squareZeroExt` and
  `Deformation.Artin.isDeformationSituation_infinitesimal` — a trivial square-zero extension
  `A[M]`, in particular the pushout algebra, and `P/J² → A` are square-zero thickenings
  of `A`.
* `Deformation.Artin.ker_sq_le_ker_cotangentPushoutMap` — the map `P ⟶ C` kills `J²`, which
  is what lets it descend to `P/J²`.
* `Deformation.Artin.cotangentPushoutToDifferentials_surjective` — the pushout algebra
  surjects onto `A[Ω_{A/Λ}]`.
* `Deformation.Artin.isDeformationSituation_cotangentPushoutImage` — `C' → A` is a
  square-zero thickening of `A`.
* `Deformation.Artin.toKaehler_eq_zero_iff` — the kernel of the conormal surjection
  `Ω_{P/Λ} ⊗_P A ⟶ Ω_{A/Λ}` is the image of the conormal module `J/J²`.
* `Deformation.Artin.isShortExactSequence_cotangentPushout` and
  `Deformation.Artin.isShortExactSequence_cotangentPushoutToDifferentials` — the triple
  `A[M] → A`, `C → A`, `C' → A` is a short exact sequence of deformation situations whenever
  `Ω_{P/Λ} ⊗_P A ⟶ M` is surjective with kernel the image of `J/J²`, in particular for
  `M = Ω_{A/Λ}`, where the kernel sequence is the conormal sequence of the presentation.
* `Deformation.Artin.contains_Spec_subring` and
  `Deformation.Artin.contains_of_isOpenImmersion` — a subring of a ring of a big fppf site,
  and the source of an open immersion into a scheme of such a site, occur in that site.
* `Deformation.Artin.presentation_mem_site`, `Deformation.Artin.infinitesimal_mem_site`,
  `Deformation.Artin.cotangentPushout_mem_site` and
  `Deformation.Artin.cotangentPushoutImage_mem_site` — the polynomial ring of a finite
  presentation, its infinitesimal extension, the pushout algebra and its subring `C'` all
  occur in the chosen big fppf site.
* `Deformation.Artin.cotangentPushoutMap_algebraMap` — the canonical map of a presentation
  into the pushout algebra is a map of `Λ`-algebras.
* `Deformation.Artin.exists_baseRingHom` — every square-zero thickening of `Spec A` lies over
  an affine open `Spec Λ` of the base through a ring map `Λ ⟶ A'` over `A`, because the closed
  immersion `Spec A ⟶ Spec A'` is surjective on points.
* `Deformation.Artin.derivedTensorTwoTermTriangle_distinguished` and
  `Deformation.Artin.exists_of_derivedTensorTwoTermδ_eq_zero`,
  `Deformation.Artin.exists_of_derivedTensorTwoTerm_mor₂_eq_zero` — the long exact sequence of
  the tensored triangle: a class on the conormal module killed by the connecting map comes from
  the two-term complex, and a class on the two-term complex dying on the conormal module comes
  from the degree-zero term.
* `Deformation.Artin.obstruction_cotangentPushout_eq_zero` — `o_x(C) = 0`, the pushout algebra
  admitting a section over the base.
* `Deformation.Artin.map_obstruction_infinitesimal_eq_zero` — `o_x(P/J²)` dies on the cotangent
  space of the presentation.
* `Deformation.Artin.exists_obstruction_eq_map_obstruction_infinitesimal` — the obstruction of
  every deformation situation is the image of `o_x(P/J²)` under the map of kernels of a
  `Λ`-algebra map `P/J² ⟶ A'` over `A`.
* `Deformation.Artin.triangleOfSESδ_eq_homOfDegreewiseSplit` — the connecting morphism of the
  triangle of a short exact sequence of cochain complexes split in every degree is the
  morphism built from the splittings; Mathlib has both but does not compare them.
* `Deformation.Artin.twoTermTriangle_mor₃` — the connecting morphism `N[-1] ⟶ M[0]⟦1⟧` of the
  triangle of a two-term complex is the image of `d` under the single functor in degree `-1`,
  with no sign.
* `Deformation.Artin.derivedTensorTwoTermδ_eq` — the connecting map of the tensored triangle
  of a two-term complex is the map induced by its differential, read through the degree shift.
* `Deformation.Artin.derivedNaiveCotangentComplexIso_hom_comp_cotangentExtensionClass` — the
  extension class of a square-zero thickening, read through an arbitrary presentation: the
  comparison isomorphism followed by `NL_{A/Λ} ⟶ I[1]` is the projection of the two-term
  complex onto its conormal module followed by the map `J/J² ⟶ I` induced by a lift of the
  presentation into the thickening. Two lifts give conormal maps differing by a map through
  the differential, so the two chain maps are homotopic rather than equal, which is all that
  is needed in the derived category.
* `Deformation.Artin.isShortExactSequence_cotangentPushoutToDifferentialsTwisted` — the same
  short exact sequence of deformation situations for the derivation-twisted surjection, with
  `Deformation.Artin.cotangentPushoutToDifferentialsTwisted_section` the statement that the
  section of `C` followed by it is the map `(1, d)`.
* `Deformation.Artin.squareZeroExtKernelEquiv_kerRestrict_infinitesimal` — under the
  identifications of the kernels, the map of kernels of `P/J² ⟶ C` is the differential of
  `NL(α)`.
* `Deformation.Artin.exists_finite_generators`,
  `Deformation.Artin.cotangentPushout_mem_site_of_finite` and
  `Deformation.Artin.presentation_mem_site_of_finite` — an algebra of finite type has a
  presentation indexed by a finite type of its own universe, whose polynomial ring and
  pushout algebra occur in the site.

## Implementation notes

The naive cotangent complex is taken in the derived category, placed in cohomological degrees
`-1` and `0`, and computed from the canonical presentation; `relativeNaiveCotangentSurjectionMap`
is the comparison with the presentation given by the surjection `A' → A` itself. The degree
shift `H¹(K ⊗ᴸ I[1]) = H²(K ⊗ᴸ I)` is the composite of the shift isomorphism of the single
functors, the shift commutation of the derived tensor product, and the shift sequence of the
homology functors, and the connecting map is the one of the distinguished triangle attached to
a short exact sequence of modules.

For each thickening in `IsCotangentObstructionClass` the `Λ`-algebra structure is asserted to
come from a factorization of the structure morphism through the affine open `Spec Λ` rather
than imposed as a further hypothesis on the thickening.

Only two of the four thickenings of the proof of 07YY admit a section, so their structure
morphisms to the base are not all of the same shape: `A[M]` and `C` have one, while `C'` and
`P/J²` do not. All four are therefore produced by `thickeningOverBase`, which takes the
structure morphism to be `Spec A' ⟶ Spec Λ ⟶ S` through the affine open of the base, the
compatibility with the closed immersion coming from the factorization of the structure
morphism of `Spec A`. Having all four in that single shape is what makes the morphisms
between them uniform: a ring map over `A` and over `Λ` is a morphism of thickenings, and the
map it induces on kernels is `kerRestrict`, whose linearity is the statement that a scalar of
`A` acts on a square-zero kernel through any of its preimages.

The spectrum of each thickened algebra is placed in the site from the size bounds of Stacks
000R: `C` is finite over `A` because the cotangent space of a finite presentation is finite
free, `C'` is a subring of `C`, `P/J²` is a quotient of a polynomial ring of finite type over
`Λ`, and `Spec Λ` itself occurs in the site because the affine open of the base is an open
immersion.

A square-zero extension of `A` admitting a section is the trivial one, so the pushout
`C = (P/J² × Ω_{P/Λ} ⊗_P A)/(J/J²)` of the source's argument is realized directly as
`A[Ω_{P/Λ} ⊗_P A]`: its section and its kernel are then the structure maps of
`TrivSqZeroExt`, and the content left to prove is that `f ↦ (α f, df ⊗ 1)` is a ring map
killing `J²`, which is the Leibniz rule for the universal derivation. The maps between
trivial square-zero extensions are stated for an arbitrary module of the module category, so
that the right action of `A` needed for the ring structure on `A[M]` is resolved once rather
than at each module. `P/J²` is Mathlib's `Algebra.Extension.infinitesimal`.

`cotangentPushoutHom` repeats `cotangentPushoutToDifferentials` with its source and target
named by `cotangentPushout` and `squareZeroExt`; that spelling is what makes the ring
structures of a short exact sequence of deformation situations agree with the ones the
commutative-ring instance of a trivial square-zero extension provides. Writing a trivial
square-zero extension of a module given by a closed term needs that instance supplied, which
is what the two `letI`s of the conormal sequence do.

A ring map from the base to an arbitrary square-zero thickening is recovered geometrically
rather than assumed: the kernel of `A' ⟶ A` is nilpotent, so `Spec A ⟶ Spec A'` is surjective
on points and the two structure morphisms to `S` have the same image, which lies in the affine
open; the morphism therefore factors through the open immersion, and a morphism of affine
schemes is the spectrum of a ring map. Conversely the polynomial ring of a presentation maps
into any such thickening by lifting the generators along the surjection, and that map kills
`J²` because the kernel of the presentation lands in the square-zero kernel.

In the boundary condition the
canonical identification `A₁' = A[I₁]` of a short exact sequence of deformation situations is
recorded by the splitting `s` and the ring map `ψ`, whose components are prescribed; for each
lift over the middle situation the condition produces a cartesian restriction along `ψ` and
asserts the boundary identity, so the identity is not guarded by antecedents that could make
it vacuous.

## References

* [Stacks Project, Tag 07YX](https://stacks.math.columbia.edu/tag/07YX)
* [Stacks Project, Tag 07YY](https://stacks.math.columbia.edu/tag/07YY)
-/
