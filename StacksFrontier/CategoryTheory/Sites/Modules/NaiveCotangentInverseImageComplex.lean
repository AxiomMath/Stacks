module

public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentInverseImageComplex.DegreeComparisons
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentInverseImageComplex.CommutingSquare

/-!
# The inverse image of the naive cotangent complex as a complex

Let `f : Sh(C) ⟶ Sh(D)` be a morphism of topoi and `a : A ⟶ B` a homomorphism of sheaves of
commutative rings on `D`. The two terms of the naive cotangent complex of Stacks 08TW are
identified with the two terms of the naive cotangent complex of `f⁻¹a` by
`Stacks.Sheaves.RingedToposModules.inverseImageConormalIso` in degree `-1` and by
`Stacks.SheafOfModules.inverseImageNaiveCotangentZeroIso` in degree `0`. This file assembles
the two into an isomorphism of two-term complexes
`f⁻¹ NL_{B/A} ≅ NL_{f⁻¹B/f⁻¹A}` of [Stacks 08TZ].

## Main definitions

* `Stacks.SheafOfModules.inverseImagePresentationConormalIso` is the transport of the conormal
  sheaf along the identification `f⁻¹(A[B]) ≅ (f⁻¹A)[f⁻¹B]` of the two presentations of `f⁻¹B`:
  the conormal sheaf of `f⁻¹(A[B]) ⟶ f⁻¹B` is the conormal sheaf of the canonical presentation
  `(f⁻¹A)[f⁻¹B] ⟶ f⁻¹B`.
* `Stacks.SheafOfModules.inverseImageNaiveCotangentNegOneIso` is the degree `-1` comparison:
  the identification of the conormal sheaves at the inverse image of the canonical presentation
  `A[B] ⟶ B`, followed by that transport.
* `Stacks.SheafOfModules.inverseImageNaiveCotangentZeroTargetIso` is the degree `0` comparison,
  at the spelling of the coefficient ring sheaf used by the naive cotangent complex.
* `Stacks.SheafOfModules.InverseImageNaiveCotangentSquare` is the commutation of those two
  comparisons with the two conormal differentials.
* `Stacks.SheafOfModules.inverseImageNaiveCotangentComplexIso` is the resulting isomorphism of
  two-term complexes.

## Main results

* `Stacks.SheafOfModules.inverseImageNaiveCotangentSquare`: the two comparisons commute with the
  two conormal differentials, which is what makes them a morphism of complexes.
* `Stacks.SheafOfModules.naiveCotangentZeroDerivationEquiv_d`: the universal property of the
  degree-`0` term of the naive cotangent complex, read on sections — the derivation attached to
  a morphism out of `B ⊗_{A[B]} Ω_{A[B]/A}` is evaluation at the local sections `1 ⊗ dp`.
* `Stacks.SheafOfModules.inverseImageNaiveCotangentZeroIso_derivation`: the degree `0`
  comparison is the morphism whose attached `f⁻¹A`-derivation of `(f⁻¹A)[f⁻¹B]` is the
  universal one.
* `Stacks.SheafOfModules.inverseImageNaiveCotangentZeroDerivationEquiv_d_freeAlgebraIso`:
  the derivation attached to a morphism out of the inverse image of the degree-`0` term,
  evaluated at the image of a local section of `f⁻¹(A[B])`, is the value of the derivation
  produced by the first four of the six bijections composing that universal property; the last
  two, `Stacks.SheafOfModules.inverseImageZeroStep₅_d` and
  `Stacks.SheafOfModules.inverseImageZeroStep₆_d`, are transports that do not change values.
* `Stacks.Sheaves.RingedToposModules.isoOfNaturalHomEquiv_apply` and
  `Stacks.Sheaves.RingedToposModules.isoOfNaturalHomEquiv_symm_apply`: a natural family of
  bijections of the morphisms out of two objects is composition with the isomorphism the
  Yoneda argument produces from it.
* `Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_inverseImageIdealChain`:
  restricting a derivation to the kernel ideal commutes with the last three steps of the
  identification of the two conormal sheaves, which is what identifies the degree `-1` and the
  degree `0` chains of bijections with one another.
* `Stacks.Sheaves.RingedToposModules.inverseImageIdealChain_app_of_sections`: that chain
  identity read on a local section of the kernel ideal of the inverse image, from the values of
  the morphism out of the kernel ideal.
* `Stacks.SheafOfModules.conormalModuleHomEquivOf_inverseImagePresentationConormalIso_app` and
  `Stacks.SheafOfModules.inverseImageNaiveCotangentZeroDerivation_d`: the two sides of the
  commuting square of Stacks 08TZ, evaluated on a local section of the kernel ideal; both are the
  local section `1 ⊗ dg` of the degree `0` term of the naive cotangent complex of `f⁻¹a`.
* `Stacks.SheafOfModules.conormalInverseImageAdjunctionEquiv_canonicalConormalDifferential_comp`:
  transposing the inverse image of the conormal differential across `f⁻¹ ⊣ f_*` gives the
  conormal differential followed by the transpose, which is what identifies the morphism out of
  the kernel ideal produced by the degree `-1` chain with the one
  `Stacks.SheafOfModules.moduleSheafFunctor_map_canonicalConormalDifferential` computes.
* `Stacks.SheafOfModules.inverseImageDerivationEquiv_symm_postcomp_d`: the third and fourth
  steps of the degree `0` chain, read on a local section, at the spelling in which the value
  produced by `Stacks.Sheaves.RingedToposModules.inverseImageIdealChain_app_of_sections` meets
  the one `Stacks.SheafOfModules.inverseImageNaiveCotangentZeroDerivation_d` computes.

## Implementation notes

Two spellings of the coefficient ring sheaf of the inverse image meet here: the inverse image
of sheaves of modules lands over `f⁻¹` of the sheaf of rings underlying `B`, while the naive
cotangent complex of `f⁻¹a` is taken over the sheaf of rings underlying `f⁻¹B`. The two are
definitionally equal, but no tactic can rewrite inside a composition that mixes them, so every
statement below is phrased at the second spelling, which
`CategoryTheory.Sheaf.inverseImageTargetModules` pins down.

The transport of the terms of the complex into the two degrees where it is nonzero is left to
`HomologicalComplex.homFromMapDouble`, which does it with the comparison isomorphisms
`HomologicalComplex.doubleXIso₀` and `HomologicalComplex.doubleXIso₁` of the two-term complex;
no `eqToHom` on the terms of the complex appears in any statement here, since an `eqToHom` in a
composition is a propositional bridge between two definitionally equal spellings that the
unifier then has to cross inside an already large statement.

The commuting square of the two comparisons with the conormal differentials is proved by
reducing it to an identity of morphisms out of the kernel ideal of the inverse image of the
canonical presentation. Injectivity of
`Stacks.Sheaves.RingedToposModules.inverseImageConormalHomEquiv`, by
`Stacks.Sheaves.RingedToposModules.isoOfNaturalHomEquiv_apply` and the universal property
`Stacks.Sites.Conormal.conormalModuleHomEquivOf` of the conormal sheaf, reduces the square to
an equation of morphisms out of the kernel ideal of the inverse image of the canonical
presentation. `Stacks.SheafOfModules.naiveCotangentZeroDerivationEquiv_d`,
`Stacks.SheafOfModules.inverseImageNaiveCotangentZeroIso_derivation` and
`Stacks.SheafOfModules.conormalModuleHomEquivOf_canonicalConormalDifferential_app` compute the
two sides of that equation down to one further comparison, which is the mathematical content
of the square: the two comparisons are built from two independent chains of bijections, the
degree `-1` one transposing a morphism of sheaves of modules across `f⁻¹ ⊣ f_*`
(`Stacks.Sheaves.RingedToposModules.inverseImageIdealAdjunctionEquiv`, together with
`Stacks.Sheaves.RingedToposModules.inverseImageIdealIso` on the kernel ideals) and the
degree `0` one transposing a derivation
(`Stacks.Sheaves.RingedToposModules.inverseImageDerivationEquiv`, the module half of
Stacks 08TQ). Both are the hom-set bijection of `f.adj` read on underlying sheaves of sets,
by `Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_toposModulesHomEquiv` and
`Stacks.Sheaves.RingedToposModules.derivationSheafHom_inverseImageDerivationEquiv`, each by
reflexivity; the comparison is that restricting a derivation to the kernel ideal commutes
with that bijection, and the same for the two remaining transports of the degree `0` chain,
the spelling of the inverse-image ring map and
`Stacks.Sites.FreeAlgebra.inverseImageFreeAlgebraIso`.

Of those, the two remaining transports of the degree `0` chain are
(`Stacks.SheafOfModules.inverseImageZeroStep₅_d`,
`Stacks.SheafOfModules.inverseImageZeroStep₆_d` and their composition
`Stacks.SheafOfModules.inverseImageNaiveCotangentZeroDerivationEquiv_d_freeAlgebraIso`),
as are the readings of the degree `-1` chain on underlying sheaves of sets
(`Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_inverseImageIdealAdjunctionEquiv`
and `Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_inverseImageIdealIso_inv_comp`)
and the universal property of the conormal sheaf on sections at an arbitrary spelling of the
ring map (`Stacks.Sites.Conormal.conormalModuleHomEquivOf_app_conormalClass`). The statement
that identifies the two chains — that restricting a derivation to the kernel ideal commutes
with the hom-set bijection of `f⁻¹ ⊣ f_*` — is
`Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_inverseImageIdealChain`; it takes as
a hypothesis the restriction to the kernel ideal of the derivation on the target side of the
adjunction, which is where its consumer supplies the derivation the square is about.

That statement is stated through the two spellings of the underlying sheaf of sets of an
inverse image of a sheaf of modules, and the composition crossing from one to the other is only
definitionally well formed; its final step therefore has to be taken by rewriting with
`Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_inverseImageIdealIso_inv_comp`, whose
two sides are syntactically present in the goal, rather than by whiskering an equality of
morphisms, whose source and target the unifier would have to identify afresh.

Both sides of the square are computed on local sections of the kernel ideal, and they
agree there:
`Stacks.SheafOfModules.conormalModuleHomEquivOf_inverseImagePresentationConormalIso_app`
evaluates the degree `-1` comparison followed by the conormal differential, and
`Stacks.SheafOfModules.inverseImageNaiveCotangentZeroDerivation_d` evaluates the derivation
which the degree `0` comparison transposes to; both values are the local section `1 ⊗ dg` of the
degree `0` term of the naive cotangent complex of `f⁻¹a`, read at the image of the section under
`Stacks.Sites.FreeAlgebra.inverseImageFreeAlgebraIso`. The hypothesis of the chain identity is
supplied by `Stacks.SheafOfModules.moduleSheafFunctor_map_canonicalConormalDifferential` through
`Stacks.Sheaves.RingedToposModules.inverseImageIdealChain_hypothesis`, and the chain identity is
read on sections by `Stacks.Sheaves.RingedToposModules.inverseImageIdealChain_app_of_sections`.
The bookkeeping that assembles those two values into the identity of morphisms is
`Stacks.SheafOfModules.inverseImageNaiveCotangentSquare`, and
`Stacks.SheafOfModules.inverseImageNaiveCotangentComplexIso` is the isomorphism of complexes
built from it: the tag is carried here in full, not conditionally on the square. The square
reduces to
an identity of morphisms out of the kernel ideal of the inverse image by `CategoryTheory.Iso`'s
cancellation, `Stacks.Sheaves.RingedToposModules.isoOfNaturalHomEquiv_apply` and
`Equiv.eq_symm_apply`; the morphism the degree `-1` chain produces is identified by
`Stacks.SheafOfModules.conormalInverseImageAdjunctionEquiv_canonicalConormalDifferential_comp`
with the one `Stacks.SheafOfModules.moduleSheafFunctor_map_canonicalConormalDifferential`
computes; the chain identity is read on sections by
`Stacks.Sheaves.RingedToposModules.inverseImageIdealChain_app_of_sections`; and its value meets
the value of the degree `0` chain by
`Stacks.SheafOfModules.inverseImageDerivationEquiv_symm_postcomp_d`.

The assembly is cut into declarations along that description:
`Stacks.SheafOfModules.conormalDirectImageIdealEquiv_canonicalConormalDifferential_app` supplies
the hypothesis of the chain identity,
`Stacks.Sheaves.RingedToposModules.conormalInverseImageIdealSheafEquiv_app_of_sections` states
the chain identity at the composite of all five steps rather than at the last three,
`Stacks.SheafOfModules.conormalInverseImageIdealSheafEquiv_canonicalConormalDifferential_app`
instantiates it at the canonical presentation, and
`Stacks.SheafOfModules.conormalModuleHomEquivOf_eq_conormalInverseImageIdealSheafEquiv` turns the
identity of values into one of morphisms. The last two steps are generic:
`Stacks.Sheaves.RingedToposModules.inverseImageConormalHomEquiv_eq_of` reads the universal
property of the conormal sheaf of the inverse image backwards, and
`Stacks.Sheaves.RingedToposModules.isoOfNaturalHomEquiv_hom_comp` turns the resulting identity of
morphisms out of the conormal sheaf of the inverse image into one out of the inverse image of the
conormal sheaf.

Every declaration here names the universe arguments of the lemma it applies. The statements are
cheap to elaborate; what is not is solving a universe metavariable of a lemma against an expected
type, since the universes of a site appear only inside `max u v w` and the unifier postpones such
a constraint and then compares the two statements with the universe still unknown. That is what
exhausts the elaboration budget of a declaration, and naming the universes removes it.

## References

* [Stacks Project, Tag 08TZ](https://stacks.math.columbia.edu/tag/08TZ)
* [Stacks Project, Tag 08TW](https://stacks.math.columbia.edu/tag/08TW), the naive cotangent
  complex.
* [Stacks Project, Tag 08TS](https://stacks.math.columbia.edu/tag/08TS), the conormal sequence.
* [Stacks Project, Tag 04BL](https://stacks.math.columbia.edu/tag/04BL), the corepresentability
  of relative derivations.
-/
