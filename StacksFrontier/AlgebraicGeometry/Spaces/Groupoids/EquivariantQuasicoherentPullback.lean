module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EquivariantQuasicoherentPullback.Reindexing
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EquivariantQuasicoherentPullback.NamedFlattening
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EquivariantQuasicoherentPullback.Functor

/-!
# Pullback of equivariant quasi-coherent modules along an equivariant morphism

Let `G` be a group algebraic space over an algebraic space `B` acting on two algebraic spaces
`X` and `Y` over `B`, and let `f : X ⟶ Y` be an equivariant morphism.  Stacks 043U asserts that
`f` induces a pullback functor from the `G`-equivariant quasi-coherent `𝒪_Y`-modules to the
`G`-equivariant quasi-coherent `𝒪_X`-modules, with underlying module the ordinary inverse image
along `f` and transition morphism the reindexing along `1_G × f` of the given one
(`AlgebraicGeometry.Space.equivariantModulePullbackTransition`, already in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/EquivariantPullback.lean`).

This file constructs that functor, together with the calculus it is made of: the reindexing and
flattening identities for the inverse image of `𝒪`-modules, the naturality of a conjugated
transition morphism in the module, the two commuting squares of an equivariant morphism read
along a test object over the action space, and the transfer of the unit and cocycle laws along
flattening.

## Main definitions

* `AlgebraicGeometry.Space.modulePullbackFlatten'` flattens a morphism between two inverse
  images of an inverse image with the two composites along the connecting morphism given as
  separate morphisms together with equations identifying them; see the implementation notes.
* `AlgebraicGeometry.Space.equivariantQuasicoherentPullback` is **Stacks 043U**, with
  `AlgebraicGeometry.Space.equivariantQuasicoherentPullbackObj` its object map.

## Main results

* `AlgebraicGeometry.Space.modulePullbackFlatten_modulePullbackReindex_conjugate`: **flattening a
  reindexed conjugated transition morphism is reindexing the original one.**  This is the
  calculation the cocycle and unit laws of the inverse image reduce to, stated for abstract
  morphisms of algebraic spaces.
* `AlgebraicGeometry.Space.modulePullbackConjugate_naturality`: **a conjugated transition
  morphism is natural in the module**, which is the compatibility of the inverse image with
  morphisms of equivariant modules.
* `AlgebraicGeometry.Space.modulePullbackReindex_comp'`,
  `AlgebraicGeometry.Space.modulePullbackReindex_pullbackTransport`,
  `AlgebraicGeometry.Space.modulePullbackFlatten_pullbackTransport`,
  `AlgebraicGeometry.Space.pullbackTransport_comp`,
  `AlgebraicGeometry.Space.modulePullbackFlatten_comp₅` and
  `AlgebraicGeometry.Space.modulePullbackReindex_naturality`: the reindexing, flattening and
  transport identities, in the shapes that are usable (see the implementation notes).
* `AlgebraicGeometry.Space.actionSpaceHom_action_square` and
  `AlgebraicGeometry.Space.actionSpaceHom_projection_square`: the two squares of an equivariant
  morphism, read along a test object over the action space of `X` with the composite `1_G × f`
  after the test morphism contracted.
* `AlgebraicGeometry.Space.modulePullbackFlatten_reindex_conjugate` and its specialization
  `AlgebraicGeometry.Space.modulePullbackFlatten_equivariantConjugate`, read on the transition
  morphism by
  `AlgebraicGeometry.Space.modulePullbackFlatten_equivariantPullbackTransition`:
  **the transition morphism of the inverse image, reindexed along a test morphism and flattened
  along `f`, is the reindexing of the given transition morphism along the pushed test
  morphism**, between the two squares of `f`.  This is the identity the laws of the inverse
  image reduce to.
* `AlgebraicGeometry.Space.equivariantPullbackConjugate_unit` and
  `AlgebraicGeometry.Space.equivariantModulePullbackTransition_unit`: **the unit law for the
  transition morphism of the inverse image**, for the conjugate written out and for
  `AlgebraicGeometry.Space.equivariantModulePullbackTransition` itself.
* `AlgebraicGeometry.Space.equivariantModulePullbackTransition_naturality`: **the transition
  morphism of the inverse image is natural in the equivariant module.**  This is the morphism
  map of the pullback of Stacks 043U.
* `AlgebraicGeometry.Space.modulePullbackFlatten_reindex_of_flatten` and
  `AlgebraicGeometry.Space.modulePullbackFlatten_reindex_cocycle_left`: the transfer of the
  reindexing calculus along flattening, and the flattened left-hand side of a cocycle law, both
  for abstract morphisms of algebraic spaces.
* `AlgebraicGeometry.Space.modulePullbackFlatten'_injective`,
  `AlgebraicGeometry.Space.modulePullbackFlatten'_comp_morphism`,
  `AlgebraicGeometry.Space.modulePullbackFlatten'_comp₅`,
  `AlgebraicGeometry.Space.modulePullbackFlatten'_pullbackTransport` and
  `AlgebraicGeometry.Space.modulePullbackFlatten'_reindex_of_flatten`: the named flattening is
  injective, compatible with composition and with the canonical identifications, and carries a
  reindexed transition morphism to the reindexing of the given one with no transports left
  over.
* `AlgebraicGeometry.Space.modulePullbackReindex_cocycle_of_flatten`: **the cocycle law
  transfers along flattening**, for abstract morphisms of algebraic spaces, and
  `AlgebraicGeometry.Space.equivariantModulePullbackTransition_cocycle`: **the cocycle law for
  the transition morphism of the inverse image.**
* `AlgebraicGeometry.Space.equivariantQuasicoherentPullback_obj_F`,
  `AlgebraicGeometry.Space.equivariantQuasicoherentPullback_obj_alpha` and
  `AlgebraicGeometry.Space.equivariantQuasicoherentPullback_map_hom`: the object map, the
  transition morphism and the morphism map of the functor of Stacks 043U.

## Implementation notes

**Every step of the module-level algebra here is the application of a lemma about an arbitrary
category** — `CategoryTheory.comp₂_congr`, `CategoryTheory.comp₃_congr`,
`CategoryTheory.comp₅_congr`, `CategoryTheory.comp_assoc₅`,
`CategoryTheory.comp_transport_merge`, `CategoryTheory.comp_naturality₅` and
`CategoryTheory.Iso.inv_comp_conjugate₃_comp_hom` — rather than a `rw` or a `simp` on the
morphisms of `AlgebraicGeometry.Space.Modules`, and the implicit objects are supplied explicitly
wherever `AlgebraicGeometry.Space.actionMap` is substituted into a general lemma.

This is not a stylistic choice.  `AlgebraicGeometry.Space.modulePullback` is the pullback of
modules along a morphism of ringed topoi, built through
`CategoryTheory.Adjunction.leftAdjointUniq`, and unfolding it is prohibitively expensive.  Two
consequences:

* a rewrite whose motive abstracts a morphism of `𝒪`-modules, or a `simp only [Category.assoc]`
  on such morphisms, produces a term the *kernel* cannot check within its budget, even when
  elaboration succeeds;
* a statement or unification that has to reconcile `w ≫ m ≫ a` with `(w ≫ m) ≫ a` underneath
  `(AlgebraicGeometry.Space.modulePullback _).obj` does not terminate, although the same
  reconciliation is cheap as a standalone `rfl` goal on the objects alone.

`AlgebraicGeometry.Space.modulePullbackReindex_comp'` is the answer to the second point: it takes
the composite `w ≫ m` as a separate morphism together with an equation identifying it, so that
no statement ever mentions the composite underneath the inverse image.  The lemmas named above
are the shapes that do work, and they are public so that the next consumer of this corner
inherits them.

**The connecting morphism `1_G × f` is written as `AlgebraicGeometry.Space.actionMap`
throughout, and that is deliberate.**  It has a second spelling,
`AlgebraicGeometry.Space.actionSpaceHom G Y hY (actionSpace G X hX).property (lift (fst _ _)
(snd _ _ ≫ f))`, which is definitionally equal to it and is the one
`AlgebraicGeometry.Space.equivariantModulePullbackTransition` is written in.  The two have
*different source objects* — `actionSpace G X hX` against
`underlyingSpace (G.obj.X ⊗ X) (actionSpace G X hX).property` — hence their morphisms of
`𝒪`-modules live in two different instances of the module category, and relating them forces a
comparison of two `Category` instances, which unfolds
`CategoryTheory.RingedSite.ringSheaf (AlgebraicGeometry.Space.smallEtaleRingedSite …)`.  That is
unbounded, not merely slow: it does not terminate at any heartbeat budget, and the measurable
symptom is that `rw [modulePullbackReindex_comp_morphism]` reports *no occurrence of the
pattern* in a goal that visibly contains it, because the `≫` is at the other instance.  Do not
"simplify" the uniform spelling back into the mixed one.

For the same reason nothing here identifies a definition of `𝒪`-module morphisms with its own
composite body.  Every such identification — by `rfl`, by the generated `eq_def` ascribed to a
hand-written body, or by `simp only [theDefinition]` — is rejected by the kernel, even with all
algebraic spaces abstract.  The two routes that do work are `rw` with the generated `eq_def`,
whose motive the kernel accepts, and composing lemmas that were proved without unfolding
anything.

The module universe is the universe of the structure rings, because
`AlgebraicGeometry.Space.modulePullback` exists only there.

## The named flattening

The cocycle law needs the flattening of a fivefold composite of three canonical transports and
two reindexed transition morphisms, and the two flattening identities it is built from disagree
about the bracketing of the composites underneath the inverse image:
`AlgebraicGeometry.Space.modulePullbackFlatten_pullbackTransport` states the flattening of a
transport between `(w ≫ a)^*ℱ` and `(w ≫ b)^*ℱ` at `(w ≫ a) ≫ g`, whereas
`AlgebraicGeometry.Space.modulePullbackFlatten_reindex_of_flatten` states the flattening of a
reindexed transition morphism at `w ≫ a ≫ g`.  The kernel reconciles the two in a *type*, and
for a canonical transport alone, at no cost; underneath a `≫` it does not: for two proofs `E`,
`E'` of the two bracketings, deciding
`pullbackTransport ℱ E ≫ modulePullbackReindex n α =`
`pullbackTransport ℱ E' ≫ modulePullbackReindex n α`
exhausts the kernel's budget, because `CategoryTheory.CategoryStruct.comp` is a projection of
the `SheafOfModules` instance and is projection-reduced before congruence is attempted.

`AlgebraicGeometry.Space.modulePullbackFlatten'` is what removes the bracketing from every
statement: it takes the two composites along `g` as separate morphisms `c` and `d` together with
equations `a ≫ g = c` and `b ≫ g = d`, so the result is a morphism `c^*ℱ ⟶ d^*ℱ` and the only
place a bracketing occurs is inside a `Prop`.  The two bracketings are reconciled once, at
`CategoryTheory.comp₃`, by
`AlgebraicGeometry.Space.modulePullbackFlatten_reindex_comp₃'`: the kernel compares two
applications of `comp₃` factor by factor, where the comparison of two canonical transports is
free.  For the same reason that step is three declarations
(`AlgebraicGeometry.Space.modulePullbackFlatten_reindex_comp₃`, its primed form and
`AlgebraicGeometry.Space.modulePullbackFlatten_reindex_of_flatten'`) rather than one chain: an
intermediate `≫`-expression written out by hand elaborates with implicit objects at the other
bracketing, and comparing it to the one the lemma produces is again the forbidden comparison.

With the named flattening the cocycle law is a chain of five identities with no transports left
over, `AlgebraicGeometry.Space.modulePullbackReindex_cocycle_of_flatten`.

## Inputs, and why the functor carries no hypotheses

The two inputs the construction needs are theorems of this development, so the functor takes
neither as a named hypothesis:

* the associativity coherence of the comparison of inverse images of Stacks 03LU, which every
  reindexing step uses, is `AlgebraicGeometry.Space.modulePullbackCompIsoAssoc` in
  `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardCompIsoAssoc.lean`, the
  adjoint mate of the corresponding coherence for direct images;
* that the inverse image preserves quasi-coherence, which is what makes the functor land in the
  quasi-coherent equivariant category, is Stacks 03GA,
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite` in
  `StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackQuasicoherentFromChartDiagrams.lean`,
  proved for an arbitrary morphism of algebraic spaces through affine chart diagrams.  The
  underlying module of the inverse image is therefore taken by
  `AlgebraicGeometry.Space.quasicoherentPullbackFunctor`, the unconditional form of
  `AlgebraicGeometry.Space.quasicoherentPullback`.

The equivariance of `f` enters as `CategoryTheory.IsModHom`, from which the action square
`AlgebraicGeometry.Space.action_comp_asSpaceHom` is derived; the projection square
`AlgebraicGeometry.Space.projection_comp_asSpaceHom` needs nothing.

## File layout

* `…EquivariantQuasicoherentPullback.Reindexing`: the category-level glue and the reindexing
  and flattening calculus for inverse images of `𝒪`-modules;
* `…EquivariantQuasicoherentPullback.NamedFlattening`: the transfer of the laws along
  flattening and the named flattening;
* `…EquivariantQuasicoherentPullback.Functor`: the equivariant situation, the laws of the
  transition morphism of the inverse image and the functor of Stacks 043U.

## References

* [Stacks Project, Tag 043U](https://stacks.math.columbia.edu/tag/043U)
* [Stacks Project, Tag 043T](https://stacks.math.columbia.edu/tag/043T)
* [Stacks Project, Tag 043Q](https://stacks.math.columbia.edu/tag/043Q)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
-/
