module

public import StacksFrontier.Homology.HomComplex.DerivedAdjunctionResolution
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeIdentification
public import StacksFrontier.RingTheory.Dualizing.RelativeUniquenessDuality

/-!
# The lax monoidal structure map against the currying isomorphism of [stacks 0A65]

`Dualizing.derivedTensorBaseChange` is the lax monoidal structure map
`μ_{X,Y} : F X ⊗ᴸ_A F Y ⟶ F (X ⊗ᴸ_R Y)` of a model `F` of derived extension of scalars, built in
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorMate` as
`StacksDraft.DerivedHom.DerivedHomAdjunction.laxTensorOfHomMate`: the mate, under the tensor--Hom
adjunctions of [stacks 0A63], of a comparison `m` of the two internal-Hom bifunctors.

Two obligations of this chapter are waiting on *one* coherence of `μ`, recorded as prose in the
module documentation of `StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaEvaluation`
and of `StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonTranspose`: the
associativity of `μ`, equivalently the compatibility of the change-of-rings isomorphism of
[stacks 0E1W] with the currying isomorphism of [stacks 0A65].  This file makes that prose into
theorems.

## What is proved

The currying isomorphism `Dualizing.homCurryIso` of [stacks 0A65] already exists for an arbitrary
`StacksDraft.DerivedHom.DerivedHomAdjunction`, built by Yoneda out of the transposition bijection
and the associator, but it carries **no** characterizing equation: it is used in exactly one place
in the library and nothing says what it does to a morphism.  The first half of this file supplies
that equation, `Dualizing.homEquiv_homEquiv_comp_homCurryIso_hom`: currying a morphism is
transposing it twice and reassociating.  It is the mixed-universe counterpart of
`StacksDraft.DerivedHom.DerivedInternalHom.Model.comp_curryingIso_hom`, which exists only when the
module universe equals the ring universe.

The second half states the two coherences and proves them equivalent, for an arbitrary adjunction
and an arbitrary comparison of internal-Hom bifunctors:

* `StacksDraft.DerivedHom.DerivedHomAdjunction.LaxTensorAssoc` — the pentagon of the lax tensor
  comparison at a triple of objects.
* `StacksDraft.DerivedHom.DerivedHomAdjunction.HomMateCurryCompat` — the Eilenberg--Kelly closed
  functor axiom for the induced internal-Hom comparison
  `StacksDraft.DerivedHom.DerivedHomAdjunction.homOfHomMate`: currying commutes with it, the two
  currying isomorphisms of [stacks 0A65] being conjugated by the lax tensor comparison.
* `StacksDraft.DerivedHom.DerivedHomAdjunction.laxTensorAssoc_of_homMateCurryCompat` and
  `StacksDraft.DerivedHom.DerivedHomAdjunction.homMateCurryCompat_of_laxTensorAssoc` — the two
  implications.  Neither needs invertibility of anything, a pentagon for either associator, or a
  derived-category model: both are transposition calculus.

The third part transports the pentagon along isomorphisms of all three of its arguments, which is
what reduces it from arbitrary objects to classes of K-flat complexes.  Both sides are named,
`StacksDraft.DerivedHom.DerivedHomAdjunction.laxTensorAssocLhs` and
`StacksDraft.DerivedHom.DerivedHomAdjunction.laxTensorAssocRhs`, and each is shown natural in all
three arguments out of
`StacksDraft.DerivedHom.DerivedHomAdjunction.laxTensorOfHomMate_naturality` and the naturality of
the associator of the bundle it belongs to; `F` applied to an isomorphism is monic, which is what
cancels.  At derived base change
`Dualizing.derivedTensorBaseChangeAssoc_of_kFlat` is the resulting reduction: the pentagon at
every triple of localizations of K-flat complexes gives it at every triple of objects, every
object of `D(R)` being isomorphic to such a localization by `Dualizing.exists_kFlat_iso`.

The pentagon turns out to be the closed-functor axiom precomposed with `F` applied to a
coevaluation, which is why the first implication is immediate once the currying law is available;
the converse cancels that coevaluation against an evaluation by the triangle identity of
[stacks 0A63].

## What is not proved

Neither coherence, at arbitrary objects or at K-flat representatives.  Two of the four shapes in
which this chapter's one remaining coherence has been stated --- the pentagon of `μ`, the
associativity of the canonical projection morphism `ω` of
`StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaCounit`, [stacks 0E1W] against
currying, and `Dualizing.ProjectionFormula.CanonicalTensorBaseChangeCoherence` --- are joined by a
theorem rather than by a module docstring, and the statement is now reduced to a triple of K-flat
representatives; what stands at those representatives is still open.

A determinate chain-level value for `μ` is no longer what it needs: that value now exists.
`Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange_eq_of_models_monoidalIso` gives the
morphism of [stacks 0E1X] a value with no existential in it and with the degreewise monoidality
isomorphism `CochainComplex.ExtendScalars.extendScalarsMonoidalIso` --- the chain-level `μ` --- as
its only chain map.  It is
`Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange_eq_of_models_Q` with its one opaque
factor replaced by
`Stacks.DerivedHom.BaseChangeIso.derivedHomChangeOfRingsModelIso_hom_eq_monoidalIso`, which is in
turn `Stacks.DerivedHom.BaseChangeIso.derivedHomChangeOfRingsModelIso_hom_eq_homComplex` with the
Hom-complex change-of-rings map eliminated by
`Stacks.DerivedHom.BaseChangeIso.inv_Q_map_homComplexChangeOfRingsMap_eq` --- the solved-for form
of the localized double transpose, which supersedes
`Stacks.DerivedHom.BaseChangeIso.homComplexChangeOfRingsMap_derived_of_hom` for this purpose
because it quantifies over no auxiliary morphism.  And
`Dualizing.derivedTensorBaseChange_eq_evaluation` carries that value to `μ` itself, so the chain
map produced existentially by `Dualizing.derivedTensorBaseChange_eq_model` is not needed anywhere.

What the coherence needs is therefore not a value but a *coherence of the value*, and that breaks
into three links, of which this library now has the first:

* the pentagon of `CochainComplex.ExtendScalars.extendScalarsMonoidalIso` at the chain level.
  **Proved**, by `CochainComplex.ExtendScalars.extendScalarsMonoidalIso_associativity`: the
  Eilenberg--Kelly associativity axiom of the degreewise comparison, unconditionally and for
  arbitrary cochain complexes.  The comparison is still assembled by hand rather than obtained
  from a `CategoryTheory.Functor.Monoidal` instance on cochain complexes, so the axiom does not
  come with it and is proved directly: both sides are read on the summand of a tridegree, where
  each becomes the module-level comparison of the three components and the identity is
  `CategoryTheory.Functor.LaxMonoidal.associativity` for `ModuleCat.extendScalars`.  The
  triple-summand description of `HomologicalComplex.associator` that this needs is
  `CochainComplex.ExtendScalars.ιTensorObj_associator_hom`, which reads Mathlib's
  `HomologicalComplex.ι_mapBifunctorAssociatorX_hom` --- stated on the *components* of the
  associator isomorphism, not on the isomorphism --- through
  `HomologicalComplex.mapBifunctor₁₂.ι_eq` and `HomologicalComplex.mapBifunctor₂₃.ι_eq`.  No
  Koszul sign enters: the signs of a total complex live in its differentials, and the associator
  is summandwise the pointwise associator.
* the identification of `μ` at a pair of localizations of K-flat complexes with
  `CochainComplex.ExtendScalars.derivedMonoidalIso`.  This is the conjugation the value above has
  still to be pushed through: the units and counits of the two scalar equivalences, the components
  of `Stacks.DerivedHom.BaseChange.scalarRestrictionIso`, the three transports along
  `Stacks.DerivedHom.BaseChange.isoQObjPreimage`, and the bridge
  `StacksDraft.DerivedHom.DerivedHomAdjunction.transportHomEquiv_apply_functor_obj` between
  `StacksDraft.DerivedHom.DerivedInternalHom.Model.homEquiv` and
  `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing`.  That list is not quite the whole
  conjugation: the comparison
  `Stacks.DerivedHom.BaseChange.derivedExtensionScalarsLiftIso` of the two composite left adjoints
  occurs in it as well — it is what the units, counits and `δ` of the third factor of
  `Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_hom_app_kFlatKInjective_Q` are the
  expansion of — and it is available in both directions, by
  `Stacks.DerivedHom.BaseChange.derivedExtensionScalarsLiftIso_inv_app` and
  `Stacks.DerivedHom.BaseChange.derivedExtensionScalarsLiftIso_hom_app`.  Which direction is
  wanted is decided by the shape the identification is read in:
  `Dualizing.tensorBaseChangeMor_eq_iff_natIso_inv` reads the component of [stacks 0E1W] through
  its inverse, which is the direction whose model value
  `Stacks.DerivedHom.BaseChangeIso.derivedHomChangeOfRingsModelIso_inv_eq_monoidalIso` inverts
  nothing, matching the value
  `Dualizing.tensorBaseChangeMor_comp_eq_q_obj` of the [stacks 068I] candidate; so what is missing
  is the inverse of that four-factor conjugation, every factor of which is a component of an
  isomorphism with a value in both directions.
* the transport of the pentagon along isomorphisms of all three arguments, which is what reduces
  it from arbitrary objects to classes of K-flat complexes.  **Proved**, unconditionally, by
  `StacksDraft.DerivedHom.DerivedHomAdjunction.laxTensorAssoc_of_iso` and its instance
  `Dualizing.derivedTensorBaseChangeAssoc_of_kFlat`.  It is pure naturality of
  `Dualizing.derivedTensorBaseChange` and of the two associators, with the product-category pair
  spellings given the splitting treatment of
  `StacksDraft.DerivedHom.DerivedHomAdjunction.laxTensorOfHomMate_naturality`.  An earlier
  version of this docstring said it could not be built before the previous link, because it
  transports a *derived* pentagon which does not yet exist; that is not so.  The pentagon is a
  `Prop` at every triple whether or not it holds at any, and the transport is an implication
  between two of its instances, so it needs no pentagon as input.  What does wait on the previous
  link is the transport of the pentagon of
  `CochainComplex.ExtendScalars.derivedMonoidalIso`, which asserts a pentagon rather than
  assuming one; that is a different statement and is not what is proved here.

  One prerequisite of that transport is no longer missing, and why it was missing is worth
  recording: the associator of `CochainComplex.DerivedTensor.canonicalDerivedTensorProduct` had no
  name.  [stacks 0BYJ] is stated as
  `CochainComplex.DerivedTensor.derivedTensorProduct_associator`, which *exhibits* an associator
  together with its naturality and its K-flat comparison law under an existential quantifier, and
  a compatibility of `μ` with the associator cannot be written against an existential.  The
  associator that theorem quantifies over is now public, as
  `CochainComplex.DerivedTensor.derivedAssociator` with component
  `CochainComplex.DerivedTensor.derivedAssociatorIso`, and the law that determines it — its value
  on K-flat representatives, i.e. its compatibility with the K-flat comparison of the derived
  tensor product — is `CochainComplex.DerivedTensor.derivedAssociatorIso_comparison`; naturality
  in all three arguments is naturality of `derivedAssociator` at a triple of morphisms.  This is
  the half of the transport that does not wait on the previous link, and it is why the pentagon
  does not transport cheaply to `CochainComplex.ExtendScalars.derivedMonoidalIso`: the transport
  needs that comparison law, not merely the existence of some associator.

None of the three is derivable from the adjunction data alone.  The change-of-rings isomorphism of
[stacks 0E1W] is equivalent to the data of a natural isomorphism `μ`, and a natural isomorphism
need not be monoidal --- twist one by any non-coherent natural automorphism --- so the coherence
is not a formal consequence of the transposition calculus of this file.

## Main results

* `Dualizing.comp_homCurryIso_hom`, `Dualizing.homEquiv_homEquiv_comp_homCurryIso_hom`,
  `Dualizing.comp_homCurryIso_inv` — the characterizing law of [stacks 0A65] for an arbitrary
  tensor--Hom adjunction bundle.
* `Dualizing.tensorHomUnit_comp_homCurryIso_hom` — currying the coevaluation of [stacks 0A63] at
  a tensor product gives the double transpose of the associator.
* `StacksDraft.DerivedHom.DerivedHomAdjunction.homOfHomMate` — the internal-Hom comparison induced
  by a comparison of internal-Hom bifunctors along an adjunction, i.e. the morphism of which the
  lax tensor comparison is the mate.
* `StacksDraft.DerivedHom.DerivedHomAdjunction.laxTensorAssoc_iff_homMateCurryCompat` — **the
  equivalence**.
* `Dualizing.DerivedTensorBaseChangeAssoc` and `Dualizing.DerivedHomBaseChangeCurryCompat` — the
  two coherences at derived base change, in the vocabulary of
  `Dualizing.derivedTensorBaseChange` and of the morphism of [stacks 0E1X].
* `Dualizing.derivedTensorBaseChangeAssoc_iff_curryCompat` — **the instance**: the pentagon of `μ`
  is the compatibility of [stacks 0E1X], hence of [stacks 0E1W], with currying.
* `StacksDraft.DerivedHom.DerivedHomAdjunction.laxTensorAssocLhs_naturality` and
  `StacksDraft.DerivedHom.DerivedHomAdjunction.laxTensorAssocRhs_naturality` — the two sides of
  the pentagon are natural in all three arguments.
* `StacksDraft.DerivedHom.DerivedHomAdjunction.laxTensorAssoc_of_iso`,
  `Dualizing.derivedTensorBaseChangeAssoc_of_iso`,
  `Dualizing.derivedTensorBaseChangeAssoc_of_kFlat`,
  `Dualizing.derivedHomBaseChangeCurryCompat_of_kFlat` — **the reduction to K-flat
  representatives**.

## Implementation notes

The abstract statements are made for variable bundles `d`, `d'`, a variable adjunction `a` and a
variable comparison `m`, and only then instantiated; written directly at the base-change square the
unifier does not cope with the resulting composites.

Morphisms of the product category are written as raw pairs with a `show`, as everywhere else in
this directory: `CategoryTheory.Functor.prod` normalizes them to `CategoryTheory.Prod.mkHom`, and
keyed matching does not fire across that.

No `@[stacks]` attribute is placed here.  The currying law is a characterization of
`Dualizing.homCurryIso`, which carries no tag of its own because [stacks 0A65] is covered by
`StacksDraft.DerivedHom.derivedHomCurrying`; the two coherences are open.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0A65](https://stacks.math.columbia.edu/tag/0A65)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
* [Stacks Project, Tag 0E2H](https://stacks.math.columbia.edu/tag/0E2H)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom

namespace Dualizing

noncomputable section

universe u v w

section Curry

variable {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
  (d : DerivedHomAdjunction R)

/-- **The characterizing law of the currying isomorphism of [stacks 0A65].**  For a morphism
`α : Z ⟶ RHom(X ⊗ᴸ Y, M)`, currying `α` is transposing it twice and reassociating.

`Dualizing.homCurryIso` is built by Yoneda from exactly this formula, so the content is that the
formula may be read at an arbitrary `α` and not only at the identity.  Naturality of the
associator in its outer factor is what crosses that gap. -/
theorem comp_homCurryIso_hom (X Y M Z : DerivedCategory (ModuleCat.{v} R))
    (α : Z ⟶ d.hom.obj (Opposite.op (d.tensor.obj (X, Y)), M)) :
    α ≫ (homCurryIso d X Y M).hom =
      (d.homEquiv Z X (d.hom.obj (Opposite.op Y, M))).symm
        ((d.homEquiv (d.tensor.obj (Z, X)) Y M).symm
          ((d.tensorAssoc Z X Y).hom ≫ d.homEquiv Z (d.tensor.obj (X, Y)) M α)) := by
  have hhom : (homCurryIso d X Y M).hom =
      (d.homEquiv (d.hom.obj (Opposite.op (d.tensor.obj (X, Y)), M)) X
          (d.hom.obj (Opposite.op Y, M))).symm
        ((d.homEquiv (d.tensor.obj (d.hom.obj (Opposite.op (d.tensor.obj (X, Y)), M), X))
            Y M).symm
          ((d.tensorAssoc (d.hom.obj (Opposite.op (d.tensor.obj (X, Y)), M)) X Y).hom ≫
            d.homEquiv (d.hom.obj (Opposite.op (d.tensor.obj (X, Y)), M))
              (d.tensor.obj (X, Y)) M (𝟙 _))) := rfl
  rw [hhom]
  apply (d.homEquiv Z X (d.hom.obj (Opposite.op Y, M))).injective
  apply (d.homEquiv (d.tensor.obj (Z, X)) Y M).injective
  rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, d.homEquiv_naturality_left,
    d.homEquiv_naturality_left, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
    reassoc_of% tensorAssoc_hom_naturality d X Y α, ← d.homEquiv_naturality_left,
    Category.comp_id]

/-- **The currying law in transposed form.**  Applying the two transposition bijections of
[stacks 0A63] to a curried morphism gives the morphism itself, reassociated.  This is
`Dualizing.comp_homCurryIso_hom` with both `AddEquiv.symm`s cancelled, and it is the form in which
the law is used. -/
theorem homEquiv_homEquiv_comp_homCurryIso_hom (X Y M Z : DerivedCategory (ModuleCat.{v} R))
    (α : Z ⟶ d.hom.obj (Opposite.op (d.tensor.obj (X, Y)), M)) :
    d.homEquiv (d.tensor.obj (Z, X)) Y M
        (d.homEquiv Z X (d.hom.obj (Opposite.op Y, M)) (α ≫ (homCurryIso d X Y M).hom)) =
      (d.tensorAssoc Z X Y).hom ≫ d.homEquiv Z (d.tensor.obj (X, Y)) M α := by
  rw [comp_homCurryIso_hom d X Y M Z α, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- **The currying law, read on the inverse.**  For a morphism `β : Z ⟶ RHom(X, RHom(Y, M))`,
uncurrying `β` is transposing it twice and reassociating backwards. -/
theorem comp_homCurryIso_inv (X Y M Z : DerivedCategory (ModuleCat.{v} R))
    (β : Z ⟶ d.hom.obj (Opposite.op X, d.hom.obj (Opposite.op Y, M))) :
    β ≫ (homCurryIso d X Y M).inv =
      (d.homEquiv Z (d.tensor.obj (X, Y)) M).symm
        ((d.tensorAssoc Z X Y).inv ≫
          d.homEquiv (d.tensor.obj (Z, X)) Y M
            (d.homEquiv Z X (d.hom.obj (Opposite.op Y, M)) β)) := by
  rw [Iso.comp_inv_eq, comp_homCurryIso_hom d X Y M Z _, AddEquiv.apply_symm_apply,
    Iso.hom_inv_id_assoc, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]

/-- **Currying is detected by evaluation.**  The double transpose of the currying isomorphism
itself is the associator followed by the evaluation of [stacks 0A63] at the tensor product.  This
is `Dualizing.homEquiv_homEquiv_comp_homCurryIso_hom` at the identity. -/
theorem homEquiv_homEquiv_homCurryIso_hom (X Y M : DerivedCategory (ModuleCat.{v} R)) :
    d.homEquiv (d.tensor.obj (d.hom.obj (Opposite.op (d.tensor.obj (X, Y)), M), X)) Y M
        (d.homEquiv (d.hom.obj (Opposite.op (d.tensor.obj (X, Y)), M)) X
          (d.hom.obj (Opposite.op Y, M)) (homCurryIso d X Y M).hom) =
      (d.tensorAssoc (d.hom.obj (Opposite.op (d.tensor.obj (X, Y)), M)) X Y).hom ≫
        d.evaluation (d.tensor.obj (X, Y)) M := by
  rw [← Category.id_comp (homCurryIso d X Y M).hom,
    homEquiv_homEquiv_comp_homCurryIso_hom d X Y M _ (𝟙 _)]
  rfl

/-- **Currying the coevaluation of [stacks 0A63] at a tensor product gives the double transpose of
the associator.**  The coevaluation `X ⟶ RHom(Y ⊗ᴸ Z, X ⊗ᴸ (Y ⊗ᴸ Z))`, curried, is the double
transpose of `(X ⊗ᴸ Y) ⊗ᴸ Z ⟶ X ⊗ᴸ (Y ⊗ᴸ Z)`.

This is `Dualizing.comp_homCurryIso_hom` at the coevaluation, whose transpose is the identity. -/
theorem tensorHomUnit_comp_homCurryIso_hom (X Y Z : DerivedCategory (ModuleCat.{v} R)) :
    d.tensorHomUnit X (d.tensor.obj (Y, Z)) ≫
        (homCurryIso d Y Z (d.tensor.obj (X, d.tensor.obj (Y, Z)))).hom =
      (d.homEquiv X Y (d.hom.obj (Opposite.op Z,
          d.tensor.obj (X, d.tensor.obj (Y, Z))))).symm
        ((d.homEquiv (d.tensor.obj (X, Y)) Z
          (d.tensor.obj (X, d.tensor.obj (Y, Z)))).symm ((d.tensorAssoc X Y Z).hom)) := by
  rw [comp_homCurryIso_hom d Y Z _ X _]
  refine congrArg _ (congrArg _ ?_)
  rw [DerivedHomAdjunction.tensorHomUnit, AddEquiv.apply_symm_apply, Category.comp_id]

end Curry

end

end Dualizing

namespace StacksDraft.DerivedHom.DerivedHomAdjunction

noncomputable section

universe uR uA v v' w w'

section Bifunctor

variable {R : Type uR} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
  (d : DerivedHomAdjunction R)

/-- **The internal-Hom bifunctor at a pair of morphisms, in either order.**  The contravariant and
the covariant variable commute, both composites being the bifunctor at the pair. -/
@[reassoc]
theorem hom_map_left_comp_hom_map_right {L L' M M' : DerivedCategory (ModuleCat.{v} R)}
    (p : L' ⟶ L) (g : M ⟶ M') :
    d.hom.map (show (Opposite.op L, M) ⟶ (Opposite.op L, M') from (𝟙 (Opposite.op L), g)) ≫
        d.hom.map (show (Opposite.op L, M') ⟶ (Opposite.op L', M') from (p.op, 𝟙 M')) =
      d.hom.map (show (Opposite.op L, M) ⟶ (Opposite.op L', M) from (p.op, 𝟙 M)) ≫
        d.hom.map (show (Opposite.op L', M) ⟶ (Opposite.op L', M') from
          (𝟙 (Opposite.op L'), g)) := by
  rw [← d.hom.map_comp, ← d.hom.map_comp]
  congr 1
  simp only [prod_comp, Category.comp_id, Category.id_comp]

end Bifunctor

section Mate

variable {R : Type uR} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
  {A : Type uA} [CommRing A] [HasDerivedCategory.{w'} (ModuleCat.{v'} A)]
  (d : DerivedHomAdjunction R) (d' : DerivedHomAdjunction A)
  {F : DerivedCategory (ModuleCat.{v} R) ⥤ DerivedCategory (ModuleCat.{v'} A)}
  {G : DerivedCategory (ModuleCat.{v'} A) ⥤ DerivedCategory (ModuleCat.{v} R)}
  (a : F ⊣ G)
  (m : d.hom ⟶ F.op.prod F ⋙ d'.hom ⋙ G)

/-- **The internal-Hom comparison induced by a comparison of internal-Hom bifunctors.**  For an
adjunction `F ⊣ G` and a comparison `m : RHom(-, -) ⟶ G RHom(F -, F -)`, this is the transpose
along `a` of the component of `m`, a morphism

`F (RHom(L, K)) ⟶ RHom(F L, F K)`.

It is the morphism of which `StacksDraft.DerivedHom.DerivedHomAdjunction.laxTensorOfHomMate` is
the mate, by `StacksDraft.DerivedHom.DerivedHomAdjunction.homEquiv_laxTensorOfHomMate`; at derived
base change it is the morphism of [stacks 0E1X]. -/
def homOfHomMate (L K : DerivedCategory (ModuleCat.{v} R)) :
    F.obj (d.hom.obj (Opposite.op L, K)) ⟶
      d'.hom.obj (Opposite.op (F.obj L), F.obj K) :=
  (a.homEquiv (d.hom.obj (Opposite.op L, K))
    (d'.hom.obj (Opposite.op (F.obj L), F.obj K))).symm (m.app (Opposite.op L, K))

/-- **The lax tensor comparison is the mate of the internal-Hom comparison.**  This is
`StacksDraft.DerivedHom.DerivedHomAdjunction.homEquiv_laxTensorOfHomMate` with the transposed
component of `m` named `StacksDraft.DerivedHom.DerivedHomAdjunction.homOfHomMate`. -/
theorem homEquiv_homOfHomMate (L K : DerivedCategory (ModuleCat.{v} R)) :
    d'.homEquiv (F.obj (d.hom.obj (Opposite.op L, K))) (F.obj L) (F.obj K)
        (homOfHomMate d d' a m L K) =
      laxTensorOfHomMate d d' a m (d.hom.obj (Opposite.op L, K)) L ≫
        F.map (d.evaluation L K) :=
  homEquiv_laxTensorOfHomMate d d' a m L K

/-- `StacksDraft.DerivedHom.DerivedHomAdjunction.laxTensorOfHomMate_comp_map` with the transposed
component of `m` named. -/
theorem laxTensorOfHomMate_comp_map' (X Y W : DerivedCategory (ModuleCat.{v} R))
    (ψ : d.tensor.obj (X, Y) ⟶ W) :
    laxTensorOfHomMate d d' a m X Y ≫ F.map ψ =
      d'.homEquiv (F.obj X) (F.obj Y) (F.obj W)
        (F.map ((d.homEquiv X Y W).symm ψ) ≫ homOfHomMate d d' a m Y W) :=
  laxTensorOfHomMate_comp_map d d' a m X Y W ψ

/-- `StacksDraft.DerivedHom.DerivedHomAdjunction.laxTensorOfHomMate_eq` with the transposed
component of `m` named. -/
theorem laxTensorOfHomMate_eq' (X Y : DerivedCategory (ModuleCat.{v} R)) :
    laxTensorOfHomMate d d' a m X Y =
      d'.homEquiv (F.obj X) (F.obj Y) (F.obj (d.tensor.obj (X, Y)))
        (F.map (d.tensorHomUnit X Y) ≫
          homOfHomMate d d' a m Y (d.tensor.obj (X, Y))) :=
  laxTensorOfHomMate_eq d d' a m X Y

/-- **The induced internal-Hom comparison is natural in the target.**  This is the naturality of
`m` at a morphism `(𝟙, g)`, transposed along `a`: the transposition bijection is natural in both
arguments, so the two transposition identities turn the one naturality square into the other. -/
@[reassoc]
theorem map_hom_map_comp_homOfHomMate (L : DerivedCategory (ModuleCat.{v} R))
    {K K' : DerivedCategory (ModuleCat.{v} R)} (g : K ⟶ K') :
    F.map (d.hom.map (show (Opposite.op L, K) ⟶ (Opposite.op L, K') from
          (𝟙 (Opposite.op L), g))) ≫ homOfHomMate d d' a m L K' =
      homOfHomMate d d' a m L K ≫
        d'.hom.map (show (Opposite.op (F.obj L), F.obj K) ⟶ (Opposite.op (F.obj L), F.obj K') from
          (𝟙 (Opposite.op (F.obj L)), F.map g)) := by
  have hm := m.naturality ((𝟙 (Opposite.op L), g) :
    (Opposite.op L, K) ⟶ (Opposite.op L, K'))
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.prod_map] at hm
  rw [CategoryTheory.Functor.map_id] at hm
  have hm' : d.hom.map ((𝟙 (Opposite.op L), g) : (Opposite.op L, K) ⟶ (Opposite.op L, K')) ≫
        m.app (Opposite.op L, K') =
      m.app (Opposite.op L, K) ≫
        G.map (d'.hom.map ((𝟙 (Opposite.op (F.obj L)), F.map g) :
          (Opposite.op (F.obj L), F.obj K) ⟶ (Opposite.op (F.obj L), F.obj K'))) := hm
  dsimp only [homOfHomMate]
  rw [← a.homEquiv_naturality_left_symm, hm', ← a.homEquiv_naturality_right_symm]

/-- **The currying isomorphism of [stacks 0A65] is natural in the target.**  Both sides transpose
twice, by `Dualizing.homEquiv_homEquiv_comp_homCurryIso_hom`, to the associator followed by
evaluation and `g`. -/
@[reassoc]
theorem hom_map_comp_homCurryIso_hom (Y Z : DerivedCategory (ModuleCat.{v} R))
    {N N' : DerivedCategory (ModuleCat.{v} R)} (g : N ⟶ N') :
    d.hom.map (show (Opposite.op (d.tensor.obj (Y, Z)), N) ⟶
          (Opposite.op (d.tensor.obj (Y, Z)), N') from
        (𝟙 (Opposite.op (d.tensor.obj (Y, Z))), g)) ≫
        (Dualizing.homCurryIso d Y Z N').hom =
      (Dualizing.homCurryIso d Y Z N).hom ≫
        d.hom.map (show (Opposite.op Y, d.hom.obj (Opposite.op Z, N)) ⟶
              (Opposite.op Y, d.hom.obj (Opposite.op Z, N')) from
            (𝟙 (Opposite.op Y),
              d.hom.map (show (Opposite.op Z, N) ⟶ (Opposite.op Z, N') from
                (𝟙 (Opposite.op Z), g)))) := by
  refine (d.homEquiv _ Y _).injective ((d.homEquiv _ Z N').injective ?_)
  rw [Dualizing.homEquiv_homEquiv_comp_homCurryIso_hom d Y Z N' _ _, d.homEquiv_naturality_right,
    d.homEquiv_naturality_right, Dualizing.homEquiv_homEquiv_homCurryIso_hom d Y Z N,
    Category.assoc]
  exact congrArg _ ((congrArg (d.homEquiv _ _ _) (Category.id_comp _).symm).trans
    (d.homEquiv_naturality_right g (𝟙 _)))

/-! ### The two coherences -/

/-- **The pentagon of the lax tensor comparison** at a triple of objects: comparing `(X ⊗ᴸ Y) ⊗ᴸ Z`
to `F ((X ⊗ᴸ Y) ⊗ᴸ Z)` in the two possible orders agrees, modulo the two associators.

This is the associativity of `μ` that the second input of [stacks 0E2H] is waiting for, by
`Dualizing.ProjectionFormula.canonicalProjTensorBaseChangeCompat_iff_coherence`.  No pentagon is
assumed for either associator and no invertibility of `μ` is used. -/
def LaxTensorAssoc (X Y Z : DerivedCategory (ModuleCat.{v} R)) : Prop :=
  d'.tensor.map (show (d'.tensor.obj (F.obj X, F.obj Y), F.obj Z) ⟶
          (F.obj (d.tensor.obj (X, Y)), F.obj Z) from
        (laxTensorOfHomMate d d' a m X Y, 𝟙 (F.obj Z))) ≫
      laxTensorOfHomMate d d' a m (d.tensor.obj (X, Y)) Z ≫
        F.map (d.tensorAssoc X Y Z).hom =
    (d'.tensorAssoc (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
      d'.tensor.map (show (F.obj X, d'.tensor.obj (F.obj Y, F.obj Z)) ⟶
            (F.obj X, F.obj (d.tensor.obj (Y, Z))) from
          (𝟙 (F.obj X), laxTensorOfHomMate d d' a m Y Z)) ≫
        laxTensorOfHomMate d d' a m X (d.tensor.obj (Y, Z))

/-- The left-hand side of the closed-functor currying axiom: curry over the source ring, then
compare twice. -/
def homMateCurryLhs (Y Z N : DerivedCategory (ModuleCat.{v} R)) :
    F.obj (d.hom.obj (Opposite.op (d.tensor.obj (Y, Z)), N)) ⟶
      d'.hom.obj (Opposite.op (F.obj Y), d'.hom.obj (Opposite.op (F.obj Z), F.obj N)) :=
  F.map (Dualizing.homCurryIso d Y Z N).hom ≫
    homOfHomMate d d' a m Y (d.hom.obj (Opposite.op Z, N)) ≫
      d'.hom.map (show (Opposite.op (F.obj Y), F.obj (d.hom.obj (Opposite.op Z, N))) ⟶
            (Opposite.op (F.obj Y), d'.hom.obj (Opposite.op (F.obj Z), F.obj N)) from
          (𝟙 (Opposite.op (F.obj Y)), homOfHomMate d d' a m Z N))

/-- The right-hand side of the closed-functor currying axiom: compare once, restrict along the lax
tensor comparison, then curry over the target ring. -/
def homMateCurryRhs (Y Z N : DerivedCategory (ModuleCat.{v} R)) :
    F.obj (d.hom.obj (Opposite.op (d.tensor.obj (Y, Z)), N)) ⟶
      d'.hom.obj (Opposite.op (F.obj Y), d'.hom.obj (Opposite.op (F.obj Z), F.obj N)) :=
  homOfHomMate d d' a m (d.tensor.obj (Y, Z)) N ≫
    d'.hom.map (show (Opposite.op (F.obj (d.tensor.obj (Y, Z))), F.obj N) ⟶
          (Opposite.op (d'.tensor.obj (F.obj Y, F.obj Z)), F.obj N) from
        ((laxTensorOfHomMate d d' a m Y Z).op, 𝟙 (F.obj N))) ≫
      (Dualizing.homCurryIso d' (F.obj Y) (F.obj Z) (F.obj N)).hom

/-- **The closed-functor currying axiom of Eilenberg--Kelly**, i.e. the coherence of the lax
tensor comparison against the currying isomorphism of [stacks 0A65]: currying over the source ring
and comparing twice is comparing once, restricting along the lax tensor comparison, and currying
over the target ring.

At derived base change this is the compatibility of the change-of-rings isomorphism of
[stacks 0E1W] with currying, which the module documentation of
`StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaEvaluation` names as the residue of
the second input of [stacks 0E2H]. -/
def HomMateCurryCompat (Y Z N : DerivedCategory (ModuleCat.{v} R)) : Prop :=
  homMateCurryLhs d d' a m Y Z N = homMateCurryRhs d d' a m Y Z N

/-! ### The pentagon is the currying axiom along a coevaluation -/

/-- **The pentagon of the lax tensor comparison is the closed-functor currying axiom precomposed
with `F` applied to a coevaluation.**  Both sides of the pentagon are double transposes over
[stacks 0A63] at the target ring: the left one because the lax tensor comparison followed by `F`
applied to a morphism out of a tensor product is a transpose
(`StacksDraft.DerivedHom.DerivedHomAdjunction.laxTensorOfHomMate_comp_map`), applied twice; the
right one because the associator of the target ring is removed by the currying law
`Dualizing.homEquiv_homEquiv_comp_homCurryIso_hom`.  The double transposes being bijections, the
pentagon *is* the resulting equation, and the coevaluation appears because the double transpose of
the source associator is the curried coevaluation
(`Dualizing.tensorHomUnit_comp_homCurryIso_hom`). -/
theorem laxTensorAssoc_iff_comp_tensorHomUnit
    (X Y Z : DerivedCategory (ModuleCat.{v} R)) :
    LaxTensorAssoc d d' a m X Y Z ↔
      F.map (d.tensorHomUnit X (d.tensor.obj (Y, Z))) ≫
          homMateCurryLhs d d' a m Y Z (d.tensor.obj (X, d.tensor.obj (Y, Z))) =
        F.map (d.tensorHomUnit X (d.tensor.obj (Y, Z))) ≫
          homMateCurryRhs d d' a m Y Z (d.tensor.obj (X, d.tensor.obj (Y, Z))) := by
  have hL : d'.tensor.map (show (d'.tensor.obj (F.obj X, F.obj Y), F.obj Z) ⟶
            (F.obj (d.tensor.obj (X, Y)), F.obj Z) from
          (laxTensorOfHomMate d d' a m X Y, 𝟙 (F.obj Z))) ≫
        laxTensorOfHomMate d d' a m (d.tensor.obj (X, Y)) Z ≫
          F.map (d.tensorAssoc X Y Z).hom =
      d'.homEquiv (d'.tensor.obj (F.obj X, F.obj Y)) (F.obj Z)
          (F.obj (d.tensor.obj (X, d.tensor.obj (Y, Z))))
        (d'.homEquiv (F.obj X) (F.obj Y)
          (d'.hom.obj (Opposite.op (F.obj Z),
            F.obj (d.tensor.obj (X, d.tensor.obj (Y, Z)))))
          (F.map (d.tensorHomUnit X (d.tensor.obj (Y, Z))) ≫
            homMateCurryLhs d d' a m Y Z (d.tensor.obj (X, d.tensor.obj (Y, Z))))) := by
    have hinner : F.map (d.tensorHomUnit X (d.tensor.obj (Y, Z))) ≫
          homMateCurryLhs d d' a m Y Z (d.tensor.obj (X, d.tensor.obj (Y, Z))) =
        (F.map ((d.homEquiv X Y (d.hom.obj (Opposite.op Z,
                  d.tensor.obj (X, d.tensor.obj (Y, Z))))).symm
              ((d.homEquiv (d.tensor.obj (X, Y)) Z
                (d.tensor.obj (X, d.tensor.obj (Y, Z)))).symm (d.tensorAssoc X Y Z).hom)) ≫
            homOfHomMate d d' a m Y
              (d.hom.obj (Opposite.op Z, d.tensor.obj (X, d.tensor.obj (Y, Z))))) ≫
          d'.hom.map (show (Opposite.op (F.obj Y),
                F.obj (d.hom.obj (Opposite.op Z, d.tensor.obj (X, d.tensor.obj (Y, Z))))) ⟶
              (Opposite.op (F.obj Y), d'.hom.obj (Opposite.op (F.obj Z),
                F.obj (d.tensor.obj (X, d.tensor.obj (Y, Z))))) from
            (𝟙 (Opposite.op (F.obj Y)),
              homOfHomMate d d' a m Z (d.tensor.obj (X, d.tensor.obj (Y, Z))))) := by
      dsimp only [homMateCurryLhs]
      rw [← Category.assoc (F.map (d.tensorHomUnit X (d.tensor.obj (Y, Z))))
          (F.map (Dualizing.homCurryIso d Y Z (d.tensor.obj (X, d.tensor.obj (Y, Z)))).hom),
        ← F.map_comp, Dualizing.tensorHomUnit_comp_homCurryIso_hom d X Y Z,
        ← Category.assoc]
    rw [laxTensorOfHomMate_comp_map' d d' a m (d.tensor.obj (X, Y)) Z _
        (d.tensorAssoc X Y Z).hom,
      ← d'.homEquiv_naturality_left]
    refine congrArg _ ?_
    rw [← Category.assoc, laxTensorOfHomMate_comp_map' d d' a m X Y _ _, hinner,
      d'.homEquiv_naturality_right]
  have hR : (d'.tensorAssoc (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
        d'.tensor.map (show (F.obj X, d'.tensor.obj (F.obj Y, F.obj Z)) ⟶
              (F.obj X, F.obj (d.tensor.obj (Y, Z))) from
            (𝟙 (F.obj X), laxTensorOfHomMate d d' a m Y Z)) ≫
          laxTensorOfHomMate d d' a m X (d.tensor.obj (Y, Z)) =
      d'.homEquiv (d'.tensor.obj (F.obj X, F.obj Y)) (F.obj Z)
          (F.obj (d.tensor.obj (X, d.tensor.obj (Y, Z))))
        (d'.homEquiv (F.obj X) (F.obj Y)
          (d'.hom.obj (Opposite.op (F.obj Z),
            F.obj (d.tensor.obj (X, d.tensor.obj (Y, Z)))))
          (F.map (d.tensorHomUnit X (d.tensor.obj (Y, Z))) ≫
            homMateCurryRhs d d' a m Y Z (d.tensor.obj (X, d.tensor.obj (Y, Z))))) := by
    have hb : F.map (d.tensorHomUnit X (d.tensor.obj (Y, Z))) ≫
          homMateCurryRhs d d' a m Y Z (d.tensor.obj (X, d.tensor.obj (Y, Z))) =
        ((F.map (d.tensorHomUnit X (d.tensor.obj (Y, Z))) ≫
              homOfHomMate d d' a m (d.tensor.obj (Y, Z))
                (d.tensor.obj (X, d.tensor.obj (Y, Z)))) ≫
            d'.hom.map (show (Opposite.op (F.obj (d.tensor.obj (Y, Z))),
                  F.obj (d.tensor.obj (X, d.tensor.obj (Y, Z)))) ⟶
                (Opposite.op (d'.tensor.obj (F.obj Y, F.obj Z)),
                  F.obj (d.tensor.obj (X, d.tensor.obj (Y, Z)))) from
              ((laxTensorOfHomMate d d' a m Y Z).op,
                𝟙 (F.obj (d.tensor.obj (X, d.tensor.obj (Y, Z))))))) ≫
          (Dualizing.homCurryIso d' (F.obj Y) (F.obj Z)
            (F.obj (d.tensor.obj (X, d.tensor.obj (Y, Z))))).hom := by
      dsimp only [homMateCurryRhs]
      rw [Category.assoc, Category.assoc]
    rw [hb, Dualizing.homEquiv_homEquiv_comp_homCurryIso_hom d' (F.obj Y) (F.obj Z) _ (F.obj X) _,
      d'.homEquiv_dinaturality, ← laxTensorOfHomMate_eq' d d' a m X (d.tensor.obj (Y, Z))]
  rw [LaxTensorAssoc, hL, hR]
  exact (AddEquiv.apply_eq_iff_eq _).trans (AddEquiv.apply_eq_iff_eq _)

/-- **The closed-functor currying axiom implies the pentagon.**  This is
`StacksDraft.DerivedHom.DerivedHomAdjunction.laxTensorAssoc_iff_comp_tensorHomUnit` read in the
easy direction: the axiom at `(Y, Z, X ⊗ᴸ (Y ⊗ᴸ Z))` is the pentagon at `(X, Y, Z)` with the
coevaluation already cancelled. -/
theorem laxTensorAssoc_of_homMateCurryCompat
    (X Y Z : DerivedCategory (ModuleCat.{v} R))
    (h : HomMateCurryCompat d d' a m Y Z (d.tensor.obj (X, d.tensor.obj (Y, Z)))) :
    LaxTensorAssoc d d' a m X Y Z :=
  (laxTensorAssoc_iff_comp_tensorHomUnit d d' a m X Y Z).2 (congrArg _ h)

/-! ### Cancelling the coevaluation -/

/-- The left-hand side of the closed-functor currying axiom is natural in the target. -/
@[reassoc]
theorem map_hom_map_comp_homMateCurryLhs (Y Z : DerivedCategory (ModuleCat.{v} R))
    {N N' : DerivedCategory (ModuleCat.{v} R)} (g : N ⟶ N') :
    F.map (d.hom.map (show (Opposite.op (d.tensor.obj (Y, Z)), N) ⟶
            (Opposite.op (d.tensor.obj (Y, Z)), N') from
          (𝟙 (Opposite.op (d.tensor.obj (Y, Z))), g))) ≫
        homMateCurryLhs d d' a m Y Z N' =
      homMateCurryLhs d d' a m Y Z N ≫
        d'.hom.map (show (Opposite.op (F.obj Y),
                d'.hom.obj (Opposite.op (F.obj Z), F.obj N)) ⟶
              (Opposite.op (F.obj Y), d'.hom.obj (Opposite.op (F.obj Z), F.obj N')) from
            (𝟙 (Opposite.op (F.obj Y)),
              d'.hom.map (show (Opposite.op (F.obj Z), F.obj N) ⟶
                    (Opposite.op (F.obj Z), F.obj N') from
                  (𝟙 (Opposite.op (F.obj Z)), F.map g)))) := by
  dsimp only [homMateCurryLhs]
  rw [← Category.assoc, ← F.map_comp, hom_map_comp_homCurryIso_hom d Y Z g, F.map_comp,
    Category.assoc, Category.assoc,
    map_hom_map_comp_homOfHomMate_assoc d d' a m Y
      (d.hom.map (show (Opposite.op Z, N) ⟶ (Opposite.op Z, N') from
        (𝟙 (Opposite.op Z), g))),
    d'.hom_map_comp_right, map_hom_map_comp_homOfHomMate d d' a m Z g,
    ← d'.hom_map_comp_right, Category.assoc]

/-- The right-hand side of the closed-functor currying axiom is natural in the target. -/
@[reassoc]
theorem map_hom_map_comp_homMateCurryRhs (Y Z : DerivedCategory (ModuleCat.{v} R))
    {N N' : DerivedCategory (ModuleCat.{v} R)} (g : N ⟶ N') :
    F.map (d.hom.map (show (Opposite.op (d.tensor.obj (Y, Z)), N) ⟶
            (Opposite.op (d.tensor.obj (Y, Z)), N') from
          (𝟙 (Opposite.op (d.tensor.obj (Y, Z))), g))) ≫
        homMateCurryRhs d d' a m Y Z N' =
      homMateCurryRhs d d' a m Y Z N ≫
        d'.hom.map (show (Opposite.op (F.obj Y),
                d'.hom.obj (Opposite.op (F.obj Z), F.obj N)) ⟶
              (Opposite.op (F.obj Y), d'.hom.obj (Opposite.op (F.obj Z), F.obj N')) from
            (𝟙 (Opposite.op (F.obj Y)),
              d'.hom.map (show (Opposite.op (F.obj Z), F.obj N) ⟶
                    (Opposite.op (F.obj Z), F.obj N') from
                  (𝟙 (Opposite.op (F.obj Z)), F.map g)))) := by
  dsimp only [homMateCurryRhs]
  rw [map_hom_map_comp_homOfHomMate_assoc d d' a m (d.tensor.obj (Y, Z)) g,
    hom_map_left_comp_hom_map_right_assoc d' (laxTensorOfHomMate d d' a m Y Z) (F.map g),
    hom_map_comp_homCurryIso_hom d' (F.obj Y) (F.obj Z) (F.map g), Category.assoc,
    Category.assoc]

/-- **The pentagon implies the closed-functor currying axiom.**  The axiom at `(Y, Z, N)` follows
from the pentagon at the *single* triple `(RHom(Y ⊗ᴸ Z, N), Y, Z)`: by
`StacksDraft.DerivedHom.DerivedHomAdjunction.laxTensorAssoc_iff_comp_tensorHomUnit` that pentagon
is the axiom at `(Y, Z, RHom(Y ⊗ᴸ Z, N) ⊗ᴸ (Y ⊗ᴸ Z))` precomposed with `F` applied to a
coevaluation, and both sides of the axiom are natural in the target, so composing with evaluation
cancels the coevaluation by the triangle identity of [stacks 0A63]. -/
theorem homMateCurryCompat_of_laxTensorAssoc (Y Z N : DerivedCategory (ModuleCat.{v} R))
    (h : LaxTensorAssoc d d' a m
      (d.hom.obj (Opposite.op (d.tensor.obj (Y, Z)), N)) Y Z) :
    HomMateCurryCompat d d' a m Y Z N := by
  have hcoev := (laxTensorAssoc_iff_comp_tensorHomUnit d d' a m
    (d.hom.obj (Opposite.op (d.tensor.obj (Y, Z)), N)) Y Z).1 h
  have hL := map_hom_map_comp_homMateCurryLhs d d' a m Y Z
    (d.evaluation (d.tensor.obj (Y, Z)) N)
  have hR := map_hom_map_comp_homMateCurryRhs d d' a m Y Z
    (d.evaluation (d.tensor.obj (Y, Z)) N)
  have hunit : F.map (d.tensorHomUnit (d.hom.obj (Opposite.op (d.tensor.obj (Y, Z)), N))
          (d.tensor.obj (Y, Z))) ≫
        F.map (d.hom.map (show (Opposite.op (d.tensor.obj (Y, Z)),
              d.tensor.obj (d.hom.obj (Opposite.op (d.tensor.obj (Y, Z)), N),
                d.tensor.obj (Y, Z))) ⟶
            (Opposite.op (d.tensor.obj (Y, Z)), N) from
          (𝟙 (Opposite.op (d.tensor.obj (Y, Z))), d.evaluation (d.tensor.obj (Y, Z)) N))) =
      𝟙 (F.obj (d.hom.obj (Opposite.op (d.tensor.obj (Y, Z)), N))) := by
    rw [← F.map_comp, d.tensorHomUnit_comp_map_evaluation, CategoryTheory.Functor.map_id]
  dsimp only [HomMateCurryCompat]
  rw [← Category.id_comp (homMateCurryLhs d d' a m Y Z N), ← hunit, Category.assoc, hL,
    ← Category.assoc, hcoev, Category.assoc, ← hR, ← Category.assoc, hunit, Category.id_comp]

/-- **The pentagon and the closed-functor currying axiom are equivalent.**  Each is the other at
one object: the axiom at `(Y, Z, N)` gives the pentagon at every `(X, Y, Z)` with that `N` read as
`X ⊗ᴸ (Y ⊗ᴸ Z)`, and the pentagon at the single triple `(RHom(Y ⊗ᴸ Z, N), Y, Z)` gives the axiom
at `(Y, Z, N)`.

So the associativity of the lax tensor comparison and the compatibility of the internal-Hom
comparison with the currying isomorphism of [stacks 0A65] are one statement, and at derived base
change that is the single residue of the second input of [stacks 0E2H]. -/
theorem laxTensorAssoc_iff_homMateCurryCompat (Y Z : DerivedCategory (ModuleCat.{v} R)) :
    (∀ X : DerivedCategory (ModuleCat.{v} R), LaxTensorAssoc d d' a m X Y Z) ↔
      ∀ N : DerivedCategory (ModuleCat.{v} R), HomMateCurryCompat d d' a m Y Z N :=
  ⟨fun h N => homMateCurryCompat_of_laxTensorAssoc d d' a m Y Z N (h _),
    fun h X => laxTensorAssoc_of_homMateCurryCompat d d' a m X Y Z (h _)⟩

/-! ### The pentagon transports along isomorphisms of its three arguments -/

/-- The left-hand side of the pentagon: compare the first two factors, then the result with the
third, then reassociate over the source ring. -/
def laxTensorAssocLhs (X Y Z : DerivedCategory (ModuleCat.{v} R)) :
    d'.tensor.obj (d'.tensor.obj (F.obj X, F.obj Y), F.obj Z) ⟶
      F.obj (d.tensor.obj (X, d.tensor.obj (Y, Z))) :=
  d'.tensor.map (show (d'.tensor.obj (F.obj X, F.obj Y), F.obj Z) ⟶
          (F.obj (d.tensor.obj (X, Y)), F.obj Z) from
        (laxTensorOfHomMate d d' a m X Y, 𝟙 (F.obj Z))) ≫
    laxTensorOfHomMate d d' a m (d.tensor.obj (X, Y)) Z ≫
      F.map (d.tensorAssoc X Y Z).hom

/-- The right-hand side of the pentagon: reassociate over the target ring, then compare the last
two factors, then the first with the result. -/
def laxTensorAssocRhs (X Y Z : DerivedCategory (ModuleCat.{v} R)) :
    d'.tensor.obj (d'.tensor.obj (F.obj X, F.obj Y), F.obj Z) ⟶
      F.obj (d.tensor.obj (X, d.tensor.obj (Y, Z))) :=
  (d'.tensorAssoc (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
    d'.tensor.map (show (F.obj X, d'.tensor.obj (F.obj Y, F.obj Z)) ⟶
          (F.obj X, F.obj (d.tensor.obj (Y, Z))) from
        (𝟙 (F.obj X), laxTensorOfHomMate d d' a m Y Z)) ≫
      laxTensorOfHomMate d d' a m X (d.tensor.obj (Y, Z))

/-- The pentagon is the equation between the two named sides. -/
theorem laxTensorAssoc_iff_lhs_eq_rhs (X Y Z : DerivedCategory (ModuleCat.{v} R)) :
    LaxTensorAssoc d d' a m X Y Z ↔
      laxTensorAssocLhs d d' a m X Y Z = laxTensorAssocRhs d d' a m X Y Z :=
  Iff.rfl

/-- **The left-hand side of the pentagon is natural in all three arguments.**  Two instances of
`StacksDraft.DerivedHom.DerivedHomAdjunction.laxTensorOfHomMate_naturality` and one of
`StacksDraft.DerivedHom.DerivedHomAdjunction.tensorAssoc_naturality` over the source ring. -/
theorem laxTensorAssocLhs_naturality
    {X X' Y Y' Z Z' : DerivedCategory (ModuleCat.{v} R)}
    (x : X ⟶ X') (y : Y ⟶ Y') (z : Z ⟶ Z') :
    laxTensorAssocLhs d d' a m X Y Z ≫
        F.map (d.tensor.map (show (X, d.tensor.obj (Y, Z)) ⟶ (X', d.tensor.obj (Y', Z')) from
          (x, d.tensor.map (show (Y, Z) ⟶ (Y', Z') from (y, z))))) =
      d'.tensor.map (show (d'.tensor.obj (F.obj X, F.obj Y), F.obj Z) ⟶
            (d'.tensor.obj (F.obj X', F.obj Y'), F.obj Z') from
          (d'.tensor.map (show (F.obj X, F.obj Y) ⟶ (F.obj X', F.obj Y') from
              (F.map x, F.map y)), F.map z)) ≫
        laxTensorAssocLhs d d' a m X' Y' Z' := by
  dsimp only [laxTensorAssocLhs]
  rw [Category.assoc, Category.assoc, ← F.map_comp, ← d.tensorAssoc_naturality, F.map_comp,
    ← laxTensorOfHomMate_naturality_assoc d d' a m
      (d.tensor.map (show (X, Y) ⟶ (X', Y') from (x, y))) z,
    d'.tensor_map_comp_assoc, Category.id_comp,
    ← laxTensorOfHomMate_naturality d d' a m x y,
    d'.tensor_map_comp_assoc (d'.tensor.map (show (F.obj X, F.obj Y) ⟶ (F.obj X', F.obj Y') from
        (F.map x, F.map y))) (F.map z) (laxTensorOfHomMate d d' a m X' Y') (𝟙 (F.obj Z')),
    Category.comp_id]

/-- **The right-hand side of the pentagon is natural in all three arguments.**  Two instances of
`StacksDraft.DerivedHom.DerivedHomAdjunction.laxTensorOfHomMate_naturality` and one of
`StacksDraft.DerivedHom.DerivedHomAdjunction.tensorAssoc_naturality` over the target ring. -/
theorem laxTensorAssocRhs_naturality
    {X X' Y Y' Z Z' : DerivedCategory (ModuleCat.{v} R)}
    (x : X ⟶ X') (y : Y ⟶ Y') (z : Z ⟶ Z') :
    laxTensorAssocRhs d d' a m X Y Z ≫
        F.map (d.tensor.map (show (X, d.tensor.obj (Y, Z)) ⟶ (X', d.tensor.obj (Y', Z')) from
          (x, d.tensor.map (show (Y, Z) ⟶ (Y', Z') from (y, z))))) =
      d'.tensor.map (show (d'.tensor.obj (F.obj X, F.obj Y), F.obj Z) ⟶
            (d'.tensor.obj (F.obj X', F.obj Y'), F.obj Z') from
          (d'.tensor.map (show (F.obj X, F.obj Y) ⟶ (F.obj X', F.obj Y') from
              (F.map x, F.map y)), F.map z)) ≫
        laxTensorAssocRhs d d' a m X' Y' Z' := by
  dsimp only [laxTensorAssocRhs]
  rw [Category.assoc, Category.assoc,
    d'.tensorAssoc_naturality_assoc (F.map x) (F.map y) (F.map z),
    d'.tensor_map_comp_assoc (F.map x) (d'.tensor.map (show (F.obj Y, F.obj Z) ⟶
        (F.obj Y', F.obj Z') from (F.map y, F.map z))) (𝟙 (F.obj X'))
      (laxTensorOfHomMate d d' a m Y' Z'),
    Category.comp_id (F.map x), laxTensorOfHomMate_naturality d d' a m y z,
    ← laxTensorOfHomMate_naturality d d' a m x (d.tensor.map (show (Y, Z) ⟶ (Y', Z') from (y, z))),
    d'.tensor_map_comp_assoc (𝟙 (F.obj X)) (laxTensorOfHomMate d d' a m Y Z) (F.map x)
      (F.map (d.tensor.map (show (Y, Z) ⟶ (Y', Z') from (y, z)))),
    Category.id_comp (F.map x)]

/-- **The pentagon transports along isomorphisms of all three arguments.**  Both sides are natural
by `StacksDraft.DerivedHom.DerivedHomAdjunction.laxTensorAssocLhs_naturality` and
`StacksDraft.DerivedHom.DerivedHomAdjunction.laxTensorAssocRhs_naturality`, and the morphism they
are postcomposed with is `F` applied to an isomorphism, so it is monic. -/
theorem laxTensorAssoc_of_iso {X X' Y Y' Z Z' : DerivedCategory (ModuleCat.{v} R)}
    (x : X ≅ X') (y : Y ≅ Y') (z : Z ≅ Z')
    (h : LaxTensorAssoc d d' a m X' Y' Z') :
    LaxTensorAssoc d d' a m X Y Z := by
  rw [laxTensorAssoc_iff_lhs_eq_rhs] at h ⊢
  have hF : IsIso (F.map (d.tensor.map (show (X, d.tensor.obj (Y, Z)) ⟶
      (X', d.tensor.obj (Y', Z')) from
      (x.hom, d.tensor.map (show (Y, Z) ⟶ (Y', Z') from (y.hom, z.hom)))))) :=
    (F.mapIso (d.tensor.mapIso (x.prod (d.tensor.mapIso (y.prod z))))).isIso_hom
  rw [← cancel_mono (F.map (d.tensor.map (show (X, d.tensor.obj (Y, Z)) ⟶
    (X', d.tensor.obj (Y', Z')) from
    (x.hom, d.tensor.map (show (Y, Z) ⟶ (Y', Z') from (y.hom, z.hom)))))),
    laxTensorAssocLhs_naturality, laxTensorAssocRhs_naturality, h]

end Mate

end

end StacksDraft.DerivedHom.DerivedHomAdjunction

namespace Dualizing

noncomputable section

universe uR uA uM

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
  (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
    DerivedCategory (ModuleCat.{max uR uA uM} A))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]

/-- **The induced internal-Hom comparison at derived base change is the morphism of
[stacks 0E1X].**  Both are the transpose along the adjunction of [stacks 0GMT] of the component of
`Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChangeMate`, the two internal-Hom bifunctors
being equal on the nose by `Dualizing.derivedHomAdjunctionOverRing_hom_eq`. -/
theorem homOfHomMate_eq_derivedHomBaseChange
    (L K : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    DerivedHomAdjunction.homOfHomMate
        (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R)
        (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A)
        (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, uM}
          f F comparison)
        (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChangeMate.{uR, uA, uM}
          f F comparison) L K =
      Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uA, uM} f F comparison L K :=
  rfl

/-- **The pentagon of the lax monoidal structure map of derived base change**, written in its own
vocabulary: comparing `(X ⊗ᴸ_R Y) ⊗ᴸ_R Z` with `F ((X ⊗ᴸ_R Y) ⊗ᴸ_R Z)` in the two orders agrees,
modulo the associators of [stacks 0A63] over `R` and over `A`.

By `Dualizing.ProjectionFormula.canonicalProjTensorBaseChangeCompat_iff_coherence` this is the
coherence the second input of [stacks 0E2H] reduces to, and by
`Dualizing.derivedTensorBaseChangeAssoc_iff_curryCompat` it is the compatibility of the morphism
of [stacks 0E1X] --- hence of the change-of-rings isomorphism of [stacks 0E1W] --- with the
currying isomorphism of [stacks 0A65]. -/
def DerivedTensorBaseChangeAssoc
    (X Y Z : DerivedCategory (ModuleCat.{max uR uA uM} R)) : Prop :=
  (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.map
        (show ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.obj
                (F.obj X, F.obj Y), F.obj Z) ⟶
              (F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
                max uR uA uM + 1} R).tensor.obj (X, Y)), F.obj Z) from
          (derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y, 𝟙 (F.obj Z))) ≫
      derivedTensorBaseChange.{uR, uA, uM} f F comparison
          ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.obj
            (X, Y)) Z ≫
        F.map ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
          max uR uA uM + 1} R).tensorAssoc X Y Z).hom =
    ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensorAssoc
        (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
      (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.map
          (show (F.obj X, (derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                  max uR uA uM + 1} A).tensor.obj (F.obj Y, F.obj Z)) ⟶
                (F.obj X, F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
                  max uR uA uM + 1} R).tensor.obj (Y, Z))) from
            (𝟙 (F.obj X), derivedTensorBaseChange.{uR, uA, uM} f F comparison Y Z)) ≫
        derivedTensorBaseChange.{uR, uA, uM} f F comparison X
          ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.obj (Y, Z))

/-- **The compatibility of the morphism of [stacks 0E1X] with the currying isomorphism of
[stacks 0A65]**, written in its own vocabulary: currying over `R` and base-changing twice is
base-changing once, restricting along the lax monoidal structure map, and currying over `A`.

Since the morphism of [stacks 0E1X] is derived Hom of the unit of [stacks 0GMT] followed by the
change-of-rings isomorphism of [stacks 0E1W]
(`Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange_homEquiv`), and the unit is natural,
this is the compatibility of [stacks 0E1W] with currying that the module documentation of
`StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaEvaluation` names as the residue of
the second input of [stacks 0E2H]. -/
def DerivedHomBaseChangeCurryCompat
    (Y Z N : DerivedCategory (ModuleCat.{max uR uA uM} R)) : Prop :=
  F.map (homCurryIso (derivedHomAdjunctionOverRing.{uR, max uR uA uM,
          max uR uA uM + 1} R) Y Z N).hom ≫
      Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uA, uM} f F comparison Y
          ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).hom.obj
            (Opposite.op Z, N)) ≫
        (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).hom.map
          (show (Opposite.op (F.obj Y),
                F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
                  max uR uA uM + 1} R).hom.obj (Opposite.op Z, N))) ⟶
              (Opposite.op (F.obj Y),
                (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).hom.obj
                  (Opposite.op (F.obj Z), F.obj N)) from
            (𝟙 (Opposite.op (F.obj Y)),
              Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uA, uM}
                f F comparison Z N)) =
    Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uA, uM} f F comparison
        ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.obj
          (Y, Z)) N ≫
      (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).hom.map
          (show (Opposite.op (F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
                  max uR uA uM + 1} R).tensor.obj (Y, Z))), F.obj N) ⟶
              (Opposite.op ((derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                  max uR uA uM + 1} A).tensor.obj (F.obj Y, F.obj Z)), F.obj N) from
            ((derivedTensorBaseChange.{uR, uA, uM} f F comparison Y Z).op, 𝟙 (F.obj N))) ≫
        (homCurryIso (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A)
          (F.obj Y) (F.obj Z) (F.obj N)).hom

/-- The pentagon of `Dualizing.derivedTensorBaseChange` is
`StacksDraft.DerivedHom.DerivedHomAdjunction.LaxTensorAssoc` at the data of derived base change:
`μ` *is* the lax tensor comparison of that data. -/
theorem derivedTensorBaseChangeAssoc_iff_laxTensorAssoc
    (X Y Z : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    DerivedTensorBaseChangeAssoc.{uR, uA, uM} f F comparison X Y Z ↔
      DerivedHomAdjunction.LaxTensorAssoc
        (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R)
        (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A)
        (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, uM}
          f F comparison)
        (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChangeMate.{uR, uA, uM}
          f F comparison) X Y Z :=
  Iff.rfl

/-- The currying compatibility of the morphism of [stacks 0E1X] is
`StacksDraft.DerivedHom.DerivedHomAdjunction.HomMateCurryCompat` at the data of derived base
change, by `Dualizing.homOfHomMate_eq_derivedHomBaseChange`. -/
theorem derivedHomBaseChangeCurryCompat_iff_homMateCurryCompat
    (Y Z N : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    DerivedHomBaseChangeCurryCompat.{uR, uA, uM} f F comparison Y Z N ↔
      DerivedHomAdjunction.HomMateCurryCompat
        (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R)
        (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A)
        (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, uM}
          f F comparison)
        (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChangeMate.{uR, uA, uM}
          f F comparison) Y Z N :=
  Iff.rfl

/-- **The associativity of the lax monoidal structure map of derived base change is the
compatibility of [stacks 0E1X] with the currying isomorphism of [stacks 0A65].**  This is
`StacksDraft.DerivedHom.DerivedHomAdjunction.laxTensorAssoc_iff_homMateCurryCompat` at the data of
derived base change: the adjunction of [stacks 0GMT] and the comparison
`Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChangeMate` built from the unit and the
change-of-rings isomorphism of [stacks 0E1W].

Unconditional, and with no K-flat representative, no invertibility and no model: it is
transposition calculus.  Both sides are open; what this buys is that the four shapes in which this
chapter's one remaining coherence has been stated --- the pentagon of `μ`, the associativity of the
canonical projection morphism `ω`, [stacks 0E1W] against currying, and
`Dualizing.ProjectionFormula.CanonicalTensorBaseChangeCoherence` --- now have two of them joined by
a theorem rather than by a module docstring. -/
theorem derivedTensorBaseChangeAssoc_iff_curryCompat
    (Y Z : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    (∀ X : DerivedCategory (ModuleCat.{max uR uA uM} R),
        DerivedTensorBaseChangeAssoc.{uR, uA, uM} f F comparison X Y Z) ↔
      ∀ N : DerivedCategory (ModuleCat.{max uR uA uM} R),
        DerivedHomBaseChangeCurryCompat.{uR, uA, uM} f F comparison Y Z N :=
  DerivedHomAdjunction.laxTensorAssoc_iff_homMateCurryCompat _ _ _ _ Y Z

/-- **The pentagon of `μ` transports along isomorphisms of all three arguments.**  This is
`StacksDraft.DerivedHom.DerivedHomAdjunction.laxTensorAssoc_of_iso` at the data of derived base
change; `Dualizing.derivedTensorBaseChange` and the two associators of [stacks 0A63] are natural,
and `F` applied to an isomorphism is monic. -/
theorem derivedTensorBaseChangeAssoc_of_iso
    {X X' Y Y' Z Z' : DerivedCategory (ModuleCat.{max uR uA uM} R)}
    (x : X ≅ X') (y : Y ≅ Y') (z : Z ≅ Z')
    (h : DerivedTensorBaseChangeAssoc.{uR, uA, uM} f F comparison X' Y' Z') :
    DerivedTensorBaseChangeAssoc.{uR, uA, uM} f F comparison X Y Z :=
  DerivedHomAdjunction.laxTensorAssoc_of_iso _ _ _ _ x y z h

/-- **The pentagon at every triple of localizations of K-flat complexes gives it at every triple
of objects.**  Every object of `D(R)` is isomorphic to the localization of a K-flat complex by
`Dualizing.exists_kFlat_iso`, i.e. by the resolution of [stacks 06Y4], and
`Dualizing.derivedTensorBaseChangeAssoc_of_iso` transports the pentagon across the three
isomorphisms.

This is the transport the module documentation of
`StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaEvaluation` records as one of the
two residues of the second input of [stacks 0E2H]; what it leaves is the pentagon at a triple of
K-flat representatives, where every factor has a chain-level value. -/
theorem derivedTensorBaseChangeAssoc_of_kFlat
    (hpent : ∀ K L M : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ,
      K.KFlat → L.KFlat → M.KFlat →
        DerivedTensorBaseChangeAssoc.{uR, uA, uM} f F comparison
          (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M))
    (X Y Z : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    DerivedTensorBaseChangeAssoc.{uR, uA, uM} f F comparison X Y Z := by
  obtain ⟨K, hK, ⟨eX⟩⟩ := exists_kFlat_iso.{uR, max uA uM} X
  obtain ⟨L, hL, ⟨eY⟩⟩ := exists_kFlat_iso.{uR, max uA uM} Y
  obtain ⟨M, hM, ⟨eZ⟩⟩ := exists_kFlat_iso.{uR, max uA uM} Z
  exact derivedTensorBaseChangeAssoc_of_iso f F comparison eX eY eZ (hpent K L M hK hL hM)

/-- **The compatibility of [stacks 0E1X] with currying, from the pentagon at K-flat
representatives.**  `Dualizing.derivedTensorBaseChangeAssoc_of_kFlat` followed by
`Dualizing.derivedTensorBaseChangeAssoc_iff_curryCompat`. -/
theorem derivedHomBaseChangeCurryCompat_of_kFlat
    (hpent : ∀ K L M : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ,
      K.KFlat → L.KFlat → M.KFlat →
        DerivedTensorBaseChangeAssoc.{uR, uA, uM} f F comparison
          (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M))
    (Y Z N : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    DerivedHomBaseChangeCurryCompat.{uR, uA, uM} f F comparison Y Z N :=
  (derivedTensorBaseChangeAssoc_iff_curryCompat f F comparison Y Z).1
    (fun X => derivedTensorBaseChangeAssoc_of_kFlat f F comparison hpent X Y Z) N

end

end Dualizing

end
