module

public import StacksFrontier.AlgebraicGeometry.Quot.NegativeExtLocus

/-!
# The two conditions of Stacks 0DLD after base change, and their consequences

Let `f : X ⟶ Y` be a proper, flat and finitely presented morphism of algebraic spaces over a
scheme `S`. Let `E` be an object of `D(𝒪_X)` which satisfies the two conditions of Stacks 0DLD:
(1) `E` is `Y`-perfect, and (2) for every point `y : Spec(k) ⟶ Y` with values in a field the
negative self-extensions `Ext^i_{𝒪_{X_y}}(E_y, E_y)`, `i < 0`, vanish. Stacks 0DLD then states:

* (a) the conditions (1) and (2) hold for `X_V ⟶ V` and `E_V` after any base change `V ⟶ Y`;
* (b) `Ext^i_{𝒪_{X_V}}(E_V, E_V) = 0` for `i < 0` and every `V` over `Y`;
* (c) `V ↦ Hom_{𝒪_{X_V}}(E_V, E_V)` is representable by an algebraic space which is affine and
  of finite presentation over `Y`.

Condition (2) of part (a) holds outright. It is
`AlgebraicGeometry.Space.HasNoNegativeFieldFibreExt.baseChange`, and it needs none of the
hypotheses on `f`. The other parts rest on results not yet proved here and have not
registered yet:

* condition (1) of part (a) is Stacks 0DKT, the base change of relative perfectness, for the
  morphism `f` and an arbitrary algebraic space over `Y`;
* parts (b) and (c) are, by the source's proof, Stacks 0DLC (2) and (3) at `K = E`. Condition
  (2) of Stacks 0DLD says that the open `W ⊆ Y` of Stacks 0DLC (1) is all of `Y`.

Each of these results enters below as an explicit hypothesis carrying exactly its Stacks
content: `AlgebraicGeometry.Space.RelativelyPerfectBaseChangeStable` (Stacks 0DKT),
`AlgebraicGeometry.Space.NegativeExtVanishesOfFibres` and
`AlgebraicGeometry.Space.RelativeDerivedHomRepresentableOfFibres` (Stacks 0DLC (2) and (3) at
`W = Y`), all stated in `StacksFrontier/AlgebraicGeometry/Quot/NegativeExtLocus.lean`. So these
lemmas are not registered. Once the result lands, the hypothesis is
discharged by it and the lemma is registered.

## Main results

* `AlgebraicGeometry.Space.ComplexesSituation.overInclusion_isFlat` and
  `AlgebraicGeometry.Space.ComplexesSituation.overInclusion_isLocallyOfFinitePresentation`: the
  base change `X_V ⟶ V` is flat and locally of finite presentation, so condition (1) makes sense
  for it.
* `AlgebraicGeometry.Space.ComplexesSituation.conditions_overBaseChange_of`: part (a), given
  Stacks 0DKT.
* `AlgebraicGeometry.Space.ComplexesSituation.subsingleton_hom_shift_overBaseChange_of`:
  part (b), given Stacks 0DLC (2).
* `Space.ComplexesSituation.relativeDerivedHom_self_isAffineFinitePresentation_of`: part (c),
  given Stacks 0DLC (3).

## Implementation notes

A base change `V ⟶ Y` is an algebraic space `V` over `Y`, an object of `Over Y`. The base
change `X_V` is the chosen fibre product `AlgebraicGeometry.Space.overBaseChange`, with the
projections `AlgebraicGeometry.Space.overProjection` to `X` and
`AlgebraicGeometry.Space.overInclusion` to `V`. A point with values in a field is a test scheme
over `Y` whose underlying scheme is the spectrum of a field, as in
`AlgebraicGeometry.Space.HasNoNegativeFieldFibreExt`. `Ext^i(M, N)` is the group of morphisms
`M ⟶ N⟦i⟧` of the derived category, and its vanishing is written as `Subsingleton`.

The derived categories are the ones that `AlgebraicGeometry.Space.derivedModules` and the
predicate `AlgebraicGeometry.Space.IsPerfectRelativeToCanonical` of Stacks 0DKN are formed at.
The instances that make relative perfectness expressible are the ones constructed in
`StacksFrontier/AlgebraicGeometry/Quot/ComplexesStack.lean`, used here as they are used in
`StacksFrontier/AlgebraicGeometry/Quot/ComplexesStackBaseChange.lean`.

## References

* [Stacks Project, Tag 0DLD](https://stacks.math.columbia.edu/tag/0DLD)
* [Stacks Project, Tag 0DLC](https://stacks.math.columbia.edu/tag/0DLC)
* [Stacks Project, Tag 0DKT](https://stacks.math.columbia.edu/tag/0DKT)
* [Stacks Project, Tag 0DKN](https://stacks.math.columbia.edu/tag/0DKN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space.ComplexesSituation

attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.Space.instModulesHasDerivedCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : ComplexesSituation B S hS)

/-- The base change `X_V ⟶ V` of `f` along an algebraic space `V` over `Y` is flat. This is the
base-change stability of flatness, Stacks 03MO, at the cartesian square defining `X_V`. -/
theorem overInclusion_isFlat (V : Over D.Y) : IsFlat B S hS (overInclusion D.f V).hom :=
  (isFlat_isStableUnderBaseChange B S hS).of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f V.hom) D.flat

/-- The base change `X_V ⟶ V` of `f` along an algebraic space `V` over `Y` is locally of finite
presentation. This is the base-change stability of Stacks 03XR at the cartesian square defining
`X_V`. -/
theorem overInclusion_isLocallyOfFinitePresentation (V : Over D.Y) :
    IsLocallyOfFinitePresentation B S hS (overInclusion D.f V).hom :=
  (isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f V.hom) D.finitePresentation.1

/-- **Part (a) of Stacks 0DLD, given Stacks 0DKT.** Suppose `E` in `D(𝒪_X)` satisfies conditions
(1) and (2) of Stacks 0DLD: `E` is `Y`-perfect, and its negative self-extensions vanish on
every fibre over a point with values in a field. Then for every algebraic space `V` over `Y`,
the derived pullback `E_V` of `E` to `X_V` satisfies both conditions for `X_V ⟶ V`.

The hypothesis `h0DKT` is Stacks 0DKT: the derived pullback of a `Y`-perfect object along the
projection of a cartesian square, here `X_V ⟶ X`, is `V`-perfect. Stacks 0DKT is not yet proved
here. Condition (2) needs nothing: it is
`AlgebraicGeometry.Space.HasNoNegativeFieldFibreExt.baseChange`. -/
theorem conditions_overBaseChange_of
    (h0DKT : RelativelyPerfectBaseChangeStable B S hS)
    (E : derivedModules B S hS D.X)
    (h1 : IsPerfectRelativeToCanonical B S hS D.f D.flat D.finitePresentation.1 E)
    (h2 : HasNoNegativeFieldFibreExt D.f E) (V : Over D.Y) :
    IsPerfectRelativeToCanonical B S hS (overInclusion D.f V) (D.overInclusion_isFlat V)
        (D.overInclusion_isLocallyOfFinitePresentation V)
        (((smallEtaleDerivedPullbackData B S hS).pull (overProjection D.f V)).obj E) ∧
      HasNoNegativeFieldFibreExt (overInclusion D.f V)
        (((smallEtaleDerivedPullbackData B S hS).pull (overProjection D.f V)).obj E) :=
  ⟨h0DKT D.f V.hom (overProjection D.f V) (overInclusion D.f V)
      (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f V.hom) D.flat D.finitePresentation.1
      (D.overInclusion_isFlat V) (D.overInclusion_isLocallyOfFinitePresentation V) E h1,
    h2.baseChange V⟩

/-- **Part (b) of Stacks 0DLD, given Stacks 0DLC (2).** If `E` in `D(𝒪_X)` satisfies conditions
(1) and (2) of Stacks 0DLD, then `Ext^i_{𝒪_{X_V}}(E_V, E_V) = 0` for every `i < 0` and every
algebraic space `V` over `Y`.

The hypothesis `h0DLC` is Stacks 0DLC (2) in the case where the open `W` of Stacks 0DLC (1) is
all of `Y`. Let `K` be pseudo-coherent and `E` be `Y`-perfect, and suppose
`Ext^i(K_y, E_y) = 0` for `i < 0` at every point `y` of `Y` with values in a field. Then
`Ext^i(K_V, E_V) = 0` for `i < 0` and every `V` over `Y`. Stacks 0DLC is not yet proved here. As in
the source, part (b) is the case `K = E`. A `Y`-perfect object is
pseudo-coherent, and condition (2) says that `W = Y`. -/
theorem subsingleton_hom_shift_overBaseChange_of
    (h0DLC : NegativeExtVanishesOfFibres B S hS)
    (E : derivedModules B S hS D.X)
    (h1 : IsPerfectRelativeToCanonical B S hS D.f D.flat D.finitePresentation.1 E)
    (h2 : HasNoNegativeFieldFibreExt D.f E) (V : Over D.Y) (i : ℤ) (hi : i < 0) :
    Subsingleton
      (((smallEtaleDerivedPullbackData B S hS).pull (overProjection D.f V)).obj E ⟶
        (((smallEtaleDerivedPullbackData B S hS).pull (overProjection D.f V)).obj E)⟦i⟧) :=
  h0DLC D.f D.proper D.flat D.finitePresentation E E h1.1 h1
    ((hasNoNegativeFieldFibreExt_iff D.f E).1 h2) V i hi

/-- **Part (c) of Stacks 0DLD, given Stacks 0DLC (3).** If `E` in `D(𝒪_X)` satisfies conditions
(1) and (2) of Stacks 0DLD, then the functor `V ↦ Hom_{𝒪_{X_V}}(E_V, E_V)` is representable by
an algebraic space which is affine and of finite presentation over `Y`.

The hypothesis `h0DLC` is Stacks 0DLC (3) in the case where the open `W` of Stacks 0DLC (1) is
all of `Y`. Let `K` be pseudo-coherent and `E` be `Y`-perfect, and suppose
`Ext^i(K_y, E_y) = 0` for `i < 0` at every point `y` of `Y` with values in a field. Then the
functor `V ↦ Hom(K_V, E_V)` is representable by an algebraic space affine and of finite
presentation over `Y`. Stacks 0DLC is not yet proved here. Part (c) is
the case `K = E`, as in part (b). -/
theorem relativeDerivedHom_self_isAffineFinitePresentation_of
    (h0DLC : RelativeDerivedHomRepresentableOfFibres B S hS)
    (E : derivedModules B S hS D.X)
    (h1 : IsPerfectRelativeToCanonical B S hS D.f D.flat D.finitePresentation.1 E)
    (h2 : HasNoNegativeFieldFibreExt D.f E) :
    IsAffineFinitePresentationAlgebraicSpaceOver D.Y (relativeDerivedHom D.f E E) :=
  h0DLC D.f D.proper D.flat D.finitePresentation E E h1.1 h1
    ((hasNoNegativeFieldFibreExt_iff D.f E).1 h2)

end AlgebraicGeometry.Space.ComplexesSituation

end
