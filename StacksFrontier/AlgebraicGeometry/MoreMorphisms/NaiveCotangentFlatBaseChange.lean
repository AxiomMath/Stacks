module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentBaseChangeComparisonMap
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentFlatAlgebraBaseChangeStalk
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentFlatBaseChangeStalk
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentComplex
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentExactSequence
public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentSixTermFirstTerms

/-!
# The base change comparison map for the naive cotangent complex of a square of schemes

Let

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

be a commutative square of schemes, so `g' ≫ f = f' ≫ g`.  There is a canonical map

`(g')^*NL_{X/Y} ⟶ NL_{X'/Y'}`

of complexes of `𝒪_{X'}`-modules.  It is built from three maps of complexes of sheaves on `X'`,
all attached to sheaves of commutative rings on the single space `X'`:

1. the identification of `(g')^*NL_{X/Y}` with the base change to `𝒪_{X'}` of the naive
   cotangent complex of `(g')^{-1}𝒪_X` over `(g')^{-1}f^{-1}𝒪_Y`, which is the inverse-image
   theorem for the naive cotangent complex (Stacks 08TM);
2. the base-change map `NL_{B/A} ⊗_B C ⟶ NL_{C/A}` of Stacks 0E1Y for the tower of sheaves of
   rings `(g')^{-1}f^{-1}𝒪_Y ⟶ (g')^{-1}𝒪_X ⟶ 𝒪_{X'}`;
3. the relative map `NL_{C/A} ⟶ NL_{C/B}` of Stacks 0E1Y for the tower
   `(g')^{-1}f^{-1}𝒪_Y ⟶ (f')^{-1}𝒪_{Y'} ⟶ 𝒪_{X'}`.

Maps 2 and 3 can be composed only once the two towers are known to have the same composite
`(g')^{-1}f^{-1}𝒪_Y ⟶ 𝒪_{X'}`.  The comparison `(g')^{-1}f^{-1}𝒪_Y ⟶ (f')^{-1}𝒪_{Y'}`
realising this, together with the equation it satisfies, is taken as an explicit argument, so
that every statement about the resulting map is a statement about the comparison it is given.
For a commutative square such a comparison exists, and for a cartesian square with either `g` or
`f` flat the canonical map is a quasi-isomorphism.

## Main results

* `Stacks.NaiveCotangentFlatBaseChange.exists_baseRingComparison_ringedSpace` and
  `Stacks.NaiveCotangentFlatBaseChange.exists_baseRingComparison`: for a commutative square of
  ringed spaces, respectively of schemes, a compatible comparison
  `(g')^{-1}f^{-1}𝒪_Y ⟶ (f')^{-1}𝒪_{Y'}` exists.
* `Stacks.NaiveCotangentFlatBaseChange.ringedSpaceStructureMap_eq_inverseImageStructureMap`:
  the two available spellings of the structure map `h^{-1}𝒪_T ⟶ 𝒪_S` of a morphism of ringed
  spaces agree.
* `Stacks.NaiveCotangentFlatBaseChange.isZero_pulledComplex_X`: `(g')^*NL_{X/Y}` vanishes
  outside degrees `-1` and `0`.
* `Stacks.NaiveCotangentFlatBaseChange.quasiIso_baseChangeMapOfComparison_of_forall_stalk`: the
  canonical map is a quasi-isomorphism as soon as all of its maps of stalk complexes are.
* `Stacks.NaiveCotangentFlatBaseChange.quasiIso_baseChangeMapOfComparison_of_flat_base`:
  **flat base change**: for a cartesian square with `g : Y' ⟶ Y` flat, the canonical
  comparison taken against the canonical base-ring comparison of the square is a
  quasi-isomorphism.
* `Stacks.NaiveCotangentFlatBaseChange.quasiIso_baseChangeMapOfComparison_of_flat_algebra`:
  **base change along a flat morphism**: for a cartesian square with `f : X ⟶ Y` flat, the
  canonical comparison taken against the canonical base-ring comparison of the square is a
  quasi-isomorphism.

## Implementation notes

`Stacks.SheafOfModules.ringedSpaceStructureMap` and
`Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap` are two independent
definitions of the adjoint transpose `h^{-1}𝒪_T ⟶ 𝒪_S` of the structure morphism of a morphism
of ringed spaces `h : S ⟶ T`.  They agree by definition, which
`ringedSpaceStructureMap_eq_inverseImageStructureMap` records; the complexes of this file are
built over the first spelling, while the factorisation lemma transposed in
`exists_baseRingComparison_ringedSpace` is stated about the second, so the transposition is
carried out against the second spelling and read off in the first.

The transposition is performed for an arbitrary commutative square of ringed spaces and the
statement for schemes obtained by instantiating it along `Scheme.Hom.toLRSHom` and
`LocallyRingedSpace.Hom.toShHom`.  Carrying it out directly for schemes makes the unifier
compare the structure sheaf of a scheme with the inverse-image functor applied to it through
those two coercions, and the inverse image of sheaves of rings is a sheafification, so the
comparison unfolds it.

## References

* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y), the base-change and
  relative maps of naive cotangent complexes of a tower of sheaves of rings.
* [Stacks Project, Tag 0E1Z](https://stacks.math.columbia.edu/tag/0E1Z), the same for a
  composition of morphisms of ringed spaces.
* [Stacks Project, Tag 08TM](https://stacks.math.columbia.edu/tag/08TM), the inverse image of
  the naive cotangent complex.
* [Stacks Project, Tag 0D0H](https://stacks.math.columbia.edu/tag/0D0H), the naive cotangent
  complex of a morphism of schemes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
open Stacks.SheafOfModules
open AlgebraicGeometry.SheafOfModules (inverseImageRingHom stalkFunctor)
open Stacks.Sheaves.RingedSpaceDifferentials (sheafAdjunction structureSheafMap inverseImageSheaf
  inverseImageStructureMap exists_inverseImageComparison)
open Stacks.NaiveCotangentFlatAlgebraBaseChangeStalk
  (quasiIso_stalkFunctor_map_baseChangeMapOfComparison)

universe u

namespace Stacks.NaiveCotangentFlatBaseChange

variable {X Y X' Y' : Scheme.{u}}

/-! ### The pullback of the naive cotangent complex -/

/-- `(g')^*NL_{X/Y}` has no terms outside degrees `-1` and `0`. -/
theorem isZero_pulledComplex_X (f : X ⟶ Y) (g' : X' ⟶ X) (i : ℤ) (hneg : i ≠ -1)
    (hzero : i ≠ 0) :
    Limits.IsZero ((pulledComplex f g').X i) := by
  have h₀ := naiveCotangentComplex_isZero_X.{u, u, u, u}
    (Opens.grothendieckTopology X.toRingedSpace.carrier)
    (inverseImageBaseRingOnMiddle f.toLRSHom.toShHom) X.toRingedSpace.sheaf
    (ringedSpaceStructureMap f.toLRSHom.toShHom) i hneg hzero
  have h₁ := Functor.map_isZero
    (_root_.SheafOfModules.pullback.{u}
      (inverseImageRingHom g'.toLRSHom.toShHom.hom.base X.toRingedSpace.sheaf)) h₀
  have := towerExtendScalars_additive (Opens.grothendieckTopology X'.toRingedSpace.carrier)
    (inverseImageMiddleRing g'.toLRSHom.toShHom) X'.toRingedSpace.sheaf
    (ringedSpaceStructureMap g'.toLRSHom.toShHom)
  exact Functor.map_isZero
    (towerExtendScalars (Opens.grothendieckTopology X'.toRingedSpace.carrier)
      (inverseImageMiddleRing g'.toLRSHom.toShHom) X'.toRingedSpace.sheaf
      (ringedSpaceStructureMap g'.toLRSHom.toShHom)) h₁

/-! ### The comparison of base rings -/

/-- The two spellings of the structure map `h^{-1}𝒪_T ⟶ 𝒪_S` of a morphism of ringed spaces
`h : S ⟶ T` agree: both are the adjoint transpose of `h^♯ : 𝒪_T ⟶ h_*𝒪_S`. -/
alias ringedSpaceStructureMap_eq_inverseImageStructureMap :=
  Stacks.SheafOfModules.ringedSpaceStructureMap_eq

/-- For a commutative square of ringed spaces `g' ≫ f = f' ≫ g` there is a comparison
`(g')^{-1}f^{-1}𝒪_S ⟶ (f')^{-1}𝒪_{S'}` of sheaves of rings on `X'` identifying the two towers
`(g')^{-1}f^{-1}𝒪_S ⟶ (g')^{-1}𝒪_X ⟶ 𝒪_{X'}` and
`(g')^{-1}f^{-1}𝒪_S ⟶ (f')^{-1}𝒪_{S'} ⟶ 𝒪_{X'}`: the two composites agree. -/
theorem exists_baseRingComparison_ringedSpace {X' X S' S : RingedSpace.{u, u}} (g' : X' ⟶ X)
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (w : g' ≫ f = f' ≫ g) :
    ∃ bc : inverseImageBaseRing g' f ⟶ inverseImageSheaf f',
      inverseImageFirstRingMap g' f ≫ ringedSpaceStructureMap g' =
        bc ≫ ringedSpaceStructureMap f' := by
  obtain ⟨ψ, hψ⟩ := exists_inverseImageComparison g' f f' g w
  refine ⟨((sheafAdjunction g').homEquiv _ _).symm ψ, ?_⟩
  have h₁ := Adjunction.homEquiv_naturality_left_symm (sheafAdjunction g')
    (inverseImageStructureMap f) (structureSheafMap g')
  have h₂ := Adjunction.homEquiv_naturality_right_symm (sheafAdjunction g') ψ
    (inverseImageStructureMap f')
  exact h₁.symm.trans
    ((congrArg ((sheafAdjunction g').homEquiv _ _).symm hψ).trans h₂)

/-- For a commutative square of schemes `g' ≫ f = f' ≫ g` there is a comparison
`(g')^{-1}f^{-1}𝒪_Y ⟶ (f')^{-1}𝒪_{Y'}` of sheaves of rings on `X'` identifying the two towers
`(g')^{-1}f^{-1}𝒪_Y ⟶ (g')^{-1}𝒪_X ⟶ 𝒪_{X'}` and
`(g')^{-1}f^{-1}𝒪_Y ⟶ (f')^{-1}𝒪_{Y'} ⟶ 𝒪_{X'}`: the two composites agree. -/
theorem exists_baseRingComparison (f : X ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X) (g : Y' ⟶ Y)
    (w : g' ≫ f = f' ≫ g) :
    ∃ bc : inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom ⟶
        inverseImageSheaf f'.toLRSHom.toShHom,
      inverseImageFirstRingMap g'.toLRSHom.toShHom f.toLRSHom.toShHom ≫
          ringedSpaceStructureMap g'.toLRSHom.toShHom =
        bc ≫ ringedSpaceStructureMap f'.toLRSHom.toShHom :=
  exists_baseRingComparison_ringedSpace g'.toLRSHom.toShHom f.toLRSHom.toShHom
    f'.toLRSHom.toShHom g.toLRSHom.toShHom
    (congrArg (fun t : X' ⟶ Y => t.toLRSHom.toShHom) w)

/-! ### The canonical base change map -/

/-- If, for every point `x` of `X'`, the map of complexes of `𝒪_{X',x}`-modules obtained from
`(g')^*NL_{X/Y} ⟶ NL_{X'/Y'}` by taking stalks at `x` degreewise is a quasi-isomorphism, then
the canonical base change map is a quasi-isomorphism. -/
theorem quasiIso_baseChangeMapOfComparison_of_forall_stalk (f : X ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X)
    (bc : inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom ⟶
      inverseImageSheaf f'.toLRSHom.toShHom)
    (hbc : inverseImageFirstRingMap g'.toLRSHom.toShHom f.toLRSHom.toShHom ≫
        ringedSpaceStructureMap g'.toLRSHom.toShHom =
      bc ≫ ringedSpaceStructureMap f'.toLRSHom.toShHom)
    (h : ∀ x : X'.toRingedSpace.carrier,
      QuasiIso (((stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (J := Opens.grothendieckTopology X'.toRingedSpace.carrier)
            X'.toRingedSpace.sheaf) x).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (baseChangeMapOfComparison f f' g' bc hbc))) :
    QuasiIso (baseChangeMapOfComparison f f' g' bc hbc) :=
  AlgebraicGeometry.SheafOfModules.quasiIso_of_forall_stalk_quasiIso _ _ h

/-! ### Flat base change -/

/-- **Flat base change.**  For a cartesian square of schemes whose lower horizontal morphism
`g : Y' ⟶ Y` is flat, the canonical comparison `(g')^*NL_{X/Y} ⟶ NL_{X'/Y'}`, taken against the
canonical base-ring comparison `AlgebraicGeometry.BaseChangeStalk.baseRingComparison` of the
square, is a quasi-isomorphism. -/
@[stacks 0FJZ "the flat-base-change quasi-isomorphism, with no hypotheses beyond a CARTESIAN \
square (`hsq : IsPullback g' f' f g`) and `[Flat g]`.  The canonical map is CONSTRUCTED, not \
assumed: `Stacks.NaiveCotangentFlatBaseChange.baseChangeMapOfComparison` is the source's own \
composite of the [Stacks, Tag 08TM] identification of `(g')^*NL_{X/Y}` with a base change \
(`Stacks.SheafOfModules.pulledNaiveCotangentComparison`), the base-change map \
`NL_{B/A} (x)_B C -> NL_{C/A}` of [Stacks, Tag 0E1Y] \
(`Stacks.SheafOfModules.spaceBaseChangeNaiveCotangentMap`) for the tower \
`(g')^-1 f^-1 O_Y -> (g')^-1 O_X -> O_{X'}`, and the relative map `NL_{C/A} -> NL_{C/B}` \
(`Stacks.SheafOfModules.spaceRelativeNaiveCotangentComplexMap`) for the tower through \
`(f')^-1 O_{Y'}`.  The base-ring comparison it is taken against is the CANONICAL one of the \
square, `AlgebraicGeometry.BaseChangeStalk.baseRingComparison`, together with its compatibility \
`AlgebraicGeometry.BaseChangeStalk.baseRingComparison_comp`; it is built from the square and is \
not a `Classical.choose` of a non-unique existence statement.  PROVED: the construction of the \
map; the degreewise vanishing outside degrees -1 and 0 (`isZero_pulledComplex_X`); the reduction \
of quasi-isomorphy to the stalks (`quasiIso_baseChangeMapOfComparison_of_forall_stalk`, resting \
on [Stacks, Tag 08TL] \
`AlgebraicGeometry.SheafOfModules.quasiIso_of_forall_stalk_quasiIso`); and the stalkwise \
statement itself, \
`Stacks.NaiveCotangentFlatBaseChangeStalk.quasiIso_stalkFunctor_map_baseChangeMapOfComparison`.  \
That stalkwise statement is \
`Stacks.NaiveCotangentTowerStalk.quasiIso_stalkFunctor_map_towerComposite` fed with the \
ring-level flat base change `NaiveCotangent.isQuasiIso_nlExtensionBaseChangeMap_of_flat_base` \
([Stacks, Tag 00S4]), read through the stalk identification of the naive cotangent complex \
([Stacks, Tag 0D09], `Stacks.SheafOfModules.stalkLegNegOne` / `stalkLegZero` / `stalkLeg_d`).  \
Its two ring-level inputs are both discharged here: the flatness of the stalk of the canonical \
base-ring comparison, which \
`AlgebraicGeometry.BaseChangeStalk.stalkFunctor_map_baseRingComparison` identifies with the stalk \
map of `g` conjugated by three isomorphisms and which Mathlib's \
`AlgebraicGeometry.Flat.stalkMap` then makes flat, so `[Flat g]` does work here and is not \
decorative; and the identification of `O_{X',x'}` as a localization of \
`O_{Y',y'} (x)_{O_{Y,y}} O_{X,x}`, which is \
`AlgebraicGeometry.BaseChangeStalk.stalk_isLocalization_of_isPullback_inverseImage_comm` \
([Stacks, Tag 01JR]) and is the one place cartesianness of the square is used.  SCOPE: the \
statement is about the undecorated comparison `(g')^*NL_{X/Y} -> NL_{X'/Y'}`; nothing is claimed \
here about the derived pullback `L(g')^*NL_{X/Y}`"]
theorem quasiIso_baseChangeMapOfComparison_of_flat_base (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (hsq : IsPullback g' f' f g) [AlgebraicGeometry.Flat g] :
    QuasiIso (baseChangeMapOfComparison f f' g'
      (AlgebraicGeometry.BaseChangeStalk.baseRingComparison f f' g' g hsq.w)
      (AlgebraicGeometry.BaseChangeStalk.baseRingComparison_comp f f' g' g hsq.w)) :=
  quasiIso_baseChangeMapOfComparison_of_forall_stalk f f' g' _ _ fun x =>
    Stacks.NaiveCotangentFlatBaseChangeStalk.quasiIso_stalkFunctor_map_baseChangeMapOfComparison
      f g f' g' hsq x

/-- **Base change along a flat morphism.**  For a cartesian square of schemes whose right
vertical morphism `f : X ⟶ Y` is flat, the canonical comparison `(g')^*NL_{X/Y} ⟶ NL_{X'/Y'}`,
taken against the canonical base-ring comparison
`AlgebraicGeometry.BaseChangeStalk.baseRingComparison` of the square, is a quasi-isomorphism. -/
@[stacks 0FK0 "the FIRST clause -- the quasi-isomorphism when `X -> Y` is flat -- with no \
hypotheses beyond a CARTESIAN square (`hsq : IsPullback g' f' f g`) and `[Flat f]`.  The \
canonical map is CONSTRUCTED, not assumed, exactly as on \
`Stacks.NaiveCotangentFlatBaseChange.quasiIso_baseChangeMapOfComparison_of_flat_base`: \
`Stacks.NaiveCotangentFlatBaseChange.baseChangeMapOfComparison` is the source's own composite of \
the [Stacks, Tag 08TM] identification of `(g')^*NL_{X/Y}` with a base change \
(`Stacks.SheafOfModules.pulledNaiveCotangentComparison`), the base-change map \
`NL_{B/A} (x)_B C -> NL_{C/A}` of [Stacks, Tag 0E1Y] \
(`Stacks.SheafOfModules.spaceBaseChangeNaiveCotangentMap`) for the tower \
`(g')^-1 f^-1 O_Y -> (g')^-1 O_X -> O_{X'}`, and the relative map `NL_{C/A} -> NL_{C/B}` \
(`Stacks.SheafOfModules.spaceRelativeNaiveCotangentComplexMap`) for the tower through \
`(f')^-1 O_{Y'}`.  The base-ring comparison it is taken against is the CANONICAL one of the \
square, `AlgebraicGeometry.BaseChangeStalk.baseRingComparison`, together with its compatibility \
`AlgebraicGeometry.BaseChangeStalk.baseRingComparison_comp`; it is built from the square and is \
not a `Classical.choose` of a non-unique existence statement.  PROVED: the construction of the \
map; the degreewise vanishing outside degrees -1 and 0 (`isZero_pulledComplex_X`); the reduction \
of quasi-isomorphy to the stalks (`quasiIso_baseChangeMapOfComparison_of_forall_stalk`, resting \
on [Stacks, Tag 08TL] \
`AlgebraicGeometry.SheafOfModules.quasiIso_of_forall_stalk_quasiIso`); and the stalkwise \
statement itself, `Stacks.NaiveCotangentFlatAlgebraBaseChangeStalk` \
`.quasiIso_stalkFunctor_map_baseChangeMapOfComparison`.  That stalkwise statement is \
`Stacks.NaiveCotangentTowerStalk.quasiIso_stalkFunctor_map_towerComposite` fed with the \
ring-level base change for a flat algebra \
`NaiveCotangent.isQuasiIso_nlExtensionBaseChangeMap_of_flat_algebra`, read through the stalk \
identification of the naive cotangent complex ([Stacks, Tag 0D09] / [Stacks, Tag 0098]).  That \
ring-level statement is proved here from the two elementwise inputs of [Stacks, Tag 0FJU]: \
surjectivity on the degree -1 cycles and bijectivity on the cokernels, which hold for an \
arbitrary base change by [Stacks, Tag 0FUZ] \
(`NaiveCotangent.naiveCotangentComplex_baseChange_homology`), and injectivity on those cycles, \
which is what flatness of the algebra buys \
(`NaiveCotangent.cotangent_intrinsic_baseChange_cycle_injective_of_flat`); then flat base change \
to the pushout is composed with localization of the target over a fixed base \
([Stacks, Tag 00S7]).  Its two geometric inputs are both discharged here: the flatness of the \
stalk of the first map of the tower, which \
`AlgebraicGeometry.BaseChangeStalk.stalkInverseImageBaseRingIso_hom_comp_stalkMap` identifies \
with the stalk map of `f` conjugated by two isomorphisms and which Mathlib's \
`AlgebraicGeometry.Flat.stalkMap` then makes flat, so `[Flat f]` does work here and is not \
decorative; and the identification of `O_{X',x'}` as a localization of \
`O_{Y',y'} (x)_{O_{Y,y}} O_{X,x}`, which is \
`AlgebraicGeometry.BaseChangeStalk.stalk_isLocalization_of_isPullback_inverseImage_comm` \
([Stacks, Tag 01JR]) and is the one place cartesianness of the square is used.  SCOPE: the \
statement is about the undecorated comparison `(g')^*NL_{X/Y} -> NL_{X'/Y'}`, which is the \
tag's first clause; nothing is claimed here about the tag's second clause, the DERIVED \
comparison `L(g')^*NL_{X/Y} -> NL_{X'/Y'}` under Tor amplitude in [-1,0]"]
theorem quasiIso_baseChangeMapOfComparison_of_flat_algebra (f : X ⟶ Y) (g : Y' ⟶ Y)
    (f' : X' ⟶ Y') (g' : X' ⟶ X) (hsq : IsPullback g' f' f g) [AlgebraicGeometry.Flat f] :
    QuasiIso (baseChangeMapOfComparison f f' g'
      (AlgebraicGeometry.BaseChangeStalk.baseRingComparison f f' g' g hsq.w)
      (AlgebraicGeometry.BaseChangeStalk.baseRingComparison_comp f f' g' g hsq.w)) :=
  quasiIso_baseChangeMapOfComparison_of_forall_stalk f f' g' _ _ fun x =>
    quasiIso_stalkFunctor_map_baseChangeMapOfComparison f g f' g' hsq x

end Stacks.NaiveCotangentFlatBaseChange

end
