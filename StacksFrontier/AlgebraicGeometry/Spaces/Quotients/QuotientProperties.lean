module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Submersive
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.CoarseQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.InvariantBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.InvariantFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.TopologicalConditions

/-!
# Universal, good and geometric quotients of a pre-relation

Let `j : R ⟶ U ×_B U` be a pre-relation of algebraic spaces over an algebraic space `B` and
let `φ : U ⟶ X` be an `R`-invariant morphism. Three strengthenings of the categorical
quotient property of `φ` are recorded here.

A categorical quotient in a full subcategory `P` closed under fibre products is *universal*
when the projection `X' ×_X U ⟶ X'` is again a categorical quotient in `P`, of the base
change of `j`, for every morphism `X' ⟶ X` of `P`, and *uniform* when this is asked only of
the flat such morphisms.

A *good quotient* is an invariant, affine, surjective morphism for which, universally, the
images of invariant closed subsets of `|U|` are closed and meet in the image of their
intersection, and whose functions are the invariant functions on `U`. A *geometric quotient*
is an orbit space which is universally submersive and whose functions are the invariant
functions on `U`.

## Main definitions

* `AlgebraicGeometry.Space.pullbackPreRelationTarget` and
  `AlgebraicGeometry.Space.pullbackPreRelationSource`: the two maps of fibre products induced
  by the target and the source of a pre-relation, and
  `AlgebraicGeometry.Space.pullbackPreRelation`: the base change of a pre-relation along a
  morphism to the codomain of an invariant morphism, taken in the slice of algebraic spaces
  over `B`.
* `AlgebraicGeometry.Space.HasUniversallyClosedInvariantImagesInter`: condition (3) of
  **Stacks 04A4**, that is `AlgebraicGeometry.Space.IsInvariantClosedMapInter` of
  `StacksFrontier/AlgebraicGeometry/Spaces/Quotients/TopologicalConditions.lean`, imposed after
  every base change.
* `AlgebraicGeometry.Space.IsUniversalCategoricalQuotientIn`: **Stacks 048L**, part (1).
* `AlgebraicGeometry.Space.IsUniformCategoricalQuotientIn`: **Stacks 048L**, part (2).
* `AlgebraicGeometry.Space.IsGoodQuotient`: **Stacks 04AC**.
* `AlgebraicGeometry.Space.IsGeometricQuotient`: **Stacks 04AE**.

## Main results

* `AlgebraicGeometry.Space.isInvariant_presheafPreRelation`: invariance of a morphism of
  algebraic spaces over `B` passes to the underlying morphism of presheaves and the
  pre-relation of presheaves.
* `AlgebraicGeometry.Space.comp_eq_comp_of_isInvariant`: an invariant morphism has equal
  composites with the target and the source of the pre-relation, as morphisms over `B`.
* `AlgebraicGeometry.Space.pullbackPreRelation_target` and
  `AlgebraicGeometry.Space.pullbackPreRelation_source`: the two maps of the base-changed
  pre-relation.
* `AlgebraicGeometry.Space.pullbackPreRelationTarget_fst`,
  `AlgebraicGeometry.Space.pullbackPreRelationTarget_snd`,
  `AlgebraicGeometry.Space.pullbackPreRelationSource_fst` and
  `AlgebraicGeometry.Space.pullbackPreRelationSource_snd`: the four equations fixing those
  two maps on the components in `X'` and in `U`.

## Implementation notes

The quotient conditions are imposed in the slice `CategoryTheory.Over B` of
`AlgebraicGeometry.AlgebraicSpaces`, which is where the categorical-quotient predicate
`AlgebraicGeometry.Space.IsCategoricalQuotientIn` of **Stacks 048J** and the invariant
functions `AlgebraicGeometry.Space.HasInvariantFunctions` of **Stacks 04AA** live. The
conditions that speak about points — being an orbit space, surjectivity, submersiveness,
and the closed-image conditions — are conditions on presheaves, and are imposed on the
images of `j` and `φ` under `AlgebraicGeometry.Space.overForgetSpace`, exactly as
`AlgebraicGeometry.Space.IsCoarseQuotient` of **Stacks 04A2** does; the translation of
invariance across that functor is `AlgebraicGeometry.Space.isInvariant_presheafPreRelation`.

`AlgebraicGeometry.Space.pullbackPreRelation` is the base change of **Stacks 048G** in the
slice of algebraic spaces: there `U' = X' ×_X U` and `R' = X' ×_X R` are the fibre products
over `X` of that slice, taken along `φ` and along `j.target ≫ φ`, so no new objects have to
be constructed and `U' ⟶ X'` is their first projection.
`AlgebraicGeometry.Space.baseChangedPreRelation` is the same base change in the slice of
presheaves over a presheaf, and carries the tags of **Stacks 048G** and **Stacks 048H**; it
is the one used by the closed-image conditions, whose point-set vocabulary is that of
presheaves.

Closure of the full subcategory under fibre products is the source's hypothesis on it and is
carried as an instance argument; it is what makes the base-changed objects lie in the
subcategory, which `AlgebraicGeometry.Space.IsCategoricalQuotientIn` asks of them.

Invariance of `φ` is a hypothesis of **Stacks 048L**, so it is an argument of the two
predicates there, as it is of `AlgebraicGeometry.Space.HasInvariantFunctions`. In **Stacks
04AC** and **Stacks 04AE** invariance is instead one of the conditions — the first one
outright, respectively through the orbit-space condition — so it is bound existentially;
being a proposition, which proof is bound does not matter.

All predicates are transparent abbreviations, so clients may use their clauses directly
without a projection API.

## References

* [Stacks Project, Tag 043C](https://stacks.math.columbia.edu/tag/043C)
* [Stacks Project, Tag 048E](https://stacks.math.columbia.edu/tag/048E)
* [Stacks Project, Tag 048G](https://stacks.math.columbia.edu/tag/048G)
* [Stacks Project, Tag 048J](https://stacks.math.columbia.edu/tag/048J)
* [Stacks Project, Tag 048L](https://stacks.math.columbia.edu/tag/048L)
* [Stacks Project, Tag 0493](https://stacks.math.columbia.edu/tag/0493)
* [Stacks Project, Tag 04A4](https://stacks.math.columbia.edu/tag/04A4)
* [Stacks Project, Tag 04AA](https://stacks.math.columbia.edu/tag/04AA)
* [Stacks Project, Tag 04AC](https://stacks.math.columbia.edu/tag/04AC)
* [Stacks Project, Tag 04AE](https://stacks.math.columbia.edu/tag/04AE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {site : BigFppfSite.{u}} {S : Scheme.{u}} {hS : site.Contains S}

/-! ### Invariance read in the slice of presheaves -/

/-- A morphism of algebraic spaces over `B` which is invariant under a pre-relation of
algebraic spaces over `B` is invariant, as a morphism of presheaves, under the induced
pre-relation of presheaves. -/
theorem isInvariant_presheafPreRelation {B : AlgebraicSpaces site S hS} {R U X : Over B}
    (j : PreRelation R U) (φ : U ⟶ X) (hφ : IsInvariant j φ.left) :
    IsInvariant (presheafPreRelation j) ((overForgetSpace B).map φ).left := by
  simp only [IsInvariant, presheafPreRelation_target, presheafPreRelation_source]
  exact congrArg (ObjectProperty.ι (algebraicSpaceProperty site S hS)).map hφ

/-! ### Base change of a pre-relation in the slice of algebraic spaces -/

section BaseChange

variable {B : AlgebraicSpaces site S hS}

/-- An invariant morphism has equal composites with the target and with the source of the
pre-relation, as morphisms of algebraic spaces over `B`. -/
theorem comp_eq_comp_of_isInvariant {R U X : Over B} (j : PreRelation R U) (φ : U ⟶ X)
    (hφ : IsInvariant j φ.left) :
    j.target ≫ φ = j.source ≫ φ :=
  Over.OverMorphism.ext hφ

/-- The morphism `X' ×_X R ⟶ X' ×_X U` of fibre products over `X` induced by the target of
the pre-relation: the identity on the component in `X'` and the target of `j` on the
component in `R`. -/
def pullbackPreRelationTarget {R U X X' : Over B} (j : PreRelation R U) (φ : U ⟶ X)
    (f : X' ⟶ X) :
    pullback f (j.target ≫ φ) ⟶ pullback f φ :=
  pullback.lift (pullback.fst f (j.target ≫ φ)) (pullback.snd f (j.target ≫ φ) ≫ j.target)
    (pullback.condition.trans (Category.assoc _ _ _).symm)

/-- The morphism `X' ×_X R ⟶ X' ×_X U` of fibre products over `X` induced by the source of
the pre-relation. It is invariance of `φ` that makes the source of `j` descend to the fibre
products, the target descending for free. -/
def pullbackPreRelationSource {R U X X' : Over B} (j : PreRelation R U) (φ : U ⟶ X)
    (f : X' ⟶ X) (hφ : IsInvariant j φ.left) :
    pullback f (j.target ≫ φ) ⟶ pullback f φ :=
  pullback.lift (pullback.fst f (j.target ≫ φ)) (pullback.snd f (j.target ≫ φ) ≫ j.source)
    (pullback.condition.trans
      ((congrArg (fun g : R ⟶ X ↦ pullback.snd f (j.target ≫ φ) ≫ g)
        (comp_eq_comp_of_isInvariant j φ hφ)).trans (Category.assoc _ _ _).symm))

/-- **Stacks 048G** in the slice of algebraic spaces over `B`: the base change of a
pre-relation `j` along a morphism `f : X' ⟶ X` to the codomain of an invariant morphism
`φ : U ⟶ X`. It is the pre-relation from `R' = X' ×_X R` to `U' = X' ×_X U` whose target and
source leave the component in `X'` alone and are those of `j` on the component in `U`. -/
def pullbackPreRelation {R U X X' : Over B} (j : PreRelation R U) (φ : U ⟶ X) (f : X' ⟶ X)
    (hφ : IsInvariant j φ.left) :
    PreRelation (pullback f (j.target ≫ φ)) (pullback f φ) :=
  prod.lift (pullbackPreRelationTarget j φ f) (pullbackPreRelationSource j φ f hφ)

/-- The target of the base-changed pre-relation is the morphism of fibre products induced by
the target of `j`. -/
@[simp]
theorem pullbackPreRelation_target {R U X X' : Over B} (j : PreRelation R U) (φ : U ⟶ X)
    (f : X' ⟶ X) (hφ : IsInvariant j φ.left) :
    (pullbackPreRelation j φ f hφ).target = pullbackPreRelationTarget j φ f :=
  prod.lift_fst _ _

/-- The source of the base-changed pre-relation is the morphism of fibre products induced by
the source of `j`. -/
@[simp]
theorem pullbackPreRelation_source {R U X X' : Over B} (j : PreRelation R U) (φ : U ⟶ X)
    (f : X' ⟶ X) (hφ : IsInvariant j φ.left) :
    (pullbackPreRelation j φ f hφ).source = pullbackPreRelationSource j φ f hφ :=
  prod.lift_snd _ _

/-- The base-changed pre-relation keeps the component in `X'` of a point of `X' ×_X R`
through its target. -/
@[simp]
theorem pullbackPreRelationTarget_fst {R U X X' : Over B} (j : PreRelation R U) (φ : U ⟶ X)
    (f : X' ⟶ X) :
    pullbackPreRelationTarget j φ f ≫ pullback.fst f φ = pullback.fst f (j.target ≫ φ) :=
  pullback.lift_fst _ _ _

/-- On the component in `U` the target of the base-changed pre-relation is the target of
`j`. -/
@[simp]
theorem pullbackPreRelationTarget_snd {R U X X' : Over B} (j : PreRelation R U) (φ : U ⟶ X)
    (f : X' ⟶ X) :
    pullbackPreRelationTarget j φ f ≫ pullback.snd f φ =
      pullback.snd f (j.target ≫ φ) ≫ j.target :=
  pullback.lift_snd _ _ _

/-- The base-changed pre-relation keeps the component in `X'` of a point of `X' ×_X R`
through its source. -/
@[simp]
theorem pullbackPreRelationSource_fst {R U X X' : Over B} (j : PreRelation R U) (φ : U ⟶ X)
    (f : X' ⟶ X) (hφ : IsInvariant j φ.left) :
    pullbackPreRelationSource j φ f hφ ≫ pullback.fst f φ =
      pullback.fst f (j.target ≫ φ) :=
  pullback.lift_fst _ _ _

/-- On the component in `U` the source of the base-changed pre-relation is the source of
`j`. -/
@[simp]
theorem pullbackPreRelationSource_snd {R U X X' : Over B} (j : PreRelation R U) (φ : U ⟶ X)
    (f : X' ⟶ X) (hφ : IsInvariant j φ.left) :
    pullbackPreRelationSource j φ f hφ ≫ pullback.snd f φ =
      pullback.snd f (j.target ≫ φ) ≫ j.source :=
  pullback.lift_snd _ _ _

end BaseChange

/-! ### Universal and uniform categorical quotients -/

/-- **Stacks 048L, part (1).** An `R`-invariant morphism `φ : U ⟶ X` is a *universal
categorical quotient* in a full subcategory `P` of the algebraic spaces over `B`, closed
under fibre products, when `R`, `U` and `X` lie in `P` and for every morphism `f : X' ⟶ X`
of `P` the projection `X' ×_X U ⟶ X'` is the categorical quotient in `P` of the base change
of `j` along `f`. -/
@[stacks 048L "part (1): universal categorical quotient"]
abbrev IsUniversalCategoricalQuotientIn {B : AlgebraicSpaces site S hS}
    (P : ObjectProperty (Over B)) [P.IsClosedUnderLimitsOfShape WalkingCospan]
    {R U X : Over B} (j : PreRelation R U) (φ : U ⟶ X) (hφ : IsInvariant j φ.left) : Prop :=
  P R ∧ P U ∧ P X ∧
    ∀ (X' : Over B) (f : X' ⟶ X), P X' →
      IsCategoricalQuotientIn P (pullbackPreRelation j φ f hφ) (pullback.fst f φ)

/-- **Stacks 048L, part (2).** An `R`-invariant morphism `φ : U ⟶ X` is a *uniform
categorical quotient* in a full subcategory `P` of the algebraic spaces over `B`, closed
under fibre products, when `R`, `U` and `X` lie in `P` and for every flat morphism
`f : X' ⟶ X` of `P` the projection `X' ×_X U ⟶ X'` is the categorical quotient in `P` of the
base change of `j` along `f`. -/
@[stacks 048L "part (2): uniform categorical quotient"]
abbrev IsUniformCategoricalQuotientIn {B : AlgebraicSpaces site S hS}
    (P : ObjectProperty (Over B)) [P.IsClosedUnderLimitsOfShape WalkingCospan]
    {R U X : Over B} (j : PreRelation R U) (φ : U ⟶ X) (hφ : IsInvariant j φ.left) : Prop :=
  P R ∧ P U ∧ P X ∧
    ∀ (X' : Over B) (f : X' ⟶ X), P X' →
      IsFlat site S hS ((overForgetSpace B).map f).left →
        IsCategoricalQuotientIn P (pullbackPreRelation j φ f hφ) (pullback.fst f φ)

/-! ### The universal closed-image condition -/

/-- Condition (3) of **Stacks 04A4** holds *universally* for an invariant morphism
`φ : U ⟶ X` of algebraic spaces over `B` when it holds for the base change of `j` and of `φ`
along every morphism `X' ⟶ X` of algebraic spaces over `B`. -/
abbrev HasUniversallyClosedInvariantImagesInter {B : AlgebraicSpaces site S hS}
    {R U X : Over B} (j : PreRelation R U) (φ : U ⟶ X) (hφ : IsInvariant j φ.left) : Prop :=
  ∀ (X' : Over B) (f : X' ⟶ X),
    IsInvariantClosedMapInter
      (baseChangedPreRelation (presheafPreRelation j) ((overForgetSpace B).map φ).left
        ((overForgetSpace B).map f).left (isInvariant_presheafPreRelation j φ hφ)).val
      (pullback.fst ((overForgetSpace B).map f).left ((overForgetSpace B).map φ).left)

/-! ### Good quotients -/

/-- **Stacks 04AC.** A morphism `φ : U ⟶ X` of algebraic spaces over `B` is a *good quotient*
of a pre-relation `j` when it is `R`-invariant, affine and surjective, condition (3) of
**Stacks 04A4** holds for it universally, and the functions on `X` are the `R`-invariant
functions on `U`. -/
@[stacks 04AC]
abbrev IsGoodQuotient {B : AlgebraicSpaces site S hS} {R U X : Over B} (j : PreRelation R U)
    (φ : U ⟶ X) : Prop :=
  ∃ hφ : IsInvariant j φ.left,
    IsAffineHom site S hS ((overForgetSpace B).map φ).left ∧
      IsSurjective site S hS ((overForgetSpace B).map φ).left ∧
        HasUniversallyClosedInvariantImagesInter j φ hφ ∧
          HasInvariantFunctions site S hS j φ.left hφ

/-! ### Geometric quotients -/

/-- **Stacks 04AE.** A morphism `φ : U ⟶ X` of algebraic spaces over `B` is a *geometric
quotient* of a pre-relation `j` when it is an orbit space for `j`, universally submersive,
and the functions on `X` are the `R`-invariant functions on `U`. -/
@[stacks 04AE]
abbrev IsGeometricQuotient {B : AlgebraicSpaces site S hS} {R U X : Over B}
    (j : PreRelation R U) (φ : U ⟶ X) : Prop :=
  ∃ hφ : IsInvariant j φ.left,
    IsOrbitSpace (presheafPreRelation j) ((overForgetSpace B).map φ).left ∧
      UniversallySubmersive site S hS ((overForgetSpace B).map φ).left ∧
        HasInvariantFunctions site S hS j φ.left hφ

end AlgebraicGeometry.Space

end
