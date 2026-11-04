module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Submersive
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.InvariantBaseChange

/-!
# Topological conditions on an invariant morphism (Stacks 04A4)

Let `j : R ⟶ U ×_Z U` be a pre-relation over a base `Z` and let `φ : U ⟶ X` be a morphism
which is invariant under `j`. **Stacks 04A4** lists four conditions one may impose on such a
`φ`, each of them a condition on the topological spaces of points:

1. `φ` is submersive;
2. the image of every `R`-invariant closed subset of `|U|` is closed in `|X|`;
3. condition (2) holds, and the images of two `R`-invariant closed subsets meet exactly in
   the image of their intersection;
4. the map `(t, s) : R ⟶ U ×_X U` assembled from the target and the source of `j` — which
   exists precisely because `φ` is invariant — is universally submersive.

Each of the four may further be required to hold after every flat base change of `X`, or
after every base change of `X`, in which case it is said to hold *uniformly* or
*universally*. The base changes are the ones of **Stacks 048H**: base changing `φ` along
`f : X' ⟶ X` replaces `U` by `U ×_X X'`, `R` by `R ×_X X'` and `φ` by the projection to
`X'`, and `j` by `AlgebraicGeometry.Space.baseChangedPreRelation`.

## Main definitions

Condition (1) is the existing `AlgebraicGeometry.Space.IsSubmersive` of **Stacks 0412** and
needs no new definition; its universal form is likewise the existing
`AlgebraicGeometry.Space.UniversallySubmersive`. The conditions proper to this file are

* `AlgebraicGeometry.Space.IsInvariantPointSet`: `R`-invariance of a subset of `|U|`, the
  notion the section introduces before the definition.
* `AlgebraicGeometry.Space.IsInvariantClosedMap`: condition (2).
* `AlgebraicGeometry.Space.IsInvariantClosedMapInter`: condition (3).
* `AlgebraicGeometry.Space.IsStronglySubmersive`: condition (4).

and their uniform and universal strengthenings

* `AlgebraicGeometry.Space.HoldsAfterFlatBaseChange` and
  `AlgebraicGeometry.Space.HoldsAfterBaseChange`: the two base-change quantifiers, taking
  the condition to be imposed as a parameter.
* `AlgebraicGeometry.Space.IsUniformlySubmersive`,
  `AlgebraicGeometry.Space.IsUniformlyInvariantClosedMap`,
  `AlgebraicGeometry.Space.IsUniversallyInvariantClosedMap`,
  `AlgebraicGeometry.Space.IsUniformlyInvariantClosedMapInter`,
  `AlgebraicGeometry.Space.IsUniversallyInvariantClosedMapInter`,
  `AlgebraicGeometry.Space.IsUniformlyStronglySubmersive` and
  `AlgebraicGeometry.Space.IsUniversallyStronglySubmersive`.

## Implementation notes

As in `StacksFrontier/AlgebraicGeometry/Spaces/RelationsOverSpace.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/Quotients/InvariantBaseChange.lean`, the pre-relation
lives over an arbitrary presheaf base `Z` on the big fppf site and `R`, `U` are arbitrary
objects of `CategoryTheory.Over Z`: no definition here uses the algebraic-space axioms on
them, and a client imposes `AlgebraicGeometry.IsAlgebraicSpace` where the source does.
Algebraicity is *not* dropped in the base-change quantifiers, however: the source quantifies
over base changes along morphisms of algebraic spaces, so `HoldsAfterBaseChange` and
`HoldsAfterFlatBaseChange` carry `AlgebraicGeometry.IsAlgebraicSpace` on the space they base
change along, exactly as `AlgebraicGeometry.Space.UniversallySubmersive` does.

A subset of `|U|` is a subset of `AlgebraicGeometry.Space.points`, carrying the topology
`AlgebraicGeometry.Space.pointTopology` of **Stacks 03BX** and **Stacks 03BY**; it is made a
local instance so that `IsClosed` means closed for it.

Condition (4) takes the invariance of `φ` as an argument rather than asserting it: the
morphism `(t, s)` whose submersiveness it is about is the pullback lift
`CategoryTheory.Limits.pullback.lift` of the target and the source of `j`, and invariance is
literally the commutation that lift requires. For the same reason the two base-change
quantifiers hand the condition they impose a proof that the base-changed morphism is again
invariant, namely `AlgebraicGeometry.Space.isInvariant_baseChangedPreRelation`; the
conditions that do not need it discard it.

## References

* [Stacks Project, Tag 04A4](https://stacks.math.columbia.edu/tag/04A4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {R U : Over Z}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Invariant subsets of the space of points -/

/-- **Stacks 04A4.** A subset `T` of the points of `U` is *`R`-invariant* for a pre-relation
`j : R ⟶ U ×_Z U` when its inverse images under the source and the target of `j` agree as
subsets of the points of `R`.

This is the notion the source introduces in the prose preceding its definition. Note that it
is a condition on subsets of `|U|` only: even for closed `T` the corresponding reduced closed
subspace of `U` need not be an invariant subspace, because the two pullbacks of `T` to `R`
need not be reduced. -/
abbrev IsInvariantPointSet (j : PreRelation R U) (T : Set (points B S hS U.left)) : Prop :=
  pointsMap B S hS R.left j.source.left ⁻¹' T =
    pointsMap B S hS R.left j.target.left ⁻¹' T

/-! ### The four conditions -/

-- Condition (1) is submersiveness, which is the existing notion of Tag 0412; so is its
-- universal form, base change along every morphism from an algebraic space. Both tags are
-- therefore registered on those declarations rather than restated here.
add_to_stacks 04A4 "condition (1): submersive" AlgebraicGeometry.Space.IsSubmersive
add_to_stacks 04A4 "universal condition (1)" AlgebraicGeometry.Space.UniversallySubmersive

/-- **Stacks 04A4, condition (2).** An invariant morphism `φ : U ⟶ X` has *closed invariant
images* when for every `R`-invariant closed subset `Z ⊆ |U|` the image `φ(Z)` is closed in
`|X|`. -/
@[stacks 04A4 "condition (2): invariant closed subsets have closed image"]
abbrev IsInvariantClosedMap (j : PreRelation R U) (φ : U.left ⟶ X) : Prop :=
  ∀ T : Set (points B S hS U.left), IsInvariantPointSet j T → IsClosed T →
    IsClosed (pointsMap B S hS U.left φ '' T)

/-- **Stacks 04A4, condition (3).** Condition (2) holds, and moreover for every pair of
`R`-invariant closed subsets `Z₁, Z₂ ⊆ |U|` one has `φ(Z₁ ∩ Z₂) = φ(Z₁) ∩ φ(Z₂)`. -/
@[stacks 04A4 "condition (3): intersections of invariant closed subsets"]
abbrev IsInvariantClosedMapInter (j : PreRelation R U) (φ : U.left ⟶ X) : Prop :=
  IsInvariantClosedMap j φ ∧
    ∀ T₁ T₂ : Set (points B S hS U.left),
      IsInvariantPointSet j T₁ → IsClosed T₁ → IsInvariantPointSet j T₂ → IsClosed T₂ →
        pointsMap B S hS U.left φ '' (T₁ ∩ T₂) =
          pointsMap B S hS U.left φ '' T₁ ∩ pointsMap B S hS U.left φ '' T₂

/-- Condition (3) of **Stacks 04A4** contains condition (2). -/
theorem IsInvariantClosedMapInter.isInvariantClosedMap {j : PreRelation R U}
    {φ : U.left ⟶ X} (h : IsInvariantClosedMapInter j φ) : IsInvariantClosedMap j φ :=
  h.1

/-- **Stacks 04A4, condition (4).** An invariant morphism `φ : U ⟶ X` is *strongly
submersive* when the morphism `(t, s) : R ⟶ U ×_X U` assembled from the target and the source
of `j` is universally submersive.

Invariance of `φ` is exactly the commutation `t ≫ φ = s ≫ φ` needed to form that morphism,
so it is taken as an argument. -/
@[stacks 04A4 "condition (4): strongly submersive"]
noncomputable abbrev IsStronglySubmersive (j : PreRelation R U) (φ : U.left ⟶ X)
    (hφ : IsInvariant j φ) : Prop :=
  UniversallySubmersive B S hS (pullback.lift j.target.left j.source.left hφ)

/-! ### Invariance after base change -/

/-- The base change of an invariant morphism along any morphism `f : X' ⟶ X` is invariant
under the base-changed pre-relation of **Stacks 048H**: both the target and the source of
that pre-relation are, by construction, the first projection of the pullback defining the
base-changed arrow space. -/
theorem isInvariant_baseChangedPreRelation (j : PreRelation R U) (φ : U.left ⟶ X)
    {X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ X) (hφ : IsInvariant j φ) :
    IsInvariant (baseChangedPreRelation j φ f hφ).val (pullback.fst f φ) :=
  (baseChangedPreRelation j φ f hφ).property.1.1.trans
    (baseChangedPreRelation j φ f hφ).property.2.1.symm

/-! ### The uniform and universal variants -/

section BaseChange

variable (j : PreRelation R U) (φ : U.left ⟶ X) (hφ : IsInvariant j φ)

/-- A condition on invariant morphisms, as quantified over by the uniform and the universal
variants of **Stacks 04A4**: a property of a pre-relation together with a morphism invariant
under it. The invariance proof is part of the data because condition (4) needs it. -/
abbrev InvariantCondition (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  ∀ {R' U' : Over Z} {X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (j' : PreRelation R' U')
    (φ' : U'.left ⟶ X'), IsInvariant j' φ' → Prop

/-- **Stacks 04A4.** A condition on invariant morphisms holds *uniformly* for `φ` when it
holds for the base change of `φ` along every flat morphism to `X` from an algebraic
space. -/
abbrev HoldsAfterFlatBaseChange (P : InvariantCondition B S hS Z) : Prop :=
  ∀ (X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS X' →
    ∀ f : X' ⟶ X, IsFlat B S hS f →
      P (baseChangedPreRelation j φ f hφ).val (pullback.fst f φ)
        (isInvariant_baseChangedPreRelation j φ f hφ)

/-- **Stacks 04A4.** A condition on invariant morphisms holds *universally* for `φ` when it
holds for the base change of `φ` along every morphism to `X` from an algebraic space. -/
abbrev HoldsAfterBaseChange (P : InvariantCondition B S hS Z) : Prop :=
  ∀ (X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS X' →
    ∀ f : X' ⟶ X,
      P (baseChangedPreRelation j φ f hφ).val (pullback.fst f φ)
        (isInvariant_baseChangedPreRelation j φ f hφ)

/-- A condition which holds universally holds uniformly: a flat base change is a base
change. -/
theorem HoldsAfterBaseChange.holdsAfterFlatBaseChange {P : InvariantCondition B S hS Z}
    (h : HoldsAfterBaseChange j φ hφ P) : HoldsAfterFlatBaseChange j φ hφ P :=
  fun X' hX' f _ ↦ h X' hX' f

/-- **Stacks 04A4, uniform condition (1).** Condition (1) holds after every flat base
change. -/
@[stacks 04A4 "uniform condition (1)"]
abbrev IsUniformlySubmersive : Prop :=
  HoldsAfterFlatBaseChange j φ hφ fun {_R' _U'} {_X'} _ φ' _ ↦ IsSubmersive B S hS φ'

/-- **Stacks 04A4, uniform condition (2).** Condition (2) holds after every flat base
change. -/
@[stacks 04A4 "uniform condition (2)"]
abbrev IsUniformlyInvariantClosedMap : Prop :=
  HoldsAfterFlatBaseChange j φ hφ fun {_R' _U'} {_X'} j' φ' _ ↦ IsInvariantClosedMap j' φ'

/-- **Stacks 04A4, universal condition (2).** Condition (2) holds after every base
change. -/
@[stacks 04A4 "universal condition (2)"]
abbrev IsUniversallyInvariantClosedMap : Prop :=
  HoldsAfterBaseChange j φ hφ fun {_R' _U'} {_X'} j' φ' _ ↦ IsInvariantClosedMap j' φ'

/-- **Stacks 04A4, uniform condition (3).** Condition (3) holds after every flat base
change. -/
@[stacks 04A4 "uniform condition (3)"]
abbrev IsUniformlyInvariantClosedMapInter : Prop :=
  HoldsAfterFlatBaseChange j φ hφ fun {_R' _U'} {_X'} j' φ' _ ↦
    IsInvariantClosedMapInter j' φ'

/-- **Stacks 04A4, universal condition (3).** Condition (3) holds after every base
change. -/
@[stacks 04A4 "universal condition (3)"]
abbrev IsUniversallyInvariantClosedMapInter : Prop :=
  HoldsAfterBaseChange j φ hφ fun {_R' _U'} {_X'} j' φ' _ ↦ IsInvariantClosedMapInter j' φ'

/-- **Stacks 04A4, uniform condition (4).** Condition (4) holds after every flat base
change. -/
@[stacks 04A4 "uniform condition (4)"]
noncomputable abbrev IsUniformlyStronglySubmersive : Prop :=
  HoldsAfterFlatBaseChange j φ hφ fun {_R' _U'} {_X'} j' φ' hφ' ↦
    IsStronglySubmersive j' φ' hφ'

/-- **Stacks 04A4, universal condition (4).** Condition (4) holds after every base
change. -/
@[stacks 04A4 "universal condition (4)"]
noncomputable abbrev IsUniversallyStronglySubmersive : Prop :=
  HoldsAfterBaseChange j φ hφ fun {_R' _U'} {_X'} j' φ' hφ' ↦ IsStronglySubmersive j' φ' hφ'

end BaseChange

end AlgebraicGeometry.Space

end
