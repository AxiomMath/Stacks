module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BootstrapEtaleSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.DescentDataSheavesEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.FinalBootstrap
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Properties
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Stability

/-!
# Effectivity of a descent datum relative to a covering with a surjective member

Let `{fᵢ : Xᵢ ⟶ T}` be an fppf covering of algebraic spaces over `S` and let `F` be a sheaf
over `T` whose fibre products `Xᵢ ×_T F` are all algebraic spaces.  If *one* member `f i` of
the covering is already surjective on points, then the projection `Xᵢ ×_T F ⟶ F` is a single
chart of `F` which is representable by algebraic spaces, surjective, flat and locally of
finite presentation, being the base change of `f i` along the structure morphism of `F`.  A
criterion recognising algebraic spaces by such a chart therefore applies to `F`, and the
descent datum of `F` is effective by the equivalence of Stacks 0ADT part (2).

This is the situation of Stacks 0ADV in which one member of the covering is surjective: the
chart needs no coproduct `∐ᵢ (F ×_T Xᵢ)`, so no countability hypothesis on the index type is
needed.

## Main results

* `AlgebraicGeometry.Space.Descent.isRepresentableByAlgebraicSpaces_fibreProj`: the
  projection `Xᵢ ×_T F ⟶ F` is representable by algebraic spaces.
* `AlgebraicGeometry.Space.Descent.hasProperty_fibreProj`: that projection inherits every
  base-change-stable property of `f i`.
* `AlgebraicGeometry.Space.Descent.isEffective_fibreDescentData_of_isSurjective`: the
  descent datum of `F` is effective, granted Stacks 04S6 part (3).
* `AlgebraicGeometry.Space.Descent.isEffective_fibreDescentData_of_unique`: the same for a
  covering with exactly one member, where the surjectivity is supplied by the covering.
* `AlgebraicGeometry.Space.Descent.isEffective_fibreDescentData_of_isEtale`: the same,
  without `hbootstrap`, when the chosen member is moreover étale.

## Implementation notes

Stacks 04S6 part (3) — a sheaf receiving a morphism from an algebraic space which is
representable by algebraic spaces, surjective, flat and locally of finite presentation is an
algebraic space — is the hypothesis `hbootstrap`, of type
`AlgebraicGeometry.Space.IsBootstrapAlgebraicSpaceAlongFlatSurjection`.

## References

* [Stacks Project, Tag 0ADT](https://stacks.math.columbia.edu/tag/0ADT)
* [Stacks Project, Tag 0ADV](https://stacks.math.columbia.edu/tag/0ADV)
* [Stacks Project, Tag 03Y3](https://stacks.math.columbia.edu/tag/03Y3)
* [Stacks Project, Tag 03Y8](https://stacks.math.columbia.edu/tag/03Y8)
* [Stacks Project, Tag 046F](https://stacks.math.columbia.edu/tag/046F)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.Descent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable {ι : Type v} {X : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A morphism of algebraic spaces over `S` with a base-change-stable property has that
property after every base change along a scheme-valued point of its target, which is what
`AlgebraicGeometry.Space.HasProperty` asks of it. -/
private theorem hasProperty_of_space_hom (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange] {Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z) (φ : Y ⟶ Z)
    (hφ : P (ObjectProperty.homMk φ :
      (⟨Y, hY⟩ : AlgebraicSpaces B S hS) ⟶ (⟨Z, hZ⟩ : AlgebraicSpaces B S hS))) :
    HasProperty B S hS P φ
      (isRepresentableByAlgebraicSpaces_of_isAlgebraicSpace B S hS hY hZ φ) := fun U ξ ↦
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct B S hS
      (ObjectProperty.homMk ξ : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :
        AlgebraicSpaces B S hS) ⟶ ⟨Z, hZ⟩)
      (ObjectProperty.homMk φ :
        (⟨Y, hY⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z, hZ⟩)).flip hφ

variable (f : ∀ i, X i ⟶ T) (hT : IsAlgebraicSpace B S hS T)
    (hX : ∀ i, IsAlgebraicSpace B S hS (X i))

include hT hX in
/-- The projection `Xᵢ ×_T F ⟶ F` of the `i`-th fibre component of a sheaf `F` over `T` is
representable by algebraic spaces. -/
theorem isRepresentableByAlgebraicSpaces_fibreProj (F : SheavesWithSpaceFibres f) (i : ι) :
    IsRepresentableByAlgebraicSpaces B S hS (pullback.fst F.obj.hom (f i)) :=
  isRepresentableByAlgebraicSpaces_of_isPullback B S hS
    (pullback.snd F.obj.hom (f i)) (pullback.fst F.obj.hom (f i)) (f i) F.obj.hom
    (IsPullback.of_hasPullback F.obj.hom (f i)).flip
    (isRepresentableByAlgebraicSpaces_of_isAlgebraicSpace B S hS (hX i) hT (f i))

/-- **Stacks 046F** for the fibre projection. The projection `Xᵢ ×_T F ⟶ F` has every
base-change-stable property of `f i`, being a base change of it. -/
theorem hasProperty_fibreProj (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange] (F : SheavesWithSpaceFibres f) (i : ι)
    (hP : P (ObjectProperty.homMk (f i) :
      (⟨X i, hX i⟩ : AlgebraicSpaces B S hS) ⟶ (⟨T, hT⟩ : AlgebraicSpaces B S hS))) :
    HasProperty B S hS P (pullback.fst F.obj.hom (f i))
      (isRepresentableByAlgebraicSpaces_fibreProj f hT hX F i) :=
  hasProperty_of_isPullback B S hS P (pullback.snd F.obj.hom (f i))
    (pullback.fst F.obj.hom (f i)) (f i) F.obj.hom
    (IsPullback.of_hasPullback F.obj.hom (f i)).flip
    (isRepresentableByAlgebraicSpaces_of_isAlgebraicSpace B S hS (hX i) hT (f i))
    (hasProperty_of_space_hom P (hX i) hT (f i) hP)

/-- **A descent datum relative to an fppf covering one member of which is surjective is
effective**, granted Stacks 04S6 part (3) as the hypothesis `hbootstrap`.

Let `{fᵢ : Xᵢ ⟶ T}` be an fppf covering of algebraic spaces over `S`, let `F` be a sheaf
over `T` whose fibre products with the members of the covering are algebraic spaces, and
suppose the member `f i` is surjective on points.  Then the descent datum of `F` relative to
the covering is effective. -/
theorem isEffective_fibreDescentData_of_isSurjective
    (hbootstrap : IsBootstrapAlgebraicSpaceAlongFlatSurjection B S hS)
    (hcov : IsFppfCovering B S hS X f) (F : SheavesWithSpaceFibres f) (i : ι)
    (hsurj : IsSurjective B S hS (f i)) :
    DescentData.IsEffective (fibreDescentData f hT hX F) := by
  refine (isAlgebraicSpace_iff_isEffective_fibreDescentData f hT hX hcov F).1 ?_
  exact hbootstrap (pullback.fst F.obj.hom (f i)) F.property.1 (F.property.2 i)
    (isRepresentableByAlgebraicSpaces_fibreProj f hT hX F i)
    (hasProperty_fibreProj f hT hX (surjectiveMorphismProperty B S hS) F i hsurj)
    (hasProperty_fibreProj f hT hX (flatProperty B S hS) F i (hcov.flat i))
    (hasProperty_fibreProj f hT hX (locallyOfFinitePresentationProperty B S hS) F i
      (hcov.locallyOfFinitePresentation i))

/-- **A descent datum relative to a one-member fppf covering is effective**, granted
Stacks 04S6 part (3) as the hypothesis `hbootstrap`.

This is `AlgebraicGeometry.Space.Descent.isEffective_fibreDescentData_of_isSurjective` for an
index type with exactly one element, whose single member is surjective by the joint
surjectivity of the covering. -/
theorem isEffective_fibreDescentData_of_unique [Unique ι]
    (hbootstrap : IsBootstrapAlgebraicSpaceAlongFlatSurjection B S hS)
    (hcov : IsFppfCovering B S hS X f) (F : SheavesWithSpaceFibres f) :
    DescentData.IsEffective (fibreDescentData f hT hX F) :=
  isEffective_fibreDescentData_of_isSurjective f hT hX hbootstrap hcov F default (fun x ↦ by
    have hmem : x ∈ ⋃ i, Set.range (pointsMap B S hS (X i) (f i)) := by
      rw [hcov.jointly_surjective]
      exact Set.mem_univ x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hmem
    have hid : i = default := Unique.eq_default i
    subst hid
    exact hi)

/-- **A descent datum relative to an fppf covering one member of which is surjective and
étale is effective**. -/
theorem isEffective_fibreDescentData_of_isEtale
    (hcov : IsFppfCovering B S hS X f) (F : SheavesWithSpaceFibres f) (i : ι)
    (hsurj : IsSurjective B S hS (f i)) (hetale : IsEtale B S hS (f i)) :
    DescentData.IsEffective (fibreDescentData f hT hX F) := by
  refine (isAlgebraicSpace_iff_isEffective_fibreDescentData f hT hX hcov F).1 ?_
  exact isAlgebraicSpace_of_isRepresentableByAlgebraicSpaces_surjective_etale
    F.property.1 (F.property.2 i) (pullback.fst F.obj.hom (f i))
    (isRepresentableByAlgebraicSpaces_fibreProj f hT hX F i)
    (hasProperty_fibreProj f hT hX (surjectiveMorphismProperty B S hS) F i hsurj)
    (hasProperty_fibreProj f hT hX (etaleMorphisms B S hS) F i hetale)

end AlgebraicGeometry.Space.Descent

end
