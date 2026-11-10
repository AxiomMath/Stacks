module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings

/-!
# Thickenings of algebraic spaces are fpqc local on the base

A morphism of algebraic spaces over a scheme `S` is a thickening when it identifies its source
with a closed subspace of its target having the same associated topological space. This
property is local on the base for the fpqc topology: a morphism whose base change to every
member of an fpqc covering of its target is a thickening is itself a thickening.

## Main definitions

* `AlgebraicGeometry.Space.thickeningMorphismProperty`: being a thickening, as a property of
  morphisms of the category of algebraic spaces over `S`.

## Main results

* `AlgebraicGeometry.Space.isThickeningHom_iff_isClosedImmersion_and_isSurjective`: a morphism
  of algebraic spaces is a thickening exactly when it is a closed immersion and surjective on
  points.
* `AlgebraicGeometry.Space.thickening_isLocalAtTarget_fpqc`: being a thickening is local on the
  base for the fpqc topology.
* `AlgebraicGeometry.Space.isThickeningHom_iff_of_isFpqcCovering`: the same statement read on
  a single fpqc covering family.

## Implementation notes

The thickening condition is `AlgebraicGeometry.Space.IsThickeningHom`: an isomorphism onto a
range which is a thickening subspace in the sense of Stacks 05ZK, part (1). Being a thickening
is identified with being a closed immersion and surjective, two properties which are separately
local on the base (Stacks 0420 and Stacks 041Q).

## References

* [Stacks Project, Tag 0BPI](https://stacks.math.columbia.edu/tag/0BPI)
* [Stacks Project, Tag 0420](https://stacks.math.columbia.edu/tag/0420)
* [Stacks Project, Tag 041Q](https://stacks.math.columbia.edu/tag/041Q)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Being a thickening, as a property of morphisms of the category of algebraic spaces over
`S`: the morphism identifies its source with a thickening subspace of its target. -/
abbrev thickeningMorphismProperty : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun ⦃_ _ : AlgebraicSpaces B S hS⦄ f => IsThickeningHom B S hS f

/-- A morphism of algebraic spaces over `S` is a thickening exactly when it is a closed
immersion and surjective on points. -/
theorem isThickeningHom_iff_isClosedImmersion_and_isSurjective
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    IsThickeningHom B S hS f ↔
      IsClosedImmersion B S hS f.hom ∧ IsSurjective B S hS f.hom := by
  refine ⟨fun h => ⟨h.isClosedImmersion, h.surjective_pointsMap⟩, fun ⟨hci, hsurj⟩ => ?_⟩
  have : Mono f.hom := mono_of_isClosedImmersion B S hS f.hom hci
  have hsurjRange : Function.Surjective
      (pointsMap B S hS (Subfunctor.range f.hom).toFunctor (Subfunctor.range f.hom).ι) :=
    Function.Surjective.of_comp (g := pointsMap B S hS X.1 (Subfunctor.toRange f.hom))
      (by rwa [← pointsMap_comp, Subfunctor.toRange_ι])
  refine (isThickeningHom_iff_of_mono f).mpr
    ⟨⟨isAlgebraicSpace_of_iso B S hS (asIso (Subfunctor.toRange f.hom)) X.property, ?_⟩,
      hsurjRange⟩
  let Q := MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS))
  have : Q.RespectsIso := inferInstance
  have hcomp : Q (Subfunctor.toRange f.hom ≫ (Subfunctor.range f.hom).ι) := by
    simpa only [Subfunctor.toRange_ι] using hci
  exact (Q.cancel_left_of_respectsIso (Subfunctor.toRange f.hom)
    (Subfunctor.range f.hom).ι).mp hcomp

/-- An identity morphism of algebraic spaces over `S` is a thickening. -/
theorem isThickeningHom_id (X : AlgebraicSpaces B S hS) :
    IsThickeningHom B S hS (𝟙 X) := by
  have hid : ∀ a : BigFppfOver B S hS, _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (𝟙 a)) := by
    intro a
    rw [(BigFppfOver.toScheme B S hS).map_id a]
    infer_instance
  have : MorphismProperty.RespectsIso (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have hci : IsClosedImmersion B S hS (𝟙 X.1) :=
    MorphismProperty.relative.of_exists fun a g =>
      ⟨a, g, 𝟙 a, by simpa using IsPullback.of_id_snd, hid a⟩
  refine (isThickeningHom_iff_isClosedImmersion_and_isSurjective B S hS (𝟙 X)).mpr ⟨hci, ?_⟩
  change Function.Surjective (pointsMap B S hS X.1 (𝟙 X.1))
  simpa only [pointsMap_id] using Function.surjective_id

/-- Being a thickening is fpqc local on the base for morphisms of algebraic spaces over `S`: a
morphism whose base change to every member of some fpqc covering of its target is a thickening is
itself a thickening. -/
@[stacks 0BPI "thickenings"]
instance thickening_isLocalAtTarget_fpqc :
    (thickeningMorphismProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fpqc B S hS) := by
  have heq : thickeningMorphismProperty B S hS =
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => IsClosedImmersion B S hS f.hom) ⊓
        surjectiveMorphismProperty B S hS := by
    ext X Y f
    exact isThickeningHom_iff_isClosedImmersion_and_isSurjective B S hS f
  rw [heq]
  have := isClosedImmersion_isLocalAtTarget_fpqc.{u, v} B S hS
  exact .inf _ _

/-- A morphism `f : X ⟶ X'` of algebraic spaces over `S` is a thickening if and only if its base
change along every member of an fpqc covering `{X'ᵢ ⟶ X'}` is a thickening. -/
theorem isThickeningHom_iff_of_isFpqcCovering {I : Type v} {X X' : AlgebraicSpaces B S hS}
    (f : X ⟶ X') (X'i : I → AlgebraicSpaces B S hS) (g : ∀ i, X'i i ⟶ X')
    (hg : IsFpqcCovering B S hS fun i => (g i).hom) :
    IsThickeningHom B S hS f ↔ ∀ i, IsThickeningHom B S hS (pullback.snd f (g i)) := by
  let 𝒰 : Precoverage.ZeroHypercover.{v} (Topology.precoverage.{u, v} .fpqc B S hS) X' :=
    { I₀ := I
      X := X'i
      f := g
      mem₀ := ⟨I, X'i, g, rfl, X'.property, fun i => (X'i i).property, hg⟩ }
  exact MorphismProperty.IsLocalAtTarget.iff_of_zeroHypercover
    (P := thickeningMorphismProperty B S hS) 𝒰

end AlgebraicGeometry.Space

end
