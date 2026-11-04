module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChartSlicingRegularSequence
public import StacksFrontier.AlgebraicGeometry.Stacks.RegularSingletonStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange

/-!
# The fibre of a smooth chart over a field-valued point: regular and nonempty

Let `𝒳` be an algebraic stack, let `f : U ⟶ 𝒳` be a **smooth** 1-morphism out of an algebraic
space, let `g : Spec k ⟶ 𝒳` be a field-valued point, and let `F = U ×_𝒳 Spec k` be the fibre of
the source's cartesian diagram in the chart construction of **Stacks 06N3**. This file supplies
the two properties of `F` that construction uses before it slices:

* `F` is **regular**: its structure morphism `F ⟶ Spec k` is a base change of the smooth chart,
  hence smooth (**Stacks 075W**), and an algebraic space smooth over the spectrum of a field is
  regular (**Stacks 06M1**);
* `F` is **nonempty** whenever the point of `|𝒳|` that `g` hits lies in the image of `|f|`
  (**Stacks 04XH**), which at a finite type point is what
  `AlgebraicGeometry.Stack.exists_relativelyUnramified_fieldSpectrum_point_of_isFiniteTypePoint`
  delivers: the range of the field-valued point on points is the singleton `{x}`.

Regularity is delivered in the form
`AlgebraicGeometry.Space.HasEtaleLocalProperty ... IsRegular`, which is the form
`AlgebraicGeometry.Space.isRegularLocalRing_chartLocalRing` consumes to produce the regularity of
`𝒪_{V, v}` at an étale chart `V` of `F` — the hypothesis of the slicing sequence of
**Stacks 06N3**.

## Main results

* `AlgebraicGeometry.Stack.isSmooth_fibreStructureMorphism`: the structure morphism `F ⟶ Spec k`
  is smooth when the chart is (**Stacks 075W**).
* `AlgebraicGeometry.Stack.hasEtaleLocalProperty_isRegular_fibreSpace`: the algebraic space
  representing `F` is regular (**Stacks 06M1**).
* `AlgebraicGeometry.Stack.exists_point_fibreOverFieldPoint_of_range_eq_singleton`: `|F|` has a
  point over any point of `|U|` that the field-valued point hits (**Stacks 04XH**).

## Implementation notes

The square of the cartesian diagram is
`AlgebraicGeometry.Stack.twoFibreProductSquareAlgebraicStacks B S hS f g`, whose first projection
is `AlgebraicGeometry.Stack.fibreProjection` and whose second is
`AlgebraicGeometry.Stack.fibreStructureMorphism`. Smoothness of the *second* projection is the
base-change statement **Stacks 075W** read at the swapped square, exactly as the flatness of the
second projection is read in
`AlgebraicGeometry.Stack.isRegularStack_of_isReducedLocallyNoetherianWithUniquePoint`.

The underlying scheme of the site object on `Spec k` is `Spec k`, so **Stacks 06M1** applies at
the identity isomorphism.

## References

* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 06M1](https://stacks.math.columbia.edu/tag/06M1)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 075W](https://stacks.math.columbia.edu/tag/075W)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
  (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)

variable (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
  (g : schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase) ⟶ 𝒳)

/-- **Stacks 075W at the cartesian diagram of Stacks 06N3.** The structure 1-morphism
`q : F = U ×_𝒳 Spec k ⟶ Spec k` is smooth when the chart `f : U ⟶ 𝒳` is, being its base change
along the field-valued point. -/
theorem isSmooth_fibreStructureMorphism (hfsm : AlgebraicStacks.IsSmooth B S hS f) :
    AlgebraicStacks.IsSmooth B S hS
      (fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g) :=
  AlgebraicStacks.isSmooth_baseChange B S hS f g
    (twoFibreProductSquareAlgebraicStacks B S hS f g).swap
    (Bicategory.isTwoFibreProduct_swap
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f g)) hfsm

variable (Fsp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hFsp : IsAlgebraicSpace B S hS Fsp)
  (eF : StacksRepresentableCFG.EquivalenceOver
    (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val.val.p
    (presheafOfCategories (Fsp ⋙ typeToCat)).p)

include hFsp eF in
/-- **Stacks 06M1 at the fibre of a smooth chart over a field-valued point.** The algebraic space
`Fsp` representing `F = U ×_𝒳 Spec k` is regular when the chart `f : U ⟶ 𝒳` is smooth: the
structure morphism `F ⟶ Spec k` is then smooth by **Stacks 075W**, and its representing map is a
smooth morphism of algebraic spaces onto the spectrum of a field.

Regularity is stated as `AlgebraicGeometry.Space.HasEtaleLocalProperty` at
`AlgebraicGeometry.IsRegular`, which is the form `AlgebraicGeometry.Space.isRegular...` delivers
and the form `AlgebraicGeometry.Space.isRegularLocalRing_chartLocalRing` consumes. -/
theorem hasEtaleLocalProperty_isRegular_fibreSpace
    (hfsm : AlgebraicStacks.IsSmooth B S hS f) :
    Space.HasEtaleLocalProperty B S hS Fsp (fun X : Scheme.{u} => IsRegular X) := by
  have hq := isSmooth_representingMap_of_isSmooth B S hS
    (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS) Fsp
    (yoneda.obj (fieldPointObject B S hS k hk toBase)) hFsp
    (isAlgebraicSpace_yoneda B S hS (fieldPointObject B S hS k hk toBase)) eF
    (PresheafOfCategories.sliceElementsEquivalenceOver _)
    (fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g)
    (isSmooth_fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g hfsm)
  exact Space.hasEtaleLocalProperty_isRegular_of_isSmooth_over_fieldSpectrum B S hS k
    (fieldPointObject B S hS k hk toBase) (Iso.refl _) hFsp _ hq

/-- **Nonemptiness of the fibre of the cartesian diagram of Stacks 06N3.** If the field-valued
point `g : Spec k ⟶ 𝒳` has range `{x}` on points and `u ∈ |U|` lies over `x`, then `|F|` has a
point over `u`.

This is **Stacks 04XH**,
`AlgebraicGeometry.Stack.AlgebraicStacks.exists_point_of_isTwoFibreProduct`:
the singleton range gives a point of `|Spec k|` with the same image in `|𝒳|` as `u`, and the two
lift. The singleton range is what
`AlgebraicGeometry.Stack.exists_relativelyUnramified_fieldSpectrum_point_of_isFiniteTypePoint`
delivers at a finite type point `x`, so this is the step that makes the source's `F` nonempty. -/
theorem exists_point_fibreOverFieldPoint_of_range_eq_singleton
    {x : AlgebraicStacks.points B S hS 𝒳}
    (hg : Set.range (AlgebraicStacks.pointsMap B S hS g) = {x})
    (u : AlgebraicStacks.points B S hS (algebraicSpaceStack.{u, w} B S hS U hU))
    (hu : AlgebraicStacks.pointsMap B S hS f u = x) :
    ∃ z : AlgebraicStacks.points B S hS
        (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g),
      AlgebraicStacks.pointsMap B S hS
        (fibreProjection B S hS 𝒳 U hU k hk toBase f g) z = u := by
  obtain ⟨t, ht⟩ : x ∈ Set.range (AlgebraicStacks.pointsMap B S hS g) := by
    rw [hg]; exact rfl
  obtain ⟨z, hz, -⟩ := AlgebraicStacks.exists_point_of_isTwoFibreProduct B S hS
    (twoFibreProductSquareAlgebraicStacks B S hS f g)
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f g) u t (hu.trans ht.symm)
  exact ⟨z, hz⟩

end AlgebraicGeometry.Stack

end
