module

public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationCocycle

/-!
# Localization of higher direct images: the nested-opens cocycle in degree zero

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `V' ≤ V` be opens of `Y`.
Stacks 01E5 asserts an *equality* of sheaves, so the comparison
`Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIso` it attaches to two nested
opens must agree.  That cocycle identity is proved in
`StacksFrontier/Topology/Sheaves/Cohomology/HigherDirectImage/LocalizationCocycle.lean` for
`higherDirectImageRestrictIsoSucc`, hence — since `higherDirectImageRestrictIso f V 0` is
`higherDirectImageRestrictIsoZero`, a *different* isomorphism — only in positive degree.  This
file supplies the degree-zero case and assembles the two into a single statement valid in every
degree.

The degree-zero case is a normalisation, not different mathematics: both pushforwards are left
exact, so both sides of the comparison are the undeived functors read through
`CategoryTheory.Functor.rightDerivedZeroIsoSelf`, and the cocycle reduces to the undeived one,
`Stacks.Cohomology.HigherDirectImage.pushforwardRestrictOfLEIso_compatibility`, together with
the naturality of the transitivity isomorphism `moduleRestrictionOfLEIso` on the `Y` side.

## Main definitions

* `Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIsoZeroOfLE` is the middle
  comparison across `V' ≤ V` in degree zero: the undeived middle comparison
  `pushforwardRestrictOfLEIso` read through `rightDerivedZeroIsoSelf` on either side.  It is
  *not* `higherDirectImageRestrictIsoSuccOfLE f h 0`, which has the same type but is built from
  the derived middle comparison and is not compatible with `higherDirectImageRestrictIsoZero`.
* `Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIsoOfLE` is the middle
  comparison in **every** degree, dispatching on the degree exactly as
  `higherDirectImageRestrictIso` does.

## Main results

* `Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIsoZero_ofLE` is the cocycle
  identity in degree zero, in the shape `higherDirectImageRestrictIsoSucc_ofLE` has it in
  positive degree.
* `Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIso_ofLE` is the cocycle
  identity **in every degree**, for `higherDirectImageRestrictIso` itself: this is the
  degree-uniform statement, obtained by cases on the degree from
  `higherDirectImageRestrictIsoZero_ofLE` and `higherDirectImageRestrictIsoSucc_ofLE`.  A
  consumer whose degree is an arbitrary natural number — such as the dimension `d` of a
  situation, which may be zero — uses this one and needs no case split.
* `higherDirectImageRestrictIso_zero`, `higherDirectImageRestrictIsoOfLE_zero` and
  `higherDirectImageRestrictIsoOfLE_succ` read the two dispatching definitions in each degree.

## References

* [The Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.HigherDirectImage

section Nested

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) {V' V : Opens Y} (h : V' ≤ V)

/-- **The middle comparison across a nested pair of opens, in degree zero.**  In degree zero the
two pushforwards are left exact, so both zeroth right derived functors are canonically the
functors themselves; the middle comparison is the undeived one, `pushforwardRestrictOfLEIso`,
read through those normalisations.

This is *not* `higherDirectImageRestrictIsoSuccOfLE f h 0`.  The two have the same type, but the
latter is built from the derived middle comparison
`rightDerivedPushforwardRestrictionOfLEIso`, which is not visibly compatible with
`CategoryTheory.Functor.toRightDerivedZero`; it is the normalised comparison here that fits
`higherDirectImageRestrictIsoZero`, and hence `higherDirectImageRestrictIso` in degree zero. -/
noncomputable def higherDirectImageRestrictIsoZeroOfLE :
    moduleRestriction X (preimageOpen f V) ⋙
          (modulePushforward (restrictedMorphism f V)).rightDerived 0 ⋙
        moduleRestrictionOfLE Y h ≅
      moduleRestriction X (preimageOpen f V') ⋙
        (modulePushforward (restrictedMorphism f V')).rightDerived 0 :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (moduleRestriction X (preimageOpen f V))
        (modulePushforward (restrictedMorphism f V)).rightDerivedZeroIsoSelf)
      (moduleRestrictionOfLE Y h) ≪≫
    pushforwardRestrictOfLEIso f h ≪≫
    Functor.isoWhiskerLeft (moduleRestriction X (preimageOpen f V'))
      (modulePushforward (restrictedMorphism f V')).rightDerivedZeroIsoSelf.symm

/-- **Stacks 01E5, higher direct images, compatibility across nested opens, in degree zero.**
The comparison `higherDirectImageRestrictIsoZero` attached to `V`, whiskered by restriction
along `V' ≤ V` and followed by the transitivity isomorphism `moduleRestrictionOfLEIso` on the
`Y` side, agrees with `higherDirectImageRestrictIsoZeroOfLE` followed by the comparison attached
to `V'`.

This is the degree-zero companion of `higherDirectImageRestrictIsoSucc_ofLE`, in the same shape.
Both sides are the undeived comparison read through `rightDerivedZeroIsoSelf`: the
normalisations on the `X` side are the same on both sides of the equation, the two
normalisations for `V'` cancel against each other, the one on the `Y` side crosses the
transitivity isomorphism by `CategoryTheory.Functor.whiskerLeft_comp_whiskerRight`, and what is
left is the undeived cocycle `pushforwardRestrictOfLEIso_compatibility`. -/
theorem higherDirectImageRestrictIsoZero_ofLE :
    Functor.whiskerRight (higherDirectImageRestrictIsoZero f V).hom
          (moduleRestrictionOfLE Y h) ≫
        Functor.whiskerLeft ((modulePushforward f).rightDerived 0)
          (moduleRestrictionOfLEIso Y h).hom =
      (higherDirectImageRestrictIsoZeroOfLE f h).hom ≫
        (higherDirectImageRestrictIsoZero f V').hom := by
  have hmid : Functor.whiskerRight (modulePushforwardRestrictIso f V).hom
          (moduleRestrictionOfLE Y h) ≫
        Functor.whiskerLeft (modulePushforward f) (moduleRestrictionOfLEIso Y h).hom =
      (pushforwardRestrictOfLEIso f h).hom ≫ (modulePushforwardRestrictIso f V').hom := by
    rw [← Iso.comp_inv_eq, Category.assoc, ← pushforwardRestrictOfLEIso_compatibility f h,
      ← Functor.whiskerRight_comp_assoc, Iso.hom_inv_id, Functor.whiskerRight_id',
      Category.id_comp]
  have hexch : Functor.whiskerRight
          (Functor.whiskerRight (modulePushforward f).rightDerivedZeroIsoSelf.inv
            (moduleRestriction Y V)) (moduleRestrictionOfLE Y h) ≫
        Functor.whiskerLeft ((modulePushforward f).rightDerived 0)
          (moduleRestrictionOfLEIso Y h).hom =
      Functor.whiskerLeft (modulePushforward f) (moduleRestrictionOfLEIso Y h).hom ≫
        Functor.whiskerRight (modulePushforward f).rightDerivedZeroIsoSelf.inv
          (moduleRestriction Y V') :=
    NatTrans.ext (funext fun M => (moduleRestrictionOfLEIso Y h).hom.naturality
      ((modulePushforward f).rightDerivedZeroIsoSelf.inv.app M))
  dsimp only [higherDirectImageRestrictIsoZero, higherDirectImageRestrictIsoZeroOfLE,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
  simp only [Functor.whiskerRight_comp, Category.assoc]
  rw [hexch, reassoc_of% hmid, ← Functor.whiskerLeft_comp_assoc, Iso.inv_hom_id,
    Functor.whiskerLeft_id', Category.id_comp]

/-- In degree zero the comparison of Stacks 01E5 is the normalised comparison
`higherDirectImageRestrictIsoZero`, by construction. -/
theorem higherDirectImageRestrictIso_zero :
    higherDirectImageRestrictIso f V 0 = higherDirectImageRestrictIsoZero f V :=
  rfl

/-- **The middle comparison across a nested pair of opens, in every degree.**  It dispatches on
the degree exactly as `higherDirectImageRestrictIso` does: the normalised comparison
`higherDirectImageRestrictIsoZeroOfLE` in degree zero, and
`higherDirectImageRestrictIsoSuccOfLE` in positive degree.  This is what makes the cocycle
identity `higherDirectImageRestrictIso_ofLE` hold in every degree with no case split on the part
of the consumer. -/
noncomputable def higherDirectImageRestrictIsoOfLE (p : ℕ) :
    moduleRestriction X (preimageOpen f V) ⋙
          (modulePushforward (restrictedMorphism f V)).rightDerived p ⋙
        moduleRestrictionOfLE Y h ≅
      moduleRestriction X (preimageOpen f V') ⋙
        (modulePushforward (restrictedMorphism f V')).rightDerived p :=
  match p with
  | 0 => higherDirectImageRestrictIsoZeroOfLE f h
  | n + 1 => higherDirectImageRestrictIsoSuccOfLE f h (n + 1)

/-- The degree-uniform middle comparison in degree zero. -/
theorem higherDirectImageRestrictIsoOfLE_zero :
    higherDirectImageRestrictIsoOfLE f h 0 = higherDirectImageRestrictIsoZeroOfLE f h :=
  rfl

/-- The degree-uniform middle comparison in positive degree. -/
theorem higherDirectImageRestrictIsoOfLE_succ (n : ℕ) :
    higherDirectImageRestrictIsoOfLE f h (n + 1) =
      higherDirectImageRestrictIsoSuccOfLE f h (n + 1) :=
  rfl

/-- **Stacks 01E5, higher direct images, compatibility across nested opens, in every degree.**
The comparison `higherDirectImageRestrictIso` attached to `V`, whiskered by restriction along
`V' ≤ V` and followed by the transitivity isomorphism `moduleRestrictionOfLEIso` on the `Y`
side, agrees with the middle comparison `higherDirectImageRestrictIsoOfLE` followed by the
comparison attached to `V'`.

This is the degree-uniform cocycle stated against `higherDirectImageRestrictIsoOfLE`, the
degree-dispatching middle comparison. `LocalizationCocycle.lean` carries a differently-shaped
degree-uniform clause of its own, `higherDirectImageRestrictIso_ofLE`, whose right-hand side is
the `...SuccOfLE` comparison in every degree; the two are distinct statements, so this one keeps
the `anyDegree` suffix its scheme-level companions already use rather than shadowing that name.
The degree is an arbitrary natural number, so a consumer
whose degree is the dimension of a situation — which may be zero — may use it directly.  In
degree zero it is `higherDirectImageRestrictIsoZero_ofLE` and in positive degree
`higherDirectImageRestrictIsoSucc_ofLE`; the two comparisons being different isomorphisms, the
case split is in the definitions and not in the statement. -/
theorem higherDirectImageRestrictIso_ofLE_anyDegree (p : ℕ) :
    Functor.whiskerRight (higherDirectImageRestrictIso f V p).hom
          (moduleRestrictionOfLE Y h) ≫
        Functor.whiskerLeft ((modulePushforward f).rightDerived p)
          (moduleRestrictionOfLEIso Y h).hom =
      (higherDirectImageRestrictIsoOfLE f h p).hom ≫
        (higherDirectImageRestrictIso f V' p).hom := by
  cases p with
  | zero => exact higherDirectImageRestrictIsoZero_ofLE f h
  | succ n => exact higherDirectImageRestrictIsoSucc_ofLE f h (n + 1)

end Nested

end Stacks.Cohomology.HigherDirectImage

end
