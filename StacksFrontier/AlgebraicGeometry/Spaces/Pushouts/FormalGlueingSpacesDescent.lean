module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Descent.IndQuasiAffineFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpaces

/-!
# Testing a property of a space over `X` on the two restrictions of a formal glueing situation

In a formal glueing situation `(f : Y ⟶ X, Z, U = X \ Z, V = Y \ f⁻¹(Z))`, the family
`{U ⟶ X, Y ⟶ X}` is refined by an fpqc covering of `X`. Consequently any property of morphisms
of algebraic spaces which is local on the base for the fpqc topology and stable under base
change can be tested on the two restrictions: a space `X'` over `X` has the property if and
only if `U ×_X X' ⟶ U` and `Y ×_X X' ⟶ Y` do.

## Main definitions

* `AlgebraicGeometry.Space.FormalGlueingSituation.spaceOfX`,
  `AlgebraicGeometry.Space.FormalGlueingSituation.spaceOfY` and
  `AlgebraicGeometry.Space.FormalGlueingSituation.spaceOfU`: the three spaces of a formal
  glueing situation read as objects of the category of algebraic spaces over `S`.
* `AlgebraicGeometry.Space.FormalGlueingSituation.homOfU` and
  `AlgebraicGeometry.Space.FormalGlueingSituation.homOfF`: the two morphisms `U ⟶ X` and
  `Y ⟶ X` of the situation in that category.

## Main results

* `AlgebraicGeometry.Space.FormalGlueingSituation.morphismProperty_iff_restrictions`: the
  criterion itself, for an arbitrary fpqc-local base-change-stable property.
* `AlgebraicGeometry.Space.FormalGlueingSituation.isAffineHom_iff_restrictions`,
  `AlgebraicGeometry.Space.FormalGlueingSituation.isClosedImmersion_iff_restrictions` and
  `AlgebraicGeometry.Space.FormalGlueingSituation.isFinite_iff_restrictions`: the criterion
  for the three conditions which cut out the subcategories of Stacks 0AF4, namely being
  affine, being a closed immersion and being finite.

## Implementation notes

The three instantiations are exactly the conditions appearing in the three clauses of
Stacks 0AF4, and the criterion is the step which the source's proof of that lemma makes after
reducing to its clause (1): "`X' → X` is a closed immersion if and only if both
`U ×_X X' → U` and `Y ×_X X' → Y` are closed immersions", and likewise for finite morphisms.
The tag asserts an equivalence of categories, whose construction of a space over `X` from a
glueing triple is not this criterion; it is registered on
`AlgebraicGeometry.Space.FormalGlueingSituation.affineGlueingFunctor_isEquivalence`,
`closedGlueingFunctor_isEquivalence` and `finiteGlueingFunctor_isEquivalence`
(`StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesRestrictedEquivalences`).

The proof is the one of Stacks 0AF5 in
`StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpaces`, carried out for an
arbitrary property instead of for invertibility and for an object of `Over X` instead of a
morphism of `Over X`: the fpqc covering `{Xᵢ ⟶ X}` refining `{U ⟶ X, Y ⟶ X}` of Stacks 0AF1
is made into a zero hypercover of `X`, over whose members the base change of `X' ⟶ X` is a
base change of one of the two restrictions, and
`CategoryTheory.MorphismProperty.IsLocalAtTarget.of_zeroHypercover` assembles the property
over the covering into the property over `X`. Only the target of the morphism is covered, so —
unlike in Stacks 0AF5, where the covering has to be pulled back to the target of the morphism
of `Over X` under consideration — the covering of Stacks 0AF1 is used as it stands.

That the base change of `X' ⟶ X` along a composite `Xᵢ ⟶ U ⟶ X` is a base change of the base
change along `U ⟶ X` is `property_pullback_snd_comp`, which reads the composite off
`CategoryTheory.Over.pullbackComp` at the object `Over.mk a`, exactly as Stacks 0AF5's
`isIso_pullback_map_of_comp` reads it off the same isomorphism at a morphism.

Affineness is the one of the three conditions with no `IsStableUnderBaseChange` instance at
the packaged spelling, so `AlgebraicGeometry.Space.isAffineHom_hom_of_isPullback` is used to
build one locally rather than registered globally, which would duplicate a declaration
belonging to the affine development.

## References

* [Stacks Project, Tag 041Z](https://stacks.math.columbia.edu/tag/041Z)
* [Stacks Project, Tag 0420](https://stacks.math.columbia.edu/tag/0420)
* [Stacks Project, Tag 0426](https://stacks.math.columbia.edu/tag/0426)
* [Stacks Project, Tag 0AF1](https://stacks.math.columbia.edu/tag/0AF1)
* [Stacks Project, Tag 0AF4](https://stacks.math.columbia.edu/tag/0AF4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.FormalGlueingSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The ambient space `X` of a formal glueing situation, as an object of the category of
algebraic spaces over `S`. -/
abbrev spaceOfX (D : FormalGlueingSituation B S hS) : AlgebraicSpaces B S hS :=
  ⟨D.X, D.algebraicSpace_X⟩

/-- The space `Y` of a formal glueing situation, as an object of the category of algebraic
spaces over `S`. -/
abbrev spaceOfY (D : FormalGlueingSituation B S hS) : AlgebraicSpaces B S hS :=
  ⟨D.Y, D.algebraicSpace_Y⟩

/-- The open complement `U = X \ Z` of a formal glueing situation, as an object of the
category of algebraic spaces over `S`. -/
abbrev spaceOfU (D : FormalGlueingSituation B S hS) : AlgebraicSpaces B S hS :=
  ⟨D.U.toFunctor, (isOpenSubspace_U D).1⟩

/-- The inclusion `U ⟶ X` of the open complement of `Z`, as a morphism of algebraic spaces
over `S`. -/
abbrev homOfU (D : FormalGlueingSituation B S hS) : spaceOfU D ⟶ spaceOfX D :=
  ⟨D.U.ι⟩

/-- The morphism `f : Y ⟶ X` being glued along, as a morphism of algebraic spaces over
`S`. -/
abbrev homOfF (D : FormalGlueingSituation B S hS) : spaceOfY D ⟶ spaceOfX D :=
  ⟨D.f⟩

/-- Base change along a composite is the composite of the base changes, so a property stable
under base change which holds for the base change of `a` along the second factor holds for
the base change of `a` along any morphism `g` equal to the composite. -/
private theorem property_pullback_snd_comp
    {P : MorphismProperty (AlgebraicSpaces B S hS)} (hbc : P.IsStableUnderBaseChange)
    {X₀ T W X' : AlgebraicSpaces B S hS} (a : X' ⟶ X₀) (t : T ⟶ X₀) (c : W ⟶ T)
    (g : W ⟶ X₀) (hg : c.hom ≫ t.hom = g.hom) (h : P (pullback.snd a t)) :
    P (pullback.snd a g) := by
  obtain rfl : c ≫ t = g := (ObjectProperty.ι _).map_injective hg
  have e := (Over.pullbackComp c t).app (Over.mk a)
  have : IsIso e.hom.left := Functor.map_isIso (Over.forget W) e.hom
  have hw : e.hom.left ≫ pullback.snd (pullback.snd a t) c =
      pullback.snd a (c ≫ t) := Over.w e.hom
  rw [← hw]
  exact (MorphismProperty.cancel_left_of_respectsIso (P := P) e.hom.left
      (pullback.snd (pullback.snd a t) c)).2
    (hbc.of_isPullback (IsPullback.of_hasPullback (pullback.snd a t) c) h)

/-- In a formal glueing situation, a property of morphisms of algebraic spaces which is local
on the base for the fpqc topology and stable under base change holds for a space over `X`
exactly when it holds for its two restrictions, to `U` and to `Y`.

The family `{U ⟶ X, Y ⟶ X}` is refined by an fpqc covering of `X` (**Stacks 0AF1**), over
each member of which the base change of `X' ⟶ X` is a base change of one of the two
restrictions. -/
theorem morphismProperty_iff_restrictions (D : FormalGlueingSituation B S hS)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    (hbc : P.IsStableUnderBaseChange)
    (hP : P.IsLocalAtTarget (Topology.precoverage.{u, u} .fpqc B S hS))
    {X' : AlgebraicSpaces B S hS} (a : X' ⟶ spaceOfX D) :
    P a ↔ P (pullback.snd a (homOfU D)) ∧ P (pullback.snd a (homOfF D)) := by
  refine ⟨fun ha => ⟨hbc.of_isPullback (IsPullback.of_hasPullback a (homOfU D)) ha,
    hbc.of_isPullback (IsPullback.of_hasPullback a (homOfF D)) ha⟩, fun ⟨hU, hY⟩ => ?_⟩
  obtain ⟨I, Xi, g, hXi, hcover, hfactor⟩ :=
    exists_fpqcCovering_refining_openComplement_and_source B S hS D
  let Xi' (i : I) : AlgebraicSpaces B S hS := ⟨Xi i, hXi i⟩
  let gi (i : I) : Xi' i ⟶ spaceOfX D := ⟨g i⟩
  let 𝒰 : (Topology.precoverage.{u, u} .fpqc B S hS).ZeroHypercover (spaceOfX D) :=
    { I₀ := I
      X := Xi'
      f := gi
      mem₀ := ⟨I, Xi', gi, rfl, (spaceOfX D).property, fun i => (Xi' i).property, hcover⟩ }
  refine MorphismProperty.IsLocalAtTarget.of_zeroHypercover (P := P) 𝒰 fun i => ?_
  show P (pullback.snd a (gi i))
  rcases hfactor i with ⟨b, hb⟩ | ⟨c, hc⟩
  · exact property_pullback_snd_comp hbc a (homOfU D) ⟨b⟩ (gi i)
      hb hU
  · exact property_pullback_snd_comp hbc a (homOfF D) ⟨c⟩ (gi i)
      hc hY

/-- In a formal glueing situation, a space over `X` is affine over `X` exactly when its two
restrictions, to `U` and to `Y`, are affine.

This is the condition cutting out the two subcategories of clause (1) of **Stacks 0AF4**;
affineness is fpqc local on the base by **Stacks 041Z**. -/
theorem isAffineHom_iff_restrictions (D : FormalGlueingSituation B S hS)
    {X' : AlgebraicSpaces B S hS} (a : X' ⟶ spaceOfX D) :
    IsAffineHom B S hS a.hom ↔
      IsAffineHom B S hS (pullback.snd a (homOfU D)).hom ∧
        IsAffineHom B S hS (pullback.snd a (homOfF D)).hom :=
  morphismProperty_iff_restrictions D
    (fun _ _ k => IsAffineHom B S hS k.hom)
    ⟨fun sq hf => isAffineHom_hom_of_isPullback sq hf⟩
    (isLocalAtTarget_isAffineHom_fpqc.{u, u} B S hS) a

/-- In a formal glueing situation, a space over `X` is a closed subspace of `X` exactly when
its two restrictions, to `U` and to `Y`, are closed immersions.

This is the condition cutting out the two subcategories of clause (2) of **Stacks 0AF4**, and
it is the step the source's proof of that clause makes after reducing to clause (1); being a
closed immersion is fpqc local on the base by **Stacks 0420**. -/
theorem isClosedImmersion_iff_restrictions (D : FormalGlueingSituation B S hS)
    {X' : AlgebraicSpaces B S hS} (a : X' ⟶ spaceOfX D) :
    IsClosedImmersion B S hS a.hom ↔
      IsClosedImmersion B S hS (pullback.snd a (homOfU D)).hom ∧
        IsClosedImmersion B S hS (pullback.snd a (homOfF D)).hom :=
  morphismProperty_iff_restrictions D (closedImmersionProperty B S hS) inferInstance
    (isClosedImmersion_isLocalAtTarget_fpqc.{u, u} B S hS) a

/-- In a formal glueing situation, a space over `X` is finite over `X` exactly when its two
restrictions, to `U` and to `Y`, are finite.

This is the condition cutting out the two subcategories of clause (3) of **Stacks 0AF4**, and
it is the step the source's proof of that clause makes after reducing to clause (1);
finiteness is fpqc local on the base by **Stacks 0426**. -/
theorem isFinite_iff_restrictions (D : FormalGlueingSituation B S hS)
    {X' : AlgebraicSpaces B S hS} (a : X' ⟶ spaceOfX D) :
    IsFinite B S hS a.hom ↔
      IsFinite B S hS (pullback.snd a (homOfU D)).hom ∧
        IsFinite B S hS (pullback.snd a (homOfF D)).hom :=
  morphismProperty_iff_restrictions D (finiteMorphismProperty B S hS) inferInstance
    (isFinite_isLocalAtTarget_fpqc.{u, u} B S hS) a

end AlgebraicGeometry.Space.FormalGlueingSituation

end
