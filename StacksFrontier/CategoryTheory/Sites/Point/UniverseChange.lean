module

public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import StacksFrontier.CategoryTheory.Sites.LocallyBijectiveUniverse
public import StacksFrontier.CategoryTheory.Sites.Point.ConservativeFamily

/-!
# Changing the universe of a point of a site

A point of a site `(C, J)` relative to a universe `w` is, in Mathlib's
`CategoryTheory.GrothendieckTopology.Point.{w}`, a fibre functor `C ⥤ Type w` whose category of
elements is cofiltered and `w`-initially small and for which covering sieves act jointly
surjectively. The universe `w` is a parameter of the notion, and the fibre functors of a point
relative to `w` compute stalks of sheaves of `Type w` only.

This file raises `w`. Composing the fibre functor with `uliftFunctor.{w'}` gives a point relative
to `max w w'`, and conservativity of a family of points is preserved: a site with enough points
relative to `w` has enough points relative to `max w w'`.

The need for this is that nothing identifies `Type w` with `Type w'` for incomparable `w` and `w'`:
a point whose fibre functor lands in `Type w` cannot be used to detect isomorphisms of sheaves of
`Type w'`, because `ObjectProperty.IsConservativeFamilyOfPoints` and
`JointlyReflectIsomorphisms` both demand that the coefficient category be concrete over the
point's own universe. Raising the point's universe is the only repair, and `ULift` is what effects
it.

## Main definitions

* `CategoryTheory.Functor.Elements.uliftEquiv`: raising the universe of a functor to types does not
  change its category of elements, `F.Elements ≌ (F ⋙ uliftFunctor.{w'}).Elements`.
* `CategoryTheory.GrothendieckTopology.Point.ulift`: a point relative to `w` as a point relative to
  `max w w'`, with fibre functor `Φ.fiber ⋙ uliftFunctor.{w'}`.

## Main results

* `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.ulift`: any family of points
  relative to `max w w'` containing the universe lifts of a `w`-small conservative family is
  conservative.
* `CategoryTheory.GrothendieckTopology.IsConservativeFamily.ulift`: the universe lift of a
  conservative family indexed by a `w`-small type is conservative.
* `CategoryTheory.GrothendieckTopology.hasEnoughPoints_ulift`: a site with enough points relative
  to `w` has enough points relative to `max w w'`.

## Implementation notes

* The lift is `Φ.fiber ⋙ uliftFunctor.{w'}` and not, say, a point produced by
  `Point.ofIsCofiltered` from the projection `Φ.fiber.Elements ⥤ C`. Both are available, but the
  composite with `uliftFunctor` has the fibre `ULift (Φ.fiber.obj X)` *definitionally*, so an
  element of the lifted fibre over `X` is a `ULift.up` of an element of the original and every
  statement about the new point reduces to the old one by `ULift.up`/`ULift.down`; the
  `ofIsCofiltered` route presents the fibre as a colimit and needs an isomorphism at each step.
  Composing on the right (`Φ.fiber ⋙ uliftFunctor`) rather than the left is forced: `uliftFunctor`
  raises the universe of the *values* of the fibre functor, which is the universe that the point's
  parameter `w` names, while `C` is untouched.
* The two smallness fields are where the work is. `IsCofiltered` transfers across
  `Functor.Elements.uliftEquiv` because an equivalence is initial. `InitiallySmall` does not
  transfer so directly: the lifted elements category must be initially small relative to the
  *larger* universe `max w w'`, so the hypothesis `InitiallySmall.{w} F.Elements` is first raised
  to `InitiallySmall.{max w w'} F.Elements` — Mathlib has no universe monotonicity lemma for
  `InitiallySmall`, and the step is to observe that the chosen initial model, being a small
  category in `Type w`, is `EssentiallySmall.{max w w'}`, so
  `initiallySmall_of_initial_of_essentiallySmall` applies to the initial functor out of it.
* Conservativity is transferred through the sieve criterion of SGA 4 IV 6.5 (a) rather than
  directly: `ObjectProperty.IsConservativeFamilyOfPoints.mk'` reduces conservativity at the larger
  universe to "every sieve on which the fibres act jointly surjectively is covering", and
  `jointly_reflect_ofArrows_mem_of_small` supplies exactly that at the smaller universe, applied to
  the family of *all* arrows of the given sieve. Going through `mk'` is what keeps the
  `Type (max w w')`-valued sheaf theory out of the argument entirely; the price is the hypotheses
  that sheafification exist in both universes and that local bijectivity detect `J.W` in the
  smaller one.
-/

@[expose] public section

universe w' w v u t

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace Functor.Elements

variable (F : C ⥤ Type w)

/-- The comparison functor of `CategoryTheory.Functor.Elements.uliftEquiv`: an element of `F` is an
element of the universe-lifted functor `F ⋙ uliftFunctor`. -/
def ulift : F.Elements ⥤ (F ⋙ uliftFunctor.{w'}).Elements where
  obj x := .mk (F := F ⋙ uliftFunctor.{w'}) (obj := x.obj) (ULift.up x.val)
  map f := Functor.Elements.homMk f.hom (congrArg ULift.up f.map_val)

/-- The inverse comparison functor of `CategoryTheory.Functor.Elements.uliftEquiv`. -/
def uliftInv : (F ⋙ uliftFunctor.{w'}).Elements ⥤ F.Elements where
  obj x := .mk (F := F) (obj := x.obj) x.val.down
  map f := Functor.Elements.homMk f.hom (congrArg ULift.down f.map_val)

/-- Raising the universe of a functor to types does not change its category of elements: an element
of `(F ⋙ uliftFunctor).obj X` is a `ULift` of an element of `F.obj X`, and a morphism of elements
is its underlying morphism of `C` either way, so the two categories are isomorphic, both round
trips being the identity functor on the nose. -/
def uliftEquiv : F.Elements ≌ (F ⋙ uliftFunctor.{w'}).Elements :=
  CategoryTheory.Equivalence.mk (ulift.{w'} F) (uliftInv.{w'} F) (eqToIso rfl) (eqToIso rfl)

/-- The category of elements of `F ⋙ uliftFunctor` is cofiltered when that of `F` is. -/
instance [IsCofiltered F.Elements] : IsCofiltered (F ⋙ uliftFunctor.{w'}).Elements :=
  IsCofiltered.of_equivalence (uliftEquiv.{w'} F)

/-- The category of elements of `F ⋙ uliftFunctor.{w'}` is `max w w'`-initially small when that
of `F` is `w`-initially small. -/
instance [InitiallySmall.{w} F.Elements] :
    InitiallySmall.{max w w'} (F ⋙ uliftFunctor.{w'}).Elements :=
  have : InitiallySmall.{max w w'} F.Elements :=
    initiallySmall_of_initial_of_essentiallySmall (fromInitialModel.{w} F.Elements)
  initiallySmall_of_initial_of_initiallySmall (uliftEquiv.{w'} F).functor

end Functor.Elements

variable {J : GrothendieckTopology C}

/-- A point of a site relative to a universe `w`, read as a point relative to the larger universe
`max w w'`: the fibre functor is composed with `uliftFunctor`, so the fibre of the new point over
`X : C` is `ULift (Φ.fiber.obj X)`. -/
@[simps fiber]
def GrothendieckTopology.Point.ulift (Φ : GrothendieckTopology.Point.{w} J) :
    GrothendieckTopology.Point.{max w w'} J where
  fiber := Φ.fiber ⋙ uliftFunctor.{w'}
  jointly_surjective R hR x := by
    obtain ⟨Y, f, hf, y, hy⟩ := Φ.jointly_surjective R hR x.down
    exact ⟨Y, f, hf, ULift.up y, congrArg ULift.up hy⟩

open GrothendieckTopology in
/-- Conservativity of a family of points survives raising the universe: if `P` is a `w`-small
conservative family of points relative to `w`, then any family `Q` of points relative to
`max w w'` which contains the universe lift of every point of `P` is conservative. -/
theorem ObjectProperty.IsConservativeFamilyOfPoints.ulift
    {P : ObjectProperty (Point.{w} J)} [ObjectProperty.Small.{w} P]
    [LocallySmall.{w} C] [HasSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]
    [LocallySmall.{max w w'} C] [HasSheafify J (Type (max w w'))]
    (hP : P.IsConservativeFamilyOfPoints)
    {Q : ObjectProperty (Point.{max w w'} J)} (hQ : ∀ Φ : Subtype P, Q (Φ.1.ulift.{w'})) :
    Q.IsConservativeFamilyOfPoints := by
  apply ObjectProperty.IsConservativeFamilyOfPoints.mk'
  intro X S hS
  refine J.superset_covering
    (S := Sieve.ofArrows (fun j : Σ Z : C, { g : Z ⟶ X // S.arrows g } ↦ j.1)
      (fun j ↦ j.2.1)) ?_ ?_
  · rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    exact fun j ↦ j.2.2
  · rw [hP.jointly_reflect_ofArrows_mem_of_small]
    intro Φ x
    obtain ⟨Z, g, hg, y, hy⟩ := hS ⟨_, hQ ⟨Φ.obj, Φ.property⟩⟩ (ULift.up x)
    exact ⟨⟨Z, g, hg⟩, y.down, congrArg ULift.down hy⟩

namespace GrothendieckTopology

/-- The universe lift of a conservative family of points indexed by a `w`-small type is a
conservative family of points relative to the larger universe. -/
theorem IsConservativeFamily.ulift {ι : Type t} [Small.{w} ι] {p : ι → Point.{w} J}
    [LocallySmall.{w} C] [HasSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]
    [LocallySmall.{max w w'} C] [HasSheafify J (Type (max w w'))]
    (hp : IsConservativeFamily p) :
    IsConservativeFamily (fun i ↦ (p i).ulift.{w'}) := by
  rw [isConservativeFamily_iff_ofObj]
  refine ((isConservativeFamily_iff_ofObj p).1 hp).ulift.{w'} (fun Φ ↦ ?_)
  obtain ⟨i, hi⟩ := (ObjectProperty.ofObj_iff p _).1 Φ.2
  rw [← hi]
  exact ObjectProperty.ofObj_apply _ i

/-- A site with enough points relative to a universe `w` has enough points relative to any larger
universe `max w w'`, provided that sheaves of `Type (max w w')` can be sheafified. -/
theorem hasEnoughPoints_ulift (J : GrothendieckTopology C) [HasEnoughPoints.{w} J]
    [LocallySmall.{w} C] [HasSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]
    [LocallySmall.{max w w'} C] [HasSheafify J (Type (max w w'))] :
    HasEnoughPoints.{max w w'} J where
  exists_objectProperty := by
    obtain ⟨P, hP₁, hP₂⟩ := HasEnoughPoints.exists_objectProperty.{w} J
    have : Small.{max w w'} (Subtype P) := Small.trans_univLE.{w, max w w'} _
    exact ⟨ObjectProperty.ofObj (fun Φ : Subtype P ↦ Φ.1.ulift.{w'}), inferInstance,
      hP₂.ulift.{w'} (fun Φ ↦ ObjectProperty.ofObj_apply _ Φ)⟩

end GrothendieckTopology

end CategoryTheory
