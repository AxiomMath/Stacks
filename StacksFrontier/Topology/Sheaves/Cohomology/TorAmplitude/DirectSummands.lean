module

public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.OnARingedSpace

/-!
# Tor amplitude passes to retracts, hence to direct summands

Tag 08CK says that if `K ⊕ L` has Tor amplitude in `[a, b]` then so do `K` and `L`.  This file
proves it against `Stacks.Cohomology.TorAmplitude.HasTorAmplitude`, the Tor-amplitude predicate
  stated for *the*
canonical derived tensor product `Stacks.Cohomology.TorAmplitude.derTensor`, and carries it through
  the two derived
predicates of Tag 08CG that the characterisation of Tag 08CQ is phrased in: finite Tor dimension
and locally finite Tor dimension.

Everything here is proved for a **retract** rather than for a biproduct summand, with the
biproduct form deduced from it.  The reason is the one recorded for Stacks Tag 08CS in
`Stacks.Cohomology.PerfectDirectSummands`: a retract is carried to a retract by *any* functor, by
functoriality alone, whereas a biproduct decomposition needs the functor to be additive.  This is
what makes the locally-finite-Tor-dimension statement cheap — the restriction of `K` to an open is
a retract of the restriction of `K ⊞ L` with no additivity of
`AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules _ _ |>.mapDerivedCategory` required.

## Main results

* `Stacks.Cohomology.TorAmplitude.isZero_obj_of_retract`: a functor carries a retract of an object
  with zero image to
  an object with zero image.
* `Stacks.Cohomology.TorAmplitude.hasTorAmplitude_of_retract` and
  `Stacks.Cohomology.TorAmplitude.hasTorAmplitude_of_biprod`: Tag 08CK
  against the canonical derived tensor product.
* `Stacks.Cohomology.TorAmplitude.hasFiniteTorDimension_of_retract`,
  `Stacks.Cohomology.TorAmplitude.hasFiniteTorDimension_of_biprod`,
  `Stacks.Cohomology.TorAmplitude.locallyHasFiniteTorDimension_of_retract` and
  `Stacks.Cohomology.TorAmplitude.locallyHasFiniteTorDimension_of_biprod`: the same for the two
    derived predicates.

## Implementation notes

**Which `HasTorAmplitude` this is stated for, and why.**  There are four Tor-amplitude predicates
in the trees.  The one used here is `Stacks.Cohomology.TorAmplitude.HasTorAmplitude`, the only one
whose tensor operation is not a hypothesis:
it is stated against `Stacks.Cohomology.TorAmplitude.derTensor`, the canonical inhabitant of Tag
  06YU's
`DerivedTensorProduct`.  That is forced by the intended consumer.  The predicate that the
forward half of Tag 08CQ
  (`Stacks.Cohomology.TorAmplitude.locallyHasFiniteTorDimension_of_isPerfect`) *produces*, and
that the converse half would consume, is
  `Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension`, which unfolds
to this `HasTorAmplitude`; a statement about an arbitrary bifunctor cannot be applied to it
without first identifying the two vocabularies.

`Stacks.TorAmplitude.hasTorAmplitude_of_biprod` is the same
mathematics for an arbitrary bifunctor on its own spelling `Stacks.TorAmplitude.DOX` of the derived
category, and it already carries the `08CK` tag.  It is deliberately **not** imported here and
nothing below is a bridge to it, for two reasons: its ambient category
`Stacks.TorAmplitude.ModOX` is built from `Stacks.TorAmplitude.structureRingSheaf` rather than from
`StrictlyPerfect.structureSheafOfRings`, so applying it would mean identifying two spellings of
the category of `O_X`-modules; and that file declares a **global**
`instance : HasDerivedCategory (ModOX X)`, which no module in the trees currently imports, so
pulling it into the Tag 08CQ chain would seat a second `HasDerivedCategory` on a spelling of
`OXMod X` for every downstream consumer.  Nothing here is therefore tagged `08CK`.

The universes of the space, its structure sheaf and its modules all coincide, as they already must
for `StrictlyPerfect.OXMod` and for `Stacks.Cohomology.TorAmplitude.derTensor`; the derived
  category's own hom
universes stay independent (`d` for `X`, `d'` for its opens), exactly as for
`Stacks.Cohomology.TorAmplitude.locallyHasFiniteTorDimension_of_isPerfect`, the perfectness half
of Tag 08CQ.  No narrowing is introduced here.

The exactness instances for restriction to an open are `local instance`s where
`Stacks.Cohomology.TorAmplitude.HasTorAmplitude` is defined, so they are re-seated by
`attribute [local instance]` rather than restated, as the perfectness half of Tag 08CQ also does.

## References

* [Stacks Project, Tag 08CK](https://stacks.math.columbia.edu/tag/08CK)
* [Stacks Project, Tag 08CG](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Tag 08CQ](https://stacks.math.columbia.edu/tag/08CQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect

namespace Stacks.Cohomology.TorAmplitude

universe u d d' v₁ u₁ v₂ u₂

section Abstract

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable [HasZeroMorphisms D]

/-- **A functor carries a retract of an object with vanishing image to an object with vanishing
image.**  Only functoriality is used: `F i ≫ F r = F (i ≫ r) = 𝟙`, and a morphism into a zero
object is zero, so the identity of `F.obj A` factors through zero. -/
theorem isZero_obj_of_retract (F : C ⥤ D) {A B : C} (i : A ⟶ B) (r : B ⟶ A)
    (hir : i ≫ r = 𝟙 A) (hB : IsZero (F.obj B)) : IsZero (F.obj A) := by
  rw [IsZero.iff_id_eq_zero, ← ((Retract.mk i r hir).map F).retract]
  exact (hB.eq_zero_of_tgt ((Retract.mk i r hir).map F).i) ▸ zero_comp

end Abstract

section TorAmplitude

variable {X : RingedSpace.{u, u}} [HasDerivedCategory.{d} (OXMod.{u} X)]

-- `Stacks.Cohomology.TorAmplitude.derTensor` is stated at the
-- `Stacks.DerivedTensor.RingedSite.Modules X.sheaf` spelling of the
-- category of `O_X`-modules, which is `OXMod X` by `rfl`; an instance proved at one spelling of a
-- non-reducible definition does not fire at the other.  `OnARingedSpace.lean` seats the
-- translation, but only locally to that file, so it is re-seated here rather than restated.
attribute [local instance] hasDerivedCategoryModules

/-- **Tag 08CK for a retract.**  If `B` has Tor amplitude in `[a, b]` and `A` is a retract of `B`
in `D(O_X)`, then `A` has Tor amplitude in `[a, b]`.  For each module `F` and each degree `i` the
object `A ⊗^L F` is, through the functor `- ⊗^L F` followed by `H^i`, a retract of `B ⊗^L F`, so
its cohomology inherits the vanishing. -/
theorem hasTorAmplitude_of_retract (a b : ℤ) {A B : DerivedCategory (OXMod.{u} X)}
    (i : A ⟶ B) (r : B ⟶ A) (hir : i ≫ r = 𝟙 A)
    (h : HasTorAmplitude X B a b) : HasTorAmplitude X A a b := by
  intro F j hj
  exact isZero_obj_of_retract
    ((derTensor X).tensor.flip.obj ((DerivedCategory.singleFunctor (OXMod.{u} X) 0).obj F) ⋙
      DerivedCategory.homologyFunctor (OXMod.{u} X) j) i r hir (h F j hj)

/-- **Tag 08CK.**  If `K ⊞ L` has Tor amplitude in `[a, b]` then so do `K` and `L`, each being a
retract of the biproduct. -/
theorem hasTorAmplitude_of_biprod (a b : ℤ) (K L : DerivedCategory (OXMod.{u} X))
    (h : HasTorAmplitude X (K ⊞ L) a b) :
    HasTorAmplitude X K a b ∧ HasTorAmplitude X L a b :=
  ⟨hasTorAmplitude_of_retract a b biprod.inl biprod.fst biprod.inl_fst h,
    hasTorAmplitude_of_retract a b biprod.inr biprod.snd biprod.inr_snd h⟩

/-- **Finite Tor dimension passes to a retract.**  The same interval works. -/
theorem hasFiniteTorDimension_of_retract {A B : DerivedCategory (OXMod.{u} X)}
    (i : A ⟶ B) (r : B ⟶ A) (hir : i ≫ r = 𝟙 A)
    (h : HasFiniteTorDimension X B) : HasFiniteTorDimension X A := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨a, b, hasTorAmplitude_of_retract a b i r hir hab⟩

/-- **Finite Tor dimension passes to the two summands of a biproduct.** -/
theorem hasFiniteTorDimension_of_biprod (K L : DerivedCategory (OXMod.{u} X))
    (h : HasFiniteTorDimension X (K ⊞ L)) :
    HasFiniteTorDimension X K ∧ HasFiniteTorDimension X L :=
  ⟨hasFiniteTorDimension_of_retract biprod.inl biprod.fst biprod.inl_fst h,
    hasFiniteTorDimension_of_retract biprod.inr biprod.snd biprod.inr_snd h⟩

end TorAmplitude

section Local

variable {X : RingedSpace.{u, u}} [HasDerivedCategory.{d} (OXMod.{u} X)]
variable [∀ U : Opens X.carrier,
  HasDerivedCategory.{d'} (OXMod.{u} (X.restrict U.isOpenEmbedding))]

attribute [local instance] restrictModules_preservesFiniteLimits
  restrictModules_preservesFiniteColimits

/-- **Locally finite Tor dimension passes to a retract.**  The cover witnessing it for `B` works
for `A`: the derived restriction functor carries the retraction to a retraction, by functoriality
alone, so the restriction of `A` is a retract of the restriction of `B` over each member. -/
theorem locallyHasFiniteTorDimension_of_retract {A B : DerivedCategory (OXMod.{u} X)}
    (i : A ⟶ B) (r : B ⟶ A) (hir : i ≫ r = 𝟙 A)
    (h : LocallyHasFiniteTorDimension X B) : LocallyHasFiniteTorDimension X A := by
  obtain ⟨I, U, hsup, hfin⟩ := h
  refine ⟨I, U, hsup, fun k => ?_⟩
  refine hasFiniteTorDimension_of_retract
    ((AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X (U k)).mapDerivedCategory.map
      i)
    ((AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X (U k)).mapDerivedCategory.map
      r) ((Retract.mk i r hir).map _).retract (hfin k)

/-- **Locally finite Tor dimension passes to the two summands of a biproduct.**  This is the
Tor-amplitude half of the two inputs that Tag 08CS needs from the characterisation of Tag 08CQ. -/
theorem locallyHasFiniteTorDimension_of_biprod (K L : DerivedCategory (OXMod.{u} X))
    (h : LocallyHasFiniteTorDimension X (K ⊞ L)) :
    LocallyHasFiniteTorDimension X K ∧ LocallyHasFiniteTorDimension X L :=
  ⟨locallyHasFiniteTorDimension_of_retract biprod.inl biprod.fst biprod.inl_fst h,
    locallyHasFiniteTorDimension_of_retract biprod.inr biprod.snd biprod.inr_snd h⟩

end Local

end Stacks.Cohomology.TorAmplitude

end
