module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkInverseImageModules
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.UnitsSquareCriterion
public import StacksFrontier.CategoryTheory.Sites.Modules.UnitsSheafStalk

/-!
# A local map of stalk rings reflects units

Let `(C, J)` be a site, `Φ` a point of it and `φ : O₁ ⟶ O₂` a morphism of sheaves of
commutative rings on `(C, J)`.  Condition (3) of Stacks 04H9 for `φ` at `Φ` asks that the
fibre functor of `Φ` on sheaves of *sets* reflect units for `φ`, in the sense of
`AlgebraicGeometry.RingedTopos.ReflectsUnitsObj`; what is usually available instead is that the
fibre of `φ` taken in commutative rings, `Φ⁻¹φ : Φ⁻¹O₁ ⟶ Φ⁻¹O₂`, is a *local* ring
homomorphism.  This file passes from the second to the first.

The two statements differ only by a change of ring structure.  The fibre at `Φ` of the
underlying sheaf of sets of a sheaf of commutative rings carries the ring structure transported
along the fibre functor, `CategoryTheory.Sheaf.ringObjRing`, and a section of it is invertible
exactly when it lifts through the units subsheaf, by
`AlgebraicGeometry.RingedTopos.isUnit_iff_exists_map_unitsIncl`.  So all that is needed is a
multiplicative bijection of that transported ring with the honest fibre of `O` in commutative
rings, natural in `O`; locality of `Φ⁻¹φ` then transports to the transported rings and gives
reflection of units.

## Main definitions

* `AlgebraicGeometry.RingedTopos.stalkRingCmp`: the comparison of the transported fibre ring of
  the underlying sheaf of sets of `O` with the fibre of `O` taken in commutative rings.
* `AlgebraicGeometry.RingedTopos.stalkRingMonoidHom` and
  `AlgebraicGeometry.RingedTopos.stalkRingMulEquiv`: that comparison as a monoid homomorphism
  and as a multiplicative equivalence.

## Main results

* `AlgebraicGeometry.RingedTopos.stalkRingCmp_mul`,
  `AlgebraicGeometry.RingedTopos.stalkRingCmp_one` and
  `AlgebraicGeometry.RingedTopos.stalkRingCmp_bijective`: the comparison is a multiplicative
  bijection.
* `AlgebraicGeometry.RingedTopos.stalkRingCmp_naturality`: it is natural in the sheaf of
  commutative rings.
* `AlgebraicGeometry.RingedTopos.reflectsUnitsObj_sheafFiber_of_isLocalHom`: **condition (3) of
  Stacks 04H9 at a point of the site**, from locality of the fibre of `φ`.
* `AlgebraicGeometry.RingedTopos.isLocalHom_sheafFiber_of_reflectsUnitsObj`: the converse —
  locality of the fibre of `φ` from reflection of units.
* `AlgebraicGeometry.RingedTopos.isLocalHom_sheafFiber_iff_reflectsUnitsObj`: the two together.

## Implementation notes

The comparison is the composite of two instances of Mathlib's
`CategoryTheory.GrothendieckTopology.Point.presheafFiberCompIso`, one for `forget RingCat` and
one for `forget₂ CommRingCat RingCat`; the first of them is
`Stacks.Sheaves.StalkTransport.ringStalkComparison`, whose multiplicativity is the only
algebraic input and is already available.  The second is a morphism of `RingCat`, so its
multiplicativity is formal.

Only the multiplicative structure of the comparison is used, so it is packaged as a `MulEquiv`
rather than a `RingEquiv`; the unit element is handled by surjectivity, exactly as in
`AlgebraicGeometry.etaleStalkMulEquiv`, and additivity is never needed.

The source and the target of the comparison are spelled through the sheaf of rings underlying
`O`, `Stacks.SheafOfModules.Tensor.ringSheaf O`, rather than through `sheafCompose J (forget
CommRingCat)`.  The two
agree definitionally, but only the first spelling lets instance search find the transported ring
structure on the fibre.

In `AlgebraicGeometry.RingedTopos.reflectsUnitsObj_sheafFiber_of_isLocalHom` the instance
arguments are listed *after* the hypothesis rather than before the point of the site.  The point
and the morphism are what the hypothesis determines, and an instance argument placed before them
is searched for while they are still unknown, which forces the universe of the sections to a
value unrelated to the one the hypothesis has; with the instances last the hypothesis is
elaborated first and determines everything.

## References

* [Stacks Project, Tag 04H9](https://stacks.math.columbia.edu/tag/04H9)
* [Stacks Project, Tag 04HA](https://stacks.math.columbia.edu/tag/04HA)
* [Stacks Project, Tag 04EH](https://stacks.math.columbia.edu/tag/04EH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.StalkTransport

attribute [local instance] CategoryTheory.Sheaf.ringObjRing

namespace AlgebraicGeometry.RingedTopos

universe w v u

section Comparison

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

section OneSheaf

variable (Φ : J.Point.{w}) (O : Sheaf J CommRingCat.{w})

/-- The comparison of Mathlib's
`CategoryTheory.GrothendieckTopology.Point.presheafFiberCompIso` for the forgetful functor from
commutative rings to rings, at the underlying presheaf of `O`: the fibre in rings of the sheaf
of rings underlying `O` is the ring underlying the fibre of `O` taken in commutative rings. -/
noncomputable abbrev stalkForget₂Iso :
    (Φ.presheafFiber (A := RingCat.{w})).obj
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O).obj ≅
      (forget₂ CommRingCat.{w} RingCat.{w}).obj ((Φ.sheafFiber (A := CommRingCat.{w})).obj O) :=
  (Φ.presheafFiberCompIso (forget₂ CommRingCat.{w} RingCat.{w})).app O.obj

/-- **The transported fibre ring of the underlying sheaf of sets of `O` is the fibre of `O` in
commutative rings.** The comparison is the fibre comparison for `forget RingCat` followed by the
fibre comparison for `forget₂ CommRingCat RingCat`. -/
noncomputable def stalkRingCmp :
    (Φ.sheafFiber (A := Type w)).obj
        (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) →
      ↥((Φ.sheafFiber (A := CommRingCat.{w})).obj O) :=
  fun a ↦ (stalkForget₂Iso Φ O).hom.hom
    (ringStalkComparison Φ ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) a)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The comparison with the fibre in commutative rings is bijective, being a composite of two
components of isomorphisms. -/
theorem stalkRingCmp_bijective : Function.Bijective (stalkRingCmp Φ O) :=
  (ConcreteCategory.bijective_of_isIso (stalkForget₂Iso Φ O).hom).comp
    (bijective_ringStalkComparison Φ ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O))

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The comparison with the fibre in commutative rings is multiplicative. -/
theorem stalkRingCmp_mul (p q : (Φ.sheafFiber (A := Type w)).obj
    (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O))) :
    stalkRingCmp Φ O (p * q) = stalkRingCmp Φ O p * stalkRingCmp Φ O q :=
  (congrArg (stalkForget₂Iso Φ O).hom.hom
    (ringStalkComparison_ringMulObj Φ
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) p q)).trans (map_mul _ _ _)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The comparison with the fibre in commutative rings preserves the unit. -/
theorem stalkRingCmp_one : stalkRingCmp Φ O 1 = 1 := by
  obtain ⟨z, hz⟩ := (stalkRingCmp_bijective Φ O).2 1
  have h1 := stalkRingCmp_mul Φ O 1 z
  rw [one_mul, hz, mul_one] at h1
  exact h1.symm

/-- The comparison with the fibre in commutative rings, as a monoid homomorphism. -/
noncomputable def stalkRingMonoidHom :
    (Φ.sheafFiber (A := Type w)).obj
        (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) →*
      ↥((Φ.sheafFiber (A := CommRingCat.{w})).obj O) where
  toFun := stalkRingCmp Φ O
  map_one' := stalkRingCmp_one Φ O
  map_mul' := stalkRingCmp_mul Φ O

/-- The transported fibre ring of the underlying sheaf of sets of `O`, as a multiplicative
equivalence with the fibre of `O` taken in commutative rings. -/
noncomputable def stalkRingMulEquiv :
    (Φ.sheafFiber (A := Type w)).obj
        (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) ≃*
      ↥((Φ.sheafFiber (A := CommRingCat.{w})).obj O) :=
  MulEquiv.ofBijective (stalkRingMonoidHom Φ O) (stalkRingCmp_bijective Φ O)

end OneSheaf

variable (Φ : J.Point.{w}) {O₁ O₂ : Sheaf J CommRingCat.{w}}

/-- **The comparison with the fibre in commutative rings is natural.** Both of its halves are
components of a natural isomorphism, so the fibre of a morphism of sheaves of commutative rings
is computed by the comparison from the fibre of the underlying morphism of sheaves of sets. -/
theorem stalkRingCmp_naturality (φ : O₁ ⟶ O₂)
    (a : (Φ.sheafFiber (A := Type w)).obj
      (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O₁))) :
    stalkRingCmp Φ O₂ ((Φ.sheafFiber (A := Type w)).map (forgetRingMap φ) a) =
      ((Φ.sheafFiber (A := CommRingCat.{w})).map φ).hom (stalkRingCmp Φ O₁ a) := by
  have h₁ : ringStalkComparison Φ ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O₂)
        ((Φ.sheafFiber (A := Type w)).map (forgetRingMap φ) a) =
      ((Φ.presheafFiber (A := RingCat.{w})).map ((Stacks.forgetCommRingSheaf J).map φ).hom).hom
        (ringStalkComparison Φ ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O₁) a) :=
    ConcreteCategory.congr_hom
      ((Φ.presheafFiberCompIso (forget RingCat.{w})).hom.naturality
        ((Stacks.forgetCommRingSheaf J).map φ).hom) a
  have h₂ : ∀ b : (Φ.presheafFiber (A := RingCat.{w})).obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O₁).obj,
      (stalkForget₂Iso Φ O₂).hom.hom
          (((Φ.presheafFiber (A := RingCat.{w})).map
            ((Stacks.forgetCommRingSheaf J).map φ).hom).hom b) =
        ((Φ.sheafFiber (A := CommRingCat.{w})).map φ).hom
          ((stalkForget₂Iso Φ O₁).hom.hom b) := fun b ↦
    ConcreteCategory.congr_hom
      ((Φ.presheafFiberCompIso (forget₂ CommRingCat.{w} RingCat.{w})).hom.naturality φ.hom) b
  exact (congrArg (stalkForget₂Iso Φ O₂).hom.hom h₁).trans (h₂ _)

end Comparison

/-- An element of the transported fibre ring is a unit iff its image under the comparison is. -/
private theorem isUnit_stalkRingCmp_iff {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget RingCat.{w})]
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] (Φ : J.Point.{w})
    (O : Sheaf J CommRingCat.{w})
    {a : (Φ.sheafFiber (A := Type w)).obj
      (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O))} :
    IsUnit (stalkRingCmp Φ O a) ↔ IsUnit a :=
  MulEquiv.isUnit_map (stalkRingMulEquiv Φ O)

/-- **Condition (3) of Stacks 04H9 at a point of the site.** If the fibre at `Φ` of a morphism
`φ : O₁ ⟶ O₂` of sheaves of commutative rings, taken in commutative rings, is a local ring
homomorphism, then the fibre functor of `Φ` on sheaves of sets reflects units for `φ`.

Both the hypothesis and the conclusion of
`AlgebraicGeometry.RingedTopos.ReflectsUnitsObj` say that an element of a transported fibre ring
is invertible, by `AlgebraicGeometry.RingedTopos.isUnit_iff_exists_map_unitsIncl`; transporting
along `AlgebraicGeometry.RingedTopos.stalkRingMulEquiv` turns them into invertibility in the
fibres taken in commutative rings, where locality is exactly the implication wanted. -/
theorem reflectsUnitsObj_sheafFiber_of_isLocalHom {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (Φ : J.Point.{w}) {O₁ O₂ : Sheaf J CommRingCat.{w}}
    (φ : O₁ ⟶ O₂) (h : IsLocalHom ((Φ.sheafFiber (A := CommRingCat.{w})).map φ).hom)
    [LocallySmall.{w} C] [J.HasSheafCompose (forget RingCat.{w})]
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] :
    ReflectsUnitsObj (Φ.sheafFiber (A := Type w)) φ := by
  intro a ha
  refine (isUnit_iff_exists_map_unitsIncl (ofStructureSheaf J O₁)
    (Φ.sheafFiber (A := Type w)) a).1 ((isUnit_stalkRingCmp_iff Φ O₁).1 (h.map_nonunit _ ?_))
  refine (congrArg IsUnit (stalkRingCmp_naturality Φ φ a)).mp ?_
  exact (isUnit_stalkRingCmp_iff Φ O₂).2 ((isUnit_iff_exists_map_unitsIncl (ofStructureSheaf J O₂)
    (Φ.sheafFiber (A := Type w)) _).2 ha)

/-- **Stacks 04H9, the passage from reflection of units to locality of the stalk map, at a point
of the site.**  If the fibre functor of `Φ` on sheaves of *sets* reflects units for
`φ : O₁ ⟶ O₂`, then the fibre of `φ` at `Φ` taken in commutative rings is a local ring
homomorphism.

This is the exact converse of
`AlgebraicGeometry.RingedTopos.reflectsUnitsObj_sheafFiber_of_isLocalHom`, run through the same
two equivalences and at the same independent universes: the site has `C : Type u` with
`Category.{v} C` and the sections live at `w`, all three free.  That is what the statement adds.
The collapsed formulation in
`StacksFrontier/CategoryTheory/Sites/Modules/LocallyRingedSites/StalkCriterion.lean`, where this
implication was already available as part of
`Stacks.Sheaves.LocallyRingedTopos.condition2_iff_condition3_of_locallyRinged`, fixes
`C : Type u` with `Category.{u} C`, and so does not accept the small étale site of a scheme,
whose underlying category is a `Type (u + 1)` with `Category.{u}`.

Composed with
`AlgebraicGeometry.RingedSite.HomGeneral.reflectsUnitsObj_of_isLocallyRinged`, which is the
direction (1) ⇒ (3) of Stacks 04H9 at independent universes, this yields the locality of
`(g^♯)_p` from the hypothesis that `(g, g^♯)` is a morphism of *locally* ringed topoi.  That step
is the one the module documentation of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/AffineCase.lean` records as
missing from step (3) of the proof of [Stacks Project, Tag 04I6], where it says that at
independent universes "only the converse direction ... is available". -/
theorem isLocalHom_sheafFiber_of_reflectsUnitsObj {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (Φ : J.Point.{w}) {O₁ O₂ : Sheaf J CommRingCat.{w}}
    (φ : O₁ ⟶ O₂) (h : ReflectsUnitsObj (Φ.sheafFiber (A := Type w)) φ)
    [LocallySmall.{w} C] [J.HasSheafCompose (forget RingCat.{w})]
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] :
    IsLocalHom ((Φ.sheafFiber (A := CommRingCat.{w})).map φ).hom := by
  refine ⟨fun b hb => ?_⟩
  obtain ⟨a, rfl⟩ := (stalkRingCmp_bijective Φ O₁).2 b
  rw [← stalkRingCmp_naturality] at hb
  refine (isUnit_stalkRingCmp_iff Φ O₁).2 ((isUnit_iff_exists_map_unitsIncl (ofStructureSheaf J O₁)
    (Φ.sheafFiber (A := Type w)) a).2 (h a ?_))
  exact (isUnit_iff_exists_map_unitsIncl (ofStructureSheaf J O₂)
    (Φ.sheafFiber (A := Type w)) _).1 ((isUnit_stalkRingCmp_iff Φ O₂).1 hb)

/-- **Stacks 04H9, reflection of units and locality of the stalk map are equivalent, at
independent universes.**  The fibre functor of `Φ` on sheaves of sets reflects units for `φ`
exactly when the fibre of `φ` at `Φ` taken in commutative rings is a local ring
homomorphism. -/
@[stacks 04H9 "that the two spellings of condition (3) at a single point of the site agree, at \
independent universes: reflection of units by the set-valued fibre functor is locality of the \
fibre ring map.  Neither implication between conditions (1), (2) and (3) is proved here — the \
forward half of this equivalence is proved in this file and the converse \
alongside it; what the statement supplies is the bridge at a site with `C : Type u`, \
`Category.{v} C` and sections at `w` all independent, which the collapsed formulation of \
StalkCriterion.lean cannot state"]
theorem isLocalHom_sheafFiber_iff_reflectsUnitsObj {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (Φ : J.Point.{w}) {O₁ O₂ : Sheaf J CommRingCat.{w}}
    (φ : O₁ ⟶ O₂)
    [LocallySmall.{w} C] [J.HasSheafCompose (forget RingCat.{w})]
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] :
    IsLocalHom ((Φ.sheafFiber (A := CommRingCat.{w})).map φ).hom ↔
      ReflectsUnitsObj (Φ.sheafFiber (A := Type w)) φ :=
  ⟨fun h => reflectsUnitsObj_sheafFiber_of_isLocalHom Φ φ h,
    fun h => isLocalHom_sheafFiber_of_reflectsUnitsObj Φ φ h⟩

end AlgebraicGeometry.RingedTopos

end
