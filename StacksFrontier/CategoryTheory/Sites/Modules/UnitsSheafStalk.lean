module

public import StacksFrontier.CategoryTheory.Sites.Modules.UnitsSheafInverseImage
public import StacksFrontier.CategoryTheory.Sites.Point.ToposPoints

/-!
# The units subsheaf under a left-exact functor to sets, and at a point

Let `X` be a ringed topos. Its units subsheaf `O_X^*` admits a description by a finite limit:
paired with the inverse, it is the fibre product of the multiplication of the structure sheaf
over the unit section. That description is
`AlgebraicGeometry.RingedTopos.unitsPair_isPullback`; it is what makes the units subsheaf
survive any left-exact operation, since a left-exact functor carries a cartesian square to a
cartesian square.

This file applies the description to a functor `P` from the topos to sets which preserves
finite limits. The image `P(O_X)` of the underlying sheaf of sets of the structure sheaf
carries the transported ring structure `CategoryTheory.Sheaf.ringObjRing`, and the conclusion
is that `P` carries the units subsheaf to the unit group of that ring, compatibly with the
inclusion into the structure sheaf. Taking `P` to be the stalk functor of a point of the site
gives the identification `(O_X^*)_p = (O_{X,p})^*`.

## Main definitions

* `AlgebraicGeometry.RingedTopos.unitsInvPair`: a section of the units subsheaf, paired with
  its inverse in the order `(u⁻¹, u)`.
* `AlgebraicGeometry.RingedTopos.unitsObjToUnits`: the image under `P` of a section of the
  units subsheaf, viewed as a unit of the transported ring.
* `AlgebraicGeometry.RingedTopos.unitsObjEquiv`: the resulting bijection
  `P(O_X^*) ≃ (P(O_X))^*`.
* `AlgebraicGeometry.RingedTopos.stalkUnitsEquiv`: the bijection `(O_X^*)_p ≃ (O_{X,p})^*` at a
  point `p` of the topos.

## Main results

* `AlgebraicGeometry.RingedTopos.isPullback_map_unitsPair`: the cartesian square of the units
  subsheaf stays cartesian after applying `P`.
* `AlgebraicGeometry.RingedTopos.bijective_unitsObjToUnits`: the comparison map is a bijection.
* `AlgebraicGeometry.RingedTopos.unitsObjEquiv_apply_val` and
  `AlgebraicGeometry.RingedTopos.stalkUnitsEquiv_apply_val`: the bijections are compatible with
  the inclusion of the units subsheaf into the structure sheaf.
* `AlgebraicGeometry.RingedTopos.isUnit_iff_exists_map_unitsIncl` and
  `AlgebraicGeometry.RingedTopos.isUnit_stalk_iff`: a section of the transported structure
  sheaf, in particular an element of a stalk, is invertible exactly when it lifts through the
  transported units subsheaf.

## Implementation notes

No tag is attached to anything here. The content of Stacks 04KR is the sheaf-level statement
`f⁻¹(O^*) = (f⁻¹O)^*` for a morphism of topoi, which is already registered on
`AlgebraicGeometry.inverseImage_units_iso`; the results below are the same argument run for an
arbitrary left-exact functor to sets, which the source does not state separately. The stalk
identification `(O^*)_p = (O_p)^*` is used inside the proof of Stacks 04H9 and is not itself a
tag.

Commutativity of the structure sheaf is never needed: a unit is turned into a unit of the
transported ring using *both* `u · u⁻¹ = 1` and `u⁻¹ · u = 1`, the second of which is supplied
by `unitsInvPair_comp_ringMulHom`. Conversely a pair `(a, b)` with `a · b = 1` in the
transported ring is enough to produce a section of `P(O_X^*)`, because the cartesian square
describes the units subsheaf by that single equation.

The ring structure on `P(O_X)` is `CategoryTheory.Sheaf.ringObjRing`, which is a `def` rather
than an instance; it is made a local instance here so that the statements can speak of
`(P(O_X))^*` directly.

## References

* [Stacks Project, Tag 04KR](https://stacks.math.columbia.edu/tag/04KR)
* [Stacks Project, Tag 04H9](https://stacks.math.columbia.edu/tag/04H9)
* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] CategoryTheory.Sheaf.ringObjRing

namespace AlgebraicGeometry.RingedTopos

universe t w v u

/-- Binary products of sheaves of sets, created by the inclusion into presheaves. Stated
directly: instance search for them otherwise wanders into limits of presheaves of rings and
times out. -/
noncomputable local instance (priority := high) hasBinaryProduct_sheaf_type'
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (A B : Sheaf J (Type w)) :
    HasBinaryProduct A B :=
  haveI : HasLimitsOfShape (Discrete WalkingPair) (Sheaf J (Type w)) :=
    hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (sheafToPresheaf J (Type w))
  HasLimitsOfShape.has_limit _

variable (X : RingedTopos.{v, u, w}) [X.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-! ### The unit and its inverse in the other order -/

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The inverse of a section of the units subsheaf, multiplied by the section itself, is
one. -/
theorem unitsInv_mul_unitsIncl (Z : X.Cᵒᵖ)
    (s : (Sheaf.sectionsFunctor X.J Z).obj (units X)) :
    (Sheaf.sectionsFunctor X.J Z).map (unitsIncl X)
          ((Sheaf.sectionsFunctor X.J Z).map (unitsInv X) s) *
        (Sheaf.sectionsFunctor X.J Z).map (unitsIncl X) s = 1 :=
  Units.inv_mul _

/-- A section of the units subsheaf, paired with its inverse in the order `(u⁻¹, u)`. -/
noncomputable def unitsInvPair :
    units X ⟶ Sheaf.ringSheaf (ringStructureSheaf X) ⨯ Sheaf.ringSheaf (ringStructureSheaf X) :=
  prod.lift (unitsInv X ≫ unitsIncl X) (unitsIncl X)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The square of the units subsheaf over multiplication and the unit section commutes also
when the unit and its inverse are taken in the other order. -/
theorem unitsInvPair_comp_ringMulHom :
    unitsInvPair X ≫ Sheaf.ringMulHom (ringStructureSheaf X) =
      terminal.from (units X) ≫ Sheaf.ringOneHom (ringStructureSheaf X) := by
  refine Sheaf.hom_ext_sections (fun Z s ↦ ?_)
  rw [Functor.map_comp, types_comp_apply, Functor.map_comp, types_comp_apply, unitsInvPair,
    Functor.map_lift_apply, Sheaf.sectionsFunctor_map_ringMulHom,
    Sheaf.sectionsFunctor_map_ringOneHom, Functor.map_comp, types_comp_apply]
  exact unitsInv_mul_unitsIncl X Z s

/-! ### Transport along a left-exact functor to sets -/

section Transport

variable (P : Sheaf X.J (Type w) ⥤ Type t) [PreservesFiniteLimits P]

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The cartesian square of the units subsheaf survives a left-exact functor to sets.** This
is the whole content of the finite-limit description of the units subsheaf. -/
theorem isPullback_map_unitsPair :
    IsPullback (P.map (unitsPair X)) (P.map (terminal.from (units X)))
      (P.map (Sheaf.ringMulHom (ringStructureSheaf X)))
      (P.map (Sheaf.ringOneHom (ringStructureSheaf X))) :=
  (unitsPair_isPullback X).map P

/-- The section of the structure sheaf underlying the image of a section of the units
subsheaf. -/
noncomputable def unitsObjVal (u : P.obj (units X)) :
    P.obj (Sheaf.ringSheaf (ringStructureSheaf X)) :=
  P.map (unitsIncl X) u

/-- The inverse section underlying the image of a section of the units subsheaf. -/
noncomputable def unitsObjInv (u : P.obj (units X)) :
    P.obj (Sheaf.ringSheaf (ringStructureSheaf X)) :=
  P.map (unitsInv X ≫ unitsIncl X) u

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
private theorem map_unitsPair_apply (u : P.obj (units X)) :
    P.map (unitsPair X) u = Functor.prodObjMk (unitsObjVal X P u) (unitsObjInv X P u) := by
  rw [unitsPair, Functor.map_lift_apply]
  rfl

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
private theorem map_unitsInvPair_apply (u : P.obj (units X)) :
    P.map (unitsInvPair X) u = Functor.prodObjMk (unitsObjInv X P u) (unitsObjVal X P u) := by
  rw [unitsInvPair, Functor.map_lift_apply]
  rfl

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The image of a section of the units subsheaf is invertible in the transported ring. -/
theorem unitsObjVal_mul_unitsObjInv (u : P.obj (units X)) :
    unitsObjVal X P u * unitsObjInv X P u = 1 := by
  change Sheaf.ringMulObj (ringStructureSheaf X) P (unitsObjVal X P u) (unitsObjInv X P u) =
    Sheaf.ringOneObj (ringStructureSheaf X) P
  rw [Sheaf.ringMulObj, ← map_unitsPair_apply, ← Functor.map_comp_apply,
    unitsPair_comp_ringMulHom, Functor.map_comp_apply, Functor.map_terminalFrom_apply,
    Sheaf.ringOneObj]

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The inverse section is a two-sided inverse in the transported ring. -/
theorem unitsObjInv_mul_unitsObjVal (u : P.obj (units X)) :
    unitsObjInv X P u * unitsObjVal X P u = 1 := by
  change Sheaf.ringMulObj (ringStructureSheaf X) P (unitsObjInv X P u) (unitsObjVal X P u) =
    Sheaf.ringOneObj (ringStructureSheaf X) P
  rw [Sheaf.ringMulObj, ← map_unitsInvPair_apply, ← Functor.map_comp_apply,
    unitsInvPair_comp_ringMulHom, Functor.map_comp_apply, Functor.map_terminalFrom_apply,
    Sheaf.ringOneObj]

/-- The image under a left-exact functor to sets of a section of the units subsheaf, as a unit
of the transported ring. -/
noncomputable def unitsObjToUnits (u : P.obj (units X)) :
    (P.obj (Sheaf.ringSheaf (ringStructureSheaf X)))ˣ where
  val := unitsObjVal X P u
  inv := unitsObjInv X P u
  val_inv := unitsObjVal_mul_unitsObjInv X P u
  inv_val := unitsObjInv_mul_unitsObjVal X P u

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The underlying element of `unitsObjToUnits X P u` is the image of `u` under `P` applied to the
inclusion of the units subsheaf. -/
@[simp]
theorem unitsObjToUnits_val (u : P.obj (units X)) :
    (unitsObjToUnits X P u : P.obj (Sheaf.ringSheaf (ringStructureSheaf X))) =
      P.map (unitsIncl X) u :=
  rfl

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The units subsheaf is carried to the unit group of the transported ring.** A section of
the image of the units subsheaf is determined by, and determines, a unit of the transported
ring: the cartesian square describing the units subsheaf is preserved, and over sets a
cartesian square says exactly that. -/
theorem bijective_unitsObjToUnits : Function.Bijective (unitsObjToUnits X P) := by
  constructor
  · intro u u' h
    refine Types.ext_of_isPullback (isPullback_map_unitsPair X P) ?_ (Subsingleton.elim _ _)
    rw [map_unitsPair_apply, map_unitsPair_apply]
    exact congrArg₂ Functor.prodObjMk (congrArg Units.val h) (congrArg Units.inv h)
  · intro v
    obtain ⟨u, hu, -⟩ :=
      Types.exists_of_isPullback (isPullback_map_unitsPair X P)
        (Functor.prodObjMk (v : P.obj (Sheaf.ringSheaf (ringStructureSheaf X)))
          (↑v⁻¹ : P.obj (Sheaf.ringSheaf (ringStructureSheaf X))))
        default
        (by
          change Sheaf.ringMulObj (ringStructureSheaf X) P _ _ =
            Sheaf.ringOneObj (ringStructureSheaf X) P
          exact v.val_inv)
    refine ⟨u, Units.ext ?_⟩
    rw [unitsObjToUnits_val, ← unitsObjVal, ← Functor.map_fst_prodObjMk (unitsObjVal X P u)
      (unitsObjInv X P u), ← map_unitsPair_apply, hu, Functor.map_fst_prodObjMk]

/-- **The image of the units subsheaf under a left-exact functor to sets is the unit group of
the transported ring.** -/
noncomputable def unitsObjEquiv :
    P.obj (units X) ≃ (P.obj (Sheaf.ringSheaf (ringStructureSheaf X)))ˣ :=
  Equiv.ofBijective _ (bijective_unitsObjToUnits X P)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The bijection `unitsObjEquiv X P` sends `u` to `unitsObjToUnits X P u`. -/
@[simp]
theorem unitsObjEquiv_apply (u : P.obj (units X)) :
    unitsObjEquiv X P u = unitsObjToUnits X P u :=
  rfl

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The bijection is compatible with the inclusion of the units subsheaf.** -/
theorem unitsObjEquiv_apply_val (u : P.obj (units X)) :
    (unitsObjEquiv X P u : P.obj (Sheaf.ringSheaf (ringStructureSheaf X))) =
      P.map (unitsIncl X) u :=
  rfl

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The sections of the transported structure sheaf which lift through the transported units
subsheaf are exactly the units.** This is the transported form of
`AlgebraicGeometry.RingedSite.isUnit_iff_exists_unitsSheaf`; for a stalk functor it is the
statement that an element of a stalk of the structure sheaf is invertible exactly when it comes
from the corresponding stalk of the units subsheaf. -/
theorem isUnit_iff_exists_map_unitsIncl
    (a : P.obj (Sheaf.ringSheaf (ringStructureSheaf X))) :
    IsUnit a ↔ ∃ u : P.obj (units X), P.map (unitsIncl X) u = a := by
  constructor
  · rintro ⟨v, rfl⟩
    obtain ⟨u, hu⟩ := (bijective_unitsObjToUnits X P).2 v
    exact ⟨u, congrArg Units.val hu⟩
  · rintro ⟨u, rfl⟩
    exact ⟨unitsObjToUnits X P u, rfl⟩

end Transport

/-! ### The stalk of the units subsheaf -/

/-- The stalk of the structure sheaf at a point of the topos, carrying the ring structure
transported along the stalk functor. This is `PointOfTopos.stalk` of the underlying sheaf of
sets of the structure sheaf, spelled through `inverseImage` so that the transported ring
structure is found by instance search. -/
noncomputable abbrev stalkRingObj (p : PointOfTopos.{w, v, u} X.J) : Type w :=
  p.inverseImage.obj (Sheaf.ringSheaf (ringStructureSheaf X))

/-- **The stalk of the units subsheaf is the unit group of the stalk ring.** The stalk functor
of a point of a topos is left exact, so it carries the cartesian square describing the units
subsheaf to the cartesian square describing the units of the stalk ring. -/
noncomputable def stalkUnitsEquiv (p : PointOfTopos.{w, v, u} X.J) :
    letI := p.preservesFiniteLimits
    p.stalk (units X) ≃ (stalkRingObj X p)ˣ :=
  letI := p.preservesFiniteLimits
  unitsObjEquiv X p.inverseImage

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The identification of stalks is compatible with the inclusion of the units subsheaf.** -/
theorem stalkUnitsEquiv_apply_val (p : PointOfTopos.{w, v, u} X.J)
    (u : p.stalk (units X)) :
    letI := p.preservesFiniteLimits
    (stalkUnitsEquiv X p u : stalkRingObj X p) = p.inverseImage.map (unitsIncl X) u :=
  rfl

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **An element of a stalk of the structure sheaf is invertible exactly when it comes from the
stalk of the units subsheaf.** -/
theorem isUnit_stalk_iff (p : PointOfTopos.{w, v, u} X.J) (a : stalkRingObj X p) :
    letI := p.preservesFiniteLimits
    IsUnit a ↔ ∃ u : p.stalk (units X), p.inverseImage.map (unitsIncl X) u = a :=
  let := p.preservesFiniteLimits
  isUnit_iff_exists_map_unitsIncl X p.inverseImage a

end AlgebraicGeometry.RingedTopos

end
