module

public import Mathlib.RingTheory.Valuation.ValuationRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# The valuative criterion for morphisms of algebraic spaces

Let `B` be a big fppf site containing a scheme `S`. A *valuative square* for a morphism
`f : X ⟶ Y` of presheaves on the big fppf site of `S` is a commutative square whose left
column is the morphism of spectra `Spec K ⟶ Spec R` attached to a valuation ring `R` with
fraction field `K`, whose top edge lands in `X` and whose bottom edge lands in `Y`. A
*lift*, or dotted arrow, is a map `Spec R ⟶ X` making both triangles commute.

The morphism `f` has the *uniqueness* property if every valuative square has at most one
lift, and the *existence* property if every valuative square acquires a lift after
replacing `R` by a valuation ring dominating it in an extension of `K`. Such a replacement
is recorded by a `DominatingExtension`: compatible ring homomorphisms on the valuation
rings and on the fraction fields, with the former local, together with the morphisms of
site objects they induce.

## Main definitions

* `AlgebraicGeometry.siteObject`: a scheme over `S` belonging to `B`, regarded as an
  object of the big fppf site of `S`.
* `AlgebraicGeometry.Space.ValuativeSquare`: the solid valuative square.
* `AlgebraicGeometry.Space.ValuativeSquare.Lift`: a dotted arrow filling in a valuative
  square.
* `AlgebraicGeometry.Space.ValuativeSquare.DominatingExtension`: a valuative square
  obtained from a given one by a field extension and a dominating valuation ring, with
  `AlgebraicGeometry.Space.ValuativeSquare.idDominatingExtension` the identity one.
* `AlgebraicGeometry.Space.ValuativeCriterion.Uniqueness` and
  `AlgebraicGeometry.Space.ValuativeCriterion.Existence`: the two halves of the criterion,
  and `AlgebraicGeometry.Space.ValuativeCriterion` their conjunction.

## Main results

* `AlgebraicGeometry.Space.valuativeCriterionExistence_of_forall_nonempty_lift`: a morphism all
  of whose valuative squares already have a lift satisfies the existence part, with no hypothesis
  on the morphism.

## Implementation notes

The spectra of the valuation ring and of its fraction field, and of any dominating extension,
are required to belong to the chosen big site; their Yoneda objects therefore retain the
generic-point data. Domination is recorded
by the locality of the homomorphism of valuation rings, which is the usual maximal-ideal
condition.

## References

* [Stacks Project, Tag 03IX](https://stacks.math.columbia.edu/tag/03IX)
* [Stacks Project, Tag 0H1V](https://stacks.math.columbia.edu/tag/0H1V)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {B S hS}

/-- A valuation-ring square for a morphism of presheaves on the big fppf site of `S`. -/
public structure ValuativeSquare {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) where
  /-- The valuation ring. -/
  R : Type u
  [commRing : CommRing R]
  [domain : IsDomain R]
  [valuationRing : ValuationRing R]
  /-- The fraction field of the valuation ring. -/
  K : Type u
  [field : Field K]
  [algebra : Algebra R K]
  [isFractionRing : IsFractionRing R K]
  /-- The spectrum of the valuation ring belongs to the big site. -/
  ring_mem : B.Contains (Spec (.of R))
  /-- The spectrum of the fraction field belongs to the big site. -/
  field_mem : B.Contains (Spec (.of K))
  /-- The structure morphism of the valuation ring over the base. -/
  base : Spec (.of R) ⟶ S
  /-- The generic point, that is, the top edge of the square. -/
  generic : yoneda.obj (siteObject B S hS field_mem
    (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ base)) ⟶ X
  /-- The bottom edge of the square. -/
  special : yoneda.obj (siteObject B S hS ring_mem base) ⟶ Y
  /-- The square commutes. -/
  comm : generic ≫ f = yoneda.map (Over.homMk
    (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R K))) :
      B.obj field_mem ⟶ B.obj ring_mem) :
    siteObject B S hS field_mem (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ base) ⟶
    siteObject B S hS ring_mem base) ≫ special

namespace ValuativeSquare

attribute [instance] commRing domain valuationRing field algebra isFractionRing

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}

/-- A dotted arrow in a valuative square, with both triangles commuting. -/
public structure Lift (q : ValuativeSquare f) where
  /-- The dotted arrow itself. -/
  map : yoneda.obj (siteObject B S hS q.ring_mem q.base) ⟶ X
  /-- The upper triangle commutes. -/
  generic_comm : yoneda.map (Over.homMk
    (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K))) :
      B.obj q.field_mem ⟶ B.obj q.ring_mem) :
    siteObject B S hS q.field_mem (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base) ⟶
    siteObject B S hS q.ring_mem q.base) ≫ map = q.generic
  /-- The lower triangle commutes. -/
  special_comm : map ≫ f = q.special

/-- A valuative square obtained from `q` by a field extension and a dominating
valuation ring. The compatibility equations identify the induced solid diagram. -/
public structure DominatingExtension (q : ValuativeSquare f) where
  /-- The new valuative square. -/
  square : ValuativeSquare f
  /-- The homomorphism of valuation rings. -/
  ringMap : q.R →+* square.R
  /-- The homomorphism of fraction fields. -/
  fieldMap : q.K →+* square.K
  /-- The new valuation ring dominates the old one. -/
  isLocalHom : IsLocalHom ringMap
  /-- The two homomorphisms are compatible with the inclusions into the fraction fields. -/
  fraction_comm : (algebraMap square.R square.K).comp ringMap = fieldMap.comp (algebraMap q.R q.K)
  /-- The new structure morphism factors the old one. -/
  base_comm : square.base = Spec.map (CommRingCat.ofHom ringMap) ≫ q.base
  /-- The induced morphism of site objects on fraction fields. -/
  genericOver : siteObject B S hS square.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap square.R square.K)) ≫ square.base) ⟶
    siteObject B S hS q.field_mem (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)
  /-- `genericOver` is the spectrum of the homomorphism of fraction fields. -/
  genericOver_left : (B.inclusion).map genericOver.left = Spec.map (CommRingCat.ofHom fieldMap)
  /-- The induced morphism of site objects on valuation rings. -/
  specialOver : siteObject B S hS square.ring_mem square.base ⟶ siteObject B S hS q.ring_mem q.base
  /-- `specialOver` is the spectrum of the homomorphism of valuation rings. -/
  specialOver_left : (B.inclusion).map specialOver.left = Spec.map (CommRingCat.ofHom ringMap)
  /-- The new generic point is the old one, pulled back. -/
  generic_comm : square.generic = yoneda.map genericOver ≫ q.generic
  /-- The new bottom edge is the old one, pulled back. -/
  special_comm : square.special = yoneda.map specialOver ≫ q.special

/-- The identity dominating extension of a valuative square, through the identity homomorphisms
of the valuation ring and of its fraction field. -/
public noncomputable def idDominatingExtension (q : ValuativeSquare f) :
    q.DominatingExtension where
  square := q
  ringMap := RingHom.id _
  fieldMap := RingHom.id _
  isLocalHom := inferInstance
  fraction_comm := by simp
  base_comm := by simp
  genericOver := 𝟙 _
  genericOver_left := by simp [BigFppfSite.obj, BigFppfSite.inclusion, schemeBelowInclusion]
  specialOver := 𝟙 _
  specialOver_left := by simp [BigFppfSite.obj, BigFppfSite.inclusion, schemeBelowInclusion]
  generic_comm := by simp
  special_comm := by simp

end ValuativeSquare

namespace ValuativeCriterion

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- There is at most one extension of a compatible generic point to any valuation ring. -/
@[stacks 03IX "uniqueness"]
public def Uniqueness (f : X ⟶ Y) : Prop := ∀ q : ValuativeSquare f, Subsingleton q.Lift

/-- A compatible generic point extends after a field extension and passage to a
dominating valuation ring. -/
@[stacks 03IX "existence"]
public def Existence (f : X ⟶ Y) : Prop :=
  ∀ q : ValuativeSquare f, ∃ e : q.DominatingExtension, Nonempty e.square.Lift

end ValuativeCriterion

/-- A morphism every valuative square of which has a lift satisfies the existence part of the
valuative criterion. -/
public theorem valuativeCriterionExistence_of_forall_nonempty_lift
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (h : ∀ q : ValuativeSquare f, Nonempty q.Lift) : ValuativeCriterion.Existence f :=
  fun q => ⟨q.idDominatingExtension, h q⟩

/-- A morphism satisfies both parts of the valuative criterion. -/
@[stacks 03IX "both parts"]
public abbrev ValuativeCriterion
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) : Prop :=
  ValuativeCriterion.Existence f ∧ ValuativeCriterion.Uniqueness f

/-! ### Valuative diagrams

The solid square and the dotted arrow of a valuative diagram for a morphism of algebraic
spaces are the constructions above, specialized to the functors representing the spaces. -/

add_to_stacks 0H1V "solid square" AlgebraicGeometry.Space.ValuativeSquare
add_to_stacks 0H1V "dotted arrow" AlgebraicGeometry.Space.ValuativeSquare.Lift

end AlgebraicGeometry.Space

end
