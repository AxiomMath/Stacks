module

public import StacksFrontier.AlgebraicGeometry.Spaces.LocalRingGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleStalkPointDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedChart

/-!
# Weakly associated points of a reduced algebraic space

The weakly associated points of a reduced algebraic space are exactly its points of
codimension zero, that is the points at which the local ring has Krull dimension zero.

## Main definitions

* `Stacks.unitModuleStalkLargeEquiv`: the stalk at a point of a site of a sheaf of commutative
  rings, viewed as a sheaf of modules over itself, is the stalk of that sheaf of rings.

## Main results

* `isWeaklyAssociatedPrime_maximalIdeal_self_iff_ringKrullDim_eq_zero`: the maximal ideal of a
  reduced local ring is weakly associated to the ring exactly when the ring has Krull dimension
  zero.
* `AlgebraicGeometry.Space.weaklyAssociatedPointsOfSpace_eq_setOf_localRingDimension_eq_zero`:
  **Stacks 0EN1**, the weakly associated points of a reduced algebraic space are its
  codimension-zero points.

## Implementation notes

Reducedness of the algebraic space is `AlgebraicGeometry.Space.HasEtaleLocalProperty` at
reducedness of schemes, which is Stacks 03E6, and the codimension-zero condition is the
vanishing of `AlgebraicGeometry.Space.localRingDimension` of Stacks 04NA.

The argument is pointwise at a geometric point and passes through no étale scheme chart. Weak
association is read on the stalks at the point of the small étale site by
`AlgebraicGeometry.Space.isWeaklyAssociatedPoint_iff_moduleStalkLarge`, so no extension of
scalars to the étale local ring is involved; there the module is the structure sheaf itself,
whose stalk is the stalk of the sheaf of rings by `Stacks.unitModuleStalkLargeEquiv`. The
remaining content is ring-theoretic: over a reduced ring the weakly associated primes are the
minimal primes, which is Stacks 0EMA, so over a reduced local ring the maximal ideal is weakly
associated exactly when it is the only prime.

Reducedness of the étale local ring at a geometric point comes from reducedness of the space
through its local rings, by Stacks 0BGS and Stacks 0E01, and is transported to the stalk at the
point of the site along `AlgebraicGeometry.Space.pointStalkRingEquiv`, which also matches the
two Krull dimensions.

`Stacks.unitModuleStalkLargeEquiv` is built from the germ maps of the sheaf of rings through
`Stacks.moduleStalkLargeDescOfCompatibleFamily`; it is bijective because germs are jointly
surjective on both sides and a germ vanishes exactly when its section dies on a refinement.

## References

* [Stacks Project, Tag 0EN1](https://stacks.math.columbia.edu/tag/0EN1)
* [Stacks Project, Tag 0EMA](https://stacks.math.columbia.edu/tag/0EMA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w t

/-! ### The stalk of a sheaf of rings as a module over itself -/

namespace Stacks

variable {C : Type t} [Category.{v} C] [LocallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (p : J.Point.{w}) (O : Sheaf J CommRingCat.{w})

/-- The germ maps of a sheaf of commutative rings, read as a family of additive maps out of
the sections of that sheaf viewed as a sheaf of modules over itself. -/
noncomputable def unitStalkFamily (U : C) (x : p.fiber.obj U) :
    (SheafOfModules.unit (commRingSheafToRingSheaf O)).val.obj (op U) →+
      ((p.presheafFiber (A := CommRingCat.{w})).obj O.obj) :=
  (p.toPresheafFiber U x O.obj).hom.toAddMonoidHom

omit [LocallySmall.{w} C] in
/-- The germ maps of a sheaf of commutative rings are compatible with restriction. -/
theorem unitStalkFamily_w ⦃U V : C⦄ (f : U ⟶ V) (x : p.fiber.obj U)
    (s : (SheafOfModules.unit (commRingSheafToRingSheaf O)).val.obj (op V)) :
    unitStalkFamily p O U x
        ((SheafOfModules.unit (commRingSheafToRingSheaf O)).val.map f.op s) =
      unitStalkFamily p O V (p.fiber.map f x) s :=
  p.toPresheafFiber_w_apply f x O.obj s

/-- The additive map from the stalk of a sheaf of commutative rings viewed as a module over
itself to the stalk of that sheaf of rings, descended from the germ maps. -/
noncomputable def unitModuleStalkLargeHom :
    moduleStalkLarge.{w} p O (SheafOfModules.unit (commRingSheafToRingSheaf O)) →+
      ((p.presheafFiber (A := CommRingCat.{w})).obj O.obj) :=
  moduleStalkLargeDescOfCompatibleFamily p O _ (unitStalkFamily p O) (unitStalkFamily_w p O)

/-- The descended map sends the germ of a regular function to the germ of the same function in
the stalk of the sheaf of rings. -/
theorem unitModuleStalkLargeHom_germ (U : C) (x : p.fiber.obj U)
    (s : (SheafOfModules.unit (commRingSheafToRingSheaf O)).val.obj (op U)) :
    unitModuleStalkLargeHom p O
        (moduleStalkLargeGerm p O (SheafOfModules.unit (commRingSheafToRingSheaf O)) U x s) =
      p.toPresheafFiber U x O.obj s :=
  moduleStalkLargeDescOfCompatibleFamily_germ p O _ (unitStalkFamily p O)
    (unitStalkFamily_w p O) U x s

/-- The descended map is linear over the stalk of the sheaf of rings. -/
theorem unitModuleStalkLargeHom_smul
    (r : ((p.presheafFiber (A := CommRingCat.{w})).obj O.obj))
    (z : moduleStalkLarge.{w} p O (SheafOfModules.unit (commRingSheafToRingSheaf O))) :
    unitModuleStalkLargeHom p O (r • z) = r • unitModuleStalkLargeHom p O z :=
  moduleStalkLargeDescOfCompatibleFamily_smul p O _ (unitStalkFamily p O)
    (unitStalkFamily_w p O) (RingHom.id _)
    (fun U x a s => map_mul (p.toPresheafFiber U x O.obj).hom a s) r z

/-- The descended map is injective: a germ of a regular function which vanishes in the stalk of
the sheaf of rings already vanishes on a refinement of its neighbourhood. -/
theorem unitModuleStalkLargeHom_injective :
    Function.Injective (unitModuleStalkLargeHom p O) := by
  refine (injective_iff_map_eq_zero _).mpr fun z hz => ?_
  obtain ⟨U, x, s, rfl⟩ := moduleStalkLargeGerm_jointly_surjective p O
    (SheafOfModules.unit (commRingSheafToRingSheaf O)) z
  rw [unitModuleStalkLargeHom_germ] at hz
  have hz' : p.toPresheafFiber U x O.obj s = p.toPresheafFiber U x O.obj 0 := by
    rw [hz, map_zero]
  obtain ⟨V, f, y, hy, hfs⟩ := (p.toPresheafFiber_eq_iff' (P := O.obj) U x s 0).mp hz'
  have hgerm := moduleStalkLargeGerm_w p O
    (SheafOfModules.unit (commRingSheafToRingSheaf O)) f y s
  rw [hy] at hgerm
  have h0 : (SheafOfModules.unit (commRingSheafToRingSheaf O)).val.map f.op s = 0 :=
    hfs.trans (map_zero (ConcreteCategory.hom (O.obj.map f.op)))
  rw [← hgerm, h0]
  exact map_zero _

/-- The descended map is surjective: every germ in the stalk of the sheaf of rings is the germ
of a regular function. -/
theorem unitModuleStalkLargeHom_surjective :
    Function.Surjective (unitModuleStalkLargeHom p O) := by
  intro r
  obtain ⟨U, x, a, rfl⟩ := p.toPresheafFiber_jointly_surjective (P := O.obj) r
  exact ⟨moduleStalkLargeGerm p O (SheafOfModules.unit (commRingSheafToRingSheaf O)) U x a,
    unitModuleStalkLargeHom_germ p O U x a⟩

/-- The descent of the germ maps, as a linear map over the stalk of the sheaf of rings. -/
noncomputable def unitModuleStalkLargeLinearMap :
    (moduleStalkLarge.{w} p O (SheafOfModules.unit (commRingSheafToRingSheaf O)) : Type w) →ₗ[
        ((p.presheafFiber (A := CommRingCat.{w})).obj O.obj)]
      ((p.presheafFiber (A := CommRingCat.{w})).obj O.obj) where
  toFun := unitModuleStalkLargeHom p O
  map_add' := (unitModuleStalkLargeHom p O).map_add
  map_smul' := unitModuleStalkLargeHom_smul p O

/-- **The stalk of a sheaf of commutative rings as a module over itself is the stalk of that
sheaf of rings.** For a point `p` of a site and a sheaf of commutative rings `O`, the stalk at
`p` of `O` viewed as a sheaf of modules over itself is `O_p` as a module over itself. -/
noncomputable def unitModuleStalkLargeEquiv :
    (moduleStalkLarge.{w} p O (SheafOfModules.unit (commRingSheafToRingSheaf O)) : Type w) ≃ₗ[
        ((p.presheafFiber (A := CommRingCat.{w})).obj O.obj)]
      ((p.presheafFiber (A := CommRingCat.{w})).obj O.obj) :=
  LinearEquiv.ofBijective (unitModuleStalkLargeLinearMap p O)
    ⟨unitModuleStalkLargeHom_injective p O, unitModuleStalkLargeHom_surjective p O⟩

end Stacks

/-! ### Weak association of the maximal ideal of a reduced local ring -/

/-- The maximal ideal of a reduced local ring is weakly associated to the ring itself exactly
when the ring has Krull dimension zero: by Stacks 0EMA the weakly associated primes of a
reduced ring are its minimal primes, and the maximal ideal of a local ring is minimal among the
primes exactly when it is the only prime. -/
theorem isWeaklyAssociatedPrime_maximalIdeal_self_iff_ringKrullDim_eq_zero
    (R : Type*) [CommRing R] [IsLocalRing R] [IsReduced R] :
    IsWeaklyAssociatedPrime R R (IsLocalRing.maximalIdeal R) ↔ ringKrullDim R = 0 := by
  rw [show IsWeaklyAssociatedPrime R R (IsLocalRing.maximalIdeal R) ↔
    IsLocalRing.maximalIdeal R ∈ weaklyAssociatedPrimes R R from Iff.rfl,
    weakAss_eq_minimalPrimes0EMA]
  constructor
  · intro hmin
    refine ringKrullDimZero_iff_ringKrullDim_eq_zero.mp (Ring.KrullDimLE.mk₀ fun I hI => ?_)
    have hle := IsLocalRing.le_maximalIdeal hI.ne_top
    have heq : IsLocalRing.maximalIdeal R = I := (hmin.2 ⟨hI, bot_le⟩ hle).antisymm hle
    rw [← heq]
    infer_instance
  · intro hdim
    have : Ring.KrullDimLE 0 R := ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hdim
    refine ⟨⟨inferInstance, bot_le⟩, ?_⟩
    rintro I ⟨hI, -⟩ -
    have : I.IsPrime := hI
    exact (Ring.KrullDimLE.eq_maximalIdeal_of_isPrime I).symm.le

/-! ### Weakly associated points of a reduced algebraic space -/

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **Stacks 0EN1.** The weakly associated points of a reduced algebraic space are exactly its
points of codimension zero, that is the points whose local ring has Krull dimension zero. -/
@[stacks 0EN1]
theorem weaklyAssociatedPointsOfSpace_eq_setOf_localRingDimension_eq_zero
    (hred : HasEtaleLocalProperty B S hS X.1 (fun Y : Scheme.{u} => IsReduced Y)) :
    weaklyAssociatedPointsOfSpace B S hS X =
      {x : points B S hS X.1 | localRingDimension B S hS x = 0} := by
  ext x
  refine (isWeaklyAssociatedPoint_iff_moduleStalkLarge B S hS X _ x).trans
    (Iff.trans (exists_congr fun xbar => and_congr_right fun _ => ?_)
      ((localRingDimension_eq_tfae X.2 x 0).out 2 1))
  have hloc : IsLocalRing (etaleLocalRing B S hS X.1 xbar) :=
    isLocalRing_etaleLocalRing B S hS X.1 X.2 xbar
  have hred' : _root_.IsReduced (etaleLocalRing B S hS X.1 xbar) :=
    (isReduced_etaleLocalRing_iff_hasLocalRingPropertyAtPoint X.2 xbar).mpr
      ((isReduced_iff_forall_localRing_isReduced B S hS X.1 X.2).mp hred xbar.image)
  have hlocFib : IsLocalRing
      (((etaleSitePoint B S hS X.1 xbar X.2).presheafFiber (A := CommRingCat.{u})).obj
        (smallEtaleRingedTopos B S hS X).O.obj) :=
    (pointStalkRingEquiv B S hS X xbar).symm.isLocalRing
  have hredFib : _root_.IsReduced
      (((etaleSitePoint B S hS X.1 xbar X.2).presheafFiber (A := CommRingCat.{u})).obj
        (smallEtaleRingedTopos B S hS X).O.obj) :=
    isReduced_of_injective (pointStalkRingEquiv B S hS X xbar)
      (pointStalkRingEquiv B S hS X xbar).injective
  refine Iff.trans (isWeaklyAssociatedPrime_maximalIdeal_congr_semilinearEquiv (RingEquiv.refl _)
    (Stacks.unitModuleStalkLargeEquiv (etaleSitePoint B S hS X.1 xbar X.2)
        (smallEtaleRingedTopos B S hS X).O).toAddEquiv
    (fun r z => (Stacks.unitModuleStalkLargeEquiv (etaleSitePoint B S hS X.1 xbar X.2)
        (smallEtaleRingedTopos B S hS X).O).map_smul r z)) ?_
  rw [isWeaklyAssociatedPrime_maximalIdeal_self_iff_ringKrullDim_eq_zero,
    ringKrullDim_eq_of_ringEquiv (pointStalkRingEquiv B S hS X xbar)]
  simp

end AlgebraicGeometry.Space

end
