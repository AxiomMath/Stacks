module

public import StacksFrontier.RingTheory.DiscreteValuationRing.HenselianIntegralClosure
public import StacksFrontier.RingTheory.DiscreteValuationRing.IntegralClosureBaseChangeConstruction

/-!
# The per-factor integral closure of a base change

Let `A → B` be an extension of discrete valuation rings with fraction fields `K ⊆ L`, and let
`K₁ / K` be finite.  The reduced base change `(L ⊗[K] K₁) ⧸ nilradical` is a finite product of
fields, and `IsDiscreteValuationRing.isWeakSolution_of_forall_reducedFactorPackages`
(`EppDegreePrimeBridge.lean`) turns a weak solution at **every** factor, all packaged over **one
shared** second extension `K₂`, into a weak solution for `A → B`.  That combiner assumes neither
completeness nor an algebraically closed residue field, which is why it is the all-factor route's
assembly step.

What it demands of the caller is the per-factor data: for each field factor `E`, a discrete
valuation ring `S` with fraction field `E`, sitting over `B` and over the base
`R = integralClosure A K₁`, together with the two squares that identify the two routes into `S`.
This file supplies that data canonically, with `S = integralClosure B E`.

Two things make the choice `S = integralClosure B E` work, and both are hypotheses of the route
rather than of this file:

* **`B` henselian.** Over a general discrete valuation ring `integralClosure B E` is only
  semilocal, so it is a Dedekind domain and not a discrete valuation ring. Henselianness makes it
  local, hence a discrete valuation ring, and `Stacks.DiscreteValuationRing.Ramification` in
  `StacksFrontier.RingTheory.DiscreteValuationRing.HenselianIntegralClosure` already assembles the
  whole instance package in that case. Nothing is re-proved here; the point of this file is the
  *horizontal* map `R → S`, which `Stacks.DiscreteValuationRing.Ramification` does not address.
* **The commuting square.** The combiner's `hsquare` asks that `A → B → S` and `A → R → S` agree.
  That is exactly what makes an element of `K₁` integral over `A` integral over `B` once pushed
  into `E`, so the same square both defines the map `R → S` and discharges the hypothesis.

The construction is the factorwise analogue of
`IsDiscreteValuationRing.integralClosureCompositumMap`, which does the same for the reduced
compositum itself rather than for one of its factors.

## Main definitions

* `Stacks.EppTheorem.integralClosureFactorMap`: the canonical ring map
  `integralClosure A K₁ → integralClosure B E`, pushing an element of `K₁` integral over `A` into
  a factor `E`, where it is integral over `B`.
* `Stacks.EppTheorem.integralClosureBaseMap` and `Stacks.EppTheorem.algebraIntegralClosureBase`:
  the same for an
  abstract base `R` which is merely integral over `A`, which is the form the combiner consumes —
  it does not take the base to be `integralClosure A K₁` on the nose.  Not an instance: `A` does
  not occur in `Algebra R (integralClosure B E)`, so synthesis could never recover it.

## Main results

* `Stacks.EppTheorem.algebraMap_factor_eq`: the square `A → B → E` and `A → K₁ → E` commutes. This
  is
  the one computation everything else rests on.
* `Stacks.EppTheorem.isIntegral_algebraMap_factor`: an element of `K₁` integral over `A` is
  integral over
  `B` once pushed into `E`.
* `Stacks.EppTheorem.algebraMap_integralClosureFactor_eq`: the combiner's `hsquare` for this choice
  of
  `S`, namely that `A → B → S` and `A → R → S` agree.
* `Stacks.EppTheorem.algebraMap_integralClosure_factor_eq_of_tower`: the combiner's `hB`, namely
  that
  `B → L → E` and `B → S → E` agree.
* `Stacks.EppTheorem.isDiscreteValuationRing_integralClosure_factor`,
  `Stacks.EppTheorem.isFractionRing_integralClosure_factor`,
  `Stacks.EppTheorem.isLocalHom_algebraMap_integralClosure_factor`,
  `Stacks.EppTheorem.faithfulSMul_integralClosure_factor`: the instance package on
  `integralClosure B E` over a henselian `B`, restated at the names this file's callers use, by
  delegation to `Stacks.DiscreteValuationRing.Ramification`.  Together they are the components of
  `IsDiscreteValuationRing.IsExtension B (integralClosure B E)`; see the note at the end of the
  file for why that is not stated as a theorem here.

* `Stacks.EppTheorem.isLocalHom_algebraMap_of_tower`: a map out of a discrete valuation ring is
  local as
  soon as the two composites from a common local base agree.  This is the only non-formal
  ingredient, and it is what makes the horizontal map an *extension* rather than merely a ring
  map; the proof is the fundamental identity `π_A = u · π_R ^ e`.
* `Stacks.EppTheorem.isExtension_base_integralClosure_factor`:
  `IsDiscreteValuationRing.IsExtension R (integralClosure B E)`, assembled from the previous two.
  This is the last of the combiner's per-factor hypotheses that does not follow by unfolding.

## What this does *not* do

It does not produce the per-factor weak solutions, and it does not synchronize them — a single
`K₂` serving every conjugate factor at once remains the caller's obligation, and it is where the
remaining mathematics of the all-factor route sits. This file removes the instance and square
plumbing that would otherwise have to be redone at every use, and nothing here distinguishes
a factor: the counterexample to clause (3) of Tag 09ET shows that constraining one
factor and inferring the rest is false.

## References

* [The Stacks Project, Tag 09EM](https://stacks.math.columbia.edu/tag/09EM)
* [The Stacks Project, Tag 09EN](https://stacks.math.columbia.edu/tag/09EN)
-/

@[expose] public section

namespace Stacks.EppTheorem

universe uA uB uK₁ uE uL uR u

/-! ### The commuting square and the horizontal map -/

section Square

/-- Two routes `A → B → E` and `A → C → E` agree when both towers are scalar towers. -/
private theorem algebraMap_tower_square (A B C E : Type*) [CommRing A] [CommRing B] [CommRing C]
    [CommRing E] [Algebra A B] [Algebra A C] [Algebra A E] [Algebra B E] [Algebra C E]
    [IsScalarTower A B E] [IsScalarTower A C E] (a : A) :
    algebraMap B E (algebraMap A B a) = algebraMap C E (algebraMap A C a) := by
  rw [← IsScalarTower.algebraMap_apply A B E, ← IsScalarTower.algebraMap_apply A C E]

variable (A : Type uA) (B : Type uB) (K₁ : Type uK₁) (E : Type uE)
    [CommRing A] [CommRing B] [Field K₁] [Field E]
    [Algebra A B] [Algebra A K₁] [Algebra A E] [Algebra B E] [Algebra K₁ E]
    [IsScalarTower A B E] [IsScalarTower A K₁ E]

/-- **The square of structure maps into a factor commutes.**

Both `A → B → E` and `A → K₁ → E` are the structure map `A → E`. Unlike the corresponding
statement for the reduced compositum
(`IsDiscreteValuationRing.algebraMap_reducedCompositum_eq`), which has to travel through `L` and
`K`, here the two towers are hypotheses and the equality is immediate — which is the reason to
take them as hypotheses rather than to rebuild them from `IsScalarTower K L E` and
`IsScalarTower K K₁ E` at every use. -/
theorem algebraMap_factor_eq (a : A) :
    algebraMap B E (algebraMap A B a) = algebraMap K₁ E (algebraMap A K₁ a) :=
  algebraMap_tower_square A B K₁ E a

/-- The commuting square of `algebraMap_factor_eq` as an equality of ring maps, which is the shape
`IsIntegral.map_of_comp_eq` consumes. -/
theorem algebraMap_factor_comp_eq :
    (algebraMap B E).comp (algebraMap A B) = (algebraMap K₁ E).comp (algebraMap A K₁) :=
  RingHom.ext fun a => algebraMap_factor_eq A B K₁ E a

/-- An element of `K₁` integral over `A` stays integral, now over `B`, once pushed into a
factor. -/
theorem isIntegral_algebraMap_factor (x : integralClosure A K₁) :
    IsIntegral B (algebraMap K₁ E (x : K₁)) :=
  IsIntegral.map_of_comp_eq (algebraMap A B) (algebraMap K₁ E)
    (algebraMap_factor_comp_eq A B K₁ E) x.2

/-- **The horizontal map of the per-factor package.**

The canonical ring map `integralClosure A K₁ → integralClosure B E`: push an element of `K₁`
integral over `A` into the factor `E`, where `isIntegral_algebraMap_factor` says it is integral
over `B`. -/
noncomputable def integralClosureFactorMap :
    integralClosure A K₁ →+* integralClosure B E :=
  RingHom.codRestrict
    ((algebraMap K₁ E).comp (algebraMap (integralClosure A K₁) K₁))
    (integralClosure B E)
    fun x => isIntegral_algebraMap_factor A B K₁ E x

/-- The image of `x` under `integralClosureFactorMap`, viewed in `E`, is the image of `x` under
`algebraMap K₁ E`. -/
@[simp]
theorem coe_integralClosureFactorMap (x : integralClosure A K₁) :
    (integralClosureFactorMap A B K₁ E x : E) = algebraMap K₁ E (x : K₁) := rfl

/-- The algebra structure on the upper integral closure over the lower one, given by
`integralClosureFactorMap`.  This is the `Algebra R (S i)` the combiner asks for. -/
@[instance_reducible]
noncomputable def algebraIntegralClosureFactor :
    Algebra (integralClosure A K₁) (integralClosure B E) :=
  (integralClosureFactorMap A B K₁ E).toAlgebra

end Square

/-! ### The horizontal map for an abstract base -/

section AbstractBase

variable (A B R E : Type*) [CommRing A] [CommRing B] [CommRing R] [Field E]
    [Algebra A B] [Algebra A R] [Algebra A E] [Algebra B E] [Algebra R E]
    [IsScalarTower A B E] [IsScalarTower A R E] [Algebra.IsIntegral A R]

include A in
/-- **An element of an `A`-integral base, pushed into a factor, is integral over `B`.**

`IsDiscreteValuationRing.isWeakSolution_of_forall_reducedFactorPackages` does not take the base
to be `integralClosure A K₁` on the nose; it takes an abstract `R` which is integral over `A` and
has `K₁` as its fraction field. This section is therefore the form the combiner actually consumes,
and `integralClosureFactorMap` above is the special case `R = integralClosure A K₁`, where
`Algebra.IsIntegral A R` is automatic. -/
theorem isIntegral_algebraMap_base (r : R) : IsIntegral B (algebraMap R E r) :=
  ((Algebra.IsIntegral.isIntegral (R := A) r).map (IsScalarTower.toAlgHom A R E)).tower_top

include A in
/-- The horizontal map `R → integralClosure B E` of the per-factor package, for an abstract
`A`-integral base `R`. -/
noncomputable def integralClosureBaseMap : R →+* integralClosure B E :=
  RingHom.codRestrict (algebraMap R E) (integralClosure B E)
    (isIntegral_algebraMap_base A B R E)

include A in
/-- The image of `r` under `integralClosureBaseMap`, viewed in `E`, is `algebraMap R E r`. -/
@[simp]
theorem coe_integralClosureBaseMap (r : R) :
    (integralClosureBaseMap A B R E r : E) = algebraMap R E r := rfl

include A in
/-- The algebra structure on the per-factor integral closure over the abstract base.

This is deliberately **not** an instance: `A` does not occur in `Algebra R (integralClosure B E)`,
so instance synthesis could never recover it. Callers introduce it with `letI`, which is also how
`IsDiscreteValuationRing.isWeakSolution_of_iterated_packages` handles the algebra structures it
has to fix before stating its hypotheses. -/
@[instance_reducible]
noncomputable def algebraIntegralClosureBase : Algebra R (integralClosure B E) :=
  (integralClosureBaseMap A B R E).toAlgebra

include A in
/-- `R` acts on the factor through its integral closure in the same way as directly: the
`IsScalarTower R S E` the combiner asks for. -/
theorem isScalarTower_base_integralClosure_factor :
    letI : Algebra R (integralClosure B E) := algebraIntegralClosureBase A B R E
    IsScalarTower R (integralClosure B E) E :=
  let : Algebra R (integralClosure B E) := algebraIntegralClosureBase A B R E
  IsScalarTower.of_algebraMap_eq fun r => (coe_integralClosureBaseMap A B R E r).symm

include A in
/-- **The combiner's `hsquare`, for an abstract base.**

`A → B → integralClosure B E` and `A → R → integralClosure B E` agree, both being the structure
map `A → integralClosure B E`. -/
theorem algebraMap_integralClosureBase_eq (a : A) :
    letI : Algebra R (integralClosure B E) := algebraIntegralClosureBase A B R E
    algebraMap B (integralClosure B E) (algebraMap A B a) =
      algebraMap R (integralClosure B E) (algebraMap A R a) := by
  let : Algebra R (integralClosure B E) := algebraIntegralClosureBase A B R E
  exact Subtype.ext (algebraMap_tower_square A B R E a)

include A in
/-- The per-factor integral closure is a faithful `R`-algebra, given that `R` acts faithfully on
the factor itself. -/
theorem faithfulSMul_base_integralClosure_factor [FaithfulSMul R E] :
    letI : Algebra R (integralClosure B E) := algebraIntegralClosureBase A B R E
    FaithfulSMul R (integralClosure B E) :=
  let : Algebra R (integralClosure B E) := algebraIntegralClosureBase A B R E
  (faithfulSMul_iff_algebraMap_injective R _).mpr fun _ _ h =>
    FaithfulSMul.algebraMap_injective R E (congrArg Subtype.val h)

end AbstractBase

/-! ### Locality of the horizontal map -/

/-- **A map out of a discrete valuation ring is local as soon as the two composites from a common
local base agree.**

Let `A → R` be an extension of discrete valuation rings, let `S` be a local ring, and suppose
`A → R → S` is the structure map `A → S`, which is local. Then `R → S` is local.

This is the one non-formal ingredient of the per-factor package: the combiner asks each
per-factor ring to be an *extension* of the base `R`, which is faithfulness together with
locality, and locality of `R → S` does not follow from locality of `A → S` by general nonsense —
`R` may be much larger than `A`.

The proof is the fundamental identity. A uniformizer `π_A` of `A` factors in `R` as a unit times
`π_R ^ e` with `e = e(R/A) ≥ 1` (`ramificationIndex_characterization`, last clause). Push that to
`S`: if `π_R` had unit image, the right-hand side would be a unit, so `π_A` would have unit image
in `S`, contradicting locality of `A → S`. Hence `π_R` lands in the maximal ideal, and since it
generates `maximalIdeal R`, so does everything else in it. -/
theorem isLocalHom_algebraMap_of_tower
    (A R S : Type*) [CommRing A] [CommRing R] [CommRing S]
    [IsDomain A] [IsDomain R] [IsDiscreteValuationRing A] [IsDiscreteValuationRing R]
    [IsLocalRing S]
    [Algebra A R] [Algebra A S] [Algebra R S] [IsScalarTower A R S]
    [IsDiscreteValuationRing.IsExtension A R] [IsLocalHom (algebraMap A S)] :
    IsLocalHom (algebraMap R S) := by
  obtain ⟨πA, hπA⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨πR, hπR⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨-, -, -, hfactor⟩ := IsDiscreteValuationRing.ramificationIndex_characterization A R
  obtain ⟨u, hu⟩ := hfactor πA hπA πR hπR
  -- The image of `π_R` in `S` is not a unit.
  have hπRS : ¬ IsUnit (algebraMap R S πR) := by
    intro hunit
    have hAS : IsUnit (algebraMap A S πA) := by
      rw [IsScalarTower.algebraMap_apply A R S, hu, map_mul, map_pow]
      exact (u.isUnit.map (algebraMap R S)).mul (hunit.pow _)
    exact hπA.not_isUnit (IsLocalHom.map_nonunit πA hAS)
  -- Hence everything in `maximalIdeal R` has non-unit image, which is locality.
  constructor
  intro r hr
  by_contra hru
  have hrm : r ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal r).mpr hru
  rw [hπR.maximalIdeal_eq, Ideal.mem_span_singleton] at hrm
  obtain ⟨c, rfl⟩ := hrm
  rw [map_mul] at hr
  exact hπRS (isUnit_of_mul_isUnit_left hr)

/-! ### The combiner's two squares -/

section Compat

variable (A : Type uA) (B : Type uB) (K₁ : Type uK₁) (E : Type uE)
    [CommRing A] [CommRing B] [Field K₁] [Field E]
    [Algebra A B] [Algebra A K₁] [Algebra A E] [Algebra B E] [Algebra K₁ E]
    [IsScalarTower A B E] [IsScalarTower A K₁ E]

attribute [local instance] algebraIntegralClosureFactor

/-- **The combiner's `hsquare`.**

`A → B → integralClosure B E` and `A → integralClosure A K₁ → integralClosure B E` agree. This is
`algebraMap_factor_eq` after both sides are recognised as elements of a subalgebra of `E`. -/
theorem algebraMap_integralClosureFactor_eq (a : A) :
    algebraMap B (integralClosure B E) (algebraMap A B a) =
      algebraMap (integralClosure A K₁) (integralClosure B E)
        (algebraMap A (integralClosure A K₁) a) :=
  Subtype.ext (algebraMap_factor_eq A B K₁ E a)

end Compat

/-! ### The vertical square through `L` -/

section Vertical

variable (B : Type uB) (L : Type uL) (E : Type uE)
    [CommRing B] [Field L] [Field E]
    [Algebra B L] [Algebra B E] [Algebra L E] [IsScalarTower B L E]

/-- **The combiner's `hB`.**

`B → L → E` and `B → integralClosure B E → E` agree: the second route is the first, read through
the subalgebra. -/
theorem algebraMap_integralClosure_factor_eq_of_tower (b : B) :
    algebraMap L E (algebraMap B L b) =
      algebraMap (integralClosure B E) E (algebraMap B (integralClosure B E) b) := by
  exact algebraMap_tower_square B L (integralClosure B E) E b

end Vertical

/-! ### The instance package over a henselian base -/

section Henselian

variable (B : Type uB) (L : Type uL) (E : Type uE)
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [HenselianLocalRing B]
    [Field L] [Field E]
    [Algebra B L] [Algebra B E] [Algebra L E] [IsScalarTower B L E]
    [IsFractionRing B L] [FiniteDimensional L E]

include L in
/-- Over a henselian discrete valuation ring the integral closure in a finite extension of the
fraction field is again a discrete valuation ring.  Delegated to
  `Stacks.DiscreteValuationRing.Ramification`; restated here
because the per-factor callers reach for it with `E` in the position of the factor.

`B`, `L` and `E` sit in independent universes.  They used to share one, to match
`IsDiscreteValuationRing.isWeakSolution_of_forall_reducedFactorPackages`, which was itself
monomorphic; that combiner is now polymorphic in the four universes of
`Stacks.EliminateRamification.EppTheorem`, so the constraint has gone. -/
theorem isDiscreteValuationRing_integralClosure_factor :
    IsDiscreteValuationRing (integralClosure B E) :=
  Stacks.DiscreteValuationRing.Ramification.isDiscreteValuationRing_integralClosure B L E

omit [IsDiscreteValuationRing B] [HenselianLocalRing B] in
include L in
/-- The factor is the fraction field of its integral closure over `B`. -/
theorem isFractionRing_integralClosure_factor :
    IsFractionRing (integralClosure B E) E :=
  Stacks.DiscreteValuationRing.Ramification.isFractionRing_integralClosure B L E

omit [IsDomain B] [IsDiscreteValuationRing B] [FiniteDimensional L E] in
include L in
/-- The structure map into the per-factor integral closure is a local homomorphism. -/
theorem isLocalHom_algebraMap_integralClosure_factor :
    IsLocalHom (algebraMap B (integralClosure B E)) :=
  Stacks.DiscreteValuationRing.Ramification.isLocalHom_algebraMap_integralClosure B L E

omit [IsDomain B] [IsDiscreteValuationRing B] [HenselianLocalRing B] [FiniteDimensional L E] in
include L in
/-- The per-factor integral closure is a faithful `B`-algebra. -/
theorem faithfulSMul_integralClosure_factor :
    FaithfulSMul B (integralClosure B E) :=
  Stacks.DiscreteValuationRing.Ramification.faithfulSMul_integralClosure B L E

/-! The three results above are exactly the components of
`IsDiscreteValuationRing.IsExtension B (integralClosure B E)`, which a caller assembles in one
line once `isDiscreteValuationRing_integralClosure_factor` is in scope as an instance:

```
haveI := isDiscreteValuationRing_integralClosure_factor B L E
exact { toFaithfulSMul := faithfulSMul_integralClosure_factor B L E,
        toIsLocalHom := isLocalHom_algebraMap_integralClosure_factor B L E }
```

It is not stated as a theorem here because `IsExtension` takes the discrete-valuation-ring
structure on the target as an instance argument, so the statement cannot be formed before that
instance is introduced, and introducing it in the statement would fix a particular `L`. -/

end Henselian

/-! ### The base is an extension of the per-factor ring -/

section BaseExtension

variable (A : Type uA) (B : Type uB) (R : Type uR) (L : Type uL) (E : Type uE)
    [CommRing A] [CommRing B] [CommRing R]
    [IsDomain A] [IsDomain B] [IsDomain R]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [IsDiscreteValuationRing R]
    [HenselianLocalRing B] [Field L] [Field E]
    [Algebra A B] [Algebra A R] [Algebra A E] [Algebra B L] [Algebra B E]
    [Algebra L E] [Algebra R E]
    [IsScalarTower A B E] [IsScalarTower A R E] [IsScalarTower B L E]
    [IsFractionRing B L] [FiniteDimensional L E] [FaithfulSMul R E]
    [Algebra.IsIntegral A R]
    [IsDiscreteValuationRing.IsExtension A B] [IsDiscreteValuationRing.IsExtension A R]

include L in
/-- **`R → integralClosure B E` is an extension of discrete valuation rings.**

This is the one hypothesis of
`IsDiscreteValuationRing.isWeakSolution_of_forall_reducedFactorPackages` about the per-factor
rings that is not formal.  Faithfulness is inherited from `R` acting faithfully on the factor;
locality is `isLocalHom_algebraMap_of_tower`, applied along `A → R → integralClosure B E`, whose
two hypotheses are supplied here:

* the `A`-algebra structure on `integralClosure B E` is the one through `B`, and it is local
  because `A → B` and `B → integralClosure B E` both are;
* `A → R → integralClosure B E` is that same structure map, which is exactly the square
  `algebraMap_integralClosureBase_eq`.

So the commuting square that defines the horizontal map is also what makes it local — the two
obligations are the same computation used twice. -/
theorem isExtension_base_integralClosure_factor :
    letI : IsDiscreteValuationRing (integralClosure B E) :=
      isDiscreteValuationRing_integralClosure_factor B L E
    letI : Algebra R (integralClosure B E) := algebraIntegralClosureBase A B R E
    IsDiscreteValuationRing.IsExtension R (integralClosure B E) := by
  let : IsDiscreteValuationRing (integralClosure B E) :=
    isDiscreteValuationRing_integralClosure_factor B L E
  let : Algebra R (integralClosure B E) := algebraIntegralClosureBase A B R E
  let : Algebra A (integralClosure B E) :=
    ((algebraMap B (integralClosure B E)).comp (algebraMap A B)).toAlgebra
  have htAB : IsScalarTower A B (integralClosure B E) := IsScalarTower.of_algebraMap_eq' rfl
  have hlhB : IsLocalHom (algebraMap B (integralClosure B E)) :=
    isLocalHom_algebraMap_integralClosure_factor B L E
  have hlhA : IsLocalHom (algebraMap A (integralClosure B E)) :=
    RingHom.isLocalHom_comp (algebraMap B (integralClosure B E)) (algebraMap A B)
  have htAR : IsScalarTower A R (integralClosure B E) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [IsScalarTower.algebraMap_apply A B (integralClosure B E)]
      exact algebraMap_integralClosureBase_eq A B R E a
  exact { toFaithfulSMul := faithfulSMul_base_integralClosure_factor A B R E
          toIsLocalHom := isLocalHom_algebraMap_of_tower A R (integralClosure B E) }

end BaseExtension

end Stacks.EppTheorem

end
