module

public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksFrontier.RingTheory.DiscreteValuationRing.Solution

/-!
# The canonical base-change package of a finite extension of fraction fields

Let `A → B` be an extension of discrete valuation rings with fraction fields `K ⊆ L`, and let
`K₁ / K` be a finite extension.  Stacks 09EM attaches to this data the *reduced compositum*
`L₁ = (L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)` together with the two integral closures
`A₁ = integralClosure A K₁` and `B₁ = integralClosure B L₁`; Stacks 09EN then asks of this
package whether it is a weak solution, a solution, or a separable solution.

The package itself is recorded by the structure
`IsDiscreteValuationRing.IntegralClosureBaseChange`, which deliberately does *not* fix carrier
types: it asks only for rings `L₁`, `A₁`, `B₁` with the right algebra maps, the right scalar
towers, the two `IsIntegralClosure` properties, an identification of `L₁` with the reduction of
`L ⊗[K] K₁`, and the commuting square `A₁ → B₁ → L₁ = A₁ → K₁ → L₁`.  That flexibility is what
lets the elimination-of-ramification proofs feed it presentations of their own choosing.

What was missing is the *canonical* instance of the structure: the one whose three carriers are
literally the reduction of the tensor product and the two integral closures.  This file builds it,
as `IsDiscreteValuationRing.canonicalBaseChange`, so that statements of the form
`∃ K₁, ∃ D : IntegralClosureBaseChange A B K L K₁, ...` can be discharged by exhibiting only the
field `K₁`.

## Main definitions

* `IsDiscreteValuationRing.reducedCompositum`: the reduced compositum
  `(L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)`, in universe `max uL uK₁`.
* `IsDiscreteValuationRing.integralClosureCompositumMap`: the canonical ring map
  `integralClosure A K₁ → integralClosure B (reducedCompositum K L K₁)`, obtained by pushing an
  element of `K₁` integral over `A` into `L₁`, where it is integral over `B`.
* `IsDiscreteValuationRing.canonicalBaseChange`: the canonical base-change package, with
  `L₁ = reducedCompositum K L K₁`, `A₁ = integralClosure A K₁` and
  `B₁ = integralClosure B (reducedCompositum K L K₁)`.

## Main results

* `IsDiscreteValuationRing.algebraMap_reducedCompositum_eq`: the square of structure maps
  `A → B → L₁` and `A → K₁ → L₁` commutes.  This is the one computation the construction needs:
  it is what makes an element of `K₁` integral over `A` integral over `B` after it is pushed into
  `L₁`, and it is also the `ringSquare` field of the package.
* `IsDiscreteValuationRing.canonicalBaseChange_L₁`, `canonicalBaseChange_A₁`,
  `canonicalBaseChange_B₁`: the three carriers are the expected ones.
* `IsDiscreteValuationRing.nonempty_integralClosureBaseChange`: a finite extension `K₁ / K` needs
  no further data to carry a base-change package.  This is the form in which the constructor is
  used to discharge existential statements over `K₁`.

## Implementation notes

The universe instantiation is
`IntegralClosureBaseChange.{uA, uB, uK, uL, uK₁, max uL uK₁, uK₁, max uL uK₁}`, matching the
convention already used by the conclusions of
`exists_isSeparableSolution_of_exists_isSolution` and
`exists_finite_extension_isWeakSolution`, so that the constructor can be used to discharge their
existential statements.

Every one of the twenty-two instance fields except three is found by instance search once the
carriers are fixed; Mathlib supplies the `S`-algebra structure on `L ⊗[K] K₁` for every ring `S`
acting on `L`, and `Ideal.Quotient.algebra`, `Ideal.Quotient.isScalarTower`,
`Subalgebra.algebra'` and `integralClosure.isIntegralClosure` then propagate everything to the
quotient and to the two subalgebras.  The three exceptions, all switched on as `local instance`s
here so that nothing leaks to consumers, are

* `Algebra.TensorProduct.rightAlgebra`, the `K₁`-algebra structure on `L ⊗[K] K₁`, which is not a
  global instance in Mathlib because it would make the action of `L` on `L ⊗[K] L` ambiguous;
* `isScalarTower_tensor_of_base`, the tower `A → B → L ⊗[K] K₁`, which is what lets
  `Subalgebra.algebra'` produce the field `algebraAB₁`;
* `algebraIntegralClosure`, the `A₁`-algebra structure on `B₁`, which is the only field carrying
  genuine mathematical content and is built from `integralClosureCompositumMap`.

## References

* [Stacks Project, Tag 09EM](https://stacks.math.columbia.edu/tag/09EM)
* [Stacks Project, Tag 09EN](https://stacks.math.columbia.edu/tag/09EN)
-/

@[expose] public section

open scoped TensorProduct

universe uA uB uK uL uK₁

namespace IsDiscreteValuationRing

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The reduced compositum of `L` and `K₁` over `K`: the quotient of `L ⊗[K] K₁` by its
nilradical.  This is the ring called `L₁` in Stacks 09EM; when `K₁ / K` is separable the
nilradical is zero and it is the tensor product itself. -/
abbrev reducedCompositum (K : Type uK) (L : Type uL) (K₁ : Type uK₁) [Field K] [Field L]
    [Field K₁] [Algebra K L] [Algebra K K₁] : Type (max uL uK₁) :=
  (L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)

section

variable (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL) (K₁ : Type uK₁)
    [CommRing A] [CommRing B] [Field K] [Field L] [Field K₁]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra A K₁]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]

/-- `A` acts on `L ⊗[K] K₁` through `B`, because it acts on `L` through `B`.  Mathlib provides the
`S`-algebra structure on `L ⊗[K] K₁` for every ring `S` acting on `L`, but not the towers between
two such `S`; this is the one the construction needs. -/
local instance isScalarTower_tensor_of_base : IsScalarTower A B (L ⊗[K] K₁) :=
  IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A L (L ⊗[K] K₁), IsScalarTower.algebraMap_apply A B L,
      ← IsScalarTower.algebraMap_apply B L (L ⊗[K] K₁)]

/-- The square of structure maps `A → B → L₁` and `A → K₁ → L₁` into the reduced compositum
commutes: both composites are the structure map `A → K → L₁`. -/
theorem algebraMap_reducedCompositum_eq (a : A) :
    algebraMap B (reducedCompositum K L K₁) (algebraMap A B a) =
      algebraMap K₁ (reducedCompositum K L K₁) (algebraMap A K₁ a) := by
  rw [← IsScalarTower.algebraMap_apply A B (reducedCompositum K L K₁),
    IsScalarTower.algebraMap_apply A K K₁, ← IsScalarTower.algebraMap_apply K K₁ _,
    ← IsScalarTower.algebraMap_apply A K (reducedCompositum K L K₁)]

/-- The commuting square of `algebraMap_reducedCompositum_eq`, as an equality of ring maps. -/
theorem algebraMap_reducedCompositum_comp_eq :
    (algebraMap B (reducedCompositum K L K₁)).comp (algebraMap A B) =
      (algebraMap K₁ (reducedCompositum K L K₁)).comp (algebraMap A K₁) :=
  RingHom.ext fun a => algebraMap_reducedCompositum_eq A B K L K₁ a

/-- An element of `K₁` integral over `A` stays integral, now over `B`, once pushed into the
reduced compositum. -/
theorem isIntegral_algebraMap_reducedCompositum (x : integralClosure A K₁) :
    IsIntegral B (algebraMap K₁ (reducedCompositum K L K₁) (x : K₁)) :=
  IsIntegral.map_of_comp_eq (algebraMap A B) (algebraMap K₁ (reducedCompositum K L K₁))
    (algebraMap_reducedCompositum_comp_eq A B K L K₁) x.2

/-- The canonical map between the two integral closures of Stacks 09EM: an element of `K₁`
integral over `A`, pushed into the reduced compositum, is integral over `B`. -/
noncomputable def integralClosureCompositumMap :
    integralClosure A K₁ →+* integralClosure B (reducedCompositum K L K₁) :=
  RingHom.codRestrict
    ((algebraMap K₁ (reducedCompositum K L K₁)).comp (algebraMap (integralClosure A K₁) K₁))
    (integralClosure B (reducedCompositum K L K₁))
    fun x => isIntegral_algebraMap_reducedCompositum A B K L K₁ x

/-- The image of `x` under `integralClosureCompositumMap`, viewed in the reduced compositum, is
the image of `x` under the structure map `K₁ → reducedCompositum K L K₁`. -/
@[simp]
theorem coe_integralClosureCompositumMap (x : integralClosure A K₁) :
    (integralClosureCompositumMap A B K L K₁ x : reducedCompositum K L K₁) =
      algebraMap K₁ (reducedCompositum K L K₁) (x : K₁) :=
  rfl

/-- The algebra structure on the upper integral closure over the lower one, given by
`integralClosureCompositumMap`. -/
noncomputable local instance algebraIntegralClosure :
    Algebra (integralClosure A K₁) (integralClosure B (reducedCompositum K L K₁)) :=
  (integralClosureCompositumMap A B K L K₁).toAlgebra

/-- `A` acts on the upper integral closure through the lower one in the same way as it acts
through `B`. -/
local instance isScalarTower_integralClosure :
    IsScalarTower A (integralClosure A K₁) (integralClosure B (reducedCompositum K L K₁)) :=
  IsScalarTower.of_algebraMap_eq fun a => by
    apply Subtype.ext
    rw [(integralClosureCompositumMap A B K L K₁).algebraMap_toAlgebra,
      coe_integralClosureCompositumMap, Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap,
      IsScalarTower.algebraMap_apply A B (reducedCompositum K L K₁),
      algebraMap_reducedCompositum_eq]

variable [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L] [Module.Finite K K₁]

/-- **The canonical base-change package.**  Given an extension of discrete valuation rings
`A → B` with fraction fields `K ⊆ L` and a finite extension `K₁ / K`, this is the
`IntegralClosureBaseChange` package of Stacks 09EM whose three carriers are the reduced
compositum `L₁ = (L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)` and the two integral closures
`A₁ = integralClosure A K₁`, `B₁ = integralClosure B L₁`.

The identification `eL₁` of `L₁` with the reduction of `L ⊗[K] K₁` is the identity, so its two
compatibility conditions hold by definition; so does the commuting square `ringSquare`, because
the map `A₁ → B₁` was defined to be the restriction of `K₁ → L₁`. -/
noncomputable def canonicalBaseChange :
    IntegralClosureBaseChange.{uA, uB, uK, uL, uK₁, max uL uK₁, uK₁, max uL uK₁} A B K L K₁ where
  L₁ := reducedCompositum K L K₁
  A₁ := integralClosure A K₁
  B₁ := integralClosure B (reducedCompositum K L K₁)
  eL₁ := AlgEquiv.refl
  eL₁_left _ := rfl
  eL₁_right _ := rfl
  ringSquare x := by
    rw [(integralClosureCompositumMap A B K L K₁).algebraMap_toAlgebra]
    rfl

/-- The ring `L₁` of `canonicalBaseChange` is the reduced compositum. -/
@[simp]
theorem canonicalBaseChange_L₁ :
    (canonicalBaseChange A B K L K₁).L₁ = reducedCompositum K L K₁ := rfl

/-- The ring `A₁` of `canonicalBaseChange` is the integral closure of `A` in `K₁`. -/
@[simp]
theorem canonicalBaseChange_A₁ :
    (canonicalBaseChange A B K L K₁).A₁ = integralClosure A K₁ := rfl

/-- The ring `B₁` of `canonicalBaseChange` is the integral closure of `B` in the reduced
compositum. -/
@[simp]
theorem canonicalBaseChange_B₁ :
    (canonicalBaseChange A B K L K₁).B₁ = integralClosure B (reducedCompositum K L K₁) := rfl

/-- A finite extension `K₁ / K` of the fraction field downstairs carries a base-change package
with no further data. -/
theorem nonempty_integralClosureBaseChange :
    Nonempty (IntegralClosureBaseChange.{uA, uB, uK, uL, uK₁, max uL uK₁, uK₁, max uL uK₁}
      A B K L K₁) :=
  ⟨canonicalBaseChange A B K L K₁⟩

end

end IsDiscreteValuationRing
