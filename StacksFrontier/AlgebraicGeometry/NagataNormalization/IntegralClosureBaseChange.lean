module

public import StacksFrontier.AlgebraicGeometry.NagataNormalization.FiniteType
public import StacksFrontier.RingTheory.Nagata.MonogenicN1
public import StacksFrontier.RingTheory.Nagata.Shrink
public import StacksFrontier.RingTheory.Nagata.Universes

/-!
# Nagata-ness of a base change along an integral closure

Let `A` be a Nagata domain with fraction field `K` and let `L/K` be a finite extension. The
integral closure `B` of `A` in `L` is module-finite over `A` and is again a Nagata ring, so the
spectrum of `B` is a Nagata scheme and every scheme locally of finite type over it — in
particular the base change `X ×_{Spec A} Spec B` of a scheme locally of finite type over `A` —
is a Nagata scheme.

## Main results

* `module_finite_integralClosure_of_isNagataRing` and `isNagataRing_integralClosure`: the
  integral closure of a Nagata domain in a finite extension of its fraction field is
  module-finite and Nagata. The fraction field and the extension may live in universes of their
  own.
* `AlgebraicGeometry.isNagataScheme_spec_of_isNagataRing`: the spectrum of a Nagata ring is a
  Nagata scheme.
* `AlgebraicGeometry.isNagataScheme_of_isNagataRing`: a scheme locally of finite type over a
  Nagata ring is a Nagata scheme.
* `AlgebraicGeometry.isNagataScheme_pullback_integralClosure`: the base change of a scheme
  locally of finite type over a Nagata domain along the integral closure in a finite extension
  of the fraction field is a Nagata scheme.

## Implementation notes

`MonogenicN1.module_finite_and_isNagataRing_integralClosure` is the same pair of statements with
the base ring, the fraction field and the extension in one common universe; the versions here
split the universes, which is what a base change of a scheme over `Spec A` needs, since `Spec`
forces `A` and `B` to share a universe while the fraction field is unconstrained.
-/

@[expose] public section

open CategoryTheory

universe u v w

/-- **The integral closure of a Nagata domain in a finite extension of its fraction field is
module-finite.** A Nagata domain is Japanese, and that is exactly this finiteness. -/
theorem module_finite_integralClosure_of_isNagataRing {A : Type u} [CommRing A] [IsDomain A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] (hA : IsNagataRing A) :
    Module.Finite A (integralClosure A L) :=
  module_finite_integralClosure_of_isJapaneseRing
    (MonogenicN1.isJapaneseRing_of_isNagataRing hA) K L

/-- **The integral closure of a Nagata domain in a finite extension of its fraction field is
again a Nagata ring.** The closure is module-finite, hence of finite type, over the Nagata
domain, and a finite type algebra over a Nagata ring is Nagata (Tag 032T). -/
theorem isNagataRing_integralClosure {A : Type u} [CommRing A] [IsDomain A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] (hA : IsNagataRing A) :
    IsNagataRing (integralClosure A L) := by
  have : Module.Finite A ↥(integralClosure A L) :=
    module_finite_integralClosure_of_isNagataRing K L hA
  have : Algebra.FiniteType A ↥(integralClosure A L) := Module.Finite.finiteType _
  exact IsNagataRing.of_finiteType hA

namespace AlgebraicGeometry

/-- **The spectrum of a Nagata ring is a Nagata scheme.** Its whole space is an affine open whose
ring of sections is isomorphic to the ring, and being Nagata is a local property of commutative
rings, hence invariant under ring isomorphism. -/
theorem isNagataScheme_spec_of_isNagataRing (R : Type u) [CommRing R] (hR : IsNagataRing R) :
    IsNagataScheme (Spec (.of R)) := fun _ ↦
  ⟨⟨⊤, isAffineOpen_top _⟩, Set.mem_univ _,
    CommRing.isNagataRing_propertyIsLocal.of_ringEquiv
      (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv hR⟩

/-- **A scheme locally of finite type over a Nagata ring is a Nagata scheme**, by Tag 035A. -/
theorem isNagataScheme_of_isNagataRing {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] (hR : IsNagataRing R) : IsNagataScheme X :=
  isNagataScheme_of_locallyOfFiniteType f (isNagataScheme_spec_of_isNagataRing R hR)

/-- **The base change along an integral closure of a scheme locally of finite type over a Nagata
domain is a Nagata scheme.** For `A` a Nagata domain with fraction field `K`, `L/K` finite and
`B` the integral closure of `A` in `L`, the ring `B` is Nagata and the projection
`X ×_{Spec A} Spec B ⟶ Spec B` is locally of finite type. -/
theorem isNagataScheme_pullback_integralClosure {A : Type u} [CommRing A] [IsDomain A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type u) [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] (hA : IsNagataRing A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] :
    IsNagataScheme (Limits.pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A L))))) :=
  isNagataScheme_of_isNagataRing (Limits.pullback.snd f _)
    (isNagataRing_integralClosure K L hA)

end AlgebraicGeometry

end
