module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.UniversallyJapanese
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.LocalProperty
public import StacksFrontier.RingTheory.Nagata.Examples

/-!
# Nagata schemes under locally finite type morphisms

The source of a locally finite type morphism to a Nagata scheme is Nagata. In particular a
scheme locally of finite type over a field is Nagata, the spectrum of a field being Nagata
because a field is a Nagata ring.

## Main results

* `AlgebraicGeometry.isNagataScheme_of_locallyOfFiniteType`: the source of a locally finite type
  morphism to a Nagata scheme is Nagata.
* `AlgebraicGeometry.isNagataScheme_spec_of_field`: the spectrum of a field is Nagata.
* `AlgebraicGeometry.isNagataScheme_of_locallyOfFiniteType_over_field`: a scheme locally of
  finite type over a field is Nagata.

## Implementation notes

Being Nagata is a pointwise condition on affine open neighbourhoods, so it suffices to produce,
for each point `x` of the source, an affine open neighbourhood contained in the preimage of a
Nagata affine open of the target. Over such a pair the ring map on sections is of finite type
(`AlgebraicGeometry.LocallyOfFiniteType.finiteType_appLE`), and a finite-type algebra over a
Nagata ring is Nagata — this is the second item of Nagata's theorem `isNagataRing_tfae`.

A scheme over `k` is represented by an explicit structure morphism to `Spec k`; the local
finite-type condition is Mathlib's `AlgebraicGeometry.LocallyOfFiniteType`.

## References

* [Stacks Project, Tag 035A](https://stacks.math.columbia.edu/tag/035A)
* [Stacks Project, Tag 035B](https://stacks.math.columbia.edu/tag/035B)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- **Stacks Project, Tag 035A (Nagata case).** The source of a locally finite type morphism to a
Nagata scheme is Nagata. -/
@[stacks 035A "nagata", ega "IV 7.7.2" "finite type stability"]
theorem isNagataScheme_of_locallyOfFiniteType {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (hS : IsNagataScheme S) : IsNagataScheme X := by
  intro x
  obtain ⟨U, hxU, hU⟩ := hS (f.base x)
  obtain ⟨V, hVaff, hxV, hVsub⟩ :=
    exists_isAffineOpen_mem_and_subset (U := f ⁻¹ᵁ U.1) (by simpa using hxU)
  refine ⟨⟨V, hVaff⟩, hxV, ?_⟩
  let : Algebra Γ(S, U.1) Γ(X, V) := (f.appLE U.1 V hVsub).hom.toAlgebra
  let : Algebra.FiniteType Γ(S, U.1) Γ(X, V) :=
    LocallyOfFiniteType.finiteType_appLE f U.2 hVaff hVsub
  have h : ∀ (T : Type u) [CommRing T] [Algebra Γ(S, U.1) T]
      [Algebra.FiniteType Γ(S, U.1) T], IsNagataRing T :=
    ((isNagataRing_tfae (R := Γ(S, U.1))).out 1 2).mp hU
  exact h Γ(X, V)

/-- The spectrum of a field is a Nagata scheme, a field being a Nagata ring (Tag 0335). -/
theorem isNagataScheme_spec_of_field (k : Type u) [Field k] :
    IsNagataScheme (Spec (.of k)) := fun _ =>
  ⟨⟨⊤, isAffineOpen_top _⟩, Set.mem_univ _,
    CommRing.isNagataRing_propertyIsLocal.of_ringEquiv
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv IsNagataRing.of_field⟩

/-- **Stacks Project, Tag 035B (field case).** A scheme locally of finite type over a field is
Nagata. -/
@[stacks 035B "field"]
theorem isNagataScheme_of_locallyOfFiniteType_over_field (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] : IsNagataScheme X :=
  isNagataScheme_of_locallyOfFiniteType f (isNagataScheme_spec_of_field k)

end AlgebraicGeometry

end
