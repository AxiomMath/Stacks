module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Excellent.Basic

/-!
# Quasi-excellent and excellent schemes

A scheme is quasi-excellent (resp. excellent) when every point has an affine open neighbourhood
whose ring of sections is quasi-excellent (resp. excellent). A scheme locally of finite type over
a (quasi-)excellent scheme is (quasi-)excellent, and consequently every scheme locally of finite
type over a field, over a Noetherian complete local ring, over the integers, or over a Dedekind
domain of characteristic zero is excellent.

## Main definitions

* `AlgebraicGeometry.IsQuasiExcellentScheme`: the quasi-excellent condition for schemes.
* `AlgebraicGeometry.IsExcellentScheme`: the excellent condition for schemes.

## Main results

* `AlgebraicGeometry.isQuasiExcellentScheme_and_isExcellentScheme_of_locallyOfFiniteType`:
  a scheme locally of finite type over a (quasi-)excellent scheme is (quasi-)excellent.
* `AlgebraicGeometry.isExcellentScheme_spec`: the spectrum of an excellent ring is excellent.
* `AlgebraicGeometry.isExcellentScheme_of_locallyOfFiniteType_over_field`,
  `AlgebraicGeometry.isExcellentScheme_of_locallyOfFiniteType_over_completeLocalRing`,
  `AlgebraicGeometry.isExcellentScheme_of_locallyOfFiniteType_over_int`,
  `AlgebraicGeometry.isExcellentScheme_of_locallyOfFiniteType_over_dedekindDomain`:
  the four families of excellent schemes.

## Implementation notes

A scheme over a ring is represented by a morphism to the spectrum of that ring, and the spectrum
of a ring in `Type u` is a scheme in universe `u`. So "over the integers" is read as "over
`Spec (ULift ℤ)`", which is no restriction on the scheme: `Spec (ULift ℤ)` is the terminal
scheme of the ambient universe, canonically isomorphic to `Spec ℤ` when that universe is `0`.

An affine open of the source of a locally finite type morphism contained in the inverse image of
an affine open of the base has a ring of sections of finite type over that of the base, so it
inherits (quasi-)excellence from the ring theoretic statement.

A Dedekind ring is `IsDedekindDomain`, which, as in the Stacks Project, includes fields.

## References

* [Stacks Project, Tag 0HA7](https://stacks.math.columbia.edu/tag/0HA7)
* [Stacks Project, Tag 0HAC](https://stacks.math.columbia.edu/tag/0HAC)
* [Stacks Project, Tag 0HAD](https://stacks.math.columbia.edu/tag/0HAD)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A scheme is **quasi-excellent** if every point has an affine open neighbourhood whose ring of
sections is quasi-excellent. -/
@[stacks 0HA7 "quasi-excellent"]
def IsQuasiExcellentScheme (X : Scheme.{u}) : Prop :=
  ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ IsQuasiExcellent Γ(X, U.1)

/-- A scheme is **excellent** if every point has an affine open neighbourhood whose ring of
sections is excellent. -/
@[stacks 0HA7 "excellent"]
def IsExcellentScheme (X : Scheme.{u}) : Prop :=
  ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ IsExcellent Γ(X, U.1)

/-- Let `P` be a property of rings inherited by finite type algebras. If every point of `S` has an
affine open neighbourhood whose ring of sections satisfies `P` and `f : X ⟶ S` is locally of
finite type, then every point of `X` has such a neighbourhood. -/
private theorem exists_affineOpen_of_locallyOfFiniteType
    (P : ∀ (R : Type u) [CommRing R], Prop)
    (hP : ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S],
      P R → P S)
    {X S : Scheme.{u}} (f : X ⟶ S) [hf : LocallyOfFiniteType f]
    (hS : ∀ s : S, ∃ U : S.affineOpens, s ∈ U.1 ∧ P Γ(S, U.1)) :
    ∀ x : X, ∃ V : X.affineOpens, x ∈ V.1 ∧ P Γ(X, V.1) := by
  intro x
  obtain ⟨U, hxU, hU⟩ := hS (f.base x)
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ f ⁻¹ᵁ (U.1 : S.Opens) from hxU) (f ⁻¹ᵁ (U.1 : S.Opens)).isOpen
  let _ : Algebra Γ(S, U.1) Γ(X, V) := (f.appLE U.1 V hVU).hom.toAlgebra
  have : Algebra.FiniteType Γ(S, U.1) Γ(X, V) :=
    HasRingHomProperty.appLE @LocallyOfFiniteType f hf U ⟨V, hV⟩ hVU
  exact ⟨⟨V, hV⟩, hxV, hP _ _ hU⟩

/-- **Stacks 0HAC.** A scheme locally of finite type over a quasi-excellent scheme is
quasi-excellent, and a scheme locally of finite type over an excellent scheme is excellent. -/
@[stacks 0HAC]
theorem isQuasiExcellentScheme_and_isExcellentScheme_of_locallyOfFiniteType {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] :
    (IsQuasiExcellentScheme S → IsQuasiExcellentScheme X) ∧
      (IsExcellentScheme S → IsExcellentScheme X) := by
  have : ∀ (R T : Type u) [CommRing R] [CommRing T] [Algebra R T] [Algebra.FiniteType R T],
      Algebra.EssFiniteType R T := fun R T _ _ _ _ => Algebra.EssFiniteType.of_finiteType R T
  exact ⟨exists_affineOpen_of_locallyOfFiniteType (fun R _ => IsQuasiExcellent R)
      (fun _ _ _ _ _ _ => isQuasiExcellent_and_isExcellent_of_essFiniteType.1) f,
    exists_affineOpen_of_locallyOfFiniteType (fun R _ => IsExcellent R)
      (fun _ _ _ _ _ _ => isQuasiExcellent_and_isExcellent_of_essFiniteType.2) f⟩

/-- The spectrum of an excellent ring is an excellent scheme. -/
theorem isExcellentScheme_spec (A : Type u) [CommRing A] (hA : IsExcellent A) :
    IsExcellentScheme (Spec (.of A)) := by
  intro x
  refine ⟨⟨⊤, isAffineOpen_top (Spec (.of A))⟩, by simp, ?_⟩
  let φ : A →+* Γ(Spec (.of A), ⊤) := (Scheme.ΓSpecIso (.of A)).inv.hom
  let _ : Algebra A Γ(Spec (.of A), ⊤) := φ.toAlgebra
  have : Algebra.FiniteType A Γ(Spec (.of A), ⊤) :=
    RingHom.FiniteType.of_surjective φ
      (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.symm.surjective
  exact (isQuasiExcellent_and_isExcellent_of_essFiniteType
    (R := A) (S := Γ(Spec (.of A), ⊤))).2 hA

/-- A scheme locally of finite type over the spectrum of an excellent ring is excellent. -/
theorem isExcellentScheme_of_locallyOfFiniteType_over_spec (A : Type u) [CommRing A]
    (hA : IsExcellent A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] :
    IsExcellentScheme X :=
  (isQuasiExcellentScheme_and_isExcellentScheme_of_locallyOfFiniteType f).2
    (isExcellentScheme_spec A hA)

/-- **Stacks 0HAD, clause (1).** A scheme locally of finite type over a field is excellent. -/
@[stacks 0HAD "clause (1): over a field"]
theorem isExcellentScheme_of_locallyOfFiniteType_over_field (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    IsExcellentScheme X :=
  isExcellentScheme_of_locallyOfFiniteType_over_spec k
    ((isExcellent_of_standard_classes_and_finiteType.{u, u}).1 k) f

/-- **Stacks 0HAD, clause (2).** A scheme locally of finite type over a Noetherian complete local
ring is excellent. -/
@[stacks 0HAD "clause (2): over a Noetherian complete local ring"]
theorem isExcellentScheme_of_locallyOfFiniteType_over_completeLocalRing (R : Type u)
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] :
    IsExcellentScheme X :=
  isExcellentScheme_of_locallyOfFiniteType_over_spec R
    ((isExcellent_of_standard_classes_and_finiteType.{u, u}).2.1 R) f

/-- The integers, lifted to an arbitrary universe, are excellent: `ULift ℤ` is a finite
algebra over `ℤ`, hence of finite type over it, and the integers are excellent. -/
private theorem isExcellent_uliftInt : IsExcellent (ULift.{u} ℤ) :=
  have : Algebra.FiniteType ℤ (ULift.{u} ℤ) := Module.Finite.finiteType _
  (isExcellent_of_standard_classes_and_finiteType.{0, u}).2.2.2.2 ℤ (ULift.{u} ℤ)
    (isExcellent_of_standard_classes_and_finiteType.{0, 0}).2.2.1

/-- **Stacks 0HAD, clause (3).** A scheme locally of finite type over the integers is excellent.
The base is `Spec (ULift ℤ)`, the terminal scheme of the ambient universe, so this is the
statement for a scheme in an arbitrary universe. -/
@[stacks 0HAD "clause (3): over the integers"]
theorem isExcellentScheme_of_locallyOfFiniteType_over_int {X : Scheme.{u}}
    (f : X ⟶ Spec (.of (ULift.{u} ℤ))) [LocallyOfFiniteType f] :
    IsExcellentScheme X :=
  isExcellentScheme_of_locallyOfFiniteType_over_spec (ULift.{u} ℤ) isExcellent_uliftInt f

/-- **Stacks 0HAD, clause (4).** A scheme locally of finite type over a Dedekind ring of
characteristic zero is excellent. -/
@[stacks 0HAD "clause (4): over a Dedekind ring of characteristic zero"]
theorem isExcellentScheme_of_locallyOfFiniteType_over_dedekindDomain (R : Type u) [CommRing R]
    [IsDedekindDomain R] [CharZero R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [LocallyOfFiniteType f] :
    IsExcellentScheme X :=
  have : CharZero (FractionRing R) :=
    (RingHom.charZero_iff (IsFractionRing.injective R (FractionRing R))).mp ‹_›
  isExcellentScheme_of_locallyOfFiniteType_over_spec R
    ((isExcellent_of_standard_classes_and_finiteType.{u, u}).2.2.2.1 R) f

end AlgebraicGeometry
