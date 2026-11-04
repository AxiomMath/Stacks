module

public import Mathlib.RingTheory.RingHom.Unramified
public import Mathlib.RingTheory.Unramified.LocalRing
public import StacksCore.Tactic.StacksAttribute

/-!
# Unramified homomorphisms of local rings

Let `A`, `B` be local rings with maximal ideals `𝔪_A`, `𝔪_B` and residue fields `κ(𝔪_A)`,
`κ(𝔪_B)`. A local homomorphism `f : A → B` is an *unramified homomorphism of local rings* if

1. `𝔪_A B = 𝔪_B`,
2. `κ(𝔪_B)` is a finite separable extension of `κ(𝔪_A)`, and
3. `B` is essentially of finite type over `A`.

By Lemmas 00UW and 02FM, conditions (1) and (2) together with (3) say exactly that `f` is
formally unramified and essentially of finite type; the finiteness of the residue field extension
is then automatic.

## Main definitions

* `RingHom.IsUnramifiedLocalHom`: the three conditions above for a local homomorphism `f`.

## Main results

* `RingHom.isUnramifiedLocalHom_iff`: a local homomorphism of local rings is unramified exactly
  when it is formally unramified and essentially of finite type.
* `RingHom.isUnramifiedLocalHom_algebraMap_iff`: the same statement for the structure map of an
  algebra, in terms of `Algebra.FormallyUnramified` and `Algebra.EssFiniteType`.

## Implementation notes

The source assumes that `A` and `B` are Noetherian. The three conditions make sense for arbitrary
local rings, and neither the definition nor its characterization uses this assumption, so it is
omitted. The residue field extension of condition (2) is the one given by
`IsLocalRing.ResidueField.map f`.

## References

* [Stacks Project, Tag 024M](https://stacks.math.columbia.edu/tag/024M)
* [Stacks Project, Tag 00UW](https://stacks.math.columbia.edu/tag/00UW)
* [Stacks Project, Tag 02FM](https://stacks.math.columbia.edu/tag/02FM)
-/

@[expose] public section

open IsLocalRing

namespace RingHom

variable {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]

/-- A local homomorphism `f : A → B` of local rings is an *unramified homomorphism of local
rings* if `𝔪_A B = 𝔪_B`, the residue field `κ(𝔪_B)` is a finite separable extension of
`κ(𝔪_A)`, and `B` is essentially of finite type over `A`. -/
@[stacks 024M]
structure IsUnramifiedLocalHom (f : A →+* B) [IsLocalHom f] : Prop where
  /-- Condition (1): the maximal ideal of `A` generates the maximal ideal of `B`. -/
  map_maximalIdeal : (maximalIdeal A).map f = maximalIdeal B
  /-- Condition (2), finiteness: `κ(𝔪_B)` is a finite extension of `κ(𝔪_A)`. -/
  finite_residueFieldMap : (ResidueField.map f).Finite
  /-- Condition (2), separability: `κ(𝔪_B)` is a separable extension of `κ(𝔪_A)`. -/
  isSeparable_residueFieldMap :
    letI := (ResidueField.map f).toAlgebra
    Algebra.IsSeparable (ResidueField A) (ResidueField B)
  /-- Condition (3): `B` is essentially of finite type over `A`. -/
  essFiniteType : f.EssFiniteType

section algebraMap

variable [Algebra A B] [IsLocalHom (algebraMap A B)]

/-- The algebra structure on residue fields induced by `IsLocalRing.ResidueField.map` of the
structure map is the canonical one. -/
private lemma residueFieldMap_toAlgebra :
    (ResidueField.map (algebraMap A B)).toAlgebra =
      (inferInstance : Algebra (ResidueField A) (ResidueField B)) :=
  Algebra.algebra_ext _ _ fun x ↦ by
    obtain ⟨x, rfl⟩ := residue_surjective x
    rfl

private lemma finite_residueFieldMap_iff :
    (ResidueField.map (algebraMap A B)).Finite ↔
      Module.Finite (ResidueField A) (ResidueField B) := by
  unfold RingHom.Finite
  rw [residueFieldMap_toAlgebra]

private lemma isSeparable_residueFieldMap_iff :
    (letI := (ResidueField.map (algebraMap A B)).toAlgebra
     Algebra.IsSeparable (ResidueField A) (ResidueField B)) ↔
      Algebra.IsSeparable (ResidueField A) (ResidueField B) := by
  rw [residueFieldMap_toAlgebra]

/-- The structure map of a local algebra `B` over `A` is an unramified homomorphism of local rings
if and only if `B` is formally unramified and essentially of finite type over `A`. -/
@[stacks 024M "Equivalently, `A → B` is formally unramified and essentially of finite type."]
theorem isUnramifiedLocalHom_algebraMap_iff :
    (algebraMap A B).IsUnramifiedLocalHom ↔
      Algebra.FormallyUnramified A B ∧ Algebra.EssFiniteType A B := by
  refine ⟨fun ⟨hm, _, hsep, hess⟩ ↦ ?_, fun ⟨_, _⟩ ↦ ?_⟩
  · have hess : Algebra.EssFiniteType A B := essFiniteType_algebraMap.mp hess
    have := isSeparable_residueFieldMap_iff.mp hsep
    exact ⟨.of_map_maximalIdeal hm, hess⟩
  · exact ⟨Algebra.FormallyUnramified.map_maximalIdeal,
      finite_residueFieldMap_iff.mpr inferInstance,
      isSeparable_residueFieldMap_iff.mpr inferInstance, essFiniteType_algebraMap.mpr ‹_›⟩

end algebraMap

/-- A local homomorphism of local rings is an unramified homomorphism of local rings if and only
if it is formally unramified and essentially of finite type. -/
@[stacks 024M "Equivalently, `f` is formally unramified and essentially of finite type."]
theorem isUnramifiedLocalHom_iff (f : A →+* B) [IsLocalHom f] :
    f.IsUnramifiedLocalHom ↔ f.FormallyUnramified ∧ f.EssFiniteType := by
  let := f.toAlgebra
  have : IsLocalHom (algebraMap A B) := ‹IsLocalHom f›
  exact isUnramifiedLocalHom_algebraMap_iff

end RingHom
