module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.FieldTheory.SeparablyGenerated
public import StacksFrontier.FieldTheory.Separable.Defs
public import StacksFrontier.FieldTheory.Separable.PerfectField
public import StacksFrontier.RingTheory.FormallySmooth.Field

/-!
# Coefficient fields of local rings with nilpotent maximal ideal

Let `A` be a local ring of prime characteristic `p` whose maximal ideal is nilpotent. Then the
residue map `A → κ_A` admits a ring-homomorphic section, a *coefficient field* for `A`. Along a
local homomorphism `A → A'` into another such local ring the sections can be chosen compatibly,
provided the induced residue field extension `κ_A → κ_{A'}` is separable.

## Main results

* `IsLocalRing.exists_residueField_section_compatible`: existence of a coefficient field for `A`,
  together with compatible coefficient fields for every local `A`-algebra `A'` whose maximal
  ideal is nilpotent and whose residue field is separable over `κ_A`.

## Implementation notes

Being annihilated by the prime `p` is expressed by `CharP A p`, which makes `A` a `ZMod p`-algebra.
The sections are produced by lifting along the residue map, whose kernel is the maximal ideal and
hence nilpotent; formal smoothness of a separable extension of fields supplies the lift.

## References

* [Stacks Project, Tag 09EZ](https://stacks.math.columbia.edu/tag/09EZ)
-/

@[expose] public section

universe u v

namespace IsLocalRing

/-- A surjection with nilpotent kernel onto a formally smooth algebra has an algebra section. -/
private theorem exists_section_of_formallySmooth {R A B : Type*} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] [Algebra.FormallySmooth R B] (q : A →ₐ[R] B)
    (hq : Function.Surjective q) (hn : IsNilpotent (RingHom.ker q)) :
    ∃ s : B →ₐ[R] A, q.comp s = AlgHom.id R B :=
  ⟨_, Algebra.FormallySmooth.comp_liftOfSurjective (AlgHom.id R B) q hq hn⟩

/-- A local ring of prime characteristic with nilpotent maximal ideal has a coefficient field,
and it can be extended compatibly across a local homomorphism whose target also has nilpotent
maximal ideal and whose residue field extension is separable. -/
@[stacks 09EZ]
theorem exists_residueField_section_compatible
    {p : ℕ} [Fact p.Prime]
    (A : Type u) [CommRing A] [IsLocalRing A] [CharP A p]
    (hA : IsNilpotent (IsLocalRing.maximalIdeal A)) :
    ∃ σ : IsLocalRing.ResidueField A →+* A,
      (IsLocalRing.residue A).comp σ = RingHom.id _ ∧
      ∀ (A' : Type v) [CommRing A'] [IsLocalRing A'] [Algebra A A']
        [IsLocalHom (algebraMap A A')],
        IsNilpotent (IsLocalRing.maximalIdeal A') →
        Algebra.IsSeparableExtension (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField A') →
        ∃ σ' : IsLocalRing.ResidueField A' →+* A',
          (IsLocalRing.residue A').comp σ' = RingHom.id _ ∧
          (algebraMap A A').comp σ =
            σ'.comp (algebraMap (IsLocalRing.ResidueField A)
              (IsLocalRing.ResidueField A')) := by
  let : Algebra (ZMod p) A := ZMod.algebra A p
  let : Algebra (ZMod p) (IsLocalRing.ResidueField A) :=
    ((IsLocalRing.residue A).comp (algebraMap (ZMod p) A)).toAlgebra
  let : Algebra.FormallySmooth (ZMod p) (IsLocalRing.ResidueField A) :=
    (Algebra.FormallySmooth.iff_isSeparableExtension _ _).2
      (Algebra.isSeparableExtension_of_perfectField _ _)
  let q : A →ₐ[ZMod p] IsLocalRing.ResidueField A :=
    { IsLocalRing.residue A with
      commutes' := fun _ => rfl }
  have hqnil : IsNilpotent (RingHom.ker q) := by
    change IsNilpotent (RingHom.ker (IsLocalRing.residue A))
    rwa [IsLocalRing.ker_residue]
  obtain ⟨s, hs⟩ := exists_section_of_formallySmooth q IsLocalRing.residue_surjective hqnil
  refine ⟨s.toRingHom, congrArg AlgHom.toRingHom hs, ?_⟩
  intro A' _ _ _ _ hA' hsep
  let : Algebra (IsLocalRing.ResidueField A) A := s.toRingHom.toAlgebra
  let : Algebra (IsLocalRing.ResidueField A) A' :=
    ((algebraMap A A').comp s.toRingHom).toAlgebra
  let : Algebra.FormallySmooth (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A') :=
    (Algebra.FormallySmooth.iff_isSeparableExtension _ _).2 hsep
  let q' : A' →ₐ[IsLocalRing.ResidueField A] IsLocalRing.ResidueField A' :=
    { IsLocalRing.residue A' with
      commutes' := fun x => by
        change IsLocalRing.residue A' (algebraMap A A' (s x)) = _
        rw [← IsLocalRing.ResidueField.map_residue (algebraMap A A') (s x)]
        exact congrArg (IsLocalRing.ResidueField.map (algebraMap A A'))
          (congrArg (· x) hs) }
  obtain ⟨s', hs'⟩ := exists_section_of_formallySmooth q' IsLocalRing.residue_surjective
    (by
      change IsNilpotent (RingHom.ker (IsLocalRing.residue A'))
      rwa [IsLocalRing.ker_residue])
  refine ⟨s'.toRingHom, congrArg AlgHom.toRingHom hs', ?_⟩
  ext x
  exact (s'.commutes x).symm

end IsLocalRing
