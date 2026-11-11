module

public import StacksFrontier.RingTheory.UniversalHomeomorphism.Examples.BaseChange
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import StacksCore.Tactic.StacksAttribute

/-!
# Surjective ring maps with locally nilpotent kernel

A surjective ring map `φ : R → S` whose kernel is locally nilpotent, i.e. contained in the
nilradical of `R`, induces a homeomorphism `Spec(S) → Spec(R)` and isomorphisms on residue
fields, and these hypotheses are stable under base change.

## Main results

* `PrimeSpectrum.isHomeomorph_comap_of_surjective_of_ker_le_nilradical`: `Spec(φ)` is a
  homeomorphism.
* `RingHom.residueFieldMap_bijective_of_surjective`: the residue field maps of a surjective ring
  map are isomorphisms.
* `Algebra.IsPushout.surjective_and_ker_le_nilradical_of_surjective`: the base change of a
  surjective ring map with locally nilpotent kernel is surjective with locally nilpotent kernel.
* `RingHom.isHomeomorph_comap_and_residueFieldMap_bijective_and_baseChange_of_surjective`:
  the three assertions together, with the base change being `R' → R' ⊗[R] S`.

## References

* [Stacks Project, Tag 0BR6](https://stacks.math.columbia.edu/tag/0BR6)
-/

@[expose] public section

open TensorProduct

/-- A surjective ring map `φ : R → S` whose kernel is locally nilpotent induces a homeomorphism
`Spec(S) → Spec(R)`. -/
@[stacks 0BR6 "(1): the homeomorphism of spectra."]
theorem PrimeSpectrum.isHomeomorph_comap_of_surjective_of_ker_le_nilradical
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (hsurj : Function.Surjective φ)
    (hker : RingHom.ker φ ≤ nilradical R) : IsHomeomorph (PrimeSpectrum.comap φ) :=
  PrimeSpectrum.isHomeomorph_comap φ
    (fun x ↦ ⟨1, one_pos, by simpa using hsurj x⟩) hker

/-- A surjective ring map `φ : R → S` induces isomorphisms on residue fields: for every prime `q`
of `S`, the map `κ(φ⁻¹ q) → κ(q)` is bijective. -/
@[stacks 0BR6 "(2): the isomorphisms on residue fields. Local nilpotence of the kernel is not \
needed for this; it ensures, through (1), that every prime of `R` is of the form `φ⁻¹ q`."]
theorem RingHom.residueFieldMap_bijective_of_surjective
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (hsurj : Function.Surjective φ)
    (q : Ideal S) [q.IsPrime] :
    Function.Bijective (Ideal.ResidueField.map (q.comap φ) q φ rfl) :=
  (RingHom.surjectiveOnStalks_of_surjective hsurj).residueFieldMap_bijective _ _ rfl

/-- Let `R → S` be a surjective ring map with locally nilpotent kernel and let `S'` be its base
change along an arbitrary ring map `R → R'` (a pushout square of `R`-algebras). Then `R' → S'` is
surjective with locally nilpotent kernel. -/
@[stacks 0BR6 "(3): the base change is surjective with locally nilpotent kernel, for an \
arbitrary pushout square."]
theorem Algebra.IsPushout.surjective_and_ker_le_nilradical_of_surjective
    {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] [Algebra R S]
    [Algebra R R'] [Algebra R S'] [Algebra S S'] [Algebra R' S'] [IsScalarTower R S S']
    [IsScalarTower R R' S'] [Algebra.IsPushout R S R' S']
    (hsurj : Function.Surjective (algebraMap R S))
    (hker : RingHom.ker (algebraMap R S) ≤ nilradical R) :
    Function.Surjective (algebraMap R' S') ∧ RingHom.ker (algebraMap R' S') ≤ nilradical R' := by
  obtain ⟨hsurj', hker'⟩ := Algebra.IsPushout.surjective_and_ker_eq_map_of_surjective
    (R := R) (S := S) (R' := R') (S' := S') hsurj
  refine ⟨hsurj', hker' ▸ Ideal.map_le_iff_le_comap.mpr fun x hx ↦ ?_⟩
  exact (mem_nilradical.mp (hker hx)).map (algebraMap R R')

/-- Let `φ : R → S` be a surjective ring map with locally nilpotent kernel. Then `φ` induces a
homeomorphism `Spec(S) → Spec(R)` and isomorphisms `κ(φ⁻¹ q) → κ(q)` on residue fields, and for
any ring map `R → R'` the ring map `R' → R' ⊗[R] S` is surjective with locally nilpotent
kernel. -/
@[stacks 0BR6]
theorem RingHom.isHomeomorph_comap_and_residueFieldMap_bijective_and_baseChange_of_surjective
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (hsurj : Function.Surjective (algebraMap R S))
    (hker : RingHom.ker (algebraMap R S) ≤ nilradical R) :
    IsHomeomorph (PrimeSpectrum.comap (algebraMap R S)) ∧
      (∀ (q : Ideal S) [q.IsPrime],
        Function.Bijective
          (Ideal.ResidueField.map (q.comap (algebraMap R S)) q (algebraMap R S) rfl)) ∧
      ∀ (R' : Type*) [CommRing R'] [Algebra R R'],
        Function.Surjective (algebraMap R' (R' ⊗[R] S)) ∧
          RingHom.ker (algebraMap R' (R' ⊗[R] S)) ≤ nilradical R' :=
  ⟨PrimeSpectrum.isHomeomorph_comap_of_surjective_of_ker_le_nilradical _ hsurj hker,
    fun q _ ↦ RingHom.residueFieldMap_bijective_of_surjective _ hsurj q,
    fun R' _ _ ↦
      letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := R') (B := S)
      Algebra.IsPushout.surjective_and_ker_le_nilradical_of_surjective
        (R := R) (S := S) (R' := R') (S' := R' ⊗[R] S) hsurj hker⟩
