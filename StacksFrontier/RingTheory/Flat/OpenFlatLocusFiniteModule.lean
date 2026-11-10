module

public import StacksFrontier.RingTheory.Flat.OpenFlatLocus

/-!
# The relative flat locus of a finite module over an algebra of finite type

Let `A → B` be a ring map of finite type and let `M` be a finite `B`-module. The locus

`U = {q ⊂ B prime | M_q is flat over A}`

is a subset of `Spec B`. Openness of this locus for every finite module over every `A`-algebra of
finite type follows from the case of the polynomial rings `A[x_1, …, x_n]`.

Without any further hypothesis the locus need not be open; for a *finitely presented* module
over a *finitely presented* algebra it is, which is
`Module.isOpen_setOf_flat_localizedModule_atPrime`.

## Main results

* `Module.isOpen_setOf_flat_localizedModule_atPrime_of_mvPolynomial`: the reduction of openness
  of the relative flat locus of a finite module to the case of a polynomial ring.
-/

@[expose] public section

universe u v w

/-- **Openness of the relative flat locus of a finite module reduces to the polynomial case.**
If for every `n` the relative flat locus of a finite module over `A[x_1, …, x_n]` is open in
`Spec A[x_1, …, x_n]`, then the relative flat locus of a finite module over any `A`-algebra of
finite type is open in its spectrum. -/
theorem Module.isOpen_setOf_flat_localizedModule_atPrime_of_mvPolynomial {A : Type u}
    [CommRing A] {B : Type v} [CommRing B] [Algebra A B] [Algebra.FiniteType A B] {M : Type w}
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M] [Module.Finite B M]
    (hpoly : ∀ (n : ℕ) (N : Type w) [AddCommGroup N] [Module (MvPolynomial (Fin n) A) N]
      [Module A N] [IsScalarTower A (MvPolynomial (Fin n) A) N]
      [Module.Finite (MvPolynomial (Fin n) A) N],
      IsOpen {p : PrimeSpectrum (MvPolynomial (Fin n) A) |
        Module.Flat A (LocalizedModule.AtPrime p.asIdeal N)}) :
    IsOpen {q : PrimeSpectrum B | Module.Flat A (LocalizedModule.AtPrime q.asIdeal M)} := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  let P := MvPolynomial (Fin n) A
  let : Algebra P B := f.toRingHom.toAlgebra
  let : Module P M := Module.compHom M f.toRingHom
  have : IsScalarTower P B M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower A P M := IsScalarTower.of_algebraMap_smul fun r m ↦ by
    change f (algebraMap A P r) • m = r • m
    rw [f.commutes, algebraMap_smul]
  have : IsScalarTower A P B := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have hsurj : Function.Surjective (algebraMap P B) := hf
  have : Module.Finite P B := Module.Finite.of_surjective (Algebra.linearMap P B) hsurj
  have : Module.Finite P M := Module.Finite.trans (R := P) B M
  have hpre : IsOpen (PrimeSpectrum.comap (algebraMap P B) ⁻¹'
      {p : PrimeSpectrum P | Module.Flat A (LocalizedModule.AtPrime p.asIdeal M)}) :=
    (hpoly n M).preimage (PrimeSpectrum.continuous_comap (algebraMap P B))
  convert hpre using 1
  ext q
  exact (Module.flat_localizedModule_atPrime_comap_iff_of_surjective (R := A) hsurj M
    q.asIdeal).symm

end
