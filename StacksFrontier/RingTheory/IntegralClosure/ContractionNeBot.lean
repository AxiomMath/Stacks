module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.TotallySplit
public import StacksCore.Tactic.StacksAttribute

/-!
# Contraction of a nonzero ideal along an algebraic extension of domains

Let `A ⊆ B` be an inclusion of integral domains, modelled as an `A`-algebra structure on
`B` whose structure map `algebraMap A B` is injective. Write `K = Frac(A)` and
`L = Frac(B)`; the inclusion induces a field embedding `K ↪ L`, encoded by an
`Algebra K L` instance together with the scalar towers `IsScalarTower A K L` and
`IsScalarTower A B L`, which say that `A → B → L`, `A → K → L` and `A → L` agree.
Assume the extension `K ⊆ L` is algebraic, i.e. `Algebra.IsAlgebraic K L`.

If `J ⊆ B` is a nonzero ideal, then its contraction
`A ∩ J = Ideal.comap (algebraMap A B) J` is a nonzero ideal of `A`; equivalently some
nonzero element of `A` lies in `J`. Choose `b ∈ J` nonzero. Its image in `L` satisfies a
polynomial relation over `K`; clearing denominators gives a nonzero `P` over `A` with
`P(b) = 0` in `B`, and dividing out the largest power of `X` dividing `P` leaves a
relation whose constant term `P.coeff m` is a nonzero element of `A` lying in `J`.

That both rings are domains is essential: it is what allows passing to fraction fields
and cancelling the factor `b ^ m`.

The topological consequence is that the image of a proper closed subset `V(J) ⊊ Spec(B)`
under `Spec(B) → Spec(A)` lies inside `V(A ∩ J)`, a proper closed subset of `Spec(A)`,
hence is not dense.
-/

@[expose] public section

/-- **Algebraic core (Stacks 0H7L).** Let `A ⊆ B` be an inclusion of integral
domains, modeled by an injective `algebraMap A B`. Let `K = Frac(A)` and
`L = Frac(B)` be their fields of fractions, with the induced field embedding
`K ↪ L` (encoded by the algebra structure `Algebra K L` and the scalar towers
`A → K → L`, `A → B → L`). Assume the extension `K ⊆ L` is algebraic. If `J` is
a nonzero ideal of `B`, then its contraction `A ∩ J = comap (algebraMap A B) J`
is a nonzero ideal of `A`. -/
@[stacks 0H7L "first sentence"]
theorem contraction_ne_bot_of_algebraic
    (A B K L : Type*)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] (hinj : Function.Injective (algebraMap A B))
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsAlgebraic K L]
    (J : Ideal B) (hJ : J ≠ ⊥) :
    Ideal.comap (algebraMap A B) J ≠ ⊥ := by
  have _ := hinj
  obtain ⟨b, hbJ, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  have hbL : IsAlgebraic K (algebraMap B L b) := Algebra.IsAlgebraic.isAlgebraic _
  exact Ideal.comap_ne_bot_of_algebraic_mem hb0 hbJ
    ((isAlgebraic_algebraMap_iff (IsFractionRing.injective B L)).mp
      ((IsFractionRing.isAlgebraic_iff A K L).mpr hbL))

/-- Let `A → B` be an algebraic ring map from a reduced ring into a domain. Then the image in
`Spec A` of a proper closed subset of `Spec B` is not dense. -/
@[stacks 0H7L "second sentence"]
theorem PrimeSpectrum.not_dense_image_comap_of_isAlgebraic {A B : Type*} [CommRing A]
    [CommRing B] [IsReduced A] [IsDomain B] [Algebra A B] [Algebra.IsAlgebraic A B]
    {Z : Set (PrimeSpectrum B)} (hZ : IsClosed Z) (hZ' : Z ≠ Set.univ) :
    ¬ Dense (PrimeSpectrum.comap (algebraMap A B) '' Z) := by
  obtain ⟨J, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Z).1 hZ
  have hJ : J ≠ ⊥ := by
    rintro rfl
    exact hZ' PrimeSpectrum.zeroLocus_bot
  rw [dense_iff_closure_eq, PrimeSpectrum.closure_image_comap_zeroLocus,
    PrimeSpectrum.zeroLocus_eq_univ_iff, nilradical_eq_zero, Submodule.zero_eq_bot,
    SetLike.coe_subset_coe, le_bot_iff]
  obtain ⟨b, hbJ, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  exact Ideal.comap_ne_bot_of_algebraic_mem hb0 hbJ (Algebra.IsAlgebraic.isAlgebraic b)
