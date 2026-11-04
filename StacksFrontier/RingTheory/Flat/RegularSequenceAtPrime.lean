module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Submodule
public import StacksFrontier.RingTheory.Flat.LocalCriteria

/-!
# Regular sequences in a local ring of a flat algebra, from the fibre

Let `A` be a Noetherian ring, let `R` be a Noetherian `A`-algebra which is flat over `A`, let `q`
be a prime of `R` and let `p = q ∩ A` be the prime of `A` it lies over. Stacks 00MG applies to the
flat local homomorphism `A_p → R_q` and says: a sequence of elements of `R_q` which is regular on
the fibre `R_q/pR_q` is regular in `R_q`, and every successive quotient `R_q/(f₁, …, f_i)` is
flat over `A_p`, hence over `A`.

This file records that localized form of 00MG, phrased entirely in terms of the prime `q` of `R`:
the base of the flatness conclusion is `A` itself rather than `A_p`, and the fibre is written with
the ideal `pR_q = Ideal.map (algebraMap A R_q) (q.comap (algebraMap A R))`, so no local ring other
than `R_q` appears in the statement.

## Main results

* `isRegular_and_flat_quotient_ofList_take_atPrime`: the statement above.

## Implementation notes

The proof builds the `A_p`-algebra structure on `R_q` out of
`Localization.AtPrime.algebraOfLiesOver` and checks the four hypotheses of 00MG for it: both rings
are Noetherian because a localization of a Noetherian ring is Noetherian, `A_p → R_q` is local
because it is a `Localization.localRingHom`,
and it is flat because `R_q` is flat over `A` and flatness over a localization of the base is
flatness over the base (`Module.flat_iff_of_isLocalization`). The two spellings of the fibre ideal,
`𝔪_p R_q` and `p R_q`, agree because `𝔪_p` is the image of `p`; the flatness of the
successive quotients over `A_p` is upgraded to flatness over `A` by transitivity.

## References

* [Stacks Project, Tag 00MG](https://stacks.math.columbia.edu/tag/00MG)
-/

@[expose] public section

open IsLocalRing

/-- The two spellings of the fibre of a flat local homomorphism `A_p → T` agree: `𝔪_p T = p T`. -/
private theorem map_maximalIdeal_eq_map_of_isLocalization_atPrime
    {A P T : Type*} [CommRing A] [CommRing P] [CommRing T]
    [Algebra A P] [Algebra A T] [Algebra P T] [IsScalarTower A P T]
    (p : Ideal A) [p.IsPrime] [IsLocalization.AtPrime P p] [IsLocalRing P] :
    (maximalIdeal P).map (algebraMap P T) = p.map (algebraMap A T) := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p P, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq A P T]

/-- **Stacks 00MG at a prime.** Let `A` be a Noetherian ring, let `R` be a Noetherian `A`-algebra
which is flat over `A`, let `q` be a prime of `R` and let `p = q ∩ A`. If a sequence `f₁, …, f_c`
of elements of `R_q` is a regular sequence on the fibre `R_q/pR_q`, then it is a regular sequence
in `R_q` and each quotient `R_q/(f₁, …, f_i)` is flat over `A`.

The fibre is the ring quotient of `R_q` by `pR_q`, the images of the `fᵢ` in it are pinned as
`Ideal.Quotient.mk`, and `R_q/(f₁, …, f_i)` is `Localization.AtPrime q ⧸ Ideal.ofList (fs.take i)`
with its canonical `A`-algebra structure. -/
theorem isRegular_and_flat_quotient_ofList_take_atPrime
    {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]
    [IsNoetherianRing A] [IsNoetherianRing R] [Module.Flat A R]
    (q : Ideal R) [q.IsPrime] {fs : List (Localization.AtPrime q)}
    (hfib : RingTheory.Sequence.IsRegular
      (Localization.AtPrime q ⧸
        (q.comap (algebraMap A R)).map (algebraMap A (Localization.AtPrime q)))
      (fs.map (Ideal.Quotient.mk
        ((q.comap (algebraMap A R)).map (algebraMap A (Localization.AtPrime q)))))) :
    RingTheory.Sequence.IsRegular (Localization.AtPrime q) fs ∧
      ∀ i, Module.Flat A (Localization.AtPrime q ⧸ Ideal.ofList (fs.take i)) := by
  let T := Localization.AtPrime q
  let p := q.comap (algebraMap A R)
  have : p.IsPrime := Ideal.comap_isPrime _ _
  have : q.LiesOver p := ⟨rfl⟩
  let P := Localization.AtPrime p
  let : Algebra P T := Localization.AtPrime.algebraOfLiesOver p q
  have : IsLocalHom (algebraMap P T) :=
    Localization.isLocalHom_localRingHom p q (algebraMap A R) rfl
  have : Module.Flat P T :=
    (Module.flat_iff_of_isLocalization P p.primeCompl T).mpr inferInstance
  have hmax : (maximalIdeal P).map (algebraMap P T) = p.map (algebraMap A T) :=
    map_maximalIdeal_eq_map_of_isLocalization_atPrime p
  have hfib' : RingTheory.Sequence.IsRegular (T ⧸ (maximalIdeal P).map (algebraMap P T))
      (fs.map (Ideal.Quotient.mk ((maximalIdeal P).map (algebraMap P T)))) := by
    rw [hmax]; exact hfib
  obtain ⟨hreg, hflat⟩ :=
    Module.Flat.isRegular_and_flat_quotient_ofList_take_of_isRegular_maximalIdeal
      (R := P) (S := T) hfib'
  refine ⟨hreg, fun i => ?_⟩
  have := hflat i
  exact Module.Flat.trans A P _
