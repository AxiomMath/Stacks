module

public import Mathlib.RingTheory.Regular.ProjectiveDimension
public import StacksFrontier.RingTheory.DividedPowers.CompleteIntersection.RegularSequenceQuotient
public import StacksFrontier.RingTheory.Tor.Balancing

/-!
# Finite projective dimension gives finite Tor dimension

`Stacks.CompleteIntersection.FiniteTorDimension M` asks that `Tor_p(M, N)` vanish for all `N`
above one uniform degree. This file derives it from a finite bound on the projective dimension of
`M`, by induction on that bound through the syzygy short exact sequence used to compare `Tor` and
`Tor'`.

This is the (1) ⇒ (2) step of [Stacks, Tag 09PX] and the form in which the Tor hypothesis of
[Stacks, Tag 09PW] is supplied; neither tag is proved here.

## Main definitions

None.

## Main results

* `Stacks.CompleteIntersection.finiteTorDimension_of_hasProjectiveDimensionLE`: a module with
  `HasProjectiveDimensionLE M n` has finite Tor dimension.

## Implementation notes

The induction is on `n`, generalizing `M`: the successor step replaces `M` by the syzygy
`Tor_iso_Tor'.syzygy R M`, whose projective dimension drops by one because the middle term of
`Tor_iso_Tor'.syzygySC` is projective, and transports the vanishing back along
`Tor_iso_Tor'.tor'Shift`.

## References

* [Stacks Project, Tag 09PX](https://stacks.math.columbia.edu/tag/09PX)
-/

namespace Stacks.CompleteIntersection

open CategoryTheory

universe u

/-- A module of finite projective dimension has finite Tor dimension. -/
public lemma finiteTorDimension_of_hasProjectiveDimensionLE
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (n : ℕ)
    (h : HasProjectiveDimensionLE M n) : FiniteTorDimension M := by
  refine ⟨n, ?_⟩
  induction n generalizing M with
  | zero =>
      intro N p hp
      obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
      have : CategoryTheory.Projective M :=
        CategoryTheory.projective_iff_hasProjectiveDimensionLT_one.mpr h
      exact Limits.IsZero.of_iso
        (CategoryTheory.isZero_Tor'_succ_of_projective (ModuleCat.{u} R) M N p)
        (((Tor_iso_Tor' R (p + 1)).app M).app N)
  | succ n ih =>
      have hP : CategoryTheory.Projective (Tor_iso_Tor'.syzygySC R M).X₂ := by
        show CategoryTheory.Projective (CategoryTheory.Projective.over M)
        infer_instance
      have hK' : HasProjectiveDimensionLE (Tor_iso_Tor'.syzygy R M) n :=
        ((Tor_iso_Tor'.syzygySC_shortExact R M).hasProjectiveDimensionLT_X₃_iff n hP).mp h
      intro N p hp
      obtain ⟨j, rfl⟩ : ∃ j, p = j + 2 := ⟨p - 2, by omega⟩
      have hz : Limits.IsZero
          (((Tor' (ModuleCat.{u} R) (j + 1)).obj
            (Tor_iso_Tor'.syzygy R M)).obj N) :=
        Limits.IsZero.of_iso (ih (Tor_iso_Tor'.syzygy R M) hK' N (j + 1) (by omega))
          (((Tor_iso_Tor' R (j + 1)).app (Tor_iso_Tor'.syzygy R M)).app N).symm
      exact Limits.IsZero.of_iso hz ((((Tor_iso_Tor' R (j + 2)).app M).app N).trans
        ((Tor_iso_Tor'.tor'Shift R j M).app N))

end Stacks.CompleteIntersection
