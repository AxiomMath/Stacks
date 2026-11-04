module

public import StacksFrontier.Homology.TorAmplitude.GlobalDimension
public import StacksFrontier.RingTheory.Tor.Balancing
public import StacksCore.Tactic.StacksAttribute

/-! # Tor vanishing above the projective dimension

A module of finite projective dimension has vanishing `Tor` in high degrees. Both `Tor` groups
of a pair of modules are left derived functors of the tensor product — `Tor` in the second
variable and `Tor'` in the first — so for `Tor'` this is immediate from the corresponding
statement about left derived functors, and for `Tor` it follows by balancing.

The consequence actually used downstream is the unquantified form
`exists_isZero_Tor_of_finite_projectiveDimension`: a module of finite projective dimension has a
degree beyond which `Tor` against *every* module vanishes. That is the elementary half of
"`M` has finite Tor dimension", and it is how finiteness of Tor dimension enters Rodicio's
theorem (Stacks Tag 09PV).

## Main results

* `isZero_Tor'_of_hasProjectiveDimensionLE` — vanishing of `Tor'` above the projective dimension.
* `isZero_Tor_of_hasProjectiveDimensionLE` — the same for `Tor`, via the balancing isomorphism.
* `exists_isZero_Tor_of_finite_projectiveDimension` — a uniform vanishing degree.

## References

* [Stacks Project, Tag 00M1](https://stacks.math.columbia.edu/tag/00M1)
-/

@[expose] public noncomputable section

namespace StacksDraft.ProjectiveDimension

open CategoryTheory Limits CategoryTheory.MonoidalCategory

universe u

/-- If `M` has projective dimension at most `d`, then `Tor' p (M, N)` vanishes for every `N` and
every `p > d`. Here `Tor'` is derived in its first variable, which is the one `M` occupies, so
this is the vanishing of a left derived functor on an object of projective dimension `≤ d`. -/
public theorem isZero_Tor'_of_hasProjectiveDimensionLE
    {R : Type u} [CommRing R] (M N : ModuleCat.{u} R) (d p : ℕ)
    (hM : HasProjectiveDimensionLE M d) (hdp : d < p) :
    IsZero (((Tor' (ModuleCat.{u} R) p).obj M).obj N) := by
  rw [CategoryTheory.Tor'_obj_obj]
  exact StacksDraft.TorAmplitude.isZero_leftDerived_of_hasProjectiveDimensionLE
    ((tensoringRight (ModuleCat.{u} R)).obj N) M d p hM hdp

/-- If `M` has projective dimension at most `d`, then `Tor p (M, N)` vanishes for every `N` and
every `p > d`. This is `isZero_Tor'_of_hasProjectiveDimensionLE` transported along the balancing
isomorphism `Tor ≅ Tor'` of Tag 00M1. -/
public theorem isZero_Tor_of_hasProjectiveDimensionLE
    {R : Type u} [CommRing R] (M N : ModuleCat.{u} R) (d p : ℕ)
    (hM : HasProjectiveDimensionLE M d) (hdp : d < p) :
    IsZero (((Tor (ModuleCat.{u} R) p).obj M).obj N) :=
  IsZero.of_iso (isZero_Tor'_of_hasProjectiveDimensionLE M N d p hM hdp)
    (((Tor_iso_Tor' R p).app M).app N)

/-- A module of finite projective dimension has a degree beyond which `Tor` against every module
vanishes. The bound is the projective dimension itself. -/
public theorem exists_isZero_Tor_of_finite_projectiveDimension
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R)
    (h : ∃ n : ℕ, HasProjectiveDimensionLT M n) :
    ∃ b : ℕ, ∀ (N : ModuleCat.{u} R) (i : ℕ), b < i →
      IsZero (((Tor (ModuleCat.{u} R) i).obj M).obj N) := by
  obtain ⟨n, hn⟩ := h
  have hn' : HasProjectiveDimensionLT M n := hn
  exact ⟨n, fun N i hi => isZero_Tor_of_hasProjectiveDimensionLE M N n i
    (hasProjectiveDimensionLT_of_ge M n (n + 1) (by omega)) hi⟩

end StacksDraft.ProjectiveDimension

end
