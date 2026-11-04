module

public import StacksFrontier.RingTheory.Fitting.Rank

/-!
# Base change of a finite locally free module of a given rank

A finite locally free module of rank `d` stays finite locally free of rank `d` after any base
change, and the property only depends on the module up to a linear equivalence.

## Main results

* `Module.IsFiniteLocallyFreeOfRank.of_linearEquiv`: being finite locally free of rank `d` is
  invariant under a linear equivalence.
* `Module.IsFiniteLocallyFreeOfRank.baseChange`: being finite locally free of rank `d` is
  preserved by base change along an arbitrary algebra.

## Implementation notes

Base change is read off the Fitting-ideal characterisation of Tag 07ZD,
`finiteLocallyFreeOfRank_fittingIdeal_tfae`: a finite module is finite locally free of rank `d`
exactly when its `(d-1)`st Fitting ideal vanishes and its `d`th Fitting ideal is the unit ideal.
Fitting ideals commute with base change, and the extension of an ideal maps the zero ideal to the
zero ideal and the unit ideal to the unit ideal, so both conditions transport. No cover has to be
carried across, which is what makes this route short.

## References

* [Stacks Project, Tag 00NW](https://stacks.math.columbia.edu/tag/00NW)
* [Stacks Project, Tag 07ZD](https://stacks.math.columbia.edu/tag/07ZD)
-/

@[expose] public section

open TensorProduct

universe u v w

/-- Being finite locally free of rank `d` only depends on the module up to a linear equivalence:
the trivialising cover is kept and the bases are transported along the localised equivalence. -/
theorem Module.IsFiniteLocallyFreeOfRank.of_linearEquiv {R : Type u} [CommRing R]
    {M : Type v} {N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) {d : ℕ} (h : Module.IsFiniteLocallyFreeOfRank R M d) :
    Module.IsFiniteLocallyFreeOfRank R N d := by
  obtain ⟨ι, f, hspan, hbasis⟩ := h
  refine ⟨ι, f, hspan, fun i ↦ ?_⟩
  let S := Submonoid.powers (f i)
  let eLoc : LocalizedModule S M ≃ₗ[Localization S] LocalizedModule S N :=
    LinearEquiv.ofBijective (LocalizedModule.map S e.toLinearMap)
      ⟨LocalizedModule.map_injective S e.toLinearMap e.injective,
        LocalizedModule.map_surjective S e.toLinearMap e.surjective⟩
  exact ⟨(hbasis i).some.map eLoc⟩

/-- Being finite locally free of rank `d` is preserved by an arbitrary base change: if `M` is a
finite locally free `R`-module of rank `d` then `S ⊗[R] M` is a finite locally free `S`-module of
rank `d`, for every `R`-algebra `S`. -/
theorem Module.IsFiniteLocallyFreeOfRank.baseChange {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (S : Type w) [CommRing S] [Algebra R S] {d : ℕ}
    (h : Module.IsFiniteLocallyFreeOfRank R M d) :
    Module.IsFiniteLocallyFreeOfRank S (TensorProduct R S M) d := by
  have hbc (k : ℕ) : fittingIdeal (R := S) (M := TensorProduct R S M) (k : ℤ) =
      Ideal.map (algebraMap R S) (fittingIdeal (R := R) (M := M) (k : ℤ)) :=
    (fittingIdeal_basic_properties.{u, v, v, w} (R := R) (M := M)).2.2.1 S k
  obtain ⟨hprev, htop⟩ := (finiteLocallyFreeOfRank_fittingIdeal_tfae
    (R := R) (M := M) d).out 1 2 |>.mp h
  refine ((finiteLocallyFreeOfRank_fittingIdeal_tfae (R := S) (M := TensorProduct R S M) d).out
    2 1).mp (And.intro ?_ (by rw [hbc d, htop, Ideal.map_top]))
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [fittingIdeal]
  · have hindex : (d : ℤ) - 1 = ((d - 1 : ℕ) : ℤ) := by omega
    rw [hindex] at hprev ⊢
    rw [hbc (d - 1), hprev, Ideal.map_bot]

end
