module

public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic

/-!
# Quasi-coherence of higher direct images reduces to the positive degrees

Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes and let `F` be a
quasi-coherent `𝒪_X`-module. [Stacks, Tag 01XJ] asserts that every higher direct image
`R ᵖ f_* F` is quasi-coherent. This file treats the degrees that do not need the
Mayer--Vietoris argument of [Stacks, Tag 01EC], reducing the statement to the positive degrees:

* negative `p` is [Stacks, Tag 01XJ]'s trivial case, the higher direct image being zero
  (`Stacks.AlgebraicGeometry.HigherDirectImage.isQuasicoherent_higherDirectImage_of_neg`);
* degree `0` is the direct image `f_* F`, quasi-coherent by [Stacks, Tag 01LC]
  (`AlgebraicGeometry.pushforward_isQuasicoherent`);
* Mathlib's `ℕ`-indexed `CategoryTheory.Functor.rightDerived` has no negative degrees at all,
  so for it only degree `0` and the positive degrees occur.

The consequence is that the whole of [Stacks, Tag 01XJ], in either indexing, and with it the
quasi-coherence clause of [Stacks, Tag 0EX4] — where properness supplies quasi-compactness and
quasi-separatedness and buys nothing else — follow from the positive-degree statement alone.

## Main results

* `Stacks.AlgebraicGeometry.HigherDirectImageQcoh.isQuasicoherent_higherDirectImage_zero` and
  `Stacks.AlgebraicGeometry.HigherDirectImageQcoh.isQuasicoherent_rightDerived_zero`: the
  degree-zero case of [Stacks, Tag 01XJ], unconditionally, in the `ℤ`-indexing and in the
  `ℕ`-indexing.
* `Stacks.AlgebraicGeometry.HigherDirectImageQcoh.isQuasicoherent_higherDirectImage_of_forall_pos`
  and
  `Stacks.AlgebraicGeometry.HigherDirectImageQcoh.isQuasicoherent_rightDerived_of_forall_pos`:
  the positive degrees imply all degrees.
* `isQuasicoherent_rightDerived_of_isProper_of_forall_pos`, in the same namespace: the same
  reduction stated for a proper morphism, which is the shape the quasi-coherence clause of
  [Stacks, Tag 0EX4] asks for.

## Implementation notes

No `@[stacks]` attribute is attached: Tag 01XJ asserts quasi-coherence in *every* degree, and
the positive degrees are not proved in this file; the full statement is
`Stacks.AlgebraicGeometry.HigherDirectImageQcoh.isQuasicoherent_higherDirectImage`. The two
indexings of the higher right derived functors are compared by
`Stacks.DerivedIndexing.rightDerivedIso`, and the derived category instances are
`CategoryTheory.HasDerivedCategory.standard`, installed as a local instance.

## References

* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
* [Stacks Project, Tag 0EX4](https://stacks.math.columbia.edu/tag/0EX4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.HigherDirectImageQcoh

variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
  (F : X.Modules) [F.IsQuasicoherent]

/-- **The degree-zero case of [Stacks, Tag 01XJ].** For a quasi-compact and quasi-separated
morphism of schemes, `R ⁰ f_* F` is quasi-coherent whenever `F` is: it is the direct image
`f_* F`, which is quasi-coherent by [Stacks, Tag 01LC]. -/
theorem isQuasicoherent_higherDirectImage_zero :
    (((Scheme.Modules.pushforward f).rightDerivedPlus 0).obj F).IsQuasicoherent :=
  (HigherDirectImage.isQuasicoherent_higherDirectImage_zero_iff f F).2 inferInstance

/-- **The degree-zero case of [Stacks, Tag 01XJ] for Mathlib's `ℕ`-indexed right derived
functors.** -/
theorem isQuasicoherent_rightDerived_zero :
    (((Scheme.Modules.pushforward f).rightDerived 0).obj F).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
    ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) 0).app F).symm
    (isQuasicoherent_higherDirectImage_zero f F)

/-- **[Stacks, Tag 01XJ] follows from its positive degrees.** If `R ⁿ f_* F` is quasi-coherent
for every `n > 0` then it is quasi-coherent in every integer degree: negative degrees vanish
and degree zero is [Stacks, Tag 01LC]. -/
theorem isQuasicoherent_higherDirectImage_of_forall_pos
    (h : ∀ n : ℕ, 0 < n →
      (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj F).IsQuasicoherent)
    (p : ℤ) : (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F).IsQuasicoherent := by
  rcases lt_trichotomy p 0 with hp | rfl | hp
  · exact HigherDirectImage.isQuasicoherent_higherDirectImage_of_neg f F p hp
  · exact isQuasicoherent_higherDirectImage_zero f F
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp.le
    exact h n (by exact_mod_cast hp)

/-- **[Stacks, Tag 01XJ] for Mathlib's `ℕ`-indexed right derived functors follows from its
positive degrees.** -/
theorem isQuasicoherent_rightDerived_of_forall_pos
    (h : ∀ n : ℕ, 0 < n →
      (((Scheme.Modules.pushforward f).rightDerived n).obj F).IsQuasicoherent)
    (i : ℕ) : (((Scheme.Modules.pushforward f).rightDerived i).obj F).IsQuasicoherent := by
  obtain _ | i := i
  · exact isQuasicoherent_rightDerived_zero f F
  · exact h (i + 1) i.succ_pos

/-- **The quasi-coherence clause of [Stacks, Tag 0EX4] follows from the positive degrees of
[Stacks, Tag 01XJ].** A proper morphism is quasi-compact and quasi-separated, and properness
is used for nothing else here. -/
theorem isQuasicoherent_rightDerived_of_isProper_of_forall_pos {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsProper g] (G : X.Modules) [G.IsQuasicoherent]
    (h : ∀ n : ℕ, 0 < n →
      (((Scheme.Modules.pushforward g).rightDerived n).obj G).IsQuasicoherent)
    (i : ℕ) : (((Scheme.Modules.pushforward g).rightDerived i).obj G).IsQuasicoherent :=
  isQuasicoherent_rightDerived_of_forall_pos g G h i

end Stacks.AlgebraicGeometry.HigherDirectImageQcoh

end
