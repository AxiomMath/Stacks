module

public import StacksFrontier.AlgebraicGeometry.PicardGroup.Scheme
public import Mathlib.Data.Nat.Choose.Basic

/-!
# An invertible module on a projective space with the Euler characteristics of the trivial one

The last paragraph of the proof of Stacks 0FH9 shows that the norm sheaf `𝒩` is trivial on a
fibre `F ≅ ℙᵐ_k` of `f : Sⁿ(X) ⟶ Pic^n_{X/k}`. The argument has two halves. First, `𝒩'|_{T × F}`
is an invertible module on `T × F` whose restriction over one `k`-point of the connected base `T`
is trivial and over another is `𝒩|_F`, so local constancy of Euler characteristics in a flat
proper family (Stacks 0B9T) gives

  `χ(F, 𝒩^{⊗s}|_F) = 1`  for every `s ∈ ℤ`.

Second — and this is the half the source closes with *"Some details omitted"* — that condition
forces `𝒩|_F ≅ 𝒪_F`, "see Cohomology of Schemes, Lemma 30.8.1", i.e. Stacks 01XT.

This file proves the second half. The reason it can be proved while the first cannot is that the
second half is not geometry: it is the statement that the function `e ↦ χ(ℙᵐ_k, 𝒪(e))` takes the
value `1` only at `e = 0`, read through the isomorphism `Pic(ℙᵐ_k) ≅ ℤ` of Stacks 0BXJ.

## The shape of the hypotheses

`ι` is Stacks 0BXJ, formalized in this repository as
`Stacks.PicardUFD.twistPicardAddEquiv`: the isomorphism `ℤ ≃+ Pic(ℙᵐ_R)` carrying `e` to the
class of `𝒪(e)`, for `0 < m`.

`hχ` is the only thing used about `χ`, and it is Stacks 01XT in the form the source invokes it:
on `ℙᵐ` over a field the twist `𝒪(e)` with `e ≥ 0` has `Hᵖ = 0` for `p > 0` and `H⁰` the
degree-`e` part of a polynomial ring in `m + 1` variables, so

  `χ(ℙᵐ, 𝒪(e)) = binom(e + m, m)`  for `e ≥ 0`.

Nothing is assumed about `χ` at negative twists: the argument reaches the positive side by
replacing `s` with `-s`, which is available because the hypothesis `hx` quantifies over all
`s ∈ ℤ`. Stacks 01XT is formalized here as the cohomology modules of the twists
(`StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistCohomologyMonomial`) rather than
as their Euler characteristic, which is why the numerical value is a hypothesis and not a
citation of a declaration.

`hx` is the output of the first half, i.e. of Stacks 0B9T applied to the family over `T = X`.
It is carried: the family `𝒩' = Norm_{id_T × π}(ℒ'₁)` of the source lives on `T × Sⁿ(X)`, which
this repository does not construct.

The conclusion `x = 0` is the triviality of the module, by
`AlgebraicGeometry.Scheme.picardClass_eq_zero_iff`; the corollary below states it that way.

## Main results

* `Stacks.Picard.eq_zero_of_eulerChar_zsmul_eq_one` — the second half of the final paragraph of
  the proof of Stacks 0FH9: a Picard class all of whose multiples have Euler characteristic `1`
  is zero.
* `Stacks.Picard.isTrivial_of_eulerChar_zsmul_eq_one` — the same, stated as the triviality of
  the invertible module.

## References

* [Stacks Project, Tag 0FH9](https://stacks.math.columbia.edu/tag/0FH9)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 0BXJ](https://stacks.math.columbia.edu/tag/0BXJ)
* [Stacks Project, Tag 0B9T](https://stacks.math.columbia.edu/tag/0B9T)
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace Stacks.Picard

/-- **A Picard class on `ℙᵐ_k` all of whose multiples have Euler characteristic `1` is zero.**

Write `x = ι e` with `e ∈ ℤ`, which is possible because `ι` is the isomorphism
`ℤ ≃+ Pic(ℙᵐ_k)` of Stacks 0BXJ. Then `s • x = ι (s·e)`, so the hypothesis says
`χ(𝒪(s·e)) = 1` for every `s`. If `e ≠ 0` then one of `e`, `-e` is a positive integer `f`, and
Stacks 01XT evaluates `χ(𝒪(f)) = binom(f + m, m) ≥ binom(m + 1, m) = m + 1 ≥ 2`, contradicting
the value `1`. -/
theorem eq_zero_of_eulerChar_zsmul_eq_one {F : Scheme.{u}} (m : ℕ) (hm : 0 < m)
    (ι : ℤ ≃+ F.picardGroup) (χ : F.picardGroup → ℤ)
    (hχ : ∀ e : ℕ, χ (ι (e : ℤ)) = (((e + m).choose m : ℕ) : ℤ))
    (x : F.picardGroup) (hx : ∀ s : ℤ, χ (s • x) = 1) : x = 0 := by
  have hxe : ∀ s : ℤ, χ (ι (s * ι.symm x)) = 1 := fun s => by
    rw [← smul_eq_mul, map_zsmul, AddEquiv.apply_symm_apply]
    exact hx s
  -- a positive twist has Euler characteristic at least `m + 1`
  have hbig : ∀ f : ℕ, 0 < f → χ (ι (f : ℤ)) ≠ 1 := by
    intro f hf h
    have hle : (m + 1).choose m ≤ (f + m).choose m :=
      Nat.choose_le_choose m (by omega)
    rw [hχ f] at h
    rw [Nat.choose_succ_self_right] at hle
    omega
  by_contra hne
  have he : ι.symm x ≠ 0 := ι.symm.map_ne_zero_iff.mpr hne
  -- some positive multiple of `ι.symm x` would be a positive twist
  have hpos : ∀ s : ℤ, 0 < s * ι.symm x → False := fun s hs => by
    obtain ⟨f, hf⟩ : ∃ f : ℕ, s * ι.symm x = (f : ℤ) :=
      ⟨(s * ι.symm x).toNat, (Int.toNat_of_nonneg hs.le).symm⟩
    exact hbig f (by omega) (hf ▸ hxe s)
  rcases lt_or_gt_of_ne he with hlt | hgt
  · exact hpos (-1) (by omega)
  · exact hpos 1 (by omega)

/-- **The second half of the final paragraph of the proof of Stacks 0FH9.** An invertible module
on `ℙᵐ_k` whose every tensor power has the Euler characteristic of the trivial module is
trivial. -/
theorem isTrivial_of_eulerChar_zsmul_eq_one {F : Scheme.{u}} (m : ℕ) (hm : 0 < m)
    (ι : ℤ ≃+ F.picardGroup) (χ : F.picardGroup → ℤ)
    (hχ : ∀ e : ℕ, χ (ι (e : ℤ)) = (((e + m).choose m : ℕ) : ℤ))
    (N : F.Modules)
    (hN : Stacks.SheafOfModules.IsInvertible F.presheaf F.ringCatIsSheaf N)
    (hx : ∀ s : ℤ, χ (s • F.picardClass N hN) = 1) :
    Stacks.SheafOfModules.IsTrivial F.presheaf F.ringCatIsSheaf N :=
  (F.picardClass_eq_zero_iff N hN).mp
    (eq_zero_of_eulerChar_zsmul_eq_one m hm ι χ hχ (F.picardClass N hN) hx)

end Stacks.Picard

end
