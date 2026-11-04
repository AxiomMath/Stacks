module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapOnCyclesDescent
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleFlat
public import StacksCore.Tactic.StacksAttribute

/-!
# The projective bundle characterization of `c_j(ℰ) ∩ α`

Let `(S, δ)` be the base situation of chapter 42, `X` locally of finite type over `S` and `ℰ` a
finite locally free `𝒪_X`-module of rank `r`, with projective bundle
`(π : 𝐏(ℰ) ⟶ X, 𝒪_{𝐏(ℰ)}(1))`, the scheme `Stacks.Chow.bundle ℰ`. For a `k`-cycle `α` on `X`,
[Stacks, Tag 02U6] says that the classes `c_j(ℰ) ∩ α ∈ A_{k-j}(X)` of [Stacks, Tag 02U5] are the
unique classes `α_j ∈ A_{k-j}(X)`, `0 ≤ j ≤ r`, with `α_0 = [α]` and

  `∑_{i=0}^{r} (-1)^i c₁(𝒪_{𝐏(ℰ)}(1))^i ∩ π^*(α_{r-i}) = 0`  in the Chow group of `𝐏(ℰ)`.

The condition is `Stacks.Chow.IsChernCapFamilyOfRank`, read on the genuine projective bundle
with the genuine flat pullback along its projection and the genuine first Chern class of its
twist. It has a unique solution `Stacks.Chow.chernCapFamilyOfRank`, by the projective space bundle
formula [Stacks, Tag 02TX]; that this solution is the family of operations of Stacks 02U5 applied
to `α` is `Stacks.Chow.GenuineChern.chernCap_mk_eq_chernCapOnCycles`.

Combined with the compatibilities of the cap products of classes with proper pushforward and
flat pullback, the same identification gives [Stacks, Tag 02U9] and [Stacks, Tag 02U8] for the
operations of Stacks 02U5 on cycles.

## Main results

* `Stacks.Chow.GenuineChern.chernCapOnCycles_eq_chernCapFamilyOfRank` — the family
  `(c_j(ℰ) ∩ α)_j` is the unique solution for `[α]`.
* `Stacks.Chow.GenuineChern.isChernCapFamilyOfRank_chernCapOnCycles` — **Stacks 02U6**.
* `Stacks.Chow.GenuineChern.properChowPushforward_chernCapOnCycles` — **Stacks 02U9**.
* `Stacks.Chow.GenuineChern.flatPullbackChow_chernCapOnCycles` — **Stacks 02U8**.

## References

* [Stacks Project, Tag 02U5](https://stacks.math.columbia.edu/tag/02U5)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02U8](https://stacks.math.columbia.edu/tag/02U8)
* [Stacks Project, Tag 02U9](https://stacks.math.columbia.edu/tag/02U9)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow.GenuineChern

variable (C : ChowSituation.{u})

section Characterization

variable {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (E : X.Modules) (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]

/-- The family `(c_j(ℰ) ∩ α)_{0 ≤ j ≤ r}` of the operations of Stacks 02U5 applied to a `k`-cycle
`α` is the unique solution of the projective bundle relation for the class of `α`. -/
theorem chernCapOnCycles_eq_chernCapFamilyOfRank (k : ℤ) (α : CycleGroup C sX k) :
    (fun j : Fin (r + 1) ↦ chernCapOnCycles C sX E r k j α) =
      chernCapFamilyOfRank E r C sX k (QuotientAddGroup.mk' (rationalEquivalences C sX k) α) := by
  funext j
  rw [← chernCap_mk_eq_chernCapOnCycles, chernCap_eq_chernCapFamilyOfRank]

/-- **Stacks 02U6.** Let `ℰ` be finite locally free of rank `r` on `X`, with projective bundle
`(π : 𝐏(ℰ) ⟶ X, 𝒪_{𝐏(ℰ)}(1))`, and let `α` be a `k`-cycle on `X`. The classes
`c_j(ℰ) ∩ α ∈ A_{k-j}(X)` of Stacks 02U5 satisfy `α_0 = [α]` and
`∑_{i=0}^{r} (-1)^i c₁(𝒪_{𝐏(ℰ)}(1))^i ∩ π^*(α_{r-i}) = 0` in the Chow group of `𝐏(ℰ)`, and they
are the only family `(α_j)_{0 ≤ j ≤ r}`, `α_j ∈ A_{k-j}(X)`, doing so. -/
@[stacks 02U6]
theorem isChernCapFamilyOfRank_chernCapOnCycles (k : ℤ) (α : CycleGroup C sX k) :
    IsChernCapFamilyOfRank E r C sX k (QuotientAddGroup.mk' (rationalEquivalences C sX k) α)
        (fun j ↦ chernCapOnCycles C sX E r k j α) ∧
      ∀ c : ∀ j : Fin (r + 1), chowGroup C sX (k - (j : ℤ)),
        IsChernCapFamilyOfRank E r C sX k (QuotientAddGroup.mk' (rationalEquivalences C sX k) α)
          c → c = fun j ↦ chernCapOnCycles C sX E r k j α := by
  rw [chernCapOnCycles_eq_chernCapFamilyOfRank]
  exact ⟨isChernCapFamilyOfRank_chernCapFamilyOfRank E r C sX k _,
    eq_chernCapFamilyOfRank_of_isChernCapFamilyOfRank E r C sX k _⟩

end Characterization

/-- **Stacks 02U9.** Let `p : X ⟶ Y` be a proper morphism of schemes locally of finite type over
`S`, `ℰ` finite locally free of rank `r` on `Y` and `α` a `k`-cycle on `X`. Then
`p_*(c_j(p^*ℰ) ∩ α) = c_j(ℰ) ∩ p_*α` in `A_{k-j}(Y)`. -/
@[stacks 02U9]
theorem properChowPushforward_chernCapOnCycles {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (p : X ⟶ Y) [IsProper p]
    (hp : p ≫ sY = sX) (E : Y.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (k : ℤ)
    (j : Fin (r + 1)) (α : CycleGroup C sX k) :
    haveI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback p E r
    properChowPushforward C sX sY p hp (k - (j : ℤ))
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sX sY p hp _)
        (chernCapOnCycles C sX ((Scheme.Modules.pullback p).obj E) r k j α) =
      chernCapOnCycles C sY E r k j (properPushforward C sX sY p hp k α) := by
  have := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback p E r
  rw [← chernCap_mk_eq_chernCapOnCycles, ← chernCap_mk_eq_chernCapOnCycles,
    ← properChowPushforward_mk C sX sY p hp k
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sX sY p hp k),
    chernCap_properPushforward C sX sY p hp E r ((Scheme.Modules.pullback p).obj E) (Iso.refl _)
      k j]

/-- **Stacks 02U8.** Let `f : X ⟶ Y` be a flat morphism of relative dimension `d` between schemes
locally of finite type over `S`, `ℰ` finite locally free of rank `r` on `Y` and `α` a `k`-cycle
on `Y`. Then `f^*(c_j(ℰ) ∩ α) = c_j(f^*ℰ) ∩ f^*α` in `A_{k+d-j}(X)`. The source takes `d = r`;
the relative dimension is arbitrary here. -/
@[stacks 02U8]
theorem flatPullbackChow_chernCapOnCycles {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Flat f] (hf : f ≫ sY = sX) (d : ℕ)
    (hd : AlgebraicGeometry.RelativeDimension f d) (E : Y.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (k : ℤ)
    (j : Fin (r + 1)) (α : CycleGroup C sY k) :
    haveI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback f E r
    flatPullbackChow C sX sY f hf d hd (k - (j : ℤ))
        (flatPullbackFactorsThroughRationalEquivalence_general C sX sY f hf d hd _)
        (chernCapOnCycles C sY E r k j α) =
      chowGroupCast C sX (by ring)
        (chernCapOnCycles C sX ((Scheme.Modules.pullback f).obj E) r (k + d) j
          (flatPullback C sX sY f hf d hd k α)) := by
  have := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback f E r
  rw [← chernCap_mk_eq_chernCapOnCycles, ← chernCap_mk_eq_chernCapOnCycles,
    ← flatPullbackChow_mk C sX sY f hf d hd k
      (flatPullbackFactorsThroughRationalEquivalence_general C sX sY f hf d hd k)]
  exact eq_of_heq ((chernCap_flatPullback_heq C sY sX f hf d hd E r
    ((Scheme.Modules.pullback f).obj E) (Iso.refl _) k j _ _ _).symm.trans
    (chowGroupCast_heq C sX _ _).symm)

end Stacks.Chow.GenuineChern

end
