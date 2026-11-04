module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.SegreClasses
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.SplittingTower
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.IteratedFirstChernCap

/-!
# Injectivity of flat pullback along a projective bundle, after base change

In Situation 0EDT let `X/B` be good, let `ℰ` be finite locally free of rank `r` on `X` and let
`(π : P ⟶ X, 𝒪_P(1))` be its projective bundle. The injectivity half of Stacks 0ERV says that
`π^* : CH_k(X) ⟶ CH_{k+r-1}(P)` is injective; its proof exhibits a left inverse,
`β ↦ π_*(c₁(𝒪_P(1))^{r-1} ∩ β)`, which is a left inverse because of the top-degree case of
Stacks 0ERU, `π_*(c₁(𝒪_P(1))^{r-1} ∩ π^*α) = α`. Since the projective bundle is compatible with
base change, the same holds for the base change `Y ×_X P ⟶ Y` along any morphism `Y ⟶ X` of good
algebraic spaces.

This file contains the formal part of that argument: a flat pullback of cycles has injective
class map on Chow groups as soon as it has a left inverse up to rational equivalence by a
homomorphism of cycle groups which respects rational equivalence, and the base change of a
proper morphism of good algebraic spaces along a morphism of good algebraic spaces is again a
good algebraic space.

## Main definitions

* `AlgebraicGeometry.Space.PrivateChern.topSegreCycle`: the homomorphism
  `β ↦ q_*(c₁(ℒ)^d ∩ β) : Z_{k+d}(Q) ⟶ Z_k(Y)` for `q : Q ⟶ Y` and `ℒ` invertible on `Q`.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.flatPullbackReflectsRationalEquivalence_of_leftInverse`:
  injectivity of flat pullback on Chow groups from a left inverse up to rational equivalence.
* `AlgebraicGeometry.Space.PrivateChern.isGood_pullback_of_isProper`: the fibre product
  `Y ×_X P` of good algebraic spaces along a proper `P ⟶ X` is good.
* `AlgebraicGeometry.Space.PrivateChern.hasInjectiveChowBaseChange_of_leftInverse`: injectivity of
  flat pullback after every base change from left inverses on the fibre products.
* `PrivateChern.eq_zero_of_isRationallyEquivalentToZero_of_deltaDimension_ne`: without integral
  closed subspaces of δ-dimension `k + 1` the only `k`-cycle rationally equivalent to zero is `0`;
  for instance in the top dimension of an integral space.
* `AlgebraicGeometry.Space.PrivateChern.hasInjectiveChowBaseChange_of_topSegre`: injectivity of
  flat pullback after every base change along a proper flat `π : P ⟶ X` with an invertible
  `ℒ` on `P`, from three statements on every fibre product `q : Y ×_X P ⟶ Y`: Stacks 0EQY for
  the pulled back `ℒ`, Stacks 0EQC for `q`, and the top-degree case of Stacks 0ERU.
* `AlgebraicGeometry.Space.PrivateChern.isRationallyEquivalentToZero_iteratedFirstChernCapCycle`:
  an iterated cap product with first Chern classes carries cycles rationally equivalent to zero
  to cycles rationally equivalent to zero as soon as each single cap product does (Stacks 0EQY
  for each factor).

## References

* [Stacks Project, Tag 0ERV](https://stacks.math.columbia.edu/tag/0ERV)
* [Stacks Project, Tag 0ERU](https://stacks.math.columbia.edu/tag/0ERU)
* [Stacks Project, Tag 0EPD](https://stacks.math.columbia.edu/tag/0EPD)
* W. Fulton, *Intersection theory*, Theorem 3.3.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.Space.PrivateChern

variable (D : BaseSpaceDimensionSituation.{u})

/-- **Injectivity of flat pullback on Chow groups from a left inverse.** Let `q : Q ⟶ Y` be a
flat morphism of good algebraic spaces of relative dimension `d`, and let
`Ψ : Z_n(Q) ⟶ Z_k(Y)`, for `k + d = n`, be homomorphisms carrying cycles rationally equivalent to
zero to cycles rationally equivalent to zero, with `Ψ(q^*α) ∼_rat α` for every `α ∈ Z_k(Y)`.
Then `q^* : CH_k(Y) ⟶ CH_{k+d}(Q)` is injective. -/
theorem flatPullbackReflectsRationalEquivalence_of_leftInverse
    {Q Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sQ : Q ⟶ D.space) (hQ : D.IsGood sQ) (sY : Y ⟶ D.space) (hY : D.IsGood sY) (q : Q ⟶ Y)
    (hq : q ≫ sY = sQ) (d : ℕ) (hflat : IsFlat D.site D.base D.base_mem q)
    (hd : HasRelativeDimension d D.site D.base D.base_mem q)
    (Ψ : ∀ k n : ℤ, k + (d : ℤ) = n → CycleGroup D sQ n →+ CycleGroup D sY k)
    (hΨ : ∀ (k n : ℤ) (hkn : k + (d : ℤ) = n) (β : CycleGroup D sQ n),
      IsRationallyEquivalentToZero.{v} D sQ hQ n β →
        IsRationallyEquivalentToZero.{v} D sY hY k (Ψ k n hkn β))
    (hleft : ∀ (k n : ℤ) (hkn : k + (d : ℤ) = n) (α : CycleGroup D sY k),
      IsRationallyEquivalentToZero.{v} D sY hY k
        (Ψ k n hkn (flatPullbackMap D sQ hQ sY hY q hq d hflat hd k n hkn α) - α)) :
    FlatPullbackReflectsRationalEquivalence.{v} D sQ hQ sY hY q hq d hflat hd := by
  intro k n hkn α h
  have h₁ := hΨ k n hkn _ h
  have h₂ := hleft k n hkn α
  have hα : α = Ψ k n hkn (flatPullbackMap D sQ hQ sY hY q hq d hflat hd k n hkn α) -
      (Ψ k n hkn (flatPullbackMap D sQ hQ sY hY q hq d hflat hd k n hkn α) - α) := by abel
  rw [hα]
  exact (rationalEquivalences.{v} D sY hY k).sub_mem h₁ h₂

/-- The first projection of the fibre product along a proper morphism is proper. -/
private theorem isProper_fst_of_isProper
    {X P Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (hP : IsAlgebraicSpace D.site D.base D.base_mem P)
    (hY : IsAlgebraicSpace D.site D.base D.base_mem Y) (π : P ⟶ X)
    (hπ : IsProper D.site D.base D.base_mem π) (f : Y ⟶ X)
    (hQ : IsAlgebraicSpace D.site D.base D.base_mem (pullback f π)) :
    IsProper D.site D.base D.base_mem (pullback.fst f π) :=
  isProper_of_isPullback D.site D.base D.base_mem hQ hP hY hX
    (IsPullback.of_hasPullback f π).flip hπ

/-- **The base change of a proper morphism to a good space is good.** For `π : P ⟶ X` proper with
`P` an algebraic space, `X` good, and `f : Y ⟶ X` a morphism over `B` from a good algebraic
space, the fibre product `Y ×_X P` is a good algebraic space over `B`, its structure morphism
being that of `Y` after the first projection. -/
theorem isGood_pullback_of_isProper
    {X P Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (hP : IsAlgebraicSpace D.site D.base D.base_mem P) (π : P ⟶ X)
    (hπ : IsProper D.site D.base D.base_mem π) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : Y ⟶ X) :
    D.IsGood (pullback.fst f π ≫ sY) := by
  have hQ : IsAlgebraicSpace D.site D.base D.base_mem (pullback f π) :=
    isAlgebraicSpace_pullback D.site D.base D.base_mem f π hY.1 hP hX.1
  have hq := isProper_fst_of_isProper D hX.1 hP hY.1 π hπ f hQ
  exact ⟨hQ,
    isQuasiSeparated_comp D.site D.base D.base_mem hQ hY.1 _ sY
      (isQuasiSeparated_of_isSeparated D.site D.base D.base_mem hq.1) hY.2.1,
    isLocallyOfFiniteType_comp' D.site D.base D.base_mem _ sY hY.1 D.isAlgebraicSpace
      hq.2.1.1 hY.2.2⟩

/-- **Injectivity of flat pullback after every base change, from left inverses.** Let
`π : P ⟶ X` be a proper flat morphism of good algebraic spaces of relative dimension `d`.
Suppose that for every morphism `f : Y ⟶ X` from a good algebraic space over `B`, the
projection `q : Y ×_X P ⟶ Y` admits homomorphisms `Ψ : Z_{k+d}(Y ×_X P) ⟶ Z_k(Y)` respecting
rational equivalence with `Ψ(q^*α) ∼_rat α`. Then the flat pullback along `π` is injective on
Chow groups after every base change. -/
theorem hasInjectiveChowBaseChange_of_leftInverse
    {X P : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sP : P ⟶ D.space) (hP : D.IsGood sP) (π : P ⟶ X) (hπP : π ≫ sX = sP)
    (hπ : IsProper D.site D.base D.base_mem π) (d : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem π)
    (hd : HasRelativeDimension d D.site D.base D.base_mem π)
    (h : ∀ ⦃Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u⦄ (sY : Y ⟶ D.space)
      (hY : D.IsGood sY) (f : Y ⟶ X) (_ : f ≫ sX = sY)
      (hflatq : IsFlat D.site D.base D.base_mem (pullback.fst f π))
      (hdq : HasRelativeDimension d D.site D.base D.base_mem (pullback.fst f π)),
      ∃ (Ψ : ∀ k n : ℤ, k + (d : ℤ) = n →
          CycleGroup D (pullback.fst f π ≫ sY) n →+ CycleGroup D sY k),
        (∀ (k n : ℤ) (hkn : k + (d : ℤ) = n) (β : CycleGroup D (pullback.fst f π ≫ sY) n),
          IsRationallyEquivalentToZero.{v} D (pullback.fst f π ≫ sY)
              (isGood_pullback_of_isProper D sX hX hP.1 π hπ sY hY f) n β →
            IsRationallyEquivalentToZero.{v} D sY hY k (Ψ k n hkn β)) ∧
        ∀ (k n : ℤ) (hkn : k + (d : ℤ) = n) (α : CycleGroup D sY k),
          IsRationallyEquivalentToZero.{v} D sY hY k
            (Ψ k n hkn (flatPullbackMap D (pullback.fst f π ≫ sY)
              (isGood_pullback_of_isProper D sX hX hP.1 π hπ sY hY f) sY hY
              (pullback.fst f π) rfl d hflatq hdq k n hkn α) - α)) :
    HasInjectiveChowBaseChange.{v} D sX π d := by
  intro Y sY hY f hf
  have hQ := isGood_pullback_of_isProper D sX hX hP.1 π hπ sY hY f
  have sq : IsPullback (pullback.snd f π) (pullback.fst f π) π f :=
    (IsPullback.of_hasPullback f π).flip
  have hbc := isFlat_and_hasRelativeDimension_of_isPullback D (pullback.fst f π ≫ sY) hQ
    sY hY sP hP sX hX rfl hπP sq.flip d hflat hd
  obtain ⟨Ψ, hΨ, hleft⟩ := h sY hY f hf hbc.2.1 hbc.2.2
  exact ⟨pullback f π, pullback.fst f π ≫ sY, hQ, pullback.snd f π, pullback.fst f π, sq, rfl,
    hbc.2.1, hbc.2.2,
    flatPullbackReflectsRationalEquivalence_of_leftInverse D _ hQ sY hY _ rfl d _ _ Ψ hΨ hleft⟩

/-- **No rational equivalences without subspaces one dimension up.** If no integral closed
subspace of `Y` has δ-dimension `k + 1`, then a `k`-cycle on `Y` rationally equivalent to zero is
zero: it is a sum of principal divisors on integral closed subspaces of δ-dimension `k + 1`, and
there are none. -/
theorem eq_zero_of_isRationallyEquivalentToZero_of_deltaDimension_ne
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (k : ℤ)
    (hdim : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem Y,
      deltaDimension D sY W ≠ k + 1)
    {α : CycleGroup D sY k} (hα : IsRationallyEquivalentToZero.{v} D sY hY k α) : α = 0 := by
  obtain ⟨J, W, hWfin, c, hWdim, -, rfl⟩ := hα
  have : IsEmpty J := ⟨fun j => hdim (W j) (hWdim j)⟩
  exact Subtype.ext (funext fun Z => by
    rw [cycleFamilySum_apply, finsum_of_isEmpty]
    rfl)

/-- Reindexing a cycle along an equality of degrees preserves rational equivalence to zero. -/
theorem isRationallyEquivalentToZero_cycleGroupCast
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) {a b : ℤ} (h : a = b) {α : CycleGroup D sX a}
    (hα : IsRationallyEquivalentToZero.{v} D sX hX a α) :
    IsRationallyEquivalentToZero.{v} D sX hX b (cycleGroupCast D sX h α) := by
  subst h
  exact hα

/-- **Iterated cap products respect rational equivalence factorwise.** If for every
`ℒ_j` the cap product `c₁(ℒ_j) ∩ -` at the canonical choices carries cycles rationally
equivalent to zero to cycles rationally equivalent to zero (Stacks 0EQY), then so does the
iterated cap product `c₁(ℒ₁) ∩ ⋯ ∩ c₁(ℒ_d) ∩ - : Z_{k+d}(X) ⟶ Z_k(X)`. -/
theorem isRationallyEquivalentToZero_iteratedFirstChernCapCycle
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) :
    ∀ (d : ℕ) (L : Fin d → Modules.{u, u} D.site D.base D.base_mem X hX.1)
      (hL : ∀ j, IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)
        (L j)),
      (∀ (j : Fin d) (k : ℤ) (α : CycleGroup D sX (k + 1)),
        IsRationallyEquivalentToZero.{v} D sX hX (k + 1) α →
          IsRationallyEquivalentToZero.{v} D sX hX k
            (firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX (L j) (hL j) k)
              α)) →
      ∀ (k : ℤ) (α : CycleGroup D sX (k + d)),
        IsRationallyEquivalentToZero.{v} D sX hX (k + d) α →
          IsRationallyEquivalentToZero.{v} D sX hX k
            (iteratedFirstChernCapCycle D sX hX d L hL k α)
  | 0, L, hL, _, k, α, hα => isRationallyEquivalentToZero_cycleGroupCast D sX hX _ hα
  | d + 1, L, hL, hcap, k, α, hα => by
    rw [iteratedFirstChernCapCycle_succ]
    refine isRationallyEquivalentToZero_iteratedFirstChernCapCycle sX hX d (Fin.init L)
      (fun j => hL _) (fun j k α hα => hcap (Fin.castSucc j) k α hα) k _ ?_
    exact hcap (Fin.last d) (k + d) _
      (isRationallyEquivalentToZero_cycleGroupCast D sX hX _ hα)

/-- **The top Segre operation on cycles**: for `q : Q ⟶ Y` quasi-compact between good algebraic
spaces and `ℒ` invertible on `Q`, the homomorphism
`β ↦ q_*(c₁(ℒ)^d ∩ β) : Z_n(Q) ⟶ Z_k(Y)`, `k + d = n`, the cap products being taken at the
canonical choices. For the projective bundle of a module of rank `d + 1` and `ℒ = 𝒪_P(1)` it is
the left inverse of `q^*` of Stacks 0ERU. -/
def topSegreCycle {Q Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sQ : Q ⟶ D.space) (hQ : D.IsGood sQ) (sY : Y ⟶ D.space) (hY : D.IsGood sY) {q : Q ⟶ Y}
    (hq : q ≫ sY = sQ) (hqc : IsQuasiCompact D.site D.base D.base_mem q)
    (L : Modules.{u, u} D.site D.base D.base_mem Q hQ.1)
    (hL : IsInvertibleModule (⟨Q, hQ.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L) (d : ℕ)
    (k n : ℤ) (h : k + (d : ℤ) = n) : CycleGroup D sQ n →+ CycleGroup D sY k :=
  (properCyclePushforward D sQ hQ sY hY hq hqc k).comp
    ((iteratedFirstChernCapCycle D sQ hQ d (fun _ => L) (fun _ => hL) k).comp
      (cycleGroupCast D sQ h.symm))

/-- The top Segre operation respects rational equivalence as soon as the cap product with `ℒ`
does (Stacks 0EQY) and the pushforward along `q` does (Stacks 0EQC). -/
theorem isRationallyEquivalentToZero_topSegreCycle
    {Q Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sQ : Q ⟶ D.space) (hQ : D.IsGood sQ) (sY : Y ⟶ D.space) (hY : D.IsGood sY) {q : Q ⟶ Y}
    (hq : q ≫ sY = sQ) (hqc : IsQuasiCompact D.site D.base D.base_mem q)
    (L : Modules.{u, u} D.site D.base D.base_mem Q hQ.1)
    (hL : IsInvertibleModule (⟨Q, hQ.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L) (d : ℕ)
    (hcap : ∀ (k : ℤ) (α : CycleGroup D sQ (k + 1)),
      IsRationallyEquivalentToZero.{v} D sQ hQ (k + 1) α →
        IsRationallyEquivalentToZero.{v} D sQ hQ k
          (firstChernCapCycleMap D sQ hQ k (canonicalFirstChernRule D sQ hQ L hL k) α))
    (hpush : ∀ (k : ℤ) (β : CycleGroup D sQ k), IsRationallyEquivalentToZero.{v} D sQ hQ k β →
      IsRationallyEquivalentToZero.{v} D sY hY k (properCyclePushforward D sQ hQ sY hY hq hqc k β))
    (k n : ℤ) (h : k + (d : ℤ) = n) (β : CycleGroup D sQ n)
    (hβ : IsRationallyEquivalentToZero.{v} D sQ hQ n β) :
    IsRationallyEquivalentToZero.{v} D sY hY k
      (topSegreCycle D sQ hQ sY hY hq hqc L hL d k n h β) :=
  hpush k _ (isRationallyEquivalentToZero_iteratedFirstChernCapCycle D sQ hQ d _ _
    (fun _ => hcap) k _ (isRationallyEquivalentToZero_cycleGroupCast D sQ hQ h.symm hβ))

/-- **Injectivity of flat pullback after every base change from the top Segre operation.** Let
`π : P ⟶ X` be a proper flat morphism of good algebraic spaces of relative dimension `d` and let
`ℒ` be invertible on `P`. Suppose that along every morphism `f : Y ⟶ X` from a good algebraic
space over `B`, for the projections `q : Y ×_X P ⟶ Y`, `p : Y ×_X P ⟶ P`:

* the cap product with `p^*ℒ` respects rational equivalence on `Y ×_X P` (Stacks 0EQY),
* the pushforward along `q` respects rational equivalence (Stacks 0EQC), and
* `q_*(c₁(p^*ℒ)^d ∩ q^*α) ∼_rat α` for every cycle `α` on `Y` (Stacks 0ERU, top degree).

Then the flat pullback along `π` is injective on Chow groups after every base change. -/
theorem hasInjectiveChowBaseChange_of_topSegre
    {X P : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sP : P ⟶ D.space) (hP : D.IsGood sP) (π : P ⟶ X) (hπP : π ≫ sX = sP)
    (hπ : IsProper D.site D.base D.base_mem π) (d : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem π)
    (hd : HasRelativeDimension d D.site D.base D.base_mem π)
    (L : Modules.{u, u} D.site D.base D.base_mem P hP.1)
    (hL : IsInvertibleModule (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (h : ∀ ⦃Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u⦄ (sY : Y ⟶ D.space)
      (hY : D.IsGood sY) (f : Y ⟶ X) (_ : f ≫ sX = sY)
      (hQ : D.IsGood (pullback.fst f π ≫ sY))
      (hqc : IsQuasiCompact D.site D.base D.base_mem (pullback.fst f π))
      (hflatq : IsFlat D.site D.base D.base_mem (pullback.fst f π))
      (hdq : HasRelativeDimension d D.site D.base D.base_mem (pullback.fst f π)),
      let p : (⟨pullback f π, hQ.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨P, hP.1⟩ :=
        ObjectProperty.homMk (pullback.snd f π)
      let hLQ := modulePullbackInvertible p L hL
      (∀ (k : ℤ) (α : CycleGroup D (pullback.fst f π ≫ sY) (k + 1)),
        IsRationallyEquivalentToZero.{v} D (pullback.fst f π ≫ sY) hQ (k + 1) α →
          IsRationallyEquivalentToZero.{v} D (pullback.fst f π ≫ sY) hQ k
            (firstChernCapCycleMap D (pullback.fst f π ≫ sY) hQ k
              (canonicalFirstChernRule D (pullback.fst f π ≫ sY) hQ
                ((modulePullback D.site D.base D.base_mem p).obj L) hLQ k) α)) ∧
      (∀ (k : ℤ) (β : CycleGroup D (pullback.fst f π ≫ sY) k),
        IsRationallyEquivalentToZero.{v} D (pullback.fst f π ≫ sY) hQ k β →
          IsRationallyEquivalentToZero.{v} D sY hY k
            (properCyclePushforward D (pullback.fst f π ≫ sY) hQ sY hY rfl hqc k β)) ∧
      ∀ (k n : ℤ) (hkn : k + (d : ℤ) = n) (α : CycleGroup D sY k),
        IsRationallyEquivalentToZero.{v} D sY hY k
          (topSegreCycle D (pullback.fst f π ≫ sY) hQ sY hY rfl hqc
              ((modulePullback D.site D.base D.base_mem p).obj L) hLQ d k n hkn
              (flatPullbackMap D (pullback.fst f π ≫ sY) hQ sY hY (pullback.fst f π) rfl d
                hflatq hdq k n hkn α) - α)) :
    HasInjectiveChowBaseChange.{v} D sX π d := by
  refine hasInjectiveChowBaseChange_of_leftInverse D sX hX sP hP π hπP hπ d hflat hd ?_
  intro Y sY hY f hf hflatq hdq
  have hQ := isGood_pullback_of_isProper D sX hX hP.1 π hπ sY hY f
  have hqc : IsQuasiCompact D.site D.base D.base_mem (pullback.fst f π) :=
    (isProper_fst_of_isProper D hX.1 hP.1 hY.1 π hπ f hQ.1).2.1.2
  obtain ⟨hcap, hpush, htop⟩ := h sY hY f hf hQ hqc hflatq hdq
  exact ⟨_, fun k n hkn β hβ => isRationallyEquivalentToZero_topSegreCycle D _ hQ sY hY rfl hqc
    _ _ d hcap hpush k n hkn β hβ, htop⟩

end AlgebraicGeometry.Space.PrivateChern

end
