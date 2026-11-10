module

public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsSerreOneAlternativeHypotheses
public import StacksFrontier.AlgebraicGeometry.FormalSectionsAlgebraization.DegreeZeroAdicLimit
public import StacksFrontier.AlgebraicGeometry.FormalSectionsAlgebraization.HigherDegreeAdicLimit

/-!
# The hypotheses of Stacks 0EG4 are those of Stacks 0EFL for `s + 1`

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, let `U = Spec(A) ∖ V(𝔞)`, let `F` be a coherent
module on `U` and `s ≥ 0`. Stacks 0EG4 assumes

1. `A` is `I`-adically complete and has a dualizing complex,
2. for `x ∈ U ∖ V(I)`, `depth(F_x) > s` or
   `depth(F_x) + dim(𝒪_{closure {x}, z}) > cd(A, I) + s + 1` for all `z ∈ V(𝔞) ∩ closure {x}`
   (`Stacks.Algebraization.SourceSheafDepthHypothesis`),
3. the restriction of `F` to `U ∖ V(I)` is `(S_{s+1})`, or the dimension of `V(𝔞)` is at most `2`
   (`Stacks.Algebraization.SourceSerreOrDimensionHypothesis`).

Its proof writes `F = M̃|_U` for a finite `A`-module `M` (Stacks 0BK0) and applies Stacks 0EFL to
`M`, `J = 𝔞`, `s + 1` and `d = cd(A, I)`. This file proves that the hypotheses of Stacks 0EFL hold
there.

## Main definitions

* `Stacks.Algebraization.SourceSerreOrDimensionHypothesis` — hypothesis (3) of Stacks 0EG4.

## Main results

* `Stacks.Algebraization.sourceDepthHypothesis_of_sourceSheafDepthHypothesis` — hypothesis (2)
  for `F ≅ M̃|_U` is its module form `Stacks.Algebraization.SourceDepthHypothesis` for `M`.
* `Stacks.Algebraization.algebraizationHypotheses_of_sourceHypotheses` — hypotheses (1), (2) and
  (3) give the hypotheses of Stacks 0EFL for `M`, `J = 𝔞`, `s + 1` and `d = cd(A, I)`.

## Implementation notes

Hypothesis (3)(a) is Serre's condition `AlgebraicGeometry.SheafHasPropertySk` for the
restriction of `F` to `U ∖ V(I)`, exactly as condition (3)(a) of Stacks 0EIF
(`Stacks.Algebraization.IsSerreOneOffVanishing`) is for `k = 1`. Hypothesis (3)(b) is the source's
footnote, which is `Stacks.Algebraization.VanishingLocusDimensionAtMostTwo`, shared with
Stacks 0EIF.

The dimension function of Stacks 0EFL is chosen according to the alternative. Under (3)(b) it is
the function that alternative provides, for which `δmax - δmin ≤ 2` on `V(𝔞)`, so condition (5)
follows from condition (4). Under (3)(a) the first alternative of condition (5) holds at every
relevant prime, and the dimension function of the dualizing complex is taken.

## References

* [Stacks Project, Tag 0EG4](https://stacks.math.columbia.edu/tag/0EG4)
* [Stacks Project, Tag 0EFL](https://stacks.math.columbia.edu/tag/0EFL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology Stacks.AlgebraicGeometry.ReflexiveModules

/-- **Hypothesis (3) of Stacks 0EG4.** Either the restriction of `F` to `U ∖ V(I)` satisfies
Serre's condition `(S_{s+1})`, or the dimension of `V(𝔞)` is at most `2` in the sense of the
source's footnote: some dimension function on `Spec(A)` varies by at most `2` on `V(𝔞)`. -/
public def SourceSerreOrDimensionHypothesis (A : Type u) [CommRing A] (I a : Ideal A)
    (F : (complementZeroLocus A a : Scheme).Modules) (s : ℕ) : Prop :=
  SheafHasPropertySk (opensOffVanishing A I a).toScheme
      ((Scheme.Modules.restrictFunctor (opensOffVanishing A I a).ι).obj F) (s + 1) ∨
    VanishingLocusDimensionAtMostTwo A a

/-- A value of `enatToEInt` above an integer `s` is at least `s + 1`. -/
private theorem add_one_le_enatToEInt_of_lt {n : ℕ∞} {s : ℤ} (h : (s : EInt) < enatToEInt n) :
    ((s + 1 : ℤ) : EInt) ≤ enatToEInt n := by
  induction n using ENat.recTopCoe with
  | top => exact le_top
  | coe k =>
    change ((s : ℤ) : EInt) < ((k : ℤ) : EInt) at h
    change ((s + 1 : ℤ) : EInt) ≤ ((k : ℤ) : EInt)
    exact WithBotTop.coe_le_coe.2 (by have := WithBotTop.coe_lt_coe.1 h; omega)

/-- A value of `enatToEInt` below `s + 1` comes from a depth at most `s`. -/
private theorem le_of_enatToEInt_lt_add_one {n : ℕ∞} {s : ℕ}
    (h : enatToEInt n < (((s : ℤ) + 1 : ℤ) : EInt)) : n ≤ (s : ℕ∞) := by
  induction n using ENat.recTopCoe with
  | top => exact absurd h (not_lt.2 le_top)
  | coe k =>
    change ((k : ℤ) : EInt) < (((s : ℤ) + 1 : ℤ) : EInt) at h
    exact Nat.cast_le.2 (by have := WithBotTop.coe_lt_coe.1 h; omega)

/-- A prime outside `V(I)` is a point of `U = Spec(A) ∖ V(𝔞)`, since `I ⊆ 𝔞`. -/
private theorem mem_complementZeroLocus_of_notMem_zeroLocus {A : Type u} [CommRing A]
    {I a : Ideal A} (hIa : I ≤ a) {p : PrimeSpectrum A}
    (hp : p ∉ PrimeSpectrum.zeroLocus (I : Set A)) : p ∈ complementZeroLocus A a :=
  fun hpa => hp ((PrimeSpectrum.zeroLocus_anti_mono (SetLike.coe_subset_coe.2 hIa)) hpa)

section Hypotheses

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I a : Ideal A} (hIa : I ≤ a)
  {F : (complementZeroLocus A a : Scheme).Modules} {M : ModuleCat.{u} A}
  [Module.Finite A M]
  (e : F ≅ (Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι).obj
    ((tilde.functor (CommRingCat.of A)).obj M))

omit [Module.Finite A M] in
include hIa e in
/-- **Hypothesis (2) of Stacks 0EG4 in module form.** For `F ≅ M̃|_U`, the sheaf form
`Stacks.Algebraization.SourceSheafDepthHypothesis` of hypothesis (2) is the module form
`Stacks.Algebraization.SourceDepthHypothesis` for `M`: at a prime `𝔭 ∉ V(I)`, which is a point of
`U` since `I ⊆ 𝔞`, the stalk of `F` has the depth of `M_𝔭`, and `dim(𝒪_{closure {𝔭}, 𝔮})` is
`dim((A/𝔭)_𝔮)`. -/
public theorem sourceDepthHypothesis_of_sourceSheafDepthHypothesis (s : ℤ)
    (h : SourceSheafDepthHypothesis A I a F s) : SourceDepthHypothesis I a M s := by
  intro p hpI
  let x : (complementZeroLocus A a : Scheme) :=
    ⟨p, mem_complementZeroLocus_of_notMem_zeroLocus hIa hpI⟩
  have hd := depth_stalk_eq_depth_localizedModule_of_iso e x p rfl
  rcases h x hpI with h1 | h1
  · left
    rwa [hd] at h1
  · right
    intro q hpq hqa
    have h2 := h1 q hpq hqa
    rw [hd] at h2
    rwa [closureLocalDimension_eq_ringKrullDim_quotient_localizationAtPrime] at h2

include hIa e in
/-- **The hypotheses of Stacks 0EG4 give those of Stacks 0EFL for `s + 1`.** Let `I ⊆ 𝔞` be
ideals of a Noetherian ring `A`, let `F ≅ M̃|_U` be a module on `U = Spec(A) ∖ V(𝔞)`
with `M` a finite `A`-module, let `s ≥ 0`, and assume hypotheses (1), (2) and (3) of
Stacks 0EG4 with `V(𝔞)` nonempty. Then there are a dualizing complex `ω`, a dimension function `δ`
on `Spec(A)` and its maximum and minimum on `V(𝔞) ∩ V(I)` for which `M`, `J = 𝔞`, `s + 1` and
`d = cd(A, I)` satisfy the hypotheses of Stacks 0EFL.

Condition (4) of Stacks 0EFL is hypothesis (2), read on `M` by
`Stacks.Algebraization.sourceDepthHypothesis_of_sourceSheafDepthHypothesis`. In condition (5),
at a prime of depth at most `s`: under `(S_{s+1})` the support of `M_𝔭` has dimension at most its
depth, hence less than `s + 3`; under the dimension alternative `δmax - δmin ≤ 2`, and the third
alternative is weaker than the second alternative of hypothesis (2). -/
public theorem algebraizationHypotheses_of_sourceHypotheses (s : ℕ)
    (hcomplete : IsAdicComplete I A)
    (hdualizing : ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K)
    (h2 : SourceSheafDepthHypothesis A I a F s) (h3 : SourceSerreOrDimensionHypothesis A I a F s)
    (hne : (PrimeSpectrum.zeroLocus (a : Set A)).Nonempty) :
    ∃ (omega : DerivedCategory (ModuleCat.{u} A)) (δ : PrimeSpectrum A → ℤ) (δmax δmin : ℤ),
      AlgebraizationHypotheses (M := M) I a ((s : ℤ) + 1)
        (cohomologicalDimension A I I.fg_of_isNoetherianRing) omega δ δmax δmin := by
  obtain ⟨omega, homega⟩ := hdualizing
  have hA := Dualizing.ringKrullDim_lt_top_of_isDualizingComplex homega
  have hVne : (PrimeSpectrum.zeroLocus (a : Set A) ∩
      PrimeSpectrum.zeroLocus (I : Set A)).Nonempty := by
    obtain ⟨q, hq⟩ := hne
    exact ⟨q, hq, PrimeSpectrum.zeroLocus_anti_mono (SetLike.coe_subset_coe.2 hIa) hq⟩
  have hM := sourceDepthHypothesis_of_sourceSheafDepthHypothesis hIa e s h2
  obtain ⟨δ', hδ'⟩ : ∃ δ' : DimensionFunction (PrimeSpectrum A),
      ¬ SheafHasPropertySk (opensOffVanishing A I a).toScheme
        ((Scheme.Modules.restrictFunctor (opensOffVanishing A I a).ι).obj F) (s + 1) →
        ∀ x z : PrimeSpectrum A, a ≤ x.asIdeal → a ≤ z.asIdeal → δ' x ≤ δ' z + 2 := by
    rcases h3 with h3 | ⟨δ, hδ⟩
    · exact ⟨Dualizing.dualizingDimensionFunctionOfArbitraryUniverse omega homega,
        fun hn => absurd h3 hn⟩
    · exact ⟨δ, fun _ => hδ⟩
  obtain ⟨⟨δmax, hmax⟩, ⟨δmin, hmin⟩⟩ :=
    exists_isGreatest_isLeast_image_dimensionFunction hA δ' hVne
  refine ⟨omega, δ'.toFun, δmax, δmin,
    { adicComplete := hcomplete
      dualizing := homega
      cohomologicalDimension_le := le_rfl
      depthOrDimensionBound := ?_
      isDimensionFunction := isDimensionFunctionProp_toFun δ'
      isGreatest_δmax := hmax
      isLeast_δmin := hmin
      supplementaryBound := ?_ }⟩
  · intro p hpI _
    rcases hM p hpI with h1 | h1
    · exact Or.inl (add_one_le_enatToEInt_of_lt h1)
    · right
      rintro q ⟨⟨hqp, hqa⟩, -⟩
      refine lt_of_le_of_lt (le_of_eq (congrArg (fun n : ℤ => (n : EInt)) (by ring)))
        (h1 q hqp hqa)
  · intro p hpI _ _ hdlt
    have hdle := le_of_enatToEInt_lt_add_one hdlt
    have hnot : ¬ ((s : ℤ) : EInt) < enatToEInt (Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl M)) :=
      fun h => absurd (add_one_le_enatToEInt_of_lt h) (not_le.2 hdlt)
    by_cases hS : SheafHasPropertySk (opensOffVanishing A I a).toScheme
        ((Scheme.Modules.restrictFunctor (opensOffVanishing A I a).ι).obj F) (s + 1)
    · left
      let x : (complementZeroLocus A a : Scheme) :=
        ⟨p, mem_complementZeroLocus_of_notMem_zeroLocus hIa hpI⟩
      have hxW : x ∈ opensOffVanishing A I a :=
        (mem_opensOffVanishing A I a x).2 hpI
      let x' : (opensOffVanishing A I a).toScheme := ⟨x, hxW⟩
      have hk := min_supportDim_le_depth_of_sheafHasPropertySk _ (s + 1) hS x'
      have hdep := Scheme.Modules.depth_stalk_restrict (opensOffVanishing A I a).ι F x'
      have hsd := Scheme.Modules.supportDim_stalk_restrict (opensOffVanishing A I a).ι F x'
      have hdep' := depth_stalk_eq_depth_localizedModule_of_iso e
        ((opensOffVanishing A I a).ι.base x') p rfl
      have hsd' := supportDim_stalk_eq_supportDim_localizedModule_of_iso e
        ((opensOffVanishing A I a).ι.base x') p rfl
      rw [hdep, hsd, hdep', hsd'] at hk
      have hdleW : ((Module.depth (Localization.AtPrime p.asIdeal)
          (maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl M) : ℕ∞) : WithBot ℕ∞) ≤
          ((s : ℕ) : WithBot ℕ∞) := by
        exact_mod_cast hdle
      have hle : Module.supportDim (Localization.AtPrime p.asIdeal)
          (LocalizedModule p.asIdeal.primeCompl M) ≤ ((s : ℕ) : WithBot ℕ∞) := by
        rcases min_le_iff.1 hk with h1 | h1
        · exact absurd (h1.trans hdleW) (by exact_mod_cast Nat.not_succ_le_self s)
        · exact h1.trans hdleW
      refine lt_of_le_of_lt (krullDimToEInt_mono hle) ?_
      rw [krullDimToEInt_natCast]
      exact WithBotTop.coe_lt_coe.2 (by omega)
    · right; right
      intro q hq
      obtain ⟨⟨hqp, hqa⟩, -⟩ := hq
      have hb := (hM p hpI).resolve_left hnot q hqp hqa
      obtain ⟨z₁, ⟨hz₁a, -⟩, hz₁⟩ := hmax.1
      obtain ⟨z₂, ⟨hz₂a, -⟩, hz₂⟩ := hmin.1
      have hδ := hδ' hS z₁ z₂ hz₁a hz₂a
      change δ' z₁ = δmax at hz₁
      change δ' z₂ = δmin at hz₂
      refine lt_of_le_of_lt (WithBotTop.coe_le_coe.2 ?_) hb
      omega

end Hypotheses

end Stacks.Algebraization

end
