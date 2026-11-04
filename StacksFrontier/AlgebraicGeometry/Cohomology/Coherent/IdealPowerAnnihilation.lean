module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.TrivialDividedPowers
public import StacksFrontier.AlgebraicGeometry.Modules.IdealPowerMultiple
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.SchemeTheoretic
public import StacksFrontier.AlgebraicGeometry.NoetherianApproximation.Reduction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksCore.Tactic.StacksAttribute

/-!
# Coherent sheaves annihilated by a power of an ideal sheaf

Let `X` be a Noetherian scheme, `ℱ` a coherent `𝒪_X`-module and `ℐ ⊆ 𝒪_X` a quasi-coherent
sheaf of ideals, cutting out the closed subscheme `Z ⊆ X`. Then `ℐ ^ n ℱ = 0` for some `n ≥ 0`
exactly when the support of `ℱ` is contained in `Z`.

Both sides are comparisons of ideal sheaves in disguise. The annihilating side says that
`ℐ ^ n` is contained in the scheme-theoretic support of `ℱ`, the ideal sheaf whose component at
an affine open is the annihilator of the module of sections there. The support side says that
the closed set cut out by that ideal sheaf — which is exactly the support of `ℱ` — is contained
in `Z`, and by the Galois connection between ideal sheaves and closed sets this says that `ℐ` is
contained in the radical of the scheme-theoretic support. So the lemma reduces to the statement
that on a Noetherian scheme an ideal sheaf lies in the radical of another exactly when one of
its powers lies in the other, which is the affine statement `Ideal.exists_pow_le_of_le_radical`
glued over a finite affine covering.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.le_radical_of_pow_le` and
  `AlgebraicGeometry.Scheme.IdealSheafData.exists_pow_le_of_le_radical`, combined in
  `AlgebraicGeometry.Scheme.IdealSheafData.exists_pow_le_iff_le_radical`: on a quasi-compact
  scheme with Noetherian affine charts, `ℐ ^ n ⊆ 𝒥` for some `n` exactly when `ℐ` lies in the
  radical of `𝒥`.
* `AlgebraicGeometry.exists_idealPowerMultiple_eq_bot_iff_supp_subset`: a power of a
  quasi-coherent ideal sheaf annihilates a coherent module on a Noetherian scheme exactly when
  the support of the module lies in the closed subscheme cut out by the ideal sheaf.

## Implementation notes

The subsheaf `ℐ ^ n ℱ` is `Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple`, the least
subsheaf of `ℱ` containing `ℐ(U) ^ n ℱ(U)` on every affine open `U`; its vanishing is therefore
tested affine-locally, through `idealPowerMultiple_le_iff` and the fact that the zero subsheaf
has zero sections over every open.

Only quasi-compactness and Noetherianness of the affine charts are used in the ideal sheaf
lemmas, so those are stated with `CompactSpace` and `IsLocallyNoetherian` rather than with
`IsNoetherian`. The finite affine covering is the one supplied by
`AlgebraicGeometry.Scheme.exists_finite_affineOpens_sup_eq_top`, and the uniform exponent is the
supremum of the finitely many local ones.

## References

* [Stacks Project, Tag 00L6](https://stacks.math.columbia.edu/tag/00L6)
* [Stacks Project, Tag 01Y9](https://stacks.math.columbia.edu/tag/01Y9)
* [Stacks Project, Tag 05JU](https://stacks.math.columbia.edu/tag/05JU)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPower

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- If a power of an ideal sheaf is contained in another ideal sheaf, then the first is
contained in the radical of the second. -/
theorem le_radical_of_pow_le {X : Scheme.{u}} {I J : X.IdealSheafData} {n : ℕ}
    (h : I ^ n ≤ J) : I ≤ J.radical := fun U _ ha =>
  Ideal.mem_radical_iff.mpr ⟨n, h U (Ideal.pow_mem_pow ha n)⟩

/-- On a quasi-compact scheme whose affine charts are Noetherian, an ideal sheaf contained in
the radical of another has a power contained in it. The exponent is obtained from the affine
statement on each member of a finite affine covering, and the uniform exponent is their
supremum. -/
theorem exists_pow_le_of_le_radical {X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    {I J : X.IdealSheafData} (h : I ≤ J.radical) : ∃ n : ℕ, I ^ n ≤ J := by
  classical
  have key : ∀ U : X.affineOpens, ∃ n : ℕ, I.ideal U ^ n ≤ J.ideal U := by
    intro U
    have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    exact Ideal.exists_pow_le_of_le_radical_of_fg (h U) (IsNoetherian.noetherian _)
  choose m hm using key
  obtain ⟨k, A, hA⟩ := X.exists_finite_affineOpens_sup_eq_top ⊥
  refine ⟨Finset.univ.sup fun l : Fin k => m (A l), le_of_iSup_eq_top A (by simpa using hA) ?_⟩
  intro l
  exact (Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ l))).trans (hm (A l))

/-- On a quasi-compact scheme whose affine charts are Noetherian, a power of an ideal sheaf is
contained in another exactly when the first is contained in the radical of the second. -/
theorem exists_pow_le_iff_le_radical {X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    {I J : X.IdealSheafData} : (∃ n : ℕ, I ^ n ≤ J) ↔ I ≤ J.radical :=
  ⟨fun ⟨_, hn⟩ => le_radical_of_pow_le hn, exists_pow_le_of_le_radical⟩

/-- Two ideal sheaves cutting out the same closed subset have the same radical: the radical is
the vanishing ideal of the closed subset, by
`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_support`. -/
theorem radical_eq_radical_of_support_eq {X : Scheme.{u}} {I J : X.IdealSheafData}
    (h : I.support = J.support) : I.radical = J.radical := by
  rw [← vanishingIdeal_support (I := I), ← vanishingIdeal_support (I := J), h]

/-- An ideal sheaf raised to a positive power still decreases. -/
theorem pow_le_pow_of_le {X : Scheme.{u}} (I : X.IdealSheafData) {m n : ℕ} (h : n ≤ m) :
    I ^ m ≤ I ^ n := fun U => by
  rw [ideal_pow, ideal_pow]; exact Ideal.pow_le_pow_right h

/-- **[Stacks, Tag 0EHR]**, the elementary input. On a quasi-compact scheme with Noetherian
affine charts, two quasi-coherent ideal sheaves cutting out the same closed subset are cofinal in
one another: there are *positive* exponents `c` and `d` with `ℐ ^ c ⊆ 𝒥` and `𝒥 ^ d ⊆ ℐ`.

Positivity is what makes the two exponents usable as reindexings of an inverse system, and it is
free: a containment for one exponent gives one for every larger exponent. -/
theorem exists_pos_pow_le_and_pow_le_of_support_eq {X : Scheme.{u}} [IsLocallyNoetherian X]
    [CompactSpace X] {I J : X.IdealSheafData} (h : I.support = J.support) :
    ∃ c d : ℕ, 1 ≤ c ∧ 1 ≤ d ∧ I ^ c ≤ J ∧ J ^ d ≤ I := by
  have hrad : I.radical = J.radical := radical_eq_radical_of_support_eq h
  obtain ⟨c, hc⟩ := exists_pow_le_of_le_radical (I := I) (J := J)
    ((le_radical I).trans hrad.le)
  obtain ⟨d, hd⟩ := exists_pow_le_of_le_radical (I := J) (J := I)
    ((le_radical J).trans hrad.ge)
  exact ⟨c + 1, d + 1, Nat.le_add_left 1 c, Nat.le_add_left 1 d,
    (pow_le_pow_of_le I (Nat.le_succ c)).trans hc,
    (pow_le_pow_of_le J (Nat.le_succ d)).trans hd⟩

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry

/-- The subsheaf `ℐ ^ n ℱ` is zero exactly when `ℐ(U) ^ n ℱ(U)` is zero for every affine open
`U`: the subsheaf is the least one containing those submodules, and the zero subsheaf has zero
sections over every open. -/
lemma idealPowerMultiple_eq_bot_iff {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ)
    (F : X.Modules) :
    idealPowerMultiple I n F = ⊥ ↔
      ∀ U : X.affineOpens, I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1)) = ⊥ := by
  rw [← le_bot_iff, idealPowerMultiple_le_iff]
  refine forall_congr' fun U => ⟨fun hU => ?_, fun hU => ?_⟩
  · exact le_bot_iff.mp (hU.trans (SheafOfModules.Submodule.bot_obj F (op U.1)).le)
  · exact hU.le.trans (SheafOfModules.Submodule.bot_obj F (op U.1)).ge

/-- A power of an ideal sheaf annihilates a quasi-coherent module of finite type exactly when
that power is contained in the scheme-theoretic support of the module. -/
lemma idealPowerMultiple_eq_bot_iff_pow_le_schemeTheoreticSupport {X : Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    idealPowerMultiple I n F = ⊥ ↔ I ^ n ≤ Scheme.Modules.schemeTheoreticSupport F := by
  rw [idealPowerMultiple_eq_bot_iff, Scheme.IdealSheafData.le_def]
  refine forall_congr' fun U => ?_
  show _ ↔ I.ideal U ^ n ≤ (Scheme.Modules.schemeTheoreticSupport F).ideal U
  rw [Scheme.Modules.schemeTheoreticSupport_ideal, ← Submodule.annihilator_top,
    Submodule.le_annihilator_iff]

/-- **Stacks Project, Tag 01Y9.** Let `ℱ` be a coherent module on a Noetherian scheme `X` and
let `ℐ ⊆ 𝒪_X` be a quasi-coherent sheaf of ideals, cutting out the closed subscheme
`Z ⊆ X`. Then some power of `ℐ` annihilates `ℱ` if and only if the support of `ℱ` is contained
in `Z`. -/
@[stacks 01Y9, ega "I 9.3.4"]
theorem exists_idealPowerMultiple_eq_bot_iff_supp_subset {X : Scheme.{u}} [IsNoetherian X]
    (F : X.Modules) [F.IsCoherent] (I : X.IdealSheafData) :
    (∃ n : ℕ, idealPowerMultiple I n F = ⊥) ↔
      SheafOfModules.supp F ⊆ (I.support : Set X) := by
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have : F.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType (M := F)
  rw [Scheme.Modules.supp_eq_support_schemeTheoreticSupport F, SetLike.coe_subset_coe,
    Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal,
    Scheme.IdealSheafData.vanishingIdeal_support,
    ← Scheme.IdealSheafData.exists_pow_le_iff_le_radical]
  exact exists_congr fun n =>
    idealPowerMultiple_eq_bot_iff_pow_le_schemeTheoreticSupport I n F

end AlgebraicGeometry

end
