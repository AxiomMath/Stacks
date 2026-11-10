module

public import StacksFrontier.AlgebraicGeometry.Chow.SecondAdamsProductRelation
public import StacksFrontier.AlgebraicGeometry.Chow.VectorBundleKZeroPullback
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.TotalChernClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.WeakChernClasses.CohomologicalChernCharacter
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.WeakChernClasses.InvertibleTensor
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.WeakChernClasses.SplittingPrinciple

/-!
# The second Adams operator scales the cohomological Chern character, in the weak situation

Tag 0FIA says that in the standing situation of Section 45.12 the second Adams operator `ψ²` of
Tag 0FEJ satisfies `ch^A_i(ψ²(α)) = 2^i ch^A_i(α)` for all `α ∈ K₀(Vect(X))`. The standing
situation through which Tag 0FIE is proved is the weak one,
`Stacks.WeilCohomology.Weak.ChernSetup` (see
`StacksFrontier.AlgebraicGeometry.WeilCohomology.WeakChernClasses.Situation`), and Tag 0FIF uses
Tag 0FIA for the cohomological Chern character `ch^H` constructed there. This file proves it in
that situation, for any rule `ch : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X)` compatible with pullbacks
and taking the value `exp(c₁^A(ℒ))` on invertible modules, and for the constructed operator
`AlgebraicGeometry.VectorBundleKZero.secondAdamsRingHom`.

The proof is the source's. The identity is additive in `α`, so it suffices to treat the class of
a finite locally free module `ℰ`; restriction to the loci where the rank of `ℰ` is constant is
jointly injective (condition (2)), and over such a locus the splitting principle (Tag 0FI7) gives
`p : P ⟶ X` with `p^*` injective and `[p^*ℰ] = ∑ [ℒ_j]` for invertible `ℒ_j`. Then
`ψ²[ℒ_j] = [ℒ_j ⊗ ℒ_j]`, and `ch^A(ℒ ⊗ ℒ) = exp(2c₁^A(ℒ))`, whose degree-`i` part is `2^i` times
that of `exp(c₁^A(ℒ))`.

## Main results

* `Stacks.WeilCohomology.Weak.coeff_secondAdams`: `ch^A_i(ψ²(α)) = 2^i ch^A_i(α)`.

## References

* [Stacks Project, Tag 0FIA](https://stacks.math.columbia.edu/tag/0FIA)
* [Stacks Project, Tag 0FEJ](https://stacks.math.columbia.edu/tag/0FEJ)
* [Stacks Project, Tag 0FI7](https://stacks.math.columbia.edu/tag/0FI7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v v₁ w

namespace Stacks.WeilCohomology.Weak

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}} (𝔚 : ChernSetup.{u, v, v₁, w} C S)
  [∀ X : C, Algebra ℚ (𝔚.A X)]
  {ch : ∀ X : C, VectorBundleKZero (S.obj X) →+* PowerSeries (𝔚.A X)}

/-- The second Adams operator of `K₀(Vect(S X))`. -/
local notation "ψ²" X => VectorBundleKZero.secondAdamsRingHom
  (VectorBundleKZero.squarePowersData (S.obj X))

/-- `ψ²` commutes with the pullback ring maps of `K₀(Vect(-))` (Tag 0FEJ). -/
theorem pullbackRingHom_secondAdams {X Y : C} (f : X ⟶ Y) (α : VectorBundleKZero (S.obj Y)) :
    VectorBundleKZero.pullbackRingHom (S.map f) ((ψ² Y) α) =
      (ψ² X) (VectorBundleKZero.pullbackRingHom (S.map f) α) := by
  rw [← RingHom.comp_apply, ← VectorBundleKZero.secondAdamsRingHom_comp_pullbackRingHom,
    RingHom.comp_apply]

variable {𝔚}

/-- The identity for an invertible module: `ch^A_n(ℒ ⊗ ℒ) = 2^n ch^A_n(ℒ)`. -/
theorem coeff_secondAdams_classOf_invertible
    (hinv : ∀ (X : C) (L : (S.obj X).Modules)
      (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
        (S.obj X).ringCatSheaf.2 L),
      ch X (VectorBundleKZero.classOf (S.obj X) L) =
        expFirstChernClass 𝔚 X (picardClassOf (S.obj X) L hL))
    (X : C) (L : (S.obj X).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 L) (n : ℕ) :
    PowerSeries.coeff n (ch X ((ψ² X) (VectorBundleKZero.classOf (S.obj X) L))) =
      (2 ^ n : ℕ) • PowerSeries.coeff n (ch X (VectorBundleKZero.classOf (S.obj X) L)) := by
  have : Stacks.SheafOfModules.IsInvertible (S.obj X).sheaf.obj
      (S.obj X).ringCatSheaf.property L :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mpr hL
  have hLL := isInvertible_tensorObjRingedSpace L L hL hL
  rw [VectorBundleKZero.secondAdamsRingHom_apply,
    VectorBundleKZero.secondAdamsAddHom_classOf_isInvertible, hinv X _ hLL, hinv X L hL,
    coeff_expFirstChernClass, coeff_expFirstChernClass,
    c₁_picardClassOf_tensorObjRingedSpace 𝔚 X L L hL hL hLL, ← two_nsmul, smul_pow,
    mul_smul_comm]

variable (hpull : ∀ {X Y : C} (f : X ⟶ Y) (α : VectorBundleKZero (S.obj Y)),
      PowerSeries.map (𝔚.pull f) (ch Y α) = ch X (VectorBundleKZero.pullbackRingHom (S.map f) α))
  (hinv : ∀ (X : C) (L : (S.obj X).Modules)
      (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
        (S.obj X).ringCatSheaf.2 L),
      ch X (VectorBundleKZero.classOf (S.obj X) L) =
        expFirstChernClass 𝔚 X (picardClassOf (S.obj X) L hL))

omit [∀ X : C, Algebra ℚ (𝔚.A X)] in
include hpull in
/-- Pulling the identity back: `p^*` of both sides of `ch^A_n(ψ²(α)) = 2^n ch^A_n(α)` is the same
identity for `p^*α`. -/
theorem pull_coeff_secondAdams {X P : C} (p : P ⟶ X) (α : VectorBundleKZero (S.obj X))
    (n : ℕ) :
    𝔚.pull p (PowerSeries.coeff n (ch X ((ψ² X) α))) =
        PowerSeries.coeff n (ch P ((ψ² P) (VectorBundleKZero.pullbackRingHom (S.map p) α))) ∧
      𝔚.pull p ((2 ^ n : ℕ) • PowerSeries.coeff n (ch X α)) =
        (2 ^ n : ℕ) •
          PowerSeries.coeff n (ch P (VectorBundleKZero.pullbackRingHom (S.map p) α)) := by
  refine ⟨?_, ?_⟩
  · rw [← PowerSeries.coeff_map, hpull, pullbackRingHom_secondAdams]
  · rw [map_nsmul, ← PowerSeries.coeff_map, hpull]

include hpull hinv in
/-- The identity for a module of constant rank, by the splitting principle. -/
theorem coeff_secondAdams_classOf_rank (X : C) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) (n : ℕ) :
    PowerSeries.coeff n (ch X ((ψ² X) (VectorBundleKZero.classOf (S.obj X) E))) =
      (2 ^ n : ℕ) • PowerSeries.coeff n (ch X (VectorBundleKZero.classOf (S.obj X) E)) := by
  classical
  obtain ⟨P, p, -, hinj, hfil⟩ :=
    𝔚.exists_injective_hasInvertibleFiltration X Unit (fun _ => E) (fun _ => r) fun _ => hE
  obtain ⟨-, L, hL, hsum⟩ := (hfil ()).exists_classOf_eq_sum
  refine hinj ?_
  obtain ⟨h1, h2⟩ := pull_coeff_secondAdams hpull p (VectorBundleKZero.classOf (S.obj X) E) n
  rw [h1, h2, VectorBundleKZero.pullbackRingHom_classOf (S.map p) E
      ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry E).mpr
        hE.isFiniteLocallyFree), hsum, map_sum, map_sum, map_sum, map_sum, map_sum,
    Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => coeff_secondAdams_classOf_invertible hinv P (L j) (hL j) n

include hpull hinv in
/-- **Tag 0FIA for the Chern character in the weak standing situation.** For a rule
`ch : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X)` of ring maps compatible with pullbacks and taking the value
`exp(c₁^A(ℒ))` on every invertible module — the rule of Tag 0FIE — the second Adams operator of
Tag 0FEJ scales the degree-`n` part by `2^n`: `ch^A_n(ψ²(α)) = 2^n ch^A_n(α)` for every
`α ∈ K₀(Vect(X))`. -/
theorem coeff_secondAdams (X : C) (α : VectorBundleKZero (S.obj X)) (n : ℕ) :
    PowerSeries.coeff n (ch X ((ψ² X) α)) = (2 ^ n : ℕ) • PowerSeries.coeff n (ch X α) := by
  classical
  have hhom : (PowerSeries.coeff n).toAddMonoidHom.comp
        ((ch X).toAddMonoidHom.comp (ψ² X).toAddMonoidHom) =
      (2 ^ n : ℕ) • (PowerSeries.coeff n).toAddMonoidHom.comp (ch X).toAddMonoidHom := by
    refine VectorBundleKZero.addHom_ext fun E hE => ?_
    change PowerSeries.coeff n (ch X ((ψ² X) (VectorBundleKZero.classOf (S.obj X) E))) =
      (2 ^ n : ℕ) • PowerSeries.coeff n (ch X (VectorBundleKZero.classOf (S.obj X) E))
    have hE' := (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry E).mp hE
    obtain ⟨ι, -, P, p, r, -, hrank, hinj⟩ := 𝔚.exists_clopenRankPieces X E hE'
    refine hinj (funext fun i => ?_)
    obtain ⟨h1, h2⟩ := pull_coeff_secondAdams hpull (p i) (VectorBundleKZero.classOf (S.obj X) E) n
    change 𝔚.pull (p i) _ = 𝔚.pull (p i) _
    rw [h1, h2, VectorBundleKZero.pullbackRingHom_classOf (S.map (p i)) E hE]
    exact coeff_secondAdams_classOf_rank hpull hinv (P i) _ (r i) (hrank i) n
  exact DFunLike.congr_fun hhom α

end Stacks.WeilCohomology.Weak

end
