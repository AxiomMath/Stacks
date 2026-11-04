module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import StacksFrontier.Algebra.Homology.RightDerivedDelta

/-!
# Finiteness of right derived functors valued in modules over a Noetherian ring

Let `Q : 𝒜 ⥤ Mod_R` be an additive functor from an abelian category with enough injectives to
modules over a Noetherian commutative ring `R`, and let `0 → X₁ → X₂ → X₃ → 0` be a short exact
sequence in `𝒜`.  Finite `R`-modules are closed under submodules, quotients and extensions, so the
long exact sequence of the right derived functors of `Q` lets finiteness of `RⁿQ` pass from two of
the three terms to the third, in the appropriate degrees.  This file records the four resulting
implications, and descent of finiteness along a retract.

They are the two-out-of-three and finite-sum conditions of the dévissage of Stacks 08AN for the
property "all `RⁿQ` are finite", as used in the proof of Stacks 08AR.

## Main results

* `Stacks.Cohomology.RightDerivedDelta.moduleFinite_rightDerived_X₂`,
  `…_X₃`, `…_succ_X₁` and `…_zero_X₁`: the four implications.
* `Stacks.Cohomology.RightDerivedDelta.moduleFinite_rightDerived_of_retract`: finiteness descends
  along a retract.

## References

* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
* [Stacks Project, Tag 08AN](https://stacks.math.columbia.edu/tag/08AN)
-/

@[expose] public section

open CategoryTheory Category Limits

universe v₁ v₂ u₁ u₂

namespace Stacks.Cohomology.RightDerivedDelta

variable {B : Type u₁} [Category.{v₁} B] [Abelian B] [EnoughInjectives B]
  {R : Type u₂} [CommRing R] [IsNoetherianRing R] (Q : B ⥤ ModuleCat.{v₂} R) [Q.Additive]

/-- **The middle term of an exact sequence of modules over a Noetherian ring whose outer terms
are finite is finite.**  The kernel of the second map is the image of the first, a quotient of a
finite module, hence Noetherian; so the middle term is Noetherian. -/
theorem moduleFinite_X₂_of_exact {T : ShortComplex (ModuleCat.{v₂} R)} (hT : T.Exact)
    (h₁ : Module.Finite R T.X₁) (h₃ : Module.Finite R T.X₃) : Module.Finite R T.X₂ := by
  have : IsNoetherian R T.X₁ := isNoetherian_of_isNoetherianRing_of_finite R T.X₁
  have : IsNoetherian R T.X₃ := isNoetherian_of_isNoetherianRing_of_finite R T.X₃
  have : IsNoetherian R T.X₂ :=
    isNoetherian_of_range_eq_ker T.f.hom T.g.hom
      ((ShortComplex.moduleCat_exact_iff_range_eq_ker T).1 hT)
  infer_instance

variable {S : ShortComplex B} (hS : S.ShortExact)

include hS in
/-- **`RⁿQ X₂` is finite when `RⁿQ X₁` and `RⁿQ X₃` are.** -/
theorem moduleFinite_rightDerived_X₂ (n : ℕ)
    (h₁ : Module.Finite R ((Q.rightDerived n).obj S.X₁))
    (h₃ : Module.Finite R ((Q.rightDerived n).obj S.X₃)) :
    Module.Finite R ((Q.rightDerived n).obj S.X₂) := by
  obtain ⟨_, _, hwin⟩ := exists_delta_exact_composableArrows₅ hS Q
  exact moduleFinite_X₂_of_exact ((hwin n).exact 0) h₁ h₃

include hS in
/-- **`RⁿQ X₃` is finite when `RⁿQ X₂` and `Rⁿ⁺¹Q X₁` are.** -/
theorem moduleFinite_rightDerived_X₃ (n : ℕ)
    (h₂ : Module.Finite R ((Q.rightDerived n).obj S.X₂))
    (h₁ : Module.Finite R ((Q.rightDerived (n + 1)).obj S.X₁)) :
    Module.Finite R ((Q.rightDerived n).obj S.X₃) := by
  obtain ⟨_, _, hwin⟩ := exists_delta_exact_composableArrows₅ hS Q
  exact moduleFinite_X₂_of_exact ((hwin n).exact 1) h₂ h₁

include hS in
/-- **`Rⁿ⁺¹Q X₁` is finite when `RⁿQ X₃` and `Rⁿ⁺¹Q X₂` are.** -/
theorem moduleFinite_rightDerived_succ_X₁ (n : ℕ)
    (h₃ : Module.Finite R ((Q.rightDerived n).obj S.X₃))
    (h₂ : Module.Finite R ((Q.rightDerived (n + 1)).obj S.X₂)) :
    Module.Finite R ((Q.rightDerived (n + 1)).obj S.X₁) := by
  obtain ⟨_, _, hwin⟩ := exists_delta_exact_composableArrows₅ hS Q
  exact moduleFinite_X₂_of_exact ((hwin n).exact 2) h₃ h₂

include hS in
/-- **`R⁰Q X₁` is finite when `R⁰Q X₂` is**: it is a submodule of it. -/
theorem moduleFinite_rightDerived_zero_X₁
    (h₂ : Module.Finite R ((Q.rightDerived 0).obj S.X₂)) :
    Module.Finite R ((Q.rightDerived 0).obj S.X₁) := by
  obtain ⟨_, hmono, _⟩ := exists_delta_exact_composableArrows₅ hS Q
  have : IsNoetherian R ((Q.rightDerived 0).obj S.X₂) :=
    isNoetherian_of_isNoetherianRing_of_finite R _
  exact Module.Finite.of_injective ((Q.rightDerived 0).map S.f).hom
    ((ModuleCat.mono_iff_injective _).1 hmono)

omit [EnoughInjectives B] [IsNoetherianRing R] in
/-- **Finiteness of the right derived functors descends along a retract.**  If `X` is a retract
of `Y` then `RⁿQ X` is a retract of `RⁿQ Y`, so it is finite as soon as `RⁿQ Y` is. -/
theorem moduleFinite_rightDerived_of_retract [HasInjectiveResolutions B] {X Y : B} (i : X ⟶ Y)
    (r : Y ⟶ X) (hri : i ≫ r = 𝟙 X) (n : ℕ)
    (h : Module.Finite R ((Q.rightDerived n).obj Y)) :
    Module.Finite R ((Q.rightDerived n).obj X) :=
  Module.Finite.of_surjective ((Q.rightDerived n).map r).hom (fun x =>
    ⟨((Q.rightDerived n).map i).hom x, by
      rw [← ModuleCat.comp_apply, ← Functor.map_comp, hri, CategoryTheory.Functor.map_id]
      rfl⟩)

end Stacks.Cohomology.RightDerivedDelta

end
