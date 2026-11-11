module

public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemeRegularSection
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClass
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeIdealSheaf
public import StacksFrontier.AlgebraicGeometry.QuasiAffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.SourceChernSetup

/-!
# Invertible modules with a nonzero section on an integral scheme

Let `X` be an integral scheme and `ℒ` an invertible `𝒪_X`-module with a nonzero global section
`s ∈ Γ(X, ℒ)`. Then `s` is a regular section, so its zero scheme `D = Z(s)` is an effective
Cartier divisor with `ℒ ≅ 𝒪_X(D)` ([Stacks, Tag 01X0]); in particular `ℒ` and `𝒪_X(D)` have the
same class in `Pic(X)`. If `ℒ` is not trivial then `D` is not the empty divisor `⊤`, since
`𝒪_X(∅) ≅ 𝒪_X`.

## Main results

* `Stacks.Divisors.isEffectiveCartierDivisor_zeroScheme_and_picardClassOf_eq_of_ne_zero`: the zero
  scheme `D` of a nonzero global section of an invertible module `ℒ` on an integral scheme is an
  effective Cartier divisor with `[𝒪_X(D)] = [ℒ]`, and `D = ⊤` only when `ℒ ≅ 𝒪_X`.
* `Stacks.Divisors.exists_isEffectiveCartierDivisor_picardClassOf_eq`: a nontrivial invertible
  module with a nonzero global section on an integral scheme is the invertible sheaf of a
  nonempty effective Cartier divisor, at the level of Picard classes.
* `Stacks.Divisors.exists_isEffectiveCartierDivisor_picardClassOf_eq_and_eq_top_iff`: the same
  without the nontriviality hypothesis, the divisor being empty exactly when `ℒ` is trivial.

## References

* [Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.Divisors

/-- **The zero scheme of a global section of an invertible module on an integral scheme, nonzero
on the whole space, is an effective Cartier divisor whose invertible sheaf is the module**: for a
section `σ` of `ℒ` with `σ(X) ≠ 0`, the zero scheme `D = Z(σ)` is an effective Cartier divisor,
`[𝒪_X(D)] = [ℒ]` in `Pic(X)` ([Stacks, Tag 01X0]), and `D` is the empty divisor `⊤` only when
`ℒ ≅ 𝒪_X`, as `𝒪_X(∅) ≅ 𝒪_X`. -/
theorem isEffectiveCartierDivisor_zeroScheme_and_picardClassOf_eq {X : Scheme.{u}}
    [IsIntegral X] (ℒ : X.Modules)
    [hℒ : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property ℒ]
    (σ : ℒ.sections) (hσ : σ.eval (op ⊤) ≠ 0) :
    ∃ (_ : IsEffectiveCartierDivisor (zeroScheme X ℒ (σ.eval (op ⊤)))),
      (zeroScheme X ℒ (σ.eval (op ⊤)) = ⊤ →
          Nonempty (ℒ ≅ _root_.SheafOfModules.unit X.ringCatSheaf)) ∧
        Stacks.WeilCohomology.picardClassOf X (divisorSheaf (zeroScheme X ℒ (σ.eval (op ⊤))))
            (isInvertible_divisorSheaf _) =
          Stacks.WeilCohomology.picardClassOf X ℒ hℒ := by
  have hD := isEffectiveCartierDivisor_zeroScheme_of_eval_top_ne_zero X ℒ σ hσ
  have hreg := (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection X ℒ σ).mp hD
  let e := invertibleSheafIsoZeroSchemeOfIsRegularSection ℒ σ hreg
  refine ⟨hD, fun htop => ?_, ?_⟩
  · have e' : invertibleSheaf' (zeroScheme X ℒ (σ.eval (op ⊤))) ≅
        invertibleSheaf' (⊤ : X.IdealSheafData) := eqToIso (congrArg invertibleSheaf' htop)
    exact ⟨e ≪≫ e' ≪≫ invertibleSheafTopIsoUnit⟩
  · exact Stacks.WeilCohomology.picardClassOf_eq_of_iso _ _ _ _ _ e.symm

/-- **The zero scheme of a nonzero global section of an invertible module on an integral scheme
is an effective Cartier divisor whose invertible sheaf is the module**: for `t ∈ Γ(X, ℒ)` nonzero,
`D = Z(t)` is an effective Cartier divisor with `[𝒪_X(D)] = [ℒ]` in `Pic(X)`
([Stacks, Tag 01X0]), and `D = ⊤` only when `ℒ ≅ 𝒪_X`. -/
theorem isEffectiveCartierDivisor_zeroScheme_and_picardClassOf_eq_of_ne_zero {X : Scheme.{u}}
    [IsIntegral X] (ℒ : X.Modules)
    [hℒ : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property ℒ]
    (t : Γ(ℒ, ⊤)) (ht : t ≠ 0) :
    ∃ (_ : IsEffectiveCartierDivisor (zeroScheme X ℒ t)),
      (zeroScheme X ℒ t = ⊤ → Nonempty (ℒ ≅ _root_.SheafOfModules.unit X.ringCatSheaf)) ∧
        Stacks.WeilCohomology.picardClassOf X (divisorSheaf (zeroScheme X ℒ t))
            (isInvertible_divisorSheaf _) =
          Stacks.WeilCohomology.picardClassOf X ℒ hℒ := by
  have hσ : (Stacks.SheafOfModules.sectionsOfTopOfRingSheaf ℒ t).eval (op ⊤) = t :=
    Stacks.SheafOfModules.sectionsOfTopOfRingSheaf_eval_top _ _
  have h := isEffectiveCartierDivisor_zeroScheme_and_picardClassOf_eq ℒ
    (Stacks.SheafOfModules.sectionsOfTopOfRingSheaf ℒ t) (by rw [hσ]; exact ht)
  rw [hσ] at h
  exact h

/-- **A nontrivial invertible module with a nonzero global section on an integral scheme is the
invertible sheaf of a nonempty effective Cartier divisor** ([Stacks, Tag 01X0]): there is an
effective Cartier divisor `D ≠ ⊤` with `[𝒪_X(D)] = [ℒ]` in `Pic(X)`, namely the zero scheme of the
section. -/
theorem exists_isEffectiveCartierDivisor_picardClassOf_eq {X : Scheme.{u}} [IsIntegral X]
    (ℒ : X.Modules)
    (hℒ : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ℒ)
    (s : Γ(ℒ, ⊤)) (hs : s ≠ 0)
    (hnt : ¬ Nonempty (ℒ ≅ _root_.SheafOfModules.unit X.ringCatSheaf)) :
    ∃ (D : X.IdealSheafData) (_ : IsEffectiveCartierDivisor D), D ≠ ⊤ ∧
      Stacks.WeilCohomology.picardClassOf X (divisorSheaf D) (isInvertible_divisorSheaf D) =
        Stacks.WeilCohomology.picardClassOf X ℒ hℒ := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property ℒ :=
    hℒ
  obtain ⟨hD, htop, hc⟩ :=
    isEffectiveCartierDivisor_zeroScheme_and_picardClassOf_eq_of_ne_zero ℒ s hs
  exact ⟨_, hD, fun h => hnt (htop h), hc⟩

/-- **An invertible module with a nonzero global section on an integral scheme is the invertible
sheaf of an effective Cartier divisor, empty exactly when the module is trivial**
([Stacks, Tag 01X0]): there is an effective Cartier divisor `D` with `[𝒪_X(D)] = [ℒ]` in `Pic(X)`
and `D = ⊤ ↔ ℒ ≅ 𝒪_X`. For nontrivial `ℒ` it is the zero scheme of the section, for trivial `ℒ`
the empty divisor. -/
theorem exists_isEffectiveCartierDivisor_picardClassOf_eq_and_eq_top_iff {X : Scheme.{u}}
    [IsIntegral X] (ℒ : X.Modules)
    (hℒ : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ℒ)
    (s : Γ(ℒ, ⊤)) (hs : s ≠ 0) :
    ∃ (D : X.IdealSheafData) (_ : IsEffectiveCartierDivisor D),
      (D = ⊤ ↔ Nonempty (ℒ ≅ _root_.SheafOfModules.unit X.ringCatSheaf)) ∧
      Stacks.WeilCohomology.picardClassOf X (divisorSheaf D) (isInvertible_divisorSheaf D) =
        Stacks.WeilCohomology.picardClassOf X ℒ hℒ := by
  by_cases hnt : Nonempty (ℒ ≅ _root_.SheafOfModules.unit X.ringCatSheaf)
  · refine ⟨⊤, inferInstance, iff_of_true rfl hnt, ?_⟩
    exact Stacks.WeilCohomology.picardClassOf_eq_of_iso _ _ _ _ _
      (invertibleSheafTopIsoUnit ≪≫ hnt.some.symm)
  · obtain ⟨D, hD, hne, hc⟩ := exists_isEffectiveCartierDivisor_picardClassOf_eq ℒ hℒ s hs hnt
    exact ⟨D, hD, iff_of_false hne hnt, hc⟩

end Stacks.Divisors

end
