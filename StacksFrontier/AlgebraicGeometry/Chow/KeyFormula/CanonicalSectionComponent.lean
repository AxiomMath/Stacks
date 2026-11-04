module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinPushforwardChernCap
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.SituationData

/-!
# The divisor of the canonical section on an integral component off the divisor

Let `E ⊆ X` be an effective Cartier divisor and `ξ ∈ X` a point outside the support of `E`. The
germ `m = 1_E|_ξ` of the canonical section of `𝒪_X(E)` at `ξ` generates the stalk there, so its
restriction to the integral component `Z_ξ = \overline{\{ξ\}}` is a nonzero meromorphic section of
`𝒪_X(E)|_{Z_ξ}` and the divisor `div_{𝒪_X(E)|Z_ξ}(m|_{Z_ξ})` of
`Stacks.Chow.restrictedWeilDivisorAt` is defined. This file identifies its cycle with the
fundamental cycle of the scheme-theoretic intersection `E ∩ Z_ξ`.

The identification is Stacks 02SK on `Z_ξ`: the restricted divisor is the divisor cycle of the
restriction of the canonical section to `Z_ξ`
(`Stacks.Chow.restrictStalk_germ_divisorSheafGlobalSection`), and the zero scheme of that
restriction is `E ∩ Z_ξ`, because the zero scheme of `1_E` is `E` (Stacks 01X0) and zero schemes
commute with pullback (Stacks 0B6Y). The hypothesis `ξ ∉ E` enters only to make the restricted
section nonzero, which is what Stacks 02SK asks: were `Z_ξ` inside `E`, its generic point `ξ`
would lie in `E`.

Note that `ξ ∉ E` does *not* make the divisor vanish: `Z_ξ` may well meet `E` away from `ξ`, and
the surviving coefficients are precisely those the intersection cycle counts.

## Main results

* `Stacks.Chow.zeroScheme_restrictedCanonicalSection` — the zero scheme of `1_E|_{Z_ξ}` is
  `E ∩ Z_ξ`.
* `Stacks.Chow.restrictedCanonicalSection_ne_zero` — that restriction is nonzero when `ξ ∉ E`.
* `Stacks.Chow.weilDivisorAlgebraicCycle_restrictedWeilDivisorAt_germ_divisorSheafGlobalSection` —
  **`div_{𝒪_X(E)|Z_ξ}(1_E|_{Z_ξ}) = [E ∩ Z_ξ]_k`.**

## References

* [Stacks Project, Tag 02SK](https://stacks.math.columbia.edu/tag/02SK)
* [Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

attribute [local instance] isIntegral_integralComponentAt

variable {X : Scheme.{u}} (E : X.IdealSheafData) [IsEffectiveCartierDivisor E]

/-- **The zero scheme of the restricted canonical section is `E ∩ Z_ξ`.** Zero schemes commute
with pullback (Stacks 0B6Y) and the zero scheme of `1_E` is `E` (Stacks 01X0). -/
theorem zeroScheme_restrictedCanonicalSection (ξ : X) :
    Stacks.Divisors.zeroScheme (integralComponentAt ξ).subscheme
        (restrictModule (integralComponentAt ξ) (divisorSheaf E))
        (AlgebraicGeometry.pullbackGlobalSections (integralComponentAt ξ).subschemeι
          (divisorSheaf E) (divisorSheafGlobalSection E)) =
      E.comap (integralComponentAt ξ).subschemeι := by
  rw [zeroScheme_pullback (integralComponentAt ξ).subschemeι (divisorSheaf E)
    (divisorSheafGlobalSection E)]
  exact congrArg (fun I : X.IdealSheafData => I.comap (integralComponentAt ξ).subschemeι)
    (zeroScheme_canonicalSection E)

/-- **The canonical section stays nonzero on the integral component at a point off `E`.** A
vanishing restriction would put `Z_ξ` inside the zero scheme `E` of `1_E` (Stacks 02OR (2)), hence
would put `ξ` into the support of `E`. -/
theorem restrictedCanonicalSection_ne_zero (ξ : X) (hξ : ξ ∉ (E.support : Set X)) :
    AlgebraicGeometry.pullbackGlobalSections (integralComponentAt ξ).subschemeι
      (divisorSheaf E) (divisorSheafGlobalSection E) ≠ 0 := by
  have hmem : ξ ∈ ((integralComponentAt ξ).support : Set X) := by
    rw [coe_support_integralComponentAt]
    exact subset_closure rfl
  refine pullbackGlobalSections_subschemeι_ne_zero (divisorSheaf E) (divisorSheafGlobalSection E)
    (integralComponentAt ξ) (isIntegral_integralComponentAt ξ) fun hle => hξ ?_
  exact SetLike.coe_subset_coe.2 (Scheme.IdealSheafData.support_antitone
    ((zeroScheme_canonicalSection E).ge.trans hle)) hmem

open Stacks.AlgebraicGeometry.SectionsBaseChange in
omit [IsEffectiveCartierDivisor E] in
/-- **The restriction of the canonical section to `Z_ξ` is the germ of its pullback.** Both sides
are the image of `1_E` under the base-change map on stalks at the generic point of `Z_ξ`. -/
theorem restrictStalk_germ_divisorSheafGlobalSection (ξ : X) :
    restrictStalk (integralComponentAt ξ) (divisorSheaf E)
        (genericPointOf_integralComponentAt ξ)
        ((divisorSheaf E).presheaf.germ ⊤ ξ trivial (divisorSheafGlobalSection E)) =
      (restrictModule (integralComponentAt ξ) (divisorSheaf E)).presheaf.germ ⊤
        (genericPoint (integralComponentAt ξ).subscheme) trivial
        (AlgebraicGeometry.pullbackGlobalSections (integralComponentAt ξ).subschemeι
          (divisorSheaf E) (divisorSheafGlobalSection E)) := by
  rw [show AlgebraicGeometry.pullbackGlobalSections (integralComponentAt ξ).subschemeι
        (divisorSheaf E) (divisorSheafGlobalSection E) =
      pullbackUnitSections (integralComponentAt ξ).subschemeι (divisorSheaf E) ⊤
        (divisorSheafGlobalSection E) by
    rw [AlgebraicGeometry.pullbackGlobalSections_eq_unit]; rfl]
  exact pullbackStalkAt_germ (integralComponentAt ξ).subschemeι (divisorSheaf E)
    (genericPoint (integralComponentAt ξ).subscheme) (genericPointOf_integralComponentAt ξ)
    ⊤ trivial (divisorSheafGlobalSection E)

variable (C : ChowSituation.{u}) (p : X ⟶ C.S) [LocallyOfFiniteType p]

include C p in
/-- **Off `E`, the divisor of the canonical section restricted to `Z_ξ` is the cycle of
`E ∩ Z_ξ`.** For an effective Cartier divisor `E` on `X` and a point `ξ` outside `E`, the germ
`m` of `1_E` at `ξ` generates `𝒪_X(E)_ξ`, so `m|_{Z_ξ}` is a nonzero meromorphic section of
`𝒪_X(E)|_{Z_ξ}`, and Stacks 02SK on `Z_ξ` identifies its divisor with the fundamental cycle of
the zero scheme `E ∩ Z_ξ` of that restriction. -/
theorem weilDivisorAlgebraicCycle_restrictedWeilDivisorAt_germ_divisorSheafGlobalSection
    (ξ : X) (hξ : ξ ∉ (E.support : Set X)) (k : ℤ)
    (hk : schemeDeltaDimension C ((integralComponentAt ξ).subschemeι ≫ p) =
      ((k + 1 : ℤ) : EInt)) :
    weilDivisorAlgebraicCycle (restrictedWeilDivisorAt C p ξ
        ((divisorSheaf E).presheaf.germ ⊤ ξ trivial (divisorSheafGlobalSection E))) =
      (cycleAssociatedToClosedSubscheme C ((integralComponentAt ξ).subschemeι ≫ p)
        (E.comap (integralComponentAt ξ).subschemeι).subschemeι k).1 := by
  have _ := isLocallyNoetherian_integralComponentAt C p ξ
  have _ := Stacks.ChernCap42.isInvertible_sheafObj_modulePullback (divisorSheaf E)
    (integralComponentAt ξ).subschemeι
  have key := Stacks.ChernCap42.chernComponentCycle_coe_eq_cycleAssociatedToZeroScheme C k
    ((integralComponentAt ξ).subschemeι ≫ p)
    (restrictModule (integralComponentAt ξ) (divisorSheaf E)) hk _
    (restrictedCanonicalSection_ne_zero E ξ hξ)
    (isTrivializedNear_restrictModule (integralComponentAt ξ) (divisorSheaf E))
  rw [genericValue_meromorphicSectionOfSection, zeroScheme_restrictedCanonicalSection E ξ] at key
  rw [← key]
  exact congrArg weilDivisorAlgebraicCycle
    (congrArg (weilDivisorOfMeromorphicSection
        (isTrivializedNear_restrictModule (integralComponentAt ξ) (divisorSheaf E)))
      (restrictStalk_germ_divisorSheafGlobalSection E ξ))

end Stacks.Chow

end
