module

public import StacksFrontier.AlgebraicGeometry.TensorSectionProduct.Basic
public import StacksFrontier.AlgebraicGeometry.SectionExtensionNoAmple.Basic

/-!
# The module-valued [Stacks, Tag 01PW] with its nonvanishing locus computed

`Stacks.SectionExtensionNoAmple.exists_tensorPow_tensorSection_of_hasPointwiseNonvanishing` is the
surjectivity half of [Stacks, Tag 01PW] for an arbitrary quasi-coherent coefficient and **no
ampleness**: a section `t` of `F` over `X_s` extends, after tensoring with a tensor power of `L`, to
a global section `τ` of `F ⊗ L ^⊗ p`, with
`τ|_{X_s} = Stacks.SectionTensorFormula.tensorSection F (L ^⊗ p) t (σ|_{X_s})`.

Every consumer wants the **nonvanishing locus** of `τ`, and that equation could not be read for
one: `StacksFrontier/AlgebraicGeometry/TensorSectionNonvanishing/Basic.lean` records in its "What is
not done" that its product formula `X_{e ⊗ f} = X_e ∩ X_f` is stated for the composite
`Stacks.TensorSectionNonvanishing.unitMul` and that the module-valued Tag 01PW, "whose conclusion is
stated with `tensorSection`, **cannot yet be composed with the results below**".

The sibling file `Basic.lean` proves the product formula for `tensorSection` itself. This file is
the composition, and it is the reason that formula was wanted.

## Main results

* `Stacks.TensorSectionProduct.exists_tensorPow_tensorSection_nonvanishingLocus`: **the
  module-valued Tag 01PW with its nonvanishing locus.** On `X_s` the nonvanishing locus of the
  extension `τ` is exactly the nonvanishing locus of the section `t` it extends. The second factor
  contributes nothing there because `σ` is, by the same conclusion, nowhere vanishing on `X_s`.

## Implementation notes

**Why the second clause of the product formula is automatic.** Tag 01PW returns `σ` together with
`X_s = X_σ`, so for `y ∈ X_s` the germ of `σ` avoids `𝔪_y · (L ^⊗ p)_y`; the germ of its
restriction `Stacks.SectionExtension.resTop` is the same element of the stalk, by
`TopCat.Presheaf.Γgerm_res_apply`. So the conjunction produced by
`Stacks.TensorSectionProduct.mem_nonvanishingLocus_iff_of_resTop_eq` collapses to its first
conjunct.

**`F` is asked to be invertible as well as quasi-coherent.** Tag 01PW itself needs only
quasi-coherence; the product formula needs both factors invertible, since it uses a trivialization
of each. For part (1) of [Stacks, Tag 0892] the coefficient is a tensor power of a relatively ample
invertible module, so nothing is lost.

## What is not done, and no tag is attached

**No `@[stacks]` attribute is attached.** None of Tag 01PW's four labels is closed: what is used
here is `Stacks.SectionExtensionNoAmple`'s form, which carries the extra hypothesis
`Stacks.SectionExtensionNoAmple.HasPointwiseNonvanishing`, and the covering-set rule withholds the
label for exactly that reason — see that file's own "What is and is not proved".

**This does not close part (1) of [Stacks, Tag 0892].** Part (1) needs, beyond this:

* the nonvanishing locus, inside `U = f⁻¹(S_t)`, of a section of `L ^⊗ k` over `U` obtained from a
  *global* section of the restriction `L|_U` — the comparison
  `Stacks.AmplePullbackPart1.sectionOfRestrictGlobalSection` transports the section but not its
  locus, and the semilinear stalk comparison across an open immersion that would transport
  `Stacks.ModuleStalk.maximalSmul` is absent (recorded at
  `../StalkFreeBridge/StalkFree.lean`, Mathlib's
  `AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso` comparing the two stalks only as abelian
  groups);
* `QuasiSeparatedSpace X`, which Tag 01PW asks of the scheme;
* the degree bookkeeping that identifies `(L ^⊗ k ⊗ (f^* M) ^⊗ p) ⊗ (f^* M) ^⊗ q` with
  `Stacks.AmplePullbackPart1.tensorPullbackSplitModule f L M a k`.

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
open Stacks.Ample Stacks.AmpleTheory Stacks.ModuleStalk

universe u

namespace Stacks.TensorSectionProduct

section Consumer

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]

/-- **The module-valued [Stacks, Tag 01PW], with no ampleness, and with the nonvanishing locus of
the extension computed on `X_s`.**

For `X` quasi-compact and quasi-separated, `L` invertible with enough sections, `F` invertible and
quasi-coherent, `s` a global section of `L ^⊗ n` with `n ≥ 1` and `t` a section of `F` over `X_s`,
there are `p` with `n ∣ p`, a global section `σ` of `L ^⊗ p` with `X_σ = X_s`, and a global section
`τ` of `F ⊗ L ^⊗ p`, such that **at every point of `X_s` the section `τ` vanishes exactly where `t`
does.**

This is `Stacks.SectionExtensionNoAmple.exists_tensorPow_tensorSection_of_hasPointwiseNonvanishing`
composed with `Stacks.TensorSectionProduct.mem_nonvanishingLocus_iff_of_resTop_eq`; the second
conjunct of the product formula is discharged by `X_σ = X_s`, see the implementation notes. -/
theorem exists_tensorPow_tensorSection_nonvanishingLocus [CompactSpace X]
    [QuasiSeparatedSpace X] (hpt : Stacks.SectionExtensionNoAmple.HasPointwiseNonvanishing L)
    (F : X.Modules) [F.IsQuasicoherent] [IsInvertibleModule X F] {n : ℕ} (hn : 1 ≤ n)
    (s : Γ(tensorPowModule X L (n : ℤ), ⊤)) (t : Γ(F, powNonvanishingOpen X L n s)) :
    ∃ (p : ℕ) (σ : Γ(tensorPowModule X L (p : ℤ), ⊤))
      (τ : Γ((F ⊗ tensorPowModule X L (p : ℤ) : X.Modules), ⊤)), n ∣ p ∧
      powNonvanishingOpen X L n s = powNonvanishingOpen X L p σ ∧
      ∀ (y : X) (hy : y ∈ powNonvanishingOpen X L n s),
        (y ∈ nonvanishingLocus (F ⊗ tensorPowModule X L (p : ℤ) : X.Modules) τ ↔
          (F.presheaf.germ (powNonvanishingOpen X L n s) y hy).hom t ∉ maximalSmul F y) := by
  obtain ⟨p, σ, τ, hdvd, hσ, heq⟩ :=
    Stacks.SectionExtensionNoAmple.exists_tensorPow_tensorSection_of_hasPointwiseNonvanishing
      L hpt F hn s t
  have hinv : IsInvertibleModule X (tensorPowModule X L (p : ℤ)) :=
    isInvertibleModule_tensorPowModule X L (p : ℤ)
  refine ⟨p, σ, τ, hdvd, hσ, fun y hy => ?_⟩
  have hσy : ((tensorPowModule X L (p : ℤ)).presheaf.germ
      (powNonvanishingOpen X L n s) y hy).hom
        (Stacks.SectionExtension.resTop (powNonvanishingOpen X L n s) σ) ∉
      maximalSmul (tensorPowModule X L (p : ℤ)) y := by
    rw [Stacks.SectionExtension.resTop,
      TopCat.Presheaf.Γgerm_res_apply (C := Ab.{u})
        (i := homOfLE (le_top : powNonvanishingOpen X L n s ≤ ⊤))
        (tensorPowModule X L (p : ℤ)).presheaf y hy σ]
    exact (hσ ▸ hy : y ∈ powNonvanishingOpen X L p σ)
  rw [mem_nonvanishingLocus_iff_of_resTop_eq τ t
    (Stacks.SectionExtension.resTop (powNonvanishingOpen X L n s) σ) heq hy]
  exact and_iff_left hσy

end Consumer

end Stacks.TensorSectionProduct

end
