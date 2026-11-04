module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.GysinZeroSectionDischarge
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.ZeroSchemeVanishing
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic

/-!
# A section restricted to a closed subscheme of its zero scheme

Let `L` be an invertible module on a scheme `X`, let `s ∈ Γ(L, ⊤)` and let `I` be a
quasi-coherent ideal sheaf on `X` whose closed subscheme is contained in the zero scheme of `s`.
Closed subschemes are ordered by their ideal sheaves and geometric inclusion is the reverse of
that order, so the hypothesis reads `zeroScheme X L s ≤ I`. Then `s` restricts to zero on that
subscheme, and consequently the scheme-theoretic inverse image of the zero scheme in it is
everything.

`Stacks.Divisors.pullbackGlobalSections_eq_zero_iff_le_ker` reads the vanishing of a
pulled-back section as an inclusion of the zero scheme in the kernel of the morphism, and the
kernel of a closed immersion of subschemes is the ideal sheaf itself
(`AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι`), so the first statement is that lemma
at `I.subschemeι`; `Stacks.Divisors.zeroScheme_pullback` ([Stacks, Tag 0B6Y]) then identifies the
inverse image with the zero scheme of the restricted section, which is the whole subscheme by
`Stacks.Divisors.zeroScheme_zero_eq_bot`.

The second statement is the form in which the case `W ⊆ D` of [Stacks, Tag 0F98] uses the
hypothesis: base-changing the diagram of [Stacks, Tag 0F97] along `W ↪ Y` turns the divisor `D`
into the whole of `W`, which is what makes the base-changed diagram's union condition read
`p^{-1}(W) = W₁ ∪ W₂`.

## Main results

* `Stacks.Divisors.pullbackGlobalSections_subschemeι_eq_zero_of_le`: **a section of an invertible
  module restricts to zero on any closed subscheme of its zero scheme.**
* `Stacks.Divisors.comap_zeroScheme_subschemeι_eq_bot`: **the scheme-theoretic inverse image of
  the zero scheme of a section in a closed subscheme of that zero scheme is the whole
  subscheme.**

## References

* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 0F98](https://stacks.math.columbia.edu/tag/0F98)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤)) (I : X.IdealSheafData) (hI : zeroScheme X L s ≤ I)

include hI in
/-- **A section of an invertible module restricts to zero on any closed subscheme of its zero
scheme.** This is `Stacks.Divisors.pullbackGlobalSections_eq_zero_iff_le_ker` at a closed
immersion, where the kernel of the immersion is the ideal sheaf itself. -/
theorem pullbackGlobalSections_subschemeι_eq_zero_of_le :
    pullbackGlobalSections I.subschemeι L s = 0 :=
  (pullbackGlobalSections_eq_zero_iff_le_ker L s I.subschemeι).mpr
    (hI.trans I.ker_subschemeι.ge)

include hI in
/-- **The scheme-theoretic inverse image of the zero scheme of a section in a closed subscheme of
that zero scheme is the whole subscheme.** The inverse image is the zero scheme of the restricted
section by [Stacks, Tag 0B6Y], and that section is zero. -/
theorem comap_zeroScheme_subschemeι_eq_bot :
    (zeroScheme X L s).comap I.subschemeι = ⊥ := by
  rw [← zeroScheme_pullback I.subschemeι L s,
    pullbackGlobalSections_subschemeι_eq_zero_of_le L s I hI, zeroScheme_zero_eq_bot]

end Stacks.Divisors

end
