module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecialFibreDimension
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemePower
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeRegular
public import StacksFrontier.AlgebraicGeometry.DivisorSum.Basic

/-!
# Powers of a regular section, and the zero scheme they cut out

Let `L` be an invertible `𝒪_X`-module on a scheme and `s` a global section. Its `k`-th power
`s^k`, a global section of `L^{⊗ k}`, has zero scheme `Z(s)^k`
(`AlgebraicGeometry.zeroScheme_sectionPow'_degreeOne`), which has the same *support* as `Z(s)`.
Two things follow, and both are used by the Enriques–Severi–Zariski connectedness theorem
[Stacks, Tag 0FD9], whose proof opens "since `s` is a regular section, so is `s^n`; moreover
the inclusion morphism `Z(s) → Z(s^n)` is a bijection on underlying topological spaces":

* a power of a regular section is regular;
* `Z(s)` and `Z(s^k)` are homeomorphic for `k ≥ 1`, so one is connected exactly when the other
  is.

## Main results

* `Stacks.AmpleSectionConnected.subschemeHomeoOfSupportEq`: closed subschemes cut out by ideal
  sheaves with the same support are homeomorphic. The homeomorphism of a closed subscheme with
  its support is not rebuilt here: it is `Stacks.Chow.subschemeHomeoSupport`.
* `Stacks.AmpleSectionConnected.isRegularSection_sectionPow'`: a power of a regular section is
  regular.
* `Stacks.AmpleSectionConnected.zeroSchemeSectionPowHomeo`: the homeomorphism
  `Z(s) ≃ₜ Z(s^k)`.

## Implementation notes

Regularity of the power is obtained through effective Cartier divisors rather than by multiplying
monomorphisms: `AlgebraicGeometry.isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection`
([Stacks, Tag 02OR (4)]) turns regularity of a section into a property of its zero scheme,
`Stacks.Divisors.isEffectiveCartierDivisor_pow` raises that property to a power, and
`AlgebraicGeometry.zeroScheme_sectionPow'_degreeOne` says the power of the zero scheme is the
zero scheme of the power. Going through the divisor avoids any comparison of the two
multiplications on sections of tensor powers.

The exponent is written `1 * k` throughout, because that is the degree
`Stacks.SheafOfModules.Invertible.sectionPow'` produces from a section read in degree one, and
`1 * k` is not definitionally `k`.

## References

* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
* [Stacks Project, Tag 0FD9](https://stacks.math.columbia.edu/tag/0FD9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.SheafOfModules.Invertible

universe u

namespace Stacks.AmpleSectionConnected

variable {X : Scheme.{u}}

/-- **Closed subschemes with the same support are homeomorphic.** Both are homeomorphic to
their common support, by `Stacks.Chow.subschemeHomeoSupport`. -/
def subschemeHomeoOfSupportEq {I J : X.IdealSheafData} (h : I.support = J.support) :
    I.subscheme ≃ₜ J.subscheme :=
  (Stacks.Chow.subschemeHomeoSupport I).trans
    ((Homeomorph.setCongr (congrArg (fun K : Closeds X => (K : Set X)) h)).trans
      (Stacks.Chow.subschemeHomeoSupport J).symm)

variable (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L]

/-- **A power of a regular section is regular.** The zero scheme of a regular section is an
effective Cartier divisor, powers of effective Cartier divisors are effective Cartier divisors,
and the `k`-th power of the zero scheme is the zero scheme of the `k`-th power of the
section. -/
theorem isRegularSection_sectionPow' (s : L.sections)
    (hs : Mono (L.unitHomEquiv.symm s)) (k : ℕ) :
    Mono ((tensorPowerModule' L ((1 * k : ℕ) : ℤ)).unitHomEquiv.symm
      (sectionPow' L (sectionsDegreeOne L (s.eval (op ⊤))) k)) := by
  have hECD : Stacks.Divisors.IsEffectiveCartierDivisor (zeroScheme X L (s.eval (op ⊤))) :=
    (AlgebraicGeometry.isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection X L s).2 hs
  have h := AlgebraicGeometry.zeroScheme_sectionPow'_degreeOne L (s.eval (op ⊤)) k
  refine (AlgebraicGeometry.isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection X _ _).1 ?_
  exact h ▸ Stacks.Divisors.isEffectiveCartierDivisor_pow hECD k

/-- **The zero scheme of a positive power of a section is homeomorphic to the zero scheme of
the section.** The two ideal sheaves differ by a power, and a power has the same support. -/
def zeroSchemeSectionPowHomeo (s : L.sections) (k : ℕ) (hk : k ≠ 0) :
    (zeroScheme X L (s.eval (op ⊤))).subscheme ≃ₜ
      (zeroScheme X (tensorPowerModule' L ((1 * k : ℕ) : ℤ))
        ((sectionPow' L (sectionsDegreeOne L (s.eval (op ⊤))) k).eval (op ⊤))).subscheme :=
  subschemeHomeoOfSupportEq
    (((congrArg Scheme.IdealSheafData.support
        (AlgebraicGeometry.zeroScheme_sectionPow'_degreeOne L (s.eval (op ⊤)) k)).trans
      (Scheme.IdealSheafData.support_pow _ k hk)).symm)

end Stacks.AmpleSectionConnected

end
