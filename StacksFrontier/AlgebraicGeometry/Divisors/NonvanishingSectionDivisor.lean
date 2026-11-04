module

public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionIntegral
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionCorrespondence
public import StacksFrontier.AlgebraicGeometry.AmplePowers.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiAffineNonvanishing.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Effective Cartier divisors from sections not vanishing at a point

On an integral scheme `X`, a global section `s` of an invertible module `𝓛` whose germ at some
point `x` generates the stalk is nonzero, hence a nonzerodivisor ([Stacks, Tag 01WY]); its zero
scheme is an effective Cartier divisor `D` ([Stacks, Tag 02OR] (4)) and `𝒪_X(D) ≅ 𝓛`
([Stacks, Tag 01X0]).

## Main results

* `AlgebraicGeometry.exists_isEffectiveCartierDivisor_iso_of_mem_nonvanishingLocus`: the
  statement above.

## References

* [Stacks Project, Tag 01WY](https://stacks.math.columbia.edu/tag/01WY)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
* [Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} [IsIntegral X]

/-- **An invertible module with a global section not vanishing at some point is the sheaf of an
effective Cartier divisor** on an integral scheme: the section is nonzero, hence a regular section,
its zero scheme `D` is an effective Cartier divisor and `𝒪_X(D) ≅ 𝓛`
([Stacks, Tag 02OR] (4) and [Stacks, Tag 01X0]). -/
@[sga "6 XIII 7.1.2" "(ii)⇒(i)"]
theorem exists_isEffectiveCartierDivisor_iso_of_mem_nonvanishingLocus (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (s : Γ(L, ⊤)) {x : X}
    (hx : x ∈ Stacks.Ample.nonvanishingLocus L s) :
    ∃ D : X.IdealSheafData, Stacks.Divisors.IsEffectiveCartierDivisor D ∧
      Nonempty (Stacks.Divisors.invertibleSheaf' D ≅ L) := by
  have : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    ‹SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L›
  have hs : s ≠ 0 := by
    rintro rfl
    rw [Stacks.Ample.nonvanishingLocus_zero] at hx
    exact hx
  have hevaltop : (Stacks.SheafOfModules.sectionsOfTop L s).eval (op ⊤) = s :=
    Stacks.SheafOfModules.sectionsOfTop_eval_top _ s
  have hreg : IsRegularSection X.sheaf.obj X.ringCatSheaf.property
      (Stacks.SheafOfModules.sectionsOfTop L s) :=
    isRegularSection_of_eval_top_ne_zero _ _ (hevaltop.symm ▸ hs)
  obtain ⟨e, -⟩ := (existsUnique_invertibleSheafIso_zeroScheme X L _ hreg).exists
  exact ⟨_, (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection X L _).2 hreg, ⟨e⟩⟩


end AlgebraicGeometry

end
