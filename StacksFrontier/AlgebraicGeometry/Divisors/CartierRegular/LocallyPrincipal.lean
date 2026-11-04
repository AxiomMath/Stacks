module

public import StacksFrontier.AlgebraicGeometry.Divisors.CartierRegular.FrameSections
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Factorization
import all StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Factorization

/-!
# The zero scheme of a section is locally principal

The zero scheme `Z(s)` of a global section `s` of an invertible module `L` on a scheme `X` is a
locally principal closed subscheme: around every point there is an affine open on which `Z(s)` is
cut out by a single function. This is one of the four clauses of
[Stacks, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR), and it is what makes `Z(s)` a
candidate for being an effective Cartier divisor — the remaining condition, that the generator be
a nonzerodivisor, is the content of the `"cartier_iff_regular"` clause.

## Main results

* `Stacks.Divisors.isLocallyPrincipal_zeroScheme` — the zero scheme of a section of an invertible
  module is locally principal.

## Implementation notes

The witness is a trivializing affine open, produced cofinally by the private
`Stacks.Divisors.exists_affine_frame_subset` of
`StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Factorization`, reached here by
`import all` rather than re-derived: that lemma is exactly the extraction of a rank-one datum from
[Stacks, Tag 0B8M] followed by a descent to an affine basis element, which is the first step of
the proof. On such an open the generator is `frameSections X L eU (s|_U)`, by
`Stacks.Divisors.zeroScheme_ideal_of_trivialization`.

## References

* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Divisors

/-- **Stacks 02OR**, the local principality clause. The zero scheme of a global section of an
invertible module on a scheme is a locally principal closed subscheme: on a trivializing affine
open it is cut out by the function representing the section.

The clause is registered on `AlgebraicGeometry.isLocallyPrincipal_zeroScheme`, which states it
for the same construction spelled `AlgebraicGeometry.zeroScheme`. -/
theorem isLocallyPrincipal_zeroScheme (X : Scheme.{u}) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) : IsLocallyPrincipal (zeroScheme X L s) := fun x => by
  obtain ⟨U, eU, hxU, -⟩ := exists_affine_frame_subset X L x ⊤ trivial
  refine ⟨U, hxU, ?_⟩
  rw [zeroScheme_ideal_of_trivialization X L s U (frameSections X L eU) _ rfl]
  exact ⟨_, rfl⟩

end Stacks.Divisors

end
