module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.ZeroSectionZeroScheme

/-!
# Regularity of the tautological section of `p^*(L^{⊗ -1})`

Let `p : Tot(L) ⟶ X` be the total space of an invertible module `L` with zero section `o`.
Clause (1) of [Stacks, Tag 0F96] says that `o(X)` is the zero scheme of a *regular* global
section of `p^*(L^{⊗ -1})`. The tautological section is constructed in `(p^*L)^{⊗ -1}`, and its
regularity there is `Stacks.LineBundle.Situation.isRegularSection_tautologicalSection`. This file
reads the same section in `p^*(L^{⊗ -1})` itself, through the dualization isomorphism
`Stacks.LineBundle.Situation.pullbackInverseIso`, and proves it regular there.

## Main results

* `Stacks.LineBundle.Situation.tautologicalSectionBaseSections`: the tautological section of
  `p^*(L^{⊗ -1})` as an element of the global sections.
* `Stacks.LineBundle.Situation.isRegularSection_tautologicalSectionBase`: that section is
  regular.

## References

* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-- The tautological global section of `p^*(L^{⊗ -1})`, as an element of the global sections of
that module: the tautological morphism out of the structure sheaf, followed by the dualization
isomorphism `(p^*L)^{⊗ -1} ≅ p^*(L^{⊗ -1})`. -/
def Situation.tautologicalSectionBaseSections : D.basePullbackInverse.sections :=
  SheafOfModules.unitHomEquiv D.basePullbackInverse
    (D.tautologicalSectionHom ≫ D.pullbackInverseIso.hom)

/-- The global-sections form of the tautological section of `p^*(L^{⊗ -1})` has
`Stacks.LineBundle.Situation.tautologicalSectionBase` as its value over the whole space. -/
theorem Situation.eval_tautologicalSectionBaseSections :
    D.tautologicalSectionBaseSections.eval (op ⊤) = D.tautologicalSectionBase := rfl

/-- The tautological global section of `p^*(L^{⊗ -1})` is a regular section, that is,
multiplication by it is injective. -/
@[stacks 0F96 "part (1), the section is regular"]
theorem Situation.isRegularSection_tautologicalSectionBase :
    AlgebraicGeometry.IsRegularSection D.totalSpace.sheaf.obj
      D.totalSpace.ringCatSheaf.property D.tautologicalSectionBaseSections := by
  have hZ : AlgebraicGeometry.zeroScheme D.totalSpace D.basePullbackInverse
      (D.tautologicalSectionBaseSections.eval (op ⊤)) = D.zeroSection.ker :=
    D.zeroScheme_tautologicalSectionBase_eq_ker_zeroSection
  refine (AlgebraicGeometry.isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection
    D.totalSpace D.basePullbackInverse _).mp ?_
  rw [hZ]
  exact D.isRelativeEffectiveCartierDivisor_ker_zeroSection.1

end Stacks.LineBundle

end
