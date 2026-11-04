module

public import StacksFrontier.AlgebraicGeometry.AmpleSurjectiveThickening.ObstructionVanishing
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Data.ZMod.Basic

/-!
# The cohomological lift of [Stacks, Tag 09MS] is satisfiable: a closed witness

We prove, with no hypotheses, an instance of the predicate
`Stacks.AmpleClosedImmersion.SectionsLiftAfterPower`. It appears as a hypothesis in several
declarations, among them the converse half of [Stacks, Tag 09MS]
(`Stacks.AmpleSurjectiveThickening.isAmple_of_isAmple_modulePullback_of_isZero_h1`, which takes
the vanishing of the obstruction group instead, the sole input of the lift). A hypothesis that
nothing produces is invisible to the compiler: the build succeeds and `#print axioms` is clean
whether or not it can ever be met. The closed term below shows that it can.

## Implementation notes

The thickening is `thickening : Spec (ZMod 2) ⟶ Spec (ZMod 4)`, the closed immersion cut out by
the ideal `(2) ⊆ ZMod 4`. That ideal is **nonzero** and its square is zero, so this is a genuine
square-zero thickening — the case the source of [Stacks, Tag 09MS] reduces to — and not the
degenerate `𝓘 = 0` where the immersion is an isomorphism. The module is `𝒪_X`, ample because `X` is
affine ([Stacks, Tag 01QE], `Stacks.Ample.isAmple_unitModule_of_isAffine`), and `X` is
proper over `ZMod 4` by the identity, so
`Stacks.AmpleSurjectiveThickening.sectionsLiftAfterPower_of_isAmple` applies.

What is degenerate here is only the ambient scheme: `X` is affine, so the obstruction group
vanishes for the trivial reason that all higher cohomology of a quasi-coherent module does. The
witness therefore certifies satisfiability of the predicate, not that the ample case it covers
is deep.

## Main results

* `Stacks.AmpleSurjectiveThickening.Example.sectionsLiftAfterPower_specZMod`: a closed term of
  `Stacks.AmpleClosedImmersion.SectionsLiftAfterPower`.

## References

* [Stacks Project, Tag 09MS](https://stacks.math.columbia.edu/tag/09MS)
* [Stacks Project, Tag 01QE](https://stacks.math.columbia.edu/tag/01QE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction
open Stacks.Ample Stacks.AmpleTheory

namespace Stacks.AmpleSurjectiveThickening.Example

/-- `2` divides `4` in `ℕ`, the divisibility the reduction map `redHom` is built from. -/
theorem two_dvd_four : (2 : ℕ) ∣ 4 := by norm_num

/-- The reduction `ZMod 4 ⟶ ZMod 2`, a surjection whose kernel `(2)` is nonzero of square
zero. -/
def redHom : CommRingCat.of (ZMod 4) ⟶ CommRingCat.of (ZMod 2) :=
  CommRingCat.ofHom (ZMod.castHom two_dvd_four (ZMod 2))

/-- The square-zero thickening `Spec (ZMod 2) ⟶ Spec (ZMod 4)`. -/
def thickening : Spec (CommRingCat.of (ZMod 2)) ⟶ Spec (CommRingCat.of (ZMod 4)) :=
  Spec.map redHom

/-- The thickening `Spec (ZMod 2) ⟶ Spec (ZMod 4)` is a closed immersion. -/
instance isClosedImmersion_thickening : IsClosedImmersion thickening :=
  IsClosedImmersion.spec_of_surjective redHom (ZMod.castHom_surjective two_dvd_four)

/-- **`Stacks.AmpleClosedImmersion.SectionsLiftAfterPower` is satisfiable**, with no hypothesis:
it holds for the square-zero thickening `Spec (ZMod 2) ⟶ Spec (ZMod 4)` and `𝒪_X`. -/
theorem sectionsLiftAfterPower_specZMod :
    Stacks.AmpleClosedImmersion.SectionsLiftAfterPower thickening
      (unitModule (Spec (CommRingCat.of (ZMod 4)))) :=
  Stacks.AmpleSurjectiveThickening.sectionsLiftAfterPower_of_isAmple thickening _
    (𝟙 (Spec (CommRingCat.of (ZMod 4))))
    (isAmple_unitModule_of_isAffine (Spec (CommRingCat.of (ZMod 4))))

end Stacks.AmpleSurjectiveThickening.Example

end
