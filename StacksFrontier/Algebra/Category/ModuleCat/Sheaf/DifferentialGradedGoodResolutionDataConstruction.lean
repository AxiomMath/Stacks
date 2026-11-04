module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAdmissibleFlat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAdmissibleTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeAdmissible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullbackTensorLeftDerived
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedShiftFlat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedResolutionTower

/-!
# The flat-resolution theory of a sheaf of differential graded algebras

`SheafOfModules.DifferentialGradedModule.GoodResolutionData` consists of a notion of goodness,
the existence of a good resolution of every right differential graded module ([Stacks, Tag 0FSH]),
and the goodness of the cone of a homomorphism of good modules ([Stacks, Tag 0FSC]). Take goodness
to be conditions (1) and (2) of [Stacks, Tag 0FSA]: flat as a right graded module, and K-flat.
Then the cone clause holds: the cone of `ψ : 𝒫 ⟶ 𝒫'` sits in an admissible short exact sequence
`0 → 𝒫' → C(ψ) → 𝒫[1] → 0` (`isAdmissibleShortExact_conePackage`), the shift of a flat K-flat
module is flat and K-flat (`isGradedFlat_shift`, `isKFlat_shift`), and both conditions satisfy
two-out-of-three along an admissible short exact sequence. The resolution clause is
`SheafOfModules.DifferentialGradedModule.exists_flat_quasiIso`.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.GoodResolutionData.ofFlatResolutions`: the
  flat-resolution theory of `(𝒜, d)`, built from the existence of flat K-flat resolutions.
* `SheafOfModules.DifferentialGradedModule.GoodResolutionData.flat`: the flat-resolution theory
  of `(𝒜, d)`, with the flat K-flat modules as its good modules.

## Main results

* `SheafOfModules.DifferentialGradedModule.isGradedFlat_and_isKFlat_cone`: **Tag 0FSC for
  conditions (1) and (2).** The cone of a homomorphism between right differential graded
  modules which are flat and K-flat is flat and K-flat.

## References

* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
* [Stacks Project, Tag 0FSC](https://stacks.math.columbia.edu/tag/0FSC)
* [Stacks Project, Tag 0FSH](https://stacks.math.columbia.edu/tag/0FSH)
* [Stacks Project, Tag 0FS5](https://stacks.math.columbia.edu/tag/0FS5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe t m v u

namespace SheafOfModules

namespace DifferentialGradedModule

section Construction

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]
  [HasWeakSheafify J (Type m)]
  {Osharp : Sheaf J CommRingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, m} (toRingCat J Osharp)}

omit [HasWeakSheafify J (Type m)] in
/-- **Tag 0FSC for conditions (1) and (2) of Tag 0FSA, at a cone.** The cone of a homomorphism
of right differential graded `𝒜`-modules which are flat as right graded modules and K-flat is
again flat and K-flat. -/
theorem isGradedFlat_and_isKFlat_cone {P P' : DifferentialGradedModule.{t, m, m} A}
    (ψ : P ⟶ P')
    (hP : RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded P) ∧
      RelativeTensor.IsKFlat P)
    (hP' : RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded P') ∧
      RelativeTensor.IsKFlat P') :
    RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded (cone ψ)) ∧
      RelativeTensor.IsKFlat (cone ψ) :=
  ⟨(isAdmissibleShortExact_conePackage ψ).isGradedFlat_middle hP'.1
      (isGradedFlat_shift P hP.1),
    (isAdmissibleShortExact_conePackage ψ).isKFlat_middle hP'.2 (isKFlat_shift P hP.2)⟩

/-- **The flat-resolution theory of `(𝒜, d)`, from the existence of resolutions.** Its good
modules are those flat as a right graded module and K-flat, and the existence of good resolutions
is the hypothesis `hres`. -/
def GoodResolutionData.ofFlatResolutions
    (hres : ∀ M : DifferentialGradedModule.{t, m, m} A,
      ∃ (Q : DifferentialGradedModule.{t, m, m} A) (f : Q ⟶ M),
        QuasiIso f.toHomologicalComplex ∧
          RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded Q) ∧
            RelativeTensor.IsKFlat Q) :
    GoodResolutionData.{t, m, m, v, u} A where
  IsGood P := RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded P) ∧
    RelativeTensor.IsKFlat P
  exists_isGood M := by
    obtain ⟨Q, f, hf, h⟩ := hres M
    exact ⟨Q, f, h, hf⟩
  isGood_cone ψ hP hP' := isGradedFlat_and_isKFlat_cone ψ hP hP'

omit [HasWeakSheafify J (Type m)] in
/-- The good modules of `GoodResolutionData.ofFlatResolutions` are the flat K-flat ones. -/
@[simp]
theorem GoodResolutionData.ofFlatResolutions_isGood (hres) :
    (GoodResolutionData.ofFlatResolutions.{t, m, v, u} (A := A) hres).IsGood =
      fun P => RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded P) ∧
        RelativeTensor.IsKFlat P :=
  rfl

/-- **The flat-resolution theory of `(𝒜, d)`**, whose good modules are those flat as a right
graded module and K-flat, every right differential graded `𝒜`-module receiving a
quasi-isomorphism from a good one by `exists_flat_quasiIso`. -/
noncomputable def GoodResolutionData.flat : GoodResolutionData.{t, m, m, v, u} A :=
  GoodResolutionData.ofFlatResolutions fun M => exists_flat_quasiIso M

/-- The good modules of `GoodResolutionData.flat` are the flat K-flat ones. -/
@[simp]
theorem GoodResolutionData.flat_isGood :
    (GoodResolutionData.flat.{t, m, v, u} (A := A)).IsGood =
      fun P => RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded P) ∧
        RelativeTensor.IsKFlat P :=
  rfl

end Construction

end DifferentialGradedModule

end SheafOfModules

end
