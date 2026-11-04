module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedResolutionToposTower

/-!
# The flat-resolution theory of a sheaf of differential graded algebras at the goodness of Tag 0FSA

`SheafOfModules.DifferentialGradedModule.GoodResolutionData` is the part of the flat-resolution
theory that the derived tensor product and the derived pullback consume: a notion of goodness,
the existence of a good resolution of every right differential graded module (Tag 0FSH), and
the goodness of the cone of a homomorphism of good modules (Tag 0FSC). Its notion of goodness is
a parameter, and
`SheafOfModules.DifferentialGradedModule.GoodResolutionData.flat` of
`DifferentialGradedGoodResolutionDataConstruction.lean` is the term of it at conditions (1) and
(2) of Tag 0FSA alone — flat as a right graded module and K-flat.

This file takes goodness to be the whole of Tag 0FSA instead:
`SheafOfModules.IsGoodToposBaseChange`, which adds condition (3), the existence of a pullback
along every morphism of ringed topoi together with its flatness and K-flatness. At that reading
the resolution clause is Tag 0FSH over a ringed topos,
`SheafOfModules.DifferentialGradedModule.exists_good_quasiIso`, which takes `M` as its only
argument, so it is discharged here by substitution. The cone clause is Tag 0FSC at the same
reading, and it is the single hypothesis `hcone` of
`SheafOfModules.DifferentialGradedModule.GoodResolutionData.ofIsGoodToposBaseChange`.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.GoodResolutionData.ofIsGoodToposBaseChange`: **the
  flat-resolution theory of `(𝒜, d)` at the goodness of Tag 0FSA**, from Tag 0FSC at that
  goodness alone.

## Implementation notes

**Why condition (3) is wanted at all.** The two clauses of `GoodResolutionData` are satisfied by
conditions (1) and (2) of Tag 0FSA, which is why `GoodResolutionData.flat` exists. What asks for
more is the other package of the proof of Tag 0FTF,
`SheafOfModules.DifferentialGradedModule.PullbackTensorExactnessData`, whose
`acyclic_pullbackTensor` is Tag 0FSI: `f^*𝒬 ⊗_𝒜 𝒩` is acyclic for a good acyclic `𝒬`, and the
goodness there is the one whose base change is part of the statement. The two packages share
their `IsGood`, so the reading of goodness that makes Tag 0FSI available is the one this file
installs.

**Why the cone clause is a hypothesis in exactly the shape of the field it fills.** `hcone` is
written with the binders of `GoodResolutionData.isGood_cone`, at `IsGoodToposBaseChange` — a
homomorphism of good modules and the goodness of the cone, with nothing auxiliary — so that
Tag 0FSC at that goodness discharges it by substitution.

Condition (3) does **not** satisfy two-out-of-three along the admissible short exact sequence of
a cone, so `hcone` is not `isGradedFlat_and_isKFlat_cone` with a third conjunct bolted on.
Conditions (1) and (2) are properties of a given module; condition (3) carries an existential, a
pullback of the middle term having to be *constructed*, and that construction is a cone whose
universal property needs the base change of the cone on an identity rather than that of the
sub-object. The two are different data, as the implementation notes of
`ConeFreeDifferentialGradedModuleToposPullback.lean` and
`ConeIdentityFreeDifferentialGradedModuleToposPullback.lean` set out. What is available at the
goodness of Tag 0FSA is the cone of a homomorphism whose *source* is a free module,
`SheafOfModules.cone_freeDGModule_isGoodToposBaseChange`, which is what the tower of Tag 0FSH
runs on; the cone of an arbitrary homomorphism asks for the base change of `C(𝟙_𝒫)` for a good
`𝒫`, which free modules supply through
`SheafOfModules.coneIdentityFreeDGModule_isGoodToposBaseChange`.

**Universes.** `SheafOfModules.IsGoodToposBaseChange` is stated for a sheaf of differential
graded algebras `A : DifferentialGradedAlgebra.{w, w} (toRingCat Y.J Y.O)` over a ringed topos
`Y : AlgebraicGeometry.RingedTopos.{v₂, u₂, w}`, so the ring universe and the module universe
are identified, and `GoodResolutionData` is accordingly produced at `.{w, w, w, v₂, u₂}`. The
two remaining universes `v₁` and `u₁` are those of the second ringed topos over which condition
(3) quantifies; they are free, and the goodness installed in `IsGood` carries them.

## References

* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
* [Stacks Project, Tag 0FSC](https://stacks.math.columbia.edu/tag/0FSC)
* [Stacks Project, Tag 0FSH](https://stacks.math.columbia.edu/tag/0FSH)
* [Stacks Project, Tag 0FSI](https://stacks.math.columbia.edu/tag/0FSI)
* [Stacks Project, Tag 0FTF](https://stacks.math.columbia.edu/tag/0FTF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks Stacks.SheafOfGradedSets Stacks.Sheaves.RingedToposModules

universe w v₁ u₁ v₂ u₂

namespace SheafOfModules.DifferentialGradedModule

variable {Y : AlgebraicGeometry.RingedTopos.{v₂, u₂, w}}
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  [HasSheafify Y.J (Type w)]
  {A : DifferentialGradedAlgebra.{w, w} (toRingCat Y.J Y.O)}

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

/-- **The flat-resolution theory of `(𝒜, d)` at the goodness of Tag 0FSA**, from Tag 0FSC at
that goodness alone. Goodness is `SheafOfModules.IsGoodToposBaseChange`: flat as a right graded
module, K-flat, and such that along every morphism of ringed topoi out of the base, every sheaf
of differential graded algebras on its source and every unital homomorphism over it a pullback
exists and is again flat and K-flat.

The resolution clause is Tag 0FSH over a ringed topos,
`SheafOfModules.DifferentialGradedModule.exists_good_quasiIso`, whose only argument is the module
being resolved; the two conjuncts of its conclusion are the two of
`GoodResolutionData.exists_isGood` in the other order. The cone clause is the hypothesis `hcone`,
which is Tag 0FSC at this goodness written with the binders of
`GoodResolutionData.isGood_cone`. -/
noncomputable def GoodResolutionData.ofIsGoodToposBaseChange [HasWeakSheafify Y.J (Type w)]
    (hcone : ∀ {P P' : DifferentialGradedModule.{w, w, w} A} (ψ : P ⟶ P'),
      IsGoodToposBaseChange.{w, v₁, u₁} P → IsGoodToposBaseChange.{w, v₁, u₁} P' →
        IsGoodToposBaseChange.{w, v₁, u₁} (cone ψ)) :
    GoodResolutionData.{w, w, w, v₂, u₂} A where
  IsGood P := IsGoodToposBaseChange.{w, v₁, u₁} P
  exists_isGood M := by
    obtain ⟨Q, f, hf, hQ⟩ := exists_good_quasiIso.{w, v₁, u₁} M
    exact ⟨Q, f, hQ, hf⟩
  isGood_cone ψ hP hP' := hcone ψ hP hP'

/-- The good modules of `GoodResolutionData.ofIsGoodToposBaseChange` are the good ones of
Tag 0FSA. -/
@[simp]
theorem GoodResolutionData.ofIsGoodToposBaseChange_isGood [HasWeakSheafify Y.J (Type w)] (hcone) :
    (GoodResolutionData.ofIsGoodToposBaseChange.{w, v₁, u₁, v₂, u₂} (A := A) hcone).IsGood =
      fun P => IsGoodToposBaseChange.{w, v₁, u₁} P :=
  rfl

end SheafOfModules.DifferentialGradedModule

end
