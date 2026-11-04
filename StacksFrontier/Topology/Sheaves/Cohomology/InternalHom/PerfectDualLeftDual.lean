module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.CompositionApplicationLawGeneral
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedApplicationRightUnitLaw
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedDualEvaluationAsApplication
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RingedSitePerfectnessFromTheSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectnessFromTheRingedSite
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectStructureSheafWitness
import StacksCore.Tactic.StacksAttribute

/-!
# The derived dual of a perfect object is a left dual

Let `(X, O_X)` be a ringed space and let `K` be a perfect object of `D(O_X)`, with
`K^∨ = RSheafHom(K, O_X)`.  The canonical map `K ⊗^L_{O_X} K^∨ ⟶ RSheafHom(K, K)` is an
isomorphism; let `η : O_X ⟶ K ⊗^L_{O_X} K^∨` be the map sending `1` to the section corresponding
to `id_K` under it, and `ε : K^∨ ⊗^L_{O_X} K ⟶ O_X` the evaluation map.  Then `K^∨, η, ε` is a
left dual of `K` (Stacks 0FPC): the two triangle identities

`(1 ⊗ ε) ∘ (η ⊗ 1) = id_K` and `(ε ⊗ 1) ∘ (1 ⊗ η) = id_{K^∨}`

hold.  The first is the composite of the defining property of `η`, the unit law of the
application morphism, and the composition law
`Stacks.SheafOfModules.compositionApplicationLaw` at intermediate object `O_X`; the second
follows from the first because `ε` detects endomorphisms of `K^∨`.

## Main results

* `Stacks.SheafOfModules.exactPairingDerivedDual`: the exact pairing `(K, K^∨)` with
  coevaluation `η` and evaluation `ε`.
* `Stacks.SheafOfModules.derivedDual_isLeftDual`: Stacks 0FPC.

## References

* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
* [Stacks Project, Tag 0FFP](https://stacks.math.columbia.edu/tag/0FFP)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 0A8V](https://stacks.math.columbia.edu/tag/0A8V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)

/-- **The composition law at intermediate object the structure sheaf**, in the monoidal spelling
of Stacks 0FPT and with the inner application written as the evaluation `ε` of `K^∨`. -/
theorem derivedSheafHomComposition_structureSheaf_whiskerRight_comp_derivedSheafHomCounit
    (K : DerivedCategory (StructureSheafModules Rc)) :
    (letI := derivedMonoidalStructure Rc
    derivedSheafHomComposition Rc K
          (RingedSite.derivedStructureSheaf (ringedSite Rc)) K ▷ K ≫
        derivedSheafHomCounit Rc K K =
      (α_ (((derivedSheafHom Rc).obj
            (op (RingedSite.derivedStructureSheaf (ringedSite Rc)))).obj K)
          (derivedDual Rc K) K).hom ≫
        (((derivedSheafHom Rc).obj
            (op (RingedSite.derivedStructureSheaf (ringedSite Rc)))).obj K ◁
          derivedDualEvaluation Rc K) ≫
          derivedSheafHomCounit Rc
            (RingedSite.derivedStructureSheaf (ringedSite Rc)) K) := by
  have h := compositionApplicationLaw Rc K (RingedSite.derivedStructureSheaf (ringedSite Rc)) K
  unfold CompositionApplicationLaw at h
  rw [derivedSheafHomCounit_structureSheaf_eq_derivedDualEvaluation] at h
  exact h

variable (K : DerivedCategory (StructureSheafModules Rc))

/-- **The left dual of a perfect object.**  For a perfect `K` the coevaluation
`η = Stacks.SheafOfModules.derivedDualCoevaluation` and the evaluation
`ε = Stacks.SheafOfModules.derivedDualEvaluation` form an exact pairing of `K` with
`K^∨ = RSheafHom(K, O_X)`. -/
@[instance_reducible]
def exactPairingDerivedDual (hK : (ringedSite Rc).IsPerfect K) :
    (letI := derivedMonoidalStructure Rc
    ExactPairing K (derivedDual Rc K)) :=
  exactPairingDerivedDualOfCompositionLaw Rc K hK
    (derivedSheafHomComposition_structureSheaf_whiskerRight_comp_derivedSheafHomCounit Rc K)

/-- The coevaluation of `exactPairingDerivedDual` is `η`. -/
theorem exactPairingDerivedDual_coevaluation' (hK : (ringedSite Rc).IsPerfect K) :
    letI := derivedMonoidalStructure Rc
    (exactPairingDerivedDual Rc K hK).coevaluation' = derivedDualCoevaluation Rc K hK :=
  rfl

/-- The evaluation of `exactPairingDerivedDual` is `ε`. -/
theorem exactPairingDerivedDual_evaluation' (hK : (ringedSite Rc).IsPerfect K) :
    letI := derivedMonoidalStructure Rc
    (exactPairingDerivedDual Rc K hK).evaluation' = derivedDualEvaluation Rc K :=
  rfl

section RingedSpace



variable (X : RingedSpace.{u, u}) (K : DerivedCategory (StructureSheafModules X.sheaf))

/-- **Stacks 0FPC.**  Let `(X, O_X)` be a ringed space and let `K` be a perfect object of
`D(O_X)` (Tag 08CM), with `K^∨ = RSheafHom(K, O_X)`.  Then

* the map `c : K ⊗^L_{O_X} K^∨ ⟶ RSheafHom(K, K)` of Stacks 08I1 is an isomorphism;
* the coevaluation `η : O_X ⟶ K ⊗^L_{O_X} K^∨` is the map sending `1` to the section
  corresponding to `id_K` under `c`: `η ≫ c` is that section;
* with `ε : K^∨ ⊗^L_{O_X} K ⟶ O_X` the evaluation map, `K^∨, η, ε` is a left dual of `K`
  (Categories, Definition 0FFP): `(1 ⊗ ε) ∘ (η ⊗ 1) = id_K` and `(ε ⊗ 1) ∘ (1 ⊗ η) = id_{K^∨}`,
  read through the associativity and unit constraints of the monoidal structure of Stacks 0FPT on
  `D(O_X)`.

The evaluation is `Stacks.SheafOfModules.derivedDualEvaluation`, the application morphism of
Stacks 08J8 at target `O_X`
(`Stacks.SheafOfModules.derivedSheafHomCounit_structureSheaf_eq_derivedDualEvaluation`), and
the coevaluation is `Stacks.SheafOfModules.derivedDualCoevaluation`. -/
@[stacks 0FPC]
theorem derivedDual_isLeftDual (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X) K) :
    letI := derivedMonoidalStructure X.sheaf
    letI : MonoidalCategory (DerivedCategory (SheafOfModules.{u}
        (Tensor.ringSheaf.{u, u, u} X.sheaf))) := derivedMonoidalStructure X.sheaf
    IsIso (derivedTensorDualToSheafHom X.sheaf K K) ∧
      derivedDualCoevaluation X.sheaf K
          (Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect X K hK) ≫
          derivedTensorDualToSheafHom X.sheaf K K =
        RingedSite.derivedIdentitySection (ringedSite X.sheaf) K ∧
      derivedDualCoevaluation X.sheaf K
          (Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect X K hK) ▷ K ≫
          (α_ K (derivedDual X.sheaf K) K).hom ≫ K ◁ derivedDualEvaluation X.sheaf K =
        (λ_ K).hom ≫ (ρ_ K).inv ∧
      derivedDual X.sheaf K ◁ derivedDualCoevaluation X.sheaf K
          (Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect X K hK) ≫
          (α_ (derivedDual X.sheaf K) K (derivedDual X.sheaf K)).inv ≫
          derivedDualEvaluation X.sheaf K ▷ derivedDual X.sheaf K =
        (ρ_ (derivedDual X.sheaf K)).hom ≫ (λ_ (derivedDual X.sheaf K)).inv :=
  let := derivedMonoidalStructure X.sheaf
  let hK' := Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect X K hK
  ⟨isIso_derivedTensorDualToSheafHom_self X.sheaf K hK',
    derivedDualCoevaluation_comp X.sheaf K hK',
    (exactPairingDerivedDual X.sheaf K hK').evaluation_coevaluation',
    (exactPairingDerivedDual X.sheaf K hK').coevaluation_evaluation'⟩

/-- **The hypothesis of `derivedDual_isLeftDual` is inhabited by the structure sheaf**: `O_X` in
degree zero is perfect in the sense of Stacks 08CM.  It is not a zero object as soon as `1 ≠ 0`
in one section ring (`Stacks.SheafOfModules.not_isZero_derivedStructureSheaf`), for instance on
`Spec ℤ` (`Stacks.SheafOfModules.OnSpace.not_isZero_derivedStructureSheaf_specULiftInt`). -/
theorem isPerfect_derivedStructureSheaf_space :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X)
      (RingedSite.derivedStructureSheaf (ringedSite X.sheaf)) :=
  Stacks.Cohomology.PerfectComplexes.isPerfect_of_ringedSite X _
    (isPerfect_derivedStructureSheaf X.sheaf)

end RingedSpace

end Stacks.SheafOfModules

end
