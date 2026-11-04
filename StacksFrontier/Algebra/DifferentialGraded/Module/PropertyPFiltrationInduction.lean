module

public import StacksFrontier.Algebra.DifferentialGraded.Module.Bijective
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryCoproducts
public import StacksFrontier.Algebra.DifferentialGraded.Module.Telescope

/-! # Induction along a property-(P) filtration

Let `(A, d)` be a differential graded algebra over a commutative ring `R` and let `P` be a right
differential graded `A`-module carrying a property-(P) filtration `0 = F_{-1} ⊆ F_0 ⊆ ⋯ ⊆ P`. A
property of right differential graded `A`-modules which is invariant under isomorphism, holds on
every direct sum of shifts of `A`, is stable under countable direct sums, and is stable under
both extensions and cokernels along admissible short exact sequences, holds at `P`.

## Main results

* `DifferentialGradedModule.PropertyPFiltration.nonempty_telescopeDirectSumObjIso`: a module with
  the universal property of the direct sum of the stages is isomorphic to `directSumObj` of them.
* `DifferentialGradedModule.propertyPFiltration_stage_induction`: the closure properties give the
  property at every stage of the filtration.
* `DifferentialGradedModule.propertyPFiltration_induction`: a property with these closure
  properties holds at every module carrying a property-(P) filtration.

## References

* [Stacks Project, Tag 09KK](https://stacks.math.columbia.edu/tag/09KK), property (P).
* [Stacks Project, Tag 09KL](https://stacks.math.columbia.edu/tag/09KL), the telescope.
* [Stacks Project, Tag 0FQE](https://stacks.math.columbia.edu/tag/0FQE), dévissage.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}

namespace PropertyPFiltration

variable {P : DifferentialGradedModule A} (F : PropertyPFiltration P)

/-- A module `S` with maps `lift i : F.F i ⟶ S` exhibiting it as a direct sum of the stages of
the property-(P) filtration `F` is isomorphic to the direct sum `directSumObj` of those stages,
indexed by `ULift ℕ`. -/
theorem nonempty_telescopeDirectSumObjIso {S : DifferentialGradedModule A}
    (lift : ∀ i : ℕ, F.F i ⟶ S)
    (huniv : ∀ (T : DifferentialGradedModule A) (g : ∀ i : ℕ, F.F i ⟶ T),
      ∃! h : S ⟶ T, ∀ i : ℕ, lift i ≫ h = g i) :
    Nonempty (S ≅ directSumObj (fun j : ULift.{u} ℕ => F.F j.down)) := by
  obtain ⟨h, hh, -⟩ :=
    huniv (directSumObj (fun j : ULift.{u} ℕ => F.F j.down))
      (fun i => directSumInj (fun j : ULift.{u} ℕ => F.F j.down) (ULift.up i))
  obtain ⟨_, _, huniq⟩ := huniv S lift
  refine ⟨⟨h, directSumDesc (fun j : ULift.{u} ℕ => F.F j.down) (fun j => lift j.down), ?_, ?_⟩⟩
  · refine (huniq _ (fun i => ?_)).trans (huniq (𝟙 S) (fun i => Category.comp_id _)).symm
    rw [← Category.assoc, hh i, directSumInj_comp_directSumDesc]
  · refine directSum_hom_ext _ (fun j => ?_)
    rw [Category.comp_id, ← Category.assoc, directSumInj_comp_directSumDesc]
    exact hh j.down

end PropertyPFiltration

/-- A property of right differential graded `A`-modules which is invariant under isomorphism, holds
on every direct sum of shifts of `A`, and is stable under extensions along admissible short exact
sequences, holds at every stage of a property-(P) filtration. -/
theorem propertyPFiltration_stage_induction (property : DifferentialGradedModule A → Prop)
    (hiso : ∀ {M M' : DifferentialGradedModule A}, (M ≅ M') → property M → property M')
    (hcells : ∀ (ι : Type u) [DecidableEq ι] (k : ι → ℤ), property (directSumShifts A k))
    (hext : ∀ {K L M : DifferentialGradedModule A} (i : K ⟶ L) (p : L ⟶ M),
      IsAdmissibleShortExact i p → property K → property M → property L)
    {P : DifferentialGradedModule A} (F : PropertyPFiltration P) (i : ℕ) : property (F.F i) := by
  induction i with
  | zero =>
      exact hiso (Hom.isoOfBijective F.bottomMap F.bottom_bijective).symm
        (@hcells F.bottomIndex F.bottomDecidableEq F.bottomShift)
  | succ i ih =>
      exact hext (F.incl i) (F.quotientMap i) (F.isAdmissibleShortExact_incl_quotientMap i) ih
        (@hcells (F.quotientIndex i) (F.quotientDecidableEq i) (F.quotientShift i))

/-- **Induction along a property-(P) filtration.** A property of right differential graded
`A`-modules which is invariant under isomorphism, holds on every direct sum of shifts of `A`, is
stable under countable direct sums, and is stable under both extensions and cokernels along
admissible short exact sequences, holds at every module carrying a property-(P) filtration. -/
theorem propertyPFiltration_induction (property : DifferentialGradedModule A → Prop)
    (hiso : ∀ {M M' : DifferentialGradedModule A}, (M ≅ M') → property M → property M')
    (hcells : ∀ (ι : Type u) [DecidableEq ι] (k : ι → ℤ), property (directSumShifts A k))
    (hsums : ∀ N : ℕ → DifferentialGradedModule A, (∀ i, property (N i)) →
      property (directSumObj (fun j : ULift.{u} ℕ => N j.down)))
    (hext : ∀ {K L M : DifferentialGradedModule A} (i : K ⟶ L) (p : L ⟶ M),
      IsAdmissibleShortExact i p → property K → property M → property L)
    (hcoker : ∀ {K L M : DifferentialGradedModule A} (i : K ⟶ L) (p : L ⟶ M),
      IsAdmissibleShortExact i p → property K → property L → property M)
    {P : DifferentialGradedModule A} (F : PropertyPFiltration P) : property P := by
  obtain ⟨S, lift, α, β, huniv, _, _, hses⟩ := exists_telescope_of_propertyPFiltration F
  have hS : property S :=
    hiso (F.nonempty_telescopeDirectSumObjIso lift huniv).some.symm
      (hsums (fun i => F.F i)
        (propertyPFiltration_stage_induction property hiso hcells hext F))
  exact hcoker α β hses hS hS

end DifferentialGradedModule

end
