module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionModule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeGradedModule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentChaoticSite
public import StacksFrontier.Algebra.DifferentialGraded.Module.LeftOrthogonalClosedBasis

/-!
# The sections of a free differential graded module on a chaotic site

Let `C` be a category carrying the chaotic topology `⊥`, let `R` be a sheaf of rings on it, let
`D` be a sheaf of differential graded `R`-algebras and let `S` be a sheaf of graded sets. On the
chaotic topology every presheaf is a sheaf, so the sheafification map from the presentation
`U ↦ ⨁_{s ∈ S(U)} s · D^{n - deg s}(U)` of the free module `D[S]` to its degree-`n` piece is
bijective on sections. Consequently the differential graded `D(U)`-module `D[S](U)` of sections
over `U` is free on the canonical generators: every section is uniquely a finite sum
`∑ e_s · a_s` with `a_s ∈ D(U)`, the generator `e_s` of a local section `s` of degree `i` being
closed and homogeneous of degree `i`.

So `D[S](U)` is a direct sum of shifts of the regular module of `D(U)`, and therefore lies in the
left orthogonal of the acyclic objects of the homotopy category of `D(U)`.

## Main definitions

* `SheafOfModules.freeUnitAddEquivBot`: the sheafification map on the sections over `U` of the
  presentation of `D[S]`, as an additive equivalence.
* `SheafOfModules.freeSectionGenerator`: the canonical generator attached to a homogeneous local
  section of `S`, as an element of `D[S](U)`.
* `SheafOfModules.freeSectionCoeff`: the coordinates of an element of `D[S](U)` with respect to
  the generators.

## Main results

* `SheafOfModules.isClosedBasis_freeSectionGenerator`: the generators are a basis of closed
  homogeneous elements of `D[S](U)`.
* `SheafOfModules.leftOrthogonal_acyclic'_sectionModule_freeDGModule`: **the module of sections
  of a free differential graded module over an object of a chaotic site is orthogonal on the left
  to the acyclic differential graded modules.**

## Implementation notes

Injectivity of the basis map is the left inverse `freeSectionCoeff`, which reads an element of
`D[S](U)` degree by degree through the inverse of the sheafification map and returns, for each
generator, its coefficient. Surjectivity is checked on the summands of the presentation by
`SheafOfModules.freeUnit_freeOf`, which says that every summand `s · a` is the generator of `s`
acted on by `a`. The degree bookkeeping on both sides is absorbed by `SheafOfModules.of_heq`.

## References

* [Stacks Project, Tag 0FSF](https://stacks.math.columbia.edu/tag/0FSF)
* [Stacks Project, Tag 09K1](https://stacks.math.columbia.edu/tag/09K1)
* [Stacks Project, Tag 09KM](https://stacks.math.columbia.edu/tag/09KM)
-/

@[expose] public noncomputable section

open CategoryTheory DirectSum

universe t m v u

namespace SheafOfModules

open Stacks Stacks.SheafOfGradedSets

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra
  Stacks.SheafOfModules.botWEqualsLocallyBijective

variable {C : Type u} [Category.{v} C] {R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{t}}
  [HasWeakSheafify (⊥ : GrothendieckTopology C) (Type m)]
  [HasWeakSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}]

/-! ### The sheafification map is bijective on a chaotic site -/

section Bijective

variable (A : GradedAlgebra.{t, m} R) (S : SheafOfGradedSets.{m} (⊥ : GrothendieckTopology C))

/-- **On a chaotic site the map from the presentation of `A[S]` to its degree-`n` piece is
bijective on sections**: every presheaf is a sheaf for the chaotic topology, so its
sheafification map is an isomorphism. -/
theorem freeUnit_app_bijective_bot (n : ℤ) (U : Cᵒᵖ) :
    Function.Bijective (fun ζ : freeSections A S n U => (freeUnit A S n).app U ζ) := by
  have : IsIso (toSheafify (⊥ : GrothendieckTopology C) (freePres A S n).presheaf) :=
    isIso_toSheafify _ (Presheaf.isSheaf_bot _)
  have h := ConcreteCategory.bijective_of_isIso
    ((toSheafify (⊥ : GrothendieckTopology C) (freePres A S n).presheaf).app U)
  exact h

/-- The map from the presentation of `A[S]` to its degree-`n` piece, on sections over `U` of a
chaotic site, as an additive equivalence. -/
def freeUnitAddEquivBot (n : ℤ) (U : Cᵒᵖ) :
    freeSections A S n U ≃+ (freePiece A S n).val.obj U :=
  AddEquiv.ofBijective (AddMonoidHom.mk' (fun ζ : freeSections A S n U =>
      (freeUnit A S n).app U ζ) (freeUnit_add A S n U))
    (freeUnit_app_bijective_bot A S n U)

/-- The equivalence `freeUnitAddEquivBot` sends a section of the presentation to its image under
the sheafification map. -/
@[simp] theorem freeUnitAddEquivBot_apply (n : ℤ) (U : Cᵒᵖ) (ζ : freeSections A S n U) :
    freeUnitAddEquivBot A S n U ζ = (freeUnit A S n).app U ζ := rfl

/-- The inverse of `freeUnitAddEquivBot` sends the image of a section of the presentation under
the sheafification map back to that section. -/
theorem freeUnitAddEquivBot_symm_freeUnit (n : ℤ) (U : Cᵒᵖ) (ζ : freeSections A S n U) :
    (freeUnitAddEquivBot A S n U).symm ((freeUnit A S n).app U ζ) = ζ :=
  (freeUnitAddEquivBot A S n U).symm_apply_apply ζ

end Bijective

/-! ### The generators and the coordinates of a section -/

variable (S : SheafOfGradedSets.{m} (⊥ : GrothendieckTopology C))
  (D : DifferentialGradedAlgebra.{t, m} R) (U : Cᵒᵖ)

/-- **The canonical generator of `D[S](U)`** attached to a homogeneous local section of `S`:
the generator of `D[S]` of that section, in the summand of its degree. -/
def freeSectionGenerator (p : S.Index U) : ((freeDGModule S D).sectionModule U).M :=
  DirectSum.of ((freeDGModule S D).sectionsPiece U) p.1
    (freeGeneratorSection D.toGradedAlgebra S p.1 U p.2.1 p.2.2)

/-- The coordinates of a section of the presentation of `D[S]` in degree `n`: the summand
`s · a` goes to the family which is `a` at the generator of `s` and zero elsewhere. -/
def freeCoeffPres (n : ℤ) :
    freeSections D.toGradedAlgebra S n U →+
      ⨁ _ : S.Index U, D.toGradedAlgebra.totalSections U :=
  DirectSum.toAddMonoid fun p =>
    (DirectSum.of (fun _ : S.Index U => D.toGradedAlgebra.totalSections U) p).comp
      (DirectSum.of (D.toGradedAlgebra.sectionsPiece U) (n - p.1))

omit [HasWeakSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}] in
/-- The coordinates of the summand `s · x` of the presentation of `D[S]` in degree `n`, for `s` of
degree `i`, are `x` at the generator of `s` and zero elsewhere. -/
theorem freeCoeffPres_freeOf (n : ℤ) (i : ℤ) (s : S.sheaf.obj.obj U) (hs : S.HasDegree U s i)
    (x : (D.toGradedAlgebra.piece (n - i)).val.obj U) :
    freeCoeffPres S D U n (freeOf D.toGradedAlgebra S n U i s hs x) =
      DirectSum.of (fun _ : S.Index U => D.toGradedAlgebra.totalSections U) ⟨i, s, hs⟩
        (DirectSum.of (D.toGradedAlgebra.sectionsPiece U) (n - i) x) :=
  DirectSum.toAddMonoid_of _ _ _

/-- **The coordinates of a section of `D[S]` over `U`** with respect to the canonical
generators, read degree by degree through the inverse of the sheafification map. -/
def freeSectionCoeff :
    ((freeDGModule S D).sectionModule U).M →+
      ⨁ _ : S.Index U, D.toGradedAlgebra.totalSections U :=
  DirectSum.toAddMonoid fun n =>
    (freeCoeffPres S D U n).comp (freeUnitAddEquivBot D.toGradedAlgebra S n U).symm.toAddMonoidHom

/-- The coordinates of the image in `D[S](U)` of a section of the presentation of `D[S]` in degree
`n` are its coordinates `freeCoeffPres` in the presentation. -/
theorem freeSectionCoeff_of_freeUnit (n : ℤ) (ζ : freeSections D.toGradedAlgebra S n U) :
    freeSectionCoeff S D U (DirectSum.of ((freeDGModule S D).sectionsPiece U) n
      ((freeUnit D.toGradedAlgebra S n).app U ζ)) = freeCoeffPres S D U n ζ :=
  (DirectSum.toAddMonoid_of _ _ _).trans
    (congrArg (freeCoeffPres S D U n) (freeUnitAddEquivBot_symm_freeUnit D.toGradedAlgebra S n U ζ))

omit [HasWeakSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}] in
/-- The coordinates of a homogeneous section of `D[S]` of degree `n` at a generator of degree
`i` are homogeneous of degree `n - i`. -/
theorem freeCoeffPres_mem (n : ℤ) (ζ : freeSections D.toGradedAlgebra S n U) (p : S.Index U) :
    freeCoeffPres S D U n ζ p ∈
      Stacks.ExternalGrading.intSummand (D.toGradedAlgebra.sectionsPiece U) (n - p.1) := by
  induction ζ using freeSections_induction with
  | hzero => rw [map_zero, DirectSum.zero_apply]; exact Submodule.zero_mem _
  | hof i s hs x =>
      rw [freeCoeffPres_freeOf]
      by_cases hp : (⟨i, s, hs⟩ : S.Index U) = p
      · subst hp
        rw [DirectSum.of_eq_same]
        exact Stacks.ExternalGrading.of_mem_intSummand _ _ _
      · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hp)]
        exact Submodule.zero_mem _
  | hadd ζ ζ' hζ hζ' => rw [map_add, DirectSum.add_apply]; exact Submodule.add_mem _ hζ hζ'

/-! ### The basis map -/

/-- The basis map on a generator acted on by a homogeneous section of `D`: it is the action of
`D` on the generator, in the summand of the total degree. -/
theorem basisMap_freeSectionGenerator_of_of (p : S.Index U) (j : ℤ)
    (a : D.toGradedAlgebra.sectionsPiece U j) :
    DifferentialGradedModule.basisMap ((freeDGModule S D).sectionModule U)
        (freeSectionGenerator S D U)
        (DirectSum.of (fun _ : S.Index U => (D.sectionAlgebra U).A) p
          (DirectSum.of (D.toGradedAlgebra.sectionsPiece U) j a)) =
      DirectSum.of ((freeDGModule S D).sectionsPiece U) (p.1 + j)
        ((freeActBilin D.toGradedAlgebra S p.1 j).app U
          (freeGeneratorSection D.toGradedAlgebra S p.1 U p.2.1 p.2.2) a) := by
  refine (DifferentialGradedModule.basisMap_of _ _ p _).trans ?_
  exact (congrArg (fun f => f (DirectSum.of (D.toGradedAlgebra.sectionsPiece U) j a))
      (DifferentialGradedModule.act_of (freeDGModule S D) U p.1
        (freeGeneratorSection D.toGradedAlgebra S p.1 U p.2.1 p.2.2))).trans
    (DifferentialGradedModule.actOn_of (freeDGModule S D) U p.1 j _ a)

/-- **The coordinates are a left inverse of the basis map.** -/
theorem freeSectionCoeff_comp_basisMap :
    (freeSectionCoeff S D U).comp (DifferentialGradedModule.basisMap
      ((freeDGModule S D).sectionModule U) (freeSectionGenerator S D U)).toAddMonoidHom =
      AddMonoidHom.id _ := by
  refine DirectSum.addHom_ext' fun p => ?_
  refine DirectSum.addHom_ext (β := D.toGradedAlgebra.sectionsPiece U) fun j a => ?_
  change freeSectionCoeff S D U (DifferentialGradedModule.basisMap
      ((freeDGModule S D).sectionModule U) (freeSectionGenerator S D U)
        (DirectSum.of (fun _ : S.Index U => (D.sectionAlgebra U).A) p
          (DirectSum.of (D.toGradedAlgebra.sectionsPiece U) j a))) =
    DirectSum.of (fun _ : S.Index U => (D.sectionAlgebra U).A) p
      (DirectSum.of (D.toGradedAlgebra.sectionsPiece U) j a)
  obtain ⟨i, s, hs⟩ := p
  refine (congrArg (freeSectionCoeff S D U)
    ((basisMap_freeSectionGenerator_of_of S D U ⟨i, s, hs⟩ j a).trans
      (congrArg (DirectSum.of ((freeDGModule S D).sectionsPiece U) (i + j))
        (freeActBilin_generator D.toGradedAlgebra S i j U s hs a
          (add_sub_cancel_left i j).symm)))).trans ?_
  refine (freeSectionCoeff_of_freeUnit S D U (i + j) _).trans ?_
  refine (freeCoeffPres_freeOf S D U (i + j) i s hs _).trans ?_
  exact congrArg _ (of_heq (add_sub_cancel_left i j) (heq_castHom _ _ U a))

/-- **The coordinates are a left inverse of the basis map**, on elements. -/
theorem freeSectionCoeff_basisMap (z : ⨁ _ : S.Index U, (D.sectionAlgebra U).A) :
    freeSectionCoeff S D U (DifferentialGradedModule.basisMap
      ((freeDGModule S D).sectionModule U) (freeSectionGenerator S D U) z) = z :=
  DFunLike.congr_fun (freeSectionCoeff_comp_basisMap S D U) z

/-- **The basis map is surjective**: every summand `s · a` of the presentation of `D[S]` is the
generator of `s` acted on by `a`. -/
theorem basisMap_freeSectionGenerator_surjective :
    Function.Surjective (DifferentialGradedModule.basisMap
      ((freeDGModule S D).sectionModule U) (freeSectionGenerator S D U)) := by
  set B := (DifferentialGradedModule.basisMap ((freeDGModule S D).sectionModule U)
    (freeSectionGenerator S D U)).toAddMonoidHom with hB
  suffices h : ∀ x, x ∈ B.range from fun x => (AddMonoidHom.mem_range.1 (h x))
  intro x
  induction x using DirectSum.induction_on with
  | zero => exact zero_mem _
  | add x x' hx hx' => exact add_mem hx hx'
  | of n y =>
      obtain ⟨ζ, rfl⟩ := (freeUnit_app_bijective_bot D.toGradedAlgebra S n U).2 y
      induction ζ using freeSections_induction with
      | hzero =>
          refine (congrArg (· ∈ B.range) ?_).mpr (zero_mem _)
          exact (congrArg (DirectSum.of ((freeDGModule S D).sectionsPiece U) n)
            (map_zero ((freeUnit D.toGradedAlgebra S n).app U).hom)).trans (map_zero _)
      | hof i s hs x =>
          refine ⟨DirectSum.of (fun _ : S.Index U => (D.sectionAlgebra U).A) ⟨i, s, hs⟩
            (DirectSum.of (D.toGradedAlgebra.sectionsPiece U) (n - i) x), ?_⟩
          refine (basisMap_freeSectionGenerator_of_of S D U ⟨i, s, hs⟩ (n - i) x).trans ?_
          refine of_heq (freeDegAdd n i) ?_
          refine (heq_castHom (freePiece D.toGradedAlgebra S) (freeDegAdd n i) U _).symm.trans ?_
          exact heq_of_eq (freeUnit_freeOf D.toGradedAlgebra S n i U s hs x (freeDegAdd n i))
      | hadd ζ ζ' hζ hζ' =>
          refine (congrArg (· ∈ B.range) ?_).mpr (add_mem hζ hζ')
          exact (congrArg (DirectSum.of ((freeDGModule S D).sectionsPiece U) n)
            (freeUnit_add D.toGradedAlgebra S n U ζ ζ')).trans (map_add _ _ _)

/-- **The canonical generators are a basis of closed homogeneous elements of `D[S](U)`** on a
chaotic site, the generator of a local section of degree `i` lying in degree `i`. -/
theorem isClosedBasis_freeSectionGenerator :
    DifferentialGradedModule.IsClosedBasis ((freeDGModule S D).sectionModule U)
      (fun p : S.Index U => p.1) (freeSectionGenerator S D U) where
  mem p := Stacks.ExternalGrading.of_mem_intSummand _ _ _
  d_eq_zero p :=
    (DifferentialGradedModule.sectionModule_d_of (freeDGModule S D) U p.1
      (freeGeneratorSection D.toGradedAlgebra S p.1 U p.2.1 p.2.2)).trans
    ((congrArg (DirectSum.of ((freeDGModule S D).sectionsPiece U) (p.1 + 1))
      (freeDGModule_d_freeGenerator S D p.1 U p.2.1 p.2.2)).trans (map_zero _))
  bijective := ⟨Function.LeftInverse.injective (freeSectionCoeff_basisMap S D U),
    basisMap_freeSectionGenerator_surjective S D U⟩
  mem_of_mem n z hz p := by
    obtain ⟨y, hy⟩ := hz
    obtain ⟨ζ, rfl⟩ := (freeUnit_app_bijective_bot D.toGradedAlgebra S n U).2 y
    have h2 : z = freeCoeffPres S D U n ζ :=
      (freeSectionCoeff_basisMap S D U z).symm.trans
        ((congrArg (freeSectionCoeff S D U) hy.symm).trans (freeSectionCoeff_of_freeUnit S D U n ζ))
    subst h2
    exact freeCoeffPres_mem S D U n ζ p

/-- **The module of sections of a free differential graded module over an object of a chaotic
site is orthogonal on the left to the acyclic differential graded modules**: it is a direct sum of
shifts of the regular module of `D(U)`, one for every homogeneous local section of `S` over `U`.
-/
theorem leftOrthogonal_acyclic'_sectionModule_freeDGModule :
    (_root_.DifferentialGradedModule.acyclic' (D.sectionAlgebra U)).leftOrthogonal
      ((_root_.DifferentialGradedModule.toHomotopyCategory (D.sectionAlgebra U)).obj
        ((freeDGModule S D).sectionModule U)) :=
  _root_.DifferentialGradedModule.leftOrthogonal_acyclic'_of_isClosedBasis
    (isClosedBasis_freeSectionGenerator S D U)

end SheafOfModules

end
