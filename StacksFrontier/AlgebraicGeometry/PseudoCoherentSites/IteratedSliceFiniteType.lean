module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeExtension
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeSheafSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalTypesUnderComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeOnSiteFromGeneratingSections
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeFromGlobalGenerators
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite type on an iterated slice

Let `R` be a sheaf of rings on a site `(C, J)`, let `M` be a sheaf of `R`-modules and let `U` be
an object of `C`.  Mathlib's finite-type condition `SheafOfModules.IsFiniteType` for the
restriction `M|_U` is a statement about the slice site `C/U`: it asks for a family of objects of
`C/U` covering its terminal object on each member of which `M|_U` has finitely many generating
global sections.  Those members are objects `W` of `C/U`, so the modules whose generators are
asked for live on the **iterated** slice `(C/U)/W`, whereas everything a development states about
`M` lives on the depth-one slices `C/W.left`.

This module is the dictionary between the two, for finite generating families of global sections,
together with the two forms in which a descent consumes it: a local criterion for
`IsFiniteType (M|_U)` and the unpacking of that hypothesis as a covering sieve of `U`.

## The dictionary

The comparison functor is `Stacks.SheafOfModules.sliceEquiv`, the *equivalence*
`SheafOfModules (R|_{W.left}) ≌ SheafOfModules ((R|_U)|_W)` induced by
`CategoryTheory.Over.iteratedSliceEquiv`, together with its two compatibilities
`Stacks.SheafOfModules.sliceEquivObjIso` (it matches `M|_{W.left}` with `(M|_U)|_W`) and
`Stacks.SheafOfModules.sliceEquivUnitIso` (it matches the two structure sheaves).

That is exactly the data which `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/`
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GlobalTypesUnderComparison.lean` — Descent,
Lemma 05VG for the global properties of Modules on
Sites, Definition 03DE — asks for: a full, faithful, coproduct-preserving functor carrying the
structure sheaf to the structure sheaf.  Its
`Stacks.Sheaves.GlobalTypeComparison.generatingSectionsMap` and `.generatingSectionsOfMap` move a
generating family of global sections in the two directions *without changing its index type*, so
finiteness is carried both ways with nothing to prove.  No morphism-level `rfl` about
`Stacks.SheafOfModules.sliceBackward` is used, and none is needed.

## Main results

* `Stacks.SheafOfModules.exists_isFiniteType_generatingSections_over_over_iff`: **the
  dictionary** — `(M|_U)|_W` has a finite generating family of global sections if and only if
  `M|_{W.left}` has one.
* `Stacks.SheafOfModules.exists_isFiniteType_generatingSections_of_generates`: finitely many
  sections over `U` generating `M` in the sectionwise sense of `PresheafOfModules.Generates` are
  a finite generating family of global sections of `M|_U`.
* `Stacks.SheafOfModules.isFiniteType_over_of_locally_finite_generators`: **the local criterion**
  — if a family of arrows into `U` generates a covering sieve and `M` has a finite generating
  family over each of its sources, then `M|_U` is of finite type.
* `Stacks.SheafOfModules.exists_covering_sieve_finite_generators_of_isFiniteType_over`: **the
  converse** — finite type of `M|_U` gives a covering sieve of `U` over each of whose arrows `M`
  has a finite generating family, on the ambient site.

## Implementation notes

**No `@[stacks]` attribute is attached to anything here.**  Finite type is the clause 03DL (5),
and its two renderings are carried elsewhere; what is below is a comparison of the slice
descriptions of one rendering, which is not a clause of 03DL or of any other tag.

The index type of the local criterion is `Type (max u v)` because that is where the objects of
`C/U` live, and `SheafOfModules.IsFiniteType` indexes its covering family by the universe of the
objects of the site it is read on.  `SheafOfModules.LocalGeneratorsData.shrink` is what makes that
no restriction.

The sheafification hypotheses on the doubly iterated slices `(J.over U).over W` are hypotheses of
the statements being compared — `((M.over U).over W).GeneratingSections` does not typecheck
without them — and not extra finiteness conditions.  On a site whose objects are small, or
essentially small, they are instances.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace Stacks.SheafOfModules

section Dictionary

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{w}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]

variable (R) in
omit [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **A finite generating family of global sections passes between a depth-one slice and an
iterated slice.**  For an object `W` of `C/U`, the module `(M|_U)|_W` on the iterated slice
`(C/U)/W` has a finite generating family of global sections if and only if the module
`M|_{W.left}` on the depth-one slice `C/W.left` has one.

The two are matched by the equivalence `Stacks.SheafOfModules.sliceEquiv` of
`CategoryTheory.Over.iteratedSliceEquiv`, which carries the structure sheaf to the structure
sheaf (`Stacks.SheafOfModules.sliceEquivUnitIso`) and `M|_{W.left}` to `(M|_U)|_W`
(`Stacks.SheafOfModules.sliceEquivObjIso`).  Transport of a generating family across such a
functor is Descent, Lemma 05VG for the clause 03DE (3), namely
`Stacks.Sheaves.GlobalTypeComparison.generatingSectionsMap` and `.generatingSectionsOfMap`; both
leave the index type alone, so finiteness needs no argument. -/
theorem exists_isFiniteType_generatingSections_over_over_iff
    (M : SheafOfModules.{w} R) (U : C) (W : Over U)
    [HasWeakSheafify ((J.over U).over W) AddCommGrpCat.{w}]
    [((J.over U).over W).WEqualsLocallyBijective AddCommGrpCat.{w}] :
    (∃ σ : ((M.over U).over W).GeneratingSections, σ.IsFiniteType) ↔
      ∃ σ : (M.over W.left).GeneratingSections, σ.IsFiniteType := by
  have hfull : (sliceEquiv R U W).functor.Full := inferInstance
  have hfaith : (sliceEquiv R U W).functor.Faithful := inferInstance
  have hcol : PreservesColimitsOfSize.{w, w} (sliceEquiv R U W).functor := inferInstance
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨Stacks.Sheaves.GlobalTypeComparison.generatingSectionsOfMap
      (sliceEquiv R U W).functor (sliceEquivUnitIso R U W)
      (SheafOfModules.GeneratingSections.equivOfIso
        (sliceEquivObjIso M U W).symm σ), ⟨?_⟩⟩
    exact hσ.finite
  · rintro ⟨σ, hσ⟩
    refine ⟨SheafOfModules.GeneratingSections.equivOfIso (sliceEquivObjIso M U W)
      (Stacks.Sheaves.GlobalTypeComparison.generatingSectionsMap
        (sliceEquiv R U W).functor (sliceEquivUnitIso R U W) σ), ⟨?_⟩⟩
    exact hσ.finite

omit [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **From the sectionwise form of generation to a finite generating family of global sections on
the slice.**  Finitely many sections of `M` over `U` which generate it in the sense of
`PresheafOfModules.Generates` are a finite generating family of global sections of `M|_U`.

The epimorphism out of the finite free module is
`Stacks.SheafOfModules.epi_freeHomEquiv_symm_mkOver`, whose index type must lie in the universe of
the sections; `Fin n` does not, so the family is reindexed by `ULift (Fin n)` with
`Stacks.SheafOfModules.generatesLocally_comp_equiv`, which changes nothing about finiteness. -/
@[ega "0 5.1.1" "partial"]
theorem exists_isFiniteType_generatingSections_of_generates (M : SheafOfModules.{w} R) {U : C}
    {n : ℕ} (s : Fin n → M.val.obj (op U))
    (hs : PresheafOfModules.Generates J M.val s) :
    ∃ σ : (M.over U).GeneratingSections, σ.IsFiniteType := by
  refine ⟨{ I := ULift.{w} (Fin n)
            s := fun i ↦ mkOver (M := M) (V := U) (s i.down)
            epi := epi_freeHomEquiv_symm_mkOver (fun i : ULift.{w} (Fin n) ↦ s i.down)
              (generatesLocally_comp_equiv Equiv.ulift s hs) }, ⟨?_⟩⟩
  exact inferInstanceAs (Finite (ULift.{w} (Fin n)))

variable (R) in
omit [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **The local criterion for finite type of a restriction to a slice.**  If a family of arrows
`f i : Y i ⟶ U` generates a covering sieve of `U` and `M|_{Y i}` has a finite generating family of
global sections for every `i`, then `M|_U` is of finite type.

The covering family that `SheafOfModules.IsFiniteType` asks for in the slice site is the given one
read there, which is `Stacks.SheafOfModules.coversTop_over_of_ofArrows_mem`, and its generators
are the given ones moved to the iterated slices by
`Stacks.SheafOfModules.exists_isFiniteType_generatingSections_over_over_iff`. -/
theorem isFiniteType_over_of_locally_finite_generators
    (M : SheafOfModules.{w} R) (U : C) {I : Type (max u v)} (Y : I → C) (f : ∀ i, Y i ⟶ U)
    [∀ W : Over U, HasWeakSheafify ((J.over U).over W) AddCommGrpCat.{w}]
    [∀ W : Over U, ((J.over U).over W).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (hcov : Sieve.ofArrows Y f ∈ J U)
    (hgen : ∀ i, ∃ σ : (M.over (Y i)).GeneratingSections, σ.IsFiniteType) :
    (M.over U).IsFiniteType := by
  have key : ∀ i, ∃ σ : ((M.over U).over (Over.mk (f i))).GeneratingSections, σ.IsFiniteType :=
    fun i ↦ (exists_isFiniteType_generatingSections_over_over_iff R M U (Over.mk (f i))).mpr
      (hgen i)
  exact ⟨⟨{ I := I, X := fun i ↦ Over.mk (f i)
            coversTop := coversTop_over_of_ofArrows_mem J U Y f hcov
            generators := fun i ↦ (key i).choose },
    ⟨fun i ↦ (key i).choose_spec⟩⟩⟩

variable (R) in
omit [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **Finite type of a restriction to a slice, read on the ambient site.**  If `M|_U` is of finite
type then there is a covering sieve of `U` over each of whose arrows `k : Z ⟶ U` the module `M|_Z`
has a finite generating family of global sections.

This is the converse of
`Stacks.SheafOfModules.isFiniteType_over_of_locally_finite_generators`, and it is the form in
which a descent consumes a finite-type hypothesis on a slice.  The covering family of
`SheafOfModules.IsFiniteType` covers the terminal object `Over.mk (𝟙 U)` of the slice, so
`CategoryTheory.GrothendieckTopology.mem_over_iff` turns it into a covering sieve of `U`; an arrow
in that sieve has a map to a member of the family by
`CategoryTheory.Sieve.mem_ofObjects_iff`, the member's generators come down to the depth-one slice
by `Stacks.SheafOfModules.exists_isFiniteType_generatingSections_over_over_iff`, and they restrict
along that map by
`Stacks.SheafOfModules.LocalCokernel.exists_finiteGeneratingSections_overMap`. -/
theorem exists_covering_sieve_finite_generators_of_isFiniteType_over
    (M : SheafOfModules.{w} R) (U : C)
    [∀ W : Over U, HasWeakSheafify ((J.over U).over W) AddCommGrpCat.{w}]
    [∀ W : Over U, ((J.over U).over W).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (h : (M.over U).IsFiniteType) :
    ∃ T : Sieve U, T ∈ J U ∧ ∀ ⦃Z : C⦄ (k : Z ⟶ U), T.arrows k →
      ∃ σ : (M.over Z).GeneratingSections, σ.IsFiniteType := by
  obtain ⟨σ, hσ⟩ := h.exists_localGeneratorsData
  refine ⟨Sieve.overEquiv (Over.mk (𝟙 U)) (Sieve.ofObjects σ.X (Over.mk (𝟙 U))),
    (J.mem_over_iff _).mp (σ.coversTop (Over.mk (𝟙 U))), ?_⟩
  intro Z k hk
  obtain ⟨i, ⟨a⟩⟩ := (Sieve.mem_ofObjects_iff σ.X
    (Over.homMk k : Over.mk (k ≫ (Over.mk (𝟙 U)).hom) ⟶ Over.mk (𝟙 U))).mp
      ((Sieve.overEquiv_iff (Sieve.ofObjects σ.X (Over.mk (𝟙 U))) k).mp hk)
  obtain ⟨τ, hτ⟩ := (exists_isFiniteType_generatingSections_over_over_iff R M U (σ.X i)).mp
    ⟨σ.generators i, hσ.isFiniteType i⟩
  have := hτ
  exact LocalCokernel.exists_finiteGeneratingSections_overMap M a.left τ

end Dictionary

end Stacks.SheafOfModules

end
