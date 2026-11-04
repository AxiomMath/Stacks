module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.Spaces
public import StacksFrontier.CategoryTheory.Sites.CechSheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDegreeZero.Augmentation
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDegreeZero.Evaluation

/-!
# The module-valued Čech complex of a sheaf of modules, and its degree zero cohomology

Let `R` be a sheaf of rings on the open-cover site of a topological space `X`, let `V` be an
open subset and let `U : ι → Opens X` be a family with `V = ⨆ i, U i`. The Čech complex of a
sheaf of `R`-modules `I` for this covering is a complex of modules over the ring `R(V)` of
sections on the covered open: one views the members of the covering in the slice category
`Over V`, restricts `I` to a sheaf of modules over the sheaf of rings `R.over V`, and then
regards it as a presheaf of `R(V)`-modules, which is possible because `Over.mk (𝟙 V)` is a
terminal object of `Over V`. This file carries out that construction and identifies the degree
`0` cohomology of the resulting complex with the module of sections of `I` over `V`.

This is the degree `0` half of [Stacks, Tag 01EP]. It uses no injectivity hypothesis; the
positive-degree half, for an injective sheaf of modules, is
`StacksFrontier/AlgebraicGeometry/Cohomology/CechModulesInjective.lean`.

## Main definitions

* `Stacks.Cohomology.sectionsPresheaf V I` is `I`, restricted to the opens over `V` and
  regarded as a presheaf of modules over `R(V)`, and `Stacks.Cohomology.sectionsSheaf V I` is
  the same thing with its sheaf condition.
* `Stacks.Cohomology.coverObject U hU i` is the `i`-th member of the covering, viewed in
  `Over V`.
* `Stacks.Cohomology.cechComplex V U hU I` is the module-valued Čech complex.
* `Stacks.Cohomology.sectionsToSlice V I` identifies the sections of `I` over `V` with the
  sections of `sectionsPresheaf V I` over the terminal object `Over.mk (𝟙 V)`, and
  `Stacks.Cohomology.cechDegreeZeroRestriction` is the resulting restriction map into degree
  `0` of the Čech complex.

## Main results

* `Stacks.Cohomology.coverSieve_mem`: the morphisms from the members of the covering to the
  terminal object of `Over V` generate a covering sieve of the slice site.
* `Stacks.Cohomology.existsUnique_cechRestrictionHomologyMap` (Stacks Tag 01EP, degree zero):
  there is a unique `R(V)`-linear map from the sections of `I` over `V` to the degree `0`
  cohomology of the Čech complex which is compatible with the restriction map, and it is an
  isomorphism.

## Implementation notes

The degree `0` identification is obtained from
`Stacks.CategoryTheory.CechComplex.existsUnique_isIso_homologyZero_of_isSheaf`, which is stated
for the terminal object `⊤_ C` of the site, whereas the slice site `Over V` has the preferred
terminal object `Over.mk (𝟙 V)`. The two are compared by `sliceTerminalIso`; the composite
`sectionsToSliceAug` of `sectionsToSlice` with that comparison is the isomorphism identifying
the source of the augmentation of the Čech complex with the module of sections over `V`, and
`cechDegreeZeroRestriction_eq` says that the restriction map of this file is that isomorphism
followed by the augmentation of `StacksFrontier/CategoryTheory/Sites/CechComplex.lean`.

`sectionsToSlice` is the identity on underlying elements; the content of the definition is that
the `R(V)`-module structure obtained by restriction of scalars along the unique morphism
`R(V) ⟶ R(V)` is the original one, which is `ModuleCat.restrictScalarsId'App`, and
`sectionsToSlice_hom_apply` records that the underlying function is the identity.

The universes of the space, the sheaf of rings, the modules and the covering are independent;
only the covering is required to be small relative to the modules, so that the products forming
the Čech complex exist.

## References

* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex (inter lift lift_comp_π hom_ext
  isLimitAugmentationFork)
open Stacks.Cohomology.CechZero (aug aug_comp_π aug_comp_d augFork)

universe uX uR uM uI

attribute [local instance] ModuleCat.hasLimitsOfSize

namespace Stacks.Cohomology

open Stacks.Cohomology.CechSheaf (SectionRing coverObject sectionsPresheaf)

variable {X : Type uX} [TopologicalSpace X]
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{uR}} {ι : Type uI}

/-- The `i`-th object of the cover of `V` by the opens `U i`, as an object over `V`, has
underlying open `U i`. -/
@[simp]
theorem coverObject_left {V : Opens X} (U : ι → Opens X) (hU : V = ⨆ i, U i) (i : ι) :
    (coverObject U hU i).left = U i :=
  rfl

/-! ### The sections over the opens contained in the covered one -/

/-- A sheaf of `R`-modules, restricted to the opens over `V` and regarded as a sheaf of modules
over the ring `R(V)` of sections on `V`. The restriction of scalars is along the unique morphism
from the terminal object of the slice category, which is `Over.mk (𝟙 V)`. -/
noncomputable def sectionsSheaf (V : Opens X) (I : SheafOfModules.{uM} R) :
    Sheaf ((Opens.grothendieckTopology X).over V) (ModuleCat.{uM} (SectionRing R V)) :=
  (SheafOfModules.forgetToSheafModuleCat (R.over V) (op (Over.mk (𝟙 V)))
    Over.mkIdTerminal.op).obj ((SheafOfModules.overFunctor R V).obj I)

/-- The presheaf underlying `sectionsSheaf V I` is `sectionsPresheaf V I`. -/
theorem sectionsSheaf_obj (V : Opens X) (I : SheafOfModules.{uM} R) :
    (sectionsSheaf V I).obj = sectionsPresheaf V I :=
  rfl

/-- **The sections of a sheaf of modules on the opens over `V` form a sheaf** of
`R(V)`-modules for the slice topology. -/
theorem isSheaf_sectionsPresheaf (V : Opens X) (I : SheafOfModules.{uM} R) :
    Presheaf.IsSheaf ((Opens.grothendieckTopology X).over V) (sectionsPresheaf V I) :=
  (sectionsSheaf V I).property

/-! ### The sections over the covered open -/

/-- **The sections of `I` over `V` are the sections of `sectionsPresheaf V I` over the terminal
object of the slice category.** Both are the same module; the restriction of scalars occurring
in the definition of `sectionsPresheaf` is along the identity of `R(V)`. -/
noncomputable def sectionsToSliceIso (V : Opens X) (I : SheafOfModules.{uM} R) :
    (SheafOfModules.evaluation R (op V)).obj I ≅
      (sectionsPresheaf V I).obj (op (Over.mk (𝟙 V))) :=
  (ModuleCat.restrictScalarsId'App _ (CechZero.hom_sectionsAtTop_eq_id V)
    ((SheafOfModules.evaluation R (op V)).obj I)).symm

/-- Sections on `V`, viewed as sections at the terminal object `Over.mk (𝟙 V)` of the slice
category over `V`. -/
noncomputable def sectionsToSlice (V : Opens X) (I : SheafOfModules.{uM} R) :
    (SheafOfModules.evaluation R (op V)).obj I ⟶
      (sectionsPresheaf V I).obj (op (Over.mk (𝟙 V))) :=
  (sectionsToSliceIso V I).hom

/-- `sectionsToSlice` is the identity on underlying elements. -/
@[simp]
theorem sectionsToSlice_hom_apply (V : Opens X) (I : SheafOfModules.{uM} R)
    (s : (SheafOfModules.evaluation R (op V)).obj I) : (sectionsToSlice V I).hom s = s :=
  rfl

/-- `sectionsToSlice` is an isomorphism of `R(V)`-modules. -/
instance isIso_sectionsToSlice (V : Opens X) (I : SheafOfModules.{uM} R) :
    IsIso (sectionsToSlice V I) :=
  inferInstanceAs (IsIso (sectionsToSliceIso V I).hom)

/-- The comparison between the terminal object of `Over V` supplied by the finite products of
the slice category and the preferred terminal object `Over.mk (𝟙 V)`. -/
noncomputable def sliceTerminalIso (V : Opens X) : (⊤_ (Over V)) ≅ Over.mk (𝟙 V) :=
  terminalIsTerminal.uniqueUpToIso Over.mkIdTerminal

/-- Sections on `V`, viewed as sections of `sectionsPresheaf V I` over the terminal object
`⊤_ (Over V)` used by the Čech complex. This is the isomorphism identifying the source of the
augmentation of the Čech complex. -/
noncomputable def sectionsToSliceAug (V : Opens X) (I : SheafOfModules.{uM} R) :
    (SheafOfModules.evaluation R (op V)).obj I ⟶
      (sectionsPresheaf V I).obj (op (⊤_ (Over V))) :=
  sectionsToSlice V I ≫ (sectionsPresheaf V I).map (sliceTerminalIso V).hom.op

/-- `sectionsToSliceAug` is an isomorphism of `R(V)`-modules. -/
instance isIso_sectionsToSliceAug (V : Opens X) (I : SheafOfModules.{uM} R) :
    IsIso (sectionsToSliceAug V I) :=
  have : IsIso ((sectionsPresheaf V I).map (sliceTerminalIso V).hom.op) :=
    (sectionsPresheaf V I).map_isIso _
  IsIso.comp_isIso

/-! ### The covering sieve of the slice site -/

/-- **The members of a covering of `V`, viewed in the slice category, cover its terminal
object.** -/
theorem coverSieve_mem (V : Opens X) (U : ι → Opens X) (hU : V = ⨆ i, U i) :
    Sieve.ofArrows (coverObject U hU) (fun i ↦ terminal.from (coverObject U hU i)) ∈
      ((Opens.grothendieckTopology X).over V) (⊤_ (Over V)) := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  intro x hx
  have hxV : x ∈ V := leOfHom (⊤_ (Over V)).hom hx
  rw [hU, Opens.mem_iSup] at hxV
  obtain ⟨i, hi⟩ := hxV
  exact ⟨U i, (terminal.from (coverObject U hU i)).left, Sieve.ofArrows_mk _ _ i, hi⟩

/-! ### Degree zero of the module-valued Čech complex -/

variable [UnivLE.{uI, uM}]

/-- The module-valued Čech complex of `I` for the covering `U` of `V`: the Čech complex, in the
slice category over `V`, of the presheaf of `R(V)`-modules of sections of `I`. -/
noncomputable abbrev cechComplex (V : Opens X) (U : ι → Opens X) (hU : V = ⨆ i, U i)
    (I : SheafOfModules.{uM} R) : CochainComplex (ModuleCat.{uM} (SectionRing R V)) ℕ :=
  (cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)

/-- The restriction map from the sections of `I` on the covered open to degree `0` of its
module-valued Čech complex. -/
noncomputable def cechDegreeZeroRestriction (V : Opens X) (U : ι → Opens X) (hU : V = ⨆ i, U i)
    (I : SheafOfModules.{uM} R) :
    (SheafOfModules.evaluation R (op V)).obj I ⟶ (cechComplex V U hU I).X 0 :=
  sectionsToSlice V I ≫ lift (coverObject U hU) (sectionsPresheaf V I)
    (fun x ↦ (sectionsPresheaf V I).map
      (Over.mkIdTerminal.from (inter (coverObject U hU) x)).op)

/-- The restriction map into degree `0` of the Čech complex is the augmentation of
`StacksFrontier/CategoryTheory/Sites/CechComplex.lean`, precomposed with the identification of the
sections of `I` over `V` with the sections over the terminal object of the slice category. -/
theorem cechDegreeZeroRestriction_eq (V : Opens X) (U : ι → Opens X) (hU : V = ⨆ i, U i)
    (I : SheafOfModules.{uM} R) :
    cechDegreeZeroRestriction V U hU I =
      sectionsToSliceAug V I ≫
        aug (coverObject U hU) (sectionsPresheaf V I) terminalIsTerminal := by
  rw [cechDegreeZeroRestriction, sectionsToSliceAug, Category.assoc]
  refine congrArg (sectionsToSlice V I ≫ ·) (hom_ext _ _ fun x ↦ ?_)
  rw [lift_comp_π, Category.assoc, aug_comp_π, ← (sectionsPresheaf V I).map_comp,
    ← op_comp]
  exact congrArg _ (congrArg _ (Over.mkIdTerminal.hom_ext _ _))

/-- The degree `0` differential kills the restriction map. -/
theorem cechDegreeZeroRestriction_comp_d (V : Opens X) (U : ι → Opens X) (hU : V = ⨆ i, U i)
    (I : SheafOfModules.{uM} R) :
    cechDegreeZeroRestriction V U hU I ≫ (cechComplex V U hU I).d 0 1 = 0 := by
  rw [cechDegreeZeroRestriction_eq, Category.assoc, aug_comp_d, comp_zero]

/-- The restriction map is the augmentation read through the isomorphism `sectionsToSliceAug`. -/
theorem inv_sectionsToSliceAug_comp_cechDegreeZeroRestriction (V : Opens X) (U : ι → Opens X)
    (hU : V = ⨆ i, U i) (I : SheafOfModules.{uM} R) :
    inv (sectionsToSliceAug V I) ≫ cechDegreeZeroRestriction V U hU I =
      aug (coverObject U hU) (sectionsPresheaf V I) terminalIsTerminal := by
  rw [cechDegreeZeroRestriction_eq, IsIso.inv_hom_id_assoc]

/-- **The restriction map into degree `0` of the module-valued Čech complex is a kernel of the
first differential.** -/
noncomputable def isLimitCechDegreeZeroFork (V : Opens X) (U : ι → Opens X) (hU : V = ⨆ i, U i)
    (I : SheafOfModules.{uM} R) :
    IsLimit (KernelFork.ofι (cechDegreeZeroRestriction V U hU I)
      (cechDegreeZeroRestriction_comp_d V U hU I)) :=
  IsLimit.ofIsoLimit
    (isLimitAugmentationFork (coverObject U hU) (sectionsPresheaf V I)
      ((Opens.grothendieckTopology X).over V) (isSheaf_sectionsPresheaf V I)
      (coverSieve_mem V U hU))
    (Fork.ext (s := augFork (coverObject U hU) (sectionsPresheaf V I) terminalIsTerminal)
      (t := KernelFork.ofι (cechDegreeZeroRestriction V U hU I)
        (cechDegreeZeroRestriction_comp_d V U hU I))
      (asIso (sectionsToSliceAug V I)).symm
      (inv_sectionsToSliceAug_comp_cechDegreeZeroRestriction V U hU I))

/-- There is a unique `R(V)`-linear map from the sections of `I` over the covered open `V` to
the degree `0` Čech cohomology whose composite with the inclusion of the homology into the
opcycles is induced by the restriction map, and it is an isomorphism. -/
@[stacks 01EP "degree zero"]
theorem existsUnique_cechRestrictionHomologyMap (V : Opens X) (U : ι → Opens X)
    (hU : V = ⨆ i, U i) (I : SheafOfModules.{uM} R) :
    ∃! f : (SheafOfModules.evaluation R (op V)).obj I ⟶ (cechComplex V U hU I).homology 0,
      IsIso f ∧ f ≫ (cechComplex V U hU I).homologyι 0 =
        cechDegreeZeroRestriction V U hU I ≫ (cechComplex V U hU I).pOpcycles 0 :=
  Stacks.Cohomology.CechZero.existsUnique_homologyMap_of_isKernel _ _
    (cechDegreeZeroRestriction_comp_d V U hU I) (isLimitCechDegreeZeroFork V U hU I)

/-- The canonical restriction-induced map from the sections of `I` over the covered open to the
degree `0` Čech cohomology. -/
noncomputable def cechRestrictionHomologyMap (V : Opens X) (U : ι → Opens X)
    (hU : V = ⨆ i, U i) (I : SheafOfModules.{uM} R) :
    (SheafOfModules.evaluation R (op V)).obj I ⟶ (cechComplex V U hU I).homology 0 :=
  (existsUnique_cechRestrictionHomologyMap V U hU I).exists.choose

/-- The canonical restriction-induced map to the degree `0` Čech cohomology is an
isomorphism. -/
noncomputable instance isIso_cechRestrictionHomologyMap (V : Opens X) (U : ι → Opens X)
    (hU : V = ⨆ i, U i) (I : SheafOfModules.{uM} R) :
    IsIso (cechRestrictionHomologyMap V U hU I) :=
  (existsUnique_cechRestrictionHomologyMap V U hU I).exists.choose_spec.1

/-- The canonical `R(V)`-linear isomorphism from the sections of `I` over the covered open to
the degree `0` Čech cohomology. -/
noncomputable abbrev cechRestrictionHomologyIso (V : Opens X) (U : ι → Opens X)
    (hU : V = ⨆ i, U i) (I : SheafOfModules.{uM} R) :
    (SheafOfModules.evaluation R (op V)).obj I ≅ (cechComplex V U hU I).homology 0 :=
  asIso (cechRestrictionHomologyMap V U hU I)

/-- The canonical degree `0` isomorphism is induced by restriction to the members of the
covering. -/
@[reassoc]
theorem cechRestrictionHomologyIso_hom_homologyι (V : Opens X) (U : ι → Opens X)
    (hU : V = ⨆ i, U i) (I : SheafOfModules.{uM} R) :
    cechRestrictionHomologyMap V U hU I ≫ (cechComplex V U hU I).homologyι 0 =
      cechDegreeZeroRestriction V U hU I ≫ (cechComplex V U hU I).pOpcycles 0 :=
  (existsUnique_cechRestrictionHomologyMap V U hU I).exists.choose_spec.2

end Stacks.Cohomology

end
