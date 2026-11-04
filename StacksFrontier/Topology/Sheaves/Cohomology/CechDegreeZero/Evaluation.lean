module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechDegreeZero.Augmentation
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfSheavesOfModules.AugmentationIsAKernel

/-!
# Degree-zero Čech cohomology against the sections functor

`Stacks.Cohomology.CechSheaf.homologyZeroIso` identifies the degree-`0` cohomology of
the module-valued Čech complex with `(sectionsPresheaf V I).obj (op (Over.mk (𝟙 V)))`, the sections
of `I` over `V` as the Čech complex itself sees them. This file restates that against
`SheafOfModules.evaluation R (op V)`, the sections functor of the sheaf of modules, which is the
form the degree-zero clause of [Stacks, Tag 01EP] is usually wanted in.

## Main definitions

* `sectionsAtTopIso`: the two spellings of `Γ(V, I)` as an `R(V)`-module agree.
* `cechRestriction`: restriction of a section of `I` over `V` to the members of the covering,
  out of `(SheafOfModules.evaluation R (op V)).obj I`.

## Main results

* `existsUnique_cechRestrictionHomologyMap`: **[Stacks, Tag 01EP], degree zero.** There is a unique
  isomorphism `Γ(V, I) ≅ Ȟ⁰(𝒰, I)` compatible with restriction to the covering.
* `cechRestrictionHomologyIso` is that isomorphism.

## Implementation notes

**The scalar action.** `sectionsPresheaf V I` sends an object `W` of the slice over `V` to the
sections of `I` over `W` with the `R(V)`-action obtained by restricting scalars along
`R(V) ⟶ R(W)`; at the terminal object `Over.mk (𝟙 V)` the restriction is along `R(V) ⟶ R(V)`, a
ring map that is the identity but not syntactically so, so instance synthesis does not identify
the two actions. `ModuleCat.restrictScalarsId'App` restricts scalars along a map provably equal to
the identity, and `hom_sectionsAtTop_eq_id` supplies that proof: the morphism is
`(R.over V).obj.map` of the unique arrow out of a terminal object, so `IsTerminal.hom_ext` makes
it `𝟙`.

**Transporting the kernel.** `cechRestriction` is the augmentation precomposed with an
isomorphism, so `IsKernel.isoKernel` turns `isLimit_augmentedKernelFork` into the statement that it
too is a kernel of the first Čech differential.

## References

* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex
open Stacks.Cohomology.Basis (res)
open Stacks.Cohomology.CechSheaf

universe uX uR uM uI

attribute [local instance] ModuleCat.hasLimitsOfSize
attribute [local instance] AddCommGrpCat.hasLimitsOfSize

namespace Stacks.Cohomology.CechZero

noncomputable section

variable {X : Type uX} [TopologicalSpace X]
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{uR}}
  (V : Opens X) {ι : Type uI} [UnivLE.{uI, uM}] (U : ι → Opens X) (hU : V = ⨆ i, U i)
  (I : SheafOfModules.{uM} R)

/-- The module-valued Čech complex of the covering, as the value of `cechComplexFunctor`; it is
`Stacks.Cohomology.CechSheaf.cechComplex` by definition, reducibly. -/
abbrev cechCx : CochainComplex (ModuleCat.{uM} (SectionRing R V)) ℕ :=
  (cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)

omit [UnivLE.{uI, uM}] in
/-- **The restriction of scalars at the terminal object of the slice is the identity.** The ring
map along which `sectionsPresheaf` restricts scalars at `Over.mk (𝟙 V)` is `R(V) ⟶ R(V)` induced by
the unique arrow out of a terminal object, hence the identity. -/
theorem hom_sectionsAtTop_eq_id :
    ((R.over V).obj.map ((Over.mkIdTerminal (X := V)).op.to (op (Over.mk (𝟙 V))))).hom =
      RingHom.id (SectionRing R V) := by
  rw [(Over.mkIdTerminal (X := V)).op.hom_ext
    ((Over.mkIdTerminal (X := V)).op.to (op (Over.mk (𝟙 V)))) (𝟙 _),
    (R.over V).obj.map_id]
  rfl

/-- **The two spellings of `Γ(V, I)` as an `R(V)`-module agree.** The sections at the terminal
object of the slice over `V`, which is what the module-valued Čech complex is augmented by, are the
sections of `I` over `V`. -/
def sectionsAtTopIso :
    (sectionsPresheaf V I).obj (op (Over.mk (𝟙 V))) ≅ (SheafOfModules.evaluation R (op V)).obj I :=
  ModuleCat.restrictScalarsId'App _ (hom_sectionsAtTop_eq_id V) _

omit [UnivLE.{uI, uM}] in
/-- The forward map of `sectionsAtTopIso` is the identity on underlying elements. -/
@[simp]
theorem sectionsAtTopIso_hom_apply (t : ToType ((abSections I).obj (op V))) :
    ConcreteCategory.hom (sectionsAtTopIso V I).hom t = t := rfl

omit [UnivLE.{uI, uM}] in
/-- The inverse map of `sectionsAtTopIso` is the identity on underlying elements. -/
@[simp]
theorem sectionsAtTopIso_inv_apply (t : ToType ((abSections I).obj (op V))) :
    ConcreteCategory.hom (sectionsAtTopIso V I).inv t = t := rfl

/-- **Restriction to the members of the covering**, out of the sections of `I` over `V`. This is
the canonical map from sections on the covered open to degree `0` of the module-valued Čech
complex. -/
def cechRestriction :
    (SheafOfModules.evaluation R (op V)).obj I ⟶ (cechCx V U hU I).X 0 :=
  (sectionsAtTopIso V I).inv ≫ cechAugmentation V U hU I

/-- The components of `cechRestriction` are the restrictions of the section. -/
theorem mcomp_cechRestriction (t : ToType ((abSections I).obj (op V))) (x : Fin 1 → ι) :
    mcomp V U hU I (ConcreteCategory.hom (cechRestriction V U hU I) t) x =
      res (abSections I) (inter_le_covered V U hU x) t :=
  (congrArg (fun w ↦ mcomp V U hU I w x)
      (ConcreteCategory.comp_apply (sectionsAtTopIso V I).inv (cechAugmentation V U hU I) t)).trans
    (mcomp_cechAugmentation V U hU I t x)

/-- `cechRestriction` lands in the degree-`0` cycles. -/
theorem cechRestriction_comp_d :
    cechRestriction V U hU I ≫ (cechCx V U hU I).d 0 1 = 0 := by
  rw [cechRestriction, Category.assoc, cechAugmentation_comp_d, comp_zero]

include hU in
/-- **The sheaf condition, against the sections functor.** Restriction to the members of the
covering is a kernel of the first Čech differential. -/
def cechRestriction_isLimit :
    IsLimit (KernelFork.ofι (cechRestriction V U hU I) (cechRestriction_comp_d V U hU I)) :=
  IsKernel.isoKernel _ _ (isLimit_augmentedKernelFork V U hU I) (sectionsAtTopIso V I).symm rfl

include hU in
/-- **[Stacks, Tag 01EP], degree zero.** There is a unique morphism from the sections of `I` over
`V` to the degree-`0` cohomology of the module-valued Čech complex of the covering whose composite
with the canonical monomorphism out of homology is restriction to the covering followed by the
projection to opcycles, and it is an isomorphism. -/
theorem existsUnique_cechRestrictionHomologyMap :
    ∃! f : (SheafOfModules.evaluation R (op V)).obj I ⟶ (cechComplex V U hU I).homology 0,
      IsIso f ∧ f ≫ (cechComplex V U hU I).homologyι 0 =
        cechRestriction V U hU I ≫ (cechComplex V U hU I).pOpcycles 0 :=
  existsUnique_homologyMap_of_isKernel _ (cechRestriction V U hU I)
    (cechRestriction_comp_d V U hU I) (cechRestriction_isLimit V U hU I)

include hU in
/-- **[Stacks, Tag 01EP], degree zero, as an isomorphism of `R(V)`-modules.** The degree-`0`
cohomology of the module-valued Čech complex of a covering of `V` is the module of sections of `I`
over `V`. -/
def cechRestrictionHomologyIso :
    (cechComplex V U hU I).homology 0 ≅ (SheafOfModules.evaluation R (op V)).obj I :=
  (Stacks.Cohomology.CechSheaf.homologyZeroIso V U hU I) ≪≫ sectionsAtTopIso V I

end

end Stacks.Cohomology.CechZero

end
