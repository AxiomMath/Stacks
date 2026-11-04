module

public import Mathlib.Algebra.Homology.QuasiIso
public import
  StacksFrontier.Topology.Sheaves.Cohomology.CechOfSheavesOfModules.ModuleValuedAlternatingComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfSheavesOfModules.SliceSiteComparison

/-!
# The alternating Čech complex computes module-valued Čech cohomology, linearly

Let `X` be a topological space carrying a sheaf of rings `R`, let `V` be an open subset, let
`U : ι → Opens X` be a cover of `V` and let `I` be a sheaf of `R`-modules. The Čech cohomology of
`I` for that cover is the homology of `Stacks.Cohomology.CechSheaf.cechComplex`, a complex of
`R(V)`-modules built on the slice site over `V`. The existing
`Stacks.Cohomology.CechSheaf.alternatingCechHomologyIso` identifies it with the homology of the
alternating Čech complex of Tag 01FH, but only after forgetting the module structures: the
alternating complex it uses is a complex of abelian groups.

This file removes that forgetful functor. The alternating Čech complex of `R(V)`-modules
`Stacks.Cohomology.CechSheaf.alternatingModuleComplex` maps `R(V)`-linearly to the slice model,
and that map induces an isomorphism on homology *in `ModuleCat R(V)`*. So an alternating —
equivalently, by Tag 01FJ, an ordered — Čech computation computes the module-valued Čech
cohomology as a module and not merely as an abelian group, which is what a consumer stating an
isomorphism of `R`-modules needs.

## Main definitions

* `Stacks.Cohomology.CechSheaf.toCochainMod`: taking the family of components of a cochain of the
  slice model, as a morphism of `R(V)`-modules.
* `Stacks.Cohomology.CechSheaf.cechComplexModuleIso`: **the bridge.** The slice model is the
  explicit usual Čech complex of `R(V)`-modules.
* `Stacks.Cohomology.CechSheaf.alternatingInclusionToCechComplex`: the `R(V)`-linear inclusion of
  the alternating Čech complex into the slice model.
* `Stacks.Cohomology.CechSheaf.cechModuleComplexForget` and
  `Stacks.Cohomology.CechSheaf.alternatingModuleComplexForget`: forgetting the module structures
  recovers the complexes of Tag 01FH.
* `Stacks.Cohomology.CechSheaf.alternatingCechHomologyModuleIso` and
  `Stacks.Cohomology.CechSheaf.orderedCechHomologyModuleIso`: **the module-valued Čech cohomology
  of the cover is the homology of the alternating, equivalently of the ordered, Čech complex**, as
  `R(V)`-modules, in every degree.

## Main results

* `Stacks.Cohomology.CechSheaf.mcomp_smul` and
  `Stacks.Cohomology.CechSheaf.toCochainFun_smul`: taking components of a cochain of the slice
  model is `R(V)`-linear.
* `Stacks.Cohomology.CechSheaf.alternatingModuleInclusion_forget`: forgetting the module
  structures, the `R(V)`-linear inclusion is the canonical inclusion
  `Stacks.Cech.alternatingCechInclusion` of Tag 01FH, and not merely some quasi-isomorphism.
* `Stacks.Cohomology.CechSheaf.quasiIsoAt_alternatingModuleInclusion` and
  `Stacks.Cohomology.CechSheaf.quasiIsoAt_alternatingInclusionToCechComplex`: **Tag 01FM,
  `R(V)`-linearly.** Both inclusions are quasi-isomorphisms of complexes of `R(V)`-modules.

## Implementation notes

**Why no homotopy is ported.** Tag 01FM is proved by signed sorting of the index tuples, which is
additive but carries no linearity, and the chain homotopy witnessing it is private to
`StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingHomotopyEquivalence`. None of it is
needed: `forget₂ (ModuleCat R(V)) AddCommGrpCat` is exact, hence preserves homology, and it
reflects isomorphisms, so `HomologicalComplex.quasiIsoAt_map_iff_of_preservesHomology` turns the
abelian-group-level statement into the `R(V)`-linear one. The only thing to supply is that the
forgetful image of `Stacks.Cohomology.CechSheaf.alternatingModuleInclusion` *is* the inclusion of
Tag 01FH, which is `alternatingModuleInclusion_forget`, true by `rfl` degreewise because the two
`_forget` identifications are `Iso.refl`-valued.

**The bridge is elementwise.** `Stacks.Cohomology.CechSheaf.toCochain` already identifies the
slice model with the explicit model in abelian groups, by taking the family of components of a
cochain; all that is added here is that this is `R(V)`-linear, which reduces through
`Stacks.Cohomology.CechSheaf.mcomp` to the linearity of one Čech projection and one restriction
of sections. No limit cone has to be compared, since
`Stacks.Cohomology.CechSheaf.sectionsModuleOfLE` takes the module structure on sections from the
slice site, the same one the slice model carries.

**The index type is in the universe of the module values**, as in
`StacksFrontier.Topology.Sheaves.Cohomology.CechOfSheavesOfModules.SliceSiteComparison`: the explicit
cochain group is a product over the tuples of indices, so the degree-`p` terms of the two models
can be compared only when the maximum of the two universes is the universe of the module values.
The explicit universes in `cechComplex.{uX, uR, uM, uM}` are needed for the same reason they are
there: with the arguments postponed, instance search for `UnivLE` picks the wrong universe.

**No `@[stacks]` attribute.** Tags 01FH, 01FJ and 01FM already carry their abelian-group-level
statements; what is added here is the module structure, which is a refinement rather than a
different clause of a tag.

## References

* [Stacks Project, Tag 01FH](https://stacks.math.columbia.edu/tag/01FH)
* [Stacks Project, Tag 01FJ](https://stacks.math.columbia.edu/tag/01FJ)
* [Stacks Project, Tag 01FM](https://stacks.math.columbia.edu/tag/01FM)
* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex
open Stacks.Cohomology.Basis (res)

universe uX uR uM

attribute [local instance] ModuleCat.hasLimitsOfSize
attribute [local instance] AddCommGrpCat.hasLimitsOfSize
attribute [local implicit_reducible] CechCochains.Cochain
attribute [local implicit_reducible] Stacks.Cohomology.CechSheaf.cechComplex

namespace Stacks.Cohomology.CechSheaf

noncomputable section

variable {X : Type uX} [TopologicalSpace X]
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{uR}}
  {ι : Type uM}
  (V : Opens X) (U : ι → Opens X) (hU : V = ⨆ i, U i) (I : SheafOfModules.{uM} R)

/-! ### Taking components is linear -/

/-- Taking the component of a cochain of the module-valued Čech complex at a tuple is
`R(V)`-linear. -/
theorem mcomp_smul {n : ℕ} (a : SectionRing R V)
    (s : ToType (((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).X n))
    (x : Fin (n + 1) → ι) :
    letI := sectionsModuleOfLE V I (inter_le_covered V U hU x)
    mcomp V U hU I (a • s) x = a • mcomp V U hU I s x := by
  let := sectionsModuleOfLE V I (inter_le_covered V U hU x)
  let := sectionsModuleOfLE V I (leOfHom (inter (coverObject U hU) x).hom)
  have h1 : rawcomp V U hU I (a • s) x = a • rawcomp V U hU I s x :=
    map_smul (π (coverObject U hU) (sectionsPresheaf V I) n x).hom a s
  have h2 : mcomp V U hU I (a • s) x =
      res (abSections I) (inter_coverObject_left V U hU x).ge (a • rawcomp V U hU I s x) := by
    rw [← h1]
    rfl
  rw [h2]
  exact res_smul V I (inter_le_covered V U hU x)
    (leOfHom (inter (coverObject U hU) x).hom) (inter_coverObject_left V U hU x).ge a _

/-- Taking the family of components of a cochain of the module-valued Čech complex is
`R(V)`-linear. -/
theorem toCochainFun_smul {n : ℕ} (a : SectionRing R V)
    (s : ToType (((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).X n)) :
    letI := cochainModule V U hU I n
    toCochainFun V U hU I (a • s) = a • toCochainFun V U hU I s := by
  let := cochainModule V U hU I n
  funext x
  let := sectionsModuleOfLE V I (cechInter_le_covered V U hU x)
  let := sectionsModuleOfLE V I (inter_le_covered V U hU x)
  rw [cochain_smul_apply V U hU I n a _ x, toCochainFun_apply, toCochainFun_apply,
    mcomp_smul V U hU I a s x]
  exact res_smul V I (cechInter_le_covered V U hU x) (inter_le_covered V U hU x)
    (Stacks.Cech.cechComplexInter_eq (X := TopCat.of X) U x).ge a _

/-- **Taking components, degreewise and `R(V)`-linearly.** The morphism of `R(V)`-modules sending
a cochain of the slice model to the family of its components over the intersections. -/
def toCochainMod (n : ℕ) :
    (cechComplex.{uX, uR, uM, uM} V U hU I).X n ⟶ cechCochainModuleObj V U hU I n :=
  letI := cochainModule V U hU I n
  ModuleCat.ofHom
    { toFun := toCochainFun V U hU I
      map_add' := fun s t => funext fun x =>
        (congrArg (res (abSections I) _) (mcomp_add V U hU I s t x)).trans (map_add _ _ _)
      map_smul' := toCochainFun_smul V U hU I }

/-- The underlying function of `toCochainMod` is `toCochainFun`. -/
theorem toCochainMod_apply (n : ℕ)
    (s : ToType (((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).X n)) :
    ConcreteCategory.hom (toCochainMod V U hU I n) s = toCochainFun V U hU I s := rfl

/-- Taking components is an isomorphism of `R(V)`-modules in every degree. -/
instance isIso_toCochainMod (n : ℕ) : IsIso (toCochainMod V U hU I n) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    ⟨toCochainFun_injective V U hU I, toCochainFun_surjective V U hU I⟩

/-- **Taking components is a morphism of complexes of `R(V)`-modules.** -/
theorem toCochainMod_comm (n : ℕ) :
    toCochainMod V U hU I n ≫ cechModuleDiff V U hU I n =
      (cechComplex.{uX, uR, uM, uM} V U hU I).d n (n + 1) ≫ toCochainMod V U hU I (n + 1) :=
  ModuleCat.hom_ext <| LinearMap.ext fun s => funext fun y => (toCochainFun_md V U hU I s y).symm

/-- **The slice model is the explicit Čech complex of `R(V)`-modules.** The module-valued Čech
complex of the cover is isomorphic, as a cochain complex of `R(V)`-modules, to the explicit Čech
complex on families of sections; in each degree the isomorphism takes a cochain to the family of
its components over the intersections. -/
def cechComplexModuleIso :
    cechComplex.{uX, uR, uM, uM} V U hU I ≅ cechModuleComplex V U hU I :=
  HomologicalComplex.Hom.isoOfComponents (fun n => asIso (toCochainMod V U hU I n))
    (by
      rintro n _ (rfl : n + 1 = _)
      rw [cechModuleComplex_d]
      exact toCochainMod_comm V U hU I n)

/-- In each degree the bridge is `toCochainMod`. -/
@[simp]
theorem cechComplexModuleIso_hom_f (n : ℕ) :
    (cechComplexModuleIso V U hU I).hom.f n = toCochainMod V U hU I n := rfl

/-- **Tag 01FH for the slice model, `R(V)`-linearly.** The inclusion of the alternating Čech
complex of `R(V)`-modules into the module-valued Čech complex of the cover. -/
def alternatingInclusionToCechComplex :
    alternatingModuleComplex V U hU I ⟶ cechComplex.{uX, uR, uM, uM} V U hU I :=
  alternatingModuleInclusion V U hU I ≫ (cechComplexModuleIso V U hU I).inv

/-! ### Forgetting the module structures -/

/-- Forgetting the module structures in the usual explicit Čech complex of `R(V)`-modules recovers
the Čech complex of abelian groups. -/
def cechModuleComplexForget :
    ((forget₂ (ModuleCat.{uM} (SectionRing R V)) AddCommGrpCat.{uM}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (cechModuleComplex V U hU I) ≅
      Stacks.Cech.cechComplex (X := TopCat.of X) U (abSections I) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    rintro p q (rfl : p + 1 = q)
    simp only [Iso.refl_hom, Functor.mapHomologicalComplex_obj_d, cechModuleComplex_d,
      Stacks.Cech.cechComplex_d]
    rfl)

/-- Forgetting the module structures in the alternating Čech complex of `R(V)`-modules recovers
the alternating Čech complex of abelian groups of Tag 01FH. -/
def alternatingModuleComplexForget :
    ((forget₂ (ModuleCat.{uM} (SectionRing R V)) AddCommGrpCat.{uM}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (alternatingModuleComplex V U hU I) ≅
      Stacks.Cech.alternatingCechComplex (X := TopCat.of X) U (abSections I) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    rintro p q (rfl : p + 1 = q)
    simp only [Iso.refl_hom, Functor.mapHomologicalComplex_obj_d, alternatingModuleComplex_d,
      Stacks.Cech.alternatingCechComplex_d]
    rfl)

/-- **Forgetting the module structures, the `R(V)`-linear inclusion of the alternating Čech
complex is the canonical inclusion of Tag 01FH**, and not merely some quasi-isomorphism. -/
theorem alternatingModuleInclusion_forget :
    (alternatingModuleComplexForget V U hU I).inv ≫
        ((forget₂ (ModuleCat.{uM} (SectionRing R V)) AddCommGrpCat.{uM}).mapHomologicalComplex
          (ComplexShape.up ℕ)).map (alternatingModuleInclusion V U hU I) ≫
        (cechModuleComplexForget V U hU I).hom =
      Stacks.Cech.alternatingCechInclusion (X := TopCat.of X) U (abSections I) := by
  ext p s
  rfl

/-! ### Čech cohomology as a module -/

section LinearOrdered

variable [LinearOrder ι]

/-- Forgetting the module structures, the `R(V)`-linear inclusion of the alternating Čech complex
induces an isomorphism on homology: this is Tag 01FM for the explicit model. -/
theorem isIso_homologyMap_map_alternatingModuleInclusion (p : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (((forget₂ (ModuleCat.{uM} (SectionRing R V)) AddCommGrpCat.{uM}).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (alternatingModuleInclusion V U hU I)) p) := by
  have hAb : IsIso (HomologicalComplex.homologyMap
      (Stacks.Cech.alternatingCechInclusion (X := TopCat.of X) U (abSections I)) p) := by
    obtain ⟨e, he⟩ := Stacks.Cech.alternatingCechInclusion_homotopyEquivalence
      (X := TopCat.of X) U (abSections I)
    rw [← he]
    exact (e.toHomologyIso p).isIso_hom
  rwa [← alternatingModuleInclusion_forget V U hU I, HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp, isIso_comp_left_iff, isIso_comp_right_iff] at hAb

/-- Forgetting the module structures, the `R(V)`-linear inclusion of the alternating Čech complex
is a quasi-isomorphism in every degree `p`. -/
instance quasiIsoAt_map_alternatingModuleInclusion (p : ℕ) :
    QuasiIsoAt
      (((forget₂ (ModuleCat.{uM} (SectionRing R V)) AddCommGrpCat.{uM}).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (alternatingModuleInclusion V U hU I)) p :=
  (quasiIsoAt_iff_isIso_homologyMap _ p).2
    (isIso_homologyMap_map_alternatingModuleInclusion V U hU I p)

/-- **Tag 01FM, `R(V)`-linearly.** For a linearly ordered index type the inclusion of the
alternating Čech complex of `R(V)`-modules into the usual explicit one is a quasi-isomorphism of
complexes of `R(V)`-modules: the forgetful functor to abelian groups is exact and reflects
isomorphisms, so the abelian-group-level statement of Tag 01FM transfers. -/
instance quasiIsoAt_alternatingModuleInclusion (p : ℕ) :
    QuasiIsoAt (alternatingModuleInclusion V U hU I) p :=
  (HomologicalComplex.quasiIsoAt_map_iff_of_preservesHomology
    (alternatingModuleInclusion V U hU I)
    (forget₂ (ModuleCat.{uM} (SectionRing R V)) AddCommGrpCat.{uM}) p).1
    (quasiIsoAt_map_alternatingModuleInclusion V U hU I p)

/-- **Tag 01FM for the slice model, `R(V)`-linearly.** -/
instance quasiIsoAt_alternatingInclusionToCechComplex (p : ℕ) :
    QuasiIsoAt (alternatingInclusionToCechComplex V U hU I) p := by
  rw [quasiIsoAt_iff_isIso_homologyMap, alternatingInclusionToCechComplex,
    HomologicalComplex.homologyMap_comp]
  infer_instance

/-- **The alternating Čech complex computes the module-valued Čech cohomology of the cover, as a
module.** For a linearly ordered index type the homology of the alternating Čech complex of
`R(V)`-modules is the module-valued Čech cohomology of the slice model, in every degree, as
`R(V)`-modules — no forgetful functor appears. This is what lets an alternating Čech computation
be fed into the comparison of [Stacks, Tag 01XD] without losing the module structure. -/
def alternatingCechHomologyModuleIso (p : ℕ) :
    (alternatingModuleComplex V U hU I).homology p ≅
      (cechComplex.{uX, uR, uM, uM} V U hU I).homology p :=
  asIso (HomologicalComplex.homologyMap (alternatingInclusionToCechComplex V U hU I) p)

/-- **The ordered Čech complex computes the module-valued Čech cohomology of the cover, as a
module.** The same statement for the ordered Čech complex of Tag 01FI, through the `R(V)`-linear
comparison of Tag 01FJ. -/
def orderedCechHomologyModuleIso (p : ℕ) :
    (orderedModuleComplex V U hU I).homology p ≅
      (cechComplex.{uX, uR, uM, uM} V U hU I).homology p :=
  HomologicalComplex.homologyMapIso (orderedIsoAlternatingModuleComplex V U hU I) p ≪≫
    alternatingCechHomologyModuleIso V U hU I p

end LinearOrdered

end

end Stacks.Cohomology.CechSheaf

end
