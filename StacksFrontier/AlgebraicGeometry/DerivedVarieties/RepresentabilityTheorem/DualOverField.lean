module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomLinearSource
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectBidualNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualAtTheSpaceHypothesis
public import Mathlib.Algebra.Homology.Linear

/-!
# The dual of a scheme over a field is linear over the field

Let `X` be a scheme over a field `k`, so that `𝒪_X`-modules are `k`-linear through the structure
morphism (`AlgebraicGeometry.modulesLinear`). The dual `E ↦ E^∨ = R𝓗om(E, 𝒪_X)` of
[Stacks, Tag 08DQ] on `D(𝒪_X)` is `k`-linear: `(r • f)^∨ = r • f^∨`. The proof of
[Stacks, Tag 0H4A] needs this to see that `E ↦ G(E^∨)` is again a `k`-linear functor.

## Main definitions

* `Stacks.AlgebraicGeometry.DerivedVarieties.DualOverField.baseSections`: the image of a scalar
  of `k` in the sections of the structure sheaf, as a compatible family.
* `Stacks.AlgebraicGeometry.DerivedVarieties.DualOverField.dual`: the dual on `D(𝒪_X)` at the
  `AlgebraicGeometry.Scheme.Modules` spelling.

## Main results

* `Stacks.AlgebraicGeometry.DerivedVarieties.DualOverField.smul_id_eq_globalSectionToEnd`: a
  scalar acts on `𝒪_X`-modules as multiplication by its image in the structure sheaf.
* `Stacks.AlgebraicGeometry.DerivedVarieties.DualOverField.dual_map_smul`: the dual is
  `k`-linear.

## Implementation notes

The dual is formed at the standard model of `D(𝒪_X)`, where the internal Hom of
[Stacks, Tag 08DH] lives; `k`-linearity is the source-linearity of the internal Hom,
`AlgebraicGeometry.RingedSite.derivedSheafHom_map_globalSectionToEnd_source`, read at the
scalars of `k`: a scalar of `k` acts on every object of `D(𝒪_X)` as its image in the global
sections of the structure sheaf does (`smul_id_eq_smul_id_of_essSurj`).

## References

* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 0H4A](https://stacks.math.columbia.edu/tag/0H4A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.DerivedVarieties.DualOverField

variable {k : Type u} [Field k] (X : Over (Spec (CommRingCat.of k)))

/-- The image of a scalar of `k` in the sections of the structure sheaf, as a compatible family. -/
def baseSections (r : k) :
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (Stacks.SheafOfModules.ringedSite X.left.sheaf).O).obj ⋙ forget RingCat).sections :=
  ⟨fun U => baseRingToSections k X U r, fun {U V} i => by
    exact (congrArg (fun g => RingCat.Hom.hom g
      (((forget₂ CommRingCat RingCat).map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        X.hom.appTop)).hom r)) (X.left.ringCatSheaf.obj.map_comp U.unop.leTop.op i)).symm⟩

/-- The category of `𝒪_X`-modules, in the ringed-site spelling the derived internal Hom is stated
at. It is `X.left.Modules`. -/
abbrev SiteModules : Type (u + 1) :=
  SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (Stacks.SheafOfModules.ringedSite X.left.sheaf).O)

/-- The `k`-linear structure on `𝒪_X`-modules, read at the ringed-site spelling. -/
abbrev siteModulesLinear : Linear k (SiteModules X) := modulesLinear k X

/-- The linear structure of `𝒪_X`-modules over the centre of their category, read at the
ringed-site spelling: it is `AlgebraicGeometry.RingedSite.linearCatCenterRingSheaf`. -/
abbrev siteCenterLinear : Linear (CatCenter (SiteModules X)) (SiteModules X) :=
  RingedSite.linearCatCenterRingSheaf (Stacks.SheafOfModules.ringedSite X.left.sheaf)

attribute [local instance] siteModulesLinear

/-- **A scalar of `k` acts on `𝒪_X`-modules as multiplication by its image in the sections of the
structure sheaf.** -/
theorem smul_id_eq_globalSectionToEnd (r : k) (M : SiteModules X) :
    r • 𝟙 M = (Stacks.SheafOfModules.globalSectionToEnd _ (baseSections X r)).asHom.app M := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- A contravariant functor which carries `r • 𝟙` to `r • 𝟙` at every object carries `r • f` to
`r • F f` for every morphism `f`. -/
theorem map_op_smul_of_map_op_smul_id {R : Type*} [Semiring R] {C D : Type*} [Category C]
    [Category D] [Preadditive C] [Preadditive D] [Linear R C] [Linear R D] (F : Cᵒᵖ ⥤ D) (r : R)
    (h : ∀ M : C, F.map (r • 𝟙 M).op = r • 𝟙 (F.obj (op M))) {M N : C} (f : M ⟶ N) :
    F.map (r • f).op = r • F.map f.op := by
  have hf : r • f = (r • 𝟙 M) ≫ f := by rw [Linear.smul_comp, Category.id_comp]
  rw [hf, op_comp, Functor.map_comp, h, Linear.comp_smul, Category.comp_id]

/-- A scalar acts on an object `N` of the target of an essentially surjective linear functor `L`
as it acts on a preimage of `N`, transported along `L.objObjPreimageIso N`. -/
private theorem smul_id_eq_objObjPreimageIso_comp {R : Type*} [Semiring R] {C D : Type*}
    [Category C] [Category D] [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
    (L : C ⥤ D) [L.Linear R] [L.EssSurj] (r : R) (N : D) :
    r • 𝟙 N = (L.objObjPreimageIso N).inv ≫ L.map (r • 𝟙 (L.objPreimage N)) ≫
      (L.objObjPreimageIso N).hom := by
  rw [Functor.map_smul, CategoryTheory.Functor.map_id, Linear.smul_comp, Linear.comp_smul,
    Category.id_comp, Iso.inv_hom_id]

/-- **Two linear structures agreeing on identities upstairs agree downstairs.** If `L : C ⥤ D` is
essentially surjective and linear for two scalar actions, and the scalars `r` and `r'` act in the
same way on every object of `C`, they act in the same way on every object of `D`. -/
theorem smul_id_eq_smul_id_of_essSurj {R R' : Type*} [Semiring R] [Semiring R'] {C D : Type*}
    [Category C] [Category D] [Preadditive C] [Preadditive D] [Linear R C] [Linear R' C]
    [Linear R D] [Linear R' D] (L : C ⥤ D) [L.Linear R] [L.Linear R'] [L.EssSurj] (r : R)
    (r' : R') (h : ∀ M : C, r • 𝟙 M = r' • 𝟙 M) (N : D) : r • 𝟙 N = r' • 𝟙 N := by
  rw [smul_id_eq_objObjPreimageIso_comp L r, smul_id_eq_objObjPreimageIso_comp L r', h]

section Derived

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] siteCenterLinear in
/-- A scalar of `k` acts on every object of `D(𝒪_X)` as its image in the sections of the
structure sheaf, read as a central endomorphism. -/
theorem smul_id_eq_globalSectionToEnd_smul_id (r : k) (E : DerivedCategory (SiteModules X)) :
    r • 𝟙 E = Stacks.SheafOfModules.globalSectionToEnd _ (baseSections X r) • 𝟙 E := by
  refine smul_id_eq_smul_id_of_essSurj (DerivedCategory.Q (C := SiteModules X)) r
    (Stacks.SheafOfModules.globalSectionToEnd _ (baseSections X r)) (fun A => ?_) E
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  rw [HomologicalComplex.smul_f_apply, HomologicalComplex.smul_f_apply, HomologicalComplex.id_f,
    smul_id_eq_globalSectionToEnd, Linear.smulOfRingMorphism_smul_eq, Category.comp_id]
  rfl

attribute [local instance] siteCenterLinear in
/-- The dual carries multiplication by a scalar of `k` to multiplication by that scalar, at the
ringed-site spelling. -/
theorem siteDual_map_smul_id (r : k) (E : DerivedCategory (SiteModules X)) :
    ((RingedSite.derivedSheafHomBifunctor (Stacks.SheafOfModules.ringedSite X.left.sheaf)).flip.obj
        (RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite X.left.sheaf))).map
        (r • 𝟙 E).op =
      r • 𝟙 (((RingedSite.derivedSheafHomBifunctor
        (Stacks.SheafOfModules.ringedSite X.left.sheaf)).flip.obj
          (RingedSite.derivedStructureSheaf
            (Stacks.SheafOfModules.ringedSite X.left.sheaf))).obj (op E)) := by
  have h := RingedSite.derivedSheafHom_map_globalSectionToEnd_source
    (Stacks.SheafOfModules.ringedSite X.left.sheaf) (baseSections X r) E
    (RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite X.left.sheaf))
  have h1 := smul_id_eq_globalSectionToEnd_smul_id X r E
  have h2 := smul_id_eq_globalSectionToEnd_smul_id X r
    (((RingedSite.derivedSheafHomBifunctor (Stacks.SheafOfModules.ringedSite X.left.sheaf)).obj
      (op E)).obj
        (RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite X.left.sheaf)))
  exact (congrArg (fun g => ((RingedSite.derivedSheafHomBifunctor
    (Stacks.SheafOfModules.ringedSite X.left.sheaf)).map g.op).app _) h1).trans (h.trans h2.symm)

attribute [local instance] modulesLinear

/-- **The dual `E ↦ E^∨ = RSheafHom(E, 𝒪_X)` of `D(𝒪_X)`**, for a scheme `X`, at the spelling
`AlgebraicGeometry.Scheme.Modules` of its category of modules. It is
`Stacks.SheafOfModules.derivedDualFunctor`. -/
abbrev dual (Y : Scheme.{u}) : (DerivedCategory Y.Modules)ᵒᵖ ⥤ DerivedCategory Y.Modules :=
  Stacks.SheafOfModules.derivedDualFunctor Y.sheaf

/-- **The dual is `k`-linear**, for a scheme `X` over a field `k`: the dual of `r • f` is
`r • f^∨`. -/
theorem dual_map_smul {E E' : DerivedCategory X.left.Modules} (f : E ⟶ E') (r : k) :
    (dual X.left).map (r • f).op = r • (dual X.left).map f.op :=
  map_op_smul_of_map_op_smul_id (dual X.left) r (fun E => siteDual_map_smul_id X r E) f

end Derived

end Stacks.AlgebraicGeometry.DerivedVarieties.DualOverField

end
