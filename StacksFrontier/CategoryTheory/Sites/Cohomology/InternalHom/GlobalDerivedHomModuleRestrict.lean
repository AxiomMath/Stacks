module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomModuleForget
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexBaseRing

/-!
# The canonical map into the global derived hom, over the source's base ring

Let `(C, O)` be a ringed site, let `R` be a ring with a sheaf of commutative `R`-algebra
structures on `O` — which is what an `AlgebraicGeometry.RingedSite.ScalarSections` instance is,
by `AlgebraicGeometry.RingedSite.ScalarSections.algebraSheaf` — and let `F`, `G` be complexes of
`O`-modules. Stacks 0CS6 asserts a canonical map `Hom^•_{Comp^dg(O)}(F, G) ⟶ RHom_O(F, G)` in
`D(R)`.

`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHomModules` is that map over the
universal base ring `Γ(C, O)`, and every `R` maps to `Γ(C, O)` by
`AlgebraicGeometry.RingedSite.ScalarSections.toGlobalSections`. This file restricts the scalars
along that map and so builds the canonical map in `D(R)` itself, for the source's `R`, and proves
that forgetting its `R`-action returns
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom`.

## Main definitions

* `CochainComplex.dgCategoryLinearRestrictIso`: the module-valued Hom complex of
  `CochainComplex.dgCategoryLinear` over `R` is the restriction of scalars of the one over `S`,
  for a ring map `R → S` through which the `R`-action factors.
* `AlgebraicGeometry.RingedSite.restrictForgetDerivedIso`: forgetting the `R`-action after
  restricting the scalars along `R → Γ(C, O)` is forgetting the `Γ(C, O)`-action, on derived
  categories.
* `AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHomModulesOver`: **the canonical map
  `Hom^•_{Comp^dg(O)}(F, G) ⟶ RHom_O(F, G)` of Stacks 0CS6 in the source's `D(R)`.**
* `AlgebraicGeometry.RingedSite.homComplexModulesOverDerivedForgetIso` and
  `AlgebraicGeometry.RingedSite.globalDerivedHomForgetAppOver`: its source and its target with
  the `R`-action forgotten.

## Main results

* `AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHomModulesOver_forget`: **the canonical
  map over `R` forgets to the canonical map in `D(ℤ)`**, so the two are one map read over two
  base rings.
* `AlgebraicGeometry.RingedSite.restrictForgetDerivedIso_hom_app_Q`: the comparison of the two
  readings of the forgetful functor, evaluated on the class of a complex.

## Implementation notes

*What the restriction of scalars costs.* Nothing beyond
`AlgebraicGeometry.RingedSite.ScalarSections.smul_eq_globalSections_smul` read on cochains. The
homogeneous morphisms of `CochainComplex.dgCategoryLinear B R` are Mathlib's
`CochainComplex.HomComplex.Cochain`, whose module structure is pointwise, and a base-ring scalar
acts on a morphism of sheaves of `O`-modules as its image in `Γ(C, O)` does; so the two module
structures on one and the same abelian group of cochains agree, which is
`CochainComplex.HomComplex.Cochain.smul_eq_smul_of_ringHom`, and
`CochainComplex.dgCategoryLinearRestrictIso` is the degreewise identity. Its differential square
is `CochainComplex.dgCategoryLinear_homComplexModules_d_apply` read at the two base rings: both
differentials are `CochainComplex.HomComplex.δ`.

*Why the comparison of the two forgetful functors is a lifted natural isomorphism.* Restriction
of scalars followed by forgetting the `R`-action **is** forgetting the `Γ(C, O)`-action, as
functors of module categories; but the functors they induce on derived categories are
constructed by localization, so the composite of the two induced functors and the induced functor
of the composite agree only up to the comparison that the universal property produces. That
comparison is `AlgebraicGeometry.RingedSite.restrictForgetDerivedIso`, obtained from
`CategoryTheory.Localization.liftNatIso` at the two liftings
`AlgebraicGeometry.RingedSite.liftingRestrictForgetComp` and
`AlgebraicGeometry.RingedSite.liftingRestrictForgetGS`.

The two liftings are deliberately stated at the *same* spelling of the lifted functor, namely
`restrictScalars.mapHomologicalComplex ⋙ (forget₂.mapHomologicalComplex ⋙ Q)` with the
whiskerings right-associated, and the one junction — that this is the complex-level forgetful
functor over `Γ(C, O)` composed with the localization — is crossed once, in term mode, inside
`AlgebraicGeometry.RingedSite.liftingRestrictForgetGS`. Writing the two liftings at two
definitionally equal spellings instead makes
`AlgebraicGeometry.RingedSite.restrictForgetDerivedIso_hom_app_Q` unprovable by rewriting: the
two spellings differ in the implicit arguments of the isomorphisms involved, so `simp` and `rw`
report that their patterns do not occur.

*Why the forgetful functor of `R`-modules needs an instance.*
`CategoryTheory.Functor.mapDerivedCategory` asks for
`CategoryTheory.Limits.PreservesFiniteColimits`, and Mathlib's instances for
`forget₂ (ModuleCat R) AddCommGrpCat` preserving *all* colimits are stated at a module universe
of the form `max w w'`, which does not unify with the section universe of a site when the base
ring's universe is unrelated to it. Finite colimits need no such hypothesis, and
`ModuleCat.preservesFiniteColimits_forget₂AddCommGrpCat` supplies them shape by shape.

*The universe parameters* are the diagonal ones of the site for the sheaves, and the base ring's
own universe `o` is independent of them.

## References

* [Stacks Project, Tag 0CS6](https://stacks.math.columbia.edu/tag/0CS6)
* [Stacks Project, Tag 0B6E](https://stacks.math.columbia.edu/tag/0B6E)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.Cohomology.SiteModules
open scoped IsMulCommutative

universe v

namespace ModuleCat

/-- **The forgetful functor from modules to abelian groups preserves finite colimits.** Mathlib
states its preservation of all colimits at a module universe of the form `max w w'`; for finite
shapes no size hypothesis is needed, and the instance is assembled shape by shape. -/
instance preservesFiniteColimits_forget₂AddCommGrpCat {R : Type*} [Ring R] :
    Limits.PreservesFiniteColimits (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}) :=
  ⟨fun _ _ _ => inferInstance⟩

end ModuleCat

namespace CochainComplex

open CochainComplex.HomComplex

universe u

variable {B : Type u} [Category.{v} B] [Preadditive B]
  {R : Type*} [CommRing R] [Linear R B] {S : Type*} [CommRing S] [Linear S B]
  (φ : R →+* S) (hφ : ∀ {P Q : B} (r : R) (f : P ⟶ Q), r • f = φ r • f)

include hφ in
/-- **A base-ring scalar acts on a cochain as its image acts.** The module structure on
`CochainComplex.HomComplex.Cochain` is pointwise, so the hypothesis on morphisms of `B` gives the
statement on cochains. -/
theorem HomComplex.Cochain.smul_eq_smul_of_ringHom {F G : CochainComplex B ℤ} {n : ℤ} (r : R)
    (z : Cochain F G n) : r • z = φ r • z :=
  Cochain.ext _ _ fun p q hpq => by
    rw [Cochain.smul_v, Cochain.smul_v]
    exact hφ r (z.v p q hpq)

/-- Degreewise, the `R`-module of degree-`n` homogeneous morphisms is the restriction of scalars
of the `S`-module of the same morphisms: the two actions agree by
`CochainComplex.HomComplex.Cochain.smul_eq_smul_of_ringHom`. -/
def dgCategoryLinearRestrictIsoX (F G : CochainComplex B ℤ) (n : ℤ) :
    (ModuleCat.restrictScalars φ).obj
        (((dgCategoryLinear B S).homComplexModules F G).X n) ≅
      ((dgCategoryLinear B R).homComplexModules F G).X n where
  hom := ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars φ).obj
      (((dgCategoryLinear B S).homComplexModules F G).X n))
    (Y := ((dgCategoryLinear B R).homComplexModules F G).X n)
    { toFun := fun z => z
      map_add' := fun _ _ => rfl
      map_smul' := fun r z => (HomComplex.Cochain.smul_eq_smul_of_ringHom φ hφ r z).symm }
  inv := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars φ).obj
      (((dgCategoryLinear B S).homComplexModules F G).X n))
    (X := ((dgCategoryLinear B R).homComplexModules F G).X n)
    { toFun := fun z => z
      map_add' := fun _ _ => rfl
      map_smul' := fun r z => HomComplex.Cochain.smul_eq_smul_of_ringHom φ hφ r z }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- **The module-valued Hom complex over `R` is the restriction of scalars of the one over
`S`.** For a ring map `φ : R → S` through which the `R`-action on `B` factors, the two
module-valued Hom complexes of `CochainComplex.dgCategoryLinear` are one complex of abelian
groups with two module structures that agree; the comparison is the degreewise identity, and both
differentials are `CochainComplex.HomComplex.δ`. -/
def dgCategoryLinearRestrictIso (F G : CochainComplex B ℤ) :
    ((ModuleCat.restrictScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((dgCategoryLinear B S).homComplexModules F G) ≅
      (dgCategoryLinear B R).homComplexModules F G :=
  HomologicalComplex.Hom.isoOfComponents (fun n => dgCategoryLinearRestrictIsoX φ hφ F G n) (by
    intro n m hnm
    obtain rfl : m = n + 1 := hnm.symm
    refine ModuleCat.hom_ext (LinearMap.ext fun f => ?_)
    have h₁ := dgCategoryLinear_homComplexModules_d_apply (B := B) (R := R) F G n (n + 1) rfl f
    have h₂ := dgCategoryLinear_homComplexModules_d_apply (B := B) (R := S) F G n (n + 1) rfl f
    exact h₁.trans h₂.symm)

end CochainComplex

namespace AlgebraicGeometry.RingedSite

universe u o

attribute [local instance] HasDerivedCategory.standard

variable (X : AlgebraicGeometry.RingedSite.{u, u, u})
  (R : Type o) [CommRing R] [Linear R (TensorModO.{u, u, u, u, u} X)]
  [ScalarSections.{u, u, u, u, u, o} X R]

/-! ### The two readings of the forgetful functor -/

/-- **Restriction of scalars along the universal map `R → Γ(C, O)`** of
`AlgebraicGeometry.RingedSite.ScalarSections.toGlobalSections`: this is how a statement in
`D(Γ(C, O))` gives the source's statement in `D(R)`. -/
abbrev scalarRestriction :
    ModuleCat.{u} ↥(GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      ModuleCat.{u} R :=
  ModuleCat.restrictScalars (ScalarSections.toGlobalSections.{u, u, u, u, u, o} X R)

/-- Forgetting the base-ring action. -/
abbrev forgetBaseRing : ModuleCat.{u} R ⥤ AddCommGrpCat.{u} :=
  forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}

/-- The lifting of the composite of the two induced functors on derived categories through the
localization. Its target spelling, with the whiskerings right-associated, is the one
`AlgebraicGeometry.RingedSite.liftingRestrictForgetGS` is stated at as well; see the
implementation notes. -/
@[instance_reducible]
def liftingRestrictForgetComp :
    Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso
        (ModuleCat.{u} ↥(GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
        (ComplexShape.up ℤ))
      ((scalarRestriction X R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        ((forgetBaseRing R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q))
      ((scalarRestriction X R).mapDerivedCategory ⋙ (forgetBaseRing R).mapDerivedCategory) :=
  ⟨(Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (scalarRestriction X R).mapDerivedCategoryFactors
      (forgetBaseRing R).mapDerivedCategory ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft ((scalarRestriction X R).mapHomologicalComplex (ComplexShape.up ℤ))
      (forgetBaseRing R).mapDerivedCategoryFactors⟩

/-- The lifting of `AlgebraicGeometry.RingedSite.underlyingDerivedGroup`, read at the composite's
spelling of the lifted functor. This is where the junction between the two readings of the
complex-level forgetful functor is crossed, in term mode. -/
@[instance_reducible]
def liftingRestrictForgetGS :
    Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso
        (ModuleCat.{u} ↥(GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
        (ComplexShape.up ℤ))
      ((scalarRestriction X R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        ((forgetBaseRing R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q))
      (underlyingDerivedGroup X) :=
  ⟨(forget₂ (ModuleCat.{u} ↥(GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    AddCommGrpCat.{u}).mapDerivedCategoryFactors⟩

/-- **Forgetting the `R`-action after restricting the scalars along `R → Γ(C, O)` is forgetting
the `Γ(C, O)`-action**, on derived categories. The two functors of module categories are equal;
the functors they induce on derived categories are produced by the universal property of the
localization, so they agree up to the comparison this isomorphism is. -/
def restrictForgetDerivedIso :
    (scalarRestriction X R).mapDerivedCategory ⋙ (forgetBaseRing R).mapDerivedCategory ≅
      underlyingDerivedGroup X :=
  letI := liftingRestrictForgetComp X R
  letI := liftingRestrictForgetGS X R
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso
      (ModuleCat.{u} ↥(GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
      (ComplexShape.up ℤ))
    ((scalarRestriction X R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      ((forgetBaseRing R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q))
    ((scalarRestriction X R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      ((forgetBaseRing R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)) _ _
    (Iso.refl _)

/-- **The comparison of the two readings of the forgetful functor, on the class of a complex.**
On an object in the image of the localization it is the two comparisons
`CategoryTheory.Functor.mapDerivedCategoryFactors` of the restriction of scalars and of the
forgetful functor of `R`-modules, against the one of the forgetful functor of
`Γ(C, O)`-modules. -/
theorem restrictForgetDerivedIso_hom_app_Q
    (Z : CochainComplex
      (ModuleCat.{u} ↥(GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ) :
    (restrictForgetDerivedIso X R).hom.app (DerivedCategory.Q.obj Z) =
      (forgetBaseRing R).mapDerivedCategory.map
          ((scalarRestriction X R).mapDerivedCategoryFactors.hom.app Z) ≫
        (forgetBaseRing R).mapDerivedCategoryFactors.hom.app
            (((scalarRestriction X R).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z) ≫
          ((forget₂
            (ModuleCat.{u} ↥(GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            AddCommGrpCat.{u}).mapDerivedCategoryFactors).inv.app Z := by
  simp [restrictForgetDerivedIso, liftingRestrictForgetComp, liftingRestrictForgetGS]

/-! ### The canonical map over the source's base ring -/

/-- **The module-valued Hom complex of `Comp^dg(O)` over `R` is the restriction of scalars of
the one over `Γ(C, O)`.** This is `CochainComplex.dgCategoryLinearRestrictIso` at
`AlgebraicGeometry.RingedSite.ScalarSections.toGlobalSections`, whose hypothesis is
`AlgebraicGeometry.RingedSite.ScalarSections.smul_eq_globalSections_smul`. -/
def homComplexModulesRestrictIso
    (F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((scalarRestriction X R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((compDGGlobalSections.{u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).homComplexModules F G) ≅
      (CompDG.{u, u, u, u, u, o} X R).homComplexModules F G :=
  CochainComplex.dgCategoryLinearRestrictIso
    (ScalarSections.toGlobalSections.{u, u, u, u, u, o} X R)
    (fun r f => ScalarSections.smul_eq_globalSections_smul r f) F G

/-- The same comparison in the derived category: the restriction of scalars is exact, so it
commutes with the localization. -/
def homComplexModulesRestrictDerivedIso
    (F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (scalarRestriction X R).mapDerivedCategory.obj
        (DerivedCategory.Q.obj
          ((compDGGlobalSections.{u, u, u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).homComplexModules F G)) ≅
      DerivedCategory.Q.obj ((CompDG.{u, u, u, u, u, o} X R).homComplexModules F G) :=
  (scalarRestriction X R).mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso (homComplexModulesRestrictIso X R F G)

/-- **Stacks 0CS6, the canonical map `Hom^•(F, G) ⟶ RHom_O(F, G)` over the source's base
ring.** The canonical map over the universal base ring `Γ(C, O)`,
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHomModules`, with its scalars restricted
along `AlgebraicGeometry.RingedSite.ScalarSections.toGlobalSections`; its source is the
`R`-module-valued Hom complex of `Comp^dg(O)` read over `R`, by
`AlgebraicGeometry.RingedSite.homComplexModulesRestrictDerivedIso`, and its target is the global
derived hom of Stacks 0B6E read over `R`.

This is a morphism of the source's `D(R)`. It forgets to
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom`, by
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHomModulesOver_forget`. -/
def homComplexToGlobalDerivedHomModulesOver
    (F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    DerivedCategory.Q.obj ((CompDG.{u, u, u, u, u, o} X R).homComplexModules F G) ⟶
      (scalarRestriction X R).mapDerivedCategory.obj
        (((globalDerivedHomModules X).obj (op (DerivedCategory.Q.obj F))).obj
          (DerivedCategory.Q.obj G)) :=
  (homComplexModulesRestrictDerivedIso X R F G).inv ≫
    (scalarRestriction X R).mapDerivedCategory.map (homComplexToGlobalDerivedHomModules F G)

/-- **The source of the canonical map over `R`, with its `R`-action forgotten, is the source of
the canonical map in `D(ℤ)`.** -/
def homComplexModulesOverDerivedForgetIso
    (F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (forgetBaseRing R).mapDerivedCategory.obj
        (DerivedCategory.Q.obj ((CompDG.{u, u, u, u, u, o} X R).homComplexModules F G)) ≅
      DerivedCategory.Q.obj (F.HomComplex G) :=
  (forgetBaseRing R).mapDerivedCategory.mapIso
      (homComplexModulesRestrictDerivedIso X R F G).symm ≪≫
    (restrictForgetDerivedIso X R).app _ ≪≫ homComplexModulesDerivedForgetIso F G

/-- **The target of the canonical map over `R`, with its `R`-action forgotten, is the
`D(ℤ)`-valued global derived hom.** -/
def globalDerivedHomForgetAppOver
    (A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (forgetBaseRing R).mapDerivedCategory.obj
        ((scalarRestriction X R).mapDerivedCategory.obj
          (((globalDerivedHomModules X).obj (op A)).obj B)) ≅
      ((globalDerivedHom X).obj (op A)).obj B :=
  (restrictForgetDerivedIso X R).app _ ≪≫ globalDerivedHomForgetApp X A B

/-- Forgetting the `R`-action of the restriction of scalars of a morphism is the composite of the
two induced functors applied to it. -/
theorem forgetBaseRing_map_scalarRestriction_map
    {A B : DerivedCategory
      (ModuleCat.{u} ↥(GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))}
    (h : A ⟶ B) :
    (forgetBaseRing R).mapDerivedCategory.map ((scalarRestriction X R).mapDerivedCategory.map h) =
      ((scalarRestriction X R).mapDerivedCategory ⋙
        (forgetBaseRing R).mapDerivedCategory).map h :=
  rfl

/-- **Stacks 0CS6: the canonical map over the source's base ring forgets to the canonical map in
`D(ℤ)`.** Forgetting the `R`-action of
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHomModulesOver`, and identifying its
source and its target with those of the `D(ℤ)`-valued map, gives
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom`. So the two are one map read over two
base rings.

The restriction of scalars cancels against itself on the source, and
`AlgebraicGeometry.RingedSite.restrictForgetDerivedIso` is moved across the map over `Γ(C, O)` by
its naturality; what is left is
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHomModules_forget`. -/
theorem homComplexToGlobalDerivedHomModulesOver_forget
    (F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (homComplexModulesOverDerivedForgetIso X R F G).inv ≫
        (forgetBaseRing R).mapDerivedCategory.map
            (homComplexToGlobalDerivedHomModulesOver X R F G) ≫
          (globalDerivedHomForgetAppOver X R (DerivedCategory.Q.obj F)
            (DerivedCategory.Q.obj G)).hom =
      homComplexToGlobalDerivedHom X F G := by
  rw [homComplexModulesOverDerivedForgetIso, globalDerivedHomForgetAppOver,
    homComplexToGlobalDerivedHomModulesOver, Iso.trans_inv, Iso.trans_inv, Iso.trans_hom,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.mapIso_inv, Iso.symm_inv,
    Iso.app_inv, Iso.app_hom]
  simp only [Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp, forgetBaseRing_map_scalarRestriction_map, NatTrans.naturality_assoc,
    Iso.inv_hom_id_app_assoc]
  exact homComplexToGlobalDerivedHomModules_forget F G

end AlgebraicGeometry.RingedSite

end
