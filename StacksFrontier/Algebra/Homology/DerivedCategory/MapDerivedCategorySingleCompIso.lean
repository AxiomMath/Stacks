module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomologyCompare

/-!
# The single-functor comparison against composition and against an isomorphism

An exact additive functor `F` between abelian categories with derived categories commutes with
the single functor `DerivedCategory.singleFunctor`, by Mathlib's
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`: it reads `Φ(A[-n])` as `(F A)[-n]`,
where `Φ` is `CategoryTheory.Functor.mapDerivedCategory`.  This file proves the two structural
laws that comparison satisfies:

* it is compatible with **composition** of exact functors, read through
  `Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso`;
* it is compatible with an **isomorphism** of exact functors, read through
  `Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso`.

Together the two laws compute the single-functor comparison of any isomorphism of functors on
derived categories assembled out of those two constructions, which is what
`Stacks.Cohomology.ModulePushforwardComparison.derivedModulePushforwardCompToSheafIso` is.  The
library already had exactly these two laws for the *cohomology* comparison, as
`CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso_comp_app` and
`CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso_isoOfNatIso_app` of
`StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomologyCompIso`, which this file
mirrors; it had neither for the single-functor comparison, and Mathlib supplies neither.

## Main results

* `HomologicalComplex.singleMapHomologicalComplex_comp`: **the composition law at the level of
  complexes.**  The degreewise comparison `HomologicalComplex.singleMapHomologicalComplex` of a
  composite is the composite of the two comparisons.
* `HomologicalComplex.singleMapHomologicalComplex_natTrans`: **the transformation law at the
  level of complexes.**  The degreewise comparison intertwines
  `CategoryTheory.NatTrans.mapHomologicalComplex` with the single complex on the transformation.
* `CategoryTheory.Functor.mapDerivedCategorySingleFunctor_comp` and
  `CategoryTheory.Functor.mapDerivedCategorySingleFunctor_comp_app`: **the composition law**, as
  an equality of natural transformations and at an object.
* `CategoryTheory.Functor.mapDerivedCategorySingleFunctor_isoOfNatIso` and
  `CategoryTheory.Functor.mapDerivedCategorySingleFunctor_isoOfNatIso_app`: **the isomorphism
  law**, in the same two forms.

## Implementation notes

Unlike the cohomology comparison, the single-functor comparison is a transformation between
functors **out of the abelian category itself**, not out of its derived category, so no
`CategoryTheory.Localization.natTrans_ext` is needed: an object of `C₁` is already the general
case, and the two laws are checked there directly.

What makes them work is that at an object both sides collapse, by
`mapDerivedCategorySingleFunctor_hom_app`, to the canonical factorisation of the degreewise
action of the functor through `DerivedCategory.Q` followed by the localisation of one
complex-level comparison.  The factorisations cancel against the values of
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso` and
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso` at the image of a cochain
complex, together with one naturality square of
`CategoryTheory.Functor.mapDerivedCategoryFactors`, and what is left is the corresponding law
for `HomologicalComplex.singleMapHomologicalComplex`.  Those two complex-level laws hold at an
arbitrary complex shape for functors preserving zero morphisms, which is how they are stated;
each is checked in the one degree where a morphism out of a single complex can be nonzero, by
`HomologicalComplex.from_single_hom_ext`.

**No declaration here carries a `@[stacks ...]` attribute.**  These are coherences between
canonical isomorphisms of Mathlib's and this library's making; they state no result of the
source.
-/

@[expose] public noncomputable section

universe w₃ w₂ w₁ v₃ v₂ v₁ u₃ u₂ u₁

open CategoryTheory Category Limits

/-! ### The laws at the level of complexes -/

namespace HomologicalComplex

variable {ι : Type*} [DecidableEq ι] (c : ComplexShape ι)
  {W₁ : Type u₁} [Category.{v₁} W₁] [Preadditive W₁] [HasZeroObject W₁]
  {W₂ : Type u₂} [Category.{v₂} W₂] [Preadditive W₂] [HasZeroObject W₂]
  {W₃ : Type u₃} [Category.{v₃} W₃] [Preadditive W₃] [HasZeroObject W₃]

/-- **The degreewise single-complex comparison is compatible with composition.**  Forming the
complex supported in degree `j` and then applying `F` and `G` degreewise is identified with
applying `F ⋙ G` and then forming the complex, either in one step or in two. -/
theorem singleMapHomologicalComplex_comp (F : W₁ ⥤ W₂) [F.PreservesZeroMorphisms]
    (G : W₂ ⥤ W₃) [G.PreservesZeroMorphisms] (j : ι) (A : W₁) :
    (G.mapHomologicalComplex c).map ((singleMapHomologicalComplex F c j).hom.app A) ≫
        (singleMapHomologicalComplex G c j).hom.app (F.obj A) =
      (singleMapHomologicalComplex (F ⋙ G) c j).hom.app A := by
  apply to_single_hom_ext
  simp [← G.map_comp_assoc]

/-- **The degreewise single-complex comparison is natural in the functor.**  A natural
transformation `α : F ⟶ G` acts degreewise on complexes, and the two comparisons intertwine that
action with the complex supported in degree `j` on `α` itself. -/
theorem singleMapHomologicalComplex_natTrans {F G : W₁ ⥤ W₂} [F.PreservesZeroMorphisms]
    [G.PreservesZeroMorphisms] (α : F ⟶ G) (j : ι) (A : W₁) :
    (NatTrans.mapHomologicalComplex α c).app ((single W₁ c j).obj A) ≫
        (singleMapHomologicalComplex G c j).hom.app A =
      (singleMapHomologicalComplex F c j).hom.app A ≫ (single W₂ c j).map (α.app A) := by
  apply to_single_hom_ext
  simp [single_map_f_self, α.naturality_assoc]

end HomologicalComplex

/-! ### The laws on the derived category -/

namespace CategoryTheory.Functor

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]

/-- **Mathlib's `CategoryTheory.Functor.mapDerivedCategorySingleFunctor` at an object**: the
canonical factorisation of the degreewise action of `F` through `DerivedCategory.Q`, followed by
the localisation of `HomologicalComplex.singleMapHomologicalComplex`.  A copy of the statement of
the same name in `StacksDraft.Topology.Sheaves.Cohomology.DerivedCategory`
`.ExactFunctorSingleHomology`, where it is `private`. -/
private theorem singleFunctor_hom_app (F : C₁ ⥤ C₂)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] (n : ℤ) (A : C₁) :
    (F.mapDerivedCategorySingleFunctor n).hom.app A =
      F.mapDerivedCategoryFactors.hom.app
          ((HomologicalComplex.single C₁ (ComplexShape.up ℤ) n).obj A) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex F
            (ComplexShape.up ℤ) n).hom.app A) := by
  simp only [comp_obj, mapDerivedCategorySingleFunctor, DerivedCategory.singleFunctorIsoCompQ,
    isoWhiskerRight_refl, isoWhiskerLeft_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_hom,
    isoWhiskerLeft_hom, Iso.symm_hom, isoWhiskerRight_hom, Iso.refl_hom, NatTrans.comp_app,
    associator_hom_app, whiskerLeft_app, associator_inv_app, DerivedCategory.Q_obj_single_obj,
    whiskerRight_app, NatTrans.id_app, comp_id, id_comp]
  exact Category.id_comp _

/-- `DerivedCategory.singleFunctor` is by construction the complex supported in degree `n`
followed by `DerivedCategory.Q`, so its action on a morphism is the localisation of the action of
`HomologicalComplex.single`.  The two are definitionally equal but not syntactically so, which is
why this restatement is needed before a rewrite can use it. -/
private theorem singleFunctor_map (n : ℤ) {X Y : C₂} (f : X ⟶ Y) :
    (DerivedCategory.singleFunctor C₂ n).map f =
      DerivedCategory.Q.map
        ((HomologicalComplex.single C₂ (ComplexShape.up ℤ) n).map f) := rfl

section Comp

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃)
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- `Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_app_Q` at a single complex.
The object `(DerivedCategory.singleFunctor C₁ n).obj A` is the image under `DerivedCategory.Q` of
the complex supported in degree `n`, but not syntactically so, which is why this restatement is
needed before a rewrite can use it. -/
private theorem compIso_inv_app_single (n : ℤ) (A : C₁) :
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso F G).inv.app
        ((DerivedCategory.singleFunctor C₁ n).obj A) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app
          ((HomologicalComplex.single C₁ (ComplexShape.up ℤ) n).obj A)) ≫
        G.mapDerivedCategoryFactors.hom.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((HomologicalComplex.single C₁ (ComplexShape.up ℤ) n).obj A)) ≫
          (F ⋙ G).mapDerivedCategoryFactors.inv.app
            ((HomologicalComplex.single C₁ (ComplexShape.up ℤ) n).obj A) :=
  Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_app_Q F G _

/-- **The composition law at an object.**  The comparison of the two descents of the composite,
followed by the comparison for the composite functor, is the outer descent applied to the
comparison for the inner functor, followed by the comparison for the outer one. -/
theorem mapDerivedCategorySingleFunctor_comp_app (n : ℤ) (A : C₁) :
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso F G).inv.app
          ((DerivedCategory.singleFunctor C₁ n).obj A) ≫
        ((F ⋙ G).mapDerivedCategorySingleFunctor n).hom.app A =
      G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor n).hom.app A) ≫
        (G.mapDerivedCategorySingleFunctor n).hom.app (F.obj A) := by
  have hnat : G.mapDerivedCategory.map (DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex F
            (ComplexShape.up ℤ) n).hom.app A)) ≫
        G.mapDerivedCategoryFactors.hom.app
          ((HomologicalComplex.single C₂ (ComplexShape.up ℤ) n).obj (F.obj A)) =
      G.mapDerivedCategoryFactors.hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((HomologicalComplex.single C₁ (ComplexShape.up ℤ) n).obj A)) ≫
        DerivedCategory.Q.map ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex F
            (ComplexShape.up ℤ) n).hom.app A)) :=
    G.mapDerivedCategoryFactors.hom.naturality _
  rw [compIso_inv_app_single, singleFunctor_hom_app, singleFunctor_hom_app,
    singleFunctor_hom_app, G.mapDerivedCategory.map_comp]
  simp only [assoc, Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% hnat, ← DerivedCategory.Q.map_comp,
    HomologicalComplex.singleMapHomologicalComplex_comp]

/-- **The composition law**, as an equality of natural transformations out of
`single ⋙ (F ⋙ G)ᴰ`. -/
theorem mapDerivedCategorySingleFunctor_comp (n : ℤ) :
    Functor.whiskerLeft (DerivedCategory.singleFunctor C₁ n)
          (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso F G).inv ≫
        ((F ⋙ G).mapDerivedCategorySingleFunctor n).hom =
      (show DerivedCategory.singleFunctor C₁ n ⋙ F.mapDerivedCategory ⋙ G.mapDerivedCategory ⟶
          (F ⋙ G) ⋙ DerivedCategory.singleFunctor C₃ n from
        Functor.whiskerRight (F.mapDerivedCategorySingleFunctor n).hom G.mapDerivedCategory ≫
          Functor.whiskerLeft F (G.mapDerivedCategorySingleFunctor n).hom) := by
  ext A
  exact mapDerivedCategorySingleFunctor_comp_app F G n A

end Comp

section NatIso

variable (F G : C₁ ⥤ C₂)
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G)

/-- `Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso` at the image of a cochain
complex; a copy of the statement of the same name in
`StacksFrontier.Topology.Sheaves.Cohomology.ModulePushforwardComparison.DerivedCategory`. -/
theorem isoOfNatIso_hom_app_Q (P : CochainComplex C₁ ℤ) :
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso F G e).hom.app
        (DerivedCategory.Q.obj P) =
      F.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app P) ≫
        G.mapDerivedCategoryFactors.inv.app P := by
  simp [Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso,
    lifting_iso_mapDerivedCategory]

/-- `isoOfNatIso_hom_app_Q` at a single complex.  The object
`(DerivedCategory.singleFunctor C₁ n).obj A` is the image under `DerivedCategory.Q` of the
complex supported in degree `n`, but not syntactically so, which is why this restatement is
needed before a rewrite can use it. -/
private theorem isoOfNatIso_hom_app_single (n : ℤ) (A : C₁) :
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso F G e).hom.app
        ((DerivedCategory.singleFunctor C₁ n).obj A) =
      F.mapDerivedCategoryFactors.hom.app
          ((HomologicalComplex.single C₁ (ComplexShape.up ℤ) n).obj A) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app
            ((HomologicalComplex.single C₁ (ComplexShape.up ℤ) n).obj A)) ≫
          G.mapDerivedCategoryFactors.inv.app
            ((HomologicalComplex.single C₁ (ComplexShape.up ℤ) n).obj A) :=
  isoOfNatIso_hom_app_Q F G e _

/-- **The isomorphism law at an object.**  The descent of an isomorphism of exact functors,
followed by the comparison for the target functor, is the comparison for the source functor
followed by the isomorphism placed in degree `n`. -/
theorem mapDerivedCategorySingleFunctor_isoOfNatIso_app (n : ℤ) (A : C₁) :
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso F G e).hom.app
          ((DerivedCategory.singleFunctor C₁ n).obj A) ≫
        (G.mapDerivedCategorySingleFunctor n).hom.app A =
      (F.mapDerivedCategorySingleFunctor n).hom.app A ≫
        (DerivedCategory.singleFunctor C₂ n).map (e.hom.app A) := by
  rw [isoOfNatIso_hom_app_single, singleFunctor_hom_app, singleFunctor_hom_app,
    singleFunctor_map]
  simp only [assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp]
  exact congrArg (fun f => _ ≫ DerivedCategory.Q.map f)
    (HomologicalComplex.singleMapHomologicalComplex_natTrans _ e.hom n A)

/-- **The isomorphism law**, as an equality of natural transformations out of `single ⋙ Fᴰ`. -/
theorem mapDerivedCategorySingleFunctor_isoOfNatIso (n : ℤ) :
    Functor.whiskerLeft (DerivedCategory.singleFunctor C₁ n)
          (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso F G e).hom ≫
        (G.mapDerivedCategorySingleFunctor n).hom =
      (F.mapDerivedCategorySingleFunctor n).hom ≫
        Functor.whiskerRight e.hom (DerivedCategory.singleFunctor C₂ n) := by
  ext A
  exact mapDerivedCategorySingleFunctor_isoOfNatIso_app F G e n A

end NatIso

end CategoryTheory.Functor

end
