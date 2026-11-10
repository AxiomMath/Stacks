module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.Single
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.RestrictionOfComplexes
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroGenerators
public import StacksFrontier.CategoryTheory.Sites.Modules.OverFunctorFree

/-!
# Morphisms of complexes out of the structure sheaf in degree zero, over an object of a site

Let `C` be a small site, `O` a sheaf of rings on it, `U` an object of `C` and `A` a complex of
`O`-modules. A morphism of complexes

`O|_U[0] ⟶ A|_U`

is the same thing as a **degree-zero cocycle section of `A` over `U`**: a section `s` of `A^0`
over `U` with `d(s) = 0`. This file sets up that correspondence.

It is the step at which the source of [Stacks, Tag 0FPV] passes from the coevaluation
`η : 𝒪 → \mathrm{Tot}(ℳ^• ⊗_𝒪 𝒩^•)` to *"the section `η(1)`"*: a morphism out of the structure
sheaf in degree zero is not a section of anything until it is evaluated at `1`, and what makes
the evaluation lossless is that the slice site `C/U` has a terminal object, so that a compatible
family of sections over `C/U` is determined by its value at `U`.

## Main definitions

* `SheafOfModules.unitHomOver`: the morphism `O|_U ⟶ M|_U` of `O|_U`-modules sending `1` to a
  prescribed section of `M` over `U`.
* `SheafOfModules.unitComplexOver`: the structure sheaf of the slice over `U`, in degree zero.
* `SheafOfModules.overFunctorUnitComplexIso`: the restriction to the slice over `U` of the
  structure sheaf in degree zero *is* the structure sheaf of the slice in degree zero.
* `SheafOfModules.cocycleHomOver`: the morphism of complexes `O|_U[0] ⟶ A|_U` attached to a
  degree-zero cocycle section of `A` over `U`.
* `SheafOfModules.cocycleOfOver`: the degree-zero section of `A` over `U` that a morphism of
  complexes `O|_U[0] ⟶ A|_U` sends `1` to.

## Main results

* `SheafOfModules.unitHom_ext_over`: a morphism out of `O|_U` is determined by the image of `1`
  at the terminal object of the slice.
* `SheafOfModules.cocycleOfOver_d`: the section a morphism of complexes produces is a cocycle.
* `SheafOfModules.cocycleOfOver_cocycleHomOver` and `SheafOfModules.eq_cocycleHomOver`: the two
  constructions are mutually inverse.
* `SheafOfModules.cocycleOfOver_comp`: the correspondence is natural in `A`.

## Implementation notes

The module-level half is read off two public site-level equivalences rather than rebuilt:
`SheafOfModules.overSectionsEquiv` of
`StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroGenerators`, which identifies a section
of `M` over `U` with a section of `M|_U` over the whole slice site, and Mathlib's
`SheafOfModules.unitHomEquiv`, which identifies the latter with a morphism out of the unit. Their
composite is `unitHomOver`, and `unitHomOver_val_app_id` is the one fact the rest is proved from.

Restriction to the slice is spelled `SheafOfModules.overFunctor O U`, whose action on a morphism
satisfies `((overFunctor O U).map φ).val.app (op W) = φ.val.app (op W.left)` **definitionally**.
At the terminal object `Over.mk (𝟙 U)` of the slice that is `φ.val.app (op U)` on the nose, which
is why the cocycle condition below is stated with `(A.d 0 1).val.app (op U)` and needs no
transport.

The ringed-space analogue is
`StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.UnitComplexMaps`, stated over the site
of opens of a space with the sections taken at the top open. That is a statement about morphisms
on the *same* site, available because `⊤` is terminal there; the statements below are about
morphisms on the *slice*, which is the form a general site has, and neither specializes to the
other.

## References

* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace SheafOfModules

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (O : Sheaf J RingCat.{u})
  [∀ V : C, HasSheafify (J.over V) AddCommGrpCat.{u}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The morphism `O|_U ⟶ M|_U` sending `1` to a prescribed section of `M` over `U`.** -/
def unitHomOver (M : SheafOfModules.{u} O) (U : C) (s : M.val.obj (op U)) :
    SheafOfModules.unit (O.over U) ⟶ M.over U :=
  (unitHomEquiv (M.over U)).symm (overSections O M U s)

omit [∀ V : C, HasSheafify (J.over V) AddCommGrpCat.{u}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `unitHomOver` sends `1` to the section it was built from. -/
theorem unitHomOver_val_app_id (M : SheafOfModules.{u} O) (U : C) (s : M.val.obj (op U)) :
    (unitHomOver O M U s).val.app (op (Over.mk (𝟙 U)))
      (1 : (O.over U).obj.obj (op (Over.mk (𝟙 U)))) = s :=
  (unitHomEquiv_symm_val_app_one (M.over U) (overSections O M U s) _).trans
    (overSections_eval_id O M U s)

omit [∀ V : C, HasSheafify (J.over V) AddCommGrpCat.{u}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **A morphism out of `O|_U` is determined by the image of `1` at the terminal object of the
slice.** -/
theorem unitHom_ext_over {M : SheafOfModules.{u} O} {U : C}
    {f g : SheafOfModules.unit (O.over U) ⟶ M.over U}
    (h : f.val.app (op (Over.mk (𝟙 U))) (1 : (O.over U).obj.obj (op (Over.mk (𝟙 U)))) =
      g.val.app (op (Over.mk (𝟙 U))) (1 : (O.over U).obj.obj (op (Over.mk (𝟙 U))))) :
    f = g := by
  refine (unitHomEquiv (M.over U)).injective ((overSectionsEquiv O M U).symm.injective ?_)
  change (unitHomEquiv (M.over U) f).val (op (Over.mk (𝟙 U))) =
    (unitHomEquiv (M.over U) g).val (op (Over.mk (𝟙 U)))
  rw [unitHomEquiv_apply_coe, unitHomEquiv_apply_coe]
  exact h

omit [∀ V : C, HasSheafify (J.over V) AddCommGrpCat.{u}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `unitHomOver` is natural: postcomposing it with a morphism of `O`-modules moves the
section. -/
theorem unitHomOver_comp {M N : SheafOfModules.{u} O} (U : C) (s : M.val.obj (op U))
    (g : M ⟶ N) :
    unitHomOver O M U s ≫ (overFunctor O U).map g = unitHomOver O N U (g.val.app (op U) s) :=
  unitHom_ext_over O (by
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, unitHomOver_val_app_id]
    exact congrArg (fun t => g.val.app (op U) t) (unitHomOver_val_app_id O M U s))

/-- **The structure sheaf of the slice over `U`, in degree zero.** -/
def unitComplexOver (U : C) : CochainComplex (SheafOfModules.{u} (O.over U)) ℤ :=
  (HomologicalComplex.single (SheafOfModules.{u} (O.over U)) (ComplexShape.up ℤ) 0).obj
    (SheafOfModules.unit (O.over U))

/-- **The restriction to the slice over `U` of the structure sheaf in degree zero is the
structure sheaf of the slice in degree zero.** Both complexes are `HomologicalComplex.single` at
`0`; restriction commutes with `single`, and it carries the unit to the unit.

This identifies the source of the morphisms that `cocycleOfOver` reads as sections with the
strictly perfect complex that Stacks 08FR (1),
`AlgebraicGeometry.RingedSite.exists_coveringSieve_complexMap`, represents morphisms out of —
the join that lets a morphism of `D(O|_U)` out of the structure sheaf be read, on a covering, as
a section. -/
def overFunctorUnitComplexIso (U : C) :
    ((overFunctor O U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (SheafOfModules.{u} O) (ComplexShape.up ℤ) 0).obj
          (SheafOfModules.unit O)) ≅
      unitComplexOver O U :=
  (HomologicalComplex.singleMapHomologicalComplex (overFunctor O U) (ComplexShape.up ℤ) 0).app
      (SheafOfModules.unit O) ≪≫
    (HomologicalComplex.single (SheafOfModules.{u} (O.over U)) (ComplexShape.up ℤ) 0).mapIso
      (overFunctorUnitIso O U)

/-- **The morphism of complexes `O|_U[0] ⟶ A|_U` attached to a degree-zero cocycle section of
`A` over `U`.** -/
def cocycleHomOver (A : CochainComplex (SheafOfModules.{u} O) ℤ) (U : C)
    (s : (A.X 0).val.obj (op U)) (hs : (A.d 0 1).val.app (op U) s = 0) :
    unitComplexOver O U ⟶
      ((overFunctor O U).mapHomologicalComplex (ComplexShape.up ℤ)).obj A :=
  HomologicalComplex.mkHomFromSingle (unitHomOver O (A.X 0) U s) (fun k hk => by
    obtain rfl : k = 1 := by simpa using hk.symm
    refine unitHom_ext_over O ?_
    change ((unitHomOver O (A.X 0) U s ≫ (overFunctor O U).map (A.d 0 1)).val.app
      (op (Over.mk (𝟙 U)))) (1 : (O.over U).obj.obj (op (Over.mk (𝟙 U)))) = _
    rw [unitHomOver_comp, unitHomOver_val_app_id, hs]
    rfl)

/-- In degree zero, `cocycleHomOver` is `unitHomOver` precomposed with the identification of the
degree-zero term of `O|_U[0]` with `O|_U`. -/
theorem cocycleHomOver_f (A : CochainComplex (SheafOfModules.{u} O) ℤ) (U : C)
    (s : (A.X 0).val.obj (op U)) (hs : (A.d 0 1).val.app (op U) s = 0) :
    (cocycleHomOver O A U s hs).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (SheafOfModules.unit (O.over U))).hom ≫ unitHomOver O (A.X 0) U s :=
  HomologicalComplex.mkHomFromSingle_f _ _

/-- **The degree-zero section of `A` over `U` that a morphism of complexes `O|_U[0] ⟶ A|_U`
sends `1` to.** -/
def cocycleOfOver {A : CochainComplex (SheafOfModules.{u} O) ℤ} {U : C}
    (β : unitComplexOver O U ⟶
      ((overFunctor O U).mapHomologicalComplex (ComplexShape.up ℤ)).obj A) :
    (A.X 0).val.obj (op U) :=
  (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (SheafOfModules.unit (O.over U))).inv ≫ β.f 0).val.app (op (Over.mk (𝟙 U))))
      (1 : (O.over U).obj.obj (op (Over.mk (𝟙 U))))

/-- **The section a morphism of complexes produces is a cocycle.** -/
theorem cocycleOfOver_d {A : CochainComplex (SheafOfModules.{u} O) ℤ} {U : C}
    (β : unitComplexOver O U ⟶
      ((overFunctor O U).mapHomologicalComplex (ComplexShape.up ℤ)).obj A) :
    (A.d 0 1).val.app (op U) (cocycleOfOver O β) = 0 := by
  have hd : (unitComplexOver O U).d 0 1 = 0 :=
    HomologicalComplex.single_obj_d (V := SheafOfModules.{u} (O.over U))
      (c := ComplexShape.up ℤ) 0 (SheafOfModules.unit (O.over U)) 0 1
  have h1 : β.f 0 ≫ (((overFunctor O U).mapHomologicalComplex (ComplexShape.up ℤ)).obj A).d 0 1
      = 0 := (β.comm 0 1).trans (by rw [hd, zero_comp])
  have h2 : (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (SheafOfModules.unit (O.over U))).inv ≫ β.f 0 ≫
        (((overFunctor O U).mapHomologicalComplex (ComplexShape.up ℤ)).obj A).d 0 1 = 0 :=
    (congrArg (fun φ => (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (SheafOfModules.unit (O.over U))).inv ≫ φ) h1).trans comp_zero
  exact (congrArg (fun φ => φ.val.app (op (Over.mk (𝟙 U)))
    (1 : (O.over U).obj.obj (op (Over.mk (𝟙 U))))) h2).trans rfl

/-- The cocycle section of the morphism of complexes attached to a cocycle section `s` is `s`. -/
theorem cocycleOfOver_cocycleHomOver (A : CochainComplex (SheafOfModules.{u} O) ℤ) (U : C)
    (s : (A.X 0).val.obj (op U)) (hs : (A.d 0 1).val.app (op U) s = 0) :
    cocycleOfOver O (cocycleHomOver O A U s hs) = s := by
  rw [cocycleOfOver, cocycleHomOver_f, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  exact unitHomOver_val_app_id O (A.X 0) U s

/-- **A morphism of complexes `O|_U[0] ⟶ A|_U` is the one attached to its own cocycle
section.** -/
theorem eq_cocycleHomOver {A : CochainComplex (SheafOfModules.{u} O) ℤ} {U : C}
    (β : unitComplexOver O U ⟶
      ((overFunctor O U).mapHomologicalComplex (ComplexShape.up ℤ)).obj A) :
    β = cocycleHomOver O A U (cocycleOfOver O β) (cocycleOfOver_d O β) := by
  refine HomologicalComplex.from_single_hom_ext ?_
  rw [cocycleHomOver_f]
  refine (Iso.inv_comp_eq _).1 (unitHom_ext_over O ?_)
  rw [unitHomOver_val_app_id]
  rfl

/-- **`cocycleOfOver` is natural in the complex.** -/
theorem cocycleOfOver_comp {A B : CochainComplex (SheafOfModules.{u} O) ℤ} {U : C}
    (β : unitComplexOver O U ⟶
      ((overFunctor O U).mapHomologicalComplex (ComplexShape.up ℤ)).obj A) (g : A ⟶ B) :
    cocycleOfOver O
        (β ≫ ((overFunctor O U).mapHomologicalComplex (ComplexShape.up ℤ)).map g) =
      (g.f 0).val.app (op U) (cocycleOfOver O β) := by
  have e : (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (SheafOfModules.unit (O.over U))).inv ≫
          (β ≫ ((overFunctor O U).mapHomologicalComplex (ComplexShape.up ℤ)).map g).f 0 =
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (SheafOfModules.unit (O.over U))).inv ≫ β.f 0) ≫ (overFunctor O U).map (g.f 0) :=
    (Category.assoc _ _ _).symm
  exact (congrArg (fun φ : SheafOfModules.unit (O.over U) ⟶ (B.X 0).over U =>
    (φ.val.app (op (Over.mk (𝟙 U))))
      (1 : (O.over U).obj.obj (op (Over.mk (𝟙 U))))) e).trans rfl

end SheafOfModules

end
