module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Retract
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.Flat.Basic

/-!
# A projective presheaf of modules is objectwise projective

Let `C` be a small category and let `R : Cᵒᵖ ⥤ RingCat` be a presheaf of rings. Mathlib resolves
every presheaf of modules `M` over `R` by an epimorphism
`M.fromFreeYonedaCoproduct : M.freeYonedaCoproduct ⟶ M`,
where `M.freeYonedaCoproduct` is the coproduct, indexed by the elements of `M`, of the free
presheaves of modules on representable presheaves of types. If `M` is a projective object then the
identity of `M` factors through that epimorphism, so `M` is a retract of
`M.freeYonedaCoproduct`.

Evaluation at an object `X : Cᵒᵖ` is a functor `PresheafOfModules R ⥤ ModuleCat (R.obj X)` which
preserves colimits, so it takes `M.freeYonedaCoproduct` to the coproduct of the modules of
sections of the free presheaves, each of which is a free `R.obj X`-module. A coproduct of
projective objects is projective and a retract of a projective object is projective, so the
sections of a projective presheaf of modules over any object form a projective module.

## Main results

* `PresheafOfModules.projective_obj`: if `P` is a projective object of `PresheafOfModules R`,
  then `P.obj X` is a projective `R.obj X`-module for every `X : Cᵒᵖ`.
* `PresheafOfModulesOfCommRing.flat_obj`: if the presheaf of rings is a presheaf of commutative
  rings, the sections of a projective presheaf of modules are moreover flat.

## Implementation notes

`Module.Flat` is only defined over a commutative base ring, so `flat_obj` is stated for a
presheaf of modules over a presheaf of commutative rings, i.e. for the category
`PresheafOfModulesOfCommRing R`; `projective_obj` needs no commutativity.

The site, the rings and the modules live in one universe `u`, as they must for
`PresheafOfModules.freeYonedaCoproduct` to be available.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace PresheafOfModules

variable {C : Type u} [SmallCategory C] {R : Cᵒᵖ ⥤ RingCat.{u}}

/-- The sections over `X` of the free presheaf of modules on a presheaf of types `F` form the
free `R.obj X`-module on `F.obj X`, hence a projective object of `ModuleCat (R.obj X)`. -/
instance projective_free_obj (F : Cᵒᵖ ⥤ Type u) (X : Cᵒᵖ) :
    Projective (((free R).obj F).obj X) :=
  ModuleCat.projective_of_free (M := ((free R).obj F).obj X)
    (Finsupp.basisSingleOne (ι := F.obj X) (R := R.obj X))

/-- The sections over `X` of `M.freeYonedaCoproduct` form a projective `R.obj X`-module:
evaluation at `X` preserves coproducts, and each summand has free modules of sections. -/
instance projective_freeYonedaCoproduct_obj (M : PresheafOfModules.{u} R) (X : Cᵒᵖ) :
    Projective (M.freeYonedaCoproduct.obj X) := by
  have : ∀ m : M.Elements, Projective ((evaluation R X).obj (Elements.freeYoneda m)) :=
    fun m ↦ projective_free_obj (R := R) (yoneda.obj m.1.unop) X
  exact Projective.of_iso
    (PreservesCoproduct.iso (evaluation R X) (Elements.freeYoneda (M := M))).symm inferInstance

/-- A projective presheaf of modules `P` is a retract of `P.freeYonedaCoproduct`: the identity of
`P` factors through the epimorphism `P.fromFreeYonedaCoproduct`. -/
def retractFreeYonedaCoproduct (P : PresheafOfModules.{u} R) [Projective P] :
    Retract P P.freeYonedaCoproduct where
  i := Projective.factorThru (𝟙 P) P.fromFreeYonedaCoproduct
  r := P.fromFreeYonedaCoproduct
  retract := Projective.factorThru_comp _ _

/-- **A projective presheaf of modules is objectwise projective**: if `P` is a projective object
of `PresheafOfModules R`, then its module of sections over any object `X` is a projective
`R.obj X`-module. -/
theorem projective_obj (P : PresheafOfModules.{u} R) [Projective P] (X : Cᵒᵖ) :
    Module.Projective (R.obj X) (P.obj X) := by
  have : Projective ((evaluation R X).obj P.freeYonedaCoproduct) :=
    projective_freeYonedaCoproduct_obj P X
  have : Projective (P.obj X) :=
    Retract.projective (P.retractFreeYonedaCoproduct.map (evaluation R X))
  exact ModuleCat.projective_of_module_projective (P.obj X)

end PresheafOfModules

namespace PresheafOfModulesOfCommRing

variable {C : Type u} [SmallCategory C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- **A projective presheaf of modules over a presheaf of commutative rings is objectwise flat**:
its module of sections over any object `X` is projective, hence flat, over `R.obj X`. -/
theorem flat_obj (P : PresheafOfModulesOfCommRing.{u} R) [CategoryTheory.Projective P]
    (X : Cᵒᵖ) : Module.Flat (R.obj X) (obj P X) := by
  have : Module.Projective (R.obj X) (obj P X) := PresheafOfModules.projective_obj P X
  infer_instance

end PresheafOfModulesOfCommRing

end
