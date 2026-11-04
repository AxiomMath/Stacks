module

public import StacksFrontier.CategoryTheory.DifferentialGraded.HomComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHom
public import StacksFrontier.CategoryTheory.Sites.Modules.ComplexesDGCategoryBaseRing

/-!
# The Hom complex is the global sections of the internal Hom complex, over `Γ(C, O)`

Let `(C, O)` be a ringed site and let `F`, `G` be complexes of `O`-modules. Stacks 0A8Z
identifies the Hom complex of `F` and `G` with the complex of global sections of their internal
Hom complex,

`Hom^•_{Comp^dg(O)}(F, G) = Γ(C, SheafHom^•(F, G))`,

and that identification is the first leg of the canonical map of Stacks 0CS6 — the equality the
source writes down just before it maps to the global derived hom of Stacks 0B6E. In
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHom` it is an
identification of complexes of **abelian groups**, which is what puts that canonical map in
`D(ℤ)`.

This file shows that it is an identification of `Γ(C, O)`-**modules** in every degree. Both
sides carry the action of a global section of the structure sheaf — the left by the
`Γ(C, O)`-linear structure of `Stacks.Cohomology.SiteModules.linearSheafOfModules` on the
sheaves of `O`-modules, the right by multiplying a global section of `SheafHom^•(F, G)` — and
the identification carries one to the other.

Stacks 0CS6 fixes a ring `R` and a sheaf of commutative `R`-algebras `O`, and asserts its
canonical map in `D(R)`. Since `R` maps to `Γ(C, O)` — which for the hypothesis under which
Tags 09LV–09LX are formed over `R` is
`AlgebraicGeometry.RingedSite.ScalarSections.toGlobalSections` — `Γ(C, O)` is the universal
base ring, and the statement below is the `R`-linearity of the first leg for every `R` at once.

## Main definitions

* `AlgebraicGeometry.RingedSite.globalSectionsModulesComplex`: global sections of a complex of
  `O`-modules, degreewise, valued in `Γ(C, O)`-modules.
* `AlgebraicGeometry.RingedSite.globalSectionsCochainEquiv`: the degree-`n` identification of
  Stacks 0A8Z as an isomorphism of `Γ(C, O)`-modules.
* `AlgebraicGeometry.RingedSite.globalSectionsHomComplexModulesIsoX`: the same identification
  read into the `Γ(C, O)`-module-valued Hom complex of the differential graded category
  `Comp^dg(O)` over `Γ(C, O)`.
* `AlgebraicGeometry.RingedSite.globalSectionsHomComplexModulesIso`: that identification as an
  isomorphism of *complexes* of `Γ(C, O)`-modules.

## Main results

* `AlgebraicGeometry.RingedSite.globalSectionsIso_smul`: the identification of Stacks 0A8Z is
  `Γ(C, O)`-linear.

## Implementation notes

The linearity is read on components. A cochain is determined by its values
`F^p ⟶ G^q` on sections, and the identification is characterized there by
`AlgebraicGeometry.RingedSite.sheafHomComplex_globalSectionsIso_v_app`: the value over `U` of
the cochain attached to a global section `s` is the value over the identity of `U` of the
cochain attached to `s` over `U`. On that local description the scalar action is the
`smul_natural` field of `AlgebraicGeometry.RingedSite.SheafHomComplex`, and since the arrow is
the identity its restriction of the scalar is the scalar itself. On the other side a global
section acts on a cochain through `Stacks.Cohomology.SiteModules.globalSmul`, that is by
multiplying the source of each component, and the components are `O`-linear, so that too is
multiplication by the section over `U`.

Two spellings of the same module have to be reconciled for this to elaborate.
`PresheafOfModules.sections` is a subtype of the sections taken *through the forgetful functor*
to abelian groups, at which spelling the module structure is not found by instance search;
`moduleSectionsForget` reinstates it, as the corresponding local instance of
`StacksFrontier.AlgebraicGeometry.Modules.IdentityEndomorphismScalar` does on a scheme. And the
`smul_natural` field cannot be used by `rw`, because the coercion of the module-valued global
sections to that subtype makes the rewritten term ill-typed at `implicit` transparency; it is
applied by `Eq.trans` instead.

Assembling the degreewise identification into an isomorphism of complexes needs the differential
of `DGCategory.homComplexModules`, which is a `dite` on the degrees, compared with the
differential of the Hom complex. Done at this category of sheaves of modules that comparison
exhausts the heartbeat budget of a single declaration, because the `dite` is reached only
through the structure instance `CochainComplex.dgCategoryLinear`. The normal form
`CochainComplex.dgCategoryLinear_homComplexModules_d_apply` pays that cost once, on an element
and at an abstract base category, after which the commuting square is the commuting square of
the abelian-group-valued identification read on an element, and
`AlgebraicGeometry.RingedSite.globalSectionsHomComplexModulesIso` is immediate. That
isomorphism is the first leg of the canonical map of Stacks 0CS6 over `Γ(C, O)`, which is
assembled in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomModuleMap`.

## References

* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 0B6E](https://stacks.math.columbia.edu/tag/0B6E)
* [Stacks Project, Tag 0CS6](https://stacks.math.columbia.edu/tag/0CS6)
* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite CochainComplex.HomComplex Stacks.Cohomology.SiteModules
open scoped IsMulCommutative

namespace AlgebraicGeometry.RingedSite

universe u

variable (X : RingedSite.{u, u, u})

/-- Global sections of a complex of `O`-modules, degreewise, valued in modules over the ring
`Γ(C, O)` of global sections of the structure sheaf. Forgetting the scalars gives
`AlgebraicGeometry.RingedSite.globalSectionsComplex`, on the nose. -/
abbrev globalSectionsModulesComplex
    (H : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    CochainComplex
      (ModuleCat.{u} ↥(GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ :=
  letI : (globalSectionsModules X).Additive :=
    globalSectionsFunctor_additive.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  ((globalSectionsModules X).mapHomologicalComplex (ComplexShape.up ℤ)).obj H

/-- **Forgetting the scalars gives the abelian-group-valued global sections complex.** -/
theorem globalSectionsModulesComplex_forget
    (H : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((forget₂ (ModuleCat.{u} ↥(GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
        AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (globalSectionsModulesComplex X H) = globalSectionsComplex X H := rfl

/-- The module structure on the sections of a sheaf of `O`-modules, at the spelling through the
forgetful functor to abelian groups in which `PresheafOfModules.sections` states them. This is
the existing instance restated, so nothing new is assumed. -/
local instance moduleSectionsForget
    (H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.Cᵒᵖ) :
    Module ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)
      ((H.val.presheaf ⋙ forget AddCommGrpCat).obj U) :=
  inferInstanceAs (Module _ (H.val.obj U))

variable {X}
  (F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- **The identification of Stacks 0A8Z is `Γ(C, O)`-linear.** A global section of the
structure sheaf acts on a global section of the internal Hom complex by multiplying it, and on
the corresponding cochain by multiplying the source of each of its components; the local
description of the internal Hom complex carries the first to the second. -/
theorem globalSectionsIso_smul (n : ℤ)
    (a : ↥(GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (s : (globalSectionsModulesComplex X (sheafHomComplex X F G).obj).X n) :
    letI := linearSheafOfModules.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    (show Cochain F G n from
        ((sheafHomComplex X F G).globalSectionsIso.hom.f n (a • s)).down) =
      a • (show Cochain F G n from
        ((sheafHomComplex X F G).globalSectionsIso.hom.f n s).down) := by
  let := linearSheafOfModules.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  apply Cochain.ext
  intro p q hpq
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  ext x
  set U := V.unop with hU
  rw [sheafHomComplex_globalSectionsIso_v_app X F G n p q hpq (a • s) U x, Cochain.smul_v]
  change _ = ((globalSmul (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a (F.X p) ≫
    ((sheafHomComplex X F G).globalSectionsIso.hom.f n s).down.v p q hpq).val.app (op U)) x
  rw [SheafOfModules.comp_val, PresheafOfModules.comp_app]
  change _ = (((sheafHomComplex X F G).globalSectionsIso.hom.f n s).down.v p q hpq).val.app
    (op U) ((globalSmul (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a (F.X p)).val.app (op U) x)
  rw [globalSmul_app, map_smul, sheafHomComplex_globalSectionsIso_v_app X F G n p q hpq s U x]
  change (((AddCommGrpCat.Hom.hom (((sheafHomComplex X F G).sectionsIso U).hom.f n)
      (a.val (op U) • s.val (op U))).v p q hpq).val.app (op (Over.mk (𝟙 U)))) x = _
  refine Eq.trans ((sheafHomComplex X F G).smul_natural U (a.val (op U)) n p q hpq
    (s.val (op U)) (𝟙 U) x) ?_
  have hid : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map (𝟙 U).op) (a.val (op U)) =
      a.val (op U) := by
    rw [op_id, (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map_id]
    rfl
  rw [hid]

/-- The degree-`n` identification of Stacks 0A8Z, as an isomorphism of additive groups: a
global section of the internal Hom complex is a cochain. -/
def globalSectionsCochainAddEquiv (n : ℤ) :
    ↥((globalSectionsModulesComplex X (sheafHomComplex X F G).obj).X n) ≃+ Cochain F G n :=
  (((HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.up ℤ) n).mapIso
      (sheafHomComplex X F G).globalSectionsIso).addCommGroupIsoToAddEquiv).trans
    (AddEquiv.ulift (α := Cochain F G n))

/-- `globalSectionsCochainAddEquiv` sends a global section of the internal Hom complex to the
cochain given by the degree-`n` component of `globalSectionsIso`. -/
@[simp] theorem globalSectionsCochainAddEquiv_apply (n : ℤ)
    (s : ↥((globalSectionsModulesComplex X (sheafHomComplex X F G).obj).X n)) :
    globalSectionsCochainAddEquiv F G n s =
      (show Cochain F G n from
        ((sheafHomComplex X F G).globalSectionsIso.hom.f n s).down) := rfl

/-- **The degree-`n` identification of Stacks 0A8Z over `Γ(C, O)`.** The global sections of
the internal Hom complex in degree `n` are the `Γ(C, O)`-module of degree-`n` cochains from `F`
to `G`. -/
def globalSectionsCochainEquiv (n : ℤ) :
    letI := linearSheafOfModules.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    ↥((globalSectionsModulesComplex X (sheafHomComplex X F G).obj).X n) ≃ₗ[
        ↥(GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] Cochain F G n :=
  letI := linearSheafOfModules.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  (globalSectionsCochainAddEquiv F G n).toLinearEquiv
    (fun c x => globalSectionsIso_smul F G n c x)

/-- **The degree-`n` identification read into the differential graded category over
`Γ(C, O)`.** The degree-`n` homogeneous morphisms `F ⟶ G` of `Comp^dg(O)`, taken over
`Γ(C, O)`, are the global sections of the internal Hom complex in degree `n`. -/
def globalSectionsHomComplexModulesIsoX (n : ℤ) :
    (globalSectionsModulesComplex X (sheafHomComplex X F G).obj).X n ≅
      ((compDGGlobalSections (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).homComplexModules
        F G).X n :=
  (globalSectionsCochainEquiv F G n).toModuleIso

/-- **Stacks 0A8Z over `Γ(C, O)`.** The complex of global sections of the internal Hom complex of
`F` and `G` is the Hom complex `Hom^•_{Comp^dg(O)}(F, G)` of the differential graded category
`Comp^dg(O)` taken over `Γ(C, O)`: an isomorphism of complexes of `Γ(C, O)`-modules, not only a
degreewise one.

This is the first leg of the canonical map of Stacks 0CS6 read over the ring of global sections
of the structure sheaf, which by
`Stacks.Cohomology.SiteModules.AlgebraSheaf.toGlobalSections` is the universal base ring of that
tag. -/
def globalSectionsHomComplexModulesIso :
    globalSectionsModulesComplex X (sheafHomComplex X F G).obj ≅
      (compDGGlobalSections (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).homComplexModules F G :=
  letI := linearSheafOfModules.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  HomologicalComplex.Hom.isoOfComponents (globalSectionsHomComplexModulesIsoX F G) (by
    intro n m hnm
    obtain rfl : m = n + 1 := hnm.symm
    refine ModuleCat.hom_ext (LinearMap.ext fun s => ?_)
    have hcomm := (sheafHomComplex X F G).globalSectionsIso.hom.comm n (n + 1)
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_comp, LinearMap.comp_apply]
    refine Eq.trans (CochainComplex.dgCategoryLinear_homComplexModules_d_apply
      (B := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (R := ↥(GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) F G n
      (n + 1) rfl _) ?_
    exact congrArg (fun φ => ULift.down (AddCommGrpCat.Hom.hom φ s)) hcomm)

end AlgebraicGeometry.RingedSite

end
