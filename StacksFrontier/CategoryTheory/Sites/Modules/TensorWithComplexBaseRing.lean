module

public import StacksFrontier.CategoryTheory.Sites.Modules.ComplexesDGCategoryBaseRing
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplex

/-!
# The base ring of Stacks 0CS6 maps to the global sections of the structure sheaf

Stacks 0CS6 fixes a ring `R` and a sheaf `O` of commutative `R`-algebras on a site `C`. The
tensor products over `R` of sheaves of `O`-modules take that hypothesis in the form of
`AlgebraicGeometry.RingedSite.ScalarSections`: a family of sections `scalarSection r U` of `O`
by which the scalar `r` multiplies, with no compatibility imposed between the members of the
family. This file shows that the compatibility is automatic — the family is a *global* section
of `O`, and `r ↦ scalarSection r` is a ring map

`R ⟶ Γ(C, O)`

whose induced linear structure is the given one. So the hypothesis under which Tags 09LV–09LX
are formed over `R` is exactly the source's: a sheaf of commutative `R`-algebras, which is
`Stacks.Cohomology.SiteModules.AlgebraSheaf`.

This is what makes `Γ(C, O)` the universal base ring: every `R` factors through it, and the
`D(R)` of the source is obtained from `D(Γ(C, O))` by restricting scalars along this map.

## Main definitions

* `AlgebraicGeometry.RingedSite.ScalarSections.toGlobalSections`: the ring map
  `R ⟶ Γ(C, O)` carried by a `ScalarSections` instance.
* `AlgebraicGeometry.RingedSite.ScalarSections.algebraSheaf`: the sheaf of `R`-algebra
  structures on `O` that it is — the source's own datum.

## Main results

* `AlgebraicGeometry.RingedSite.ScalarSections.scalarSection_restrict`: the sections by which a
  scalar multiplies are compatible with restriction.
* `AlgebraicGeometry.RingedSite.ScalarSections.smul_eq_globalSections_smul`: a base-ring scalar
  acts on morphisms of sheaves of `O`-modules as its image in `Γ(C, O)` does, so the `R`-linear
  structure is the one restricted along
  `AlgebraicGeometry.RingedSite.ScalarSections.toGlobalSections` by
  `CategoryTheory.Linear.ofRingHom`.
* `AlgebraicGeometry.RingedSite.scalarSectionsGlobalSectionRing`: the universal base ring
  `Γ(C, O)` itself satisfies the hypothesis, with its tautological family of sections.

## Implementation notes

The compatibility is read off the free module of rank one. A base-ring scalar `r` acts on the
identity of a sheaf of `O`-modules `P` by a morphism `r • 𝟙 P`, which by the `smul_app` field of
`AlgebraicGeometry.RingedSite.ScalarSections` multiplies sections over `U` by
`scalarSection r U`. Taking `P` to be the free module of rank one — the unit object of
`Stacks.SheafOfModules.uliftUnit`, whose sections over `U` are `O(U)` raised to the module
universe of the ambient category, with canonical generator `ULift.up 1` — the value of
`r • 𝟙 P` on that generator is `scalarSection r U` itself. A morphism of sheaves of modules is
natural, so those values form a compatible family, which is
`Stacks.SheafOfModules.uliftUnitSection`; that is the restriction compatibility. The ring axioms
are read at the same generator from `one_smul`, `mul_smul`, `add_smul` and `zero_smul`, the
multiplicative one using `smul_app` a second time, at the morphism `r' • 𝟙 P` rather than at the
identity.

The free module has to be taken in the ambient module universe of
`AlgebraicGeometry.RingedSite.TensorModO`, which need not contain the universe of the sections
of `O`; `Stacks.SheafOfModules.uliftUnit` is the unit object raised to it, and it is still free
of rank one.

## References

* [Stacks Project, Tag 0CS6](https://stacks.math.columbia.edu/tag/0CS6)
* [Stacks Project, Tag 09LV](https://stacks.math.columbia.edu/tag/09LV)
* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped IsMulCommutative

namespace AlgebraicGeometry.RingedSite

universe u v w t s o

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
  (R : Type o) [CommRing R] [Linear R (TensorModO.{u, v, w, t, s} X)]

/-- The rings of sections of the structure sheaf are commutative. -/
local instance :
    ∀ object : X.Cᵒᵖ,
      IsMulCommutative ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj object) :=
  fun object => ringSheafSectionsIsMulCommutative X object

universe moduleUniverse

/-- The morphisms between two sheaves of `O`-modules form a module over the global sections of
`O`. -/
local instance
    (source target : SheafOfModules.{moduleUniverse} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    Module ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (source ⟶ target) :=
  Stacks.Cohomology.SiteModules.homModule (Stacks.SheafOfModules.Tensor.ringSheaf X.O) source target

/-- The category of sheaves of `O`-modules is linear over the global sections of `O`. -/
local instance : Linear ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (SheafOfModules.{moduleUniverse} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  Stacks.Cohomology.SiteModules.linearSheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O)

/-- The free `O`-module of rank one, in the ambient module universe of
`AlgebraicGeometry.RingedSite.TensorModO`. Its sections over `U` are those of `O`, raised to that
universe. -/
abbrev freeAmbient : TensorModO.{u, v, w, t, s} X :=
  Stacks.SheafOfModules.uliftUnit.{max u v t s} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)

/-- The canonical generator of the free `O`-module of rank one. -/
abbrev freeAmbientGen (U : X.Cᵒᵖ) : (freeAmbient.{u, v, w, t, s} X).val.obj U :=
  ULift.up (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)

/-- A global section of the structure sheaf, read over an object of the site. -/
abbrev eval (U : X.Cᵒᵖ)
    (a : ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U := a.val U

namespace ScalarSections

variable {X R} [ScalarSections.{u, v, w, t, s, o} X R]

/-- **A scalar acts on the generator of the free module of rank one by its section.** This is
the `smul_app` field of `AlgebraicGeometry.RingedSite.ScalarSections` at the identity of the
free module of rank one, evaluated at the canonical generator. -/
theorem smul_id_freeAmbientGen (r : R) (U : X.Cᵒᵖ) :
    ((r • 𝟙 (freeAmbient.{u, v, w, t, s} X)).val.app U) (freeAmbientGen.{u, v, w, t, s} X U) =
      ULift.up (ScalarSections.scalarSection (X := X) r U) := by
  rw [ScalarSections.smul_app r (𝟙 (freeAmbient.{u, v, w, t, s} X)) U
    (freeAmbientGen.{u, v, w, t, s} X U)]
  change ULift.up (ScalarSections.scalarSection (X := X) r U * 1) = _
  rw [mul_one]

/-- **The sections by which a scalar multiplies are compatible with restriction.** They are the
values of a morphism of sheaves of `O`-modules on the canonical generator of the free module of
rank one, and a morphism of sheaves of modules commutes with restriction. -/
theorem scalarSection_restrict (r : R) {U V : X.Cᵒᵖ} (g : U ⟶ V) :
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map g)
        (ScalarSections.scalarSection (X := X) (R := R) r U) =
      ScalarSections.scalarSection (X := X) (R := R) r V := by
  have h := (Stacks.SheafOfModules.uliftUnitSection
    (r • 𝟙 (freeAmbient.{u, v, w, t, s} X))).property g
  rw [Stacks.SheafOfModules.uliftUnitSection_val, Stacks.SheafOfModules.uliftUnitSection_val,
    smul_id_freeAmbientGen (R := R) r U, smul_id_freeAmbientGen (R := R) r V] at h
  exact congrArg ULift.down h

variable (X R)

/-- **The base ring of Stacks 0CS6 maps to the global sections of the structure sheaf.** The
sections by which a scalar multiplies form a global section of `O`, by
`AlgebraicGeometry.RingedSite.ScalarSections.scalarSection_restrict`, and the assignment is a
ring map because the scalar action of `R` on the identity of the free module of rank one is one.

This is the ring map `R → Γ(C, O)` of
`Stacks.Cohomology.SiteModules.AlgebraSheaf.toGlobalSections`: the datum of a sheaf of
commutative `R`-algebras on `O`, which is the hypothesis of the source. -/
def toGlobalSections :
    R →+* ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) where
  toFun r := ⟨fun U => ScalarSections.scalarSection (X := X) (R := R) r U,
    fun g => scalarSection_restrict (R := R) r g⟩
  map_one' := by
    refine Subtype.ext (funext fun U => ?_)
    have h := smul_id_freeAmbientGen (X := X) (R := R) 1 U
    rw [one_smul] at h
    exact (congrArg ULift.down h).symm
  map_mul' r r' := by
    refine Subtype.ext (funext fun U => ?_)
    have h := smul_id_freeAmbientGen (X := X) (R := R) (r * r') U
    rw [mul_smul, ScalarSections.smul_app r (r' • 𝟙 (freeAmbient.{u, v, w, t, s} X)) U
      (freeAmbientGen.{u, v, w, t, s} X U), smul_id_freeAmbientGen (R := R) r' U] at h
    exact (congrArg ULift.down h).symm
  map_zero' := by
    refine Subtype.ext (funext fun U => ?_)
    have h := smul_id_freeAmbientGen (X := X) (R := R) 0 U
    rw [zero_smul] at h
    change (0 : (freeAmbient.{u, v, w, t, s} X).val.obj U) =
      ULift.up (ScalarSections.scalarSection (X := X) (R := R) 0 U) at h
    exact (congrArg ULift.down h).symm
  map_add' r r' := by
    refine Subtype.ext (funext fun U => ?_)
    have h := smul_id_freeAmbientGen (X := X) (R := R) (r + r') U
    rw [add_smul] at h
    change ((r • 𝟙 (freeAmbient.{u, v, w, t, s} X)) +
      (r' • 𝟙 (freeAmbient.{u, v, w, t, s} X))).val.app U _ = _ at h
    rw [SheafOfModules.add_val, PresheafOfModules.add_app] at h
    simp only [ModuleCat.hom_add, LinearMap.add_apply] at h
    rw [smul_id_freeAmbientGen (R := R) r U, smul_id_freeAmbientGen (R := R) r' U] at h
    exact (congrArg ULift.down h).symm

/-- The section of `toGlobalSections r` over `U` is the section by which `r` multiplies. -/
@[simp] theorem toGlobalSections_val (r : R) (U : X.Cᵒᵖ) :
    (toGlobalSections.{u, v, w, t, s, o} X R r).val U =
      ScalarSections.scalarSection (X := X) (R := R) r U := rfl

/-- **The sheaf of `R`-algebras that a `ScalarSections` instance is.** The structure maps are
the sections by which the scalars multiply; their compatibility with restriction is
`AlgebraicGeometry.RingedSite.ScalarSections.scalarSection_restrict`. -/
def algebraSheaf :
    Stacks.Cohomology.SiteModules.AlgebraSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) R where
  algebraMap U :=
    { toFun r := ScalarSections.scalarSection (X := X) (R := R) r U
      map_one' := congrArg (eval X U) (toGlobalSections X R).map_one
      map_mul' r r' := congrArg (eval X U) ((toGlobalSections X R).map_mul r r')
      map_zero' := congrArg (eval X U) (toGlobalSections X R).map_zero
      map_add' r r' := congrArg (eval X U) ((toGlobalSections X R).map_add r r') }
  algebraMap_restrict g r := scalarSection_restrict (R := R) r g

variable {X R}

/-- **The `R`-linear structure is restricted along the map to the global sections.** A
base-ring scalar acts on a morphism of sheaves of `O`-modules exactly as its image in
`Γ(C, O)` does, so the `Linear R` structure assumed on
`AlgebraicGeometry.RingedSite.TensorModO` agrees with
`CategoryTheory.Linear.ofRingHom` at
`AlgebraicGeometry.RingedSite.ScalarSections.toGlobalSections`. -/
theorem smul_eq_globalSections_smul {P Q : TensorModO.{u, v, w, t, s} X} (r : R) (f : P ⟶ Q) :
    r • f = toGlobalSections.{u, v, w, t, s, o} X R r • f := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
  ext y
  rw [ScalarSections.smul_app r f U y]
  change _ = ((Stacks.Cohomology.SiteModules.globalSmul (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    (toGlobalSections.{u, v, w, t, s, o} X R r) P ≫ f).val.app U) y
  rw [SheafOfModules.comp_val, PresheafOfModules.comp_app]
  change _ = (f.val.app U) ((Stacks.Cohomology.SiteModules.globalSmul
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    (toGlobalSections.{u, v, w, t, s, o} X R r) P).val.app U y)
  rw [Stacks.Cohomology.SiteModules.globalSmul_app]
  exact (map_smul (f.val.app U).hom _ y).symm

end ScalarSections

/-- **The universal base ring satisfies the hypothesis.** For `R = Γ(C, O)` the section by which
a scalar multiplies is the scalar itself, read over `U`; this makes `Γ(C, O)` a base ring for
Tags 09LV–09LX. -/
instance scalarSectionsGlobalSectionRing :
    ScalarSections.{u, v, w, t, s, max u w} X
      ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) where
  scalarSection a U := a.val U
  smul_app a P Q f U y := by
    change ((Stacks.Cohomology.SiteModules.globalSmul
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a P ≫ f).val.app U) y = _
    rw [SheafOfModules.comp_val, PresheafOfModules.comp_app]
    change (f.val.app U) ((Stacks.Cohomology.SiteModules.globalSmul
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a P).val.app U y) = _
    rw [Stacks.Cohomology.SiteModules.globalSmul_app]
    exact map_smul (f.val.app U).hom _ y

end AlgebraicGeometry.RingedSite

end
