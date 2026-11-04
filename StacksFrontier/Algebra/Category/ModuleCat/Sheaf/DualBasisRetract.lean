module

public import Mathlib.CategoryTheory.Retract
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorDualEndomorphism
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A finite dual basis from a finite free retract

Let `𝒪` be a presheaf of commutative rings on a site `(C, J)` whose underlying presheaf of rings
is a sheaf, let `F` be a sheaf of `𝒪`-modules and let `U` be an object of `C`. The local
hypothesis of [Stacks, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV) is that `F` is
*locally a direct summand of a finite free sheaf of modules*: on the members of some covering
family the restriction `F|_U` is a retract of `SheafOfModules.free I` for a finite index type `I`.

The sectionwise form of this hypothesis is a `Stacks.SheafOfModules.FiniteDualBasis`: a finite
family `e` of sections of `F` over `U` together with a family `lam` of sections of the dual `F^∨`
over `U` whose values are the coordinates of every local section with respect to `e`. This file
constructs a finite dual basis from a retract; the converse is
`Stacks.SheafOfModules.nonempty_retract_free_of_localDualBasis`.

The dual basis read off a retract `i ≫ p = 𝟙` of `F|_U` onto `free I` is the expected one:
`e j` is the image under `p` of the `j`-th basis section, and `lam j` is `i` followed by the
`j`-th coordinate projection of the free sheaf of modules.

## Main definitions

* `Stacks.SheafOfModules.FiniteDualBasis.retractSections`: the family `e`, the images under the
  retraction of the basis sections of the free sheaf of modules.
* `Stacks.SheafOfModules.FiniteDualBasis.retractCoords`: the family `lam`, the section `i` of the
  retract followed by the coordinate projections of the free sheaf of modules, read as sections
  of the dual `F^∨` over `U`.
* `Stacks.SheafOfModules.FiniteDualBasis.ofRetract`: **the finite dual basis attached to a
  retract of `F|_U` onto a finite free sheaf of modules.**

## Main results

* `Stacks.SheafOfModules.FiniteDualBasis.retract_r_eq_freeToOver`: the retraction is the morphism
  out of the free sheaf of modules determined by the family `retractSections`.
* `Stacks.SheafOfModules.FiniteDualBasis.span_of_retract`: **the dual-basis identity for the
  families above**, i.e. the `span` field of `ofRetract`: on every object `V` of the slice site
  `C/U` a section `g` of `F` over `V.left` is `∑ j, lam j (g) • (e j)|_V`.

## Implementation notes

**No change of scalars is needed, and no surgery.** A section of `F^∨` over `U` is by Tag 03EM a
morphism `(restrFun 𝒪 U).obj F.val ⟶ (restrFun 𝒪 U).obj 𝒪|_U` of presheaves of modules on the
slice site, while `i` and the coordinate projections are morphisms of *sheaves* of modules on the
slice site, i.e. morphisms out of `(F.over U).val`. Those two presheaves of modules are not
merely isomorphic: they are **equal**, since `restrFun 𝒪 U` and Mathlib's
`SheafOfModules.overFunctor` are both `PresheafOfModules.pushforward` along the identity morphism
of ring presheaves, so `(restrFun 𝒪 U).obj F.val = (F.over U).val` holds by `rfl` and
`retractCoords` is `(i ≫ freeProj j).val` with nothing inserted. In particular the
slice/base scalar boundary that
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceScalarRestriction` crosses with
`Stacks.SheafOfModules.overBase` does not arise here at all: `overBase` respells the scalars of a
presheaf of modules on the slice site, and both sides of this comparison already carry the slice
spelling.

**Where the base spelling does appear, it is already supplied.** The `span` field needs the
generation identity with scalars in `𝒪(V.left)` acting on `F(V.left)`, which is the base
spelling, whereas `Stacks.SheafOfModules.app_eq_sum_smul_freeCoord` of
`...Sheaf.FreeSheafSections` delivers it with scalars in the structure sheaf of the slice site.
Going through that lemma would need the respelling. It is not needed:
`Stacks.SheafOfModules.freeToOver_app_ofCoordsOver` of `...Sheaf.StalkFreeCover` *already* states
the evaluation of a morphism out of the free sheaf of modules on a section given by its
base-spelled coordinates, so the whole of `span_of_retract` is that lemma, the round trip
`ofCoordsOver_coordsOver`, and the retract identity. The two reindexings
`dualApp (retractCoords h j) V g = coordsOver V.unop (h.i.val.app V g) j` and
`resSection V (retractSections h j) = res F V.unop.hom (retractSections h j)` hold by `rfl`, so no
rewriting crosses a transparency boundary.

**`DecidableEq` on the index type.** `Stacks.SheafOfModules.freeProj`, hence `retractCoords`,
needs `DecidableEq I`; `Stacks.SheafOfModules.FiniteDualBasis` itself does not. The hypothesis is
kept rather than discharged by `Classical.decEq` inside `ofRetract` so that `ofRetract_e` and
`ofRetract_lam` are available to consumers as `rfl`: with a classical instance introduced inside
the definition, the two fields could only be described in terms of that instance. A consumer with
an index type carrying no decidable equality supplies `letI := Classical.decEq I`, which costs a
line and loses nothing, every `Fintype` having decidable equality classically.

**Universes.** The site is `C : Type u` with `Category.{v} C` and the module universe is
`max u v`, which is the universe at which `Stacks.SheafOfModules.FiniteDualBasis` and the dual
sheaf are stated; nothing here is narrowed relative to the imported files. The index type `I` is
in `Type (max u v)`, which is forced and not chosen: `SheafOfModules.free` takes its index type in
the module universe. `FiniteDualBasis` leaves its index universe free, so instantiating it here at
`max u v` narrows nothing either — a retract onto `free I` only exists for `I` in that universe.

**Hypotheses.** Beyond the site and the structure sheaf, only the two slice-site sheafification
hypotheses `HasWeakSheafify (J.over U)` and `(J.over U).WEqualsLocallyBijective` for the single
object `U` at hand, which is what `SheafOfModules.free` and `Stacks.SheafOfModules.freeProj` need
on the slice site. In particular no hypothesis on `J` itself is used, and no
`GrothendieckTopology.HasSheafCompose`.

## References

* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
* [Stacks Project, Tag 0FNZ](https://stacks.math.columbia.edu/tag/0FNZ) — the converse direction,
  an exact pairing makes `F` locally a finite free summand.
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM) — the internal hom, whose
  sections over `U` are the morphisms of presheaves of modules on the slice site `C/U`.
-/

@[expose] public section

open CategoryTheory Opposite SheafOfModules

universe v u

namespace Stacks.SheafOfModules.FiniteDualBasis

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
  (h𝒪 : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪))
  {F : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)}
  {U : C} [HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  {I : Type (max u v)}

/-- **The basis sections attached to a retract.** If `F|_U` is a retract of the free sheaf of
modules on `I`, the `j`-th candidate basis section of `F` over `U` is the image under the
retraction of the `j`-th basis section of the free sheaf of modules. -/
noncomputable def retractSections
    (h : Retract (F.over U) (free (R := (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪).over U) I)) (j : I) :
    F.val.obj (op U) :=
  (freeHomEquiv (F.over U) h.r j).eval (op (Over.mk (𝟙 U)))

/-- **The dual coordinates attached to a retract.** The section of the retract followed by the
`j`-th coordinate projection of the free sheaf of modules is a morphism `F|_U ⟶ 𝒪|_U` of
presheaves of modules on the slice site `C/U`, which by Tag 03EM *is* a section of the dual `F^∨`
over `U`. -/
@[sga "3 VIB 11.8" "more general"]
noncomputable def retractCoords [DecidableEq I]
    (h : Retract (F.over U) (free (R := (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪).over U) I)) (j : I) :
    (dualSheaf 𝒪 h𝒪 F).val.obj (op U) :=
  (h.i ≫ freeProj j).val

/-- **The retraction is the morphism determined by the basis sections.** A morphism out of a free
sheaf of modules on the slice site is determined by a family of global sections of the target
there, and a global section of `F.over U` is determined by its value over `U`; so the retraction
of a retract is `Stacks.SheafOfModules.freeToOver` applied to the family
`Stacks.SheafOfModules.FiniteDualBasis.retractSections`. -/
theorem retract_r_eq_freeToOver
    (h : Retract (F.over U) (free (R := (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪).over U) I)) :
    h.r = freeToOver F (retractSections 𝒪 h𝒪 h) :=
  ((freeHomEquiv (F.over U)).symm_apply_apply h.r).symm.trans
    (freeHomEquiv_symm_eq_freeToOver F _)

/-- **The dual-basis identity for the families attached to a retract.** On every object `V` of
the slice site `C/U`, a section `g` of `F` over `V.left` is the combination of the restricted
basis sections with the values of the dual coordinates on `g` as coefficients, the scalars
lying in `𝒪(V.left)`. -/
theorem span_of_retract [Fintype I] [DecidableEq I]
    (h : Retract (F.over U) (free (R := (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪).over U) I))
    (V : (Over U)ᵒᵖ) (g : F.val.obj (op V.unop.left)) :
    ∑ j, dualApp (retractCoords 𝒪 h𝒪 h j) V g •
      resSection V (retractSections 𝒪 h𝒪 h j) = g := by
  have hid : (freeToOver F (retractSections 𝒪 h𝒪 h)).val.app V (h.i.val.app V g) = g := by
    rw [← retract_r_eq_freeToOver 𝒪 h𝒪 h]
    exact congrArg (fun φ : F.over U ⟶ F.over U => φ.val.app V g) h.retract
  have hcoords := freeToOver_app_ofCoordsOver F (retractSections 𝒪 h𝒪 h) V.unop
    (coordsOver (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪) V.unop
      (h.i.val.app V g))
  rw [ofCoordsOver_coordsOver] at hcoords
  exact hcoords.symm.trans hid

/-- **A retract of `F|_U` onto a finite free sheaf of modules is a finite dual basis.** Its
basis sections are `retractSections` and its dual coordinates are `retractCoords`. -/
noncomputable def ofRetract [Fintype I] [DecidableEq I]
    (h : Retract (F.over U) (free (R := (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪).over U) I)) :
    FiniteDualBasis 𝒪 h𝒪 F U I where
  e := retractSections 𝒪 h𝒪 h
  lam := retractCoords 𝒪 h𝒪 h
  span := span_of_retract 𝒪 h𝒪 h

/-- The basis sections of `ofRetract h` are `retractSections h`. -/
@[simp]
lemma ofRetract_e [Fintype I] [DecidableEq I]
    (h : Retract (F.over U) (free (R := (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪).over U) I)) :
    (ofRetract 𝒪 h𝒪 h).e = retractSections 𝒪 h𝒪 h := rfl

/-- The dual coordinates of `ofRetract h` are `retractCoords h`. -/
@[simp]
lemma ofRetract_lam [Fintype I] [DecidableEq I]
    (h : Retract (F.over U) (free (R := (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪).over U) I)) :
    (ofRetract 𝒪 h𝒪 h).lam = retractCoords 𝒪 h𝒪 h := rfl

end Stacks.SheafOfModules.FiniteDualBasis

end
