module

public import StacksFrontier.AlgebraicGeometry.Coherent.IdealSheafFiniteTypeBridge
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.FiniteTypeIdealSheafDirected.Operations
public import StacksFrontier.AlgebraicGeometry.Modules.IdealSheafDataSubmodule

/-!
# Finite type for the two spellings of a quasi-coherent sheaf of ideals

A quasi-coherent sheaf of ideals on a scheme `X` is spelled in two ways in this library:
`AlgebraicGeometry.Scheme.IdealSheafData`, which records the ideal of sections over each affine
open, and a submodule of the structure sheaf regarded as a sheaf of modules, which is what
`AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule` produces. Each spelling carries its own
finite type condition: `AlgebraicGeometry.Scheme.IdealSheafData.IsFiniteType` asks that every
one of those ideals be finitely generated, while `SheafOfModules.IsFiniteType` asks for local
generation by finitely many sections.

This file identifies the two. For a quasi-coherent sheaf of modules, finite type is exactly
finiteness of the sections over every affine open, and the sections of `I.unitSubmodule` over
an affine open are `I.ideal` there; so the two conditions say the same thing about the same
object.

## Main results

* `Stacks.FiniteTypeIdealSheaf.isFiniteType_unitSubmodule_iff`: **the dictionary** — a sheaf of
  ideals is of finite type exactly when the submodule of the structure sheaf it determines is.
* `Stacks.FiniteTypeIdealSheaf.isFiniteType_unitSubmodule` and
  `Stacks.FiniteTypeIdealSheaf.isFiniteType_of_isFiniteType_unitSubmodule`: the two directions
  separately, the second with the module condition as an instance.

## Implementation notes

Both directions run through `Module.Finite`: finite generation of an ideal is finiteness of it
as a module (`Module.Finite.iff_fg`), and the equality of submodules
`AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule_obj_affine` is crossed once, by a
rewrite. The geometric content is entirely in the two halves already available:
`Stacks.AlgebraicGeometry.FiniteTypeBridge.isFiniteType_of_finite_sections` for one direction
and `AlgebraicGeometry.moduleFinite_sections_on_affine` for the other.

The module structure on the sections of `I.unitSubmodule.toSheafOfModules` over an affine open
is **not** synthesizable at that spelling — the instance `Module Γ(X, U) Γ(M, U)` matches only
when the sheaf of modules is presented as a term of type `AlgebraicGeometry.Scheme.Modules`,
and the structure projections of `SheafOfModules.Submodule.toSheafOfModules` do not reduce to
that form at instance transparency. Every statement below therefore obtains the instance by
*unification* rather than synthesis: the submodule argument `N` of `Module.Finite.iff_fg` is
supplied explicitly in the first direction, and in the second the module structure arrives
through the restatement `moduleFinite_sections_affine`, whose parameter is declared at type
`AlgebraicGeometry.Scheme.Modules`. This is the `instance_reducible` issue documented at
`StacksFrontier/AlgebraicGeometry/AffineExtend/Basic.lean`.

The dictionary is **not** needed to obtain [Stacks, Tag 01PG] for a sheaf of ideals: that
statement is proved natively in the `IdealSheafData` lattice as
`AlgebraicGeometry.isSupOfFinitePresentation_of_qcqs`, and is restated in the finite type
vocabulary as `Stacks.FiniteTypeIdealSheaf.iSup_isFiniteType_eq`. What the dictionary is for is
transporting the finite type hypothesis between results stated at the two spellings.

## References

* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace Stacks.FiniteTypeIdealSheaf

variable {X : Scheme.{u}}

/-- **A finite type sheaf of ideals determines a finite type submodule of the structure
sheaf.** Over an affine open the sections of `I.unitSubmodule` are the ideal `I.ideal U`, which
is finitely generated, hence finite as a module; finite type of a quasi-coherent sheaf of
modules is detected by its sections over the affine opens. -/
theorem isFiniteType_unitSubmodule (I : X.IdealSheafData) (hI : I.IsFiniteType) :
    I.unitSubmodule.toSheafOfModules.IsFiniteType := by
  refine Stacks.AlgebraicGeometry.FiniteTypeBridge.isFiniteType_of_finite_sections _
    fun V ↦ (Module.Finite.iff_fg
      (N := I.unitSubmodule.toSubmodule.obj (op V.1))).mpr ?_
  rw [I.unitSubmodule_obj_affine V]
  exact hI V

/-- The sections of a quasi-coherent sheaf of modules of finite type over an affine open are a
finite module, stated with the sheaf of modules as a parameter.

`AlgebraicGeometry.moduleFinite_sections_on_affine` says exactly this; the point of restating it
is that `M` is declared here at type `AlgebraicGeometry.Scheme.Modules`, so instantiating it at
`N.toSheafOfModules` substitutes the module structure on the sections instead of asking for it
to be synthesized at a spelling where it is not found. -/
private lemma moduleFinite_sections_affine (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (U : X.affineOpens) : Module.Finite Γ(X, U.1) Γ(M, U.1) :=
  AlgebraicGeometry.moduleFinite_sections_on_affine M U.1 U.2

/-- **The converse.** If the submodule of the structure sheaf determined by `I` is of finite
type then its sections over every affine open are a finite module, and they are the ideal
`I.ideal U`. -/
theorem isFiniteType_of_isFiniteType_unitSubmodule (I : X.IdealSheafData)
    [I.unitSubmodule.toSheafOfModules.IsFiniteType] : I.IsFiniteType := fun V ↦ by
  have hsub : (I.unitSubmodule.toSubmodule.obj (op V.1)).FG :=
    Module.Finite.iff_fg.mp (moduleFinite_sections_affine I.unitSubmodule.toSheafOfModules V)
  rwa [I.unitSubmodule_obj_affine V] at hsub

/-- **The dictionary between the two finite type conditions on a quasi-coherent sheaf of
ideals.** -/
theorem isFiniteType_unitSubmodule_iff (I : X.IdealSheafData) :
    I.unitSubmodule.toSheafOfModules.IsFiniteType ↔ I.IsFiniteType :=
  ⟨fun h ↦ have := h; isFiniteType_of_isFiniteType_unitSubmodule I,
    isFiniteType_unitSubmodule I⟩

end Stacks.FiniteTypeIdealSheaf

end
