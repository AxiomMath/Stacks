module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeSheafSections

/-!
# The sectionwise relations among a finite family of sections, and the kernel of the free sheaf

Fix a site `(C, J)`, a sheaf of rings `R`, a sheaf of `R`-modules `M`, an object `U` and a finite
family `s : I → M(U)` of sections. There are two descriptions of the relations among `s` over an
object `V → U` of the slice site:

* the **sectionwise** one, `Stacks.SheafOfModules.relationsSubmodule M.val s V`, the submodule of
  tuples `a : I → R(V.left)` with `∑ i, a i • s i|_V = 0`. This is how Stacks 03DL states
  coherence, and it mentions neither the free sheaf of modules nor sheafification;
* the **categorical** one, the sections over `V` of `kernel (freeToOver M s)`, a kernel taken in
  the abelian category `SheafOfModules (R.over U)`.

This file identifies them, elementwise and in both directions, through the coordinate layer
`Stacks.SheafOfModules.coordsOver` / `ofCoordsOver` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover`, whose whole purpose is that it
spells its scalars `R(V.left)` — the spelling the sectionwise description needs — rather than
`(R.over U).obj.obj (op V)`, the spelling `free`, `kernel` and
`Stacks.SheafOfModules.exists_kernel_section` use.

## Main results

* `Stacks.SheafOfModules.injective_app_kernel_ι` : the inclusion of a kernel of a morphism of
  sheaves of modules is injective on the sections over every object.
* `Stacks.SheafOfModules.app_freeToOver_eq_sum_smul_coordsOver` : the morphism out of the free
  sheaf determined by `s` sends a section of `free I` over `V` to the linear combination of the
  restricted `s` with that section's coordinates as coefficients, the whole identity written with
  scalars in `R(V.left)`.
* `Stacks.SheafOfModules.coordsOver_mem_relationsSubmodule_iff` : **the coordinates of a section
  of `free I` over `V` are a relation among `s` exactly when that section is killed by
  `freeToOver M s`.**
* `Stacks.SheafOfModules.coordsOver_kernel_mem_relationsSubmodule` : the coordinates of a section
  of `kernel (freeToOver M s)` over `V` are a relation among `s`.
* `Stacks.SheafOfModules.exists_kernel_section_coordsOver_eq` : conversely, every relation among
  `s` over `V` is the coordinate tuple of a section of `kernel (freeToOver M s)` over `V`.
* `Stacks.SheafOfModules.bijOn_coordsOver_kernel` : **the two descriptions agree.** Taking
  coordinates is a bijection from the sections of `kernel (freeToOver M s)` over `V` onto
  `relationsSubmodule M.val s V`.

## Implementation notes

**What this file does not do, and why.** It does not build an isomorphism of presheaves of
modules `relationsPresheaf M.val s ≅ (kernel (freeToOver M s)).val`, which is what would let
`Stacks.SheafOfModules.isFiniteTypeSections_of_iso` transport finite type from the kernel to the
sectionwise relations. The obstruction is not the elementwise mathematics — that is exactly the
bijection proved here — but the *scalar action*: for `a : ToType (R.obj.obj (op V.left))` and a
section `e` of `free I` over `V` the expression `a • e` has no `HSMul` instance, because instance
synthesis will not unfold `(R.over U).obj.obj (op V)` to `R.obj.obj (op V.left)`. So the
bijection below cannot be packaged as a semilinear map without an explicit
`ModuleCat.restrictScalars` wrapper on one side, in the manner
`Stacks.SheafOfModules.relationsPresheaf` itself uses. The results here are the elementwise
content such a wrapper would be built on, and they are stated so as to be usable as they stand:
each one quantifies over an arbitrary object `V` of the slice site and keeps every scalar in
`R(V.left)`.

**Why the statements are elementwise and not about `LinearMap.ker`.**
`relationsSubmodule M.val s V` is defined as `LinearMap.ker (Fintype.linearCombination …)`, so
membership unfolds to a vanishing sum, and that sum is the only form in which the two
descriptions can be compared; the proofs go through it rather than through any `ker` API.

**Why `Fintype I` and not `Finite I`.** `relationsSubmodule` and `ofCoordsOver` both take
`Fintype I`, since both are stated with an explicit `∑ i : I`. A `Finite` version would have to
choose a `Fintype` instance and would then not be about the same submodule.

**Which sheafification hypotheses.** Only the slice ones. The two coordinate formulas need
`HasWeakSheafify (J.over U)`, which is what `SheafOfModules.free` itself needs; the three
statements that mention a kernel need `HasSheafify (J.over U)`, since the kernel is taken in
`SheafOfModules (R.over U)` and that is where its abelian structure comes from. The base site
carries no hypothesis at all.

**Universes.** The site is `C : Type u'` with `Category.{v} C`, the sheaf of rings is
`R : Sheaf J RingCat.{u}` and the sheaves of modules are `SheafOfModules.{u} R`, the same three
independent universes `StalkFreeCover` uses. The index type is in `Type u`, which is what
`SheafOfModules.free` requires.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 01B4](https://stacks.math.columbia.edu/tag/01B4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

universe u v u'

namespace Stacks.SheafOfModules

/-! ### Kernels are sectionwise, in the injective direction -/

section Kernel

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

universe u₂

/-- **The inclusion of a kernel is injective on sections over every object.** This is the
companion of `Stacks.SheafOfModules.exists_kernel_section`, which is the surjective direction:
together they say that the sections of `kernel g` over an object are exactly the sections of the
source killed by `g`. Evaluation at an object preserves monomorphisms, and a monomorphism of
modules is an injective map. The universe of the module sections is independent of the universe
of the sections of the sheaf of rings. -/
theorem injective_app_kernel_ι {N P : SheafOfModules.{u₂} R} (g : N ⟶ P) (V : Cᵒᵖ) :
    Function.Injective ((kernel.ι g).val.app V) :=
  (ModuleCat.mono_iff_injective _).mp ((SheafOfModules.evaluation R V).map_mono (kernel.ι g))

end Kernel

/-! ### The restriction used by the sectionwise relations -/

section Restrict

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- The restriction of a section of `M` that `Stacks.SheafOfModules.relationsSubmodule` is
written with is `Stacks.SheafOfModules.res`. Both sides are `M.val.map V.hom.op m`; the two
spellings differ only in which API they belong to. -/
theorem restrictₛₗ_eq_res (M : SheafOfModules.{u} R) {U : C} (V : Over U)
    (m : ToType (M.val.obj (op U))) : M.val.restrictₛₗ V.hom.op m = res M V.hom m := rfl

end Restrict

/-! ### Coordinates of a section of the free sheaf as a tuple of relations -/

section Coords

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  (M : SheafOfModules.{u} R) {U : C} [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] {I : Type u} [DecidableEq I] [Fintype I]
  (s : I → ToType (M.val.obj (op U)))

/-- **The morphism out of the free sheaf on `s`, evaluated through coordinates in the base.** The
value at a section `e` of `free I` over an object `V` of the slice site is the linear combination
of the restrictions of `s` with the coordinates of `e` as coefficients. Both the coefficients and
the restricted sections are read over `V.left`, so the whole identity lives in the base
spelling. -/
theorem app_freeToOver_eq_sum_smul_coordsOver (V : Over U)
    (e : ToType ((free (R := R.over U) I).val.obj (op V))) :
    (freeToOver M s).val.app (op V) e
      = ∑ i : I, coordsOver V e i • res M V.hom (s i) :=
  (congrArg (fun y => (freeToOver M s).val.app (op V) y)
    (ofCoordsOver_coordsOver V e)).symm.trans
      (freeToOver_app_ofCoordsOver M s V (coordsOver V e))

/-- **The coordinates of a section of `free I` over `V` are a relation among `s` exactly when
that section is killed by `freeToOver M s`.** This is the comparison of the sectionwise
description of the relations with the categorical one, at the level of elements. -/
theorem coordsOver_mem_relationsSubmodule_iff (V : Over U)
    (e : ToType ((free (R := R.over U) I).val.obj (op V))) :
    coordsOver V e ∈ relationsSubmodule M.val s V
      ↔ (freeToOver M s).val.app (op V) e = 0 := by
  rw [app_freeToOver_eq_sum_smul_coordsOver, LinearMap.mem_ker,
    Fintype.linearCombination_apply]
  exact Iff.rfl

end Coords

/-! ### The two descriptions of the relations agree -/

section CoordsKernel

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  (M : SheafOfModules.{u} R) {U : C} [HasSheafify (J.over U) AddCommGrpCat.{u}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] {I : Type u} [DecidableEq I] [Fintype I]
  (s : I → ToType (M.val.obj (op U)))

/-- **The coordinates of a section of the kernel are a relation among `s`.** -/
theorem coordsOver_kernel_mem_relationsSubmodule (V : Over U)
    (w : ToType ((kernel (freeToOver M s)).val.obj (op V))) :
    coordsOver V ((kernel.ι (freeToOver M s)).val.app (op V) w)
      ∈ relationsSubmodule M.val s V :=
  (coordsOver_mem_relationsSubmodule_iff M s V _).mpr
    (congrArg (fun φ : kernel (freeToOver M s) ⟶ M.over U => φ.val.app (op V) w)
      (kernel.condition (freeToOver M s)))

/-- **Every relation among `s` over `V` is the coordinate tuple of a section of the kernel.**
Kernels of morphisms of sheaves of modules are computed sectionwise
(`Stacks.SheafOfModules.exists_kernel_section`), so the section of `free I` with the given
coordinates lifts to the kernel. -/
theorem exists_kernel_section_coordsOver_eq (V : Over U)
    (a : I → ToType (R.obj.obj (op V.left))) (ha : a ∈ relationsSubmodule M.val s V) :
    ∃ w : ToType ((kernel (freeToOver M s)).val.obj (op V)),
      coordsOver V ((kernel.ι (freeToOver M s)).val.app (op V) w) = a := by
  obtain ⟨w, hw⟩ := exists_kernel_section (freeToOver M s) (op V) (ofCoordsOver V a)
    ((coordsOver_mem_relationsSubmodule_iff M s V _).mp
      (by rw [coordsOver_ofCoordsOver]; exact ha))
  exact ⟨w, (congrArg (fun y => coordsOver V y) hw).trans (coordsOver_ofCoordsOver V a)⟩

/-- **The sectionwise and categorical descriptions of the relations among `s` agree.** Taking
coordinates in the base is a bijection from the sections of `kernel (freeToOver M s)` over an
object `V` of the slice site onto the submodule of relations among the restrictions of `s`.

Injectivity is `Stacks.SheafOfModules.injective_app_kernel_ι` followed by the round trip
`Stacks.SheafOfModules.ofCoordsOver_coordsOver`; the other two halves are
`coordsOver_kernel_mem_relationsSubmodule` and `exists_kernel_section_coordsOver_eq`. -/
theorem bijOn_coordsOver_kernel (V : Over U) :
    Set.BijOn (fun w : ToType ((kernel (freeToOver M s)).val.obj (op V)) =>
        coordsOver V ((kernel.ι (freeToOver M s)).val.app (op V) w))
      Set.univ (relationsSubmodule M.val s V) := by
  refine ⟨fun w _ => coordsOver_kernel_mem_relationsSubmodule M s V w, fun w _ w' _ hww => ?_,
    fun a ha => ?_⟩
  · refine injective_app_kernel_ι (freeToOver M s) (op V) ?_
    exact ((ofCoordsOver_coordsOver V _).symm.trans
      (congrArg (ofCoordsOver V) hww)).trans (ofCoordsOver_coordsOver V _)
  · obtain ⟨w, hw⟩ := exists_kernel_section_coordsOver_eq M s V a ha
    exact ⟨w, Set.mem_univ w, hw⟩

end CoordsKernel

end Stacks.SheafOfModules

end
