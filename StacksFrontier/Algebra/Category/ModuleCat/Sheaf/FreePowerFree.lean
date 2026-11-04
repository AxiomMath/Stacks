module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseAlgebras
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerSheafification
public import StacksFrontier.LinearAlgebra.SymmetricPower.FreePresentation

/-!
# Symmetric and exterior powers of a finite free sheaf of modules are sectionwise free

Let `(C, J)` be a site, `O` a presheaf of commutative rings on it whose underlying presheaf of
rings is a sheaf, and `ι` a finite type. Stacks Tag 01CG identifies the degree-`n` symmetric power
`Symⁿ F` of a sheaf of `O`-modules with the **sheafification** of the presheaf of sectionwise
symmetric powers `V ↦ Symⁿ_{O(V)}(F(V))`, and likewise for the exterior powers. This file settles
the sectionwise half of the free case of Stacks Tag 00DN at that presheaf: for the free sheaf of
modules `SheafOfModules.free ι` on a finite index type,

`Symⁿ_{O(V)}((free ι)(V))` and `⋀ⁿ_{O(V)}((free ι)(V))`

are **free** `O(V)`-modules, of finite rank, for every object `V` of the site, and an explicit
basis is produced in each case.

## Main definitions

* `Stacks.SheafOfModules.freeCoordLinearEquiv` : the coordinates of a section of a finite free
  sheaf of modules, as a linear equivalence `(free ι)(V) ≃ₗ[O(V)] (ι → O(V))`. This is
  `Stacks.SheafOfModules.freeCoord_bijective` with its linearity recorded.
* `Stacks.SheafOfModules.freeCoordBasis` : the resulting basis of `(free ι)(V)`, indexed by `ι`.
* `Stacks.SheafOfModules.basisSymPowSections` : the monomial basis of
  `(PresheafOfModules.symPow n (free ι).val)(V)`, indexed by the degree-`n` monomials
  `{d : ι →₀ ℕ | d.degree = n}`.
* `Stacks.SheafOfModules.basisExtPowSections` : the basis of
  `(PresheafOfModules.extPow n (free ι).val)(V)`, indexed by the `n`-element subsets of `ι` for a
  linear order on `ι`, which is Mathlib's `Module.Basis.exteriorPower`.

## Main results

* `Stacks.SheafOfModules.free_freeSections` and `finite_freeSections` : the sections of a finite
  free sheaf of modules over any object form a free module of finite rank.
* `Stacks.SheafOfModules.free_symPowSections` and `finite_symPowSections` : **the sectionwise
  symmetric power of a finite free sheaf of modules is free of finite rank over every object.**
* `Stacks.SheafOfModules.free_extPowSections` and `finite_extPowSections` : **the sectionwise
  exterior power of a finite free sheaf of modules is free of finite rank over every object.**

## Implementation notes

**The base is `ringSheafOfIsSheaf`, not `CategoryTheory.Sheaf.toRingCat`.**
`PresheafOfModules.symPow` and `PresheafOfModules.extPow` take a presheaf of modules over a ring
presheaf that is *syntactically* `O ⋙ forget₂ CommRingCat RingCat`, while `toRingCat J O♯` is a
`CategoryTheory.Sheaf.obj` applied to a bundled sheaf, so unification has to unfold it and gets
stuck on the resulting universe constraints. `SheafOfModules.GradedAlgebra.ringSheafOfIsSheaf`
packages the same data with the presheaf kept in the syntactic form, and
`SheafOfModules.GradedAlgebra.ringSheafOfIsSheaf_eq_toRingCat` shows the two coincide on the
nose, so the results apply to `toRingCat J O♯` as well.

**Finiteness does not go through the basis.** `Finite {d : ι →₀ ℕ | d.degree = n}` is not an
instance, and `SymPow.finite_symmetricPower` needs no basis and no freeness — only that the
sections are a finite module — so `Module.Finite.equiv` transports it along
`PresheafOfModules.symPowSections`.

**Decidability and the order on the index.** `Stacks.SheafOfModules.freeCoord_bijective` needs
`DecidableEq ι`, and Mathlib's exterior basis needs a `LinearOrder ι`; neither appears in the
statements of the freeness and finiteness instances, so those are proved with `classical` rather
than carrying a hypothesis their types do not mention. The two bases keep the hypothesis they
genuinely need, since their index types depend on it.

## References

* [Stacks Project, Tag 00DN](https://stacks.math.columbia.edu/tag/00DN)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Tag 01CL](https://stacks.math.columbia.edu/tag/01CL)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules.GradedAlgebra (ringSheafOfIsSheaf)

universe v u₁ u

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  {O : Cᵒᵖ ⥤ CommRingCat.{u}}
  (hO : Presheaf.IsSheaf J (O ⋙ forget₂ CommRingCat RingCat))
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-! ### The sections of a finite free sheaf of modules -/

/-- **The coordinates of a section of a finite free sheaf of modules, as a linear
equivalence.** For finite `ι` the coproduct `SheafOfModules.free ι = ∐ unit O` is also a product,
so taking coordinates is a linear bijection from the sections over an object to the families of
sections of the structure sheaf. -/
noncomputable def freeCoordLinearEquiv {ι : Type u} [DecidableEq ι] [Finite ι] (V : Cᵒᵖ) :
    ToType ((_root_.SheafOfModules.free (R := ringSheafOfIsSheaf hO) ι).val.obj V) ≃ₗ[
        ToType ((ringSheafOfIsSheaf hO).obj.obj V)]
      (ι → ToType ((ringSheafOfIsSheaf hO).obj.obj V)) :=
  LinearEquiv.ofBijective
    ({ toFun := freeCoord (S := ringSheafOfIsSheaf hO) V
       map_add' := fun a b => funext fun i =>
         ((freeProj (S := ringSheafOfIsSheaf hO) i).val.app V).hom.map_add a b
       map_smul' := fun r a => funext fun i =>
         ((freeProj (S := ringSheafOfIsSheaf hO) i).val.app V).hom.map_smul r a } :
      ToType ((_root_.SheafOfModules.free (R := ringSheafOfIsSheaf hO) ι).val.obj V) →ₗ[
          ToType ((ringSheafOfIsSheaf hO).obj.obj V)]
        (ι → ToType ((ringSheafOfIsSheaf hO).obj.obj V)))
    (freeCoord_bijective V)

/-- The linear equivalence `freeCoordLinearEquiv` sends a section to its family of coordinates
`freeCoord`. -/
@[simp]
theorem freeCoordLinearEquiv_apply {ι : Type u} [DecidableEq ι] [Finite ι] (V : Cᵒᵖ)
    (e : ToType ((_root_.SheafOfModules.free (R := ringSheafOfIsSheaf hO) ι).val.obj V)) :
    freeCoordLinearEquiv hO V e = freeCoord (S := ringSheafOfIsSheaf hO) V e :=
  rfl

/-- The basis of the sections of a finite free sheaf of modules over an object, indexed by the
index type of the free sheaf and dual to the coordinates. -/
noncomputable def freeCoordBasis {ι : Type u} [DecidableEq ι] [Finite ι] (V : Cᵒᵖ) :
    Module.Basis ι (ToType ((ringSheafOfIsSheaf hO).obj.obj V))
      (ToType ((_root_.SheafOfModules.free (R := ringSheafOfIsSheaf hO) ι).val.obj V)) :=
  (Pi.basisFun (ToType ((ringSheafOfIsSheaf hO).obj.obj V)) ι).map
    (freeCoordLinearEquiv hO V).symm

/-- The sections of a finite free sheaf of modules over an object form a free module. -/
instance free_freeSections {ι : Type u} [Finite ι] (V : Cᵒᵖ) :
    Module.Free (ToType ((ringSheafOfIsSheaf hO).obj.obj V))
      (ToType ((_root_.SheafOfModules.free (R := ringSheafOfIsSheaf hO) ι).val.obj V)) := by
  classical
  exact Module.Free.of_basis (freeCoordBasis hO V)

/-- The sections of a finite free sheaf of modules over an object form a finite module. -/
instance finite_freeSections {ι : Type u} [Finite ι] (V : Cᵒᵖ) :
    Module.Finite (ToType ((ringSheafOfIsSheaf hO).obj.obj V))
      (ToType ((_root_.SheafOfModules.free (R := ringSheafOfIsSheaf hO) ι).val.obj V)) := by
  classical
  exact Module.Finite.of_basis (freeCoordBasis hO V)

/-! ### The sectionwise symmetric powers of a finite free sheaf of modules -/

/-- **The monomial basis of the sectionwise symmetric power of a finite free sheaf of modules.**
Over each object `V` the sections of `PresheafOfModules.symPow n (free ι).val` are
`Symⁿ_{O(V)}((free ι)(V))`, and `(free ι)(V)` is free on `ι`, so the degree-`n` monomials in
those coordinates form a basis; the index type is the degree-`n` elements of `ι →₀ ℕ`. -/
noncomputable def basisSymPowSections {ι : Type u} [DecidableEq ι] [Finite ι] (n : ℕ)
    (V : Cᵒᵖ) :
    Module.Basis {d : ι →₀ ℕ | d.degree = n} (ToType ((ringSheafOfIsSheaf hO).obj.obj V))
      (ToType ((PresheafOfModules.symPow n
        (_root_.SheafOfModules.free (R := ringSheafOfIsSheaf hO) ι).val).obj V)) :=
  (SymPow.basisSymmetricPower (freeCoordBasis hO V) n).map
    (PresheafOfModules.symPowSections n
      (_root_.SheafOfModules.free (R := ringSheafOfIsSheaf hO) ι).val V).symm

/-- **The sectionwise symmetric power of a finite free sheaf of modules is free over every
object.** -/
instance free_symPowSections {ι : Type u} [Finite ι] (n : ℕ) (V : Cᵒᵖ) :
    Module.Free (ToType ((ringSheafOfIsSheaf hO).obj.obj V))
      (ToType ((PresheafOfModules.symPow n
        (_root_.SheafOfModules.free (R := ringSheafOfIsSheaf hO) ι).val).obj V)) :=
  Module.Free.of_equiv
    (PresheafOfModules.symPowSections n
      (_root_.SheafOfModules.free (R := ringSheafOfIsSheaf hO) ι).val V).symm

/-- **The sectionwise symmetric power of a finite free sheaf of modules is of finite rank over
every object.** -/
instance finite_symPowSections {ι : Type u} [Finite ι] (n : ℕ) (V : Cᵒᵖ) :
    Module.Finite (ToType ((ringSheafOfIsSheaf hO).obj.obj V))
      (ToType ((PresheafOfModules.symPow n
        (_root_.SheafOfModules.free (R := ringSheafOfIsSheaf hO) ι).val).obj V)) :=
  Module.Finite.equiv
    (PresheafOfModules.symPowSections n
      (_root_.SheafOfModules.free (R := ringSheafOfIsSheaf hO) ι).val V).symm

/-! ### The sectionwise exterior powers of a finite free sheaf of modules -/

/-- **A basis of the sectionwise exterior power of a finite free sheaf of modules.** Over each
object `V` the sections of `PresheafOfModules.extPow n (free ι).val` are
`⋀ⁿ_{O(V)}((free ι)(V))`, and `(free ι)(V)` is free on `ι`, so for a linear order on `ι` the
wedges of `n`-element subsets of the coordinates form a basis; this is Mathlib's
`Module.Basis.exteriorPower`. -/
noncomputable def basisExtPowSections {ι : Type u} [LinearOrder ι] [Finite ι] (n : ℕ)
    (V : Cᵒᵖ) :
    Module.Basis ↥(Set.powersetCard ι n) (ToType ((ringSheafOfIsSheaf hO).obj.obj V))
      (ToType ((PresheafOfModules.extPow n
        (_root_.SheafOfModules.free (R := ringSheafOfIsSheaf hO) ι).val).obj V)) :=
  ((freeCoordBasis hO V).exteriorPower n).map
    (PresheafOfModules.extPowSections n
      (_root_.SheafOfModules.free (R := ringSheafOfIsSheaf hO) ι).val V).symm

/-- **The sectionwise exterior power of a finite free sheaf of modules is free over every
object.** -/
instance free_extPowSections {ι : Type u} [Finite ι] (n : ℕ) (V : Cᵒᵖ) :
    Module.Free (ToType ((ringSheafOfIsSheaf hO).obj.obj V))
      (ToType ((PresheafOfModules.extPow n
        (_root_.SheafOfModules.free (R := ringSheafOfIsSheaf hO) ι).val).obj V)) :=
  Module.Free.of_equiv
    (PresheafOfModules.extPowSections n
      (_root_.SheafOfModules.free (R := ringSheafOfIsSheaf hO) ι).val V).symm

/-- **The sectionwise exterior power of a finite free sheaf of modules is of finite rank over
every object.** -/
instance finite_extPowSections {ι : Type u} [Finite ι] (n : ℕ) (V : Cᵒᵖ) :
    Module.Finite (ToType ((ringSheafOfIsSheaf hO).obj.obj V))
      (ToType ((PresheafOfModules.extPow n
        (_root_.SheafOfModules.free (R := ringSheafOfIsSheaf hO) ι).val).obj V)) :=
  Module.Finite.equiv
    (PresheafOfModules.extPowSections n
      (_root_.SheafOfModules.free (R := ringSheafOfIsSheaf hO) ι).val V).symm

end Stacks.SheafOfModules

end
