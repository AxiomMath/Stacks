module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalEtaleRestrictionSquareMap
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafMapStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelIdealSquareMap

/-!
# The map of kernel ideal sheaves of a square agrees in degree one with the map of defining ideal
sheaves

Let
```
Z --i--→ X
|        |
f        g
↓        ↓
Z' -i'-→ X'
```
be a commutative square of algebraic spaces over a scheme `S` contained in a big fppf site `B`,
in which `Z` is a closed subspace of `X` and `Z'` is a closed subspace of `X'` and `i`, `i'` are
their inclusions.  Two maps `g^*𝓘' ⟶ 𝓘` are then available, built the same way out of the same
chartwise pullback of regular functions but from different descriptions of the two sheaves of
ideals:

* `AlgebraicGeometry.Space.idealSheafMap`, the map of [Stacks Project, Tag 04CP] built from the
  **defining** ideal sheaves of the two closed subspaces (Stacks 03MB);
* `AlgebraicGeometry.Space.kernelIdealSquareMap` in degree one, built from the powers of the
  **kernel** ideal sheaves of `i` and `i'`, whose second factor is the ambient map
  `AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraAmbient.lean`.

This file proves that the two agree.  That is the degree-one agreement which the implementation
notes of `StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraAmbient.lean` recorded as not
asserted.

## Main results

* `AlgebraicGeometry.Space.kernelIdealSquareMap_one_eq_idealSheafMap`: **the map of kernel ideal
  sheaves of the square in degree one is the map of defining ideal sheaves**, across the
  transports of its source and target along
  `AlgebraicGeometry.Space.kernelIdealSheafZPow_one_eq_definingIdealSheaf`.
* `AlgebraicGeometry.Space.kernelIdealSheafZPow_one_eq_definingIdealSheaf`: the degree-one power
  of the kernel ideal sheaf of the inclusion of a closed subspace is its defining ideal sheaf.

## Route

Both maps are pinned by the same equation — their composite with the inclusion of the ideal
sheaf into the structure sheaf, which is
`AlgebraicGeometry.Space.idealSheafMap_comp_definingIdealSheaf_ι` on one side and
`AlgebraicGeometry.Space.kernelIdealSquareMap_comp_ι` on the other, the two right-hand sides
being the same term once the two sheaves of ideals are identified.  The inclusion is a
monomorphism, so the two maps agree.

The identification of the sheaves of ideals is
`AlgebraicGeometry.Space.kernelIdealSheafZPow_one` followed by
`AlgebraicGeometry.Space.kernelIdealSheaf_eq_definingIdealSheaf`, which is `rfl`; it is an
equality of submodules of the unit module, so it is carried past the two inclusions by
`Stacks.SheafOfModules.Submodule.eqToHom_comp_ι` and under the inverse image by
`CategoryTheory.eqToHom_map`.  Nothing beyond degree one is available: for `n ≠ 1` there is no
map of defining ideal sheaves to compare with.

## Implementation notes

**The statement is in the `AlgebraicGeometry.Space.kernelIdealSquareMap` spelling, and that is
forced.**  `AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap B S hS i g 1` has
`g^*(Ker((i ≫ g)^♯))` for its source, the kernel ideal sheaf of the composite `Z ⟶ X'`, which is
the defining ideal sheaf of `Z'` only when `Z ⟶ X'` is itself the inclusion of `Z'`.  So the
ambient map alone has no source in common with
`AlgebraicGeometry.Space.idealSheafMap`, and the agreement can be stated, without adding a
hypothesis, only for the square map — which by
`AlgebraicGeometry.Space.kernelIdealSquareMap_eq` is the inverse image of the containment of the
two kernel ideal sheaves followed by that ambient map.  An agreement for the ambient map alone is
available only where `i ≫ g` is itself the inclusion of a closed subspace of `X'`, as the case
`i' = i ≫ g`, `f = 𝟙` of the statement below; that is a hypothesis on `g ∘ i`, so it is not what
is proved here.

**The crossing of the two spellings of the category of modules is supplied, not left to
unification.**  The equality of sheaves of ideals holds in
`Stacks.SheafOfModules.Submodule` of `AlgebraicGeometry.Space.structureRingSheaf`, while the
inverse image is a functor out of `AlgebraicGeometry.Space.Modules`; `rw` with
`AlgebraicGeometry.Space.kernelIdealSquareMap_comp_ι` against the cancelled goal reports *did not
find an occurrence of the pattern*, with the note that the target is not type-correct at
`implicit` transparency and the application type mismatch between
`SheafOfModules (structureRingSheaf B S hS X')` and `Modules B S hS X'.obj _`.  The whole
assembly is therefore an instantiation of `CategoryTheory.eq_eqToHom_comp_comp_eqToHom_of_mono`,
stated at variables in an arbitrary category, where every reassociation is done; this is the
same discipline the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/KernelIdealSquareMap.lean` record for that file.  The
monomorphism is passed explicitly rather than found by instance search: at the instantiation its
morphism is still a metavariable, and the search fails there while succeeding against an
ascribed `have`.

## References

* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 09RS](https://stacks.math.columbia.edu/tag/09RS)
-/

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory

/-- **Two maps agree across the transports of their source and target when each has the same
composite with the inclusion of its target and one inclusion is a monomorphism.**

`m` goes `F.obj A ⟶ T` and `m'` goes `F.obj A' ⟶ T'`, with `A = A'` and `T' = T`; the inclusions
`ιA`, `ιA'` of the sources into a common `O` and `ιT`, `ιT'` of the targets into a common `V`
correspond under the transports, and `m`, `m'` have the same composite `F.map _ ≫ t` with the
latter.  Then `m` is `m'` conjugated by the transports.

Stated at variables in an arbitrary category so that a consumer supplies existing lemmas and no
reassociation is done at the instantiation; the implementation notes of this file record why
that matters here. -/
theorem eq_eqToHom_comp_comp_eqToHom_of_mono {C : Type*} [Category C] {D : Type*} [Category D]
    (F : C ⥤ D) {A A' O : C} {T T' V : D} {hA : A = A'} {ιA : A ⟶ O} {ιA' : A' ⟶ O}
    (hιA : eqToHom hA ≫ ιA' = ιA) {hT : T' = T} {ιT : T ⟶ V} {ιT' : T' ⟶ V}
    (hιT : eqToHom hT ≫ ιT = ιT') (hmono : Mono ιT) {t : F.obj O ⟶ V}
    {m : F.obj A ⟶ T} {m' : F.obj A' ⟶ T'}
    (hm : m ≫ ιT = F.map ιA ≫ t) (hm' : m' ≫ ιT' = F.map ιA' ≫ t) :
    m = eqToHom (congrArg F.obj hA) ≫ m' ≫ eqToHom hT := by
  have := hmono
  refine (cancel_mono ιT).1 ?_
  rw [hm, Category.assoc, Category.assoc, hιT, hm', ← Category.assoc,
    ← eqToHom_map F hA, ← F.map_comp, hιA]

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The degree-one power of the kernel ideal sheaf of a closed subspace -/

/-- **The degree-one power of the kernel ideal sheaf of the inclusion of a closed subspace is its
defining ideal sheaf.**  This is `AlgebraicGeometry.Space.kernelIdealSheafZPow_one` followed by
`AlgebraicGeometry.Space.kernelIdealSheaf_eq_definingIdealSheaf`. -/
theorem kernelIdealSheafZPow_one_eq_definingIdealSheaf (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) :
    kernelIdealSheafZPow B S hS (subspaceInclusion B S hS X Z) 1 =
      definingIdealSheaf B S hS X Z :=
  (kernelIdealSheafZPow_one B S hS _).trans (kernelIdealSheaf_eq_definingIdealSheaf B S hS X Z)

/-- `AlgebraicGeometry.Space.kernelIdealSheafZPow_one_eq_definingIdealSheaf` read as an equality
of `𝒪_X`-modules, which is the form in which the inverse image and the inclusion into the
structure sheaf consume it. -/
theorem kernelIdealSheafZPow_one_toSheafOfModules_eq (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) :
    (kernelIdealSheafZPow B S hS (subspaceInclusion B S hS X Z) 1).toSheafOfModules =
      (definingIdealSheaf B S hS X Z).toSheafOfModules :=
  congrArg (fun N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule =>
    N.toSheafOfModules) (kernelIdealSheafZPow_one_eq_definingIdealSheaf B S hS X Z)

/-! ### The two maps of ideal sheaves agree in degree one -/

variable {X X' : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
    (Z' : ClosedSubspaces B S hS X'.1) (g : X ⟶ X')
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))

/-- **The degree-one agreement of the map of kernel ideal sheaves of a commutative square with
the map of defining ideal sheaves of [Stacks Project, Tag 04CP].**

For a commutative square of the inclusions of a closed subspace `Z` of `X` and a closed subspace
`Z'` of `X'` over `g` and `f`, the map `g^*((𝓘')¹) ⟶ 𝓘¹` of
`AlgebraicGeometry.Space.kernelIdealSquareMap` in degree one is the map `g^*𝓘' ⟶ 𝓘` of
`AlgebraicGeometry.Space.idealSheafMap`, read across the transports of its source and target
along `AlgebraicGeometry.Space.kernelIdealSheafZPow_one_eq_definingIdealSheaf`.

Both maps are pinned by their composite with the inclusion of the sheaf of ideals into the
structure sheaf, which is a monomorphism; see the module documentation.  The square map is the
only spelling in which the agreement can be stated without a further hypothesis — the
implementation notes record why the ambient factor
`AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap` has no source in common with
`AlgebraicGeometry.Space.idealSheafMap` on its own. -/
theorem kernelIdealSquareMap_one_eq_idealSheafMap
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z') :
    kernelIdealSquareMap B S hS (subspaceInclusion B S hS X Z)
        (subspaceInclusion B S hS X' Z') f g hsq 1 =
      eqToHom (congrArg (modulePullback B S hS g).obj
          (kernelIdealSheafZPow_one_toSheafOfModules_eq B S hS X' Z')) ≫
        idealSheafMap B S hS Z Z' g f hsq ≫
          eqToHom (kernelIdealSheafZPow_one_toSheafOfModules_eq B S hS X Z).symm := by
  have hmono : Mono (kernelIdealSheafZPow B S hS (subspaceInclusion B S hS X Z) 1).ι :=
    inferInstance
  exact CategoryTheory.eq_eqToHom_comp_comp_eqToHom_of_mono (modulePullback B S hS g)
    (Stacks.SheafOfModules.Submodule.eqToHom_comp_ι
      (kernelIdealSheafZPow_one_eq_definingIdealSheaf B S hS X' Z')
      (kernelIdealSheafZPow_one_toSheafOfModules_eq B S hS X' Z'))
    (Stacks.SheafOfModules.Submodule.eqToHom_comp_ι
      (kernelIdealSheafZPow_one_eq_definingIdealSheaf B S hS X Z).symm
      (kernelIdealSheafZPow_one_toSheafOfModules_eq B S hS X Z).symm)
    hmono
    (kernelIdealSquareMap_comp_ι B S hS (subspaceInclusion B S hS X Z)
      (subspaceInclusion B S hS X' Z') f g hsq 1)
    (idealSheafMap_comp_definingIdealSheaf_ι B S hS Z Z' g f hsq)

end AlgebraicGeometry.Space

end
