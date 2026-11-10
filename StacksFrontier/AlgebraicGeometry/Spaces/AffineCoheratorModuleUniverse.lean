module

public import StacksFrontier.Algebra.Category.ModuleCat.NoUniverseEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineCoheratorGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineRepresentedQuasicoherent

/-!
# The associated-module equivalence carried by Stacks 08H0 cannot be had at module universe `u`

`StacksFrontier/AlgebraicGeometry/Spaces/AffineCoheratorGlobalSections.lean` states **Stacks 08H0**
(1) for an affine algebraic space `X` with two carried binders, the first of which is an
associated-module equivalence

`assoc : Mod(A) ≌ QCoh(𝒪_X)`,  `A = Γ(X, 𝒪_X)`,

with the modules on the left read at `ModuleCat.{max (u + 1) m}` of
`AlgebraicGeometry.Space.globalSectionRingSmallEtale` — a `Subring` of a product indexed by the
objects of the small étale site, so a ring in `Type (u + 1)` — and `QCoh(𝒪_X)` read at module
universe `m`.  That file's module documentation records the binder as *open*: the affine case of
Descent, Proposition **03DX** (2) is available at module universe `u`, as
`AlgebraicGeometry.Space.affineRepresentedQuasicoherentModulesEquivalence`, and what the binder
asks for at `m := u` is the same identification one universe up, which the development does not
have.

This file settles what that gap is.  It is not a missing theorem:  **at `m := u` the binder is
unsatisfiable**, for a representable affine algebraic space whose ring of global functions is
nontrivial.  So no module-universe-polymorphic form of **Stacks 03DX** (2) is to be looked for,
and both statements of that file are vacuous at `m := u`.

The reason is `ModuleCat.not_nonempty_equivalence_of_category_succ`:  the module category of a
ring in `Type (u + 1)`, taken at module universe `u + 1`, is not equivalent to any category whose
Hom-sets lie in `Type u`, and `ModuleCat.{u} Γ(T, ⊤)` is such a category.  Composing a witness of
the binder with the affine identification produces exactly that.

## Main results

* `AlgebraicGeometry.Space.not_nonempty_equivalence_moduleCat_quasicoherentSheaves_yoneda`:
  **the carried associated-module equivalence does not exist at module universe `u`.**

## Implementation notes

*What this does not say.*  It says nothing against **Stacks 08H0** (1) as mathematics, and nothing
against the two statements of `AffineCoheratorGlobalSections.lean` at the module universes where
their binder is satisfiable — `m := u + 1` and above, where the two sides of the binder are at one
and the same module universe.  What it rules out is the one instantiation a consumer at the
seating of `AlgebraicGeometry.Space.Modules.{u, u}` would want, which is `m := u`.

*Why this matters for Stacks 073K, part (1).*  The `assoc` binder is not what stands
between the affine case of part (2) — a statement about modules — and the sheaf statement part
(1)'s reduction consumes
(in `StacksFrontier/AlgebraicGeometry/Spaces/CohomologyFlatBaseChange.lean`).
The crossing part (1) needs is at module universe `u`, where
`AlgebraicGeometry.Space.QuasicoherentSheaves.{u, u}` is a full subcategory of the very
`AlgebraicGeometry.Space.Modules.{u, u}` that
`AlgebraicGeometry.Space.toposModuleDerivedBaseChangeMap` is seated on, and there the affine
identification is available and unconditional; while the `assoc` binder, at that same `m := u`, is
not a thing that could be proved at all.  What part (1) actually needs on that side is the
identification of the *global sections* functor with the inverse of
`affineRepresentedQuasicoherentModulesEquivalence`, and of the comparison map that identification
carries with `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeMap` — neither
of which is a universe question.

*Nontriviality.*  It is a hypothesis and it is necessary:  over the zero ring every module is
zero, so all the module categories of the zero ring are equivalent to one another at every
universe, and the binder is then satisfiable whenever `QCoh(𝒪_X)` is equivalent to the
one-object category as well.

## References

* [Stacks Project, Tag 08H0](https://stacks.math.columbia.edu/tag/08H0)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The associated-module equivalence carried by Stacks 08H0 does not exist at module universe
`u`.**  Let `U` be an object of the big fppf site over `S` whose underlying scheme is affine and
whose ring of global functions, read as compatible sections on the small étale site of the
algebraic space `yoneda.obj U`, is nontrivial.  Then there is no equivalence between
`ModuleCat.{u + 1}` of that ring and the quasi-coherent `𝒪`-modules on the small étale site at
module universe `u`.

This is the `assoc` binder of
`AlgebraicGeometry.Space.inclusionAdjunctionGlobalSectionsAssociated` and of
`AlgebraicGeometry.Space.coheratorIsoAssociatedGlobalSections` at `m := u`, so both of those are
vacuous there.

A witness would compose with the affine identification
`AlgebraicGeometry.Space.affineRepresentedQuasicoherentModulesEquivalence` to give an equivalence
of `ModuleCat.{u + 1}` of a ring in `Type (u + 1)` with `ModuleCat.{u}` of a ring in `Type u`, and
`ModuleCat.not_nonempty_equivalence_of_category_succ` says there is none. -/
theorem not_nonempty_equivalence_moduleCat_quasicoherentSheaves_yoneda
    (U : BigFppfOver B S hS) (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    [Nontrivial (globalSectionRingSmallEtale B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U))] :
    ¬ Nonempty (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U)) ≌
      QuasicoherentSheaves.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)) := by
  rintro ⟨E⟩
  exact ModuleCat.not_nonempty_equivalence_of_category_succ
    ⟨E.trans (affineRepresentedQuasicoherentModulesEquivalence B S hS U hU).symm⟩

end AlgebraicGeometry.Space

end
