module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule

/-!
# Submodules survive restriction of scalars unchanged

Let `α : R ⟶ R'` be a morphism of sheaves of rings on a site and let `M` be a sheaf of
`R'`-modules. Restriction of scalars along `α` does not change the underlying sheaf of abelian
groups of `M`: `SheafOfModules.restrictScalars` keeps the sections, the restriction maps and even
the `isSheaf` field of `M`, and only narrows the ring acting on each `M(X)`. Consequently a
submodule of `M` **is** a submodule of its restriction of scalars, on the same family of subsets:
a subset closed under the `R'`-action is closed under the `R`-action, because the `R`-action is the
`R'`-action precomposed with `α`.

This file records that transport. It is wanted whenever a family of submodules has been produced
over one sheaf of rings and a construction consumes it over another — for instance when a
subcomplex has to be cut out of a complex of sheaves of `f^{-1}𝒪_S`-modules by submodules that
were constructed as `𝒪_X`-submodules.

## Main definitions

* `SheafOfModules.Submodule.restrictScalars`: **a submodule of `M`, read as a submodule of the
  restriction of scalars of `M`.**

## Main results

* `SheafOfModules.Submodule.mem_restrictScalars_obj`: membership is unchanged, by definition.
* `SheafOfModules.Submodule.restrictScalars_monotone`: the transport is monotone, so a chain of
  containments between submodules is preserved.

## Implementation notes

All three fields are the fields of the original submodule. `PresheafOfModules.restrictScalarsObj`
is defined with `obj X := (ModuleCat.restrictScalars (α.app X).hom).obj (M.obj X)`, whose carrier
is the carrier of `M.obj X`, and with the *same* underlying function for each restriction map; and
`SheafOfModules.restrictScalars` sets `isSheaf := M.isSheaf`. So `map` and `isSheaf` are literally
the original proofs, and only `smul_mem'` has anything to say — that the `R`-action lands back in
the subset, which is the `R'`-action of `α` applied to the scalar.

The statement is made over a bare site with the two sheaves of rings as *variables*, not at any
particular ringed space. That is deliberate: instantiating an already-elaborated statement raises
no instance goal, whereas a version stated at a concrete sheaf of rings forces the elaborator to
unify spellings of that sheaf — the failure mode recorded in the implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness`.

## References

* [Stacks Project, Tag 01AC](https://stacks.math.columbia.edu/tag/01AC)
-/

@[expose] public noncomputable section

universe v v₁ u₁ u

open CategoryTheory Opposite

namespace SheafOfModules.Submodule

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R R' : Sheaf J RingCat.{u}} (α : R ⟶ R') {M : SheafOfModules.{v} R'} (N : M.Submodule)

/-- **A submodule of a sheaf of `R'`-modules is a submodule of its restriction of scalars along
`α : R ⟶ R'`**, on the same family of subsets: the `R`-action on each section module is the
`R'`-action precomposed with `α`, so the subsets are closed under it, and the restriction maps and
the sheaf condition are untouched by restriction of scalars. -/
def restrictScalars : ((SheafOfModules.restrictScalars α).obj M).Submodule where
  obj X :=
    { carrier := (N.obj X : Set (M.val.obj X))
      zero_mem' := (N.obj X).zero_mem
      add_mem' := fun hx hy => (N.obj X).add_mem hx hy
      smul_mem' := fun r _ hx => (N.obj X).smul_mem ((α.hom.app X).hom r) hx }
  map f := N.map f
  isSheaf := N.isSheaf

/-- **Membership in the transported submodule is membership in the original one.** -/
theorem mem_restrictScalars_obj (X : Cᵒᵖ) (x : M.val.obj X) :
    x ∈ (restrictScalars α N).obj X ↔ x ∈ N.obj X :=
  Iff.rfl

/-- **The transport preserves containment**, so a bound proved between submodules over `R'` is a
bound between their restrictions of scalars. -/
theorem restrictScalars_monotone {N₁ N₂ : M.Submodule} (h : N₁ ≤ N₂) :
    restrictScalars α N₁ ≤ restrictScalars α N₂ := by
  intro X x hx
  exact h X hx

end SheafOfModules.Submodule

end
