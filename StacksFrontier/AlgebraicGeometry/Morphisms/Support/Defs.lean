module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Topology.Sheaves.Stalks
public import StacksCore.Tactic.StacksAttribute

/-!
# The support of a sheaf of modules

The support of a sheaf of modules on a topological space is the set of points at which its
stalk is nonzero.

## Main definitions

* `SheafOfModules.supp` is the support of a sheaf of modules on a topological space.

## Main results

* `SheafOfModules.mem_supp_iff_nontrivial_stalk` characterizes membership in the support by
  nonvanishing of the stalk.
* `SheafOfModules.supp_eq_of_iso` says that isomorphic modules on a scheme have the same
  support.

## Implementation notes

The support is read off the underlying sheaf of abelian groups, so neither quasi-coherence nor
a scheme structure is used; it is defined for an arbitrary sheaf of rings on a topological
space. Its invariance under isomorphism is stated for modules on a scheme, which is the form
every consumer in this repository uses.

## References

* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace SheafOfModules

/-- The support of a sheaf of modules is the set of points where its stalk has a nonzero
element. -/
noncomputable def supp {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}
    (F : SheafOfModules.{u} R) : Set X :=
  {x | ∃ a : (show TopCat.Presheaf Ab.{u} X from F.val.presheaf).stalk x, a ≠ 0}

/-- A point is in the support of a sheaf of modules if and only if its stalk is nonzero. -/
@[stacks 056J "support_by_stalk"]
lemma mem_supp_iff_nontrivial_stalk {X : TopCat.{u}}
    {R : TopCat.Sheaf RingCat.{u} X} (F : SheafOfModules.{u} R) (x : X) :
    x ∈ supp F ↔
      Nontrivial ((show TopCat.Presheaf Ab.{u} X from F.val.presheaf).stalk x) :=
  (nontrivial_iff_exists_ne (0 : _)).symm

/-- Isomorphic modules on a scheme have the same support: an isomorphism of modules induces an
isomorphism of stalks, so one stalk is trivial exactly when the other is. -/
public lemma supp_eq_of_iso {X : AlgebraicGeometry.Scheme.{u}} {M N : X.Modules} (e : M ≅ N) :
    supp M = supp N := by
  ext x
  refine ((mem_supp_iff_nontrivial_stalk M x).trans ?_).trans
    (mem_supp_iff_nontrivial_stalk N x).symm
  exact Equiv.nontrivial_congr ((AlgebraicGeometry.Scheme.Modules.toPresheaf X ⋙
    TopCat.Presheaf.stalkFunctor Ab.{u} x).mapIso e).addCommGroupIsoToAddEquiv.toEquiv

end SheafOfModules
