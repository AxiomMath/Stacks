module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs

/-!
# A sheaf of modules with empty support is zero

The support of a sheaf of modules is the set of points at which its stalk is nonzero, so a
sheaf of modules with empty support has every stalk zero. This file records that such a sheaf
is a zero object of its category of modules.

The statement is made at the generality of `SheafOfModules.supp` and
`SheafOfModules.isClosed_supp` themselves: a sheaf of modules over an arbitrary sheaf of rings
on a topological space. Neither a scheme structure nor a ringed space structure nor
quasi-coherence is used, so the criterion applies verbatim to the modules on an open subspace
of a ringed space, which is where the strictly perfect local models of the perfect-complex
development live.

## Main results

* `SheafOfModules.isZero_of_supp_eq_empty`: a sheaf of modules with empty support is zero.

## Implementation notes

Every stalk being subsingleton makes every module of sections subsingleton, by
`CategoryTheory.Presheaf.IsSheaf.section_ext`: two sections with equal germs at every point of
an open agree after restriction to a neighbourhood of each such point. A morphism out of a
sheaf of modules is determined by its components on each open, so the identity of the sheaf
agrees with the zero morphism, and `CategoryTheory.Limits.IsZero.iff_id_eq_zero` turns that
into the conclusion.

**The sheaf of rings is spelled `CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat`
rather than `TopCat.Sheaf RingCat X`.** The two are the same notion — the latter is a `def`
for the former — but they are not interchangeable in a statement that mentions
`CategoryTheory.Limits.IsZero`: instance search does not unfold the `def`, so with the
`TopCat.Sheaf` spelling the `CategoryTheory.Category` instance on `SheafOfModules R` is not
found and the statement does not even elaborate. Unification does unfold it, so the unfolded
spelling costs nothing at the use sites: a module over a `TopCat.Sheaf RingCat X`, over the
structure sheaf of rings of a ringed space, or over `AlgebraicGeometry.Scheme.ringCatSheaf`,
is accepted with no transport.

The germ comparison is phrased with `TopCat.Presheaf.germ_eq` rather than with a stalk
injectivity statement, because what it returns — a common neighbourhood on which the two
sections already restrict to the same section — is exactly the datum `section_ext` consumes.
The two restriction maps it supplies are forced to be the inclusion by `Subsingleton.elim`,
there being at most one morphism between two opens.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace SheafOfModules

/-- **A sheaf of modules with empty support is a zero object.** Every stalk is subsingleton,
hence so is every module of sections, hence the identity morphism is the zero morphism. -/
theorem isZero_of_supp_eq_empty {X : TopCat.{u}}
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
    (F : SheafOfModules.{u} R) (h : supp F = ∅) : IsZero F := by
  have hst : ∀ x : X,
      Subsingleton (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) := by
    intro x
    refine not_nontrivial_iff_subsingleton.mp fun hnt => ?_
    have hx := (mem_supp_iff_nontrivial_stalk F x).mpr hnt
    rw [h] at hx
    exact hx
  have hsec : ∀ U : Opens X, Subsingleton (ToType (F.val.obj (op U))) := by
    intro U
    refine ⟨fun s t => ?_⟩
    refine TopCat.Presheaf.IsSheaf.section_ext F.isSheaf (U := op U) fun x hx => ?_
    have := hst x
    obtain ⟨W, hxW, iU, iV, he⟩ :=
      TopCat.Presheaf.germ_eq (C := Ab.{u}) F.val.presheaf x hx hx s t (Subsingleton.elim _ _)
    exact ⟨W, leOfHom iU, hxW, by
      rw [Subsingleton.elim (homOfLE (leOfHom iU)) iU, he, Subsingleton.elim iV iU]⟩
  rw [IsZero.iff_id_eq_zero]
  refine hom_ext (PresheafOfModules.hom_ext fun U => ?_)
  exact ConcreteCategory.hom_ext _ _ fun _ => (hsec U.unop).elim _ _

end SheafOfModules

end
