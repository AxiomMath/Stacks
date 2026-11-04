module

public import Mathlib.AlgebraicGeometry.Properties

@[expose] public section

/-!
# Restriction to a dense open subset of a reduced scheme

On a reduced scheme a section of the structure sheaf over an open `W` is determined by its
restriction to any open `V ≤ W` which is dense in `W`: the complement of the basic open set of a
section is where the section vanishes, and on a reduced scheme a section whose basic open set is
empty is zero.

## Main results

* `Stacks.DenseRestriction.eq_zero_of_res_eq_zero`: a section restricting to zero on a dense open
  subset of a reduced scheme is zero.
* `Stacks.DenseRestriction.injective_res`: hence restriction to a dense open subset is injective.

This is the input that makes the ideal of denominators of a section defined on a dense open
subset well behaved: the extension of a product `u * f` from the dense open subset is unique, so
"multiplication by `u`" is a map and not a relation. See
`StacksFrontier.RingTheory.ModuleQuadraticExtension` for the algebra built from it.
-/

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Stacks.DenseRestriction

variable {X : Scheme.{u}} [IsReduced X]

/-- If a section over `W` restricts to zero on `V ≤ W`, then `V` misses its basic open set. -/
private lemma inf_basicOpen_eq_bot_of_res_eq_zero {X : Scheme.{u}} {V W : X.Opens} (h : V ≤ W)
    {s : Γ(X, W)}
    (hs : (X.presheaf.map (homOfLE h).op).hom s = 0) : V ⊓ X.basicOpen s = ⊥ := by
  rw [← Scheme.basicOpen_res X (f := s) (homOfLE h).op, hs, Scheme.basicOpen_zero X]

/-- On a reduced scheme, a section over `W` whose restriction to an open `V ≤ W` that is dense in
`W` vanishes is itself zero. -/
lemma eq_zero_of_res_eq_zero {V W : X.Opens} (h : V ≤ W)
    (hd : (W : Set X) ⊆ closure (V : Set X)) (s : Γ(X, W))
    (hs : (X.presheaf.map (homOfLE h).op).hom s = 0) : s = 0 := by
  rw [← basicOpen_eq_bot_iff s]
  by_contra hne
  have hnonempty : ((X.basicOpen s : X.Opens) : Set X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun hempty => hne (Opens.coe_eq_empty.mp hempty)
  obtain ⟨y, hy⟩ := hnonempty
  have hyW : y ∈ (W : Set X) := X.basicOpen_le s hy
  have h0 := inf_basicOpen_eq_bot_of_res_eq_zero h hs
  obtain ⟨z, hz⟩ := mem_closure_iff.mp (hd hyW) _ (X.basicOpen s).isOpen hy
  have : z ∈ (↑(V ⊓ X.basicOpen s) : Set X) := ⟨hz.2, hz.1⟩
  rw [h0] at this
  exact this

/-- On a reduced scheme, restriction of sections to a dense open subset is injective. -/
lemma injective_res {V W : X.Opens} (h : V ≤ W)
    (hd : (W : Set X) ⊆ closure (V : Set X)) :
    Function.Injective (X.presheaf.map (homOfLE h).op).hom := by
  intro s t hst
  refine sub_eq_zero.mp (eq_zero_of_res_eq_zero h hd (s - t) ?_)
  rw [map_sub, hst, sub_self]

/-- **On a reduced scheme, a section over `W` vanishing on an open subset `V` that contains the
basic open set of `r : Γ(X, W)` is killed by `r`.** The basic open set of `r * s` is contained
in the intersection of `V` with the basic open set of `s`, which is the basic open set of the
restriction of `s` to `V`, hence empty.

This is the one input beyond `Stacks.DenseRestriction.injective_res` that makes the ideal of
denominators of a section defined on a dense open subset *quasi-coherent*: it turns a relation
holding only on a basic open subset of an affine open into one holding on the whole of it, at
the cost of one factor of `r`. -/
lemma mul_eq_zero_of_res_eq_zero_of_basicOpen_le {V W : X.Opens} (h : V ≤ W) (r s : Γ(X, W))
    (hr : X.basicOpen r ≤ V)
    (hs : (X.presheaf.map (homOfLE h).op).hom s = 0) : r * s = 0 := by
  rw [← basicOpen_eq_bot_iff (r * s), Scheme.basicOpen_mul]
  exact le_bot_iff.mp
    ((inf_basicOpen_eq_bot_of_res_eq_zero h hs).le.trans' (inf_le_inf_right (X.basicOpen s) hr))

end Stacks.DenseRestriction

end
