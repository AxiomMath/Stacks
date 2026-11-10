module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksCore.Tactic.StacksAttribute

/-!
# Global functions vanishing at a point, and the closedness of that condition

Let `X` be a scheme and let `x` be a point of it.  Pulling a global function `f` back along the
canonical map `\Spec κ(x) ⟶ X` of `AlgebraicGeometry.Scheme.fromSpecResidueField` gives zero
exactly when `x` lies outside the basic open `X.basicOpen f`; so the set of points at which `f`
pulls back to zero is closed, and the ideal of functions vanishing at a point of the closure of a
subset contains every function vanishing on that subset.

## Main results

* `AlgebraicGeometry.Scheme.appTop_fromSpecResidueField_eq_zero_iff`: the pullback of a global
  function along `\Spec κ(x) ⟶ X` vanishes exactly when `x ∉ X.basicOpen f`.
* `AlgebraicGeometry.Scheme.isClosed_setOf_appTop_fromSpecResidueField_eq_zero`: that condition
  cuts out a closed subset of `X`.
* `AlgebraicGeometry.Scheme.appTop_fromSpecResidueField_eq_zero_of_mem_closure`: a global function
  vanishing at every point of a subset vanishes at every point of its closure.

## Implementation notes

The pullback `\Gamma(X, ⊤) ⟶ \Gamma(\Spec κ(x), ⊤)` is used rather than the evaluation map
`AlgebraicGeometry.Scheme.Γevaluation` to the residue field itself, because it is the pullback
along a morphism of the big fppf site that the geometric consumers meet: the ideal they form is
the kernel of the map on global functions of the structure morphism of `\Spec κ(x)` over the base.
No comparison of the two is needed: `\Spec κ(x)` is the spectrum of a field, hence reduced, so a
global function on it vanishes exactly when its basic open is empty, and that basic open is the
preimage of `X.basicOpen f`, whose emptiness is the statement that the image point `x` of
`\Spec κ(x)` misses `X.basicOpen f`.

No tag is claimed; this is elementary scheme theory, used as the topological input of the proof of
Stacks 0CWB.

## References

* [Stacks Project, Tag 0CWB](https://stacks.math.columbia.edu/tag/0CWB)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- **A global function pulls back to zero on `\Spec κ(x)` exactly when `x` lies outside its basic
open.**

`\Spec κ(x)` is reduced, so a global function on it vanishes exactly when its basic open is empty;
that basic open is the preimage of `X.basicOpen f`, and the image of `\Spec κ(x)` is the single
point `x`. -/
theorem appTop_fromSpecResidueField_eq_zero_iff (x : X) (f : Γ(X, ⊤)) :
    (X.fromSpecResidueField x).appTop.hom f = 0 ↔ x ∉ X.basicOpen f := by
  rw [← basicOpen_eq_bot_iff ((X.fromSpecResidueField x).appTop.hom f),
    show (Spec (X.residueField x)).basicOpen ((X.fromSpecResidueField x).appTop.hom f) =
      (X.fromSpecResidueField x) ⁻¹ᵁ X.basicOpen f from
      (preimage_basicOpen_top (X.fromSpecResidueField x) f).symm]
  constructor
  · intro h hx
    obtain ⟨p, hp⟩ : x ∈ Set.range (X.fromSpecResidueField x) := by
      rw [range_fromSpecResidueField]
      exact rfl
    have hp' : p ∈ (X.fromSpecResidueField x) ⁻¹ᵁ X.basicOpen f := by
      change (X.fromSpecResidueField x) p ∈ X.basicOpen f
      rw [hp]
      exact hx
    rw [h] at hp'
    exact hp'
  · intro hx
    refine Opens.ext (Set.eq_empty_iff_forall_notMem.2 fun p hp => hx ?_)
    have : (X.fromSpecResidueField x) p ∈ X.basicOpen f := hp
    rwa [fromSpecResidueField_apply] at this

/-- **The points at which a global function vanishes form a closed subset.**  It is the complement
of `X.basicOpen f`. -/
theorem isClosed_setOf_appTop_fromSpecResidueField_eq_zero (f : Γ(X, ⊤)) :
    IsClosed {x : X | (X.fromSpecResidueField x).appTop.hom f = 0} := by
  have h : {x : X | (X.fromSpecResidueField x).appTop.hom f = 0} =
      ((X.basicOpen f : Set X))ᶜ :=
    Set.ext fun x => appTop_fromSpecResidueField_eq_zero_iff X x f
  rw [h]
  exact (X.basicOpen f).isOpen.isClosed_compl

/-- **A global function vanishing at every point of a subset vanishes at every point of its
closure.** -/
theorem appTop_fromSpecResidueField_eq_zero_of_mem_closure (f : Γ(X, ⊤)) (T : Set X) {s : X}
    (hs : s ∈ closure T) (hT : ∀ t ∈ T, (X.fromSpecResidueField t).appTop.hom f = 0) :
    (X.fromSpecResidueField s).appTop.hom f = 0 :=
  closure_minimal (fun t ht => hT t ht)
    (isClosed_setOf_appTop_fromSpecResidueField_eq_zero X f) hs

end AlgebraicGeometry.Scheme

end
