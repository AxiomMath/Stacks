module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Specializations
public import StacksFrontier.Topology.Sober.Defs

/-!
# The point space of a decent algebraic space is Kolmogorov

Let `X` be an algebraic space over a scheme `S` every point of which has finite fibres in
every étale chart of `X` by an affine scheme — condition `(α)` of Stacks 03JX, which is in
particular what Stacks 03I8's definition of a *decent* algebraic space gives. Two points of
`X` which are topologically indistinguishable in the point topology of Stacks 03BX are then
equal: the space `|X|` is Kolmogorov. This is **Stacks 03K3**.

## Main results

* `AlgebraicGeometry.Space.t0Space_points_of_hasFiniteChartFibers`: **Stacks 03K3**.

## Implementation notes

Two indistinguishable points specialize to one another, so each of the two specializations
lifts to a surjective étale scheme atlas of `X` by Stacks 03K2. Composing the two lifts gives
two points of the atlas above the *same* point of `X`, one a specialization of the other,
which Stacks 03K5 identifies. That collapses the lifted chain to a pair of indistinguishable
points of the atlas, and these are equal because the points of a represented presheaf are the
points of the representing scheme, a Kolmogorov space.

Decency is spelled here as `AlgebraicGeometry.Space.HasFiniteChartFibersAtEveryPoint`,
condition `(α)` of Stacks 03JX, which is what the argument uses; see the implementation notes
of `StacksFrontier/AlgebraicGeometry/Spaces/Decent/Specializations.lean` for the relation
between that predicate, condition `(γ)` and `AlgebraicGeometry.Space.IsDecentSpace`.

The Kolmogorov property is Mathlib's `T0Space`, which is the first half of
`StacksSober` — soberness in the sense of Stacks 004X — through
`stacksSober_iff_t0_and_quasiSober`.

## References

* [Stacks Project, Tag 03K3](https://stacks.math.columbia.edu/tag/03K3)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03K3.** The point space of an algebraic space over `S` all of whose points have
finite fibres in every étale chart by an affine scheme — in particular, of a decent algebraic
space — is Kolmogorov. -/
@[stacks 03K3]
theorem t0Space_points_of_hasFiniteChartFibers
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdecent : HasFiniteChartFibersAtEveryPoint B S hS X) :
    T0Space (points B S hS X) := by
  refine ⟨fun x y hxy ↦ ?_⟩
  obtain ⟨U, φ, hsurj, hφ⟩ := hX.exists_atlas
  obtain ⟨p, hp⟩ := (presheafSurjective_iff_isSurjective_yoneda B S hS X hX U φ).1 hsurj y
  -- Lift the specialization `x ⤳ y` to the atlas, from the chosen point above `y`.
  obtain ⟨p₁, hp₁p, hφp₁⟩ := exists_specializes_pointsMap_eq_of_isEtale B S hS hX
    hxy.specializes (hdecent x) U φ hφ p hp
  -- Lift the specialization `y ⤳ x` back, from the point just produced.
  obtain ⟨p₂, hp₂p₁, hφp₂⟩ := exists_specializes_pointsMap_eq_of_isEtale B S hS hX
    hxy.specializes' (hdecent y) U φ hφ p₁ hφp₁
  -- `p` and `p₂` lie above the same point of `X` and specialize, so Stacks 03K5 identifies
  -- them; the lifted chain therefore collapses.
  have hpp₂ : p = p₂ :=
    eq_of_specializes_of_pointsMap_eq_of_hasFiniteChartFibers B S hS hX hdecent U φ hφ p p₂
      (hp.trans hφp₂.symm) (hp₂p₁.trans hp₁p)
  have hinsep : Inseparable p₁ p := hp₁p.antisymm (hpp₂ ▸ hp₂p₁)
  have hpoints : p₁ = p :=
    (schemePointsHomeomorph B S hS U).injective
      (hinsep.map (schemePointsHomeomorph B S hS U).continuous).eq
  rw [← hφp₁, hpoints, hp]

end AlgebraicGeometry.Space

end
