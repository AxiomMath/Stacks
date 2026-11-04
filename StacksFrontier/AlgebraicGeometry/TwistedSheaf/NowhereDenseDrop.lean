module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.Dimension
public import StacksFrontier.Topology.Dimension.NowhereDense

/-!
# The support-dimension drop from nowhere density

[Stacks, Tag 0BEM] descends on `AlgebraicGeometry.natDimSupp`, the dimension of the support of
a coherent sheaf read as a natural number, and the two short exact sequences its inductive step
asks for must have third terms of strictly smaller support dimension. What the geometry of
[Stacks, Tag 02P2] produces is weaker-looking: the third terms are supported on a subset of
`Supp ℱ` that is closed and *nowhere dense* in `Supp ℱ`.

This file converts the one into the other. All of the content is the purely topological
`IsNowhereDense.toNat_unbotD_topologicalKrullDim_lt`; what is added here is that the support of
a sheaf of modules is closed (`SheafOfModules.isClosed_supp`) and that the support of a sheaf on
a scheme proper over a field is finite-dimensional
(`AlgebraicGeometry.topologicalKrullDim_supp_ne_top`), so that neither of the topological
lemma's two side conditions has to be carried by a supplier.

## Main results

* `AlgebraicGeometry.natDimSupp_lt_natDimSupp_of_isNowhereDense`: a sheaf whose support is
  nowhere dense in the support of `𝒢` has strictly smaller `natDimSupp` than `𝒢`, provided
  `natDimSupp 𝒢 ≠ 0` — which is exactly the hypothesis the inductive step of Tag 0BEM has in
  hand.
* `AlgebraicGeometry.natDimSupp_lt_natDimSupp_of_forall_irreducibleComponents`: the same, with
  the relative nowhere-density hypothesis replaced by the condition in which it is checkable,
  namely that no irreducible component of `Supp 𝒢` lies inside `Supp ℱ`.
* `AlgebraicGeometry.natDimSupp_lt_natDimSupp_of_isNowhereDense_of_supp_eq_univ`: the same
  again for a sheaf `𝒢` of **full support**, where the hypothesis needed is nowhere density in
  the whole scheme. This is the form the geometry of [Stacks, Tag 02P2] supplies, that tag
  being stated only for a sheaf of full support.

## Implementation notes

**Why there are three forms and not one.** The nowhere-density hypothesis of the first statement
is relative to `Supp 𝒢`, and the nowhere density that [Stacks, Tag 02P2] produces is relative to
the scheme. Absolute nowhere density does not imply the relative one — `Supp 𝒢` is itself
typically nowhere dense in the scheme, and then `Supp ℱ = Supp 𝒢` satisfies the absolute
hypothesis with no drop at all — so the two cannot be bridged in general. They *do* agree when
`Supp 𝒢` is everything, which is Tag 02P2's own hypothesis on the sheaf it acts on, and that is
the content of the third statement; the second records what a supplier would have to check
instead for a `𝒢` of smaller support.
-/

@[expose] public section

open CategoryTheory Topology TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A coherent sheaf supported on a nowhere dense closed part of `Supp 𝒢` has strictly
smaller support dimension.** This is the shape in which the inductive step of
[Stacks, Tag 0BEM] needs its two support-dimension drops: the hypothesis `hG0` is the step's
own `natDimSupp 𝒢 ≠ 0`, and `hnd` is the nowhere-density the geometry of [Stacks, Tag 02P2]
produces.

Nowhere density is asked for *inside* `Supp 𝒢`, which is the only form in which it can carry
information: a subset nowhere dense in the whole of `X` need not be nowhere dense in a
positive-dimensional closed subset, and conversely `Supp 𝒢` itself is typically nowhere dense
in `X`. -/
theorem natDimSupp_lt_natDimSupp_of_isNowhereDense (k : Type u) [Field k] {X : Scheme.{u}}
    [NoetherianSpace X] (f : X ⟶ Spec (.of k)) [IsProper f] (G F : X.Modules)
    (hF : SheafOfModules.IsCoherent F)
    (hsub : SheafOfModules.supp F ⊆ SheafOfModules.supp G)
    (hnd : IsNowhereDense
      ((Subtype.val : SheafOfModules.supp G → X) ⁻¹' SheafOfModules.supp F))
    (hG0 : natDimSupp G ≠ 0) :
    natDimSupp F < natDimSupp G :=
  have := hF.isFiniteType
  toNat_unbotD_topologicalKrullDim_lt_of_isNowhereDense_subspace hsub
    (_root_.SheafOfModules.isClosed_supp F) hnd (topologicalKrullDim_supp_ne_top k f G) hG0

/-- **The support-dimension drop from the irreducible components of `Supp 𝒢`.** This is
`AlgebraicGeometry.natDimSupp_lt_natDimSupp_of_isNowhereDense` with its relative
nowhere-density hypothesis replaced, via
`isNowhereDense_preimage_val_iff_forall_irreducibleComponents`, by the condition a supplier can
actually check: no irreducible component of `Supp 𝒢` lies inside `Supp ℱ`. For a Noetherian
space the two are equivalent for a closed `Supp ℱ`, and this is the form in which a
generic-point argument discharges the hypothesis. -/
theorem natDimSupp_lt_natDimSupp_of_forall_irreducibleComponents (k : Type u) [Field k]
    {X : Scheme.{u}} [NoetherianSpace X] (f : X ⟶ Spec (.of k)) [IsProper f] (G F : X.Modules)
    (hF : SheafOfModules.IsCoherent F)
    (hsub : SheafOfModules.supp F ⊆ SheafOfModules.supp G)
    (hcomp : ∀ Z ∈ irreducibleComponents (SheafOfModules.supp G),
      ¬ (Subtype.val '' Z ⊆ SheafOfModules.supp F))
    (hG0 : natDimSupp G ≠ 0) :
    natDimSupp F < natDimSupp G :=
  have := hF.isFiniteType
  natDimSupp_lt_natDimSupp_of_isNowhereDense k f G F hF hsub
    ((isNowhereDense_preimage_val_iff_forall_irreducibleComponents
      (_root_.SheafOfModules.isClosed_supp F)).2 hcomp) hG0

/-- **The support-dimension drop for a sheaf of full support, from nowhere density in the
scheme.** When `Supp 𝒢` is everything, `natDimSupp 𝒢` is the dimension of the scheme and the
relative nowhere density of `AlgebraicGeometry.natDimSupp_lt_natDimSupp_of_isNowhereDense` is
nowhere density in the scheme; no conversion is needed, and the strict drop is
`IsNowhereDense.toNat_unbotD_topologicalKrullDim_lt` applied directly.

This is the form in which the geometry of [Stacks, Tag 02P2] feeds the inductive step of
[Stacks, Tag 0BEM]: that tag produces a closed subset nowhere dense **in the scheme**, and it is
stated only for a coherent sheaf of full support.

The Noetherian and locally Noetherian hypotheses are not asked of the caller: a scheme proper
over a field is locally of finite type over a Noetherian base and quasi-compact, hence
Noetherian. -/
theorem natDimSupp_lt_natDimSupp_of_isNowhereDense_of_supp_eq_univ (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (G F : X.Modules)
    (hF : SheafOfModules.IsCoherent F)
    (hG : SheafOfModules.supp G = Set.univ)
    (hnd : IsNowhereDense (SheafOfModules.supp F))
    (hG0 : natDimSupp G ≠ 0) :
    natDimSupp F < natDimSupp G := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := IsNoetherian.mk
  have := hF.isFiniteType
  have hdimG : natDimSupp G = ((topologicalKrullDim X).unbotD 0).toNat := by
    unfold natDimSupp
    rw [hG, topologicalKrullDim_univ]
  rw [hdimG] at hG0 ⊢
  exact hnd.toNat_unbotD_topologicalKrullDim_lt (_root_.SheafOfModules.isClosed_supp F)
    (topologicalKrullDim_ne_top_of_isProper k f) hG0

end AlgebraicGeometry
