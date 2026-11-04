module

public import StacksFrontier.AlgebraicGeometry.AffineClosedUnion.TwistedRestrict

/-!
# A set-theoretic cover of a reduced scheme makes two ideal sheaves meet in zero

The twisted square of
`StacksDraft.AlgebraicGeometry.F3b.AffineClosedUnion.TwistedSections` and its canonical-leg
refinements in the two sibling files all stand on one hypothesis, `I₁ ⊓ I₂ = ⊥`: the two closed
subschemes meet in the empty subscheme in the sense of ideal sheaves, not merely of points.  This
file discharges that hypothesis from the data a geometric situation actually supplies — the
underlying closed sets cover, and the ambient scheme is reduced — and restates the vanishing form
of the square with the hypothesis gone.

That is the shape in which the proof of [Stacks, Tag 09NX] uses it.  There `X` is reduced, `Z₁` is
one irreducible component and `Z` is the reduced closed subscheme on the union of the others, so
the two closed sets cover `X` by `TopologicalSpace.sUnion_irreducibleComponents` and nothing else
is known about the ideal sheaves.

## Why reducedness is the whole of it

`AlgebraicGeometry.Scheme.IdealSheafData.support` is antitone, so the support of `I ⊓ J` contains
both supports and therefore everything; and on a reduced scheme an ideal sheaf with full support
is `⊥` (`AlgebraicGeometry.Scheme.IdealSheafData.support_eq_top_iff`).  No radicality of either
ideal sheaf is needed, and neither is quasi-compactness, Noetherianness or finiteness of the
family: the `n`-ary statement is proved for an arbitrary index type.

At the level of rings this is the first step of [Stacks, Tag 09NW] — `I ∩ J` is zero because `A`
is reduced and `Spec(A) = V(I) ∪ V(J) = V(I ∩ J)` — which is proved as
`Stacks.Variety.DimensionOne.inf_eq_bot_of_zeroLocus_union_eq_univ`.  The statements here are its
scheme-level analogue, through `support` and `vanishingIdeal` rather than through zero loci.

## Main results

* `Stacks.AffineClosedUnion.inf_eq_bot_of_sup_support_eq_top`: two ideal sheaves on a reduced
  scheme whose supports cover it meet in `⊥`, and
  `Stacks.AffineClosedUnion.iInf_eq_bot_of_iSup_support_eq_top` for a family.
* `Stacks.AffineClosedUnion.vanishingIdeal_inf_eq_bot_of_sup_eq_top` and
  `Stacks.AffineClosedUnion.vanishingIdeal_iInf_eq_bot_of_iSup_eq_top`: the same for the reduced
  closed subschemes cut out by a cover by closed sets.
* `Stacks.AffineClosedUnion.existsUnique_unit_app_eq_zero_of_sup_support_eq_top` and
  `Stacks.AffineClosedUnion.existsUnique_unit_app_eq_zero_of_closeds_sup_eq_top`: **the vanishing
  form of the twisted square with its standing hypothesis discharged** — a section of `L` on the
  second closed subscheme whose canonical restriction to the scheme-theoretic intersection
  vanishes extends uniquely to a section on the ambient scheme vanishing on the first, given only
  that the ambient scheme is reduced and the two closed sets cover.

## Implementation notes

`Stacks.AffineClosedUnion.support_vanishingIdeal` is the `TopologicalSpace.Closeds`-level form of
Mathlib's `AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal`, which is stated
for the underlying sets.  Mathlib carries the converse composite
(`vanishingIdeal_support : vanishingIdeal I.support = I.radical`) but not this one.

No `@[stacks]` attribute is attached.  [Stacks, Tag 09NW] is a remark, and the ring-level content
it states is already carried, in all three of its parts, by the tagged declarations of
`StacksFrontier.AlgebraicGeometry.Variety.DimensionOne.Conductor`; a scheme-level restatement of its
first step is not the remark.  [Stacks, Tag 09NX] is the ampleness criterion, which is not proved
here.

## References

* [Stacks Project, Tag 09NW](https://stacks.math.columbia.edu/tag/09NW)
* [Stacks Project, Tag 09NX](https://stacks.math.columbia.edu/tag/09NX)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.IdealSheafData
open Stacks.RingedSpace

universe u

namespace Stacks.AffineClosedUnion

variable {X : Scheme.{u}}

/-! ### Ideal sheaves whose supports cover -/

/-- An ideal sheaf on a reduced scheme whose support is everything is `⊥`. -/
private theorem eq_bot_of_top_le_support [IsReduced X] {I : X.IdealSheafData}
    (h : ⊤ ≤ I.support) : I = ⊥ :=
  Scheme.IdealSheafData.support_eq_top_iff.mp (top_le_iff.mp h)

/-- **Two ideal sheaves on a reduced scheme whose supports cover it meet in `⊥`.**  The support of
`I ⊓ J` contains both supports because `AlgebraicGeometry.Scheme.IdealSheafData.support` is
antitone, hence is everything; and on a reduced scheme full support forces `⊥`.

This is the scheme-level form of the first step of [Stacks, Tag 09NW]. -/
theorem inf_eq_bot_of_sup_support_eq_top [IsReduced X] {I J : X.IdealSheafData}
    (h : I.support ⊔ J.support = ⊤) : I ⊓ J = ⊥ := by
  exact eq_bot_of_top_le_support (h.symm.le.trans
    (sup_le (support_antitone inf_le_left) (support_antitone inf_le_right)))

/-- **A family of ideal sheaves on a reduced scheme whose supports cover it has infimum `⊥`.**
The index type is arbitrary: no finiteness is used, since the cover hypothesis already carries
whatever is needed. -/
theorem iInf_eq_bot_of_iSup_support_eq_top [IsReduced X] {ι : Type*}
    (I : ι → X.IdealSheafData) (h : (⨆ i, (I i).support) = ⊤) : (⨅ i, I i) = ⊥ := by
  exact eq_bot_of_top_le_support
    (h.symm.le.trans (iSup_le fun i => support_antitone (iInf_le I i)))

/-! ### Reduced closed subschemes cut out by a cover by closed sets -/

/-- The support of the vanishing ideal sheaf of a closed set is that closed set.  Mathlib states
this for the underlying sets (`coe_support_vanishingIdeal`); this is the
`TopologicalSpace.Closeds` form. -/
theorem support_vanishingIdeal (A : Closeds X) : (vanishingIdeal A).support = A :=
  TopologicalSpace.Closeds.ext (coe_support_vanishingIdeal A)

/-- **The reduced closed subschemes on two closed sets covering a reduced scheme meet in the empty
subscheme.** -/
theorem vanishingIdeal_inf_eq_bot_of_sup_eq_top [IsReduced X] (A B : Closeds X)
    (h : A ⊔ B = ⊤) : vanishingIdeal A ⊓ vanishingIdeal B = ⊥ := by
  rw [← vanishingIdeal_sup, h, vanishingIdeal_top, AlgebraicGeometry.Scheme.nilradical_eq_bot]

/-- **The reduced closed subschemes on a family of closed sets covering a reduced scheme have
infimum the empty subscheme.** -/
theorem vanishingIdeal_iInf_eq_bot_of_iSup_eq_top [IsReduced X] {ι : Type*} (A : ι → Closeds X)
    (h : (⨆ i, A i) = ⊤) : (⨅ i, vanishingIdeal (A i)) = ⊥ := by
  rw [← vanishingIdeal_iSup, h, vanishingIdeal_top, AlgebraicGeometry.Scheme.nilradical_eq_bot]

/-! ### The twisted square with its hypothesis discharged -/

/-- **The vanishing form of the twisted square for two ideal sheaves whose supports cover a
reduced scheme.**  A section of `i₂^*L` over the preimage of `V` whose canonical restriction to
the scheme-theoretic intersection vanishes is the restriction of a unique section of `L` over `V`
vanishing on the first closed subscheme.

This is `Stacks.AffineClosedUnion.existsUnique_unit_app_eq_zero_of_unitRestrict_eq_zero` with
`I₁ ⊓ I₂ = ⊥` replaced by the hypothesis a geometric situation supplies. -/
theorem existsUnique_unit_app_eq_zero_of_sup_support_eq_top [IsReduced X] (L : X.Modules)
    (I₁ I₂ : X.IdealSheafData) (hcov : I₁.support ⊔ I₂.support = ⊤)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L] (V : X.Opens)
    (b : Γ((Scheme.Modules.pullback I₂.subschemeι).obj L, I₂.subschemeι ⁻¹ᵁ V))
    (hb : (unitRestrict (AlgebraicGeometry.Scheme.IdealSheafData.inclusion
      (le_sup_right : I₂ ≤ I₁ ⊔ I₂)) I₂.subschemeι L).app V b = 0) :
    ∃! c : Γ(L, V),
      ((Scheme.Modules.pullbackPushforwardAdjunction I₁.subschemeι).unit.app L).app V c = 0 ∧
        ((Scheme.Modules.pullbackPushforwardAdjunction I₂.subschemeι).unit.app L).app V c = b :=
  existsUnique_unit_app_eq_zero_of_unitRestrict_eq_zero L I₁ I₂
    (inf_eq_bot_of_sup_support_eq_top hcov) V b hb

/-- **The vanishing form of the twisted square at two closed sets covering a reduced scheme**,
with the two reduced closed subschemes they cut out.  This is the form the proof of
[Stacks, Tag 09NX] uses, with `B` an irreducible component and `A` the union of the others. -/
theorem existsUnique_unit_app_eq_zero_of_closeds_sup_eq_top [IsReduced X] (L : X.Modules)
    (A B : Closeds X) (hAB : A ⊔ B = ⊤)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L] (V : X.Opens)
    (b : Γ((Scheme.Modules.pullback (vanishingIdeal B).subschemeι).obj L,
      (vanishingIdeal B).subschemeι ⁻¹ᵁ V))
    (hb : (unitRestrict (AlgebraicGeometry.Scheme.IdealSheafData.inclusion
      (le_sup_right : vanishingIdeal B ≤ vanishingIdeal A ⊔ vanishingIdeal B))
      (vanishingIdeal B).subschemeι L).app V b = 0) :
    ∃! c : Γ(L, V),
      ((Scheme.Modules.pullbackPushforwardAdjunction
        (vanishingIdeal A).subschemeι).unit.app L).app V c = 0 ∧
        ((Scheme.Modules.pullbackPushforwardAdjunction
          (vanishingIdeal B).subschemeι).unit.app L).app V c = b :=
  existsUnique_unit_app_eq_zero_of_sup_support_eq_top L _ _
    (by rw [support_vanishingIdeal, support_vanishingIdeal]; exact hAB) V b hb

end Stacks.AffineClosedUnion

end
