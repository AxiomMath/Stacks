module

public import StacksFrontier.AlgebraicGeometry.Thickenings

/-!
# Restricting a first-order thickening to an open of the ambient scheme

A first-order thickening `i : X ⟶ X'` is a closed immersion whose kernel ideal sheaf is
square-zero. Both halves of that condition survive passing to an open `V` of the ambient
scheme `X'`: being a closed immersion is Zariski-local at the target, and the kernel ideal
sheaf of the restricted morphism `i ∣_ V` is computed, affine open by affine open, by the
kernel ideal sheaf of `i` over the corresponding affine open of `X'`.

This is the restriction statement that the sheaf of [Stacks Project, Tag 04FH] needs in order
to have restriction maps: the lifts of a morphism over an open `V` of `X'` are constrained by
the conormal sheaf of `i ∣_ V`, so passing from `V` to a smaller open presupposes that
`i ∣_ V` is again a first-order thickening.

## Main results

* `Stacks.Thickenings.ideal_ker_pow_morphismRestrict`: a power of the kernel ideal sheaf of a
  quasi-compact morphism restricts, on an affine open of `V`, to the same power of the kernel
  ideal sheaf of the morphism itself on the corresponding affine open of the ambient scheme.
* `Stacks.Thickenings.ker_pow_morphismRestrict_eq_bot`: consequently a vanishing power of the
  kernel ideal sheaf is inherited by the restriction.
* `Stacks.Thickenings.IsFirstOrderThickening.morphismRestrict`: a first-order thickening
  restricts to a first-order thickening over any open of the ambient scheme.
* `Stacks.Thickenings.IsFiniteOrderThickening.morphismRestrict`: the same for a finite-order
  thickening, with the same order.

## Implementation notes

The two ideal sheaves are compared through their families: multiplication of ideal sheaves is
pointwise on affine opens, so `ideal_ker_pow_morphismRestrict` is Mathlib's
`AlgebraicGeometry.Scheme.ker_morphismRestrict_ideal` raised to a power, and the equality of
ideal sheaves is then extensionality in the family.

That is a choice of route, not a necessity. A lemma relating
`AlgebraicGeometry.Scheme.Hom.ker` directly to the restricted morphism's global sections does
exist: `AlgebraicGeometry.GoodDiagramKer.ker_resLE_appTop` states, for quasi-compact `f` and an
affine open `U` of the target, that `f.ker.ideal U` transported along
`AlgebraicGeometry.Scheme.Opens.topIso` is `RingHom.ker (f.resLE U V hV.le).appTop.hom`, and
`AlgebraicGeometry.Scheme.Hom.resLE_eq_morphismRestrict` turns that into the `∣_` spelling in
one rewrite — which is exactly `AlgebraicGeometry.GoodDiagramKer.ker_morphismRestrict_appTop`,
with the `f.ker.ideal U` orientation in
`AlgebraicGeometry.GoodDiagramKer.ideal_ker_eq_comap_ker_morphismRestrict_appTop`. The kernel on
global sections alone, with no hypothesis on `f`, is
`Stacks.AlgebraicGeometry.ker_appTop_morphismRestrict`.

Quasi-compactness is needed because `AlgebraicGeometry.Scheme.Hom.ker` is only the largest
quasi-coherent ideal sheaf below the componentwise kernel, and agrees with the componentwise
kernel exactly under that hypothesis. For a closed immersion it is automatic, so it does not
appear in `IsFirstOrderThickening.morphismRestrict`.

## References

* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 04FH](https://stacks.math.columbia.edu/tag/04FH)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Thickenings

variable {X X' : Scheme.{u}}

/-- **A power of the kernel ideal sheaf is local on the ambient scheme.** For a quasi-compact
`i : X ⟶ X'` and an affine open `W` of an open `V` of `X'`, the `n`-th power of the kernel ideal
sheaf of `i ∣_ V` over `W` is the `n`-th power of the kernel ideal sheaf of `i` over the image
of `W` in `X'`. -/
theorem ideal_ker_pow_morphismRestrict (i : X ⟶ X') [QuasiCompact i] (V : X'.Opens) (n : ℕ)
    (W : V.toScheme.affineOpens) :
    ((i ∣_ V).ker ^ n).ideal W =
      (i.ker ^ n).ideal ⟨V.ι ''ᵁ W.1, W.2.image_of_isOpenImmersion _⟩ := by
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
  rw [Scheme.ker_morphismRestrict_ideal]
  rfl

/-- **A vanishing power of the kernel ideal sheaf is inherited by a restriction to an open of
the ambient scheme.** -/
theorem ker_pow_morphismRestrict_eq_bot (i : X ⟶ X') [QuasiCompact i] {n : ℕ}
    (hn : i.ker ^ n = ⊥) (V : X'.Opens) : (i ∣_ V).ker ^ n = ⊥ :=
  Scheme.IdealSheafData.ext (funext fun W =>
    (ideal_ker_pow_morphismRestrict i V n W).trans
      (congrFun (congrArg Scheme.IdealSheafData.ideal hn) _))

/-- **A first-order thickening restricts to a first-order thickening over any open of the
ambient scheme.** Being a closed immersion is Zariski-local at the target, and the kernel ideal
sheaf of the restriction is the restriction of the kernel ideal sheaf. -/
theorem IsFirstOrderThickening.morphismRestrict {i : X ⟶ X'} (hi : IsFirstOrderThickening i)
    (V : X'.Opens) : IsFirstOrderThickening (i ∣_ V) :=
  have : IsClosedImmersion i := hi.1
  ⟨IsZariskiLocalAtTarget.restrict ‹IsClosedImmersion i› V,
    ker_pow_morphismRestrict_eq_bot i hi.2 V⟩

/-- **A finite-order thickening restricts to a finite-order thickening over any open of the
ambient scheme**, with the same order. -/
theorem IsFiniteOrderThickening.morphismRestrict {i : X ⟶ X'} (hi : IsFiniteOrderThickening i)
    (V : X'.Opens) : IsFiniteOrderThickening (i ∣_ V) :=
  have : IsClosedImmersion i := hi.1
  ⟨IsZariskiLocalAtTarget.restrict ‹IsClosedImmersion i› V,
    hi.2.choose, ker_pow_morphismRestrict_eq_bot i hi.2.choose_spec V⟩

end Stacks.Thickenings

end
