module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne.Converse
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder.Stalk

/-!
# An invertible module is trivialized near every point

Let `X` be a scheme and let `L` be an invertible `𝒪_X`-module. This file proves that `L` is
*trivialized near* every point of `X` in the sense of `Stacks.Divisors.IsTrivializedNear`: some
open neighbourhood of the point carries a section of `L` whose germ is a basis of the free
rank-one stalk at each of its points.

That condition is the rank-one hypothesis which the order of vanishing of a meromorphic section
(`Stacks.Divisors.orderOfVanishing`, Stacks 02SF) and its Weil divisor
(`Stacks.Divisors.weilDivisorOfMeromorphicSection`, Stacks 0BE6 (1)) carry explicitly, so the
bridge here discharges that hypothesis for an invertible module and makes the whole
order-of-vanishing calculus of `StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder` apply to the
situation of Stacks 02SJ, where `L` is invertible.

## The argument

Invertibility produces a module `N` and a trivialization `ψ : L ⊗_{𝒪_X} N ≅ 𝒪_X`, and
`Stacks.SheafOfModules.exists_tensorPairing_eq_one_nhds` turns that, at a point whose structure
stalk is a local ring, into sections `s` of `L` and `b` of `N` on a neighbourhood `U` pairing to
the unit section. `Stacks.SheafOfModules.bijective_smul_grpGerm_of_tensorPairing_eq_one` then says
that multiplication by the germ of `s` is bijective at *every* point of `U`, which is exactly the
stalk-basis condition. All the mathematics is therefore already in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleRankOne/Converse.lean`, the converse
clause of Stacks 0B8M; what is added here is the passage from the ringed-space spelling of the
stalk to the scheme one. Both the germ maps (`Stacks.SheafOfModules.grpGerm_eq_germ`) and the
module structures agree by `rfl`: the module structure of
[Stacks, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB) is Mathlib's.

## Main results

* `Stacks.Divisors.isTrivializedNear_of_isInvertible` — an invertible module is trivialized near
  every point.
* `Stacks.Divisors.exists_ne_zero_genericStalk` — on an integral scheme a module trivialized near
  the generic point has a nonzero generic stalk.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 02OZ](https://stacks.math.columbia.edu/tag/02OZ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
  Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.SheafOfModules

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (L : X.Modules)

/-- **An invertible `𝒪_X`-module is trivialized near every point.** This is the stalkwise form of
the converse clause of Stacks 0B8M, and it discharges the `Stacks.Divisors.IsTrivializedNear`
hypothesis of the order-of-vanishing calculus for an invertible module.

No Stacks attribute is attached: Tag 0B8M is the equivalence of invertibility with finite local
freeness of rank one together with the failure of its converse for general ringed spaces, and
this is a consequence of one direction of it, not the tag. -/
theorem isTrivializedNear_of_isInvertible
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (x : X) :
    IsTrivializedNear L x := by
  have hinv : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L :=
    IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance
  obtain ⟨N, ⟨ψ⟩⟩ := (isInvertible_iff_exists_tensor_iso_unit
    (O := X.toRingedSpace.presheaf)
    (hO := (structureSheafRing X.toRingedSpace).property) L).mp hinv
  obtain ⟨U, hxU, s, b, hsb⟩ := exists_tensorPairing_eq_one_nhds ψ x
  refine ⟨U, hxU, s, fun y hyU => ?_⟩
  have h := bijective_smul_grpGerm_of_tensorPairing_eq_one hsb y hyU
  exact h

variable {L}

/-- **A regular meromorphic section exists, in the generic-stalk model.** On an integral scheme a
module trivialized near the generic point has a nonzero element of its generic stalk: a
trivializing germ there is a basis of a free rank-one module over the function field, hence
nonzero.

This is the content of Stacks 02OZ (1) for the model of a meromorphic section used in
`StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder`, where a meromorphic section of `L` on an
integral scheme is an element of `L_η` and regularity is nonvanishing. It is *not* Stacks 02OZ,
whose statement is about a global section of the sheaf `K_X(L)`: the identification of `K_X(L)`
with the constant sheaf on `L_η` is Stacks 01X5 (2), which this library does not have, so no
Stacks attribute is attached. -/
theorem exists_ne_zero_genericStalk [IsIntegral X] (hL : IsTrivializedNear L (genericPoint X)) :
    ∃ s : L.presheaf.stalk (genericPoint X), s ≠ 0 := by
  obtain ⟨W, hηW, t, hb⟩ := hL
  refine ⟨L.presheaf.germ W (genericPoint X) hηW t, fun h0 => zero_ne_one (α := X.functionField)
    ((hb _ hηW).injective (a₁ := 0) (a₂ := 1) ?_)⟩
  show (0 : X.presheaf.stalk (genericPoint X)) • _ = (1 : X.presheaf.stalk _) • _
  rw [h0, smul_zero, smul_zero]

/-- An invertible module on an integral scheme has a nonzero generic stalk. -/
theorem exists_ne_zero_genericStalk_of_isInvertible [IsIntegral X] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    ∃ s : L.presheaf.stalk (genericPoint X), s ≠ 0 :=
  exists_ne_zero_genericStalk (isTrivializedNear_of_isInvertible L _)

end Stacks.Divisors

end
