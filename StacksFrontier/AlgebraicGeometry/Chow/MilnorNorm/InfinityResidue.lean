module

public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.ConstantRetraction
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ProjectiveLineInfinity

/-!
# The residue at infinity of a rational function field, in every degree

Let `k` be a field and let `F = RatFunc k` be the field of rational functions over `k`. Besides
the closed points of `A¹_k`, whose residues are `Stacks.Chow.affineLineResidue`, the projective
line has the point at infinity, and the residue there,

`∂_∞ : K^M_{i+1}(F) ⟶ K^M_i(k)`,

is the remaining term of Milnor's exact sequence for `F`. This file constructs it.

The local ring at infinity is the image of the local ring at the origin under the substitution
`X ↦ 1/X`, so `∂_∞` is the residue at the origin precomposed with the involution of `F` that
substitution defines. That involution is already in the tree as
`AlgebraicGeometry.projectiveLineChartInversion`, where it is obtained from the two charts of
`ℙ¹_k` and the identifications of their function fields with `RatFunc k`; its two computations
`AlgebraicGeometry.projectiveLineChartInversion_C` and
`AlgebraicGeometry.projectiveLineChartInversion_X` say that it fixes the constants and inverts
the coordinate, which is all that is used here. The residue field at infinity is therefore
identified with `k` by `Stacks.Chow.residueFieldAtOriginEquiv`, as it should be, the point at
infinity being a rational point of `ℙ¹_k`.

## Main definitions

* `Stacks.Chow.infinityResidue` — the residue `∂_∞ : K^M_{i+1}(F) ⟶ K^M_i(k)`.

## Main results

* `Stacks.Chow.projectiveLineChartInversion_constantsHom` — the involution fixes a constant read
  as a rational function.
* `Stacks.Chow.infinityResidue_eq_zero_of_constants` — **`∂_∞` kills a symbol of constants.**
  This is what makes the norm map of a simple extension well defined once Milnor's sequence is
  exact, the constants being the image of `K^M_{i+1}(k)`.

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
-/

@[expose] public noncomputable section

open IsLocalRing Polynomial

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k]

/-! ### The involution `X ↦ 1/X` on the constants -/

/-- The involution gluing the two charts of `ℙ¹_k` fixes a constant. This is
`AlgebraicGeometry.projectiveLineChartInversion_C`, read through `Stacks.Chow.constantsHom`. -/
theorem projectiveLineChartInversion_constantsHom (c : k) :
    AlgebraicGeometry.projectiveLineChartInversion k (constantsHom k c) = constantsHom k c :=
  AlgebraicGeometry.projectiveLineChartInversion_C k c

/-! ### The residue at infinity -/

/-- **The residue at infinity `∂_∞ : K^M_{i+1}(k(X)) ⟶ K^M_i(k)`, in every degree.** The local
ring of `P¹_k` at infinity is carried to the local ring at the origin by the substitution
`X ↦ 1/X`, so this is the residue at the origin read through that involution. -/
def infinityResidue (i : ℕ) :
    MilnorKTheory (RatFunc k) (i + 1) →+ MilnorKTheory k i :=
  ((milnorKTransportEquiv (residueFieldAtOriginEquiv k) i).symm.toAddMonoidHom.comp
      (dvrMilnorTameSymbol (F := RatFunc k)
        (irreducible_algebraMap_X (k := k)) i)).comp
    (milnorKTransport (AlgebraicGeometry.projectiveLineChartInversion k).toRingHom (i + 1))

/-- **The residue at infinity kills a symbol of constants.** The substitution `X ↦ 1/X` fixes the
constants, and a constant is a unit of the local ring at the origin, so this is the vanishing of
the tame symbol on a symbol of units. -/
theorem infinityResidue_eq_zero_of_constants (i : ℕ)
    {y : MilnorKTheory (RatFunc k) (i + 1)} (l : List kˣ)
    (hy : (y : MilnorKRing (RatFunc k)) =
      milnorKSymbolProd (RatFunc k)
        (l.map (Units.map (constantsHom k).toMonoidHom))) :
    infinityResidue i y = 0 := by
  have hcoe : (milnorKTransport
        (AlgebraicGeometry.projectiveLineChartInversion k).toRingHom (i + 1) y :
      MilnorKRing (RatFunc k)) =
      unitSymbolProd (RatFunc k) (l.map constantUnit) := by
    rw [milnorKTransport_coe, hy, milnorKRingMap_milnorKSymbolProd]
    refine Eq.trans ?_ (milnorKSymbolProd_constants_eq_unitSymbolProd l)
    refine congrArg (milnorKSymbolProd (RatFunc k)) ?_
    rw [List.map_map]
    exact List.map_congr_left fun c _ ↦
      Units.ext (projectiveLineChartInversion_constantsHom (c : k))
  show (milnorKTransportEquiv (residueFieldAtOriginEquiv k) i).symm
    (dvrMilnorTameSymbol (irreducible_algebraMap_X (k := k)) i
      (milnorKTransport (AlgebraicGeometry.projectiveLineChartInversion k).toRingHom
        (i + 1) y)) = 0
  rw [dvrMilnorTameSymbol_eq_zero_of_units (irreducible_algebraMap_X (k := k)) i
    (l.map constantUnit) hcoe, map_zero]

end Stacks.Chow

end
