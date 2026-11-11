module

public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier
public import StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.Basic
public import StacksFrontier.AlgebraicGeometry.Intersection.ComputingIntersectionMultiplicities.SchemeTheoreticIntersectionMultiplicity
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The intersection multiplicity of two closed subschemes at a point

Let `X` be a nonsingular variety and let `V`, `W ⊆ X` be closed subvarieties which intersect
properly, and let `Z` be an irreducible component of `V ∩ W` with generic point `ξ`. Section
43.14 of the source attaches to this data the **intersection multiplicity**

`e(X, V · W, Z) = ∑ᵢ (-1)ⁱ length_{𝒪_{X, ξ}} Torᵢ^{𝒪_{X, ξ}}(𝒪_{W, ξ}, 𝒪_{V, ξ})`,

the coefficient of `Z` in the intersection product `V · W`. This file defines that multiplicity
for any two quasi-coherent sheaves of ideals on any scheme, at any point: at `ξ` the local ideals
of `V` and `W` are the stalks `V_ξ`, `W_ξ` of their ideal sheaves, the local rings are
`𝒪_{V, ξ} = 𝒪_{X, ξ} ⧸ V_ξ` and `𝒪_{W, ξ} = 𝒪_{X, ξ} ⧸ W_ξ`, and the alternating sum above is
the Tor-formula multiplicity `Ideal.localIntersectionMultiplicity` of the pair.

The scheme-theoretic intersection `V ∩ W` is cut out by the join `V ⊔ W` of the two ideal
sheaves, and its local ring at `ξ` is `𝒪_{X, ξ} ⧸ (V ⊔ W)_ξ`; this is recorded by
`AlgebraicGeometry.IdealSheafData.stalk_sup`.

With this vocabulary the local form of Tag 0B07 part (1)(a) becomes a statement about a point of
a scheme: when `V` is an effective Cartier divisor near `ξ` and `W` is a subvariety whose local
ring has dimension one, the multiplicity `e(X, V · W, Z)` is the length of the local ring of the
scheme-theoretic intersection, which is the multiplicity of `Z` in the closed subscheme `V ∩ W`.

## Main definitions

* `Stacks.Intersection.intersectionMultiplicity` — the multiplicity `e(X, V · W, Z)`, read at a
  point of `X`.

## Main results

* `AlgebraicGeometry.IdealSheafData.stalk_sup` — the stalk of a join of ideal sheaves is the
  join of the stalks, so the local ring of the scheme-theoretic intersection is
  `𝒪_{X, ξ} ⧸ (V_ξ ⊔ W_ξ)`.
* `Stacks.Intersection.intersectionMultiplicity_eq_length_stalk_sup` — the multiplicity against
  an effective Cartier divisor is the length of the local ring of the scheme-theoretic
  intersection, which is Tag 0B07 part (1)(a) read at one point.

## Implementation notes

The stalk of a quasi-coherent sheaf of ideals is `AlgebraicGeometry.IdealSheafData.stalk`, the
spelling used throughout the Chow tree; the library also carries
`AlgebraicGeometry.Scheme.IdealSheafData.stalkIdeal`, a second definition of the same ideal, and
nothing here uses it.

The multiplicity is `ℚ`-valued because `Ideal.localIntersectionMultiplicity` is: the alternating
sum is formed with `tsum`, which needs a topological target. Its values are integers wherever
the alternating sum is finite, but no integrality statement is proved here and none is needed
for the results below, whose right-hand sides are casts of natural numbers.

### The intersection product

Section 43.14 introduces two things: the multiplicity `e(X, V · W, Z)` displayed above, which is
defined here, and the intersection product itself,
`W · V = ∑ᵢ (-1)ⁱ [Torᵢ^{𝒪_X}(𝒪_W, 𝒪_V)]_{r + s - dim X}`, which is
`AlgebraicGeometry.TorFormula.subvarietyIntersectionProduct`. That the coefficient of the
product at the generic point of an irreducible component `Z` of `V ∩ W` is the multiplicity
defined here, applied to the reduced ideal sheaves of `V` and `W`, is
`AlgebraicGeometry.TorFormula.subvarietyIntersectionProduct_apply`; it rests on the stalk clause of
Tag 0AZT, `Torᵢ^{𝒪_X}(ℱ, 𝒢)_x ≅ Torᵢ^{𝒪_{X, x}}(ℱ_x, 𝒢_x)`, which is
`AlgebraicGeometry.TorFormula.torSheafStalkIso`.

## References

* [Stacks Project, Tag 0AZR](https://stacks.math.columbia.edu/tag/0AZR)
* [Stacks Project, Tag 0B07](https://stacks.math.columbia.edu/tag/0B07)
* [Stacks Project, Tag 0AZT](https://stacks.math.columbia.edu/tag/0AZT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.IdealSheafData

/-- **The stalk of a join of ideal sheaves is the join of the stalks.** Geometrically, the local
ring of the scheme-theoretic intersection of two closed subschemes at a point is the quotient of
the local ring of the ambient scheme by the join of the two local ideals. -/
theorem stalk_sup {X : Scheme.{u}} (I J : X.IdealSheafData) (x : X) :
    IdealSheafData.stalk (I ⊔ J) x = IdealSheafData.stalk I x ⊔ IdealSheafData.stalk J x := by
  obtain ⟨U, hxU⟩ := Stacks.Divisors.exists_affineOpens_mem x
  rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ (I ⊔ J) x U hxU,
    AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ I x U hxU,
    AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ J x U hxU, ← Ideal.map_sup]
  rfl

end AlgebraicGeometry.IdealSheafData

namespace Stacks.Intersection

/-- **Stacks 0AZR.** The intersection multiplicity `e(X, V · W, Z)` of two closed subschemes of a
scheme at a point: the alternating sum `∑ᵢ (-1)ⁱ length Torᵢ(𝒪_W, 𝒪_V)` of the lengths of the
`Tor` modules of their local rings over the local ring of the ambient scheme. For `V` and `W`
closed subvarieties of a nonsingular variety which intersect properly and `x` the generic point
of an irreducible component `Z` of `V ∩ W`, this is the coefficient of `Z` in `V · W`. -/
@[stacks 0AZR "the definition of the intersection multiplicity `e(X, V · W, Z)`, the displayed \
alternating sum of lengths of the local `Tor` modules `Torᵢ^{𝒪_{X, Z}}(𝒪_{V, Z}, 𝒪_{W, Z})` over \
the local ring at the generic point of `Z`, formed for two quasi-coherent sheaves of ideals at a \
point of any scheme. Its agreement with the coefficient of `Z` in the intersection product is \
`AlgebraicGeometry.TorFormula.subvarietyIntersectionProduct_apply`.",
  sga "4½ Cycle 2.3.9",
  sga "4½ Cycle 3.5"]
def intersectionMultiplicity {X : Scheme.{u}} (V W : X.IdealSheafData) (x : X) : ℚ :=
  (IdealSheafData.stalk V x).localIntersectionMultiplicity
    ((X.presheaf.stalk x) ⧸ IdealSheafData.stalk W x)

/-- The intersection multiplicity at a point is the Tor-formula multiplicity of the two local
ideals, by definition. -/
theorem intersectionMultiplicity_eq {X : Scheme.{u}} (V W : X.IdealSheafData) (x : X) :
    intersectionMultiplicity V W x =
      (IdealSheafData.stalk V x).localIntersectionMultiplicity
        ((X.presheaf.stalk x) ⧸ IdealSheafData.stalk W x) :=
  rfl

/-- **Stacks 0B07, part (1)(a) at one point of a scheme.** Let `x` be a point of a scheme at
which the local ring is regular, let `V` be a sheaf of ideals cut out at `x` by a one-element
regular sequence, and let `W` be a sheaf of ideals whose local ring `𝒪_{X, x} ⧸ W_x` at `x` is a
domain of dimension one, and suppose `x` is a generic point of `V ∩ W`, that is,
`dim (𝒪_{X, x} ⧸ (V ⊔ W)_x) = 0`. Then the intersection multiplicity of `V` and `W` at `x` is
the length of the local ring of the scheme-theoretic intersection `V ∩ W` at `x`.

Geometrically, for `X × P¹` in place of `X`, `V` the effective Cartier divisor `X × a` and `W` a
closed subvariety of dimension `k + 1` meeting it properly, the right-hand side is the
multiplicity of the component `Z` in the scheme-theoretic fibre `W_a = W ∩ X × a`, that is, the
coefficient of `Z` in `[W_a]_k`, and the left-hand side is its coefficient in `W · X × a`. -/
theorem intersectionMultiplicity_eq_length_stalk_sup {X : Scheme.{u}} (V W : X.IdealSheafData)
    (x : X) [IsRegularLocalRing (X.presheaf.stalk x)]
    [IsDomain ((X.presheaf.stalk x) ⧸ IdealSheafData.stalk W x)]
    (f : Fin 1 → (X.presheaf.stalk x))
    (hf : RingTheory.Sequence.IsRegular (X.presheaf.stalk x) (List.ofFn f))
    (hV : IdealSheafData.stalk V x = Ideal.span (Set.range f))
    (h0 : ringKrullDim ((X.presheaf.stalk x) ⧸ IdealSheafData.stalk (V ⊔ W) x) = 0)
    (hW : ringKrullDim ((X.presheaf.stalk x) ⧸ IdealSheafData.stalk W x) = 1) :
    intersectionMultiplicity V W x =
      ((Module.length (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ IdealSheafData.stalk (V ⊔ W) x)).toNat : ℚ) := by
  rw [intersectionMultiplicity_eq]
  rw [AlgebraicGeometry.IdealSheafData.stalk_sup] at h0 ⊢
  exact localIntersectionMultiplicity_eq_length_quotient_sup_of_isDomain f
    (IdealSheafData.stalk V x) (IdealSheafData.stalk W x) hf hV h0 hW

end Stacks.Intersection

end
