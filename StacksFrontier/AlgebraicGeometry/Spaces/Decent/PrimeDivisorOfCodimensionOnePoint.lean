module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FunctionFieldAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.InvertibleSheafDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionLocalRing

/-!
# The prime divisor with a prescribed codimension-one generic point

Let `X` be a decent algebraic space over a scheme `S` and let `ξ` be a point of `|X|` whose
local ring has dimension one — equivalently, by Stacks 0ED1, whose closure has codimension one
in `|X|`. Then `ξ` is the generic point of a prime divisor of `X`, and of exactly one.

This is the direction of Stacks 0ENF that the proof of Stacks 0EPX uses: the source attaches a
prime divisor `Z` to a codimension-one point `ξ` of `|X|` and then reads the order of vanishing
along `Z`. Each ingredient is already available — the reduced induced closed subspace on the
closure of a point
(`AlgebraicGeometry.Space.integralClosedSubspaceOfPoint`), the passage from an integral closed
subspace of codimension one to a prime divisor
(`AlgebraicGeometry.Space.IntegralClosedSubspace.toPrimeDivisor`), the identification of
codimension with the dimension of the local ring (Stacks 0ED1,
`AlgebraicGeometry.Space.codimension_eq_localRingDimension`) and the injectivity of
`ξ ↦ closure {ξ}` on a decent space (Stacks 0ENF,
`AlgebraicGeometry.Space.injective_closureSingleton_points`) — but not their composite.

## Main results

* `AlgebraicGeometry.Space.exists_primeDivisor_genericPoint_eq_of_localRingDimension_eq_one`: a
  point whose local ring has dimension one is the generic point of a prime divisor.
* `AlgebraicGeometry.Space.existsUnique_primeDivisor_genericPoint_eq_of_localRingDimension_eq_one`:
  it is the generic point of exactly one prime divisor.

## Implementation notes

The hypothesis is on the dimension of the local ring rather than on the codimension of the
closure because that is the form a client holding a chart has: the dimension of the local ring at
a point of `|X|` is the dimension of the local ring of any étale chart above it, which is
`AlgebraicGeometry.Space.localRingDimension_eq_of_chartPoint`. Stacks 0ED1 turns it into the
codimension that `AlgebraicGeometry.Space.PrimeDivisor` asks for.

Uniqueness is not the injectivity of
`AlgebraicGeometry.Space.integralClosedSubspaceSupport` but of `ξ ↦ closure {ξ}`: two prime
divisors with the same generic point have the same point set, hence the same subfunctor by
`AlgebraicGeometry.Space.injective_integralClosedSubspaceSupport`, hence are equal by
`AlgebraicGeometry.Space.PrimeDivisor.eq_of_subspace_eq`. The generic point a prime divisor
carries is itself only determined up to that injectivity, `AlgebraicGeometry.Space.PrimeDivisor`
recording a choice of generic point as data.

## References

* [Stacks Project, Tag 0ED1](https://stacks.math.columbia.edu/tag/0ED1)
* [Stacks Project, Tag 0ENF](https://stacks.math.columbia.edu/tag/0ENF)
* [Stacks Project, Tag 0ENJ](https://stacks.math.columbia.edu/tag/0ENJ)
* [Stacks Project, Tag 0EPX](https://stacks.math.columbia.edu/tag/0EPX)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X)

include hX hdec in
/-- **A point of codimension one is the generic point of a prime divisor.** The reduced induced
closed subspace on the closure of such a point is an integral closed subspace whose point set is
that closure, so by Stacks 0ED1 it has codimension one in `|X|` and is therefore a prime
divisor; the generic point it carries has the same closure as `ξ`, and on a decent space that
forces it to be `ξ`.

This is the direction of Stacks 0ENF used in the proof of Stacks 0EPX, where a prime divisor is
attached to a codimension-one point of `|X|` in order to read an order of vanishing along it. -/
theorem exists_primeDivisor_genericPoint_eq_of_localRingDimension_eq_one
    (ξ : points B S hS X) (hξ : localRingDimension B S hS ξ = 1) :
    ∃ Z : PrimeDivisor B S hS X, Z.genericPoint B S hS X = ξ := by
  have hξgen : IsGenericPoint ξ (IrreducibleCloseds.closureSingleton ξ : Set (points B S hS X)) :=
    (IrreducibleCloseds.coe_closureSingleton ξ).symm
  have hgen : IsGenericPoint ξ (subspacePointSet B S hS X
      (integralClosedSubspaceOfPoint B S hS hX hdec ξ).subspace) :=
    isGenericPoint_integralClosedSubspaceOfPoint B S hS hX hdec ξ
  have hsupp : integralClosedSubspaceSupport B S hS hX
      (integralClosedSubspaceOfPoint B S hS hX hdec ξ) =
      IrreducibleCloseds.closureSingleton ξ :=
    IrreducibleCloseds.ext hgen.symm
  have hcod : codimension (integralClosedSubspaceSupport B S hS hX
      (integralClosedSubspaceOfPoint B S hS hX hdec ξ)) = 1 := by
    rw [hsupp, codimension_eq_localRingDimension B S hS hX hdec _ ξ hξgen]
    exact hξ
  refine ⟨(integralClosedSubspaceOfPoint B S hS hX hdec ξ).toPrimeDivisor B S hS hX hcod, ?_⟩
  refine injective_closureSingleton_points B S hS hX hdec (IrreducibleCloseds.ext ?_)
  exact (((integralClosedSubspaceOfPoint B S hS hX hdec ξ).toPrimeDivisor B S hS hX
    hcod).isGenericPoint_genericPoint B S hS X).trans hgen.symm

include hX hdec in
/-- **A point of codimension one is the generic point of exactly one prime divisor.** Two prime
divisors with the same generic point have the same point set, and an integral closed subspace is
determined by its point set. -/
theorem existsUnique_primeDivisor_genericPoint_eq_of_localRingDimension_eq_one
    (ξ : points B S hS X) (hξ : localRingDimension B S hS ξ = 1) :
    ∃! Z : PrimeDivisor B S hS X, Z.genericPoint B S hS X = ξ := by
  obtain ⟨Z, hZ⟩ :=
    exists_primeDivisor_genericPoint_eq_of_localRingDimension_eq_one B S hS hX hdec ξ hξ
  refine ⟨Z, hZ, fun W hW => ?_⟩
  refine PrimeDivisor.injective_toIntegralClosedSubspace B S hS
    (injective_integralClosedSubspaceSupport B S hS hX (IrreducibleCloseds.ext ?_))
  exact ((W.isGenericPoint_genericPoint B S hS X).symm.trans
    (congrArg (fun y : points B S hS X => closure {y}) (hW.trans hZ.symm))).trans
    (Z.isGenericPoint_genericPoint B S hS X)

/-! ### The hypothesis as a client holding a chart has it -/

include hX hdec in
/-- **A codimension-one point of an étale scheme chart lies over the generic point of a prime
divisor.** If `u` is a point of an étale scheme chart of `X` whose coheight in that chart is one
— equivalently, by Stacks 02IZ, whose local ring there has Krull dimension one — then the point
`ξ` of `|X|` it lies over is the generic point of a prime divisor of `X`.

This is the form of the two results above that a client holding a chart can use, and it is the
shape the proof of Stacks 0EPX needs: the source runs over the height-one primes of an affine
chart `Spec(A)` and attaches a prime divisor of `X` to each. The dimension of the local ring of
`|X|` at `ξ` is the Krull dimension of the local ring of *any* étale chart at *any* point above
`ξ`, which is `AlgebraicGeometry.Space.localRingDimension_eq_of_chartPoint`, so the hypothesis
on the chart is already the hypothesis on the space. -/
theorem exists_primeDivisor_genericPoint_eq_of_coheight_chartPoint_eq_one
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X)
    (ha : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) a)
    (u : (BigFppfOver.toScheme B S hS).obj U) (ξ : points B S hS X)
    (hu : ChartPoint B S hS U a u ξ) (hcoh : Order.coheight u = 1) :
    ∃ Z : PrimeDivisor B S hS X, Z.genericPoint B S hS X = ξ := by
  refine exists_primeDivisor_genericPoint_eq_of_localRingDimension_eq_one B S hS hX hdec ξ ?_
  have h := localRingDimension_eq_of_chartPoint B S hS hX U a ha u ξ hu
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight u, hcoh] at h
  exact_mod_cast h

include hX hdec in
/-- **A codimension-one point of an étale scheme chart lies over the generic point of exactly
one prime divisor.** The chart form of
`AlgebraicGeometry.Space.existsUnique_primeDivisor_genericPoint_eq_of_localRingDimension_eq_one`,
uniqueness being the injectivity of `ξ ↦ closure {ξ}` on a decent space. -/
theorem existsUnique_primeDivisor_genericPoint_eq_of_coheight_chartPoint_eq_one
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X)
    (ha : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) a)
    (u : (BigFppfOver.toScheme B S hS).obj U) (ξ : points B S hS X)
    (hu : ChartPoint B S hS U a u ξ) (hcoh : Order.coheight u = 1) :
    ∃! Z : PrimeDivisor B S hS X, Z.genericPoint B S hS X = ξ := by
  refine existsUnique_primeDivisor_genericPoint_eq_of_localRingDimension_eq_one B S hS hX hdec
    ξ ?_
  have h := localRingDimension_eq_of_chartPoint B S hS hX U a ha u ξ hu
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight u, hcoh] at h
  exact_mod_cast h

end AlgebraicGeometry.Space

end
