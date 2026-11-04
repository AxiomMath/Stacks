module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ProjectionFormula.PoincareDuality

/-!
# Functoriality and the projection formula for the Poincaré-dual pushforward

The pushforward adjoint to pullback with respect to perfect trace pairings is covariantly
functorial, and it commutes with cup multiplication by a pulled-back class.

## Main results

* `Stacks.WeilCohomology.poincareDualPushforward_comp` identifies the pushforward of a composite
  pullback with the composite of the corresponding pushforwards.
* `Stacks.WeilCohomology.poincareDualPushforward_cup` is the projection formula
  `f₊ (f⁺ b ∪ a) = b ∪ f₊ a`.
* `Stacks.WeilCohomology.poincareDualPushforward_externalProduct` computes the pushforward along
  the second projection of an external product: `pr₂,₊ (a × b) = (∫_X a) • b`.

## Implementation notes

The statements use the abstract pairing formulation of Poincaré duality of
`Stacks.WeilCohomology.poincareDualPushforward`: the pairings stand for the cup-product trace
pairings of the schemes involved, and Tate twists and degree shifts are incorporated into the
module types.

In the projection formula the two pairs of dual modules represent the complementary cohomological
degrees before and after multiplication by `b`.  The two `cupLeft` maps express associativity of
cup product inside the trace pairings, and the compatibility of `pullback` with these maps is
multiplicativity of cohomological pullback.

In `poincareDualPushforward_externalProduct` the data are read as follows.  `pairXY` and `pairY`
are the trace pairings of `X × Y` and of `Y`, and `[pairY.IsPerfPair]` is Poincaré duality for
`Y`; `pullbackSnd` is `pr₂⁺`; `ext a b` is the external product `pr₁⁺ a ∪ pr₂⁺ b`, taken in the
two ranges of degrees `ext` and `ext'` that occur.  The hypothesis `cup_externalProduct` is the
identity `pr₂⁺ v ∪ (a × b) = a × (v ∪ b)` and `integral_externalProduct` is the factorization
`∫_{X × Y} = ∫_X ⊗ ∫_Y` of the trace of a product.  The conclusion is
`pr₂,₊ (a × b) = (∫_X a) • b`.

`poincareDualPushforward_externalProduct` takes `cup_externalProduct` and
`integral_externalProduct` as hypotheses.

## References

* [Stacks Project, Tag 0FHB](https://stacks.math.columbia.edu/tag/0FHB)
-/

@[expose] public section

namespace Stacks.WeilCohomology

universe uR uHX uHY uHZ uDX uDY uDZ

/-- Poincaré-dual pushforward is covariantly functorial for composable pullbacks. -/
@[stacks 0FHB "pushforward_composition"]
theorem poincareDualPushforward_comp
    {R : Type uR} [CommSemiring R]
    {HX : Type uHX} [AddCommMonoid HX] [Module R HX]
    {HY : Type uHY} [AddCommMonoid HY] [Module R HY]
    {HZ : Type uHZ} [AddCommMonoid HZ] [Module R HZ]
    {DX : Type uDX} [AddCommMonoid DX] [Module R DX]
    {DY : Type uDY} [AddCommMonoid DY] [Module R DY]
    {DZ : Type uDZ} [AddCommMonoid DZ] [Module R DZ]
    (pairX : HX →ₗ[R] DX →ₗ[R] R)
    (pairY : HY →ₗ[R] DY →ₗ[R] R)
    (pairZ : HZ →ₗ[R] DZ →ₗ[R] R)
    [pairY.IsPerfPair] [pairZ.IsPerfPair]
    (pullbackF : HY →ₗ[R] HX) (pullbackG : HZ →ₗ[R] HY) :
    (poincareDualPushforward pairY pairZ pullbackG).comp
        (poincareDualPushforward pairX pairY pullbackF) =
      poincareDualPushforward pairX pairZ (pullbackF.comp pullbackG) := by
  ext a
  apply (pairZ.flip.toPerfPair).injective
  ext c
  simp

/-- Two vectors paired equally against everything by a perfect pairing are equal. -/
private theorem eq_of_forall_pair_eq
    {R : Type*} [CommSemiring R] {H D : Type*}
    [AddCommMonoid H] [Module R H] [AddCommMonoid D] [Module R D]
    (pair : H →ₗ[R] D →ₗ[R] R) [pair.IsPerfPair] {x y : D}
    (h : ∀ v, pair v x = pair v y) : x = y :=
  (LinearMap.IsPerfPair.bijective_right pair).injective (LinearMap.ext h)

/-- The projection formula `f₊ (f⁺ b ∪ a) = b ∪ f₊ a` for the pushforward defined by Poincaré
duality.  The pairing identities are associativity of cup product under integration, and
`pullback_cup` is its naturality. -/
@[stacks 0FHB "projection_formula"]
theorem poincareDualPushforward_cup
    {R : Type*} [CommSemiring R]
    {HX DX HX' DX' HY DY HY' DY' BX BY : Type*}
    [AddCommMonoid HX] [Module R HX]
    [AddCommMonoid DX] [Module R DX]
    [AddCommMonoid HX'] [Module R HX']
    [AddCommMonoid DX'] [Module R DX']
    [AddCommMonoid HY] [Module R HY]
    [AddCommMonoid DY] [Module R DY]
    [AddCommMonoid HY'] [Module R HY']
    [AddCommMonoid DY'] [Module R DY']
    [AddCommMonoid BX] [Module R BX]
    [AddCommMonoid BY] [Module R BY]
    (pairX : HX →ₗ[R] DX →ₗ[R] R)
    (pairY : HY →ₗ[R] DY →ₗ[R] R) [pairY.IsPerfPair]
    (pairX' : HX' →ₗ[R] DX' →ₗ[R] R)
    (pairY' : HY' →ₗ[R] DY' →ₗ[R] R) [pairY'.IsPerfPair]
    (pullback : HY →ₗ[R] HX)
    (pullback' : HY' →ₗ[R] HX')
    (pullbackB : BY →ₗ[R] BX)
    (cupX : BX →ₗ[R] DX →ₗ[R] DX')
    (cupY : BY →ₗ[R] DY →ₗ[R] DY')
    (cupLeftX : HX' →ₗ[R] BX →ₗ[R] HX)
    (cupLeftY : HY' →ₗ[R] BY →ₗ[R] HY)
    (pullback_cup : ∀ c b,
      pullback (cupLeftY c b) = cupLeftX (pullback' c) (pullbackB b))
    (trace_assoc_X : ∀ c b a,
      pairX' c (cupX b a) = pairX (cupLeftX c b) a)
    (trace_assoc_Y : ∀ c b a,
      pairY' c (cupY b a) = pairY (cupLeftY c b) a)
    (b : BY) (a : DX) :
    poincareDualPushforward pairX' pairY' pullback'
        (cupX (pullbackB b) a) =
      cupY b (poincareDualPushforward pairX pairY pullback a) := by
  refine eq_of_forall_pair_eq pairY' fun c => ?_
  simp [trace_assoc_X, trace_assoc_Y, ← pullback_cup]

/-- The pushforward along the second projection `X × Y → Y` sends an external product
`a × b = pr₁⁺ a ∪ pr₂⁺ b` to `(∫_X a) • b`.  The hypotheses express the trace pairings as
integrals of cup products, the interaction of a pulled-back class with an external product, and
the factorization `∫_{X × Y} = ∫_X ⊗ ∫_Y` of the trace of a product.

The identity `cup_externalProduct : pr₂⁺ v ∪ (a × b) = a × (v ∪ b)` is taken as a hypothesis. -/
theorem poincareDualPushforward_externalProduct
    {R : Type*} [CommSemiring R]
    {HXY DXY DXY' HY DY DY' AX : Type*}
    [AddCommMonoid HXY] [Module R HXY]
    [AddCommMonoid DXY] [Module R DXY]
    [AddCommMonoid DXY'] [Module R DXY']
    [AddCommMonoid HY] [Module R HY]
    [AddCommMonoid DY] [Module R DY]
    [AddCommMonoid DY'] [Module R DY']
    [AddCommMonoid AX] [Module R AX]
    (pairXY : HXY →ₗ[R] DXY →ₗ[R] R)
    (pairY : HY →ₗ[R] DY →ₗ[R] R) [pairY.IsPerfPair]
    (pullbackSnd : HY →ₗ[R] HXY)
    (ext : AX →ₗ[R] DY →ₗ[R] DXY)
    (ext' : AX →ₗ[R] DY' →ₗ[R] DXY')
    (cupXY : HXY →ₗ[R] DXY →ₗ[R] DXY')
    (cupY : HY →ₗ[R] DY →ₗ[R] DY')
    (integralXY : DXY' →ₗ[R] R)
    (integralX : AX →ₗ[R] R)
    (integralY : DY' →ₗ[R] R)
    (pairXY_eq : ∀ c z, pairXY c z = integralXY (cupXY c z))
    (pairY_eq : ∀ v b, pairY v b = integralY (cupY v b))
    (cup_externalProduct : ∀ v a b, cupXY (pullbackSnd v) (ext a b) = ext' a (cupY v b))
    (integral_externalProduct : ∀ a c, integralXY (ext' a c) = integralX a * integralY c)
    (a : AX) (b : DY) :
    poincareDualPushforward pairXY pairY pullbackSnd (ext a b) = integralX a • b := by
  refine eq_of_forall_pair_eq pairY fun v => ?_
  rw [pair_poincareDualPushforward, pairXY_eq, cup_externalProduct, integral_externalProduct]
  simp [pairY_eq]

end Stacks.WeilCohomology

end
