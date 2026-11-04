module

public import StacksFrontier.AlgebraicGeometry.Chow.DivisorTransport.Order
public import StacksFrontier.AlgebraicGeometry.Chow.RationalFunctions.FunctionField
public import StacksFrontier.AlgebraicGeometry.Chow.Vocabulary.PrincipalCycle

/-!
# Transporting divisor theory along an isomorphism of schemes

Chapter 42 of the Stacks Project attaches to a locally Noetherian integral scheme `V` its ring of
rational functions `R(V)`, the order of vanishing `ord_z` of a rational function at a point `z`
of codimension one, and the principal divisor `div(f) = ∑_z ord_z(f) [z]`. All three are
isomorphism invariants, and this file says so.

The content is the invariance of the order of vanishing
(`Stacks.Chow.ord_functionFieldRingEquivOfIso`); the rest is bookkeeping. On top of it this file
puts the two statements that a user of chapter 42 actually wants: the transport of the ring of
rational functions of Stacks 01RU, and the naturality of the principal divisor as an algebraic
cycle, that is, that the weighted pushforward `AlgebraicGeometry.AlgebraicCycle.map` along an
isomorphism carries `div(f)` to `div` of the transported function. Pushing forward along an
isomorphism introduces no multiplicity: the fibre over a point is a single point, the residue
field extension is trivial, and the only hypothesis left is that the two weight functions agree
under the isomorphism — which they do in every intended use, the weights being a relative
dimension over a common base.

The transport of `Stacks.Chow.rationalFunctions` is obtained from the transport of the function
field through Stacks 01RU's identification `R(V) ≃+* R(V)` of the ring of rational functions of an
integral scheme with its function field, `Stacks.Chow.rationalFunctionsEquivFunctionField`; for an
integral scheme the two rings are canonically isomorphic, so nothing is lost, and the resulting
`RingEquiv` is characterised by
`Stacks.Chow.rationalFunctionsEquivFunctionField_rationalFunctionsRingEquivOfIso`.

## Main definitions

* `Stacks.Chow.rationalFunctionsRingEquivOfIso` — the transport `R(V) ≃+* R(W)` of the ring of
  rational functions along an isomorphism of integral schemes, and
  `Stacks.Chow.rationalFunctionsUnitsMulEquivOfIso` its restriction to the units.

## Main results

* `Stacks.Chow.residueDegree_eq_one_of_iso` — an isomorphism has residue degree one.
* `Stacks.Chow.principalCycle_functionFieldRingEquivOfIso_apply` — the coefficientwise
  invariance of the principal divisor.
* `Stacks.Chow.map_principalCycle_of_iso` — the naturality of the principal divisor under the
  weighted pushforward of cycles along an isomorphism.
* `Stacks.Chow.map_principalCycle_rationalFunctions_of_iso` — the same, stated for a rational
  function in the sense of Stacks 01RU.

## References

* [Stacks Project, Tag 01RU](https://stacks.math.columbia.edu/tag/01RU)
* [Stacks Project, Tag 02RL](https://stacks.math.columbia.edu/tag/02RL)
* [Stacks Project, Tag 0BE3](https://stacks.math.columbia.edu/tag/0BE3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

universe u

namespace Stacks.Chow

variable {V W : Scheme.{u}}

/-! ### Rational functions -/

/-- The transport of the ring of rational functions of Stacks 01RU along an isomorphism of
integral schemes, through the identification of `R(V)` with the function field of `V`. -/
def rationalFunctionsRingEquivOfIso (φ : V ≅ W) [IsIntegral V] [IsIntegral W] :
    rationalFunctions V ≃+* rationalFunctions W :=
  ((rationalFunctionsEquivFunctionField V).1.trans (functionFieldRingEquivOfIso φ)).trans
    (rationalFunctionsEquivFunctionField W).1.symm

/-- `Stacks.Chow.rationalFunctionsRingEquivOfIso` is, by construction, the transport of the
function field read through Stacks 01RU's identification of `R(V)` with the function field. -/
@[simp]
theorem rationalFunctionsEquivFunctionField_rationalFunctionsRingEquivOfIso (φ : V ≅ W)
    [IsIntegral V] [IsIntegral W] (g : rationalFunctions V) :
    (rationalFunctionsEquivFunctionField W).1 (rationalFunctionsRingEquivOfIso φ g) =
      functionFieldRingEquivOfIso φ ((rationalFunctionsEquivFunctionField V).1 g) := by
  simp [rationalFunctionsRingEquivOfIso]

/-- The transport of the units of the ring of rational functions — the nonzero rational functions
of Stacks 02RL — along an isomorphism of integral schemes. -/
def rationalFunctionsUnitsMulEquivOfIso (φ : V ≅ W) [IsIntegral V] [IsIntegral W] :
    (rationalFunctions V)ˣ ≃* (rationalFunctions W)ˣ :=
  Units.mapEquiv (rationalFunctionsRingEquivOfIso φ).toMulEquiv

/-- The underlying rational function of the transport of a unit is the transport of its
underlying rational function. -/
@[simp]
theorem rationalFunctionsUnitsMulEquivOfIso_coe (φ : V ≅ W) [IsIntegral V] [IsIntegral W]
    (g : (rationalFunctions V)ˣ) :
    ((rationalFunctionsUnitsMulEquivOfIso φ g : rationalFunctions W)) =
      rationalFunctionsRingEquivOfIso φ (g : rationalFunctions V) :=
  rfl

/-! ### Residue degree and fibres of an isomorphism -/

/-- An isomorphism of schemes has residue degree one at every point: it induces an isomorphism of
residue fields. -/
theorem residueDegree_eq_one_of_iso (φ : V ≅ W) (z : V) : φ.hom.residueDegree z = 1 := by
  have hb : Function.Bijective (φ.hom.residueFieldMap z) :=
    ConcreteCategory.bijective_of_isIso (C := CommRingCat) (φ.hom.residueFieldMap z)
  let _ := (φ.hom.residueFieldMap z).hom.toAlgebra
  show Module.finrank (W.residueField (φ.hom.base z)) (V.residueField z) = 1
  exact Module.finrank_of_bijective_algebraMap hb

/-- The fibre of an isomorphism over a point is the single preimage point. -/
theorem preimage_singleton_of_iso (φ : V ≅ W) (y : W) :
    φ.hom.base ⁻¹' {y} = {φ.inv.base y} := by
  ext x
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · have : φ.inv.base (φ.hom.base x) = x := Scheme.hom_inv_apply φ x
    rw [Set.mem_singleton_iff, ← this, Set.mem_preimage.mp hx]
  · rw [Set.mem_preimage, Set.mem_singleton_iff.mp hx, Scheme.inv_hom_apply,
      Set.mem_singleton_iff]

/-! ### The principal divisor -/

variable [IsIntegral V] [IsIntegral W] [IsLocallyNoetherian V] [IsLocallyNoetherian W]

/-- The coefficient of the principal divisor of a rational function at a point is unchanged by
transporting the function and the point along an isomorphism. -/
theorem principalCycle_functionFieldRingEquivOfIso_apply (φ : V ≅ W) (f : V.functionField)
    (z : V) :
    principalCycle W (functionFieldRingEquivOfIso φ f) (φ.hom.base z) = principalCycle V f z := by
  rw [principalCycle_apply, principalCycle_apply, ord_functionFieldRingEquivOfIso]

/-- **Naturality of the principal divisor.** The weighted pushforward of cycles along an
isomorphism `φ : V ≅ W` of locally Noetherian integral schemes carries the principal divisor of a
rational function `f` to the principal divisor of the transported rational function, as soon as
the two weight functions agree under `φ`. -/
theorem map_principalCycle_of_iso (φ : V ≅ W) (wv : V → ℤ) (ww : W → ℤ)
    (hw : ∀ z : V, wv z = ww (φ.hom.base z)) (f : V.functionField) :
    AlgebraicCycle.map φ.hom wv ww (principalCycle V f) =
      principalCycle W (functionFieldRingEquivOfIso φ f) := by
  apply Function.locallyFinsuppWithin.ext
  intro y
  have hweight : (AlgebraicCycle.mapCoeff φ.hom wv ww (φ.inv.base y) : ℤ) = 1 := by
    simp [AlgebraicCycle.mapCoeff, hw (φ.inv.base y), residueDegree_eq_one_of_iso]
  show (∑ᶠ x ∈ φ.hom.base ⁻¹' {y}, principalCycle V f x *
    (AlgebraicCycle.mapCoeff φ.hom wv ww x : ℤ)) = _
  rw [preimage_singleton_of_iso, finsum_mem_singleton, hweight, mul_one,
    ← principalCycle_functionFieldRingEquivOfIso_apply φ f (φ.inv.base y),
    Scheme.inv_hom_apply]

/-- **Naturality of the principal divisor, for a rational function in the sense of Stacks
01RU.** -/
theorem map_principalCycle_rationalFunctions_of_iso (φ : V ≅ W) (wv : V → ℤ) (ww : W → ℤ)
    (hw : ∀ z : V, wv z = ww (φ.hom.base z)) (g : rationalFunctions V) :
    AlgebraicCycle.map φ.hom wv ww
        (principalCycle V ((rationalFunctionsEquivFunctionField V).1 g)) =
      principalCycle W ((rationalFunctionsEquivFunctionField W).1
        (rationalFunctionsRingEquivOfIso φ g)) := by
  rw [rationalFunctionsEquivFunctionField_rationalFunctionsRingEquivOfIso]
  exact map_principalCycle_of_iso φ wv ww hw _

end Stacks.Chow

end
