module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local rings of a fibre over a point whose local ring is a field

The scheme-theoretic fibre of `f : X ⟶ Y` over a point `y` is cut out by the maximal ideal of
`𝒪_{Y, y}`, so over a point whose local ring is already a field the fibre has the same local
rings as the source. This file records that, and the case the first paragraph of Stacks Tag
0BD7 uses: the generic point of an integral scheme, where the local ring is the function
field.

That paragraph reads a trivializing section of `ℒ` on the generic fibre `X_ξ` as a *meromorphic*
section of `ℒ` on `X`. For an integral `X` a meromorphic section is a germ at the generic point
of `X`, which lies over `ξ`, so the step needs exactly the identification below: the canonical
map `𝒪_{X, x} ⟶ 𝒪_{X_ξ, x}` is an isomorphism for every point `x` of the generic fibre.

The same presentation of the fibre's local ring as a quotient gives, with no hypothesis on the
target's local ring, that an *integral* fibre makes the extended maximal ideal prime — the
hypothesis the penultimate paragraph of the same tag needs, at the maximal ideal.

## Main definitions

* `AlgebraicGeometry.stalkEquivFiberStalk`: the local ring of the fibre through `x`, identified
  with the local ring of the source at `x`, when the local ring of the target at `f x` is a
  field.

## Main results

* `AlgebraicGeometry.stalkEquivFiberStalk_apply`: that identification is the canonical map on
  stalks, so it identifies the two rings canonically rather than merely abstractly.
* `AlgebraicGeometry.isIso_stalkMap_fiberι`: consequently the canonical map on stalks is an
  isomorphism.
* `AlgebraicGeometry.maximalIdeal_stalk_genericPoint_eq_bot`: the hypothesis is satisfied at the
  generic point of an integral scheme.
* `AlgebraicGeometry.isIso_stalkMap_fiberι_genericPoint`: hence the local rings of the generic
  fibre of a morphism to an integral scheme are the local rings of the source.
* `AlgebraicGeometry.isPrime_map_maximalIdeal_stalkMap_of_isIntegral_fiber`: over a point with
  integral fibre, the extension of the maximal ideal of `𝒪_{Y, f x}` to `𝒪_{X, x}` is prime.
* `AlgebraicGeometry.isPrime_map_algebraMap_maximalIdeal_of_isIntegral_fiber`: the same, written
  through the `Algebra` structure the stalk map induces, which is the spelling in which
  `Ideal.exists_isUnit_mul_eq_of_isUnit` asks for it.

## Implementation notes

`AlgebraicGeometry.quotientStalkEquivFiberStalk` presents the fibre's local ring as the quotient
of `𝒪_{X, x}` by the extension of the maximal ideal of `𝒪_{Y, f x}`, and
`AlgebraicGeometry.quotientStalkEquivFiberStalk_mk` says that presentation is induced by the
canonical stalk map. Both hold for an arbitrary morphism, so nothing here needs flatness, a
Noetherian hypothesis, or affineness: when that maximal ideal is `⊥` its extension is `⊥` by
`Ideal.map_bot` and the quotient disappears.

The hypothesis is stated as `IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)) = ⊥` rather than
as `IsField (Y.presheaf.stalk (f x))`, because that is the form in which it is used and because
it avoids carrying a second `Field` instance on a carrier that already has a `CommRing` one —
the two do not agree definitionally, and asserting the `Field` instance instead makes the
specialization below fail to elaborate.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
* [Stacks Project, Tag 0C0X](https://stacks.math.columbia.edu/tag/0C0X)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **The local ring of a fibre over a point whose local ring is a field.** The fibre is cut out
by the maximal ideal of the target's local ring, so when that ideal vanishes the fibre has the
local ring of the source at the same point. -/
noncomputable def stalkEquivFiberStalk {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (h : IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)) = ⊥) :
    X.presheaf.stalk x ≃+* (f.fiber (f x)).presheaf.stalk (f.asFiber x) :=
  (RingEquiv.quotientBot _).symm.trans
    ((Ideal.quotEquivOfEq (by rw [h, Ideal.map_bot])).trans
      (quotientStalkEquivFiberStalk f x))

/-- The identification of the fibre's local ring with the source's is the canonical map on
stalks, transported along `f.fiberι _ (f.asFiber x) = x`. -/
theorem stalkEquivFiberStalk_apply {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (h : IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)) = ⊥) (b : X.presheaf.stalk x) :
    stalkEquivFiberStalk f x h b =
      ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom
        ((X.presheaf.stalkCongr (.of_eq (f.fiberι_asFiber x).symm)).hom b) :=
  quotientStalkEquivFiberStalk_mk f x b

/-- The canonical map from a local ring of the source to the corresponding local ring of the
fibre is bijective, over a point whose local ring is a field. -/
theorem bijective_stalkMap_fiberι {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (h : IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)) = ⊥) :
    Function.Bijective ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom := by
  have hc : Function.Bijective
      ((X.presheaf.stalkCongr (.of_eq (f.fiberι_asFiber x).symm)).hom) :=
    ConcreteCategory.bijective_of_isIso _
  refine (Function.Bijective.of_comp_iff _ hc).mp ?_
  have he : (((f.fiberι (f x)).stalkMap (f.asFiber x)).hom ∘
      (X.presheaf.stalkCongr (.of_eq (f.fiberι_asFiber x).symm)).hom) =
      stalkEquivFiberStalk f x h :=
    funext fun b => (stalkEquivFiberStalk_apply f x h b).symm
  rw [he]
  exact (stalkEquivFiberStalk f x h).bijective

/-- The canonical map from a local ring of the source to the corresponding local ring of the
fibre is an isomorphism, over a point whose local ring is a field. -/
theorem isIso_stalkMap_fiberι {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (h : IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)) = ⊥) :
    IsIso ((f.fiberι (f x)).stalkMap (f.asFiber x)) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_stalkMap_fiberι f x h)

/-- The local ring of an integral scheme at its generic point is the function field, so its
maximal ideal vanishes. This witnesses the hypothesis of the results above. -/
@[ega "I 8.2.1" "partial"]
theorem maximalIdeal_stalk_genericPoint_eq_bot (Y : Scheme.{u}) [IsIntegral Y] :
    IsLocalRing.maximalIdeal (Y.presheaf.stalk (genericPoint Y)) = ⊥ := by
  let : Field (Y.presheaf.stalk (genericPoint Y)) :=
    (inferInstance : Field Y.functionField)
  exact IsLocalRing.maximalIdeal_eq_bot

/-- **The generic fibre has the local rings of the source.** For a morphism to an integral
scheme and a point of the source lying over the generic point of the target, the canonical map
from the local ring of the source to the local ring of the generic fibre is an isomorphism.
This is what lets the first paragraph of Stacks Tag 0BD7 read a trivializing section of the
generic fibre as a meromorphic section of the original module. -/
theorem isIso_stalkMap_fiberι_genericPoint {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral Y] (x : X)
    (hx : f.base x = genericPoint Y) :
    IsIso ((f.fiberι (f x)).stalkMap (f.asFiber x)) :=
  isIso_stalkMap_fiberι f x (by
    rw [show f x = genericPoint Y from hx]
    exact maximalIdeal_stalk_genericPoint_eq_bot Y)

/-- **An integral fibre makes the extended maximal ideal prime.** The fibre is cut out by the
maximal ideal of `𝒪_{Y, f x}`, so `𝒪_{X, x} ⧸ 𝔪_{f x} 𝒪_{X, x}` is the local ring of the fibre at
`x` (`AlgebraicGeometry.quotientStalkEquivFiberStalk`); if the fibre is integral that local ring
is a domain, and a quotient is a domain exactly when the ideal is prime.

This is the hypothesis `hprime` of `Ideal.exists_isUnit_mul_eq_of_isUnit` — the source's "by
assumption `𝔮ᵢ = 𝔭ᵢ A` is a prime" — **at the single prime `𝔭 = 𝔪_{f x}`**. That theorem needs it
at *every* prime of `𝒪_{Y, f x}`, and the primes other than the maximal one correspond to points
`y'` of `Y` with `f x` in their closure; for those the relevant ring is not the local ring of a
fibre but a localization of one, so this result does not reach them. -/
theorem isPrime_map_maximalIdeal_stalkMap_of_isIntegral_fiber {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) [IsIntegral (f.fiber (f x))] :
    (Ideal.map (f.stalkMap x).hom
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)))).IsPrime :=
  (Ideal.Quotient.isDomain_iff_prime _).mp
    ((quotientStalkEquivFiberStalk f x).toMulEquiv.isDomain _)

/-- `AlgebraicGeometry.isPrime_map_maximalIdeal_stalkMap_of_isIntegral_fiber` written through the
`Algebra` structure that the stalk map induces, which is the spelling the ring-theoretic results
of `StacksFrontier/AlgebraicGeometry/InvertiblePullbackFlat/StalkGenerator.lean` are stated at. The
two agree by `rfl`, `RingHom.toAlgebra` taking the given map as its `algebraMap`. -/
theorem isPrime_map_algebraMap_maximalIdeal_of_isIntegral_fiber {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) [IsIntegral (f.fiber (f x))] :
    letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    (Ideal.map (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x))
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)))).IsPrime :=
  isPrime_map_maximalIdeal_stalkMap_of_isIntegral_fiber f x

end AlgebraicGeometry

end
