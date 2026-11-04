module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.OpenComplementRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrimeDivisorIsoTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.HenselianLocalRingOfIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorCanonicalRatio
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Sober

/-!
# The order of vanishing along a prime divisor transported by an isomorphism of spaces

Let `e : X ≅ Y` be an isomorphism of decent algebraic spaces over a scheme `S` and let `Z` be a
prime divisor of `X`, with image the prime divisor
`AlgebraicGeometry.Space.PrimeDivisor.pushforwardOfIso` of `Y`. This file identifies the two
rings in which the order of vanishing along `Z` and along its image are read, and transports the
order of vanishing itself:

* the generic point of the image is the image of the generic point;
* the two henselian local rings `𝒪^h_{Y, e(ξ)}` and `𝒪^h_{X, ξ}` are isomorphic, and so are their
  total rings of fractions;
* the order of vanishing of a unit of `Q(𝒪^h_{Y, e(ξ)})` along the image of `Z` is the order of
  vanishing along `Z` of the unit of `Q(𝒪^h_{X, ξ})` it corresponds to.

## Main definitions

* `AlgebraicGeometry.Space.PrimeDivisor.genericHenselianLocalRingEquivOfIso`: the isomorphism
  `𝒪^h_{Y, e(ξ)} ≃+* 𝒪^h_{X, ξ}`.
* `AlgebraicGeometry.Space.PrimeDivisor.genericTotalFractionRingEquivOfIso`: the induced
  isomorphism of total rings of fractions.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.genericPoint_pushforwardOfIso`: the generic point of the
  image of a prime divisor along an isomorphism is the image of its generic point.
* `AlgebraicGeometry.Space.PrimeDivisor.ord_pushforwardOfIso`: the order of vanishing is carried
  by that isomorphism.
* `AlgebraicGeometry.Space.PrimeDivisor.ord_pushforwardOfIso_of_eq_unit_mul`: the same, with the
  two units compared only up to a unit of the henselian local ring.
* `AlgebraicGeometry.Space.orderOfVanishingSection_pushforwardOfIso_of_canonicalGenericRatio_eq`:
  the order of vanishing of a regular meromorphic section along the image of `Z` is that of a
  regular meromorphic section on `X` along `Z`, when their canonical ratios of Stacks 0EPR
  correspond up to a unit of the henselian local ring.

## References

* [Stacks Project, Tag 0EMY](https://stacks.math.columbia.edu/tag/0EMY)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EQE](https://stacks.math.columbia.edu/tag/0EQE)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The generic point of the image of a prime divisor -/

/-- **The generic point of the image of a prime divisor along an isomorphism is the image of its
generic point.** -/
theorem PrimeDivisor.genericPoint_pushforwardOfIso (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hYdec : IsDecentSpace B S hS Y) (e : X ≅ Y)
    (Z : PrimeDivisor B S hS X) :
    (Z.pushforwardOfIso B S hS hX hY hYdec e).genericPoint B S hS Y =
      pointsMap B S hS X e.hom (Z.genericPoint B S hS X) := by
  have : T0Space (points B S hS Y) := t0Space_points_of_isDecentSpace B S hS hY hYdec
  have himg := (Z.isGenericPoint_genericPoint B S hS X).image
    (continuous_pointsMap B S hS e.hom)
  have hclosed : IsClosed (pointsMap B S hS X e.hom '' Z.support B S hS X) :=
    (pointsHomeomorphOfIso B S hS e).isClosedMap _
      (Z.isGenericPoint_genericPoint B S hS X).isClosed
  rw [hclosed.closure_eq] at himg
  refine IsGenericPoint.eq
    ((Z.pushforwardOfIso B S hS hX hY hYdec e).isGenericPoint_genericPoint B S hS Y) ?_
  rwa [PrimeDivisor.support_pushforwardOfIso B S hS hX hY hYdec e Z]

/-! ### The henselian local ring and its total ring of fractions -/

/-- **The henselian local rings at the generic points of a prime divisor and of its image along
an isomorphism agree.** -/
def PrimeDivisor.genericHenselianLocalRingEquivOfIso (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hXdec : IsDecentSpace B S hS X)
    (hYdec : IsDecentSpace B S hS Y) (e : X ≅ Y) (Z : PrimeDivisor B S hS X) :
    ↥((Z.pushforwardOfIso B S hS hX hY hYdec e).genericHenselianLocalRing B S hS hY hYdec) ≃+*
      ↥(Z.genericHenselianLocalRing B S hS hX hXdec) :=
  henselianLocalRingEquivOfIsIso B S hS hX hY hXdec hYdec e.hom (Z.genericPoint B S hS X)
    ((Z.pushforwardOfIso B S hS hX hY hYdec e).genericPoint B S hS Y)
    (Z.genericPoint_pushforwardOfIso B S hS hX hY hYdec e).symm

/-- **The total rings of fractions of the henselian local rings at the generic points of a prime
divisor and of its image along an isomorphism agree**, through the isomorphism
`AlgebraicGeometry.Space.PrimeDivisor.genericHenselianLocalRingEquivOfIso`. -/
def PrimeDivisor.genericTotalFractionRingEquivOfIso (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hXdec : IsDecentSpace B S hS X)
    (hYdec : IsDecentSpace B S hS Y) (e : X ≅ Y) (Z : PrimeDivisor B S hS X) :
    (Z.pushforwardOfIso B S hS hX hY hYdec e).genericTotalFractionRing B S hS hY hYdec ≃+*
      Z.genericTotalFractionRing B S hS hX hXdec :=
  IsFractionRing.ringEquivOfRingEquiv
    (Z.genericHenselianLocalRingEquivOfIso B S hS hX hY hXdec hYdec e)

/-! ### The order of vanishing -/

variable (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXdec : IsDecentSpace B S hS X) (hYdec : IsDecentSpace B S hS Y) (e : X ≅ Y)
    (Z : PrimeDivisor B S hS X)

section Ord

variable [Nontrivial ↥(Z.genericHenselianLocalRing B S hS hX hXdec)]
    [IsNoetherianRing ↥(Z.genericHenselianLocalRing B S hS hX hXdec)]
    [Ring.KrullDimLE 1 ↥(Z.genericHenselianLocalRing B S hS hX hXdec)]
    [Nontrivial
      ↥((Z.pushforwardOfIso B S hS hX hY hYdec e).genericHenselianLocalRing B S hS hY hYdec)]
    [IsNoetherianRing
      ↥((Z.pushforwardOfIso B S hS hX hY hYdec e).genericHenselianLocalRing B S hS hY hYdec)]
    [Ring.KrullDimLE 1
      ↥((Z.pushforwardOfIso B S hS hX hY hYdec e).genericHenselianLocalRing B S hS hY hYdec)]

/-- **The order of vanishing along a prime divisor is carried by an isomorphism of spaces.** The
order of vanishing along the image of `Z` of a unit of `Q(𝒪^h_{Y, e(ξ)})` is the order of
vanishing along `Z` of the corresponding unit of `Q(𝒪^h_{X, ξ})`. -/
theorem PrimeDivisor.ord_pushforwardOfIso
    (f : (Z.pushforwardOfIso B S hS hX hY hYdec e).genericTotalFractionRing B S hS hY hYdec)
    (hf : IsUnit f) :
    (Z.pushforwardOfIso B S hS hX hY hYdec e).ord B S hS hY hYdec f hf =
      Z.ord B S hS hX hXdec
        (Z.genericTotalFractionRingEquivOfIso B S hS hX hY hXdec hYdec e f)
        (hf.map (Z.genericTotalFractionRingEquivOfIso B S hS hX hY hXdec hYdec e).toRingHom) :=
  PrimeDivisor.ord_ringEquiv B S hS hY hYdec (Z.pushforwardOfIso B S hS hX hY hYdec e) hX hXdec Z
    (Z.genericHenselianLocalRingEquivOfIso B S hS hX hY hXdec hYdec e) f hf

/-- **The order of vanishing is carried by an isomorphism of spaces up to a unit.** If the unit
of `Q(𝒪^h_{Y, e(ξ)})` corresponds to a unit of `𝒪^h_{X, ξ}` times a unit `g` of
`Q(𝒪^h_{X, ξ})`, the two orders of vanishing agree. -/
theorem PrimeDivisor.ord_pushforwardOfIso_of_eq_unit_mul
    (f : (Z.pushforwardOfIso B S hS hX hY hYdec e).genericTotalFractionRing B S hS hY hYdec)
    (hf : IsUnit f) (g : Z.genericTotalFractionRing B S hS hX hXdec) (hg : IsUnit g)
    {v : ↥(Z.genericHenselianLocalRing B S hS hX hXdec)} (hv : IsUnit v)
    (hfg : Z.genericTotalFractionRingEquivOfIso B S hS hX hY hXdec hYdec e f =
      algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hXdec)
          (Z.genericTotalFractionRing B S hS hX hXdec) v * g) :
    (Z.pushforwardOfIso B S hS hX hY hYdec e).ord B S hS hY hYdec f hf =
      Z.ord B S hS hX hXdec g hg := by
  have hvu : IsUnit (algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hXdec)
      (Z.genericTotalFractionRing B S hS hX hXdec) v) :=
    IsLocalization.map_units _ ⟨v, hv.mem_nonZeroDivisors⟩
  rw [Z.ord_pushforwardOfIso B S hS hX hY hXdec hYdec e f hf]
  refine Eq.trans (PrimeDivisor.ord_congr B S hS hX hXdec Z _ (hvu.mul hg) hfg) ?_
  rw [Z.ord_mul B S hS hX hXdec _ _ hvu hg,
    show Z.ord B S hS hX hXdec _ hvu = _ from
      PrimeDivisor.ord_congr B S hS hX hXdec Z hvu hvu rfl,
    Z.ord_algebraMap B S hS hX hXdec v hv.mem_nonZeroDivisors, Ring.ord_of_isUnit hv]
  simp

end Ord

/-! ### The order of vanishing of a meromorphic section -/

variable (hXint : IsIntegralSpace B S hS X) (hYint : IsIntegralSpace B S hS Y)
    (hXN : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (hYN : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))

/-- The order of vanishing of a regular meromorphic section against its canonical local ratio is
the order of vanishing of its canonical generic ratio. -/
private theorem orderOfVanishingSection_canonicalLocalRatio_eq_ord
    [∀ W : PrimeDivisor B S hS X, Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hXdec)]
    [∀ W : PrimeDivisor B S hS X, IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hXdec)]
    [∀ W : PrimeDivisor B S hS X, Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hXdec)]
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (σ : MeromorphicSection.{u, u} B S hS X hX L)
    (hσ : IsRegularMeromorphicSection.{u, u} B S hS X hX L σ) :
    orderOfVanishingSection.{u, u} B S hS hX hXdec Z L σ
        (Z.canonicalLocalRatio B S hS hX hXdec L hL hXint hXN) =
      Z.ord B S hS hX hXdec (Z.canonicalGenericRatio B S hS hX hXdec L hL hXint hXN σ)
        (Z.isUnit_canonicalGenericRatio B S hS hX hXdec L hL hXint hXN σ hσ) :=
  PrimeDivisor.ord_congr B S hS hX hXdec Z _ _
    (Z.coe_canonicalLocalRatio B S hS hX hXdec L hL hXint hXN σ hσ)

include hXint hYint hXN hYN in
/-- **The order of vanishing of a meromorphic section is carried by an isomorphism of spaces,
given the comparison of the canonical ratios of Stacks 0EPR.** Let `e : X ≅ Y` be an
isomorphism of decent, locally Noetherian, integral algebraic spaces over `S`, let `Z` be a prime
divisor of `X`, let `σ` be a regular meromorphic section of an invertible module on `X` and `τ`
one of an invertible module on `Y`. If the canonical ratio `τ / s_{e(ξ)}` corresponds, under the
isomorphism of total rings of fractions of the henselian local rings, to a unit of `𝒪^h_{X, ξ}`
times the canonical ratio `σ / s_ξ`, then `ord` of `τ` along the image of `Z` is `ord` of `σ`
along `Z`. -/
theorem orderOfVanishingSection_pushforwardOfIso_of_canonicalGenericRatio_eq
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (M : Modules.{u, u} B S hS Y hY) (hM : IsInvertibleModule (B := B) ⟨Y, hY⟩ M)
    (σ : MeromorphicSection.{u, u} B S hS X hX L)
    (hσ : IsRegularMeromorphicSection.{u, u} B S hS X hX L σ)
    (τ : MeromorphicSection.{u, u} B S hS Y hY M)
    (hτ : IsRegularMeromorphicSection.{u, u} B S hS Y hY M τ)
    {v : ↥(Z.genericHenselianLocalRing B S hS hX hXdec)} (hv : IsUnit v)
    (hratio : Z.genericTotalFractionRingEquivOfIso B S hS hX hY hXdec hYdec e
          ((Z.pushforwardOfIso B S hS hX hY hYdec e).canonicalGenericRatio B S hS hY hYdec M hM
            hYint hYN τ) =
        algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hXdec)
            (Z.genericTotalFractionRing B S hS hX hXdec) v *
          Z.canonicalGenericRatio B S hS hX hXdec L hL hXint hXN σ) :
    haveI : ∀ W : PrimeDivisor B S hS X,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hXdec) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS hX hXdec hXint hXN
    haveI : ∀ W : PrimeDivisor B S hS X,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hXdec) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS hX hXdec hXint hXN
    haveI : ∀ W : PrimeDivisor B S hS X,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hXdec) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS hX hXdec hXint hXN
    haveI : ∀ W : PrimeDivisor B S hS Y,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS hY hYdec) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS hY hYdec hYint hYN
    haveI : ∀ W : PrimeDivisor B S hS Y,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hY hYdec) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS hY hYdec hYint hYN
    haveI : ∀ W : PrimeDivisor B S hS Y,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hY hYdec) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS hY hYdec hYint hYN
    orderOfVanishingSection.{u, u} B S hS hY hYdec
          (Z.pushforwardOfIso B S hS hX hY hYdec e) M τ
          ((Z.pushforwardOfIso B S hS hX hY hYdec e).canonicalLocalRatio B S hS hY hYdec M hM
            hYint hYN) =
      orderOfVanishingSection.{u, u} B S hS hX hXdec Z L σ
        (Z.canonicalLocalRatio B S hS hX hXdec L hL hXint hXN) := by
  have : ∀ W : PrimeDivisor B S hS X,
      Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hXdec) := fun W =>
    W.nontrivial_genericHenselianLocalRing B S hS hX hXdec hXint hXN
  have : ∀ W : PrimeDivisor B S hS X,
      IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hXdec) := fun W =>
    W.isNoetherianRing_genericHenselianLocalRing B S hS hX hXdec hXint hXN
  have : ∀ W : PrimeDivisor B S hS X,
      Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hXdec) := fun W =>
    W.krullDimLE_genericHenselianLocalRing B S hS hX hXdec hXint hXN
  have : ∀ W : PrimeDivisor B S hS Y,
      Nontrivial ↥(W.genericHenselianLocalRing B S hS hY hYdec) := fun W =>
    W.nontrivial_genericHenselianLocalRing B S hS hY hYdec hYint hYN
  have : ∀ W : PrimeDivisor B S hS Y,
      IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hY hYdec) := fun W =>
    W.isNoetherianRing_genericHenselianLocalRing B S hS hY hYdec hYint hYN
  have : ∀ W : PrimeDivisor B S hS Y,
      Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hY hYdec) := fun W =>
    W.krullDimLE_genericHenselianLocalRing B S hS hY hYdec hYint hYN
  set P := Z.pushforwardOfIso B S hS hX hY hYdec e with hP
  rw [orderOfVanishingSection_canonicalLocalRatio_eq_ord B S hS hY hYdec P hYint hYN M hM τ hτ,
    orderOfVanishingSection_canonicalLocalRatio_eq_ord B S hS hX hXdec Z hXint hXN L hL σ hσ]
  exact Z.ord_pushforwardOfIso_of_eq_unit_mul B S hS hX hY hXdec hYdec e _ _ _ _ hv hratio

end AlgebraicGeometry.Space

end
