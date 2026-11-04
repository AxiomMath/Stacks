module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceCycleTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.InvertibleSheafDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.HenselianLocalRingIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorFunctionFieldChartIndependence
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.OrderOfVanishingIso
public import StacksFrontier.AlgebraicGeometry.Spaces.RationalFunctionsIso
public import StacksFrontier.Topology.Dimension.CodimensionHomeomorph

/-!
# Orders of vanishing and principal divisors along an isomorphism

Let `e : X ≅ X'` be an isomorphism of decent algebraic spaces over `S`. It matches the integral
closed subspaces of `X` and of `X'` (`AlgebraicGeometry.Space.IntegralClosedSubspace.equivOfIso`),
and since it is a homeomorphism on points it preserves codimension, hence matches prime
divisors and their generic points. At a prime divisor `Z` with generic point `ξ` and its image
`Z'` with generic point `ξ' = e(ξ)`, the isomorphism `𝒪^h_{X, ξ} ≅ 𝒪^h_{X', ξ'}` of henselian
local rings (`AlgebraicGeometry.Space.henselianLocalRingEquivOfIso`) extends to the total rings
of fractions, and the order of vanishing of Stacks 0ENL is an invariant of the ring, so

`ord_{Z'}(σ(f)) = ord_Z(f)`.

For an integral, locally Noetherian `X` the canonical embedding `R(X) → Q(𝒪^h_{X, ξ})` of
Stacks 0ENK is compatible with these isomorphisms and with the transport
`e_* : R(X) → R(X')` of rational functions: both are read on an elementary étale neighbourhood,
the neighbourhood of `ξ` composed with `e` is one of `ξ'`, and the embedding does not depend on
the neighbourhood. Hence `e` carries the principal divisor `div(f)` of Stacks 0EQ6, at the
canonical embeddings, to `div(e_* f)`:

`e_*(div(f)) = div(e_* f)`.

## Main results

* `AlgebraicGeometry.Space.IntegralClosedSubspace.codimension_equivOfIso`: codimension is
  preserved.
* `AlgebraicGeometry.Space.PrimeDivisor.ord_totalFracRingEquiv`: the order of vanishing along
  matched prime divisors.
* `AlgebraicGeometry.Space.PrimeDivisor.rationalFunctionsToGenericTotalFractionRing_mapIso`: the
  canonical embedding of Stacks 0ENK is compatible with the transport.
* `AlgebraicGeometry.Space.principalDivisorCycleCoefficients_equivOfIso`: the coefficients of
  `div(f)` along an isomorphism, for any compatible families of embeddings.
* `AlgebraicGeometry.Space.divisorCycleCoefficients_equivOfIso`: the coefficients of
  `div_ℒ(s)` of Stacks 0EQE along an isomorphism, for compatible ratio data of Stacks 0EPR.
* `AlgebraicGeometry.Space.divisorCycleCoefficients_equivOfIso_of_orderOfVanishingSection_eq`:
  the same, from equality of the orders of vanishing along matched prime divisors.
* `AlgebraicGeometry.Space.cycleClosedPushforward_principalDivisorCycleCoefficients_of_iso`:
  `e_*(div(f)) = div(e_* f)` at the canonical embeddings.
* `AlgebraicGeometry.Space.cycleClosedPushforward_principalDivisorCycleCoefficients_image`:
  for a closed immersion `j : T → X` and an integral closed subspace `V ⊆ T`, the pushforward to
  `X` of `div(f)` on `V` is the pushforward of `div(φ_* f)` on the image `j(V) ⊆ X`, so principal
  divisors on integral closed subspaces of `T` are principal divisors on integral closed
  subspaces of `X`.

## References

* [Stacks Project, Tag 0BGW](https://stacks.math.columbia.edu/tag/0BGW)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0ENL](https://stacks.math.columbia.edu/tag/0ENL)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u z

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section PrimeDivisor

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hX' : IsAlgebraicSpace B S hS X') (hdec : IsDecentSpace B S hS X)
    (hdec' : IsDecentSpace B S hS X') (e : X ≅ X')

/-- **An isomorphism preserves the codimension of integral closed subspaces.** -/
theorem IntegralClosedSubspace.codimension_equivOfIso (Z : IntegralClosedSubspace B S hS X) :
    codimension (integralClosedSubspaceSupport B S hS hX'
        (IntegralClosedSubspace.equivOfIso _ _ _ hX hX' hdec hdec' e Z)) =
      codimension (integralClosedSubspaceSupport B S hS hX Z) := by
  have h : integralClosedSubspaceSupport B S hS hX'
      (IntegralClosedSubspace.equivOfIso _ _ _ hX hX' hdec hdec' e Z) =
      IrreducibleCloseds.orderIsoOfHomeomorph (pointsHomeomorphOfIso B S hS e)
        (integralClosedSubspaceSupport B S hS hX Z) := by
    refine IrreducibleCloseds.ext ?_
    show subspacePointSet B S hS X' _ = _
    rw [IntegralClosedSubspace.subspacePointSet_equivOfIso,
      IrreducibleCloseds.coe_orderIsoOfHomeomorph]
    rfl
  rw [h, codimension_orderIsoOfHomeomorph]

include hX hdec in
/-- The generic point of a prime divisor is any generic point of its support. -/
theorem PrimeDivisor.genericPoint_eq_of_isGenericPoint (P : PrimeDivisor B S hS X)
    {x : points B S hS X} (hx : IsGenericPoint x (P.support B S hS X)) :
    P.genericPoint B S hS X = x := by
  have : T0Space (points B S hS X) := t0Space_points_of_isDecentSpace B S hS hX hdec
  exact (P.isGenericPoint_genericPoint B S hS X).eq hx

/-- The generic point of the prime divisor on the image of an integral closed subspace of
codimension one is the image of the generic point. -/
theorem IntegralClosedSubspace.genericPoint_toPrimeDivisor_equivOfIso
    (Z : IntegralClosedSubspace B S hS X)
    (h : codimension (integralClosedSubspaceSupport B S hS hX Z) = 1)
    (h' : codimension (integralClosedSubspaceSupport B S hS hX'
      (IntegralClosedSubspace.equivOfIso _ _ _ hX hX' hdec hdec' e Z)) = 1) :
    pointsMap B S hS X e.hom ((Z.toPrimeDivisor B S hS hX h).genericPoint B S hS X) =
      ((IntegralClosedSubspace.equivOfIso _ _ _ hX hX' hdec hdec' e Z).toPrimeDivisor B S hS hX'
        h').genericPoint B S hS X' := by
  refine (PrimeDivisor.genericPoint_eq_of_isGenericPoint hX' hdec' _ ?_).symm
  have hgen := ((Z.toPrimeDivisor B S hS hX h).isGenericPoint_genericPoint B S hS X).image
    (continuous_pointsMap B S hS e.hom)
  change IsGenericPoint _ (closure (pointsMap B S hS X e.hom ''
    subspacePointSet B S hS X Z.subspace)) at hgen
  show IsGenericPoint _ (subspacePointSet B S hS X'
    (IntegralClosedSubspace.equivOfIso _ _ _ hX hX' hdec hdec' e Z).subspace)
  rw [IntegralClosedSubspace.subspacePointSet_equivOfIso]
  have hcl : IsClosed (pointsMap B S hS X e.hom '' subspacePointSet B S hS X Z.subspace) :=
    (pointsHomeomorphOfIso B S hS e).isClosedMap _
      (isClosed_range_pointsMap_integralClosedSubspace B S hS hX Z)
  rwa [hcl.closure_eq] at hgen

/-- A function defined by cases on codimension one agrees at `Z` and at its image under `e`,
given agreement at the matched prime divisors. -/
private theorem dite_codimension_equivOfIso (Z : IntegralClosedSubspace B S hS X)
    {a : codimension (integralClosedSubspaceSupport B S hS hX Z) = 1 → ℤ}
    {a' : codimension (integralClosedSubspaceSupport B S hS hX'
      (IntegralClosedSubspace.equivOfIso _ _ _ hX hX' hdec hdec' e Z)) = 1 → ℤ}
    (H : ∀ (h : codimension (integralClosedSubspaceSupport B S hS hX Z) = 1)
      (h' : codimension (integralClosedSubspaceSupport B S hS hX'
        (IntegralClosedSubspace.equivOfIso _ _ _ hX hX' hdec hdec' e Z)) = 1),
      pointsMap B S hS X e.hom ((Z.toPrimeDivisor B S hS hX h).genericPoint B S hS X) =
        ((IntegralClosedSubspace.equivOfIso _ _ _ hX hX' hdec hdec' e Z).toPrimeDivisor B S hS
          hX' h').genericPoint B S hS X' → a' h' = a h) :
    (if h' : codimension (integralClosedSubspaceSupport B S hS hX'
        (IntegralClosedSubspace.equivOfIso _ _ _ hX hX' hdec hdec' e Z)) = 1 then a' h' else 0) =
      if h : codimension (integralClosedSubspaceSupport B S hS hX Z) = 1 then a h else 0 := by
  have hcod := IntegralClosedSubspace.codimension_equivOfIso hX hX' hdec hdec' e Z
  by_cases h : codimension (integralClosedSubspaceSupport B S hS hX Z) = 1
  · have h' := hcod.trans h
    rw [dif_pos h', dif_pos h]
    exact H h h' (IntegralClosedSubspace.genericPoint_toPrimeDivisor_equivOfIso hX hX' hdec
      hdec' e Z h h')
  · rw [dif_neg (hcod ▸ h), dif_neg h]

/-- **The order of vanishing along matched prime divisors.** Let `P` be a prime divisor of `X`
and `P'` one of `X'` whose generic point is the image of that of `P`. Under the isomorphism of
total rings of fractions of the henselian local rings at the generic points induced by `e`, the
order of vanishing along `P'` is the order of vanishing along `P`. -/
theorem PrimeDivisor.ord_totalFracRingEquiv (P : PrimeDivisor B S hS X)
    (P' : PrimeDivisor B S hS X')
    (hP : pointsMap B S hS X e.hom (P.genericPoint B S hS X) = P'.genericPoint B S hS X')
    [Nontrivial ↥(P.genericHenselianLocalRing B S hS hX hdec)]
    [IsNoetherianRing ↥(P.genericHenselianLocalRing B S hS hX hdec)]
    [Ring.KrullDimLE 1 ↥(P.genericHenselianLocalRing B S hS hX hdec)]
    [Nontrivial ↥(P'.genericHenselianLocalRing B S hS hX' hdec')]
    [IsNoetherianRing ↥(P'.genericHenselianLocalRing B S hS hX' hdec')]
    [Ring.KrullDimLE 1 ↥(P'.genericHenselianLocalRing B S hS hX' hdec')]
    (f : P.genericTotalFractionRing B S hS hX hdec) (hf : IsUnit f)
    (hf' : IsUnit (Ring.totalFracRingEquiv (henselianLocalRingEquivOfIso hdec hdec' e hP)
      (K' := P'.genericTotalFractionRing B S hS hX' hdec') f)) :
    P'.ord B S hS hX' hdec' (Ring.totalFracRingEquiv (henselianLocalRingEquivOfIso hdec hdec' e hP)
        (K' := P'.genericTotalFractionRing B S hS hX' hdec') f) hf' =
      P.ord B S hS hX hdec f hf :=
  Ring.ordTotalFracInt_ringEquiv _ f hf hf'

/-- The canonical image in the henselian local ring of a section of an elementary étale
neighbourhood of the generic point of a prime divisor is its image under the canonical section
homomorphism. -/
theorem PrimeDivisor.neighborhoodSectionsToGenericHenselianLocalRing_eq_sectionHom
    (P : PrimeDivisor B S hS X)
    (U : ElementaryEtaleNeighborhood B S hS X hX (P.genericPoint B S hS X))
    (s : Γ(U.scheme.left.1, ⊤)) :
    P.neighborhoodSectionsToGenericHenselianLocalRing B S hS hX hdec U s =
      sectionHom B S hS X hX (P.genericPoint B S hS X) hdec (op U) s :=
  (stalkToHenselianLocalRing_openGerm B S hS X hX _ hdec U ⊤ (by simp) s).trans
    (openRestrictionSectionHom_top B S hS X hX _ hdec U s)

/-- **The canonical embedding of Stacks 0ENK along an isomorphism.** Let `X` and `X'` be decent,
locally Noetherian, integral algebraic spaces and `e : X ≅ X'`, and let `P`, `P'` be prime
divisors with `e(ξ_P) = ξ_{P'}`. Then the canonical embedding at `P'` of the transported
rational function `e_* f` is the image of the canonical embedding at `P` of `f` under the
isomorphism of total rings of fractions induced by `e`. -/
theorem PrimeDivisor.rationalFunctionsToGenericTotalFractionRing_mapIso
    (hInt : IsIntegralSpace B S hS X) (hInt' : IsIntegralSpace B S hS X')
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    (hN' : HasEtaleLocalProperty B S hS X' (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    (P : PrimeDivisor B S hS X) (P' : PrimeDivisor B S hS X')
    (hP : pointsMap B S hS X e.hom (P.genericPoint B S hS X) = P'.genericPoint B S hS X')
    (r : rationalFunctions B S hS hX) :
    P'.rationalFunctionsToGenericTotalFractionRing B S hS hX' hdec' hInt' hN'
        (rationalFunctionsMapIso hX' e r) =
      Ring.totalFracRingEquiv (henselianLocalRingEquivOfIso hdec hdec' e hP)
        (K' := P'.genericTotalFractionRing B S hS hX' hdec')
        (P.rationalFunctionsToGenericTotalFractionRing B S hS hX hdec hInt hN r) := by
  have : IsLocalRing ↥(P.genericHenselianLocalRing B S hS hX hdec) :=
    henselianLocalRing_isLocalRing B S hS X hX _ hdec
  have : IsLocalRing ↥(P'.genericHenselianLocalRing B S hS hX' hdec') :=
    henselianLocalRing_isLocalRing B S hS X' hX' _ hdec'
  let U := P.genericChart B S hS hX hdec
  let U' : ElementaryEtaleNeighborhood B S hS X' hX' (P'.genericPoint B S hS X') :=
    ElementaryEtaleNeighborhood.mapIso e hP U
  have : IsAffine U.scheme.left.1 := P.isAffine_genericChart B S hS hX hdec
  have : IsReduced U.scheme.left.1 := P.isReduced_chart B S hS hX hInt U
  have : IsLocallyNoetherian U.scheme.left.1 := P.isLocallyNoetherian_chart B S hS hX hN U
  have : IsAffine U'.scheme.left.1 := P.isAffine_genericChart B S hS hX hdec
  have : IsReduced U'.scheme.left.1 := P.isReduced_chart B S hS hX hInt U
  have : IsLocallyNoetherian U'.scheme.left.1 := P.isLocallyNoetherian_chart B S hS hX hN U
  have hCof := ElementaryEtaleNeighborhood.isCofiltered_of_nonempty B S hS X hX
    (P.genericPoint B S hS X) ⟨U⟩
  have hCof' := ElementaryEtaleNeighborhood.isCofiltered_of_nonempty B S hS X' hX'
    (P'.genericPoint B S hS X') ⟨U'⟩
  have key : P'.neighborhoodTotalFractionRingToGeneric B S hS hX' hdec' U' hCof' =
      (Ring.totalFracRingEquiv (henselianLocalRingEquivOfIso hdec hdec' e hP)
        (K' := P'.genericTotalFractionRing B S hS hX' hdec')).toRingHom.comp
        (P.neighborhoodTotalFractionRingToGeneric B S hS hX hdec U hCof) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors Γ(U'.scheme.left.1, ⊤))
      (RingHom.ext fun a => ?_)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [PrimeDivisor.neighborhoodTotalFractionRingToGeneric,
      PrimeDivisor.neighborhoodTotalFractionRingToGeneric, IsLocalization.map_eq,
      IsLocalization.map_eq, Ring.totalFracRingEquiv, IsLocalization.ringEquivOfRingEquiv_eq,
      PrimeDivisor.neighborhoodSectionsToGenericHenselianLocalRing_eq_sectionHom,
      PrimeDivisor.neighborhoodSectionsToGenericHenselianLocalRing_eq_sectionHom]
    exact congrArg (algebraMap _ _)
      (henselianLocalRingEquivOfIso_sectionHom hdec hdec' e hP (op U) a).symm
  calc P'.rationalFunctionsToGenericTotalFractionRing B S hS hX' hdec' hInt' hN'
        (rationalFunctionsMapIso hX' e r)
      = P'.neighborhoodTotalFractionRingToGeneric B S hS hX' hdec' U' hCof'
          (rationalFunctionsToTotalFractionRing B S hS hX' U'.scheme U'.toSpace
            U'.etale_toSpace (rationalFunctionsMapIso hX' e r)) :=
        (P'.neighborhoodTotalFractionRingToGeneric_pullback_eq B S hS hX' hdec' hInt' hN' U'
          hCof' _).symm
    _ = P'.neighborhoodTotalFractionRingToGeneric B S hS hX' hdec' U' hCof'
          (rationalFunctionsToTotalFractionRing B S hS hX U.scheme U.toSpace
            U.etale_toSpace r) :=
        congrArg _ (rationalFunctionsToTotalFractionRing_rationalFunctionsMapIso hX' e U'.scheme
          U.toSpace U.etale_toSpace U'.toSpace U'.etale_toSpace rfl r)
    _ = _ := by
        rw [key, ← P.neighborhoodTotalFractionRingToGeneric_pullback_eq B S hS hX hdec hInt hN U
          hCof r]
        rfl

end PrimeDivisor

/-! ### Principal divisors -/

section PrincipalDivisor

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sX' : X' ⟶ D.space) (hX' : D.IsGood sX')
    (hdec : IsDecentSpace D.site D.base D.base_mem X)
    (hdec' : IsDecentSpace D.site D.base D.base_mem X') (e : X ≅ X')

/-- **The coefficients of `div(f)` along an isomorphism.** Let `emb` and `emb'` be families of
embeddings of `R(X)` and of `R(X')` into the total rings of fractions of the henselian local
rings at the generic points of prime divisors, and let `f ∈ R(X)` and `f' ∈ R(X')` be such that,
at any two prime divisors matched by `e`, the image of `f'` is the image of `f` under the
isomorphism of total rings of fractions induced by `e`. Then the coefficient of `div(f')` at the
image of an integral closed subspace `Z ⊆ X` is the coefficient of `div(f)` at `Z`. -/
theorem principalDivisorCycleCoefficients_equivOfIso
    [∀ W : PrimeDivisor D.site D.base D.base_mem X,
      Nontrivial ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdec)]
    [∀ W : PrimeDivisor D.site D.base D.base_mem X,
      IsNoetherianRing ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdec)]
    [∀ W : PrimeDivisor D.site D.base D.base_mem X,
      Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdec)]
    [∀ W : PrimeDivisor D.site D.base D.base_mem X',
      Nontrivial ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX'.1 hdec')]
    [∀ W : PrimeDivisor D.site D.base D.base_mem X',
      IsNoetherianRing ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX'.1 hdec')]
    [∀ W : PrimeDivisor D.site D.base D.base_mem X',
      Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX'.1 hdec')]
    (emb : ∀ W : PrimeDivisor D.site D.base D.base_mem X,
      rationalFunctions D.site D.base D.base_mem hX.1 →+*
        W.genericTotalFractionRing D.site D.base D.base_mem hX.1 hdec)
    (emb' : ∀ W : PrimeDivisor D.site D.base D.base_mem X',
      rationalFunctions D.site D.base D.base_mem hX'.1 →+*
        W.genericTotalFractionRing D.site D.base D.base_mem hX'.1 hdec')
    (f : rationalFunctions D.site D.base D.base_mem hX.1)
    (hf : ∀ W : PrimeDivisor D.site D.base D.base_mem X, IsUnit (emb W f))
    (f' : rationalFunctions D.site D.base D.base_mem hX'.1)
    (hf' : ∀ W : PrimeDivisor D.site D.base D.base_mem X', IsUnit (emb' W f'))
    (hcompat : ∀ (P : PrimeDivisor D.site D.base D.base_mem X)
      (P' : PrimeDivisor D.site D.base D.base_mem X')
      (hP : pointsMap D.site D.base D.base_mem X e.hom (P.genericPoint D.site D.base D.base_mem X) =
        P'.genericPoint D.site D.base D.base_mem X'),
      emb' P' f' = Ring.totalFracRingEquiv (henselianLocalRingEquivOfIso hdec hdec' e hP)
        (K' := P'.genericTotalFractionRing D.site D.base D.base_mem hX'.1 hdec') (emb P f))
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    principalDivisorCycleCoefficients D sX' hX' hdec' emb' f' hf'
        (IntegralClosedSubspace.equivOfIso _ _ _ hX.1 hX'.1 hdec hdec' e Z) =
      principalDivisorCycleCoefficients D sX hX hdec emb f hf Z := by
  unfold principalDivisorCycleCoefficients
  refine dite_codimension_equivOfIso hX.1 hX'.1 hdec hdec' e Z fun h h' hP => ?_
  rw [PrimeDivisor.ord_congr D.site D.base D.base_mem hX'.1 hdec' _ _ _ (hcompat _ _ hP)]
  · exact PrimeDivisor.ord_totalFracRingEquiv hX.1 hX'.1 hdec hdec' e _ _ hP _ _ _
  · rw [← hcompat _ _ hP]
    exact hf' _

/-- **The coefficients of `div_ℒ(s)` along an isomorphism.** Let `ℒ` on `X` and `ℒ'` on `X'` be
modules with meromorphic sections `s` and `s'`, and let the ratio data of Stacks 0EPR be
compatible with `e`: at any two prime divisors matched by `e`, the ratio `s' / s'_{ξ'}` is the
image of `s / s_ξ` under the isomorphism of total rings of fractions induced by `e`. Then the
coefficient of `div_{ℒ'}(s')` at the image of an integral closed subspace `Z ⊆ X` is the
coefficient of `div_ℒ(s)` at `Z`. -/
theorem divisorCycleCoefficients_equivOfIso
    [∀ W : PrimeDivisor D.site D.base D.base_mem X,
      Nontrivial ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdec)]
    [∀ W : PrimeDivisor D.site D.base D.base_mem X,
      IsNoetherianRing ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdec)]
    [∀ W : PrimeDivisor D.site D.base D.base_mem X,
      Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdec)]
    [∀ W : PrimeDivisor D.site D.base D.base_mem X',
      Nontrivial ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX'.1 hdec')]
    [∀ W : PrimeDivisor D.site D.base D.base_mem X',
      IsNoetherianRing ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX'.1 hdec')]
    [∀ W : PrimeDivisor D.site D.base D.base_mem X',
      Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX'.1 hdec')]
    (L : Modules.{u, max u z} D.site D.base D.base_mem X hX.1)
    (L' : Modules.{u, max u z} D.site D.base D.base_mem X' hX'.1)
    (s : MeromorphicSection.{u, z} D.site D.base D.base_mem X hX.1 L)
    (s' : MeromorphicSection.{u, z} D.site D.base D.base_mem X' hX'.1 L')
    (ratio : LocalRatioFamily.{u, z} D.site D.base D.base_mem hX.1 hdec L)
    (ratio' : LocalRatioFamily.{u, z} D.site D.base D.base_mem hX'.1 hdec' L')
    (hcompat : ∀ (P : PrimeDivisor D.site D.base D.base_mem X)
      (P' : PrimeDivisor D.site D.base D.base_mem X')
      (hP : pointsMap D.site D.base D.base_mem X e.hom (P.genericPoint D.site D.base D.base_mem X) =
        P'.genericPoint D.site D.base D.base_mem X'),
      (ratio' P' s' : P'.genericTotalFractionRing D.site D.base D.base_mem hX'.1 hdec') =
        Ring.totalFracRingEquiv (henselianLocalRingEquivOfIso hdec hdec' e hP)
          (K' := P'.genericTotalFractionRing D.site D.base D.base_mem hX'.1 hdec')
          (ratio P s : P.genericTotalFractionRing D.site D.base D.base_mem hX.1 hdec))
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    divisorCycleCoefficients D sX' hX' hdec' L' s' ratio'
        (IntegralClosedSubspace.equivOfIso _ _ _ hX.1 hX'.1 hdec hdec' e Z) =
      divisorCycleCoefficients D sX hX hdec L s ratio Z := by
  unfold divisorCycleCoefficients
  refine dite_codimension_equivOfIso hX.1 hX'.1 hdec hdec' e Z fun h h' hP => ?_
  simp only [divisorCoefficients, orderOfVanishingSection]
  rw [PrimeDivisor.ord_congr D.site D.base D.base_mem hX'.1 hdec' _ _ _ (hcompat _ _ hP)]
  · exact PrimeDivisor.ord_totalFracRingEquiv hX.1 hX'.1 hdec hdec' e _ _ hP _ _ _
  · rw [← hcompat _ _ hP]
    exact (ratio' _ s').isUnit

/-- **The coefficients of `div_ℒ(s)` along an isomorphism, from the orders of vanishing.** Let
`ℒ` on `X` and `ℒ'` on `X'` be modules with meromorphic sections `s` and `s'` and ratio data of
Stacks 0EPR, such that at any two prime divisors matched by `e` the orders of vanishing agree.
Then the coefficient of `div_{ℒ'}(s')` at the image of an integral closed subspace `Z ⊆ X` is the
coefficient of `div_ℒ(s)` at `Z`.

This is `AlgebraicGeometry.Space.divisorCycleCoefficients_equivOfIso` with the comparison made
on the orders themselves rather than on the ratios: the ratios of Stacks 0EPR are read against
generators chosen independently at the two generic points, and need not correspond under `e`,
while their orders do. -/
theorem divisorCycleCoefficients_equivOfIso_of_orderOfVanishingSection_eq
    [∀ W : PrimeDivisor D.site D.base D.base_mem X,
      Nontrivial ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdec)]
    [∀ W : PrimeDivisor D.site D.base D.base_mem X,
      IsNoetherianRing ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdec)]
    [∀ W : PrimeDivisor D.site D.base D.base_mem X,
      Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdec)]
    [∀ W : PrimeDivisor D.site D.base D.base_mem X',
      Nontrivial ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX'.1 hdec')]
    [∀ W : PrimeDivisor D.site D.base D.base_mem X',
      IsNoetherianRing ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX'.1 hdec')]
    [∀ W : PrimeDivisor D.site D.base D.base_mem X',
      Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX'.1 hdec')]
    (L : Modules.{u, max u z} D.site D.base D.base_mem X hX.1)
    (L' : Modules.{u, max u z} D.site D.base D.base_mem X' hX'.1)
    (s : MeromorphicSection.{u, z} D.site D.base D.base_mem X hX.1 L)
    (s' : MeromorphicSection.{u, z} D.site D.base D.base_mem X' hX'.1 L')
    (ratio : LocalRatioFamily.{u, z} D.site D.base D.base_mem hX.1 hdec L)
    (ratio' : LocalRatioFamily.{u, z} D.site D.base D.base_mem hX'.1 hdec' L')
    (hord : ∀ (P : PrimeDivisor D.site D.base D.base_mem X)
      (P' : PrimeDivisor D.site D.base D.base_mem X'),
      pointsMap D.site D.base D.base_mem X e.hom (P.genericPoint D.site D.base D.base_mem X) =
        P'.genericPoint D.site D.base D.base_mem X' →
      orderOfVanishingSection.{u, z} D.site D.base D.base_mem hX'.1 hdec' P' L' s' (ratio' P') =
        orderOfVanishingSection.{u, z} D.site D.base D.base_mem hX.1 hdec P L s (ratio P))
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    divisorCycleCoefficients D sX' hX' hdec' L' s' ratio'
        (IntegralClosedSubspace.equivOfIso _ _ _ hX.1 hX'.1 hdec hdec' e Z) =
      divisorCycleCoefficients D sX hX hdec L s ratio Z := by
  unfold divisorCycleCoefficients
  refine dite_codimension_equivOfIso hX.1 hX'.1 hdec hdec' e Z fun h h' hP => ?_
  exact hord _ _ hP

variable (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (hint' : IsIntegralSpace D.site D.base D.base_mem X')

/-- **`e_*(div(f)) = div(e_* f)`.** Let `e : X ≅ X'` be an isomorphism of integral good algebraic
spaces and `f` a unit of `R(X)`. Then `e` carries the principal divisor `div(f)` of Stacks 0EQ6,
at the canonical embeddings of Stacks 0ENK, to the principal divisor `div(e_* f)`. -/
theorem cycleClosedPushforward_principalDivisorCycleCoefficients_of_iso
    (f : rationalFunctions D.site D.base D.base_mem hX.1) (hf : IsUnit f) :
    letI E := genericFractionEmbedding D.site D.base D.base_mem hX.1 hdec hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType D.site D.base
        D.base_mem hX.1 D.isAlgebraicSpace sX hX.2.2 D.locallyNoetherian)
    letI E' := genericFractionEmbedding D.site D.base D.base_mem hX'.1 hdec' hint'
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType D.site D.base
        D.base_mem hX'.1 D.isAlgebraicSpace sX' hX'.2.2 D.locallyNoetherian)
    letI := E.nontrivial
    letI := E.isNoetherianRing
    letI := E.krullDimLE
    letI := E'.nontrivial
    letI := E'.isNoetherianRing
    letI := E'.krullDimLE
    cycleClosedPushforward D hX'.1 hX.1 hdec'
        (isClosedImmersion_of_isIso D.site D.base D.base_mem e.hom)
        (principalDivisorCycleCoefficients D sX hX hdec E.emb f fun W => hf.map (E.emb W)) =
      principalDivisorCycleCoefficients D sX' hX' hdec' E'.emb (rationalFunctionsMapIso hX'.1 e f)
        fun W => (hf.map (rationalFunctionsMapIso hX'.1 e)).map (E'.emb W) := by
  let E := genericFractionEmbedding D.site D.base D.base_mem hX.1 hdec hint
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType D.site D.base
      D.base_mem hX.1 D.isAlgebraicSpace sX hX.2.2 D.locallyNoetherian)
  let E' := genericFractionEmbedding D.site D.base D.base_mem hX'.1 hdec' hint'
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType D.site D.base
      D.base_mem hX'.1 D.isAlgebraicSpace sX' hX'.2.2 D.locallyNoetherian)
  let := E.nontrivial
  let := E.isNoetherianRing
  let := E.krullDimLE
  let := E'.nontrivial
  let := E'.isNoetherianRing
  let := E'.krullDimLE
  funext Z'
  obtain ⟨Z, rfl⟩ := (IntegralClosedSubspace.equivOfIso _ _ _ hX.1 hX'.1 hdec hdec' e).surjective Z'
  rw [IntegralClosedSubspace.equivOfIso_apply, cycleClosedPushforward_apply_pushforward,
    ← IntegralClosedSubspace.equivOfIso_apply]
  exact (principalDivisorCycleCoefficients_equivOfIso D sX hX sX' hX' hdec hdec' e E.emb E'.emb
    f _ _ _ (fun P P' hP => PrimeDivisor.rationalFunctionsToGenericTotalFractionRing_mapIso hX.1
      hX'.1 hdec hdec' e hint hint'
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType D.site D.base
        D.base_mem hX.1 D.isAlgebraicSpace sX hX.2.2 D.locallyNoetherian)
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType D.site D.base
        D.base_mem hX'.1 D.isAlgebraicSpace sX' hX'.2.2 D.locallyNoetherian) P P' hP f) Z).symm

/-- **The pushforward of a principal divisor along a closed immersion.** Let `j : T → X` be a
closed immersion into a good algebraic space, `V ⊆ T` an integral closed subspace, `j(V) ⊆ X`
its image and `φ : V ≅ j(V)` the isomorphism over `X`
(`AlgebraicGeometry.Space.IntegralClosedSubspace.isoPushforward`). For a unit `f` of `R(V)`,
pushing `div(f)` forward from `V` to `T` and then to `X` is pushing `div(φ_* f)` forward from
`j(V)` to `X`, the principal divisors being taken at the canonical embeddings of Stacks 0ENK.

This is the step that carries a rational equivalence on `T` to one on `X`: a principal divisor
on an integral closed subspace of `T` is a principal divisor on its image in `X`. -/
theorem cycleClosedPushforward_principalDivisorCycleCoefficients_image
    {T : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace D.site D.base D.base_mem T)
    (hTdec : IsDecentSpace D.site D.base D.base_mem T) {j : T ⟶ X}
    (hj : IsClosedImmersion D.site D.base D.base_mem j)
    (V : IntegralClosedSubspace D.site D.base D.base_mem T) (sV : V.subspace.toFunctor ⟶ D.space)
    (hV : D.IsGood sV)
    (sV' : (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hT hdec hj
      V).subspace.toFunctor ⟶ D.space)
    (hV' : D.IsGood sV')
    (f : rationalFunctions D.site D.base D.base_mem hV.1) (hf : IsUnit f) :
    letI W := IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hT hdec hj V
    letI φ := IntegralClosedSubspace.isoPushforward hX.1 hT hdec hj V
    letI E := genericFractionEmbedding D.site D.base D.base_mem hV.1
      (D.isDecentSpace_of_isGood sV hV) V.isIntegralSpace
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType D.site D.base
        D.base_mem hV.1 D.isAlgebraicSpace sV hV.2.2 D.locallyNoetherian)
    letI E' := genericFractionEmbedding D.site D.base D.base_mem hV'.1
      (D.isDecentSpace_of_isGood sV' hV') W.isIntegralSpace
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType D.site D.base
        D.base_mem hV'.1 D.isAlgebraicSpace sV' hV'.2.2 D.locallyNoetherian)
    letI := E.nontrivial
    letI := E.isNoetherianRing
    letI := E.krullDimLE
    letI := E'.nontrivial
    letI := E'.isNoetherianRing
    letI := E'.krullDimLE
    cycleClosedPushforward D hX.1 hT hdec hj
        (cycleClosedPushforward D hT hV.1 hTdec V.isClosedSubspace.2
          (principalDivisorCycleCoefficients D sV hV (D.isDecentSpace_of_isGood sV hV) E.emb f
            fun P => hf.map (E.emb P))) =
      cycleClosedPushforward D hX.1 hV'.1 hdec W.isClosedSubspace.2
        (principalDivisorCycleCoefficients D sV' hV' (D.isDecentSpace_of_isGood sV' hV') E'.emb
          (rationalFunctionsMapIso hV'.1 φ f)
          fun P => (hf.map (rationalFunctionsMapIso hV'.1 φ)).map (E'.emb P)) := by
  let W := IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hT hdec hj V
  let φ := IntegralClosedSubspace.isoPushforward hX.1 hT hdec hj V
  have hc := isClosedImmersion_comp D.site D.base D.base_mem _ _ V.isClosedSubspace.2 hj
  rw [cycleClosedPushforward_cycleClosedPushforward D hX.1 hT hV.1 hdec hTdec rfl
      V.isClosedSubspace.2 hj hc,
    ← cycleClosedPushforward_principalDivisorCycleCoefficients_of_iso D sV hV sV' hV'
      (D.isDecentSpace_of_isGood sV hV) (D.isDecentSpace_of_isGood sV' hV') φ V.isIntegralSpace
      W.isIntegralSpace f hf,
    cycleClosedPushforward_cycleClosedPushforward D hX.1 hV'.1 hV.1 hdec
      (D.isDecentSpace_of_isGood sV' hV')
      (IntegralClosedSubspace.isoPushforward_hom_comp_ι hX.1 hT hdec hj V)
      (isClosedImmersion_of_isIso D.site D.base D.base_mem φ.hom) W.isClosedSubspace.2 hc]

end PrincipalDivisor

end AlgebraicGeometry.Space

end
