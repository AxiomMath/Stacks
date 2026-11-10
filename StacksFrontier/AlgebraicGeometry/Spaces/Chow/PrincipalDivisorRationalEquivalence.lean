module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackOrderOfVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GenericFractionEmbeddingOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RefinedGysinOfSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.HenselianLocalRingOfIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingRankStrata

/-!
# The principal divisor of a rational function is rationally equivalent to zero

In Situation 0EDT let `X/B` be good and integral with `n = dim_δ(X)`, and let `f ∈ R(X)^*`. The
principal divisor `div(f)` is an `(n-1)`-cycle on `X` which is rationally equivalent to zero:
in the definition of Stacks 0EQ6 take the one-member family `{X}`, the integral closed subspace
`X ⊆ X` of δ-dimension `n`, with the rational function `f` on it.

The integral closed subspaces of this repository are subfunctors, so the member `X` of that
family is the top subfunctor `⊤ ⊆ X`, whose inclusion `ι : ⊤ ⟶ X` is an isomorphism of
algebraic spaces but not an identity. Reading `div(f)` on `⊤`, at the canonical embeddings of
Stacks 0ENK, therefore compares the ingredients of the order of vanishing along `ι`:

* the integral closed subspaces and the prime divisors, through the image along the closed
  immersion `ι`, which preserves the δ-dimension and hence (Stacks 0EPZ) codimension one;
* the field of rational functions, through the isomorphism of function fields `ι` induces;
* the order of vanishing itself, which is compatible with the open immersion `ι`,
  `AlgebraicGeometry.Space.genericFractionEmbedding_ord_rationalFunctionMap_of_isOpenImmersion`.

## Main definitions

* `AlgebraicGeometry.Space.IntegralClosedSubspace.top`: an integral algebraic space as an
  integral closed subspace of itself.
* `AlgebraicGeometry.Space.rationalFunctionsEquivOfIsIso`: the isomorphism of function fields
  induced by an isomorphism of integral algebraic spaces.

## Main results

* `Ring.ordTotalFracInt_ringEquivOfRingEquiv`: the order of vanishing on the total ring of
  fractions is invariant under a ring isomorphism.
* `AlgebraicGeometry.Space.canonicalPrincipalCycleCoefficients`: the coefficients of `div(f)`.
* `isRationallyEquivalentToZero_of_coe_eq_canonicalPrincipalCycleCoefficients`:
  an `(n-1)`-cycle on `X` whose coefficients are those of `div(f)` is rationally equivalent to
  zero, in the sense of Stacks 0EQ6, part (2).

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0END](https://stacks.math.columbia.edu/tag/0END)
* [Stacks Project, Tag 0ENP](https://stacks.math.columbia.edu/tag/0ENP)
* [Stacks Project, Tag 0EPZ](https://stacks.math.columbia.edu/tag/0EPZ)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace IsLocalRing

universe v u

/-! ### The order of vanishing along a ring isomorphism -/

namespace Ring

/-- **The order of vanishing is invariant under ring isomorphism.** For a ring isomorphism
`φ : A ≃ B` of Noetherian local rings of dimension at most one, the order of vanishing of the
image of a unit `x` of the total ring of fractions of `A` under the induced isomorphism of total
rings of fractions is the order of vanishing of `x`. An isomorphism is a flat local homomorphism
carrying the maximal ideal onto the maximal ideal, so this is
`Ring.ordTotalFracInt_map_mk'_of_flatHom` with multiplicity one. -/
theorem ordTotalFracInt_ringEquivOfRingEquiv {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    [IsNoetherianRing B] [Ring.KrullDimLE 1 B]
    {KA : Type*} [CommRing KA] [Algebra A KA] [IsFractionRing A KA]
    {KB : Type*} [CommRing KB] [Algebra B KB] [IsFractionRing B KB]
    (φ : A ≃+* B) (x : KA) (hx : IsUnit x) :
    ordTotalFracInt B (IsFractionRing.ringEquivOfRingEquiv φ x : KB) (hx.map _) =
      ordTotalFracInt A x hx := by
  obtain ⟨⟨a₀, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) x
  change IsUnit (IsLocalization.mk' KA a₀ b) at hx
  have ha₀ : a₀ ∈ nonZeroDivisors A := by
    have hu : IsUnit (algebraMap A KA a₀) := by
      rw [← IsLocalization.mk'_spec KA a₀ b]
      exact hx.mul (IsLocalization.map_units KA b)
    exact mem_nonZeroDivisors_of_injective (IsFractionRing.injective A KA) hu.mem_nonZeroDivisors
  let a : nonZeroDivisors A := ⟨a₀, ha₀⟩
  change ordTotalFracInt B (IsFractionRing.ringEquivOfRingEquiv φ
    (IsLocalization.mk' KA (a : A) b) : KB) _ =
      ordTotalFracInt A (IsLocalization.mk' KA (a : A) b) hx
  have hloc : IsLocalHom (φ : A →+* B) := inferInstance
  have hflat : (φ : A →+* B).Flat := RingHom.Flat.of_bijective φ.bijective
  have hm : Module.length B (B ⧸ Ideal.map (φ : A →+* B) (maximalIdeal A)) =
      ((1 : ℕ) : ℕ∞) := by
    rw [show Ideal.map (φ : A →+* B) (maximalIdeal A) = maximalIdeal B from
      IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv φ), Nat.cast_one]
    have : IsSimpleModule B (B ⧸ maximalIdeal B) :=
      isSimpleModule_iff_isCoatom.2 (IsLocalRing.maximalIdeal.isMaximal B).out
    exact Module.length_eq_one _ _
  have hu' : IsUnit (IsLocalization.mk' KB ((φ : A →+* B) (a : A))
      (⟨(φ : A →+* B) (b : A), map_mem_nonZeroDivisors_of_flatHom hflat b.2⟩ :
        nonZeroDivisors B)) :=
    isUnit_mk'_of_mem _ (map_mem_nonZeroDivisors_of_flatHom hflat a.2) _
  have heq : (IsFractionRing.ringEquivOfRingEquiv φ (IsLocalization.mk' KA (a : A) b) : KB) =
      IsLocalization.mk' KB ((φ : A →+* B) (a : A))
        (⟨(φ : A →+* B) (b : A), map_mem_nonZeroDivisors_of_flatHom hflat b.2⟩ :
          nonZeroDivisors B) :=
    IsLocalization.ringEquivOfRingEquiv_mk' _ _ _
  rw [ordTotalFracInt_congr B _ hu' heq,
    ordTotalFracInt_map_mk'_of_flatHom hloc hflat hm a b hx hu', Nat.cast_one, one_mul]

end Ring

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### An integral algebraic space as an integral closed subspace of itself -/

section Top

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hint : IsIntegralSpace B S hS X)

/-- An integral algebraic space `X` as an integral closed subspace of itself: the top
subfunctor, whose inclusion is an isomorphism, so that it is closed and integral because `X`
is. -/
def IntegralClosedSubspace.top : IntegralClosedSubspace B S hS X where
  subspace := ⊤
  isClosedSubspace := isClosedSubspace_top_subfunctor B S hS hX
  isIntegralSpace := by
    refine ⟨?_, isDecentSpace_of_iso B S hS (asIso (⊤ : Subfunctor X).ι).symm hint.2.1,
      (pointsHomeomorphOfIso B S hS (asIso (⊤ : Subfunctor X).ι)).irreducibleSpace_iff.2
        hint.2.2⟩
    obtain ⟨U, a, haSurjective, haEtale, hP⟩ := hint.1
    exact ⟨U, a ≫ inv (⊤ : Subfunctor X).ι,
      MorphismProperty.RespectsIso.postcomp _ (inv (⊤ : Subfunctor X).ι) a haSurjective,
      MorphismProperty.RespectsIso.postcomp _ (inv (⊤ : Subfunctor X).ι) a haEtale, hP⟩

/-- The underlying subfunctor of `IntegralClosedSubspace.top` is the top subfunctor of `X`. -/
@[simp]
theorem IntegralClosedSubspace.subspace_top :
    (IntegralClosedSubspace.top B S hS hX hint).subspace = ⊤ :=
  rfl

/-- Every point of `X` lies in the top subfunctor. -/
theorem IntegralClosedSubspace.range_pointsMap_top :
    Set.range (pointsMap B S hS (IntegralClosedSubspace.top B S hS hX hint).subspace.toFunctor
      (IntegralClosedSubspace.top B S hS hX hint).subspace.ι) = Set.univ :=
  Set.range_eq_univ.2 (pointsMap_surjective_of_isIso B S hS (⊤ : Subfunctor X).ι)

end Top

/-! ### The function field along an isomorphism -/

section FunctionField

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hintX : IsIntegralSpace B S hS X) (hintY : IsIntegralSpace B S hS Y)

/-- An isomorphism of integral algebraic spaces carries the generic point to the generic
point: its map on points is a homeomorphism, and the point spaces are Kolmogorov. -/
theorem pointsMap_genericPoint_of_isIso (p : X ⟶ Y) [IsIso p] :
    pointsMap B S hS X p (genericPoint B S hS hX hintX) = genericPoint B S hS hY hintY := by
  have : T0Space (points B S hS Y) := t0Space_points_of_isDecentSpace B S hS hY hintY.2.1
  refine IsGenericPoint.eq ?_ (isGenericPoint_genericPoint B S hS hY hintY)
  have h := (isGenericPoint_genericPoint B S hS hX hintX).image (continuous_pointsMap B S hS p)
  rwa [Set.image_univ, Set.range_eq_univ.2 (pointsMap_surjective_of_isIso B S hS p),
    closure_univ] at h

/-- **Stacks 0END along an isomorphism.** An isomorphism `p : X ⟶ Y` of integral algebraic
spaces induces a bijective homomorphism of function fields `R(Y) → R(X)`: under the
identifications of Stacks 0END it is the homomorphism of residue fields at the generic points,
which is bijective by Stacks 0EMX because the residue field morphism of `X` followed by an
isomorphism is a monomorphism. -/
theorem bijective_rationalFunctionMap_of_isIso (p : X ⟶ Y) [IsIso p] :
    Function.Bijective (rationalFunctionMap B S hS hX hY hintX hintY p
      (pointsMap_genericPoint_of_isIso B S hS hX hY hintX hintY p)) := by
  have hmono : Mono (residueFieldMorphism B S hS X hintX.2.1 (genericPoint B S hS hX hintX) ≫
      p) := by
    have : Mono (residueFieldMorphism B S hS X hintX.2.1 (genericPoint B S hS hX hintX)) :=
      (residueFieldRepresentative B S hS X hintX.2.1 (genericPoint B S hS hX hintX)).2.2
    exact @mono_comp _ _ _ _ _ _ this p (IsIso.mono_of_iso p)
  have hiso := (isIso_residueFieldHom_iff_mono B S hS X Y hY hintX.2.1 hintY.2.1 p
    (genericPoint B S hS hX hintX)).2 hmono
  have hb : Function.Bijective (residueFieldHom B S hS X Y hY hintX.2.1 hintY.2.1 p
      (genericPoint B S hS hX hintX)) :=
    ConcreteCategory.bijective_of_isIso (CommRingCat.ofHom _)
  exact (rationalFunctionsRingEquiv B S hS hX hintX).symm.bijective.comp
    ((hb.comp (residueFieldCongr B S hS hintY.2.1
      (pointsMap_genericPoint_of_isIso B S hS hX hY hintX hintY p)).symm.bijective).comp
      (rationalFunctionsRingEquiv B S hS hY hintY).bijective)

/-- The isomorphism of function fields `R(Y) ≃ R(X)` induced by an isomorphism `p : X ⟶ Y` of
integral algebraic spaces. -/
def rationalFunctionsEquivOfIsIso (p : X ⟶ Y) [IsIso p] :
    rationalFunctions B S hS hY ≃+* rationalFunctions B S hS hX :=
  RingEquiv.ofBijective _ (bijective_rationalFunctionMap_of_isIso B S hS hX hY hintX hintY p)

end FunctionField

/-! ### The principal divisor of a rational function is rationally equivalent to zero -/

section RationallyTrivial

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (hint : IsIntegralSpace D.site D.base D.base_mem X)

/-- The δ-dimension of `X`, read on `X` as an integral closed subspace of itself. -/
theorem deltaDimension_top {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt)) :
    deltaDimension D sX (IntegralClosedSubspace.top D.site D.base D.base_mem hX.1 hint) = n := by
  have h := deltaDimensionClosed_univ_eq_deltaValue_genericPoint D sX hX hint
  rw [hn] at h
  rw [deltaDimension_eq_of_isGenericPoint D sX hX.1 _
    (genericPoint D.site D.base D.base_mem hX.1 hint)]
  · exact (WithBotTop.coe_injective h).symm
  · rw [subspacePointSet, IntegralClosedSubspace.range_pointsMap_top]
    exact isGenericPoint_genericPoint D.site D.base D.base_mem hX.1 hint

/-- The coefficients of the principal divisor `div(f) = ∑ ord_Z(f) [Z]` of an invertible
rational function `f` on an integral good algebraic space, indexed by the integral closed
subspaces of `X`, the order of vanishing being taken through the embeddings
`R(X) → Q(𝒪^h_{X,ξ})` of Stacks 0ENK: the coefficient at `Z` is `ord_Z(f)` when `Z` is a prime
divisor and zero otherwise. -/
def canonicalPrincipalCycleCoefficients
    (f : (rationalFunctions D.site D.base D.base_mem hX.1)ˣ)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) : ℤ :=
  if h : codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hX.1 Z) = 1 then
    (genericFractionEmbedding D.site D.base D.base_mem hX.1 hint.2.1 hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)).ord f
      (Z.toPrimeDivisor D.site D.base D.base_mem hX.1 h)
  else 0

/-- **The principal divisor of a rational function is rationally equivalent to zero** (Stacks
0EQ6, part (2), for the one-member family `{X}`). Let `X/B` be good and integral with
`dim_δ(X) = n` and let `f ∈ R(X)^*`. An `(n-1)`-cycle on `X` whose coefficients are those of
`div(f)` is rationally equivalent to zero: it is `ι_* div(f)` for the integral closed subspace
`X ⊆ X` of δ-dimension `n`, read as the top subfunctor `ι : ⊤ ⟶ X`.

On `⊤` the rational function is the image of `f` under the isomorphism of function fields `ι`
induces, and both principal divisors are read at the canonical embeddings of Stacks 0ENK: the
prime divisors of `⊤` are those of `X` (`ι` preserves δ-dimensions, and codimension one is
δ-dimension `n - 1` by Stacks 0EPZ on either side), and the order of vanishing along a prime
divisor of `⊤` is the one along its image in `X`, `ι` being an open immersion
(`AlgebraicGeometry.Space.genericFractionEmbedding_ord_rationalFunctionMap_of_isOpenImmersion`). -/
theorem isRationallyEquivalentToZero_of_coe_eq_canonicalPrincipalCycleCoefficients {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (f : (rationalFunctions D.site D.base D.base_mem hX.1)ˣ) (α : CycleGroup D sX (n - 1))
    (hα : (α : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ) =
      canonicalPrincipalCycleCoefficients D sX hX hint f) :
    IsRationallyEquivalentToZero.{v} D sX hX (n - 1) α := by
  -- the integral closed subspace `X ⊆ X` and its inclusion `ι`
  let T := IntegralClosedSubspace.top D.site D.base D.base_mem hX.1 hint
  have hιiso : IsIso T.subspace.ι := inferInstanceAs (IsIso (⊤ : Subfunctor X).ι)
  have hYg : D.IsGood (T.subspace.ι ≫ sX) := isGood_integralClosedSubspace D sX hX T
  have hYint : IsIntegralSpace D.site D.base D.base_mem T.subspace.toFunctor := T.isIntegralSpace
  have hXdec : IsDecentSpace D.site D.base D.base_mem X := hint.2.1
  have hTdim : deltaDimension D sX T = n := deltaDimension_top D sX hX hint hn
  have hYn : deltaDimensionClosed D (T.subspace.ι ≫ sX) hYg Set.univ isClosed_univ =
      ((n : ℤ) : EInt) := by
    rw [deltaDimensionClosed_univ_integralClosedSubspace D sX hX T, hTdim]
  obtain ⟨dX, hdX⟩ := exists_dimensionFunction_deltaValue_of_isGood D sX hX
  obtain ⟨dY, hdY⟩ := exists_dimensionFunction_deltaValue_of_isGood D _ hYg
  let push := IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1
    T.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX) T.isClosedSubspace.2
  -- codimension one on `⊤` is codimension one on `X`
  have hcod : ∀ Z' : IntegralClosedSubspace D.site D.base D.base_mem T.subspace.toFunctor,
      codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hYg.1 Z') = 1 ↔
        codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hX.1
          (push Z')) = 1 := fun Z' => by
    refine ((isPrimeDivisor_tfae_of_isIntegralSpace D _ hYg hYint dY hdY hYn Z').out 2 3).trans
      (Iff.trans ?_
        ((isPrimeDivisor_tfae_of_isIntegralSpace D sX hX hint dX hdX hn (push Z')).out 2 3).symm)
    rw [IntegralClosedSubspace.deltaDimension_pushforward D sX hX.2.2 hX.1 _ _ _ Z']
  -- the prime divisor of `X` beneath a prime divisor of `⊤`
  have hcodP : ∀ P' : PrimeDivisor D.site D.base D.base_mem T.subspace.toFunctor,
      codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hX.1
        (push (P'.toIntegralClosedSubspace D.site D.base D.base_mem))) = 1 := fun P' =>
    (hcod _).1 (P'.codimension_integralClosedSubspaceSupport D.site D.base D.base_mem hYg.1)
  let up : PrimeDivisor D.site D.base D.base_mem T.subspace.toFunctor →
      PrimeDivisor D.site D.base D.base_mem X := fun P' =>
    (push (P'.toIntegralClosedSubspace D.site D.base D.base_mem)).toPrimeDivisor
      D.site D.base D.base_mem hX.1 (hcodP P')
  have hgen : ∀ P' : PrimeDivisor D.site D.base D.base_mem T.subspace.toFunctor,
      pointsMap D.site D.base D.base_mem T.subspace.toFunctor T.subspace.ι
          (P'.genericPoint D.site D.base D.base_mem T.subspace.toFunctor) =
        (up P').genericPoint D.site D.base D.base_mem X := fun P' => by
    have : T0Space (points D.site D.base D.base_mem X) :=
      t0Space_points_of_isDecentSpace D.site D.base D.base_mem hX.1 hXdec
    refine IsGenericPoint.eq ?_ ((up P').isGenericPoint_genericPoint D.site D.base D.base_mem X)
    have h := (P'.isGenericPoint_genericPoint D.site D.base D.base_mem
      T.subspace.toFunctor).image (continuous_pointsMap D.site D.base D.base_mem T.subspace.ι)
    have hcl : IsClosed (pointsMap D.site D.base D.base_mem T.subspace.toFunctor T.subspace.ι ''
        P'.support D.site D.base D.base_mem T.subspace.toFunctor) :=
      (isClosedEmbedding_pointsMap_of_isClosedImmersion D.site D.base D.base_mem hX.1
        T.isClosedSubspace.2).isClosedMap _ (isClosed_range_pointsMap_integralClosedSubspace
          D.site D.base D.base_mem hYg.1 (P'.toIntegralClosedSubspace D.site D.base D.base_mem))
    have hsupp : (up P').support D.site D.base D.base_mem X =
        pointsMap D.site D.base D.base_mem T.subspace.toFunctor T.subspace.ι ''
          P'.support D.site D.base D.base_mem T.subspace.toFunctor :=
      IntegralClosedSubspace.subspacePointSet_pushforward D.site D.base D.base_mem hX.1
        T.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX) T.isClosedSubspace.2
        (P'.toIntegralClosedSubspace D.site D.base D.base_mem)
    rw [hsupp]
    rwa [hcl.closure_eq] at h
  -- the canonical embeddings of Stacks 0ENK on `X` and on `⊤`, and the function field
  let EX := genericFractionEmbedding D.site D.base D.base_mem hX.1 hXdec hint
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)
  let EY := genericFractionEmbedding D.site D.base D.base_mem hYg.1 hYint.isDecentSpace hYint
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D _ hYg)
  let eR := rationalFunctionsEquivOfIsIso D.site D.base D.base_mem hYg.1 hX.1 hYint hint
    T.subspace.ι
  -- the order of vanishing along a prime divisor of `⊤` is the one along its image in `X`
  have hord : ∀ P' : PrimeDivisor D.site D.base D.base_mem T.subspace.toFunctor,
      EY.ord (Units.map (eR : rationalFunctions D.site D.base D.base_mem hX.1 →*
        rationalFunctions D.site D.base D.base_mem hYg.1) f) P' = EX.ord f (up P') := fun P' =>
    genericFractionEmbedding_ord_rationalFunctionMap_of_isOpenImmersion D.site D.base D.base_mem
      hYg.1 hX.1 hYint hint (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D _ hYg)
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) T.subspace.ι
      (isOpenImmersion_of_isIso D.site D.base D.base_mem T.subspace.ι)
      (pointsMap_genericPoint_of_isIso D.site D.base D.base_mem hYg.1 hX.1 hYint hint
        T.subspace.ι) P' (up P') (hgen P') f
  -- the cycle on `⊤` pushing forward to `α`
  have hc : (fun Z' => α.1 (push Z')) ∈ cyclesOfDimension D (T.subspace.ι ≫ sX) (n - 1) := by
    refine ⟨locallyFinite_of_continuous_comap
        (continuous_pointsMap D.site D.base D.base_mem T.subspace.ι)
        (IntegralClosedSubspace.injective_pushforward D.site D.base D.base_mem hX.1
          T.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX) T.isClosedSubspace.2)
        (fun Z' => ?_) α.2.1, fun Z' hZ' => ?_⟩
    · split_ifs
      · simp
      · rw [IntegralClosedSubspace.subspacePointSet_pushforward]
    · rw [← IntegralClosedSubspace.deltaDimension_pushforward D sX hX.2.2 hX.1
        T.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX) T.isClosedSubspace.2 Z']
      exact α.2.2 _ hZ'
  let c : CycleGroup D (T.subspace.ι ≫ sX) (n - 1) := ⟨fun Z' => α.1 (push Z'), hc⟩
  have hpush : integralClosedSubspacePushforward D sX hX T (n - 1) c = α := by
    refine Subtype.ext (funext fun Z => ?_)
    obtain ⟨Z', rfl⟩ := IntegralClosedSubspace.exists_pushforward_eq D.site D.base D.base_mem
      hX.1 T.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX) hYint.2.1
      T.isClosedSubspace.2 Z (by
        rw [IntegralClosedSubspace.range_pointsMap_top]
        exact Set.subset_univ _)
    exact cycleClosedPushforward_apply_pushforward D hX.1 T.isClosedSubspace.1
      (D.isDecentSpace_of_isGood sX hX) T.isClosedSubspace.2 c.1 Z'
  refine ⟨PUnit.{v + 1}, fun _ => T, fun _ => ⟨Set.univ, Filter.univ_mem, Set.toFinite _⟩,
    fun _ => c, fun _ => by rw [hTdim, sub_add_cancel], fun _ => ?_, ?_⟩
  · refine ⟨hYg, hYint, Units.map (eR : rationalFunctions D.site D.base D.base_mem hX.1 →*
      rationalFunctions D.site D.base D.base_mem hYg.1) f, ?_⟩
    let := EY.nontrivial
    let := EY.isNoetherianRing
    let := EY.krullDimLE
    let := EX.nontrivial
    let := EX.isNoetherianRing
    let := EX.krullDimLE
    funext Z'
    change α.1 (push Z') = _
    rw [hα]
    by_cases h' : codimension
        (integralClosedSubspaceSupport D.site D.base D.base_mem hYg.1 Z') = 1
    · have h := (hcod Z').1 h'
      rw [show principalDivisorCycleCoefficients D (T.subspace.ι ≫ sX) hYg _
          EY.emb _ _ Z' = _ from dite_eq_left h',
        show canonicalPrincipalCycleCoefficients D sX hX hint f (push Z') = _ from
          dite_eq_left h]
      exact (hord (Z'.toPrimeDivisor D.site D.base D.base_mem hYg.1 h')).symm
    · rw [show principalDivisorCycleCoefficients D (T.subspace.ι ≫ sX) hYg _
          EY.emb _ _ Z' = 0 from dite_eq_right h',
        show canonicalPrincipalCycleCoefficients D sX hX hint f (push Z') = 0 from
          dite_eq_right ((not_congr (hcod Z')).1 h')]
  · refine Subtype.ext (funext fun Z => ?_)
    change α.1 Z = ∑ᶠ _ : PUnit.{v + 1},
      (integralClosedSubspacePushforward D sX hX T (n - 1) c).1 Z
    rw [finsum_unique, hpush]

end RationallyTrivial

end AlgebraicGeometry.Space

end
