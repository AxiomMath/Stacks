module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.IntersectionNumberIntegralImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.IntersectionNumberMeromorphicSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.MeromorphicDenominatorCodimensionZero
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralCodimensionZeroHypotheses
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationFiniteness

/-!
# Intersecting with the divisor of a regular meromorphic section, summed over prime divisors

Let `Y` be an integral algebraic space proper over a field `k`, of dimension `e + 1`, let `𝒩` be
invertible with a regular meromorphic section `t` and let `M₁, …, M_e` be invertible. Then

`(𝒩 M₁ ⋯ M_e · Y) = ∑_Z ord_Z(t) (M₁ ⋯ M_e · Z)`,

the sum over the integral closed subspaces `Z ⊆ Y`, the coefficient `ord_Z(t)` being that of the
Weil divisor `div_𝒩(t)` (zero unless `Z` is a prime divisor).

## Main definitions

* `AlgebraicGeometry.Space.integralClosedSubspaceIntersectionNumber`: `(L₁ ⋯ L_d · Z)` for an
  integral closed subspace `Z`, extended by zero off dimension `d`.

## Main results

All in the namespace `AlgebraicGeometry.Space`:

* `topologicalKrullDim_le_of_isClosed_ne_univ`: a proper closed subset of an irreducible space of
  dimension at most `n + 1` has dimension at most `n`.
* `twistedEulerMixedDifference_cons_eq_finsum_divisorCycleCoefficients`:
  `(𝒩 M₁ ⋯ M_e · Y) = ∑_Z ord_Z(t) (M₁ ⋯ M_e · Z)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

attribute [local instance 5000] SheafOfModules.instAbelian

universe u w

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- **A proper closed subset of an irreducible space has smaller dimension**: if `dim α ≤ n + 1`
then every closed `T ≠ α` has `dim T ≤ n`. -/
theorem topologicalKrullDim_le_of_isClosed_ne_univ {α : Type*} [TopologicalSpace α]
    [IrreducibleSpace α] {T : Set α} (hT : IsClosed T) (hne : T ≠ Set.univ) {n : ℕ}
    (h : topologicalKrullDim α ≤ n + 1) : topologicalKrullDim T ≤ n := by
  by_cases hTe : Nonempty (IrreducibleCloseds T)
  swap
  · rw [not_nonempty_iff] at hTe
    rw [topologicalKrullDim, Order.krullDim_eq_bot]
    exact bot_le
  let img : IrreducibleCloseds T → IrreducibleCloseds α := fun C =>
    ⟨Subtype.val '' (C : Set T), C.isIrreducible.image _ continuous_subtype_val.continuousOn,
      hT.isClosedEmbedding_subtypeVal.isClosedMap _ C.isClosed⟩
  let φ : WithTop (IrreducibleCloseds T) → IrreducibleCloseds α := fun C =>
    WithTop.recTopCoe ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩ img C
  have hφ : StrictMono φ := by
    intro a b hab
    induction b using WithTop.recTopCoe with
    | top =>
      induction a using WithTop.recTopCoe with
      | top => exact absurd hab (lt_irrefl _)
      | coe a =>
        show img a < ⟨Set.univ, _, _⟩
        refine lt_of_le_of_ne (fun x _ => Set.mem_univ x) fun heq => hne ?_
        have h1 : (Subtype.val '' (a : Set T)) = Set.univ := congrArg SetLike.coe heq
        exact Set.eq_univ_of_univ_subset (h1 ▸ Subtype.coe_image_subset _ _)
    | coe b =>
      induction a using WithTop.recTopCoe with
      | top => exact absurd hab not_top_lt
      | coe a =>
        have hab' : a < b := WithTop.coe_lt_coe.1 hab
        have hab'' : (a : Set T) < (b : Set T) := hab'
        show img a < img b
        exact (Subtype.val_injective.image_strictMono hab'' : _)
  have hle := Order.krullDim_le_of_strictMono φ hφ
  rw [Order.krullDim_WithTop] at hle
  change Order.krullDim (IrreducibleCloseds T) + 1 ≤ topologicalKrullDim α at hle
  have h2 := hle.trans h
  rw [topologicalKrullDim]
  obtain ⟨m, hm⟩ : ∃ m : ℕ∞, Order.krullDim (IrreducibleCloseds T) = m :=
    (WithBot.ne_bot_iff_exists.1
      (Order.krullDim_eq_bot_iff.not.2 (not_isEmpty_of_nonempty _))).imp fun _ h => h.symm
  rw [hm] at h2 ⊢
  have h3 : m + 1 ≤ (n : ℕ∞) + 1 := by exact_mod_cast h2
  exact_mod_cast (ENat.add_le_add_iff_right ENat.one_ne_top).1 h3

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))

/-- The intersection number `(L₁ ⋯ L_d · Z)` of an integral closed subspace `Z ⊆ X` when `Z` has
dimension `d`, and zero otherwise. -/
def integralClosedSubspaceIntersectionNumber (X : AlgebraicSpaces B (Spec (.of k)) hk)
    (f : X.1 ⟶ yoneda.obj (baseObject k B hk)) (hf : IsProper B (Spec (.of k)) hk f) {d : ℕ}
    (L : Fin d → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)]
    (Z : IntegralClosedSubspace B (Spec (.of k)) hk X.1) : ℤ :=
  if h : dimension B (Spec (.of k)) hk Z.subspace.toFunctor Z.isClosedSubspace.1 = d then
    intersectionNumber.{u, w} k B hk X
      (closedSubspaceToSpace B (Spec (.of k)) hk X ⟨Z.subspace, Z.isClosedSubspace⟩) d f hf
      (closedSubspaceInclusion B (Spec (.of k)) hk X ⟨Z.subspace, Z.isClosedSubspace⟩)
      Z.isClosedSubspace.2 h L
  else 0

/-- On an integral closed subspace `Z` of dimension `d`,
`integralClosedSubspaceIntersectionNumber` is the intersection number `(L₁ ⋯ L_d · Z)`. -/
theorem integralClosedSubspaceIntersectionNumber_of_dimension_eq
    (X : AlgebraicSpaces B (Spec (.of k)) hk)
    (f : X.1 ⟶ yoneda.obj (baseObject k B hk)) (hf : IsProper B (Spec (.of k)) hk f) {d : ℕ}
    (L : Fin d → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)]
    (Z : IntegralClosedSubspace B (Spec (.of k)) hk X.1)
    (h : dimension B (Spec (.of k)) hk Z.subspace.toFunctor Z.isClosedSubspace.1 = d) :
    integralClosedSubspaceIntersectionNumber.{u, w} k B hk X f hf L Z =
      intersectionNumber.{u, w} k B hk X
        (closedSubspaceToSpace B (Spec (.of k)) hk X ⟨Z.subspace, Z.isClosedSubspace⟩) d f hf
        (closedSubspaceInclusion B (Spec (.of k)) hk X ⟨Z.subspace, Z.isClosedSubspace⟩)
        Z.isClosedSubspace.2 h L :=
  dif_pos h

/-- **Intersecting with the divisor of a regular meromorphic section.** Let `Y` be an integral
algebraic space proper over `k` of dimension `e + 1`, `𝒩` invertible with a regular meromorphic
section `t` and `M₁, …, M_e` invertible. Then
`(𝒩 M₁ ⋯ M_e · Y) = ∑_Z ord_Z(t) (M₁ ⋯ M_e · Z)`, the coefficients being those of
`div_𝒩(t)` at the canonical ratios. -/
theorem twistedEulerMixedDifference_cons_eq_finsum_divisorCycleCoefficients
    (Y : AlgebraicSpaces B (Spec (.of k)) hk) (fY : Y.1 ⟶ yoneda.obj (baseObject k B hk))
    (hfY : IsProper B (Spec (.of k)) hk fY) (hint : IsIntegralSpace B (Spec (.of k)) hk Y.1)
    {e : ℕ} (hdimY : topologicalKrullDim (points B (Spec (.of k)) hk Y.1) = (e : WithBot ℕ∞) + 1)
    (hn : deltaDimensionClosed (fieldSpaceSituation k B hk) fY
      (isGood_fieldSpaceSituation_of_isProper k B hk Y hfY) Set.univ isClosed_univ =
        (((e : ℤ) + 1 : ℤ) : EInt))
    (N : Modules.{u, u} B (Spec (.of k)) hk Y.1 Y.2)
    [hN : Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk Y.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk Y.1 Y.2).O).property N]
    (t : MeromorphicSection.{u, u} B (Spec (.of k)) hk Y.1 Y.2 N)
    (ht : IsRegularMeromorphicSection.{u, u} B (Spec (.of k)) hk Y.1 Y.2 N t)
    (M : Fin e → Modules.{u, u} B (Spec (.of k)) hk Y.1 Y.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk Y.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk Y.1 Y.2).O).property (M j)] :
    haveI := fun W : PrimeDivisor B (Spec (.of k)) hk Y.1 =>
      W.nontrivial_genericHenselianLocalRing B (Spec (.of k)) hk Y.2
        (isDecentSpace_of_isProper_baseObject k B hk Y.1 Y.2 fY hfY) hint
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hk Y.1 Y.2 fY hfY)
    haveI := fun W : PrimeDivisor B (Spec (.of k)) hk Y.1 =>
      W.isNoetherianRing_genericHenselianLocalRing B (Spec (.of k)) hk Y.2
        (isDecentSpace_of_isProper_baseObject k B hk Y.1 Y.2 fY hfY) hint
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hk Y.1 Y.2 fY hfY)
    haveI := fun W : PrimeDivisor B (Spec (.of k)) hk Y.1 =>
      W.krullDimLE_genericHenselianLocalRing B (Spec (.of k)) hk Y.2
        (isDecentSpace_of_isProper_baseObject k B hk Y.1 Y.2 fY hfY) hint
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hk Y.1 Y.2 fY hfY)
    haveI : Fact (HasEtaleLocalProperty B (Spec (.of k)) hk Y.1
        (fun T : Scheme.{u} => IsLocallyNoetherian T)) :=
      ⟨hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hk Y.1 Y.2 fY hfY⟩
    twistedEulerMixedDifference.{u, w} k B hk Y fY hfY
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B (Spec (.of k)) hk Y.1 Y.2).O)) inferInstance (Fin.cons N M) =
      ∑ᶠ Z : IntegralClosedSubspace B (Spec (.of k)) hk Y.1,
        divisorCycleCoefficients (fieldSpaceSituation k B hk) fY
            (isGood_fieldSpaceSituation_of_isProper k B hk Y hfY)
            (isDecentSpace_of_isProper_baseObject k B hk Y.1 Y.2 fY hfY) N t
            (canonicalLocalRatioFamily B (Spec (.of k)) hk Y.2
              (isDecentSpace_of_isProper_baseObject k B hk Y.1 Y.2 fY hfY) N hN hint
              (hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hk Y.1 Y.2 fY hfY)) Z *
          integralClosedSubspaceIntersectionNumber.{u, w} k B hk Y fY hfY M Z := by
  have hY := isGood_fieldSpaceSituation_of_isProper k B hk Y hfY
  have hdec := isDecentSpace_of_isProper_baseObject k B hk Y.1 Y.2 fY hfY
  have hLN := hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hk Y.1 Y.2 fY hfY
  have := fun W : PrimeDivisor B (Spec (.of k)) hk Y.1 =>
    W.nontrivial_genericHenselianLocalRing B (Spec (.of k)) hk Y.2 hdec hint hLN
  have := fun W : PrimeDivisor B (Spec (.of k)) hk Y.1 =>
    W.isNoetherianRing_genericHenselianLocalRing B (Spec (.of k)) hk Y.2 hdec hint hLN
  have := fun W : PrimeDivisor B (Spec (.of k)) hk Y.1 =>
    W.krullDimLE_genericHenselianLocalRing B (Spec (.of k)) hk Y.2 hdec hint hLN
  have hfact : Fact (HasEtaleLocalProperty B (Spec (.of k)) hk Y.1
      (fun T : Scheme.{u} => IsLocallyNoetherian T)) := ⟨hLN⟩
  have hwa := forall_localRingDimension_eq_zero_of_isIntegralSpace B (Spec (.of k)) hk Y hint
  have hfin := hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B (Spec (.of k)) hk
    Y.1 Y.2 hLN
  have hdimO : topologicalKrullDim (moduleSupportSet B (Spec (.of k)) hk Y
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk Y.1 Y.2).O))) ≤ e + 1 :=
    (topologicalKrullDim_subspace_le _ _).trans hdimY.le
  rw [twistedEulerMixedDifference_cons_eq_sub_denominatorQuotients.{u, w} B k hk Y fY hfY hdimO hwa
    hfin N t ht M]
  have hL' := Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hN
  have hIc := isCoherent_meromorphicDenominatorIdeal B (Spec (.of k)) hk Y N t hL' hwa hfin
  have hLc : IsCoherent B (Spec (.of k)) hk Y.1 Y.2 N :=
    { __ := isQuasicoherentOnSite_of_isInvertible B (Spec (.of k)) hk Y N hL'
      __ := isCoherentOnSite_of_isInvertible N hN }
  have hQ₁ : IsCoherent B (Spec (.of k)) hk Y.1 Y.2
      (meromorphicDenominatorQuotient B (Spec (.of k)) hk Y N t hL') :=
    isCoherent_cokernel B (Spec (.of k)) hk Y.1 Y.2 hIc inferInstance _
  have hQ₂ : IsCoherent B (Spec (.of k)) hk Y.1 Y.2
      (meromorphicNumeratorQuotient B (Spec (.of k)) hk Y N t hL') :=
    isCoherent_cokernel B (Spec (.of k)) hk Y.1 Y.2 hIc hLc _
  set Q₁ := meromorphicDenominatorQuotient B (Spec (.of k)) hk Y N t hL' with hQ₁def
  set Q₂ := meromorphicNumeratorQuotient B (Spec (.of k)) hk Y N t hL' with hQ₂def
  set T := moduleSupportSet B (Spec (.of k)) hk Y Q₁ ∪ moduleSupportSet B (Spec (.of k)) hk Y Q₂
    with hTdef
  have hTcl : IsClosed T :=
    (isClosed_supportOfSheaf_of_isCoherentOnSite B (Spec (.of k)) hk Y Q₁).union
      (isClosed_supportOfSheaf_of_isCoherentOnSite B (Spec (.of k)) hk Y Q₂)
  have : IrreducibleSpace (points B (Spec (.of k)) hk Y.1) := hint.2.2
  have : T0Space (points B (Spec (.of k)) hk Y.1) :=
    t0Space_points_of_isDecentSpace B (Spec (.of k)) hk Y.2 hdec
  set η := genericPoint B (Spec (.of k)) hk Y.2 hint with hηdef
  have hηgen := isGenericPoint_genericPoint B (Spec (.of k)) hk Y.2 hint
  have hηT : η ∉ T := by
    have hloc : localRingDimension B (Spec (.of k)) hk η = 0 := by
      rw [← codimension_eq_localRingDimension B (Spec (.of k)) hk Y.2 hdec
        ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩ η hηgen]
      exact Order.coheight_eq_zero.2 fun b _ => fun x _ => Set.mem_univ x
    obtain ⟨h₂, h₁⟩ := geometricLength_meromorphicQuotients_eq_zero_of_localRingDimension_eq_zero
      B (Spec (.of k)) hk Y hLN hwa hfin N hN t ht
      (canonicalGeometricPoint B (Spec (.of k)) hk Y.1 η)
      (by rw [canonicalGeometricPoint_image]; exact hloc)
    rintro (h | h)
    · have hpos := (geometricLength_pos_iff_image_mem B (Spec (.of k)) hk Y Q₁
        (canonicalGeometricPoint B (Spec (.of k)) hk Y.1 η)).2
        (by rw [canonicalGeometricPoint_image]; exact h)
      rw [h₁] at hpos
      exact lt_irrefl _ hpos
    · have hpos := (geometricLength_pos_iff_image_mem B (Spec (.of k)) hk Y Q₂
        (canonicalGeometricPoint B (Spec (.of k)) hk Y.1 η)).2
        (by rw [canonicalGeometricPoint_image]; exact h)
      rw [h₂] at hpos
      exact lt_irrefl _ hpos
  have hTne : T ≠ Set.univ := fun h => hηT (h ▸ Set.mem_univ η)
  have hTd : topologicalKrullDim T ≤ e :=
    topologicalKrullDim_le_of_isClosed_ne_univ hTcl hTne hdimY.le
  let x : irreducibleComponents T → GeometricPoint B (Spec (.of k)) hk Y.1 := fun C =>
    canonicalGeometricPoint B (Spec (.of k)) hk Y.1
      ((closedSetComponent B (Spec (.of k)) hk Y.2 hdec T hTcl C).ambientGenericPoint
        B (Spec (.of k)) hk)
  have hx : ∀ C, IsGenericPoint (x C).image (Subtype.val '' (C : Set T)) := by
    intro C
    have h := (closedSetComponent B (Spec (.of k)) hk Y.2 hdec T hTcl
      C).isGenericPoint_ambientGenericPoint B (Spec (.of k)) hk Y.2
    rw [subspacePointSet_closedSetComponent] at h
    rw [canonicalGeometricPoint_image]
    exact h
  rw [twistedEulerMixedDifference_eq_finsum_components_of_le.{u, w} k B hk Y fY hfY M Q₂ hQ₂ hTcl
      hTd x hx Set.subset_union_right,
    twistedEulerMixedDifference_eq_finsum_components_of_le.{u, w} k B hk Y fY hfY M Q₁ hQ₁ hTcl
      hTd x hx Set.subset_union_left]
  have := noetherianSpace_points_of_isProper_baseObject k B hk Y.1 Y.2 fY hfY
  have : Finite (irreducibleComponents T) :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype
  rw [← finsum_sub_distrib (Set.toFinite _) (Set.toFinite _)]
  set ratio := canonicalLocalRatioFamily B (Spec (.of k)) hk Y.2 hdec N hN hint hLN with hratio
  have hcoef : ∀ (Z : IntegralClosedSubspace B (Spec (.of k)) hk Y.1)
      (hcod : codimension (integralClosedSubspaceSupport B (Spec (.of k)) hk Y.2 Z) = 1)
      (xbar : GeometricPoint B (Spec (.of k)) hk Y.1)
      (hxbar : xbar.image = Z.ambientGenericPoint B (Spec (.of k)) hk),
      divisorCycleCoefficients (fieldSpaceSituation k B hk) fY hY hdec N t ratio Z =
        ((geometricLength B (Spec (.of k)) hk Y xbar Q₂).toNat : ℤ) -
          ((geometricLength B (Spec (.of k)) hk Y xbar Q₁).toNat : ℤ) := by
    intro Z hcod xbar hxbar
    rw [divisorCycleCoefficients_of_codimension_eq_one (fieldSpaceSituation k B hk) fY hY hdec N t
      ratio hcod]
    set P := Z.toPrimeDivisor B (Spec (.of k)) hk Y.2 hcod
    have hPgen :
        P.genericPoint B (Spec (.of k)) hk Y.1 = Z.ambientGenericPoint B (Spec (.of k)) hk :=
      (P.isGenericPoint_genericPoint B (Spec (.of k)) hk Y.1).eq
        (Z.isGenericPoint_ambientGenericPoint B (Spec (.of k)) hk Y.2)
    exact (toNat_geometricLength_numeratorQuotient_sub_eq_orderOfVanishingSection B
      (Spec (.of k)) hk Y hdec hint hLN hwa hfin N hN t ht P xbar (hxbar.trans hPgen.symm)).symm
  set δf := deltaDimensionFunction (fieldSpaceSituation k B hk) fY hY
  have hδf : ∀ y, δf y = (fieldSpaceSituation k B hk).deltaValue fY y :=
    deltaDimensionFunction_apply (fieldSpaceSituation k B hk) fY hY
  have hδη : (fieldSpaceSituation k B hk).deltaValue fY η = e + 1 := by
    have h := deltaDimensionClosed_univ_eq_deltaValue_genericPoint (fieldSpaceSituation k B hk) fY
      hY hint
    rw [hn] at h
    exact (WithBotTop.coe_injective h).symm
  have htfae := fun Z => (isPrimeDivisor_tfae_of_isIntegralSpace (fieldSpaceSituation k B hk) fY
    hY hint δf hδf hn Z).out 2 3
  have hδdim : ∀ Z : IntegralClosedSubspace B (Spec (.of k)) hk Y.1,
      dimension B (Spec (.of k)) hk Z.subspace.toFunctor Z.isClosedSubspace.1 = e ↔
        deltaDimension (fieldSpaceSituation k B hk) fY Z = e := by
    intro Z
    obtain ⟨h0, hdim⟩ := dimension_integralClosedSubspace_eq_deltaDimension k B hk Y hfY Z
    rw [hdim]
    constructor
    · intro h
      have h' : (deltaDimension (fieldSpaceSituation k B hk) fY Z).toNat = e := by exact_mod_cast h
      omega
    · intro h
      rw [h]
      simp
  let φ : {C : irreducibleComponents T //
      topologicalKrullDim (Subtype.val '' (C : Set T)) = e} →
      IntegralClosedSubspace B (Spec (.of k)) hk Y.1 := fun C =>
    closedSetComponent B (Spec (.of k)) hk Y.2 hdec T hTcl C.1
  have hφ : Function.Injective φ := by
    intro C₁ C₂ h
    have h' := congrArg (fun Z : IntegralClosedSubspace B (Spec (.of k)) hk Y.1 =>
      subspacePointSet B (Spec (.of k)) hk Y.1 Z.subspace) h
    simp only [φ, subspacePointSet_closedSetComponent] at h'
    exact Subtype.ext (Subtype.ext (Subtype.val_injective.image_injective h'))
  have hsupp : Function.support (fun Z : IntegralClosedSubspace B (Spec (.of k)) hk Y.1 =>
      divisorCycleCoefficients (fieldSpaceSituation k B hk) fY hY hdec N t ratio Z *
        integralClosedSubspaceIntersectionNumber.{u, w} k B hk Y fY hfY M Z) ⊆ Set.range φ := by
    intro Z hZ
    have hc : divisorCycleCoefficients (fieldSpaceSituation k B hk) fY hY hdec N t ratio Z ≠ 0 :=
      left_ne_zero_of_mul hZ
    have hcod : codimension (integralClosedSubspaceSupport B (Spec (.of k)) hk Y.2 Z) = 1 := by
      by_contra h
      exact hc (divisorCycleCoefficients_of_codimension_ne_one (fieldSpaceSituation k B hk) fY hY
        hdec N t ratio h)
    set ξ := Z.ambientGenericPoint B (Spec (.of k)) hk with hξdef
    have hZgen := Z.isGenericPoint_ambientGenericPoint B (Spec (.of k)) hk Y.2
    have hξT : ξ ∈ T := by
      by_contra hξ
      apply hc
      rw [hcoef Z hcod (canonicalGeometricPoint B (Spec (.of k)) hk Y.1 ξ)
        (canonicalGeometricPoint_image _ _ _ _ _),
        geometricLength_eq_zero_of_image_notMem B (Spec (.of k)) hk Y Q₂ _
          (by rw [canonicalGeometricPoint_image]; exact fun h => hξ (Or.inr h)),
        geometricLength_eq_zero_of_image_notMem B (Spec (.of k)) hk Y Q₁ _
          (by rw [canonicalGeometricPoint_image]; exact fun h => hξ (Or.inl h))]
      rfl
    obtain ⟨C, hC, hξC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
      ({⟨ξ, hξT⟩} : Set T) isIrreducible_singleton
    let C' : irreducibleComponents T := ⟨C, hC⟩
    set ZC := closedSetComponent B (Spec (.of k)) hk Y.2 hdec T hTcl C' with hZCdef
    have hgenC : IsGenericPoint (ZC.ambientGenericPoint B (Spec (.of k)) hk)
        (Subtype.val '' C) := by
      have h := ZC.isGenericPoint_ambientGenericPoint B (Spec (.of k)) hk Y.2
      rw [hZCdef, subspacePointSet_closedSetComponent] at h
      exact h
    have hξmem : ξ ∈ Subtype.val '' C := ⟨⟨ξ, hξT⟩, hξC rfl, rfl⟩
    have hspec := hgenC.specializes hξmem
    have hξCT : ZC.ambientGenericPoint B (Spec (.of k)) hk ∈ T :=
      Subtype.coe_image_subset _ _ hgenC.mem
    have hηspec : η ⤳ ZC.ambientGenericPoint B (Spec (.of k)) hk :=
      hηgen.specializes (Set.mem_univ _)
    have hne : η ≠ ZC.ambientGenericPoint B (Spec (.of k)) hk := fun h => hηT (h ▸ hξCT)
    have h1 := δf.strictAnti_specializes hηspec hne
    have hδZ : deltaDimension (fieldSpaceSituation k B hk) fY Z = e := by
      rw [(htfae Z).1 hcod]
      ring
    have hδξ : (fieldSpaceSituation k B hk).deltaValue fY ξ = e := by
      rw [← deltaDimension_eq_of_isGenericPoint (fieldSpaceSituation k B hk) fY Y.2 Z ξ hZgen]
      exact hδZ
    have hξeq : ZC.ambientGenericPoint B (Spec (.of k)) hk = ξ := by
      by_contra hneq
      have h2 := δf.strictAnti_specializes hspec hneq
      rw [hδf, hδf] at h2
      rw [hδf, hδf] at h1
      omega
    have hZeq : ZC = Z := by
      refine eq_closedSetComponent B (Spec (.of k)) hk Y.2 hdec T hTcl C' Z ?_
      have h : closure {ξ} = Subtype.val '' (C' : Set T) := by
        rw [← hξeq]
        exact hgenC.def
      exact hZgen.def.symm.trans h
    have hdimC : topologicalKrullDim (Subtype.val '' (C' : Set T)) = e := by
      have h := dimension_eq_topologicalKrullDim_range_of_isClosedImmersion B (Spec (.of k)) hk Y.2
        hdec Z.isClosedSubspace.1 Z.subspace.ι Z.isClosedSubspace.2
      change _ = topologicalKrullDim (subspacePointSet B (Spec (.of k)) hk Y.1 Z.subspace) at h
      rw [← hZeq, hZCdef, subspacePointSet_closedSetComponent] at h
      rw [← h]
      have h' := (hδdim Z).2 hδZ
      rw [← hZeq] at h'
      exact h'
    exact ⟨⟨C', hdimC⟩, hZeq⟩
  conv_rhs => rw [← finsum_mem_univ, finsum_mem_inter_support_eq' _ Set.univ (Set.range φ)
    (fun Z hZ => ⟨fun _ => hsupp hZ, fun _ => Set.mem_univ _⟩), finsum_mem_range hφ]
  refine finsum_congr fun C => ?_
  have hdimφ :
      dimension B (Spec (.of k)) hk (φ C).subspace.toFunctor (φ C).isClosedSubspace.1 = e :=
    (dimension_reducedClosedSubspace B (Spec (.of k)) hk Y.1 Y.2 hdec (Subtype.val '' (C.1 : Set T))
      (closedSetComponentPoints B (Spec (.of k)) hk T hTcl C.1).isClosed).trans C.2
  have hcod : codimension (integralClosedSubspaceSupport B (Spec (.of k)) hk Y.2 (φ C)) = 1 :=
    (htfae (φ C)).2 (by rw [(hδdim (φ C)).1 hdimφ]; ring)
  rw [integralClosedSubspaceIntersectionNumber_of_dimension_eq.{u, w} k B hk Y fY hfY M (φ C)
      hdimφ,
    hcoef (φ C) hcod (x C.1) (canonicalGeometricPoint_image _ _ _ _ _), ← sub_mul]
  rfl

end AlgebraicGeometry.Space

end
