module

public import StacksFrontier.AlgebraicGeometry.Blowup.ClassifyingMorphism
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassOfSection.TotalChern
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.MaximalDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.SmoothIntersectionProductMixed
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.CodimensionClasses
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecializationRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.TensorPowerSums
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionZeroScheme
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Codimension
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.UFDExtension
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionCycleClass

/-!
# The first Chern class of `𝒪_X(D)` against the fundamental class

Let `k` be a field, let `X` be a scheme smooth and quasi-compact over `k` and let `D ⊆ X` be an
effective Cartier divisor. This file proves

  `ch_1(𝒪_X(D)) ∩ [X] = [D]`   in   `CH_*(X) ⊗ 𝐐`,

where `[D]` is the codimension-one class `Stacks.WeilCohomology.closedSubschemeClass` of `D`,
read in `CH_*(X) ⊗ 𝐐` through `Stacks.Chow.codimensionToRationalChow`. Part by part this is
Stacks 0FA9 in rank one
(`Stacks.Chow.totalChernOfFiniteLocallyFree_cap_fundamentalCycle_eq_zeroSchemeCycle`) for the
canonical section `1_D` of `𝒪_X(D)`, whose zero scheme is `D` (Stacks 01X0): on the part `X_d` of
dimension `d` the ideal of `D` is generated at every point by a nonzerodivisor, and the components
of `D ∩ X_d` have dimension `d - 1` (Stacks 0BCN).

## Main results

* `Stacks.Chow.chowCohomologyCap_firstChern_divisorSheaf_dimPart` — on the part `X_d`,
  `c_1(𝒪_X(D)) ∩ [X_d]_d = [D ∩ X_d]_{d-1}`.
* `Stacks.Chow.codimensionToRationalChow_closedSubschemeClass_eq_chernCharacterCap` —
  `[D] = ch_1(𝒪_X(D)) ∩ [X]` in `CH_*(X) ⊗ 𝐐`.

## References

* [Stacks Project, Tag 0FA9](https://stacks.math.columbia.edu/tag/0FA9)
* [Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0)
* [Stacks Project, Tag 0BCN](https://stacks.math.columbia.edu/tag/0BCN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace Stacks.Chow

open Stacks.WeilCohomology (dimPart partBase relativeDimension_partBase
  isClopenDecomposition_dimPart closedSubschemeClass closedSubschemeClass_apply)

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  [LocallyOfFiniteType sX] [Smooth sX] (D : X.IdealSheafData)
  [Stacks.Divisors.IsEffectiveCartierDivisor D]

/-- `𝒪_X(D)` is finite locally free of rank one, being invertible. -/
theorem isFiniteLocallyFreeOfRank_divisorSheaf :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Stacks.Divisors.divisorSheaf D) 1 :=
  isFiniteLocallyFreeOfRank_one_of_isInvertible _

/-- `𝒪_X(D)` is finite locally free. -/
theorem isFiniteLocallyFree_divisorSheaf :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Stacks.Divisors.divisorSheaf D) :=
  have := isFiniteLocallyFreeOfRank_divisorSheaf D
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1

attribute [local instance] isFiniteLocallyFreeOfRank_divisorSheaf isFiniteLocallyFree_divisorSheaf

/-- The pullback to the part `X_d` of the canonical section `1_D` of `𝒪_X(D)`. -/
abbrev dimPartCanonicalSection (d : ℕ) :
    Γ((Scheme.Modules.pullback (dimPart sX d).ι).obj (Stacks.Divisors.divisorSheaf D), ⊤) :=
  pullbackGlobalSections (dimPart sX d).ι (Stacks.Divisors.divisorSheaf D)
    (Stacks.Divisors.divisorSheafGlobalSection D)

omit [LocallyOfFiniteType sX] in
/-- The zero scheme of the pulled back canonical section is the inverse image `D ∩ X_d` of `D`. -/
theorem zeroScheme_dimPartCanonicalSection (d : ℕ) :
    haveI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (Stacks.Divisors.divisorSheaf D) 1 :=
      isFiniteLocallyFreeOfRank_one_of_isInvertible _
    RegularSectionSequence.zeroScheme (dimPart sX d).toScheme
        ((Scheme.Modules.pullback (dimPart sX d).ι).obj (Stacks.Divisors.divisorSheaf D))
        (dimPartCanonicalSection sX D d) = D.comap (dimPart sX d).ι := by
  rw [RegularSectionSequence.zeroScheme_pullbackGlobalSections _ _ 1]
  exact congrArg (fun I : X.IdealSheafData => I.comap (dimPart sX d).ι)
    (Stacks.Divisors.zeroScheme_canonicalSection D)

omit [LocallyOfFiniteType sX] in
/-- **The ideal of `D ∩ X_d` is generated at every point by a nonzerodivisor**, read as a regular
sequence of length one: the ideal of `D` is so generated in `𝒪_{X, x}` (Stacks 01WS), and the
stalk map of the open immersion `X_d ⟶ X` is an isomorphism carrying it to the ideal of the
inverse image. -/
theorem exists_isRegular_ker_stalkMap_comap_dimPart (d : ℕ)
    (ξ : (D.comap (dimPart sX d).ι).subscheme) :
    ∃ rs : List ((dimPart sX d).toScheme.presheaf.stalk
        ((D.comap (dimPart sX d).ι).subschemeι ξ)),
      rs.length = 1 ∧
        RingTheory.Sequence.IsRegular
          ((dimPart sX d).toScheme.presheaf.stalk ((D.comap (dimPart sX d).ι).subschemeι ξ)) rs ∧
        Ideal.ofList rs = RingHom.ker ((D.comap (dimPart sX d).ι).subschemeι.stalkMap ξ).hom := by
  obtain ⟨f, hf, hspan⟩ :=
    AlgebraicGeometry.exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor D ‹_›
      ((dimPart sX d).ι ((D.comap (dimPart sX d).ι).subschemeι ξ))
  let e := (asIso ((dimPart sX d).ι.stalkMap
    ((D.comap (dimPart sX d).ι).subschemeι ξ))).commRingCatIsoToRingEquiv
  let g := e f
  have hker : RingHom.ker ((D.comap (dimPart sX d).ι).subschemeι.stalkMap ξ).hom =
      Ideal.span {g} := by
    rw [ker_stalkMap_subschemeι_eq_stalk, AlgebraicGeometry.stalk_comap, hspan, Ideal.map_span,
      Set.image_singleton]
    rfl
  have hg : IsSMulRegular ((dimPart sX d).toScheme.presheaf.stalk
      ((D.comap (dimPart sX d).ι).subschemeι ξ)) g := by
    intro a b hab
    have h := congrArg e.symm hab
    simp only [smul_eq_mul, map_mul] at h
    rw [show e.symm g = f from e.symm_apply_apply f] at h
    exact e.symm.injective (hf.1 h)
  refine ⟨[g], rfl, ⟨(RingTheory.Sequence.isWeaklyRegular_singleton_iff _ g).mpr hg, ?_⟩, ?_⟩
  · rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.ofList_singleton, ← hker]
    exact (RingHom.ker_ne_top _).symm
  · rw [Ideal.ofList_singleton, hker]

/-- **The regular-sequence hypothesis of Stacks 0FA9** for the canonical section of `𝒪_X(D)`
pulled back to the part `X_d`, in rank one. -/
theorem isRegularSequenceOnZeroScheme_dimPartCanonicalSection (d : ℕ) (m : ℤ) :
    IsRegularSequenceOnZeroScheme (fieldChowSituation k) (partBase sX d)
      ((Scheme.Modules.pullback (dimPart sX d).ι).obj (Stacks.Divisors.divisorSheaf D))
      (dimPartCanonicalSection sX D d) 1 m := by
  have key : ∀ I : (dimPart sX d).toScheme.IdealSheafData, I = D.comap (dimPart sX d).ι →
      ∀ ξ : I.subscheme, ∃ rs : List ((dimPart sX d).toScheme.presheaf.stalk (I.subschemeι ξ)),
        rs.length = 1 ∧
          RingTheory.Sequence.IsRegular ((dimPart sX d).toScheme.presheaf.stalk (I.subschemeι ξ))
            rs ∧ Ideal.ofList rs = RingHom.ker (I.subschemeι.stalkMap ξ).hom := by
    rintro I rfl ξ
    exact exists_isRegular_ker_stalkMap_comap_dimPart sX D d ξ
  intro ξ _
  exact key _ (zeroScheme_dimPartCanonicalSection sX D d) ξ.1

/-- The part `X_d` has delta-dimension at most `d`. -/
theorem schemeDeltaDimension_partBase_le (d : ℕ) :
    schemeDeltaDimension (fieldChowSituation k) (partBase sX d) ≤ ((d : ℤ) : EInt) := by
  simpa only [Category.id_comp] using
    schemeDeltaDimension_le_of_forall_relativeDimension_le (fieldChowSituation k)
      (partBase sX d) (𝟙 _) (k := (d : ℤ)) fun w => by
        have h1 := (ringKrullDim_stalk_of_relativeDimension k (partBase sX d)
          (relativeDimension_partBase sX d) ((𝟙 (dimPart sX d).toScheme : _ ⟶ _) w)).1
        have h0 := relativeDimension_fieldChowSituation_nonneg k (partBase sX d)
          ((𝟙 (dimPart sX d).toScheme : _ ⟶ _) w)
        omega

/-- **The divisor `D ∩ X_d` has delta-dimension at most `d - 1`**: at the generic point of each of
its components the local ring of `X_d` has dimension one (Stacks 0BCN), and on `X_d` the
dimension of the local ring and the delta-dimension add up to `d`. -/
theorem schemeDeltaDimension_comap_dimPart_le (d : ℕ) :
    schemeDeltaDimension (fieldChowSituation k)
        ((D.comap (dimPart sX d).ι).subschemeι ≫ partBase sX d) ≤
      (((d : ℤ) - ((1 : ℕ) : ℤ) : ℤ) : EInt) := by
  have : IsLocallyNoetherian (dimPart sX d).toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian (partBase sX d)
  have key : ∀ ξ : (D.comap (dimPart sX d).ι).subscheme,
      (∃ Z : irreducibleComponents (D.comap (dimPart sX d).ι).subscheme,
        IsGenericPoint ξ (Z : Set (D.comap (dimPart sX d).ι).subscheme)) →
      relativeDimension (fieldChowSituation k).dimensionFunction (partBase sX d)
        ((D.comap (dimPart sX d).ι).subschemeι ξ) ≤ (d : ℤ) - ((1 : ℕ) : ℤ) := by
    intro ξ hξ
    have h1 := AlgebraicGeometry.ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor _
      (Stacks.Blowup.isEffectiveCartierDivisor_comap_of_isOpenImmersion D ‹_› (dimPart sX d).ι) ξ hξ
    obtain ⟨hle, hdim⟩ := ringKrullDim_stalk_of_relativeDimension k (partBase sX d)
      (relativeDimension_partBase sX d) ((D.comap (dimPart sX d).ι).subschemeι ξ)
    have h0 := relativeDimension_fieldChowSituation_nonneg k (partBase sX d)
      ((D.comap (dimPart sX d).ι).subschemeι ξ)
    rw [h1] at hdim
    have h2 : (1 : ℕ) = d - (relativeDimension (fieldChowSituation k).dimensionFunction
        (partBase sX d) ((D.comap (dimPart sX d).ι).subschemeι ξ)).toNat :=
      mod_cast hdim
    omega
  rw [schemeDeltaDimension_eq_iSup]
  refine iSup_le fun V => WithBotTop.coe_le_coe.mpr ?_
  rw [deltaDimension, relativeDimension_comp_closedImmersion]
  refine key _ ⟨V, ?_⟩
  change closure _ = _
  exact (V.2.1.isGenericPoint_genericPoint_closure).trans
    (isClosed_of_mem_irreducibleComponents _ V.2).closure_eq

omit [Divisors.IsEffectiveCartierDivisor D] in
/-- The restriction to `X_d` of the cycle of `D` is the cycle of `D ∩ X_d`. -/
theorem chowGroupRestrict_mk_cycleAssociatedToClosedSubscheme_dimPart (d : ℕ) (m : ℤ) :
    chowGroupRestrict (fieldChowSituation k) sX (partBase sX d) (dimPart sX d).ι rfl m
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX
          D.subschemeι m)) =
      QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) (partBase sX d) m)
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) (partBase sX d)
          (D.comap (dimPart sX d).ι).subschemeι m) := by
  change chowGroupRestrict (fieldChowSituation k) sX (partBase sX d) (dimPart sX d).ι rfl m
      (QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) sX m) _) = _
  rw [chowGroupRestrict_mk]
  congr 1
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y => ?_)
  rw [cycleGroupRestrict_apply, cycleAssociatedToClosedSubscheme_comap_of_isOpenImmersion
    (fieldChowSituation k) sX (partBase sX d) (dimPart sX d).ι rfl D m y]

/-- **`c_1(𝒪_X(D)) ∩ [X_d]_d = [D ∩ X_d]_{d-1}` on the part `X_d`**, for the first Chern class of
`𝒪_X(D)` restricted to `X_d`: Stacks 0FA9 in rank one, at the test scheme `X_d ⟶ X`, for the
pullback of the canonical section `1_D`, whose zero scheme is `D ∩ X_d`. -/
theorem chowCohomologyCap_firstChern_divisorSheaf_dimPart (d : ℕ) :
    chowCohomologyCap (fieldChowSituation k) (gysinSystemOfInvertible _) (partBase sX d)
        ((1 : ℕ) : ℤ)
        (chowCohomologyRestrictionOfEq (fieldChowSituation k) (partBase sX d) sX
          (f := (dimPart sX d).ι) rfl (gysinSystemOfInvertible _)
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _) ((1 : ℕ) : ℤ)
          (totalChernOfFiniteLocallyFree (fieldChowSituation k) sX
            (Stacks.Divisors.divisorSheaf D) 1)) d
        (fundamentalChowClass (fieldChowSituation k) (partBase sX d) d) =
      chowGroupRestrict (fieldChowSituation k) sX (partBase sX d) (dimPart sX d).ι rfl
        ((d : ℤ) - ((1 : ℕ) : ℤ))
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX
          D.subschemeι ((d : ℤ) - ((1 : ℕ) : ℤ)))) := by
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (dimPart sX d).ι).obj (Stacks.Divisors.divisorSheaf D)) 1 :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ 1
  have hZ := schemeDeltaDimension_comap_dimPart_le sX D d
  rw [← zeroScheme_dimPartCanonicalSection sX D d] at hZ
  rw [chowCohomologyCap_restrictionOfEq,
    chowGroupRestrict_mk_cycleAssociatedToClosedSubscheme_dimPart]
  refine (totalChernOfFiniteLocallyFree_cap_fundamentalCycle_eq_zeroSchemeCycle
    (fieldChowSituation k) sX (Stacks.Divisors.divisorSheaf D) 1 (dimPart sX d).ι
    (dimPartCanonicalSection sX D d) d (schemeDeltaDimension_partBase_le sX d) hZ
    (isRegularSequenceOnZeroScheme_dimPartCanonicalSection sX D d _)).trans ?_
  rw [zeroScheme_dimPartCanonicalSection sX D d]

omit [Smooth sX] in
/-- `ch_1(𝒪_X(D)) = c_1(𝒪_X(D))`, `𝒪_X(D)` being invertible: `P_1 = c_1` in rank one. -/
theorem chernCharacterVectorBundle_classOf_divisorSheaf_one :
    chernCharacterVectorBundle (fieldChowSituation k) sX
        (VectorBundleKZero.classOf X (Stacks.Divisors.divisorSheaf D)) 1 =
      (1 : ℚ) ⊗ₜ[ℤ] totalChernOfFiniteLocallyFree (fieldChowSituation k) sX
        (Stacks.Divisors.divisorSheaf D) 1 := by
  rw [chernCharacterVectorBundle_apply, powerSumKHom_classOf,
    powerSumOfFiniteLocallyFree_eq_powerSumTotal _ _ _ 1, powerSumTotal_of_rank_one, pow_one,
    TotalChowClass.homComponent_apply, ite_eq_left rfl,
    totalChernOfFiniteLocallyFree_eq_totalChern _ _ _ 1,
    show ((Nat.factorial 1 : ℕ) : ℚ)⁻¹ = 1 by norm_num]

/-- **`ch_1(𝒪_X(D)) ∩ [X] = [D]` in `CH_*(X) ⊗ 𝐐`** for an effective Cartier divisor `D` on a
scheme `X` smooth and quasi-compact over a field: the codimension-one class of `D` is the cap of
the first Chern character of `𝒪_X(D)` with the fundamental class. Part by part, both sides are
`c_1(𝒪_X(D)) ∩ [X_d]_d = [D ∩ X_d]_{d-1}`. -/
theorem codimensionToRationalChow_closedSubschemeClass_eq_chernCharacterCap [CompactSpace X] :
    haveI := isNoetherian_of_compactSpace sX
    codimensionToRationalChow k sX 1 (closedSubschemeClass sX D.subschemeι 1) =
      rationalChernCharacterComponentCap (fieldChowSituation k) sX 1
        (1 ⊗ₜ VectorBundleKZero.classOf X (Stacks.Divisors.divisorSheaf D))
        (rationalFundamentalClass (fieldChowSituation k) sX) := by
  have := isNoetherian_of_compactSpace sX
  rw [rationalChernCharacterComponentCap_tmul, one_smul,
    chernCharacterVectorBundle_classOf_divisorSheaf_one]
  conv_rhs => rw [← sum_rationalIncludePart_rationalRestrictPart k sX
    (rationalFundamentalClass (fieldChowSituation k) sX)]
  rw [map_sum, codimensionToRationalChow_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [rationalRestrictPart_rationalFundamentalClass,
    rationalFundamentalClass_eq_of_relativeDimension k (partBase sX d)
      (relativeDimension_partBase sX d), ← rationalIncludePart_rationalChowCap,
    LinearMap.baseChange_tmul, rationalChowCap_of_tmul, one_mul, AddMonoidHom.coe_toIntLinearMap,
    chowCohomologyCap_firstChern_divisorSheaf_dimPart, closedSubschemeClass_apply]
  rfl

end Stacks.Chow

end
