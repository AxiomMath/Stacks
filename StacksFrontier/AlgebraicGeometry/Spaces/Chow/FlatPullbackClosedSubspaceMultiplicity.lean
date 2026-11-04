module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackCycleComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.InverseImageDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.MaximalDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackGeometricLength
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.RingTheory.Length.FlatLocalHom

/-!
# Multiplicativity of the multiplicity of a closed subspace along a flat morphism

In Situation 0EDT let `X/B` and `Y/B` be good, let `f : X ⟶ Y` be flat of relative dimension
`r` over the base and let `Y' ⊆ Y` be a closed subspace with `dim_δ(Y') ≤ m`. Writing `[Y']_m`
over the top-dimensional components `V` of `Y'` as Stacks 0EE9 does, the multiplicity of an
integral closed subspace `T ⊆ X` in the inverse image `f^{-1}(Y')` satisfies

`m_{T, f^{-1}(Y')} = ∑_V m_{V, Y'} · m_{T, f^{-1}(V)}`,

the sum over those components, whenever the three multiplicities are the lengths `length_A(A/I)`,
`length_B(B/𝔪_A B)` and `length_B(B/IB)` for a flat local homomorphism `A → B` of local rings and
an ideal `I ⊆ A`. This is the coefficientwise form of the cycle identity
`[f^{-1}(Y')]_{m+r} = f^*[Y']_m` of Stacks 0EPB, part (1).

## Main results

* `Ring.length_quotient_mul_length_quotient_maximalIdeal_map`: for a flat local homomorphism
  `A → B` of local rings and an ideal `I ⊆ A`,
  `length_A(A/I) · length_B(B/𝔪_A B) = length_B(B/IB)` in `ℕ∞`.
* `Ring.toNat_length_quotient_mul_toNat_length_quotient_maximalIdeal_map`: the same identity of
  integers, when `length_B(B/IB)` is finite.
* `AlgebraicGeometry.Space.inducedDimensionValue_image_ambientGenericPoint_eq`: the generic
  point of a subspace occurring in `f^*[V]` lies over a point of δ-dimension exactly `m`.
* `AlgebraicGeometry.Space.topComponentSubspaces_eq_of_flatPullbackMult_ne_zero`: two
  top-dimensional components of `Y'` whose flat pullbacks both contain `T` are equal.
* `AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace_preimage_eq_finsum_of_deltaDimension_ne`:
  if `T` does not have δ-dimension `m + r`, both sides of the identity vanish.
* `AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace_preimage_eq_finsum_of_length`: the
  identity, given the three multiplicities as lengths along a flat local homomorphism of local
  rings.
* `AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace_preimage_eq_finsum_of_etaleLocalRingLength`:
  the identity, given the three multiplicities as lengths over the étale local rings of `Y` and
  `X` at a geometric point of `X` and its image, along the canonical homomorphism of
  Stacks 04NG.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1)
* [Stacks Project, Tag 02M2](https://stacks.math.columbia.edu/tag/02M2)
* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
* [Stacks Project, Tag 0EE4](https://stacks.math.columbia.edu/tag/0EE4)
* [Stacks Project, Tag 0EE6](https://stacks.math.columbia.edu/tag/0EE6)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0EP5](https://stacks.math.columbia.edu/tag/0EP5)
* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 0EPA](https://stacks.math.columbia.edu/tag/0EPA)
* [Stacks Project, Tag 0EPB](https://stacks.math.columbia.edu/tag/0EPB)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace Ring

/-- **Multiplicativity of length along a flat local homomorphism, at a quotient.** Let `φ : A → B`
be a flat local homomorphism of local rings and let `I ⊆ A` be an ideal. Then

`length_A(A/I) · length_B(B/𝔪_A B) = length_B(B/IB)`,

an identity in `ℕ∞`. -/
@[ega "IV 2.5.5.1" "special case", ega "IV 4.7.1" "cyclic modules", ega "IV 4.7.2" "special case"]
theorem length_quotient_mul_length_quotient_maximalIdeal_map {A B : Type*} [CommRing A]
    [CommRing B] [IsLocalRing A] [IsLocalRing B] {φ : A →+* B} (hloc : IsLocalHom φ)
    (hflat : φ.Flat) (I : Ideal A) :
    Module.length A (A ⧸ I) *
        Module.length B (B ⧸ Ideal.map φ (IsLocalRing.maximalIdeal A)) =
      Module.length B (B ⧸ Ideal.map φ I) := by
  let : Algebra A B := φ.toAlgebra
  have halg : algebraMap A B = φ := rfl
  have : IsLocalHom (algebraMap A B) := halg ▸ hloc
  have : Module.Flat A B := hflat
  have key := IsLocalRing.length_baseChange A B (A ⧸ I)
  rw [halg] at key
  rw [← key, length_baseChange_quotient_eq φ I]

/-- **Multiplicativity of length along a flat local homomorphism, as an identity of integers.** Let
`φ : A → B` be a flat local homomorphism of local rings and let `I ⊆ A` be an ideal such that
`length_B(B/IB)` is finite. Then, the lengths being read through `ENat.toNat`,

`length_A(A/I) · length_B(B/𝔪_A B) = length_B(B/IB)`

in `ℤ`. -/
theorem toNat_length_quotient_mul_toNat_length_quotient_maximalIdeal_map {A B : Type*}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] {φ : A →+* B}
    (hloc : IsLocalHom φ) (hflat : φ.Flat) (I : Ideal A)
    (hfin : Module.length B (B ⧸ Ideal.map φ I) ≠ ⊤) :
    ((Module.length A (A ⧸ I)).toNat : ℤ) *
        ((Module.length B (B ⧸ Ideal.map φ (IsLocalRing.maximalIdeal A))).toNat : ℤ) =
      ((Module.length B (B ⧸ Ideal.map φ I)).toNat : ℤ) := by
  have := hloc
  have key := length_quotient_mul_length_quotient_maximalIdeal_map hloc hflat I
  have hcne : Module.length B (B ⧸ Ideal.map φ (IsLocalRing.maximalIdeal A)) ≠ 0 := by
    rw [ne_eq, Module.length_eq_zero_iff, not_subsingleton_iff_nontrivial]
    exact Ideal.Quotient.nontrivial_iff.mpr
      (ne_of_lt (IsLocalRing.map_maximalIdeal_lt_top φ))
  rcases eq_or_ne (Module.length A (A ⧸ I)) 0 with ha | ha
  · rw [← key, ha, zero_mul]
    simp
  · have hane : Module.length A (A ⧸ I) ≠ ⊤ := by
      intro h
      rw [← key, h, ENat.top_mul hcne] at hfin
      exact hfin rfl
    have hcfin : Module.length B (B ⧸ Ideal.map φ (IsLocalRing.maximalIdeal A)) ≠ ⊤ := by
      intro h
      rw [← key, h, ENat.mul_top ha] at hfin
      exact hfin rfl
    obtain ⟨na, hna⟩ := ENat.ne_top_iff_exists.mp hane
    obtain ⟨nc, hnc⟩ := ENat.ne_top_iff_exists.mp hcfin
    rw [← key, ← hna, ← hnc]
    simp

end Ring

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (Y' : Subfunctor Y) (hY' : IsClosedSubspace D.site D.base D.base_mem Y') (m : ℤ)

/-! ### The image of the generic point has δ-dimension exactly `m` -/

/-- The points of the image in `Y` of an integral closed subspace of `Y'` lie in `Y'`. -/
private theorem subspacePointSet_closedSubspaceComponentImage_subset
    (V : IntegralClosedSubspace D.site D.base D.base_mem Y'.toFunctor) :
    subspacePointSet D.site D.base D.base_mem Y
        (closedSubspaceComponentImage D sY hY Y' hY' V).subspace ⊆
      subspacePointSet D.site D.base D.base_mem Y Y' := by
  rw [IntegralClosedSubspace.subspacePointSet_pushforward]
  exact Set.image_subset_range _ _

/-- **The δ-dimension of the image of the generic point.** Let `Y' ⊆ Y` be a closed subspace with
`dim_δ(Y') ≤ m`, let `V` be an integral closed subspace of `Y'` whose image in `Y` has δ-dimension
`m`, and let `T ⊆ X` be an integral closed subspace occurring in `f^*[V]`. Then the image under `f`
of the generic point of `T` has induced dimension exactly `m`. -/
theorem inducedDimensionValue_image_ambientGenericPoint_eq
    (hdim : deltaDimensionSubspace D sY hY Y' hY' ≤ (m : EInt))
    (V : topComponentSubspaces D sY hY Y' hY' m)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hT : flatPullbackMult D sX hX sY hY f hbase r hflat hr
      (closedSubspaceComponentImage D sY hY Y' hY' V.1) T ≠ 0) :
    inducedDimensionValue D.site D.base D.base_mem D.delta sY
        (pointsMap D.site D.base D.base_mem X f
          (T.ambientGenericPoint D.site D.base D.base_mem)) = m := by
  have hcl : IsClosed (subspacePointSet D.site D.base D.base_mem Y Y') :=
    isClosed_subspacePointSet_of_isClosedSubspace D hY.1 Y' hY'
  have hmemV := mem_subspacePointSet_of_flatPullbackMult_ne_zero D sX hX sY hY f hbase r
    hflat hr (closedSubspaceComponentImage D sY hY Y' hY' V.1) T hT
  have hdim' : deltaDimensionClosed D sY hY
      (subspacePointSet D.site D.base D.base_mem Y Y') hcl ≤ (m : EInt) := hdim
  have hupper := (deltaDimensionClosed_le_coe_iff D sY hY
    (subspacePointSet D.site D.base D.base_mem Y Y') hcl m).1 hdim' _
    (subspacePointSet_closedSubspaceComponentImage_subset D sY hY Y' hY' V.1 hmemV)
  have hTval : inducedDimensionValue D.site D.base D.base_mem D.delta sX
      (T.ambientGenericPoint D.site D.base D.base_mem) = m + (r : ℤ) := by
    show deltaDimension D sX T = m + (r : ℤ)
    rw [deltaDimension_eq_of_flatPullbackMult_ne_zero D sX hX sY hY f hbase r hflat hr
      (closedSubspaceComponentImage D sY hY Y' hY' V.1) T hT, V.2]
  have hle := inducedDimensionValue_le_add_of_hasRelativeDimension D sX hX sY hY f hbase r hr
    (T.ambientGenericPoint D.site D.base D.base_mem)
  omega

/-! ### At most one top component contributes -/

/-- **At most one top-dimensional component contributes.** Let `Y' ⊆ Y` be a closed subspace with
`dim_δ(Y') ≤ m` and let `T ⊆ X` be an integral closed subspace. If `T` occurs in the flat pullbacks
`f^*[V₁]` and `f^*[V₂]` of two top-dimensional components of `Y'`, then `V₁ = V₂`. -/
theorem topComponentSubspaces_eq_of_flatPullbackMult_ne_zero
    (hdim : deltaDimensionSubspace D sY hY Y' hY' ≤ (m : EInt))
    (T : IntegralClosedSubspace D.site D.base D.base_mem X)
    (V₁ V₂ : topComponentSubspaces D sY hY Y' hY' m)
    (h₁ : flatPullbackMult D sX hX sY hY f hbase r hflat hr
      (closedSubspaceComponentImage D sY hY Y' hY' V₁.1) T ≠ 0)
    (h₂ : flatPullbackMult D sX hX sY hY f hbase r hflat hr
      (closedSubspaceComponentImage D sY hY Y' hY' V₂.1) T ≠ 0) :
    V₁ = V₂ := by
  classical
  have hcl : IsClosed (subspacePointSet D.site D.base D.base_mem Y Y') :=
    isClosed_subspacePointSet_of_isClosedSubspace D hY.1 Y' hY'
  have hm₁ := mem_subspacePointSet_of_flatPullbackMult_ne_zero D sX hX sY hY f hbase r
    hflat hr (closedSubspaceComponentImage D sY hY Y' hY' V₁.1) T h₁
  have hm₂ := mem_subspacePointSet_of_flatPullbackMult_ne_zero D sX hX sY hY f hbase r
    hflat hr (closedSubspaceComponentImage D sY hY Y' hY' V₂.1) T h₂
  have hmem : pointsMap D.site D.base D.base_mem X f
      (T.ambientGenericPoint D.site D.base D.base_mem) ∈
      subspacePointSet D.site D.base D.base_mem Y Y' :=
    subspacePointSet_closedSubspaceComponentImage_subset D sY hY Y' hY' V₁.1 hm₁
  have hval := inducedDimensionValue_image_ambientGenericPoint_eq D sX hX sY hY f hbase r
    hflat hr Y' hY' m hdim V₁ T h₁
  have hdim' : deltaDimensionClosed D sY hY
      (subspacePointSet D.site D.base D.base_mem Y Y') hcl ≤ (m : EInt) := hdim
  obtain ⟨C, hC⟩ := isGenericPoint_of_deltaDimensionClosed_le D sY hY
    (subspacePointSet D.site D.base D.base_mem Y Y') hcl _ hmem m hdim' hval
  obtain ⟨C₁, hC₁⟩ := exists_irreducibleComponents_closedSubspaceComponentImage D sY hY Y' hY'
    m hdim V₁.1 V₁.2
  obtain ⟨C₂, hC₂⟩ := exists_irreducibleComponents_closedSubspaceComponentImage D sY hY Y' hY'
    m hdim V₂.1 V₂.2
  have key : ∀ (Cv : irreducibleComponents (subspacePointSet D.site D.base D.base_mem Y Y')),
      (⟨pointsMap D.site D.base D.base_mem X f
          (T.ambientGenericPoint D.site D.base D.base_mem), hmem⟩ :
        subspacePointSet D.site D.base D.base_mem Y Y') ∈ (Cv : Set _) →
      (C : Set (subspacePointSet D.site D.base D.base_mem Y Y')) = (Cv : Set _) := by
    intro Cv hmv
    have hCvcl : IsClosed (Cv : Set (subspacePointSet D.site D.base D.base_mem Y Y')) :=
      isClosed_of_mem_irreducibleComponents _ Cv.2
    have hle : (C : Set (subspacePointSet D.site D.base D.base_mem Y Y')) ⊆ (Cv : Set _) := by
      rw [← hC]
      exact hCvcl.closure_subset_iff.2 (Set.singleton_subset_iff.2 hmv)
    exact le_antisymm hle (C.2.2 Cv.2.1 hle)
  have hmv : ∀ C : irreducibleComponents (subspacePointSet D.site D.base D.base_mem Y Y'),
      pointsMap D.site D.base D.base_mem X f
        (T.ambientGenericPoint D.site D.base D.base_mem) ∈
        Subtype.val '' (C : Set (subspacePointSet D.site D.base D.base_mem Y Y')) →
      (⟨pointsMap D.site D.base D.base_mem X f
          (T.ambientGenericPoint D.site D.base D.base_mem), hmem⟩ :
        subspacePointSet D.site D.base D.base_mem Y Y') ∈ (C : Set _) := by
    rintro C ⟨p, hp, hpe⟩
    have hpeq : p = ⟨_, hmem⟩ := Subtype.ext hpe
    exact hpeq ▸ hp
  have himg : subspacePointSet D.site D.base D.base_mem Y
      (closedSubspaceComponentImage D sY hY Y' hY' V₁.1).subspace =
      subspacePointSet D.site D.base D.base_mem Y
        (closedSubspaceComponentImage D sY hY Y' hY' V₂.1).subspace := by
    rw [hC₁, hC₂, ← key C₁ (hmv C₁ (hC₁ ▸ hm₁)), ← key C₂ (hmv C₂ (hC₂ ▸ hm₂))]
  have himage : closedSubspaceComponentImage D sY hY Y' hY' V₁.1 =
      closedSubspaceComponentImage D sY hY Y' hY' V₂.1 :=
    injective_integralClosedSubspaceSupport D.site D.base D.base_mem hY.1
      (IrreducibleCloseds.ext himg)
  exact Subtype.ext (IntegralClosedSubspace.injective_pushforward D.site D.base D.base_mem
    hY.1 hY'.1 (D.isDecentSpace_of_isGood sY hY) hY'.2 himage)

/-! ### The identity -/

/-- **Off the top δ-dimension both sides vanish.** If the integral closed subspace `T ⊆ X` does not
have δ-dimension `m + r`, then its multiplicity in `f^{-1}(Y')` is zero, and so is every term of
the sum `∑_V m_{V, Y'} · m_{T, f^{-1}(V)}` over the top-dimensional components `V` of `Y'`; in
particular the two are equal. -/
theorem cycleCoeffOfClosedSubspace_preimage_eq_finsum_of_deltaDimension_ne
    (γpre : points D.site D.base D.base_mem (Y'.preimage f).toFunctor →
      GeometricPoint D.site D.base D.base_mem (Y'.preimage f).toFunctor)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hT : deltaDimension D sX T ≠ m + (r : ℤ)) :
    cycleCoeffOfClosedSubspace D sX hX (Y'.preimage f)
        (isClosedSubspace_preimage D.site D.base D.base_mem f Y' hY.1 hX.1 hY')
        (m + (r : ℤ)) γpre T =
      ∑ᶠ V : topComponentSubspaces D sY hY Y' hY' m,
        closedSubspaceMultiplicity D Y' hY' V.1 *
          flatPullbackMult D sX hX sY hY f hbase r hflat hr
            (closedSubspaceComponentImage D sY hY Y' hY' V.1) T := by
  rw [cycleCoeffOfClosedSubspace, ite_eq_right hT]
  refine (finsum_eq_zero_of_forall_eq_zero fun V => ?_).symm
  refine mul_eq_zero_of_right _ ?_
  by_contra hne
  refine hT ?_
  rw [deltaDimension_eq_of_flatPullbackMult_ne_zero D sX hX sY hY f hbase r hflat hr
    (closedSubspaceComponentImage D sY hY Y' hY' V.1) T hne, V.2]

/-- **Multiplicativity of the multiplicity of a closed subspace along a flat morphism.** In
Situation 0EDT let `X/B` and `Y/B` be good, let `f : X ⟶ Y` be flat of relative dimension `r` over
the base, let `Y' ⊆ Y` be a closed subspace with `dim_δ(Y') ≤ m`, and let `T ⊆ X` be an integral
closed subspace occurring in `f^*[V]` for a top-dimensional component `V` of `Y'`. Let `φ : A → B'`
be a flat local homomorphism of local rings and let `I ⊆ A` be an ideal with `length_{B'}(B'/IB')`
finite, such that `m_{V, Y'} = length_A(A/I)`, `m_{T, f^{-1}(V)} = length_{B'}(B'/𝔪_A B')` and
`m_{T, f^{-1}(Y')} = length_{B'}(B'/IB')`. Then

`m_{T, f^{-1}(Y')} = ∑_{V'} m_{V', Y'} · m_{T, f^{-1}(V')}`,

the sum over the integral closed subspaces `V'` of `Y'` whose image in `Y` has δ-dimension `m`. -/
theorem cycleCoeffOfClosedSubspace_preimage_eq_finsum_of_length
    (hdim : deltaDimensionSubspace D sY hY Y' hY' ≤ (m : EInt))
    (γpre : points D.site D.base D.base_mem (Y'.preimage f).toFunctor →
      GeometricPoint D.site D.base D.base_mem (Y'.preimage f).toFunctor)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X)
    (V : topComponentSubspaces D sY hY Y' hY' m)
    (hV : flatPullbackMult D sX hX sY hY f hbase r hflat hr
      (closedSubspaceComponentImage D sY hY Y' hY' V.1) T ≠ 0)
    {A Bl : Type*} [CommRing A] [CommRing Bl] [IsLocalRing A] [IsLocalRing Bl]
    {φ : A →+* Bl} (hloc : IsLocalHom φ) (hflatφ : φ.Flat) (I : Ideal A)
    (hfin : Module.length Bl (Bl ⧸ Ideal.map φ I) ≠ ⊤)
    (hmultV : closedSubspaceMultiplicity D Y' hY' V.1 =
      ((Module.length A (A ⧸ I)).toNat : ℤ))
    (hmultT : flatPullbackMult D sX hX sY hY f hbase r hflat hr
        (closedSubspaceComponentImage D sY hY Y' hY' V.1) T =
      ((Module.length Bl (Bl ⧸ Ideal.map φ (IsLocalRing.maximalIdeal A))).toNat : ℤ))
    (hcoeff : cycleCoeffOfClosedSubspace D sX hX (Y'.preimage f)
        (isClosedSubspace_preimage D.site D.base D.base_mem f Y' hY.1 hX.1 hY')
        (m + (r : ℤ)) γpre T =
      ((Module.length Bl (Bl ⧸ Ideal.map φ I)).toNat : ℤ)) :
    cycleCoeffOfClosedSubspace D sX hX (Y'.preimage f)
        (isClosedSubspace_preimage D.site D.base D.base_mem f Y' hY.1 hX.1 hY')
        (m + (r : ℤ)) γpre T =
      ∑ᶠ V' : topComponentSubspaces D sY hY Y' hY' m,
        closedSubspaceMultiplicity D Y' hY' V'.1 *
          flatPullbackMult D sX hX sY hY f hbase r hflat hr
            (closedSubspaceComponentImage D sY hY Y' hY' V'.1) T := by
  rw [finsum_eq_single _ V ?_]
  · rw [hcoeff, hmultV, hmultT,
      Ring.toNat_length_quotient_mul_toNat_length_quotient_maximalIdeal_map hloc hflatφ I hfin]
  · intro V' hV'
    refine mul_eq_zero_of_right _ ?_
    by_contra hne
    exact hV' (topComponentSubspaces_eq_of_flatPullbackMult_ne_zero D sX hX sY hY f hbase r
      hflat hr Y' hY' m hdim T V' V hne hV)

/-- **Multiplicativity of the multiplicity along a flat morphism, at étale local rings.** In the
setting of `AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace_preimage_eq_finsum_of_length`, let
`x̄` be a geometric point of `X`, let `φ : 𝒪_{Y, f ∘ x̄} → 𝒪_{X, x̄}` be the canonical homomorphism
of étale local rings of Stacks 04NG, and let `I ⊆ 𝒪_{Y, f ∘ x̄}` be an ideal with
`length(𝒪_{X, x̄}/I𝒪_{X, x̄})` finite, such that `m_{V, Y'} = length(𝒪_{Y, f ∘ x̄}/I)`,
`m_{T, f^{-1}(V)} = length(𝒪_{X, x̄}/𝔪𝒪_{X, x̄})` for `𝔪` the maximal ideal of `𝒪_{Y, f ∘ x̄}`, and
`m_{T, f^{-1}(Y')} = length(𝒪_{X, x̄}/I𝒪_{X, x̄})`. Then

`m_{T, f^{-1}(Y')} = ∑_{V'} m_{V', Y'} · m_{T, f^{-1}(V')}`. -/
theorem cycleCoeffOfClosedSubspace_preimage_eq_finsum_of_etaleLocalRingLength
    (hdim : deltaDimensionSubspace D sY hY Y' hY' ≤ (m : EInt))
    (γpre : points D.site D.base D.base_mem (Y'.preimage f).toFunctor →
      GeometricPoint D.site D.base D.base_mem (Y'.preimage f).toFunctor)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X)
    (V : topComponentSubspaces D sY hY Y' hY' m)
    (hV : flatPullbackMult D sX hX sY hY f hbase r hflat hr
      (closedSubspaceComponentImage D sY hY Y' hY' V.1) T ≠ 0)
    (xbar : GeometricPoint D.site D.base D.base_mem X)
    (I : Ideal ↥(etaleLocalRing D.site D.base D.base_mem Y (geometricPointMap f xbar)))
    (hfin : Module.length ↥(etaleLocalRing D.site D.base D.base_mem X xbar)
      (↥(etaleLocalRing D.site D.base D.base_mem X xbar) ⧸
        Ideal.map (etaleLocalRingMap hX.1 f xbar) I) ≠ ⊤)
    (hmultV : closedSubspaceMultiplicity D Y' hY' V.1 =
      ((Module.length ↥(etaleLocalRing D.site D.base D.base_mem Y
        (geometricPointMap f xbar))
        (↥(etaleLocalRing D.site D.base D.base_mem Y (geometricPointMap f xbar)) ⧸
          I)).toNat : ℤ))
    (hmultT :
      letI : IsLocalRing ↥(etaleLocalRing D.site D.base D.base_mem Y
          (geometricPointMap f xbar)) :=
        isLocalRing_etaleLocalRing D.site D.base D.base_mem Y hY.1 (geometricPointMap f xbar)
      flatPullbackMult D sX hX sY hY f hbase r hflat hr
          (closedSubspaceComponentImage D sY hY Y' hY' V.1) T =
        ((Module.length ↥(etaleLocalRing D.site D.base D.base_mem X xbar)
          (↥(etaleLocalRing D.site D.base D.base_mem X xbar) ⧸
            Ideal.map (etaleLocalRingMap hX.1 f xbar)
              (IsLocalRing.maximalIdeal
                ↥(etaleLocalRing D.site D.base D.base_mem Y
                  (geometricPointMap f xbar))))).toNat : ℤ))
    (hcoeff : cycleCoeffOfClosedSubspace D sX hX (Y'.preimage f)
        (isClosedSubspace_preimage D.site D.base D.base_mem f Y' hY.1 hX.1 hY')
        (m + (r : ℤ)) γpre T =
      ((Module.length ↥(etaleLocalRing D.site D.base D.base_mem X xbar)
        (↥(etaleLocalRing D.site D.base D.base_mem X xbar) ⧸
          Ideal.map (etaleLocalRingMap hX.1 f xbar) I)).toNat : ℤ)) :
    cycleCoeffOfClosedSubspace D sX hX (Y'.preimage f)
        (isClosedSubspace_preimage D.site D.base D.base_mem f Y' hY.1 hX.1 hY')
        (m + (r : ℤ)) γpre T =
      ∑ᶠ V' : topComponentSubspaces D sY hY Y' hY' m,
        closedSubspaceMultiplicity D Y' hY' V'.1 *
          flatPullbackMult D sX hX sY hY f hbase r hflat hr
            (closedSubspaceComponentImage D sY hY Y' hY' V'.1) T := by
  have : IsLocalRing ↥(etaleLocalRing D.site D.base D.base_mem Y (geometricPointMap f xbar)) :=
    isLocalRing_etaleLocalRing D.site D.base D.base_mem Y hY.1 (geometricPointMap f xbar)
  have : IsLocalRing ↥(etaleLocalRing D.site D.base D.base_mem X xbar) :=
    isLocalRing_etaleLocalRing D.site D.base D.base_mem X hX.1 xbar
  exact cycleCoeffOfClosedSubspace_preimage_eq_finsum_of_length D sX hX sY hY f hbase r hflat hr
    Y' hY' m hdim γpre T V hV
    (isLocalHom_etaleLocalRingMap D.site D.base D.base_mem hX.1 hY.1 f xbar)
    (flat_etaleLocalRingMap D.site D.base D.base_mem hX.1 hY.1 f hflat xbar) I hfin hmultV
    hmultT hcoeff

end AlgebraicGeometry.Space

end
