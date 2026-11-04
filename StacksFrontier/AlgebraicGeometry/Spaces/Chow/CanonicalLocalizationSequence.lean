module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GenericFractionEmbeddingOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.LocalizationSequenceRationalEquivalence

/-!
# The localization sequence for canonical rational equivalence

In Situation 0EDT let `X/B` be good, let `j : U ⟶ X` be an open immersion and `i : Y ⟶ X` a
closed immersion over the base with complementary images. The first assertion of Stacks 0EQ7 says
that if `α, β ∈ Z_k(X)` have `α|_U ∼_rat β|_U`, then `α ∼_rat β + i_*γ` for some `γ ∈ Z_k(Y)`.
This file proves it for the rational equivalence of Stacks 0EQ6, defined through the principal
divisors at the canonical embeddings of Stacks 0ENK
(`AlgebraicGeometry.Space.IsCanonicallyRationallyEquivalentToZeroWithin`).

## Main results

* `AlgebraicGeometry.Space.canonicalPrincipalDivisorCycleAt_apply_closureImage`: the canonical
  principal divisor of `f ∈ R(X)^*` along an open immersion `j : U ⟶ X`, at the closure of the
  image, is the canonical principal divisor of its restriction.
* `AlgebraicGeometry.Space.exists_mem_canonicalPrincipalDivisors_closureImage`: the lifting step
  of Stacks 0EQ7 at the canonical embeddings.
* `exists_isCanonicallyRationallyEquivalentToZeroWithin_sub_add_cycleGroupClosedPushforward`:
  the first assertion of Stacks 0EQ7 at the canonical embeddings.

## References

* [Stacks Project, Tag 0EQ7](https://stacks.math.columbia.edu/tag/0EQ7)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EP9](https://stacks.math.columbia.edu/tag/0EP9)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Canonical

variable (D : BaseSpaceDimensionSituation.{u})
    {X U : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sU : U ⟶ D.space) (hU : D.IsGood sU)
    (hXint : IsIntegralSpace D.site D.base D.base_mem X)
    (hUint : IsIntegralSpace D.site D.base D.base_mem U)
    {j : U ⟶ X} (hj : IsOpenImmersion D.site D.base D.base_mem j)

include hj in
/-- Let `j : U ⟶ X` be an open immersion of good integral spaces and `f ∈ R(X)^*`, and write
`ρ f ∈ R(U)^*` for its restriction. The coefficient of the canonical principal divisor `div_X(f)`
at the closure of the image of an integral closed subspace `V ⊆ U` is the coefficient of
`div_U(ρ f)` at `V`. -/
theorem canonicalPrincipalDivisorCycleAt_apply_closureImage
    (f : (rationalFunctions D.site D.base D.base_mem hX.1)ˣ) {k : ℤ}
    (hk : deltaDimensionClosed D sX hX Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt))
    (hk' : deltaDimensionClosed D sU hU Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt))
    (V : IntegralClosedSubspace D.site D.base D.base_mem U) :
    (canonicalPrincipalDivisorCycleAt D sX hX hXint f hk).1
        (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX.1 hXint.2.1 j V) =
      (canonicalPrincipalDivisorCycleAt D sU hU hUint
        (Units.map (rationalFunctionMap D.site D.base D.base_mem hU.1 hX.1 hUint hXint j
          (pointsMap_genericPoint_of_isOpenImmersion D.site D.base D.base_mem hU.1 hX.1 hUint
            hXint hj)).toMonoidHom f) hk').1 V := by
  have hgen := pointsMap_genericPoint_of_isOpenImmersion D.site D.base D.base_mem hU.1 hX.1 hUint
    hXint hj
  let EX := genericFractionEmbedding D.site D.base D.base_mem hX.1 hXint.isDecentSpace hXint
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)
  let EU := genericFractionEmbedding D.site D.base D.base_mem hU.1 hUint.isDecentSpace hUint
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sU hU)
  let := EX.nontrivial
  let := EX.isNoetherianRing
  let := EX.krullDimLE
  let := EU.nontrivial
  let := EU.isNoetherianRing
  let := EU.krullDimLE
  set g := Units.map (rationalFunctionMap D.site D.base D.base_mem hU.1 hX.1 hUint hXint j
    hgen).toMonoidHom f
  refine principalDivisorCycleCoefficients_closureImage_of_ord_eq D sX hX sU hU
    hXint.isDecentSpace hUint.isDecentSpace hj EX.emb
    (f : rationalFunctions D.site D.base D.base_mem hX.1) (fun W => f.isUnit.map (EX.emb W))
    EU.emb (g : rationalFunctions D.site D.base D.base_mem hU.1)
    (fun W => g.isUnit.map (EU.emb W)) (fun Z => ?_) V
  exact (genericFractionEmbedding_ord_rationalFunctionMap_of_isOpenImmersion D.site D.base
    D.base_mem hU.1 hX.1 hUint hXint (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sU hU)
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) j hj hgen Z _
    (Z.pointsMap_genericPoint_closureImage D.site D.base D.base_mem hX.1 hU.1
      hXint.isDecentSpace hj) f).symm

end Canonical

/-! ### The lifting step -/

section Lift

variable (D : BaseSpaceDimensionSituation.{u})
    {X U : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sU : U ⟶ D.space) (hU : D.IsGood sU)
    {j : U ⟶ X} (himm : IsImmersion D.site D.base D.base_mem j) (hjc : j ≫ sX = sU)

include himm hjc in
/-- The lifting step of Stacks 0EQ7 at the canonical embeddings. Let `j : U ⟶ X` be an
immersion over the base, `W ⊆ U` an integral closed subspace, `W' ⊆ X` the integral closed
subspace on the closure of its image, and suppose the comparison morphism `m : W ⟶ W'` is an open
immersion. A canonical principal divisor `div_W(f)` on `W` is the coefficientwise restriction
along `m` of a canonical principal divisor on `W'`, namely `div_{W'}(f')` for the rational
function `f'` of `W'` which restricts to `f`. -/
theorem exists_mem_canonicalPrincipalDivisors_closureImage (k : ℤ)
    (W : IntegralClosedSubspace D.site D.base D.base_mem U)
    {c : CycleGroup D (W.subspace.ι ≫ sU) k} (hc : c ∈ canonicalPrincipalDivisors D sU hU k W)
    (m : W.subspace.toFunctor ⟶ (closureSubspace D sX hX j W).subspace.toFunctor)
    (hmopen : IsOpenImmersion D.site D.base D.base_mem m) :
    ∃ c' ∈ canonicalPrincipalDivisors D sX hX k (closureSubspace D sX hX j W),
      ∀ V : IntegralClosedSubspace D.site D.base D.base_mem W.subspace.toFunctor,
        c'.1 (IntegralClosedSubspace.closureImage D.site D.base D.base_mem
          (closureSubspace D sX hX j W).isClosedSubspace.1
          (closureSubspace D sX hX j W).isIntegralSpace.2.1 m V) = c.1 V := by
  obtain ⟨hk, f, rfl⟩ := hc
  have hWg := isGood_integralClosedSubspace D sU hU W
  have hW'g := isGood_integralClosedSubspace D sX hX (closureSubspace D sX hX j W)
  have hW'int := (closureSubspace D sX hX j W).isIntegralSpace
  have hgen := pointsMap_genericPoint_of_isOpenImmersion D.site D.base D.base_mem hWg.1 hW'g.1
    W.isIntegralSpace hW'int hmopen
  have : Mono m := mono_of_isOpenImmersion D.site D.base D.base_mem m hmopen
  let e := RingEquiv.ofBijective _ (rationalFunctionMap_bijective_of_mono D.site D.base
    D.base_mem hWg.1 hW'g.1 W.isIntegralSpace hW'int m hgen)
  have hk' : deltaDimensionClosed D ((closureSubspace D sX hX j W).subspace.ι ≫ sX) hW'g
      Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt) := by
    rwa [deltaDimensionClosed_univ_integralClosedSubspace D sX hX (closureSubspace D sX hX j W),
      show closureSubspace D sX hX j W = IntegralClosedSubspace.closureImage D.site D.base
          D.base_mem hX.1 (D.isDecentSpace_of_isGood sX hX) j W from rfl,
      IntegralClosedSubspace.deltaDimension_closureImage D sX hX.2.2 hX.1 hU.1
        (D.isDecentSpace_of_isGood sX hX) himm W, hjc,
      ← deltaDimensionClosed_univ_integralClosedSubspace D sU hU W]
  let f' : (rationalFunctions D.site D.base D.base_mem hW'g.1)ˣ :=
    Units.map e.symm.toRingHom.toMonoidHom f
  have hf' : Units.map (rationalFunctionMap D.site D.base D.base_mem hWg.1 hW'g.1
      W.isIntegralSpace hW'int m hgen).toMonoidHom f' = f :=
    Units.ext (e.apply_symm_apply (f : rationalFunctions D.site D.base D.base_mem hWg.1))
  refine ⟨canonicalPrincipalDivisorCycleAt D ((closureSubspace D sX hX j W).subspace.ι ≫ sX)
    hW'g hW'int f' hk', ⟨hk', f', rfl⟩, fun V => ?_⟩
  rw [canonicalPrincipalDivisorCycleAt_apply_closureImage D
    ((closureSubspace D sX hX j W).subspace.ι ≫ sX) hW'g (W.subspace.ι ≫ sU) hWg hW'int
    W.isIntegralSpace hmopen f' hk' hk V, hf']

end Lift

/-! ### The localization sequence -/

section Localization

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y U : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX)

/-- Stacks 0EQ7, the first assertion, at the canonical embeddings. In Situation 0EDT let
`X/B` be good, let `j : U ⟶ X` be an open immersion and `i : Y ⟶ X` a closed immersion over the
base whose images in `|X|` are complementary. If `α, β ∈ Z_k(X)` have `α|_U - β|_U` canonically
rationally equivalent to zero, then there is `γ ∈ Z_k(Y)` with `α - (β + i_*γ)` canonically
rationally equivalent to zero. -/
theorem exists_isCanonicallyRationallyEquivalentToZeroWithin_sub_add_cycleGroupClosedPushforward
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) (sU : U ⟶ D.space) (hU : D.IsGood sU)
    {i : Y ⟶ X} (hi : IsClosedImmersion D.site D.base D.base_mem i) (hic : i ≫ sX = sY)
    {j : U ⟶ X} (hj : IsOpenImmersion D.site D.base D.base_mem j) (hjc : j ≫ sX = sU)
    (hcomplement : Set.range (pointsMap D.site D.base D.base_mem Y i) =
      (Set.range (pointsMap D.site D.base D.base_mem U j))ᶜ) (k : ℤ)
    (α β : CycleGroup D sX k)
    (h : IsCanonicallyRationallyEquivalentToZeroWithin.{u, v} D sU hU k
      (cycleGroupRestrict D sX hX sU hU hj hjc k α - cycleGroupRestrict D sX hX sU hU hj hjc k β)
      Set.univ) :
    ∃ γ : CycleGroup D sY k,
      IsCanonicallyRationallyEquivalentToZeroWithin.{u, v} D sX hX k
        (α - (β + cycleGroupClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hi
          sX hX.2.2 sY hic k γ)) Set.univ := by
  have himm : IsImmersion D.site D.base D.base_mem j :=
    isImmersion_of_isOpenImmersion D.site D.base D.base_mem hj
  have hdec := D.isDecentSpace_of_isGood sX hX
  obtain ⟨J, W, hWfin, c, -, hcan, heq⟩ := h
  choose m hm using fun n => IntegralClosedSubspace.exists_hom_closureImage D.site D.base
    D.base_mem hX.1 hdec j (W n)
  choose c' hc' hcc using fun n => exists_mem_canonicalPrincipalDivisors_closureImage D sX hX sU
    hU himm hjc k (W n) (hcan n) (m n)
    (IntegralClosedSubspace.isOpenImmersion_of_comp_ι_eq_closureImage D.site D.base D.base_mem
      hX.1 hU.1 hdec hj (W n) (hm n))
  have hW'fin := locallyFinite_subspacePointSet_closureImage D sX hX hj W hWfin
  set δ := cycleFamilySum D sX hX _ hW'fin k c' with hδ
  have hres : cycleGroupRestrict D sX hX sU hU hj hjc k (α - β - δ) = 0 := by
    rw [map_sub, map_sub, hδ,
      cycleGroupRestrict_cycleFamilySum_closureImage D sX hX sU hU hj hjc W hWfin _
        (fun n => rfl) hW'fin hm k c c' hcc, ← heq, sub_self]
  obtain ⟨γ, hγ⟩ := (cycleGroupRestrict_eq_zero_iff D sX hX sY hY sU hU hi hic hj hjc
    hcomplement k (α - β - δ)).1 hres
  refine ⟨γ, ?_⟩
  rw [hγ, show α - (β + (α - β - δ)) = δ by abel]
  exact ⟨J, _, hW'fin, c', fun _ => Set.subset_univ _, hc', rfl⟩

end Localization

end AlgebraicGeometry.Space

end
