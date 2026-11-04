module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernRuleSubspaceImagePrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackRationalEquivalenceSummand

/-!
# Two cap-product cycles on isomorphic integral spaces differ by a principal divisor

In Situation 0EDT let `X/B` be good, let `𝒩` be an invertible `𝒪_X`-module and let `T ⊆ X` be
an integral closed subspace of δ-dimension `k + 1`.  Suppose `T₀` is a good integral algebraic
space identified with `T` by an isomorphism `e : T₀ ≅ T` over the base, and `ℳ` is an invertible
`𝒪_{T₀}`-module identified with `e^*(𝒩|_T)`.  For any regular meromorphic section `σ` of `ℳ` the
cycle

`a · (c₁(𝒩|_T) ∩ [T] - e_* div_ℳ(σ))`

is a principal divisor on `T` at the canonical embeddings of Stacks 0ENK, for every `a : ℤ`.  Here
`c₁(𝒩|_T) ∩ [T]` is the component cycle `AlgebraicGeometry.Space.canonicalFirstChernRule` of
Stacks 0EQJ.

For a morphism `f : X ⟶ Y`, an invertible `𝒪_Y`-module `ℒ`, an integral closed subspace `W ⊆ Y`
and an integral closed subspace `V` of `f^{-1}(W)` with image `V' ⊆ X`, this applies to the
identification `e : V ≅ V'`: for `g : V ⟶ W` lifting `V → X → Y` and a regular meromorphic section
`σ` of `g^*(ℒ|_W)`, the cycle `a · (c₁((f^*ℒ)|_{V'}) ∩ [V'] - e_* div(σ))` is a principal divisor
on `V'`.

## Main definitions

* `Space.preimageComponentImage`: the image in `X` of an integral closed subspace of `f^{-1}(W)`.
* `Space.preimageComponentModuleIso`: the isomorphism `g^*(ℒ|_W) ≅ e^*((f^*ℒ)|_{V'})`.

## Main results

* `Space.isPrincipalDivisorCycleOfGood_zsmul_canonicalFirstChernRule_sub_isoTransport`:
  the statement above.
* `Space.isPrincipalDivisorCycleOfGood_zsmul_canonicalFirstChernRule_sub_preimageComponent`:
  its form on an integral closed subspace of `f^{-1}(W)`.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EQR](https://stacks.math.columbia.edu/tag/0EQR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X T₀ : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)
    (k : ℤ) (T : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hT : deltaDimension D sX T = k + 1)
    (sT₀ : T₀ ⟶ D.space) (hT₀ : D.IsGood sT₀) (hint₀ : IsIntegralSpace D.site D.base D.base_mem T₀)
    (e : T₀ ≅ T.subspace.toFunctor) (hcomp : e.hom ≫ T.subspace.ι ≫ sX = sT₀)
    (M : Modules.{u, u} D.site D.base D.base_mem T₀ hT₀.1)
    (hM : IsInvertibleModule (⟨T₀, hT₀.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) M)

/-- **A cap-product cycle transported along an isomorphism differs from the chosen one by a
principal divisor.**  For `e : T₀ ≅ T` an isomorphism over the base from a good integral space
onto an integral closed subspace `T ⊆ X` of δ-dimension `k + 1`, an invertible module `ℳ` on `T₀`
with `φ : ℳ ≅ e^*(𝒩|_T)`, a regular meromorphic section `σ` of `ℳ` and `a : ℤ`, the cycle
`a · (c₁(𝒩|_T) ∩ [T] - e_* div_ℳ(σ))` is a principal divisor on `T` at the canonical embeddings
of Stacks 0ENK. -/
theorem isPrincipalDivisorCycleOfGood_zsmul_canonicalFirstChernRule_sub_isoTransport
    (φ : M ≅ (modulePullback D.site D.base D.base_mem
      (algebraicSpacesIsoOfIso D.site D.base D.base_mem hT₀.1 T.isClosedSubspace.1 e).hom).obj
        (integralClosedSubspaceRestrict D sX hX N T))
    (σ : MeromorphicSection.{u, u} D.site D.base D.base_mem T₀ hT₀.1 M)
    (hσ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem T₀ hT₀.1 M σ)
    (hk : deltaDimensionClosed D sT₀ hT₀ Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt))
    (a : ℤ) :
    IsPrincipalDivisorCycleOfGood D (T.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX T)
        T.isIntegralSpace k
      (a • (canonicalFirstChernRule D sX hX N hN k T hT -
        cycleGroupClosedPushforward D (isGood_integralClosedSubspace D sX hX T).1 hT₀.1
          (isDecentSpace_of_isGood D _ (isGood_integralClosedSubspace D sX hX T))
          (isClosedImmersion_of_isIso D.site D.base D.base_mem e.hom) (T.subspace.ι ≫ sX)
          (isGood_integralClosedSubspace D sX hX T).2.2 sT₀ hcomp k
          (canonicalDivisorCycleAt D sT₀ hT₀ hint₀ M hM σ hσ hk))) := by
  have hNT := isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN T
  have hτreg := isRegularMeromorphicSection_componentMeromorphicSection sX hX
    (subspaceDivisorSetupOfIsGood D sX hX) N hN T
  have hτ'reg := isRegularMeromorphicSection_pullbackMeromorphicSection_algebraicSpacesIsoOfIso
    D.site D.base D.base_mem hT₀.1 T.isClosedSubspace.1 e
    (integralClosedSubspaceRestrict D sX hX N T) hNT _ hτreg
  have hσ'reg := isRegularMeromorphicSection_sectionsMap_of_iso D.site D.base D.base_mem
    T₀ hT₀.1 φ _ hσ
  have hkT : deltaDimensionClosed D (T.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX T)
      Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt) := by
    rw [deltaDimensionClosed_univ_integralClosedSubspace D sX hX T, hT]
  have hM' := isInvertibleModule_modulePullback_algebraicSpacesIsoOfIso D.site D.base D.base_mem
    hT₀.1 T.isClosedSubspace.1 e (integralClosedSubspaceRestrict D sX hX N T) hNT
  have hpush := canonicalDivisorCycleAt_pushforwardOfIso D sT₀ hT₀ (T.subspace.ι ≫ sX)
    (isGood_integralClosedSubspace D sX hX T) hint₀ T.isIntegralSpace e
    (integralClosedSubspaceRestrict D sX hX N T) hNT
    (componentMeromorphicSection sX hX (subspaceDivisorSetupOfIsGood D sX hX) N hN T)
    hτreg hcomp hk hkT
  have hcarry := canonicalDivisorCycleAt_sectionsMap_iso D sT₀ hT₀ hint₀ M _ hM hM' φ σ hσ
    hσ'reg hk
  rw [show canonicalFirstChernRule D sX hX N hN k T hT =
      canonicalDivisorCycleAt D (T.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX T)
        T.isIntegralSpace (integralClosedSubspaceRestrict D sX hX N T) hNT
        (componentMeromorphicSection sX hX (subspaceDivisorSetupOfIsGood D sX hX) N hN T)
        hτreg hkT from rfl, ← hpush, ← hcarry, ← map_sub, ← map_zsmul]
  exact isPrincipalDivisorCycleOfGood_cycleGroupClosedPushforward_of_iso D sT₀ hT₀
    (T.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX T) hint₀ T.isIntegralSpace e
    hcomp k
    (isPrincipalDivisorCycleOfGood_zsmul_canonicalDivisorCycleAt_sub D sT₀ hT₀ hint₀ _ hM' _ _
      hτ'reg hσ'reg hk a)

/-! ### Components of the inverse image of an integral closed subspace -/

section Preimage

variable {D : BaseSpaceDimensionSituation.{u}}
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **Two inverse images of one module along equal composites.**  For `g ≫ p = g' ≫ p'` the
modules `g^* p^* ℒ` and `g'^* p'^* ℒ` are isomorphic, through `(g ≫ p)^* ℒ = (g' ≫ p')^* ℒ` and
the composition isomorphisms `AlgebraicGeometry.Space.modulePullbackCompIso` of Stacks 03LU. -/
def modulePullbackCompCongrIso {A B B' C : AlgebraicSpaces D.site D.base D.base_mem}
    (g : A ⟶ B) (p : B ⟶ C) (g' : A ⟶ B') (p' : B' ⟶ C) (h : g ≫ p = g' ≫ p')
    (L : Modules.{u, u} D.site D.base D.base_mem C.1 C.2) :
    (modulePullback D.site D.base D.base_mem g).obj
        ((modulePullback D.site D.base D.base_mem p).obj L) ≅
      (modulePullback D.site D.base D.base_mem g').obj
        ((modulePullback D.site D.base D.base_mem p').obj L) :=
  (modulePullbackCompIso D.site D.base D.base_mem g p).app L ≪≫
    eqToIso (by rw [h]) ≪≫ ((modulePullbackCompIso D.site D.base D.base_mem g' p').app L).symm

variable (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (L : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (V : IntegralClosedSubspace D.site D.base D.base_mem (W.subspace.preimage f).toFunctor)

/-- The image in `X` of an integral closed subspace `V` of the inverse image `f^{-1}(W)`. -/
abbrev preimageComponentImage : IntegralClosedSubspace D.site D.base D.base_mem X :=
  IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1
    (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W).1
    (D.isDecentSpace_of_isGood sX hX)
    (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W).2 V

/-- The identification of `V ⊆ f^{-1}(W)` with its image in `X`. -/
abbrev preimageComponentIso :
    V.subspace.toFunctor ≅ (preimageComponentImage sX hX sY hY f W V).subspace.toFunctor :=
  IntegralClosedSubspace.pushforwardIso D.site D.base D.base_mem hX.1
    (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W).1
    (D.isDecentSpace_of_isGood sX hX)
    (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W).2 V

/-- **`g^*(ℒ|_W) ≅ e^*((f^*ℒ)|_{V'})`.**  For an integral closed subspace `V` of `f^{-1}(W)`, with
image `V' ⊆ X` and identification `e : V ≅ V'`, and for any morphism `g : V ⟶ W` lifting
`V → f^{-1}(W) → X → Y`, the inverse image along `g` of the restriction `ℒ|_W` is the inverse
image along `e` of the restriction of `f^*ℒ` to `V'`.  Both are inverse images of `ℒ` along one
morphism `V ⟶ Y`. -/
def preimageComponentModuleIso
    (g : (⟨V.subspace.toFunctor, V.isClosedSubspace.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
      ⟨W.subspace.toFunctor, W.isClosedSubspace.1⟩)
    (hg : g.hom ≫ W.subspace.ι = V.subspace.ι ≫ (W.subspace.preimage f).ι ≫ f) :
    (modulePullback D.site D.base D.base_mem g).obj (integralClosedSubspaceRestrict D sY hY L W) ≅
      (modulePullback D.site D.base D.base_mem
          (algebraicSpacesIsoOfIso D.site D.base D.base_mem V.isClosedSubspace.1
            (preimageComponentImage sX hX sY hY f W V).isClosedSubspace.1
            (preimageComponentIso sX hX sY hY f W V)).hom).obj
        (integralClosedSubspaceRestrict D sX hX
          ((modulePullback D.site D.base D.base_mem
            (ObjectProperty.homMk f : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
              ⟨Y, hY.1⟩)).obj L)
          (preimageComponentImage sX hX sY hY f W V)) :=
  modulePullbackCompCongrIso g
      (closedSubspaceHom D.site D.base D.base_mem hY.1 W.subspace W.isClosedSubspace)
      ((algebraicSpacesIsoOfIso D.site D.base D.base_mem V.isClosedSubspace.1
            (preimageComponentImage sX hX sY hY f W V).isClosedSubspace.1
            (preimageComponentIso sX hX sY hY f W V)).hom ≫
        closedSubspaceHom D.site D.base D.base_mem hX.1
          (preimageComponentImage sX hX sY hY f W V).subspace
          (preimageComponentImage sX hX sY hY f W V).isClosedSubspace)
      (ObjectProperty.homMk f) (ObjectProperty.hom_ext _ (by
        change g.hom ≫ W.subspace.ι = ((preimageComponentIso sX hX sY hY f W V).hom ≫
          (preimageComponentImage sX hX sY hY f W V).subspace.ι) ≫ f
        rw [IntegralClosedSubspace.pushforwardIso_hom_comp_ι, hg, Category.assoc])) L ≪≫
    ((modulePullbackCompIso D.site D.base D.base_mem
      (algebraicSpacesIsoOfIso D.site D.base D.base_mem V.isClosedSubspace.1
        (preimageComponentImage sX hX sY hY f W V).isClosedSubspace.1
        (preimageComponentIso sX hX sY hY f W V)).hom
      (closedSubspaceHom D.site D.base D.base_mem hX.1
        (preimageComponentImage sX hX sY hY f W V).subspace
        (preimageComponentImage sX hX sY hY f W V).isClosedSubspace)).app
      ((modulePullback D.site D.base D.base_mem
        (ObjectProperty.homMk f : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
          ⟨Y, hY.1⟩)).obj L)).symm

variable (hL : IsInvertibleModule (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (k : ℤ)

/-- **The pulled-back section and the chosen section on a component of `f^{-1}(W)` differ by a
principal divisor.**  Let `V` be an integral closed subspace of `f^{-1}(W)` whose image `V' ⊆ X`
has δ-dimension `k + 1`, let `g : V ⟶ W` lift `V → X → Y` and let `σ` be a regular meromorphic
section of `g^*(ℒ|_W)`.  Then for every `a : ℤ` the cycle

`a · (c₁((f^*ℒ)|_{V'}) ∩ [V'] - e_* div_{g^*(ℒ|_W)}(σ))`

is a principal divisor on `V'` at the canonical embeddings of Stacks 0ENK, where `e : V ≅ V'` is
the identification and `c₁((f^*ℒ)|_{V'}) ∩ [V']` is the component cycle of Stacks 0EQJ on `X` for
`f^*ℒ`. -/
theorem isPrincipalDivisorCycleOfGood_zsmul_canonicalFirstChernRule_sub_preimageComponent
    (g : (⟨V.subspace.toFunctor, V.isClosedSubspace.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
      ⟨W.subspace.toFunctor, W.isClosedSubspace.1⟩)
    (hg : g.hom ≫ W.subspace.ι = V.subspace.ι ≫ (W.subspace.preimage f).ι ≫ f)
    (hV : deltaDimension D sX (preimageComponentImage sX hX sY hY f W V) = k + 1)
    (σ : MeromorphicSection.{u, u} D.site D.base D.base_mem V.subspace.toFunctor
      V.isClosedSubspace.1
      ((modulePullback D.site D.base D.base_mem g).obj
        (integralClosedSubspaceRestrict D sY hY L W)))
    (hσ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem V.subspace.toFunctor
      V.isClosedSubspace.1 _ σ)
    (hk : deltaDimensionClosed D (V.subspace.ι ≫ (W.subspace.preimage f).ι ≫ sX)
      (isGood_integralClosedSubspace D ((W.subspace.preimage f).ι ≫ sX)
        (isGood_ι_preimage_integralClosedSubspace D sX hX sY hY f W) V)
      Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt))
    (a : ℤ) :
    IsPrincipalDivisorCycleOfGood D ((preimageComponentImage sX hX sY hY f W V).subspace.ι ≫ sX)
        (isGood_integralClosedSubspace D sX hX (preimageComponentImage sX hX sY hY f W V))
        (preimageComponentImage sX hX sY hY f W V).isIntegralSpace k
      (a • (canonicalFirstChernRule D sX hX
          ((modulePullback D.site D.base D.base_mem
            (ObjectProperty.homMk f : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
              ⟨Y, hY.1⟩)).obj L)
          (modulePullbackInvertible
            (ObjectProperty.homMk f : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
              ⟨Y, hY.1⟩) L hL) k (preimageComponentImage sX hX sY hY f W V) hV -
        IntegralClosedSubspace.pushforwardCycleTransport D sX hX
          (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W).1
          (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W).2 V k
          (canonicalDivisorCycleAt D (V.subspace.ι ≫ (W.subspace.preimage f).ι ≫ sX)
            (isGood_integralClosedSubspace D ((W.subspace.preimage f).ι ≫ sX)
              (isGood_ι_preimage_integralClosedSubspace D sX hX sY hY f W) V)
            V.isIntegralSpace _
            (modulePullbackInvertible g _
              (isInvertibleModule_integralClosedSubspaceRestrict D sY hY L hL W))
            σ hσ hk))) :=
  isPrincipalDivisorCycleOfGood_zsmul_canonicalFirstChernRule_sub_isoTransport D sX hX _
    (modulePullbackInvertible
            (ObjectProperty.homMk f : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
              ⟨Y, hY.1⟩) L hL) k (preimageComponentImage sX hX sY hY f W V) hV _
    (isGood_integralClosedSubspace D ((W.subspace.preimage f).ι ≫ sX)
      (isGood_ι_preimage_integralClosedSubspace D sX hX sY hY f W) V)
    V.isIntegralSpace (preimageComponentIso sX hX sY hY f W V)
    (by rw [← Category.assoc, IntegralClosedSubspace.pushforwardIso_hom_comp_ι, Category.assoc])
    _ (modulePullbackInvertible g _
      (isInvertibleModule_integralClosedSubspaceRestrict D sY hY L hL W))
    (preimageComponentModuleIso sX hX sY hY f L W V g hg) σ hσ hk a

end Preimage

end AlgebraicGeometry.Space

end
