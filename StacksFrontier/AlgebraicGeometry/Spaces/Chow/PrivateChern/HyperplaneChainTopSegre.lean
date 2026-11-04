module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.CapCartierStep
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.HyperplaneChainCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardClosedImmersionSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardOfDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FunctionFieldAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeConditions

/-!
# The top Segre identity on a represented projective bundle with a hyperplane chain

Let `q : T ⟶ W` be a morphism of schemes of the big fppf site such that `h_q : h_T ⟶ h_W` is
proper and flat of relative dimension `d` between good algebraic spaces, `𝒩` an invertible
`𝒪_{h_T}`-module and `τ₁, …, τ_d` global sections of `𝒩` whose vanishing loci, read as ideal
sheaves of `T`, form a hyperplane chain over `W` (`Stacks.Chow.IsHyperplaneChain`), as the
coordinate hyperplanes of `ℙ^d_W` do. Then for every integral closed subspace `Z' ⊆ h_W` of
δ-dimension `k`,

`q_*(c₁(𝒩)^d ∩ q^*[Z']) ∼_rat [Z']` on `|Z'|`.

The chain is base changed to the closed subscheme `A ⊆ W` representing `Z'`; its members are the
closed subspaces `C_d = q^{-1}(Z')`, `C_j = C_{j+1} ∩ Z(τ_{j+1})`, each cut is an effective Cartier
divisor, and `C_0` maps isomorphically onto `Z'`, so `q_*[C_0] = [Z']`. The identity is then the
chain computation of
`rationallyEquivalentOn_topSegreCycle_flatPullbackMap_integralCycle_of_regularChain`.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.isIntegralSpace_of_iso`: integrality is invariant under
  isomorphism.
* `AlgebraicGeometry.Space.PrivateChern.properCyclePushforward_integralCycle_of_isClosedImmersion`:
  the pushforward of `[V]` along a closed immersion is the cycle of the image.
* `AlgebraicGeometry.Space.PrivateChern.properCyclePushforward_closedSubspaceCycle_of_iso`: the
  pushforward of the cycle of a closed subspace mapping isomorphically onto an integral closed
  subspace `Z'` is `[Z']`.
* `AlgebraicGeometry.Space.PrivateChern.rationallyEquivalentOn_topSegreCycle_of_isHyperplaneChain`:
  **the top Segre identity from a hyperplane chain.**

## References

* [Stacks Project, Tag 0ERU](https://stacks.math.columbia.edu/tag/0ERU)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space.PrivateChern

attribute [local instance] pointTopology

section Integral

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Integrality of an algebraic space is invariant under isomorphism.** -/
theorem isIntegralSpace_of_iso {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G)
    (h : IsIntegralSpace B S hS F) : IsIntegralSpace B S hS G := by
  have hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).RespectsIso :=
    (MorphismProperty.relative_isStableUnderBaseChange _).respectsIso
  have hetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).RespectsIso :=
    (MorphismProperty.relative_isStableUnderBaseChange _).respectsIso
  obtain ⟨⟨U, a, ha₁, ha₂, hP⟩, hdec, hirr⟩ := h
  refine ⟨⟨U, a ≫ e.hom, MorphismProperty.RespectsIso.postcomp _ e.hom a ha₁,
    MorphismProperty.RespectsIso.postcomp _ e.hom a ha₂, hP⟩,
    isDecentSpace_of_iso B S hS e hdec, ?_⟩
  have hs := pointsMap_surjective_of_isIso B S hS e.hom
  refine (irreducibleSpace_def _).2 ?_
  show IsIrreducible Set.univ
  rw [← hs.range_eq, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ _).image _
    (continuous_pointsMap B S hS e.hom).continuousOn

end Integral

variable (D : BaseSpaceDimensionSituation.{u})

/-- An integral closed subspace is determined by its set of points. -/
alias IntegralClosedSubspace.eq_of_subspacePointSet_eq :=
  AlgebraicGeometry.Space.IntegralClosedSubspace.eq_of_subspacePointSet_eq

/-- **The pushforward of `[V]` along a closed immersion is the cycle of the image.** For a
closed immersion `f : Y ⟶ X` of good algebraic spaces over the base and an integral closed
subspace `V ⊆ Y` of δ-dimension `k`, `f_*[V] = [f(V)]`: the closure of the image is the image,
the δ-dimension is preserved and the degree of the extension of function fields is `1`. -/
theorem properCyclePushforward_integralCycle_of_isClosedImmersion
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) {f : Y ⟶ X}
    (hfB : f ≫ sX = sY) (hf : IsClosedImmersion D.site D.base D.base_mem f) (k : ℤ)
    (V : IntegralClosedSubspace D.site D.base D.base_mem Y) (hV : deltaDimension D sY V = k) :
    properCyclePushforward D sY hY sX hX hfB
        (isQuasiCompact_of_isClosedImmersion' D.site D.base D.base_mem hf) k
        (integralCycle D sY k V hV) =
      integralCycle D sX k
        (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
          (D.isDecentSpace_of_isGood sX hX) hf V)
        (by rw [IntegralClosedSubspace.deltaDimension_pushforward D sX hX.2.2 hX.1 hY.1
          (D.isDecentSpace_of_isGood sX hX) hf V, hfB]; exact hV) := by
  classical
  have hcl := IntegralClosedSubspace.closureImage_eq_pushforward D.site D.base D.base_mem hX.1
    hY.1 (D.isDecentSpace_of_isGood sX hX) hf V
  have hdim : deltaDimension D sX (IntegralClosedSubspace.closureImage D.site D.base D.base_mem
      hX.1 (D.isDecentSpace_of_isGood sX hX) f V) = deltaDimension D sY V := by
    rw [hcl, IntegralClosedSubspace.deltaDimension_pushforward D sX hX.2.2 hX.1 hY.1
      (D.isDecentSpace_of_isGood sX hX) hf V, hfB]
  have hone : functionFieldDegree D sY hY sX hX f V = 1 :=
    IntegralClosedSubspace.degreeOverClosureImage_eq_one_of_isClosedImmersion D.site D.base
      D.base_mem hX.1 (D.isDecentSpace_of_isGood sX hX) (D.isDecentSpace_of_isGood sY hY) hf V
  have hdeg : properCycleDegree D sY hY sX hX f V = 1 := by
    rw [properCycleDegree, if_pos hdim, hone, Nat.cast_one]
  refine Subtype.ext (funext fun W => ?_)
  rw [properPushforward_apply, integralCycle_coe,
    finsum_eq_single _ V fun V' hV' => by rw [integralCycleCoeff_eq_zero D _ hV', zero_mul],
    integralCycleCoeff_self, one_mul, integralCycle_coe, properCycleMult, hdeg, hcl]
  by_cases hW : IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
      (D.isDecentSpace_of_isGood sX hX) hf V = W
  · rw [if_pos hW, ← hW, integralCycleCoeff_self]
  · rw [if_neg hW, integralCycleCoeff_eq_zero D _ (Ne.symm hW)]

/-- Cycles of equal integral closed subspaces are equal. -/
theorem integralCycle_congr {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (k : ℤ) {V W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (h : V = W) (hV : deltaDimension D sX V = k) (hW : deltaDimension D sX W = k) :
    integralCycle D sX k V hV = integralCycle D sX k W hW := by
  subst h
  rfl

/-- **The pushforward of the cycle of a closed subspace mapping isomorphically onto an integral
closed subspace.** Let `π : P ⟶ U` be proper between good algebraic spaces over the base, `C ⊆ P`
a closed subspace and `Z' ⊆ U` an integral closed subspace of δ-dimension `k`, and suppose `π`
restricts to an isomorphism `C ≅ Z'`. Then `π_*[C]_k = [Z']`: `C` is integral of δ-dimension `k`,
its cycle is the pushforward of its fundamental cycle along the inclusion, and the composite
`C ⟶ U` is a closed immersion with image `Z'`. -/
theorem properCyclePushforward_closedSubspaceCycle_of_iso
    {P U : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sP : P ⟶ D.space) (hP : D.IsGood sP) (sU : U ⟶ D.space) (hU : D.IsGood sU) {π : P ⟶ U}
    (hπ : π ≫ sU = sP) (hπp : IsProper D.site D.base D.base_mem π)
    (C : ClosedSubspaces D.site D.base D.base_mem P)
    (Z' : IntegralClosedSubspace D.site D.base D.base_mem U)
    (θ : C.1.toFunctor ≅ Z'.subspace.toFunctor) (hθ : θ.hom ≫ Z'.subspace.ι = C.1.ι ≫ π)
    (k : ℤ) (hZ' : deltaDimension D sU Z' = k)
    (hdim : deltaDimensionSubspace D sP hP C.1 C.2 ≤ (k : EInt)) :
    properCyclePushforward D sP hP sU hU hπ hπp.2.1.2 k
        (closedSubspaceCycle D sP hP C.1 C.2 k hdim) =
      integralCycle D sU k Z' hZ' := by
  classical
  have hInt : IsIntegralSpace D.site D.base D.base_mem C.1.toFunctor :=
    isIntegralSpace_of_iso D.site D.base D.base_mem θ.symm Z'.isIntegralSpace
  let C' : IntegralClosedSubspace D.site D.base D.base_mem P := ⟨C.1, C.2, hInt⟩
  have hgood : D.IsGood (C.1.ι ≫ sP) := isGood_integralClosedSubspace D sP hP C'
  let Ub := integralClosedSubspaceUniv D (C.1.ι ≫ sP) hgood hInt
  have hUb : subspacePointSet D.site D.base D.base_mem C.1.toFunctor Ub.subspace = Set.univ := by
    have : QuasiSober (points D.site D.base D.base_mem C.1.toFunctor) :=
      quasiSober_points_of_isDecentSpace D.site D.base D.base_mem C.2.1 hInt.2.1
    have : IrreducibleSpace (points D.site D.base D.base_mem C.1.toFunctor) := hInt.2.2
    rw [subspacePointSet_integralClosedSubspaceOfPoint]
    exact (genericPoint_spec (points D.site D.base D.base_mem C.1.toFunctor)).def
  have hfι : IsClosedImmersion D.site D.base D.base_mem C.1.ι := C.2.2
  have hf : IsClosedImmersion D.site D.base D.base_mem (C.1.ι ≫ π) := by
    rw [← hθ]
    exact isClosedImmersion_comp D.site D.base D.base_mem _ _
      (isClosedImmersion_of_isIso D.site D.base D.base_mem θ.hom) Z'.isClosedSubspace.2
  have hpC : IntegralClosedSubspace.pushforward D.site D.base D.base_mem hP.1 C.2.1
      (D.isDecentSpace_of_isGood sP hP) hfι Ub = C' := by
    refine IntegralClosedSubspace.eq_of_subspacePointSet_eq D hP.1 ?_
    rw [IntegralClosedSubspace.subspacePointSet_pushforward, hUb, Set.image_univ]
  have hpZ : IntegralClosedSubspace.pushforward D.site D.base D.base_mem hU.1 C.2.1
      (D.isDecentSpace_of_isGood sU hU) hf Ub = Z' := by
    refine IntegralClosedSubspace.eq_of_subspacePointSet_eq D hU.1 ?_
    rw [IntegralClosedSubspace.subspacePointSet_pushforward, hUb, Set.image_univ, ← hθ,
      pointsMap_comp]
    rw [Set.range_comp, (pointsMap_surjective_of_isIso D.site D.base D.base_mem θ.hom).range_eq,
      Set.image_univ]
  have hdimU : deltaDimension D (C.1.ι ≫ sP) Ub = k := by
    have := IntegralClosedSubspace.deltaDimension_pushforward D sU hU.2.2 hU.1 C.2.1
      (D.isDecentSpace_of_isGood sU hU) hf Ub
    rw [hpZ, hZ', Category.assoc, hπ] at this
    exact this.symm
  have hdimC : deltaDimension D sP C' = k := by
    rw [← hpC, IntegralClosedSubspace.deltaDimension_pushforward D sP hP.2.2 hP.1 C.2.1
      (D.isDecentSpace_of_isGood sP hP) hfι Ub]
    exact hdimU
  -- the cycle of `C` is the cycle of the integral closed subspace `C'`
  have hcyc : closedSubspaceCycle D sP hP C.1 C.2 k hdim = integralCycle D sP k C' hdimC := by
    subst hdimC
    refine Subtype.ext (funext fun W => ?_)
    rw [integralCycle_coe]
    by_cases hW : W = C'
    · subst hW
      rw [integralCycleCoeff_self]
      exact closedSubspaceCycle_integral_apply_self D sP hP C' hdim
    · rw [integralCycleCoeff_eq_zero D _ hW]
      exact closedSubspaceCycle_integral_apply_of_ne D sP hP C' W hdim hW
  have hιp : IsProper D.site D.base D.base_mem C.1.ι :=
    isProper_of_isClosedImmersion D.site D.base D.base_mem C.2.1 hP.1 _ hfι
  rw [hcyc, integralCycle_congr D sP k hpC.symm hdimC (hpC ▸ hdimC),
    ← properCyclePushforward_integralCycle_of_isClosedImmersion D sP hP (C.1.ι ≫ sP) hgood rfl hfι
      k Ub hdimU,
    properCyclePushforward_comp D (C.1.ι ≫ sP) sP sU hgood hP hU rfl hπ hιp hπp,
    properCyclePushforward_congr D (C.1.ι ≫ sP) hgood sU hU (rfl : C.1.ι ≫ π = C.1.ι ≫ π) _ _
      (by rw [Category.assoc, hπ])
      (isQuasiCompact_of_isClosedImmersion' D.site D.base D.base_mem hf),
    properCyclePushforward_integralCycle_of_isClosedImmersion D sU hU (C.1.ι ≫ sP) hgood
      (by rw [Category.assoc, hπ]) hf k Ub hdimU]
  exact integralCycle_congr D sU k hpZ _ hZ'

/-- **The top Segre identity on a represented projective bundle with a hyperplane chain.** Let
`q : T ⟶ W` be a morphism of the site with `h_q` proper and flat of relative dimension `d`
between good algebraic spaces, `𝒩` an invertible `𝒪_{h_T}`-module and `τ_j` global sections of
`𝒩` whose vanishing loci, read as ideal sheaves of `T`, form a hyperplane chain over `W`. Then
`q_*(c₁(𝒩)^d ∩ q^*[Z']) ∼_rat [Z']` on `|Z'|` for every integral closed subspace `Z' ⊆ h_W`. -/
theorem rationallyEquivalentOn_topSegreCycle_of_isHyperplaneChain
    {T Wb : BigFppfOver D.site D.base D.base_mem} (q : T ⟶ Wb)
    (sQ : yoneda.obj T ⟶ D.space) (hQ : D.IsGood sQ) (sW : yoneda.obj Wb ⟶ D.space)
    (hW : D.IsGood sW) (hq : yoneda.map q ≫ sW = sQ)
    (hqp : IsProper D.site D.base D.base_mem (yoneda.map q)) (d : ℕ)
    (hqf : IsFlat D.site D.base D.base_mem (yoneda.map q))
    (hqd : HasRelativeDimension d D.site D.base D.base_mem (yoneda.map q))
    (N : Modules.{u, u} D.site D.base D.base_mem (yoneda.obj T) hQ.1)
    (hN : IsInvertibleModule (⟨yoneda.obj T, hQ.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)
    (hNs : IsInvertibleSheaf D sQ hQ N) (τ : ℕ → N.sections)
    (hchain : Stacks.Chow.IsHyperplaneChain d
      ((BigFppfOver.toScheme D.site D.base D.base_mem).map q)
      (fun j => schemeSpaceIdeal D.site D.base D.base_mem T (vanishingLocus D sQ hQ N (τ j))))
    (k : ℤ) (Z' : IntegralClosedSubspace D.site D.base D.base_mem (yoneda.obj Wb))
    (hZ' : deltaDimension D sW Z' = k) :
    RationallyEquivalentOn.{u + 1} D sW hW k
      (subspacePointSet D.site D.base D.base_mem (yoneda.obj Wb) Z'.subspace)
      (topSegreCycle D sQ hQ sW hW hq hqp.2.1.2 N hN d k (k + d) rfl
        (flatPullbackMap D sQ hQ sW hW (yoneda.map q) hq d hqf hqd k (k + d) rfl
          (integralCycle D sW k Z' hZ')))
      (integralCycle D sW k Z' hZ') := by
  set 𝒯 := BigFppfOver.toScheme D.site D.base D.base_mem
  obtain ⟨A0, i, hi, hrange, hker⟩ := exists_closedImmersion_range_eq D.site D.base D.base_mem Wb
    ⟨Z'.subspace, Z'.isClosedSubspace⟩
  have := hi
  have hsq : IsPullback (pullback.fst (𝒯.map q) (𝒯.map i)) (pullback.snd (𝒯.map q) (𝒯.map i))
      (𝒯.map q) (𝒯.map i) := IsPullback.of_hasPullback _ _
  have hchR := hchain.of_isPullback hsq
  let Zs : ℕ → ClosedSubspaces D.site D.base D.base_mem (yoneda.obj T) :=
    fun j => vanishingLocus D sQ hQ N (τ j)
  let Ctop : ClosedSubspaces D.site D.base D.base_mem (yoneda.obj T) :=
    ⟨Z'.subspace.preimage (yoneda.map q), isClosedSubspace_preimage D.site D.base D.base_mem
      (yoneda.map q) Z'.subspace hW.1 hQ.1 Z'.isClosedSubspace⟩
  have hCtop : schemeSpaceIdeal D.site D.base D.base_mem T Ctop =
      (pullback.fst (𝒯.map q) (𝒯.map i)).ker := by
    rw [schemeSpaceIdeal_eq_comap_of_preimage_eq D.site D.base D.base_mem Wb q
      ⟨Z'.subspace, Z'.isClosedSubspace⟩ Ctop rfl, ← hker,
      Stacks.Divisors.ker_eq_comap_of_isPullback hsq]
  obtain ⟨hcart, s, hs, hsq', hs0⟩ := hyperplaneChainSubspaces_spec (Zs := Zs) (𝒯.map q) hchR
    (pullback.fst (𝒯.map q) (𝒯.map i)) inferInstance (𝒯.map i) hsq.w Ctop hCtop
    (fun j _ => rfl)
  have := hs
  refine rationallyEquivalentOn_topSegreCycle_flatPullbackMap_integralCycle_of_regularChain D sQ hQ
    sW hW hq hqp d hqf hqd N hN hNs τ k Z' hZ'
    (hyperplaneChainSubspaces D.site D.base D.base_mem T Zs d Ctop)
    (by rw [hyperplaneChainSubspaces_self])
    (fun j hj => hyperplaneChainSubspaces_eq_inf Zs d Ctop j hj)
    hcart (fun h0dim => ?_)
  -- the bottom of the chain maps isomorphically onto `Z'`
  set C0 := hyperplaneChainSubspaces D.site D.base D.base_mem T Zs d Ctop 0
  obtain ⟨R0, j0, hj0, hr0, hk0⟩ := exists_closedImmersion_range_eq D.site D.base D.base_mem T C0
  have := hj0
  have hkk : (𝒯.map j0).ker = s.ker := hk0.trans hs0
  let e : 𝒯.obj R0 ⟶ 𝒯.obj A0 := _root_.AlgebraicGeometry.IsClosedImmersion.lift s (𝒯.map j0) hkk.ge
  have he : e ≫ s = 𝒯.map j0 := _root_.AlgebraicGeometry.IsClosedImmersion.lift_fac _ _ _
  have : IsIso e := _root_.AlgebraicGeometry.IsClosedImmersion.isIso_lift s _ hkk.symm
  have he' : e ≫ 𝒯.map i = 𝒯.map (j0 ≫ q) := by
    rw [← hsq', ← Category.assoc, he, Functor.map_comp]
  let e' : R0 ⟶ A0 := Over.homMk (ObjectProperty.homMk e) (by
    rw [← Over.w i, ← Over.w (j0 ≫ q), ← Category.assoc]
    congr 1
    exact D.site.inclusion.map_injective (by rw [Functor.map_comp]; exact he'))
  have : IsIso (𝒯.map e') := inferInstanceAs (IsIso e)
  have : IsIso e' := isIso_of_reflects_iso e' 𝒯
  have he'' : e' ≫ i = j0 ≫ q := 𝒯.map_injective (by rw [Functor.map_comp]; exact he')
  have hιeq : ∀ {X : BigFppfOver D.site D.base D.base_mem} {F₁ F₂ : Subfunctor (yoneda.obj X)}
      (h : F₁ = F₂), eqToHom (congrArg Subfunctor.toFunctor h) ≫ F₂.ι = F₁.ι := by
    intro X F₁ F₂ h
    subst h
    simp
  have := isIso_toRange_yoneda_map D.site D.base D.base_mem j0 hj0
  have := isIso_toRange_yoneda_map D.site D.base D.base_mem i hi
  let θ : C0.1.toFunctor ≅ Z'.subspace.toFunctor :=
    eqToIso (congrArg Subfunctor.toFunctor hr0.symm) ≪≫
      (asIso (Subfunctor.toRange (yoneda.map j0))).symm ≪≫ yoneda.mapIso (asIso e') ≪≫
      asIso (Subfunctor.toRange (yoneda.map i)) ≪≫
      eqToIso (congrArg Subfunctor.toFunctor
        (hrange : Subfunctor.range (yoneda.map i) = Z'.subspace))
  have hθ : θ.hom ≫ Z'.subspace.ι = C0.1.ι ≫ yoneda.map q := by
    have hinv : inv (Subfunctor.toRange (yoneda.map j0)) ≫ yoneda.map j0 =
        (Subfunctor.range (yoneda.map j0)).ι := by
      rw [IsIso.inv_comp_eq, Subfunctor.toRange_ι]
    simp only [θ, Iso.trans_hom, Iso.symm_hom, eqToIso.hom, asIso_inv, asIso_hom,
      Functor.mapIso_hom, Category.assoc]
    rw [hιeq (hrange : Subfunctor.range (yoneda.map i) = Z'.subspace), Subfunctor.toRange_ι,
      ← Functor.map_comp, he'', Functor.map_comp, ← Category.assoc (inv _), hinv,
      ← Category.assoc, hιeq hr0.symm]
  exact properCyclePushforward_closedSubspaceCycle_of_iso D sQ hQ sW hW hq hqp C0 Z' θ hθ k hZ' _

end AlgebraicGeometry.Space.PrivateChern

end
