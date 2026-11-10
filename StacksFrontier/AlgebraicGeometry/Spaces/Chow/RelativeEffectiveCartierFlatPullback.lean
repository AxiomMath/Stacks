module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinFlatPullbackRelativeCartier
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IsomorphismRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RefinedGysinPushforwardCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RegularSectionFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalenceCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ZeroSchemeComponentCycles
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroSchemeEffectiveCartier

/-!
# Relative effective Cartier divisors and flat pullback

In Situation 0EDT let `X, Y/B` be good, let `p : X ⟶ Y` be flat of relative dimension `r` and let
`i : D → X` be a relative effective Cartier divisor on `X/Y` (Stacks 0EPP), with `ℒ = 𝒪_X(D)`.
**Stacks 0ERE** asserts that for every `α ∈ CH_{k+1}(Y)`

`i^* p^* α = (p|_D)^* α` in `CH_{k+r}(D)` and `c₁(ℒ) ∩ p^* α = i_*((p|_D)^* α)` in `CH_{k+r}(X)`.

The proof is the source's. For an integral closed subspace `W ⊆ Y` of δ-dimension `k + 1`, the
intersection `D ∩ p^{-1}(W)` is an effective Cartier divisor on `p^{-1}(W)` (Stacks 0EPN), so
Stacks 0ER7 gives `i^*[p^{-1}(W)]_{k+r+1} = [D ∩ p^{-1}(W)]_{k+r} = [(p|_D)^{-1}(W)]_{k+r}` as
cycles; that is `i^* p^*[W] = (p|_D)^*[W]`. Summing over the components of a general cycle gives
the first identity, and Stacks 0ER4 turns it into the second.

Stacks 0ER7 is used only for the closed subspaces `p^{-1}(W)`, and is proved here in that case,
`finsum_flatPullbackMult_mul_gysinComponentCycle_sectionGysinRule`: the section `s|_{p^{-1}(W)}`
is regular, and Stacks 0EQL on `p^{-1}(W)` is read in `X`
(`cycleClosedPushforward_vanishingLocus_eq_finsum_closedSubspaceCycle_mul`).

Declarations named here without a namespace are in `AlgebraicGeometry.Space`.

## Main results

* `cycleClosedPushforward_vanishingLocus_eq_finsum_closedSubspaceCycle_mul`: Stacks 0EQL on a
  closed subspace `Z ⊆ X`, pushed forward to `X`.
* `isEffectiveCartierDivisor_preimage_ι_preimage`: Stacks 0EPN for the inverse image of an
  integral closed subspace.
* `gysinCycleMap_sectionGysinRule_flatPullbackMap`: `i^* p^* α = (p|_E)^* α` as cycles, for the
  vanishing locus `E = Z(s)` of a section of an invertible sheaf which is a relative effective
  Cartier divisor.
* `chowClassCanonical_gysinCycleMap_canonicalSection_flatPullbackMap` and
  `chowClassCanonical_firstChernCapCycleMap_canonicalSection_flatPullbackMap`: **Stacks 0ERE**,
  the two identities, for `r ≥ 1`, in the Chow groups of Stacks 0EQ6 at the canonical embeddings
  of Stacks 0ENK.
* `chowClassCanonical_flatPullbackMap_canonicalSection_eq_zero_of_hasRelativeDimension_zero`:
  **Stacks 0ERE** for `r = 0`, where `D` is empty.
* `sectionRefinedGysin_canonicalSection_flatPullbackMap`,
  `canonicalFirstChernCap_canonicalSection_flatPullbackMap` and
  `flatPullbackMap_canonicalSection_eq_zero_of_hasRelativeDimension_zero`: the same statements in
  the coarser quotient `chowGroup`, through the operations on Chow groups.

## Implementation notes

The relative dimension of `p` is written `r + 1`, so that `p|_D` has relative dimension `r`
(`AlgebraicGeometry.Space.hasRelativeDimension_ι_comp`) and the degrees of the source become
`α ∈ Z_{k+1}(Y)`, `p^* α ∈ Z_{k+r+2}(X)` and `i^* p^* α ∈ CH_{k+r+1}(D)`. In relative dimension
`0` the divisor `D` has no points, so all of its cycles vanish and both identities say `0 = 0`.

The identities are stated for every cycle `α ∈ Z_{k+1}(Y)`, the outer operations taking values in
the Chow groups of Stacks 0EQ6: `i^*` is `AlgebraicGeometry.Space.sectionRefinedGysin`, with
values in `CH_{k+r+1}(D)`, `c₁(ℒ) ∩ -` is `AlgebraicGeometry.Space.canonicalFirstChernCap`, and
`(p|_D)^* α` is the class of the flat pullback of the cycle. This form does not use that flat
pullback descends to Chow groups (Stacks 0EQB); with that descent it is the source's statement on
classes. The first identity holds already on cycles.

The divisor `D` enters through the pair `(𝒪_X(D), 1_D)` of Stacks 0841, whose vanishing locus is
`D` by Stacks 0847; the Gysin map of Stacks 0ER1 lands in the cycles of that vanishing locus.

## References

* [Stacks Project, Tag 0ERE](https://stacks.math.columbia.edu/tag/0ERE)
* [Stacks Project, Tag 0ER7](https://stacks.math.columbia.edu/tag/0ER7)
* [Stacks Project, Tag 0ER4](https://stacks.math.columbia.edu/tag/0ER4)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0EQL](https://stacks.math.columbia.edu/tag/0EQL)
* [Stacks Project, Tag 0EPN](https://stacks.math.columbia.edu/tag/0EPN)
* [Stacks Project, Tag 0EPP](https://stacks.math.columbia.edu/tag/0EPP)
* [Stacks Project, Tag 0847](https://stacks.math.columbia.edu/tag/0847)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (p : X ⟶ Y) (hbase : p ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem p)
    (hr : HasRelativeDimension (r + 1) D.site D.base D.base_mem p)


/-! ### Stacks 0EQL on a closed subspace, read in the ambient space -/

section AmbientZeroCycle

variable (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (Z : ClosedSubspaces D.site D.base D.base_mem X)
    (s : (closedSubspaceModuleRestrict D sX hX L Z).sections)

include hL in
/-- **Stacks 0EQL on a closed subspace `Z ⊆ X`, read in `X`.** Let `Z ⊆ X` be a closed subspace
with `dim_δ(Z) ≤ k + 1` and `s ∈ Γ(Z, ℒ|_Z)` a regular section. Let `F` assign to every integral
closed subspace `W ⊆ X` a coefficient family on `X` which, at the image `W` of an integral closed
subspace `V ⊆ Z` occurring in `[Z]_{k+1}`, is the pushforward to `X` of the cycle `[Z(s|_V)]_k`.
Then the pushforward to `X` of `[Z(s)]_k` is `∑_W n_W F(W)`, the `n_W` being the coefficients of
`[Z]_{k+1}`.

This is Stacks 0EQL on `Z`
(`cycleCoeffOfClosedSubspace_vanishingLocus_eq_componentZeroCycleSumCoeff_of_isRegularSection`)
pushed forward to `X`, the sum over the irreducible components of `Z` of δ-dimension `k + 1`
being reindexed by their images in `X`. -/
theorem cycleClosedPushforward_vanishingLocus_eq_finsum_closedSubspaceCycle_mul
    (hs : AlgebraicGeometry.IsRegularSection
      (structureCommRings D.site D.base D.base_mem ⟨Z.1.toFunctor, Z.2.1⟩)
      (structureRingSheaf D.site D.base D.base_mem ⟨Z.1.toFunctor, Z.2.1⟩).property s) {k : ℤ}
    (hdim : deltaDimensionSubspace D sX hX Z.1 Z.2 ≤ ((k + 1 : ℤ) : EInt))
    (F : IntegralClosedSubspace D.site D.base D.base_mem X →
      IntegralClosedSubspace D.site D.base D.base_mem X → ℤ)
    (hF : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem Z.1.toFunctor,
      (closedSubspaceCycle D sX hX Z.1 Z.2 (k + 1) hdim).1
          (closedSubspaceComponentImage D sX hX Z.1 Z.2 V) ≠ 0 →
        F (closedSubspaceComponentImage D sX hX Z.1 Z.2 V) =
          cycleClosedPushforward D hX.1 Z.2.1 (D.isDecentSpace_of_isGood sX hX) Z.2.2
            (componentZeroCycleCoeff D (Z.1.ι ≫ sX) (isGood_closedSubspace D sX hX Z)
              (closedSubspaceModuleRestrict D sX hX L Z) s k V
              (canonicalGeometricPoint D.site D.base D.base_mem _)))
    (T : IntegralClosedSubspace D.site D.base D.base_mem X) :
    cycleClosedPushforward D hX.1 Z.2.1 (D.isDecentSpace_of_isGood sX hX) Z.2.2
        (cycleCoeffOfClosedSubspace D (Z.1.ι ≫ sX) (isGood_closedSubspace D sX hX Z)
          (vanishingLocus D (Z.1.ι ≫ sX) (isGood_closedSubspace D sX hX Z)
            (closedSubspaceModuleRestrict D sX hX L Z) s).1
          (vanishingLocus D (Z.1.ι ≫ sX) (isGood_closedSubspace D sX hX Z)
            (closedSubspaceModuleRestrict D sX hX L Z) s).2 k
          (canonicalGeometricPoint D.site D.base D.base_mem _)) T =
      ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem X,
        (closedSubspaceCycle D sX hX Z.1 Z.2 (k + 1) hdim).1 W * F W T := by
  classical
  have hXdec := D.isDecentSpace_of_isGood sX hX
  have hZg := isGood_closedSubspace D sX hX Z
  have hinvZ := isInvertible_modulePullback_obj D.site D.base D.base_mem
    (closedSubspaceHom D.site D.base D.base_mem hX.1 Z.1 Z.2) L
    (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL)
  have hdimZ := deltaDimensionClosed_univ_closedSubspace_le D sX hX Z _ hdim
  set α := closedSubspaceCycle D sX hX Z.1 Z.2 (k + 1) hdim with hα
  set g : ComponentsOfDeltaDimension D (Z.1.ι ≫ sX) hZg (k + 1) →
      IntegralClosedSubspace D.site D.base D.base_mem X :=
    fun V => closedSubspaceComponentImage D sX hX Z.1 Z.2 V.1 with hg
  have hginj : Function.Injective g := fun V V' h => Subtype.ext
    (IntegralClosedSubspace.injective_pushforward D.site D.base D.base_mem hX.1 Z.2.1 hXdec
      Z.2.2 h)
  -- the multiplicity of a component in `[Z]_{k+1}` read on `Z` and on `X`
  have hn : ∀ V : ComponentsOfDeltaDimension D (Z.1.ι ≫ sX) hZg (k + 1),
      fundamentalCycleCoeff D (Z.1.ι ≫ sX) hZg (k + 1)
          (canonicalGeometricPoint D.site D.base D.base_mem _) V.1 = α.1 (g V) := fun V => by
    rw [hα, hg, closedSubspaceCycle_apply_closedSubspaceComponentImage,
      deltaDimension_closedSubspaceComponentImage]
    rfl
  rw [cycleCoeffOfClosedSubspace_vanishingLocus_eq_componentZeroCycleSumCoeff_of_isRegularSection
    D (Z.1.ι ≫ sX) hZg _ s k hinvZ hs hdimZ]
  refine (cycleClosedPushforward_finsum_mul D hX.1 Z.2.1 hXdec Z.2.2
    (fun V : ComponentsOfDeltaDimension D (Z.1.ι ≫ sX) hZg (k + 1) =>
      fundamentalCycleCoeff D (Z.1.ι ≫ sX) hZg (k + 1)
        (canonicalGeometricPoint D.site D.base D.base_mem _) V.1)
    (fun V => componentZeroCycleCoeff D (Z.1.ι ≫ sX) hZg
      (closedSubspaceModuleRestrict D sX hX L Z) s k V.1
      (canonicalGeometricPoint D.site D.base D.base_mem _)) T).trans ?_
  -- reindex the sum over the components of `Z` by their images in `X`
  rw [← finsum_mem_univ (fun W => α.1 W * F W T),
    finsum_mem_inter_support_eq' (fun W => α.1 W * F W T) Set.univ (Set.range g) ?_,
    finsum_mem_range hginj]
  · refine finsum_congr fun V => ?_
    rw [hn V]
    by_cases h0 : α.1 (g V) = 0
    · rw [h0, zero_mul, zero_mul]
    · rw [hF V.1 h0]
  · intro W hW
    simp only [Set.mem_univ, true_iff]
    have hW0 : α.1 W ≠ 0 := left_ne_zero_of_mul hW
    obtain ⟨V, hV⟩ : ∃ V, closedSubspaceComponentImage D sX hX Z.1 Z.2 V = W := by
      by_contra h
      push Not at h
      exact hW0 (closedSubspaceCycle_apply_eq_zero_of_forall_ne D sX hX Z.1 Z.2 (k + 1) hdim W h)
    have hVk : deltaDimension D (Z.1.ι ≫ sX) V = k + 1 := by
      rw [← deltaDimension_closedSubspaceComponentImage D sX hX Z.1 Z.2 V, hV]
      exact α.2.2 W hW0
    exact ⟨⟨V, isIrreducibleComponent_of_deltaDimension_eq D sX hX Z hdim V hVk, hVk⟩, hV⟩

end AmbientZeroCycle


/-! ### A relative effective Cartier divisor meets the inverse image of a subspace in a divisor -/

/-- **Stacks 0EPN for the inverse image of an integral closed subspace.** If `E ⊆ X` is a
relative effective Cartier divisor on `X/Y` and `W ⊆ Y` is an integral closed subspace, then
`E ∩ p^{-1}(W)` is an effective Cartier divisor on `p^{-1}(W)`: the square
`p^{-1}(W) → W`, `p^{-1}(W) → X` is cartesian (Stacks 083Q), and the base change of a relative
effective Cartier divisor is an effective Cartier divisor
(`AlgebraicGeometry.Space.isPullbackDefined_of_isPullback_of_isFlat`). -/
theorem isEffectiveCartierDivisor_preimage_ι_preimage
    (E : ClosedSubspaces D.site D.base D.base_mem X)
    (hE : IsRelativeEffectiveCartierDivisor D.site D.base D.base_mem
      (ObjectProperty.homMk p : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨Y, hY.1⟩) E)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    IsEffectiveCartierDivisor D.site D.base D.base_mem
      ⟨(W.subspace.preimage p).toFunctor,
        (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY p W).1⟩
      ⟨E.1.preimage (W.subspace.preimage p).ι,
        isClosedSubspace_preimage D.site D.base D.base_mem _ E.1 hX.1
          (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY p W).1 E.2⟩ := by
  have hsq : IsPullback
      (ObjectProperty.homMk (W.subspace.fromPreimage p) :
        (⟨(W.subspace.preimage p).toFunctor,
          (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY p W).1⟩ :
          AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨W.subspace.toFunctor, W.isClosedSubspace.1⟩)
      (ObjectProperty.homMk (W.subspace.preimage p).ι :
        (⟨(W.subspace.preimage p).toFunctor,
          (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY p W).1⟩ :
          AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hX.1⟩)
      (ObjectProperty.homMk W.subspace.ι :
        (⟨W.subspace.toFunctor, W.isClosedSubspace.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)
          ⟶ ⟨Y, hY.1⟩)
      (ObjectProperty.homMk p : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨Y, hY.1⟩) :=
    IsPullback.of_map_of_faithful (F := ObjectProperty.ι _)
      (Subfunctor.isPullback_preimage p W.subspace)
  exact isPullbackDefined_of_isPullback_of_isFlat D.site D.base D.base_mem _ _ hsq E hE.1 hE.2

section Section

variable (L : Modules.{u, u} D.site D.base D.base_mem X hX.1) (hL : IsInvertibleSheaf D sX hX L)
    (s : L.sections)
    (hE : IsRelativeEffectiveCartierDivisor D.site D.base D.base_mem
      (ObjectProperty.homMk p : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨Y, hY.1⟩) (vanishingLocus D sX hX L s))


/-- The cycle of a closed subspace depends only on the subfunctor, not on the proof that it is a
closed subspace. -/
theorem cycleCoeffOfClosedSubspace_congr_subfunctor
    {T : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sT : T ⟶ D.space) (hT : D.IsGood sT) (n : ℤ) {A A' : Subfunctor T}
    (hA : IsClosedSubspace D.site D.base D.base_mem A)
    (hA' : IsClosedSubspace D.site D.base D.base_mem A') (h : A = A') :
    cycleCoeffOfClosedSubspace D sT hT A hA n
        (canonicalGeometricPoint D.site D.base D.base_mem A.toFunctor) =
      cycleCoeffOfClosedSubspace D sT hT A' hA' n
        (canonicalGeometricPoint D.site D.base D.base_mem A'.toFunctor) := by
  subst h
  rfl

include hL in
/-- **Stacks 0ER7 for the inverse image of an integral closed subspace.** Let `W ⊆ Y` be an
integral closed subspace of δ-dimension `k + 1`. Then the refined Gysin map of `E = Z(s)` sends
`p^*[W] = [p^{-1}(W)]_{k+r+2}` to `[(p|_E)^{-1}(W)]_{k+r+1}`, coefficientwise: for every integral
closed subspace `T ⊆ E`

`∑_{W'} m_{W', p^{-1}(W)} · (i^*[W'])_T = m_{T, (p|_E)^{-1}(W)}`.

The section `s|_{p^{-1}(W)}` is regular, its zero scheme `E ∩ p^{-1}(W)` being an effective
Cartier divisor on `p^{-1}(W)` (Stacks 0EPN), so Stacks 0EQL applies on `p^{-1}(W)`. Its
right-hand side is the sum of the cycles `[E ∩ W']_k` of clause (1)(a) of Stacks 0ER1 over the
components `W'` of `p^{-1}(W)`, none of which lies in `E`; its left-hand side is the cycle of
`E ∩ p^{-1}(W) = (p|_E)^{-1}(W)`. Both sides are compared after pushing forward to `X`. -/
theorem finsum_flatPullbackMult_mul_gysinComponentCycle_sectionGysinRule (k : ℤ)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y) (hW : deltaDimension D sY W = k + 1)
    (T : IntegralClosedSubspace D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor) :
    ∑ᶠ W' : IntegralClosedSubspace D.site D.base D.base_mem X,
        flatPullbackMult D sX hX sY hY p hbase (r + 1) hflat hr W W' *
          (gysinComponentCycle D sX (vanishingLocus D sX hX L s)
            (isGood_vanishingLocus D sX hX L s) (k + r + 1)
            (sectionGysinRule D sX hX L s (k + r + 1) hL) W').1 T =
      flatPullbackMult D ((vanishingLocus D sX hX L s).1.ι ≫ sX)
        (isGood_vanishingLocus D sX hX L s) sY hY ((vanishingLocus D sX hX L s).1.ι ≫ p)
        (comp_structureMorphism_eq D _ sX sY _ p rfl hbase) r hE.2
        (hasRelativeDimension_ι_comp D sX hX sY hY p hbase r hr _ hE) W T := by
  classical
  have hEg : D.IsGood ((vanishingLocus D sX hX L s).1.ι ≫ sX) := isGood_vanishingLocus D sX hX L s
  have hXdec := D.isDecentSpace_of_isGood sX hX
  have hLm : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  have heq : (k + 1 + ((r + 1 : ℕ) : ℤ) : ℤ) = k + r + 1 + 1 := by push_cast; ring
  have heq' : (k + 1 + (r : ℤ) : ℤ) = k + r + 1 := by ring
  -- the closed subspace `Z = p^{-1}(W)` and the restriction of `s` to it
  set Zc : ClosedSubspaces D.site D.base D.base_mem X :=
    ⟨W.subspace.preimage p, isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY p W⟩
    with hZcdef
  have hZg : D.IsGood (Zc.1.ι ≫ sX) := isGood_closedSubspace D sX hX Zc
  have hdim : deltaDimensionSubspace D sX hX Zc.1 Zc.2 ≤ (((k + r + 1) + 1 : ℤ) : EInt) := by
    have h := deltaDimensionSubspace_preimage_integralClosedSubspace_le D sX hX sY hY p hbase
      (r + 1) hflat hr W
    rwa [hW, heq] at h
  set sZ : (closedSubspaceModuleRestrict D sX hX L Zc).sections :=
    modulePullbackSections D.site D.base D.base_mem
      (closedSubspaceHom D.site D.base D.base_mem hX.1 Zc.1 Zc.2) L s with hsZdef
  have hZ0 : vanishingLocus D (Zc.1.ι ≫ sX) hZg (closedSubspaceModuleRestrict D sX hX L Zc) sZ =
      ⟨(vanishingLocus D sX hX L s).1.preimage Zc.1.ι,
        isClosedSubspace_preimage D.site D.base D.base_mem _ (vanishingLocus D sX hX L s).1 hX.1
          Zc.2.1 (vanishingLocus D sX hX L s).2⟩ :=
    zeroScheme_modulePullbackSections D.site D.base D.base_mem ⟨X, hX.1⟩
      ⟨Zc.1.toFunctor, Zc.2.1⟩ L hL s (closedSubspaceHom D.site D.base D.base_mem hX.1 Zc.1 Zc.2)
  have hinvZ := isInvertible_modulePullback_obj D.site D.base D.base_mem
    (closedSubspaceHom D.site D.base D.base_mem hX.1 Zc.1 Zc.2) L hL
  have hs : AlgebraicGeometry.IsRegularSection
      (structureCommRings D.site D.base D.base_mem ⟨Zc.1.toFunctor, Zc.2.1⟩)
      (structureRingSheaf D.site D.base D.base_mem ⟨Zc.1.toFunctor, Zc.2.1⟩).property sZ := by
    have hC : IsEffectiveCartierDivisor D.site D.base D.base_mem ⟨Zc.1.toFunctor, Zc.2.1⟩
        (vanishingLocus D (Zc.1.ι ≫ sX) hZg (closedSubspaceModuleRestrict D sX hX L Zc) sZ) := by
      rw [hZ0]
      exact isEffectiveCartierDivisor_preimage_ι_preimage D sX hX sY hY p _ hE W
    exact isRegularSection_of_isEffectiveCartierDivisor_zeroScheme D.site D.base D.base_mem
      ⟨Zc.1.toFunctor, Zc.2.1⟩ _ sZ hinvZ hC
  -- the multiplicities of `p^*[W]` are the coefficients of `[p^{-1}(W)]_{k+r+2}`
  have hm : ∀ W', flatPullbackMult D sX hX sY hY p hbase (r + 1) hflat hr W W' =
      (closedSubspaceCycle D sX hX Zc.1 Zc.2 (k + r + 1 + 1) hdim).1 W' := by
    intro W'
    change cycleCoeffOfClosedSubspace D sX hX (W.subspace.preimage p) _
        (deltaDimension D sY W + ((r + 1 : ℕ) : ℤ)) _ W' =
      cycleCoeffOfClosedSubspace D sX hX (W.subspace.preimage p) _ (k + r + 1 + 1) _ W'
    rw [hW, heq]
  -- the multiplicities of `(p|_E)^*[W]` are the coefficients of `[E ∩ p^{-1}(W)]_{k+r+1}`
  have hmE : ∀ T', flatPullbackMult D ((vanishingLocus D sX hX L s).1.ι ≫ sX) hEg sY hY
      ((vanishingLocus D sX hX L s).1.ι ≫ p)
      (comp_structureMorphism_eq D _ sX sY _ p rfl hbase) r hE.2
      (hasRelativeDimension_ι_comp D sX hX sY hY p hbase r hr _ hE) W T' =
      cycleCoeffOfClosedSubspace D ((vanishingLocus D sX hX L s).1.ι ≫ sX) hEg
        (Zc.1.preimage (vanishingLocus D sX hX L s).1.ι)
        (isClosedSubspace_preimage D.site D.base D.base_mem _ Zc.1 hX.1 hEg.1 Zc.2)
        (k + r + 1) (canonicalGeometricPoint D.site D.base D.base_mem _) T' := by
    intro T'
    change cycleCoeffOfClosedSubspace D ((vanishingLocus D sX hX L s).1.ι ≫ sX) hEg
        (W.subspace.preimage ((vanishingLocus D sX hX L s).1.ι ≫ p)) _
        (deltaDimension D sY W + (r : ℤ)) _ T' = _
    rw [hW, heq']
    rfl
  -- it suffices to compare the pushforwards to `X`
  suffices key : cycleClosedPushforward D hX.1 (vanishingLocus D sX hX L s).2.1 hXdec
      (vanishingLocus D sX hX L s).2.2
      (fun T' => ∑ᶠ W' : IntegralClosedSubspace D.site D.base D.base_mem X,
        flatPullbackMult D sX hX sY hY p hbase (r + 1) hflat hr W W' *
          (gysinComponentCycle D sX (vanishingLocus D sX hX L s) hEg (k + r + 1)
            (sectionGysinRule D sX hX L s (k + r + 1) hL) W').1 T') =
      cycleClosedPushforward D hX.1 (vanishingLocus D sX hX L s).2.1 hXdec
        (vanishingLocus D sX hX L s).2.2
        (cycleCoeffOfClosedSubspace D ((vanishingLocus D sX hX L s).1.ι ≫ sX) hEg
          (Zc.1.preimage (vanishingLocus D sX hX L s).1.ι)
          (isClosedSubspace_preimage D.site D.base D.base_mem _ Zc.1 hX.1 hEg.1 Zc.2)
          (k + r + 1) (canonicalGeometricPoint D.site D.base D.base_mem _)) by
    have h := congrFun key
      (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1
        (vanishingLocus D sX hX L s).2.1 hXdec (vanishingLocus D sX hX L s).2.2 T)
    rw [cycleClosedPushforward_apply_pushforward, cycleClosedPushforward_apply_pushforward] at h
    rw [h, hmE]
  funext T'
  rw [cycleClosedPushforward_finsum_mul D hX.1 (vanishingLocus D sX hX L s).2.1 hXdec
      (vanishingLocus D sX hX L s).2.2]
  simp_rw [hm]
  rw [← cycleClosedPushforward_vanishingLocus_eq_finsum_closedSubspaceCycle_mul D sX hX L hLm Zc sZ
    hs hdim (fun W' => cycleClosedPushforward D hX.1 (vanishingLocus D sX hX L s).2.1 hXdec
      (vanishingLocus D sX hX L s).2.2 (gysinComponentCycle D sX (vanishingLocus D sX hX L s) hEg
        (k + r + 1) (sectionGysinRule D sX hX L s (k + r + 1) hL) W').1) ?_ T']
  · -- the cycle of `E ∩ p^{-1}(W)`, read on `p^{-1}(W)` and on `E`
    have hd₁ : deltaDimensionSubspace D (Zc.1.ι ≫ sX) hZg
        ((vanishingLocus D sX hX L s).1.preimage Zc.1.ι)
        (isClosedSubspace_preimage D.site D.base D.base_mem _ (vanishingLocus D sX hX L s).1 hX.1
          Zc.2.1 (vanishingLocus D sX hX L s).2) ≤ ((k + r + 1 : ℤ) : EInt) := by
      have h := deltaDimensionSubspace_vanishingLocus_closedSubspaceModuleRestrict_le D sX hX L Zc
        hLm sZ hs hdim
      rw [hZ0] at h
      exact h
    have hd₂ : deltaDimensionSubspace D ((vanishingLocus D sX hX L s).1.ι ≫ sX) hEg
        (Zc.1.preimage (vanishingLocus D sX hX L s).1.ι)
        (isClosedSubspace_preimage D.site D.base D.base_mem _ Zc.1 hX.1 hEg.1 Zc.2) ≤
          ((k + r + 1 : ℤ) : EInt) := by
      have h := deltaDimensionSubspace_preimage_integralClosedSubspace_le D
        ((vanishingLocus D sX hX L s).1.ι ≫ sX) hEg sY hY ((vanishingLocus D sX hX L s).1.ι ≫ p)
        (comp_structureMorphism_eq D _ sX sY _ p rfl hbase) r hE.2
        (hasRelativeDimension_ι_comp D sX hX sY hY p hbase r hr _ hE) W
      rwa [hW, heq'] at h
    have key := congrFun (congrArg Subtype.val
      (cycleGroupClosedPushforward_closedSubspaceCycle_eq_of_iso D sX hX Zc.2.2
        (vanishingLocus D sX hX L s).2.2 _ hZg _ hEg rfl rfl _ _ _ _
        (Subfunctor.preimageιIso Zc.1 (vanishingLocus D sX hX L s).1)
        (Subfunctor.preimageιIso_hom_comp_ι Zc.1 (vanishingLocus D sX hX L s).1) (k + r + 1)
        hd₁ hd₂)) T'
    refine Eq.trans ?_ key
    rw [cycleCoeffOfClosedSubspace_congr_subfunctor D _ hZg _ _ _ (congrArg Subtype.val hZ0)]
    rfl
  · -- the summand of Stacks 0EQL at a component is the Gysin component of its image
    intro V hV
    have hmW : flatPullbackMult D sX hX sY hY p hbase (r + 1) hflat hr W
        (closedSubspaceComponentImage D sX hX Zc.1 Zc.2 V) ≠ 0 := by
      rw [hm]
      exact hV
    have hWE := not_le_of_flatPullbackMult_ne_zero D sX hX sY hY p hbase r hflat hr _ hE W _ hmW
    have hW'd : deltaDimension D sX (closedSubspaceComponentImage D sX hX Zc.1 Zc.2 V) =
        k + r + 1 + 1 := (closedSubspaceCycle D sX hX Zc.1 Zc.2 (k + r + 1 + 1) hdim).2.2 _ hV
    rw [gysinComponentCycle_of_not_le D sX (vanishingLocus D sX hX L s) hEg (k + r + 1) _ hW'd hWE]
    change (closedSubspaceCyclePushforward D sX hX (vanishingLocus D sX hX L s) (k + r + 1)
      (gysinIntersectionCycle D sX hX (vanishingLocus D sX hX L s) hEg (k + r + 1) _ hW'd
        hWE)).1 = _
    rw [← integralClosedSubspacePushforward_closedSubspaceCycle_preimage_eq_gysinIntersectionCycle
      D sX hX (vanishingLocus D sX hX L s) hEg _ (isGood_integralClosedSubspace D sX hX _)
        (k + r + 1) hW'd hWE,
      ← cycleClosedPushforward_vanishingLocus_closedSubspaceComponentImageSection D sX hX L Zc hLm
        sZ hs hdim V]
    refine congrArg (cycleClosedPushforward D hX.1 _ hXdec _)
      (cycleCoeffOfClosedSubspace_congr_subfunctor D _ _ _ _ _ ?_)
    have h1 := congrArg Subtype.val
      (zeroScheme_closedSubspaceComponentImageSection D sX hX L Zc hLm sZ V)
    have hι : (closedSubspaceComponentImageHom D sX hX Zc V).hom ≫ Zc.1.ι =
        (closedSubspaceComponentImage D sX hX Zc.1 Zc.2 V).subspace.ι :=
      congrArg (fun m => m.hom)
        (closedSubspaceComponentImageHom_comp_closedSubspaceHom D sX hX Zc V)
    refine Eq.trans ?_ h1.symm
    change _ = (vanishingLocus D (Zc.1.ι ≫ sX) hZg (closedSubspaceModuleRestrict D sX hX L Zc)
      sZ).1.preimage (closedSubspaceComponentImageHom D sX hX Zc V).hom
    rw [hZ0]
    change _ = ((vanishingLocus D sX hX L s).1.preimage Zc.1.ι).preimage
        (closedSubspaceComponentImageHom D sX hX Zc V).hom
    rw [← Subfunctor.preimage_comp, hι]

/-- **The first identity of Stacks 0ERE on cycles.** Let `ℒ` be an invertible `𝒪_X`-module with a
global section `s` whose vanishing locus `E = Z(s)` is a relative effective Cartier divisor on
`X/Y`. Then the refined Gysin map of Stacks 0ER1 at the level of cycles satisfies
`i^* p^* α = (p|_E)^* α` in `Z_{k+r+1}(E)` for every `(k+1)`-cycle `α` on `Y`. -/
theorem gysinCycleMap_sectionGysinRule_flatPullbackMap (k : ℤ) (α : CycleGroup D sY (k + 1)) :
    gysinCycleMap D sX (vanishingLocus D sX hX L s) (isGood_vanishingLocus D sX hX L s)
        (k + r + 1) (sectionGysinRule D sX hX L s (k + r + 1) hL)
        (flatPullbackMap D sX hX sY hY p hbase (r + 1) hflat hr (k + 1) (k + r + 1 + 1)
          (by push_cast; ring) α) =
      flatPullbackMap D ((vanishingLocus D sX hX L s).1.ι ≫ sX)
        (isGood_vanishingLocus D sX hX L s) sY hY ((vanishingLocus D sX hX L s).1.ι ≫ p)
        (comp_structureMorphism_eq D _ sX sY _ p rfl hbase) r hE.2
        (hasRelativeDimension_ι_comp D sX hX sY hY p hbase r hr _ hE) (k + 1) (k + r + 1)
        (by ring) α :=
  gysinCycleMap_flatPullbackMap_eq_of_forall_integral D sX hX sY hY p hbase r hflat hr _ hE k _
    (fun W hW T => finsum_flatPullbackMult_mul_gysinComponentCycle_sectionGysinRule D sX hX sY hY p
      hbase r hflat hr L hL s hE k W hW T) α

/-- **The first identity of Stacks 0ERE**, for the vanishing locus `E = Z(s)` of a global section
of an invertible sheaf which is a relative effective Cartier divisor: `i^* p^* α = (p|_E)^* α` in
`CH_{k+r+1}(E)`. -/
theorem sectionRefinedGysin_flatPullbackMap (k : ℤ) (α : CycleGroup D sY (k + 1)) :
    sectionRefinedGysin.{v} D sX hX L s (k + r + 1) hL
        (flatPullbackMap D sX hX sY hY p hbase (r + 1) hflat hr (k + 1) (k + r + 1 + 1)
          (by push_cast; ring) α) =
      chowClass.{v} D ((vanishingLocus D sX hX L s).1.ι ≫ sX)
        (isGood_vanishingLocus D sX hX L s) (k + r + 1)
        (flatPullbackMap D ((vanishingLocus D sX hX L s).1.ι ≫ sX)
          (isGood_vanishingLocus D sX hX L s) sY hY ((vanishingLocus D sX hX L s).1.ι ≫ p)
          (comp_structureMorphism_eq D _ sX sY _ p rfl hbase) r hE.2
          (hasRelativeDimension_ι_comp D sX hX sY hY p hbase r hr _ hE) (k + 1) (k + r + 1)
          (by ring) α) :=
  congrArg (chowClass.{v} D _ (isGood_vanishingLocus D sX hX L s) (k + r + 1))
    (gysinCycleMap_sectionGysinRule_flatPullbackMap D sX hX sY hY p hbase r hflat hr L hL s hE k α)

/-- **The second identity of Stacks 0ERE**, for the vanishing locus `E = Z(s)` of a global section
of an invertible sheaf which is a relative effective Cartier divisor:
`c₁(ℒ) ∩ p^* α = i_*((p|_E)^* α)` in `CH_{k+r+1}(X)`, by the first identity and Stacks 0ER4. -/
theorem canonicalFirstChernCap_flatPullbackMap (k : ℤ) (α : CycleGroup D sY (k + 1)) :
    canonicalFirstChernCap.{u, max (u + 1) v} D sX hX L
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) (k + r + 1)
        (flatPullbackMap D sX hX sY hY p hbase (r + 1) hflat hr (k + 1) (k + r + 1 + 1)
          (by push_cast; ring) α) =
      chowGroupClosedPushforward.{max (u + 1) v} D sX hX (vanishingLocus D sX hX L s).1
        (vanishingLocus D sX hX L s).2 (k + r + 1)
        (chowClass.{max (u + 1) v} D ((vanishingLocus D sX hX L s).1.ι ≫ sX)
          (isGood_vanishingLocus D sX hX L s) (k + r + 1)
          (flatPullbackMap D ((vanishingLocus D sX hX L s).1.ι ≫ sX)
            (isGood_vanishingLocus D sX hX L s) sY hY ((vanishingLocus D sX hX L s).1.ι ≫ p)
            (comp_structureMorphism_eq D _ sX sY _ p rfl hbase) r hE.2
            (hasRelativeDimension_ι_comp D sX hX sY hY p hbase r hr _ hE) (k + 1) (k + r + 1)
            (by ring) α)) := by
  rw [← sectionRefinedGysin_flatPullbackMap.{max (u + 1) v} D sX hX sY hY p hbase r hflat hr L hL
    s hE k α, chowGroupClosedPushforward_sectionRefinedGysin]

/-- The first identity of Stacks 0ERE in the Chow group of Stacks 0EQ6 at the canonical
embeddings of Stacks 0ENK: the class of the identity of cycles
`AlgebraicGeometry.Space.gysinCycleMap_sectionGysinRule_flatPullbackMap`. -/
theorem chowClassCanonical_gysinCycleMap_sectionGysinRule_flatPullbackMap (k : ℤ)
    (α : CycleGroup D sY (k + 1)) :
    chowClassCanonical.{v} D ((vanishingLocus D sX hX L s).1.ι ≫ sX)
        (isGood_vanishingLocus D sX hX L s) (k + r + 1)
        (gysinCycleMap D sX (vanishingLocus D sX hX L s) (isGood_vanishingLocus D sX hX L s)
          (k + r + 1) (sectionGysinRule D sX hX L s (k + r + 1) hL)
          (flatPullbackMap D sX hX sY hY p hbase (r + 1) hflat hr (k + 1) (k + r + 1 + 1)
            (by push_cast; ring) α)) =
      chowClassCanonical.{v} D ((vanishingLocus D sX hX L s).1.ι ≫ sX)
        (isGood_vanishingLocus D sX hX L s) (k + r + 1)
        (flatPullbackMap D ((vanishingLocus D sX hX L s).1.ι ≫ sX)
          (isGood_vanishingLocus D sX hX L s) sY hY ((vanishingLocus D sX hX L s).1.ι ≫ p)
          (comp_structureMorphism_eq D _ sX sY _ p rfl hbase) r hE.2
          (hasRelativeDimension_ι_comp D sX hX sY hY p hbase r hr _ hE) (k + 1) (k + r + 1)
          (by ring) α) :=
  congrArg (chowClassCanonical.{v} D _ (isGood_vanishingLocus D sX hX L s) (k + r + 1))
    (gysinCycleMap_sectionGysinRule_flatPullbackMap D sX hX sY hY p hbase r hflat hr L hL s hE k α)

/-- The second identity of Stacks 0ERE in the Chow group of Stacks 0EQ6 at the canonical
embeddings of Stacks 0ENK, for the vanishing locus `E = Z(s)` of a global section of an
invertible sheaf which is a relative effective Cartier divisor:
`c₁(ℒ) ∩ p^* α = i_*((p|_E)^* α)`, by the identity of cycles
`gysinCycleMap_sectionGysinRule_flatPullbackMap` and Stacks 0ER4,
`chowClassCanonical_closedSubspaceCyclePushforward_gysinCycleMap_sectionGysinRule`. -/
theorem chowClassCanonical_firstChernCapCycleMap_flatPullbackMap (k : ℤ)
    (α : CycleGroup D sY (k + 1)) :
    chowClassCanonical.{max (u + 1) v} D sX hX (k + r + 1)
        (firstChernCapCycleMap D sX hX (k + r + 1)
          (canonicalFirstChernRule D sX hX L
            (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) (k + r + 1))
          (flatPullbackMap D sX hX sY hY p hbase (r + 1) hflat hr (k + 1) (k + r + 1 + 1)
            (by push_cast; ring) α)) =
      chowClassCanonical.{max (u + 1) v} D sX hX (k + r + 1)
        (closedSubspaceCyclePushforward D sX hX (vanishingLocus D sX hX L s) (k + r + 1)
          (flatPullbackMap D ((vanishingLocus D sX hX L s).1.ι ≫ sX)
            (isGood_vanishingLocus D sX hX L s) sY hY ((vanishingLocus D sX hX L s).1.ι ≫ p)
            (comp_structureMorphism_eq D _ sX sY _ p rfl hbase) r hE.2
            (hasRelativeDimension_ι_comp D sX hX sY hY p hbase r hr _ hE) (k + 1) (k + r + 1)
            (by ring) α)) := by
  rw [← gysinCycleMap_sectionGysinRule_flatPullbackMap D sX hX sY hY p hbase r hflat hr L hL s hE
    k α]
  exact (chowClassCanonical_closedSubspaceCyclePushforward_gysinCycleMap_sectionGysinRule D sX hX L
    hL s (k + r + 1) _).symm

end Section

section Divisor

variable (Dv : ClosedSubspaces D.site D.base D.base_mem X)
    (hDv : IsRelativeEffectiveCartierDivisor D.site D.base D.base_mem
      (ObjectProperty.homMk p : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨Y, hY.1⟩) Dv)

/-- The vanishing locus `Z(1_D)` of the canonical section of `𝒪_X(D)` is `D` (Stacks 0847), so it
is a relative effective Cartier divisor when `D` is one. -/
theorem isRelativeEffectiveCartierDivisor_vanishingLocus_canonicalSection :
    IsRelativeEffectiveCartierDivisor D.site D.base D.base_mem
      (ObjectProperty.homMk p : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨Y, hY.1⟩)
      (vanishingLocus D sX hX
        (associatedInvertibleSheaf D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1)
        (canonicalSection D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1)) := by
  have h : vanishingLocus D sX hX
      (associatedInvertibleSheaf D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1)
      (canonicalSection D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1) = Dv :=
    zeroScheme_canonicalSection_eq D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1
  rw [h]
  exact hDv

/-- The first identity of Stacks 0ERE in the Chow group `AlgebraicGeometry.Space.chowGroup`
whose rational equivalences quantify the embedding `R(W) → Q(𝒪^h_{W,ξ})` existentially. In
Situation 0EDT let `X, Y/B` be good, let `p : X ⟶ Y` be flat of relative dimension `r + 1` and
let `i : D → X` be a relative effective Cartier divisor on `X/Y` (Stacks 0EPP), with
`ℒ = 𝒪_X(D)` and its canonical section `1_D` (Stacks 0841), whose vanishing locus `Z(1_D)` is `D`
(Stacks 0847). Then for every `(k+1)`-cycle `α` on `Y`

`i^* p^* α = (p|_D)^* α` in `CH_{k+r+1}(D)`,

where `p^*` is the flat pullback of Stacks 0EP8, `i^*` the refined Gysin homomorphism of Stacks
0ER1 for the pair `(𝒪_X(D), 1_D)` (`AlgebraicGeometry.Space.sectionRefinedGysin`), and
`(p|_D)^*` the flat pullback along `p|_D : D → Y`, which is flat of relative dimension `r`. The
identity holds already on cycles,
`AlgebraicGeometry.Space.gysinCycleMap_sectionGysinRule_flatPullbackMap`. -/
theorem sectionRefinedGysin_canonicalSection_flatPullbackMap (k : ℤ)
    (α : CycleGroup D sY (k + 1)) :
    sectionRefinedGysin.{v} D sX hX
        (associatedInvertibleSheaf D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1)
        (canonicalSection D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1) (k + r + 1)
        (associatedInvertibleSheaf_isInvertible D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1)
        (flatPullbackMap D sX hX sY hY p hbase (r + 1) hflat hr (k + 1) (k + r + 1 + 1)
          (by push_cast; ring) α) =
      chowClass.{v} D (_ ≫ sX) (isGood_vanishingLocus D sX hX _ _) (k + r + 1)
        (flatPullbackMap D (_ ≫ sX) (isGood_vanishingLocus D sX hX _ _) sY hY (_ ≫ p)
          (comp_structureMorphism_eq D _ sX sY _ p rfl hbase) r
          (isRelativeEffectiveCartierDivisor_vanishingLocus_canonicalSection D sX hX sY hY p Dv
            hDv).2
          (hasRelativeDimension_ι_comp D sX hX sY hY p hbase r hr _
            (isRelativeEffectiveCartierDivisor_vanishingLocus_canonicalSection D sX hX sY hY p Dv
              hDv)) (k + 1) (k + r + 1) (by ring) α) :=
  sectionRefinedGysin_flatPullbackMap D sX hX sY hY p hbase r hflat hr _
    (associatedInvertibleSheaf_isInvertible D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1) _
    (isRelativeEffectiveCartierDivisor_vanishingLocus_canonicalSection D sX hX sY hY p Dv hDv) k α

/-- The second identity of Stacks 0ERE in the Chow group `AlgebraicGeometry.Space.chowGroup`.
In the situation of `AlgebraicGeometry.Space.sectionRefinedGysin_canonicalSection_flatPullbackMap`,
for every
`(k+1)`-cycle `α` on `Y`

`c₁(𝒪_X(D)) ∩ p^* α = i_* ((p|_D)^* α)` in `CH_{k+r+1}(X)`,

where `c₁(𝒪_X(D)) ∩ -` is the cap product of Stacks 0EQJ
(`AlgebraicGeometry.Space.canonicalFirstChernCap`) and `i_*` the pushforward along the closed
immersion `i : D → X` (`AlgebraicGeometry.Space.chowGroupClosedPushforward`). It follows from the
first identity and Stacks 0ER4. -/
theorem canonicalFirstChernCap_canonicalSection_flatPullbackMap (k : ℤ)
    (α : CycleGroup D sY (k + 1)) :
    canonicalFirstChernCap.{u, max (u + 1) v} D sX hX
        (associatedInvertibleSheaf D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1)
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
          (associatedInvertibleSheaf_isInvertible D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1))
        (k + r + 1)
        (flatPullbackMap D sX hX sY hY p hbase (r + 1) hflat hr (k + 1) (k + r + 1 + 1)
          (by push_cast; ring) α) =
      chowGroupClosedPushforward.{max (u + 1) v} D sX hX
        (vanishingLocus D sX hX
          (associatedInvertibleSheaf D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1)
          (canonicalSection D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1)).1
        (vanishingLocus D sX hX _ _).2 (k + r + 1)
        (chowClass.{max (u + 1) v} D (_ ≫ sX) (isGood_vanishingLocus D sX hX _ _) (k + r + 1)
          (flatPullbackMap D (_ ≫ sX) (isGood_vanishingLocus D sX hX _ _) sY hY (_ ≫ p)
            (comp_structureMorphism_eq D _ sX sY _ p rfl hbase) r
            (isRelativeEffectiveCartierDivisor_vanishingLocus_canonicalSection D sX hX sY hY p Dv
              hDv).2
            (hasRelativeDimension_ι_comp D sX hX sY hY p hbase r hr _
              (isRelativeEffectiveCartierDivisor_vanishingLocus_canonicalSection D sX hX sY hY p
                Dv hDv)) (k + 1) (k + r + 1) (by ring) α)) :=
  canonicalFirstChernCap_flatPullbackMap.{v} D sX hX sY hY p hbase r hflat hr _
    (associatedInvertibleSheaf_isInvertible D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1) _
    (isRelativeEffectiveCartierDivisor_vanishingLocus_canonicalSection D sX hX sY hY p Dv hDv) k α

/-- **Stacks 0ERE, first identity.** In Situation 0EDT let `X, Y/B` be good, let `p : X ⟶ Y` be
flat of relative dimension `r + 1` and let `i : D → X` be a relative effective Cartier divisor on
`X/Y` (Stacks 0EPP), with `ℒ = 𝒪_X(D)` and its canonical section `1_D` (Stacks 0841), whose
vanishing locus `Z(1_D)` is `D` (Stacks 0847). Then for every `(k+1)`-cycle `α` on `Y`

`i^* p^* α = (p|_D)^* α` in `CH_{k+r+1}(D)`,

where `p^*` is the flat pullback of cycles of Stacks 0EP8
(`AlgebraicGeometry.Space.flatPullbackMap`), `i^*` the refined Gysin map of Stacks 0ER1 for the
pair `(𝒪_X(D), 1_D)` on cycles (`AlgebraicGeometry.Space.gysinCycleMap` at
`AlgebraicGeometry.Space.sectionGysinRule`), and `(p|_D)^*` the flat pullback along
`p|_D : D → Y`, which is flat of relative dimension `r`; the classes are taken in `CH_{k+r+1}(D)`
of Stacks 0EQ6, `AlgebraicGeometry.Space.chowGroupCanonical`. The identity holds already on
cycles, `AlgebraicGeometry.Space.gysinCycleMap_sectionGysinRule_flatPullbackMap`. -/
@[stacks 0ERE "first identity: i^* p^* α = (p|_D)^* α in CH_{k+r}(D), on cycles: i^* is the \
refined Gysin map of Stacks 0ER1 for (O_X(D), 1_D) (gysinCycleMap at sectionGysinRule), p^* and \
(p|_D)^* the flat pullbacks of Stacks 0EP8, the classes taken in the Chow group of Stacks 0EQ6 at \
the canonical embeddings of Stacks 0ENK (chowGroupCanonical); the identity holds already in Z(D)"]
theorem chowClassCanonical_gysinCycleMap_canonicalSection_flatPullbackMap (k : ℤ)
    (α : CycleGroup D sY (k + 1)) :
    chowClassCanonical.{v} D (_ ≫ sX) (isGood_vanishingLocus D sX hX _ _) (k + r + 1)
        (gysinCycleMap D sX (vanishingLocus D sX hX
            (associatedInvertibleSheaf D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1)
            (canonicalSection D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1))
          (isGood_vanishingLocus D sX hX _ _) (k + r + 1)
          (sectionGysinRule D sX hX _ _ (k + r + 1)
            (associatedInvertibleSheaf_isInvertible D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1))
          (flatPullbackMap D sX hX sY hY p hbase (r + 1) hflat hr (k + 1) (k + r + 1 + 1)
            (by push_cast; ring) α)) =
      chowClassCanonical.{v} D (_ ≫ sX) (isGood_vanishingLocus D sX hX _ _) (k + r + 1)
        (flatPullbackMap D (_ ≫ sX) (isGood_vanishingLocus D sX hX _ _) sY hY (_ ≫ p)
          (comp_structureMorphism_eq D _ sX sY _ p rfl hbase) r
          (isRelativeEffectiveCartierDivisor_vanishingLocus_canonicalSection D sX hX sY hY p Dv
            hDv).2
          (hasRelativeDimension_ι_comp D sX hX sY hY p hbase r hr _
            (isRelativeEffectiveCartierDivisor_vanishingLocus_canonicalSection D sX hX sY hY p Dv
              hDv)) (k + 1) (k + r + 1) (by ring) α) :=
  chowClassCanonical_gysinCycleMap_sectionGysinRule_flatPullbackMap D sX hX sY hY p hbase r hflat
    hr _ (associatedInvertibleSheaf_isInvertible D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1) _
    (isRelativeEffectiveCartierDivisor_vanishingLocus_canonicalSection D sX hX sY hY p Dv hDv) k α

/-- **Stacks 0ERE, second identity.** In the situation of
`AlgebraicGeometry.Space.chowClassCanonical_gysinCycleMap_canonicalSection_flatPullbackMap`, for
every `(k+1)`-cycle `α` on `Y`

`c₁(𝒪_X(D)) ∩ p^* α = i_* ((p|_D)^* α)` in `CH_{k+r+1}(X)`,

where `c₁(𝒪_X(D)) ∩ -` is the cycle-level cap product of Stacks 0EQJ at the canonical choices
(`AlgebraicGeometry.Space.firstChernCapCycleMap` at
`AlgebraicGeometry.Space.canonicalFirstChernRule`), `i_*` the pushforward of cycles along the
closed immersion `i : D → X`, and the classes are taken in `CH_{k+r+1}(X)` of Stacks 0EQ6,
`AlgebraicGeometry.Space.chowGroupCanonical`. It follows from the first identity and Stacks
0ER4. -/
@[stacks 0ERE "second identity: c₁(O_X(D)) ∩ p^* α = i_*((p|_D)^* α) in CH_{k+r}(X), on cycles: \
c₁ ∩ - is the cap product of Stacks 0EQJ at the canonical choices, p^* and (p|_D)^* the flat \
pullbacks of Stacks 0EP8, i_* the pushforward along the closed immersion, the classes taken in the \
Chow group of Stacks 0EQ6 at the canonical embeddings of Stacks 0ENK (chowGroupCanonical)"]
theorem chowClassCanonical_firstChernCapCycleMap_canonicalSection_flatPullbackMap (k : ℤ)
    (α : CycleGroup D sY (k + 1)) :
    chowClassCanonical.{max (u + 1) v} D sX hX (k + r + 1)
        (firstChernCapCycleMap D sX hX (k + r + 1)
          (canonicalFirstChernRule D sX hX
            (associatedInvertibleSheaf D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1)
            (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
              (associatedInvertibleSheaf_isInvertible D.site D.base D.base_mem ⟨X, hX.1⟩ Dv
                hDv.1)) (k + r + 1))
          (flatPullbackMap D sX hX sY hY p hbase (r + 1) hflat hr (k + 1) (k + r + 1 + 1)
            (by push_cast; ring) α)) =
      chowClassCanonical.{max (u + 1) v} D sX hX (k + r + 1)
        (closedSubspaceCyclePushforward D sX hX (vanishingLocus D sX hX
            (associatedInvertibleSheaf D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1)
            (canonicalSection D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1)) (k + r + 1)
          (flatPullbackMap D (_ ≫ sX) (isGood_vanishingLocus D sX hX _ _) sY hY (_ ≫ p)
            (comp_structureMorphism_eq D _ sX sY _ p rfl hbase) r
            (isRelativeEffectiveCartierDivisor_vanishingLocus_canonicalSection D sX hX sY hY p Dv
              hDv).2
            (hasRelativeDimension_ι_comp D sX hX sY hY p hbase r hr _
              (isRelativeEffectiveCartierDivisor_vanishingLocus_canonicalSection D sX hX sY hY p
                Dv hDv)) (k + 1) (k + r + 1) (by ring) α)) :=
  chowClassCanonical_firstChernCapCycleMap_flatPullbackMap D sX hX sY hY p hbase r hflat hr _
    (associatedInvertibleSheaf_isInvertible D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1) _
    (isRelativeEffectiveCartierDivisor_vanishingLocus_canonicalSection D sX hX sY hY p Dv hDv) k α

end Divisor

/-! ### Relative dimension zero -/

section RelativeDimensionZero

variable (hr₀ : HasRelativeDimension 0 D.site D.base D.base_mem p)

/-- The refined Gysin map of Stacks 0ER1 is zero when the vanishing locus has no points, the
Chow groups of that locus being zero. -/
theorem sectionRefinedGysin_eq_zero_of_isEmpty_points
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1) (s : L.sections)
    (hL : IsInvertibleSheaf D sX hX L)
    [IsEmpty (points D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor)] (k : ℤ)
    (β : CycleGroup D sX (k + 1)) : sectionRefinedGysin.{v} D sX hX L s k hL β = 0 := by
  refine (sectionRefinedGysin_apply D sX hX L s k hL β).1.trans ?_
  rw [CycleGroup.eq_zero_of_isEmpty_points D _ inferInstance (gysinCycleMap _ _ _ _ _ _ β),
    map_zero]

/-- In relative dimension zero a relative effective Cartier divisor has no points, so every cycle
on it vanishes. -/
private theorem isEmpty_points_and_cycleGroup_canonicalSection_eq_zero
    (hbase : p ≫ sY = sX) (hr₀ : HasRelativeDimension 0 D.site D.base D.base_mem p)
    (Dv : ClosedSubspaces D.site D.base D.base_mem X)
    (hDv : IsRelativeEffectiveCartierDivisor D.site D.base D.base_mem
      (ObjectProperty.homMk p : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨Y, hY.1⟩) Dv) :
    IsEmpty (points D.site D.base D.base_mem (vanishingLocus D sX hX
        (associatedInvertibleSheaf D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1)
        (canonicalSection D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1)).1.toFunctor) ∧
    ∀ (n : ℤ) (β : CycleGroup D ((vanishingLocus D sX hX
        (associatedInvertibleSheaf D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1)
        (canonicalSection D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1)).1.ι ≫ sX) n), β = 0 := by
  have := isEmpty_points_of_isRelativeEffectiveCartierDivisor D.site D.base D.base_mem _
    (isLocallyOfFiniteType_of_comp D.site D.base D.base_mem hX.1 hY.1 D.isAlgebraicSpace p sY
      (hbase ▸ hX.2.2)) hr₀ _
    (isRelativeEffectiveCartierDivisor_vanishingLocus_canonicalSection D sX hX sY hY p Dv hDv)
  exact ⟨this, fun n β => CycleGroup.eq_zero_of_isEmpty_points D _ inferInstance β⟩

include hbase hr₀ in
/-- Stacks 0ERE in relative dimension zero, in the Chow group `AlgebraicGeometry.Space.chowGroup`.
If `p : X ⟶ Y` is flat of relative dimension `0` and `i : D → X` is a relative effective Cartier
divisor on `X/Y`, then `D` has no points
(`AlgebraicGeometry.Space.isEmpty_points_of_isRelativeEffectiveCartierDivisor`), so every cycle on
`D` is zero, and for every `(k+1)`-cycle `α` on `Y` both sides of the two identities of Stacks
0ERE vanish: `i^* p^* α = 0` in `CH_k(D)` and `c₁(𝒪_X(D)) ∩ p^* α = i_*(0) = 0` in `CH_k(X)`. -/
theorem flatPullbackMap_canonicalSection_eq_zero_of_hasRelativeDimension_zero
    (Dv : ClosedSubspaces D.site D.base D.base_mem X)
    (hDv : IsRelativeEffectiveCartierDivisor D.site D.base D.base_mem
      (ObjectProperty.homMk p : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨Y, hY.1⟩) Dv) (k : ℤ) (α : CycleGroup D sY (k + 1)) :
    (∀ (n : ℤ) (β : CycleGroup D ((vanishingLocus D sX hX
        (associatedInvertibleSheaf D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1)
        (canonicalSection D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1)).1.ι ≫ sX) n), β = 0) ∧
    sectionRefinedGysin.{v} D sX hX
        (associatedInvertibleSheaf D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1)
        (canonicalSection D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1) k
        (associatedInvertibleSheaf_isInvertible D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1)
        (flatPullbackMap D sX hX sY hY p hbase 0 hflat hr₀ (k + 1) (k + 1) (by simp) α) = 0 ∧
    canonicalFirstChernCap.{u, max (u + 1) v} D sX hX
        (associatedInvertibleSheaf D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1)
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
          (associatedInvertibleSheaf_isInvertible D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1)) k
        (flatPullbackMap D sX hX sY hY p hbase 0 hflat hr₀ (k + 1) (k + 1) (by simp) α) = 0 := by
  obtain ⟨hempty, h0⟩ := isEmpty_points_and_cycleGroup_canonicalSection_eq_zero D sX hX sY hY p
    hbase hr₀ Dv hDv
  refine ⟨h0, sectionRefinedGysin_eq_zero_of_isEmpty_points D sX hX
      (associatedInvertibleSheaf D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1)
      (canonicalSection D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1)
      (associatedInvertibleSheaf_isInvertible D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1) k _, ?_⟩
  refine (chowGroupClosedPushforward_sectionRefinedGysin.{v} D sX hX _
    (associatedInvertibleSheaf_isInvertible D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1)
    (canonicalSection D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1) k
    (flatPullbackMap D sX hX sY hY p hbase 0 hflat hr₀ (k + 1) (k + 1) (by simp) α)).symm.trans ?_
  rw [sectionRefinedGysin_eq_zero_of_isEmpty_points D sX hX
      (associatedInvertibleSheaf D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1)
      (canonicalSection D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1)
      (associatedInvertibleSheaf_isInvertible D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1) k _,
          map_zero]

include hbase hr₀ in
/-- **Stacks 0ERE in relative dimension zero.** If `p : X ⟶ Y` is flat of relative dimension `0`
and `i : D → X` is a relative effective Cartier divisor on `X/Y`, then `D` has no points
(`AlgebraicGeometry.Space.isEmpty_points_of_isRelativeEffectiveCartierDivisor`), so every cycle on
`D` is zero, and for every `(k+1)`-cycle `α` on `Y` both sides of the two identities of Stacks
0ERE vanish: `i^* p^* α = 0` in `CH_k(D)` and `c₁(𝒪_X(D)) ∩ p^* α = i_*(0) = 0` in `CH_k(X)`, the
operations being those on cycles and the classes taken in the Chow groups of Stacks 0EQ6,
`AlgebraicGeometry.Space.chowGroupCanonical`. -/
@[stacks 0ERE "the case of relative dimension r = 0, where D is empty: every cycle on D is zero, \
and i^* p^* α = 0 in CH_k(D) and c₁(O_X(D)) ∩ p^* α = 0 in CH_k(X), on cycles, the classes taken \
in the Chow groups of Stacks 0EQ6 at the canonical embeddings of Stacks 0ENK (chowGroupCanonical)"]
theorem chowClassCanonical_flatPullbackMap_canonicalSection_eq_zero_of_hasRelativeDimension_zero
    (Dv : ClosedSubspaces D.site D.base D.base_mem X)
    (hDv : IsRelativeEffectiveCartierDivisor D.site D.base D.base_mem
      (ObjectProperty.homMk p : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨Y, hY.1⟩) Dv) (k : ℤ) (α : CycleGroup D sY (k + 1)) :
    (∀ (n : ℤ) (β : CycleGroup D ((vanishingLocus D sX hX
        (associatedInvertibleSheaf D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1)
        (canonicalSection D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1)).1.ι ≫ sX) n), β = 0) ∧
    chowClassCanonical.{v} D (_ ≫ sX) (isGood_vanishingLocus D sX hX _ _) k
        (gysinCycleMap D sX (vanishingLocus D sX hX
            (associatedInvertibleSheaf D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1)
            (canonicalSection D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1))
          (isGood_vanishingLocus D sX hX _ _) k
          (sectionGysinRule D sX hX _ _ k
            (associatedInvertibleSheaf_isInvertible D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1))
          (flatPullbackMap D sX hX sY hY p hbase 0 hflat hr₀ (k + 1) (k + 1) (by simp) α)) = 0 ∧
    chowClassCanonical.{max (u + 1) v} D sX hX k
        (firstChernCapCycleMap D sX hX k
          (canonicalFirstChernRule D sX hX
            (associatedInvertibleSheaf D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1)
            (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
              (associatedInvertibleSheaf_isInvertible D.site D.base D.base_mem ⟨X, hX.1⟩ Dv
                hDv.1)) k)
          (flatPullbackMap D sX hX sY hY p hbase 0 hflat hr₀ (k + 1) (k + 1) (by simp) α)) = 0 := by
  obtain ⟨hempty, h0⟩ := isEmpty_points_and_cycleGroup_canonicalSection_eq_zero D sX hX sY hY p
    hbase hr₀ Dv hDv
  refine ⟨h0, by rw [h0 _ (gysinCycleMap _ _ _ _ _ _ _), map_zero], ?_⟩
  rw [← chowClassCanonical_closedSubspaceCyclePushforward_gysinCycleMap_sectionGysinRule D sX hX _
    (associatedInvertibleSheaf_isInvertible D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1)
    (canonicalSection D.site D.base D.base_mem ⟨X, hX.1⟩ Dv hDv.1) k,
    h0 _ (gysinCycleMap _ _ _ _ _ _ _), map_zero, map_zero]

end RelativeDimensionZero

end AlgebraicGeometry.Space

end
