module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackAssociatedCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackOfCycles
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedImageDegree
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.MaximalDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardCycles
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardModuleCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceUnramifiedPairSplitting
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingGenericPointField
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFlatBaseChangeQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackGeometricLength
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# The degree count of Stacks 0EPD at the generic points

In Situation 0EDT let

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

be a cartesian square of good algebraic spaces over `B`, with `f` proper and `g` flat of relative
dimension `r`.  The third assertion of **Stacks 0EPD**, the identity
`g^* f_* α = f'_* (g')^* α` in `Z_{k+r}(Y')`, is an identity of two locally finite sums of prime
cycles whose coefficients at an integral closed subspace `T' ⊆ Y'` are, for an integral closed
subspace `Z ⊆ X` with `f`-image closure `Z'`, the two sides of the degree count at the generic
points:

`deg(Z/Z') · m_{T'}(g^{-1}(Z')) = ∑_{T ⊆ X'} m_T((g')^{-1}(Z)) · deg(T/T')`.

**This file proves that count**, which is what makes the third assertion unconditional in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange`, where the passage from a prime
cycle to an arbitrary cycle is carried out.  The proof is the source's: write `[Z] = [𝒪_Z]_k`
(Stacks 0EED), push forward and pull back the cycle of a module (part (1) of Stacks 0EP3 on both
sides) and compare the two modules by flat base change in degree zero, part (1) of Stacks 073K.

## How the two sides are computed

Write `ζ'` for the generic point of `Z'` and `t'` for the generic point of `T'`.  Both sides are
zero unless `g(t')` lies in `|Z'|` and `dim_δ(T') = dim_δ(Z) + r`, and under those two conditions
`dim_δ(Z') = dim_δ(Z)` and `g(t') = ζ'`, by Stacks 0EE6.  There:

* the *left* side is `deg(Z/Z')` times the multiplicity of `T'` in `g^{-1}(Z')`, and that
  multiplicity is the length of the fibre ring `𝒪_{Y', t'}/𝔪_{ζ'}𝒪_{Y', t'}`, by
  `AlgebraicGeometry.Space.flatPullbackMult_eq_toNat_length`, which is Stacks 02M1 at the flat
  local homomorphism `𝒪_{Y, ζ'} → 𝒪_{Y', t'}`;
* the *right* side is the length at `t'` of the direct image `(f' ∘ j)_*𝒪_{(g')^{-1}(Z)}`, by
  part (1) of Stacks 0EP3 for `f'`.  That module is `g^*((f ∘ i)_*𝒪_Z)`, by flat base change
  in degree zero for the cartesian square cut out by `Z`, so its length at `t'` is the length of
  `(f ∘ i)_*𝒪_Z` at `ζ'` times the length of the same fibre ring, by Stacks 02M1 again.  The
  first factor is `deg(Z/Z')`, by part (1) of Stacks 0EP3 for `f` evaluated at `Z'`, the
  fundamental cycle of `Z` being the indicator of `Z`.

## Main results

All in the namespace `AlgebraicGeometry.Space.BaseChangeDegreeCount`:

* `closedSubspaceCycle_integral_apply_self` and `closedSubspaceCycle_integral_apply_of_ne`: the
  fundamental cycle of Stacks 0EE9 of an integral closed subspace is its indicator.
* `isPullback_closedSubspacePreimage`: the cartesian square cut out of the given square by a
  closed subspace of `X`.
* `nonempty_modulePullbackIso_closedSubspaceDirectImageStructureSheaf`: flat base change in
  degree zero for the direct image of the structure sheaf of that closed subspace.
* `properCycleDegree_mul_flatPullbackMult_eq_finsum_of_isProper`: the degree count of
  Stacks 0EPD.

`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChangeUnconditional` keeps each of these
under its short name as an alias.

## Implementation notes

**Why this file sits above
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange`.**  The count is the one input
the general-cycle identity of that file needs, so it has to be provable before it: the form of
that identity carrying the tag,
`AlgebraicGeometry.Space.flatPullback_properPushforward_of_isPullback`, supplies the count rather
than assuming it.  Two one-line facts of that file are therefore reproved inline here
rather than imported — that the base change of a proper morphism is proper (Stacks 04WP, by
`AlgebraicGeometry.Space.isProper_isStableUnderBaseChange`) and that the multiplicity of the image
closure of `Z` in `f_*[Z]` is the degree of Stacks 0EP1 at `Z` (the branch of
`AlgebraicGeometry.Space.properCycleMult` that is not cut to zero).

**Why the identity is a statement about lengths and not about cycles.**  The step
`g^*[F]_k = [g^*F]_{k+r}` of part (2) of Stacks 0EPB is available only for a coherent `F`, and
coherence of `(f ∘ i)_*𝒪_Z` along a proper morphism of algebraic spaces is Stacks 08AR, which
this repository has only for a *representable* proper morphism
(`AlgebraicGeometry.Space.isCoherent_modulePushforward_of_isProper`).  The identity is therefore
proved at the single pair of generic points it is needed at, where the collapse of the two sums
comes from the cycle structure — the pushforward of a prime cycle is concentrated at the image
closure, by `AlgebraicGeometry.Space.finsum_properCycleMult_mul_flatPullbackMult` — rather than
from the support of a coherent module, and the pointwise length identity
`AlgebraicGeometry.Space.geometricLength_mul_length_quotient_extendedMaximalIdeal` is used
directly; it asks nothing of the module.

## References

* [Stacks Project, Tag 0EPD](https://stacks.math.columbia.edu/tag/0EPD)
* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1)
* [Stacks Project, Tag 04WP](https://stacks.math.columbia.edu/tag/04WP)
* [Stacks Project, Tag 04XY](https://stacks.math.columbia.edu/tag/04XY)
* [Stacks Project, Tag 04XZ](https://stacks.math.columbia.edu/tag/04XZ)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EE6](https://stacks.math.columbia.edu/tag/0EE6)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0EED](https://stacks.math.columbia.edu/tag/0EED)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 0EP3](https://stacks.math.columbia.edu/tag/0EP3)
* [Stacks Project, Tag 0EP6](https://stacks.math.columbia.edu/tag/0EP6)
* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 0EPB](https://stacks.math.columbia.edu/tag/0EPB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.BaseChangeDegreeCount

attribute [local instance] pointTopology

section Indicator

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX)

include hX in
/-- A point of `|Z|` at which the induced dimension function attains `dim_δ(Z)` is the generic
point of `Z`. -/
theorem eq_ambientGenericPoint_of_mem_of_inducedDimensionValue_eq
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (x : points D.site D.base D.base_mem X)
    (hmem : x ∈ subspacePointSet D.site D.base D.base_mem X Z.subspace)
    (hval : inducedDimensionValue D.site D.base D.base_mem D.delta sX x =
      deltaDimension D sX Z) :
    x = Z.ambientGenericPoint D.site D.base D.base_mem := by
  by_contra hne
  have hspec : Z.ambientGenericPoint D.site D.base D.base_mem ⤳ x := by
    rw [specializes_iff_mem_closure,
      Z.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hX.1]
    exact hmem
  have hlt := lt_inducedDimensionValue_of_specializes D.site D.base D.base_mem hX.1
    (D.isDecentSpace_of_isGood sX hX) D.isAlgebraicSpace
    (isDecentSpace_of_isAbsolutelyQuasiSeparated D.site D.base D.base_mem D.space
      D.isAlgebraicSpace D.quasiSeparated)
    D.locallyNoetherian D.universallyCatenary D.delta sX hX.2.2 hspec (Ne.symm hne)
  have e2 : inducedDimensionValue D.site D.base D.base_mem D.delta sX
      (Z.ambientGenericPoint D.site D.base D.base_mem) = deltaDimension D sX Z := rfl
  rw [hval, e2] at hlt
  omega

include hX in
/-- An integral closed subspace whose generic point lies in `|Z|` and whose δ-dimension equals
that of `Z` is `Z` itself. -/
theorem eq_of_mem_of_deltaDimension_eq
    (Z W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hmem : W.ambientGenericPoint D.site D.base D.base_mem ∈
      subspacePointSet D.site D.base D.base_mem X Z.subspace)
    (hdim : deltaDimension D sX W = deltaDimension D sX Z) : W = Z := by
  have hdec := D.isDecentSpace_of_isGood sX hX
  have hgenZ := Z.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hX.1
  have hgenW := W.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hX.1
  have hpt := eq_ambientGenericPoint_of_mem_of_inducedDimensionValue_eq D sX hX Z
    (W.ambientGenericPoint D.site D.base D.base_mem) hmem hdim
  exact (eq_integralClosedSubspaceOfPoint D.site D.base D.base_mem hX.1 hdec
      (Z.ambientGenericPoint D.site D.base D.base_mem) W (by rw [← hpt]; exact hgenW)).trans
    (eq_integralClosedSubspaceOfPoint D.site D.base D.base_mem hX.1 hdec
      (Z.ambientGenericPoint D.site D.base D.base_mem) Z hgenZ).symm

include hX in
/-- **The coefficient of an integral closed subspace in its own fundamental cycle is one.** -/
theorem closedSubspaceCycle_integral_apply_self
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hdimZ : deltaDimensionSubspace D sX hX Z.subspace Z.isClosedSubspace ≤
      ((deltaDimension D sX Z : ℤ) : EInt)) :
    (closedSubspaceCycle D sX hX Z.subspace Z.isClosedSubspace (deltaDimension D sX Z)
        hdimZ).1 Z = 1 := by
  have hmemZ : Z.ambientGenericPoint D.site D.base D.base_mem ∈
      subspacePointSet D.site D.base D.base_mem X Z.subspace := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ := exists_closedSubspaceComponentImage_eq_of_mem D sX hX Z.subspace
    Z.isClosedSubspace Z hmemZ
  have hVgen : V.ambientGenericPoint D.site D.base D.base_mem =
      Z.genericPoint D.site D.base D.base_mem := by
    refine pointsMap_ι_injective D hX.1 Z.subspace Z.isClosedSubspace ?_
    have e := ambientGenericPoint_closedSubspaceComponentImage D sX hX Z.subspace
      Z.isClosedSubspace V
    rw [hV] at e
    exact e.symm
  have hcoeff := cycleCoeffOfClosedSubspace_eq_closedSubspaceMultiplicity D sX hX Z.subspace
    Z.isClosedSubspace (deltaDimension D sX Z)
    (canonicalGeometricPoint D.site D.base D.base_mem Z.subspace.toFunctor) V
    (canonicalGeometricPoint_image D.site D.base D.base_mem Z.subspace.toFunctor _)
    (by rw [hV])
  rw [hV] at hcoeff
  rw [closedSubspaceCycle_coe, hcoeff,
    closedSubspaceMultiplicity_eq_toNat_geometricLength D Z.subspace Z.isClosedSubspace V
      (canonicalGeometricPoint D.site D.base D.base_mem Z.subspace.toFunctor
        (V.ambientGenericPoint D.site D.base D.base_mem))
      (canonicalGeometricPoint_image D.site D.base D.base_mem Z.subspace.toFunctor _),
    geometricLength_structureSheafModule_eq_one_of_isIntegralSpace D.site D.base D.base_mem
      ⟨Z.subspace.toFunctor, Z.isClosedSubspace.1⟩ Z.isIntegralSpace _
      (by rw [canonicalGeometricPoint_image, hVgen]; exact Z.genericPoint_mem_genericPoints D)]
  rfl

include hX in
/-- **The fundamental cycle of an integral closed subspace vanishes off that subspace.** -/
theorem closedSubspaceCycle_integral_apply_of_ne
    (Z W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hdimZ : deltaDimensionSubspace D sX hX Z.subspace Z.isClosedSubspace ≤
      ((deltaDimension D sX Z : ℤ) : EInt)) (hne : W ≠ Z) :
    (closedSubspaceCycle D sX hX Z.subspace Z.isClosedSubspace (deltaDimension D sX Z)
        hdimZ).1 W = 0 := by
  classical
  rw [closedSubspaceCycle_coe]
  by_cases hdimW : deltaDimension D sX W = deltaDimension D sX Z
  · refine cycleCoeffOfClosedSubspace_eq_zero D sX hX Z.subspace Z.isClosedSubspace
      (deltaDimension D sX Z)
      (canonicalGeometricPoint D.site D.base D.base_mem Z.subspace.toFunctor) W fun V hV => ?_
    refine hne (eq_of_mem_of_deltaDimension_eq D sX hX Z W ?_ hdimW)
    rw [← hV, ambientGenericPoint_closedSubspaceComponentImage]
    exact ⟨_, rfl⟩
  · rw [cycleCoeffOfClosedSubspace, ite_eq_right hdimW]

end Indicator

section Comparison

variable (D : BaseSpaceDimensionSituation.{u})
    {X' X Y' Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX' : X' ⟶ D.space) (hX' : D.IsGood sX') (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY' : Y' ⟶ D.space) (hY' : D.IsGood sY') (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (hg'base : g' ≫ sX = sX') (hf'base : f' ≫ sY' = sX') (hfbase : f ≫ sY = sX)
    (hgbase : g ≫ sY = sY') (r : ℕ)
    (hgflat : IsFlat D.site D.base D.base_mem g)
    (hgr : HasRelativeDimension r D.site D.base D.base_mem g)
    (hg'flat : IsFlat D.site D.base D.base_mem g')
    (hg'r : HasRelativeDimension r D.site D.base D.base_mem g')

/-- **The square cut out of a cartesian square by a closed subspace of `X`.**  For a cartesian
square with `g' : X' ⟶ X` and `f' : X' ⟶ Y'` over `f : X ⟶ Y` and `g : Y' ⟶ Y`, and for a closed
subspace `Z ⊆ X`, the square

```
(g')^{-1}(Z) ----> Z
     |             |
     v             v
    Y' ----g----> Y
```

whose vertical arrows are the composites with the two closed immersions is again cartesian: it is
the vertical pasting of the cartesian square of Stacks 083Q for `Z` and `g'` with the given
square. -/
theorem isPullback_closedSubspacePreimage (sq : IsPullback g' f' f g)
    (Zs : Subfunctor X) (hZs : IsClosedSubspace D.site D.base D.base_mem Zs) :
    IsPullback
      (ObjectProperty.homMk (Zs.fromPreimage g') :
        (⟨(Zs.preimage g').toFunctor,
            (isClosedSubspace_preimage D.site D.base D.base_mem g' Zs hX.1 hX'.1 hZs).1⟩ :
          AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Zs.toFunctor, hZs.1⟩)
      (closedSubspaceHom D.site D.base D.base_mem hX'.1 (Zs.preimage g')
          (isClosedSubspace_preimage D.site D.base D.base_mem g' Zs hX.1 hX'.1 hZs) ≫
        (ObjectProperty.homMk f' :
          (⟨X', hX'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y', hY'.1⟩))
      (closedSubspaceHom D.site D.base D.base_mem hX.1 Zs hZs ≫
        (ObjectProperty.homMk f :
          (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY.1⟩))
      (ObjectProperty.homMk g :
        (⟨Y', hY'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY.1⟩) :=
  IsPullback.paste_vert
    (isPullback_homMk D.site D.base D.base_mem hZs.1 hX'.1 hX.1
      (isClosedSubspace_preimage D.site D.base D.base_mem g' Zs hX.1 hX'.1 hZs).1
      (Subfunctor.isPullback_preimage g' Zs))
    (isPullback_homMk D.site D.base D.base_mem hX.1 hY'.1 hY.1 hX'.1 sq)

/-- The composite `Z → X → Y` of the inclusion of a closed subspace and a proper morphism is
proper: a closed immersion is proper by Stacks 04XZ, and properness is stable under composition
by Stacks 04XY. -/
theorem isProper_closedSubspaceHom_comp (hfproper : IsProper D.site D.base D.base_mem f)
    (Zs : Subfunctor X) (hZs : IsClosedSubspace D.site D.base D.base_mem Zs) :
    IsProper D.site D.base D.base_mem
      (closedSubspaceHom D.site D.base D.base_mem hX.1 Zs hZs ≫
        (ObjectProperty.homMk f :
          (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY.1⟩)).hom :=
  isProper_comp' D.site D.base D.base_mem Zs.ι f hX.1 hY.1
    (isProper_of_isClosedImmersion D.site D.base D.base_mem hZs.1 hX.1 _
      (isClosedImmersion_closedSubspaceHom D.site D.base D.base_mem hX.1 Zs hZs))
    hfproper

/-- The direct image of the structure sheaf of a closed subspace along a proper morphism is
quasi-coherent. -/
private theorem isQuasicoherentOnSite_closedSubspaceDirectImageStructureSheaf
    (hfproper : IsProper D.site D.base D.base_mem f)
    (Zs : Subfunctor X) (hZs : IsClosedSubspace D.site D.base D.base_mem Zs) :
    (closedSubspaceDirectImageStructureSheaf D sX hX sY hY f Zs hZs).IsQuasicoherentOnSite := by
  have hb := isProper_closedSubspaceHom_comp D sX hX sY hY hfproper Zs hZs
  exact isQuasicoherentOnSite_modulePushforward_of_qcqs D.site D.base D.base_mem _ hb.2.1.2
    (isQuasiSeparated_of_isSeparated D.site D.base D.base_mem hb.1) _
    (SheafOfModules.isQuasicoherentOnSite_unit _)

/-- **Flat base change in degree zero for the direct image of the structure sheaf of a closed
subspace.**  For a closed subspace `Z ⊆ X` of a cartesian square as above with `g` flat and `f`
proper, the module `g^*((f ∘ i)_*𝒪_Z)` on `Y'` is isomorphic to `(f' ∘ j)_*𝒪_{(g')^{-1}(Z)}`,
where `i` and `j` are the two closed immersions.

This is part (1) of Stacks 073K in degree zero,
`AlgebraicGeometry.Space.isIso_moduleBaseChangeMap_app_of_isFlat`, applied to the cartesian
square `AlgebraicGeometry.Space.isPullback_closedSubspacePreimage` cut out by `Z`, whose
right-hand leg `Z → X → Y` is proper hence quasi-compact and quasi-separated, together with the
identification of the inverse image of the structure sheaf with the structure sheaf,
`AlgebraicGeometry.Space.modulePullbackUnitIso`. -/
theorem nonempty_modulePullbackIso_closedSubspaceDirectImageStructureSheaf
    (sq : IsPullback g' f' f g) (hgflat : IsFlat D.site D.base D.base_mem g)
    (hfproper : IsProper D.site D.base D.base_mem f)
    (Zs : Subfunctor X) (hZs : IsClosedSubspace D.site D.base D.base_mem Zs) :
    Nonempty ((modulePullback D.site D.base D.base_mem
          (ObjectProperty.homMk g :
            (⟨Y', hY'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY.1⟩)).obj
        (closedSubspaceDirectImageStructureSheaf D sX hX sY hY f Zs hZs) ≅
      closedSubspaceDirectImageStructureSheaf D sX' hX' sY' hY' f' (Zs.preimage g')
        (isClosedSubspace_preimage D.site D.base D.base_mem g' Zs hX.1 hX'.1 hZs)) := by
  have hsq := isPullback_closedSubspacePreimage D sX' hX' sX hX sY' hY' sY hY sq Zs hZs
  have hiso := isIso_moduleBaseChangeMap_app_of_isFlat hsq
    (isProper_closedSubspaceHom_comp D sX hX sY hY hfproper Zs hZs).2.1.2
    (isQuasiSeparated_of_isSeparated D.site D.base D.base_mem
      (isProper_closedSubspaceHom_comp D sX hX sY hY hfproper Zs hZs).1)
    hgflat (SheafOfModules.unit _) (SheafOfModules.isQuasicoherentOnSite_unit _)
  have e1 := @asIso _ _ _ _ _ hiso
  have e2 := (modulePushforward D.site D.base D.base_mem
      (closedSubspaceHom D.site D.base D.base_mem hX'.1 (Zs.preimage g')
          (isClosedSubspace_preimage D.site D.base D.base_mem g' Zs hX.1 hX'.1 hZs) ≫
        (ObjectProperty.homMk f' :
          (⟨X', hX'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y', hY'.1⟩))).mapIso
    (modulePullbackUnitIso D.site D.base D.base_mem
      (ObjectProperty.homMk (Zs.fromPreimage g') :
        (⟨(Zs.preimage g').toFunctor,
            (isClosedSubspace_preimage D.site D.base D.base_mem g' Zs hX.1 hX'.1 hZs).1⟩ :
          AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Zs.toFunctor, hZs.1⟩))
  exact ⟨e1 ≪≫ e2⟩

include hg'base hf'base hfbase hgbase in
/-- **The degree count of Stacks 0EPD at the generic points.**  In Situation 0EDT, for a
cartesian square of good algebraic spaces over `B` with `f : X ⟶ Y` proper and `g : Y' ⟶ Y` flat
of relative dimension `r`, for an integral closed subspace `Z ⊆ X` with `f`-image closure `Z'`,
and for an integral closed subspace `T' ⊆ Y'`,

`deg(Z/Z') · m_{T'}(g^{-1}(Z')) = ∑_{T ⊆ X'} m_T((g')^{-1}(Z)) · deg(T/T')`.

Both sides are read as lengths at the generic point `t'` of `T'`.  If `g(t')` is not a point of
`|Z'|` both sides vanish, by Stacks 0EP6 on the left and by
the closure-image containment on the right.  Otherwise the
δ-dimension bounds force `dim_δ(T') = dim_δ(Z') + r = dim_δ(Z) + r` whenever either side is
nonzero, and Stacks 0EE6 (`AlgebraicGeometry.Space.exists_isGenericPoint_image`) then puts `g(t')`
at the generic point of `Z'`.  There the right-hand side is the length of
`(f' ∘ j)_*𝒪_{(g')^{-1}(Z)}` at `t'` by part (1) of Stacks 0EP3, hence the length of
`g^*((f ∘ i)_*𝒪_Z)` by flat base change in degree zero (part (1) of Stacks 073K), which by
Stacks 02M1 (`AlgebraicGeometry.Space.geometricLength_mul_length_quotient_extendedMaximalIdeal`)
is the product of the length of `(f ∘ i)_*𝒪_Z` at the generic point of `Z'` — which is
`deg(Z/Z')`, again by part (1) of Stacks 0EP3 — with the length of the fibre ring of `g` at `t'`.
The left-hand side is the same product, by Stacks 0EE9 and
`AlgebraicGeometry.Space.flatPullbackMult_eq_toNat_length`. -/
theorem properCycleDegree_mul_flatPullbackMult_eq_finsum_of_isProper (sq : IsPullback g' f' f g)
    (hfproper : IsProper D.site D.base D.base_mem f)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (T' : IntegralClosedSubspace D.site D.base D.base_mem Y') :
    properCycleDegree D sX hX sY hY f Z *
        flatPullbackMult D sY' hY' sY hY g hgbase r hgflat hgr
          (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
            (D.isDecentSpace_of_isGood sY hY) f Z) T' =
      ∑ᶠ T : IntegralClosedSubspace D.site D.base D.base_mem X',
        flatPullbackMult D sX' hX' sX hX g' hg'base r hg'flat hg'r Z T *
          properCycleMult D sX' hX' sY' hY' f' T T' := by
  classical
  -- the multiplicity of the image closure of a subspace in its pushforward is its degree: it is
  -- the branch of `AlgebraicGeometry.Space.properCycleMult` that is not cut to zero
  have hmultClosureImage : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      properCycleMult D sX hX sY hY f W
          (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
            (D.isDecentSpace_of_isGood sY hY) f W) =
        properCycleDegree D sX hX sY hY f W := by
    intro W
    unfold properCycleMult
    split_ifs with h
    · rfl
    · exact absurd rfl h
  -- a subspace of `X'` occurring in `(g')^*[Z]` with image closure `T'` puts the generic point
  -- of `T'` over the closure of the image of `Z`: the square commutes on points
  have hclosure : ∀ T : IntegralClosedSubspace D.site D.base D.base_mem X',
      flatPullbackMult D sX' hX' sX hX g' hg'base r hg'flat hg'r Z T ≠ 0 →
      IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY'.1
          (D.isDecentSpace_of_isGood sY' hY') f' T = T' →
      pointsMap D.site D.base D.base_mem Y' g
          (T'.ambientGenericPoint D.site D.base D.base_mem) ∈
        subspacePointSet D.site D.base D.base_mem Y
          (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
            (D.isDecentSpace_of_isGood sY hY) f Z).subspace := by
    intro T hm hT
    have hsub := subspacePointSet_subset_of_flatPullbackMult_ne_zero D sX' hX' sX hX g' hg'base r
      hg'flat hg'r Z T hm
    have hclosed : IsClosed (subspacePointSet D.site D.base D.base_mem Y
        (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
          (D.isDecentSpace_of_isGood sY hY) f Z).subspace) :=
      isClosed_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem hY.1 _
    have hcomm : pointsMap D.site D.base D.base_mem Y' g ∘
        pointsMap D.site D.base D.base_mem X' f' =
        pointsMap D.site D.base D.base_mem X f ∘ pointsMap D.site D.base D.base_mem X' g' := by
      rw [← pointsMap_comp D.site D.base D.base_mem X' f' g,
        ← pointsMap_comp D.site D.base D.base_mem X' g' f, sq.w]
    have himg : pointsMap D.site D.base D.base_mem X' f' ''
        subspacePointSet D.site D.base D.base_mem X' T.subspace ⊆
        pointsMap D.site D.base D.base_mem Y' g ⁻¹'
          subspacePointSet D.site D.base D.base_mem Y
            (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
              (D.isDecentSpace_of_isGood sY hY) f Z).subspace := by
      rintro y ⟨x', hx', rfl⟩
      have hval : pointsMap D.site D.base D.base_mem Y' g
          (pointsMap D.site D.base D.base_mem X' f' x') =
          pointsMap D.site D.base D.base_mem X f
            (pointsMap D.site D.base D.base_mem X' g' x') := congrFun hcomm x'
      rw [Set.mem_preimage, hval,
        IntegralClosedSubspace.subspacePointSet_closureImage D.site D.base D.base_mem hY.1
          (D.isDecentSpace_of_isGood sY hY) f Z]
      exact subset_closure ⟨_, hsub hx', rfl⟩
    have hgen := T'.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hY'.1
    have hmemT' : T'.ambientGenericPoint D.site D.base D.base_mem ∈
        closure (pointsMap D.site D.base D.base_mem X' f' ''
          subspacePointSet D.site D.base D.base_mem X' T.subspace) := by
      rw [← IntegralClosedSubspace.subspacePointSet_closureImage D.site D.base D.base_mem hY'.1
        (D.isDecentSpace_of_isGood sY' hY') f' T, hT, ← hgen]
      exact subset_closure rfl
    exact closure_minimal himg
      (hclosed.preimage (continuous_pointsMap D.site D.base D.base_mem g)) hmemT'
  have hYdec := D.isDecentSpace_of_isGood sY hY
  have hf'proper : IsProper D.site D.base D.base_mem f' :=
    (isProper_isStableUnderBaseChange D.site D.base D.base_mem).of_isPullback
      (isPullback_homMk D.site D.base D.base_mem hX.1 hY'.1 hY.1 hX'.1 sq) hfproper
  set Z' := IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1 hYdec f Z with hZ'def
  set t' := T'.ambientGenericPoint D.site D.base D.base_mem with ht'def
  by_cases hmem : pointsMap D.site D.base D.base_mem Y' g t' ∈
      subspacePointSet D.site D.base D.base_mem Y Z'.subspace
  case neg =>
    have hL : flatPullbackMult D sY' hY' sY hY g hgbase r hgflat hgr Z' T' = 0 := by
      by_contra hc
      exact hmem (mem_subspacePointSet_of_flatPullbackMult_ne_zero D sY' hY' sY hY g hgbase r
        hgflat hgr Z' T' hc)
    rw [hL, mul_zero]
    refine (finsum_eq_zero_of_forall_eq_zero fun T => ?_).symm
    by_contra hc
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hc
    exact hmem (hclosure T h1
      ((properCycleMult_ne_zero_iff D sX' hX' sY' hY' f' T T').1 h2).1)
  -- the main case: the generic point of `T'` lies over `|Z'|`
  have hPre := isClosedSubspace_preimage_integralClosedSubspace D sY' hY' sY hY g Z'
  have hmemT' : t' ∈ subspacePointSet D.site D.base D.base_mem Y' (Z'.subspace.preimage g) := by
    rw [subspacePointSet_preimage]
    exact hmem
  have hbound := deltaDimensionSubspace_preimage_le D sY' hY' sY hY g hgbase r hgflat hgr
    (deltaDimension D sY Z') Z'.subspace Z'.isClosedSubspace
    (deltaDimensionSubspace_integralClosedSubspace D sY hY Z').le
  have hle : deltaDimension D sY' T' ≤ deltaDimension D sY Z' + (r : ℤ) :=
    (deltaDimensionClosed_le_coe_iff D sY' hY' _ _ _).1 hbound t' hmemT'
  have hle2 : deltaDimension D sY Z' ≤ deltaDimension D sX Z :=
    IntegralClosedSubspace.deltaDimension_closureImage_le D sX sY hX hY f hfbase Z
  by_cases hT'dim : deltaDimension D sY' T' = deltaDimension D sX Z + (r : ℤ)
  case neg =>
    have hL : properCycleDegree D sX hX sY hY f Z *
        flatPullbackMult D sY' hY' sY hY g hgbase r hgflat hgr Z' T' = 0 := by
      by_contra hc
      obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hc
      refine hT'dim ?_
      rw [deltaDimension_eq_of_flatPullbackMult_ne_zero D sY' hY' sY hY g hgbase r hgflat hgr
        Z' T' h2, deltaDimension_closureImage_of_properCycleDegree_ne_zero D sX hX sY hY f h1]
    rw [hL]
    refine (finsum_eq_zero_of_forall_eq_zero fun T => ?_).symm
    by_contra hc
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hc
    obtain ⟨hTim, hTdeg⟩ := (properCycleMult_ne_zero_iff D sX' hX' sY' hY' f' T T').1 h2
    refine hT'dim ?_
    rw [← hTim, deltaDimension_closureImage_of_properCycleDegree_ne_zero D sX' hX' sY' hY' f'
      hTdeg, deltaDimension_eq_of_flatPullbackMult_ne_zero D sX' hX' sX hX g' hg'base r hg'flat
      hg'r Z T h1]
  -- the δ-dimension of the image closure does not drop
  have hZ'dim : deltaDimension D sY Z' = deltaDimension D sX Z := by omega
  -- the generic point of `T'` lies over the generic point of `Z'`
  have hηval := (exists_isGenericPoint_image D sY' hY' sY hY g hgbase r hgr
    (deltaDimension D sY Z') (subspacePointSet D.site D.base D.base_mem Y Z'.subspace)
    (isClosed_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem hY.1 Z')
    (deltaDimensionSubspace_integralClosedSubspace D sY hY Z').le T'
    (by rw [hT'dim, hZ'dim]) hmem).1
  have hη : pointsMap D.site D.base D.base_mem Y' g t' =
      Z'.ambientGenericPoint D.site D.base D.base_mem :=
    eq_ambientGenericPoint_of_mem_of_inducedDimensionValue_eq D sY hY Z' _ hmem hηval
  -- a geometric point of `Y'` over the generic point of `T'`, taken inside `g^{-1}(Z')`
  obtain ⟨V, hV⟩ := exists_closedSubspaceComponentImage_eq_of_mem D sY' hY'
    (Z'.subspace.preimage g) hPre T' hmemT'
  have hVimg := ambientGenericPoint_closedSubspaceComponentImage D sY' hY'
    (Z'.subspace.preimage g) hPre V
  rw [hV] at hVimg
  set z := canonicalGeometricPoint D.site D.base D.base_mem (Z'.subspace.preimage g).toFunctor
    (V.ambientGenericPoint D.site D.base D.base_mem) with hzdef
  have hximg : (geometricPointMap (Z'.subspace.preimage g).ι z).image = t' := by
    rw [geometricPointMap_image, hzdef, canonicalGeometricPoint_image]
    exact hVimg.symm
  have hLmult := flatPullbackMult_eq_toNat_length D sY' hY' sY hY g hgbase r hgflat hgr Z' V
    (by rw [hV, hT'dim, hZ'dim]) z
    (canonicalGeometricPoint_image D.site D.base D.base_mem (Z'.subspace.preimage g).toFunctor _)
    (by rw [← hVimg]; exact hη)
  rw [hV] at hLmult
  -- the two modules
  have hMqc := isQuasicoherentOnSite_closedSubspaceDirectImageStructureSheaf D sX hX sY hY
    hfproper Z.subspace Z.isClosedSubspace
  have hM'qc := isQuasicoherentOnSite_closedSubspaceDirectImageStructureSheaf D sX' hX' sY' hY'
    hf'proper (Z.subspace.preimage g')
    (isClosedSubspace_preimage D.site D.base D.base_mem g' Z.subspace hX.1 hX'.1
      Z.isClosedSubspace)
  have hdimZ := (deltaDimensionSubspace_integralClosedSubspace D sX hX Z).le
  have hRHS := congrFun (properCyclePushforwardCoeff_closedSubspaceCycle_eq D sX' hX' sY' hY'
    hf'base hf'proper (Z.subspace.preimage g')
    (isClosedSubspace_preimage D.site D.base D.base_mem g' Z.subspace hX.1 hX'.1
      Z.isClosedSubspace) (deltaDimension D sX Z + (r : ℤ))
    (deltaDimensionSubspace_preimage_le D sX' hX' sX hX g' hg'base r hg'flat hg'r
      (deltaDimension D sX Z) Z.subspace Z.isClosedSubspace hdimZ)
    (canonicalGeometricPoint D.site D.base D.base_mem Y')
    (canonicalGeometricPoint_image D.site D.base D.base_mem Y')) T'
  rw [cycleCoeffOfModule_eq_moduleMultiplicity, ite_eq_left hT'dim, moduleMultiplicity] at hRHS
  -- the degree is the length of the direct image at the generic point of `Z'`
  have hdeg : properCycleDegree D sX hX sY hY f Z =
      ((geometricLength D.site D.base D.base_mem ⟨Y, hY.1⟩
        (geometricPointMap g (geometricPointMap (Z'.subspace.preimage g).ι z))
        (closedSubspaceDirectImageStructureSheaf D sX hX sY hY f Z.subspace
          Z.isClosedSubspace)).toNat : ℤ) := by
    have h := congrFun (properCyclePushforwardCoeff_closedSubspaceCycle_eq D sX hX sY hY hfbase
      hfproper Z.subspace Z.isClosedSubspace (deltaDimension D sX Z) hdimZ
      (canonicalGeometricPoint D.site D.base D.base_mem Y)
      (canonicalGeometricPoint_image D.site D.base D.base_mem Y)) Z'
    rw [cycleCoeffOfModule_eq_moduleMultiplicity, ite_eq_left hZ'dim, moduleMultiplicity,
      geometricLength_eq_of_image_eq D.site D.base D.base_mem hY.1
        (canonicalGeometricPoint D.site D.base D.base_mem Y
          (Z'.ambientGenericPoint D.site D.base D.base_mem))
        (geometricPointMap g (geometricPointMap (Z'.subspace.preimage g).ι z))
        (by rw [canonicalGeometricPoint_image, geometricPointMap_image, hximg]; exact hη.symm)
        _] at h
    rw [← h, show properCyclePushforwardCoeff D sX hX sY hY f
          (closedSubspaceCycle D sX hX Z.subspace Z.isClosedSubspace
            (deltaDimension D sX Z) hdimZ).1 Z' =
        ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem X,
          (closedSubspaceCycle D sX hX Z.subspace Z.isClosedSubspace
            (deltaDimension D sX Z) hdimZ).1 W * properCycleMult D sX hX sY hY f W Z' from rfl,
      finsum_eq_single _ Z fun W hW => by
        rw [closedSubspaceCycle_integral_apply_of_ne D sX hX Z W hdimZ hW, zero_mul],
      closedSubspaceCycle_integral_apply_self D sX hX Z hdimZ, one_mul]
    exact (hmultClosureImage Z).symm
  -- the flat base change comparison of the two direct images
  have hpull := geometricLength_mul_length_quotient_extendedMaximalIdeal D.site D.base D.base_mem
    (ObjectProperty.homMk g : (⟨Y', hY'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
      ⟨Y, hY.1⟩) hgflat (geometricPointMap (Z'.subspace.preimage g).ι z)
    (closedSubspaceDirectImageStructureSheaf D sX hX sY hY f Z.subspace Z.isClosedSubspace)
  rw [show (∑ᶠ T : IntegralClosedSubspace D.site D.base D.base_mem X',
        flatPullbackMult D sX' hX' sX hX g' hg'base r hg'flat hg'r Z T *
          properCycleMult D sX' hX' sY' hY' f' T T') =
      properCyclePushforwardCoeff D sX' hX' sY' hY' f'
        (closedSubspaceCycle D sX' hX' (Z.subspace.preimage g')
          (isClosedSubspace_preimage D.site D.base D.base_mem g' Z.subspace hX.1 hX'.1
            Z.isClosedSubspace) (deltaDimension D sX Z + (r : ℤ))
          (deltaDimensionSubspace_preimage_le D sX' hX' sX hX g' hg'base r hg'flat hg'r
            (deltaDimension D sX Z) Z.subspace Z.isClosedSubspace hdimZ)).1 T' from rfl,
    hRHS, hLmult, hdeg,
    geometricLength_eq_of_image_eq D.site D.base D.base_mem hY'.1
      (canonicalGeometricPoint D.site D.base D.base_mem Y'
        (T'.ambientGenericPoint D.site D.base D.base_mem))
      (geometricPointMap (Z'.subspace.preimage g).ι z)
      ((canonicalGeometricPoint_image D.site D.base D.base_mem Y' _).trans hximg.symm) _,
    geometricLength_eq_of_iso D.site D.base D.base_mem ⟨Y', hY'.1⟩ _
      (nonempty_modulePullbackIso_closedSubspaceDirectImageStructureSheaf D sX' hX' sX hX sY'
        hY' sY hY sq hgflat hfproper Z.subspace Z.isClosedSubspace).some.symm,
    ← hpull, ENat.toNat_mul, Nat.cast_mul]
  rfl

end Comparison

end AlgebraicGeometry.Space.BaseChangeDegreeCount

end
