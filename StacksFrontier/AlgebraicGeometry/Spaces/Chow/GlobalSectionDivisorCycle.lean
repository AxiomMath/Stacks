module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.DivisorOfSectionCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.WeilDivisorOfInvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceChartColength
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleLocalRingChartHenselization
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorGlobalSectionCoefficient
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroSchemeInvertibleIdeal

/-!
# The divisor of a nonzero global section is the cycle of its zero scheme

In Situation 0EDT let `X/B` be good, let `X` be integral with `n = dim_δ(X)`, let `ℒ` be an
invertible `𝒪_X`-module and let `s ∈ Γ(X, ℒ)` be a nonzero global section. **Stacks 0EQF**
asserts

`div_ℒ(s) = [Z(s)]_{n-1}` in `Z_{n-1}(X)`  and  `c₁(ℒ) ∩ [X] = [Z(s)]_{n-1}` in `CH_{n-1}(X)`.

Here `div_ℒ(s)` is the Weil divisor of Stacks 0EQE, part (1), of the meromorphic section of `ℒ`
that `s` is, `AlgebraicGeometry.Space.sectionWeilDivisor` at
`AlgebraicGeometry.Space.globalSectionMeromorphic`; `c₁(ℒ) ∩ [X]` is Stacks 0EQE, part (2),
`AlgebraicGeometry.Space.weilDivisorOfInvertibleSheaf`, in the Chow group of Stacks 0EQ6; and
`[Z(s)]_{n-1}` is the cycle of Stacks 0EE9 of the zero scheme `Z(s)` of Stacks 0845,
`AlgebraicGeometry.Space.zeroSchemeCycle`, its multiplicities read at the canonical geometric
representative of each point as everywhere `AlgebraicGeometry.Space.closedSubspaceCycle` is used.

## The proof

It is the source's. Fix a prime divisor `Z` with generic point `ξ`, let `(U, u)` be the chosen
affine elementary étale neighbourhood of `ξ` and `A = 𝒪_{U, u}`. By
`StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorGlobalSectionCoefficient`,
`ord_{Z,ℒ}(s) = length_A(A / aA)` for the germ `a` of `s` against the generator `s_ξ`, and `aA` is
the extension to `A` of the evaluation ideal of `s` over `U`, which is the defining ideal of
`Z(s)` over `U` (`AlgebraicGeometry.Space.definingIdealAt_zeroScheme_eq_of_isInvertible`). On
the other side the multiplicity of `Z` in `Z(s)` is the colength in `A` of that same ideal
(`AlgebraicGeometry.Space.geometricLength_unit_eq_length_quotient_definingIdealAt`), the
elementary étale neighbourhood being a neighbourhood of every geometric point over `ξ`. When `Z`
is not contained in `Z(s)` both sides vanish: `u` is then not in the zero locus of the defining
ideal (`AlgebraicGeometry.Space.range_rep_snd_eq_zeroLocus_definingIdealAt`), so that ideal
extends to the unit ideal of `A` and `a` is a unit.

Away from the prime divisors both coefficient families vanish, by Stacks 0EQE part (1) on one
side and by Stacks 0EPZ on the other. So the two coefficient families are *equal*, which in
particular makes the coefficients of `[Z(s)]_{n-1}` locally finite: `[Z(s)]_{n-1}` is an
`(n-1)`-cycle because `div_ℒ(s)` is one. The identity in `CH_{n-1}(X)` is the image of the one in
`Z_{n-1}(X)` under the class map, `c₁(ℒ) ∩ [X]` being the class of `div_ℒ(s)` for every nonzero
meromorphic section (`AlgebraicGeometry.Space.chowClass_sectionWeilDivisor`).

## Main results

* `zeroSchemeCycleCoeff_eq_invertibleDivisorCoefficients_globalSection`: the coefficient
  families of `div_ℒ(s)` and of `[Z(s)]_{n-1}` agree, for every choice of geometric
  representatives lying over the points they represent.
* `sectionWeilDivisor_eq_zeroSchemeCycle_and_weilDivisorOfInvertibleSheaf_eq`: both identities
  of Stacks 0EQF.

## References

* [Stacks Project, Tag 0EQF](https://stacks.math.columbia.edu/tag/0EQF)
* [Stacks Project, Tag 0845](https://stacks.math.columbia.edu/tag/0845)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPZ](https://stacks.math.columbia.edu/tag/0EPZ)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQE](https://stacks.math.columbia.edu/tag/0EQE)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1) (hL : IsInvertibleSheaf D sX hX L)

/-! ### Containment of a prime divisor in a closed subspace -/

/-- The generic point of the integral closed subspace of a prime divisor is its generic point. -/
private theorem ambientGenericPoint_toIntegralClosedSubspace_eq (hX : D.IsGood sX)
    [T0Space (points D.site D.base D.base_mem X)] (W : PrimeDivisor D.site D.base D.base_mem X) :
    (W.toIntegralClosedSubspace D.site D.base D.base_mem).ambientGenericPoint
      D.site D.base D.base_mem = W.genericPoint D.site D.base D.base_mem X :=
  ((W.toIntegralClosedSubspace D.site D.base D.base_mem).isGenericPoint_ambientGenericPoint
    D.site D.base D.base_mem hX.1).eq (W.isGenericPoint_genericPoint D.site D.base D.base_mem X)

/-- **A prime divisor whose chart point lies on a closed subspace is the image of an integral
closed subspace of it.** If the defining ideal of a closed subspace `Y` over the chosen affine
elementary étale neighbourhood `(U, u)` of the generic point `ξ` of a prime divisor `Z` does not
extend to the unit ideal of `𝒪_{U, u}`, then `u` lies in its zero locus, so `ξ` lies in `|Y|`,
hence so does its closure `|Z|`, and `Z` is the image of an integral closed subspace of `Y`. -/
theorem PrimeDivisor.exists_closedSubspaceComponentImage_of_map_ne_top
    (Y : ClosedSubspaces D.site D.base D.base_mem X) (Z : PrimeDivisor D.site D.base D.base_mem X)
    (hne : Ideal.map
        ((Z.genericChart D.site D.base D.base_mem hX.1 hint.2.1).scheme.left.1.presheaf.germ ⊤
          (Z.genericChart D.site D.base D.base_mem hX.1 hint.2.1).point trivial).hom
        (definingIdealAt D.site D.base D.base_mem ⟨X, hX.1⟩ Y
          (op (Z.genericEtaleChart D.site D.base D.base_mem hX.1 hint.2.1))) ≠ ⊤) :
    ∃ Zc : IntegralClosedSubspace D.site D.base D.base_mem Y.1.toFunctor,
      closedSubspaceComponentImage D sX hX Y.1 Y.2 Zc =
        Z.toIntegralClosedSubspace D.site D.base D.base_mem := by
  set U := Z.genericChart D.site D.base D.base_mem hX.1 hint.2.1 with hU
  have : IsAffine ((BigFppfOver.toScheme D.site D.base D.base_mem).obj
      (Z.genericEtaleChart D.site D.base D.base_mem hX.1 hint.2.1).1.left) :=
    Z.isAffine_genericChart D.site D.base D.base_mem hX.1 hint.2.1
  -- the marked point lies in the zero locus of the defining ideal
  have hzero : U.point ∈ ((BigFppfOver.toScheme D.site D.base D.base_mem).obj
      (Z.genericEtaleChart D.site D.base D.base_mem hX.1 hint.2.1).1.left).zeroLocus
        {k | k ∈ definingIdealAt D.site D.base D.base_mem ⟨X, hX.1⟩ Y
          (op (Z.genericEtaleChart D.site D.base D.base_mem hX.1 hint.2.1))} := by
    refine (Scheme.mem_zeroLocus_iff _ _ _).2 fun k hk hku => hne ?_
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hk)
      ((Scheme.mem_basicOpen _ k U.point trivial).1 hku)
  have hrange := range_rep_snd_eq_zeroLocus_definingIdealAt D.site D.base D.base_mem ⟨X, hX.1⟩ Y
    (Z.genericEtaleChart D.site D.base D.base_mem hX.1 hint.2.1)
  have hz' : U.point ∈ Set.range ((BigFppfOver.toScheme D.site D.base D.base_mem).map
      (Y.2.2.rep.snd (Z.genericEtaleChart D.site D.base D.base_mem hX.1 hint.2.1).1.hom)) :=
    Eq.mpr (congrArg (fun T => U.point ∈ T) hrange) hzero
  -- so the generic point lies in the image of `|Y|`
  have hξ : Z.genericPoint D.site D.base D.base_mem X ∈
      Set.range (pointsMap D.site D.base D.base_mem Y.1.toFunctor Y.1.ι) := by
    rw [← U.map_point, mem_range_pointsMap_ι_iff D.site D.base D.base_mem ⟨X, hX.1⟩ Y U.toSpace,
      pointsToScheme_presheafPoint]
    exact hz'
  have hYi : IsClosedImmersion D.site D.base D.base_mem Y.1.ι := Y.2.2
  have hclosed : IsClosed (Set.range (pointsMap D.site D.base D.base_mem Y.1.toFunctor Y.1.ι)) :=
    (isClosedEmbedding_pointsMap_of_isClosedImmersion D.site D.base D.base_mem hX.1
      hYi).isClosed_range
  have : T0Space (points D.site D.base D.base_mem X) :=
    t0Space_points_of_isDecentSpace D.site D.base D.base_mem hX.1 hint.2.1
  have hW := ambientGenericPoint_toIntegralClosedSubspace_eq D sX hX Z
  have hsub := ((Z.toIntegralClosedSubspace D.site D.base D.base_mem
    ).isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hX.1 |>.mem_closed_set_iff
      hclosed).1 (hW ▸ hξ)
  exact IntegralClosedSubspace.exists_pushforward_eq D.site D.base D.base_mem hX.1 Y.2.1
    (D.isDecentSpace_of_isGood sX hX) (isDecentSpace_of_isClosedSubspace D.site D.base D.base_mem
      (D.isDecentSpace_of_isGood sX hX) Y.2) hYi _ hsub

/-! ### The coefficient at a prime divisor -/

variable {n : ℤ} (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))

include hL in
/-- The meromorphic section of a nonzero global section of an invertible module is nonzero. -/
theorem globalSectionMeromorphic_ne_zero_of_isInvertibleSheaf {s : L.sections} (hs : s ≠ 0) :
    globalSectionMeromorphic D.site D.base D.base_mem hX.1 L s ≠ 0 :=
  globalSectionMeromorphic_ne_zero D.site D.base D.base_mem hX.1 L
    (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) hs

include hn in
/-- **Stacks 0EQF at a prime divisor.** The coefficient of a prime divisor `Z` in `div_ℒ(s)`,
the order of vanishing `ord_{Z,ℒ}(s)` of Stacks 0EPR, is the multiplicity of `Z` in the zero
scheme `Z(s)`, read at any family `γ` of geometric representatives lying over the points they
represent.

Both are colengths in `A = 𝒪_{U, u}` of one ideal: `ord_{Z,ℒ}(s) = length_A(A / aA)` for the
germ `a` of `s` against `s_ξ`, `aA` is the extended defining ideal of `Z(s)` over `U`, and the
multiplicity is the colength of that extended ideal when `Z ⊆ Z(s)`. When `Z ⊄ Z(s)` the
multiplicity is zero and the extended ideal is the unit ideal, so `a` is a unit. -/
theorem invertibleDivisorCoefficients_globalSection_toIntegralClosedSubspace
    {s : L.sections} (hs : s ≠ 0)
    (γ : points D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor →
      GeometricPoint D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor)
    (hγ : ∀ x, (γ x).LiesOver x) (W : PrimeDivisor D.site D.base D.base_mem X) :
    invertibleDivisorCoefficients D sX hX hint L hL
        (globalSectionMeromorphic D.site D.base D.base_mem hX.1 L s)
        (W.toIntegralClosedSubspace D.site D.base D.base_mem) =
      zeroSchemeCycleCoeff D sX hX L s (n - 1) γ
        (W.toIntegralClosedSubspace D.site D.base D.base_mem) := by
  have hN := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX
  have hLm := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  have hσ := globalSectionMeromorphic_ne_zero_of_isInvertibleSheaf D sX hX L hL hs
  set U := W.genericChart D.site D.base D.base_mem hX.1 hint.2.1 with hUdef
  set a := W.globalSectionGerm D.site D.base D.base_mem hX.1 hint.2.1 L hLm s with ha
  -- the left side is the order of vanishing of the germ
  have hleft : invertibleDivisorCoefficients D sX hX hint L hL
      (globalSectionMeromorphic D.site D.base D.base_mem hX.1 L s)
      (W.toIntegralClosedSubspace D.site D.base D.base_mem) =
      ((Ring.ord ↥(U.scheme.left.1.presheaf.stalk U.point) a).toNat : ℤ) :=
    (sectionWeilDivisor_apply_toIntegralClosedSubspace D sX hX hint L hL hn _ hσ W).trans
      (W.orderOfVanishingSection_globalSectionMeromorphic D.site D.base D.base_mem hX.1 hint.2.1
        L hLm hint hN hs)
  -- the germ generates the extended defining ideal of the zero scheme
  have hideal : Ideal.map (U.scheme.left.1.presheaf.germ ⊤ U.point trivial).hom
      (definingIdealAt D.site D.base D.base_mem ⟨X, hX.1⟩ (vanishingLocus D sX hX L s)
        (op (W.genericEtaleChart D.site D.base D.base_mem hX.1 hint.2.1))) =
      Ideal.span {a} := by
    rw [definingIdealAt_zeroScheme_eq_of_isInvertible D.site D.base D.base_mem ⟨X, hX.1⟩ L s hL
      (W.genericEtaleChart D.site D.base D.base_mem hX.1 hint.2.1)
      (W.isAffine_genericChart D.site D.base D.base_mem hX.1 hint.2.1)]
    exact (W.span_globalSectionGerm_eq_map D.site D.base D.base_mem hX.1 hint.2.1 L hLm s).symm
  rw [hleft]
  by_cases hc : ∃ Zc : IntegralClosedSubspace D.site D.base D.base_mem
      (vanishingLocus D sX hX L s).1.toFunctor,
      closedSubspaceComponentImage D sX hX (vanishingLocus D sX hX L s).1
          (vanishingLocus D sX hX L s).2 Zc =
        W.toIntegralClosedSubspace D.site D.base D.base_mem
  · obtain ⟨Zc, hZc⟩ := hc
    -- the representative of the generic point of the component lies over `ξ`
    have hlies : (geometricPointMap (closedSubspaceHom D.site D.base D.base_mem hX.1
          (vanishingLocus D sX hX L s).1 (vanishingLocus D sX hX L s).2).hom
          (γ (Zc.ambientGenericPoint D.site D.base D.base_mem))).LiesOver
        (W.genericPoint D.site D.base D.base_mem X) := by
      have : T0Space (points D.site D.base D.base_mem X) :=
        t0Space_points_of_isDecentSpace D.site D.base D.base_mem hX.1 hint.2.1
      have hW := ambientGenericPoint_toIntegralClosedSubspace_eq D sX hX W
      change pointsMap D.site D.base D.base_mem _ _
        (γ (Zc.ambientGenericPoint D.site D.base D.base_mem)).image = _
      rw [hγ, ← hW, ← hZc, IntegralClosedSubspace.ambientGenericPoint_pushforward]
      rfl
    have hex : ∃ W' : PrimeDivisor D.site D.base D.base_mem X,
        W'.subspace =
          (PrimeDivisor.toIntegralClosedSubspace D.site D.base D.base_mem W).subspace :=
      ⟨W, (PrimeDivisor.subspace_toIntegralClosedSubspace D.site D.base D.base_mem W).symm⟩
    obtain ⟨dimF, hdimF⟩ := exists_dimensionFunction_deltaValue_of_isGood D sX hX
    have hdelta : deltaDimension D sX
        (W.toIntegralClosedSubspace D.site D.base D.base_mem) = n - 1 :=
      ((isPrimeDivisor_tfae_of_isIntegralSpace D sX hX hint dimF hdimF hn
        (W.toIntegralClosedSubspace D.site D.base D.base_mem)).out 1 3).mp hex
    have hcoeff : zeroSchemeCycleCoeff D sX hX L s (n - 1) γ
        (W.toIntegralClosedSubspace D.site D.base D.base_mem) =
        ((geometricLength D.site D.base D.base_mem
          ⟨(vanishingLocus D sX hX L s).1.toFunctor, (vanishingLocus D sX hX L s).2.1⟩
          (γ (Zc.ambientGenericPoint D.site D.base D.base_mem))
          (SheafOfModules.unit _)).toNat : ℤ) := by
      rw [zeroSchemeCycleCoeff, ← hZc,
        cycleCoeffOfClosedSubspace_closedSubspaceComponentImage D sX hX
          (vanishingLocus D sX hX L s).1 (vanishingLocus D sX hX L s).2 (n - 1) γ Zc,
        ite_eq_left (hZc ▸ hdelta)]
    have hlen := geometricLength_unit_eq_length_quotient_definingIdealAt D.site D.base
      D.base_mem hX.1 (vanishingLocus D sX hX L s).1 (vanishingLocus D sX hX L s).2
      (γ (Zc.ambientGenericPoint D.site D.base D.base_mem))
      (U.smallEtaleNeighborhood _ hlies) (W.isAffine_genericChart D.site D.base D.base_mem
        hX.1 hint.2.1) U.point
      ((chartPoint_baseChange D.site D.base D.base_mem
        (closedSubspaceHom D.site D.base D.base_mem hX.1 (vanishingLocus D sX hX L s).1
          (vanishingLocus D sX hX L s).2) (vanishingLocus D sX hX L s).2.2.rep
        (γ (Zc.ambientGenericPoint D.site D.base D.base_mem))
        (U.smallEtaleNeighborhood _ hlies)).trans
        (chartPoint_smallEtaleNeighborhood _ _ _ _ _ U _ hlies))
    rw [hcoeff, hlen]
    exact congrArg (fun m : ℕ∞ => (m.toNat : ℤ))
      (congrArg (fun I : Ideal ↥(U.scheme.left.1.presheaf.stalk U.point) =>
        Module.length ↥(U.scheme.left.1.presheaf.stalk U.point)
          (↥(U.scheme.left.1.presheaf.stalk U.point) ⧸ I)) hideal).symm
  · -- `Z ⊄ Z(s)`: the multiplicity vanishes and the germ is a unit
    push Not at hc
    rw [zeroSchemeCycleCoeff, cycleCoeffOfClosedSubspace_eq_zero D sX hX
      (vanishingLocus D sX hX L s).1 (vanishingLocus D sX hX L s).2 (n - 1) γ _ hc]
    have htop : Ideal.span {a} = ⊤ := by
      by_contra hne
      obtain ⟨Zc, hZc⟩ := W.exists_closedSubspaceComponentImage_of_map_ne_top D sX hX hint
        (vanishingLocus D sX hX L s) (hideal ▸ hne)
      exact hc Zc hZc
    rw [Ring.ord_of_isUnit (Ideal.span_singleton_eq_top.1 htop)]
    rfl

/-! ### The two coefficient families agree -/

include hn in
/-- **The coefficient families of `div_ℒ(s)` and of `[Z(s)]_{n-1}` are equal**, for any family `γ`
of geometric representatives lying over the points they represent. At a prime divisor this is
`AlgebraicGeometry.Space.invertibleDivisorCoefficients_globalSection_toIntegralClosedSubspace`;
at an integral closed subspace which is not a prime divisor both vanish, by Stacks 0EQE part (1)
on one side and by Stacks 0EPZ — the subspace then has δ-dimension other than `n - 1` — on the
other. -/
theorem zeroSchemeCycleCoeff_eq_invertibleDivisorCoefficients_globalSection
    {s : L.sections} (hs : s ≠ 0)
    (γ : points D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor →
      GeometricPoint D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor)
    (hγ : ∀ x, (γ x).LiesOver x) :
    zeroSchemeCycleCoeff D sX hX L s (n - 1) γ =
      invertibleDivisorCoefficients D sX hX hint L hL
        (globalSectionMeromorphic D.site D.base D.base_mem hX.1 L s) := by
  funext Z
  by_cases hZ : codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hX.1 Z) = 1
  · have h := invertibleDivisorCoefficients_globalSection_toIntegralClosedSubspace D sX hX hint L
      hL hn hs γ hγ (Z.toPrimeDivisor D.site D.base D.base_mem hX.1 hZ)
    rw [IntegralClosedSubspace.toIntegralClosedSubspace_toPrimeDivisor] at h
    exact h.symm
  · obtain ⟨dimF, hdimF⟩ := exists_dimensionFunction_deltaValue_of_isGood D sX hX
    rw [zeroSchemeCycleCoeff_of_deltaDimension_ne D sX hX L s (n - 1) γ
      fun h => hZ (((isPrimeDivisor_tfae_of_isIntegralSpace D sX hX hint dimF hdimF hn
        Z).out 3 2).mp h), invertibleDivisorCoefficients]
    have hN := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX
    have : ∀ W : PrimeDivisor D.site D.base D.base_mem X, Nontrivial
        ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hint.2.1) := fun W =>
      W.nontrivial_genericHenselianLocalRing D.site D.base D.base_mem hX.1 hint.2.1 hint hN
    have : ∀ W : PrimeDivisor D.site D.base D.base_mem X, IsNoetherianRing
        ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hint.2.1) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing D.site D.base D.base_mem hX.1 hint.2.1 hint hN
    have : ∀ W : PrimeDivisor D.site D.base D.base_mem X, Ring.KrullDimLE 1
        ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hint.2.1) := fun W =>
      W.krullDimLE_genericHenselianLocalRing D.site D.base D.base_mem hX.1 hint.2.1 hint hN
    exact (divisorCycleCoefficients_of_codimension_ne_one D sX hX hint.2.1 L _ _ hZ).symm

include hint hL hn in
/-- **`[Z(s)]_{n-1}` is an `(n-1)`-cycle**: its coefficient family is that of `div_ℒ(s)`. -/
theorem zeroSchemeCycleCoeff_globalSection_mem_cyclesOfDimension {s : L.sections} (hs : s ≠ 0)
    (γ : points D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor →
      GeometricPoint D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor)
    (hγ : ∀ x, (γ x).LiesOver x) :
    zeroSchemeCycleCoeff D sX hX L s (n - 1) γ ∈ cyclesOfDimension D sX (n - 1) := by
  rw [zeroSchemeCycleCoeff_eq_invertibleDivisorCoefficients_globalSection D sX hX hint L hL hn hs
    γ hγ]
  exact (sectionWeilDivisor D sX hX hint L hL hn _
    (globalSectionMeromorphic_ne_zero_of_isInvertibleSheaf D sX hX L hL hs)).2

include hint hL hn in
/-- **The coefficients of `[Z(s)]_{n-1}` are locally finite**, as those of `div_ℒ(s)` are. -/
theorem locallyFinite_zeroSchemeCycleCoeff_globalSection {s : L.sections} (hs : s ≠ 0)
    (γ : points D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor →
      GeometricPoint D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor)
    (hγ : ∀ x, (γ x).LiesOver x) :
    LocallyFinite fun Z : IntegralClosedSubspace D.site D.base D.base_mem X =>
      if zeroSchemeCycleCoeff D sX hX L s (n - 1) γ Z = 0 then ∅
      else subspacePointSet D.site D.base D.base_mem X Z.subspace :=
  (zeroSchemeCycleCoeff_globalSection_mem_cyclesOfDimension D sX hX hint L hL hn hs γ hγ).1

/-- The canonical geometric representatives of the points of a space lie over them. -/
theorem canonicalGeometricPoint_liesOver (G : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u)
    (x : points D.site D.base D.base_mem G) :
    (canonicalGeometricPoint D.site D.base D.base_mem G x).LiesOver x :=
  (exists_geometricRepresentative D.site D.base D.base_mem G x).choose_spec

/-! ### Stacks 0EQF -/

include hn in
/-- **Stacks 0EQF, for any family of geometric representatives.** Both identities hold with the
multiplicities of `[Z(s)]_{n-1}` read at any family `γ` of geometric representatives lying over
the points they represent. -/
theorem sectionWeilDivisor_eq_zeroSchemeCycle_and_weilDivisorOfInvertibleSheaf_eq_of_liesOver
    {s : L.sections} (hs : s ≠ 0)
    (γ : points D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor →
      GeometricPoint D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor)
    (hγ : ∀ x, (γ x).LiesOver x) :
    sectionWeilDivisor D sX hX hint L hL hn
        (globalSectionMeromorphic D.site D.base D.base_mem hX.1 L s)
        (globalSectionMeromorphic_ne_zero_of_isInvertibleSheaf D sX hX L hL hs) =
      zeroSchemeCycle D sX hX L s (n - 1) γ
        (locallyFinite_zeroSchemeCycleCoeff_globalSection D sX hX hint L hL hn hs γ hγ) ∧
    weilDivisorOfInvertibleSheaf.{v} D sX hX hint L hL hn =
      chowClass.{v} D sX hX (n - 1) (zeroSchemeCycle D sX hX L s (n - 1) γ
        (locallyFinite_zeroSchemeCycleCoeff_globalSection D sX hX hint L hL hn hs γ hγ)) := by
  have h1 : sectionWeilDivisor D sX hX hint L hL hn
      (globalSectionMeromorphic D.site D.base D.base_mem hX.1 L s)
      (globalSectionMeromorphic_ne_zero_of_isInvertibleSheaf D sX hX L hL hs) =
      zeroSchemeCycle D sX hX L s (n - 1) γ
        (locallyFinite_zeroSchemeCycleCoeff_globalSection D sX hX hint L hL hn hs γ hγ) :=
    Subtype.ext (zeroSchemeCycleCoeff_eq_invertibleDivisorCoefficients_globalSection D sX hX hint
      L hL hn hs γ hγ).symm
  exact ⟨h1, (chowClass_sectionWeilDivisor.{v} D sX hX hint L hL hn _ _).symm.trans
    (congrArg (chowClass.{v} D sX hX (n - 1)) h1)⟩

include hn in
/-- **Stacks 0EQF.** In Situation 0EDT let `X/B` be good, let `X` be integral with
`n = dim_δ(X)`, let `ℒ` be an invertible `𝒪_X`-module and let `s ∈ Γ(X, ℒ)` be a nonzero global
section. Then

`div_ℒ(s) = [Z(s)]_{n-1}` in `Z_{n-1}(X)`  and  `c₁(ℒ) ∩ [X] = [Z(s)]_{n-1}` in `CH_{n-1}(X)`.

`div_ℒ(s)` is the Weil divisor of Stacks 0EQE, part (1), of the meromorphic section of `ℒ` that
`s` is; `c₁(ℒ) ∩ [X]` is Stacks 0EQE, part (2), in the Chow group `CH_{n-1}(X)` of Stacks 0EQ6;
and `[Z(s)]_{n-1}` is the cycle of Stacks 0EE9 of the zero scheme of Stacks 0845, its
multiplicities read at the canonical geometric representative of each point — by Stacks 0EE1
any representatives lying over the points give the same cycle, and
`sectionWeilDivisor_eq_zeroSchemeCycle_and_weilDivisorOfInvertibleSheaf_eq_of_liesOver` states
the identities for all of them. That `[Z(s)]_{n-1}` is an `(n-1)`-cycle is part of the
conclusion: its coefficients are those of `div_ℒ(s)`. -/
@[stacks 0EQF "both identities: div_ℒ(s) = [Z(s)]_{n-1} in Z_{n-1}(X) and c₁(ℒ) ∩ [X] = \
  [Z(s)]_{n-1} in CH_{n-1}(X), for X/B good and integral with n = dim_δ(X), ℒ invertible and s a \
  nonzero global section; div_ℒ(s) and c₁(ℒ) ∩ [X] are Stacks 0EQE parts (1) and (2) with every \
  ingredient constructed, CH_{n-1}(X) is Stacks 0EQ6, [Z(s)]_{n-1} is Stacks 0EE9 of the zero \
  scheme of Stacks 0845 at the canonical geometric representatives; nothing carried"]
theorem sectionWeilDivisor_eq_zeroSchemeCycle_and_weilDivisorOfInvertibleSheaf_eq
    {s : L.sections} (hs : s ≠ 0) :
    sectionWeilDivisor D sX hX hint L hL hn
        (globalSectionMeromorphic D.site D.base D.base_mem hX.1 L s)
        (globalSectionMeromorphic_ne_zero_of_isInvertibleSheaf D sX hX L hL hs) =
      zeroSchemeCycle D sX hX L s (n - 1)
        (canonicalGeometricPoint D.site D.base D.base_mem
          (vanishingLocus D sX hX L s).1.toFunctor)
        (locallyFinite_zeroSchemeCycleCoeff_globalSection D sX hX hint L hL hn hs _
          (canonicalGeometricPoint_liesOver D _)) ∧
    weilDivisorOfInvertibleSheaf.{v} D sX hX hint L hL hn =
      chowClass.{v} D sX hX (n - 1) (zeroSchemeCycle D sX hX L s (n - 1)
        (canonicalGeometricPoint D.site D.base D.base_mem
          (vanishingLocus D sX hX L s).1.toFunctor)
        (locallyFinite_zeroSchemeCycleCoeff_globalSection D sX hX hint L hL hn hs _
          (canonicalGeometricPoint_liesOver D _))) :=
  sectionWeilDivisor_eq_zeroSchemeCycle_and_weilDivisorOfInvertibleSheaf_eq_of_liesOver D sX hX
    hint L hL hn hs _ (canonicalGeometricPoint_liesOver D _)

end AlgebraicGeometry.Space

end
