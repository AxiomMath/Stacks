module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalDivisorCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EqualDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardOfDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardOfDivisorChart
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericallyFiniteCodimensionOne
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralGenericallyFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.NormalIntegralElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardOfDivisorGenericRank
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardFibreSumGenericPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularMeromorphicSectionNeZero
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.WeilDivisorOfInvertibleSheaf

/-!
# Stacks 0EQS: the pushforward of the divisor of a pulled-back section

In Situation 0EDT let `X/B` and `Y/B` be good, let `f : X ⟶ Y` be proper, let `ℒ` be an
invertible sheaf on `Y`, assume `X` and `Y` integral, `f` dominant and `dim_δ(X) = dim_δ(Y) = n`,
and let `s` be a nonzero meromorphic section of `ℒ`. Then

`f_*(div_{f^*ℒ}(f^*s)) = [R(X) : R(Y)] div_ℒ(s)` in `Z_{n-1}(Y)`,

and in particular `f_*(c₁(f^*ℒ) ∩ [X]) = c₁(ℒ) ∩ f_*[X]` in `CH_{n-1}(Y)`.

## Main results

* `AlgebraicGeometry.Space.finsum_canonicalDivisorCycle_pullback_mul_properCycleMult_eq`: the
  identity at one prime divisor `W` of `Y`, `∑_Z ord_Z(f^*s) deg(Z/W) = [R(X) : R(Y)] ord_W(s)`.
* `AlgebraicGeometry.Space.properCyclePushforward_eq_zsmul_of_forall_primeDivisor`: a proper
  pushforward of `k`-cycles with `dim_δ(Y) = k + 1` is determined by its coefficients at the
  prime divisors of `Y`.
* `AlgebraicGeometry.Space.properCyclePushforward_canonicalDivisorCycle_pullback`: Stacks 0EQS,
  first conclusion, for the Weil divisors at the canonical generators.
* `AlgebraicGeometry.Space.properCyclePushforward_canonicalDivisorCycleAt_pullback`: the same,
  graded by `k` with `dim_δ = k + 1`.
* `AlgebraicGeometry.Space.properCyclePushforward_sectionWeilDivisor_pullback`: Stacks 0EQS, both
  conclusions, for the Weil divisor and the class `c₁(ℒ) ∩ [Y]` of Stacks 0EQE.

## Implementation notes

The first identity is proved at each prime divisor `W` of `Y`, on one étale chart: an elementary
affine étale neighbourhood `V` of the generic point of `W` on which `ℒ` is free and over which
`f` is finite with `U = X ×_Y V` affine
(`AlgebraicGeometry.Space.exists_finite_affine_chartDiagram_free`). With `A = Γ(V, 𝒪)`,
`B = Γ(U, 𝒪)` and `𝔭 ⊆ A` the prime of the generic point of `W`, the points of `X` over the
generic point of `W` are the primes `𝔮` of `B` over `𝔭`, the orders of vanishing are lengths
read on `A_𝔭` and the `B_𝔮`, and the identity is the ring-theoretic

`∑_{𝔮 ∣ 𝔭} [κ(𝔮) : κ(𝔭)] ord_{B_𝔮}(a) = d · ord_{A_𝔭}(a)`

(`Stacks.Length.finsum_primeResidueDegree_mul_ord_eq_mul_ord`, from Stacks 02QG and 02M0) with
`d` the generic rank of `B` over `A`, which is `[R(X) : R(Y)]` by the generic fibre square of
`f` (`AlgebraicGeometry.Space.length_localizedModule_chartRing_eq_functionFieldDegree_mul`). This
is a norm-free form of Stacks 0EQ4.

## References

* [Stacks Project, Tag 0EQS](https://stacks.math.columbia.edu/tag/0EQS)
* [Stacks Project, Tag 0EQE](https://stacks.math.columbia.edu/tag/0EQE)
* [Stacks Project, Tag 0EQ4](https://stacks.math.columbia.edu/tag/0EQ4)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 02QG](https://stacks.math.columbia.edu/tag/02QG)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (hintX : IsIntegralSpace D.site D.base D.base_mem X)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y)

/-! ### The fibre over the generic point of a prime divisor -/

section Fibre

/-- On an integral good space of δ-dimension `n`, an integral closed subspace has codimension one
exactly when its δ-dimension is `n - 1`. -/
private theorem codimension_eq_one_iff_deltaDimension_eq_sub_one
    (hintX : IsIntegralSpace D.site D.base D.base_mem X) {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hX.1 Z) = 1 ↔
      deltaDimension D sX Z = n - 1 :=
  (isPrimeDivisor_tfae D sX hX hintX hn Z).out 2 3

include hintX hintY in
/-- Every point over the generic point of a prime divisor of `Y` is the generic point of a prime
divisor of `X`: for `f` proper, carrying the generic point to the generic point, with
`dim_δ(X) = dim_δ(Y) = n`, the integral closed subspace of `X` whose generic point lies over the
generic point of a prime divisor of `Y` has δ-dimension `n - 1`. -/
theorem deltaDimension_integralClosedSubspaceOfPoint_of_pointsMap_eq_genericPoint {f : X ⟶ Y}
    (hfB : f ≫ sY = sX) (hf : IsProper D.site D.base D.base_mem f)
    (hgen : pointsMap D.site D.base D.base_mem X f
        (genericPoint D.site D.base D.base_mem hX.1 hintX) =
      genericPoint D.site D.base D.base_mem hY.1 hintY) {n : ℤ}
    (hnX : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (hnY : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (n : EInt))
    (W : PrimeDivisor D.site D.base D.base_mem Y) (x : points D.site D.base D.base_mem X)
    (hx : pointsMap D.site D.base D.base_mem X f x = W.genericPoint D.site D.base D.base_mem Y) :
    deltaDimension D sX (integralClosedSubspaceOfPoint D.site D.base D.base_mem hX.1
      (D.isDecentSpace_of_isGood sX hX) x) = n - 1 := by
  have hXdec := D.isDecentSpace_of_isGood sX hX
  have hYdec := D.isDecentSpace_of_isGood sY hY
  have hflft : IsLocallyOfFiniteType D.site D.base D.base_mem f := hf.2.1.1
  have hqf : IsQuasiFiniteAt D.site D.base D.base_mem f x := by
    refine isQuasiFiniteAt_of_localRingDimension_le_one D.site D.base D.base_mem hX.1 hY.1 f hflft
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY) _
      (le_of_eq (W.localRingDimension_genericPoint D.site D.base D.base_mem hY.1 hYdec))
      (Or.inl fun x' hx' => ?_) x hx
    let : QuasiSober (points D.site D.base D.base_mem X) :=
      quasiSober_points_of_isDecentSpace D.site D.base D.base_mem hX.1 hXdec
    let : IrreducibleSpace (points D.site D.base D.base_mem X) := hintX.2.2
    let : T0Space (points D.site D.base D.base_mem X) :=
      t0Space_points_of_isDecentSpace D.site D.base D.base_mem hX.1 hXdec
    have hx'g : x' = genericPoint D.site D.base D.base_mem hX.1 hintX := by
      have := (mem_genericPoints_iff_localRingDimension_eq_zero D.site D.base D.base_mem hX.1
        hXdec x').mpr hx'
      rw [genericPoints_eq_singleton] at this
      exact this
    rw [hx'g]
    exact hasTranscendenceDegreeAt_genericPoint_eq_zero D sX sY hX hY hintX hintY f hfB hgen
      (hnX.trans hnY.symm)
  have htr := hasTranscendenceDegreeAt_zero_of_isQuasiFiniteAt D.site D.base D.base_mem hX.1 hY.1
    f hqf
  obtain ⟨b, hb⟩ := exists_finite_transcendenceDegreeAt D.site D.base D.base_mem sY hY.2.2
    (pointsMap D.site D.base D.base_mem X f x)
  have hcomp : HasTranscendenceDegreeAt D.site D.base D.base_mem sX x ((0 : ℕ∞) + (b : ℕ∞)) := by
    rw [← hfB]
    exact hasTranscendenceDegreeAt_comp D.site D.base D.base_mem hX.1 hY.1 D.isAlgebraicSpace
      f sY x 0 (b : ℕ∞) htr hb
  rw [zero_add] at hcomp
  have hXval := inducedDimensionValue_eq D.site D.base D.base_mem hX.1 D.isAlgebraicSpace
    D.delta sX hX.2.2 x (b : ℕ∞) hcomp
  have hYval := inducedDimensionValue_eq D.site D.base D.base_mem hY.1 D.isAlgebraicSpace
    D.delta sY hY.2.2 (pointsMap D.site D.base D.base_mem X f x) (b : ℕ∞) hb
  have himg : pointsMap D.site D.base D.base_mem X sX x =
      pointsMap D.site D.base D.base_mem Y sY (pointsMap D.site D.base D.base_mem X f x) := by
    rw [← hfB, pointsMap_comp_apply]
  have hW := (codimension_eq_one_iff_deltaDimension_eq_sub_one D sY hY hintY hnY
    (W.toIntegralClosedSubspace D.site D.base D.base_mem)).mp
    (W.codimension_integralClosedSubspaceSupport D.site D.base D.base_mem hY.1)
  rw [deltaDimension_eq_of_isGenericPoint D sY hY.1 _ (W.genericPoint D.site D.base D.base_mem Y)
    (W.isGenericPoint_genericPoint D.site D.base D.base_mem)] at hW
  rw [deltaDimension_eq_of_isGenericPoint D sX hX.1 _ x
    (isGenericPoint_integralClosedSubspaceOfPoint D.site D.base D.base_mem hX.1 hXdec x)]
  rw [← hx] at hW
  change inducedDimensionValue D.site D.base D.base_mem D.delta sX x = n - 1
  change inducedDimensionValue D.site D.base D.base_mem D.delta sY
    (pointsMap D.site D.base D.base_mem X f x) = n - 1 at hW
  rw [hXval, himg, ← hW, hYval]

end Fibre

/-! ### The coefficient of the canonical divisor at an integral closed subspace -/

section Coefficient

variable {Z : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sZ : Z ⟶ D.space)
    (hZ : D.IsGood sZ) (hintZ : IsIntegralSpace D.site D.base D.base_mem Z)

/-- At an integral closed subspace of codimension one, the coefficient of the canonical divisor
`div_ℒ(s)` is the order of vanishing of `s` along the corresponding prime divisor at the
canonical ratio. -/
theorem canonicalDivisorCycle_apply_of_codimension_eq_one
    (L : Modules.{u, u} D.site D.base D.base_mem Z hZ.1)
    (hL : IsInvertibleModule (B := D.site) ⟨Z, hZ.1⟩ L)
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem Z hZ.1 L)
    (hs : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Z hZ.1 L s) {n : ℤ}
    (hn : deltaDimensionClosed D sZ hZ Set.univ isClosed_univ = (n : EInt))
    (W : IntegralClosedSubspace D.site D.base D.base_mem Z)
    (h : codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hZ.1 W) = 1) :
    haveI : ∀ W : PrimeDivisor D.site D.base D.base_mem Z,
        Nontrivial ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hZ.1
          (isDecentSpace_of_isGood D sZ hZ)) := fun W =>
      W.nontrivial_genericHenselianLocalRing D.site D.base D.base_mem hZ.1
        (isDecentSpace_of_isGood D sZ hZ) hintZ
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sZ hZ)
    haveI : ∀ W : PrimeDivisor D.site D.base D.base_mem Z,
        IsNoetherianRing ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hZ.1
          (isDecentSpace_of_isGood D sZ hZ)) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing D.site D.base D.base_mem hZ.1
        (isDecentSpace_of_isGood D sZ hZ) hintZ
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sZ hZ)
    haveI : ∀ W : PrimeDivisor D.site D.base D.base_mem Z,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hZ.1
          (isDecentSpace_of_isGood D sZ hZ)) := fun W =>
      W.krullDimLE_genericHenselianLocalRing D.site D.base D.base_mem hZ.1
        (isDecentSpace_of_isGood D sZ hZ) hintZ
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sZ hZ)
    (canonicalDivisorCycle D sZ hZ hintZ L hL s hs hn).1 W =
      orderOfVanishingSection.{u, u} D.site D.base D.base_mem hZ.1 (isDecentSpace_of_isGood D sZ hZ)
        (W.toPrimeDivisor D.site D.base D.base_mem hZ.1 h) L s
        ((W.toPrimeDivisor D.site D.base D.base_mem hZ.1 h).canonicalLocalRatio D.site D.base
          D.base_mem hZ.1 (isDecentSpace_of_isGood D sZ hZ) L hL hintZ
          (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sZ hZ)) := by
  unfold canonicalDivisorCycle
  rw [divisorCycleOfSection_coe]
  unfold divisorCycleCoefficients
  rw [dite_eq_left h]
  rfl

end Coefficient

/-! ### The coefficient identity at a prime divisor of `Y` -/

section Identity

/-- `f` read as a morphism of the category of algebraic spaces. -/
abbrev goodSpacesHom (f : X ⟶ Y) :
    (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY.1⟩ :=
  ⟨f⟩

variable (L : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hL : IsInvertibleModule (B := D.site) ⟨Y, hY.1⟩ L)
    (σ : MeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 L)
    (hσ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 L σ)

include hintX hintY in
/-- Stacks 0EQS at one prime divisor of `Y`: in the situation of Stacks 0EQS, for every prime
divisor `W` of `Y` the coefficient of `f_*(div_{f^*ℒ}(f^*s))` at `W` is `[R(X) : R(Y)]` times the
coefficient of `div_ℒ(s)` at `W`. -/
theorem finsum_canonicalDivisorCycle_pullback_mul_properCycleMult_eq {f : X ⟶ Y}
    (hfB : f ≫ sY = sX) (hf : IsProper D.site D.base D.base_mem f)
    (hdom : IsDominant D.site D.base D.base_mem f)
    (hPull : PullbacksMeromorphicSections D.site D.base D.base_mem f) {n : ℤ}
    (hnX : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (hnY : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (n : EInt))
    (W : PrimeDivisor D.site D.base D.base_mem Y) :
    ∑ᶠ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
        (canonicalDivisorCycle D sX hX hintX
          ((modulePullback D.site D.base D.base_mem (goodSpacesHom D sX hX sY hY f)).obj L)
          (modulePullbackInvertible (goodSpacesHom D sX hX sY hY f) L hL)
          (pullbackMeromorphicSection D.site D.base D.base_mem (goodSpacesHom D sX hX sY hY f) L
            hPull σ)
          (isRegularMeromorphicSection_pullbackMeromorphicSection D.site D.base D.base_mem
            (goodSpacesHom D sX hX sY hY f) hPull L
            (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL) σ hσ) hnX).1 Z *
          properCycleMult D sX hX sY hY f Z (W.toIntegralClosedSubspace D.site D.base D.base_mem) =
      (functionFieldDegreeAtGenericPoint D sX hX sY hY hintX f : ℤ) *
        (canonicalDivisorCycle D sY hY hintY L hL σ hσ hnY).1
          (W.toIntegralClosedSubspace D.site D.base D.base_mem) := by
  classical
  have hXdec := D.isDecentSpace_of_isGood sX hX
  have hYdec := D.isDecentSpace_of_isGood sY hY
  have hXN := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX
  have hYN := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY
  have hgen := pointsMap_genericPoint_of_isDominant D.site D.base D.base_mem hX.1 hY.1 hintX
    hintY f hdom
  have hdim : deltaDimensionClosed D sX hX Set.univ isClosed_univ =
      deltaDimensionClosed D sY hY Set.univ isClosed_univ := hnX.trans hnY.symm
  let : T0Space (points D.site D.base D.base_mem Y) :=
    t0Space_points_of_isDecentSpace D.site D.base D.base_mem hY.1 hYdec
  let : T0Space (points D.site D.base D.base_mem X) :=
    t0Space_points_of_isDecentSpace D.site D.base D.base_mem hX.1 hXdec
  set φ := goodSpacesHom D sX hX sY hY f
  set c := canonicalDivisorCycle D sX hX hintX
    ((modulePullback D.site D.base D.base_mem φ).obj L) (modulePullbackInvertible φ L hL)
    (pullbackMeromorphicSection D.site D.base D.base_mem φ L hPull σ)
    (isRegularMeromorphicSection_pullbackMeromorphicSection D.site D.base D.base_mem φ hPull L
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL) σ hσ) hnX
  have hα : ∀ Z, c.1 Z ≠ 0 → deltaDimension D sX Z = n - 1 := fun Z hZ => c.2.2 Z hZ
  set W' := W.toIntegralClosedSubspace D.site D.base D.base_mem
  have hW'cod := W.codimension_integralClosedSubspaceSupport D.site D.base D.base_mem hY.1
  have hW' : deltaDimension D sY W' = n - 1 :=
    (codimension_eq_one_iff_deltaDimension_eq_sub_one D sY hY hintY hnY W').mp hW'cod
  have hamb : W'.ambientGenericPoint D.site D.base D.base_mem =
      W.genericPoint D.site D.base D.base_mem Y :=
    (W'.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hY.1).eq
      (W.isGenericPoint_genericPoint D.site D.base D.base_mem)
  rw [finsum_mul_properCycleMult_eq_finsum_fibre D sX hX sY hY f (n - 1) c.1 hα W' hW', hamb]
  set G : points D.site D.base D.base_mem X → ℤ := fun x =>
    c.1 (integralClosedSubspaceOfPoint D.site D.base D.base_mem hX.1 hXdec x) *
      (cycleResidueDegree D sX hX sY hY f x : ℤ)
  have hdrop : (∑ᶠ x ∈ {x | pointsMap D.site D.base D.base_mem X f x =
          W.genericPoint D.site D.base D.base_mem Y ∧
        c.1 (integralClosedSubspaceOfPoint D.site D.base D.base_mem hX.1 hXdec x) ≠ 0}, G x) =
      ∑ᶠ x ∈ {x | pointsMap D.site D.base D.base_mem X f x =
        W.genericPoint D.site D.base D.base_mem Y}, G x := by
    rw [← finsum_mem_inter_support G, ← finsum_mem_inter_support G {x |
      pointsMap D.site D.base D.base_mem X f x = W.genericPoint D.site D.base D.base_mem Y}]
    refine finsum_mem_congr ?_ fun _ _ => rfl
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Function.mem_support]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, left_ne_zero_of_mul h.2⟩, h.2⟩⟩
  rw [hdrop]
  have hfib := finite_fibre_primeDivisor_genericPoint D sX hX sY hY hintX hintY hfB hf hgen hdim W
  obtain ⟨d, e, hd, hV, hU, hfinite, he, huniq, hmono, eM, hcompat, hbij⟩ :=
    exists_finite_affine_chartDiagram_free D.site D.base D.base_mem hXdec hYdec φ hf
      (W.genericPoint D.site D.base D.base_mem Y) hfib L hL
  have := hU
  have := hV
  have hbijOn := bijOn_chartSchemeToPoints_fibre D.site D.base D.base_mem φ d hd _ e
    he huniq hmono
  have hfinw : {w : chartScheme d.U | ((BigFppfOver.toScheme D.site D.base D.base_mem).map
      d.g).base w = e}.Finite :=
    Set.Finite.of_finite_image (hbijOn.image_eq ▸ hfib) hbijOn.injOn
  rw [← finsum_mem_eq_of_bijOn (chartSchemeToPoints D.site D.base D.base_mem X d.U) hbijOn
    (fun w _ => rfl)]
  rw [canonicalDivisorCycle_apply_of_codimension_eq_one D sY hY hintY L hL σ hσ hnY W' hW'cod,
    IntegralClosedSubspace.toPrimeDivisor_eq D.site D.base D.base_mem hY.1 W' hW'cod W rfl]
  have hmin := comap_mem_minimalPrimes_chartDiagramRestrict D.site D.base D.base_mem hintX hintY φ
    hgen d hU hV
  have hαw : ∀ w, ((BigFppfOver.toScheme D.site D.base D.base_mem).map d.g).base w = e →
      ∃ P : PrimeDivisor D.site D.base D.base_mem X,
        P.genericPoint D.site D.base D.base_mem X =
          chartSchemeToPoints D.site D.base D.base_mem X d.U w ∧
        have : ∀ W : PrimeDivisor D.site D.base D.base_mem X,
            Nontrivial ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hXdec) :=
          fun W => W.nontrivial_genericHenselianLocalRing D.site D.base D.base_mem hX.1 hXdec hintX
            hXN
        have : ∀ W : PrimeDivisor D.site D.base D.base_mem X,
            IsNoetherianRing ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hXdec) :=
          fun W => W.isNoetherianRing_genericHenselianLocalRing D.site D.base D.base_mem hX.1 hXdec
            hintX hXN
        have : ∀ W : PrimeDivisor D.site D.base D.base_mem X,
            Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hXdec) :=
          fun W => W.krullDimLE_genericHenselianLocalRing D.site D.base D.base_mem hX.1 hXdec hintX
            hXN
        c.1 (integralClosedSubspaceOfPoint D.site D.base D.base_mem hX.1 hXdec
            (chartSchemeToPoints D.site D.base D.base_mem X d.U w)) =
          orderOfVanishingSection.{u, u} D.site D.base D.base_mem hX.1 hXdec P
            ((modulePullback D.site D.base D.base_mem φ).obj L)
            (pullbackMeromorphicSection D.site D.base D.base_mem φ L hPull σ)
            (P.canonicalLocalRatio D.site D.base D.base_mem hX.1 hXdec
              ((modulePullback D.site D.base D.base_mem φ).obj L) (modulePullbackInvertible φ L hL)
              hintX hXN) := by
    intro w hw
    set x := chartSchemeToPoints D.site D.base D.base_mem X d.U w
    have hx : pointsMap D.site D.base D.base_mem X f x =
        W.genericPoint D.site D.base D.base_mem Y :=
      hbijOn.mapsTo hw
    have hδ := deltaDimension_integralClosedSubspaceOfPoint_of_pointsMap_eq_genericPoint D sX hX sY
      hY hintX hintY hfB hf hgen hnX hnY W x hx
    have hcod := (codimension_eq_one_iff_deltaDimension_eq_sub_one D sX hX hintX hnX
      (integralClosedSubspaceOfPoint D.site D.base D.base_mem hX.1 hXdec x)).mpr hδ
    refine ⟨(integralClosedSubspaceOfPoint D.site D.base D.base_mem hX.1 hXdec x).toPrimeDivisor
      D.site D.base D.base_mem hX.1 hcod, ?_, ?_⟩
    · exact (PrimeDivisor.isGenericPoint_genericPoint D.site D.base D.base_mem X _).eq
        (isGenericPoint_integralClosedSubspaceOfPoint D.site D.base D.base_mem hX.1 hXdec x)
    · exact canonicalDivisorCycle_apply_of_codimension_eq_one D sX hX hintX _ _ _ _ hnX _ hcod
  refine Eq.trans (finsum_mem_congr rfl fun w hw => ?_)
    (finsum_primeResidueDegree_mul_orderOfVanishingSection_eq D.site D.base D.base_mem φ hPull d hU
      hV hXdec hYdec hintX hintY hXN hYN hfinite L hL σ hσ eM hcompat hbij W e he hmin
      (functionFieldDegreeAtGenericPoint D sX hX sY hY hintX f)
      (fun P hP _ => length_localizedModule_chartRing_eq_functionFieldDegree_mul D sX hX sY hY
        hintX hintY hfB hf hdom hdim d hd hU hV P hP) hfinw _ hαw)
  change c.1 (integralClosedSubspaceOfPoint D.site D.base D.base_mem hX.1 hXdec
      (chartSchemeToPoints D.site D.base D.base_mem X d.U w)) *
      (cycleResidueDegree D sX hX sY hY f
        (chartSchemeToPoints D.site D.base D.base_mem X d.U w) : ℤ) =
    _
  rw [mul_comm]
  congr 2
  exact (primeResidueDegree_chartPrime_eq_finrank D.site D.base D.base_mem hXdec hYdec φ d hd _ e
    he huniq hmono w hw).symm

end Identity

/-! ### From the prime divisors of `Y` to the whole cycle -/

section Assembly

include hintY in
/-- A proper pushforward is determined by its coefficients at the prime divisors. Let
`dim_δ(Y) = k + 1`. If a `k`-cycle `α` on `X` and a `k`-cycle `β` on `Y` satisfy
`∑_Z α(Z) · deg(Z/W) = m · β(W)` at every prime divisor `W` of `Y`, then `f_* α = m · β`. -/
theorem properCyclePushforward_eq_zsmul_of_forall_primeDivisor {f : X ⟶ Y}
    (hfB : f ≫ sY = sX) (hqc : IsQuasiCompact D.site D.base D.base_mem f) {k : ℤ}
    (hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt))
    (α : CycleGroup D sX k) (β : CycleGroup D sY k) (m : ℤ)
    (h : ∀ W : PrimeDivisor D.site D.base D.base_mem Y,
      ∑ᶠ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
          α.1 Z * properCycleMult D sX hX sY hY f Z
            (W.toIntegralClosedSubspace D.site D.base D.base_mem) =
        m * β.1 (W.toIntegralClosedSubspace D.site D.base D.base_mem)) :
    properCyclePushforward D sX hX sY hY hfB hqc k α = m • β := by
  refine Subtype.ext (funext fun Z' => ?_)
  rw [properPushforward_apply]
  change _ = m • β.1 Z'
  rw [smul_eq_mul]
  by_cases hcod :
      codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hY.1 Z') = 1
  · have hW := h (Z'.toPrimeDivisor D.site D.base D.base_mem hY.1 hcod)
    rwa [IntegralClosedSubspace.toIntegralClosedSubspace_toPrimeDivisor] at hW
  · have hcod' := fun hδ => hcod
      ((codimension_eq_one_iff_deltaDimension_eq_sub_one D sY hY hintY hk Z').mpr hδ)
    have hβ : β.1 Z' = 0 := by
      by_contra hb
      exact hcod' (by rw [β.2.2 Z' hb]; ring)
    rw [hβ, mul_zero]
    refine finsum_eq_zero_of_forall_eq_zero fun Z => ?_
    by_cases hα : α.1 Z = 0
    · rw [hα, zero_mul]
    by_cases hm : properCycleMult D sX hX sY hY f Z Z' = 0
    · rw [hm, mul_zero]
    obtain ⟨him, hdeg⟩ := (properCycleMult_ne_zero_iff D sX hX sY hY f Z Z').1 hm
    have hδY := deltaDimension_closureImage_of_properCycleDegree_ne_zero D sX hX sY hY f hdeg
    rw [him, α.2.2 Z hα] at hδY
    exact (hcod' (by rw [hδY]; ring)).elim

variable (L : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hL : IsInvertibleModule (B := D.site) ⟨Y, hY.1⟩ L)
    (σ : MeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 L)

include hintX hintY in
/-- In Situation 0EDT let `X/B` and `Y/B` be good, let `f : X ⟶ Y` be a proper morphism, let `ℒ`
be an invertible `𝒪_Y`-module, assume `X` and `Y` integral, `f` dominant and
`dim_δ(X) = dim_δ(Y) = n`, and let `s` be a nonzero meromorphic section of `ℒ`. Then

`f_*(div_{f^*ℒ}(f^*s)) = [R(X) : R(Y)] div_ℒ(s)` in `Z_{n-1}(Y)`.

Here `f^*ℒ` is the inverse image `AlgebraicGeometry.Space.modulePullback` (invertible by
`AlgebraicGeometry.Space.modulePullbackInvertible`), `f^*s` is the pullback of meromorphic
sections, defined because `f` carries the generic point of `X` to the generic point of `Y`
(`AlgebraicGeometry.Space.pullbacksMeromorphicSections_of_genericPoint`, from dominance), and it
is nonzero because `f^*` preserves regular meromorphic sections; `div` is the Weil divisor of
Stacks 0EQE, part (1), at the canonical generators of Stacks 0EPR, `f_*` is proper pushforward
of cycles (Stacks 0EP2) and `[R(X) : R(Y)]` is the degree of the extension of function fields
(Stacks 0ENY). -/
@[stacks 0EQS "first conclusion: f_*(div_{f^*L}(f^*s)) = [R(X):R(Y)] div_L(s) in Z_{n-1}(Y),
for f : X → Y proper and dominant of good integral spaces with dim_δ X = dim_δ Y = n, L invertible
on Y, s a nonzero meromorphic section; f^*L, f^*s, div (0EQE (1) at the canonical generators of
0EPR), f_* and [R(X):R(Y)] all constructed; nothing carried", ega "IV 21.10.19" "special case"]
theorem properCyclePushforward_canonicalDivisorCycle_pullback {f : X ⟶ Y} (hfB : f ≫ sY = sX)
    (hf : IsProper D.site D.base D.base_mem f) (hdom : IsDominant D.site D.base D.base_mem f)
    {n : ℤ} (hnX : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (hnY : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (n : EInt)) (hσ : σ ≠ 0) :
    properCyclePushforward D sX hX sY hY hfB hf.2.1.2 (n - 1)
        (canonicalDivisorCycle D sX hX hintX
          ((modulePullback D.site D.base D.base_mem (goodSpacesHom D sX hX sY hY f)).obj L)
          (modulePullbackInvertible (goodSpacesHom D sX hX sY hY f) L hL)
          (pullbackMeromorphicSection D.site D.base D.base_mem (goodSpacesHom D sX hX sY hY f) L
            (pullbacksMeromorphicSections_of_genericPoint D.site D.base D.base_mem (Z := ⟨X, hX.1⟩)
              (Y := ⟨Y, hY.1⟩) hintX hintY f
              (pointsMap_genericPoint_of_isDominant D.site D.base D.base_mem hX.1 hY.1 hintX hintY
                f hdom)) σ)
          (isRegularMeromorphicSection_pullbackMeromorphicSection D.site D.base D.base_mem
            (goodSpacesHom D sX hX sY hY f)
            (pullbacksMeromorphicSections_of_genericPoint D.site D.base D.base_mem (Z := ⟨X, hX.1⟩)
              (Y := ⟨Y, hY.1⟩) hintX hintY f
              (pointsMap_genericPoint_of_isDominant D.site D.base D.base_mem hX.1 hY.1 hintX hintY
                f hdom)) L
            (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL) σ
            ((isRegularMeromorphicSection_iff_ne_zero D.site D.base D.base_mem hY.1 hintY
              (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY) L hL σ).2 hσ)) hnX) =
      (functionFieldDegreeAtGenericPoint D sX hX sY hY hintX f : ℤ) •
        canonicalDivisorCycle D sY hY hintY L hL σ
          ((isRegularMeromorphicSection_iff_ne_zero D.site D.base D.base_mem hY.1 hintY
            (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY) L hL σ).2 hσ) hnY := by
  have hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (((n - 1) + 1 : ℤ) : EInt) := by
    rwa [sub_add_cancel]
  exact properCyclePushforward_eq_zsmul_of_forall_primeDivisor D sX hX sY hY hintY hfB hf.2.1.2
    hk _ _ _ fun W => finsum_canonicalDivisorCycle_pullback_mul_properCycleMult_eq D sX hX sY hY
      hintX hintY L hL σ _ hfB hf hdom _ hnX hnY W

include hintX hintY in
/-- Stacks 0EQS, first conclusion, graded by `k` with `dim_δ = k + 1`: the identity
`f_*(div_{f^*ℒ}(f^*s)) = [R(X) : R(Y)] div_ℒ(s)` in `Z_k(Y)` for the cycles
`AlgebraicGeometry.Space.canonicalDivisorCycleAt`, which are
`AlgebraicGeometry.Space.canonicalDivisorCycle` graded by `k` rather than by `(k + 1) - 1`; the
pullback of meromorphic sections is taken along any witness `hPull` that it is defined, and the
section is any regular one. -/
theorem properCyclePushforward_canonicalDivisorCycleAt_pullback {f : X ⟶ Y}
    (hfB : f ≫ sY = sX) (hf : IsProper D.site D.base D.base_mem f)
    (hdom : IsDominant D.site D.base D.base_mem f)
    (hPull : PullbacksMeromorphicSections D.site D.base D.base_mem f)
    (hσ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 L σ) {k : ℤ}
    (hkX : deltaDimensionClosed D sX hX Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt))
    (hkY : deltaDimensionClosed D sY hY Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt)) :
    properCyclePushforward D sX hX sY hY hfB hf.2.1.2 k
        (canonicalDivisorCycleAt D sX hX hintX
          ((modulePullback D.site D.base D.base_mem (goodSpacesHom D sX hX sY hY f)).obj L)
          (modulePullbackInvertible (goodSpacesHom D sX hX sY hY f) L hL)
          (pullbackMeromorphicSection D.site D.base D.base_mem (goodSpacesHom D sX hX sY hY f) L
            hPull σ)
          (isRegularMeromorphicSection_pullbackMeromorphicSection D.site D.base D.base_mem
            (goodSpacesHom D sX hX sY hY f) hPull L
            (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL) σ hσ) hkX) =
      (functionFieldDegreeAtGenericPoint D sX hX sY hY hintX f : ℤ) •
        canonicalDivisorCycleAt D sY hY hintY L hL σ hσ hkY :=
  properCyclePushforward_eq_zsmul_of_forall_primeDivisor D sX hX sY hY hintY hfB hf.2.1.2 hkY _ _
    _ fun W => finsum_canonicalDivisorCycle_pullback_mul_properCycleMult_eq D sX hX sY hY hintX
      hintY L hL σ hσ hfB hf hdom hPull hkX hkY W

/-! ### The two conclusions in the vocabulary of Stacks 0EQE -/

include hX hY hintX hintY in
/-- A dominant morphism of integral algebraic spaces pulls back meromorphic sections. -/
theorem pullbacksMeromorphicSections_of_isDominant_of_isIntegralSpace {f : X ⟶ Y}
    (hdom : IsDominant D.site D.base D.base_mem f) :
    PullbacksMeromorphicSections D.site D.base D.base_mem f :=
  pullbacksMeromorphicSections_of_genericPoint D.site D.base D.base_mem (Z := ⟨X, hX.1⟩)
    (Y := ⟨Y, hY.1⟩) hintX hintY f
    (pointsMap_genericPoint_of_isDominant D.site D.base D.base_mem hX.1 hY.1 hintX hintY f hdom)

include hX hY hintX hintY hL in
/-- The pullback of a nonzero meromorphic section of an invertible module along a dominant
morphism of good integral algebraic spaces is nonzero. -/
theorem pullbackMeromorphicSection_ne_zero_of_isDominant {f : X ⟶ Y}
    (hdom : IsDominant D.site D.base D.base_mem f) (hσ : σ ≠ 0) :
    pullbackMeromorphicSection D.site D.base D.base_mem (goodSpacesHom D sX hX sY hY f) L
      (pullbacksMeromorphicSections_of_isDominant_of_isIntegralSpace D sX hX sY hY hintX hintY
        hdom) σ ≠ 0 :=
  (isRegularMeromorphicSection_iff_ne_zero D.site D.base D.base_mem hX.1 hintX
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) _
    (modulePullbackInvertible (goodSpacesHom D sX hX sY hY f) L hL) _).1
    (isRegularMeromorphicSection_pullbackMeromorphicSection D.site D.base D.base_mem
      (goodSpacesHom D sX hX sY hY f) _ L
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL) σ
      ((isRegularMeromorphicSection_iff_ne_zero D.site D.base D.base_mem hY.1 hintY
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY) L hL σ).2 hσ))

include hintX hintY in
/-- In Situation 0EDT let `X/B` and `Y/B` be good, let `f : X ⟶ Y` be a proper morphism, let `ℒ`
be an invertible `𝒪_Y`-module, assume `X` and `Y` integral, `f` dominant and
`dim_δ(X) = dim_δ(Y) = n`, and let `s` be a nonzero meromorphic section of `ℒ`. Then

`f_*(div_{f^*ℒ}(f^*s)) = [R(X) : R(Y)] div_ℒ(s)` as cycles on `Y`, in `Z_{n-1}(Y)`,

and in particular

`f_*(c₁(f^*ℒ) ∩ [X]) = c₁(ℒ) ∩ f_*[X]` in `CH_{n-1}(Y)`.

`div` is the Weil divisor `AlgebraicGeometry.Space.sectionWeilDivisor` of Stacks 0EQE, part
(1), `f^*ℒ` the inverse image `AlgebraicGeometry.Space.modulePullback`, `f^*s` the pullback of
meromorphic sections (defined by
`AlgebraicGeometry.Space.pullbacksMeromorphicSections_of_isDominant_of_isIntegralSpace` and
nonzero by `AlgebraicGeometry.Space.pullbackMeromorphicSection_ne_zero_of_isDominant`), `f_*`
proper pushforward of cycles (Stacks 0EP2) and `[R(X) : R(Y)]` the degree of the extension of
function fields (Stacks 0ENY).

In the second identity `c₁(f^*ℒ) ∩ [X]` is represented by the class of `div_{f^*ℒ}(f^*s)` in
`CH_{n-1}(X)` (Stacks 0EQE, part (2)), and `c₁(ℒ) ∩ f_*[X]` is written as
`[R(X) : R(Y)] (c₁(ℒ) ∩ [Y])`, since `f_*[X] = [R(X) : R(Y)] [Y]` (Stacks 0EP1), with
`c₁(ℒ) ∩ [Y]` the class `AlgebraicGeometry.Space.weilDivisorOfInvertibleSheaf`. -/
@[stacks 0EQS "both conclusions: f_*(div_{f^*L}(f^*s)) = [R(X):R(Y)] div_L(s) in Z_{n-1}(Y), and
f_*(c_1(f^*L) ∩ [X]) = c_1(L) ∩ f_*[X] = [R(X):R(Y)] (c_1(L) ∩ [Y]) in CH_{n-1}(Y), for f : X → Y
proper and dominant of good integral spaces with dim_δ X = dim_δ Y = n, L invertible on Y, s a
nonzero meromorphic section; div and c_1(-) ∩ [-] are Stacks 0EQE (1) and (2), f^*L, f^*s, f_*
and [R(X):R(Y)] constructed; the left side of the second identity is the class of the
pushforward of the cycle div_{f^*L}(f^*s) representing c_1(f^*L) ∩ [X]; nothing carried"]
theorem properCyclePushforward_sectionWeilDivisor_pullback (hL : IsInvertibleSheaf D sY hY L)
    {f : X ⟶ Y} (hfB : f ≫ sY = sX) (hf : IsProper D.site D.base D.base_mem f)
    (hdom : IsDominant D.site D.base D.base_mem f) {n : ℤ}
    (hnX : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (hnY : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (n : EInt)) (hσ : σ ≠ 0) :
    properCyclePushforward D sX hX sY hY hfB hf.2.1.2 (n - 1)
        (sectionWeilDivisor D sX hX hintX
          ((modulePullback D.site D.base D.base_mem (goodSpacesHom D sX hX sY hY f)).obj L)
          (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
            (modulePullbackInvertible (goodSpacesHom D sX hX sY hY f) L
              (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL))) hnX
          (pullbackMeromorphicSection D.site D.base D.base_mem (goodSpacesHom D sX hX sY hY f) L
            (pullbacksMeromorphicSections_of_isDominant_of_isIntegralSpace D sX hX sY hY hintX
              hintY hdom) σ)
          (pullbackMeromorphicSection_ne_zero_of_isDominant D sX hX sY hY hintX hintY L
            (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) σ hdom hσ)) =
        (functionFieldDegreeAtGenericPoint D sX hX sY hY hintX f : ℤ) •
          sectionWeilDivisor D sY hY hintY L hL hnY σ hσ ∧
      chowClass.{v} D sY hY (n - 1) (properCyclePushforward D sX hX sY hY hfB hf.2.1.2 (n - 1)
        (sectionWeilDivisor D sX hX hintX
          ((modulePullback D.site D.base D.base_mem (goodSpacesHom D sX hX sY hY f)).obj L)
          (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
            (modulePullbackInvertible (goodSpacesHom D sX hX sY hY f) L
              (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL))) hnX
          (pullbackMeromorphicSection D.site D.base D.base_mem (goodSpacesHom D sX hX sY hY f) L
            (pullbacksMeromorphicSections_of_isDominant_of_isIntegralSpace D sX hX sY hY hintX
              hintY hdom) σ)
          (pullbackMeromorphicSection_ne_zero_of_isDominant D sX hX sY hY hintX hintY L
            (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) σ hdom hσ))) =
        (functionFieldDegreeAtGenericPoint D sX hX sY hY hintX f : ℤ) •
          weilDivisorOfInvertibleSheaf.{v} D sY hY hintY L hL hnY := by
  have h1 := properCyclePushforward_canonicalDivisorCycle_pullback D sX hX sY hY hintX hintY L
    (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) σ hfB hf hdom hnX hnY hσ
  refine ⟨h1, (congrArg _ h1).trans ?_⟩
  rw [map_zsmul]
  exact congrArg _ (chowClass_sectionWeilDivisor D sY hY hintY L hL hnY σ hσ)

end Assembly

end AlgebraicGeometry.Space

end
