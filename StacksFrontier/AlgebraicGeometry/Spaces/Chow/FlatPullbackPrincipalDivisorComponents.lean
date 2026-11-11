module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatFibreChartColength
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatInverseImageDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatReadingHenselianNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.InverseImageDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardClosedImmersionSquare

/-!
# Flat pullback of a principal divisor

In Situation 0EDT let `X, Y/B` be good, assume `Y` integral with `dim_δ(Y) = k`, and let
`f : X ⟶ Y` be a flat morphism of relative dimension `r`. **Stacks 0EQA** says that for
`g ∈ R(Y)^*`

  `f^* div_Y(g) = ∑_{X'} m_{X', X} (X' → X)_* div_{X'}(g ∘ f|_{X'})`

as `(k + r - 1)`-cycles on `X`, the sum running over the irreducible components `X'` of `X` and
`m_{X', X}` being the multiplicity of `X'` in `X`. This file proves it.

Every object is the one of this chapter: the left-hand side is the flat pullback of Stacks 0EP8
(`AlgebraicGeometry.Space.flatPullbackMap`) of the principal divisor of Stacks 0EQ1 at the
canonical embeddings of Stacks 0ENK
(`AlgebraicGeometry.Space.rationalFunctionPrincipalDivisorCycle`);
on the right, `X'` runs over `AlgebraicGeometry.Space.IrreducibleComponentSubspace`, `g ∘ f|_{X'}`
is the image of `g` under the extension of function fields of the dominant morphism `f|_{X'}`
(Morphisms of Spaces, Section 0EML), its principal divisor is again the one of Stacks 0EQ1 on
`X'`, which has δ-dimension `k + r` by Stacks 0EP5, the pushforward is the proper pushforward of
Stacks 0EP1 along the inclusion, and `m_{X', X}` is the length of `𝒪_X` at the generic point of
`X'` (Stacks 0EE9, part (1), for the space `X` itself,
`AlgebraicGeometry.Space.spaceMultiplicity`). The family of components is only locally finite,
so the right-hand side is the cycle whose coefficient at each integral closed subspace is the
(finite) sum of the coefficients of the terms, and the identity is the identity of the
coefficients at every integral closed subspace of `X`.

## The proof

Fix an integral closed subspace `Z ⊆ X`. Both sides are `(k + r - 1)`-cycles, so only
`dim_δ(Z) = k + r - 1` needs an argument; then `Z` is a prime divisor of `X`
(`AlgebraicGeometry.Space.exists_primeDivisor_toIntegralClosedSubspace_eq_of_isFlat`), since the
δ-function is at most `k + r` on a flat source and equals `k + r` at the generic points of its
components. Let `ξ` be its generic point and `B = 𝒪^h_{X, ξ}`.

* **The right-hand side** at `Z` is `ord_B(ĝ)`, `ĝ` being the reading of `g` in `Q(B)`: the terms
  of the components not through `ξ` vanish, and over the components through `ξ` this is the
  additivity of the order of vanishing over the branches of `B` grouped by components, with the
  multiplicities `m_{X', X}` as the lengths at the branches
  (`AlgebraicGeometry.Space.exists_natCast_ord_sub_eq_finsum_components_mul_ordRationalFunction`,
  the Stacks 02QG argument, here applied to `X` itself).
* **The left-hand side** at `Z` is `∑_W ord_W(g) · m_{Z, f^{-1}(W)}`, and a term is nonzero only if
  `f(ξ)` is the generic point of `W`, the δ-function growing by at most `r` along `f`. The
  δ-value of `f(ξ)` is `k` or `k - 1`. If it is `k`, then `f(ξ)` is the generic point of `Y`, the
  left-hand side vanishes, and so does `ord_B(ĝ)`, the reading being a quotient of two units
  (`AlgebraicGeometry.Space.PrimeDivisor.natCast_ord_sub_eq_zero_of_pointsMap_eq_genericPoint`).
  If it is `k - 1`, the closure of `f(ξ)` is a prime divisor `W` of `Y`, the left-hand side is
  `ord_W(g) · m_{Z, f^{-1}(W)}`, and `ord_B(ĝ) = m · ord_W(g)` by Stacks 02M1 along the flat local
  homomorphism `𝒪^h_{Y, f(ξ)} → B` that `f` induces, the colength `m` being computed on a square of
  étale charts and identified there with `m_{Z, f^{-1}(W)}`
  (`AlgebraicGeometry.Space.PrimeDivisor.exists_natCast_ord_sub_eq_length_mul_ordRationalFunction`,
  `AlgebraicGeometry.Space.flatPullbackMult_eq_toNat_length_of_neighborhoods`).

This is the source's identity read at `Z` directly, rather than through its reduction to the étale
case Stacks 0EQ2 and the case of schemes Stacks 0EPH: the henselian local ring `𝒪^h_{X, ξ}` plays
the part of the étale chart `U` of the source, and the two multiplicities the source compares
through Lemma 0EPY are compared here on one chart.

## Main results

* `Space.flatPullbackMap_rationalFunctionPrincipalDivisorCycle_eq_finsum_components`:
  **Stacks 0EQA**.
* `AlgebraicGeometry.Space.IrreducibleComponentSubspace.deltaDimensionClosed_univ_of_isFlat`:
  every irreducible component of `X` has δ-dimension `k + r` (Stacks 0EP5).
* `AlgebraicGeometry.Space.IrreducibleComponentSubspace.flatPullbackRationalFunction` and
  `AlgebraicGeometry.Space.IrreducibleComponentSubspace.flatPullbackDivisorPushforward`:
  `g ∘ f|_{X'}` and `(X' → X)_* div_{X'}(g ∘ f|_{X'})`.

## References

* [Stacks Project, Tag 0EQA](https://stacks.math.columbia.edu/tag/0EQA)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0EML](https://stacks.math.columbia.edu/tag/0EML)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 0EP5](https://stacks.math.columbia.edu/tag/0EP5)
* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 0EPZ](https://stacks.math.columbia.edu/tag/0EPZ)
* [Stacks Project, Tag 0EQ1](https://stacks.math.columbia.edu/tag/0EQ1)
* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1)
* [Stacks Project, Tag 02QG](https://stacks.math.columbia.edu/tag/02QG)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace IsLocalRing
open scoped nonZeroDivisors

universe u

/-! ### Codimension one from a dimension function bounded above -/

/-- **A point one below the maximum of a dimension function, with a proper generalization, has
codimension one.** On a sober space carrying a dimension function `δ` with `δ ≤ n` everywhere,
the closure of a point `x` with `δ x = n - 1` which is not a generic point has codimension one:
a point strictly generalizing `x` has `δ`-value `n`, so it has no proper generalization itself. -/
theorem codimension_closureSingleton_eq_one_of_dimensionFunction_le {α : Type*}
    [TopologicalSpace α] [QuasiSober α] [T0Space α] (δ : DimensionFunction α) {n : ℤ}
    (hle : ∀ y, δ y ≤ n) (x : α) (hx : δ x = n - 1) (hgen : ∃ y, y ⤳ x ∧ y ≠ x) :
    codimension (IrreducibleCloseds.closureSingleton x) = 1 := by
  let _ := specializationOrder α
  have hxset : irreducibleSetEquivPoints (IrreducibleCloseds.closureSingleton x) = x := by
    have h : IrreducibleCloseds.closureSingleton x = irreducibleSetEquivPoints.symm x :=
      IrreducibleCloseds.ext rfl
    rw [h, OrderIso.apply_symm_apply]
  rw [codimension_eq_coheight, ← Order.coheight_orderIso irreducibleSetEquivPoints, hxset]
  obtain ⟨y, hyx, hne⟩ := hgen
  have hlt : x < y := lt_of_le_of_ne hyx (Ne.symm hne)
  refine le_antisymm ?_ ?_
  · refine Order.coheight_le_coe_iff.mpr fun z hz => ?_
    have hmax : IsMax z := by
      intro w hw
      by_contra hwz
      have h1 : δ x < δ z := δ.strictAnti_specializes hz.le (ne_of_gt hz)
      have h2 : δ z < δ w := δ.strictAnti_specializes hw (Ne.symm (fun h => hwz (h ▸ le_rfl)))
      have h3 := hle w
      omega
    rw [Order.coheight_eq_zero.mpr hmax]
    simp
  · have hstep := Order.coheight_add_one_le hlt
    exact le_trans (by simp) hstep

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)

/-! ### The δ-function along a morphism of relative dimension `r` -/

include hX hY hbase hr in
/-- Along a morphism of relative dimension `r` the δ-function grows by at most `r`. -/
theorem deltaValue_le_add_of_hasRelativeDimension (x : points D.site D.base D.base_mem X) :
    D.deltaValue sX x ≤ D.deltaValue sY (pointsMap D.site D.base D.base_mem X f x) + r :=
  inducedDimensionValue_le_add_of_hasRelativeDimension D sX hX sY hY f hbase r hr x

include hX hY hbase hr in
/-- **At a generic point of an irreducible component the δ-function grows by exactly `r`.** The
local ring of the fibre there has dimension zero (Stacks 0ABV), so the transcendence degree of
the residue field extension is the whole relative dimension, and the δ-function of Situation
0EDT is the δ-function of the base plus that transcendence degree. -/
theorem deltaValue_eq_add_of_mem_genericPoints (x : points D.site D.base D.base_mem X)
    (hx : x ∈ genericPoints (points D.site D.base D.base_mem X)) :
    D.deltaValue sX x = D.deltaValue sY (pointsMap D.site D.base D.base_mem X f x) + r := by
  have hfft : IsLocallyOfFiniteType D.site D.base D.base_mem f :=
    isLocallyOfFiniteType_of_comp D.site D.base D.base_mem hX.1 hY.1 D.isAlgebraicSpace f sY
      (by rw [hbase]; exact hX.2.2)
  have hfib0 := hasFiberLocalRingDimension_zero_of_mem_genericPoints D.site D.base D.base_mem
    hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) f x hx
  obtain ⟨a, ha⟩ := exists_finite_transcendenceDegreeAt D.site D.base D.base_mem f hfft x
  have hsum := relativeDimensionAt_eq_fiberLocalRingDimension_add_transcendenceDegreeAt
    D.site D.base D.base_mem hX.1 hY.1 f x hfft (r : ℕ∞) 0 (a : ℕ∞) (hr x) hfib0 ha
  have har : a = r := by
    have hra : ((r : ℕ) : ℕ∞) = ((a : ℕ) : ℕ∞) := by simpa using hsum
    exact_mod_cast hra.symm
  obtain ⟨b, hb⟩ := exists_finite_transcendenceDegreeAt D.site D.base D.base_mem sY hY.2.2
    (pointsMap D.site D.base D.base_mem X f x)
  have hcomp : HasTranscendenceDegreeAt D.site D.base D.base_mem sX x ((a + b : ℕ) : ℕ∞) := by
    rw [← hbase]
    simpa only [Nat.cast_add] using hasTranscendenceDegreeAt_comp D.site D.base D.base_mem
      hX.1 hY.1 D.isAlgebraicSpace f sY x (a : ℕ∞) (b : ℕ∞) ha hb
  have hXval := inducedDimensionValue_eq D.site D.base D.base_mem hX.1 D.isAlgebraicSpace
    D.delta.toFun sX hX.2.2 x ((a + b : ℕ) : ℕ∞) hcomp
  have hYval := inducedDimensionValue_eq D.site D.base D.base_mem hY.1 D.isAlgebraicSpace
    D.delta.toFun sY hY.2.2 (pointsMap D.site D.base D.base_mem X f x) (b : ℕ∞) hb
  have himg : pointsMap D.site D.base D.base_mem X sX x =
      pointsMap D.site D.base D.base_mem Y sY
        (pointsMap D.site D.base D.base_mem X f x) := by
    rw [← hbase, pointsMap_comp_apply]
  change inducedDimensionValue D.site D.base D.base_mem D.delta.toFun sX x =
    inducedDimensionValue D.site D.base D.base_mem D.delta.toFun sY
      (pointsMap D.site D.base D.base_mem X f x) + (r : ℤ)
  rw [hXval, hYval, himg, ← har]
  simp only [ENat.toNat_natCast]
  omega

/-! ### The irreducible components of a flat source -/

section Components

variable (hflat : IsFlat D.site D.base D.base_mem f)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y)

/-- The δ-function of a good integral algebraic space at its generic point is its
δ-dimension. -/
theorem deltaValue_genericPoint_eq_of_deltaDimensionClosed {k : ℤ}
    (hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (k : EInt)) :
    D.deltaValue sY (genericPoint D.site D.base D.base_mem hY.1 hintY) = k := by
  have h := deltaDimensionClosed_univ_eq_deltaValue_genericPoint D sY hY hintY
  rw [hk] at h
  exact (WithBotTop.coe_injective h).symm

/-- The generic point of an irreducible component of `X`, as a point of `|X|`, is a generic
point of `|X|`. -/
theorem IrreducibleComponentSubspace.ambientGenericPoint_mem_genericPoints
    (W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1) :
    W.1.ambientGenericPoint D.site D.base D.base_mem ∈
      genericPoints (points D.site D.base D.base_mem X) := by
  change closure {W.1.ambientGenericPoint D.site D.base D.base_mem} ∈
    irreducibleComponents (points D.site D.base D.base_mem X)
  rw [(W.1.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hX.1).def]
  exact W.2.2.2

include hflat in
/-- The generic point of an irreducible component of a flat source maps to the generic point of
the integral target (the dominance clause of Stacks 0EP5, as carried in
`pointsMap_genericPoint_eq_genericPoint_irreducibleComponentSubspace_of_isFlat`). -/
theorem IrreducibleComponentSubspace.pointsMap_ambientGenericPoint_of_isFlat
    (W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1) :
    pointsMap D.site D.base D.base_mem X f (W.1.ambientGenericPoint D.site D.base D.base_mem) =
      genericPoint D.site D.base D.base_mem hY.1 hintY :=
  (congrFun (pointsMap_comp D.site D.base D.base_mem W.1.subspace.toFunctor W.1.subspace.ι
    f) _).symm.trans
    (pointsMap_genericPoint_eq_genericPoint_irreducibleComponentSubspace_of_isFlat D sX hX sY hY
      hflat hintY W.1 W.2.2.2)

include hbase hr hflat hintY in
/-- The δ-function at the generic point of an irreducible component of `X` is `dim_δ(Y) + r`. -/
theorem IrreducibleComponentSubspace.deltaValue_ambientGenericPoint_of_isFlat {k : ℤ}
    (hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (k : EInt))
    (W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1) :
    D.deltaValue sX (W.1.ambientGenericPoint D.site D.base D.base_mem) = k + r := by
  rw [deltaValue_eq_add_of_mem_genericPoints D sX hX sY hY f hbase r hr _
      (W.ambientGenericPoint_mem_genericPoints D sX hX),
    W.pointsMap_ambientGenericPoint_of_isFlat D sX hX sY hY f hflat hintY,
    deltaValue_genericPoint_eq_of_deltaDimensionClosed D sY hY hintY hk]

include hbase hr hflat hintY in
/-- **Every irreducible component of a flat source of relative dimension `r` over an integral
`Y` has δ-dimension `dim_δ(Y) + r`** (Stacks 0EP5). This is what makes
`div_{X'}(g ∘ f|_{X'})` a `(k + r - 1)`-cycle. -/
theorem IrreducibleComponentSubspace.deltaDimensionClosed_univ_of_isFlat {k : ℤ}
    (hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (k : EInt))
    (W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1) :
    deltaDimensionClosed D (W.1.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W.1)
        Set.univ isClosed_univ = ((k + r : ℤ) : EInt) := by
  rw [deltaDimensionClosed_univ_eq_deltaValue_genericPoint D (W.1.subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX W.1) W.1.isIntegralSpace,
    D.deltaValue_comp_of_isLocallyQuasiFinite W.1.isClosedSubspace.1 hX.1 W.1.subspace.ι sX
      (isLocallyQuasiFinite_of_isImmersion D.site D.base D.base_mem W.1.subspace.ι
        (isImmersion_of_isClosedImmersion D.site D.base D.base_mem W.1.isClosedSubspace.2))
      hX.2.2]
  exact congrArg (fun n : ℤ => (n : EInt))
    (W.deltaValue_ambientGenericPoint_of_isFlat D sX hX sY hY f hbase r hr hflat hintY hk)

/-- **`g ∘ f|_{X'}` ∈ `R(X')^*`.** The pullback of an invertible rational function of `Y` to an
irreducible component `X'` of a flat source: its image under the extension of function fields
`R(Y) → R(X')` of the dominant morphism `f|_{X'}` (Morphisms of Spaces, Section 0EML). -/
def IrreducibleComponentSubspace.flatPullbackRationalFunction
    (W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1)
    (g : (rationalFunctions D.site D.base D.base_mem hY.1)ˣ) :
    (rationalFunctions D.site D.base D.base_mem
      (isGood_integralClosedSubspace D sX hX W.1).1)ˣ :=
  Units.map (rationalFunctionMap D.site D.base D.base_mem
    (isGood_integralClosedSubspace D sX hX W.1).1 hY.1 W.1.isIntegralSpace hintY
    (W.1.subspace.ι ≫ f)
    (pointsMap_genericPoint_eq_genericPoint_irreducibleComponentSubspace_of_isFlat D sX hX sY hY
      hflat hintY W.1 W.2.2.2)).toMonoidHom g

/-- **`(X' → X)_* div_{X'}(g ∘ f|_{X'})`**, the pushforward along the inclusion of an
irreducible component `X'` of `X` (Stacks 0EP1) of the principal divisor (Stacks 0EQ1) of the
pullback of `g` to `X'`, as a `(k + r - 1)`-cycle on `X`. -/
def IrreducibleComponentSubspace.flatPullbackDivisorPushforward {k : ℤ}
    (hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (k : EInt))
    (W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1)
    (g : (rationalFunctions D.site D.base D.base_mem hY.1)ˣ) :
    CycleGroup D sX (k + r - 1) :=
  properCyclePushforward D (W.1.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W.1)
    sX hX (f := W.1.subspace.ι) rfl
    (isQuasiCompact_of_isClosedImmersion' D.site D.base D.base_mem W.1.isClosedSubspace.2)
    (k + r - 1)
    (rationalFunctionPrincipalDivisorCycle D (W.1.subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX W.1) W.1.isIntegralSpace
      (W.deltaDimensionClosed_univ_of_isFlat D sX hX sY hY f hbase r hr hflat hintY hk)
      (W.flatPullbackRationalFunction D sX hX sY hY f hflat hintY g))

end Components

/-! ### Integral closed subspaces and prime divisors of a flat source -/

section PrimeDivisors

variable (hflat : IsFlat D.site D.base D.base_mem f)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y)

/-- An integral closed subspace of a decent algebraic space is determined by its generic
point. -/
theorem IntegralClosedSubspace.eq_of_ambientGenericPoint_eq
    {T : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace D.site D.base D.base_mem T)
    {W W' : IntegralClosedSubspace D.site D.base D.base_mem T}
    (h : W.ambientGenericPoint D.site D.base D.base_mem =
      W'.ambientGenericPoint D.site D.base D.base_mem) : W = W' := by
  refine injective_integralClosedSubspaceSupport D.site D.base D.base_mem hT
    (IrreducibleCloseds.ext ?_)
  change subspacePointSet D.site D.base D.base_mem T W.subspace =
    subspacePointSet D.site D.base D.base_mem T W'.subspace
  rw [← (W.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hT).def,
    ← (W'.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hT).def, h]

/-- The irreducible component subspace cutting out an irreducible component of `|X|`. -/
def IrreducibleComponentSubspace.ofComponent
    (C : irreducibleComponents (points D.site D.base D.base_mem X)) :
    IrreducibleComponentSubspace D.site D.base D.base_mem hX.1 :=
  ⟨integralClosedSubspaceOfComponent D.site D.base D.base_mem hX.1
      (D.isDecentSpace_of_isGood sX hX) C,
    (integralClosedSubspaceOfComponent D.site D.base D.base_mem hX.1
      (D.isDecentSpace_of_isGood sX hX) C).isClosedSubspace,
    (integralClosedSubspaceOfComponent D.site D.base D.base_mem hX.1
      (D.isDecentSpace_of_isGood sX hX) C).isIntegralSpace,
    by
      change subspacePointSet D.site D.base D.base_mem X _ ∈ _
      rw [subspacePointSet_integralClosedSubspaceOfComponent D.site D.base D.base_mem hX.1
        (D.isDecentSpace_of_isGood sX hX) C]
      exact C.2⟩

/-- The point set of the irreducible component subspace attached to a component is that
component. -/
theorem IrreducibleComponentSubspace.subspacePointSet_ofComponent
    (C : irreducibleComponents (points D.site D.base D.base_mem X)) :
    subspacePointSet D.site D.base D.base_mem X
        (IrreducibleComponentSubspace.ofComponent D sX hX C).1.subspace = C.1 :=
  subspacePointSet_integralClosedSubspaceOfComponent D.site D.base D.base_mem hX.1
    (D.isDecentSpace_of_isGood sX hX) C

/-- The δ-dimension of an integral closed subspace is the δ-value at its ambient generic point. -/
private theorem deltaDimension_eq_deltaValue_ambientGenericPoint
    (hX' : IsAlgebraicSpace D.site D.base D.base_mem X)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    deltaDimension D sX Z = D.deltaValue sX (Z.ambientGenericPoint D.site D.base D.base_mem) :=
  deltaDimension_eq_of_isGenericPoint D sX hX' Z _
    (Z.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hX')

/-- The δ-function strictly drops along a proper specialization. -/
private theorem deltaValue_lt_of_specializes (hX : D.IsGood sX)
    {x y : points D.site D.base D.base_mem X} (hxy : x ⤳ y) (hne : x ≠ y) :
    D.deltaValue sX y < D.deltaValue sX x := by
  obtain ⟨d, hd⟩ := exists_dimensionFunction_deltaValue_of_isGood D sX hX
  have hlt := d.strictAnti_specializes hxy hne
  rwa [hd, hd] at hlt

/-- Every point of `|X|` is a specialization of the generic point of an irreducible component. -/
private theorem exists_ambientGenericPoint_specializes (hX : D.IsGood sX)
    (y : points D.site D.base D.base_mem X) :
    ∃ W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1,
      W.1.ambientGenericPoint D.site D.base D.base_mem ⤳ y := by
  obtain ⟨C, hC, hyC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    ({y} : Set (points D.site D.base D.base_mem X)) isIrreducible_singleton
  have hgen := (IrreducibleComponentSubspace.ofComponent D sX hX ⟨C, hC⟩).1
    |>.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hX.1
  rw [IrreducibleComponentSubspace.subspacePointSet_ofComponent D sX hX ⟨C, hC⟩] at hgen
  exact ⟨_, hgen.specializes (hyC rfl)⟩

include hX hY hbase hr hflat hintY in
/-- **On a flat source the δ-function is at most `dim_δ(Y) + r`.** Every point specializes from
the generic point of an irreducible component, where the δ-function is `dim_δ(Y) + r`, and the
δ-function drops along a specialization. -/
theorem deltaValue_le_add_of_isFlat {k : ℤ}
    (hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (k : EInt))
    (y : points D.site D.base D.base_mem X) : D.deltaValue sX y ≤ k + r := by
  obtain ⟨W, hspec⟩ := exists_ambientGenericPoint_specializes D sX hX y
  rw [← W.deltaValue_ambientGenericPoint_of_isFlat D sX hX sY hY f hbase r hr hflat hintY hk]
  by_cases h : W.1.ambientGenericPoint D.site D.base D.base_mem = y
  · rw [h]
  · exact (deltaValue_lt_of_specializes D sX hX hspec h).le

include hX hY hbase hr hflat hintY in
/-- **An integral closed subspace of a flat source of δ-dimension `dim_δ(Y) + r - 1` is a prime
divisor.** Its generic point `ξ` has codimension one: the δ-function is at most `dim_δ(Y) + r`
on `|X|`, the generic point of an irreducible component through `ξ` has δ-value
`dim_δ(Y) + r`, so it is a proper generalization of `ξ`, and a dimension function with these
properties gives codimension one. -/
theorem exists_primeDivisor_toIntegralClosedSubspace_eq_of_isFlat {k : ℤ}
    (hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (k : EInt))
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : deltaDimension D sX Z = k + r - 1) :
    ∃ P : PrimeDivisor D.site D.base D.base_mem X,
      P.toIntegralClosedSubspace D.site D.base D.base_mem = Z ∧
        P.genericPoint D.site D.base D.base_mem X = Z.ambientGenericPoint D.site D.base D.base_mem
        := by
  have _hsober : QuasiSober (points D.site D.base D.base_mem X) :=
    quasiSober_points_of_isGood D sX hX
  have _ht0 : T0Space (points D.site D.base D.base_mem X) :=
    t0Space_points_of_isDecentSpace D.site D.base D.base_mem hX.1
      (D.isDecentSpace_of_isGood sX hX)
  have hξ := Z.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hX.1
  have hδξ : D.deltaValue sX (Z.ambientGenericPoint D.site D.base D.base_mem) = k + r - 1 :=
    (deltaDimension_eq_deltaValue_ambientGenericPoint D sX hX.1 Z).symm.trans hZ
  obtain ⟨d, hd⟩ := exists_dimensionFunction_deltaValue_of_isGood D sX hX
  obtain ⟨W, hspec⟩ := exists_ambientGenericPoint_specializes D sX hX
    (Z.ambientGenericPoint D.site D.base D.base_mem)
  have hδη := W.deltaValue_ambientGenericPoint_of_isFlat D sX hX sY hY f hbase r hr hflat hintY hk
  have hcodim : codimension (IrreducibleCloseds.closureSingleton
      (Z.ambientGenericPoint D.site D.base D.base_mem)) = 1 := by
    refine codimension_closureSingleton_eq_one_of_dimensionFunction_le d (n := k + r)
      (fun y => (hd y).symm ▸ deltaValue_le_add_of_isFlat D sX hX sY hY f hbase r hr hflat
        hintY hk y) _ (by rw [hd, hδξ]) ⟨_, hspec, fun h => ?_⟩
    rw [h, hδξ] at hδη
    omega
  exact ⟨⟨Z.subspace, Z.isClosedSubspace, Z.isIntegralSpace,
    ⟨Z.ambientGenericPoint D.site D.base D.base_mem, hξ, hcodim⟩⟩, rfl,
    (PrimeDivisor.isGenericPoint_genericPoint D.site D.base D.base_mem X _).eq hξ⟩

end PrimeDivisors

/-! ### The two sides at one integral closed subspace -/

section Coefficients

variable (hflat : IsFlat D.site D.base D.base_mem f)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y)

/-- The distinguished point of an elementary étale neighbourhood of `x` lies over `x`. -/
theorem ElementaryEtaleNeighborhood.chartSchemeToPoints_chart_point
    {T : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    {hT : IsAlgebraicSpace D.site D.base D.base_mem T} {x : points D.site D.base D.base_mem T}
    (U : ElementaryEtaleNeighborhood D.site D.base D.base_mem T hT x) :
    chartSchemeToPoints D.site D.base D.base_mem T U.chart U.point = x := by
  refine (chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm D.site D.base D.base_mem T _
    _).trans ?_
  have h : (pointsEquivScheme D.site D.base D.base_mem U.scheme).symm U.point =
      presheafPoint D.site D.base D.base_mem _ U.point U.residueField_contained :=
    (Equiv.symm_apply_eq _).2 (pointsToScheme_presheafPoint D.site D.base D.base_mem _ _ _).symm
  refine Eq.trans ?_ U.map_point
  exact congrArg (pointsMap D.site D.base D.base_mem (yoneda.obj U.scheme) U.toSpace) h

include hbase hr in
/-- An integral closed subspace of `X` occurring in the flat pullback `f^*[W]` has its generic
point over the generic point of `W`: it lies over a point of `W`, and a proper specialization
of the generic point of `W` would have too small a δ-value, the δ-function growing by at most
`r` along `f`. -/
theorem pointsMap_ambientGenericPoint_eq_of_flatPullbackMult_ne_zero
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (h : flatPullbackMult D sX hX sY hY f hbase r hflat hr W Z ≠ 0) :
    pointsMap D.site D.base D.base_mem X f (Z.ambientGenericPoint D.site D.base D.base_mem) =
      W.ambientGenericPoint D.site D.base D.base_mem := by
  have hmem := mem_subspacePointSet_of_flatPullbackMult_ne_zero D sX hX sY hY f hbase r hflat hr
    W Z h
  have hdim := deltaDimension_eq_of_flatPullbackMult_ne_zero D sX hX sY hY f hbase r hflat hr W Z
    h
  rw [deltaDimension_eq_deltaValue_ambientGenericPoint D sX hX.1 Z,
    deltaDimension_eq_deltaValue_ambientGenericPoint D sY hY.1 W] at hdim
  have hle := deltaValue_le_add_of_hasRelativeDimension D sX hX sY hY f hbase r hr
    (Z.ambientGenericPoint D.site D.base D.base_mem)
  by_contra hne
  have hlt := deltaValue_lt_of_specializes D sY hY
    ((W.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hY.1).specializes hmem)
    (Ne.symm hne)
  omega

include hbase hr in
/-- **The multiplicity of the flat pullback of a prime cycle, as a colength on a square of
elementary étale neighbourhoods** — the form in which
`AlgebraicGeometry.Space.PrimeDivisor.exists_natCast_ord_sub_eq_length_mul_ordRationalFunction`
produces it. This is
`AlgebraicGeometry.Space.flatPullbackMult_eq_toNat_length_chartStalk` at the integral closed
subspace of `f^{-1}(W)` whose image is `Z`. -/
theorem flatPullbackMult_eq_toNat_length_of_neighborhoods
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : pointsMap D.site D.base D.base_mem X f (Z.ambientGenericPoint D.site D.base D.base_mem) =
      W.ambientGenericPoint D.site D.base D.base_mem)
    (hdim : deltaDimension D sX Z = deltaDimension D sY W + r)
    {x : points D.site D.base D.base_mem X}
    (hx : x = Z.ambientGenericPoint D.site D.base D.base_mem)
    (U : ElementaryEtaleNeighborhood D.site D.base D.base_mem X hX.1 x)
    {y : points D.site D.base D.base_mem Y}
    (V : ElementaryEtaleNeighborhood D.site D.base D.base_mem Y hY.1 y)
    (j : U.scheme ⟶ V.scheme) (hsq : yoneda.map j ≫ V.toSpace = U.toSpace ≫ f) :
    flatPullbackMult D sX hX sY hY f hbase r hflat hr W Z =
      ((Module.length (U.scheme.left.1.presheaf.stalk U.point)
        (U.scheme.left.1.presheaf.stalk U.point ⧸
          Ideal.map (j.left.1.stalkMap U.point).hom
            (maximalIdeal (V.scheme.left.1.presheaf.stalk (j.left.1 U.point))))).toNat : ℤ) := by
  subst hx
  have hpre := isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W
  have hsub : subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆
      Set.range (pointsMap D.site D.base D.base_mem _ (W.subspace.preimage f).ι) := by
    change _ ⊆ subspacePointSet D.site D.base D.base_mem X (W.subspace.preimage f)
    rw [subspacePointSet_preimage, ← (Z.isGenericPoint_ambientGenericPoint D.site D.base
      D.base_mem hX.1).def]
    refine closure_minimal (Set.singleton_subset_iff.mpr ?_)
      ((isClosed_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem hY.1 W).preimage
        (continuous_pointsMap D.site D.base D.base_mem f))
    change pointsMap D.site D.base D.base_mem X f _ ∈
      Set.range (pointsMap D.site D.base D.base_mem W.subspace.toFunctor W.subspace.ι)
    rw [hZ]
    exact (W.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hY.1).mem
  obtain ⟨Vs, hVs⟩ := IntegralClosedSubspace.exists_pushforward_eq D.site D.base D.base_mem hX.1
    hpre.1 (D.isDecentSpace_of_isGood sX hX)
    (isDecentSpace_of_isClosedSubspace D.site D.base D.base_mem (D.isDecentSpace_of_isGood sX hX)
      hpre) hpre.2 Z hsub
  have hagp : pointsMap D.site D.base D.base_mem _ (W.subspace.preimage f).ι
      (Vs.ambientGenericPoint D.site D.base D.base_mem) =
      Z.ambientGenericPoint D.site D.base D.base_mem := by
    rw [← hVs, IntegralClosedSubspace.ambientGenericPoint_pushforward]
  have key := flatPullbackMult_eq_toNat_length_chartStalk D sX hX sY hY f hbase r hflat hr W Vs
    (by rw [show closedSubspaceComponentImage D sX hX (W.subspace.preimage f) hpre Vs = Z from hVs]
        exact hdim)
    (canonicalGeometricPoint D.site D.base D.base_mem _
      (Vs.ambientGenericPoint D.site D.base D.base_mem))
    (canonicalGeometricPoint_image D.site D.base D.base_mem _ _)
    (by rw [hagp, hZ]) U.chart V.chart j hsq.symm U.point
    (by rw [ElementaryEtaleNeighborhood.chartSchemeToPoints_chart_point, geometricPointMap_image,
          canonicalGeometricPoint_image, hagp])
  rw [show closedSubspaceComponentImage D sX hX (W.subspace.preimage f) hpre Vs = Z from hVs]
    at key
  exact key

/-- A term of the right-hand side vanishes at an integral closed subspace whose generic point
does not lie on the component: such a subspace is the image of no integral closed subspace of
the component. -/
theorem IrreducibleComponentSubspace.flatPullbackDivisorPushforward_apply_of_notMem {k : ℤ}
    (hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (k : EInt))
    (W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1)
    (g : (rationalFunctions D.site D.base D.base_mem hY.1)ˣ)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : Z.ambientGenericPoint D.site D.base D.base_mem ∉
      subspacePointSet D.site D.base D.base_mem X W.1.subspace) :
    (W.flatPullbackDivisorPushforward D sX hX sY hY f hbase r hr hflat hintY hk g).1 Z = 0 := by
  change properCyclePushforwardCoeff D (W.1.subspace.ι ≫ sX)
    (isGood_integralClosedSubspace D sX hX W.1) sX hX W.1.subspace.ι _ Z = 0
  rw [properCyclePushforwardCoeff_ι_eq_cycleClosedPushforward D sX hX W.1]
  refine cycleClosedPushforward_apply_of_forall_ne D hX.1 W.1.isClosedSubspace.1
    (D.isDecentSpace_of_isGood sX hX) W.1.isClosedSubspace.2 _ Z fun V hV => hZ ?_
  rw [← hV, IntegralClosedSubspace.ambientGenericPoint_pushforward]
  exact ⟨_, rfl⟩

/-- A term of the right-hand side at an integral closed subspace `Z` whose generic point is the
image of the generic point of a prime divisor `P` of the component is the order of vanishing of
`g ∘ f|_{X'}` along `P`. -/
theorem IrreducibleComponentSubspace.flatPullbackDivisorPushforward_apply_eq_ord {k : ℤ}
    (hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (k : EInt))
    (W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1)
    (g : (rationalFunctions D.site D.base D.base_mem hY.1)ˣ)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (P : PrimeDivisor D.site D.base D.base_mem W.1.subspace.toFunctor)
    (hP : pointsMap D.site D.base D.base_mem W.1.subspace.toFunctor W.1.subspace.ι
        (P.genericPoint D.site D.base D.base_mem W.1.subspace.toFunctor) =
      Z.ambientGenericPoint D.site D.base D.base_mem) :
    (W.flatPullbackDivisorPushforward D sX hX sY hY f hbase r hr hflat hintY hk g).1 Z =
      (canonicalGenericFractionEmbedding D (W.1.subspace.ι ≫ sX)
        (isGood_integralClosedSubspace D sX hX W.1) W.1.isIntegralSpace).ord
        (W.flatPullbackRationalFunction D sX hX sY hY f hflat hintY g) P := by
  have _ht0 : T0Space (points D.site D.base D.base_mem W.1.subspace.toFunctor) :=
    t0Space_points_of_isDecentSpace D.site D.base D.base_mem W.1.isClosedSubspace.1
      W.1.isIntegralSpace.isDecentSpace
  have hgP : (P.toIntegralClosedSubspace D.site D.base D.base_mem).ambientGenericPoint D.site
      D.base D.base_mem = P.genericPoint D.site D.base D.base_mem W.1.subspace.toFunctor :=
    ((P.toIntegralClosedSubspace D.site D.base D.base_mem).isGenericPoint_ambientGenericPoint
      D.site D.base D.base_mem W.1.isClosedSubspace.1).eq
      (P.isGenericPoint_genericPoint D.site D.base D.base_mem W.1.subspace.toFunctor)
  have hZ : IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1
      W.1.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX) W.1.isClosedSubspace.2
      (P.toIntegralClosedSubspace D.site D.base D.base_mem) = Z :=
    IntegralClosedSubspace.eq_of_ambientGenericPoint_eq D hX.1 (by
      rw [IntegralClosedSubspace.ambientGenericPoint_pushforward, hgP, hP])
  subst hZ
  change properCyclePushforwardCoeff D (W.1.subspace.ι ≫ sX)
    (isGood_integralClosedSubspace D sX hX W.1) sX hX W.1.subspace.ι _ _ = _
  rw [properCyclePushforwardCoeff_ι_eq_cycleClosedPushforward D sX hX W.1,
    cycleClosedPushforward_apply_pushforward]
  exact rationalFunctionPrincipalDivisorCycle_toIntegralClosedSubspace D (W.1.subspace.ι ≫ sX)
    (isGood_integralClosedSubspace D sX hX W.1) W.1.isIntegralSpace _ _ P

include hbase hr in
/-- **The right-hand side of Stacks 0EQA at a prime divisor of `X`, as an order of vanishing at
the henselian local ring.** At an integral closed subspace `Z` of δ-dimension `dim_δ(Y) + r - 1`
underlying a prime divisor `P` with generic point `ξ`, the coefficient
`∑_{X'} m_{X', X} ((X' → X)_* div_{X'}(g ∘ f|_{X'}))(Z)` is `ord(a) - ord(b)` for a presentation
`a / b` of the reading of `g` in `Q(𝒪^h_{X, ξ})`.

The terms of the components not through `ξ` vanish; the components through `ξ` are the index
of `AlgebraicGeometry.Space.exists_natCast_ord_sub_eq_finsum_components_mul_ordRationalFunction`,
whose prime divisors on the components are the ones the pushforwards are read at; its
δ-dimension hypothesis is Stacks 0EP5 in the form
`AlgebraicGeometry.Space.IrreducibleComponentSubspace.deltaValue_ambientGenericPoint_of_isFlat`. -/
theorem exists_natCast_ord_sub_eq_finsum_flatPullbackDivisorPushforward {k : ℤ}
    (hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (k : EInt))
    (g : (rationalFunctions D.site D.base D.base_mem hY.1)ˣ)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : deltaDimension D sX Z = k + r - 1) (P : PrimeDivisor D.site D.base D.base_mem X)
    (hPZ : P.toIntegralClosedSubspace D.site D.base D.base_mem = Z)
    (hPgp : P.genericPoint D.site D.base D.base_mem X =
      Z.ambientGenericPoint D.site D.base D.base_mem) :
    ∃ a b : (↥(P.genericHenselianLocalRing D.site D.base D.base_mem hX.1
        (D.isDecentSpace_of_isGood sX hX)))⁰,
      IsLocalization.mk' (P.genericTotalFractionRing D.site D.base D.base_mem hX.1
            (D.isDecentSpace_of_isGood sX hX))
          (a : ↥(P.genericHenselianLocalRing D.site D.base D.base_mem hX.1
            (D.isDecentSpace_of_isGood sX hX))) b =
        P.rationalFunctionsToGenericTotalFractionRingOfFlat D.site D.base D.base_mem hX.1
          (D.isDecentSpace_of_isGood sX hX)
          (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) hY.1 hintY f hflat
          (g : rationalFunctions D.site D.base D.base_mem hY.1) ∧
      ∑ᶠ W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1,
          spaceMultiplicity D X hX.1 W.1 *
            (W.flatPullbackDivisorPushforward D sX hX sY hY f hbase r hr hflat hintY hk g).1 Z =
        ((Ring.ord ↥(P.genericHenselianLocalRing D.site D.base D.base_mem hX.1
              (D.isDecentSpace_of_isGood sX hX))
            (a : ↥(P.genericHenselianLocalRing D.site D.base D.base_mem hX.1
              (D.isDecentSpace_of_isGood sX hX)))).toNat : ℤ) -
          ((Ring.ord ↥(P.genericHenselianLocalRing D.site D.base D.base_mem hX.1
              (D.isDecentSpace_of_isGood sX hX))
            (b : ↥(P.genericHenselianLocalRing D.site D.base D.base_mem hX.1
              (D.isDecentSpace_of_isGood sX hX)))).toNat : ℤ) := by
  have hdim : ∀ C : irreducibleComponents (points D.site D.base D.base_mem X),
      P.genericPoint D.site D.base D.base_mem X ∈
          (C : Set (points D.site D.base D.base_mem X)) →
        deltaDimension D sX (integralClosedSubspaceOfComponent D.site D.base D.base_mem hX.1
            (D.isDecentSpace_of_isGood sX hX) C) =
          deltaDimension D sX (P.toIntegralClosedSubspace D.site D.base D.base_mem) + 1 := by
    intro C _
    have h1 := deltaDimension_eq_deltaValue_ambientGenericPoint D sX hX.1
      (IrreducibleComponentSubspace.ofComponent D sX hX C).1
    rw [IrreducibleComponentSubspace.deltaValue_ambientGenericPoint_of_isFlat
      D sX hX sY hY f hbase r hr hflat hintY hk
      (IrreducibleComponentSubspace.ofComponent D sX hX C)] at h1
    change deltaDimension D sX (IrreducibleComponentSubspace.ofComponent D sX hX C).1 = _
    rw [h1, hPZ, hZ]
    ring
  obtain ⟨a, b, Zc, hZc, hab, hsum⟩ :=
    exists_natCast_ord_sub_eq_finsum_components_mul_ordRationalFunction D X hX.1 sX hX
      (D.isDecentSpace_of_isGood sX hX) P sY hY hintY f hflat hdim g
  refine ⟨a, b, hab, ?_⟩
  rw [hsum]
  have hchart := P.chartSchemeToPoints_genericEtaleChart_point D.site D.base D.base_mem hX.1
    (D.isDecentSpace_of_isGood sX hX)
  set s : Set (IrreducibleComponentSubspace D.site D.base D.base_mem hX.1) :=
    {W | Z.ambientGenericPoint D.site D.base D.base_mem ∈
      subspacePointSet D.site D.base D.base_mem X W.1.subspace} with hsdef
  have hsupp : Function.support (fun W : IrreducibleComponentSubspace D.site D.base D.base_mem
      hX.1 => spaceMultiplicity D X hX.1 W.1 *
        (W.flatPullbackDivisorPushforward D sX hX sY hY f hbase r hr hflat hintY hk g).1 Z) ⊆
      s := by
    intro W hW
    by_contra hWs
    apply hW
    change spaceMultiplicity D X hX.1 W.1 *
      (W.flatPullbackDivisorPushforward D sX hX sY hY f hbase r hr hflat hintY hk g).1 Z = 0
    rw [W.flatPullbackDivisorPushforward_apply_of_notMem D sX hX sY hY f hbase r hr
      hflat hintY hk g Z hWs, mul_zero]
  let e : s ≃ P.genericComponentIndex D X hX.1 (D.isDecentSpace_of_isGood sX hX) :=
    { toFun := fun W => ⟨⟨subspacePointSet D.site D.base D.base_mem X W.1.1.subspace,
          W.1.2.2.2⟩, by
        change chartSchemeToPoints D.site D.base D.base_mem X _ _ ∈
          subspacePointSet D.site D.base D.base_mem X W.1.1.subspace
        rw [hchart, hPgp]
        exact W.2⟩
      invFun := fun i => ⟨IrreducibleComponentSubspace.ofComponent D sX hX i.1, by
        change Z.ambientGenericPoint D.site D.base D.base_mem ∈
          subspacePointSet D.site D.base D.base_mem X
            (IrreducibleComponentSubspace.ofComponent D sX hX i.1).1.subspace
        rw [IrreducibleComponentSubspace.subspacePointSet_ofComponent]
        exact hPgp ▸ (hchart.subst
          (motive := fun p => p ∈ (i.1 : Set (points D.site D.base D.base_mem X))) i.2)⟩
      left_inv := fun W => Subtype.ext (Subtype.ext
        (injective_integralClosedSubspaceSupport D.site D.base D.base_mem hX.1
          (IrreducibleCloseds.ext
            (IrreducibleComponentSubspace.subspacePointSet_ofComponent D sX hX _))))
      right_inv := fun i => Subtype.ext (Subtype.ext
        (IrreducibleComponentSubspace.subspacePointSet_ofComponent D sX hX i.1)) }
  have hmem : (∑ᶠ W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1,
      spaceMultiplicity D X hX.1 W.1 *
        (W.flatPullbackDivisorPushforward D sX hX sY hY f hbase r hr hflat hintY hk g).1 Z) =
      ∑ᶠ W ∈ s, spaceMultiplicity D X hX.1 W.1 *
        (W.flatPullbackDivisorPushforward D sX hX sY hY f hbase r hr hflat hintY hk g).1 Z := by
    rw [finsum_mem_def, Set.indicator_eq_self.mpr hsupp]
  rw [hmem, ← finsum_set_coe_eq_finsum_mem s, ← finsum_comp_equiv e.symm]
  refine finsum_congr fun i => ?_
  exact congrArg (fun n : ℤ => irreducibleComponentMultiplicity D X hX.1
      (D.isDecentSpace_of_isGood sX hX) i.1 * n)
    (IrreducibleComponentSubspace.flatPullbackDivisorPushforward_apply_eq_ord
      D sX hX sY hY f hbase r hr hflat hintY hk
      (IrreducibleComponentSubspace.ofComponent D sX hX i.1) g Z (Zc i) ((hZc i).trans hPgp))

end Coefficients

/-! ### Stacks 0EQA -/

section Statement

variable (hflat : IsFlat D.site D.base D.base_mem f)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y)

/-- **Stacks 0EQA.** *Flat pullback of a principal divisor.* In Situation 0EDT let `X, Y/B` be
good, assume `Y` integral with `dim_δ(Y) = k`, and let `f : X ⟶ Y` be a flat morphism over `B`
of relative dimension `r`. Then for `g ∈ R(Y)^*`

  `f^* div_Y(g) = ∑_{X'} m_{X', X} (X' → X)_* div_{X'}(g ∘ f|_{X'})`

as `(k + r - 1)`-cycles on `X`: at every integral closed subspace `Z ⊆ X` the coefficient of the
flat pullback (Stacks 0EP8) of `div_Y(g)` (Stacks 0EQ1) is the sum over the irreducible
components `X'` of `X` of `m_{X', X}`, the multiplicity of `X'` in `X` (Stacks 0EE9), times the
coefficient at `Z` of the pushforward along `X' → X` (Stacks 0EP1) of the principal divisor of
`g ∘ f|_{X'} ∈ R(X')^*`. The sum is a locally finite one, which is why the identity of cycles is
stated at each coefficient. -/
@[stacks 0EQA "the displayed identity of (k + r - 1)-cycles on X, at every integral closed
  subspace of X; the sum is over the irreducible components X' of X (a locally finite family),
  m_{X',X} is the length of O_X at the generic point of X' (0EE9 part (1) for the space X),
  g ∘ f|_{X'} is the image of g under the extension of function fields of the dominant
  f|_{X'} (0EML), and every cycle is the one of this chapter: f^* is 0EP8, div is 0EQ1 at the
  canonical embeddings of 0ENK, (X' → X)_* is 0EP1; the hypotheses are exactly the tag's"]
theorem flatPullbackMap_rationalFunctionPrincipalDivisorCycle_eq_finsum_components {k : ℤ}
    (hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (k : EInt))
    (g : (rationalFunctions D.site D.base D.base_mem hY.1)ˣ)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (flatPullbackMap D sX hX sY hY f hbase r hflat hr (k - 1) (k + r - 1) (by ring)
        (rationalFunctionPrincipalDivisorCycle D sY hY hintY hk g)).1 Z =
      ∑ᶠ W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1,
        spaceMultiplicity D X hX.1 W.1 *
          (W.flatPullbackDivisorPushforward D sX hX sY hY f hbase r hr hflat hintY hk g).1 Z := by
  by_cases hZd : deltaDimension D sX Z = k + r - 1
  swap
  · have hvan : ∀ c : CycleGroup D sX (k + r - 1), c.1 Z = 0 := fun c =>
      by_contra fun h => hZd (c.2.2 Z h)
    rw [hvan]
    symm
    refine finsum_eq_zero_of_forall_eq_zero fun W => ?_
    rw [hvan (W.flatPullbackDivisorPushforward D sX hX sY hY f hbase r hr hflat hintY hk g),
      mul_zero]
  obtain ⟨P, hPZ, hPgp⟩ := exists_primeDivisor_toIntegralClosedSubspace_eq_of_isFlat D sX hX sY hY
    f hbase r hr hflat hintY hk Z hZd
  obtain ⟨a, b, hab, hR⟩ := exists_natCast_ord_sub_eq_finsum_flatPullbackDivisorPushforward D sX
    hX sY hY f hbase r hr hflat hintY hk g Z hZd P hPZ hPgp
  rw [hR, flatPullbackMap_apply]
  have _ht0Y : T0Space (points D.site D.base D.base_mem Y) :=
    t0Space_points_of_isDecentSpace D.site D.base D.base_mem hY.1
      (D.isDecentSpace_of_isGood sY hY)
  have hδξ : D.deltaValue sX (Z.ambientGenericPoint D.site D.base D.base_mem) = k + r - 1 :=
    (deltaDimension_eq_deltaValue_ambientGenericPoint D sX hX.1 Z).symm.trans hZd
  have hle := deltaValue_le_add_of_hasRelativeDimension D sX hX sY hY f hbase r hr
    (Z.ambientGenericPoint D.site D.base D.base_mem)
  have hδηY := deltaValue_genericPoint_eq_of_deltaDimensionClosed D sY hY hintY hk
  have hspecY : genericPoint D.site D.base D.base_mem hY.1 hintY ⤳
      pointsMap D.site D.base D.base_mem X f (Z.ambientGenericPoint D.site D.base D.base_mem) :=
    (isGenericPoint_genericPoint D.site D.base D.base_mem hY.1 hintY).specializes
      (Set.mem_univ _)
  have hterm : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem Y,
      (rationalFunctionPrincipalDivisorCycle D sY hY hintY hk g).1 W *
          flatPullbackMult D sX hX sY hY f hbase r hflat hr W Z ≠ 0 →
        W.ambientGenericPoint D.site D.base D.base_mem =
            pointsMap D.site D.base D.base_mem X f
              (Z.ambientGenericPoint D.site D.base D.base_mem) ∧
          deltaDimension D sY W = k - 1 := fun W h =>
    ⟨(pointsMap_ambientGenericPoint_eq_of_flatPullbackMult_ne_zero D sX hX sY hY f hbase r hr
        hflat W Z (right_ne_zero_of_mul h)).symm,
      (rationalFunctionPrincipalDivisorCycle D sY hY hintY hk g).2.2 W (left_ne_zero_of_mul h)⟩
  by_cases hηY : pointsMap D.site D.base D.base_mem X f
      (Z.ambientGenericPoint D.site D.base D.base_mem) =
      genericPoint D.site D.base D.base_mem hY.1 hintY
  · -- the generic point of `Z` dominates `Y`: both sides vanish
    rw [P.natCast_ord_sub_eq_zero_of_pointsMap_eq_genericPoint D.site D.base D.base_mem hX.1
      (D.isDecentSpace_of_isGood sX hX)
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) hY.1 hintY
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY) f hflat
      (by rw [hPgp]; exact hηY) g a b hab]
    refine finsum_eq_zero_of_forall_eq_zero fun W => ?_
    by_contra h
    obtain ⟨h1, h2⟩ := hterm W h
    rw [deltaDimension_eq_deltaValue_ambientGenericPoint D sY hY.1 W, h1, hηY, hδηY] at h2
    omega
  · -- the generic point of `Z` lies over the generic point of a prime divisor of `Y`
    have hlt := deltaValue_lt_of_specializes D sY hY hspecY (Ne.symm hηY)
    rw [hδηY] at hlt
    have hδη : D.deltaValue sY (pointsMap D.site D.base D.base_mem X f
        (Z.ambientGenericPoint D.site D.base D.base_mem)) = k - 1 := by omega
    obtain ⟨W₀, hW₀⟩ := (bijective_integralClosedSubspaceSupport D.site D.base D.base_mem hY.1
      (D.isDecentSpace_of_isGood sY hY)).2 (IrreducibleCloseds.closureSingleton
        (pointsMap D.site D.base D.base_mem X f (Z.ambientGenericPoint D.site D.base D.base_mem)))
    have hW₀set : subspacePointSet D.site D.base D.base_mem Y W₀.subspace =
        closure {pointsMap D.site D.base D.base_mem X f
                  (Z.ambientGenericPoint D.site D.base D.base_mem)} :=
      congrArg IrreducibleCloseds.carrier hW₀
    have hW₀gp : W₀.ambientGenericPoint D.site D.base D.base_mem =
        pointsMap D.site D.base D.base_mem X f (Z.ambientGenericPoint D.site D.base D.base_mem) :=
      (W₀.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hY.1).eq
        (by rw [hW₀set]; exact isGenericPoint_closure)
    have hW₀d : deltaDimension D sY W₀ = k - 1 := by
      rw [deltaDimension_eq_deltaValue_ambientGenericPoint D sY hY.1 W₀, hW₀gp, hδη]
    obtain ⟨PW, hPW⟩ := ((isPrimeDivisor_tfae_of_isIntegralSpace' D sY hY hintY hk W₀).out 3
      1).mp hW₀d
    have hPWW : PW.toIntegralClosedSubspace D.site D.base D.base_mem = W₀ := by
      have hext : ∀ A A' : IntegralClosedSubspace D.site D.base D.base_mem Y,
          A.subspace = A'.subspace → A = A' := by
        rintro ⟨_, _, _⟩ ⟨_, _, _⟩ rfl
        rfl
      exact hext _ _ hPW
    have hPWgp : PW.genericPoint D.site D.base D.base_mem Y =
        pointsMap D.site D.base D.base_mem X f (Z.ambientGenericPoint D.site D.base D.base_mem) :=
      (PW.isGenericPoint_genericPoint D.site D.base D.base_mem Y).eq (by
        rw [← hW₀gp]
        change IsGenericPoint _ (subspacePointSet D.site D.base D.base_mem Y PW.subspace)
        rw [hPW]
        exact W₀.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hY.1)
    rw [finsum_eq_single _ W₀ (fun W hW => by
      by_contra h
      exact hW (IntegralClosedSubspace.eq_of_ambientGenericPoint_eq D hY.1
        ((hterm W h).1.trans hW₀gp.symm)))]
    obtain ⟨U, V, j, hsq, hloc⟩ :=
      P.exists_natCast_ord_sub_eq_length_mul_ordRationalFunction D.site D.base D.base_mem hX.1
        (D.isDecentSpace_of_isGood sX hX)
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) hY.1 hintY
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY) PW f hflat
        (by rw [hPgp, hPWgp])
    rw [hloc g a b hab, ← hPWW,
      rationalFunctionPrincipalDivisorCycle_toIntegralClosedSubspace D sY hY hintY hk g PW,
      flatPullbackMult_eq_toNat_length_of_neighborhoods D sX hX sY hY f hbase r hr hflat
        (PW.toIntegralClosedSubspace D.site D.base D.base_mem) Z (by rw [hPWW, hW₀gp])
        (by rw [hPWW, hW₀d, hZd]; ring) hPgp U V j hsq]
    ring

end Statement

end AlgebraicGeometry.Space

end
