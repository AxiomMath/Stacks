module

public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.PointFamilyFibreDifference

/-!
# The graph construction of Tag 02RQ at a pair with one point at infinity

`StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.PointFamilyFibreDifference` does part (6)
of Tag 02RQ, and the production step it feeds, at an arbitrary pair of points `t`, `t'` of the
*affine* chart of `ℙ¹_S`. This file does the same at the pair `(t, ∞)`: one point `t` of the
affine chart and the point at infinity.

## The simplification over the two-affine-point case

At `(t, t')` the fibre-difference identity `div_W(z - t) = [W_t] - [W_∞]` of
`Stacks.Chow.principalDivisorCycle_eq_sub_linePointFibreCycles` is applied at both `t` and `t'`
and the common `∞` terms are cancelled by subtraction, which needs the Möbius ratio and the
hypothesis `t ≠ t'`. At `(t, ∞)` no cancellation is needed: a single application of that lemma,
at `t`, already produces `[W_t] - [W_∞]`, and the non-degeneracy of the `∞` term,
`Stacks.Chow.notMem_support_graphInfinityFiber_genericPoint`, needs no hypothesis at all. There is
accordingly no Möbius section here, and no hypothesis analogous to `t ≠ t'`: the point at infinity
is never a point of the affine chart, so the two points of a `(t, ∞)` pair are always distinct.

## Main results

* `Stacks.Chow.principalDivisorCycle_eq_sub_pointInfinityImageCycles` — **part (6) of Tag 02RQ at
  the pair `(t, ∞)`.**
* `Stacks.Chow.principalDivisorPushforward_eq_sub_pointInfinityFibreCycles` — the identity carried
  from `V` to `X`.
* `Stacks.Chow.exists_pointInfinityGraphFamilyMember` — **the production step of part (3) of Tag
  0B07 at the pair `(t, ∞)`**, given the invertibility of `baseSectionOn t + g₀`.

## References

* [Stacks Project, Tag 02RQ](https://stacks.math.columbia.edu/tag/02RQ)
* [Stacks Project, Tag 0B07](https://stacks.math.columbia.edu/tag/0B07)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Part (6) of Tag 02RQ at the pair `(t, ∞)` -/

/-- **The principal divisor on `X` as a difference of the fibre cycle at `t` and the fibre cycle
at infinity.** Let `U ⊆ X` be a dense open on which `g` is invertible, and let `t` be a global
function on the base with `g - t` invertible on `U` — that is, the graph of `g` meets neither the
section at `t` nor the section at infinity (the latter automatically). Then for every nonzero
rational function `a` on `X` equal to the germ of `g - t`,

  `div_X(a) = [Y_t ⊆ X]_{n-1} - [Y_∞ ⊆ X]_{n-1}`.

This is `Stacks.Chow.principalDivisorCycle_eq_sub_pointImageCycles` at the pair `(t, ∞)`: a single
application of `Stacks.Chow.principalDivisorCycle_eq_sub_linePointFibreCycles`, with no Möbius
ratio needed. -/
theorem principalDivisorCycle_eq_sub_pointInfinityImageCycles (C : ChowSituation.{u})
    {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [IsIntegral X] (U : X.Opens)
    [QuasiCompact U.ι] [Nonempty U.toScheme] (g : (Γ(X, U))ˣ) (t : Γ(C.S, ⊤)) {n : ℤ}
    (hn : schemeDeltaDimension C sX = (n : EInt)) (hU : Dense (U : Set X))
    (hu : IsUnit ((g : Γ(X, U)) - baseSectionOn sX U t))
    (a : X.functionField) (ha : a ≠ 0)
    (hrel : a = X.germToFunctionField U ((g : Γ(X, U)) - baseSectionOn sX U t))
    [IsClosedImmersion ((graphInfinityFiber sX U ↑g).subschemeι ≫ graphProjection sX U ↑g)] :
    principalDivisorCycle C sX hn a =
      cycleAssociatedToClosedSubscheme C sX
          (((lineSection C.S t).ker.comap (graphLineProjection sX U ↑g)).subschemeι ≫
            graphProjection sX U ↑g) (n - 1) -
        cycleAssociatedToClosedSubscheme C sX
          ((graphInfinityFiber sX U ↑g).subschemeι ≫ graphProjection sX U ↑g) (n - 1) := by
  have hYint : IsIntegral (graphClosure sX U ↑g) := isIntegral_graphClosure sX U ↑g hU
  have hYft : LocallyOfFiniteType (graphBaseMorphism sX U ↑g) :=
    locallyOfFiniteType_graphBaseMorphism sX U ↑g
  have hLNY : IsLocallyNoetherian (graphClosure sX U ↑g) :=
    LocallyOfFiniteType.isLocallyNoetherian (graphBaseMorphism sX U ↑g)
  have hd : GraphPreimageDense sX U ↑g := dense_graphPreimage sX U ↑g
  have hWne : Nonempty (graphPreimage sX U ↑g) := Set.nonempty_coe_sort.mpr hd.nonempty
  have hηW : genericPoint (graphClosure sX U ↑g) ∈ graphPreimage sX U ↑g :=
    ((genericPoint_spec (graphClosure sX U ↑g)).mem_open_set_iff
      (graphPreimage sX U ↑g).2).mpr (by simpa using hd.nonempty)
  have hYdim : schemeDeltaDimension C (graphBaseMorphism sX U ↑g) = (n : EInt) :=
    schemeDeltaDimension_graphClosure C sX U g n hn hU hYft
  have hWA : graphPreimage sX U ↑g ≤ graphLineProjection sX U ↑g ⁻¹ᵁ chartOpen C.S :=
    graphPreimage_le_preimage_image_chart sX U g (affineChart C.S) (g : Γ(X, U)) rfl
  have hη1 : genericPoint (graphClosure sX U ↑g) ∈
      graphLineProjection sX U ↑g ⁻¹ᵁ chartOpen C.S := hWA hηW
  have hgenT : genericPoint (graphClosure sX U ↑g) ∉ Set.range
      ((lineSection C.S t).ker.comap (graphLineProjection sX U ↑g)).subschemeι.base := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact notMem_support_comap_lineSectionKer_genericPoint sX U g t hu
  have hgenInf : genericPoint (graphClosure sX U ↑g) ∉ Set.range
      (graphInfinityFiber sX U ↑g).subschemeι.base := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact notMem_support_graphInfinityFiber_genericPoint sX U g
  have hDT := principalDivisorCycle_eq_sub_linePointFibreCycles C (graphBaseMorphism sX U ↑g)
    (graphLineProjection sX U ↑g) t hYdim hη1 hgenT hgenInf
  have hane : dominantFunctionFieldMap (graphProjection sX U ↑g) a ≠ 0 := fun h0 =>
    ha (RingHom.injective (dominantFunctionFieldMap (graphProjection sX U ↑g))
      (h0.trans (map_zero _).symm))
  have hφrel : dominantFunctionFieldMap (graphProjection sX U ↑g) a =
      linePointFunction (graphLineProjection sX U ↑g) t hη1 := by
    rw [linePointFunction_graphLineProjection sX U g t hηW hη1,
      germToFunctionField_graphProjection_app sX U g ((g : Γ(X, U)) - baseSectionOn sX U t), hrel]
  have hdiff : principalDivisorCycle C (graphBaseMorphism sX U ↑g) hYdim
        (dominantFunctionFieldMap (graphProjection sX U ↑g) a) =
      cycleAssociatedToClosedSubscheme C (graphBaseMorphism sX U ↑g)
          ((lineSection C.S t).ker.comap (graphLineProjection sX U ↑g)).subschemeι (n - 1) -
        cycleAssociatedToClosedSubscheme C (graphBaseMorphism sX U ↑g)
          (graphInfinityFiber sX U ↑g).subschemeι (n - 1) := by
    rw [hφrel]
    exact hDT
  rw [principalDivisorCycle_eq_properPushforward_of_functionField C sX U g hn a ha hYint hYft
      hYdim, hdiff, properPushforward_sub,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C
      (graphBaseMorphism sX U ↑g) sX (graphProjection sX U ↑g) rfl
      ((lineSection C.S t).ker.comap (graphLineProjection sX U ↑g)).subschemeι (n - 1),
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C
      (graphBaseMorphism sX U ↑g) sX (graphProjection sX U ↑g) rfl
      (graphInfinityFiber sX U ↑g).subschemeι (n - 1)]

/-! ### The pushforward of the principal divisor as a fibre difference at `(t, ∞)` -/

/-- **The pushforward of the principal divisor of a rational function on an integral closed
subscheme `V ⊆ X` is the fibre difference of the graph member at the pair `(t, ∞)`.**

This is `Stacks.Chow.principalDivisorPushforward_eq_sub_pointFibreCycles` at the pair `(t, ∞)` in
place of an arbitrary pair of the affine chart: part (6) at that pair, which is
`Stacks.Chow.principalDivisorCycle_eq_sub_pointInfinityImageCycles`, gives the identity on `V`,
proper pushforward along the closed immersion `V ⟶ X` carries it to `X`, and
`Stacks.Chow.cycleAssociatedToClosedSubscheme_pointFiber_graphFamilyMember` and
`Stacks.Chow.cycleAssociatedToClosedSubscheme_infinityFiber_graphFamilyMember` identify the two
fibres of the member with the images of the two fibres of the graph closure. -/
theorem principalDivisorPushforward_eq_sub_pointInfinityFibreCycles (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ) (V : X.IdealSheafData)
    (hV : IsIntegral V.subscheme)
    (hdim : schemeDeltaDimension C (V.subschemeι ≫ f) = ((k + 1 : ℤ) : EInt))
    (gg : (rationalFunctions V.subscheme)ˣ) (U : V.subscheme.Opens) [QuasiCompact U.ι]
    [Nonempty U.toScheme] (hU : Dense (U : Set V.subscheme)) (σ : (Γ(V.subscheme, U))ˣ)
    (t : Γ(C.S, ⊤))
    (hu : IsUnit ((σ : Γ(V.subscheme, U)) - baseSectionOn (V.subschemeι ≫ f) U t))
    (hrel : (rationalFunctionsEquivFunctionField V.subscheme).1
          (gg : rationalFunctions V.subscheme) =
      V.subscheme.germToFunctionField U
        ((σ : Γ(V.subscheme, U)) - baseSectionOn (V.subschemeι ≫ f) U t)) :
    principalDivisorPushforward C f V hV gg =
      (cycleAssociatedToClosedSubscheme C f
          (pointFiber f t (graphFamilyMember f V.subschemeι U
            (σ : Γ(V.subscheme, U)))).subschemeι k).1 -
        (cycleAssociatedToClosedSubscheme C f
          (infinityFiber f (graphFamilyMember f V.subschemeι U
            (σ : Γ(V.subscheme, U)))).subschemeι k).1 := by
  have hVint : IsIntegral V.subscheme := hV
  have : IsLocallyNoetherian V.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (V.subschemeι ≫ f)
  have hCIinf : IsClosedImmersion
      ((graphInfinityFiber (V.subschemeι ≫ f) U
          (σ : Γ(V.subscheme, U))).subschemeι ≫
        graphProjection (V.subschemeι ≫ f) U (σ : Γ(V.subscheme, U))) :=
    isClosedImmersion_graphInfinityFiber_comp (V.subschemeι ≫ f) U (σ : Γ(V.subscheme, U))
  have hk : (k + 1 - 1 : ℤ) = k := by ring
  have hane : (rationalFunctionsEquivFunctionField V.subscheme).1
      (gg : rationalFunctions V.subscheme) ≠ 0 :=
    (gg.isUnit.map (rationalFunctionsEquivFunctionField V.subscheme).1.toRingHom).ne_zero
  have h6 := principalDivisorCycle_eq_sub_pointInfinityImageCycles C (V.subschemeι ≫ f) U σ t hdim
    hU hu ((rationalFunctionsEquivFunctionField V.subscheme).1
      (gg : rationalFunctions V.subscheme)) hane hrel
  have h6' : principalCycle V.subscheme ((rationalFunctionsEquivFunctionField V.subscheme).1
        (gg : rationalFunctions V.subscheme)) =
      (cycleAssociatedToClosedSubscheme C (V.subschemeι ≫ f)
          (((lineSection C.S t).ker.comap (graphLineProjection (V.subschemeι ≫ f) U
              (σ : Γ(V.subscheme, U)))).subschemeι ≫
            graphProjection (V.subschemeι ≫ f) U (σ : Γ(V.subscheme, U))) (k + 1 - 1)).1 -
        (cycleAssociatedToClosedSubscheme C (V.subschemeι ≫ f)
          ((graphInfinityFiber (V.subschemeι ≫ f) U
              (σ : Γ(V.subscheme, U))).subschemeι ≫
            graphProjection (V.subschemeι ≫ f) U (σ : Γ(V.subscheme, U))) (k + 1 - 1)).1 := by
    have h := congrArg Subtype.val h6
    rw [AddSubgroup.coe_sub] at h
    exact h
  rw [hk] at h6'
  have hmem : principalCycle V.subscheme ((rationalFunctionsEquivFunctionField V.subscheme).1
      (gg : rationalFunctions V.subscheme)) ∈ cyclesOfDimension C (V.subschemeι ≫ f) k := by
    have h := principalCycle_mem_cyclesOfDimension C (V.subschemeι ≫ f) hdim
      ((rationalFunctionsEquivFunctionField V.subscheme).1
        (gg : rationalFunctions V.subscheme))
    rwa [hk] at h
  have hc : (⟨_, hmem⟩ : CycleGroup C (V.subschemeι ≫ f) k) =
      cycleAssociatedToClosedSubscheme C (V.subschemeι ≫ f)
          (((lineSection C.S t).ker.comap (graphLineProjection (V.subschemeι ≫ f) U
              (σ : Γ(V.subscheme, U)))).subschemeι ≫
            graphProjection (V.subschemeι ≫ f) U (σ : Γ(V.subscheme, U))) k -
        cycleAssociatedToClosedSubscheme C (V.subschemeι ≫ f)
          ((graphInfinityFiber (V.subschemeι ≫ f) U
              (σ : Γ(V.subscheme, U))).subschemeι ≫
            graphProjection (V.subschemeι ≫ f) U (σ : Γ(V.subscheme, U))) k := by
    refine Subtype.ext ?_
    rw [AddSubgroup.coe_sub]
    exact h6'
  have hpush := congrArg Subtype.val
    (congrArg (properPushforward C (V.subschemeι ≫ f) f V.subschemeι rfl k) hc)
  rw [properPushforward_sub,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C
      (V.subschemeι ≫ f) f V.subschemeι rfl
      (((lineSection C.S t).ker.comap (graphLineProjection (V.subschemeι ≫ f) U
          (σ : Γ(V.subscheme, U)))).subschemeι ≫
        graphProjection (V.subschemeι ≫ f) U (σ : Γ(V.subscheme, U))) k,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C
      (V.subschemeι ≫ f) f V.subschemeι rfl
      ((graphInfinityFiber (V.subschemeι ≫ f) U
          (σ : Γ(V.subscheme, U))).subschemeι ≫
        graphProjection (V.subschemeι ≫ f) U (σ : Γ(V.subscheme, U))) k,
    cycleAssociatedToClosedSubscheme_pointFiber_graphFamilyMember C f V.subschemeι U
      (σ : Γ(V.subscheme, U)) t k,
    cycleAssociatedToClosedSubscheme_infinityFiber_graphFamilyMember C f V.subschemeι U
      (σ : Γ(V.subscheme, U)) k, AddSubgroup.coe_sub] at hpush
  exact hpush

/-! ### The member of Tag 02S4 part (3) at the pair `(t, ∞)` -/

/-- **The subvariety of `X ×_S ℙ¹_S` realising the principal divisor of a rational function as a
fibre difference at the pair `(t, ∞)`.** Let `V ⊆ X` be an integral closed subscheme of
delta-dimension `k + 1`, let `gg` be a nonzero rational function on `V` represented by a unit
section `g₀` on a dense open `U`, and let `t` be a point of the affine chart. Suppose
`baseSectionOn t + g₀` is invertible on `U`. Then the closure `W` of the graph of the unit
`σ = baseSectionOn t + g₀`, read inside `X ×_S ℙ¹_S`, has every property Tag 02S4 part (3) asks
of a family member at the pair `(t, ∞)` — it is integral, of relative dimension `k + 1` at its
generic points, contained in neither section, and supported over `V` — and

  `pr_{X,*}(div_V(gg)) = [W_t]_k - [W_∞]_k`.

This is `Stacks.Chow.exists_pointGraphFamilyMember` at the pair `(t, ∞)`: no Möbius section is
needed, since `σ - baseSectionOn t = g₀` is already a unit and the non-degeneracy at `∞` is
`Stacks.Chow.notSubset_range_infinitySection_graphFamilyMember`, which needs no hypothesis at
all. -/
theorem exists_pointInfinityGraphFamilyMember (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ) (V : X.IdealSheafData)
    (hV : IsIntegral V.subscheme)
    (hdim : schemeDeltaDimension C (V.subschemeι ≫ f) = ((k + 1 : ℤ) : EInt))
    (gg : (rationalFunctions V.subscheme)ˣ) (U : V.subscheme.Opens) [QuasiCompact U.ι]
    [Nonempty U.toScheme] (hU : Dense (U : Set V.subscheme)) (g₀ : (Γ(V.subscheme, U))ˣ)
    (hg₀ : ofSection V.subscheme ⟨U, hU⟩ (g₀ : Γ(V.subscheme, U)) =
      (gg : rationalFunctions V.subscheme))
    (t : Γ(C.S, ⊤))
    (hw : IsUnit (baseSectionOn (V.subschemeι ≫ f) U t + (g₀ : Γ(V.subscheme, U)))) :
    ∃ W : (projectiveLineProduct f).IdealSheafData,
      IsIntegral W.subscheme ∧
      (∀ ξ : genericPoints W.subscheme,
        relativeDimension C.dimensionFunction (familyBase f W) ξ.1 = k + 1) ∧
      ¬ Set.range W.subschemeι ⊆ Set.range (pointSection f t) ∧
      ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection f) ∧
      ((W.support : Set (projectiveLineProduct f)) ⊆
        pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ⁻¹' (V.support : Set X)) ∧
      (∀ x : X, principalDivisorPushforward C f V hV gg x =
        (cycleAssociatedToClosedSubscheme C f (pointFiber f t W).subschemeι k).1 x -
          (cycleAssociatedToClosedSubscheme C f (infinityFiber f W).subschemeι k).1 x) := by
  have hVint : IsIntegral V.subscheme := hV
  have : IsLocallyNoetherian V.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (V.subschemeι ≫ f)
  set σ := hw.unit with hσdef
  have hσsub : (σ : Γ(V.subscheme, U)) - baseSectionOn (V.subschemeι ≫ f) U t =
      (g₀ : Γ(V.subscheme, U)) := by
    rw [hσdef, hw.unit_spec]; ring
  have hYint : IsIntegral (graphClosure (V.subschemeι ≫ f) U (σ : Γ(V.subscheme, U))) :=
    isIntegral_graphClosure (V.subschemeι ≫ f) U (σ : Γ(V.subscheme, U)) hU
  have hηU : genericPoint V.subscheme ∈ U :=
    ((genericPoint_spec V.subscheme).mem_open_set_iff U.2).mpr
      (by simpa using ‹Nonempty U.toScheme›)
  have hgf : (rationalFunctionsEquivFunctionField V.subscheme).1
        (gg : rationalFunctions V.subscheme) =
      V.subscheme.germToFunctionField U (g₀ : Γ(V.subscheme, U)) := by
    rw [← hg₀]
    exact (rationalFunctionsEquivFunctionField V.subscheme).2 ⟨U, hU⟩
      (g₀ : Γ(V.subscheme, U)) hηU
  have hu : IsUnit ((σ : Γ(V.subscheme, U)) - baseSectionOn (V.subschemeι ≫ f) U t) := by
    rw [hσsub]; exact g₀.isUnit
  have hrel : (rationalFunctionsEquivFunctionField V.subscheme).1
        (gg : rationalFunctions V.subscheme) =
      V.subscheme.germToFunctionField U
        ((σ : Γ(V.subscheme, U)) - baseSectionOn (V.subschemeι ≫ f) U t) := by
    rw [hσsub]; exact hgf
  refine ⟨graphFamilyMember f V.subschemeι U (σ : Γ(V.subscheme, U)),
    isIntegral_graphFamilyMember f V.subschemeι U (σ : Γ(V.subscheme, U)),
    fun ξ => relativeDimension_familyBase_graphFamilyMember C f V.subschemeι U σ hU hdim ξ,
    notSubset_range_pointSection_graphFamilyMember f V.subschemeι U σ t hu,
    notSubset_range_infinitySection_graphFamilyMember f V.subschemeι U σ, ?_, fun x => ?_⟩
  · refine (support_graphFamilyMember_subset f V.subschemeι U (σ : Γ(V.subscheme, U))).trans ?_
    rw [V.range_subschemeι]
  · have h := principalDivisorPushforward_eq_sub_pointInfinityFibreCycles C f k V hV hdim gg U hU
      σ t hu hrel
    simpa using congrArg (fun c : AlgebraicCycle X ℤ => c x) h

end Stacks.Chow
