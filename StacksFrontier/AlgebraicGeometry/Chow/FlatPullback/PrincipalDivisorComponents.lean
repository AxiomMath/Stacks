module

public import StacksFrontier.AlgebraicGeometry.Chow.DimensionFunction.PrincipalDivisorFamily
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ClosedImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.ClosedCoverExactSequence
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.PointwiseDivisor

/-!
# Flat pullback of one term of a rational equivalence

Let `C = (S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` and `X'` be
schemes locally of finite type over `S`, let `f : X' ⟶ X` be flat of relative dimension `r`, let
`W ⊆ X` be an integral closed subscheme of delta-dimension `k + 1` and let `g` be a nonzero
rational function on `W`. The cycle `i_* div_W(g)` is one term of a presentation of a cycle
rationally equivalent to zero on `X`; this file computes its flat pullback.

The computation is the reduction of
[Stacks, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1) to the case of an integral target,
which is where the order-of-vanishing calculation lives. Writing `W' = f^{-1}(W)` for the
scheme-theoretic inverse image and `q : W' ⟶ W` for the restriction of `f`, which is again flat
of relative dimension `r`, the two steps are

* `f^*(i_* div_W(g)) = i'_*(q^* div_W(g))`, the closed-immersion case of Stacks 02RG, available
  as `Stacks.Chow.flatPullback_properPushforward_comap`; and
* `q^* div_W(g) = ∑_j n_j (i_j)_* div_{W'_j}(g ∘ q)`, Stacks 0EPH, available as
  `Stacks.Chow.flatPullback_principalDivisor_eq_sum_components`, the sum being over the
  irreducible components `W'_j` of `W'` with their reduced structure and `n_j` the multiplicity
  of `W'_j` in the fundamental cycle of `W'`.

## Main results

* `Stacks.Chow.principalDivisorPushforward_eq_properPushforward` — the cycle
  `Stacks.Chow.principalDivisorPushforward` is the proper pushforward along the closed immersion
  of `W` of the principal divisor cycle of `g` on `W`.
* `Stacks.Chow.exists_principalDivisorPushforward_map_integralComponentAt` — the pushforward
  along a closed immersion of a principal divisor on the integral component of a point is a
  principal divisor on the integral component of the image point, for a suitable rational
  function there; this reindexes a component of `f^{-1}(W)` as an integral closed subscheme of
  `X'`.
* `Stacks.Chow.flatPullback_principalDivisorPushforward_apply` — the computation above, read
  coefficientwise at a point of `X'`: the flat pullback of `i_* div_W(g)` is the locally finite
  sum over the irreducible components of `f^{-1}(W)` of the multiplicity of the component times
  the pushforward to `X'` of the principal divisor on that component of the pulled-back function.

## Implementation notes

Both statements are read coefficientwise, because the irreducible components of a locally
Noetherian scheme need not form a finite set, exactly as in Stacks 0EPH.

The degree of a cycle enters `Stacks.Chow.properPushforward` only through the subtype property,
so the underlying cycle of a pushforward is independent of it; the statement below therefore
mixes `k + 1 + r - 1` and `k + r` freely and the two are reconciled by `rfl`. The flat pullback
is not degree-independent — the degree enters `Stacks.Chow.flatPullbackWeight` — so there the
arithmetic is done explicitly.

What is still missing for Stacks 02S1 itself is the bookkeeping that turns this computation into
a presentation of the pulled-back cycle: the multiplicities must be absorbed into the rational
functions as powers, by `Stacks.Chow.principalDivisorPushforward_zpow`, and the family obtained
by ranging over the terms of a presentation on `X` and over the components of each inverse image
must be shown to be locally finite.

## References

* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02RO](https://stacks.math.columbia.edu/tag/02RO)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 0EPH](https://stacks.math.columbia.edu/tag/0EPH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### A principal divisor pushed forward is a proper pushforward -/

/-- The cycle `Stacks.Chow.principalDivisorPushforward` on `X` attached to an integral closed
subscheme `W ⊆ X` and a nonzero rational function `g` on `W` is the proper pushforward along the
closed immersion of `W` of the principal divisor cycle of `g`.

Both sides are the weighted pushforward `AlgebraicCycle.map` of the principal cycle of `g`, so
the identity holds by definition once the cycle underlying `γ` is recognised. -/
theorem principalDivisorPushforward_eq_properPushforward (C : ChowSituation.{u})
    {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme) (k : ℤ) (g : (rationalFunctions W.subscheme)ˣ)
    (γ : CycleGroup C (W.subschemeι ≫ sX) k)
    (hγ : γ.1 =
      letI := hW
      letI : IsLocallyNoetherian W.subscheme :=
        LocallyOfFiniteType.isLocallyNoetherian (W.subschemeι ≫ sX)
      principalCycle W.subscheme ((rationalFunctionsEquivFunctionField W.subscheme).1
        (g : rationalFunctions W.subscheme))) :
    principalDivisorPushforward C sX W hW g =
      (properPushforward C (W.subschemeι ≫ sX) sX W.subschemeι rfl k γ).1 := by
  have := hW
  have : IsLocallyNoetherian W.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (W.subschemeι ≫ sX)
  have hmap : (properPushforward C (W.subschemeι ≫ sX) sX W.subschemeι rfl k γ).1 =
      AlgebraicCycle.map W.subschemeι
        (relativeDimension C.dimensionFunction (W.subschemeι ≫ sX))
        (relativeDimension C.dimensionFunction sX) γ.1 := rfl
  rw [hmap, hγ]
  rfl

/-! ### Reindexing a component as a closed subscheme of the ambient scheme -/

/-- The pushforward along a closed immersion `i : Z ⟶ X` over the base of the principal divisor
of a nonzero rational function on the integral component of a point `t` of `Z` is the principal
divisor on the integral component of `i t` of a nonzero rational function there.

The two integral closed subschemes have the same ideal sheaf — the closure of the image of the
closure of `{t}` is the closure of `{i t}`, which is
`Stacks.Chow.map_integralComponentAt` — so `i` restricts to an isomorphism between them, and the
rational function transports along that isomorphism. The function is produced rather than
prescribed because the isomorphism is. -/
theorem exists_principalDivisorPushforward_map_integralComponentAt (C : ChowSituation.{u})
    {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sZ) (t : Z)
    (g : (rationalFunctions (integralComponentAt t).subscheme)ˣ) :
    ∃ u : (rationalFunctions (integralComponentAt (i.base t)).subscheme)ˣ,
      AlgebraicCycle.map i (relativeDimension C.dimensionFunction sZ)
          (relativeDimension C.dimensionFunction sX)
          (principalDivisorPushforward C sZ (integralComponentAt t)
            (isIntegral_integralComponentAt t) g) =
        principalDivisorPushforward C sX (integralComponentAt (i.base t))
          (isIntegral_integralComponentAt (i.base t)) u := by
  have := isIntegral_integralComponentAt t
  have := isIntegral_integralComponentAt (i.base t)
  have hker : ((integralComponentAt t).subschemeι ≫ i).ker =
      (integralComponentAt (i.base t)).subschemeι.ker := by
    rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι,
      Scheme.IdealSheafData.ker_subschemeι, map_integralComponentAt]
  obtain ⟨e, he⟩ := exists_iso_of_ker_eq ((integralComponentAt t).subschemeι ≫ i)
    (integralComponentAt (i.base t)).subschemeι hker
  exact ⟨rationalFunctionsUnitsMulEquivOfIso e g,
    map_principalDivisorPushforward_of_iso C sZ sX i hi (integralComponentAt t)
      (integralComponentAt (i.base t)) e he g⟩

/-! ### The flat pullback of one term of a rational equivalence -/

/-- **The reduction of Stacks 02S1 to an integral target.** Let `f : X' ⟶ X` be flat of relative
dimension `r`, let `W ⊆ X` be an integral closed subscheme of delta-dimension `k + 1` and let `g`
be a nonzero rational function on `W`. Then, coefficientwise at a point `x'` of `X'`,

  `f^*(i_* div_W(g)) = ∑_j n_j (i_j)_* div_{W'_j}(g ∘ q)`,

the sum being over the irreducible components `W'_j` of the scheme-theoretic inverse image
`W' = f^{-1}(W)` taken with their reduced structure, `i_j : W'_j ⟶ W' ⟶ X'` the inclusion and
`n_j` the multiplicity of `W'_j` in the fundamental cycle `[W']_{k + 1 + r}`.

The left hand side is one term of the flat pullback of a presentation of a cycle rationally
equivalent to zero, and every term on the right is a principal divisor on an integral closed
subscheme of `X'` of delta-dimension `k + 1 + r`, which is the shape Stacks 02RW asks for.

The proof restricts `f` to the inverse image, which is flat of the same relative dimension, and
combines the closed-immersion base change of Stacks 02RG with the componentwise formula of
Stacks 0EPH on the integral target `W`. -/
theorem flatPullback_principalDivisorPushforward_apply (C : ChowSituation.{u})
    {X' X : Scheme.{u}} (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (f : X' ⟶ X) [LocallyOfFiniteType f] [Flat f]
    (hbase : f ≫ sX = sX') (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ)
    (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ sX) = ((k + 1 : ℤ) : EInt))
    (g : (rationalFunctions W.subscheme)ˣ) (x' : X') :
    letI := hW
    letI := locallyOfFiniteType_comapRestrict W f
    letI := flat_comapRestrict W f
    (flatPullback C sX' sX f hbase r hf k
        ⟨principalDivisorPushforward C sX W hW g,
          principalDivisorPushforward_mem_cyclesOfDimension C sX k W hW hDim g⟩).1 x' =
      ∑ᶠ V : irreducibleComponents (W.comap f).subscheme,
        (cycleAssociatedToClosedSubscheme C ((W.comap f).subschemeι ≫ sX')
            (𝟙 (W.comap f).subscheme) (k + 1 + (r : ℤ))).1 V.2.1.genericPoint *
          (letI : IsIntegral (integralComponentAt V.2.1.genericPoint).subscheme :=
             isIntegral_integralComponentAt _
           letI := isDominant_subschemeι_integralComponentAt_comp (comapRestrict W f) V
           (properPushforward C
             ((integralComponentAt V.2.1.genericPoint).subschemeι ≫
               ((W.comap f).subschemeι ≫ sX')) sX'
             ((integralComponentAt V.2.1.genericPoint).subschemeι ≫ (W.comap f).subschemeι)
             (by rw [Category.assoc]) (k + 1 + (r : ℤ) - 1)
             (principalDivisorCycle C _
               (schemeDeltaDimension_integralComponentAt_comp C ((W.comap f).subschemeι ≫ sX')
                 (W.subschemeι ≫ sX) (comapRestrict W f)
                 (comapRestrict_comp_base C sX' sX f hbase W) r
                 (relativeDimension_comapRestrict W f hf) hDim V)
               (dominantFunctionFieldMap
                 ((integralComponentAt V.2.1.genericPoint).subschemeι ≫ comapRestrict W f)
                 ((rationalFunctionsEquivFunctionField W.subscheme).1
                   (g : rationalFunctions W.subscheme))))).1 x') := by
  have := hW
  have : IsLocallyNoetherian W.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (W.subschemeι ≫ sX)
  have := locallyOfFiniteType_comapRestrict W f
  have := flat_comapRestrict W f
  have hqr : AlgebraicGeometry.RelativeDimension (comapRestrict W f) r :=
    relativeDimension_comapRestrict W f hf
  have hbq : comapRestrict W f ≫ (W.subschemeι ≫ sX) = (W.comap f).subschemeι ≫ sX' :=
    comapRestrict_comp_base C sX' sX f hbase W
  set gg := (rationalFunctionsEquivFunctionField W.subscheme).1
    (g : rationalFunctions W.subscheme) with hggdef
  have hgg : gg ≠ 0 := rationalFunctionsEquivFunctionField_ne_zero _ g
  -- the principal divisor of `g` on `W`, read in degree `k`
  have hmemγ : principalCycle W.subscheme gg ∈ cyclesOfDimension C (W.subschemeι ≫ sX) k := by
    have h := principalCycle_mem_cyclesOfDimension C (W.subschemeι ≫ sX) hDim gg
    simpa only [show k + 1 - 1 = k from by omega] using h
  set γ : CycleGroup C (W.subschemeι ≫ sX) k := ⟨principalCycle W.subscheme gg, hmemγ⟩ with hγdef
  -- Step one: the closed-immersion base change of Stacks 02RG.
  have hstep1 : (⟨principalDivisorPushforward C sX W hW g,
        principalDivisorPushforward_mem_cyclesOfDimension C sX k W hW hDim g⟩ :
      CycleGroup C sX k) =
      properPushforward C (W.subschemeι ≫ sX) sX W.subschemeι rfl k γ :=
    Subtype.ext (principalDivisorPushforward_eq_properPushforward C sX W hW k g γ rfl)
  rw [hstep1, flatPullback_properPushforward_comap C sX' sX f hbase r hf k W γ]
  -- Step two: split on whether `x'` lies on the inverse image of `W`.
  by_cases hx : x' ∈ Set.range (W.comap f).subschemeι.base
  · obtain ⟨z, rfl⟩ := hx
    rw [properPushforward_apply_image_of_isClosedImmersion]
    -- the flat pullback along the restriction, in the degree Stacks 0EPH uses
    have hdeg : (flatPullback C ((W.comap f).subschemeι ≫ sX') (W.subschemeι ≫ sX)
          (comapRestrict W f) hbq r hqr k γ).1 z =
        (flatPullback C ((W.comap f).subschemeι ≫ sX') (W.subschemeι ≫ sX)
          (comapRestrict W f) hbq r hqr (k + 1 - 1)
          (principalDivisorCycle C (W.subschemeι ≫ sX) hDim gg)).1 z := by
      rw [flatPullback_apply, flatPullback_apply]
      have hcoeff : γ.1 ((comapRestrict W f).base z) =
          (principalDivisorCycle C (W.subschemeι ≫ sX) hDim gg).1
            ((comapRestrict W f).base z) := rfl
      have hk : k + (r : ℤ) = k + 1 - 1 + (r : ℤ) := by omega
      rw [hcoeff, hk]
    rw [hdeg, flatPullback_principalDivisor_eq_sum_components C
      ((W.comap f).subschemeι ≫ sX') (W.subschemeι ≫ sX) (comapRestrict W f) hbq r hqr hDim
      gg hgg z]
    refine finsum_congr fun V ↦ ?_
    have : IsIntegral (integralComponentAt V.2.1.genericPoint).subscheme :=
      isIntegral_integralComponentAt _
    have := isDominant_subschemeι_integralComponentAt_comp (comapRestrict W f) V
    congr 1
    -- the pushforward to `X'` of a cycle on a component, read at the image point
    have hcomp := congrFun (properPushforward_comp C
      ((integralComponentAt V.2.1.genericPoint).subschemeι ≫ ((W.comap f).subschemeι ≫ sX'))
      ((W.comap f).subschemeι ≫ sX') sX'
      (integralComponentAt V.2.1.genericPoint).subschemeι (W.comap f).subschemeι rfl rfl
      (k + 1 + (r : ℤ) - 1))
      (principalDivisorCycle C _
        (schemeDeltaDimension_integralComponentAt_comp C ((W.comap f).subschemeι ≫ sX')
          (W.subschemeι ≫ sX) (comapRestrict W f) hbq r hqr hDim V)
        (dominantFunctionFieldMap
          ((integralComponentAt V.2.1.genericPoint).subschemeι ≫ comapRestrict W f) gg))
    rw [← hcomp, Function.comp_apply, properPushforward_apply_image_of_isClosedImmersion]
  · rw [properPushforward_apply_of_notMem_range _ _ _ _ _ _ _ hx]
    refine (finsum_eq_zero_of_forall_eq_zero fun V ↦ ?_).symm
    refine mul_eq_zero_of_right _ ?_
    refine properPushforward_apply_of_notMem_range _ _ _ _ _ _ _ fun hmem ↦ hx ?_
    obtain ⟨w, hw⟩ := hmem
    exact ⟨(integralComponentAt V.2.1.genericPoint).subschemeι.base w, hw⟩

end Stacks.Chow

end
