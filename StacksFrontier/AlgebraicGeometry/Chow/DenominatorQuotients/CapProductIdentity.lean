module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.ClassRule
public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.ClosedImmersionCarrier
public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.ComponentDivisorClass
public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.CycleIdentity
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisorEquivalence

/-!
# Part (4) of Stacks 02SW as a cap product

In the situation of [Stacks, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW) — `X` locally of
finite type over the base of a Chow situation with `dim_δ(X) ≤ k + 1` and no embedded points, `ℱ`
coherent of full support with no embedded associated points, `ℒ` invertible and `s` a regular
meromorphic section of `ℒ` — part (4) reads

  `[𝒬₂]_k - [𝒬₁]_k = ∑ᵢ mᵢ (Xᵢ → X)_* div_{ℒ|_{Xᵢ}}(sᵢ)`   in   `Z_k(X)`.

The right-hand side is, up to rational equivalence, the cap product
`c₁(ℒ) ∩ [ℱ]_{k+1}` of [Stacks, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO): the cap
product is computed on the same locally finite presentation of `[ℱ]_{k+1}`, and on each component
the cycle it uses and the divisor of the restriction of `s` have the same class. So part (4)
becomes an identity in the Chow group:

  `c₁(ℒ) ∩ [ℱ]_{k+1} = [[𝒬₂]_k - [𝒬₁]_k]`   in   `CH_k(X)`.

## Main results

* `Stacks.Chow.firstChernClassCapOfInvertible_cycleAssociatedToCoherentSheaf_eq_mk_sub` — the
  identity above.
* `Stacks.Chow.firstChernClassCapOfInvertible_cycleAssociatedToCoherentSheaf_eq_mk_sub'` — the
  same identity with the witness that `[ℱ]_{k+1}` is defined discharged from
  `dim_δ(X) ≤ k + 1`, so that its hypotheses are exactly the five assumptions of the tag.
* `Stacks.Chow.denominatorQuotients_shortExact_isCoherent_and_firstChernClassCap` — the whole of
  Tag 02SW, parts (1), (2), (3) and (4) together, under the hypotheses of the source and nothing
  more. This is the declaration carrying the tag; the results above and the parts assembled from
  `StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.Basic`,
  `StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.ComponentDivisor` and
  `StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.CycleIdentity` are its components.

## Implementation notes

The presentation of `[ℱ]_{k+1}` fed to the component formula of Tag 02SO
(`Stacks.Chow.firstChernClassCap_finsum`) is the one of
`Stacks.Chow.cycleAssociatedToCoherentSheaf_apply_eq_finsum`, indexed by
`Stacks.Chow.topSupportPoints`; that is also the index set over which part (4) sums, so the two
locally finite sums have the same index and the same multiplicities, and
[Stacks, Tag 02RZ](https://stacks.math.columbia.edu/tag/02RZ) —
`Stacks.Chow.rationallyEquivalent_finsum_of_closedSupports` — assembles the componentwise
equivalences of
`Stacks.Chow.rationallyEquivalent_firstChernComponentCycleRule_componentDivisorCycleOn` into one
rational equivalence on `X`.

**The coefficient of a pushed-forward multiple of a cycle** is re-derived here as a `private`
lemma, so that this module does not have to import
`StacksFrontier.AlgebraicGeometry.Chow.FirstChernClassTensor` for the one statement
`Stacks.Chow.properPushforward_zsmul_apply`; it is two lines from `map_zsmul` for
`Stacks.Chow.properPushforwardHom`.

## References

* [Stacks Project, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02RZ](https://stacks.math.columbia.edu/tag/02RZ)
* [Stacks Project, Tag 02QX](https://stacks.math.columbia.edu/tag/02QX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}} (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (L F : X.Modules) (s : AlgebraicGeometry.MeromorphicSection X.sheaf L) [F.IsCoherent] {k : ℤ}
  (hdim : schemeDeltaDimension C f ≤ ((k + 1 : ℤ) : EInt))
  (hX : HasNoEmbeddedPoints X)
  (hF : HasNoEmbeddedAssociatedPoints F)
  (hSupp : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F).supp = Set.univ)
  [hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (hs : IsRegularMeromorphicSection X.sheaf L s)
  (hFk : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ f) ≤ ((k + 1 : ℤ) : EInt))

/-- The difference of the denominator quotient cycles at a point is the sum over the components
of `ℱ` of the multiplicities times the coefficients of the component divisor cycles. -/
private theorem denominatorQuotients_cycle_sub_apply_eq_finsum_componentDivisorCycle (x : X) :
    (denominatorSectionQuotientCycle C f L F s hdim hX hF hSupp hL hs).1 x -
        (denominatorQuotientCycle C f L F s hdim hX hF hSupp hL hs).1 x =
      ∑ᶠ j : topSupportPoints C f F (k + 1), sheafMultiplicity F j.1 *
        (componentDivisorCycle C f L s hL hs
          (mem_genericPoints_of_relativeDimension_eq C f hdim j.2.2) j.2.2).1 x := by
  rw [denominatorQuotients_cycle_sub_apply_eq_finsum C f L F s hdim hX hF hSupp hL hs x,
    ← finsum_set_coe_eq_finsum_mem]
  exact finsum_congr fun j =>
    congrArg (fun z : ℤ => sheafMultiplicity F j.1 * z)
      (componentDivisorCoefficient_eq C f L s hL hs
        (mem_genericPoints_of_relativeDimension_eq C f hdim j.2.2) j.2.2 x)

/-- **Part (4) of [Stacks, Tag 02SW] as a cap product.** In the situation of Tag 02SW the class
in `CH_k(X)` of the difference `[𝒬₂]_k - [𝒬₁]_k` of the cycles of the two denominator quotients
is the cap product `c₁(ℒ) ∩ [ℱ]_{k+1}` of [Stacks, Tag 02SO].

Both sides are locally finite sums over the points of the support of `ℱ` of delta-dimension
`k + 1`, with the multiplicities of `ℱ` as coefficients: for the left-hand side by part (4) of
the tag, for the right-hand side by the component formula of Tag 02SO applied to the presentation
`Stacks.Chow.cycleAssociatedToCoherentSheaf_apply_eq_finsum`. The summands agree in the Chow group
of each component by [Stacks, Tag 02SJ] part (2), and Tag 02RZ sums those equivalences.

The witness `hFk` that `[ℱ]_{k+1}` is defined is a hypothesis only because
`Stacks.Chow.cycleAssociatedToCoherentSheaf` takes it as an argument, and it is implied by
`hdim`; `Stacks.Chow.firstChernClassCapOfInvertible_cycleAssociatedToCoherentSheaf_eq_mk_sub'`
below is the same identity with it discharged, at exactly the hypotheses of the tag. -/
theorem firstChernClassCapOfInvertible_cycleAssociatedToCoherentSheaf_eq_mk_sub :
    firstChernClassCapOfInvertible C f k L (cycleAssociatedToCoherentSheaf C f F (k + 1) hFk) =
      QuotientAddGroup.mk
        (denominatorSectionQuotientCycle C f L F s hdim hX hF hSupp hL hs -
          denominatorQuotientCycle C f L F s hdim hX hF hSupp hL hs) := by
  classical
  obtain ⟨β, hcap, hβ⟩ := firstChernClassCap_finsum C f k (firstChernComponentCycleRule C f k L)
    (fun j : topSupportPoints C f F (k + 1) => integralComponentAt j.1)
    (fun j => isIntegral_integralComponentAt j.1)
    (fun j => schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C f j.1 j.2.2)
    (locallyFinite_topSupportSubscheme C f F (k + 1) hFk)
    (fun j => sheafMultiplicity F j.1)
    (cycleAssociatedToCoherentSheaf C f F (k + 1) hFk)
    (cycleAssociatedToCoherentSheaf_apply_eq_finsum C f F (k + 1) hFk)
  have hgen : ∀ j : topSupportPoints C f F (k + 1), j.1 ∈ genericPoints X := fun j =>
    mem_genericPoints_of_relativeDimension_eq C f hdim j.2.2
  rw [show firstChernClassCapOfInvertible C f k L
        (cycleAssociatedToCoherentSheaf C f F (k + 1) hFk) =
      firstChernClassCap C f k (firstChernComponentCycleRule C f k L)
        (cycleAssociatedToCoherentSheaf C f F (k + 1) hFk) from rfl, hcap]
  refine QuotientAddGroup.eq_iff_sub_mem.2 (rationallyEquivalent_finsum_of_closedSupports C f k
    (fun j : topSupportPoints C f F (k + 1) => integralComponentAt j.1)
    (locallyFinite_topSupportSubscheme C f F (k + 1) hFk)
    (fun j => sheafMultiplicity F j.1 • firstChernComponentCycleRule C f k L
      (integralComponentAt j.1) (isIntegral_integralComponentAt j.1)
      (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C f j.1 j.2.2))
    (fun j => sheafMultiplicity F j.1 • componentDivisorCycleOn C f L s hL hs (hgen j) j.2.2)
    (fun j => ?_) (fun x => ?_) (fun x => ?_))
  · have hm := (rationalEquivalences C ((integralComponentAt j.1).subschemeι ≫ f) k).zsmul_mem
      (rationallyEquivalent_firstChernComponentCycleRule_componentDivisorCycleOn C f L s hs
        (hgen j) j.2.2) (sheafMultiplicity F j.1)
    rwa [smul_sub] at hm
  · rw [hβ x]
    refine finsum_congr fun j => ?_
    exact (properPushforward_zsmul_apply_aux C _ f _ rfl k _ _ x).symm
  · refine (denominatorQuotients_cycle_sub_apply_eq_finsum_componentDivisorCycle C f L F s hdim
      hX hF hSupp hs x).trans (finsum_congr fun j => ?_)
    exact (properPushforward_zsmul_apply_aux C _ f _ rfl k _ _ x).symm

include hdim in
/-- The cycle `[ℱ]_{k+1}` is defined as soon as `dim_δ(X) ≤ k + 1`: every point of `X`, so in
particular every point of the support of `ℱ`, then has relative dimension at most `k + 1`. -/
theorem schemeDeltaDimension_reducedSupport_le_of_schemeDeltaDimension_le :
    schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ f) ≤ ((k + 1 : ℤ) : EInt) :=
  schemeDeltaDimension_reducedSupport_le C f F fun x _ =>
    StalkLocalSituation.relativeDimension_le_of_schemeDeltaDimension_le C f hdim x

/-- **The last assertion of [Stacks, Tag 02SW]**, at exactly the hypotheses of the tag:

  `[𝒬₂]_k - [𝒬₁]_k = c₁(ℒ) ∩ [ℱ]_{k+1}`   in   `CH_k(X)`.

This is
`Stacks.Chow.firstChernClassCapOfInvertible_cycleAssociatedToCoherentSheaf_eq_mk_sub` with the
witness that `[ℱ]_{k+1}` is defined supplied from `dim_δ(X) ≤ k + 1` rather than assumed. -/
theorem firstChernClassCapOfInvertible_cycleAssociatedToCoherentSheaf_eq_mk_sub' :
    firstChernClassCapOfInvertible C f k L (cycleAssociatedToCoherentSheaf C f F (k + 1)
        (schemeDeltaDimension_reducedSupport_le_of_schemeDeltaDimension_le C f F hdim)) =
      QuotientAddGroup.mk
        (denominatorSectionQuotientCycle C f L F s hdim hX hF hSupp hL hs -
          denominatorQuotientCycle C f L F s hdim hX hF hSupp hL hs) :=
  firstChernClassCapOfInvertible_cycleAssociatedToCoherentSheaf_eq_mk_sub C f L F s hdim hX hF
    hSupp hs _

/-! ### The lemma -/

/-- **Stacks 02SW.** Let `(S, δ)` be as in Situation 42.7.1, let `X` be locally of finite type
over `S`, let `ℒ` be an invertible `𝒪_X`-module, let `ℱ` be a coherent `𝒪_X`-module and let
`s ∈ Γ(X, 𝒦_X(ℒ))` be a meromorphic section of `ℒ`. Assume

1. `dim_δ(X) ≤ k + 1`,
2. `X` has no embedded points,
3. `ℱ` has no embedded associated points,
4. the support of `ℱ` is `X`, and
5. the section `s` is regular meromorphic.

Let `ℐ ⊂ 𝒪_X` be the ideal of denominators of `s`. Then we have the following:

1. there are short exact sequences

     `0 ⟶ ℐℱ ⟶^1 ℱ ⟶ 𝒬₁ ⟶ 0`,   `0 ⟶ ℐℱ ⟶^s ℱ ⊗_{𝒪_X} ℒ ⟶ 𝒬₂ ⟶ 0`;

2. the coherent sheaves `𝒬₁`, `𝒬₂` are supported in δ-dimension `≤ k`;
3. the section `s` restricts to a regular meromorphic section `sᵢ` on every irreducible
   component `Xᵢ` of `X` of δ-dimension `k + 1`; and
4. writing `[ℱ]_{k+1} = ∑ᵢ mᵢ[Xᵢ]` we have

     `[𝒬₂]_k - [𝒬₁]_k = ∑ᵢ mᵢ (Xᵢ ⟶ X)_* div_{ℒ|_{Xᵢ}}(sᵢ)`   in   `Z_k(X)`,

   in particular

     `[𝒬₂]_k - [𝒬₁]_k = c₁(ℒ) ∩ [ℱ]_{k+1}`   in   `CH_k(X)`.

This is the declaration carrying the tag; the results above and in
`StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.Basic`,
`StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.ComponentDivisor` and
`StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.CycleIdentity` are its components.

An irreducible component of `X` is named by its generic point `η`, carrying the reduced induced
structure `Stacks.Chow.integralComponentAt η`; `sᵢ` is `Stacks.Chow.componentMeromorphicSection`,
the pullback of `s` along its closed immersion, and `(Xᵢ ⟶ X)_* div_{ℒ|_{Xᵢ}}(sᵢ)` is
`Stacks.Chow.componentDivisorCycle`.

The presentation `[ℱ]_{k+1} = ∑ᵢ mᵢ[Xᵢ]` is the first conjunct of part (4): its index is
`Stacks.Chow.topSupportPoints C f ℱ (k + 1)`, the points of the support of `ℱ` of
δ-dimension `k + 1`, and its coefficients `mᵢ` are the multiplicities
`Stacks.Chow.sheafMultiplicity ℱ ηᵢ`. The second conjunct — the equality in `Z_k(X)` — is read
coefficientwise, at an arbitrary point `x` of `X`, because the family of components of
δ-dimension `k + 1` is locally finite rather than finite, so both sides exist as locally finite
sums; a cycle is its coefficient function, so this is the asserted equality of cycles. -/
@[stacks 02SW "parts (1), (2), (3) and (4)"]
theorem denominatorQuotients_shortExact_isCoherent_and_firstChernClassCap
    (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (L F : X.Modules) (s : AlgebraicGeometry.MeromorphicSection X.sheaf L) [F.IsCoherent]
    {k : ℤ}
    (hdim : schemeDeltaDimension C f ≤ ((k + 1 : ℤ) : EInt))
    (hX : HasNoEmbeddedPoints X)
    (hF : HasNoEmbeddedAssociatedPoints F)
    (hSupp : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F).supp = Set.univ)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hs : IsRegularMeromorphicSection X.sheaf L s) :
    -- (1) `0 ⟶ ℐℱ ⟶^1 ℱ ⟶ 𝒬₁ ⟶ 0` is short exact
    (denominatorQuotientShortComplex X L F s).ShortExact ∧
    -- (1) `0 ⟶ ℐℱ ⟶^s ℱ ⊗ ℒ ⟶ 𝒬₂ ⟶ 0` is short exact
    (@denominatorSectionQuotientShortComplex X L F s
        (LocallyOfFiniteType.isLocallyNoetherian f) hL hs inferInstance hF hSupp).ShortExact ∧
    -- (2) `𝒬₁` and `𝒬₂` are coherent
    (denominatorQuotient X L F s).IsCoherent ∧
    (@denominatorSectionQuotient X L F s (LocallyOfFiniteType.isLocallyNoetherian f) hL hs
        inferInstance hF hSupp).IsCoherent ∧
    -- (2) and are supported in δ-dimension `≤ k`
    schemeDeltaDimension C ((@reducedSupport X (denominatorQuotient X L F s)
        (isCoherent_denominatorQuotient C f L F s hdim hX hF hSupp hL hs)).subschemeι ≫ f)
      ≤ (k : EInt) ∧
    schemeDeltaDimension C ((@reducedSupport X
        (@denominatorSectionQuotient X L F s (LocallyOfFiniteType.isLocallyNoetherian f) hL hs
          inferInstance hF hSupp)
        (isCoherent_denominatorSectionQuotient C f L F s hdim hX hF hSupp hL hs)).subschemeι ≫ f)
      ≤ (k : EInt) ∧
    -- (3) `s` restricts to a regular meromorphic section on every component of δ-dimension `k+1`
    (∀ (η : X) (hη : η ∈ genericPoints X),
        relativeDimension C.dimensionFunction f η = k + 1 →
        AlgebraicGeometry.IsRegularMeromorphicSection (integralComponentAt η).subscheme.sheaf
          ((Scheme.Modules.pullback (integralComponentAt η).subschemeι).obj L)
          (componentMeromorphicSection L s hη)) ∧
    -- (4) `[ℱ]_{k+1} = ∑ᵢ mᵢ[Xᵢ]`, over the components of δ-dimension `k + 1`
    (∀ x : X, (cycleAssociatedToCoherentSheaf C f F (k + 1)
          (schemeDeltaDimension_reducedSupport_le_of_schemeDeltaDimension_le C f F hdim)).1 x =
        ∑ᶠ j : topSupportPoints C f F (k + 1), sheafMultiplicity F j.1 *
          (cycleAssociatedToClosedSubscheme C f (integralComponentAt j.1).subschemeι (k + 1)).1
            x) ∧
    -- (4) `[𝒬₂]_k - [𝒬₁]_k = ∑ᵢ mᵢ (Xᵢ ⟶ X)_* div_{ℒ|_{Xᵢ}}(sᵢ)` in `Z_k(X)`
    (∀ x : X,
        (denominatorSectionQuotientCycle C f L F s hdim hX hF hSupp hL hs).1 x -
            (denominatorQuotientCycle C f L F s hdim hX hF hSupp hL hs).1 x =
          ∑ᶠ j : topSupportPoints C f F (k + 1), sheafMultiplicity F j.1 *
            (componentDivisorCycle C f L s hL hs
              (mem_genericPoints_of_relativeDimension_eq C f hdim j.2.2) j.2.2).1 x) ∧
    -- (4) in particular `[𝒬₂]_k - [𝒬₁]_k = c₁(ℒ) ∩ [ℱ]_{k+1}` in `CH_k(X)`
    QuotientAddGroup.mk
        (denominatorSectionQuotientCycle C f L F s hdim hX hF hSupp hL hs -
          denominatorQuotientCycle C f L F s hdim hX hF hSupp hL hs) =
      firstChernClassCapOfInvertible C f k L (cycleAssociatedToCoherentSheaf C f F (k + 1)
        (schemeDeltaDimension_reducedSupport_le_of_schemeDeltaDimension_le C f F hdim)) := by
  classical
  refine ⟨denominatorQuotientShortComplex_shortExact C f L F s hdim hX hF hSupp hL hs,
    denominatorSectionQuotientShortComplex_shortExact C f L F s hdim hX hF hSupp hL hs,
    isCoherent_denominatorQuotient C f L F s hdim hX hF hSupp hL hs,
    isCoherent_denominatorSectionQuotient C f L F s hdim hX hF hSupp hL hs,
    schemeDeltaDimension_denominatorQuotient_le C f L F s hdim hX hF hSupp hL hs,
    schemeDeltaDimension_denominatorSectionQuotient_le C f L F s hdim hX hF hSupp hL hs,
    fun η hη _ => isRegularMeromorphicSection_componentMeromorphicSection L s hL hs hη,
    cycleAssociatedToCoherentSheaf_apply_eq_finsum C f F (k + 1)
      (schemeDeltaDimension_reducedSupport_le_of_schemeDeltaDimension_le C f F hdim),
    fun x => ?_,
    (firstChernClassCapOfInvertible_cycleAssociatedToCoherentSheaf_eq_mk_sub' C f L F s hdim hX
      hF hSupp hs).symm⟩
  exact denominatorQuotients_cycle_sub_apply_eq_finsum_componentDivisorCycle C f L F s hdim hX hF
    hSupp hs x

end Stacks.Chow

end
