module

public import StacksFrontier.AlgebraicGeometry.F6Rank136.ExceptionalCurveContractionBirational
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DominateByNormalizedBlowUps.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.GenericPoints
public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.EffectiveCartier

/-!
# Dropping integrality from the 0C2L chain

`AlgebraicGeometry.isContractionOfExceptionalCurve_toNormalization_of_steinSetup_of_isBirational`
asks for `[IsIntegral X]` and for the Stein base to be integral. Those are **surplus**
hypotheses: the section [Stacks, Tag 0C2I] in which 0C2L lives carries no standing situation,
and the word "integral" does not occur anywhere in it. This file removes them, leaving only
`[IsReduced X]`, which is a hypothesis of the isomorphism criterion itself
(`AlgebraicGeometry.isIso_of_comp_blowUpToBase_eq_of_isBirational`) and so cannot be dropped
here.

Integrality entered through one step: the criterion wants `IsBirational g` of the *classifying*
morphism, and the only route to it was
`AlgebraicGeometry.isBirational_of_comp_blowUpToBase` ([Stacks, Tag 02OS]), which trades
`IsBirational f` for `IsBirational g` and wants both schemes integral. The trade is unnecessary,
because `g` is already known to be an isomorphism over `b^{-1}(Y ∖ {y})`
(`AlgebraicGeometry.isIso_morphismRestrict_blowUpClassifying`), and
`AlgebraicGeometry.isBirational_of_isIso_morphismRestrict` turns that into
`IsBirational g` given only that every generic point of the blowup lies in that open and every
generic point of `X` is carried into it. Both follow from one observation, below: **the support
of an effective Cartier divisor contains no generic point**
(`AlgebraicGeometry.notMem_support_of_mem_genericPoints_of_isEffectiveCartierDivisor`, which
needs no reducedness — the elements of a minimal prime are zerodivisors). Applied to

* `D`, the exceptional curve, which is an effective Cartier divisor and whose support is
  `f^{-1}(y)` by `hfibre`, it says no generic point of `X` is carried to `y`;
* the exceptional ideal `ℐ_y · 𝒪_{Bl}`, which is an effective Cartier divisor by the universal
  property of blowing up, it says no generic point of the blowup lies over `y`.

So the same lemma serves both, and `hI0` and `hbir` disappear along with the integrality: the
criterion's `IsBirational g` is now produced rather than assumed.

## Main results

* `AlgebraicGeometry.base_ne_of_mem_genericPoints_of_isEffectiveCartierDivisor_comap` — if the
  inverse image of an ideal sheaf supported at `y` is an effective Cartier divisor, no generic
  point of the source is carried to `y`.
* `AlgebraicGeometry.isBirational_blowUpClassifying_of_isIso_c` — the classifying morphism of a
  proper `f` with `f_* 𝒪_X = 𝒪_Y` which is quasi-finite off the curve is birational, with no
  integrality and no reducedness.
* `AlgebraicGeometry.isIso_blowUpClassifying_of_steinSetup_of_isReduced` — `hclassify` for a
  morphism carrying the Stein data, asking only `[IsReduced X]`.
* `AlgebraicGeometry.isContractionOfExceptionalCurve_toNormalization_of_steinSetup_of_isReduced`
  — both conjuncts of [Stacks, Tag 0C2L] with `hres`, `hI0`, `hbir` **and** integrality all
  discharged.

## What 0C2L still asks for

The tag is **not** registered here. Two inputs remain, plus `[IsReduced X]`. Each is stated below
together with the links that *do* exist, so that neither is looked for again:

* `hreg`, `hdim` and `hfibre` — in the source these come from [Stacks, Tag 0C2K]. That tag is a
  statement about `formalNeighborhoodRing D` on the **source**, whereas `hreg` and `hdim` are
  about `𝒪_{Y, y}` on the **base**. Three of the four links of the transport are present:
  [Stacks, Tag 02OD] itself, as
  `Stacks.FormalFunctions.nonempty_adicCompletionHigherDirectImageStalkEquiv`, with the `p = 0`
  structure-sheaf form `Stacks.FormalFunctions.isFormalFunctionsStalk_of_isProper`; and the
  descent of regularity and of dimension from the completion, as
  `isRegularLocalRing_iff_adicCompletion_maximalIdeal` ([Stacks, Tag 07NY]) and
  `ringKrullDim_adicCompletion_maximalIdeal` ([Stacks, Tag 07NV]), which are the two tags the
  source cites here. What was missing is the **cofinality** `Eₙ ⊆ X ×_Y Spec(𝒪/𝔪ⁿ) ⊆ E_{nm}`.
  That is now proved at the level of ideal sheaves, in
  `ExceptionalCurveContractionCofinality.lean` of this directory, as
  `AlgebraicGeometry.exists_forall_pow_le_comap_pow_vanishingIdeal_singleton`, over one
  topological hypothesis: that the set-theoretic fibre over `y` is contained in the support of
  `D`. Two things previously recorded as absent here are not: the inverse-image ideal sheaf is
  multiplicative, as `Stacks.IdealSheaf.comap_pow`, and the ideal-sheaf consequence of
  [Stacks, Tag 01Y9] is
  `AlgebraicGeometry.Scheme.IdealSheafData.exists_pow_le_iff_le_radical`. What remains between
  that cofinality and `hreg`, `hdim`, `hfibre` is the passage from cofinal towers of *ideal
  sheaves* to an isomorphism of the two limits of *sections* — and 02OD as formalized gives only a
  linear bijection, where transporting `IsRegularLocalRing` wants a ring isomorphism. Note also
  that 0C2K's regularity and dimension clauses
  (`AlgebraicGeometry.Scheme.IdealSheafData.isRegularLocalRing_formalNeighborhoodRing` and
  `AlgebraicGeometry.Scheme.IdealSheafData.ringKrullDim_formalNeighborhoodRing_eq_two`) still
  rest, through the lemma of the namespace `AlgebraicGeometry.Scheme.IdealSheafData` named
  `isNoetherianCompleteLocalRing_and_isRegular_and_dim_formalNeighborhoodRing_of_monomialValueLaw`,
  on the monomial value law
  `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.MonomialValueLaw`,
  which nothing concludes;
* `AlgebraicGeometry.Scheme.Hom.QuasiFiniteAt` for the classifying morphism somewhere over each
  point of the exceptional curve of the blowup. This is **not** blocked on the identification of
  that curve with `𝐏¹` over the residue field, which is part (1) of [Stacks, Tag 0AGQ] and is
  proved, as
  `Stacks.Blowup.exists_isClosedImmersion_isPullback_projectiveLine_blowUpSpec_maximalIdeal`. It
  is blocked on the `IsExceptionalCurveOfFirstKind` **witness** for the blowup: no declaration
  concludes `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind` of an
  `AlgebraicGeometry.exceptionalIdeal`. Of the two clauses of that predicate the first is
  already available — `Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal` is an instance
  and fires for any centre — so what is wanted is the parameter
  `e : projectiveLineProj κ ≅ (exceptionalIdeal _).subscheme`, which means 0AGQ part (1)
  globalised off `Stacks.Blowup.blowUpSpec` and turned from an `IsPullback` into that
  isomorphism, together with the normal-sheaf clause `𝒩 ≅ 𝒪(-1)`, for which nothing exists.
  Only with that witness does
  `Stacks.ResolutionOfSurfaces.quasiFiniteAt_of_exceptionalCurvePair` become applicable — and
  that machine in turn carries `Stacks.ResolutionOfSurfaces.ConormalSequenceSecondArrow`, which
  is a standing hypothesis of the whole [Stacks, Tag 0C5R] chain and is discharged nowhere, and
  asks for a nonzero conormal comparison map. The weaker machines
  `Stacks.UnramifiedAlongImmersion.quasiFiniteAt_of_isZero_pullback_relativeDifferentials` and
  `Stacks.ResolutionOfSurfaces.quasiFiniteAt_of_isZero_pullback_relativeDifferentials_subscheme`
  need no exceptional-curve data at all, but deliver quasi-finiteness at points in the image of
  an immersion into the *source*, where `hqfE` asks for it over each point of the *blowup*.

`[IsReduced X]` is not a hypothesis of the tag either, so it must still be named by any carrier
that eventually takes it.

## References

* [Stacks Project, Tag 0C2I](https://stacks.math.columbia.edu/tag/0C2I)
* [Stacks Project, Tag 0C2L](https://stacks.math.columbia.edu/tag/0C2L)
* [Stacks Project, Tag 0BFP](https://stacks.math.columbia.edu/tag/0BFP)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **No generic point is carried to a point whose inverse-image ideal is an effective Cartier
divisor.** If `I` is an ideal sheaf on `Y` whose support is the single point `y`, and the inverse
image `I · 𝒪_X` along `f` is an effective Cartier divisor, then `f` carries no generic point of
an irreducible component of `X` to `y`.

The support of an effective Cartier divisor contains no generic point
(`AlgebraicGeometry.notMem_support_of_mem_genericPoints_of_isEffectiveCartierDivisor`) — the
elements of a minimal prime are zerodivisors, so no reducedness is needed — and the support of
`I · 𝒪_X` is `f^{-1}` of the support of `I`. -/
public theorem base_ne_of_mem_genericPoints_of_isEffectiveCartierDivisor_comap
    {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y)
    (hcart : Stacks.Divisors.IsEffectiveCartierDivisor (I.comap f))
    (y : Y) (hsupp : I.supportSet = ({y} : Set Y))
    {x : X} (hx : x ∈ genericPoints X) :
    f.base x ≠ y := by
  intro hxy
  refine notMem_support_of_mem_genericPoints_of_isEffectiveCartierDivisor _ hcart hx ?_
  simp only [Scheme.IdealSheafData.mem_supportSet_iff_mem_support,
    Scheme.IdealSheafData.support_comap]
  change f.base x ∈ I.supportSet
  rw [hsupp]
  exact hxy

/-- **The classifying morphism is birational**, with no integrality and no reducedness. It is an
isomorphism over `b^{-1}(Y ∖ {y})`, and that open contains every generic point of the blowup and
receives every generic point of `X`, both by
`AlgebraicGeometry.base_ne_of_mem_genericPoints_of_isEffectiveCartierDivisor_comap`. -/
public theorem isBirational_blowUpClassifying_of_isIso_c {X Y : Scheme.{u}}
    {D : X.IdealSheafData} {k : Type u} [Field k]
    {e : projectiveLineProj k ≅ D.subscheme} (hE : D.IsExceptionalCurveOfFirstKind k e)
    (f : X ⟶ Y) [IsProper f] [IsIso f.c] (y : Y) (hy : IsClosed ({y} : Set Y))
    (hmaps : ∀ x ∈ (D.support : Set X), f.base x = y)
    (hqf : ∀ x ∉ (D.support : Set X), quasiFiniteAt f x)
    (hfibre : D = (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).comap f)
    (g : X ⟶ AlgebraicGeometry.blowUp
      (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)))
    (hg : g ≫ AlgebraicGeometry.blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) = f) :
    IsBirational g := by
  obtain ⟨W, hWc⟩ : ∃ W : Y.Opens, (W : Set Y) = ({y} : Set Y)ᶜ :=
    ⟨⟨{y}ᶜ, hy.isOpen_compl⟩, rfl⟩
  have hW : ∀ w : AlgebraicGeometry.blowUp
      (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)),
      (AlgebraicGeometry.blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y))).base w ≠ y →
      (AlgebraicGeometry.blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y))).base w ∈ W :=
    fun w hw ↦ by rw [← SetLike.mem_coe, hWc]; exact hw
  refine isBirational_of_isIso_morphismRestrict g _
    (isIso_morphismRestrict_blowUpClassifying (D := D) f y hy hmaps hqf g hg W hWc) ?_ ?_
  · intro x hx
    refine hW _ ?_
    rw [← Scheme.Hom.comp_apply, hg]
    exact base_ne_of_mem_genericPoints_of_isEffectiveCartierDivisor_comap _ f
      (hfibre ▸ hE.isEffectiveCartierDivisor) y (supportSet_vanishingIdeal_singleton hy) hx
  · intro w hw
    exact hW _ (base_ne_of_mem_genericPoints_of_isEffectiveCartierDivisor_comap _ _
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal _) y
      (supportSet_vanishingIdeal_singleton hy) hw)

/-- **`hclassify` for a morphism carrying the Stein data, asking only `[IsReduced X]`.** Against
`AlgebraicGeometry.isIso_blowUpClassifying_of_steinSetup` the integrality of both schemes, the
nonvanishing `hI0` of the centre and the birationality `hbir` of `f` are all gone:
`IsBirational g` is produced by
`AlgebraicGeometry.isBirational_blowUpClassifying_of_isIso_c` instead of being routed through
[Stacks, Tag 02OS]. -/
public theorem isIso_blowUpClassifying_of_steinSetup_of_isReduced {X Y : Scheme.{u}}
    [IsReduced X] {D : X.IdealSheafData} {k : Type u} [Field k]
    {e : projectiveLineProj k ≅ D.subscheme} (hE : D.IsExceptionalCurveOfFirstKind k e)
    (f : X ⟶ Y) (y : Y) (hsetup : D.IsSteinContractionSetup f y)
    (hy : IsClosed ({y} : Set Y))
    (hreg : IsRegularLocalRing (Y.presheaf.stalk y))
    (hdim : ringKrullDim (Y.presheaf.stalk y) = 2)
    (hfibre : D = (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).comap f)
    (g : X ⟶ AlgebraicGeometry.blowUp
      (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)))
    (hg : g ≫ AlgebraicGeometry.blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) = f)
    (hqfE : ∀ w : AlgebraicGeometry.blowUp
        (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)),
      AlgebraicGeometry.blowUpToBase
          (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) w = y →
        ∃ x : X, g.base x = w ∧ g.QuasiFiniteAt x) :
    IsIso g :=
  have := hsetup.isNoetherian
  have := hsetup.isProper
  have := hsetup.isIso_c
  have hsupp : ∀ x ∈ (D.support : Set X), f.base x = y :=
    (D.forall_subschemeι_base_eq_iff_forall_mem_support f y).1 hsetup.base_eq
  isIso_of_comp_blowUpToBase_eq_of_isBirational _ y hy rfl hreg hdim f g hg
    (isBirational_blowUpClassifying_of_isIso_c hE f y hy hsupp hsetup.quasiFinite_of_notMem
      hfibre g hg)
    hqfE
    fun w hw ↦ exists_isIso_morphismRestrict_blowUpClassifying (D := D) f y hy hsupp
      hsetup.quasiFinite_of_notMem g hg w hw

/-- **Both conjuncts of [Stacks, Tag 0C2L] with integrality gone.** The first factor
`f.toNormalization` of the Stein factorization of `f` is a contraction of the exceptional curve
— so a contraction exists and it is the Stein factorization of `f` — granted `[IsReduced X]` and,
of every morphism carrying an
`AlgebraicGeometry.Scheme.IdealSheafData.IsSteinContractionSetup`:

* `hreg` and `hdim`, that the local ring at the image point is regular of dimension two;
* `hfibre`, that the scheme-theoretic fibre over that point is the curve;
* `hqfE`, that the classifying morphism is quasi-finite somewhere over each point of the
  exceptional curve of the blowup.

Against
`AlgebraicGeometry.isContractionOfExceptionalCurve_toNormalization_of_steinSetup_of_isIntegral`
the binders `hintegral`, `hI0` and `hbir` are all gone, and `[IsIntegral X]` has weakened to
`[IsReduced X]`. -/
public theorem isContractionOfExceptionalCurve_toNormalization_of_steinSetup_of_isReduced
    {X Y : Scheme.{u}} [IsNoetherian Y] [IsReduced X] {D : X.IdealSheafData} {k : Type u}
    [Field k] {e : projectiveLineProj k ≅ D.subscheme} (hE : D.IsExceptionalCurveOfFirstKind k e)
    (f : X ⟶ Y) [IsProper f] (y : Y)
    (hmaps : ∀ z : D.subscheme, f.base (D.subschemeι.base z) = y)
    (hqf : ∀ x ∉ (D.support : Set X), quasiFiniteAt f x)
    (hreg : ∀ (Y' : Scheme.{u}) (f' : X ⟶ Y') (y' : Y'),
      D.IsSteinContractionSetup f' y' → IsRegularLocalRing (Y'.presheaf.stalk y'))
    (hdim : ∀ (Y' : Scheme.{u}) (f' : X ⟶ Y') (y' : Y'),
      D.IsSteinContractionSetup f' y' → ringKrullDim (Y'.presheaf.stalk y') = 2)
    (hfibre : ∀ (Y' : Scheme.{u}) (f' : X ⟶ Y') (y' : Y'),
      D.IsSteinContractionSetup f' y' → ∀ hy' : IsClosed ({y'} : Set Y'),
        D = (Scheme.IdealSheafData.vanishingIdeal (⟨{y'}, hy'⟩ : Closeds Y')).comap f')
    (hqfE : ∀ (Y' : Scheme.{u}) (f' : X ⟶ Y') (y' : Y'),
      D.IsSteinContractionSetup f' y' → ∀ (hy' : IsClosed ({y'} : Set Y'))
        (g : X ⟶ AlgebraicGeometry.blowUp
          (Scheme.IdealSheafData.vanishingIdeal (⟨{y'}, hy'⟩ : Closeds Y'))),
        g ≫ AlgebraicGeometry.blowUpToBase
            (Scheme.IdealSheafData.vanishingIdeal (⟨{y'}, hy'⟩ : Closeds Y')) = f' →
        ∀ w : AlgebraicGeometry.blowUp
            (Scheme.IdealSheafData.vanishingIdeal (⟨{y'}, hy'⟩ : Closeds Y')),
          AlgebraicGeometry.blowUpToBase
              (Scheme.IdealSheafData.vanishingIdeal (⟨{y'}, hy'⟩ : Closeds Y')) w = y' →
            ∃ x : X, g.base x = w ∧ g.QuasiFiniteAt x) :
    IsContractionOfExceptionalCurve D f.toNormalization :=
  isContractionOfExceptionalCurve_toNormalization_of_steinSetup hE f y hmaps hqf hreg hdim
    hfibre fun Y' f' y' hsetup hy' g hgf ↦
      isIso_blowUpClassifying_of_steinSetup_of_isReduced hE f' y' hsetup hy'
        (hreg Y' f' y' hsetup) (hdim Y' f' y' hsetup) (hfibre Y' f' y' hsetup hy') g hgf
        (hqfE Y' f' y' hsetup hy' g hgf)

end AlgebraicGeometry

end
