module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Vanishing
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapClosedImmersionInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.CapProduct
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardUncontained
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.DivisorGysinComparison
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicCascade.DivisorCycle
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicCascade.RegularGenericValue
public import StacksFrontier.AlgebraicGeometry.Chow.PointClosureRelativeClosure
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionZeroScheme
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal

/-!
# Stacks 02TM, unconditionally

Let `X` be integral, locally Noetherian and locally of finite type over the base scheme `S` of
chapter 42 of the Stacks Project, of delta-dimension `k + 2`. Let `L` be an invertible
`𝒪_X`-module with a nonzero global section `s`, with zero scheme `i : D = Z(s) ⟶ X`, and let `N`
be an invertible `𝒪_X`-module with a nonzero meromorphic section `t`. Then

  `i^* div_N(t) = c₁(N|_D) ∩ [D]_{k+1}`  in  `A_k(D)`,

which is Lemma 42.30.1 of the source for `n = k + 2`. Nothing is assumed: the key formula of
Stacks 0AYC is `Stacks.Chow.KeyFormulaSituation.keyFormula_toKeyFormulaData` and the two
presentations the source's proof uses are produced here.

For an effective Cartier divisor `E` the pair `(𝒪_X(E), 1_E)` has `Z(1_E) = E`
(`Stacks.Divisors.zeroScheme_canonicalSection`) and `1_E ≠ 0`, so this gives the statement of the
source, `Stacks.Chow.gysin_divisorOfMeromorphicSection_eq_firstChernClassCap`, stated with the
divisor cycle of Stacks 02SJ (1) of a regular meromorphic section, the fundamental cycle of the
divisor, and `n = dim_δ(X)`; local Noetherianity there follows from the base.

## The argument

The source's proof has three moving parts, and all three are discharged.

* The rational equivalence on `D` is
  `Stacks.Chow.isRationallyEquivalentToZeroWithin_properPushforward_gysinCycle_sub` of
  `StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.DivisorGysinComparison`: the Gysin cycle of
  `div_N(t)`, pushed forward to `X`, differs from
  `∑_i ord_{B_i}(f_i) (Z_i → X)_* div_{N|Z_i}(t_i|Z_i)` by a cycle rationally equivalent to zero
  with witnesses inside `D`. Since `i` is a closed immersion this descends into `D`, by the lemma
  `isRationallyEquivalentToZero_of_properPushforward_isRationallyEquivalentToZeroWithin` of the
  namespace `Stacks.Chow`.

* The presentation of `div_N(t)` by the family of the situation with the orders
  `ord_{B_i}(g_i)` is
  `Stacks.Chow.KeyFormulaSituation.weilDivisorAlgebraicCycle_weilDivisorN_apply`, and the Gysin
  cycle then comes from the component formula of Stacks 02T8.

* The presentation of `[D]_{k+1}`, read as a cycle on `D`, is produced here: `[D]_{k+1}` is
  `div_L(s)` by Stacks 02SK, which the family presents with the orders `ord_{B_i}(f_i)`
  (`Stacks.Chow.KeyFormulaSituation.weilDivisorAlgebraicCycle_weilDivisorL_apply`), and the
  members carrying a nonzero order are exactly those contained in `D` — there `f_i = 1`
  otherwise. Each such member is the integral component of a point of `D`, by
  `Stacks.Chow.integralComponentIso`.

That `∑_i ord_{B_i}(f_i) (Z_i → X)_* div_{N|Z_i}(t_i|Z_i)` is the pushforward of a representative
of `c₁(N|_D) ∩ [D]_{k+1}` is read off the transported component rule of
`StacksFrontier.AlgebraicGeometry.Chow.ChernCapClosedImmersion`: the rule on `D` transported from
the rule on `X` prescribed by the generators `t_i` has
`Stacks.Chow.firstChernComponentCycleAt_pullbackComponentRule` — an *equality*, not merely a
rational equivalence — for its compatibility with `i_*`, and it computes the same cap product as
the rule of `N|_D` because the two agree in the Chow group of every component
(`Stacks.Chow.rationallyEquivalent_firstChernComponentCycleRule_pullbackComponentRule` and
`Stacks.Chow.rationallyEquivalent_restrictedChernRule`).

## Main results

* `Stacks.Chow.gysinHomomorphismOfInvertible_eq_firstChernClassCapOfInvertible` — the identity
  for the zero scheme of a nonzero section of an invertible module.
* `Stacks.Chow.gysin_divisorOfMeromorphicSection_eq_firstChernClassCap` — **Stacks 02TM**.

## References

* [Stacks Project, Tag 02TM](https://stacks.math.columbia.edu/tag/02TM)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02SK](https://stacks.math.columbia.edu/tag/02SK)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 02SU](https://stacks.math.columbia.edu/tag/02SU)
* [Stacks Project, Tag 0AYB](https://stacks.math.columbia.edu/tag/0AYB)
* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

attribute [local instance] isIntegral_integralComponentAt

/-! ### Two helpers -/

/-- The component cycle of a rule only depends on the ideal sheaf: the two proof arguments are
transported by proof irrelevance. -/
private theorem firstChernComponentCycle_congr (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) (chern : FirstChernComponentCycleRule C p k)
    {W W' : X.IdealSheafData} (h : W = W') (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (hW' : IsIntegral W'.subscheme)
    (hDim' : schemeDeltaDimension C (W'.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) :
    firstChernComponentCycle C p k chern W hW hDim =
      firstChernComponentCycle C p k chern W' hW' hDim' := by
  subst h
  rfl

/-- A locally finite family of subsets pulls back to a locally finite family along a continuous
map. -/
private theorem locallyFinite_preimage {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {J : Type*} {E : J → Set B} (hE : LocallyFinite E) {f : A → B} (hf : Continuous f) :
    LocallyFinite fun j ↦ f ⁻¹' E j := by
  intro a
  obtain ⟨U, hU, hfin⟩ := hE (f a)
  refine ⟨f ⁻¹' U, hf.continuousAt.preimage_mem_nhds hU, hfin.subset ?_⟩
  rintro j ⟨b, hb, hbU⟩
  exact ⟨f b, hb, hbU⟩

/-! ### Stacks 02TM -/

section Main

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  (C : ChowSituation.{u}) (p : X ⟶ C.S) [LocallyOfFiniteType p] {k : ℤ}

/-- **Stacks 02TM for the zero scheme of a section.** Let `X` be integral, locally Noetherian and
locally of finite type over the base, of delta-dimension `k + 2`. Let `L` be an invertible
`𝒪_X`-module with a nonzero global section `s`, let `i : D = Z(s) ⟶ X` be its zero scheme, and
let `N` be an invertible `𝒪_X`-module with a nonzero meromorphic section `t`. Then

`i^* div_N(t) = c₁(N|_D) ∩ [D]_{k+1}`  in  `A_k(D)`.

The two cycles the source's proof names are the two explicit arguments, each pinned down rather
than assumed: `divN` is the divisor cycle `div_N(t)` of Stacks 02SJ, pinned by `hdivN`, and
`fund` is the fundamental cycle `[D]_{k+1}` read as a cycle on `D`, pinned by `hfund` through its
pushforward to `X`, which determines it because a closed immersion transports coefficients.

The key formula of Stacks 0AYC enters through
`Stacks.Chow.isRationallyEquivalentToZeroWithin_properPushforward_gysinCycle_sub`; see the module
documentation. For an effective Cartier divisor, with the canonical cycles and the grading of the
source, this is `Stacks.Chow.gysin_divisorOfMeromorphicSection_eq_firstChernClassCap`. -/
theorem gysinHomomorphismOfInvertible_eq_firstChernClassCapOfInvertible
    (hn : schemeDeltaDimension C p = ((k + 2 : ℤ) : EInt)) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (hs : s ≠ 0) (N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (hNtriv : ∀ x : X, Stacks.Divisors.IsTrivializedNear N x)
    (t : N.presheaf.stalk (genericPoint X)) (ht : t ≠ 0) (divN : CycleGroup C p (k + 1))
    (hdivN : divN.1 =
      Stacks.Chow.weilDivisorAlgebraicCycle
        (Stacks.Divisors.weilDivisorOfMeromorphicSection hNtriv t))
    (fund : CycleGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) (k + 1))
    (hfund : properPushforward C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
        (Stacks.Divisors.zeroScheme X L s).subschemeι rfl (k + 1) fund =
      cycleAssociatedToClosedSubscheme C p
        (Stacks.Divisors.zeroScheme X L s).subschemeι (k + 1)) :
    gysinHomomorphismOfInvertible C p k L s divN =
      firstChernClassCapOfInvertible C
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
        ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme X L s).subschemeι).obj N) fund := by
  classical
  have _ := Stacks.Divisors.isInvertible_presheaf L
  have _ := Stacks.Divisors.isInvertible_presheaf N
  have hsne : L.presheaf.germ ⊤ (genericPoint X) trivial s ≠ 0 :=
    germ_genericPoint_ne_zero_of_ne_zero L s hs
  -- the situation of Stacks 0AYB with the generator of `L` adapted to `s`
  set ℱ : KeyFormulaSituation L N :=
    (keyFormulaSituationOf L N (L.presheaf.germ ⊤ (genericPoint X) trivial s) t hsne
      ht).withSectionGeneratorsL s with hℱ
  have hratio : ∀ i, ¬ Stacks.Divisors.zeroScheme X L s ≤
      integralComponentAt (ℱ.componentPoint i) → ℱ.ratioL i = 1 := fun i hi ↦
    KeyFormulaSituation.withSectionGeneratorsL_ratioL_eq_one
      (keyFormulaSituationOf L N (L.presheaf.germ ⊤ (genericPoint X) trivial s) t hsne ht) s hs
      i rfl hi
  have hgenL : ∀ i, ¬ Stacks.Divisors.zeroScheme X L s ≤
      integralComponentAt (ℱ.componentPoint i) →
      ℱ.localGeneratorL i = L.presheaf.germ ⊤ (ℱ.componentPoint i) trivial s := fun i hi ↦
    gysinGenerator_eq_germ L s hs hi
  have horderL : ∀ i, ¬ Stacks.Divisors.zeroScheme X L s ≤
      integralComponentAt (ℱ.componentPoint i) → ℱ.orderL i = 0 := fun i hi ↦
    ℱ.orderL_eq_zero_of_ratioL_eq_one (hratio i hi)
  have hsubtype : ∀ g : ℱ.Index → ℤ, ∑ᶠ i, ℱ.orderL i * g i =
      ∑ᶠ i : {i : ℱ.Index // Stacks.Divisors.zeroScheme X L s ≤
        integralComponentAt (ℱ.componentPoint i)}, ℱ.orderL i.1 * g i.1 := fun g ↦
    finsum_eq_finsum_subtype (fun i ↦ ℱ.orderL i * g i)
      (fun i hi ↦ by rw [horderL i hi, zero_mul])
  have hdimX : ∀ i : ℱ.Index,
      schemeDeltaDimension C ((integralComponentAt (ℱ.componentPoint i)).subschemeι ≫ p) =
        ((k + 1 : ℤ) : EInt) :=
    ℱ.schemeDeltaDimension_integralComponentAt_componentPoint C p k hn
  have hrelX : ∀ i : ℱ.Index,
      relativeDimension C.dimensionFunction p (ℱ.componentPoint i) = k + 1 := fun i ↦ by
    have h := relativeDimension_genericPointOf C p (integralComponentAt (ℱ.componentPoint i))
      (isIntegral_integralComponentAt _) (hdimX i)
    rwa [genericPointOf_integralComponentAt] at h
  -- the divisor cycle of `t`, presented by the family
  have hdivNpres : ∀ x : X, divN.1 x = ∑ᶠ i, ℱ.orderN i *
      (cycleAssociatedToClosedSubscheme C p
        (integralComponentAt (ℱ.componentPoint i)).subschemeι (k + 1)).1 x := fun x ↦ by
    rw [hdivN]
    exact ℱ.weilDivisorAlgebraicCycle_weilDivisorN_apply C p k hn x
  obtain ⟨β, hβcls, hβ⟩ := gysinHomomorphismOfInvertible_finsum C p k L s
    (fun i ↦ integralComponentAt (ℱ.componentPoint i))
    (fun i ↦ isIntegral_integralComponentAt _) hdimX
    ℱ.locallyFinite_support_integralComponentAt ℱ.orderN divN hdivNpres
  -- the component rule on `X` prescribed by the chosen generators of `N`
  set chernX : FirstChernComponentCycleRule C p k :=
    restrictedChernRule C p k N ℱ.componentPoint ℱ.localGeneratorN ℱ.componentPoint_injective
      ℱ.isStalkBasis_localGeneratorN with hchernX
  set chernD : FirstChernComponentCycleRule C
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k :=
    pullbackComponentRule C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
      (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k chernX with hchernD
  -- the members of the family contained in the divisor, and the points of `D` under them
  have hmem : ∀ i : {i : ℱ.Index // Stacks.Divisors.zeroScheme X L s ≤
      integralComponentAt (ℱ.componentPoint i)},
      ℱ.componentPoint i.1 ∈ Set.range (Stacks.Divisors.zeroScheme X L s).subschemeι.base :=
    fun i ↦ by
      rw [Scheme.IdealSheafData.range_subschemeι]
      exact (le_integralComponentAt_iff_mem_support _ _).1 i.2
  obtain ⟨zPt, hzPtEq⟩ : ∃ z : {i : ℱ.Index // Stacks.Divisors.zeroScheme X L s ≤
        integralComponentAt (ℱ.componentPoint i)} →
        (Stacks.Divisors.zeroScheme X L s).subscheme,
      ∀ i, (Stacks.Divisors.zeroScheme X L s).subschemeι.base (z i) = ℱ.componentPoint i.1 :=
    ⟨fun i ↦ (hmem i).choose, fun i ↦ (hmem i).choose_spec⟩
  have hrelp : ∀ i, relativeDimension C.dimensionFunction p
      ((Stacks.Divisors.zeroScheme X L s).subschemeι.base (zPt i)) = k + 1 := fun i ↦ by
    rw [hzPtEq i]
    exact hrelX i.1
  have hrelD : ∀ i, relativeDimension C.dimensionFunction
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) (zPt i) = k + 1 := fun i ↦ by
    rw [relativeDimension_comp_closedImmersion]
    exact hrelp i
  have hVdim : ∀ i, schemeDeltaDimension C ((integralComponentAt (zPt i)).subschemeι ≫
      (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt) := fun i ↦
    schemeDeltaDimension_integralComponentAt_of_eq C
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) (hrelD i)
  have hVlocal : LocallyFinite fun i ↦ (((integralComponentAt (zPt i)).support) :
      Set (Stacks.Divisors.zeroScheme X L s).subscheme) := by
    have h0 : LocallyFinite fun i : ℱ.Index ↦
        (Stacks.Divisors.zeroScheme X L s).subschemeι.base ⁻¹'
          (((integralComponentAt (ℱ.componentPoint i)).support) : Set X) :=
      locallyFinite_preimage ℱ.locallyFinite_support_integralComponentAt
        (Stacks.Divisors.zeroScheme X L s).subschemeι.continuous
    refine (h0.comp_injective Subtype.val_injective).subset fun i z hz ↦ ?_
    rw [coe_support_integralComponentAt] at hz
    show (Stacks.Divisors.zeroScheme X L s).subschemeι.base z ∈
      (((integralComponentAt (ℱ.componentPoint i.1)).support) : Set X)
    rw [coe_support_integralComponentAt, ← hzPtEq i]
    exact specializes_iff_mem_closure.mp ((specializes_iff_mem_closure.mpr hz).map
      (Stacks.Divisors.zeroScheme X L s).subschemeι.continuous)
  -- the fundamental cycle of `D`, presented by those members
  have hVpush : ∀ i, properPushforward C
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
        (Stacks.Divisors.zeroScheme X L s).subschemeι rfl (k + 1)
        (cycleAssociatedToClosedSubscheme C
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
          (integralComponentAt (zPt i)).subschemeι (k + 1)) =
      cycleAssociatedToClosedSubscheme C p
        (integralComponentAt (ℱ.componentPoint i.1)).subschemeι (k + 1) := by
    intro i
    have key : properPushforward C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
          (Stacks.Divisors.zeroScheme X L s).subschemeι rfl (k + 1)
          (cycleAssociatedToClosedSubscheme C
            ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
            (integralComponentAt (zPt i)).subschemeι (k + 1)) =
        cycleAssociatedToClosedSubscheme C p
          (integralComponentAt ((Stacks.Divisors.zeroScheme X L s).subschemeι.base
            (zPt i))).subschemeι (k + 1) := by
      rw [properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
        (Stacks.Divisors.zeroScheme X L s).subschemeι rfl
        (integralComponentAt (zPt i)).subschemeι (k + 1)]
      exact cycleAssociatedToClosedSubscheme_eq_of_iso C p _ _
        (integralComponentIso (Stacks.Divisors.zeroScheme X L s).subschemeι (zPt i))
        (integralComponentMap_subschemeι (Stacks.Divisors.zeroScheme X L s).subschemeι (zPt i))
        (k + 1)
    rw [hzPtEq i] at key
    exact key
  have hzeroCycle : ∀ x : X, (cycleAssociatedToClosedSubscheme C p
      (Stacks.Divisors.zeroScheme X L s).subschemeι (k + 1)).1 x =
      weilDivisorAlgebraicCycle ℱ.weilDivisorL x := by
    have hq1 : schemeDeltaDimension C p = (((k + 1) + 1 : ℤ) : EInt) := by
      rw [hn, show (k + 1 + 1 : ℤ) = k + 2 from by ring]
    have h := Stacks.ChernCap42.chernComponentCycle_coe_eq_cycleAssociatedToZeroScheme C
      (k := k + 1) p L hq1 s hs (Stacks.Divisors.isTrivializedNear_of_isInvertible L)
    rw [Stacks.Divisors.genericValue_meromorphicSectionOfSection] at h
    have hwL : ℱ.weilDivisorL = Stacks.Divisors.weilDivisorOfMeromorphicSection
        (Stacks.Divisors.isTrivializedNear_of_isInvertible L)
        (L.presheaf.germ ⊤ (genericPoint X) trivial s) := by rw [hℱ]; rfl
    intro x
    rw [← h, hwL]
    rfl
  have hfundpres : ∀ z : (Stacks.Divisors.zeroScheme X L s).subscheme, fund.1 z =
      ∑ᶠ i : {i : ℱ.Index // Stacks.Divisors.zeroScheme X L s ≤
        integralComponentAt (ℱ.componentPoint i)}, ℱ.orderL i.1 *
        (cycleAssociatedToClosedSubscheme C
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
          (integralComponentAt (zPt i)).subschemeι (k + 1)).1 z := by
    intro z
    have h1 : fund.1 z = (cycleAssociatedToClosedSubscheme C p
        (Stacks.Divisors.zeroScheme X L s).subschemeι (k + 1)).1
          ((Stacks.Divisors.zeroScheme X L s).subschemeι.base z) := by
      rw [← hfund, properPushforward_apply_image_of_isClosedImmersion]
    rw [h1, hzeroCycle, ℱ.weilDivisorAlgebraicCycle_weilDivisorL_apply C p k hn,
      hsubtype fun i ↦ (cycleAssociatedToClosedSubscheme C p
          (integralComponentAt (ℱ.componentPoint i)).subschemeι (k + 1)).1
            ((Stacks.Divisors.zeroScheme X L s).subschemeι.base z)]
    refine finsum_congr fun i ↦ ?_
    rw [← hVpush i, properPushforward_apply_image_of_isClosedImmersion]
  obtain ⟨γ, hγcls, hγ⟩ := firstChernClassCap_finsum C
    ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k chernD
    (fun i ↦ integralComponentAt (zPt i)) (fun i ↦ isIntegral_integralComponentAt _) hVdim
    hVlocal (fun i ↦ ℱ.orderL i.1) fund hfundpres
  -- the pushforward of the component cycles of the transported rule
  set cycN : ℱ.Index → CycleGroup C p k := fun i ↦
    properPushforward C ((integralComponentAt (ℱ.componentPoint i)).subschemeι ≫ p) p
      (integralComponentAt (ℱ.componentPoint i)).subschemeι rfl k
      (chernCycleOfRestrictedStalk C p k N (integralComponentAt (ℱ.componentPoint i))
        (isIntegral_integralComponentAt _) (hdimX i)
        (genericPointOf_integralComponentAt _) (ℱ.localGeneratorN i))
  have hfccX : ∀ i : ℱ.Index,
      firstChernComponentCycle C p k chernX (integralComponentAt (ℱ.componentPoint i))
          (isIntegral_integralComponentAt _) (hdimX i) = cycN i := fun i ↦ by
    rw [hchernX]
    exact congrArg _ (restrictedChernRule_of_genericPointOf C p k N ℱ.componentPoint
      ℱ.localGeneratorN ℱ.componentPoint_injective ℱ.isStalkBasis_localGeneratorN _
      (isIntegral_integralComponentAt _) (hdimX i) i (genericPointOf_integralComponentAt _))
  have hpushfcc : ∀ i, properPushforward C
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
        (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k
        (firstChernComponentCycle C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k chernD
          (integralComponentAt (zPt i)) (isIntegral_integralComponentAt _) (hVdim i)) =
      firstChernComponentCycle C p k chernX (integralComponentAt (ℱ.componentPoint i.1))
        (isIntegral_integralComponentAt _) (hdimX i.1) := by
    intro i
    rw [← firstChernComponentCycleAt_eq C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
      chernD (hrelD i), hchernD,
      firstChernComponentCycleAt_pullbackComponentRule C
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
        (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k chernX (zPt i) (hrelD i),
      firstChernComponentCycleAt_eq C p k chernX (hrelp i)]
    exact firstChernComponentCycle_congr C p k chernX
      (congrArg integralComponentAt (hzPtEq i)) _ _ _ _
  -- the pushforward of `γ` is the cycle the Gysin comparison asks for
  have hδ : ∀ x : X, (properPushforward C
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
        (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k γ).1 x =
      ∑ᶠ i : ℱ.Index, ℱ.orderL i * (cycN i).1 x := by
    intro x
    rw [hsubtype fun i ↦ (cycN i).1 x]
    by_cases hr : x ∈ Set.range (Stacks.Divisors.zeroScheme X L s).subschemeι.base
    · obtain ⟨z, rfl⟩ := hr
      rw [properPushforward_apply_image_of_isClosedImmersion, hγ z]
      refine finsum_congr fun i ↦ ?_
      rw [← hfccX i.1, ← hpushfcc i, properPushforward_apply_image_of_isClosedImmersion]
    · rw [properPushforward_apply_of_notMem_range C
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
        (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k _ hr]
      refine ((finsum_congr fun i ↦ ?_).trans finsum_zero).symm
      have hx : x ∉ (((integralComponentAt (ℱ.componentPoint i.1)).support) : Set X) := by
        intro hmemx
        refine hr ?_
        rw [Scheme.IdealSheafData.range_subschemeι]
        exact ((Stacks.Divisors.zeroScheme X L s).support.isClosed.closure_subset_iff).mpr
          (Set.singleton_subset_iff.mpr
            ((le_integralComponentAt_iff_mem_support _ _).1 i.2))
          (by rwa [coe_support_integralComponentAt] at hmemx)
      have hsupp : x ∉ Function.support fun y ↦ (cycN i.1).1 y := fun hy ↦ hx (by
        rw [← Scheme.IdealSheafData.range_subschemeι]
        exact support_properPushforward_subset C
          ((integralComponentAt (ℱ.componentPoint i.1)).subschemeι ≫ p) p
          (integralComponentAt (ℱ.componentPoint i.1)).subschemeι rfl k _ hy)
      rw [Function.notMem_support.1 hsupp, mul_zero]
  -- the Gysin comparison, descended into the divisor
  have hwithin := isRationallyEquivalentToZeroWithin_properPushforward_gysinCycle_sub C p hn s hs
    ℱ hratio hgenL β hβ (properPushforward C
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
      (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k γ) hδ
  have hsub : IsRationallyEquivalentToZero C
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k (β - γ) := by
    refine isRationallyEquivalentToZero_of_properPushforward_isRationallyEquivalentToZeroWithin C
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
      (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k (β - γ) ?_
    rw [properPushforward_sub, Scheme.IdealSheafData.range_subschemeι]
    exact hwithin
  -- the two component rules on `D` compute the same cap product
  have hcap : firstChernClassCapOfInvertible C
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme X L s).subschemeι).obj N) fund =
      firstChernClassCap C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k chernD fund := by
    refine firstChernClassCap_congr C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
      (firstChernComponentCycleRule C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
        ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme X L s).subschemeι).obj N))
      chernD (fun W hW hDim ↦ ?_) fund
    have e1 := rationallyEquivalent_firstChernComponentCycleRule_pullbackComponentRule C
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
      (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k N W hW hDim
    have e2 := properPushforward_rationallyEquivalent C
      (((W.map (Stacks.Divisors.zeroScheme X L s).subschemeι).subschemeι) ≫ p)
      (W.subschemeι ≫ (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
      (imageIsoOfIsClosedImmersion (Stacks.Divisors.zeroScheme X L s).subschemeι W).inv
      (imageIsoOfIsClosedImmersion_inv_comp_base C
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
        (Stacks.Divisors.zeroScheme X L s).subschemeι rfl W) k
      (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
        (imageIsoOfIsClosedImmersion (Stacks.Divisors.zeroScheme X L s).subschemeι W).inv C _ _
        (imageIsoOfIsClosedImmersion_inv_comp_base C
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
          (Stacks.Divisors.zeroScheme X L s).subschemeι rfl W) k)
      (rationallyEquivalent_restrictedChernRule C p k N ℱ.componentPoint ℱ.localGeneratorN
        ℱ.componentPoint_injective ℱ.isStalkBasis_localGeneratorN
        (W.map (Stacks.Divisors.zeroScheme X L s).subschemeι)
        (isIntegral_subscheme_map (Stacks.Divisors.zeroScheme X L s).subschemeι W hW)
        (schemeDeltaDimension_subscheme_map C
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
          (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k W hW hDim))
    exact QuotientAddGroup.eq_iff_sub_mem.1
      ((QuotientAddGroup.eq_iff_sub_mem.2 e1).trans
        (QuotientAddGroup.eq_iff_sub_mem.2 e2).symm)
  rw [hβcls, hcap, hγcls]
  exact (QuotientAddGroup.eq_iff_sub_mem.2 hsub)

end Main

/-! ### Stacks 02TM for an effective Cartier divisor -/

section EffectiveCartier

open Stacks.Divisors

/-- On a nonempty scheme the zero ideal sheaf is not an effective Cartier divisor: near a point
its ideal would be generated by a regular element, which is `0`. -/
theorem not_isEffectiveCartierDivisor_bot {X : Scheme.{u}} [IsIntegral X] :
    ¬ IsEffectiveCartierDivisor (⊥ : X.IdealSheafData) := by
  intro h
  obtain ⟨U, hU, hxU, f, hf, hgen⟩ :=
    exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor (⊥ : X.IdealSheafData) h
      (genericPoint X)
  have : Nonempty U := ⟨⟨genericPoint X, hxU⟩⟩
  have hf0 : f = 0 := by
    have hmem : f ∈ (⊥ : X.IdealSheafData).ideal ⟨U, hU⟩ := by
      rw [hgen]
      exact Ideal.mem_span_singleton_self f
    simpa using hmem
  rw [hf0] at hf
  exact zero_ne_one (hf.left (show (0 : Γ(X, U)) * 0 = 0 * 1 by simp))

/-- **The canonical section `1_E` of `𝒪_X(E)` is nonzero** for an effective Cartier divisor `E`
on an integral scheme: its zero scheme is `E` (Stacks 02OR), while the zero scheme of the zero
section is the whole scheme, which is not an effective Cartier divisor. -/
theorem divisorSheafGlobalSection_ne_zero {X : Scheme.{u}} [IsIntegral X] (E : X.IdealSheafData)
    [IsEffectiveCartierDivisor E] : divisorSheafGlobalSection E ≠ 0 := by
  intro h0
  have hbot : Stacks.Divisors.zeroScheme X (divisorSheaf E) 0 = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro U
    refine (Scheme.IdealSheafData.ideal_ofIdeals_le _ U).trans ?_
    rw [Ideal.span_le]
    rintro a ⟨φ, rfl⟩
    simp
  have hE : E = ⊥ := by
    rw [← zeroScheme_canonicalSection E, h0]
    exact hbot
  exact not_isEffectiveCartierDivisor_bot (hE ▸ ‹IsEffectiveCartierDivisor E›)

/-- Reading a fundamental cycle in an equal degree gives the fundamental cycle of that degree. -/
theorem cycleGroupOfEq_fundamentalCycle {C : ChowSituation.{u}} {T : Scheme.{u}} (q : T ⟶ C.S)
    [LocallyOfFiniteType q] {d e : ℤ} (h : d = e) :
    cycleGroupOfEq h (fundamentalCycle C q d) = fundamentalCycle C q e := by
  subst h
  rfl

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  [IsIntegral X]

/-- **Stacks 02TM.** Let `X` be integral and locally of finite type over the base scheme `S` of
chapter 42, with `n = dim_δ(X)`, let `i : D ⟶ X` be an effective Cartier divisor, and let `N` be
an invertible `𝒪_X`-module with a nonzero (that is, regular) meromorphic section `t`. Then

  `i^* div_N(t) = c₁(N|_D) ∩ [D]_{n-1}`  in  `CH_{n-2}(D)`.

Here `i^*` is the Gysin homomorphism of Stacks 02T8 for the pair `(𝒪_X(D), 1_D)`, whose zero
scheme is `D` (`Stacks.Divisors.zeroScheme_canonicalSection`), so it takes values in the Chow
group of `D`; `div_N(t)` is the divisor cycle of Stacks 02SJ (1); `N|_D` is the pullback of `N`
along `i`; and `[D]_{n-1}` is the fundamental cycle of `D`, the cycle of `D` as a closed
subscheme of itself. Cycles of degree `n - 1` are read in degree `(n - 2) + 1`, the source of
`i^*` and of the cap product into degree `n - 2`, by `Stacks.Chow.cycleGroupOfEq`. -/
@[stacks 02TM]
theorem gysin_divisorOfMeromorphicSection_eq_firstChernClassCap (n : ℤ)
    (hn : schemeDeltaDimension C p = (n : EInt)) (E : X.IdealSheafData)
    [IsEffectiveCartierDivisor E] (N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (t : AlgebraicGeometry.MeromorphicSection X.sheaf N)
    (ht : AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf N t) :
    gysinHomomorphismOfInvertible C p (n - 2) (divisorSheaf E) (divisorSheafGlobalSection E)
        (cycleGroupOfEq (by ring) (divisorOfMeromorphicSectionCycle C p n hn N t ht)) =
      firstChernClassCapOfInvertible C
        ((Stacks.Divisors.zeroScheme X (divisorSheaf E)
          (divisorSheafGlobalSection E)).subschemeι ≫ p) (n - 2)
        ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme X (divisorSheaf E)
          (divisorSheafGlobalSection E)).subschemeι).obj N)
        (cycleGroupOfEq (by ring) (fundamentalCycle C
          ((Stacks.Divisors.zeroScheme X (divisorSheaf E)
            (divisorSheafGlobalSection E)).subschemeι ≫ p) (n - 1))) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have _ := isInvertible_presheaf N
  have hn' : schemeDeltaDimension C p = ((n - 2 + 2 : ℤ) : EInt) := by
    rw [sub_add_cancel]
    exact hn
  rw [cycleGroupOfEq_fundamentalCycle]
  exact gysinHomomorphismOfInvertible_eq_firstChernClassCapOfInvertible C p hn' (divisorSheaf E)
    (divisorSheafGlobalSection E) (divisorSheafGlobalSection_ne_zero E) N
    (isTrivializedNear_of_isInvertible N) (genericValue N t)
    (genericValue_ne_zero_of_isRegularMeromorphicSection N t ht) _ rfl _
    (properPushforward_fundamentalCycle_of_isClosedImmersion C _ p _ rfl _)

end EffectiveCartier

end Stacks.Chow

end
