module

public import StacksFrontier.AlgebraicGeometry.Chow.AdamsOperator.CoherentToSupportedPerfectGeneral
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CapFundamentalClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChowHomologyCoherentKZeroBijective
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.MaximalDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedChernCharacterKMap
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardCoherent.StalkProduct

/-!
# The coherent Chow character of a closed subscheme of a regular scheme

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `i : X ⟶ Y` be a
closed immersion of schemes locally of finite type over `S`, with `Y` regular and quasi-compact.
Proposition 42.57.1 (Stacks 0FEW) considers the composition

  `K'₀(X) ⟶ K₀(D_{X,perf}(𝒪_Y)) ⟶ A^*(X ⟶ Y) ⊗ 𝐐 ⟶ CH_*(X) ⊗ 𝐐`

of the map `ℱ ↦ ℱ[0]` of Remark 0FEQ, the localized Chern character `ch(X ⟶ Y, -)` of Remark 0FET
and the cap product `c ↦ c ∩ [Y]` with the fundamental class of `Y`. It sends the class of a
coherent `𝒪_X`-module `ℱ` to `ch(X ⟶ Y, ℱ[0]) ∩ [Y]`.

The first step of the proof of the proposition is condition (1): if the support of `ℱ` has
delta-dimension at most `k`, the image of `[ℱ]` lies in `⨁_{k' ≤ k} CH_{k'}(X) ⊗ 𝐐`. Indeed `ℱ[0]`
is supported on the reduced closed subscheme `Z ⊆ X` carried by the support of `ℱ`, so by
Stacks 0FB7 `ch(X ⟶ Y, ℱ[0]) = (Z ⟶ X)_* ∘ ch(Z ⟶ Y, ℱ[0])`; capping with `[Y]` therefore factors
through the Chow groups of `Z`, which vanish above the delta-dimension of `Z`.

## Main definitions

* `Stacks.Chow.rationalCapFundamentalClassSum` — `c ↦ c ∩ [Y]` on `A^*(X ⟶ Y) ⊗ 𝐐`.
* `Stacks.Chow.coherentChowCharacter` — the composition of Stacks 0FEW.

## Main results

* `Stacks.Chow.coherentChowCharacter_mk` — the value `ch(X ⟶ Y, ℱ[0]) ∩ [Y]` on `[ℱ]`.
* `Stacks.Chow.capFundamentalClassAt_bivariantProperPushforward_eq_zero` — `(f_* ∘ c) ∩ [Y]_n`
  vanishes in degrees above the delta-dimension of the source of `f`.
* `Stacks.Chow.isDimensionTriangular_coherentChowCharacter` — condition (1) of the proof of
  Stacks 0FEW.

## Implementation notes

The localized Chern character map is `Stacks.Chow.localizedChernCharKMapDirectSum`, well defined
by Lemma 0FBE (`Stacks.Chow.supportedLocalizedChernChar_triangle`). The fundamental class `[Y]` is
the cycle associated to `Y` (`Stacks.Chow.totalFundamentalClass`), which for the locally
equidimensional scheme `Y` (Lemma 0FE3) is the class of Remark 0FE4.

## References

* [Stacks Project, Tag 0FEW](https://stacks.math.columbia.edu/tag/0FEW)
* [Stacks Project, Tag 0FEQ](https://stacks.math.columbia.edu/tag/0FEQ)
* [Stacks Project, Tag 0FET](https://stacks.math.columbia.edu/tag/0FET)
* [Stacks Project, Tag 0FB7](https://stacks.math.columbia.edu/tag/0FB7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  StrictlyPerfect

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Capping a pushed-forward class with the fundamental class -/

section Vanishing

variable (C : ChowSituation.{u}) {W X Y : Scheme.{u}} (sW : W ⟶ C.S) [LocallyOfFiniteType sW]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : W ⟶ X)
  [IsProper f] (g : X ⟶ Y) [LocallyOfFiniteType g] (hf : f ≫ sX = sW) (hg : g ≫ sY = sX) (p : ℤ)

/-- **`(f_* ∘ c) ∩ [Y]_n` vanishes above the delta-dimension of `W`.** For `f : W ⟶ X` proper,
`g : X ⟶ Y` and `c ∈ A^p(W ⟶ Y)`, the class `(f_* ∘ c) ∩ [Y]_n ∈ CH_{n-p}(X)` is zero when every
point of `W` has relative dimension at most `k < n - p`. -/
theorem capFundamentalClassAt_bivariantProperPushforward_eq_zero {k : ℤ}
    (hW : ∀ w : W, relativeDimension C.dimensionFunction sW w ≤ k) (n : ℤ) (hn : k < n - p)
    (c : BivariantClass C (gysinSystemOfInvertible C) sW sY (f ≫ g)
      (comp_comp_structureMorphism_eq hf hg) p) :
    capFundamentalClassAt C (gysinSystemOfInvertible C) sX sY g hg p n
      (bivariantProperPushforwardOfInvertible C sW sX sY f g hf hg p c) = 0 := by
  have h0 : c.cap (𝟙 Y) n (fundamentalChowClass C (𝟙 Y ≫ sY) n) = 0 := by
    refine chowGroup_eq_zero C (pullback.fst (f ≫ g) (𝟙 Y) ≫ sW) (fun w hw ↦ ?_) _
    have hle := hW (pullback.fst (f ≫ g) (𝟙 Y) w)
    rw [relativeDimension_comp_closedImmersion] at hw
    omega
  rw [capFundamentalClassAt_apply, bivariantProperPushforwardOfInvertible_cap,
    bivariantProperPushforwardCap_apply, h0, map_zero, map_zero]

end Vanishing

/-! ### The cap product on `A^*(X ⟶ Y) ⊗ 𝐐` -/

section Sum

/-- A homomorphism out of a direct sum over `ℕ`, on an element vanishing from `N` on. -/
theorem toAddMonoid_eq_sum_range {M : ℕ → Type*} [∀ p, AddCommMonoid (M p)] {B : Type*}
    [AddCommMonoid B] (φ : ∀ p, M p →+ B) (x : DirectSum ℕ M) (N : ℕ)
    (hx : ∀ p ≥ N, x p = 0) :
    DirectSum.toAddMonoid φ x = ∑ p ∈ Finset.range N, φ p (x p) := by
  classical
  rw [DirectSum.toAddMonoid, DFinsupp.liftAddHom_apply, DFinsupp.sumAddHom_apply]
  refine DFinsupp.sum_of_support_subset (fun p hp ↦ ?_) fun p _ ↦ map_zero _
  exact Finset.mem_range.2 (not_le.1 fun h ↦ DFinsupp.mem_support_iff.1 hp (hx p h))

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
  [LocallyOfFiniteType f] (hf : f ≫ sY = sX) [IsNoetherian Y]

/-- **The cap product `A^*(X ⟶ Y) ⊗ 𝐐 ⟶ CH_*(X) ⊗ 𝐐`, `c ↦ c ∩ [Y]`**, on
`A^*(X ⟶ Y) ⊗ 𝐐 = ⨁_{p ≥ 0} A^p(X ⟶ Y) ⊗ 𝐐`: the sum of the maps
`Stacks.Chow.rationalCapFundamentalClass` of the degrees `p`. -/
def rationalCapFundamentalClassSum :
    (DirectSum ℕ fun p : ℕ ↦ TensorProduct ℤ ℚ (BivariantClass C G sX sY f hf (p : ℤ))) →+
      DirectSum ℤ fun k ↦ TensorProduct ℤ ℚ (chowGroup C sX k) :=
  DirectSum.toAddMonoid fun p : ℕ ↦
    (rationalCapFundamentalClass C G sX sY f hf (p : ℤ)).toAddMonoidHom

/-- The cap product on an element of `A^*(X ⟶ Y) ⊗ 𝐐` with components vanishing from `N` on. -/
theorem rationalCapFundamentalClassSum_apply
    (x : DirectSum ℕ fun p : ℕ ↦ TensorProduct ℤ ℚ (BivariantClass C G sX sY f hf (p : ℤ)))
    (N : ℕ) (hx : ∀ p ≥ N, x p = 0) :
    rationalCapFundamentalClassSum C G sX sY f hf x =
      ∑ p ∈ Finset.range N, rationalCapFundamentalClass C G sX sY f hf (p : ℤ) (x p) :=
  toAddMonoid_eq_sum_range _ x N hx

end Sum

/-! ### The composition of Stacks 0FEW -/

section Composite

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (a : Y ⟶ C.S) [LocallyOfFiniteType a]
  (i : X ⟶ Y) [IsClosedImmersion i]

include a in
/-- A scheme locally of finite type over the base which is quasi-compact is Noetherian. -/
theorem isNoetherian_of_compactSpace [CompactSpace Y] : IsNoetherian Y :=
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian a
  ⟨⟩

include a i in
/-- A closed subscheme of a quasi-compact scheme locally of finite type over the base is
Noetherian. -/
theorem isNoetherian_of_isClosedImmersion_of_compactSpace [CompactSpace Y] : IsNoetherian X :=
  have : CompactSpace X := (IsClosedImmersion.isClosedEmbedding i).compactSpace
  isNoetherian_of_compactSpace C (i ≫ a)

/-- In a quasi-compact space the irreducible components are quasi-compact, being closed. -/
theorem isCompact_of_mem_irreducibleComponents {α : Type*} [TopologicalSpace α] [CompactSpace α] :
    ∀ T ∈ irreducibleComponents α, IsCompact T :=
  fun T hT ↦ (isClosed_of_mem_irreducibleComponents T hT).isCompact

variable (hY : IsRegular Y)

/-- The cohomology sheaves of `ℱ[0]`, for a coherent `𝒪_X`-module `ℱ` pushed forward to `Y`, are
supported on the closed subscheme of `X` carried by the support of `ℱ`. -/
theorem supp_homology_singlePushforwardSupportedPerfect_subset
    (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℤ) :
    haveI : _root_.SheafOfModules.IsCoherent (F.obj : X.Modules) :=
      CoherentAbelian.isCoherent_of_stacksIsCoherent F.property
    _root_.SheafOfModules.supp
        ((DerivedCategory.homologyFunctor (OXMod.{u, u} Y.toRingedSpace) n).obj
          (singlePushforwardSupportedPerfectGeneral i hY F).obj) ⊆
      Set.range ((reducedSupport (F.obj : X.Modules)).subschemeι ≫ i).base := by
  have : _root_.SheafOfModules.IsCoherent (F.obj : X.Modules) :=
    CoherentAbelian.isCoherent_of_stacksIsCoherent F.property
  by_cases hn : n = 0
  · subst hn
    refine (_root_.SheafOfModules.supp_eq_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (OXMod.{u, u} Y.toRingedSpace) 0).app
        ((Scheme.Modules.pushforward i).obj F.obj))).subset.trans ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := supp_pushforward_subset_image i (F.obj : X.Modules)
      (_root_.SheafOfModules.isClosed_supp _) hy
    have hx' : x ∈ Set.range (reducedSupport (F.obj : X.Modules)).subschemeι.base := by
      rw [Scheme.IdealSheafData.range_subschemeι]
      exact (Set.ext_iff.1 (coe_support_reducedSupport (F.obj : X.Modules)) x).2 hx
    obtain ⟨z, rfl⟩ := hx'
    exact ⟨z, by rw [Scheme.Hom.comp_apply]⟩
  · have hz := DerivedCategory.isZero_homology_singleFunctor_obj
      (C := OXMod.{u, u} Y.toRingedSpace) ((Scheme.Modules.pushforward i).obj F.obj) hn
    exact (_root_.SheafOfModules.supp_eq_empty_of_isZero hz).subset.trans (Set.empty_subset _)

/-- `ℱ[0]` as a perfect complex supported on the closed subscheme of `X` carried by the support
of `ℱ`. -/
def singlePushforwardSupportedPerfectOfSupport
    (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) :
    haveI : _root_.SheafOfModules.IsCoherent (F.obj : X.Modules) :=
      CoherentAbelian.isCoherent_of_stacksIsCoherent F.property
    supportedPerfectDerivedCategory ((reducedSupport (F.obj : X.Modules)).subschemeι ≫ i) :=
  ⟨(singlePushforwardSupportedPerfectGeneral i hY F).obj,
    (singlePushforwardSupportedPerfectGeneral i hY F).2.1,
    supp_homology_singlePushforwardSupportedPerfect_subset i hY F⟩

variable [CompactSpace Y]

/-- **The composition of Stacks 0FEW**
`K'₀(X) ⟶ K₀(D_{X,perf}(𝒪_Y)) ⟶ A^*(X ⟶ Y) ⊗ 𝐐 ⟶ CH_*(X) ⊗ 𝐐`, for a closed immersion
`i : X ⟶ Y` with `Y` regular and quasi-compact: the map `ℱ ↦ ℱ[0]` of Remark 0FEQ, the localized
Chern character `ch(X ⟶ Y, -)` of Remark 0FET (which is well defined by Lemma 0FBE), and the cap
product `c ↦ c ∩ [Y]`. -/
def coherentChowCharacter :
    KZero (Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) →+
      DirectSum ℤ fun k ↦ TensorProduct ℤ ℚ (chowGroup C (i ≫ a) k) :=
  haveI := isNoetherian_of_compactSpace C a
  ((rationalCapFundamentalClassSum C (gysinSystemOfInvertible C) (i ≫ a) a i rfl).comp
    (localizedChernCharKMapDirectSum C a isCompact_of_mem_irreducibleComponents)).comp
      (coherentToSupportedPerfectHomGeneral i hY)

/-- **The value of the composition of Stacks 0FEW on a coherent module**:
`[ℱ] ↦ ch(X ⟶ Y, ℱ[0]) ∩ [Y] = ∑_p ch_p(X ⟶ Y, ℱ[0]) ∩ [Y]`, the sum running over any range of
degrees outside of which `ch_p(X ⟶ Y, ℱ[0])` vanishes. -/
theorem coherentChowCharacter_mk (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf)
    (N : ℕ) (hN : ∀ p ≥ N, supportedLocalizedChernChar C a isCompact_of_mem_irreducibleComponents
      (singlePushforwardSupportedPerfectGeneral i hY F) p = 0) :
    haveI := isNoetherian_of_compactSpace C a
    coherentChowCharacter C a i hY (KZero.mk _ F) =
      ∑ p ∈ Finset.range N, rationalCapFundamentalClass C (gysinSystemOfInvertible C) (i ≫ a) a i
        rfl (p : ℤ) (supportedLocalizedChernChar C a isCompact_of_mem_irreducibleComponents
          (singlePushforwardSupportedPerfectGeneral i hY F) p) := by
  have := isNoetherian_of_compactSpace C a
  show rationalCapFundamentalClassSum C (gysinSystemOfInvertible C) (i ≫ a) a i rfl
    (localizedChernCharKMapDirectSum C a isCompact_of_mem_irreducibleComponents
      (coherentToSupportedPerfectHomGeneral i hY (KZero.mk _ F))) = _
  rw [coherentToSupportedPerfectHomGeneral_mk, localizedChernCharKMapDirectSum_cls,
    rationalCapFundamentalClassSum_apply _ _ _ _ _ _ _ N (by
      simpa only [coe_supportedLocalizedChernCharDirectSum] using hN)]
  simp only [coe_supportedLocalizedChernCharDirectSum]

/-! ### Condition (1) of the proof of Stacks 0FEW -/

/-- **Condition (1) of the proof of Stacks 0FEW.** If the support of a coherent `𝒪_X`-module `ℱ`
has delta-dimension at most `k`, the composition of Stacks 0FEW sends `[ℱ]` into
`⨁_{k' ≤ k} CH_{k'}(X) ⊗ 𝐐`. -/
theorem isDimensionTriangular_coherentChowCharacter :
    haveI := isNoetherian_of_isClosedImmersion_of_compactSpace C a i
    IsDimensionTriangular C (i ≫ a) (coherentChowCharacter C a i hY) := by
  have := isNoetherian_of_compactSpace C a
  have := isNoetherian_of_isClosedImmersion_of_compactSpace C a i
  intro k k' F hkk'
  have : _root_.SheafOfModules.IsCoherent (F.obj.obj : X.Modules) :=
    CoherentAbelian.isCoherent_of_stacksIsCoherent F.obj.property
  set ι := (reducedSupport (F.obj.obj : X.Modules)).subschemeι
  have hdim : schemeDeltaDimension C (ι ≫ (i ≫ a)) ≤ (k : EInt) := F.property
  have hZ : ∀ z, relativeDimension C.dimensionFunction ((ι ≫ i) ≫ a) z ≤ k := fun z ↦ by
    rw [Category.assoc, relativeDimension_comp_closedImmersion]
    exact relativeDimension_le_of_schemeDeltaDimension_le C (i ≫ a) ι hdim z
  obtain ⟨N, hN⟩ := exists_supportedLocalizedChernChar_eq_zero C a
    isCompact_of_mem_irreducibleComponents (singlePushforwardSupportedPerfectGeneral i hY F.obj)
  rw [coherentChowCharacter_mk C a i hY F.obj N hN, DFinsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun p _ ↦ ?_
  rw [supportedLocalizedChernChar_apply,
    supportedLocalizedPowerSum_eq_bivariantProperPushforward C a (j := ι) rfl
      isCompact_of_mem_irreducibleComponents (singlePushforwardSupportedPerfectOfSupport i hY F.obj)
      (singlePushforwardSupportedPerfectGeneral i hY F.obj) rfl p,
    rationalCapFundamentalClass_tmul, DFinsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun n _ ↦ ?_
  by_cases hnk : n - (p : ℤ) = k'
  · rw [capFundamentalClassAt_bivariantProperPushforward_eq_zero C _ _ _ ι i _ rfl _ hZ n
      (by omega), TensorProduct.tmul_zero, map_zero, DirectSum.zero_apply]
  · exact DirectSum.of_eq_of_ne _ _ _ (Ne.symm hnk)

end Composite

end Stacks.Chow

end
