module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapClosedImmersionInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerChowComparison
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerTwist
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.TensorMultiplicity
public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.CapProductIdentity
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardCoherent.Basic

/-!
# The twist of a coherent module in a dimension layer, and the first Chern class

Let `X` be locally of finite type over the base scheme of chapter 42 of the Stacks Project, let
`ℒ` be an invertible `𝒪_X`-module and let `ℱ` be coherent with `dim_δ(Supp ℱ) ≤ k + 1`. This file
proves the **cap-product clause of [Stacks, Tag 02SX]**: the image of

`[ℱ ⊗ ℒ] - [ℱ] ∈ Bₖ(X) ⊆ K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))`

under the homomorphism `Bₖ(X) ⟶ CH_k(X)` of [Stacks, Tag 02SC] is the cap product
`c₁(ℒ) ∩ [ℱ]_{k+1}` of [Stacks, Tag 02SO]. Together with the membership clause, which is
`Stacks.Chow.coherentDimensionKZeroMk_layerMkTensor_sub_mem` of
`StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerTwist`, this is the whole of Tag 02SX,
and the two clauses are stated as one result here.

The argument is the source's.

* The source's first paragraph reduces to the case where `ℱ` has no embedded associated points.
  One application of [Stacks, Tag 02OL] is enough: with `𝒦 ⊆ ℱ` the greatest coherent subsheaf of
  nowhere dense support and `ℱ' = ℱ/𝒦`, the element splits as
  `([𝒦 ⊗ ℒ] - [𝒦]) + ([ℱ' ⊗ ℒ] - [ℱ'])`, and the first bracket maps to zero because its two
  terms lie in `Bₖ(X)` separately and have the same `k`-cycle — tensoring with an invertible
  module does not change multiplicities, which is
  `Stacks.Chow.cycleAssociatedToCoherentSheaf_tensorModules_of_isInvertible`. On the cycle side
  `[ℱ]_{k+1} = [ℱ']_{k+1}`, since `dim_δ(Supp 𝒦) ≤ k`.
* For `ℱ` with no embedded associated points, [Stacks, Tag 02OM] descends it along the closed
  immersion `i : Z ⟶ X` of its scheme-theoretic support to a coherent `𝒪_Z`-module `𝒢` of full
  support with no embedded associated points, on a `Z` without embedded points. The restriction
  `𝒩 = i^*ℒ` is invertible and has a regular meromorphic section `s` by [Stacks, Tag 02OZ] case
  (3). Parts (1) and (2) of [Stacks, Tag 02SW] put the two canonical maps of the ideal of
  denominators of `s` in two short exact sequences with common first term, which identifies
  `[i_*(𝒢 ⊗ 𝒩)] - [i_*𝒢]` with `[i_*𝒬₂] - [i_*𝒬₁]`; the projection formula
  [Stacks, Tag 01E8] for a closed immersion turns the left-hand side into `[ℱ ⊗ ℒ] - [ℱ]`.
* The identity on `Z` is the cap-product form of part (4) of [Stacks, Tag 02SW],
  `Stacks.Chow.firstChernClassCapOfInvertible_cycleAssociatedToCoherentSheaf_eq_mk_sub`. It is
  carried to `X` by [Stacks, Tag 02SU] for a closed immersion, for the cap product, and by
  [Stacks, Tag 02R6] part (2), for the cycle of a coherent module.

## Main results

* `Stacks.Chow.coherentDimensionLayerImageChowHom_eq_firstChernClassCap` — the cap-product clause.
* `Stacks.Chow.exists_mem_coherentDimensionLayerImage_layerMkTensor_sub` — **Tag 02SX**, both
  clauses at once.

## Implementation notes

**The subgroup element is a parameter.** Every statement of the chain takes an element `x` of
`Bₖ(X)` together with an equation identifying the underlying class, rather than an explicit
anonymous constructor carrying a membership proof. Membership is a `Prop`, so the two forms are
interchangeable; the parametrized form is the one that composes, since the membership proof the
reduction produces is not the one a later step would write down.

**The hypotheses of Tag 02SX, and nothing more.** In particular
`AlgebraicGeometry.HasNoEmbeddedPoints X` is *not* assumed: the source obtains the
no-embedded-points hypothesis of Tag 02SW by passing to the scheme-theoretic support of `ℱ`, and
so does the proof here.

## References

* [Stacks Project, Tag 02SX](https://stacks.math.columbia.edu/tag/02SX)
* [Stacks Project, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW)
* [Stacks Project, Tag 02SU](https://stacks.math.columbia.edu/tag/02SU)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02SC](https://stacks.math.columbia.edu/tag/02SC)
* [Stacks Project, Tag 02R6](https://stacks.math.columbia.edu/tag/02R6)
* [Stacks Project, Tag 02QZ](https://stacks.math.columbia.edu/tag/02QZ)
* [Stacks Project, Tag 02OM](https://stacks.math.columbia.edu/tag/02OM)
* [Stacks Project, Tag 02OL](https://stacks.math.columbia.edu/tag/02OL)
* [Stacks Project, Tag 02OZ](https://stacks.math.columbia.edu/tag/02OZ)
* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.CoherentSubquotients

universe u

namespace Stacks.Chow

/-! ### The image in `CH_k(X)` of a class coming from a module of support dimension `≤ k` -/

/-- The class of an object of the layer whose support has delta-dimension at most `k` lies in
`Bₖ(X)`, and its image in `CH_k(X)` is the class of its `k`-cycle. -/
private theorem exists_mem_chowHom_eq_mk_layerCycleOfLE (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)
    (A : CoherentModulesDimLE C f (k + 1)) (hA : coherentModulesDimLE C f k A.obj) :
    ∃ hm : coherentDimensionKZeroMk C f (k - 1) (k + 1) A ∈ coherentDimensionLayerImage C f k,
      coherentDimensionLayerImageChowHom C f k ⟨_, hm⟩ =
        QuotientAddGroup.mk' (rationalEquivalences C f k) (layerCycleOfLE C f k A hA) :=
  ⟨coherentDimensionKZeroMk_mem_coherentDimensionLayerImage C f k A hA,
    coherentDimensionLayerImageChowHom_coherentDimensionKZeroMk C f k ⟨A.obj, hA⟩ _⟩

/-- The homomorphism `Bₖ(X) ⟶ CH_k(X)` on an element of `Bₖ(X)` which is the class of an object
of the layer `(k-1, k+1]` whose support has delta-dimension at most `k`. -/
theorem coherentDimensionLayerImageChowHom_eq_mk_layerCycleOfLE (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)
    (A : CoherentModulesDimLE C f (k + 1)) (hA : coherentModulesDimLE C f k A.obj)
    (x : coherentDimensionLayerImage C f k)
    (hx : (x : coherentDimensionKZero C f (k - 1) (k + 1)) =
      coherentDimensionKZeroMk C f (k - 1) (k + 1) A) :
    coherentDimensionLayerImageChowHom C f k x =
      QuotientAddGroup.mk' (rationalEquivalences C f k) (layerCycleOfLE C f k A hA) := by
  obtain ⟨hm, h⟩ := exists_mem_chowHom_eq_mk_layerCycleOfLE C f k A hA
  rw [show x = ⟨_, hm⟩ from Subtype.ext hx]
  exact h

/-! ### The equation behind the K-group bookkeeping of Stacks 02SX -/

/-- **Two short exact sequences with a common first term identify a difference of classes.** The
equation form of `Stacks.Chow.coherentDimensionKZeroMk_finitePushforward_sub_mem`: the difference
of the classes of the direct images of the two middle terms is the difference of the classes of
the direct images of the two third terms. -/
theorem coherentDimensionKZeroMk_finitePushforward_sub_eq (C : ChowSituation.{u})
    {X Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (sZ : Z ⟶ C.S)
    [LocallyOfFiniteType sZ] (i : Z ⟶ X) [IsFinite i] (hπ : i ≫ f = sZ) {k : ℤ}
    {P B₁ B₂ Q₁ Q₂ : CoherentModulesDimLE C sZ (k + 1)}
    (u₁ : P.obj.obj ⟶ B₁.obj.obj) (v₁ : B₁.obj.obj ⟶ Q₁.obj.obj) (w₁ : u₁ ≫ v₁ = 0)
    (h₁ : (ShortComplex.mk u₁ v₁ w₁).ShortExact)
    (u₂ : P.obj.obj ⟶ B₂.obj.obj) (v₂ : B₂.obj.obj ⟶ Q₂.obj.obj) (w₂ : u₂ ≫ v₂ = 0)
    (h₂ : (ShortComplex.mk u₂ v₂ w₂).ShortExact) :
    coherentDimensionKZeroMk C f (k - 1) (k + 1)
          ((finitePushforwardDimLE C sZ f i hπ (k + 1)).obj B₂) -
        coherentDimensionKZeroMk C f (k - 1) (k + 1)
          ((finitePushforwardDimLE C sZ f i hπ (k + 1)).obj B₁) =
      coherentDimensionKZeroMk C f (k - 1) (k + 1)
          ((finitePushforwardDimLE C sZ f i hπ (k + 1)).obj Q₂) -
        coherentDimensionKZeroMk C f (k - 1) (k + 1)
          ((finitePushforwardDimLE C sZ f i hπ (k + 1)).obj Q₁) := by
  have hadd₁ := coherentDimensionKZeroMk_finitePushforward_add_of_modules C f sZ i hπ (k - 1)
    (k + 1) u₁ v₁ w₁ h₁
  have hadd₂ := coherentDimensionKZeroMk_finitePushforward_add_of_modules C f sZ i hπ (k - 1)
    (k + 1) u₂ v₂ w₂ h₂
  rw [hadd₁, hadd₂]
  abel

/-- **The `k`-cycle of a direct image along a finite morphism**, read on the layers: this is
[Stacks, Tag 02R6] part (2) at the layer spelling. -/
theorem layerCycleOfLE_finitePushforwardDimLE (C : ChowSituation.{u}) {X Z : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (i : Z ⟶ X)
    [IsClosedImmersion i] (hπ : i ≫ f = sZ) {k : ℤ} (A : CoherentModulesDimLE C sZ (k + 1))
    (h : coherentModulesDimLE C sZ k A.obj)
    (hp : coherentModulesDimLE C f k ((finitePushforwardDimLE C sZ f i hπ (k + 1)).obj A).obj) :
    layerCycleOfLE C f k ((finitePushforwardDimLE C sZ f i hπ (k + 1)).obj A) hp =
      properPushforward C sZ f i hπ k (layerCycleOfLE C sZ k A h) := by
  have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have _ : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have _ := isCoherent_layerToModules C sZ (k + 1) A
  have _ : _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward i).obj A.obj.obj) :=
    Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite i
      A.obj.obj
  exact (properPushforward_cycleAssociatedToCoherentSheaf C sZ f i hπ A.obj.obj k h).symm

/-- **The image in `CH_k(X)` of a difference of classes of direct images.** If an element of
`Bₖ(X)` is the difference of the classes of the direct images of two objects of the layer over
`Z` whose supports have delta-dimension at most `k`, then its image in `CH_k(X)` is the class of
the difference of the proper pushforwards of their `k`-cycles. -/
theorem coherentDimensionLayerImageChowHom_eq_mk_properPushforward_sub (C : ChowSituation.{u})
    {X Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (sZ : Z ⟶ C.S)
    [LocallyOfFiniteType sZ] (i : Z ⟶ X) [IsClosedImmersion i] (hπ : i ≫ f = sZ) {k : ℤ}
    (A₁ A₂ : CoherentModulesDimLE C sZ (k + 1))
    (h₁ : coherentModulesDimLE C sZ k A₁.obj) (h₂ : coherentModulesDimLE C sZ k A₂.obj)
    (x : coherentDimensionLayerImage C f k)
    (hx : (x : coherentDimensionKZero C f (k - 1) (k + 1)) =
      coherentDimensionKZeroMk C f (k - 1) (k + 1)
          ((finitePushforwardDimLE C sZ f i hπ (k + 1)).obj A₂) -
        coherentDimensionKZeroMk C f (k - 1) (k + 1)
          ((finitePushforwardDimLE C sZ f i hπ (k + 1)).obj A₁)) :
    coherentDimensionLayerImageChowHom C f k x =
      QuotientAddGroup.mk' (rationalEquivalences C f k)
        (properPushforward C sZ f i hπ k (layerCycleOfLE C sZ k A₂ h₂) -
          properPushforward C sZ f i hπ k (layerCycleOfLE C sZ k A₁ h₁)) := by
  have hpf₁ : coherentModulesDimLE C f k
      ((finitePushforwardDimLE C sZ f i hπ (k + 1)).obj A₁).obj :=
    coherentModulesDimLE_finitePushforward C sZ f i hπ k A₁.obj h₁
  have hpf₂ : coherentModulesDimLE C f k
      ((finitePushforwardDimLE C sZ f i hπ (k + 1)).obj A₂).obj :=
    coherentModulesDimLE_finitePushforward C sZ f i hπ k A₂.obj h₂
  obtain ⟨hm₁, e₁⟩ := exists_mem_chowHom_eq_mk_layerCycleOfLE C f k _ hpf₁
  obtain ⟨hm₂, e₂⟩ := exists_mem_chowHom_eq_mk_layerCycleOfLE C f k _ hpf₂
  rw [show x = ⟨_, hm₂⟩ - ⟨_, hm₁⟩ from Subtype.ext hx, map_sub, e₂, e₁, ← map_sub,
    layerCycleOfLE_finitePushforwardDimLE C f sZ i hπ A₁ h₁ hpf₁,
    layerCycleOfLE_finitePushforwardDimLE C f sZ i hπ A₂ h₂ hpf₂]

/-! ### The two denominator quotients as objects of a layer -/

section Quotients

variable (C : ChowSituation.{u}) {Z : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (N G : Z.Modules) (s : AlgebraicGeometry.MeromorphicSection Z.sheaf N) [G.IsCoherent] {k : ℤ}
  (hdimZ : schemeDeltaDimension C sZ ≤ ((k + 1 : ℤ) : EInt))
  (hZemb : HasNoEmbeddedPoints Z) (hGemb : HasNoEmbeddedAssociatedPoints G)
  (hGsupp : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules G).supp = Set.univ)
  (hN : AlgebraicGeometry.SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property N)
  (hs : IsRegularMeromorphicSection Z.sheaf N s)

/-- **`𝒬₁` as an object of the dimension layer `Coh_{≤k+1}(𝒪_Z)`.** -/
def denominatorQuotientLayer : CoherentModulesDimLE C sZ (k + 1) :=
  letI := isCoherent_denominatorQuotient C sZ N G s hdimZ hZemb hGemb hGsupp hN hs
  layerMk C sZ (k + 1) (denominatorQuotient Z N G s)
    ((schemeDeltaDimension_denominatorQuotient_le C sZ N G s hdimZ hZemb hGemb hGsupp hN hs).trans
      (WithBotTop.coe_le_coe.mpr (by omega)))

/-- **`𝒬₂` as an object of the dimension layer `Coh_{≤k+1}(𝒪_Z)`.** -/
def denominatorSectionQuotientLayer : CoherentModulesDimLE C sZ (k + 1) :=
  letI := LocallyOfFiniteType.isLocallyNoetherian sZ
  letI := isCoherent_denominatorSectionQuotient C sZ N G s hdimZ hZemb hGemb hGsupp hN hs
  layerMk C sZ (k + 1) (denominatorSectionQuotient Z N G s hN hs hGemb hGsupp)
    ((schemeDeltaDimension_denominatorSectionQuotient_le C sZ N G s hdimZ hZemb hGemb hGsupp hN
      hs).trans (WithBotTop.coe_le_coe.mpr (by omega)))

/-- The support of `𝒬₁` has delta-dimension at most `k`, by part (2) of [Stacks, Tag 02SW]. -/
theorem coherentModulesDimLE_denominatorQuotientLayer :
    coherentModulesDimLE C sZ k
      (denominatorQuotientLayer C sZ N G s hdimZ hZemb hGemb hGsupp hN hs).obj :=
  schemeDeltaDimension_denominatorQuotient_le C sZ N G s hdimZ hZemb hGemb hGsupp hN hs

/-- The support of `𝒬₂` has delta-dimension at most `k`, by part (2) of [Stacks, Tag 02SW]. -/
theorem coherentModulesDimLE_denominatorSectionQuotientLayer :
    coherentModulesDimLE C sZ k
      (denominatorSectionQuotientLayer C sZ N G s hdimZ hZemb hGemb hGsupp hN hs).obj :=
  schemeDeltaDimension_denominatorSectionQuotient_le C sZ N G s hdimZ hZemb hGemb hGsupp hN hs

/-- The `k`-cycle of `𝒬₁` read on the layer is `[𝒬₁]_k`. -/
theorem layerCycleOfLE_denominatorQuotientLayer :
    layerCycleOfLE C sZ k (denominatorQuotientLayer C sZ N G s hdimZ hZemb hGemb hGsupp hN hs)
        (coherentModulesDimLE_denominatorQuotientLayer C sZ N G s hdimZ hZemb hGemb hGsupp hN
          hs) =
      denominatorQuotientCycle C sZ N G s hdimZ hZemb hGemb hGsupp hN hs :=
  rfl

/-- The `k`-cycle of `𝒬₂` read on the layer is `[𝒬₂]_k`. -/
theorem layerCycleOfLE_denominatorSectionQuotientLayer :
    layerCycleOfLE C sZ k
        (denominatorSectionQuotientLayer C sZ N G s hdimZ hZemb hGemb hGsupp hN hs)
        (coherentModulesDimLE_denominatorSectionQuotientLayer C sZ N G s hdimZ hZemb hGemb hGsupp
          hN hs) =
      denominatorSectionQuotientCycle C sZ N G s hdimZ hZemb hGemb hGsupp hN hs :=
  rfl

end Quotients

/-! ### The two sequences of Stacks 02SW, as an equation in the layer over `X` -/

/-- **The equation form of
`Stacks.Chow.coherentDimensionKZeroMk_finitePushforward_tensor_sub_mem_of_regularSection`.**
Parts (1) and (2) of [Stacks, Tag 02SW] put the two canonical maps of the ideal of denominators
in two short exact sequences with common first term `ℐ𝒢`, so the difference of the classes of the
direct images of `𝒢 ⊗ 𝒩` and `𝒢` is the difference of the classes of the direct images of `𝒬₂`
and `𝒬₁`. -/
theorem coherentDimensionKZeroMk_finitePushforward_tensor_sub_eq_of_regularSection
    (C : ChowSituation.{u}) {X Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (i : Z ⟶ X) [IsClosedImmersion i] [LocallyOfFiniteType (i ≫ f)] (N G : Z.Modules)
    [G.IsCoherent] [(tensorModules G N).IsCoherent]
    (hN : AlgebraicGeometry.SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property N)
    {k : ℤ} (hdimZ : schemeDeltaDimension C (i ≫ f) ≤ ((k + 1 : ℤ) : EInt))
    (hZemb : HasNoEmbeddedPoints Z) (hGemb : HasNoEmbeddedAssociatedPoints G)
    (hGsupp : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules G).supp = Set.univ)
    (s : AlgebraicGeometry.MeromorphicSection Z.sheaf N)
    (hs : IsRegularMeromorphicSection Z.sheaf N s) :
    coherentDimensionKZeroMk C f (k - 1) (k + 1)
          ((finitePushforwardDimLE C (i ≫ f) f i rfl (k + 1)).obj
            (layerMk C (i ≫ f) (k + 1) (tensorModules G N)
              (schemeDeltaDimension_reducedSupport_le_of_le C (i ≫ f) (tensorModules G N) hdimZ))) -
        coherentDimensionKZeroMk C f (k - 1) (k + 1)
          ((finitePushforwardDimLE C (i ≫ f) f i rfl (k + 1)).obj
            (layerMk C (i ≫ f) (k + 1) G
              (schemeDeltaDimension_reducedSupport_le_of_le C (i ≫ f) G hdimZ))) =
      coherentDimensionKZeroMk C f (k - 1) (k + 1)
          ((finitePushforwardDimLE C (i ≫ f) f i rfl (k + 1)).obj
            (denominatorSectionQuotientLayer C (i ≫ f) N G s hdimZ hZemb hGemb hGsupp hN hs)) -
        coherentDimensionKZeroMk C f (k - 1) (k + 1)
          ((finitePushforwardDimLE C (i ≫ f) f i rfl (k + 1)).obj
            (denominatorQuotientLayer C (i ≫ f) N G s hdimZ hZemb hGemb hGsupp hN hs)) := by
  have hZN : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (i ≫ f)
  have hPcoh : (denominatorIdealTimesModule Z N G s).IsCoherent :=
    isCoherent_denominatorIdealTimesModule N G s hN
  exact coherentDimensionKZeroMk_finitePushforward_sub_eq C f (i ≫ f) i rfl
    (P := layerMk C (i ≫ f) (k + 1) (denominatorIdealTimesModule Z N G s)
      (schemeDeltaDimension_reducedSupport_le_of_le C (i ≫ f) _ hdimZ))
    (Q₁ := denominatorQuotientLayer C (i ≫ f) N G s hdimZ hZemb hGemb hGsupp hN hs)
    (Q₂ := denominatorSectionQuotientLayer C (i ≫ f) N G s hdimZ hZemb hGemb hGsupp hN hs)
    (denominatorIdealTimesModuleι Z N G s)
    (cokernel.π (denominatorIdealTimesModuleι Z N G s)) (cokernel.condition _)
    (denominatorQuotientShortComplex_shortExact C (i ≫ f) N G s hdimZ hZemb hGemb hGsupp hN hs)
    (denominatorIdealTimesModuleMul Z N G s hN hs hGemb hGsupp).val
    (cokernel.π (denominatorIdealTimesModuleMul Z N G s hN hs hGemb hGsupp).val)
    (cokernel.condition _)
    (denominatorSectionQuotientShortComplex_shortExact C (i ≫ f) N G s hdimZ hZemb hGemb hGsupp
      hN hs)

/-! ### The difference `[ℱ ⊗ ℒ] - [ℱ]` for a descended module, as a difference of quotients -/

/-- **The difference `[ℱ ⊗ ℒ] - [ℱ]` is the difference of the classes of the direct images of the
two denominator quotients of [Stacks, Tag 02SW].** Let `i : Z ⟶ X` be a closed immersion with
`dim_δ(Z) ≤ k + 1` and no embedded points, let `𝒢` be a coherent `𝒪_Z`-module of full support
with no embedded associated points, let `ℱ ≅ i_*𝒢`, and let `s` be a regular meromorphic section
of `𝒩 = i^*ℒ`. This is the equation form of
`Stacks.Chow.coherentDimensionKZeroMk_layerMkTensor_sub_mem_of_descends`: the two classes it
compares are `[ℱ ⊗ ℒ]` and `[ℱ]` by the projection formula [Stacks, Tag 01E8] for a closed
immersion together with `i_*𝒢 ≅ ℱ`. -/
theorem coherentDimensionKZeroMk_layerMkTensor_sub_eq_of_descends (C : ChowSituation.{u})
    {X Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFiniteType (i ≫ f)] (F : X.Modules) [F.IsCoherent] (L : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    {k : ℤ}
    (hdim : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ f) ≤ ((k + 1 : ℤ) : EInt))
    (hdimZ : schemeDeltaDimension C (i ≫ f) ≤ ((k + 1 : ℤ) : EInt))
    (hZemb : HasNoEmbeddedPoints Z) (G : Z.Modules) [G.IsCoherent]
    (hGemb : HasNoEmbeddedAssociatedPoints G)
    (hGsupp : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules G).supp = Set.univ)
    (e : (Scheme.Modules.pushforward i).obj G ≅ F)
    (hN : AlgebraicGeometry.SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property
      ((Scheme.Modules.pullback i).obj L))
    (s : AlgebraicGeometry.MeromorphicSection Z.sheaf ((Scheme.Modules.pullback i).obj L))
    (hs : IsRegularMeromorphicSection Z.sheaf ((Scheme.Modules.pullback i).obj L) s) :
    coherentDimensionKZeroMk C f (k - 1) (k + 1) (layerMkTensor C f (k + 1) F L hL hdim) -
        coherentDimensionKZeroMk C f (k - 1) (k + 1) (layerMk C f (k + 1) F hdim) =
      coherentDimensionKZeroMk C f (k - 1) (k + 1)
          ((finitePushforwardDimLE C (i ≫ f) f i rfl (k + 1)).obj
            (denominatorSectionQuotientLayer C (i ≫ f) ((Scheme.Modules.pullback i).obj L) G s
              hdimZ hZemb hGemb hGsupp hN hs)) -
        coherentDimensionKZeroMk C f (k - 1) (k + 1)
          ((finitePushforwardDimLE C (i ≫ f) f i rfl (k + 1)).obj
            (denominatorQuotientLayer C (i ≫ f) ((Scheme.Modules.pullback i).obj L) G s hdimZ
              hZemb hGemb hGsupp hN hs)) := by
  have hL' : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := hL
  have hGNcoh : (tensorModules G ((Scheme.Modules.pullback i).obj L)).IsCoherent :=
    isCoherent_tensorModules_of_isInvertible G _ hN
  have heq := coherentDimensionKZeroMk_finitePushforward_tensor_sub_eq_of_regularSection C f i
    ((Scheme.Modules.pullback i).obj L) G hN hdimZ hZemb hGemb hGsupp s hs
  have heG : coherentDimensionKZeroMk C f (k - 1) (k + 1)
      ((finitePushforwardDimLE C (i ≫ f) f i rfl (k + 1)).obj
        (layerMk C (i ≫ f) (k + 1) G
          (schemeDeltaDimension_reducedSupport_le_of_le C (i ≫ f) G hdimZ))) =
      coherentDimensionKZeroMk C f (k - 1) (k + 1) (layerMk C f (k + 1) F hdim) :=
    coherentDimensionKZeroMk_eq_of_moduleIso C f (k - 1) (k + 1) e
  have heGN : coherentDimensionKZeroMk C f (k - 1) (k + 1)
      ((finitePushforwardDimLE C (i ≫ f) f i rfl (k + 1)).obj
        (layerMk C (i ≫ f) (k + 1) (tensorModules G ((Scheme.Modules.pullback i).obj L))
          (schemeDeltaDimension_reducedSupport_le_of_le C (i ≫ f)
            (tensorModules G ((Scheme.Modules.pullback i).obj L)) hdimZ))) =
      coherentDimensionKZeroMk C f (k - 1) (k + 1) (layerMkTensor C f (k + 1) F L hL hdim) :=
    coherentDimensionKZeroMk_eq_of_moduleIso C f (k - 1) (k + 1)
      ((pushforwardTensorModulesIso i G L).symm ≪≫ tensorModulesIsoLeft e L)
  rw [heG, heGN] at heq
  exact heq

/-! ### The cap-product identity of Stacks 02SX for a descended module -/

/-- **[Stacks, Tag 02SX], the cap-product clause, for a module descended to a closed subscheme
without embedded points.** Let `i : Z ⟶ X` be a closed immersion with `dim_δ(Z) ≤ k + 1` and no
embedded points, let `𝒢` be a coherent `𝒪_Z`-module of full support with no embedded associated
points, and let `ℱ ≅ i_*𝒢` be coherent with `dim_δ(Supp ℱ) ≤ k + 1`. Then the image of
`[ℱ ⊗ ℒ] - [ℱ]` under the homomorphism `Bₖ(X) ⟶ CH_k(X)` of [Stacks, Tag 02SC] is
`c₁(ℒ) ∩ [ℱ]_{k+1}`.

The identity is read on `Z`, where it is the cap-product form of part (4) of
[Stacks, Tag 02SW] —
`Stacks.Chow.firstChernClassCapOfInvertible_cycleAssociatedToCoherentSheaf_eq_mk_sub` for a
regular meromorphic section of `𝒩 = i^*ℒ`, which exists by [Stacks, Tag 02OZ] case (3) —
and then pushed forward along `i`: the cap product travels by [Stacks, Tag 02SU] for a closed
immersion, and the cycle of a coherent module by [Stacks, Tag 02R6] part (2). -/
theorem coherentDimensionLayerImageChowHom_eq_firstChernClassCap_of_descends
    (C : ChowSituation.{u}) {X Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (i : Z ⟶ X)
    [IsClosedImmersion i] [LocallyOfFiniteType (i ≫ f)] (F : X.Modules) [F.IsCoherent]
    (L : X.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    {k : ℤ}
    (hdim : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ f) ≤ ((k + 1 : ℤ) : EInt))
    (hdimZ : schemeDeltaDimension C (i ≫ f) ≤ ((k + 1 : ℤ) : EInt))
    (hZemb : HasNoEmbeddedPoints Z) (G : Z.Modules) [G.IsCoherent]
    (hGemb : HasNoEmbeddedAssociatedPoints G)
    (hGsupp : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules G).supp = Set.univ)
    (e : (Scheme.Modules.pushforward i).obj G ≅ F) (x : coherentDimensionLayerImage C f k)
    (hx : (x : coherentDimensionKZero C f (k - 1) (k + 1)) =
      coherentDimensionKZeroMk C f (k - 1) (k + 1) (layerMkTensor C f (k + 1) F L hL hdim) -
        coherentDimensionKZeroMk C f (k - 1) (k + 1) (layerMk C f (k + 1) F hdim)) :
    coherentDimensionLayerImageChowHom C f k x =
      firstChernClassCapOfInvertible C f k L
        (cycleAssociatedToCoherentSheaf C f F (k + 1) hdim) := by
  have hL' : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := hL
  have hXN : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hZN : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (i ≫ f)
  have hNpre : AlgebraicGeometry.SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
      ((Scheme.Modules.pullback i).obj L) :=
    AlgebraicGeometry.SheafOfModules.isInvertible_pullback i L
  have hN : AlgebraicGeometry.SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property
      ((Scheme.Modules.pullback i).obj L) := hNpre
  have hGk : schemeDeltaDimension C ((reducedSupport G).subschemeι ≫ (i ≫ f)) ≤
      ((k + 1 : ℤ) : EInt) :=
    schemeDeltaDimension_reducedSupport_le_of_le C (i ≫ f) G hdimZ
  have hGpush : _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward i).obj G) :=
    Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite i G
  obtain ⟨s, hs⟩ := AlgebraicGeometry.exists_isRegularMeromorphicSection_of_hasNoEmbeddedPoints Z
    hZemb ((Scheme.Modules.pullback i).obj L)
  -- the image of `[ℱ ⊗ ℒ] - [ℱ]` is the class of the pushforward of `[𝒬₂]_k - [𝒬₁]_k`
  have hKey := coherentDimensionLayerImageChowHom_eq_mk_properPushforward_sub C f (i ≫ f) i rfl
    (denominatorQuotientLayer C (i ≫ f) ((Scheme.Modules.pullback i).obj L) G s hdimZ hZemb hGemb
      hGsupp hN hs)
    (denominatorSectionQuotientLayer C (i ≫ f) ((Scheme.Modules.pullback i).obj L) G s hdimZ
      hZemb hGemb hGsupp hN hs)
    (coherentModulesDimLE_denominatorQuotientLayer C (i ≫ f) ((Scheme.Modules.pullback i).obj L) G
      s hdimZ hZemb hGemb hGsupp hN hs)
    (coherentModulesDimLE_denominatorSectionQuotientLayer C (i ≫ f)
      ((Scheme.Modules.pullback i).obj L) G s hdimZ hZemb hGemb hGsupp hN hs)
    x (hx.trans (coherentDimensionKZeroMk_layerMkTensor_sub_eq_of_descends C f i F L hL hdim hdimZ
      hZemb G hGemb hGsupp e hN s hs))
  rw [hKey, layerCycleOfLE_denominatorQuotientLayer,
    layerCycleOfLE_denominatorSectionQuotientLayer]
  -- the same class is `c₁(ℒ) ∩ [ℱ]_{k+1}`, read on `Z` and pushed forward
  have hZid := firstChernClassCapOfInvertible_cycleAssociatedToCoherentSheaf_eq_mk_sub C (i ≫ f)
    ((Scheme.Modules.pullback i).obj L) G s hdimZ hZemb hGemb hGsupp hs hGk
  have h1 : properPushforward C (i ≫ f) f i rfl (k + 1)
        (cycleAssociatedToCoherentSheaf C (i ≫ f) G (k + 1) hGk) =
      cycleAssociatedToCoherentSheaf C f F (k + 1) hdim := by
    rw [properPushforward_cycleAssociatedToCoherentSheaf C (i ≫ f) f i rfl G (k + 1) hGk]
    exact cycleAssociatedToCoherentSheaf_eq_of_iso C f e (k + 1) _ hdim
  rw [← h1, ← properChowPushforward_firstChernClassCapOfInvertible C (i ≫ f) f i rfl k L, hZid,
    show (QuotientAddGroup.mk
          (denominatorSectionQuotientCycle C (i ≫ f) ((Scheme.Modules.pullback i).obj L) G s
              hdimZ hZemb hGemb hGsupp hN hs -
            denominatorQuotientCycle C (i ≫ f) ((Scheme.Modules.pullback i).obj L) G s hdimZ
              hZemb hGemb hGsupp hN hs) : chowGroup C (i ≫ f) k) =
        QuotientAddGroup.mk' (rationalEquivalences C (i ≫ f) k)
          (denominatorSectionQuotientCycle C (i ≫ f) ((Scheme.Modules.pullback i).obj L) G s
              hdimZ hZemb hGemb hGsupp hN hs -
            denominatorQuotientCycle C (i ≫ f) ((Scheme.Modules.pullback i).obj L) G s hdimZ
              hZemb hGemb hGsupp hN hs) from rfl,
    properChowPushforward_mk, properPushforward_sub]

/-! ### The cap-product identity of Stacks 02SX for a module with no embedded associated points -/

/-- **[Stacks, Tag 02SX], the cap-product clause, for a module with no embedded associated
points.** This is the previous result at the scheme-theoretic support of `ℱ`, whose data is
[Stacks, Tag 02OM]. -/
theorem coherentDimensionLayerImageChowHom_eq_firstChernClassCap_of_hasNoEmbedded
    (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsCoherent] (hF : HasNoEmbeddedAssociatedPoints F) (L : X.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    {k : ℤ}
    (hdim : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ f) ≤ ((k + 1 : ℤ) : EInt))
    (x : coherentDimensionLayerImage C f k)
    (hx : (x : coherentDimensionKZero C f (k - 1) (k + 1)) =
      coherentDimensionKZeroMk C f (k - 1) (k + 1) (layerMkTensor C f (k + 1) F L hL hdim) -
        coherentDimensionKZeroMk C f (k - 1) (k + 1) (layerMk C f (k + 1) F hdim)) :
    coherentDimensionLayerImageChowHom C f k x =
      firstChernClassCapOfInvertible C f k L
        (cycleAssociatedToCoherentSheaf C f F (k + 1) hdim) := by
  have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨G, hGcoh, hGemb, hGsupp, ⟨e⟩⟩ :=
    AlgebraicGeometry.exists_coherent_module_on_annihilatorIdeal_subscheme F hF
  have _ : G.IsCoherent := hGcoh
  exact coherentDimensionLayerImageChowHom_eq_firstChernClassCap_of_descends C f
    (annihilatorIdeal' F).subschemeι F L hdim (schemeDeltaDimension_annihilatorIdeal_le C f F hdim)
    (AlgebraicGeometry.hasNoEmbeddedPoints_annihilatorIdeal_subscheme F hF) G hGemb hGsupp e x hx

/-! ### Vanishing of a cycle in a grading above the dimension of the support -/

/-- **The `k`-cycle of a coherent module whose support has delta-dimension below `k` vanishes.**
A point of the support has relative dimension at most that bound, so it is not one of the points
of relative dimension `k` carrying the coefficients of a `k`-cycle. -/
theorem cycleAssociatedToCoherentSheaf_eq_zero_of_lt (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (M : X.Modules) [M.IsCoherent] {k l : ℤ} (hlk : l < k)
    (hk : schemeDeltaDimension C ((reducedSupport M).subschemeι ≫ f) ≤ (k : EInt))
    (hl : schemeDeltaDimension C ((reducedSupport M).subschemeι ≫ f) ≤ (l : EInt)) :
    cycleAssociatedToCoherentSheaf C f M k hk = 0 := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  change (cycleAssociatedToCoherentSheaf C f M k hk).1 x = 0
  by_cases hx : relativeDimension C.dimensionFunction f x = k
  · rw [cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq C f M k hk hx]
    refine sheafMultiplicity_eq_zero_of_notMem_supp M fun hmem => ?_
    have hle := relativeDimension_le_of_mem_supp C f M hl hmem
    omega
  · exact cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_ne C f M k hk hx

/-! ### The cap-product identity of Stacks 02SX -/

/-- **[Stacks, Tag 02SX], the cap-product clause.** For `ℒ` invertible and `ℱ` coherent with
`dim_δ(Supp ℱ) ≤ k + 1`, the image of `[ℱ ⊗ ℒ] - [ℱ]` under the homomorphism `Bₖ(X) ⟶ CH_k(X)`
of [Stacks, Tag 02SC] is the cap product `c₁(ℒ) ∩ [ℱ]_{k+1}` of [Stacks, Tag 02SO].

The reduction to the case of no embedded associated points is the source's first paragraph, in
the one-step form: [Stacks, Tag 02OL] produces the greatest coherent subsheaf `𝒦 ⊆ ℱ` whose
support is nowhere dense in `Supp ℱ`, the quotient `ℱ' = ℱ/𝒦` has no embedded associated points
and the same support as `ℱ`, and `dim_δ(Supp 𝒦) ≤ k`. Tensoring by `ℒ` is exact, so

`[ℱ ⊗ ℒ] - [ℱ] = ([𝒦 ⊗ ℒ] - [𝒦]) + ([ℱ' ⊗ ℒ] - [ℱ'])`

and both brackets lie in `Bₖ(X)`. The first maps to zero, because both of its terms separately
lie in `Bₖ(X)` and `[𝒦 ⊗ ℒ]_k = [𝒦]_k` — tensoring with an invertible module does not change
multiplicities, which is `Stacks.Chow.cycleAssociatedToCoherentSheaf_tensorModules_of_isInvertible`
and is why one application of Tag 02OL suffices here. The second maps to `c₁(ℒ) ∩ [ℱ']_{k+1}`,
and `[ℱ]_{k+1} = [𝒦]_{k+1} + [ℱ']_{k+1} = [ℱ']_{k+1}` by [Stacks, Tag 02QZ] and the vanishing of
`[𝒦]_{k+1}`. -/
theorem coherentDimensionLayerImageChowHom_eq_firstChernClassCap (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (F : X.Modules) [F.IsCoherent]
    (L : X.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    {k : ℤ}
    (hdim : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ f) ≤ ((k + 1 : ℤ) : EInt))
    (x : coherentDimensionLayerImage C f k)
    (hx : (x : coherentDimensionKZero C f (k - 1) (k + 1)) =
      coherentDimensionKZeroMk C f (k - 1) (k + 1) (layerMkTensor C f (k + 1) F L hL hdim) -
        coherentDimensionKZeroMk C f (k - 1) (k + 1) (layerMk C f (k + 1) F hdim)) :
    coherentDimensionLayerImageChowHom C f k x =
      firstChernClassCapOfInvertible C f k L
        (cycleAssociatedToCoherentSheaf C f F (k + 1) hdim) := by
  have hXN : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  -- the greatest nowhere dense coherent subsheaf of Tag 02OL, and the quotient by it
  obtain ⟨K, hK, hmax⟩ := exists_greatest_isNowhereDenseCoherentSubobject F
  have hKcoh : (K : X.Modules).IsCoherent := hK.1
  have hQcoh : (cokernel K.arrow).IsCoherent := isCoherent_cokernel K.arrow
  have hQemb : HasNoEmbeddedAssociatedPoints (cokernel K.arrow) :=
    cokernel_hasNoEmbeddedAssociatedPoints F K hK hmax
  have hKTcoh : (tensorModules (K : X.Modules) L).IsCoherent :=
    isCoherent_tensorModules_of_isInvertible (K : X.Modules) L hL
  -- the support bounds
  have hKdimk : schemeDeltaDimension C ((reducedSupport (K : X.Modules)).subschemeι ≫ f) ≤
      (k : EInt) :=
    schemeDeltaDimension_isNowhereDenseCoherentSubobject_le C f F K hK hdim
  have hKdim : schemeDeltaDimension C ((reducedSupport (K : X.Modules)).subschemeι ≫ f) ≤
      ((k + 1 : ℤ) : EInt) :=
    hKdimk.trans (WithBotTop.coe_le_coe.mpr (by omega))
  have hKTdimk : schemeDeltaDimension C
      ((reducedSupport (tensorModules (K : X.Modules) L)).subschemeι ≫ f) ≤ (k : EInt) :=
    schemeDeltaDimension_reducedSupport_tensorModules_le C f (K : X.Modules) L hKdimk
  have hsuppQ : SheafOfModules.supp (cokernel K.arrow) = SheafOfModules.supp F :=
    supp_cokernel_eq F K hK
  have hQdim : schemeDeltaDimension C ((reducedSupport (cokernel K.arrow)).subschemeι ≫ f) ≤
      ((k + 1 : ℤ) : EInt) :=
    schemeDeltaDimension_reducedSupport_le C f (cokernel K.arrow) fun x hx =>
      relativeDimension_le_of_mem_supp C f F hdim (hsuppQ ▸ hx)
  -- the short exact sequence `0 ⟶ 𝒦 ⟶ ℱ ⟶ ℱ' ⟶ 0` and its twist
  have hSES : (ShortComplex.mk K.arrow (cokernel.π K.arrow)
      (cokernel.condition K.arrow)).ShortExact :=
    ShortComplex.shortExact_mk_cokernel_π K.arrow
  have hadd : coherentDimensionKZeroMk C f (k - 1) (k + 1) (layerMk C f (k + 1) F hdim) =
      coherentDimensionKZeroMk C f (k - 1) (k + 1)
          (layerMk C f (k + 1) (K : X.Modules) hKdim) +
        coherentDimensionKZeroMk C f (k - 1) (k + 1)
          (layerMk C f (k + 1) (cokernel K.arrow) hQdim) :=
    coherentDimensionKZeroMk_add_of_modules C f (k - 1) (k + 1)
      (A := layerMk C f (k + 1) (K : X.Modules) hKdim) (B := layerMk C f (k + 1) F hdim)
      (D := layerMk C f (k + 1) (cokernel K.arrow) hQdim)
      K.arrow (cokernel.π K.arrow) (cokernel.condition K.arrow) hSES
  have haddT := coherentDimensionKZeroMk_layerMkTensor_add_of_modules C f (k - 1) (k + 1)
    K.arrow (cokernel.π K.arrow) (cokernel.condition K.arrow) hSES L hL hKdim hdim hQdim
  -- the three memberships
  obtain ⟨hmemK, eK⟩ := exists_mem_chowHom_eq_mk_layerCycleOfLE C f k
    (layerMk C f (k + 1) (K : X.Modules) hKdim) hKdimk
  obtain ⟨hmemKT, eKT⟩ := exists_mem_chowHom_eq_mk_layerCycleOfLE C f k
    (layerMkTensor C f (k + 1) (K : X.Modules) L hL hKdim) hKTdimk
  have hmemQ := coherentDimensionKZeroMk_layerMkTensor_sub_mem_of_hasNoEmbeddedAssociatedPoints
    C f (cokernel K.arrow) hQemb L hL hQdim
  -- split `x` along the sequence
  have hkey : (x : coherentDimensionKZero C f (k - 1) (k + 1)) =
      (coherentDimensionKZeroMk C f (k - 1) (k + 1)
            (layerMkTensor C f (k + 1) (K : X.Modules) L hL hKdim) -
          coherentDimensionKZeroMk C f (k - 1) (k + 1)
            (layerMk C f (k + 1) (K : X.Modules) hKdim)) +
        (coherentDimensionKZeroMk C f (k - 1) (k + 1)
              (layerMkTensor C f (k + 1) (cokernel K.arrow) L hL hQdim) -
            coherentDimensionKZeroMk C f (k - 1) (k + 1)
              (layerMk C f (k + 1) (cokernel K.arrow) hQdim)) := by
    rw [hx, hadd, haddT]
    abel
  have hxsplit : x = (⟨_, hmemKT⟩ - ⟨_, hmemK⟩ : coherentDimensionLayerImage C f k) +
      ⟨_, hmemQ⟩ := Subtype.ext (by simpa using hkey)
  rw [hxsplit, map_add, map_sub, eKT, eK,
    coherentDimensionLayerImageChowHom_eq_firstChernClassCap_of_hasNoEmbedded C f
      (cokernel K.arrow) hQemb L hQdim _ rfl]
  -- the subsheaf contributes nothing on either side
  have hKcyc : layerCycleOfLE C f k (layerMkTensor C f (k + 1) (K : X.Modules) L hL hKdim)
        hKTdimk =
      layerCycleOfLE C f k (layerMk C f (k + 1) (K : X.Modules) hKdim) hKdimk :=
    cycleAssociatedToCoherentSheaf_tensorModules_of_isInvertible C f (K : X.Modules) L hL k
      hKTdimk hKdimk
  have hFcyc : cycleAssociatedToCoherentSheaf C f F (k + 1) hdim =
      cycleAssociatedToCoherentSheaf C f (cokernel K.arrow) (k + 1) hQdim := by
    have hsum := cycleAssociatedToCoherentSheaf_add C f
      (ShortComplex.mk K.arrow (cokernel.π K.arrow) (cokernel.condition K.arrow)) hSES (k + 1)
      hKdim hdim hQdim
    rw [hsum, cycleAssociatedToCoherentSheaf_eq_zero_of_lt C f (K : X.Modules)
      (l := k) (by omega) hKdim hKdimk, zero_add]
  rw [hKcyc, sub_self, zero_add, hFcyc]

/-! ### Stacks 02SX -/

/-- **[Stacks, Tag 02SX].** Let `(S, δ)` be a Chow situation, let `X` be locally of finite type
over `S`, let `ℒ` be an invertible `𝒪_X`-module and let `ℱ` be a coherent `𝒪_X`-module with
`dim_δ(Supp ℱ) ≤ k + 1`. Then the element

`[ℱ ⊗ ℒ] - [ℱ] ∈ K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))`

lies in the subgroup `Bₖ(X)` of [Stacks, Tag 02SC] and maps to `c₁(ℒ) ∩ [ℱ]_{k+1}` under the
homomorphism `Bₖ(X) ⟶ CH_k(X)` of that tag.

Both clauses are asserted: the membership is the existential witness, and the equation is the
statement about it. The membership is
`Stacks.Chow.coherentDimensionKZeroMk_layerMkTensor_sub_mem` and the equation is
`Stacks.Chow.coherentDimensionLayerImageChowHom_eq_firstChernClassCap`. -/
@[stacks 02SX]
theorem exists_mem_coherentDimensionLayerImage_layerMkTensor_sub
    (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsCoherent] (L : X.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    {k : ℤ}
    (hdim : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ f) ≤ ((k + 1 : ℤ) : EInt)) :
    ∃ hmem : coherentDimensionKZeroMk C f (k - 1) (k + 1)
            (layerMkTensor C f (k + 1) F L hL hdim) -
          coherentDimensionKZeroMk C f (k - 1) (k + 1) (layerMk C f (k + 1) F hdim) ∈
        coherentDimensionLayerImage C f k,
      coherentDimensionLayerImageChowHom C f k ⟨_, hmem⟩ =
        firstChernClassCapOfInvertible C f k L
          (cycleAssociatedToCoherentSheaf C f F (k + 1) hdim) :=
  ⟨coherentDimensionKZeroMk_layerMkTensor_sub_mem C f F L hL hdim,
    coherentDimensionLayerImageChowHom_eq_firstChernClassCap C f F L hdim _ rfl⟩

end Stacks.Chow

end
