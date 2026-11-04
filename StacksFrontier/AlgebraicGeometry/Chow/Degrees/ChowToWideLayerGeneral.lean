module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ChowToWideLayer
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerCycleEquiv
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.LocallyFiniteCoproductCycle
public import StacksFrontier.AlgebraicGeometry.HigherRank.Basic

/-!
# The homomorphism `CH_k(X) ⟶ K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))` for `X` locally of finite type

Let `(S, δ)` be as in Situation 02QL and let `X` be a scheme locally of finite type over `S`.
Tag 0FDS asserts that the map `Z_k(X) ⟶ K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` of Tag 02S9, followed by
the map to the wide layer `K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))`, kills the cycles rationally
equivalent to zero, and hence induces a homomorphism

`CH_k(X) ⟶ K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))`.

This is proved here for `X` merely locally of finite type over the base, with no
quasi-compactness. A cycle rationally equivalent to zero is `α = ∑_j (i_j)_* div(f_j)` for a
locally finite family of integral closed subschemes `i_j : W_j ⟶ X` of delta-dimension `k + 1`
(Tag 02RW). For each `j` the two short exact sequences of Tag 02P0 for the ideal of denominators
`I_j` of `f_j`,

`0 ⟶ I_j ⟶ 𝒪_{W_j} ⟶ 𝒪_{W_j}/I_j ⟶ 0`   and   `0 ⟶ I_j ⟶^{f_j} 𝒪_{W_j} ⟶ 𝒪_{W_j}/f_jI_j ⟶ 0`,

share their first two terms and satisfy `[𝒪_{W_j}/f_jI_j]_k − [𝒪_{W_j}/I_j]_k = div(f_j)`. Push
them forward to `X` and take the direct sum over `j`: the family of supports is locally finite, so
the direct sums are coherent, the two sequences stay short exact
(`Stacks.Chow.shortExact_sigmaShortComplex`), and the cycle of the direct sum is the sum of the
cycles (`Stacks.Chow.dimensionLayerCycle_sigmaDimLE_apply`). This yields two short exact sequences
in `Coh_{≤k+1}(X)` with the same first two terms and with third terms `A`, `B` of
`Coh_{≤k}(X)` such that `[B]_k − [A]_k = α`. By Tag 02S9 the class of `α` in the wide layer is
`[B] − [A]`, which vanishes because the two sequences share their first two terms.

## Main definitions

* `Stacks.Chow.chowToWideLayerHom` — **Stacks 0FDS**: the homomorphism
  `CH_k(X) ⟶ K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))`.

## Main results

* `Stacks.Chow.cycleDimensionLayerWideHom_dimensionLayerCycle` — the wide class of the cycle of a
  coherent module of support dimension at most `k` is the class of the module.
* `Stacks.Chow.cycleDimensionLayerWideHom_eq_zero_of_sigma` — the vanishing for a cycle presented
  by a locally finite family of pairs of short exact sequences.
* `Stacks.Chow.cycleDimensionLayerWideHom_eq_zero_of_isRationallyEquivalentToZero'` — the wide
  class of a cycle rationally equivalent to zero vanishes.

## Implementation notes

The cycle identity is used in the orientation `[𝒪/fI]_k − [𝒪/I]_k = div(f)` of
`Stacks.Chow.dimensionLayerCycle_denominatorQuotientUnit_sub_eq`; the chain printed in the proof
of Tag 0FDS has the opposite sign, which does not affect the vanishing.

## References

* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02S9](https://stacks.math.columbia.edu/tag/02S9)
* [Stacks Project, Tag 0FDS](https://stacks.math.columbia.edu/tag/0FDS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-! ### The wide class of the cycle of a module -/

/-- **Tag 02S9 read in the wide layer.** For `X` locally of finite type over the base, the class in
`K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))` of the cycle `[F]_k` of an object `F` of `Coh_{≤k}(X)` is the
class of `F`. -/
theorem cycleDimensionLayerWideHom_dimensionLayerCycle (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) (F : CoherentModulesDimLE C f k) :
    cycleDimensionLayerWideHom C f k (dimensionLayerCycle C f k F) =
      coherentDimensionKZeroMk C f (k - 1) (k + 1) ((dimensionLayerInclusion C f k).obj F) :=
  cycleDimensionLayerWideHom_dimensionLayerCycle_of_surjective C f k
    (cycleGroupAddEquivDimensionLayer C f k).surjective F

/-- **The wide class of a difference of two quotient cycles vanishes**, for `X` locally of finite
type over the base. This is `Stacks.Chow.cycleDimensionLayerWideHom_eq_zero_of_shortExact` with no
quasi-compactness of `X`. -/
theorem cycleDimensionLayerWideHom_eq_zero_of_shortExact' (C : ChowSituation.{u}) (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (k : ℤ)
    {S T : ShortComplex (CoherentModulesDimLE C p (k + 1))}
    (hS : S.ShortExact) (hT : T.ShortExact) (e₁ : S.X₁ ≅ T.X₁) (e₂ : S.X₂ ≅ T.X₂)
    {Q₁ Q₂ : CoherentModulesDimLE C p k}
    (hQ₁ : (dimensionLayerInclusion C p k).obj Q₁ = S.X₃)
    (hQ₂ : (dimensionLayerInclusion C p k).obj Q₂ = T.X₃)
    {α : CycleGroup C p k}
    (hα : dimensionLayerCycle C p k Q₂ - dimensionLayerCycle C p k Q₁ = α) :
    cycleDimensionLayerWideHom C p k α = 0 := by
  rw [← hα, map_sub, cycleDimensionLayerWideHom_dimensionLayerCycle,
    cycleDimensionLayerWideHom_dimensionLayerCycle, hQ₁, hQ₂,
    coherentDimensionKZeroMk_eq_of_shortExact C p (k - 1) (k + 1) hS hT e₁ e₂, sub_self]

/-! ### The vanishing along a locally finite family of pairs of sequences -/

/-- The first and third terms of a short exact sequence in `Coh_{≤k+1}(X)` are supported in any
set containing the support of its middle term. -/
private theorem supp_X₁_X₃_subset_of_shortExact (C : ChowSituation.{u}) (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (k : ℤ) {R : ShortComplex (CoherentModulesDimLE C sX (k + 1))}
    (hR : R.ShortExact) {Z : Set X} (h : SheafOfModules.supp R.X₂.obj.obj ⊆ Z) :
    SheafOfModules.supp R.X₁.obj.obj ⊆ Z ∧ SheafOfModules.supp R.X₃.obj.obj ⊆ Z := by
  have hR' := hR.map_of_exact (dimLEForget C sX (k + 1))
  have := hR'.mono_f
  have := hR'.epi_g
  exact ⟨(supp_subset_of_mono (R.map (dimLEForget C sX (k + 1))).f).trans h,
    (supp_subset_of_epi (R.map (dimLEForget C sX (k + 1))).g).trans h⟩

/-- **The wide class of a locally finite sum of differences of quotient cycles vanishes.** Let
`S j` and `T j` be short exact sequences of `Coh_{≤k+1}(X)` with isomorphic first terms and
isomorphic second terms, whose third terms are the images of objects `Q₁ j`, `Q₂ j` of
`Coh_{≤k}(X)`, and whose supports lie in a locally finite family of subsets `Z j` of `X`. Then a
`k`-cycle `β` with `β = ∑_j ([Q₂ j]_k − [Q₁ j]_k)` has vanishing class in
`K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))`.

The direct sums over `j` of the two families of sequences are short exact sequences of coherent
modules with isomorphic first and second terms, and the cycles of the direct sums of the third
terms are the locally finite sums of the cycles. -/
theorem cycleDimensionLayerWideHom_eq_zero_of_sigma (C : ChowSituation.{u}) (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (k : ℤ) {J : Type u}
    (S T : J → ShortComplex (CoherentModulesDimLE C sX (k + 1)))
    (hS : ∀ j, (S j).ShortExact) (hT : ∀ j, (T j).ShortExact)
    (e₁ : ∀ j, (S j).X₁ ≅ (T j).X₁) (e₂ : ∀ j, (S j).X₂ ≅ (T j).X₂)
    (Q₁ Q₂ : J → CoherentModulesDimLE C sX k)
    (hQ₁ : ∀ j, (dimensionLayerInclusion C sX k).obj (Q₁ j) = (S j).X₃)
    (hQ₂ : ∀ j, (dimensionLayerInclusion C sX k).obj (Q₂ j) = (T j).X₃)
    (Z : J → Set X) (hZ : LocallyFinite Z)
    (hSZ : ∀ j, SheafOfModules.supp (S j).X₂.obj.obj ⊆ Z j)
    (hTZ : ∀ j, SheafOfModules.supp (T j).X₂.obj.obj ⊆ Z j)
    (β : CycleGroup C sX k)
    (hβ : ∀ x, β.1 x = ∑ᶠ j, ((dimensionLayerCycle C sX k (Q₂ j)).1 x -
      (dimensionLayerCycle C sX k (Q₁ j)).1 x)) :
    cycleDimensionLayerWideHom C sX k β = 0 := by
  -- the sequences of underlying modules
  set G := dimLEForget C sX (k + 1) with hG
  set ES : J → ShortComplex X.Modules := fun j ↦ (S j).map G with hES
  set ET : J → ShortComplex X.Modules := fun j ↦ (T j).map G with hET
  have hES' : ∀ j, (ES j).ShortExact := fun j ↦ (hS j).map_of_exact G
  have hET' : ∀ j, (ET j).ShortExact := fun j ↦ (hT j).map_of_exact G
  -- the supports
  have hsS := fun j ↦ supp_X₁_X₃_subset_of_shortExact C sX k (hS j) (hSZ j)
  have hsT := fun j ↦ supp_X₁_X₃_subset_of_shortExact C sX k (hT j) (hTZ j)
  have hQ₁o : ∀ j, (Q₁ j).obj.obj = (S j).X₃.obj.obj := fun j ↦
    congrArg (fun M : CoherentModulesDimLE C sX (k + 1) ↦ M.obj.obj) (hQ₁ j)
  have hQ₂o : ∀ j, (Q₂ j).obj.obj = (T j).X₃.obj.obj := fun j ↦
    congrArg (fun M : CoherentModulesDimLE C sX (k + 1) ↦ M.obj.obj) (hQ₂ j)
  have hLS₁ : LocallyFinite fun j ↦ SheafOfModules.supp (S j).X₁.obj.obj :=
    hZ.subset fun j ↦ (hsS j).1
  have hLS₂ : LocallyFinite fun j ↦ SheafOfModules.supp (S j).X₂.obj.obj := hZ.subset hSZ
  have hLS₃ : LocallyFinite fun j ↦ SheafOfModules.supp (S j).X₃.obj.obj :=
    hZ.subset fun j ↦ (hsS j).2
  have hLT₁ : LocallyFinite fun j ↦ SheafOfModules.supp (T j).X₁.obj.obj :=
    hZ.subset fun j ↦ (hsT j).1
  have hLT₂ : LocallyFinite fun j ↦ SheafOfModules.supp (T j).X₂.obj.obj := hZ.subset hTZ
  have hLT₃ : LocallyFinite fun j ↦ SheafOfModules.supp (T j).X₃.obj.obj :=
    hZ.subset fun j ↦ (hsT j).2
  have hLQ₁ : LocallyFinite fun j ↦ SheafOfModules.supp (Q₁ j).obj.obj :=
    hZ.subset fun j ↦ by rw [hQ₁o j]; exact (hsS j).2
  have hLQ₂ : LocallyFinite fun j ↦ SheafOfModules.supp (Q₂ j).obj.obj :=
    hZ.subset fun j ↦ by rw [hQ₂o j]; exact (hsT j).2
  -- the direct sums, as objects of `Coh_{≤k+1}(X)` and `Coh_{≤k}(X)`
  set A₁ := sigmaDimLE C sX (k + 1) (fun j ↦ (S j).X₁) hLS₁
  set A₂ := sigmaDimLE C sX (k + 1) (fun j ↦ (S j).X₂) hLS₂
  set A₃ := sigmaDimLE C sX (k + 1) (fun j ↦ (S j).X₃) hLS₃
  set B₁ := sigmaDimLE C sX (k + 1) (fun j ↦ (T j).X₁) hLT₁
  set B₂ := sigmaDimLE C sX (k + 1) (fun j ↦ (T j).X₂) hLT₂
  set B₃ := sigmaDimLE C sX (k + 1) (fun j ↦ (T j).X₃) hLT₃
  set P₁ := sigmaDimLE C sX k Q₁ hLQ₁
  set P₂ := sigmaDimLE C sX k Q₂ hLQ₂
  have hS' := shortExact_shortComplexDimLE C sX (k + 1) A₁ A₂ A₃ _ _ _
    (shortExact_sigmaShortComplex ES hES')
  have hT' := shortExact_shortComplexDimLE C sX (k + 1) B₁ B₂ B₃ _ _ _
    (shortExact_sigmaShortComplex ET hET')
  have hP₁ : (dimensionLayerInclusion C sX k).obj P₁ = A₃ :=
    dimLE_ext C sX (k + 1) (congrArg (fun F : J → X.Modules ↦ ∐ F) (funext hQ₁o))
  have hP₂ : (dimensionLayerInclusion C sX k).obj P₂ = B₃ :=
    dimLE_ext C sX (k + 1) (congrArg (fun F : J → X.Modules ↦ ∐ F) (funext hQ₂o))
  refine cycleDimensionLayerWideHom_eq_zero_of_shortExact' C sX k hS' hT'
    (dimLEIsoOfModuleIso C sX (k + 1) A₁ B₁ (Sigma.mapIso fun j ↦ G.mapIso (e₁ j)))
    (dimLEIsoOfModuleIso C sX (k + 1) A₂ B₂ (Sigma.mapIso fun j ↦ G.mapIso (e₂ j)))
    hP₁ hP₂ ?_
  -- the cycle of the difference of the two direct sums is `β`
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
  show (dimensionLayerCycle C sX k P₂).1 x - (dimensionLayerCycle C sX k P₁).1 x = β.1 x
  rw [hβ x, dimensionLayerCycle_sigmaDimLE_apply, dimensionLayerCycle_sigmaDimLE_apply]
  have hfin : ∀ Q : J → CoherentModulesDimLE C sX k,
      (LocallyFinite fun j ↦ SheafOfModules.supp (Q j).obj.obj) →
        (Function.support fun j ↦ (dimensionLayerCycle C sX k (Q j)).1 x).Finite :=
    fun Q hQ ↦ (hQ.point_finite x).subset fun j hj ↦ by
      by_contra hx
      exact hj (dimensionLayerCycle_apply_of_notMem_supp C sX k (Q j) hx)
  refine (finsum_sub_distrib ?_ ?_).symm
  · exact hfin _ hLQ₂
  · exact hfin _ hLQ₁

/-! ### The two sequences of one integral closed subscheme, pushed forward -/

section Piece

variable (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (k : ℤ)
  (V : X.IdealSheafData) [hV : IsIntegral V.subscheme]
  (hDim : schemeDeltaDimension C (V.subschemeι ≫ sX) = ((k + 1 : ℤ) : EInt))
  (g : (rationalFunctions V.subscheme)ˣ)

/-- The rational function `g` on the integral closed subscheme `V`, as a unit of its function
field. -/
def pieceUnit : V.subscheme.functionFieldˣ :=
  Units.map (rationalFunctionsEquivFunctionField V.subscheme).1.toMonoidHom g

/-- The sequence `0 ⟶ I ⟶ 𝒪_V ⟶ 𝒪_V/I ⟶ 0` for the ideal of denominators `I` of `g`, pushed
forward to `X`. -/
def pieceIdealSeq : ShortComplex (CoherentModulesDimLE C sX (k + 1)) :=
  (denominatorShortComplexUnit C (V.subschemeι ≫ sX)
      (AlgebraicGeometry.meromorphicSectionOfFunctionField V.subscheme (pieceUnit V g))
      (AlgebraicGeometry.isRegularMeromorphicSection_meromorphicSectionOfFunctionField
        V.subscheme (pieceUnit V g)) hDim.le).map
    (finitePushforwardDimLE C (V.subschemeι ≫ sX) sX V.subschemeι rfl (k + 1))

/-- The sequence `0 ⟶ I ⟶^{g} 𝒪_V ⟶ 𝒪_V/gI ⟶ 0` for the ideal of denominators `I` of `g`,
pushed forward to `X`. -/
def pieceSectionSeq : ShortComplex (CoherentModulesDimLE C sX (k + 1)) :=
  (denominatorSectionShortComplexUnit C (V.subschemeι ≫ sX)
      (AlgebraicGeometry.meromorphicSectionOfFunctionField V.subscheme (pieceUnit V g))
      (AlgebraicGeometry.isRegularMeromorphicSection_meromorphicSectionOfFunctionField
        V.subscheme (pieceUnit V g)) hDim.le).map
    (finitePushforwardDimLE C (V.subschemeι ≫ sX) sX V.subschemeι rfl (k + 1))

/-- `𝒪_V/I`, pushed forward to `X`, as an object of `Coh_{≤k}(X)`. -/
def pieceQuot₁ : CoherentModulesDimLE C sX k :=
  (finitePushforwardDimLE C (V.subschemeι ≫ sX) sX V.subschemeι rfl k).obj
    (denominatorQuotientUnitDimLE C (V.subschemeι ≫ sX)
      (AlgebraicGeometry.meromorphicSectionOfFunctionField V.subscheme (pieceUnit V g))
      (AlgebraicGeometry.isRegularMeromorphicSection_meromorphicSectionOfFunctionField
        V.subscheme (pieceUnit V g)) hDim.le)

/-- `𝒪_V/gI`, pushed forward to `X`, as an object of `Coh_{≤k}(X)`. -/
def pieceQuot₂ : CoherentModulesDimLE C sX k :=
  (finitePushforwardDimLE C (V.subschemeι ≫ sX) sX V.subschemeι rfl k).obj
    (denominatorSectionQuotientUnitDimLE C (V.subschemeι ≫ sX)
      (AlgebraicGeometry.meromorphicSectionOfFunctionField V.subscheme (pieceUnit V g))
      (AlgebraicGeometry.isRegularMeromorphicSection_meromorphicSectionOfFunctionField
        V.subscheme (pieceUnit V g)) hDim.le)

/-- The pushed-forward sequence `0 ⟶ I ⟶ 𝒪_V ⟶ 𝒪_V/I ⟶ 0` is short exact. -/
theorem shortExact_pieceIdealSeq : (pieceIdealSeq C sX k V hDim g).ShortExact :=
  shortExact_map_finitePushforwardDimLE C _ sX _ rfl (k + 1)
    (shortExact_denominatorShortComplexUnit C _ _ _ hDim.le)

/-- The pushed-forward sequence `0 ⟶ I ⟶^{g} 𝒪_V ⟶ 𝒪_V/gI ⟶ 0` is short exact. -/
theorem shortExact_pieceSectionSeq : (pieceSectionSeq C sX k V hDim g).ShortExact :=
  shortExact_map_finitePushforwardDimLE C _ sX _ rfl (k + 1)
    (shortExact_denominatorSectionShortComplexUnit C _ _ _ hDim.le)

/-- The two pushed-forward sequences have the same first object, the pushforward of `I`. -/
theorem pieceIdealSeq_X₁ :
    (pieceIdealSeq C sX k V hDim g).X₁ = (pieceSectionSeq C sX k V hDim g).X₁ :=
  rfl

/-- The two pushed-forward sequences have the same middle object, the pushforward of `𝒪_V`. -/
theorem pieceIdealSeq_X₂ :
    (pieceIdealSeq C sX k V hDim g).X₂ = (pieceSectionSeq C sX k V hDim g).X₂ :=
  rfl

/-- The object `pieceQuot₁`, viewed in `Coh_{≤k+1}(X)`, is the third object of
`pieceIdealSeq`. -/
theorem pieceQuot₁_incl :
    (dimensionLayerInclusion C sX k).obj (pieceQuot₁ C sX k V hDim g) =
      (pieceIdealSeq C sX k V hDim g).X₃ :=
  dimLE_ext C sX (k + 1) rfl

/-- The object `pieceQuot₂`, viewed in `Coh_{≤k+1}(X)`, is the third object of
`pieceSectionSeq`. -/
theorem pieceQuot₂_incl :
    (dimensionLayerInclusion C sX k).obj (pieceQuot₂ C sX k V hDim g) =
      (pieceSectionSeq C sX k V hDim g).X₃ :=
  dimLE_ext C sX (k + 1) rfl

omit hV in
/-- The support of a direct image along the inclusion of a closed subscheme lies in the
subscheme. -/
theorem supp_pushforward_subschemeι_subset (H : V.subscheme.Modules) :
    SheafOfModules.supp ((Scheme.Modules.pushforward V.subschemeι).obj H) ⊆
      (V.support : Set X) := by
  intro x hx
  rw [← Scheme.IdealSheafData.range_subschemeι]
  exact Stacks.AlgebraicGeometry.Tag01YMHigherRank.supp_pushforward_subset_range
    V.subschemeι H x ((SheafOfModules.mem_supp_iff_nontrivial_stalk _ x).mp hx)

/-- The support of the middle object of `pieceIdealSeq` lies in `V`. -/
theorem supp_pieceIdealSeq_X₂ :
    SheafOfModules.supp (pieceIdealSeq C sX k V hDim g).X₂.obj.obj ⊆ (V.support : Set X) :=
  supp_pushforward_subschemeι_subset V _

/-- The support of the middle object of `pieceSectionSeq` lies in `V`. -/
theorem supp_pieceSectionSeq_X₂ :
    SheafOfModules.supp (pieceSectionSeq C sX k V hDim g).X₂.obj.obj ⊆ (V.support : Set X) :=
  supp_pushforward_subschemeι_subset V _

/-- **Stacks 02R6 (2) on a dimension layer.** The cycle of the direct image along a finite
morphism of an object of `Coh_{≤k}` is the proper pushforward of its cycle. -/
theorem dimensionLayerCycle_finitePushforwardDimLE {W : Scheme.{u}} (sW : W ⟶ C.S)
    [LocallyOfFiniteType sW] (π : W ⟶ X) [IsFinite π] (hπ : π ≫ sX = sW)
    (F : CoherentModulesDimLE C sW k) :
    dimensionLayerCycle C sX k ((finitePushforwardDimLE C sW sX π hπ k).obj F) =
      properPushforwardHom C sW sX π hπ k (dimensionLayerCycle C sW k F) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hc : _root_.SheafOfModules.IsCoherent F.obj.obj :=
    AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent F.obj.property
  have hp : _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward π).obj F.obj.obj) :=
    Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite π
      F.obj.obj
  rw [properPushforwardHom_apply]
  exact (properPushforward_cycleAssociatedToCoherentSheaf C sW sX π hπ F.obj.obj k
    F.property).symm

/-- **The cycle identity of the proof of Stacks 0FDS, pushed forward.** The difference of the
cycles of `𝒪_V/gI` and of `𝒪_V/I`, pushed forward to `X`, is `(V ⟶ X)_* div(g)`. -/
theorem pieceQuot_sub_apply (x : X) :
    (dimensionLayerCycle C sX k (pieceQuot₂ C sX k V hDim g)).1 x -
        (dimensionLayerCycle C sX k (pieceQuot₁ C sX k V hDim g)).1 x =
      principalDivisorPushforward C sX V hV g x := by
  have : IsLocallyNoetherian V.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (V.subschemeι ≫ sX)
  have hc : ∀ y : V.subscheme,
      ((subschemePrincipalDivisorCycle C sX k V hV hDim g : CycleGroup _ _ k) :
        AlgebraicCycle V.subscheme ℤ) y =
        V.subscheme.ord (pieceUnit V g : V.subscheme.functionField) y := fun y ↦
    principalCycle_apply V.subscheme _ y
  have key := dimensionLayerCycle_denominatorQuotientUnit_sub_eq C (V.subschemeι ≫ sX) hDim
    (pieceUnit V g) hc
  rw [← properPushforward_subschemePrincipalDivisorCycle C sX k V hV hDim g, ← key,
    ← properPushforwardHom_apply, map_sub]
  rw [pieceQuot₂, pieceQuot₁, dimensionLayerCycle_finitePushforwardDimLE,
    dimensionLayerCycle_finitePushforwardDimLE]
  rfl

end Piece

/-! ### Tag 0FDS -/

/-- **Stacks 0FDS, the vanishing.** On a scheme `X` locally of finite type over the base, the class
in `K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))` of a `k`-cycle rationally equivalent to zero vanishes. -/
theorem cycleDimensionLayerWideHom_eq_zero_of_isRationallyEquivalentToZero'
    (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (k : ℤ)
    {α : CycleGroup C sX k} (hα : IsRationallyEquivalentToZero C sX k α) :
    cycleDimensionLayerWideHom C sX k α = 0 := by
  obtain ⟨J, W, hW, hDim, hLocal, g, hg⟩ := hα
  refine cycleDimensionLayerWideHom_eq_zero_of_sigma C sX k
    (fun j ↦ pieceIdealSeq C sX k (W j) (hV := hW j) (hDim j) (g j))
    (fun j ↦ pieceSectionSeq C sX k (W j) (hV := hW j) (hDim j) (g j))
    (fun j ↦ shortExact_pieceIdealSeq C sX k (W j) (hV := hW j) (hDim j) (g j))
    (fun j ↦ shortExact_pieceSectionSeq C sX k (W j) (hV := hW j) (hDim j) (g j))
    (fun j ↦ eqToIso (pieceIdealSeq_X₁ C sX k (W j) (hV := hW j) (hDim j) (g j)))
    (fun j ↦ eqToIso (pieceIdealSeq_X₂ C sX k (W j) (hV := hW j) (hDim j) (g j)))
    (fun j ↦ pieceQuot₁ C sX k (W j) (hV := hW j) (hDim j) (g j))
    (fun j ↦ pieceQuot₂ C sX k (W j) (hV := hW j) (hDim j) (g j))
    (fun j ↦ pieceQuot₁_incl C sX k (W j) (hV := hW j) (hDim j) (g j))
    (fun j ↦ pieceQuot₂_incl C sX k (W j) (hV := hW j) (hDim j) (g j))
    (fun j ↦ ((W j).support : Set X)) hLocal
    (fun j ↦ supp_pieceIdealSeq_X₂ C sX k (W j) (hV := hW j) (hDim j) (g j))
    (fun j ↦ supp_pieceSectionSeq_X₂ C sX k (W j) (hV := hW j) (hDim j) (g j)) α fun x ↦ ?_
  rw [hg x]
  exact finsum_congr fun j ↦
    (pieceQuot_sub_apply C sX k (W j) (hV := hW j) (hDim j) (g j) x).symm

/-- **Stacks 0FDS, the vanishing on the subgroup of rational equivalences.** -/
theorem cycleDimensionLayerWideHom_eq_zero_of_mem_rationalEquivalences'
    (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (k : ℤ)
    (α : CycleGroup C sX k) (hα : α ∈ rationalEquivalences C sX k) :
    cycleDimensionLayerWideHom C sX k α = 0 :=
  cycleDimensionLayerWideHom_eq_zero_of_isRationallyEquivalentToZero' C sX k hα

/-- **Stacks 0FDS.** For a scheme `X` locally of finite type over the base of a Chow situation
there is a canonical homomorphism `CH_k(X) ⟶ K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))` induced by the map
`Z_k(X) ⟶ K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` of Tag 02S9: it sends the class of a `k`-cycle `c` to
the image of the class of `c` under the map widening the layer, see
`Stacks.Chow.chowToWideLayerHom_mk`. -/
@[stacks 0FDS]
def chowToWideLayerHom (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (k : ℤ) : chowGroup C sX k →+ coherentDimensionKZero C sX (k - 1) (k + 1) :=
  chowToDimensionLayerHom C sX k
    (cycleDimensionLayerWideHom_eq_zero_of_mem_rationalEquivalences' C sX k)

/-- The homomorphism of Tag 0FDS on the class of a cycle `c`: the class of `c` in
`K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` (Tag 02S9), read in `K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))`. -/
theorem chowToWideLayerHom_mk (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (k : ℤ) (c : CycleGroup C sX k) :
    chowToWideLayerHom C sX k (QuotientAddGroup.mk' (rationalEquivalences C sX k) c) =
      coherentDimensionLayerHom C sX k
        (KZero.ofGrothendieckGroup (cycleDimensionLayerHom C sX k c)) :=
  chowToDimensionLayerHom_mk C sX k _ c

end Stacks.Chow

end
