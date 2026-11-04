module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.PreparationWhitney
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.PreparationSum
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.ModificationComparison
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.CommonModification
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.TotalLocalizedChern
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.WhitneyHomotopy

/-!
# The direct-sum case of Stacks 0FBD and 0FBE

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `i : Z ⟶ X` be a closed
immersion of schemes locally of finite type over `S`, and let `(X, Z, E₁)`, `(X, Z, E₃)` be as in
Situation 0GUJ, with `E₁|_{X ∖ Z}`, `E₃|_{X ∖ Z}` finite locally free of ranks `< p₁`, `< p₃` in
degree `0`. The last paragraph of the proof of Stacks 0FBD treats `E₂ = E₁ ⊕ E₃`: for `j = 1, 3`
let `b_j : W_j ⟶ 𝐏¹_X`, `Q_j` and `T'_j ⊆ T_j ⊆ W_{j,∞}` be the graph construction of `E_j` and
the closed subschemes of the proof of Stacks 0FB2, so that `c_n(Z ⟶ X, E_j) = c'_n(Q_j)`. On
`W = W₁ ×_{𝐏¹_X} W₃`, with projections `g_j` and `b = b_j ∘ g_j`, the closed subscheme
`T' = g₁⁻¹(T'₁) ∩ g₃⁻¹(T'₃)` of `W_∞` still contains every point lying over `X ∖ Z`. By Stacks
0FAU the classes of `E_j` may be computed from `W`, `b`, `Lg_j^*Q_j` and `T'`; by Stacks 0FE8 those
of `E₂` from `W`, `b`, `Lg₁^*Q₁ ⊕ Lg₃^*Q₃` and `T'`; and Stacks 0FAY gives

  `c⁽ᵖ¹⁺ᵖ³⁾(Z ⟶ X, E₂) = c⁽ᵖ¹⁾(Z ⟶ X, E₁) c⁽ᵖ³⁾(Z ⟶ X, E₃)`   in `A⁽ᵖ¹⁺ᵖ³⁾(Z ⟶ X)`,

while Stacks 0FAZ gives `P_p(Z ⟶ X, E₂) = P_p(Z ⟶ X, E₁) + P_p(Z ⟶ X, E₃)` when `E₁`, `E₃` vanish
off `Z` (the corresponding case of Stacks 0FBE).

This file carries this out for every common modification `g_j : W ⟶ W_j` (the fibre product is one,
`Stacks.Chow.isIso_pullbackSnd_pullbackFst_comp_projectiveLineAffineChart`), with the identity of
Stacks 0FE8 for `E₂` on `W` as a hypothesis, and for the total classes with any output cutoff
`r ≥ p₁ + p₃ - 1` of the product of Stacks 0FA0.

## Main definitions

* `Stacks.Chow.LocalizedChernData.situationWithObject`,
  `Stacks.Chow.LocalizedChernData.situationWithZeroObject` — the instance of Situation 0GUJ for
  another object with the closed immersion of given data.
* `Stacks.Chow.LocalizedChernData.withZeroObject` — the data of a localized Chern class for another
  object vanishing off `Z`.

## Main results

* `Stacks.Chow.LocalizedChernData.totalLocalizedChern_eq_mul_of_modification` — the direct-sum case
  of Stacks 0FBD, given Stacks 0FE8 on a common modification.
* `Stacks.Chow.LocalizedChernData.totalLocalizedChern_eq_cutoffMul_of_modification` — the same for
  the product of Stacks 0FA0 with output cutoff `r`, `p₁ + p₃ ≤ r + 1`; for `p₁ = p₃ = r = 1` this
  is the product of `A⁽¹⁾(Z ⟶ X)` (Stacks 0FES).
* `Stacks.Chow.LocalizedChernData.localizedPowerSum_eq_add_of_modification` — the direct-sum case
  of Stacks 0FBE, given Stacks 0FE8 on a common modification.
* `Stacks.Chow.modificationTotalChernClass_biprod_cutoffMul` — Stacks 0FAY for the product with
  output cutoff `r`.
* `Stacks.Chow.LocalizedSituation.localizedChern_eq_modificationChernClass`,
  `Stacks.Chow.LocalizedSituation.localizedPowerSum_eq_modificationPowerSum`,
  `Stacks.Chow.LocalizedSituation.totalLocalizedChern_eq_modificationTotalChernClass` — the
  classes of Stacks 0FB2 computed on any further modification of the graph construction, by
  Stacks 0FAU.
* `Stacks.Chow.exists_closedImmersion_inter_preimage` — the closed subscheme
  `g₁⁻¹(T₁) ∩ g₃⁻¹(T₃)` of the fibre at infinity.
* `Stacks.Chow.modificationSectionAtZero_comp_of_comp_eq` — a morphism of modifications preserves
  the sections at zero.
* `Stacks.Chow.LocalizedChernData.exists_isFiniteLocallyFreeOfRankLT_restrict_of_iso_biprod`,
  `Stacks.Chow.LocalizedChernData.isZero_restrict_of_iso_biprod` — the statements make sense:
  `(E₁ ⊕ E₃)|_{X ∖ Z}` is finite locally free of rank `< p₁ + p₃ - 1`, resp. zero.
* `Stacks.Chow.LocalizedChernData.finiteness_of_iso_biprod` — condition (3) of Situation 0GUJ for
  `E₁ ⊕ E₃` under alternatives (a), (b), or (c) for both summands.
* `Stacks.Chow.nonempty_derivedPullback_affineChart_derivedPullback_graphObject`,
  `Stacks.Chow.nonempty_derivedPullback_biprod_iso`,
  `Stacks.Chow.exists_isLocallyBoundedFiniteLocallyFree_biprod`,
  `Stacks.Chow.exists_isLocallyBoundedFiniteLocallyFree_biprod_derivedPullback` — the hypotheses of
  Stacks 0FE8 for `Lg₁^*Q₁ ⊕ Lg₃^*Q₃` and `E₁ ⊕ E₃`: the restriction over `𝐀¹_X` is the pullback
  of `E₁ ⊕ E₃`, and representability by locally bounded complexes of finite locally free modules
  passes to pullbacks and direct sums.

## Implementation notes

The identity of Stacks 0FE8 enters as the hypothesis `h0FE8` of the main results: for every closed
`T ⊆ W_∞` containing the points over `X ∖ Z` on which `Q = Lg₁^*Q₁ ⊕ Lg₃^*Q₃` is finite locally
free of rank `< n` in degree `0` (resp. zero), the class `c_n(Z ⟶ X, E₂)` (resp. `P_p`) of
Remark 0GUK is the class `c'_n(Q)` (resp. `P'_p(Q)`) of Stacks 0F9K built from `W`, `b`, `Q`, `T`.

The classes are those of Remark 0GUK (`Stacks.Chow.LocalizedChernData.localizedChern`), which in
Situation 0GUJ are those of Stacks 0FB2
(`Stacks.Chow.LocalizedSituation.localizedChern_toLocalizedChernData`). The object `E₂` is any
object with an isomorphism `E₂ ≅ E₁ ⊕ E₃`; its Chern classes are defined because those of the
summands are (`Stacks.Chow.hasDefinedChernClasses_biprod`).

The total classes are compared with the classes of Stacks 0FAY through their components: below the
cutoff both are the Chern classes of `E_j ≅ (Lg_j^*Q_j)|_{X × {0}}`, and from the cutoff on both
are the classes of Stacks 0F9K. The output cutoff `r` of the product may be any `r` with
`p₁ + p₃ ≤ r + 1`, because `(E₁ ⊕ E₃)|_{X ∖ Z}` has rank `≤ (p₁ - 1) + (p₃ - 1)`; the proof of
Stacks 0FAY applies verbatim, every summand of a component of degree `n ≥ r` having a factor in
degree at least its cutoff.

## References

* [Stacks Project, Tag 0FBD](https://stacks.math.columbia.edu/tag/0FBD)
* [Stacks Project, Tag 0FBE](https://stacks.math.columbia.edu/tag/0FBE)
* [Stacks Project, Tag 0FB2](https://stacks.math.columbia.edu/tag/0FB2)
* [Stacks Project, Tag 0FAU](https://stacks.math.columbia.edu/tag/0FAU)
* [Stacks Project, Tag 0FE8](https://stacks.math.columbia.edu/tag/0FE8)
* [Stacks Project, Tag 0FAY](https://stacks.math.columbia.edu/tag/0FAY)
* [Stacks Project, Tag 0FAZ](https://stacks.math.columbia.edu/tag/0FAZ)
* [Stacks Project, Tag 0FA0](https://stacks.math.columbia.edu/tag/0FA0)
* [Stacks Project, Tag 0GUK](https://stacks.math.columbia.edu/tag/0GUK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Direct sums of finite locally free modules of bounded rank -/

section Rank

/-- **Direct sums, for any bound `r` with `p + q ≤ r + 1`.** If `E|_W` and `F|_W` are isomorphic
to finite locally free modules of ranks `< p` and `< q` placed in degree `0`, then `(E ⊕ F)|_W` is
isomorphic to one of rank `< r`: the ranks add, so they are `≤ p + q - 2`
(`Stacks.Chow.exists_isFiniteLocallyFreeOfRankLT_iso_obj₂` for the split triangle). The case
`r = p + q` is `Stacks.Chow.exists_isFiniteLocallyFreeOfRankLT_derivedPullback_biprod`. -/
theorem exists_isFiniteLocallyFreeOfRankLT_derivedPullback_biprod_of_add_le {W Y : Scheme.{u}}
    (z : W ⟶ Y) {E F : DerivedCategory Y.Modules} {p q r : ℕ} (hr : p + q ≤ r + 1)
    (hE : ∃ M : W.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((derivedPullback z.toLRSHom.toShHom).obj E ≅
        (DerivedCategory.singleFunctor _ 0).obj M))
    (hF : ∃ N : W.Modules, IsFiniteLocallyFreeOfRankLT N q ∧
      Nonempty ((derivedPullback z.toLRSHom.toShHom).obj F ≅
        (DerivedCategory.singleFunctor _ 0).obj N)) :
    ∃ M : W.Modules, IsFiniteLocallyFreeOfRankLT M r ∧
      Nonempty ((derivedPullback z.toLRSHom.toShHom).obj (E ⊞ F : DerivedCategory Y.Modules) ≅
        (DerivedCategory.singleFunctor _ 0).obj M) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := exists_isFiniteLocallyFreeOfRankLT_iso_obj₂ _
    (binaryBiproductTriangle_distinguished ((derivedPullback z.toLRSHom.toShHom).obj E)
      ((derivedPullback z.toLRSHom.toShHom).obj F)) hE hF
  exact ⟨M, hM.mono (by omega), ⟨derivedPullbackBiprodIso z E F ≪≫ e⟩⟩

end Rank

/-! ### Morphisms of modifications -/

section MorphismOfModifications

variable {X S W W' : Scheme.{u}} (f : X ⟶ S) {b : W ⟶ projectiveLineProduct f}
  {b' : W' ⟶ projectiveLineProduct f} (g : W' ⟶ W) (hb : g ≫ b = b')

include hb in
/-- **A morphism of modifications preserves the sections at zero**: if `b' = b ∘ g` and `b`, `b'`
are isomorphisms over `𝐀¹_X`, then `g ∘ i'_0 = i_0`, both being the unique lift of the zero
section of `𝐏¹_X` through `b`. -/
theorem modificationSectionAtZero_comp_of_comp_eq
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))
    (hA' : IsIso (pullback.snd b' (projectiveLineAffineChart f))) :
    modificationSectionAtZero f b' (isIso_modificationFibreAtZeroProjection f b' hA') ≫ g =
      modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA) := by
  have := isIso_modificationFibreAtZeroProjection f b hA
  have hc : (modificationSectionAtZero f b' (isIso_modificationFibreAtZeroProjection f b' hA') ≫
      g) ≫ b = 𝟙 X ≫ zeroSection f := by
    rw [Category.assoc, hb, modificationSectionAtZero_comp f b' hA', Category.id_comp]
  have hl : pullback.lift _ _ hc = inv (pullback.snd b (zeroSection f)) :=
    IsIso.eq_inv_of_inv_hom_id (pullback.lift_snd _ _ _)
  rw [← pullback.lift_fst _ _ hc, hl]
  rfl

end MorphismOfModifications

/-! ### The closed subscheme `T' = g₁⁻¹(T₁) ∩ g₃⁻¹(T₃)` of the fibre at infinity -/

section Intersection

variable {X S W₁ W₃ W Z T₁ T₃ : Scheme.{u}} (f : X ⟶ S) {b₁ : W₁ ⟶ projectiveLineProduct f}
  {b₃ : W₃ ⟶ projectiveLineProduct f} {b : W ⟶ projectiveLineProduct f} (g₁ : W ⟶ W₁)
  (g₃ : W ⟶ W₃) (hb₁ : g₁ ≫ b₁ = b) (hb₃ : g₃ ≫ b₃ = b) (z : Z ⟶ X)
  (t₁ : T₁ ⟶ modificationFibreAtInfinity f b₁) [IsClosedImmersion t₁]
  (t₃ : T₃ ⟶ modificationFibreAtInfinity f b₃) [IsClosedImmersion t₃]

include hb₁ hb₃ in
/-- **The intersection of the inverse images of two closed subschemes of the fibres at infinity.**
Let `g₁ : W ⟶ W₁` and `g₃ : W ⟶ W₃` be morphisms of modifications of `𝐏¹_X`, and let
`T₁ ⊆ W_{1,∞}`, `T₃ ⊆ W_{3,∞}` be closed and contain every point lying over `X ∖ Z`. Then there is
a closed subscheme `T' ⊆ W_∞`, the intersection `g₁⁻¹(T₁) ∩ g₃⁻¹(T₃)`, which contains every point
of `W_∞` lying over `X ∖ Z` and maps to `T₁` and to `T₃` compatibly with `g₁` and `g₃`. -/
theorem exists_closedImmersion_inter_preimage
    (hT₁ : ∀ w, modificationProjectionAtInfinity f b₁ w ∉ Set.range z → w ∈ Set.range t₁)
    (hT₃ : ∀ w, modificationProjectionAtInfinity f b₃ w ∉ Set.range z → w ∈ Set.range t₃) :
    ∃ (T : Scheme.{u}) (t : T ⟶ modificationFibreAtInfinity f b) (_ : IsClosedImmersion t)
      (a₁ : T ⟶ T₁) (a₃ : T ⟶ T₃),
      (∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t) ∧
        a₁ ≫ t₁ ≫ modificationInclusionAtInfinity f b₁ =
          (t ≫ modificationInclusionAtInfinity f b) ≫ g₁ ∧
        a₃ ≫ t₃ ≫ modificationInclusionAtInfinity f b₃ =
          (t ≫ modificationInclusionAtInfinity f b) ≫ g₃ := by
  let τ₁ := pullback.snd (t₁ ≫ modificationInclusionAtInfinity f b₁)
    (modificationInclusionAtInfinity f b ≫ g₁)
  let τ₃ := pullback.snd (t₃ ≫ modificationInclusionAtInfinity f b₃)
    (modificationInclusionAtInfinity f b ≫ g₃)
  refine ⟨pullback τ₁ τ₃, pullback.fst τ₁ τ₃ ≫ τ₁, inferInstance,
    pullback.fst τ₁ τ₃ ≫ pullback.fst _ _, pullback.snd τ₁ τ₃ ≫ pullback.fst _ _,
    fun w hw => ?_, ?_, ?_⟩
  · obtain ⟨x₁, hx₁⟩ := mem_range_pullbackSnd_of_notMem_range f g₁ hb₁ z t₁ hT₁ w hw
    obtain ⟨x₃, hx₃⟩ := mem_range_pullbackSnd_of_notMem_range f g₃ hb₃ z t₃ hT₃ w hw
    obtain ⟨y, hy₁, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := τ₁) (g := τ₃) x₁ x₃
      (hx₁.trans hx₃.symm)
    exact ⟨y, by rw [Scheme.Hom.comp_apply, hy₁, hx₁]⟩
  · rw [Category.assoc, pullback.condition]
    rfl
  · simp only [Category.assoc]
    rw [pullback.condition_assoc (f := τ₁), pullback.condition]

end Intersection

/-! ### The classes of Stacks 0FB2 on a further modification -/

namespace LocalizedSituation

variable (S : LocalizedSituation.{u}) {W T : Scheme.{u}}
  (g : W ⟶ graphBlowup S.a S.E S.perfect) [IsProper g] {b : W ⟶ projectiveLineProduct S.a}
  [IsProper b] (hb : g ≫ graphBlowupToBase S.a S.E S.perfect = b)
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart S.a)))
  (t : T ⟶ modificationFibreAtInfinity S.a b) [IsClosedImmersion t]
  (hT : ∀ w, modificationProjectionAtInfinity S.a b w ∉ Set.range S.i → w ∈ Set.range t)

include hb in
/-- **`c_p(Z ⟶ X, E)` on a further modification** (Stacks 0FAU). Let `b : W ⟶ 𝐏¹_X`, `Q` be the
graph construction for `E`, and let `g : W' ⟶ W` be proper with `b' = b ∘ g` an isomorphism over
`𝐀¹_X`. For every closed `T' ⊆ W'_∞` containing the points over `X ∖ Z` on which `Lg^*Q` is
finite locally free of rank `< p` in degree `0`, the class `c'_p(Lg^*Q)` of Stacks 0F9K built
from `W'`, `b'` and `T'` is the class `c_p(Z ⟶ X, E)` of Stacks 0FB2. -/
theorem localizedChern_eq_modificationChernClass
    (hrank : ∃ M : T.Modules, IsFiniteLocallyFreeOfRankLT M S.p ∧
      Nonempty ((derivedPullback (t ≫ modificationInclusionAtInfinity S.a b).toLRSHom.toShHom).obj
        ((derivedPullback g.toLRSHom.toShHom).obj (graphObject S.a S.E S.perfect)) ≅
          (DerivedCategory.singleFunctor _ 0).obj M))
    (h : S.IsFiniteLocallyFreeOfRankLTOnComplement) :
    S.localizedChern h = modificationChernClass S.base S.a b hA S.i t
      (S.hasDefinedChernClasses_graphObject.derivedPullback g) S.p hT hrank := by
  have := isProper_graphBlowupToBase S.a S.E S.perfect
  let _ := isClosedImmersion_graphSmallRankLocus_ι S.a S.E S.perfect S.graphSubschemeι
    S.isFiniteLocallyFree_graphObjectRestrictHomology S.p
  exact (modificationChernClass_eq_of_modification S.base S.a
    (graphBlowupToBase S.a S.E S.perfect) b
    (isIso_pullback_snd_graphBlowupToBase S.a S.E S.perfect) g hb hA S.i
    ((graphSmallRankLocus S.a S.E S.perfect S.graphSubschemeι
      S.isFiniteLocallyFree_graphObjectRestrictHomology S.p).ι ≫ S.graphSubschemeι) t
    S.hasDefinedChernClasses_graphObject S.p
    (mem_range_graphSmallRankLocus S.base S.a S.E S.perfect S.i S.graphSubschemeι
      S.isFiniteLocallyFree_graphObjectRestrictHomology S.p S.mem_range_graphSubschemeι
      (S.finiteLocallyFreeRank_graphSubscheme_lt h)) hT
    (exists_isFiniteLocallyFreeOfRankLT_derivedPullback_graphSmallRankLocus S.a S.E S.perfect
      S.graphSubschemeι S.isFiniteLocallyFree_graphObjectRestrictHomology S.p) hrank).symm

include hb in
/-- **`P_p(Z ⟶ X, E)` on a further modification** (Stacks 0FAU): as
`Stacks.Chow.LocalizedSituation.localizedChern_eq_modificationChernClass`, for the classes
`P'_p(Lg^*Q)` built from a closed `T' ⊆ W'_∞` on which `Lg^*Q` is zero. -/
theorem localizedPowerSum_eq_modificationPowerSum (p : ℕ)
    (hzero : IsZero ((derivedPullback
      (t ≫ modificationInclusionAtInfinity S.a b).toLRSHom.toShHom).obj
        ((derivedPullback g.toLRSHom.toShHom).obj (graphObject S.a S.E S.perfect))))
    (h : S.IsZeroOnComplement) :
    S.localizedPowerSum h p = modificationPowerSum S.base S.a b hA S.i t
      (S.hasDefinedChernClasses_graphObject.derivedPullback g) p hT hzero := by
  have := isProper_graphBlowupToBase S.a S.E S.perfect
  let _ := isClosedImmersion_graphZeroLocus_ι S.a S.E S.perfect S.graphSubschemeι
    S.isFiniteLocallyFree_graphObjectRestrictHomology
  exact (modificationPowerSum_eq_of_modification S.base S.a (graphBlowupToBase S.a S.E S.perfect) b
    (isIso_pullback_snd_graphBlowupToBase S.a S.E S.perfect) g hb hA S.i
    ((graphZeroLocus S.a S.E S.perfect S.graphSubschemeι
      S.isFiniteLocallyFree_graphObjectRestrictHomology).ι ≫ S.graphSubschemeι) t
    S.hasDefinedChernClasses_graphObject p
    (mem_range_graphZeroLocus S.base S.a S.E S.perfect S.i S.graphSubschemeι
      S.isFiniteLocallyFree_graphObjectRestrictHomology S.mem_range_graphSubschemeι
      (S.finiteLocallyFreeRank_graphSubscheme_eq_zero h)) hT
    (isZero_derivedPullback_graphZeroLocus S.a S.E S.perfect S.graphSubschemeι
      S.isFiniteLocallyFree_graphObjectRestrictHomology) hzero).symm

end LocalizedSituation

/-! ### The total localized Chern class as the class of Stacks 0FAY of a modification -/

namespace LocalizedChernData

variable {D : LocalizedChernData.{u}} (hE : HasDefinedChernClasses D.E)
  (h : D.IsFiniteLocallyFreeOfRankLTOnComplement) {W T : Scheme.{u}}
  {b : W ⟶ projectiveLineProduct D.a} [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart D.a)))
  (t : T ⟶ modificationFibreAtInfinity D.a b) [IsClosedImmersion t] {Q : DerivedCategory W.Modules}
  (hQ : HasDefinedChernClasses Q)
  (hT : ∀ w, modificationProjectionAtInfinity D.a b w ∉ Set.range D.i → w ∈ Set.range t)
  (hrank : ∃ M : T.Modules, IsFiniteLocallyFreeOfRankLT M D.p ∧
    Nonempty ((derivedPullback (t ≫ modificationInclusionAtInfinity D.a b).toLRSHom.toShHom).obj
      Q ≅ (DerivedCategory.singleFunctor _ 0).obj M))

/-- **`c⁽ᵖ⁾(Z ⟶ X, E)` is the class `c⁽ᵖ⁾(Q)` of Stacks 0FAY of a modification** as soon as the
localized classes agree. Let `b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X`, let
`T ⊆ W_∞` be closed and contain the points over `X ∖ Z`, and let `Q ∈ D(𝒪_W)` have defined Chern
classes, with `Q|_T` finite locally free of rank `< p` in degree `0` and `c(Q|_{X × {0}}) = c(E)`
(as when `Q|_{X × {0}} ≅ E`). If
`c_q(Z ⟶ X, E) = c'_q(Q)` for every `q ≥ p`, then `c⁽ᵖ⁾(Z ⟶ X, E) = c⁽ᵖ⁾(Q)` in `A⁽ᵖ⁾(Z ⟶ X)`:
below the cutoff both components are the Chern classes of `E`, resp. of `Q|_{X × {0}}`. -/
theorem totalLocalizedChern_eq_modificationTotalChernClass
    (hc : perfectChernClass D.base D.a hE = perfectChernClass D.base D.a (hQ.derivedPullback
      (modificationSectionAtZero D.a b (isIso_modificationFibreAtZeroProjection D.a b hA))))
    (hloc : ∀ (q : ℕ) (hq : D.p ≤ q), (D.ofLe hq).localizedChern hE (h.ofLe hq) =
      modificationChernClass D.base D.a b hA D.i t hQ q hT
        (hrank.imp fun _ hM => ⟨hM.1.mono hq, hM.2⟩)) :
    totalLocalizedChern hE h =
      modificationTotalChernClass D.base D.a b hA D.i t hQ D.p hT hrank := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · rw [totalLocalizedChern_fst, modificationTotalChernClass_fst, hc]
  · rw [totalLocalizedChern_snd, localizedChernOfLe]
    exact congrArg (bivariantClassDegreeCongr D.base _ (D.i ≫ D.a) D.a D.i rfl _) (hloc _ _)

end LocalizedChernData

/-! ### Stacks 0FAY for the product with output cutoff `r` -/

section WhitneyCutoff

variable {C : ChowSituation.{u}} {X W Z T : Scheme.{u}} {f : X ⟶ C.S} [LocallyOfFiniteType f]
  {b : W ⟶ projectiveLineProduct f} [IsProper b]
  {hA : IsIso (pullback.snd b (projectiveLineAffineChart f))}
  {z : Z ⟶ X} [IsClosedImmersion z] {t : T ⟶ modificationFibreAtInfinity f b}
  [IsClosedImmersion t] {Q Q' : DerivedCategory W.Modules} (hQ : HasDefinedChernClasses Q)
  (hQ' : HasDefinedChernClasses Q') {p p' r : ℕ}
  {hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t}

/-- **Stacks 0FAY with output cutoff `r`.** In the situation of
`Stacks.Chow.modificationTotalChernClass_biprod`, for every `r` with `p + p' ≤ r + 1`,

  `c⁽ʳ⁾(Q ⊕ Q') = c⁽ᵖ⁾(Q) c⁽ᵖ'⁾(Q')`   in `A⁽ʳ⁾(Z ⟶ X)`,

with the multiplication of Stacks 0FA0 with output cutoff `r`
(`Stacks.Chow.localizedGradingCutoffMul`); the case `r = p + p'` is Stacks 0FAY. The hypothesis
of Stacks 0F9K on `(Q ⊕ Q')|_T`, of rank `< r`, follows from those on `Q|_T` and `Q'|_T`
(`Stacks.Chow.exists_isFiniteLocallyFreeOfRankLT_derivedPullback_biprod_of_add_le`). The proof is
that of Stacks 0FAY: below the cutoff the components are the Chern classes of
`(Q ⊕ Q')|_{X × {0}}`, and from the cutoff on both sides are localized classes of
`c_n(Q ⊕ Q') = ∑ c_i(Q) c_{n-i}(Q')`, summand by summand; since `n ≥ r ≥ p + p' - 1`, every
summand has `i ≥ p` or `n - i ≥ p'`. -/
theorem modificationTotalChernClass_biprod_cutoffMul (hr : p + p' ≤ r + 1)
    (hrank : ∃ M : T.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((derivedPullback (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj
        Q ≅ (DerivedCategory.singleFunctor _ 0).obj M))
    (hrank' : ∃ M : T.Modules, IsFiniteLocallyFreeOfRankLT M p' ∧
      Nonempty ((derivedPullback (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj
        Q' ≅ (DerivedCategory.singleFunctor _ 0).obj M)) :
    modificationTotalChernClass C f b hA z t (hasDefinedChernClasses_biprod hQ hQ') r hT
        (exists_isFiniteLocallyFreeOfRankLT_derivedPullback_biprod_of_add_le _ hr hrank
          hrank') =
      localizedGradingCutoffMul C (z ≫ f) f z rfl r hr
        (modificationTotalChernClass C f b hA z t hQ p hT hrank)
        (modificationTotalChernClass C f b hA z t hQ' p' hT hrank') := by
  have hEF := hasDefinedChernClasses_biprod hQ hQ'
  have hs : modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA) ≫
      modificationProjection f b ≫ f = f := by
    rw [← Category.assoc, modificationSectionAtZero_comp_projection f b hA, Category.id_comp]
  refine Prod.ext (funext fun n => ?_) (funext fun n => ?_)
  · -- Below the cutoff: the Whitney formula on `X`, through Stacks 0F9K.
    have hX : perfectChernClass C f (hEF.derivedPullback
          (modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA))) =
        perfectChernClass C f (hQ.derivedPullback
          (modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA))) *
        perfectChernClass C f (hQ'.derivedPullback
          (modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA))) := by
      rw [← res_perfectChernClass_derivedPullback_of_comp_eq C _ hEF _ hs,
        perfectChernClass_biprod C _ hQ hQ' hEF, map_mul,
        res_perfectChernClass_derivedPullback_of_comp_eq C _ hQ _ hs,
        res_perfectChernClass_derivedPullback_of_comp_eq C _ hQ' _ hs]
    rw [localizedGradingCutoffMul_fst, modificationTotalChernClass_fst, hX,
      TotalChowClass.intComponent_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [localizedGradingPush_modificationTotalChernClass,
      localizedGradingPush_modificationTotalChernClass]
  · -- From the cutoff on: both sides are localized classes of `c_n(Q ⊕ Q')`.
    have hn := n.2
    have key : IsLocalizedModificationClass (gysinAtInfinityData C f b hA) z t hT
        ((perfectChernClass C (modificationProjection f b ≫ f) hEF).intComponent C _ n.1)
        ((localizedGradingCutoffMul C (z ≫ f) f z rfl r hr
          (modificationTotalChernClass C f b hA z t hQ p hT hrank)
          (modificationTotalChernClass C f b hA z t hQ' p' hT hrank')).2 n) := by
      rw [perfectChernClass_biprod C _ hQ hQ' hEF, TotalChowClass.intComponent_mul,
        localizedGradingCutoffMul_snd]
      refine IsLocalizedModificationClass.sum _ fun i hi => ?_
      have hi' := Finset.mem_Icc.mp hi
      refine IsLocalizedModificationClass.bivariantClassDegreeCongr _ ?_
      by_cases hpi : (p : ℤ) ≤ i
      · by_cases hqi : (p' : ℤ) ≤ n.1 - i
        · rw [localizedGradingTerm_of_le_of_le _ _ _ hpi hqi]
          exact (isLocalizedModificationClass_modificationTotalChernClass_snd hrank
            ⟨i, hpi⟩).supportedMul
            (isLocalizedModificationClass_modificationTotalChernClass_snd hrank' ⟨n.1 - i, hqi⟩)
            (commutesAtInfinity_gysinAtInfinityData C f b hA _)
        · rw [localizedGradingTerm_of_le_of_lt _ _ _ hpi (not_le.mp hqi),
            modificationTotalChernClass_fst,
            intComponent_perfectChernClass_derivedPullback C _ hs hQ']
          exact (isLocalizedModificationClass_modificationTotalChernClass_snd hrank
            ⟨i, hpi⟩).supportedRightComp _ (commutesAtInfinity_gysinAtInfinityData C f b hA _)
      · have hqi : (p' : ℤ) ≤ n.1 - i := by omega
        rw [localizedGradingTerm_of_lt _ _ _ (not_le.mp hpi) hqi,
          modificationTotalChernClass_fst]
        obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hi'.1
        rw [TotalChowClass.intComponent_natCast, TotalChowClass.intComponent_natCast]
        refine ((isLocalizedModificationClass_modificationTotalChernClass_snd hrank'
          ⟨n.1 - m, hqi⟩).supportedRightComp _
            (commutesAtInfinity_gysinAtInfinityData C f b hA
              (perfectChernClass C (modificationProjection f b ≫ f) hQ m))).of_heq
          (add_comm _ _) (BivariantClass.heq_mulId_perfectChernClass _ hQ m) ?_
        rw [← perfectChernClass_derivedPullback_apply C _ hs hQ m]
        exact (ambientSupportedMul_perfectChernClass_heq C (z ≫ f) f z rfl _ m _).symm
    obtain ⟨hv, hH⟩ := key
    rw [hH]
    exact (isLocalizedModificationClass_modificationTotalChernClass_snd _ n).eq hv

end WhitneyCutoff

/-! ### The graph construction pulled back to a further modification -/

section GraphPullback

variable {X S W : Scheme.{u}} (f : X ⟶ S) (E : DerivedCategory X.Modules)
  (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E) {b : W ⟶ projectiveLineProduct f}
  (g : W ⟶ graphBlowup f E hE) (hb : g ≫ graphBlowupToBase f E hE = b)

include hb in
/-- **`(Lg^*Q)|_{X × {0}} ≅ E`** for the object `Q` of the graph construction of `E` pulled back
along a morphism of modifications `g : W' ⟶ W`: the section at zero of `W'` followed by `g` is
that of `W`, along which `Q` restricts to `E` (Stacks 0F90 (2)). -/
theorem nonempty_derivedPullback_modificationSectionAtZero_derivedPullback_graphObject
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) :
    Nonempty ((derivedPullback (modificationSectionAtZero f b
        (isIso_modificationFibreAtZeroProjection f b hA)).toLRSHom.toShHom).obj
        ((derivedPullback g.toLRSHom.toShHom).obj (graphObject f E hE)) ≅ E) := by
  obtain ⟨e⟩ := nonempty_derivedPullback_modificationSectionAtZero_graphObject f E hE
  have hs := modificationSectionAtZero_comp_of_comp_eq f g hb
    (isIso_pullback_snd_graphBlowupToBase f E hE) hA
  refine ⟨derivedPullbackCompIsoOfScheme _ g _ ≪≫ ?_⟩
  rw [hs]
  exact e

include hb in
/-- **`(Lg^*Q)|_{b'^{-1}(𝐀¹_X)}` is the pullback of `E`** for the object `Q` of the graph
construction of `E` pulled back along a morphism of modifications `g : W' ⟶ W` (Stacks 0F90 (2)
and `Stacks.Chow.nonempty_derivedPullback_affineChart_derivedPullback_iso`). -/
theorem nonempty_derivedPullback_affineChart_derivedPullback_graphObject :
    Nonempty ((derivedPullback (pullback.fst b (projectiveLineAffineChart f)).toLRSHom.toShHom).obj
        ((derivedPullback g.toLRSHom.toShHom).obj (graphObject f E hE)) ≅
      (derivedPullback (pullback.fst b (projectiveLineAffineChart f) ≫
        modificationProjection f b).toLRSHom.toShHom).obj E) :=
  nonempty_derivedPullback_affineChart_derivedPullback_iso f g hb
    (nonempty_derivedPullback_graphObject f E hE _ fun x =>
      ⟨pullback.snd (graphBlowupToBase f E hE) (projectiveLineAffineChart f) x, by
        rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]⟩)

end GraphPullback

/-- The termwise pullback of a K-flat representative of `Q₁` represents `Lg^*Q₁`. -/
private theorem nonempty_derivedPullback_iso_pullbackComplex {W W₁ : Scheme.{u}} (g : W ⟶ W₁)
    {Q₁ : DerivedCategory W₁.Modules} {P : CochainComplex W₁.Modules ℤ}
    (hP : IsLocallyBoundedFiniteLocallyFree P) (e : DerivedCategory.Q.obj P ≅ Q₁) :
    Nonempty ((derivedPullback g.toLRSHom.toShHom).obj Q₁ ≅
      DerivedCategory.Q.obj (pullbackComplex g P)) :=
  ⟨(derivedPullback g.toLRSHom.toShHom).mapIso e.symm ≪≫
    Cohomology.derivedPullbackIsoPullbackOfKFlat g.toLRSHom.toShHom P
      (Stacks.BlowUpComplexes.kFlatComplex_of_isLocallyBoundedFiniteLocallyFree P hP)⟩

/-- **The derived pullback of an object represented by a locally bounded complex of finite
locally free modules** is represented by the termwise pullback of the complex, again locally
bounded and finite locally free (the complex is K-flat). -/
theorem exists_isLocallyBoundedFiniteLocallyFree_derivedPullback {W W₁ : Scheme.{u}}
    (g : W ⟶ W₁) {Q₁ : DerivedCategory W₁.Modules}
    (hc : ∃ P : CochainComplex W₁.Modules ℤ, IsLocallyBoundedFiniteLocallyFree P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ Q₁)) :
    ∃ P : CochainComplex (OXMod.{u, u, u} W.toRingedSpace) ℤ, IsLocallyBoundedFiniteLocallyFree P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ (derivedPullback g.toLRSHom.toShHom).obj Q₁) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := hc
  exact ⟨pullbackComplex g P,
    Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback _ P hP,
    ⟨(nonempty_derivedPullback_iso_pullbackComplex g hP e).some.symm⟩⟩

/-- **Pullbacks of objects represented by locally bounded complexes of finite locally free
modules, and their direct sum.** If `Q₁` and `Q₃` are represented by locally bounded complexes of
finite locally free modules, so is `Lg₁^*Q₁ ⊕ Lg₃^*Q₃`, by the termwise biproduct of the termwise
pullbacks (the complexes are K-flat). -/
theorem exists_isLocallyBoundedFiniteLocallyFree_biprod_derivedPullback {W W₁ W₃ : Scheme.{u}}
    (g₁ : W ⟶ W₁) (g₃ : W ⟶ W₃) {Q₁ : DerivedCategory W₁.Modules}
    {Q₃ : DerivedCategory W₃.Modules}
    (hc₁ : ∃ P : CochainComplex W₁.Modules ℤ, IsLocallyBoundedFiniteLocallyFree P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ Q₁))
    (hc₃ : ∃ P : CochainComplex W₃.Modules ℤ, IsLocallyBoundedFiniteLocallyFree P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ Q₃)) :
    ∃ P : CochainComplex W.Modules ℤ, IsLocallyBoundedFiniteLocallyFree P ∧
      Nonempty ((derivedPullback g₁.toLRSHom.toShHom).obj Q₁ ⊞
        (derivedPullback g₃.toLRSHom.toShHom).obj Q₃ ≅ DerivedCategory.Q.obj P) := by
  obtain ⟨P₁, hP₁, ⟨e₁⟩⟩ := hc₁
  obtain ⟨P₃, hP₃, ⟨e₃⟩⟩ := hc₃
  have := preservesBinaryBiproducts_of_preservesBiproducts
    (DerivedCategory.Q (C := W.Modules))
  exact ⟨(pullbackComplex g₁ P₁ ⊞ pullbackComplex g₃ P₃ : CochainComplex W.Modules ℤ),
    isLocallyBoundedFiniteLocallyFree_biprod
      (Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback _ P₁ hP₁)
      (Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback _ P₃ hP₃),
    ⟨biprod.mapIso (nonempty_derivedPullback_iso_pullbackComplex g₁ hP₁ e₁).some
      (nonempty_derivedPullback_iso_pullbackComplex g₃ hP₃ e₃).some ≪≫
      ((DerivedCategory.Q (C := W.Modules)).mapBiprod _ _).symm⟩⟩

/-! ### The total localized Chern class on a further modification -/

namespace LocalizedSituation

variable (S : LocalizedSituation.{u}) (h : S.IsFiniteLocallyFreeOfRankLTOnComplement)
  {W T : Scheme.{u}} (g : W ⟶ graphBlowup S.a S.E S.perfect) [IsProper g]
  {b : W ⟶ projectiveLineProduct S.a} [IsProper b]
  (hb : g ≫ graphBlowupToBase S.a S.E S.perfect = b)
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart S.a)))
  (t : T ⟶ modificationFibreAtInfinity S.a b) [IsClosedImmersion t]
  (hT : ∀ w, modificationProjectionAtInfinity S.a b w ∉ Set.range S.i → w ∈ Set.range t)

include hb in
/-- **`c⁽ᵖ⁾(Z ⟶ X, E)` on a further modification** (Stacks 0FB2 and 0FAU). Let `b : W ⟶ 𝐏¹_X`,
`Q` be the graph construction for `E`, let `g : W' ⟶ W` be proper with `b' = b ∘ g` an
isomorphism over `𝐀¹_X`, and let `T' ⊆ W'_∞` be closed, contain the points over `X ∖ Z`, and be
such that `(Lg^*Q)|_{T'}` is finite locally free of rank `< p` in degree `0`. Then
`c⁽ᵖ⁾(Z ⟶ X, E)` (with the classes of Remark 0GUK, which are those of Stacks 0FB2) is the class
`c⁽ᵖ⁾(Lg^*Q)` of Stacks 0FAY built from `W'`, `b'` and `T'`. -/
theorem totalLocalizedChern_eq_modificationTotalChernClass
    (hrank : ∃ M : T.Modules, IsFiniteLocallyFreeOfRankLT M S.p ∧
      Nonempty ((derivedPullback (t ≫ modificationInclusionAtInfinity S.a b).toLRSHom.toShHom).obj
        ((derivedPullback g.toLRSHom.toShHom).obj (graphObject S.a S.E S.perfect)) ≅
          (DerivedCategory.singleFunctor _ 0).obj M)) :
    LocalizedChernData.totalLocalizedChern (D := S.toLocalizedChernData)
        S.hasDefinedChernClasses_E h =
      modificationTotalChernClass S.base S.a b hA S.i t
        (S.hasDefinedChernClasses_graphObject.derivedPullback g) S.p hT hrank :=
  LocalizedChernData.totalLocalizedChern_eq_modificationTotalChernClass
    S.hasDefinedChernClasses_E h hA t _ hT hrank
    (perfectChernClass_congr S.base S.a _ _
      (nonempty_derivedPullback_modificationSectionAtZero_derivedPullback_graphObject S.a S.E
        S.perfect g hb hA).some.symm)
    fun q hq => by
      have : @IsProper W (graphBlowup (S.ofLe hq).a (S.ofLe hq).E (S.ofLe hq).perfect) g :=
        ‹IsProper g›
      have : @IsProper W (projectiveLineProduct (S.ofLe hq).a) b := ‹IsProper b›
      have : @IsClosedImmersion T (modificationFibreAtInfinity (S.ofLe hq).a b) t :=
        ‹IsClosedImmersion t›
      exact (localizedChern_toLocalizedChernData (S.ofLe hq) (h.ofLe hq)).trans
        ((S.ofLe hq).localizedChern_eq_modificationChernClass g hb hA t hT _ (h.ofLe hq))

end LocalizedSituation

/-! ### The direct-sum case of Stacks 0FBD and 0FBE -/

/-- **An object isomorphic to a direct sum of perfect objects is perfect** (Stacks 08CR, for the
distinguished triangle `E ⟶ E ⊕ F ⟶ F ⟶ E[1]`). -/
theorem isPerfect_of_iso_biprod {X : Scheme.{u}} {E F G : DerivedCategory X.Modules}
    (e : G ≅ E ⊞ F)
    (hE : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (hF : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) F) :
    Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) G :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso e.symm
    (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₂_of_distinguished _
      (binaryBiproductTriangle_distinguished E F) hE hF)

namespace LocalizedChernData

section DirectSum

variable (D : LocalizedChernData.{u}) {E₁ E₃ : DerivedCategory D.X.Modules} {p₁ p₃ : ℕ}

/-- **The statement of Stacks 0FBD makes sense, for a direct sum**: if `E₁|_{X ∖ Z}` and
`E₃|_{X ∖ Z}` are finite locally free of ranks `< p₁` and `< p₃` in degree `0`, then for every
object `E₂ ≅ E₁ ⊕ E₃` the restriction `E₂|_{X ∖ Z}` is finite locally free of rank `< r` in
degree `0` for every `r` with `p₁ + p₃ ≤ r + 1`. -/
theorem exists_isFiniteLocallyFreeOfRankLT_restrict_of_iso_biprod {E₂ : DerivedCategory D.X.Modules}
    (e : E₂ ≅ E₁ ⊞ E₃) {r : ℕ} (hr : p₁ + p₃ ≤ r + 1)
    (r₁ : ∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M p₁ ∧
        Nonempty ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
          D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
            D.X.Opens).isOpenEmbedding)).obj E₁ ≅ (DerivedCategory.singleFunctor _ 0).obj M))
    (r₃ : ∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M p₃ ∧
        Nonempty ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
          D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
            D.X.Opens).isOpenEmbedding)).obj E₃ ≅ (DerivedCategory.singleFunctor _ 0).obj M)) :
    ∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M r ∧
        Nonempty ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
          D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
            D.X.Opens).isOpenEmbedding)).obj E₂ ≅ (DerivedCategory.singleFunctor _ 0).obj M) := by
  have key : ∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M r ∧
        Nonempty ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
          D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
            D.X.Opens).isOpenEmbedding)).obj (E₁ ⊞ E₃ : DerivedCategory D.X.Modules) ≅
          (DerivedCategory.singleFunctor _ 0).obj M) :=
    exists_isFiniteLocallyFreeOfRankLT_derivedPullback_biprod_of_add_le
      (Scheme.Opens.ι (⟨(Set.range D.i.base)ᶜ,
        D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens)) hr r₁ r₃
  obtain ⟨M, hM, ⟨e'⟩⟩ := key
  exact ⟨M, hM, ⟨(derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
    D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).mapIso e ≪≫
      e'⟩⟩

/-- **The statement of Stacks 0FBE makes sense, for a direct sum**: if `E₁|_{X ∖ Z}` and
`E₃|_{X ∖ Z}` are zero, so is `E₂|_{X ∖ Z}` for every object `E₂ ≅ E₁ ⊕ E₃`. -/
theorem isZero_restrict_of_iso_biprod {E₂ : DerivedCategory D.X.Modules} (e : E₂ ≅ E₁ ⊞ E₃)
    (z₁ : IsZero ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).obj E₁))
    (z₃ : IsZero ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).obj E₃)) :
    IsZero ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).obj E₂) :=
  (isZero_derivedPullback_biprod
    (Scheme.Opens.ι (⟨(Set.range D.i.base)ᶜ, D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
      D.X.Opens)) z₁ z₃).of_iso ((derivedPullback (D.X.toRingedSpace.ofRestrict
        (⟨(Set.range D.i.base)ᶜ, D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
          D.X.Opens).isOpenEmbedding)).mapIso e)

end DirectSum

/-! ### The direct-sum case of Stacks 0FBD, through a common modification -/

section DirectSumModification

variable (D : LocalizedChernData.{u}) {E₁ E₃ : DerivedCategory D.X.Modules} {p₁ p₃ : ℕ}
  (h₁ : Cohomology.PerfectComplexes.IsPerfect (X := D.X.toRingedSpace) E₁)
  (h₃ : Cohomology.PerfectComplexes.IsPerfect (X := D.X.toRingedSpace) E₃)
  (r₁ : ∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
    D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
    IsFiniteLocallyFreeOfRankLT M p₁ ∧
      Nonempty ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
        D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
          D.X.Opens).isOpenEmbedding)).obj E₁ ≅ (DerivedCategory.singleFunctor _ 0).obj M))
  (r₃ : ∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
    D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
    IsFiniteLocallyFreeOfRankLT M p₃ ∧
      Nonempty ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
        D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
          D.X.Opens).isOpenEmbedding)).obj E₃ ≅ (DerivedCategory.singleFunctor _ 0).obj M))
  (fin₁ : CompactSpace D.X ∨ (∀ C ∈ irreducibleComponents D.X, IsCompact C) ∨
    (∃ P : CochainComplex (OXMod.{u, u, u} D.X.toRingedSpace) ℤ,
      IsLocallyBoundedFiniteLocallyFree P ∧ Nonempty (DerivedCategory.Q.obj P ≅ E₁)) ∨
    (∃ (X' : Scheme.{u}) (a' : X' ⟶ D.base.S) (f : D.X ⟶ X')
        (E' : DerivedCategory (OXMod.{u, u, u} X'.toRingedSpace)),
      LocallyOfFiniteType a' ∧ f ≫ a' = D.a ∧
        Cohomology.PerfectComplexes.IsPerfect (X := X'.toRingedSpace) E' ∧
        Nonempty ((derivedPullback f.toLRSHom.toShHom).obj E' ≅ E₁) ∧
        ∀ C ∈ irreducibleComponents X', IsCompact C))
  (fin₃ : CompactSpace D.X ∨ (∀ C ∈ irreducibleComponents D.X, IsCompact C) ∨
    (∃ P : CochainComplex (OXMod.{u, u, u} D.X.toRingedSpace) ℤ,
      IsLocallyBoundedFiniteLocallyFree P ∧ Nonempty (DerivedCategory.Q.obj P ≅ E₃)) ∨
    (∃ (X' : Scheme.{u}) (a' : X' ⟶ D.base.S) (f : D.X ⟶ X')
        (E' : DerivedCategory (OXMod.{u, u, u} X'.toRingedSpace)),
      LocallyOfFiniteType a' ∧ f ≫ a' = D.a ∧
        Cohomology.PerfectComplexes.IsPerfect (X := X'.toRingedSpace) E' ∧
        Nonempty ((derivedPullback f.toLRSHom.toShHom).obj E' ≅ E₃) ∧
        ∀ C ∈ irreducibleComponents X', IsCompact C))

/-- **The instance of Situation 0GUJ for another object** with the closed immersion `Z ⟶ X` of
`D`: the data `Stacks.Chow.LocalizedChernData.withObject`, with a finiteness condition (3) of
Situation 0GUJ for the object. -/
abbrev situationWithObject (E : DerivedCategory D.X.Modules) (q : ℕ)
    (hE : Cohomology.PerfectComplexes.IsPerfect (X := D.X.toRingedSpace) E)
    (h : ∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
    D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
    IsFiniteLocallyFreeOfRankLT M q ∧
      Nonempty ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
        D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
          D.X.Opens).isOpenEmbedding)).obj E ≅ (DerivedCategory.singleFunctor _ 0).obj M))
    (fin : CompactSpace D.X ∨ (∀ C ∈ irreducibleComponents D.X, IsCompact C) ∨
    (∃ P : CochainComplex (OXMod.{u, u, u} D.X.toRingedSpace) ℤ,
      IsLocallyBoundedFiniteLocallyFree P ∧ Nonempty (DerivedCategory.Q.obj P ≅ E)) ∨
    (∃ (X' : Scheme.{u}) (a' : X' ⟶ D.base.S) (f : D.X ⟶ X')
        (E' : DerivedCategory (OXMod.{u, u, u} X'.toRingedSpace)),
      LocallyOfFiniteType a' ∧ f ≫ a' = D.a ∧
        Cohomology.PerfectComplexes.IsPerfect (X := X'.toRingedSpace) E' ∧
        Nonempty ((derivedPullback f.toLRSHom.toShHom).obj E' ≅ E) ∧
        ∀ C ∈ irreducibleComponents X', IsCompact C)) :
    LocalizedSituation.{u} :=
  ⟨D.withObject E q hE h, fin⟩

/-- **The data of a localized Chern class for another object vanishing off `Z`**, with the closed
immersion `Z ⟶ X` and the degree of `D`: a perfect object `E` of `D(𝒪_X)` with `E|_{X ∖ Z}` zero.
It is `{ D with E := E, perfect := hE, restriction := Or.inl h }`. -/
abbrev withZeroObject (E : DerivedCategory D.X.Modules)
    (hE : Cohomology.PerfectComplexes.IsPerfect (X := D.X.toRingedSpace) E)
    (h : IsZero ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
    D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).obj E)) :
    LocalizedChernData.{u} :=
  { D with E := E, perfect := hE, restriction := Or.inl h }

/-- **The instance of Situation 0GUJ for another object vanishing off `Z`**: the data
`Stacks.Chow.LocalizedChernData.withZeroObject`, with a finiteness condition (3) of
Situation 0GUJ for the object. -/
abbrev situationWithZeroObject (E : DerivedCategory D.X.Modules)
    (hE : Cohomology.PerfectComplexes.IsPerfect (X := D.X.toRingedSpace) E)
    (h : IsZero ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
    D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).obj E))
    (fin : CompactSpace D.X ∨ (∀ C ∈ irreducibleComponents D.X, IsCompact C) ∨
      (∃ P : CochainComplex (OXMod.{u, u, u} D.X.toRingedSpace) ℤ,
        IsLocallyBoundedFiniteLocallyFree P ∧ Nonempty (DerivedCategory.Q.obj P ≅ E)) ∨
      (∃ (X' : Scheme.{u}) (a' : X' ⟶ D.base.S) (f : D.X ⟶ X')
          (E' : DerivedCategory (OXMod.{u, u, u} X'.toRingedSpace)),
        LocallyOfFiniteType a' ∧ f ≫ a' = D.a ∧
          Cohomology.PerfectComplexes.IsPerfect (X := X'.toRingedSpace) E' ∧
          Nonempty ((derivedPullback f.toLRSHom.toShHom).obj E' ≅ E) ∧
          ∀ C ∈ irreducibleComponents X', IsCompact C)) :
    LocalizedSituation.{u} :=
  ⟨D.withZeroObject E hE h, fin⟩

/-- **The direct-sum case of Stacks 0FBD with output cutoff `r`, given Stacks 0FE8 on a common
modification.** Let `(X, Z, E₁)` and `(X, Z, E₃)` be as in Situation 0GUJ, with `E₁|_{X ∖ Z}`,
`E₃|_{X ∖ Z}` finite locally free of ranks `< p₁`, `< p₃` in degree `0`, let `E₂ ≅ E₁ ⊕ E₃`, let
`b_j : W_j ⟶ 𝐏¹_X`, `Q_j` be the graph constructions of `E₁`, `E₃`, and let `b : W ⟶ 𝐏¹_X` be
proper and an isomorphism over `𝐀¹_X`, with proper `g_j : W ⟶ W_j` such that `b = b_j ∘ g_j`.
Suppose that for `Q = Lg₁^*Q₁ ⊕ Lg₃^*Q₃` and every `n ≥ r` the localized Chern class
`c_n(Z ⟶ X, E₂)` is the class `c'_n(Q)` of Stacks 0F9K built from `W`, `b`, `Q` and any closed
`T ⊆ W_∞` with the properties of Stacks 0F9K (this is Stacks 0FE8 for `F = E₂`). Then for every
`r` with `p₁ + p₃ ≤ r + 1`

  `c⁽ʳ⁾(Z ⟶ X, E₂) = c⁽ᵖ¹⁾(Z ⟶ X, E₁) c⁽ᵖ³⁾(Z ⟶ X, E₃)`   in `A⁽ʳ⁾(Z ⟶ X)`,

with the multiplication of Stacks 0FA0 with output cutoff `r` (the source's case is `r = p₁ + p₃`).
Following the last paragraph of the proof of Stacks 0FBD: in `W_∞` the intersection
`T' = g₁⁻¹(T'₁) ∩ g₃⁻¹(T'₃)` still contains the points over `X ∖ Z`, by Stacks 0FAU the classes
of `E_j` may be computed from `W`, `b`, `Lg_j^*Q_j` and `T'`, by the hypothesis those of `E₂` from
`W`, `b`, `Q` and `T'`, and Stacks 0FAY (with output cutoff `r`) concludes. -/
theorem totalLocalizedChern_eq_cutoffMul_of_modification {E₂ : DerivedCategory D.X.Modules}
    (e : E₂ ≅ E₁ ⊞ E₃) {r : ℕ} (hr : p₁ + p₃ ≤ r + 1)
    {W : Scheme.{u}} {b : W ⟶ projectiveLineProduct D.a} [IsProper b]
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart D.a)))
    (g₁ : W ⟶ graphBlowup D.a E₁ h₁) [IsProper g₁] (hb₁ : g₁ ≫ graphBlowupToBase D.a E₁ h₁ = b)
    (g₃ : W ⟶ graphBlowup D.a E₃ h₃) [IsProper g₃] (hb₃ : g₃ ≫ graphBlowupToBase D.a E₃ h₃ = b)
    (h0FE8 : ∀ (n : ℕ) (hn : r ≤ n) {T : Scheme.{u}}
      (t : T ⟶ modificationFibreAtInfinity D.a b) [IsClosedImmersion t]
      (hT : ∀ w, modificationProjectionAtInfinity D.a b w ∉ Set.range D.i → w ∈ Set.range t)
      (hrank : ∃ M : T.Modules, IsFiniteLocallyFreeOfRankLT M n ∧
        Nonempty ((derivedPullback (t ≫ modificationInclusionAtInfinity D.a b).toLRSHom.toShHom).obj
          ((derivedPullback g₁.toLRSHom.toShHom).obj (graphObject D.a E₁ h₁) ⊞
            (derivedPullback g₃.toLRSHom.toShHom).obj (graphObject D.a E₃ h₃)) ≅
          (DerivedCategory.singleFunctor _ 0).obj M)),
      (D.withObject E₂ n (isPerfect_of_iso_biprod e h₁ h₃)
          (D.exists_isFiniteLocallyFreeOfRankLT_restrict_of_iso_biprod e (by omega) r₁
            r₃)).localizedChern
          ((hasDefinedChernClasses_of_iso (hasDefinedChernClasses_biprod (E := E₁) (F := E₃)
            (D.situationWithObject E₁ p₁ h₁ r₁ fin₁).hasDefinedChernClasses_E
            (D.situationWithObject E₃ p₃ h₃ r₃ fin₃).hasDefinedChernClasses_E) e.symm :
              HasDefinedChernClasses E₂))
          (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject _) =
        modificationChernClass D.base D.a b hA D.i t
          (hasDefinedChernClasses_biprod
            (HasDefinedChernClasses.derivedPullback
              (D.situationWithObject E₁ p₁ h₁ r₁ fin₁).hasDefinedChernClasses_graphObject g₁)
            (HasDefinedChernClasses.derivedPullback
              (D.situationWithObject E₃ p₃ h₃ r₃ fin₃).hasDefinedChernClasses_graphObject g₃))
          n hT hrank) :
    totalLocalizedChern (D := D.withObject E₂ r (isPerfect_of_iso_biprod e h₁ h₃)
        (D.exists_isFiniteLocallyFreeOfRankLT_restrict_of_iso_biprod e hr r₁ r₃))
        ((hasDefinedChernClasses_of_iso (hasDefinedChernClasses_biprod (E := E₁) (F := E₃)
          (D.situationWithObject E₁ p₁ h₁ r₁ fin₁).hasDefinedChernClasses_E
          (D.situationWithObject E₃ p₃ h₃ r₃ fin₃).hasDefinedChernClasses_E) e.symm :
            HasDefinedChernClasses E₂))
        (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject _) =
      localizedGradingCutoffMul D.base (D.i ≫ D.a) D.a D.i rfl r hr
        (totalLocalizedChern (D := D.withObject E₁ p₁ h₁ r₁)
          (D.situationWithObject E₁ p₁ h₁ r₁ fin₁).hasDefinedChernClasses_E
          (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₁))
        (totalLocalizedChern (D := D.withObject E₃ p₃ h₃ r₃)
          (D.situationWithObject E₃ p₃ h₃ r₃ fin₃).hasDefinedChernClasses_E
          (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₃)) := by
  let S₁ := D.situationWithObject E₁ p₁ h₁ r₁ fin₁
  let S₃ := D.situationWithObject E₃ p₃ h₃ r₃ fin₃
  have h₁' : S₁.IsFiniteLocallyFreeOfRankLTOnComplement := r₁
  have h₃' : S₃.IsFiniteLocallyFreeOfRankLTOnComplement := r₃
  let _ := isClosedImmersion_graphSmallRankLocus_ι D.a E₁ h₁ S₁.graphSubschemeι
    S₁.isFiniteLocallyFree_graphObjectRestrictHomology p₁
  let _ := isClosedImmersion_graphSmallRankLocus_ι D.a E₃ h₃ S₃.graphSubschemeι
    S₃.isFiniteLocallyFree_graphObjectRestrictHomology p₃
  -- the closed subscheme `T' = g₁⁻¹(T'₁) ∩ g₃⁻¹(T'₃)` of `W_∞`
  obtain ⟨T, t, _, a₁, a₃, hT, ha₁, ha₃⟩ := exists_closedImmersion_inter_preimage D.a g₁ g₃ hb₁
    hb₃ D.i
    ((graphSmallRankLocus D.a E₁ h₁ S₁.graphSubschemeι
      S₁.isFiniteLocallyFree_graphObjectRestrictHomology p₁).ι ≫ S₁.graphSubschemeι)
    ((graphSmallRankLocus D.a E₃ h₃ S₃.graphSubschemeι
      S₃.isFiniteLocallyFree_graphObjectRestrictHomology p₃).ι ≫ S₃.graphSubschemeι)
    (mem_range_graphSmallRankLocus D.base D.a E₁ h₁ D.i S₁.graphSubschemeι
      S₁.isFiniteLocallyFree_graphObjectRestrictHomology p₁ S₁.mem_range_graphSubschemeι
      (S₁.finiteLocallyFreeRank_graphSubscheme_lt h₁'))
    (mem_range_graphSmallRankLocus D.base D.a E₃ h₃ D.i S₃.graphSubschemeι
      S₃.isFiniteLocallyFree_graphObjectRestrictHomology p₃ S₃.mem_range_graphSubschemeι
      (S₃.finiteLocallyFreeRank_graphSubscheme_lt h₃'))
  -- `Lg_j^*Q_j` restricts to rank `< p_j` on `T'`
  have hrank₁ := exists_isFiniteLocallyFreeOfRankLT_derivedPullback_of_comp_eq ha₁
    (exists_isFiniteLocallyFreeOfRankLT_derivedPullback_graphSmallRankLocus D.a E₁ h₁
      S₁.graphSubschemeι S₁.isFiniteLocallyFree_graphObjectRestrictHomology p₁)
  have hrank₃ := exists_isFiniteLocallyFreeOfRankLT_derivedPullback_of_comp_eq ha₃
    (exists_isFiniteLocallyFreeOfRankLT_derivedPullback_graphSmallRankLocus D.a E₃ h₃
      S₃.graphSubschemeι S₃.isFiniteLocallyFree_graphObjectRestrictHomology p₃)
  -- the classes of `E₁` and `E₃` through `W`, `b`, `Lg_j^*Q_j`, `T'` (Stacks 0FAU)
  have tot₁ := S₁.totalLocalizedChern_eq_modificationTotalChernClass h₁' g₁ hb₁ hA t hT hrank₁
  have tot₃ := S₃.totalLocalizedChern_eq_modificationTotalChernClass h₃' g₃ hb₃ hA t hT hrank₃
  -- the class of `E₂` through `W`, `b`, `Lg₁^*Q₁ ⊕ Lg₃^*Q₃`, `T'` (Stacks 0FE8)
  have hc₂ : perfectChernClass D.base D.a
        (hasDefinedChernClasses_of_iso (hasDefinedChernClasses_biprod (E := E₁) (F := E₃)
          S₁.hasDefinedChernClasses_E S₃.hasDefinedChernClasses_E) e.symm) =
      perfectChernClass D.base D.a ((hasDefinedChernClasses_biprod
        (S₁.hasDefinedChernClasses_graphObject.derivedPullback g₁)
        (S₃.hasDefinedChernClasses_graphObject.derivedPullback g₃)).derivedPullback
          (modificationSectionAtZero D.a b
            (isIso_modificationFibreAtZeroProjection D.a b hA))) := by
    let s₀ := modificationSectionAtZero D.a b (isIso_modificationFibreAtZeroProjection D.a b hA)
    have hP₁ := (S₁.hasDefinedChernClasses_graphObject.derivedPullback g₁).derivedPullback s₀
    have hP₃ := (S₃.hasDefinedChernClasses_graphObject.derivedPullback g₃).derivedPullback s₀
    rw [perfectChernClass_congr D.base D.a _
        (hasDefinedChernClasses_biprod (E := E₁) (F := E₃) S₁.hasDefinedChernClasses_E
          S₃.hasDefinedChernClasses_E) e,
      perfectChernClass_congr D.base D.a _ (hasDefinedChernClasses_biprod hP₁ hP₃)
        (derivedPullbackBiprodIso s₀ _ _),
      perfectChernClass_biprod D.base D.a hP₁ hP₃, perfectChernClass_biprod D.base D.a,
      perfectChernClass_congr D.base D.a hP₁ S₁.hasDefinedChernClasses_E
        (nonempty_derivedPullback_modificationSectionAtZero_derivedPullback_graphObject D.a E₁ h₁ g₁
          hb₁ hA).some,
      perfectChernClass_congr D.base D.a hP₃ S₃.hasDefinedChernClasses_E
        (nonempty_derivedPullback_modificationSectionAtZero_derivedPullback_graphObject D.a E₃ h₃ g₃
          hb₃ hA).some]
  have tot₂ := LocalizedChernData.totalLocalizedChern_eq_modificationTotalChernClass
    (D := D.withObject E₂ r (isPerfect_of_iso_biprod e h₁ h₃)
      (D.exists_isFiniteLocallyFreeOfRankLT_restrict_of_iso_biprod e hr r₁ r₃))
    (hasDefinedChernClasses_of_iso (hasDefinedChernClasses_biprod (E := E₁) (F := E₃)
      S₁.hasDefinedChernClasses_E S₃.hasDefinedChernClasses_E) e.symm)
    (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject _) hA t
    (hasDefinedChernClasses_biprod (S₁.hasDefinedChernClasses_graphObject.derivedPullback g₁)
      (S₃.hasDefinedChernClasses_graphObject.derivedPullback g₃)) hT
    (exists_isFiniteLocallyFreeOfRankLT_derivedPullback_biprod_of_add_le _ hr hrank₁ hrank₃) hc₂
    fun q hq => h0FE8 q hq t hT _
  refine tot₂.trans ((modificationTotalChernClass_biprod_cutoffMul
    (S₁.hasDefinedChernClasses_graphObject.derivedPullback g₁)
    (S₃.hasDefinedChernClasses_graphObject.derivedPullback g₃) hr hrank₁ hrank₃).trans ?_)
  rw [← tot₁, ← tot₃]

/-- **The direct-sum case of Stacks 0FBD, given Stacks 0FE8 on a common modification**: in the
situation of `Stacks.Chow.LocalizedChernData.totalLocalizedChern_eq_cutoffMul_of_modification`,
for `E₂ ≅ E₁ ⊕ E₃`,

  `c⁽ᵖ¹⁺ᵖ³⁾(Z ⟶ X, E₂) = c⁽ᵖ¹⁾(Z ⟶ X, E₁) c⁽ᵖ³⁾(Z ⟶ X, E₃)`   in `A⁽ᵖ¹⁺ᵖ³⁾(Z ⟶ X)`,

with the multiplication of Stacks 0FA0 (`Stacks.Chow.localizedGradingMul`). -/
theorem totalLocalizedChern_eq_mul_of_modification {E₂ : DerivedCategory D.X.Modules}
    (e : E₂ ≅ E₁ ⊞ E₃)
    {W : Scheme.{u}} {b : W ⟶ projectiveLineProduct D.a} [IsProper b]
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart D.a)))
    (g₁ : W ⟶ graphBlowup D.a E₁ h₁) [IsProper g₁] (hb₁ : g₁ ≫ graphBlowupToBase D.a E₁ h₁ = b)
    (g₃ : W ⟶ graphBlowup D.a E₃ h₃) [IsProper g₃] (hb₃ : g₃ ≫ graphBlowupToBase D.a E₃ h₃ = b)
    (h0FE8 : ∀ (n : ℕ) (hn : p₁ + p₃ ≤ n) {T : Scheme.{u}}
      (t : T ⟶ modificationFibreAtInfinity D.a b) [IsClosedImmersion t]
      (hT : ∀ w, modificationProjectionAtInfinity D.a b w ∉ Set.range D.i → w ∈ Set.range t)
      (hrank : ∃ M : T.Modules, IsFiniteLocallyFreeOfRankLT M n ∧
        Nonempty ((derivedPullback (t ≫ modificationInclusionAtInfinity D.a b).toLRSHom.toShHom).obj
          ((derivedPullback g₁.toLRSHom.toShHom).obj (graphObject D.a E₁ h₁) ⊞
            (derivedPullback g₃.toLRSHom.toShHom).obj (graphObject D.a E₃ h₃)) ≅
          (DerivedCategory.singleFunctor _ 0).obj M)),
      (D.withObject E₂ n (isPerfect_of_iso_biprod e h₁ h₃)
          (D.exists_isFiniteLocallyFreeOfRankLT_restrict_of_iso_biprod e (by omega) r₁
            r₃)).localizedChern
          ((hasDefinedChernClasses_of_iso (hasDefinedChernClasses_biprod (E := E₁) (F := E₃)
            (D.situationWithObject E₁ p₁ h₁ r₁ fin₁).hasDefinedChernClasses_E
            (D.situationWithObject E₃ p₃ h₃ r₃ fin₃).hasDefinedChernClasses_E) e.symm :
              HasDefinedChernClasses E₂))
          (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject _) =
        modificationChernClass D.base D.a b hA D.i t
          (hasDefinedChernClasses_biprod
            (HasDefinedChernClasses.derivedPullback
              (D.situationWithObject E₁ p₁ h₁ r₁ fin₁).hasDefinedChernClasses_graphObject g₁)
            (HasDefinedChernClasses.derivedPullback
              (D.situationWithObject E₃ p₃ h₃ r₃ fin₃).hasDefinedChernClasses_graphObject g₃))
          n hT hrank) :
    totalLocalizedChern (D := D.withObject E₂ (p₁ + p₃) (isPerfect_of_iso_biprod e h₁ h₃)
        (D.exists_isFiniteLocallyFreeOfRankLT_restrict_of_iso_biprod e (by omega) r₁ r₃))
        ((hasDefinedChernClasses_of_iso (hasDefinedChernClasses_biprod (E := E₁) (F := E₃)
          (D.situationWithObject E₁ p₁ h₁ r₁ fin₁).hasDefinedChernClasses_E
          (D.situationWithObject E₃ p₃ h₃ r₃ fin₃).hasDefinedChernClasses_E) e.symm :
            HasDefinedChernClasses E₂))
        (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject _) =
      localizedGradingMul D.base (D.i ≫ D.a) D.a D.i rfl
        (totalLocalizedChern (D := D.withObject E₁ p₁ h₁ r₁)
          (D.situationWithObject E₁ p₁ h₁ r₁ fin₁).hasDefinedChernClasses_E
          (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₁))
        (totalLocalizedChern (D := D.withObject E₃ p₃ h₃ r₃)
          (D.situationWithObject E₃ p₃ h₃ r₃ fin₃).hasDefinedChernClasses_E
          (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₃)) :=
  D.totalLocalizedChern_eq_cutoffMul_of_modification h₁ h₃ r₁ r₃ fin₁ fin₃ e (by omega) hA g₁ hb₁
    g₃ hb₃ h0FE8

variable
  (z₁ : IsZero ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
    D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).obj E₁))
  (z₃ : IsZero ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
    D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).obj E₃))

/-- **The direct-sum case of Stacks 0FBE, given Stacks 0FE8 on a common modification.** Let
`(X, Z, E₁)` and `(X, Z, E₃)` be as in Situation 0GUJ, with `E₁|_{X ∖ Z}` and `E₃|_{X ∖ Z}` zero,
let `b_j : W_j ⟶ 𝐏¹_X`, `Q_j` be their graph constructions, and let `b : W ⟶ 𝐏¹_X` be proper and
an isomorphism over `𝐀¹_X`, with proper `g_j : W ⟶ W_j` such that `b = b_j ∘ g_j`. Suppose that
for `E₂ ≅ E₁ ⊕ E₃` and `Q = Lg₁^*Q₁ ⊕ Lg₃^*Q₃` the localized class `P_p(Z ⟶ X, E₂)` is the class
`P'_p(Q)` of Stacks 0F9K built from `W`, `b`, `Q` and any closed `T ⊆ W_∞` with the properties of
Stacks 0F9K (this is Stacks 0FE8 for `F = E₂`). Then

  `P_p(Z ⟶ X, E₂) = P_p(Z ⟶ X, E₁) + P_p(Z ⟶ X, E₃)`

for the classes of Remark 0GUK (those of Stacks 0FB2 in Situation 0GUJ). As in the last paragraph
of the proof of Stacks 0FBD, with Stacks 0FAZ in place of Stacks 0FAY. -/
theorem localizedPowerSum_eq_add_of_modification {E₂ : DerivedCategory D.X.Modules}
    (e : E₂ ≅ E₁ ⊞ E₃) {W : Scheme.{u}} {b : W ⟶ projectiveLineProduct D.a} [IsProper b]
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart D.a)))
    (g₁ : W ⟶ graphBlowup D.a E₁ h₁) [IsProper g₁] (hb₁ : g₁ ≫ graphBlowupToBase D.a E₁ h₁ = b)
    (g₃ : W ⟶ graphBlowup D.a E₃ h₃) [IsProper g₃] (hb₃ : g₃ ≫ graphBlowupToBase D.a E₃ h₃ = b)
    (p : ℕ)
    (h0FE8 : ∀ {T : Scheme.{u}} (t : T ⟶ modificationFibreAtInfinity D.a b) [IsClosedImmersion t]
      (hT : ∀ w, modificationProjectionAtInfinity D.a b w ∉ Set.range D.i → w ∈ Set.range t)
      (hzero : IsZero ((derivedPullback
        (t ≫ modificationInclusionAtInfinity D.a b).toLRSHom.toShHom).obj
          ((derivedPullback g₁.toLRSHom.toShHom).obj (graphObject D.a E₁ h₁) ⊞
            (derivedPullback g₃.toLRSHom.toShHom).obj (graphObject D.a E₃ h₃)))),
      (D.withZeroObject E₂ (isPerfect_of_iso_biprod e h₁ h₃)
          (D.isZero_restrict_of_iso_biprod e z₁ z₃)).localizedPowerSum
          ((hasDefinedChernClasses_of_iso (hasDefinedChernClasses_biprod (E := E₁) (F := E₃)
            (D.situationWithZeroObject E₁ h₁ z₁ fin₁).hasDefinedChernClasses_E
            (D.situationWithZeroObject E₃ h₃ z₃ fin₃).hasDefinedChernClasses_E) e.symm :
              HasDefinedChernClasses E₂))
          (D.isZero_restrict_of_iso_biprod e z₁ z₃) p =
        modificationPowerSum D.base D.a b hA D.i t
          (hasDefinedChernClasses_biprod
            (HasDefinedChernClasses.derivedPullback
              (D.situationWithZeroObject E₁ h₁ z₁ fin₁).hasDefinedChernClasses_graphObject g₁)
            (HasDefinedChernClasses.derivedPullback
              (D.situationWithZeroObject E₃ h₃ z₃ fin₃).hasDefinedChernClasses_graphObject g₃))
          p hT hzero) :
    (D.withZeroObject E₂ (isPerfect_of_iso_biprod e h₁ h₃)
        (D.isZero_restrict_of_iso_biprod e z₁ z₃)).localizedPowerSum
        ((hasDefinedChernClasses_of_iso (hasDefinedChernClasses_biprod (E := E₁) (F := E₃)
          (D.situationWithZeroObject E₁ h₁ z₁ fin₁).hasDefinedChernClasses_E
          (D.situationWithZeroObject E₃ h₃ z₃ fin₃).hasDefinedChernClasses_E) e.symm :
            HasDefinedChernClasses E₂))
        (D.isZero_restrict_of_iso_biprod e z₁ z₃) p =
      (D.withZeroObject E₁ h₁ z₁).localizedPowerSum
          (D.situationWithZeroObject E₁ h₁ z₁ fin₁).hasDefinedChernClasses_E z₁ p +
        (D.withZeroObject E₃ h₃ z₃).localizedPowerSum
          (D.situationWithZeroObject E₃ h₃ z₃ fin₃).hasDefinedChernClasses_E z₃ p := by
  let S₁ := D.situationWithZeroObject E₁ h₁ z₁ fin₁
  let S₃ := D.situationWithZeroObject E₃ h₃ z₃ fin₃
  have z₁' : S₁.IsZeroOnComplement := z₁
  have z₃' : S₃.IsZeroOnComplement := z₃
  let _ := isClosedImmersion_graphZeroLocus_ι D.a E₁ h₁ S₁.graphSubschemeι
    S₁.isFiniteLocallyFree_graphObjectRestrictHomology
  let _ := isClosedImmersion_graphZeroLocus_ι D.a E₃ h₃ S₃.graphSubschemeι
    S₃.isFiniteLocallyFree_graphObjectRestrictHomology
  -- the closed subscheme `T' = g₁⁻¹(T'₁) ∩ g₃⁻¹(T'₃)` of `W_∞`
  obtain ⟨T, t, _, a₁, a₃, hT, ha₁, ha₃⟩ := exists_closedImmersion_inter_preimage D.a g₁ g₃ hb₁
    hb₃ D.i
    ((graphZeroLocus D.a E₁ h₁ S₁.graphSubschemeι
      S₁.isFiniteLocallyFree_graphObjectRestrictHomology).ι ≫ S₁.graphSubschemeι)
    ((graphZeroLocus D.a E₃ h₃ S₃.graphSubschemeι
      S₃.isFiniteLocallyFree_graphObjectRestrictHomology).ι ≫ S₃.graphSubschemeι)
    (mem_range_graphZeroLocus D.base D.a E₁ h₁ D.i S₁.graphSubschemeι
      S₁.isFiniteLocallyFree_graphObjectRestrictHomology S₁.mem_range_graphSubschemeι
      (S₁.finiteLocallyFreeRank_graphSubscheme_eq_zero z₁'))
    (mem_range_graphZeroLocus D.base D.a E₃ h₃ D.i S₃.graphSubschemeι
      S₃.isFiniteLocallyFree_graphObjectRestrictHomology S₃.mem_range_graphSubschemeι
      (S₃.finiteLocallyFreeRank_graphSubscheme_eq_zero z₃'))
  -- `Lg_j^*Q_j` restricts to zero on `T'`
  have hzero₁ := isZero_derivedPullback_of_isZero_of_comp_eq ha₁
    (isZero_derivedPullback_graphZeroLocus D.a E₁ h₁ S₁.graphSubschemeι
      S₁.isFiniteLocallyFree_graphObjectRestrictHomology)
  have hzero₃ := isZero_derivedPullback_of_isZero_of_comp_eq ha₃
    (isZero_derivedPullback_graphZeroLocus D.a E₃ h₃ S₃.graphSubschemeι
      S₃.isFiniteLocallyFree_graphObjectRestrictHomology)
  -- Stacks 0FE8, Stacks 0FAZ, and Stacks 0FAU for `E₁` and `E₃`
  refine (h0FE8 t hT (isZero_derivedPullback_biprod _ hzero₁ hzero₃)).trans
    ((modificationPowerSum_biprod D.base D.a b hA D.i t
      (S₁.hasDefinedChernClasses_graphObject.derivedPullback g₁)
      (S₃.hasDefinedChernClasses_graphObject.derivedPullback g₃) p hT hzero₁ hzero₃).trans ?_)
  rw [LocalizedSituation.localizedPowerSum_toLocalizedChernData S₁ z₁' p,
    LocalizedSituation.localizedPowerSum_toLocalizedChernData S₃ z₃' p,
    S₁.localizedPowerSum_eq_modificationPowerSum g₁ hb₁ hA t hT p hzero₁ z₁',
    S₃.localizedPowerSum_eq_modificationPowerSum g₃ hb₃ hA t hT p hzero₃ z₃']

end DirectSumModification

end LocalizedChernData

/-! ### Direct sums of objects represented by complexes of finite locally free modules -/

section Complexes

variable {X S W₁ W₃ : Scheme.{u}} (f : X ⟶ S) (E₁ E₃ : DerivedCategory X.Modules)

/-- **`E₁ ⊕ E₃` is represented by a locally bounded complex of finite locally free modules** when
`E₁` and `E₃` are: the termwise biproduct of representatives. -/
theorem exists_isLocallyBoundedFiniteLocallyFree_biprod
    (hc₁ : ∃ P : CochainComplex (OXMod.{u, u, u} X.toRingedSpace) ℤ,
      IsLocallyBoundedFiniteLocallyFree P ∧ Nonempty (DerivedCategory.Q.obj P ≅ E₁))
    (hc₃ : ∃ P : CochainComplex (OXMod.{u, u, u} X.toRingedSpace) ℤ,
      IsLocallyBoundedFiniteLocallyFree P ∧ Nonempty (DerivedCategory.Q.obj P ≅ E₃)) :
    ∃ P : CochainComplex (OXMod.{u, u, u} X.toRingedSpace) ℤ,
      IsLocallyBoundedFiniteLocallyFree P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ (E₁ ⊞ E₃ : DerivedCategory X.Modules)) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := exists_isLocallyBoundedFiniteLocallyFree_biprod_derivedPullback
    (𝟙 X) (𝟙 X) hc₁ hc₃
  exact ⟨P, hP, ⟨e.symm ≪≫ (derivedPullbackBiprodIso (𝟙 X) E₁ E₃).symm ≪≫
    (Cohomology.DerivedPullbackAlongIso.derivedPullbackIdIso X.toRingedSpace).app _⟩⟩

/-- **Restrictions of a direct sum along a commutative square.** If `Lu^*A ≅ Lv^*E₁` and
`Lu^*B ≅ Lv^*E₃`, then `Lu^*(A ⊕ B) ≅ Lv^*(E₁ ⊕ E₃)`. -/
theorem nonempty_derivedPullback_biprod_iso {V W : Scheme.{u}} (u : V ⟶ W) (v : V ⟶ X)
    (A B : DerivedCategory W.Modules)
    (e₁ : Nonempty ((derivedPullback u.toLRSHom.toShHom).obj A ≅
      (derivedPullback v.toLRSHom.toShHom).obj E₁))
    (e₃ : Nonempty ((derivedPullback u.toLRSHom.toShHom).obj B ≅
      (derivedPullback v.toLRSHom.toShHom).obj E₃)) :
    Nonempty ((derivedPullback u.toLRSHom.toShHom).obj (A ⊞ B : DerivedCategory W.Modules) ≅
      (derivedPullback v.toLRSHom.toShHom).obj (E₁ ⊞ E₃ : DerivedCategory X.Modules)) :=
  ⟨derivedPullbackBiprodIso u A B ≪≫ biprod.mapIso e₁.some e₃.some ≪≫
    (derivedPullbackBiprodIso v E₁ E₃).symm⟩

/-- **Condition (3) of Situation 0GUJ for a direct sum**: for `E₂ ≅ E₁ ⊕ E₃` it holds when `X` is
quasi-compact or has quasi-compact irreducible components (alternatives (a), (b), which concern
`X` only), or when `E₁` and `E₃` are both represented by locally bounded complexes of finite
locally free modules (alternative (c), for the termwise biproduct). -/
theorem LocalizedChernData.finiteness_of_iso_biprod (D : LocalizedChernData.{u})
    {E₁ E₂ E₃ : DerivedCategory D.X.Modules}
    (e : E₂ ≅ E₁ ⊞ E₃)
    (h : CompactSpace D.X ∨ (∀ C ∈ irreducibleComponents D.X, IsCompact C) ∨
      ((∃ P : CochainComplex (OXMod.{u, u, u} D.X.toRingedSpace) ℤ,
        IsLocallyBoundedFiniteLocallyFree P ∧ Nonempty (DerivedCategory.Q.obj P ≅ E₁)) ∧
       (∃ P : CochainComplex (OXMod.{u, u, u} D.X.toRingedSpace) ℤ,
        IsLocallyBoundedFiniteLocallyFree P ∧ Nonempty (DerivedCategory.Q.obj P ≅ E₃)))) :
    CompactSpace D.X ∨ (∀ C ∈ irreducibleComponents D.X, IsCompact C) ∨
      (∃ P : CochainComplex (OXMod.{u, u, u} D.X.toRingedSpace) ℤ,
        IsLocallyBoundedFiniteLocallyFree P ∧ Nonempty (DerivedCategory.Q.obj P ≅ E₂)) ∨
      (∃ (X' : Scheme.{u}) (a' : X' ⟶ D.base.S) (f : D.X ⟶ X')
          (E' : DerivedCategory (OXMod.{u, u, u} X'.toRingedSpace)),
        LocallyOfFiniteType a' ∧ f ≫ a' = D.a ∧
          Cohomology.PerfectComplexes.IsPerfect (X := X'.toRingedSpace) E' ∧
          Nonempty ((derivedPullback f.toLRSHom.toShHom).obj E' ≅ E₂) ∧
          ∀ C ∈ irreducibleComponents X', IsCompact C) := by
  rcases h with h | h | ⟨hc₁, hc₃⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · obtain ⟨P, hP, ⟨e'⟩⟩ := exists_isLocallyBoundedFiniteLocallyFree_biprod E₁ E₃ hc₁ hc₃
    exact Or.inr (Or.inr (Or.inl ⟨P, hP, ⟨e' ≪≫ e.symm⟩⟩))

end Complexes

end Stacks.Chow

end
