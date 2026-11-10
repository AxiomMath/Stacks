module

public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.NotDominant
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ClosedSubschemeRestriction
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChangeBirational.Basic
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.DiagonalUnit

/-!
# Composition of graphs of morphisms in mixed dimension

Let `k` be a field and let `f : Y ⟶ X` be a morphism of schemes smooth and separated over `k`.
Decompose `X = ∐_d X_d` and `Y = ∐_e Y_e` into their open and closed parts of constant dimension
(Stacks 02NM). The graph `Γ_f ⊆ X × Y` meets `X_d × Y_e` in the open and closed subscheme
`Y_e ∩ f⁻¹(X_d)` of `Y`, embedded by `(f, 1)`; this has dimension `e`, so its class lies in
`CH_e(X_d × Y_e) ⊗ ℚ`, the `(d, e)` block of `Corr⁰(X, Y)`. Collecting these blocks gives the
graph correspondence `[Γ_f] ∈ Corr⁰(X, Y)` of Stacks 0FG1 for schemes of mixed dimension.

Stacks 0FG3 shows that graphs compose, `[Γ_g] ∘ [Γ_f] = [Γ_{f ∘ g}]` for `g : Z ⟶ Y`, and the
proof of Stacks 0FG2 shows that `[Γ_{id_X}]` is the class `[Δ_X]` of the diagonal. Blockwise, the
`(d, n)` block of `[Γ_g] ∘ [Γ_f]` is `Σ_e [Γ_g ∩ (Y_e × Z_n)] ∘ [Γ_f ∩ (X_d × Y_e)]`. Each summand
is a proper intersection, computed by the formula of Stacks 0FFD as the class of the fibre product
over `Y_e`, which is the open and closed piece `Z_n ∩ g⁻¹(Y_e) ∩ (f ∘ g)⁻¹(X_d)` of
`Γ_{f ∘ g} ∩ (X_d × Z_n)`; and these pieces, for `e` varying, partition it.

As in `StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.DiagonalUnit`, the
intersection products are formed with a family of diagonal classes `Δ`, and the results hold for
every family satisfying the proper-intersection formula
`Stacks.WeilCohomology.DiagonalClassFamily.ProperIntersectionFormula`.

## Main definitions

* `Stacks.WeilCohomology.graphPiece`: the closed immersion `Γ_f ∩ (X_d × Y_e) ⟶ X_d × Y_e`.
* `Stacks.WeilCohomology.graphBlock`: its class, the `(d, e)` block of `[Γ_f]`.
* `Stacks.WeilCohomology.graphCorr`: the graph correspondence `[Γ_f] ∈ Corr⁰(X, Y)`, for `Y`
  quasi-compact.
* `Stacks.WeilCohomology.graphFibreι`: the open and closed immersion of the fibre product
  `(Γ_f ∩ (X_d × Y_e)) ×_{Y_e} (Γ_g ∩ (Y_e × Z_n))` into `Γ_{f ∘ g} ∩ (X_d × Z_n)`.

## Main results

* `Stacks.Chow.cycleAssociatedToClosedSubscheme_eq_sum_of_isOpenImmersion`: the cycle of a closed
  subscheme which is the disjoint union of finitely many open pieces is the sum of their cycles.
* `Stacks.WeilCohomology.graphCorr_eq_sum`: `[Γ_f]` is the sum of its blocks over any finite sets
  of indices containing those of the nonempty parts.
* `Stacks.WeilCohomology.graphCorr_id`: `[Γ_{id_X}] = [Δ_X]`.
* `Stacks.WeilCohomology.DiagonalClassFamily.ProperIntersectionFormula.comp_graphCorr`:
  `[Γ_g] ∘ [Γ_f] = [Γ_{f ∘ g}]` (Stacks 0FG3) for schemes of mixed dimension.

## Implementation notes

The source works with smooth projective schemes. Here `X`, `Y`, `Z` are smooth and separated over
`k`; the middle factor `Y` of the composition is proper, as composition requires, and `Y` and `Z`
are quasi-compact, so that each graph correspondence is a finite sum of blocks. The canonical
family of diagonal classes (Stacks 0FBR) is not yet constructed, so its instance of the
proper-intersection formula (Stacks 0FFD) is pending, and no declaration here carries a
`@[stacks]` attribute.

The block of `[Γ_f]` indexed by `(d, e)` is the class of `Stacks.WeilCohomology.graphPartMorphism`
for the morphism `Y_e ⟶ X` over the part `X_d`; its source is the open subscheme
`Y_e ∩ f⁻¹(X_d)` of `Y_e`. When `X` and `Y` have constant dimension the only nonzero block is the
equidimensional graph class `Stacks.WeilCohomology.graphCorrespondence`.

## References

* [Stacks Project, Tag 0FG1](https://stacks.math.columbia.edu/tag/0FG1)
* [Stacks Project, Tag 0FG2](https://stacks.math.columbia.edu/tag/0FG2)
* [Stacks Project, Tag 0FG3](https://stacks.math.columbia.edu/tag/0FG3)
* [Stacks Project, Tag 0FFD](https://stacks.math.columbia.edu/tag/0FFD)
* [Stacks Project, Section 0FFZ](https://stacks.math.columbia.edu/tag/0FFZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.Chow

/-- **The cycle of a closed subscheme is the sum of the cycles of its open and closed pieces.**
Let `c : W ⟶ T` be a closed subscheme and let `j_i : F_i ⟶ W`, `i ∈ s`, be open immersions with
pairwise disjoint images covering `W`, such that each `F_i ⟶ T` is a closed immersion. Then
`[W]_k = Σ_{i ∈ s} [F_i]_k`. A generic point of `W` lies in exactly one `F_i`, where it is again
a generic point with the same multiplicity, the multiplicity being the length of a local ring
which an open immersion does not change. -/
theorem cycleAssociatedToClosedSubscheme_eq_sum_of_isOpenImmersion {C : ChowSituation.{u}}
    {T W : Scheme.{u}} (p : T ⟶ C.S) [LocallyOfFiniteType p] (c : W ⟶ T) [IsClosedImmersion c]
    {ι : Type*} (s : Finset ι) {F : ι → Scheme.{u}} (j : ∀ i, F i ⟶ W)
    [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i ≫ c)]
    (hcover : ∀ w : W, ∃ i ∈ s, w ∈ Set.range (j i))
    (hdisj : ∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → Disjoint (Set.range (j i)) (Set.range (j i')))
    (k : ℤ) :
    ∑ i ∈ s, cycleAssociatedToClosedSubscheme C p (j i ≫ c) k =
      cycleAssociatedToClosedSubscheme C p c k := by
  classical
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
  simp only [AddSubgroup.val_finsetSum, Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
  by_cases hx : ∃ ξ : genericPoints W, c ξ.1 = x ∧ relativeDimension C.dimensionFunction p x = k
  · obtain ⟨ξ, rfl, hk⟩ := hx
    obtain ⟨i₀, hi₀, ζ, hζ⟩ := hcover ξ.1
    have hζgen : ζ ∈ genericPoints (F i₀) :=
      mem_genericPoints_source_of_isOpenImmersion (j i₀) (by rw [hζ]; exact ξ.2)
    rw [Finset.sum_eq_single_of_mem i₀ hi₀]
    · have h₁ := cycleAssociatedToClosedSubscheme_apply C p (j i₀ ≫ c) k ⟨ζ, hζgen⟩
        (by rwa [Scheme.Hom.comp_apply, hζ])
      rw [Scheme.Hom.comp_apply, hζ] at h₁
      rw [h₁, cycleAssociatedToClosedSubscheme_apply C p c k ξ hk]
      exact componentMultiplicity_eq_of_isOpenImmersion (j i₀ ≫ c) c (j i₀) ⟨ζ, hζgen⟩ ξ hζ
    · intro i hi hne
      refine cycleAssociatedToClosedSubscheme_apply_eq_zero C p _ k _ ?_
      rintro ⟨η, hη, -⟩
      rw [Scheme.Hom.comp_apply] at hη
      have hηξ : j i η.1 = ξ.1 := c.isClosedEmbedding.injective hη
      exact Set.disjoint_left.1 (hdisj i hi i₀ hi₀ hne) ⟨η.1, hηξ.trans hζ.symm⟩ ⟨ζ, rfl⟩
  · rw [cycleAssociatedToClosedSubscheme_apply_eq_zero C p c k x hx]
    refine Finset.sum_eq_zero fun i _ ↦ cycleAssociatedToClosedSubscheme_apply_eq_zero C p _ k x ?_
    rintro ⟨η, hη, hk⟩
    exact hx ⟨⟨j i η.1, mem_genericPoints_target_of_isOpenImmersion (j i) η.2⟩,
      by rwa [← Scheme.Hom.comp_apply], hk⟩

end Stacks.Chow

namespace Stacks.WeilCohomology

open Stacks.Chow

/-! ### The blocks of the graph -/

section Blocks

variable (k : Type u) [Field k] {X Y Z : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sY : Y ⟶ (fieldChowSituation k).S)
  (sZ : Z ⟶ (fieldChowSituation k).S)
  [Smooth sX] [Smooth sY] [Smooth sZ] [IsSeparated sX] [IsSeparated sY] [IsSeparated sZ]

/-- The graph of a morphism over the part `X_d` of its target is a closed immersion. -/
instance isClosedImmersion_graphPartMorphism_dimPart {T : Scheme.{u}}
    (sT : T ⟶ (fieldChowSituation k).S) (f : T ⟶ X) (hf : f ≫ sX = sT) (d : ℕ) :
    IsClosedImmersion (graphPartMorphism sX sT f hf (dimPart sX d)) :=
  isClosedImmersion_graphPartMorphism sX sT f hf ((isClopenDecomposition_dimPart sX).isClopen d)

/-- Followed by the second projection, the graph of a morphism over an open part of its target is
the inclusion of the preimage of that part, an open immersion. -/
instance isOpenImmersion_graphPartMorphism_snd {T : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pT : T ⟶ Spec (.of k)) (f : T ⟶ X) (hf : f ≫ pX = pT)
    (U : X.Opens) :
    IsOpenImmersion (graphPartMorphism pX pT f hf U ≫ pullback.snd (U.ι ≫ pX) pT) := by
  rw [graphPartMorphism_snd]
  infer_instance

/-- **`Γ_f ∩ (X_d × Y_e)`**: for `f : Y ⟶ X`, the closed immersion of the open and closed
subscheme `Y_e ∩ f⁻¹(X_d)` of `Y_e` into `X_d × Y_e` by `(f, 1)`. -/
abbrev graphPiece (f : Y ⟶ X) (hf : f ≫ sX = sY) (d e : ℕ) :
    (((dimPart sY e).ι ≫ f) ⁻¹ᵁ dimPart sX d).toScheme ⟶
      (Limits.pullback (partBase sX d) (partBase sY e) : Scheme.{u}) :=
  graphPartMorphism sX (partBase sY e) ((dimPart sY e).ι ≫ f) (by rw [Category.assoc, hf])
    (dimPart sX d)

omit [IsSeparated sX] [IsSeparated sY] in
/-- The second coordinate of `Γ_f ∩ (X_d × Y_e) ⟶ X_d × Y_e` is the inclusion into `Y_e`. -/
@[reassoc (attr := simp)]
theorem graphPiece_snd (f : Y ⟶ X) (hf : f ≫ sX = sY) (d e : ℕ) :
    graphPiece k sX sY f hf d e ≫ pullback.snd (partBase sX d) (partBase sY e) =
      (((dimPart sY e).ι ≫ f) ⁻¹ᵁ dimPart sX d).ι :=
  graphPartMorphism_snd _ _ _ _ _

omit [IsSeparated sX] [IsSeparated sY] in
/-- The first coordinate of `Γ_f ∩ (X_d × Y_e) ⟶ X_d × Y_e` is the restriction of `f`. -/
@[reassoc (attr := simp)]
theorem graphPiece_fst (f : Y ⟶ X) (hf : f ≫ sX = sY) (d e : ℕ) :
    graphPiece k sX sY f hf d e ≫ pullback.fst (partBase sX d) (partBase sY e) =
      ((dimPart sY e).ι ≫ f) ∣_ dimPart sX d :=
  graphPartMorphism_fst _ _ _ _ _

omit [IsSeparated sX] [IsSeparated sY] in
/-- `Γ_f ∩ (X_d × Y_e)` lies over `k` as the open subscheme `Y_e ∩ f⁻¹(X_d)` of `Y_e`. -/
theorem graphPiece_prodBase (f : Y ⟶ X) (hf : f ≫ sX = sY) (d e : ℕ) :
    graphPiece k sX sY f hf d e ≫ prodBase (partBase sX d) (partBase sY e) =
      (((dimPart sY e).ι ≫ f) ⁻¹ᵁ dimPart sX d).ι ≫ partBase sY e := by
  rw [show prodBase (partBase sX d) (partBase sY e) =
      pullback.snd (partBase sX d) (partBase sY e) ≫ partBase sY e from pullback.condition,
    graphPiece_snd_assoc]

omit [IsSeparated sY] in
/-- Every irreducible component of `Γ_f ∩ (X_d × Y_e)` has delta-dimension `e`. -/
theorem deltaDimension_graphPiece (f : Y ⟶ X) (hf : f ≫ sX = sY) (d e : ℕ)
    (T : irreducibleComponents (((dimPart sY e).ι ≫ f) ⁻¹ᵁ dimPart sX d).toScheme) :
    deltaDimension (fieldChowSituation k)
      (graphPiece k sX sY f hf d e ≫ prodBase (partBase sX d) (partBase sY e))
      ⟨T, T.2.1, isClosed_of_mem_irreducibleComponents _ T.2⟩ = (e : ℤ) - 0 := by
  rw [deltaDimension_congr (graphPiece_prodBase k sX sY f hf d e), sub_zero]
  exact deltaDimension_irreducibleComponent_of_relativeDimension k _ e
    (RelativeDimension.comp_isOpenImmersion _ _ (relativeDimension_partBase sY e)) T

/-- **The `(d, e)` block of the graph correspondence**: the class of `Γ_f ∩ (X_d × Y_e)` in
`CH_e(X_d × Y_e) ⊗ ℚ`, the summand of `Corr⁰(X, Y)` indexed by `(d, e)`. -/
def graphBlock (f : Y ⟶ X) (hf : f ≫ sX = sY) (d e : ℕ) :
    Correspondence (fieldChowSituation k) (partBase sX d) (partBase sY e) e 0 :=
  (1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
    (prodBase (partBase sX d) (partBase sY e)) (graphPiece k sX sY f hf d e) ((e : ℤ) - 0))

omit [IsSeparated sY] in
/-- The block `(d, e)` of the graph vanishes when `f` maps no point of `Y_e` into `X_d`. -/
theorem graphBlock_eq_zero (f : Y ⟶ X) (hf : f ≫ sX = sY) {d e : ℕ}
    (h : ∀ y : Y, y ∈ dimPart sY e → f y ∉ dimPart sX d) :
    graphBlock k sX sY f hf d e = 0 := by
  have : IsEmpty (((dimPart sY e).ι ≫ f) ⁻¹ᵁ dimPart sX d).toScheme :=
    ⟨fun x ↦ h x.1.1 x.1.2 x.2⟩
  rw [graphBlock, cycleAssociatedToClosedSubscheme_eq_zero_of_isEmpty, QuotientAddGroup.mk_zero,
    TensorProduct.tmul_zero]

omit [IsSeparated sX] in
/-- For `Y` quasi-compact, `f` maps `Y` into finitely many of the parts `X_d`. -/
theorem finite_setOf_nonempty_preimage_dimPart [CompactSpace Y] (f : Y ⟶ X) :
    {d | (f ⁻¹ᵁ dimPart sX d : Set Y).Nonempty}.Finite := by
  have hlf : LocallyFinite fun d ↦ (dimPart sX d : Set X) :=
    Stacks.Topology.locallyFinite_of_disjoint_open_cover _ (fun d ↦ (dimPart sX d).2)
      (isClopenDecomposition_dimPart sX).exists_mem fun _ _ hij ↦
        TopologicalSpace.Opens.coe_disjoint.2 ((isClopenDecomposition_dimPart sX).disjoint _ _ hij)
  refine (hlf.finite_nonempty_inter_compact (isCompact_range f.continuous)).subset ?_
  rintro d ⟨y, hy⟩
  exact ⟨f y, hy, y, rfl⟩

/-- **The graph correspondence** `[Γ_f] ∈ Corr⁰(X, Y)` of a morphism `f : Y ⟶ X` over `k`, for
`Y` quasi-compact (Stacks 0FG1): on the decompositions `X = ∐_d X_d` and `Y = ∐_e Y_e` into
equidimensional parts, its `(d, e)` block is the class of `Γ_f ∩ (X_d × Y_e)` in
`CH_e(X_d × Y_e) ⊗ ℚ`. Only finitely many blocks are nonzero, and the sum runs over them. -/
def graphCorr [QuasiCompact sY] (f : Y ⟶ X) (hf : f ≫ sX = sY) : Corr k sX sY 0 :=
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  ∑ d ∈ (finite_setOf_nonempty_preimage_dimPart k sX f).toFinset,
    ∑ e ∈ (finite_setOf_nonempty_dimPart sY).toFinset,
      DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e (graphBlock k sX sY f hf d e))

omit [IsSeparated sY] in
/-- `[Γ_f]` is the sum of its blocks over any finite sets of indices containing the indices of
the parts `X_d` met by `f(Y)` and of the nonempty parts `Y_e`. -/
theorem graphCorr_eq_sum [QuasiCompact sY] (f : Y ⟶ X) (hf : f ≫ sX = sY) {D E : Finset ℕ}
    (hD : ∀ d, (f ⁻¹ᵁ dimPart sX d : Set Y).Nonempty → d ∈ D)
    (hE : ∀ e, (dimPart sY e : Set Y).Nonempty → e ∈ E) :
    graphCorr k sX sY f hf = ∑ d ∈ D, ∑ e ∈ E,
      DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e (graphBlock k sX sY f hf d e)) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  unfold graphCorr
  refine (Finset.sum_subset (fun d hd ↦ hD d
      ((finite_setOf_nonempty_preimage_dimPart k sX f).mem_toFinset.1 hd)) fun d _ hd ↦ ?_).trans
    (Finset.sum_congr rfl fun d _ ↦ Finset.sum_subset (fun e he ↦ hE e
      ((finite_setOf_nonempty_dimPart sY).mem_toFinset.1 he)) fun e _ he ↦ ?_)
  · refine Finset.sum_eq_zero fun e _ ↦ ?_
    rw [graphBlock_eq_zero k sX sY f hf fun y _ hy ↦
      hd ((finite_setOf_nonempty_preimage_dimPart k sX f).mem_toFinset.2 ⟨y, hy⟩), map_zero,
      map_zero]
  · rw [graphBlock_eq_zero k sX sY f hf fun y hy _ ↦
      he ((finite_setOf_nonempty_dimPart sY).mem_toFinset.2 ⟨y, hy⟩), map_zero, map_zero]

/-- The diagonal block of the graph of the identity is the class of the diagonal of `X_d`. -/
theorem graphBlock_id_self (d : ℕ) :
    graphBlock k sX sX (𝟙 X) (Category.id_comp sX) d d =
      graphCorrespondence (partBase sX d) (partBase sX d) (𝟙 _) (Category.id_comp _) d := by
  set A := ((dimPart sX d).ι ≫ 𝟙 X) ⁻¹ᵁ dimPart sX d with hA
  have hrange : Set.range A.ι = Set.range (𝟙 (dimPart sX d).toScheme) := by
    rw [Scheme.Opens.range_ι]
    refine (Set.eq_univ_of_forall fun x ↦ ?_).trans (Set.range_id).symm
    simp [hA]
  have hcomp : (IsOpenImmersion.isoOfRangeEq A.ι (𝟙 _) hrange).hom ≫
      graphMorphism (partBase sX d) (partBase sX d) (𝟙 _) (Category.id_comp _) =
        graphPiece k sX sX (𝟙 X) (Category.id_comp sX) d d := by
    have hι : (IsOpenImmersion.isoOfRangeEq A.ι (𝟙 _) hrange).hom = A.ι := by
      simpa using IsOpenImmersion.isoOfRangeEq_hom_fac A.ι (𝟙 _) hrange
    rw [hι]
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, graphMorphism_fst, Category.comp_id, graphPiece_fst,
        ← cancel_mono (dimPart sX d).ι, morphismRestrict_ι]
      exact ((Category.assoc _ _ _).symm.trans (Category.comp_id _)).symm
    · rw [Category.assoc, graphMorphism_snd, Category.comp_id, graphPiece_snd]
  have := isClosedImmersion_graphMorphism (partBase sX d) (partBase sX d) (𝟙 _)
    (Category.id_comp _)
  rw [graphBlock, graphCorrespondence,
    cycleAssociatedToClosedSubscheme_eq_of_iso _ _ _ _ _ hcomp]

end Blocks

/-! ### The fibre product of two graph pieces -/

section Fibre

variable (k : Type u) [Field k] {X Y Z : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sY : Y ⟶ (fieldChowSituation k).S)
  (sZ : Z ⟶ (fieldChowSituation k).S)
  [Smooth sX] [Smooth sY] [Smooth sZ] [IsSeparated sX] [IsSeparated sY] [IsSeparated sZ]
  (f : Y ⟶ X) (hf : f ≫ sX = sY) (g : Z ⟶ Y) (hg : g ≫ sY = sZ) (d e n : ℕ)

omit [IsSeparated sX] [IsSeparated sY] [IsSeparated sZ] in
/-- The two maps `A ×_{Y_e} B ⟶ X` through `A = Γ_f ∩ (X_d × Y_e)` and through
`B = Γ_g ∩ (Y_e × Z_n)` agree. -/
theorem graphFibre_condition :
    pullback.snd (graphPiece k sX sY f hf d e ≫ pullback.snd _ _)
        (graphPiece k sY sZ g hg e n ≫ pullback.fst _ _) ≫
      (((dimPart sZ n).ι ≫ g) ⁻¹ᵁ dimPart sY e).ι ≫ (dimPart sZ n).ι ≫ g ≫ f =
    pullback.fst (graphPiece k sX sY f hf d e ≫ pullback.snd _ _)
        (graphPiece k sY sZ g hg e n ≫ pullback.fst _ _) ≫
      (((dimPart sY e).ι ≫ f) ⁻¹ᵁ dimPart sX d).ι ≫ (dimPart sY e).ι ≫ f := by
  have h₁ := pullback.condition (f := graphPiece k sX sY f hf d e ≫ pullback.snd _ _)
    (g := graphPiece k sY sZ g hg e n ≫ pullback.fst _ _)
  simp only [graphPiece, graphPartMorphism_snd, graphPartMorphism_fst] at h₁
  rw [reassoc_of% h₁, morphismRestrict_ι_assoc, Category.assoc]

omit [IsSeparated sX] [IsSeparated sY] [IsSeparated sZ] in
/-- The image of `A ×_{Y_e} B ⟶ B ⟶ Z_n` lies in `Z_n ∩ (f ∘ g)⁻¹(X_d)`. -/
theorem range_graphFibre_subset :
    Set.range (pullback.snd (graphPiece k sX sY f hf d e ≫ pullback.snd _ _)
        (graphPiece k sY sZ g hg e n ≫ pullback.fst _ _) ≫
      (((dimPart sZ n).ι ≫ g) ⁻¹ᵁ dimPart sY e).ι) ⊆
      Set.range (((dimPart sZ n).ι ≫ g ≫ f) ⁻¹ᵁ dimPart sX d).ι := by
  rintro _ ⟨w, rfl⟩
  rw [Scheme.Opens.range_ι]
  have h := congrArg (fun φ ↦ φ w) (graphFibre_condition k sX sY sZ f hf g hg d e n)
  simp only [Scheme.Hom.comp_apply] at h
  have hw := (pullback.fst (graphPiece k sX sY f hf d e ≫ pullback.snd _ _)
    (graphPiece k sY sZ g hg e n ≫ pullback.fst _ _) w).2
  simp only [Scheme.Hom.mem_preimage, Scheme.Hom.comp_apply] at hw
  simp only [SetLike.mem_coe, Scheme.Hom.mem_preimage, Scheme.Hom.comp_apply]
  rwa [h]

/-- **The fibre product of two graph pieces as a piece of the graph of the composite**: the open
immersion of `(Γ_f ∩ (X_d × Y_e)) ×_{Y_e} (Γ_g ∩ (Y_e × Z_n))` into
`Γ_{f ∘ g} ∩ (X_d × Z_n) = Z_n ∩ (f ∘ g)⁻¹(X_d)`, through the second factor. -/
def graphFibreι :
    compositionFibre (graphPiece k sX sY f hf d e) (graphPiece k sY sZ g hg e n) ⟶
      (((dimPart sZ n).ι ≫ g ≫ f) ⁻¹ᵁ dimPart sX d).toScheme :=
  IsOpenImmersion.lift (((dimPart sZ n).ι ≫ g ≫ f) ⁻¹ᵁ dimPart sX d).ι
    (pullback.snd _ _ ≫ (((dimPart sZ n).ι ≫ g) ⁻¹ᵁ dimPart sY e).ι)
    (range_graphFibre_subset k sX sY sZ f hf g hg d e n)

omit [IsSeparated sX] [IsSeparated sY] [IsSeparated sZ] in
/-- The comparison map followed by the inclusion into `Z_n` is the second factor. -/
@[reassoc (attr := simp)]
theorem graphFibreι_ι :
    graphFibreι k sX sY sZ f hf g hg d e n ≫
        (((dimPart sZ n).ι ≫ g ≫ f) ⁻¹ᵁ dimPart sX d).ι =
      pullback.snd _ _ ≫ (((dimPart sZ n).ι ≫ g) ⁻¹ᵁ dimPart sY e).ι :=
  IsOpenImmersion.lift_fac _ _ _

/-- The comparison map is an open immersion: followed by the open immersion into `Z_n` it is the
base change of the open immersion `A ⟶ Y_e` followed by the inclusion of `B` into `Z_n`. -/
instance : IsOpenImmersion (graphFibreι k sX sY sZ f hf g hg d e n) := by
  have : IsOpenImmersion (graphFibreι k sX sY sZ f hf g hg d e n ≫
      (((dimPart sZ n).ι ≫ g ≫ f) ⁻¹ᵁ dimPart sX d).ι) := by
    rw [graphFibreι_ι]
    infer_instance
  exact IsOpenImmersion.of_comp _ (((dimPart sZ n).ι ≫ g ≫ f) ⁻¹ᵁ dimPart sX d).ι

omit [IsSeparated sX] [IsSeparated sY] [IsSeparated sZ] in
/-- A point of `Z_n ∩ (f ∘ g)⁻¹(X_d)` comes from `A ×_{Y_e} B` if and only if `g` maps it into
`Y_e`. -/
theorem mem_range_graphFibreι_iff (z : (((dimPart sZ n).ι ≫ g ≫ f) ⁻¹ᵁ dimPart sX d).toScheme) :
    z ∈ Set.range (graphFibreι k sX sY sZ f hf g hg d e n) ↔
      ((((dimPart sZ n).ι ≫ g ≫ f) ⁻¹ᵁ dimPart sX d).ι ≫ (dimPart sZ n).ι ≫ g) z ∈
        dimPart sY e := by
  constructor
  · rintro ⟨w, rfl⟩
    rw [← Scheme.Hom.comp_apply, graphFibreι_ι_assoc]
    have hw := (pullback.snd (graphPiece k sX sY f hf d e ≫ pullback.snd _ _)
      (graphPiece k sY sZ g hg e n ≫ pullback.fst _ _) w).2
    simp only [Scheme.Hom.comp_apply]
    exact hw
  · intro hz
    obtain ⟨b, hb⟩ : (((dimPart sZ n).ι ≫ g ≫ f) ⁻¹ᵁ dimPart sX d).ι z ∈
        Set.range (((dimPart sZ n).ι ≫ g) ⁻¹ᵁ dimPart sY e).ι := by
      rwa [Scheme.Opens.range_ι, SetLike.mem_coe, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply]
    obtain ⟨w, hw⟩ : b ∈ Set.range
        (pullback.snd (graphPiece k sX sY f hf d e ≫ pullback.snd _ _)
          (graphPiece k sY sZ g hg e n ≫ pullback.fst _ _)) := by
      rw [IsOpenImmersion.range_pullbackSnd, SetLike.mem_coe, Scheme.Hom.mem_preimage]
      change _ ∈ Set.range _
      rw [graphPiece_snd, graphPiece_fst, Scheme.Opens.range_ι, SetLike.mem_coe,
        Scheme.Hom.mem_preimage,
        ← Scheme.Hom.comp_apply, morphismRestrict_ι_assoc, Scheme.Hom.comp_apply, hb,
        ← Scheme.Hom.comp_apply, Category.assoc, ← Scheme.Hom.mem_preimage]
      exact z.2
    refine ⟨w, (((dimPart sZ n).ι ≫ g ≫ f) ⁻¹ᵁ dimPart sX d).ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, graphFibreι_ι, Scheme.Hom.comp_apply, hw, hb]

omit [IsSeparated sX] [IsSeparated sY] [IsSeparated sZ] in
/-- The image of `A ×_{Y_e} B` in `Z_n ∩ (f ∘ g)⁻¹(X_d)` is the preimage of `Y_e` under `g`. -/
theorem range_graphFibreι :
    Set.range (graphFibreι k sX sY sZ f hf g hg d e n) =
      ((((dimPart sZ n).ι ≫ g ≫ f) ⁻¹ᵁ dimPart sX d).ι ≫ (dimPart sZ n).ι ≫ g) ⁻¹'
        (dimPart sY e : Set Y) :=
  Set.ext fun z ↦ mem_range_graphFibreι_iff k sX sY sZ f hf g hg d e n z

/-- The comparison map is a closed immersion: it is an open immersion whose image, the preimage
of the open and closed part `Y_e`, is closed. -/
instance : IsClosedImmersion (graphFibreι k sX sY sZ f hf g hg d e n) :=
  IsClosedImmersion.of_isPreimmersion _ (by
    rw [range_graphFibreι]
    exact ((isClopenDecomposition_dimPart sY).isClopen e).isClosed.preimage
      (Scheme.Hom.continuous _))

omit [IsSeparated sX] [IsSeparated sY] [IsSeparated sZ] in
/-- The comparison map followed by `Γ_{f ∘ g} ∩ (X_d × Z_n) ⟶ X_d × Z_n` is the map
`A ×_{Y_e} B ⟶ X_d × Z_n`. -/
theorem graphFibreι_graphPiece :
    graphFibreι k sX sY sZ f hf g hg d e n ≫
        graphPiece k sX sZ (g ≫ f) (by rw [Category.assoc, hf, hg]) d n =
      compositionFibre.toProduct (graphPiece k sX sY f hf d e) (graphPiece k sY sZ g hg e n) := by
  refine pullback.hom_ext ?_ ?_
  · rw [← cancel_mono (dimPart sX d).ι]
    simp only [Category.assoc, graphPiece, graphPartMorphism_fst, morphismRestrict_ι,
      graphFibreι_ι_assoc, compositionFibre.toProduct, pullback.lift_fst]
    exact graphFibre_condition k sX sY sZ f hf g hg d e n
  · simp only [Category.assoc, graphPiece, graphPartMorphism_snd, graphFibreι_ι,
      compositionFibre.toProduct, pullback.lift_snd]

end Fibre

/-! ### Composition of graphs -/

section Composition

variable (k : Type u) [Field k] {X Y Z : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sY : Y ⟶ (fieldChowSituation k).S)
  (sZ : Z ⟶ (fieldChowSituation k).S)
  [Smooth sX] [Smooth sY] [Smooth sZ] [IsSeparated sX] [IsSeparated sY] [IsSeparated sZ]
  {Δ : DiagonalClassFamily k}

omit [IsSeparated sX] [IsSeparated sY] [IsSeparated sZ] in
/-- Composition of a pure block `c ∈ Corrʳ(X_d, Y_e)` with a finite sum of pure blocks
`c'_{e', m} ∈ Corrˢ(Y_{e'}, Z_m)`: only the blocks with `e' = e` contribute, and
`(Σ_{e', m} c'_{e', m}) ∘ c = Σ_m c'_{e, m} ∘ c`. -/
theorem comp_lof_lof_sum_sum [IsProper sY] (Δ : DiagonalClassFamily k) (r s : ℤ) (d e : ℕ)
    (c : Correspondence (fieldChowSituation k) (partBase sX d) (partBase sY e) e r)
    {E : Finset ℕ} (he : e ∈ E) (N : Finset ℕ)
    (c' : ∀ e' m : ℕ, Correspondence (fieldChowSituation k) (partBase sY e') (partBase sZ m) m s) :
    comp k sX sY sZ Δ r s (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e c))
        (∑ e' ∈ E, ∑ m ∈ N, DirectSum.lof ℚ ℕ _ e' (DirectSum.lof ℚ ℕ _ m (c' e' m))) =
      ∑ m ∈ N, DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ m
        (composition k (partBase sX d) (partBase sY e) (partBase sZ m) Δ
          (relativeDimension_partBase sX d) (relativeDimension_partBase sY e)
          (relativeDimension_partBase sZ m) r s c (c' e m))) := by
  rw [map_sum, Finset.sum_eq_single_of_mem e he, map_sum]
  · exact Finset.sum_congr rfl fun m _ ↦ comp_lof_lof_lof_lof k sX sY sZ Δ r s d e m _ _
  · intro e' _ hne
    rw [map_sum]
    exact Finset.sum_eq_zero fun m _ ↦
      comp_lof_lof_lof_of_ne k sX sY sZ Δ r s d e e' (Ne.symm hne) _ _

omit [IsSeparated sX] [IsSeparated sY] [IsSeparated sZ] in
/-- Composition of two finite sums of pure blocks, `c = Σ_{d, e} c_{d, e}` and
`c' = Σ_{e, m} c'_{e, m}` with the middle indices running over the same finite set:
`(c' ∘ c)_{d, m} = Σ_e c'_{e, m} ∘ c_{d, e}`. -/
theorem comp_sum_lof_lof [IsProper sY] (Δ : DiagonalClassFamily k) (r s : ℤ) (D E N : Finset ℕ)
    (c : ∀ d e : ℕ, Correspondence (fieldChowSituation k) (partBase sX d) (partBase sY e) e r)
    (c' : ∀ e m : ℕ, Correspondence (fieldChowSituation k) (partBase sY e) (partBase sZ m) m s) :
    comp k sX sY sZ Δ r s (∑ d ∈ D, ∑ e ∈ E, DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e (c d e)))
        (∑ e ∈ E, ∑ m ∈ N, DirectSum.lof ℚ ℕ _ e (DirectSum.lof ℚ ℕ _ m (c' e m))) =
      ∑ d ∈ D, ∑ m ∈ N, DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ m
        (∑ e ∈ E, composition k (partBase sX d) (partBase sY e) (partBase sZ m) Δ
          (relativeDimension_partBase sX d) (relativeDimension_partBase sY e)
          (relativeDimension_partBase sZ m) r s (c d e) (c' e m))) := by
  rw [map_sum (comp k sX sY sZ Δ r s), LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [map_sum (comp k sX sY sZ Δ r s), LinearMap.sum_apply, Finset.sum_congr rfl fun e he ↦
    comp_lof_lof_sum_sum k sX sY sZ Δ r s d e (c d e) he N c', Finset.sum_comm]
  exact Finset.sum_congr rfl fun m _ ↦ by rw [map_sum, map_sum]

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for the nested `DirectSum` module structures on the correspondence blocks
omit [IsSeparated sX] [IsSeparated sY] in
/-- Transport along an equality of degrees of a finite sum of pure blocks is blockwise. -/
theorem corrCongr_sum_lof_lof {r r' : ℤ} (h : r = r') (D E : Finset ℕ)
    (c : ∀ d e : ℕ, Correspondence (fieldChowSituation k) (partBase sX d) (partBase sY e) e r) :
    corrCongr k sX sY h (∑ d ∈ D, ∑ e ∈ E, DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e (c d e))) =
      ∑ d ∈ D, ∑ e ∈ E, DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e
        (correspondenceCongr k (partBase sX d) (partBase sY e) h (c d e))) := by
  simp only [map_sum, corrCongr_lof_lof]

/-- **Composition of two graph blocks.** For a family of diagonal classes satisfying the
proper-intersection formula, `[Γ_g ∩ (Y_e × Z_n)] ∘ [Γ_f ∩ (X_d × Y_e)]` is the class of the
piece `Z_n ∩ g⁻¹(Y_e) ∩ (f ∘ g)⁻¹(X_d)` of `Γ_{f ∘ g} ∩ (X_d × Z_n)`. Both graph pieces are open
in smooth schemes, so their local rings are Cohen–Macaulay, and their fibre product over `Y_e`
has dimension `n`, so the intersection is proper. -/
theorem DiagonalClassFamily.ProperIntersectionFormula.composition_graphBlock
    (hΔ : Δ.ProperIntersectionFormula) [IsProper sY] (f : Y ⟶ X) (hf : f ≫ sX = sY)
    (g : Z ⟶ Y) (hg : g ≫ sY = sZ) (d e n : ℕ) :
    composition k (partBase sX d) (partBase sY e) (partBase sZ n) Δ
        (relativeDimension_partBase sX d) (relativeDimension_partBase sY e)
        (relativeDimension_partBase sZ n) 0 0 (graphBlock k sX sY f hf d e)
        (graphBlock k sY sZ g hg e n) =
      (1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase (partBase sX d) (partBase sZ n))
        (graphFibreι k sX sY sZ f hf g hg d e n ≫
          graphPiece k sX sZ (g ≫ f) (by rw [Category.assoc, hf, hg]) d n)
        ((n : ℤ) - (0 + 0))) := by
  have hjc := graphFibreι_graphPiece k sX sY sZ f hf g hg d e n
  have : IsClosedImmersion (compositionFibre.toProduct (graphPiece k sX sY f hf d e)
      (graphPiece k sY sZ g hg e n)) := by
    rw [← hjc]
    infer_instance
  have hF : compositionFibre.toProduct (graphPiece k sX sY f hf d e)
      (graphPiece k sY sZ g hg e n) ≫ prodBase (partBase sX d) (partBase sZ n) =
        (graphFibreι k sX sY sZ f hf g hg d e n ≫
          (((dimPart sZ n).ι ≫ g ≫ f) ⁻¹ᵁ dimPart sX d).ι) ≫ partBase sZ n := by
    rw [← hjc, Category.assoc, graphPiece_prodBase, Category.assoc]
  rw [graphBlock, graphBlock, composition_tmul, one_mul,
    hΔ.compositionInt_closedSubscheme k (partBase sX d) (partBase sY e) (partBase sZ n)
      (relativeDimension_partBase sX d) (relativeDimension_partBase sY e)
      (relativeDimension_partBase sZ n) 0 0 (graphPiece k sX sY f hf d e)
      (graphPiece k sY sZ g hg e n)
      (deltaDimension_graphPiece k sX sY f hf d e) (deltaDimension_graphPiece k sY sZ g hg e n)
      (by
        rw [schemeDeltaDimension_congr _ hF, add_zero, sub_zero]
        exact schemeDeltaDimension_le_of_forall_irreducibleComponent _
          (deltaDimension_irreducibleComponent_of_relativeDimension k _ n
            (RelativeDimension.comp_isOpenImmersion _ _ (relativeDimension_partBase sZ n))))
      (fun _ _ ↦ ⟨isCohenMacaulayLocalRing_stalk_of_smooth k
          ((((dimPart sY e).ι ≫ f) ⁻¹ᵁ dimPart sX d).ι ≫ partBase sY e) _,
        isCohenMacaulayLocalRing_stalk_of_smooth k
          ((((dimPart sZ n).ι ≫ g) ⁻¹ᵁ dimPart sY e).ι ≫ partBase sZ n) _⟩),
    cycleAssociatedToClosedSubscheme_congr _ _ _ _ hjc.symm]

/-- **The `(d, n)` block of `[Γ_g] ∘ [Γ_f]`.** Summing the compositions of the graph blocks over
the parts `Y_e` gives the `(d, n)` block of `[Γ_{f ∘ g}]`: the pieces
`Z_n ∩ g⁻¹(Y_e) ∩ (f ∘ g)⁻¹(X_d)` partition `Γ_{f ∘ g} ∩ (X_d × Z_n)`. -/
theorem DiagonalClassFamily.ProperIntersectionFormula.sum_composition_graphBlock
    (hΔ : Δ.ProperIntersectionFormula) [IsProper sY] (f : Y ⟶ X) (hf : f ≫ sX = sY)
    (g : Z ⟶ Y) (hg : g ≫ sY = sZ) (d n : ℕ) {E : Finset ℕ}
    (hE : ∀ e, (dimPart sY e : Set Y).Nonempty → e ∈ E) :
    ∑ e ∈ E, composition k (partBase sX d) (partBase sY e) (partBase sZ n) Δ
        (relativeDimension_partBase sX d) (relativeDimension_partBase sY e)
        (relativeDimension_partBase sZ n) 0 0 (graphBlock k sX sY f hf d e)
        (graphBlock k sY sZ g hg e n) =
      correspondenceCongr k (partBase sX d) (partBase sZ n) (add_zero 0).symm
        (graphBlock k sX sZ (g ≫ f) (by rw [Category.assoc, hf, hg]) d n) := by
  rw [Finset.sum_congr rfl fun e _ ↦ hΔ.composition_graphBlock k sX sY sZ f hf g hg d e n,
    ← TensorProduct.tmul_sum]
  simp only [← QuotientAddGroup.mk'_apply, ← map_sum]
  rw [cycleAssociatedToClosedSubscheme_eq_sum_of_isOpenImmersion _ _ E
      (fun e ↦ graphFibreι k sX sY sZ f hf g hg d e n) (fun z ↦ ?_) (fun e _ e' _ hne ↦ ?_),
    graphBlock, correspondenceCongr_tmul, chowGroupDegreeEquiv_mk_cycleAssociatedToClosedSubscheme]
  · rfl
  · obtain ⟨e, he⟩ := (isClopenDecomposition_dimPart sY).exists_mem
      (((((dimPart sZ n).ι ≫ g ≫ f) ⁻¹ᵁ dimPart sX d).ι ≫ (dimPart sZ n).ι ≫ g) z)
    exact ⟨e, hE e ⟨_, he⟩, (mem_range_graphFibreι_iff k sX sY sZ f hf g hg d e n z).2 he⟩
  · rw [range_graphFibreι, range_graphFibreι]
    exact Set.disjoint_left.2 fun z hz hz' ↦
      hne ((isClopenDecomposition_dimPart sY).eq_of_mem hz hz')

/-- **Stacks 0FG3, functoriality of graphs in mixed dimension, for a family of diagonal classes
satisfying the proper-intersection formula.** For morphisms `f : Y ⟶ X` and `g : Z ⟶ Y` of schemes
smooth and separated over `k`, with `Y` proper and `Z` quasi-compact, the composition of the graph
correspondences is the graph correspondence of the composite: `[Γ_g] ∘ [Γ_f] = [Γ_{f ∘ g}]` in
`Corr⁰(X, Z)`, the degrees `0` and `0 + 0` being identified.

This is the statement of the source for the canonical family of diagonal classes once that
family is shown to satisfy `Stacks.WeilCohomology.DiagonalClassFamily.ProperIntersectionFormula`
(Stacks 0FFD); that instance is pending, as the canonical family is not yet constructed. -/
theorem DiagonalClassFamily.ProperIntersectionFormula.comp_graphCorr
    (hΔ : Δ.ProperIntersectionFormula) [IsProper sY] [QuasiCompact sZ] (f : Y ⟶ X)
    (hf : f ≫ sX = sY) (g : Z ⟶ Y) (hg : g ≫ sY = sZ) :
    comp k sX sY sZ Δ 0 0 (graphCorr k sX sY f hf) (graphCorr k sY sZ g hg) =
      corrCongr k sX sZ (add_zero 0).symm
        (graphCorr k sX sZ (g ≫ f) (by rw [Category.assoc, hf, hg])) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  have hD : ∀ d, (f ⁻¹ᵁ dimPart sX d : Set Y).Nonempty →
      d ∈ (finite_setOf_nonempty_preimage_dimPart k sX f).toFinset := fun _ ↦
    (finite_setOf_nonempty_preimage_dimPart k sX f).mem_toFinset.2
  have hE : ∀ e, (dimPart sY e : Set Y).Nonempty →
      e ∈ (finite_setOf_nonempty_dimPart sY).toFinset := fun _ ↦
    (finite_setOf_nonempty_dimPart sY).mem_toFinset.2
  have hN : ∀ m, (dimPart sZ m : Set Z).Nonempty →
      m ∈ (finite_setOf_nonempty_dimPart sZ).toFinset := fun _ ↦
    (finite_setOf_nonempty_dimPart sZ).mem_toFinset.2
  rw [graphCorr_eq_sum k sX sY f hf hD hE,
    graphCorr_eq_sum k sY sZ g hg (fun e ⟨z, hz⟩ ↦ hE e ⟨g z, hz⟩) hN,
    graphCorr_eq_sum k sX sZ (g ≫ f) _ (fun d ⟨z, hz⟩ ↦ hD d ⟨g z, hz⟩) hN,
    comp_sum_lof_lof, corrCongr_sum_lof_lof]
  exact Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun m _ ↦ by
    rw [hΔ.sum_composition_graphBlock k sX sY sZ f hf g hg d m hE]

/-- **The graph of the identity is the diagonal.** For `X` quasi-compact and smooth over `k`,
`[Γ_{id_X}] = [Δ_X]` in `Corr⁰(X, X)`: the graph of the identity meets `X_d × X_e` in the
diagonal of `X_d` when `d = e` and nowhere otherwise. -/
theorem graphCorr_id [QuasiCompact sX] :
    graphCorr k sX sX (𝟙 X) (Category.id_comp sX) = diagonalCorr k sX := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hmem : ∀ d, (dimPart sX d : Set X).Nonempty →
      d ∈ (finite_setOf_nonempty_dimPart sX).toFinset := fun _ ↦
    (finite_setOf_nonempty_dimPart sX).mem_toFinset.2
  rw [graphCorr_eq_sum k sX sX (𝟙 X) (Category.id_comp sX) (fun d ⟨y, hy⟩ ↦ hmem d ⟨y, hy⟩)
    hmem]
  unfold diagonalCorr
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [Finset.sum_eq_single_of_mem d hd fun e _ hne ↦ by
    rw [graphBlock_eq_zero k sX sX (𝟙 X) (Category.id_comp sX) fun y hy hy' ↦
      hne ((isClopenDecomposition_dimPart sX).eq_of_mem hy hy'), map_zero,
      map_zero], graphBlock_id_self]

end Composition

end Stacks.WeilCohomology

end
