module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FrobeniusAlphaPCoverSmooth
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.NoetherianSpace
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.Topology.Dimension.Krull
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A smooth stratum in a closed subset of a variety

Let `W` be a scheme locally of finite type over a perfect field `k` and `Z ⊆ W` a nonempty closed
subset. Then there are an open `Y` of `W` meeting `Z` and a closed immersion `i : T → Y` with
image `Z ∩ Y` and `T` nonempty and smooth of some relative dimension `e'` over `k`. If moreover
`W` is noetherian of dimension at most `e` and `Z` has empty interior, then `e' < e`, since a
closed subset with empty interior of a noetherian space has smaller dimension.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_lt_of_isClosed_of_interior_eq_empty`.
* `AlgebraicGeometry.exists_smoothOfRelativeDimension_closedImmersion_of_isClosed`.
* `AlgebraicGeometry.topologicalKrullDim_le_of_isOpen_of_irreducibleSpace`: an irreducible scheme
  locally of finite type over a field has dimension at most that of any nonempty open.
-/

@[expose] public section

open CategoryTheory Topology TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A closed subset with empty interior of a noetherian space has smaller dimension**, and so
does every space inducing into it: if `X` is noetherian of dimension at most `n`, `Z ⊆ X` is
closed with empty interior and `g : Y → X` is inducing with image in `Z`, then `dim Y < n`. -/
theorem topologicalKrullDim_lt_of_isClosed_of_interior_eq_empty {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [NoetherianSpace X] {Z : Set X} (hZ : IsClosed Z)
    (hint : interior Z = ∅) {n : ℕ} (hdim : topologicalKrullDim X ≤ n) {g : Y → X}
    (hg : IsInducing g) (hgZ : Set.range g ⊆ Z) : topologicalKrullDim Y < n := by
  rw [show topologicalKrullDim Y = Order.krullDim (IrreducibleCloseds Y) from rfl,
    Order.krullDim_lt_coe_iff]
  intro p
  let φ : IrreducibleCloseds Y → IrreducibleCloseds X := IrreducibleCloseds.map g hg.continuous
  have hφ : StrictMono φ := IrreducibleCloseds.map_strictMono_of_isInducing hg
  let q := p.map φ hφ
  have hlastsub : (φ p.last : Set X) ⊆ Z := by
    rw [IrreducibleCloseds.coe_map]
    refine closure_minimal ?_ hZ
    rintro x ⟨y, -, rfl⟩
    exact hgZ ⟨y, rfl⟩
  obtain ⟨C, hC, hCcontains⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible (φ p.last : Set X) (φ p.last).2
  have hCnot : ¬ C ⊆ Z := by
    intro hCZ
    obtain ⟨O, hO, hOne, hOC⟩ :=
      NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC
    have : O ⊆ interior Z := interior_maximal (hOC.trans hCZ) hO
    rw [hint] at this
    exact hOne.ne_empty (Set.subset_empty_iff.1 this)
  let C' : IrreducibleCloseds X := ⟨C, hC.1, isClosed_of_mem_irreducibleComponents C hC⟩
  have hlt : q.last < C' := by
    refine lt_of_le_of_ne hCcontains fun heq => hCnot ?_
    have hc : C = (φ p.last : Set X) := congrArg SetLike.coe heq.symm
    rw [hc]
    exact hlastsub
  let r := q.snoc C' hlt
  have hrle : (r.length : WithBot ℕ∞) ≤ n := (Order.LTSeries.length_le_krullDim r).trans hdim
  have hrlen : r.length = p.length + 1 := rfl
  have hrlenNat : r.length ≤ n := by exact_mod_cast hrle
  omega

/-- **A smooth stratum in a closed subset.** For `W` locally of finite type over a perfect field
`k` and a nonempty closed `Z ⊆ W` of a noetherian `W`, there are an open `Y` of `W` and a
closed immersion `i : T → Y` with image `Z ∩ Y`, `T` nonempty, irreducible and smooth of some
relative dimension over `k`. -/
theorem exists_smoothOfRelativeDimension_closedImmersion_of_isClosed {k : Type u} [Field k]
    [PerfectField k] {W : Scheme.{u}} (f : W ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    [NoetherianSpace W] (Z : Set W) (hZ : IsClosed Z) (hne : Z.Nonempty) :
    ∃ (Y : W.Opens) (T : Scheme.{u}) (i : T ⟶ Y.toScheme) (_ : IsClosedImmersion i) (e' : ℕ),
      SmoothOfRelativeDimension e' (i ≫ Y.ι ≫ f) ∧ Nonempty T ∧ IrreducibleSpace T ∧
        Set.range (i ≫ Y.ι).base = Z ∩ (Y : Set W) := by
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨Z, hZ⟩ : Closeds W)
  let ιZ := I.subschemeι
  have hrange : Set.range ιZ.base = Z := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  let g : I.subscheme ⟶ Spec (.of k) := ιZ ≫ f
  obtain ⟨z₀, hz₀⟩ : ∃ z, ιZ.base z ∈ Z := by
    obtain ⟨x, hx⟩ := hne
    rw [← hrange] at hx
    obtain ⟨z, rfl⟩ := hx
    exact ⟨z, by rw [← hrange]; exact ⟨z, rfl⟩⟩
  have hdense := Scheme.Hom.dense_smoothLocus_of_perfectField g
  obtain ⟨z, hz⟩ := hdense.nonempty_iff.2 ⟨z₀⟩
  let S := g.smoothLocus
  have : Smooth (S.ι ≫ g) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq S.ι g]
    ext x
    simp only [Scheme.Hom.coe_preimage, Set.mem_preimage, SetLike.mem_coe, Opens.coe_top,
      Set.mem_univ, iff_true]
    exact x.2
  obtain ⟨V₀, hzV, e', he'⟩ := Smooth.exists_smoothOfRelativeDimension_nbhd (S.ι ≫ g) ⟨z, hz⟩
  have : NoetherianSpace V₀.toScheme :=
    (V₀.ι ≫ S.ι ≫ ιZ).isEmbedding.isInducing.noetherianSpace
  have : Nonempty V₀.toScheme := ⟨⟨⟨z, hz⟩, hzV⟩⟩
  obtain ⟨C, hC, -⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    ({⟨⟨z, hz⟩, hzV⟩} : Set V₀.toScheme) isIrreducible_singleton
  obtain ⟨O, hO, hOne, hOC⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC
  let V : V₀.toScheme.Opens := ⟨O, hO⟩
  have hVirr : IrreducibleSpace V.toScheme :=
    Subtype.irreducibleSpace ⟨hOne, (hC.1.2.open_subset hO hOC)⟩
  have : SmoothOfRelativeDimension e' (V.ι ≫ V₀.ι ≫ S.ι ≫ g) := by
    rw [← zero_add e']; infer_instance
  let a : V.toScheme ⟶ W := V.ι ≫ V₀.ι ≫ S.ι ≫ ιZ
  have ha : IsOpen (Set.range (V.ι ≫ V₀.ι ≫ S.ι).base) :=
    (V.ι ≫ V₀.ι ≫ S.ι).isOpenEmbedding.isOpen_range
  obtain ⟨O, hO, hOpre⟩ := (ιZ.isClosedEmbedding.isInducing.isOpen_iff).1 ha
  let Y : W.Opens := ⟨O, hO⟩
  have hra : Set.range a.base = Z ∩ (Y : Set W) := by
    change Set.range ((V.ι ≫ V₀.ι ≫ S.ι) ≫ ιZ).base = _
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, ← hOpre,
      Set.image_preimage_eq_inter_range, hrange, Set.inter_comm]
    rfl
  have haY : Set.range a.base ⊆ Set.range Y.ι.base := by
    rw [Scheme.Opens.range_ι, hra]
    exact Set.inter_subset_right
  let i : V.toScheme ⟶ Y.toScheme := IsOpenImmersion.lift Y.ι a haY
  have hi : i ≫ Y.ι = a := IsOpenImmersion.lift_fac _ _ _
  have : IsPreimmersion (i ≫ Y.ι) := by rw [hi]; infer_instance
  have : IsPreimmersion i := IsPreimmersion.of_comp i Y.ι
  have hri : Set.range i.base = Y.ι.base ⁻¹' Z := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      have : (i ≫ Y.ι).base x ∈ Set.range a.base := by rw [hi]; exact ⟨x, rfl⟩
      rw [hra] at this
      exact this.1
    · intro hy
      have hy' : Y.ι.base y ∈ Set.range a.base := by
        rw [hra]
        exact ⟨hy, y.2⟩
      obtain ⟨x, hx⟩ := hy'
      refine ⟨x, Y.ι.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, hi, hx]
  have : IsClosedImmersion i := .of_isPreimmersion _ (by rw [hri]; exact hZ.preimage Y.ι.continuous)
  refine ⟨Y, V.toScheme, i, this, e', ?_, ⟨⟨hOne.some, hOne.some_mem⟩⟩, hVirr, by rw [hi, hra]⟩
  rw [← Category.assoc, hi]
  exact ‹SmoothOfRelativeDimension e' (V.ι ≫ V₀.ι ≫ S.ι ≫ g)›

/-- **An irreducible scheme locally of finite type over a field has dimension at most that of any
nonempty open.** -/
@[sga "3 VIB 1.5" "partial"]
theorem topologicalKrullDim_le_of_isOpen_of_irreducibleSpace {k : Type u} [Field k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [IrreducibleSpace X]
    {U : Set X} (hU : IsOpen U) (hne : U.Nonempty) :
    topologicalKrullDim X ≤ topologicalKrullDim U := by
  obtain ⟨x, hx⟩ := hne
  have h1 : topologicalKrullDim X ≤ topologicalKrullDimAt X x := by
    rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents k X p x]
    have huniv : (Set.univ : Set X) ∈ irreducibleComponents X := by
      rw [irreducibleComponents_eq_singleton]; rfl
    refine le_trans (le_of_eq ?_) (le_iSup₂_of_le Set.univ ⟨huniv, Set.mem_univ x⟩ le_rfl)
    exact ((Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq).symm
  have h2 : topologicalKrullDimAt X x = topologicalKrullDimAt U ⟨x, hx⟩ :=
    hU.isOpenEmbedding_subtypeVal.topologicalKrullDimAt_eq ⟨x, hx⟩
  exact h1.trans (h2 ▸ topologicalKrullDimAt_le_topologicalKrullDim _)

end AlgebraicGeometry
