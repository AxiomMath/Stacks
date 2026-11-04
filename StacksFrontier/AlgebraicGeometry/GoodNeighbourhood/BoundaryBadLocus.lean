module

public import StacksFrontier.AlgebraicGeometry.GoodNeighbourhood.BadLocus
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroCyclesSeparablePointsBertini

/-!
# The bad locus of the boundary of a smooth open has dimension at most `d - 2`

Let `X` be an integral scheme locally of finite type over a field `k`, containing a nonempty open
`W` smooth of relative dimension `d`, and let `Y` be the reduced closed subscheme on `X ∖ W`. Every
point of `Y` has dimension `δ ≤ d - 1`, and, when `k` is algebraically closed, every point `z` of
`Y` at which `Y` is not smooth of relative dimension `d - 1` has `δ(z) ≤ d - 2`.

The points of a closed subscheme `T` at which `T` is not smooth of relative dimension `r` form a
closed subset `AlgebraicGeometry.GoodNeighbourhood.notSmoothLocus` of the ambient scheme, the
image of the complement of the good locus.

## Main definitions

* `notSmoothLocus`: the closed set where `T` is not smooth of relative dimension `r`.

## Main results

* `mem_notSmoothLocus_iff`: a point lies in `notSmoothLocus` if and only if it lies in the
  support of `T` and `T` is not smooth of relative dimension `r` there.
* `relativeDimension_add_one_le_of_mem_support_vanishingIdeal`: the boundary has dimension at
  most `d - 1`.
* `relativeDimension_add_two_le_of_not_subschemeSmoothAt_vanishingIdeal`: its bad locus has
  dimension at most `d - 2`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace Stacks.Chow

universe u

namespace AlgebraicGeometry.GoodNeighbourhood

section NotSmoothLocus

variable {X S : Scheme.{u}} (f : X ⟶ S) (T : X.IdealSheafData) (r : ℕ)

/-- A point lies in the support of `T` if and only if it is the image of a point of `T`. -/
private theorem mem_support_iff_exists_subschemeι_eq {z : X} :
    z ∈ T.support ↔ ∃ y, T.subschemeι y = z := by
  rw [← SetLike.mem_coe, ← Scheme.IdealSheafData.range_subschemeι]
  rfl

/-- **A point of the good locus is a point where `T` is smooth of relative dimension `r`.** -/
theorem subschemeSmoothAt_of_mem_goodLocus (y : (goodLocus f T r).toScheme) :
    SubschemeSmoothAt f T r (T.subschemeι ((goodLocus f T r).ι y)) :=
  ⟨_, rfl, goodLocus f T r, y.2, smoothOfRelativeDimension_goodLocus f T r⟩

/-- **The locus where a closed subscheme is not smooth of relative dimension `r`**, as a closed
subset of the ambient scheme: the image of the complement of the good locus. -/
def notSmoothLocus : Closeds X :=
  ⟨T.subschemeι '' (goodLocus f T r : Set T.subscheme)ᶜ,
    T.subschemeι.isClosedEmbedding.isClosedMap _ (goodLocus f T r).isOpen.isClosed_compl⟩

/-- A point `z` lies in `notSmoothLocus f T r` if and only if it lies in the support of `T` and
`T` is not smooth of relative dimension `r` at `z`. -/
theorem mem_notSmoothLocus_iff {z : X} :
    z ∈ notSmoothLocus f T r ↔ z ∈ T.support ∧ ¬ SubschemeSmoothAt f T r z := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, fun h => ?_⟩
    · exact (mem_support_iff_exists_subschemeι_eq T).2 ⟨y, rfl⟩
    · obtain ⟨y', hy'⟩ := exists_mem_goodLocus_of_subschemeSmoothAt f T r h
      have : (goodLocus f T r).ι y' = y := T.subschemeι.isClosedEmbedding.injective hy'
      exact hy (this ▸ y'.2)
  · rintro ⟨hz, hns⟩
    obtain ⟨y, rfl⟩ := (mem_support_iff_exists_subschemeι_eq T).1 hz
    refine ⟨y, fun hy => hns ?_, rfl⟩
    exact subschemeSmoothAt_of_mem_goodLocus f T r ⟨y, hy⟩

end NotSmoothLocus

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))

/-- **The boundary of a nonempty smooth open of an integral scheme has dimension at most
`d - 1`.** -/
theorem relativeDimension_add_one_le_of_mem_support_vanishingIdeal [LocallyOfFiniteType p]
    [IsIntegral X] (W : X.Opens) [Nonempty W] (d : ℕ) [SmoothOfRelativeDimension d (W.ι ≫ p)]
    {z : X} (hz : z ∈ (Scheme.IdealSheafData.vanishingIdeal
      ⟨(W : Set X)ᶜ, W.isOpen.isClosed_compl⟩).support) :
    relativeDimension (fieldChowSituation k).dimensionFunction p z + 1 ≤ d := by
  have hgen := relativeDimension_genericPoint_eq_of_opens p W d
  have hgenW : genericPoint X ∈ W := by
    obtain ⟨w⟩ := ‹Nonempty W›
    exact ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr ⟨w.1, Set.mem_univ _, w.2⟩
  have hzW : z ∉ W := by
    have h := hz
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal] at h
    exact h
  have hne : z ≠ genericPoint X := fun h => hzW (h ▸ hgenW)
  have hmem : z ∈ closure ({genericPoint X} : Set X) := by
    rw [(genericPoint_spec X).def]; trivial
  have hlt : relativeDimension (fieldChowSituation k).dimensionFunction p z <
      relativeDimension (fieldChowSituation k).dimensionFunction p (genericPoint X) :=
    relativeDimension_lt_of_mem_closure_of_ne (fieldChowSituation k) p hmem hne
  omega

/-- **The bad locus of the boundary has dimension at most `d - 2`.** Over an algebraically closed
field, every point of the reduced boundary of a nonempty open of an integral scheme smooth of
relative dimension `d`, at which the boundary is not smooth of relative dimension `d - 1`, has
dimension at most `d - 2`. -/
theorem relativeDimension_add_two_le_of_not_subschemeSmoothAt_vanishingIdeal [IsAlgClosed k]
    [LocallyOfFiniteType p] [IsIntegral X] (W : X.Opens) [Nonempty W] (d : ℕ)
    [SmoothOfRelativeDimension d (W.ι ≫ p)] {z : X}
    (hzY : z ∈ (Scheme.IdealSheafData.vanishingIdeal
      ⟨(W : Set X)ᶜ, W.isOpen.isClosed_compl⟩).support)
    (hz : ¬ SubschemeSmoothAt p (Scheme.IdealSheafData.vanishingIdeal
      ⟨(W : Set X)ᶜ, W.isOpen.isClosed_compl⟩) (d - 1) z) :
    relativeDimension (fieldChowSituation k).dimensionFunction p z + 2 ≤ d := by
  set Y := Scheme.IdealSheafData.vanishingIdeal
    (⟨(W : Set X)ᶜ, W.isOpen.isClosed_compl⟩ : Closeds X)
  have hY : ∀ y ∈ Y.support,
      relativeDimension (fieldChowSituation k).dimensionFunction p y + 1 ≤ d :=
    fun y hy => relativeDimension_add_one_le_of_mem_support_vanishingIdeal p W d hy
  by_contra hlt
  have hz1 := hY z hzY
  apply hz
  obtain ⟨s, rfl⟩ := (mem_support_iff_exists_subschemeι_eq Y).1 hzY
  have hmax : ∀ η : Y.subscheme, η ⤳ s → η = s := by
    intro η hη
    by_contra hne
    have hlt' : relativeDimension (fieldChowSituation k).dimensionFunction p (Y.subschemeι s) <
        relativeDimension (fieldChowSituation k).dimensionFunction p (Y.subschemeι η) :=
      relativeDimension_lt_of_mem_closure_of_ne (fieldChowSituation k) p
        (specializes_iff_mem_closure.1 (hη.map Y.subschemeι.continuous))
        (fun h => hne (Y.subschemeι.isClosedEmbedding.injective h).symm)
    have := hY _ ((mem_support_iff_exists_subschemeι_eq Y).2 ⟨η, rfl⟩)
    omega
  have : IsReduced Y.subscheme := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have hcomp : closure ({s} : Set Y.subscheme) ∈ irreducibleComponents Y.subscheme := by
    obtain ⟨η, hη⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := s))
      isClosed_irreducibleComponent
    rw [← hmax η (hη.specializes mem_irreducibleComponent), hη.def]
    exact irreducibleComponent_mem_irreducibleComponents s
  have hfield := isField_stalk_of_closure_mem_irreducibleComponents (X := Y.subscheme) s hcomp
  have hreg : IsRegularLocalRing (Y.subscheme.presheaf.stalk s) := by
    let := hfield.toField
    infer_instance
  have hsm : InfinitesimalLifting.SmoothAt (Y.subschemeι ≫ p) s := by
    have hs : s ∈ {x : Y.subscheme | IsRegularLocalRing (Y.subscheme.presheaf.stalk x)} := hreg
    rw [← smoothAt_locus_eq_regular_locus k (Y.subschemeι ≫ p)] at hs
    exact hs
  refine subschemeSmoothAt_of_smoothAt p Y s hsm (d - 1) fun η hη _ => ?_
  rw [hmax η hη]
  have h0 := Stacks.Chow.BertiniChain.relativeDimension_nonneg_of_field k p (Y.subschemeι s)
  omega

end AlgebraicGeometry.GoodNeighbourhood

end
