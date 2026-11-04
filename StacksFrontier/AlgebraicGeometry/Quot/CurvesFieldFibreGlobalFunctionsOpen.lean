module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesPrestableOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.DimensionLocallyConstant
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.FibreBettiZeroGlobalFunctions

/-!
# The open locus of `k = H⁰(X_k, 𝒪_{X_k})` on the fibres of a family of curves

For a family of curves `f : X → S`, the fibrewise condition "`k = H⁰(X_k, 𝒪_{X_k})` for every
morphism `Spec k → S` from the spectrum of a field"
(`AlgebraicGeometry.CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres`) satisfies condition
(o) of Stacks 0E0E, and it implies `f_*𝒪_X = 𝒪_S` universally (Stacks 0E6B, part (a)). These
are the two inputs `hopen` and `hpush` of the open substacks `Curves^{h0,1}`, `Curves_g`,
`Curves^{smooth,h0}`, … of the base, which this file supplies unconditionally.

The proof of the openness is the one of Stacks 0E6I: `k = H⁰(X_k, 𝒪_{X_k})` holds exactly when
`dim_k H⁰(X_k, 𝒪_{X_k}) ≤ 1` and the fibre is nonempty (a nonempty fibre has `H⁰ ≠ 0`, and a
nonzero `k`-algebra of dimension at most one is `k`). The first locus is open by the upper
semicontinuity of the `0`-th Betti number of the fibres (Stacks 0E0R at `i = 0`,
`AlgebraicGeometry.CurveFamily.isOpenCurvesLocus_hasH0RankLeOneOnFieldFibres_of_fibreBetti`); the
second is the locus where the fibre dimension is not `⊥`, open because the fibre dimension of a
flat, proper morphism of finite presentation is locally constant (Stacks 0D4R).

## Main results

* `AlgebraicGeometry.CurveFamily.hasUniversallyBijectiveGlobalFunctions_of_fieldFibres`:
  `k = H⁰(X_k, 𝒪)` on the fibres over fields gives `f_*𝒪_X = 𝒪_S` universally (Stacks 0E6B (a)).
* `AlgebraicGeometry.CurveFamily.isOpenCurvesLocus_hasNonemptyFibres`: condition (o) for having
  nonempty fibres.
* `AlgebraicGeometry.CurveFamily.isOpenCurvesLocus_hasBijectiveGlobalFunctionsOnFieldFibres`:
  condition (o) for `k = H⁰(X_k, 𝒪_{X_k})` on the fibres over fields.

## References

* [Stacks Project, Tag 0E6I](https://stacks.math.columbia.edu/tag/0E6I)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 0E0R](https://stacks.math.columbia.edu/tag/0E0R)
* [Stacks Project, Tag 0E6B](https://stacks.math.columbia.edu/tag/0E6B)
* [Stacks Project, Tag 0D4R](https://stacks.math.columbia.edu/tag/0D4R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **Stacks 0E6B, part (a), for a family of curves.** If `k = H⁰(X_k, 𝒪_{X_k})` for every
morphism `Spec k → S` from the spectrum of a field, then `f_*𝒪_X = 𝒪_S`, universally: the
structure maps of `f` and of all its base changes are isomorphisms
(`AlgebraicGeometry.Space.isIso_structureSharp_and_baseChange_of_bijective_algebraMap_fibre`). -/
theorem hasUniversallyBijectiveGlobalFunctions_of_fieldFibres (X : CurveFamily B hZ)
    (hX : HasBijectiveGlobalFunctionsOnFieldFibres B hZ X) :
    HasUniversallyBijectiveGlobalFunctions B hZ X :=
  hasUniversallyBijectiveGlobalFunctions_of_hasBijectiveGlobalFunctionsOnFieldFibres
    (fun f hf hfl hfp h => Space.isIso_structureSharp_and_baseChange_of_bijective_algebraMap_fibre
      B integerBase hZ f hf hfl hfp h) hX

/-- A family of curves has *nonempty fibres* when every point of its base has a point of the total
space over it, i.e. the fibre dimension is nowhere `⊥`: `AlgebraicGeometry.Space.fiberDimension`
is `⊥` exactly at the points outside the image (`Space.fiberDimension_eq_bot_iff`). -/
def HasNonemptyFibres (X : CurveFamily B hZ) : Prop :=
  ∀ s : Space.points B integerBase hZ (schemeSpace X.base).obj,
    Space.fiberDimension B integerBase hZ X.toBase.hom s ≠ ⊥

/-- **Condition (o) of Stacks 0E0E for having nonempty fibres.** The locus of points of the base
whose fibre is nonempty is the complement of the fibre of `⊥` of the fibre dimension, which is
locally constant for a flat, proper morphism of finite presentation (Stacks 0D4R); and a family
mapping to the given one has nonempty fibres exactly when its base maps into that locus. -/
theorem isOpenCurvesLocus_hasNonemptyFibres :
    IsOpenCurvesLocus B hZ (HasNonemptyFibres (B := B) (hZ := hZ)) := by
  refine IsOpenCurvesLocus.of_points fun G => ?_
  refine ⟨{s | Space.fiberDimension B integerBase hZ G.toBase.hom s = ⊥}ᶜ,
    ((Space.isLocallyConstant_fiberDimension B integerBase hZ G.total.property
      (schemeSpace G.base).property G.toBase.hom G.proper G.flat
        G.finitePresentation).isClosed_fiber ⊥).isOpen_compl, fun F a => ?_⟩
  unfold HasNonemptyFibres
  rw [fiberDimension_toBase_of_hom a, Set.range_subset_iff]
  rfl

/-- **`k = H⁰(X_k, 𝒪_{X_k})` on the fibres over fields, read on `dim_k H⁰` and nonemptiness.**
A fibre over a field `k` has `H⁰ = k` exactly when it is nonempty and `dim_k H⁰ ≤ 1`: a nonempty
fibre has nonzero global functions, a nonzero `k`-algebra of dimension at most one is `k`, and
conversely `H⁰ = k` is nonzero, so the fibre is nonempty (through Stacks 0E6B (a), which makes
`f_*𝒪_X = 𝒪_S` universal and hence `f` surjective). -/
theorem hasBijectiveGlobalFunctionsOnFieldFibres_iff (X : CurveFamily B hZ) :
    HasBijectiveGlobalFunctionsOnFieldFibres B hZ X ↔
      HasH0RankLeOneOnFieldFibres X ∧ HasNonemptyFibres X := by
  constructor
  · intro h
    refine ⟨fun p => (Space.toENat_rank_eq_one_of_bijective _
      ((Space.bijective_h0FibreAlgebraMap_iff B integerBase hZ X.toBase p).2 (h p))).le,
      fun s hs => (Space.fiberDimension_eq_bot_iff B integerBase hZ X.toBase.hom s).1 hs
        (exists_point_over_of_hasUniversallyBijectiveGlobalFunctions
          (hasUniversallyBijectiveGlobalFunctions_of_fieldFibres X h) s)⟩
  · rintro ⟨hR, hN⟩ p
    have hx : ∃ x : Space.points B integerBase hZ X.total.obj,
        Space.pointsMap B integerBase hZ X.total.obj X.toBase.hom x =
          p.class B integerBase hZ (yoneda.obj X.base) := by
      by_contra hne
      exact hN (p.class B integerBase hZ (yoneda.obj X.base))
        ((Space.fiberDimension_eq_bot_iff B integerBase hZ X.toBase.hom _).2
          fun ⟨x, hx⟩ => hne ⟨x, hx⟩)
    have := Space.nontrivial_globalFunctions_h0Fibre B integerBase hZ X.toBase p hx
    exact (Space.bijective_h0FibreAlgebraMap_iff B integerBase hZ X.toBase p).1
      (Space.bijective_of_toENat_rank_le_one _ (hR p))

/-- **Condition (o) of Stacks 0E0E for `k = H⁰(X_k, 𝒪_{X_k})` on the fibres over fields**,
unconditionally: the intersection of the open loci of `dim_k H⁰ ≤ 1` (Stacks 0E0R at `i = 0`) and
of nonempty fibres (Stacks 0D4R). -/
theorem isOpenCurvesLocus_hasBijectiveGlobalFunctionsOnFieldFibres :
    IsOpenCurvesLocus B hZ (HasBijectiveGlobalFunctionsOnFieldFibres B hZ) := by
  intro G
  obtain ⟨W, hW, hchar⟩ := (isOpenCurvesLocus_hasH0RankLeOneOnFieldFibres_of_fibreBetti.and
    isOpenCurvesLocus_hasNonemptyFibres) G
  exact ⟨W, hW, fun F a => (hasBijectiveGlobalFunctionsOnFieldFibres_iff F).trans (hchar F a)⟩

end CurveFamily

end AlgebraicGeometry

end
