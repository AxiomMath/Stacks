module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.JacobsonSpace
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Locus
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocusOpen
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.FibreComparison
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ResidueFieldMap
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Preliminaries for spreading out a geometrically connected open in a fibre

Four elementary facts used in the proof of Stacks Tag 055W are collected here: an open
subscheme of a geometrically reduced family is again geometrically reduced; an open of a fibre
of a flat family locally of finite presentation contains a point which is closed in that fibre
and at which the family is Cohen–Macaulay; an open of a fibre of a quasi-compact family locally
of finite presentation is cut out by a quasi-compact open of the total space contained in the
preimage of a prescribed open of the base; and an elementary étale neighbourhood may be refined
to an affine one.

## Main results

* `AlgebraicGeometry.ConnectedComponentSection.geometricallyReduced_comp_opens`
* `AlgebraicGeometry.ConnectedComponentSection.exists_closed_cohenMacaulay_point_mem_opens`
* `AlgebraicGeometry.ConnectedComponentSection.exists_isCompact_opens_preimage_fiber_eq`
* `AlgebraicGeometry.ConnectedComponentSection.exists_isAffine_elementary_refinement`

## Implementation notes

The Cohen–Macaulay locus of a flat family locally of finite presentation is open (Tag 045U) and
meets every fibre in a dense subset; a locally closed nonempty subset of a Jacobson space
contains a closed point of the ambient space, which gives the point of the second result.

The third result is a compactness argument: the given open of the fibre is quasi-compact,
because the fibre is a Noetherian space, so finitely many affine opens of the total space
suffice to cover it.

## References

* [Stacks Project, Tag 055W](https://stacks.math.columbia.edu/tag/055W)
* [Stacks Project, Tag 045U](https://stacks.math.columbia.edu/tag/045U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry.ConnectedComponentSection

/-- An open subscheme of a geometrically reduced family is geometrically reduced. -/
theorem geometricallyReduced_comp_opens {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Opens)
    [GeometricallyReduced f] : GeometricallyReduced (U.ι ≫ f) := by
  constructor
  intro K _ y Z fst snd h
  have hP : IsReduced (pullback f y) :=
    GeometricallyReduced.geometrically_isReduced (f := f) (K := K) y
      (pullback.fst f y) (pullback.snd f y) (IsPullback.of_hasPullback f y)
  let k : Z ⟶ pullback f y := h.isoPullback.hom ≫ (pullbackRightPullbackFstIso f y U.ι).inv ≫
    pullback.snd U.ι (pullback.fst f y)
  have hk : IsOpenImmersion k := by
    dsimp [k]
    infer_instance
  exact isReduced_of_isOpenImmersion k

/-- A nonempty open of a fibre of a flat family locally of finite presentation contains a point
which is closed in the fibre and at which the family is Cohen–Macaulay. -/
@[sga "3 VIA 1.1.2" "special case"]
theorem exists_closed_cohenMacaulay_point_mem_opens {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
    (T : (f.fiber s).Opens) [LocallyOfFinitePresentation f] [Flat f]
    (hT : (T : Set (f.fiber s)).Nonempty) :
    ∃ y : f.fiber s, y ∈ T ∧ y ∈ closedPoints (f.fiber s) ∧
      Scheme.Hom.IsCohenMacaulayAt f
        (fun y : S => isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f y)
        (f.fiberι s y) := by
  let hf : ∀ y : S, IsLocallyNoetherian (f.fiber y) := fun y =>
    isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f y
  let C : Set (f.fiber s) := (f.fiberι s) ⁻¹' {x : X | Scheme.Hom.IsCohenMacaulayAt f hf x}
  have hC : IsOpen C := (isOpen_setOf_isCohenMacaulayAt f).preimage (f.fiberι s).continuous
  have hInt : ((T : Set (f.fiber s)) ∩ C).Nonempty :=
    (dense_cohenMacaulayAt_fiber f s : Dense C).inter_open_nonempty _ T.2 hT
  obtain ⟨y, hy⟩ := nonempty_inter_closedPoints hInt (T.2.inter hC).isLocallyClosed
  exact ⟨y, hy.1.1, hy.2, hy.1.2⟩

/-- An open of a fibre of a quasi-compact family locally of finite presentation is the trace on
that fibre of a quasi-compact open of the total space, which may moreover be taken inside the
preimage of any prescribed open neighbourhood of the base point. -/
theorem exists_isCompact_opens_preimage_fiber_eq {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
    [LocallyOfFinitePresentation f] [QuasiCompact f] (T : (f.fiber s).Opens) (S₀ : S.Opens)
    (hs₀ : s ∈ S₀) :
    ∃ W : X.Opens, IsCompact (W : Set X) ∧ (f.fiberι s) ⁻¹ᵁ W = T ∧ W ≤ f ⁻¹ᵁ S₀ := by
  classical
  have : IsLocallyNoetherian (f.fiber s) :=
    isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f s
  have : IsNoetherian (f.fiber s) := AlgebraicGeometry.IsNoetherian.mk
  obtain ⟨O, hO, hpre⟩ := (f.fiberι s).isEmbedding.isInducing.isOpen_iff.mp T.2
  let O₀ : X.Opens := ⟨O, hO⟩ ⊓ f ⁻¹ᵁ S₀
  have hmemO₀ (x : T) : (f.fiberι s) x.1 ∈ O₀ := by
    refine ⟨?_, ?_⟩
    · change x.1 ∈ (f.fiberι s) ⁻¹' O
      rw [hpre]
      exact x.2
    · have hbase : f (f.fiberι s x.1) = s := (f.range_fiberι s).le ⟨x.1, rfl⟩
      change f (f.fiberι s x.1) ∈ S₀
      rw [hbase]
      exact hs₀
  choose A hAaff hAcov hAsub using fun x : T =>
    exists_isAffineOpen_mem_and_subset (U := O₀) (hmemO₀ x)
  let B (x : T) : (f.fiber s).Opens := (f.fiberι s) ⁻¹ᵁ A x
  have hcover : (T : Set (f.fiber s)) ⊆ ⋃ x : T, (B x : Set (f.fiber s)) := fun x hx =>
    Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hAcov ⟨x, hx⟩⟩
  obtain ⟨F, hF⟩ := (TopologicalSpace.NoetherianSpace.isCompact
    (T : Set (f.fiber s))).elim_finite_subcover (fun x : T => (B x : Set (f.fiber s)))
    (fun x => (B x).2) hcover
  let W : X.Opens := ⨆ x : {x : T // x ∈ F}, A x.1
  have hWsub : (W : Set X) ⊆ O₀ := by
    intro x hx
    obtain ⟨y, hy⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact hAsub y.1 hy
  refine ⟨W, ?_, ?_, fun x hx => (hWsub hx).2⟩
  · rw [TopologicalSpace.Opens.coe_iSup]
    exact isCompact_iUnion fun x : {x : T // x ∈ F} => (hAaff x.1).isCompact
  · ext x
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · have hmem : x ∈ (f.fiberι s) ⁻¹' O := (hWsub hx).1
      rwa [hpre] at hmem
    · obtain ⟨y, hyF, hy⟩ := Set.mem_iUnion₂.mp (hF hx)
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hyF⟩, hy⟩

/-- Every elementary étale neighbourhood is refined by an affine elementary étale
neighbourhood, by an open immersion. -/
theorem exists_isAffine_elementary_refinement {S : Scheme.{u}} {s : S}
    (U : EtaleNeighborhood S s) (hU : U.IsElementary) :
    ∃ (U' : EtaleNeighborhood S s) (j : U'.scheme ⟶ U.scheme), U'.IsElementary ∧
      IsAffine U'.scheme ∧ IsOpenImmersion j ∧ j ≫ U.toBase = U'.toBase ∧
        j U'.point = U.point := by
  obtain ⟨A, hAaff, hpoint, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := (⊤ : U.scheme.Opens)) (by simp)
  let p : A.toScheme := ⟨U.point, hpoint⟩
  have hp : A.ι p = U.point := rfl
  have hbase : IsIso (U.toBase.residueFieldMap (A.ι p)) := by
    rw [hp]
    exact (U.isElementary_iff).mp hU
  refine ⟨{ scheme := A.toScheme
            point := p
            toBase := A.ι ≫ U.toBase
            map_point := by rw [Scheme.Hom.comp_apply, hp]; exact U.map_point }, A.ι, ?_, hAaff,
    inferInstance, rfl, hp⟩
  rw [EtaleNeighborhood.isElementary_iff]
  exact isIso_residueFieldMap_comp A.ι U.toBase p inferInstance hbase

end AlgebraicGeometry.ConnectedComponentSection

end
