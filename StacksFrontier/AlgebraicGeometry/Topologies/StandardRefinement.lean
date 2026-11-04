module

public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.Smooth.StandardRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.StandardCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.StandardRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.Zariski.StandardCovering

/-!
# Standard refinements of coverings of affine schemes

Every covering of an affine scheme in one of the five standard topologies — fppf, syntomic,
smooth, étale or Zariski — admits a refinement which is a *standard* covering for the same
topology: a finite family of affine schemes whose members have the standard affine form
attached to the topology.

## Main results

* `AlgebraicGeometry.exists_standardCovering_refinement`: a `τ`-covering of an affine scheme
  is refined by a `τ`-standard covering.

## Implementation notes

A covering family is a `CategoryTheory.PreZeroHypercover` whose presieve belongs to the
precoverage of the topology, and a refinement is a morphism of pre-zero-hypercovers over the
fixed affine target; this is the form in which the conclusion is used when comparing the big
and the affine sites. The refinement produced is indexed in the same universe as the given
family, which for the three middle topologies requires transporting an already-constructed
`Type u`-indexed standard covering along a bijection with a `ULift` of a `Fin`; that step is
isolated in `AlgebraicGeometry.IsStandardCovering.exists_reindex`.

The five cases are proved from the topology-specific refinement results already in the
library: Tag 020Q for Zariski, Tag 0222 for smooth and Tag 0228 for syntomic. In the fppf and
étale cases no separate refinement result is needed, since a flat locally-finitely-presented
or an étale morphism is open, so Mathlib's refinement of a quasi-compact cover by affines
applies directly.

## References

* [Stacks Project, Tag 03XA](https://stacks.math.columbia.edu/tag/03XA)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- A standard covering of an affine scheme can be reindexed, inside the universe of any
family it refines, so that it still refines that family. -/
public theorem IsStandardCovering.exists_reindex (τ : CoveringTopology)
    {T : Scheme.{u}} [IsAffine T] (U : PreZeroHypercover.{v} T)
    (W : PreZeroHypercover.{u} T) (r : W.Hom U)
    (h : IsStandardCovering τ W.X W.f) :
    ∃ (V : PreZeroHypercover.{v} T) (_ : V.Hom U), IsStandardCovering τ V.X V.f := by
  classical
  have := h.finite_index
  let : Fintype W.I₀ := Fintype.ofFinite W.I₀
  let e : W.I₀ ≃ Fin (Fintype.card W.I₀) := Fintype.equivFin W.I₀
  let ix : ULift.{v} (Fin (Fintype.card W.I₀)) → W.I₀ := fun i => e.symm i.down
  let V : PreZeroHypercover.{v} T :=
    { I₀ := ULift.{v} (Fin (Fintype.card W.I₀)), X i := W.X (ix i), f i := W.f (ix i) }
  refine ⟨V, ⟨fun i => r.s₀ (ix i), fun i => r.h₀ (ix i), fun i => r.w₀ (ix i)⟩, ?_⟩
  refine ⟨inferInstance, fun i => h.affine_source (ix i), ?_,
    fun i => by cases τ <;> exact h.standard (ix i)⟩
  refine Set.iUnion_eq_univ_iff.mpr fun x => ?_
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (h.jointly_surjective ▸ Set.mem_univ x)
  refine ⟨ULift.up (e i), ?_⟩
  show x ∈ Set.range (W.f (ix (ULift.up (e i))))
  rwa [show ix (ULift.up (e i)) = i from e.symm_apply_apply i]

/-- The members of a family whose presieve is a covering family jointly surject onto the target. -/
private theorem iUnion_range_eq_univ_of_mem_precoverage {P : MorphismProperty Scheme.{u}}
    {T : Scheme.{u}} {V : PreZeroHypercover.{v} T} (h : V.presieve₀ ∈ Scheme.precoverage P T) :
    (⋃ i, Set.range (V.f i)) = Set.univ :=
  Set.iUnion_eq_univ_iff.mpr ((Scheme.presieve₀_mem_precoverage_iff V).mp h).1

/-- **Stacks Project, Tag 03XA.** A covering of an affine scheme in one of the five standard
topologies can be refined by a standard covering in that topology. -/
@[stacks 03XA]
public theorem exists_standardCovering_refinement (τ : CoveringTopology)
    {T : Scheme.{u}} [IsAffine T] (U : PreZeroHypercover.{v} T)
    (hU : U.presieve₀ ∈ Scheme.precoverage (coveringMorphismProperty τ) T) :
    ∃ (V : PreZeroHypercover.{v} T) (_ : V.Hom U), IsStandardCovering τ V.X V.f := by
  classical
  cases τ with
  | fppf =>
      let Uc : T.Cover (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) :=
        { __ := U, mem₀ := by simpa [coveringMorphismProperty] using hU }
      have : MorphismProperty.RespectsLeft
          (@Flat ⊓ @LocallyOfFinitePresentation) @IsOpenImmersion :=
        ⟨fun i _ f hf => ⟨MorphismProperty.comp_mem @Flat i f inferInstance hf.1,
          MorphismProperty.comp_mem @LocallyOfFinitePresentation i f inferInstance hf.2⟩⟩
      have : QuasiCompactCover Uc.toPreZeroHypercover := by
        refine QuasiCompactCover.of_isOpenMap fun i => ?_
        have : Flat (Uc.f i) := (Uc.map_prop i).1
        have : LocallyOfFinitePresentation (Uc.f i) := (Uc.map_prop i).2
        exact isOpenMap_of_generalizingMap _ (Flat.generalizingMap _)
      obtain ⟨W, r, hfin, _⟩ := QuasiCompactCover.exists_hom Uc
      refine ⟨W.cover.toPreZeroHypercover, r, hfin,
        fun i => inferInstanceAs (IsAffine (Spec (W.X i))),
        iUnion_range_eq_univ_of_mem_precoverage W.cover.mem₀, fun i => ?_⟩
      have : IsAffine (W.cover.X i) := inferInstanceAs (IsAffine (Spec (W.X i)))
      exact ⟨(W.cover.map_prop i).1,
        FinitePresentation.mk (W.cover.map_prop i).2 inferInstance inferInstance⟩
  | syntomic =>
      have hm := (Scheme.presieve₀_mem_precoverage_iff U).mp hU
      obtain ⟨W, r, hfin, hstandard, _⟩ :=
        exists_finite_affine_standardSyntomic_refinement U
          ⟨hm.2, iUnion_range_eq_univ_of_mem_precoverage hU⟩
      exact IsStandardCovering.exists_reindex .syntomic U W.cover.toPreZeroHypercover r
        ⟨hfin, fun i => inferInstanceAs (IsAffine (Spec (W.X i))),
          iUnion_range_eq_univ_of_mem_precoverage W.cover.mem₀, hstandard⟩
  | smooth =>
      let Uc : T.Cover (Scheme.precoverage (@Smooth)) :=
        { __ := U, mem₀ := by simpa [coveringMorphismProperty] using hU }
      obtain ⟨W, r, hfin, hstandard, _⟩ := exists_finite_affine_standardSmooth_refinement Uc
      exact IsStandardCovering.exists_reindex .smooth U W.cover.toPreZeroHypercover r
        ⟨hfin, fun i => inferInstanceAs (IsAffine (Spec (W.X i))),
          iUnion_range_eq_univ_of_mem_precoverage W.cover.mem₀, hstandard⟩
  | etale =>
      let Uc : T.Cover (Scheme.precoverage (@Etale)) :=
        { __ := U, mem₀ := by simpa [coveringMorphismProperty] using hU }
      have : Scheme.JointlySurjective (Scheme.precoverage (@Etale.{u})) :=
        Scheme.instJointlySurjectivePrecoverage
      have : MorphismProperty.RespectsLeft @Etale @IsOpenImmersion :=
        ⟨fun i _ f _ => Etale.etale_comp (f := i) (g := f)⟩
      have : QuasiCompactCover Uc.toPreZeroHypercover := by
        refine QuasiCompactCover.of_isOpenMap fun i => ?_
        have : Etale (Uc.f i) := Uc.map_prop i
        exact (Uc.f i).isOpenMap
      obtain ⟨W, r, hfin, _⟩ := QuasiCompactCover.exists_hom Uc
      exact ⟨W.cover.toPreZeroHypercover, r, hfin,
        fun i => inferInstanceAs (IsAffine (Spec (W.X i))),
        iUnion_range_eq_univ_of_mem_precoverage W.cover.mem₀, W.cover.map_prop⟩
  | zariski =>
      let O : T.OpenCover.{v} :=
        { __ := U
          mem₀ := by
            simpa [coveringMorphismProperty, Scheme.zariskiPrecoverage] using hU }
      obtain ⟨W, r, hfin, hbasic⟩ := O.exists_isStandardZariski_refinement
      refine ⟨W.toPreZeroHypercover, r, hfin, fun i => ?_,
        iUnion_range_eq_univ_of_mem_precoverage W.mem₀, hbasic⟩
      obtain ⟨a, e, -⟩ := hbasic i
      exact isAffine_of_isAffineHom e.hom

end AlgebraicGeometry
