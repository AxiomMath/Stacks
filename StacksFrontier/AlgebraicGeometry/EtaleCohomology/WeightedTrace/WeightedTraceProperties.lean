module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceConstruction
public import StacksCore.Tactic.StacksAttribute

/-!
# Functoriality of the weighted trace in the sheaf

Let `f : X ⟶ Y` be a locally quasi-finite morphism of a big étale site and let `w` be an
integer-valued function on `X`. Stacks 0GKG characterises the trace map
`Tr_{f, w, ℱ} : f_! f^{-1}ℱ ⟶ ℱ` by its behaviour on geometric stalks, which is the predicate
`AlgebraicGeometry.SmallEtale.HasWeightedTraceStalks` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceConstruction`. Part (1)
of Stacks 0GKH asserts that those trace maps are functorial in `ℱ`, and its proof in the source
is exactly that the characterising property on stalks forces the naturality square to commute.
That deduction is carried out here, for an arbitrary locally quasi-finite `f` and an arbitrary
integer-valued `w`.

## Main results

* `AlgebraicGeometry.SmallEtale.weightedTraceStalkMap_natural` — the weighted sum over the
  geometric fibre is natural in the abelian sheaf on the base.
* `AlgebraicGeometry.SmallEtale.hasWeightedTraceStalks_naturality` — **Stacks 0GKH, part (1).**
  Any two morphisms with the weighted behaviour on geometric stalks, at `ℱ` and at `𝒢`, make the
  naturality square for a morphism `ℱ ⟶ 𝒢` commute.

## Implementation notes

**What this does and does not depend on.** The statement proved here quantifies over morphisms
satisfying the characterising stalk property rather than over the trace maps themselves: the
*existence* half of Stacks 0GKG is available in this library only for an étale morphism with its
canonical weighting, where the trace map is the counit of `j_! ⊣ j^{-1}`
(`AlgebraicGeometry.hasWeightedTraceStalks_counit` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.EtaleTraceIsCounit`), so for a
general `f` and a general `w` there is no term `Tr_{f, w, ℱ}` to be natural. Once existence
is supplied, part (1) of Stacks 0GKH is this theorem applied to it, with no further work: the
trace maps are characterised by the hypotheses `hF` and `hG` here, so nothing beyond them is
used. By `AlgebraicGeometry.SmallEtale.hasWeightedTraceStalks_unique` there is at most one such
morphism for each sheaf, so the statement is about the trace maps and not about an
under-determined family.

The companion statement for an étale morphism with its canonical weighting, where the trace is
taken to be the counit of `j_! ⊣ j^{-1}` and functoriality is the naturality of that counit, is
`AlgebraicGeometry.etaleCanonicalTrace_naturality` in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.EtaleTraceCounit`. The present
theorem is the general one: it is about the weighted trace of Stacks 0GKG for any locally
quasi-finite `f` and any `w`, and it does not assume that the morphisms it quantifies over come
from an adjunction.

Part (2) of Stacks 0GKH, compatibility with arbitrary base change, is
`AlgebraicGeometry.SmallEtale.hasWeightedTraceStalks_baseChange` in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceBaseChange`, proved in
the same generality and in the same style as part (1) here.

## References

* [Stacks Project, Tag 0GKH](https://stacks.math.columbia.edu/tag/0GKH)
* [Stacks Project, Tag 0GKG](https://stacks.math.columbia.edu/tag/0GKG)
* [Stacks Project, Tag 0F5F](https://stacks.math.columbia.edu/tag/0F5F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum

universe u v

namespace AlgebraicGeometry.SmallEtale

section Functoriality

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)

/-- The map induced on the direct sum of stalks over the geometric fibre by a morphism of
sheaves acts on the summand indexed by a point of the fibre by the map on that stalk. -/
public theorem fiberStalksMap_fiberStalkOf (s : GeometricPoint Y.obj)
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}}
    (φ : F ⟶ G) (x : GeometricFiberPoint B f s)
    (z : ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B f s) F.obj)) :
    fiberStalksMap.{u, max (u + 1) v} B f s φ (fiberStalkOf.{u, v} B f s F x z) =
      fiberStalkOf.{u, v} B f s G x
        ((colim.map (Functor.whiskerLeft (CategoryOfElements.π
          (geometricPointFiber B X.obj X.property (x.toGeometricPoint B f s))).op φ.1)) z) := by
  let _inst : DecidableEq (GeometricFiberPoint B f s) := Classical.decEq _
  exact DirectSum.map_of (fun y : GeometricFiberPoint B f s =>
    (colim.map (Functor.whiskerLeft (CategoryOfElements.π
      (geometricPointFiber B X.obj X.property (y.toGeometricPoint B f s))).op φ.1)).hom) x z

/-- The weighted sum over the geometric fibre is natural in the abelian sheaf on the base: the
square formed by the weighted sums for `F` and for `G`, the map induced on the direct sums of
stalks by the inverse image of `φ : F ⟶ G`, and the map induced by `φ` on the stalk below,
commutes. -/
public theorem weightedTraceStalkMap_natural (w : X.obj → ℤ)
    {F G : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v}}
    (φ : F ⟶ G) (s : GeometricPoint Y.obj)
    [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] :
    AddCommGrpCat.ofHom (fiberStalksMap.{u, max (u + 1) v} B f s
          ((abPullback.{u, v} B f).map φ)) ≫
        weightedTraceStalkMap.{u, v} B f w G s =
      weightedTraceStalkMap.{u, v} B f w F s ≫
        colim.map (Functor.whiskerLeft
          (CategoryOfElements.π (geometricPointFiber B Y.obj Y.property s)).op φ.1) := by
  refine fiberStalks_hom_ext.{u, v} B f s fun x z => ?_
  have hmap := fiberStalksMap_fiberStalkOf.{u, v} B f s ((abPullback.{u, v} B f).map φ) x z
  have hnat : (fiberPointPullbackStalkIso.{u, v} B f s G x).hom
        ((colim.map (Functor.whiskerLeft (CategoryOfElements.π
          (geometricPointFiber B X.obj X.property (x.toGeometricPoint B f s))).op
            ((abPullback.{u, v} B f).map φ).1)) z) =
      (colim.map (Functor.whiskerLeft
          (CategoryOfElements.π (geometricPointFiber B Y.obj Y.property s)).op φ.1))
        ((fiberPointPullbackStalkIso.{u, v} B f s F x).hom z) :=
    ConcreteCategory.congr_hom (fiberPointPullbackStalkIso_natural.{u, v} B f s φ x) z
  show (weightedTraceStalkMap.{u, v} B f w G s)
        (fiberStalksMap.{u, max (u + 1) v} B f s ((abPullback.{u, v} B f).map φ)
          (fiberStalkOf.{u, v} B f s ((abPullback.{u, v} B f).obj F) x z)) =
      (colim.map (Functor.whiskerLeft
          (CategoryOfElements.π (geometricPointFiber B Y.obj Y.property s)).op φ.1))
        ((weightedTraceStalkMap.{u, v} B f w F s)
          (fiberStalkOf.{u, v} B f s ((abPullback.{u, v} B f).obj F) x z))
  rw [hmap, weightedTraceStalkMap_fiberStalkOf.{u, v} B f w G s x
      ((colim.map (Functor.whiskerLeft (CategoryOfElements.π
        (geometricPointFiber B X.obj X.property (x.toGeometricPoint B f s))).op
          ((abPullback.{u, v} B f).map φ).1)) z),
    weightedTraceStalkMap_fiberStalkOf.{u, v} B f w F s x z, hnat]
  exact (map_zsmul _ _ _).symm

variable [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

/-- The stalk of a morphism with the weighted behaviour on geometric stalks is the weighted sum,
read through the decomposition of the stalk of `f_! f^{-1}F`. -/
private theorem colim_map_trace_eq (w : X.obj → ℤ)
    {F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v}}
    {τ : (fShriekFunctor.{u, v} B f).obj ((abPullback.{u, v} B f).obj F) ⟶ F}
    (h : HasWeightedTraceStalks.{u, v} B f w F τ) (s : GeometricPoint Y.obj) :
    colim.map (Functor.whiskerLeft
        (CategoryOfElements.π (geometricPointFiber B Y.obj Y.property s)).op τ.1) =
      (fShriekStalkIso.{u, v} B f s ((abPullback.{u, v} B f).obj F)).hom ≫
        weightedTraceStalkMap.{u, v} B f w F s :=
  ((Iso.eq_inv_comp _).1 (h s).symm).symm

/-- **Stacks 0GKH, part (1): the trace map is functorial in the abelian sheaf.** If `τ_F` and
`τ_G` are trace maps for `(f, w)` at `F` and at `G` — morphisms with the weighted behaviour on
geometric stalks which characterises the trace of Stacks 0GKG — then for every `φ : F ⟶ G` the
square
`f_! f^{-1}F ⟶ f_! f^{-1}G ⟶ G` versus `f_! f^{-1}F ⟶ F ⟶ G`
commutes.

The source deduces this from the characterisation on stalks, and so does the proof here: the
geometric stalk functors are jointly faithful, the stalk of a trace map is the weighted sum over
the geometric fibre read through the decomposition of Stacks 0F5F, that decomposition is natural
in the sheaf, and the weighted sum is natural by
`AlgebraicGeometry.SmallEtale.weightedTraceStalkMap_natural`. No hypothesis on `w` is needed. -/
@[stacks 0GKH "part (1), functoriality of the trace map in the sheaf, for an arbitrary locally \
quasi-finite morphism and an arbitrary integer-valued weight. Stated for morphisms with the \
behaviour on geometric stalks by which Lemma 0GKG characterises the trace map, which by \
`AlgebraicGeometry.SmallEtale.existsUnique_hasWeightedTraceStalks` is exactly the trace map of \
that lemma: it exists for every weighting and every sheaf, and is unique. Part (2) is \
`AlgebraicGeometry.SmallEtale.hasWeightedTraceStalks_baseChange`.", sga "4 XVII 6.2.5"]
public theorem hasWeightedTraceStalks_naturality (w : X.obj → ℤ)
    {F G : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v}}
    (φ : F ⟶ G)
    {τF : (fShriekFunctor.{u, v} B f).obj ((abPullback.{u, v} B f).obj F) ⟶ F}
    {τG : (fShriekFunctor.{u, v} B f).obj ((abPullback.{u, v} B f).obj G) ⟶ G}
    (hF : HasWeightedTraceStalks.{u, v} B f w F τF)
    (hG : HasWeightedTraceStalks.{u, v} B f w G τG) :
    (fShriekFunctor.{u, v} B f).map ((abPullback.{u, v} B f).map φ) ≫ τG = τF ≫ φ := by
  refine (jointlyFaithful_etaleStalkSheafFiber.{u, v} B Y.obj Y.property).map_injective
    fun s => ?_
  have hLsplit : colim.map (Functor.whiskerLeft
        (CategoryOfElements.π (geometricPointFiber B Y.obj Y.property s)).op
        (((fShriekFunctor.{u, v} B f).map ((abPullback.{u, v} B f).map φ)).1 ≫ τG.1)) =
      colim.map (Functor.whiskerLeft
          (CategoryOfElements.π (geometricPointFiber B Y.obj Y.property s)).op
          ((fShriekFunctor.{u, v} B f).map ((abPullback.{u, v} B f).map φ)).1) ≫
        colim.map (Functor.whiskerLeft
          (CategoryOfElements.π (geometricPointFiber B Y.obj Y.property s)).op τG.1) :=
    (etaleStalkPresheafFunctor B Y.obj Y.property s AddCommGrpCat.{max (u + 1) v}).map_comp
      ((fShriekFunctor.{u, v} B f).map ((abPullback.{u, v} B f).map φ)).1 τG.1
  have hRsplit : colim.map (Functor.whiskerLeft
        (CategoryOfElements.π (geometricPointFiber B Y.obj Y.property s)).op (τF.1 ≫ φ.1)) =
      colim.map (Functor.whiskerLeft
          (CategoryOfElements.π (geometricPointFiber B Y.obj Y.property s)).op τF.1) ≫
        colim.map (Functor.whiskerLeft
          (CategoryOfElements.π (geometricPointFiber B Y.obj Y.property s)).op φ.1) :=
    (etaleStalkPresheafFunctor B Y.obj Y.property s AddCommGrpCat.{max (u + 1) v}).map_comp
      τF.1 φ.1
  have hdecomp := fShriekStalkIso_natural.{u, v} B f s ((abPullback.{u, v} B f).map φ)
  have hwt := weightedTraceStalkMap_natural.{u, v} B f w φ s
  show colim.map (Functor.whiskerLeft
      (CategoryOfElements.π (geometricPointFiber B Y.obj Y.property s)).op
      (((fShriekFunctor.{u, v} B f).map ((abPullback.{u, v} B f).map φ)).1 ≫ τG.1)) =
    colim.map (Functor.whiskerLeft
      (CategoryOfElements.π (geometricPointFiber B Y.obj Y.property s)).op (τF.1 ≫ φ.1))
  rw [hLsplit, hRsplit, colim_map_trace_eq B f w hF s, colim_map_trace_eq B f w hG s]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ weightedTraceStalkMap.{u, v} B f w G s) hdecomp).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun z =>
            (fShriekStalkIso.{u, v} B f s ((abPullback.{u, v} B f).obj F)).hom ≫ z) hwt).trans
          (Category.assoc _ _ _).symm)))

end Functoriality

end AlgebraicGeometry.SmallEtale

end
