module

public import StacksFrontier.AlgebraicGeometry.RingedSpace.KFlatResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.Defs
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectnessFromTheRingedSite
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PseudoCoherentAndFiniteTorDimension
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.FlatOpcycles
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.LocalTorAmplitude
import StacksCore.Tactic.StacksAttribute

/-!
# A perfect object on a quasi-compact ringed space has finite Tor dimension

**Stacks 08G8** says that a perfect object of `D(O_X)` has finite Tor amplitude. In this library
perfectness yields that amplitude only *locally*
(`Stacks.Cohomology.TorAmplitude.locallyHasFiniteTorDimension_of_isPerfect`), with the interval
quantified separately on each member of the covering, and the global statement needs two further
steps, which this file supplies:

* the local-to-global passage, `Stacks.Cohomology.TorAmplitude.hasTorAmplitude_of_iSup_eq_top`,
  carries a *single* interval from an open covering to the whole space, so a **finite**
  subcovering — which quasi-compactness provides — turns the per-member intervals into one
  interval, the smallest interval containing all of them (widening an interval weakens Tor
  amplitude, which is
  `Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_mono`, reused rather
  than restated);
* the result is Tor amplitude for the ringed-*space* predicate
  `Stacks.Cohomology.TorAmplitude.HasTorAmplitude`, measured against
  `Stacks.Cohomology.TorAmplitude.derTensor`, whereas the consumers of finite Tor dimension —
  the compactness results of Stacks 09JC and 09J7 — use the ringed-*site* predicate
  `Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension`, measured against an
  arbitrary derived tensor product datum on the site of opens. The two are bridged here.

## Main results

* `Stacks.Cohomology.TorAmplitude.hasTorAmplitude_iff_derivedTensorProduct`: **the bridge.** For
  every derived tensor product datum `T` of Stacks 06YU on the site of opens of `X`, Tor
  amplitude in `[a, b]` measured against `T` is Tor amplitude in `[a, b]` on the ringed space,
  as an iff.
* `Stacks.Cohomology.TorAmplitude.hasFiniteTorDimension_of_locallyHasFiniteTorDimension`: on a
  quasi-compact space, locally finite Tor dimension is finite Tor dimension.
* `Stacks.Cohomology.TorAmplitude.hasFiniteTorDimension_of_ringedSite_isPerfect`: **Stacks 08G8
  globally.** On a quasi-compact ringed space, an object of `D(O_X)` perfect for the site of
  opens has finite Tor dimension against any derived tensor product datum on that site.

## Implementation notes

**The bridge is an iff, and it is proved by one isomorphism.** Both predicates say that the
cohomology sheaves of `E ⊗^L F[0]` vanish outside `[a, b]` for every `O_X`-module `F`; they
differ only in which inhabitant of the derived-tensor-product interface computes `⊗^L`. The two
inhabitants need not be equal — each is a `Classical.choice` — but they are isomorphic on any
object admitting a K-flat representative, and on a ringed space *every* object admits one
(`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.exists_kFlat_representative`, Stacks 06YS):
the `comparisonLeft` field of each datum computes its value at a K-flat left argument as the
localization of the same total tensor complex, so the two values are isomorphic through that
common complex. No boundedness, no flatness and no relation between `a` and `b` is used, so
neither direction is the harder one and the statement is a genuine iff.

Two of the three K-flatness predicates of the trees meet here —
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat` as produced,
`Stacks.SheafOfModules.IsKFlat` as consumed by the site datum and
`Stacks.SheafOfModules.KFlat.KFlat` as consumed by `derTensor` — and they are the same
proposition definitionally, so the one witness serves all three without conversion.

The finite subcovering is taken with `IsCompact.elim_finite_subcover` on the underlying sets and
reindexed by the resulting `Finset`; the uniform interval is `[min A, max A]` for `A` the finite
set of all the endpoints together with `0`, the `0` being there only so that `A` is nonempty
when the subcovering is empty, which happens exactly when the space is.

## References

* [Stacks Project, Tag 08G8](https://stacks.math.columbia.edu/tag/08G8)
* [Stacks Project, Tag 08CG](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect

namespace Stacks.Cohomology.TorAmplitude

universe u d

section Bridge

variable (X : RingedSpace.{u, u}) [HasDerivedCategory.{d} (OXMod.{u, u} X)]

attribute [local instance] hasDerivedCategoryModules
attribute [local instance]
  Stacks.Cohomology.PerfectComplexes.hasDerivedCategoryRingedSiteModules

/-- **The bridge between the two Tor-amplitude predicates of the trees.** Tor amplitude in
`[a, b]` measured against a derived tensor product datum `T` of Stacks 06YU on the site of opens
of `X` is Tor amplitude in `[a, b]` on the ringed space `X`, which is measured against
`Stacks.Cohomology.TorAmplitude.derTensor`.

The two sides quantify over the same modules and the same degrees; a K-flat representative of
`E` makes the two derived tensor products isomorphic, both being computed from it by the
`comparisonLeft` field of the respective datum. -/
theorem hasTorAmplitude_iff_derivedTensorProduct
    (T : Stacks.SheafOfModules.DerivedTensorProduct.{u, u, u, d}
      (AlgebraicGeometry.RingedSpace.ringedSite X))
    (E : DerivedCategory (OXMod.{u, u} X)) (a b : ℤ) :
    Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude T E a b ↔
      HasTorAmplitude X E a b := by
  obtain ⟨K, hK, ⟨eK⟩⟩ :=
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.exists_kFlat_representative (X := X) E
  have key : ∀ F : OXMod.{u, u} X,
      (T.tensor.obj E).obj ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F) ≅
        ((derTensor X).tensor.obj E).obj
          ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F) := by
    intro F
    have e1 : (T.tensor.obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj
          ((HomologicalComplex.single (OXMod.{u, u} X) (ComplexShape.up ℤ) 0).obj F)) ≅
        ((derTensor X).tensor.obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj
          ((HomologicalComplex.single (OXMod.{u, u} X) (ComplexShape.up ℤ) 0).obj F)) :=
      T.comparisonLeft K _ hK ≪≫ ((derTensor X).comparisonLeft K _ hK).symm
    exact ((T.tensor.mapIso eK.symm).app _) ≪≫ e1 ≪≫ ((derTensor X).tensor.mapIso eK).app _
  refine ⟨fun h F i hi => ?_, fun h F i hi => ?_⟩
  · exact (h F i hi).of_iso
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).mapIso (key F)).symm
  · exact (h F i hi).of_iso
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).mapIso (key F))

end Bridge

section Global

variable (X : RingedSpace.{u, u}) [HasDerivedCategory.{d} (OXMod.{u, u} X)]

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 10000] hasDerivedCategoryModules
attribute [local instance 10000]
  Stacks.Cohomology.PerfectComplexes.hasDerivedCategoryRingedSiteModules
attribute [local instance] restrictModules_preservesFiniteLimits
  restrictModules_preservesFiniteColimits

/-- **On a quasi-compact space, locally finite Tor dimension is finite Tor dimension.** The
covering witnessing local finiteness has a finite subcovering, and
`Stacks.Cohomology.TorAmplitude.hasTorAmplitude_of_iSup_eq_top` carries one interval from a
covering to the space, so the smallest interval containing the finitely many per-member
intervals works. -/
theorem hasFiniteTorDimension_of_locallyHasFiniteTorDimension [CompactSpace X.carrier]
    (E : DerivedCategory (OXMod.{u, u} X)) (h : LocallyHasFiniteTorDimension X E) :
    HasFiniteTorDimension X E := by
  classical
  obtain ⟨I, U, hsup, hmod⟩ := h
  choose af bf hab using hmod
  have cov : ∀ {ι : Type u} (V : ι → Opens X.carrier),
      iSup V = ⊤ ↔ (Set.univ : Set X.carrier) ⊆ ⋃ i, (V i : Set X.carrier) := fun V => by
    rw [← SetLike.coe_set_eq, Opens.coe_iSup]
    simp [Set.eq_univ_iff_forall, Set.subset_def]
  obtain ⟨s, hs⟩ := (isCompact_univ (X := X.carrier)).elim_finite_subcover
    (fun i => (U i : Set X.carrier)) (fun i => (U i).isOpen) ((cov U).1 hsup)
  set A : Finset ℤ := insert 0 (s.image af ∪ s.image bf)
  have hA0 : (0 : ℤ) ∈ A := Finset.mem_insert_self _ _
  refine ⟨A.min' ⟨0, hA0⟩, A.max' ⟨0, hA0⟩,
    hasTorAmplitude_of_iSup_eq_top X E _ _ (fun i : {i // i ∈ s} => U i.1) ?_ ?_⟩
  · exact (cov _).2 (by simpa [Set.iUnion_subtype] using hs)
  · intro i
    exact FlatOpcycles.hasTorAmplitude_mono (hab i.1) (A.min'_le _ (by simp [A]; grind))
      (A.le_max' _ (by simp [A]; grind))

/-- **Stacks 08G8 globally, on a quasi-compact ringed space.** An object of `D(O_X)` which is
perfect for the site of opens of `X` has finite Tor dimension against any derived tensor product
datum of Stacks 06YU on that site.

Perfectness is transported to the ringed-space spelling by
`Stacks.Cohomology.PerfectComplexes.isPerfect_of_ringedSite`, which is what makes the
Tor-amplitude machinery applicable; `locallyHasFiniteTorDimension_of_isPerfect` then supplies the
local intervals, quasi-compactness makes them one interval, and the bridge reads it against
`T`. -/
@[stacks 08G8 "a perfect object has finite tor dimension, globally on a quasi-compact space",
  sga "6 0 3.1" "partial",
  sga "6 I 8.5" "partial",
  sga "6 III 4.2" "special case"]
theorem hasFiniteTorDimension_of_ringedSite_isPerfect [CompactSpace X.carrier]
    (T : Stacks.SheafOfModules.DerivedTensorProduct.{u, u, u, d}
      (AlgebraicGeometry.RingedSpace.ringedSite X))
    (E : DerivedCategory (OXMod.{u, u} X))
    (hE : (AlgebraicGeometry.RingedSpace.ringedSite X).IsPerfect E) :
    Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension
      (X := AlgebraicGeometry.RingedSpace.ringedSite X) T E := by
  obtain ⟨a, b, hab⟩ := hasFiniteTorDimension_of_locallyHasFiniteTorDimension X E
    (locallyHasFiniteTorDimension_of_isPerfect E
      (Stacks.Cohomology.PerfectComplexes.isPerfect_of_ringedSite X E hE))
  exact ⟨a, b, (hasTorAmplitude_iff_derivedTensorProduct X T E a b).2 hab⟩

end Global

end Stacks.Cohomology.TorAmplitude

end
