module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence

/-!
# Quasi-coherence passes from a coarser topology to a finer one

Let `K ≤ J` be two Grothendieck topologies on a category `C` and let `R` be a sheaf of rings
for the finer topology `J`. Its presheaf is then also a `K`-sheaf, so every sheaf of `R`-modules
for `J` can be read as a sheaf of modules for `K` without changing anything but the sheaf
condition it is asserted to satisfy. A module sheaf for `J` whose reading for `K` is
quasi-coherent on `(C, K)`, in the sense of Stacks 03DL(6), is quasi-coherent on `(C, J)`.

## Main definitions

* `Stacks.SheafOfModules.ringOfLe`: a sheaf of rings for the finer topology, read for the
  coarser one.
* `Stacks.SheafOfModules.comparisonPushforward`: a sheaf of modules for the finer topology,
  read for the coarser one. Neither the presheaf of modules nor the morphisms change.
* `Stacks.SheafOfModules.comparisonPullback`: its left adjoint, sheafification for the finer
  topology.

## Main results

* `Stacks.SheafOfModules.hasGlobalPresentation_of_le`: a global presentation for the coarser
  topology of a module sheaf for the finer one gives a global presentation for the finer
  topology.
* `Stacks.SheafOfModules.isQuasicoherentOnSite_of_le`: hence quasi-coherence for the coarser
  topology implies quasi-coherence for the finer one, for a module sheaf for the finer
  topology.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 0EM8](https://stacks.math.columbia.edu/tag/0EM8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w m

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J K : GrothendieckTopology C} (h : K ≤ J)
  (R : Sheaf J RingCat.{w})

include h in
/-- The identity functor is continuous from a coarser topology to a finer one, since a sheaf
for the finer topology is a sheaf for the coarser one. -/
public theorem isContinuous_id_of_le : (Functor.id C).IsContinuous K J where
  op_comp_isSheaf_of_types F := (isSheaf_iff_isSheaf_of_type _ _).1 (F.property.of_le h)

/-- A sheaf of rings for the finer topology, read as a sheaf of rings for the coarser one. -/
public abbrev ringOfLe : Sheaf K RingCat.{w} := ⟨R.obj, R.property.of_le h⟩

/-- A sheaf of modules for the finer topology, read as a sheaf of modules for the coarser one.
Neither the underlying presheaf of modules nor the morphisms between them change. -/
public def comparisonPushforward :
    SheafOfModules.{m} R ⥤ SheafOfModules.{m} (ringOfLe h R) where
  obj M := ⟨M.val, M.isSheaf.of_le h⟩
  map f := ⟨f.val⟩

/-- Reading a module sheaf for the coarser topology is fully faithful: a morphism of module
sheaves is a morphism of the underlying presheaves of modules either way. -/
public def comparisonPushforwardFullyFaithful :
    (comparisonPushforward.{u, v, w, m} h R).FullyFaithful where
  preimage f := ⟨f.val⟩
  map_preimage _ := rfl
  preimage_map _ := rfl

/-- Reading a module sheaf for the coarser topology is additive. -/
public theorem additive_comparisonPushforward :
    (comparisonPushforward.{u, v, w, m} h R).Additive where
  map_add := rfl

section Pullback

variable [HasWeakSheafify J AddCommGrpCat.{m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- Sheafification for the finer topology, as a functor on sheaves of modules: the left adjoint
of `Stacks.SheafOfModules.comparisonPushforward`. -/
public noncomputable def comparisonPullback :
    SheafOfModules.{m} (ringOfLe h R) ⥤ SheafOfModules.{m} R := by
  letI := isContinuous_id_of_le h
  letI : (PresheafOfModules.pushforward.{m}
      (F := Functor.id C) (𝟙 R.obj)).IsRightAdjoint := inferInstance
  exact _root_.SheafOfModules.pullback.{m} (F := Functor.id C)
    (⟨𝟙 R.obj⟩ : ringOfLe h R ⟶
      ((Functor.id C).sheafPushforwardContinuous RingCat.{w} K J).obj R)

/-- Sheafification for the finer topology is left adjoint to reading a module sheaf for the
coarser one. -/
public noncomputable def comparisonAdjunction :
    comparisonPullback.{u, v, w, m} h R ⊣ comparisonPushforward.{u, v, w, m} h R := by
  letI := isContinuous_id_of_le h
  letI : (PresheafOfModules.pushforward.{m}
      (F := Functor.id C) (𝟙 R.obj)).IsRightAdjoint := inferInstance
  exact _root_.SheafOfModules.pullbackPushforwardAdjunction.{m} (F := Functor.id C)
    (⟨𝟙 R.obj⟩ : ringOfLe h R ⟶
      ((Functor.id C).sheafPushforwardContinuous RingCat.{w} K J).obj R)

/-- Sheafification for the finer topology preserves colimits, being a left adjoint. -/
public theorem preservesColimitsOfSize_comparisonPullback :
    PreservesColimitsOfSize.{m, m} (comparisonPullback.{u, v, w, m} h R) :=
  (comparisonAdjunction.{u, v, w, m} h R).leftAdjoint_preservesColimits

/-- Sheafification for the finer topology is additive, being left adjoint to an additive
functor. -/
public theorem additive_comparisonPullback :
    (comparisonPullback.{u, v, w, m} h R).Additive := by
  have := additive_comparisonPushforward.{u, v, w, m} h R
  exact (comparisonAdjunction.{u, v, w, m} h R).left_adjoint_additive

/-- Sheafification for the finer topology preserves zero morphisms. -/
public theorem preservesZeroMorphisms_comparisonPullback :
    (comparisonPullback.{u, v, w, m} h R).PreservesZeroMorphisms := by
  have := additive_comparisonPullback.{u, v, w, m} h R
  infer_instance

/-- Sheafification for the finer topology does nothing to a module sheaf that is already a
sheaf for it: the counit of the adjunction is an isomorphism because reading a module sheaf
for the coarser topology is fully faithful. -/
public noncomputable def comparisonPullbackObjIso (M : SheafOfModules.{m} R) :
    (comparisonPullback.{u, v, w, m} h R).obj
      ((comparisonPushforward.{u, v, w, m} h R).obj M) ≅ M := by
  have hff := comparisonPushforwardFullyFaithful.{u, v, w, m} h R
  haveI : (comparisonPushforward.{u, v, w, m} h R).Full := hff.full
  haveI : (comparisonPushforward.{u, v, w, m} h R).Faithful := hff.faithful
  haveI : IsIso ((comparisonAdjunction.{u, v, w, m} h R).counit.app M) :=
    isIso_of_epi_of_isSplitMono _
  exact asIso ((comparisonAdjunction.{u, v, w, m} h R).counit.app M)

end Pullback

/-- **A global presentation for a coarser topology gives one for a finer topology.** If a
sheaf of modules for the finer topology `J` has a global presentation when read as a sheaf of
modules for the coarser topology `K`, then it has one on `(C, J)`. -/
public theorem hasGlobalPresentation_of_le (M : _root_.SheafOfModules.{w} R)
    (hM : ((comparisonPushforward.{u, v, w, w} h R).obj M).HasGlobalPresentation) :
    M.HasGlobalPresentation := by
  have : HasWeakSheafify J AddCommGrpCat.{max u v w} :=
    (GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v w, v, u} J).isRightAdjoint
  have : J.WEqualsLocallyBijective AddCommGrpCat.{max u v w} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v w, u, v} J
  have : PreservesColimitsOfSize.{max u v w, max u v w}
      (comparisonPullback.{u, v, w, max u v w} h R) :=
    preservesColimitsOfSize_comparisonPullback.{u, v, w, max u v w} h R
  have : (comparisonPullback.{u, v, w, max u v w} h R).PreservesZeroMorphisms :=
    preservesZeroMorphisms_comparisonPullback.{u, v, w, max u v w} h R
  exact hasGlobalPresentation_map
    (F₀ := (Functor.const _).obj M)
    (F := comparisonPullback.{u, v, w, max u v w} h R)
    ((comparisonPushforward.{u, v, w, w} h R).obj M)
    (comparisonPullbackObjIso.{u, v, w, max u v w} h R
      (_root_.SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w}
        (_root_.SheafOfModules.unit R)))
    (comparisonPullbackObjIso.{u, v, w, max u v w} h R
      (_root_.SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} M))
    hM

/-- **Quasi-coherence for a coarser topology implies quasi-coherence for a finer one.** If a
sheaf of modules for the finer topology `J` is quasi-coherent in the sense of Stacks 03DL(6)
when read as a sheaf of modules for the coarser topology `K`, then it is quasi-coherent on
`(C, J)`. -/
public theorem isQuasicoherentOnSite_of_le (M : _root_.SheafOfModules.{w} R)
    (hM : ((comparisonPushforward.{u, v, w, w} h R).obj M).IsQuasicoherentOnSite) :
    M.IsQuasicoherentOnSite where
  locally_hasGlobalPresentation U := by
    obtain ⟨I, V, f, hcov, hpres⟩ := hM.locally_hasGlobalPresentation U
    refine ⟨I, V, f, h _ hcov, fun i => ?_⟩
    have hle : K.over (V i) ≤ J.over (V i) := by
      intro Y T hT
      rw [GrothendieckTopology.mem_over_iff] at hT ⊢
      exact h _ hT
    exact hasGlobalPresentation_of_le hle (R.over (V i)) (M.over (V i)) (hpres i)

end Stacks.SheafOfModules

end
