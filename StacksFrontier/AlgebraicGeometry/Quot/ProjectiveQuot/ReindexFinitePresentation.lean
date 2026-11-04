module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleInternalHomFinitePresentation

/-!
# Finite presentation is carried along an equivalence of ringed sites

If a sheaf of modules on a ringed site `(C, J, R)` is of finite presentation (Stacks 03DL (7)),
then so is its reindexing along an equivalence of sites `e : C' ≌ C`. This is one implication of
Stacks 03DM for clause (7) of Stacks 03DL; the same statement for quasi-coherence is
`Stacks.SheafOfModules.isQuasicoherentOnSite_reindex`.

## Main results

* `Stacks.SheafOfModules.isFinitePresentationOnSite_reindex`: the reindexing of a sheaf of modules
  of finite presentation along an equivalence of ringed sites is of finite presentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {C' : Type u} [Category.{v} C']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}

variable (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  (R : Sheaf J RingCat.{w}) [e.inverse.IsDenseSubsite J J']

omit [e.inverse.IsContinuous J J'] in
/-- Reindexing carries a finite global presentation of the restriction to `e.functor.obj V` to a
finite global presentation of the restriction of the reindexing to `V`. -/
theorem hasFiniteGlobalPresentation_over_reindex (M : _root_.SheafOfModules.{w} R) (V : C')
    (h : (M.over (e.functor.obj V)).HasFiniteGlobalPresentation) :
    (((_root_.SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj M).over
      V).HasFiniteGlobalPresentation := by
  rw [over_reindex_eq]
  exact hasFiniteGlobalPresentation_reindex (overSiteEquivalence e V) (R.over (e.functor.obj V))
    (M.over (e.functor.obj V)) h

omit [e.inverse.IsContinuous J J'] in
/-- If a sheaf of modules on `(C, J, R)` is of finite presentation, then so is its reindexing
along the equivalence of sites `e : C' ≌ C`. -/
theorem isFinitePresentationOnSite_reindex (M : _root_.SheafOfModules.{w} R)
    [hM : M.IsFinitePresentationOnSite] :
    ((_root_.SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj
      M).IsFinitePresentationOnSite := by
  refine ⟨fun V => ?_⟩
  obtain ⟨I, W, g, hcov, hpres⟩ := hM.locally_hasFiniteGlobalPresentation (e.functor.obj V)
  refine ⟨I, fun i => e.inverse.obj (W i),
    fun i => e.inverse.map (g i) ≫ (e.unitIso.app V).inv, ?_, fun i => ?_⟩
  · refine J'.superset_covering (fun Z h hh => ?_) (e.functor.cover_lift J' J hcov)
    obtain ⟨i, a, ha⟩ := (Sieve.mem_ofArrows_iff W g _).1 hh
    rw [Sieve.mem_ofArrows_iff]
    refine ⟨i, (e.unitIso.app Z).hom ≫ e.inverse.map a, ?_⟩
    have hnat := e.unit.naturality h
    simp only [Functor.id_obj, Functor.id_map, Functor.comp_map] at hnat
    simp only [Category.assoc]
    rw [← Category.assoc (e.inverse.map a), ← e.inverse.map_comp, ← ha, ← Category.assoc,
      show (e.unitIso.app Z).hom = e.unit.app Z from rfl, ← hnat]
    simp
  · exact hasFiniteGlobalPresentation_over_reindex e R M _
      (FinitePresentationTransport.hasFiniteGlobalPresentation_overMap M
        (e.counitIso.app (W i)).hom (hpres i))

end Stacks.SheafOfModules

end
