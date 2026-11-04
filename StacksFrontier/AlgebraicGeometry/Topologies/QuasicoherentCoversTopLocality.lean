module

public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentModuleUniverse

/-!
# Quasi-coherence tested on a family covering the final object

A sheaf of modules on a site is quasi-coherent as soon as its restrictions to the members of a
family of objects covering the final object are quasi-coherent.

## Main results

* `Stacks.SheafOfModules.isQuasicoherentOnSite_of_coversTop_isQuasicoherentOnSite`: a sheaf of
  modules whose restriction to every member of a family covering the final object is
  quasi-coherent is quasi-coherent, with the universe of the module sections independent of the
  universe of the coefficient rings.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w m

namespace Stacks.SheafOfModules

/-- If a family of objects `W i` covers the final object of the site and the restriction of a
sheaf of modules to every member is quasi-coherent, then the module is quasi-coherent. The
universe of the module sections is independent of the universe of the coefficient rings. -/
theorem isQuasicoherentOnSite_of_coversTop_isQuasicoherentOnSite {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}} (M : SheafOfModules.{m} R)
    {I : Type*} {W : I → C} (hW : J.CoversTop W)
    (hQ : ∀ i, (M.over (W i)).IsQuasicoherentOnSite) :
    M.IsQuasicoherentOnSite := by
  classical
  choose K V g hcov hpres using fun (i : I) (f : Over (W i)) =>
    (hQ i).locally_hasGlobalPresentation f
  let Y : (i : I) → (Σ f : Over (W i), K i f) → Over (W i) := fun i k => V i k.1 k.2
  have hY : ∀ i, (J.over (W i)).CoversTop (Y i) := by
    intro i f
    refine (J.over (W i)).superset_covering ?_ (hcov i f)
    refine (Sieve.ofArrows_le_ofObjects (V i f) (g i f)).trans (Sieve.ofObjects_mono ?_)
    rintro x ⟨j, rfl⟩
    exact ⟨⟨f, j⟩, rfl⟩
  refine isQuasicoherentOnSite_of_coversTop_hasGlobalPresentation M
    (W := fun t : {V : C // (M.over V).HasGlobalPresentation} => t.1) (fun X => ?_)
    (fun t => t.2)
  refine J.superset_covering (Sieve.ofObjects_mono ?_) (hW.over hY X)
  rintro x ⟨k, rfl⟩
  exact ⟨⟨_, hasGlobalPresentation_iteratedSlice' M (W k.1) (Y k.1 k.2) (hpres k.1 k.2.1 k.2.2)⟩,
    rfl⟩

end Stacks.SheafOfModules

end
