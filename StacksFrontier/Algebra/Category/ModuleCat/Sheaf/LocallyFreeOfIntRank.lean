module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SingleDegreeRankOpenSubspace
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree

/-!
# Finite local freeness of an integer rank, from a covering

A sheaf of modules is finite locally free of rank `r`
(`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfIntRank`) when it has a local free
presentation each of whose basis-indexing types has cardinality `r`. We show that a sheaf of
modules which is free of rank `r` on the members of a covering is finite locally free of rank `r`.

## Main definitions

* `SheafOfModules.GeneratingSections.ofIsoFree`: the generating sections given by an isomorphism
  with a free module.

## Main results

* `AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfIntRank_of_coversTop`: a sheaf of modules
  which is free of rank `r` on the members of a covering is finite locally free of rank `r`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v u₁

/-- The generating sections of a sheaf of modules given by an isomorphism with a free module. -/
def _root_.SheafOfModules.GeneratingSections.ofIsoFree {C : Type u₁} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {M : _root_.SheafOfModules.{u} R}
    {I : Type u} [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (e : _root_.SheafOfModules.free I ≅ M) : M.GeneratingSections where
  I := I
  s := M.freeHomEquiv e.hom
  epi := by simp only [Equiv.symm_apply_apply]; infer_instance

/-- The morphism from the free module defined by `SheafOfModules.GeneratingSections.ofIsoFree e`
is `e.hom`. -/
lemma _root_.SheafOfModules.GeneratingSections.ofIsoFree_π {C : Type u₁} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {M : _root_.SheafOfModules.{u} R}
    {I : Type u} [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (e : _root_.SheafOfModules.free I ≅ M) :
    (_root_.SheafOfModules.GeneratingSections.ofIsoFree e).π = e.hom :=
  Equiv.symm_apply_apply _ _

namespace AlgebraicGeometry.SheafOfModules

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A sheaf of modules which is free of rank `r` on the members of a covering is finite locally
free of rank `r`. -/
theorem isFiniteLocallyFreeOfIntRank_of_coversTop {ι : Type u₁} {V : ι → C} (hV : J.CoversTop V)
    (M : _root_.SheafOfModules.{u} R) (r : ℤ)
    (e : ∀ k, ∃ n : ℕ, (n : ℤ) = r ∧
      Nonempty (_root_.SheafOfModules.free (R := R.over (V k)) (ULift.{u} (Fin n)) ≅
        M.over (V k))) :
    IsFiniteLocallyFreeOfIntRank.{u, v, u₁} M r :=
  ⟨{ I := ι, X := V, coversTop := hV
     generators k := _root_.SheafOfModules.GeneratingSections.ofIsoFree (e k).choose_spec.2.some },
    ⟨fun k => by
      show IsIso (_root_.SheafOfModules.GeneratingSections.ofIsoFree _).π
      rw [_root_.SheafOfModules.GeneratingSections.ofIsoFree_π]
      exact Iso.isIso_hom _⟩,
    fun k => ⟨(e k).choose, (e k).choose_spec.1, ⟨Equiv.ulift⟩⟩⟩

end AlgebraicGeometry.SheafOfModules

end
