module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.FiniteLocallyFree

/-!
# The covering-family form of finite local freeness gives local generators

Let `M` be a sheaf of modules on a site `C` with a final object `T`. If `M` is finite locally free
in the covering-family sense of Stacks 03DL(2) (`SheafOfModules.IsFiniteLocallyFreeOnSite`), then
it is finite locally free in the local-generators sense of Stacks 01C6(2)
(`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree`): a covering family of `T` on whose
members `M` is finite free is a family covering the final object, and on each member a finite
free basis is a finite family of generating sections whose morphism out of the free sheaf is
invertible.

## Main results

* `Stacks.SheafOfModules.isFiniteLocallyFree_of_isFiniteLocallyFreeOnSite`: the implication,
  converse to `Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_isFiniteLocallyFree`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [hsh : ∀ Y : C, HasWeakSheafify (J.over Y) AddCommGrpCat.{w}]
  [hlb : ∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- A finite family of morphisms from the structure sheaf exhibiting a sheaf of modules as their
coproduct gives generating sections whose morphism out of the free sheaf is invertible. -/
private theorem exists_generatingSections_isIso_of_isColimit (M : SheafOfModules.{w} R) (Y : C)
    {n : ℕ} (ι : Fin n → (SheafOfModules.unit (R.over Y) ⟶ M.over Y))
    (hι : IsColimit (Cofan.mk (M.over Y) ι)) :
    ∃ σ : (M.over Y).GeneratingSections, IsIso σ.π ∧ σ.IsFiniteType := by
  let e : ULift.{w} (Fin n) ≃ Fin n := Equiv.ulift
  let ι' : ULift.{w} (Fin n) → (SheafOfModules.unit (R.over Y) ⟶ M.over Y) := fun j => ι (e j)
  have hι' : IsColimit (Cofan.mk (M.over Y) ι') :=
    Cofan.isColimitEquivOfEquiv e (Cofan.mk (M.over Y) ι) hι
  let s : ULift.{w} (Fin n) → (M.over Y).sections := fun j => (M.over Y).unitHomEquiv (ι' j)
  have hs : ∀ j, SheafOfModules.ιFree j ≫ (M.over Y).freeHomEquiv.symm s = ι' j := fun j =>
    (M.over Y).unitHomEquiv.injective (congrFun ((M.over Y).freeHomEquiv.apply_symm_apply s) j)
  let inv : M.over Y ⟶ SheafOfModules.free (ULift.{w} (Fin n)) :=
    Cofan.IsColimit.desc hι' SheafOfModules.ιFree
  have hinv : ∀ j, ι' j ≫ inv = SheafOfModules.ιFree j := Cofan.IsColimit.fac hι' _
  have : IsIso ((M.over Y).freeHomEquiv.symm s) := by
    refine ⟨inv, ?_, ?_⟩
    · refine Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan _) _ _ fun j => ?_
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ inv) (hs j)).trans
        ((hinv j).trans (Category.comp_id _).symm))
    · refine Cofan.IsColimit.hom_ext hι' _ _ fun j => ?_
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (M.over Y).freeHomEquiv.symm s) (hinv j)).trans
          ((hs j).trans (Category.comp_id _).symm))
  exact ⟨⟨ULift.{w} (Fin n), s, inferInstance⟩,
    inferInstance,
    ⟨inferInstanceAs (Finite (ULift.{w} (Fin n)))⟩⟩

/-- **The covering-family form of Stacks 03DL(2) implies the local-generators form of Stacks
01C6(2) on a site with a final object.** A sheaf of modules which is finite locally free on the
site carries local generators data which is a finite local free basis. -/
theorem isFiniteLocallyFree_of_isFiniteLocallyFreeOnSite {T : C} (hT : IsTerminal T)
    (M : SheafOfModules.{w} R) (hM : SheafOfModules.IsFiniteLocallyFreeOnSite M) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{w, v, u} M := by
  obtain ⟨I, V, f, hcov, hfree⟩ :=
    (SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isColimit M).mp hM T
  have hgen : ∀ i : I, ∃ σ : (M.over (V i)).GeneratingSections, IsIso σ.π ∧ σ.IsFiniteType :=
    fun i => by
      obtain ⟨n, ι, ⟨hι⟩⟩ := hfree i
      exact exists_generatingSections_isIso_of_isColimit M (V i) ι hι
  choose σ hσiso hσfin using hgen
  have hTop : J.CoversTop V := by
    rw [GrothendieckTopology.coversTop_iff_of_isTerminal J T hT]
    refine J.superset_covering ?_ hcov
    rintro Y g ⟨Z, a, b, ⟨i⟩, rfl⟩
    exact ⟨i, ⟨a⟩⟩
  let q : M.LocalGeneratorsData :=
    { I := I
      X := V
      coversTop := hTop
      generators := σ }
  have : q.IsLocallyFreeData := ⟨hσiso⟩
  exact ⟨⟨q.shrink, inferInstance, ⟨fun i => hσfin _⟩⟩⟩

end Stacks.SheafOfModules

end
