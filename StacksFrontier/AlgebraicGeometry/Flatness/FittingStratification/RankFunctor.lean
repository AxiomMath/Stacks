module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleAdjunction
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
import StacksFrontier.AlgebraicGeometry.Recovery27.PullbackLocallyFree

/-!
# The rank `r` functor of a module on a scheme

Let `F` be a module on a scheme `S` and let `r` be a natural number. The *rank `r` functor* of
`F` is the contravariant functor on schemes over `S` whose value at `T ⟶ S` is a singleton
exactly when the pullback of `F` to `T` is finite locally free of rank `r`, and is empty
otherwise. It is a subfunctor of the terminal functor, and it is the functor whose
representability by a locally closed subscheme of `S` cuts out the rank `r` stratum of the
Fitting stratification of `F`.

## Main definitions

* `AlgebraicGeometry.rankRFunctor`: the rank `r` functor of a module on a scheme.

## Main results

* `AlgebraicGeometry.rankRFunctor_obj`: the value of the rank `r` functor at a scheme over `S`.

## Implementation notes

The rank condition is a proposition. It is made into a type by `PLift` and then raised to the
universe of the functor by `ULift`, so that the value of the functor is a singleton when the
condition holds and empty otherwise. The restriction maps transport the rank condition along a
further pullback: the two iterated pullbacks of `F` are compared by an isomorphism, and local
bases of the same rank are carried across it, keeping their index types unchanged. Finite type
and quasicoherence of `F` are not needed to define the functor; they are hypotheses of its
representability. The definition is marked `implicit_reducible` so that its fibres unfold in
representability statements.

## References

* [Stacks Project, Tag 05P8](https://stacks.math.columbia.edu/tag/05P8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Transport the rank condition from one scheme over `S` to another along a morphism over `S`,
by comparing the two iterated pullbacks of the module. -/
private theorem rank_restrict (S : Scheme.{u}) (F : S.Modules)
    (r : ℕ) {T T' : (Over S)ᵒᵖ} (f : T ⟶ T')
    (h : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback T.unop.hom).obj F) r) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback T'.unop.hom).obj F) r := by
  refine SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    ((Scheme.Modules.pullbackComp f.unop.left T.unop.hom).app F ≪≫
      (Scheme.Modules.pullbackCongr f.unop.w).app F) ?_
  exact AlgebraicGeometry.Grassmannian.isFiniteLocallyFreeOfRank_pullback f.unop.left.base
    f.unop.left.toRingCatSheafHom _ r h

/-- The rank `r` functor of a module `F` on a scheme `S`: the contravariant functor on schemes
over `S` whose value is a singleton exactly when the pullback of `F` is finite locally free of
rank `r`, and is empty otherwise. -/
@[implicit_reducible]
noncomputable def rankRFunctor (S : Scheme.{u}) (F : S.Modules) (r : ℕ) :
    (Over S)ᵒᵖ ⥤ Type u :=
  { obj T := ULift.{u, 0} (PLift
      (SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback T.unop.hom).obj F) r))
    map f := ↾fun h ↦ ⟨⟨by exact rank_restrict S F r f h.down.down⟩⟩
    map_id _ := by ext; apply Subsingleton.elim
    map_comp _ _ := by ext; apply Subsingleton.elim }

/-- The rank `r` functor has one element exactly at those schemes over `S` whose pullback of `F`
is finite locally free of rank `r`. -/
@[simp]
theorem rankRFunctor_obj (S : Scheme.{u}) (F : S.Modules) (r : ℕ) (T : (Over S)ᵒᵖ) :
    (rankRFunctor S F r).obj T = ULift.{u, 0} (PLift
      (SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback T.unop.hom).obj F) r)) := rfl

end AlgebraicGeometry

end
