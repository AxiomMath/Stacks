module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import StacksCore.Tactic.StacksAttribute

/-!
# Finite locally free sheaves of modules

A sheaf of modules is *locally free* if it is locally isomorphic to a direct sum of copies of
the structure sheaf. It is *finite locally free* when the local indexing types can be chosen
finite, and *finite locally free of rank `r`* when they can be chosen with cardinality `r`.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree`: the local free presentations have
  finite bases.
* `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank`: their bases all have
  cardinality `r`.

## Main results

* `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree`: a fixed
  finite rank forgets to finiteness of the rank.
* `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso`: finite local freeness of
  rank `r` only depends on the isomorphism class.
* `AlgebraicGeometry.SheafOfModules.overCofanIsColimit`: a finite basis on the slice over an
  object restricts to a finite basis on the slice over any object above it.

## Implementation notes

Local freeness itself is Mathlib's `SheafOfModules.IsLocallyFree`, whose local generator data
consists of a cover together with isomorphisms from free sheaves. The two classes here refine
the same data, respectively by finiteness and by equivalences of the basis types with `Fin r`.
An instance forgets the finiteness refinement, while a named theorem forgets the fixed-rank
refinement, because the rank cannot be inferred from the target type.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v u₁

namespace AlgebraicGeometry.SheafOfModules

/-- A finite basis of a sheaf of modules on the slice over an object restricts to a finite
basis on the slice over any object above it: restriction is additive, so it preserves finite
coproducts. -/
noncomputable def overCofanIsColimit
    {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (F : _root_.SheafOfModules.{u} R)
    {I : Type u} [Finite I] {U V : C} (f : V ⟶ U)
    (ι : I → (_root_.SheafOfModules.unit (R.over U) ⟶ F.over U))
    (h : IsColimit (Cofan.mk (F.over U) ι)) :
    IsColimit (Cofan.mk (F.over V)
      (fun i => (_root_.SheafOfModules.overMap R f).map (ι i))) := by
  let T := _root_.SheafOfModules.overMap R f
  letI : T.Additive := ⟨rfl⟩
  exact (Cofan.isColimitMapCoconeEquiv T _ _).toFun (isColimitOfPreserves T h)

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A sheaf of modules is finite locally free if it has local free presentations whose
basis-indexing types are finite. -/
@[stacks 01C6 "(2)", ega "0 5.4.1" "finite rank"]
class IsFiniteLocallyFree (M : _root_.SheafOfModules.{u} R) : Prop where
  exists_isFiniteLocallyFreeData :
    ∃ q : _root_.SheafOfModules.LocalGeneratorsData.{u₁} M,
      q.IsLocallyFreeData ∧ q.IsFiniteType

/-- A sheaf of modules is finite locally free of rank `r` if it has local free presentations
whose basis-indexing types are equivalent to `Fin r`. -/
@[stacks 01C6 "(3)", ega "0 5.4.1" "rank n"]
class IsFiniteLocallyFreeOfRank (M : _root_.SheafOfModules.{u} R) (r : ℕ) : Prop where
  exists_isFiniteLocallyFreeOfRankData :
    ∃ q : _root_.SheafOfModules.LocalGeneratorsData.{u₁} M,
      q.IsLocallyFreeData ∧ ∀ i, Nonempty ((q.generators i).I ≃ Fin r)

/-- A finite locally free sheaf of modules is locally free. -/
instance (M : _root_.SheafOfModules.{u} R) [hM : IsFiniteLocallyFree M] : M.IsLocallyFree :=
  hM.exists_isFiniteLocallyFreeData.elim fun q h ↦ ⟨q, h.1⟩

/-- A finite locally free sheaf of fixed rank is finite locally free. This is not an
instance because the rank cannot in general be inferred from `IsFiniteLocallyFree M`. -/
theorem IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    (M : _root_.SheafOfModules.{u} R) (r : ℕ) [hM : IsFiniteLocallyFreeOfRank M r] :
    IsFiniteLocallyFree M :=
  hM.exists_isFiniteLocallyFreeOfRankData.elim fun q ⟨h, hr⟩ ↦
    ⟨q, h, ⟨fun i ↦ ⟨Finite.of_equiv (Fin r) (hr i).some.symm⟩⟩⟩

/-- Finite local freeness of rank `r` depends only on the isomorphism class of a sheaf of
modules: an isomorphism carries a local free presentation to one over the same cover and with
the same basis-indexing types. -/
theorem IsFiniteLocallyFreeOfRank.of_iso {M N : _root_.SheafOfModules.{u} R} {r : ℕ}
    (e : M ≅ N) (h : IsFiniteLocallyFreeOfRank.{u, v, u₁} M r) :
    IsFiniteLocallyFreeOfRank.{u, v, u₁} N r := by
  obtain ⟨q, hq, hr⟩ := h.exists_isFiniteLocallyFreeOfRankData
  let q' : _root_.SheafOfModules.LocalGeneratorsData.{u₁} N :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators i := (q.generators i).ofEpi
        ((_root_.SheafOfModules.overFunctor R (q.X i)).mapIso e).hom }
  refine ⟨q', ⟨fun i ↦ ?_⟩, hr⟩
  have h₀ : IsIso (q.generators i).π := hq.isIso i
  have h₁ : IsIso ((q.generators i).π ≫
      ((_root_.SheafOfModules.overFunctor R (q.X i)).mapIso e).hom) := inferInstance
  exact Eq.mpr (congrArg IsIso (_root_.SheafOfModules.GeneratingSections.ofEpi_π
    (q.generators i) ((_root_.SheafOfModules.overFunctor R (q.X i)).mapIso e).hom)) h₁

end AlgebraicGeometry.SheafOfModules
