module

public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFiniteFreeSummand.Defs

/-!
# A finite locally free module is locally a finite free summand

Let `(X, O_X)` be a ringed space. A finite locally free sheaf of `O_X`-modules is locally
isomorphic to a finite free module, hence in particular locally a *direct summand* of one, which
is the hypothesis `Stacks.SheafOfModules.IsLocallyFiniteFreeSummand` of Stacks 0FNV.

## Main results

* `Stacks.SheafOfModules.OnSpace.isLocallyFiniteFreeSummand_of_isFiniteLocallyFree`.

## Implementation notes

The local generator data of `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` gives, around
each point, an open `U` and an isomorphism from a free module on a finite index type `I`; the
predicate here asks for a retract of `O_U^{⊕n}` with `n : ℕ`, so `I` is re-indexed by
`ULift (Fin (Fintype.card I))` through `SheafOfModules.freeFunctor`.

The retract is produced as the `hom`/`inv` pair of a *single* composite isomorphism rather than
as two composites with a proof that they cancel. That is not a stylistic choice: with the two
composites written out, discharging `i ≫ r = 𝟙` by `simp` does not terminate, and by
`rw [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id]` it reports a deterministic `isDefEq`
timeout at `Iso.hom_inv_id_assoc` — matching `α.hom ≫ α.inv ≫ f` against a composite of a
`mapIso` of `freeFunctor` and an `asIso` makes the unifier unfold both. `Iso.hom_inv_id` of the
composite needs no matching at all.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace Stacks.SheafOfModules.OnSpace

open Stacks.SheafOfModules.TensorStalkRingedSpace

variable (X : AlgebraicGeometry.RingedSpace.{u, u})

/-- A finite locally free sheaf of modules is locally a direct summand of a finite free
module. -/
theorem isLocallyFiniteFreeSummand_of_isFiniteLocallyFree
    (E : SheafOfModules.{u} (structureSheafRing X))
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    IsLocallyFiniteFreeSummand X E := by
  classical
  obtain ⟨q, hq, hqfin⟩ :=
    (inferInstance :
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        E).exists_isFiniteLocallyFreeData
  let _ : q.IsLocallyFreeData := hq
  let _ : q.IsFiniteType := hqfin
  intro x
  have hxcover : x ∈ ⨆ i, q.X i := by
    have hc := (Opens.coversTop_iff X.carrier q.X).mp q.coversTop
    rw [hc]
    trivial
  rw [TopologicalSpace.Opens.mem_iSup] at hxcover
  obtain ⟨i, hi⟩ := hxcover
  let U : TopologicalSpace.Opens X.carrier := q.X i
  let G := q.generators i
  let _ : IsIso G.π := hq.isIso i
  let _ : G.IsFiniteType := hqfin.isFiniteType i
  let _ : Fintype G.I := Fintype.ofFinite G.I
  let n : ℕ := Fintype.card G.I
  let e : G.I ≃ ULift.{u} (Fin n) := (Fintype.equivFin G.I).trans Equiv.ulift.symm
  let eFree : SheafOfModules.free (R := (structureSheafRing X).over U) G.I ≅
      SheafOfModules.free (R := (structureSheafRing X).over U) (ULift.{u} (Fin n)) :=
    (SheafOfModules.freeFunctor (R := (structureSheafRing X).over U)).mapIso (Equiv.toIso e)
  let eStart : SheafOfModules.free (R := (structureSheafRing X).over U) G.I ≅ E.over U :=
    asIso G.π
  let eTot : E.over U ≅
      SheafOfModules.free (R := (structureSheafRing X).over U) (ULift.{u} (Fin n)) :=
    eStart.symm.trans eFree
  exact ⟨U, hi, n, ⟨⟨eTot.hom, eTot.inv, eTot.hom_inv_id⟩⟩⟩

end Stacks.SheafOfModules.OnSpace
