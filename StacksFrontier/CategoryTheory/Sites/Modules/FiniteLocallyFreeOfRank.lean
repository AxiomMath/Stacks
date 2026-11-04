module

public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
import StacksCore.Tactic.StacksAttribute

/-!
# Finite locally free modules of a fixed rank on a ringed site

Let `(C, O)` be a ringed site. A sheaf of `O`-modules has **rank `r`** when every object `U`
of `C` admits a covering family `{V i ⟶ U}` on each member of which the restricted module is
a coproduct of `r` copies of the restricted structure sheaf. This is the rank clause of
Stacks 0409.

The covering condition already implies finite local freeness in the sense of Stacks 03DL(2),
so no separate hypothesis is needed: taking the index type of the free model to be `Fin r`
on every member of the covering exhibits the module as finite locally free with the rank
simply forgotten. That implication is `IsFiniteLocallyFreeOfRank.isFiniteLocallyFreeOnSite`.

## Main definitions

* `AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank`: having rank `r`, for a sheaf of
  modules on a ringed site.

## Main results

* `AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank.isFiniteLocallyFreeOnSite`: a module
  of rank `r` is finite locally free.

## Implementation notes

As in Stacks 03DL(2), freeness of a restricted module is expressed by a colimit cofan of
copies of the restricted structure sheaf, `SheafOfModules.unit (X.ringSheaf.over (V i))`.
What distinguishes the rank condition from plain finite local freeness is that the index type
is `Fin r` on *every* member of the covering, rather than a natural number allowed to vary
with the member; the condition is therefore stated directly as a covering-family criterion
rather than through `SheafOfModules.IsFiniteFree`, which quantifies over that number.

This is **not** `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank`
(`StacksFrontier/Topology/Sheaves/Modules/LocallyFree.lean`), which carries Stacks 01C6(3) and
asks for local generators over a covering of the *terminal* object of the site; the present
condition is imposed over every object, which is how Stacks 0409 states it, and the two
notions are not interchangeable on a site without a final object.

## References

* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.RingedSite

universe u v w

/-- A sheaf of modules on a ringed site is finite locally free of rank `r` if it is, over a
covering family of every object, a coproduct of `r` copies of the structure sheaf. This is the
rank clause of Stacks 0409. -/
@[stacks 0409 "rank", ega "0 5.4.1" "rank n"]
abbrev IsFiniteLocallyFreeOfRank (X : RingedSite.{u, v, w})
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (r : ℕ) : Prop :=
  ∀ U : X.C,
    ∃ (I : Type (max u v)) (V : I → X.C) (f : ∀ i, V i ⟶ U),
      (Sieve.ofArrows V f ∈ X.J U) ∧
        ∀ i : I,
          ∃ (ι : ∀ _ : Fin r,
              SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (V i)) ⟶
                F.over (V i)),
            Nonempty (IsColimit (Cofan.mk (F.over (V i)) ι))

/-- A sheaf of modules of rank `r` is finite locally free: the free model on each member of the
covering is the coproduct of `r` copies of the structure sheaf. -/
theorem IsFiniteLocallyFreeOfRank.isFiniteLocallyFreeOnSite
    {X : RingedSite.{u, v, w}}
    {F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} {r : ℕ}
    (h : IsFiniteLocallyFreeOfRank X F r) :
    SheafOfModules.IsFiniteLocallyFreeOnSite F :=
  (SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isColimit F).mpr fun U => by
    obtain ⟨I, V, f, hf, hfree⟩ := h U
    exact ⟨I, V, f, hf, fun i => ⟨r, hfree i⟩⟩

end AlgebraicGeometry.RingedSite
