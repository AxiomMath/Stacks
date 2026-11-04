module

public import StacksFrontier.AlgebraicGeometry.InternalHomLocalKernel.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.FlatFinitePresentation
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.LocalKernelPresentation
import StacksCore.Tactic.StacksAttribute

/-!
# The dual of a finite locally free module is finite locally free

Let `X` be a scheme and let `ℰ` be a finite locally free `𝒪_X`-module. Then the dual
`ℰ^∨ = SheafHom(ℰ, 𝒪_X)` is again finite locally free, with no assumption that the rank of `ℰ`
be constant.

The argument is local and does not go through the rank. On a member `U` of a local free
presentation of `ℰ` the restriction `ℰ|_U` is free on a finite index set `I`; duality commutes
with restriction to `U`, and the dual of a free module on a finite index set is free on the same
index set, because internal Hom turns a finite coproduct in its first variable into a finite
product, which in an additive category is again that coproduct, and the dual of `𝒪_U` is `𝒪_U`.
So `ℰ^∨|_U` is free on `I`, and the members of the presentation of `ℰ` cover `X`.

## Main definitions

* `Stacks.AlgebraicGeometry.ReflexiveModules.freeIsoDualSheafOver`: on an open over which a
  module is free on a finite index set, its dual is free on the same index set.

## Main results

* `Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf`: the dual of a
  finite locally free module on a scheme is finite locally free.

## Implementation notes

Both local inputs are read off results already stated for a ringed site, at the ringed site
`Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite X` of the opens of `X`: duality
commutes with restriction is `Stacks.AlgebraicGeometry.InternalHomLocalKernel`'s
`sheafInternalHomOverIso`, the sheaf form of Tag 0E8H, and the dual of a finite free module is
`freeSheafInternalHomIso` at target the unit, both read on the slice site over `U`. No
computation with local sections and no local dual basis enters.

The rank-indexed results of the library require a constant rank and so do not apply: a finite
locally free module has a rank only locally, and the index sets of a local free presentation
vary from one member of the covering to another. What replaces them is
`AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_of_forall_exists_iso_free_over`, which
assembles finite local freeness from free restrictions on a neighbourhood of every point and so
never names a global rank. The index set used at a point is the one the presentation of `ℰ`
itself provides there, finite by the finiteness of that presentation.

The local statement is about the restriction `ℰ|_U` to the slice site of the opens of `X` over
`U`, and no open subscheme of `X` is formed.

## References

* [Stacks Project, Tag 0FA7](https://stacks.math.columbia.edu/tag/0FA7)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry Stacks.SheafOfModules.InternalHom
open Stacks.AlgebraicGeometry.InternalHomLocalKernel

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

/-- **The dual of a free module on a finite index set is free on that index set**, read on the
slice site of the opens of `X` over `U`: if the restriction of `ℰ` to `U` is free on a finite
index set `I`, then so is the restriction of `ℰ^∨` to `U`.

The restriction of the dual is the dual of the restriction, by Tag 0E8H, and the dual of
`𝒪_U^{⊕I}` is `𝒪_U^{⊕I}`, by Tag 03EN together with the computation of the dual of `𝒪_U`. -/
noncomputable def freeIsoDualSheafOver (X : Scheme.{u}) (U : X.Opens) (E : X.Modules)
    {I : Type u} [Finite I]
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ E.over U) :
    SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ (dualSheaf E).over U :=
  (sheafInternalHomOverIso (schemeRingedSite X) U E (SheafOfModules.unit X.ringCatSheaf) ≪≫
    ((sheafInternalHomFunctor ((Opens.grothendieckTopology ↥X).over U) (X.sheaf.over U)
        (SheafOfModules.unit (X.ringCatSheaf.over U))).mapIso e).unop ≪≫
      freeSheafInternalHomIso (X.sheaf.over U)
        (SheafOfModules.unit (X.ringCatSheaf.over U)) I).symm

/-- **Stacks Project, Tag 0FA7, the clause on the dual.** The dual `ℰ^∨ = SheafHom(ℰ, 𝒪_X)` of a
finite locally free module on a scheme is finite locally free. The rank of `ℰ` is not assumed
constant.

Every point has a neighbourhood `U` on which a local free presentation of `ℰ` trivialises it on
a finite index set, and there `ℰ^∨` is free on the same index set by `freeIsoDualSheafOver`. -/
@[stacks 0FA7 "dual_nonconstant_rank"]
theorem isFiniteLocallyFree_dualSheaf {X : Scheme.{u}} (E : X.Modules)
    (hE : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (dualSheaf E) := by
  apply SheafOfModules.isFiniteLocallyFree_of_forall_exists_iso_free_over
  intro x
  obtain ⟨q, hq, hqf⟩ := hE.exists_isFiniteLocallyFreeData
  obtain ⟨i, hxi⟩ := ((Opens.coversTop_iff _ q.X).1 q.coversTop).exists_mem x
  have hiso : IsIso (q.generators i).π := hq.isIso i
  have hfin : Finite (q.generators i).I := (hqf.isFiniteType i).finite
  exact ⟨q.X i, hxi, (q.generators i).I, hfin,
    ⟨freeIsoDualSheafOver X (q.X i) E (asIso (q.generators i).π)⟩⟩

/-- **Stacks Project, Tag 0FA7, the clause on the dual at a constant rank.** The dual
`ℰ^∨ = SheafHom(ℰ, 𝒪_X)` of a finite locally free module of rank `r` on a scheme is finite
locally free of rank `r`.

The covering and the index sets are those of `ℰ` itself: over each member `U` of a local free
presentation of `ℰ` on an index set `I`, `freeIsoDualSheafOver` trivialises `ℰ^∨` on the *same*
`I`, so the condition `I ≃ Fin r` carries over unchanged. In particular the rank is not
recomputed, and no local dual basis is chosen.

No `@[stacks]` attribute is placed on this declaration. Tag 0FA7 is the remark that the
identities above hold for modules of *nonconstant* rank, and that relations among homogeneous
polynomials in `r, c_1, c_2, …` may be proved by the splitting principle; it does not state that
the dual of a finite locally free module is finite locally free, at a constant rank or at any
other. This statement is a prerequisite of Tag 0FAE — it is what lets the Chern classes of `ℰ^∨`
be written at all, since `Stacks.Chow.GenuineChern.chernCap` is indexed by a constant rank. -/
theorem isFiniteLocallyFreeOfRank_dualSheaf {X : Scheme.{u}} (E : X.Modules) (r : ℕ)
    (hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R := X.ringCatSheaf) E r) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R := X.ringCatSheaf) (dualSheaf E) r := by
  obtain ⟨q, hq, hr⟩ := hE.exists_isFiniteLocallyFreeOfRankData
  have hfin : ∀ i, Finite (q.generators i).I := fun i => Finite.of_equiv _ (hr i).some.symm
  have hiso : ∀ i, IsIso (q.generators i).π := hq.isIso
  let e : ∀ i, _root_.SheafOfModules.free (R := X.ringCatSheaf.over (q.X i))
      (q.generators i).I ≅
        (dualSheaf E : _root_.SheafOfModules.{u} X.ringCatSheaf).over (q.X i) := fun i =>
    freeIsoDualSheafOver X (q.X i) E (asIso (q.generators i).π)
  refine ⟨⟨{ I := q.I
             X := q.X
             coversTop := q.coversTop
             generators := fun i => (_root_.SheafOfModules.free.generatingSections
               (R := X.ringCatSheaf.over (q.X i)) (q.generators i).I).ofEpi (e i).hom },
           ?_, fun i => ⟨(hr i).some⟩⟩⟩
  constructor
  intro i
  exact _root_.AlgebraicGeometry.SheafOfModules.isIso_free_generatingSections_ofEpi_π
    (q.generators i).I (e i)

end Stacks.AlgebraicGeometry.ReflexiveModules

end
