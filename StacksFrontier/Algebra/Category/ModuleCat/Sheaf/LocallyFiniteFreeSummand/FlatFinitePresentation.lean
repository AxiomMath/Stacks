module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatFiniteFreeSummand
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFiniteFreeSummand.Defs
public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
import StacksCore.Tactic.StacksAttribute

/-!
# A flat module of finite presentation on a ringed space is locally a finite free summand

Let `(X, O_X)` be a ringed space and let `F` be a sheaf of `O_X`-modules which is flat and of
finite presentation. Then every point of `X` has an open neighbourhood on which `F` becomes a
direct summand of a finite free `O_X`-module. This is Stacks 08BL.

## Main results

* `Stacks.SheafOfModules.isLocallyFiniteFreeSummand_of_isFlat_of_isFinitePresentation`:
  **Stacks 08BL.**

## Implementation notes

A ringed space is the ringed site of its opens, so the statement is the ringed-site statement
Stacks 08FD, `Stacks.SheafOfModules.exists_coveringSieve_retract_free`, read on that site; no
part of the argument is redone here. Two translations are needed.

*From a covering sieve to a neighbourhood.* Stacks 08FD produces, for each object of the site, a
covering sieve on each member of which `F` is a retract of a free module on a finite index type.
Applied to the object `⊤` and read through `TopologicalSpace.Opens.mem_grothendieckTopology`,
that sieve is exactly a neighbourhood of each point of `X` with the required retraction, which
is the form `Stacks.SheafOfModules.IsLocallyFiniteFreeSummand` asks for.

*From a finite index type to `Fin n`.* The predicate of Stacks 0FNV is stated against
`SheafOfModules.free (ULift (Fin n))`, so that the rank is a natural number as in the source's
`O_U^{⊕n}`, while Stacks 08FD produces an arbitrary finite index type. A finite `I` is in
bijection with `ULift (Fin (Nat.card I))` and `SheafOfModules.freeFunctor` carries that bijection
to an isomorphism of free modules, along which the retract transports. This is the same
reindexing as `Stacks.SheafOfModules.isDirectSummandOfFiniteFree_of_retract_free`, which cannot
be reused because it lands in the *global* predicate on a slice rather than in a retract.

Two parallel copies of the flatness notion of Stacks 03ER exist in this repository:
`Stacks.SheafOfModules.IsFlat`, which Stacks 08FD is stated against, and
`AlgebraicGeometry.SheafOfModules.IsFlat`, which the ringed-space Tor-amplitude development uses.
They are the same proposition; `isFlat_iff_stacksIsFlat_sheaf` is that identification, and the
statement below is given at the second spelling, which is the one its consumers produce.

The universes of the ringed space, its structure sheaf and its modules all coincide. That is
forced, not chosen: the predicate `Stacks.SheafOfModules.IsLocallyFiniteFreeSummand` is stated at
`RingedSpace.{u, u}` with modules in `u`, and the sections of the modules in Stacks 08FD live in
`max v w` for a site `(C, J)` with `C : Type u` and `Category.{v} C` — and for `C = Opens X` both
site universes are the universe of the space.

## References

* [Stacks Project, Tag 08BL](https://stacks.math.columbia.edu/tag/08BL)
* [Stacks Project, Tag 08FD](https://stacks.math.columbia.edu/tag/08FD)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Stacks.SheafOfModules

universe u

variable {X : AlgebraicGeometry.RingedSpace.{u, u}}

/-- **The two copies of the flatness predicate of Stacks 03ER for sheaves of modules agree.**
`AlgebraicGeometry.SheafOfModules.IsFlat` and `Stacks.SheafOfModules.IsFlat` are built from two
separately declared but definitionally equal tensor functors. -/
theorem isFlat_iff_stacksIsFlat_sheaf
    (F : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) F ↔
      IsFlat.{u, u, u, u} (O := X.sheaf) F :=
  Iff.rfl

/-- **Stacks 08BL at the spelling Stacks 08FD is stated with.** The structure sheaf of rings of
a ringed space has two definitionally equal spellings, `Stacks.commRingSheafToRingSheaf` of its
`CommRingCat`-valued structure sheaf and
`structureSheafRing`; typeclass synthesis does not
cross between them, so the argument is run once at the first and transported to the second by
the explicit application below. -/
private theorem isLocallyFiniteFreeSummand_of_isFlat_ringSheafSpelling
    (F : _root_.SheafOfModules.{u} (commRingSheafToRingSheaf.{u, u, u} X.sheaf))
    [hfp : F.IsFinitePresentation] (hF : IsFlat.{u, u, u, u} (O := X.sheaf) F) :
    IsLocallyFiniteFreeSummand X F := by
  obtain ⟨S, hS, h⟩ := exists_coveringSieve_retract_free X.sheaf F hF ⊤
  intro x
  obtain ⟨V, f, hf, hxV⟩ := (Opens.mem_grothendieckTopology X.carrier).1 hS x trivial
  obtain ⟨I, hI, i, r, hir⟩ := h f hf
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  let φ : _root_.SheafOfModules.free
        (R := (commRingSheafToRingSheaf.{u, u, u} X.sheaf).over V) I ≅
      _root_.SheafOfModules.free
        (R := (commRingSheafToRingSheaf.{u, u, u} X.sheaf).over V) (ULift.{u} (Fin n)) :=
    (_root_.SheafOfModules.freeFunctor
      (R := (commRingSheafToRingSheaf.{u, u, u} X.sheaf).over V)).mapIso
      (e.trans Equiv.ulift.symm).toIso
  have ρ : Retract (F.over V) (_root_.SheafOfModules.free
      (R := (commRingSheafToRingSheaf.{u, u, u} X.sheaf).over V) (ULift.{u} (Fin n))) :=
    ⟨i ≫ φ.hom, φ.inv ≫ r, by simp [hir]⟩
  exact ⟨V, hxV, n, ⟨ρ⟩⟩

/-- **Stacks 08BL.** A flat sheaf of `O_X`-modules of finite presentation on a ringed space is,
locally on `X`, a direct summand of a finite free `O_X`-module.

This is Stacks 08FD on the site of opens of `X`: the covering sieve it produces on `⊤` is, by
`TopologicalSpace.Opens.mem_grothendieckTopology`, a neighbourhood of each point of `X` carrying
the retraction, and the finite index type of the free module there is reindexed by `Fin n`. -/
@[stacks 08BL]
theorem isLocallyFiniteFreeSummand_of_isFlat_of_isFinitePresentation
    (F : _root_.SheafOfModules.{u} (structureSheafRing X))
    [hfp₀ : F.IsFinitePresentation]
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) F) :
    IsLocallyFiniteFreeSummand X F :=
  isLocallyFiniteFreeSummand_of_isFlat_ringSheafSpelling F (hfp := hfp₀)
    ((isFlat_iff_stacksIsFlat_sheaf F).1 hF)

end Stacks.SheafOfModules

end
