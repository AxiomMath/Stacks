module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatFiniteFreeSummand
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.ConeOfAMorphism
import StacksCore.Tactic.StacksAttribute

/-!
# A flat module of finite presentation is locally a direct summand of a finite free module

Stacks 08FD says that a flat sheaf of modules of finite presentation on a ringed site is, locally
on the site, a retract of a free sheaf of modules on a *finite index type*. The predicate the
strictly perfect complexes of Stacks 08FM are built from, `IsDirectSummandOfFiniteFree`, instead
asks for a retract of the free sheaf of modules on `ULift (Fin n)`. This file connects the two:
a finite index type is in bijection with `ULift (Fin n)` for `n` its cardinality, and the free
sheaf of modules is functorial in the index type, so the retract transports.

## Main results

* `Stacks.SheafOfModules.isDirectSummandOfFiniteFree_of_retract_free`: a retract of a free sheaf
  of modules on a finite index type is a direct summand of a finite free sheaf of modules.
* `Stacks.SheafOfModules.exists_coveringSieve_isDirectSummandOfFiniteFree`: Stacks 08FD in that
  vocabulary.

## Implementation notes

The tag `08FD` stays on `Stacks.SheafOfModules.exists_coveringSieve_retract_free`, which states
the same assertion; the statement here is that assertion read through the predicate its consumers
use, so it carries no second copy of the attribute.

`IsDirectSummandOfFiniteFree` is stated at a module universe `m` independent of the structure
sheaf's universe `w` and compares the two after raising both with
`Stacks.SheafOfModules.moduleULift`; at `m = w`, which is where Stacks 08FD lands, that is the
plain retract condition, by `isDirectSummandOfFiniteFree_iff_free`.

Stating the predicate on a slice needs the sheaf condition for `AddCommGrpCat`-valued sheaves to
be preserved by `forget₂ RingCat AddCommGrpCat` there; that is the one typeclass hypothesis the
corollary adds to those of Stacks 08FD.

## References

* [Stacks Project, Tag 08FD](https://stacks.math.columbia.edu/tag/08FD)
* [Stacks Project, Tag 08FM](https://stacks.math.columbia.edu/tag/08FM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section

variable (R : Sheaf J RingCat.{w})
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **A retract of a free sheaf of modules on a finite index type is a direct summand of a
finite free sheaf of modules.** A finite `I` is in bijection with `ULift (Fin n)` for
`n = Nat.card I`, and `SheafOfModules.freeFunctor` carries that bijection to an isomorphism of
free sheaves of modules, along which the retract transports. -/
theorem isDirectSummandOfFiniteFree_of_retract_free (F : _root_.SheafOfModules.{w} R)
    (I : Type w) [Finite I] (i : F ⟶ _root_.SheafOfModules.free (R := R) I)
    (r : _root_.SheafOfModules.free (R := R) I ⟶ F) (hir : i ≫ r = 𝟙 F) :
    IsDirectSummandOfFiniteFree R F := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  let φ : _root_.SheafOfModules.free (R := R) I ≅
      _root_.SheafOfModules.free (R := R) (ULift.{w} (Fin n)) :=
    (_root_.SheafOfModules.freeFunctor (R := R)).mapIso (e.trans Equiv.ulift.symm).toIso
  rw [isDirectSummandOfFiniteFree_iff_free]
  refine ⟨n, i ≫ φ.hom, φ.inv ≫ r, ?_⟩
  rw [Category.assoc, ← Category.assoc φ.hom, φ.hom_inv_id, Category.id_comp, hir]

end

/-- **Stacks 08FD, in the vocabulary of `IsDirectSummandOfFiniteFree`.** A flat sheaf of modules
of finite presentation on a ringed site is, locally on the site, a direct summand of a finite
free sheaf of modules. This is the form in which the strictly perfect complexes of Stacks 08FM
consume Stacks 08FD. -/
theorem exists_coveringSieve_isDirectSummandOfFiniteFree
    [J.HasSheafCompose (forget₂ CommRingCat.{max v w} RingCat.{max v w})]
    [HasWeakSheafify J AddCommGrpCat.{max v w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max v w}]
    [∀ T : C, HasWeakSheafify (J.over T) AddCommGrpCat.{max v w}]
    [∀ T : C, (J.over T).WEqualsLocallyBijective AddCommGrpCat.{max v w}]
    (O : Sheaf J CommRingCat.{max v w})
    (F : _root_.SheafOfModules.{max v w} (commRingSheafToRingSheaf O))
    [F.IsFinitePresentation] (hF : IsFlat F) (U : C) :
    ∃ S : Sieve U, S ∈ J U ∧ ∀ {V : C} (f : V ⟶ U), S f →
      IsDirectSummandOfFiniteFree ((commRingSheafToRingSheaf O).over V) (F.over V) := by
  obtain ⟨S, hS, h⟩ := exists_coveringSieve_retract_free O F hF U
  refine ⟨S, hS, fun {V} f hf => ?_⟩
  obtain ⟨I, _, i, r, hir⟩ := h f hf
  exact isDirectSummandOfFiniteFree_of_retract_free _ _ I i r hir

end Stacks.SheafOfModules

end
