module

public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree

/-!
# Recognising finite local freeness from a trivialising cover

The predicates `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` and
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank` of Stacks Tag 01C6 are phrased in
terms of `SheafOfModules.LocalGeneratorsData`: a family of objects covering the terminal object
together with generating sections of the restrictions, subject to `IsLocallyFreeData`, which
asks that each `(generators i).π : free (generators i).I ⟶ M.over (X i)` be an isomorphism.

In practice one does not meet that data directly. What one produces instead is a *trivialising
cover*: a family `Y : I → C` covering the terminal object together with, for each `i`, an
isomorphism `free A ≅ M.over (Y i)`. This file converts the latter into the former, which is
the generic last step of the sheaf-level direction of Stacks Tags 01C6 and 05JM.

## Main definitions

* `Stacks.SheafOfModules.localGeneratorsDataOfFreeIso` packages a trivialising cover as
  `SheafOfModules.LocalGeneratorsData`.

## Main results

* `Stacks.SheafOfModules.isIso_generatingSections_ofEpi`: pushing the tautological generating
  sections of a free sheaf forward along an isomorphism again has invertible evaluation map.
* `Stacks.SheafOfModules.isFiniteLocallyFree_of_free_iso`: a sheaf trivialised by a cover with
  a finite index set is finite locally free.
* `Stacks.SheafOfModules.isFiniteLocallyFreeOfRank_of_free_iso`: a sheaf trivialised by a
  cover with index set `ULift (Fin r)` is finite locally free of rank `r`.

## Implementation notes

`isIso_generatingSections_ofEpi` is stated and proved on a bare site rather than inside the
slice-site variable block of the two main results, and it is the reason both of those can be
term proofs. The direct tactic proof of `IsIso ((free.generatingSections A).ofEpi e.hom).π`
fails: `SheafOfModules.GeneratingSections.ofEpi_π` rewrites the goal into
`IsIso ((free.generatingSections A).π ≫ e.hom)`, after which instance search no longer sees
Mathlib's `IsIso (free.generatingSections A).π`, because the rewrite leaves the index argument
as `(free.generatingSections A).I` rather than `A` — defeq but not syntactically equal. The
remedy is to establish the composite instance *first*, where it elaborates against `A`
directly, and then rewrite backwards in that hypothesis. No compiler option is involved.

For the same reason the covering family in `localGeneratorsDataOfFreeIso` is named `Y` and the
two main results feed `h i` to the helper as a term: the field `IsLocallyFreeData.isIso` binds
`i` at type `(localGeneratorsDataOfFreeIso Y hY h).I`, so the application has to be checked at
default transparency, which a term proof does and a `rw`-based tactic proof does not.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 05JM](https://stacks.math.columbia.edu/tag/05JM)
-/

@[expose] public section

open CategoryTheory

universe u v u₁

namespace Stacks.SheafOfModules

section Site

variable {D : Type u₁} [Category.{v} D] {K : GrothendieckTopology D} {S : Sheaf K RingCat.{u}}
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Transporting the tautological generating sections of `free A` along an isomorphism
`free A ≅ N` yields generating sections of `N` whose evaluation map is an isomorphism. -/
theorem isIso_generatingSections_ofEpi {N : _root_.SheafOfModules.{u} S} {A : Type u}
    (e : _root_.SheafOfModules.free.{u} A ≅ N) :
    IsIso ((_root_.SheafOfModules.free.generatingSections (R := S) A).ofEpi e.hom).π := by
  have h : IsIso ((_root_.SheafOfModules.free.generatingSections (R := S) A).π ≫ e.hom) :=
    inferInstance
  rwa [← _root_.SheafOfModules.GeneratingSections.ofEpi_π] at h

end Site

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The local generators data of a sheaf of modules trivialised by a cover: the covering family
is `Y`, and the generating sections over `Y i` are those of `free A` pushed forward along the
given isomorphism `free A ≅ M.over (Y i)`. -/
noncomputable def localGeneratorsDataOfFreeIso {M : _root_.SheafOfModules.{u} R} {A : Type u}
    {I : Type u₁} (Y : I → C) (hY : J.CoversTop Y)
    (h : ∀ i, _root_.SheafOfModules.free.{u} A ≅ M.over (Y i)) :
    _root_.SheafOfModules.LocalGeneratorsData.{u₁} M where
  I := I
  X := Y
  coversTop := hY
  generators i :=
    (_root_.SheafOfModules.free.generatingSections (R := R.over (Y i)) A).ofEpi (h i).hom

/-- A sheaf of modules trivialised over a cover of the terminal object by a free sheaf on a
finite index set is finite locally free. -/
theorem isFiniteLocallyFree_of_free_iso {M : _root_.SheafOfModules.{u} R} {A : Type u}
    [Finite A] {I : Type u₁} (Y : I → C) (hY : J.CoversTop Y)
    (h : ∀ i, _root_.SheafOfModules.free.{u} A ≅ M.over (Y i)) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree M :=
  ⟨localGeneratorsDataOfFreeIso Y hY h, ⟨fun i => isIso_generatingSections_ofEpi (h i)⟩,
    ⟨fun _ => ⟨‹Finite A›⟩⟩⟩

/-- A sheaf of modules trivialised over a cover of the terminal object by the free sheaf on
`ULift (Fin r)` is finite locally free of rank `r`. -/
theorem isFiniteLocallyFreeOfRank_of_free_iso {M : _root_.SheafOfModules.{u} R} (r : ℕ)
    {I : Type u₁} (Y : I → C) (hY : J.CoversTop Y)
    (h : ∀ i, _root_.SheafOfModules.free.{u} (ULift.{u} (Fin r)) ≅ M.over (Y i)) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank M r :=
  ⟨localGeneratorsDataOfFreeIso Y hY h, ⟨fun i => isIso_generatingSections_ofEpi (h i)⟩,
    fun _ => ⟨Equiv.ulift⟩⟩

end Stacks.SheafOfModules

end
